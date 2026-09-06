"""Kernel-IR frontend: extract one C++ point-kernel function from a clang JSON
AST dump into the kernel IR (``groundline/kir.py``).

The C++ mirror of ``frontend/flang_kernel.py`` (DESIGN §2.3, §4):
everything clang-specific about kernel bodies lives here; the kernel IR,
``functionalize``, and the Lean printer are reused unchanged. TIM's kernels are
already per-point scalar functions, so extraction produces a rank-0
:class:`~groundline.kir.Kernel` directly — there is no ``pointize`` on this side.

Two calling conventions are admitted, never mixed: a ``void`` function whose
outputs are its ``Real &`` parameters, and a ``Real``-returning function whose
return value is the single output (the mirror of a Fortran ``result(name)``
function). In the latter the value flows through ``return e`` statements,
which must all sit in *tail position* — the last statement of the body, or of
a branch of an ``if`` that is itself in tail position — so that every path
ends in exactly one return; an early return (statements follow it on some
path) refuses, and a path that falls off the end without returning refuses
in ``functionalize`` (the result is unassigned there).

Trusted-base rule (VISION D6): everything here is deterministic and small
enough to audit. Any construct outside the supported subset raises
:class:`~groundline.kir.UnsupportedConstruct` — refusal, never a guess.

The JSON dump is an *intermediate*, never persisted: clang's node ``id`` fields
are memory addresses, nondeterministic across runs, so raw dumps must never be
golden-compared. Assertions belong on the extracted kernel IR or the printed
Lean, both of which are address-free.
"""

from __future__ import annotations

import json
import math
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Optional, Sequence

from groundline.kir import (
    ArrayRef, Assign, BinOp, Call, CallStmt, Cmp, ComponentRef, Do, Expr, If,
    IntLit, Kernel, Neg, Param, Paren, RealLit, Stmt, UnsupportedConstruct, Var,
)
from groundline.frontend.kernel_base import CppKernelSpec

# --------------------------------------------------------------------------- #
# clang invocation (pinned flags; JSON is an in-memory intermediate)
# --------------------------------------------------------------------------- #

BASE_FLAGS = ("-std=c++20", "-fsyntax-only")


def clang_version(clang: str = "clang++") -> str:
    """First line of ``clang++ --version`` — stamped into generated provenance."""
    out = subprocess.run([clang, "--version"], capture_output=True, text=True,
                         check=True)
    return out.stdout.splitlines()[0].strip()


def dump_function_json(source: Path, function: str, *, clang: str = "clang++",
                       include_dirs: Sequence[str] = ()) -> str:
    """Run clang on ``source`` and return the filtered JSON AST of ``function``.

    A header source is wrapped in a one-line translation unit (``#include``)
    in a temporary directory, mirroring how the header is consumed in a real
    build; ``.cpp`` sources are compiled directly.
    """
    source = Path(source).resolve()
    args = [clang, *BASE_FLAGS]
    args += [f"-I{d}" for d in include_dirs]
    args += ["-Xclang", "-ast-dump=json",
             "-Xclang", "-ast-dump-filter", "-Xclang", function]
    if source.suffix in (".hpp", ".hh", ".h"):
        with tempfile.TemporaryDirectory() as td:
            tu = Path(td) / "tu.cpp"
            tu.write_text(f'#include "{source}"\n')
            return _run_clang(args + [str(tu)])
    return _run_clang(args + [str(source)])


def _run_clang(args: list[str]) -> str:
    proc = subprocess.run(args, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"clang failed ({proc.returncode}): {' '.join(args)}\n"
                           f"{proc.stderr}")
    return proc.stdout


def parse_ast_objects(text: str) -> list[dict]:
    """Parse the dump output — one or more concatenated JSON objects."""
    decoder = json.JSONDecoder()
    objs: list[dict] = []
    i = 0
    while i < len(text):
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text):
            break
        obj, i = decoder.raw_decode(text, i)
        objs.append(obj)
    return objs


def find_function(objs: list[dict], name: str) -> dict:
    """The unique FunctionDecl *definition* (has a body) named ``name``."""
    hits = [o for o in objs
            if o.get("kind") == "FunctionDecl" and o.get("name") == name
            and any(c.get("kind") == "CompoundStmt" for c in o.get("inner", []))]
    if len(hits) != 1:
        raise UnsupportedConstruct(
            f"function '{name}': found {len(hits)} definitions in the dump")
    return hits[0]


# A real literal token as written: digits with an optional fraction and
# exponent, optionally amrex's `_rt` suffix. Hex floats and the f/l suffixes
# (a different type than Real) fall outside and refuse.
_LIT_TOKEN = re.compile(r"^(?=.*\d)(\d*\.?\d*(?:[eE][+-]?\d+)?)(_rt)?$")


def annotate_literal_spellings(objs: list[dict]) -> None:
    """Attach each ``FloatingLiteral``'s *source spelling* to its node
    (``n["spelling"]``), read from the file at the node's byte offset.

    The JSON's ``value`` is the parsed number printed back from clang's
    internal float — for a long-double literal (every ``_rt`` literal) that is
    an approximation with its own digits (``0.1_rt`` prints as
    ``0.100000000000000000001``), and printing it into an ℝ model would state
    a value the source never wrote. The spelling is the truth; ``value`` is
    kept as a cross-check (the two must agree to double precision, or the
    spelling is not attached and the literal refuses).

    Locations are tracked the way clang prints them — a ``file`` key appears
    on the first location in a new file and is elided until it changes. A
    token produced by a macro carries a ``spellingLoc`` (the macro's file)
    and an ``expansionLoc`` (where it landed); the file is tracked by the
    expansion — that is where the following tokens live — and a literal that
    is itself macro-produced gets no spelling (and refuses)."""
    files: dict[str, bytes] = {}

    def loc_of(d: Optional[dict]) -> Optional[dict]:
        if not isinstance(d, dict):
            return None
        return d.get("expansionLoc", d) if "offset" not in d else d

    def walk(n: dict, cur_file: Optional[str]) -> Optional[str]:
        for key in ("loc", "range"):
            d = n.get(key)
            if key == "range" and isinstance(d, dict):
                d = d.get("begin")
            d = loc_of(d)
            if isinstance(d, dict) and d.get("file"):
                cur_file = d["file"]
        if n.get("kind") == "FloatingLiteral" and cur_file:
            begin = n.get("range", {}).get("begin")
            if isinstance(begin, dict) and "offset" in begin and "tokLen" in begin:
                try:
                    data = files.setdefault(cur_file, Path(cur_file).read_bytes())
                    tok = data[begin["offset"]:begin["offset"] + begin["tokLen"]].decode("ascii")
                except (OSError, UnicodeDecodeError):
                    tok = ""
                m = _LIT_TOKEN.match(tok)
                if m:
                    spelling = m.group(1)
                    try:
                        agree = math.isclose(float(spelling), float(n.get("value", "nan")),
                                             rel_tol=1e-15, abs_tol=0.0)
                    except ValueError:
                        agree = False
                    if agree:
                        n["spelling"] = spelling
        for c in n.get("inner", []):
            if isinstance(c, dict):
                cur_file = walk(c, cur_file)
        return cur_file

    cur: Optional[str] = None
    for o in objs:
        cur = walk(o, cur)


def load_function(source: Path, function: str, *, clang: str = "clang++",
                  include_dirs: Sequence[str] = ()) -> dict:
    """Run clang and return ``function``'s FunctionDecl, literal spellings
    attached (the single entry point both extraction modes use)."""
    text = dump_function_json(source, function, clang=clang, include_dirs=include_dirs)
    objs = parse_ast_objects(text)
    annotate_literal_spellings(objs)
    return find_function(objs, function)


def _lit_text(n: dict) -> str:
    """A FloatingLiteral's source spelling (see :func:`annotate_literal_spellings`)."""
    spelling = n.get("spelling")
    if spelling is None:
        raise UnsupportedConstruct(
            f"real literal (clang value '{n.get('value')}') without a recoverable "
            f"source spelling — the parsed value is not the written one, and only "
            f"the written one is printed")
    return spelling


# --------------------------------------------------------------------------- #
# Node helpers
# --------------------------------------------------------------------------- #

def _inner(n: dict) -> list[dict]:
    """Semantic children: drop doc-comment nodes and kind-less placeholders."""
    return [c for c in n.get("inner", [])
            if c.get("kind") and "Comment" not in c["kind"]]


def _only(n: dict, context: str) -> dict:
    kids = _inner(n)
    if len(kids) != 1:
        raise UnsupportedConstruct(
            f"expected exactly one child under {context}, "
            f"have {[c.get('kind') for c in kids]}")
    return kids[0]


# --------------------------------------------------------------------------- #
# Expression extraction
# --------------------------------------------------------------------------- #

# ImplicitCastExpr kinds unwrapped transparently — ONLY casts that provably
# preserve the value for the real-scalar subset. Any kind not listed refuses:
# a value-CHANGING implicit cast (IntegralToFloating, FloatingCast, ...)
# silently unwrapped is exactly the plausible-but-wrong model this pipeline must
# never produce.
_TRANSPARENT_CASTS = {
    # Reading a variable: the lvalue (a storage location) is converted to the
    # rvalue it currently holds. Pure value-category bookkeeping — the value
    # read is by definition the value stored; no representation change.
    "LValueToRValue",
    # A function name decaying to a function pointer in callee position. No
    # data value is involved; which function is called is unchanged.
    "FunctionToPointerDecay",
    # A conversion that changes nothing but qualifiers (`Real` → `const Real`
    # when a prvalue binds to a `const Real &` parameter, as amrex::max's
    # do). The value is untouched by definition of the cast kind.
    "NoOp",
}

# Single-child wrapper nodes clang inserts around an expression without
# changing its value: the cleanup scope for temporaries a full-expression
# created, and the temporary materialized to bind a prvalue to a const
# reference. Both are unwrapped transparently.
_TRANSPARENT_WRAPPERS = {"ExprWithCleanups", "MaterializeTemporaryExpr"}

# Callees admitted as intrinsics, with their arity: amrex::Math::abs, and
# amrex::max / amrex::min in their binary form (AMReX's three-argument
# overloads refuse until a kernel needs them). Acceptance is on the
# referenced declaration's name — the JSON drops the namespace qualifier.
_CALLEES = {"abs": 1, "max": 2, "min": 2}

_BINOPS = {"+": "add", "-": "sub", "*": "mul", "/": "div"}
_CMPS = {"<": "lt", "<=": "le", ">": "gt", ">=": "ge", "==": "eq", "!=": "ne"}

# Variable references must resolve to a parameter or a local — a DeclRefExpr
# to anything else (a global, an enumerator) is outside the subset.
_VAR_DECL_KINDS = {"ParmVarDecl", "VarDecl"}


def _unwrap_casts(n: dict) -> dict:
    """Strip allowlisted implicit casts; any other cast kind refuses."""
    while n.get("kind") == "ImplicitCastExpr":
        ck = n.get("castKind")
        if ck not in _TRANSPARENT_CASTS:
            raise UnsupportedConstruct(f"implicit cast kind '{ck}' is not on the "
                                       f"value-preserving allowlist")
        n = _only(n, "ImplicitCastExpr")
    return n


def extract_expr(n: dict) -> Expr:
    kind = n.get("kind")
    if kind == "ImplicitCastExpr":
        return extract_expr(_unwrap_casts(n))
    if kind in _TRANSPARENT_WRAPPERS:
        return extract_expr(_only(n, kind))
    if kind == "DeclRefExpr":
        ref = n.get("referencedDecl", {})
        if ref.get("kind") not in _VAR_DECL_KINDS:
            raise UnsupportedConstruct(
                f"reference to '{ref.get('name')}' ({ref.get('kind')}) — only "
                f"parameters and locals are supported in expressions")
        return Var(ref["name"])
    if kind == "FloatingLiteral":
        return RealLit(_lit_text(n))
    if kind == "UserDefinedLiteral":
        return _extract_udl(n)
    if kind == "ParenExpr":
        return Paren(extract_expr(_only(n, "ParenExpr")))
    if kind == "UnaryOperator":
        if n.get("opcode") != "-" or n.get("isPostfix"):
            raise UnsupportedConstruct(f"unary operator '{n.get('opcode')}'")
        return Neg(extract_expr(_only(n, "UnaryOperator")))
    if kind == "BinaryOperator":
        op = n.get("opcode")
        kids = _inner(n)
        if len(kids) != 2:
            raise UnsupportedConstruct(f"binary operator with {len(kids)} operands")
        if op in _BINOPS:
            return BinOp(_BINOPS[op], extract_expr(kids[0]), extract_expr(kids[1]))
        if op == "!=" and _is_flag_array_read(kids[0]) and _is_int_zero(kids[1]):
            # `do_I(i,j,0) != 0`: the C++ spelling of a logical flag stored in
            # an integer Array4 — the read IS the flag (a Bool per cell); the
            # integer never appears as a value.
            return _extract_array_read(_unwrap_casts(kids[0]), as_flag=True)
        if op in _CMPS:
            return Cmp(_CMPS[op], extract_expr(kids[0]), extract_expr(kids[1]))
        raise UnsupportedConstruct(f"binary operator '{op}' in expression position")
    if kind == "CallExpr":
        return _extract_call(n)
    if kind == "CXXOperatorCallExpr":
        return _extract_array_read(n)
    if kind == "MemberExpr":
        # `CS.vol_CFL`: a member of a struct parameter — rule B's mirror.
        if n.get("isArrow"):
            raise UnsupportedConstruct("member access through a pointer ('->')")
        base = _unwrap_casts(_only(n, "MemberExpr"))
        if base.get("kind") != "DeclRefExpr" or \
                base.get("referencedDecl", {}).get("kind") != "ParmVarDecl":
            raise UnsupportedConstruct("member read on something other than a parameter")
        return ComponentRef(base["referencedDecl"]["name"], n["name"], ())
    raise UnsupportedConstruct(f"expression node '{kind}'")


# The integer Array4 spelling of a per-cell logical flag (AMReX has no bool
# Array4); readable only as `x(i,j,k) != 0` — see extract_expr.
_FLAG_ARRAY_TYPES = ("const Array4<const int> &",)


def _is_flag_array_read(n: dict) -> bool:
    n = _unwrap_casts(n)
    if n.get("kind") != "CXXOperatorCallExpr":
        return False
    kids = _inner(n)
    arr = _unwrap_casts(kids[1]) if len(kids) >= 2 else {}
    qual = arr.get("referencedDecl", {}).get("type", {}).get("qualType", "")
    return arr.get("kind") == "DeclRefExpr" and qual in _FLAG_ARRAY_TYPES


def _is_int_zero(n: dict) -> bool:
    n = _unwrap_casts(n)
    return n.get("kind") == "IntegerLiteral" and n.get("value") == "0"


def _extract_array_read(n: dict, *, as_flag: bool = False) -> ArrayRef:
    """``a(i, j, k)`` on an ``Array4`` parameter — ``operator()`` applied to
    the array and three index expressions. Indices are addresses: a lambda
    column index or the loop variable (a ``DeclRefExpr``), one of them plus
    or minus an integer literal (a stencil), or a trailing literal ``0`` — the
    unit third extent AMReX gives 2-D fields, dropped so the reference has
    the column shape. Anything else in an index position refuses. An integer
    (flag) array is readable only in the ``!= 0`` shape (``as_flag``)."""
    kids = _inner(n)
    if not kids:
        raise UnsupportedConstruct("operator call with no callee")
    callee = _unwrap_casts(kids[0])
    if callee.get("referencedDecl", {}).get("name") != "operator()":
        raise UnsupportedConstruct(
            f"operator '{callee.get('referencedDecl', {}).get('name')}'")
    if len(kids) != 5:
        raise UnsupportedConstruct(f"operator() with {len(kids) - 2} indices (3 expected)")
    arr = _unwrap_casts(kids[1])
    if arr.get("kind") != "DeclRefExpr" or \
            arr.get("referencedDecl", {}).get("kind") != "ParmVarDecl":
        raise UnsupportedConstruct("Array4 access on something other than a parameter")
    if _is_flag_array_read(n) and not as_flag:
        raise UnsupportedConstruct(
            f"integer Array4 '{arr['referencedDecl']['name']}' read as a value — "
            f"an integer array is admitted only as a per-cell flag, in the "
            f"shape `x(i,j,k) != 0`")
    subs: list[Expr] = []
    for pos, idx in enumerate(kids[2:]):
        idx = _unwrap_casts(idx)
        if idx.get("kind") == "IntegerLiteral":
            if pos == 2 and idx.get("value") == "0":
                continue                 # the unit third extent of a 2-D field
            raise UnsupportedConstruct(
                f"literal index '{idx.get('value')}' in position {pos + 1}")
        subs.append(_extract_index(idx))
    return ArrayRef(arr["referencedDecl"]["name"], tuple(subs))


def _extract_index(n: dict) -> Expr:
    """An index expression: a variable, or variable ± integer literal."""
    n = _unwrap_casts(n)
    if n.get("kind") == "DeclRefExpr":
        return Var(n["referencedDecl"]["name"])
    if n.get("kind") == "BinaryOperator" and n.get("opcode") in ("+", "-"):
        a, b = _inner(n)
        a, b = _unwrap_casts(a), _unwrap_casts(b)
        if a.get("kind") == "DeclRefExpr" and b.get("kind") == "IntegerLiteral":
            return BinOp("add" if n["opcode"] == "+" else "sub",
                         Var(a["referencedDecl"]["name"]), IntLit(b["value"]))
    raise UnsupportedConstruct(f"index expression '{n.get('kind')}'")


def _extract_udl(n: dict) -> RealLit:
    """``3.0_rt`` — amrex's Real literal suffix. The node is a call to
    ``operator""_rt`` whose operand is the FloatingLiteral; the literal's
    printed ``value`` is taken textually (spelling fidelity)."""
    kids = _inner(n)
    if len(kids) != 2:
        raise UnsupportedConstruct("user-defined literal with unexpected shape")
    callee = _unwrap_casts(kids[0])
    op_name = callee.get("referencedDecl", {}).get("name")
    if op_name != 'operator""_rt':
        raise UnsupportedConstruct(f"user-defined literal suffix '{op_name}' "
                                   f"(only _rt is supported)")
    lit = kids[1]
    if lit.get("kind") != "FloatingLiteral":
        raise UnsupportedConstruct(
            f"user-defined literal operand '{lit.get('kind')}'")
    return RealLit(_lit_text(lit))


def _extract_call(n: dict) -> Call:
    """The intrinsic callees of ``_CALLEES``, at their arity. NOTE: the JSON
    drops the callee's nested-name-specifier — ``amrex::Math::abs`` surfaces
    as a DeclRefExpr whose ``referencedDecl`` is the FunctionDecl named
    ``abs`` (found through amrex's ``using std::abs`` shadow), ``amrex::max``
    as the FunctionDecl ``max`` — so the check is on the referenced
    declaration's name, not the source spelling."""
    kids = _inner(n)
    if not kids:
        raise UnsupportedConstruct("call with no callee")
    callee = _unwrap_casts(kids[0])
    if callee.get("kind") != "DeclRefExpr":
        raise UnsupportedConstruct(f"callee node '{callee.get('kind')}'")
    fname = callee.get("referencedDecl", {}).get("name")
    if fname not in _CALLEES:
        raise UnsupportedConstruct(
            f"call to '{fname}' (only {sorted(_CALLEES)} are supported)")
    args = kids[1:]
    if len(args) != _CALLEES[fname]:
        raise UnsupportedConstruct(
            f"{fname} with {len(args)} arguments (only the "
            f"{_CALLEES[fname]}-argument form is modeled)")
    return Call(fname, tuple(extract_expr(a) for a in args))


# --------------------------------------------------------------------------- #
# Statement extraction
# --------------------------------------------------------------------------- #

# Local declarations: real scalars, matched on the observed qualType
# spellings — `Real` (amrex's alias; the headers do `using amrex::Real`, so
# qualType prints the alias) and plain `double`, each optionally const — and
# bool scalars (a `let` of a Bool-valued expression). Anything else — an
# integer local, a pointer, a reference — refuses.
_REAL_LOCAL_TYPES = {"Real", "const Real", "double", "const double"}
_BOOL_LOCAL_TYPES = {"bool", "const bool"}


def _extract_stmts(n: dict, locals_out: list[Param], *,
                   result: Optional[str] = None, tail: bool = False,
                   column: Optional["_ColumnCtx"] = None) -> list[Stmt]:
    """One statement node → kernel-IR statements. ``locals_out`` accumulates
    the VarDecls encountered (C++ declares locals inline, not up front).

    ``result`` is the name the kernel's return value is assigned to (``None``
    for a void kernel); ``tail`` says whether this statement is in tail
    position — the only place a ``return`` may appear (see the module
    docstring). ``column`` is set inside a ``ParallelFor`` lambda (column
    mode): it carries the hypotheses that prune guarded blocks and admits
    the column shapes — Array4 writes, ``for k`` loops, ``+=``, and call
    statements to banked primitives."""
    kind = n.get("kind")
    if kind == "CompoundStmt":
        out: list[Stmt] = []
        kids = _inner(n)
        for i, c in enumerate(kids):
            out.extend(_extract_stmts(c, locals_out, result=result,
                                      tail=tail and i == len(kids) - 1,
                                      column=column))
        return out
    if column is not None:
        if kind == "CompoundAssignOperator" and n.get("opcode") == "+=":
            lhs, rhs = _inner(n)
            target = _extract_target(lhs, locals_out)
            read = target if isinstance(target, Var) else ArrayRef(target.name, target.subscripts)
            return [Assign(target, BinOp("add", read, extract_expr(rhs)))]
        if kind == "CallExpr":
            # A call statement: `f(a, b(i,j,k), out1, out2);` — the actuals in
            # order; `Real&` receivers arrive as bare DeclRefExprs (lvalues).
            kids = _inner(n)
            callee = _unwrap_casts(kids[0])
            fname = callee.get("referencedDecl", {}).get("name")
            if callee.get("kind") != "DeclRefExpr" or fname is None:
                raise UnsupportedConstruct("call statement with a non-function callee")
            return [CallStmt(fname, tuple(_extract_actual(a) for a in kids[1:]))]
        if kind == "ForStmt":
            return [_extract_for(n, locals_out, column)]
        if kind == "IfStmt" and _cxx_decided_false(_inner(n)[0], column.assume):
            if n.get("hasElse"):
                raise UnsupportedConstruct(
                    "an `if` decided false by a hypothesis, but carrying an else "
                    "branch — reducing it is not yet supported")
            return []
    if kind == "DeclStmt":
        out = []
        for vd in _inner(n):
            init = _extract_vardecl(vd, locals_out)
            if init is not None:
                out.append(init)
        return out
    if kind == "BinaryOperator" and n.get("opcode") == "=":
        kids = _inner(n)
        if len(kids) != 2:
            raise UnsupportedConstruct("assignment with unexpected shape")
        lhs, rhs = kids
        if column is not None and lhs.get("kind") == "CXXOperatorCallExpr":
            return [Assign(_extract_array_read(lhs), extract_expr(rhs))]
        ref = lhs.get("referencedDecl", {}) if lhs.get("kind") == "DeclRefExpr" else {}
        is_local = (ref.get("kind") == "VarDecl"
                    and any(l.name == ref.get("name") for l in locals_out))
        if ref.get("kind") != "ParmVarDecl" and not is_local:
            raise UnsupportedConstruct(
                "assignment target must be a (reference) parameter or a "
                f"declared local; got '{lhs.get('kind')}'")
        return [Assign(Var(ref["name"]), extract_expr(rhs))]
    if kind == "IfStmt":
        return [_extract_if(n, locals_out, result=result, tail=tail, column=column)]
    if kind == "ReturnStmt":
        # The return value is the kernel's single output: `return e` assigns
        # it. Only in tail position — an early return would make the
        # statements after it conditional in a way the flat body cannot say.
        if result is None:
            raise UnsupportedConstruct("return statement in a void kernel")
        kids = _inner(n)
        if len(kids) != 1:
            raise UnsupportedConstruct(
                "return without a value in a non-void kernel")
        if not tail:
            raise UnsupportedConstruct(
                "return in non-tail position (an early return — statements "
                "follow it on some path)")
        return [Assign(Var(result), extract_expr(kids[0]))]
    raise UnsupportedConstruct(f"statement '{kind}'")


def _extract_vardecl(vd: dict, locals_out: list[Param]) -> Optional[Stmt]:
    """``Real const x = e;`` → record the local + return the initializing
    Assign (feeds ``functionalize``'s Let path, exactly like a Fortran local).
    ``Real x;`` (no initializer) → record the local only; its later
    assignments arrive as ordinary statements, and a read before the first
    one refuses in ``functionalize``. List/direct initialization refuses."""
    if vd.get("kind") != "VarDecl":
        raise UnsupportedConstruct(f"declaration '{vd.get('kind')}'")
    name = vd["name"]
    qual = vd.get("type", {}).get("qualType")
    if qual not in _REAL_LOCAL_TYPES and qual not in _BOOL_LOCAL_TYPES:
        raise UnsupportedConstruct(f"local '{name}': type '{qual}' (only real "
                                   f"scalars — Real or double — and bool are supported)")
    init = vd.get("init")
    if init is not None and init != "c":
        raise UnsupportedConstruct(
            f"local '{name}' with a list/direct initializer — only the "
            f"copy-initializer (= form) and a bare declaration are supported")
    if any(p.name == name for p in locals_out):
        raise UnsupportedConstruct(
            f"local '{name}' declared more than once (C++ block scoping does "
            f"not map to the flat Let model)")
    locals_out.append(Param(name, "logical" if qual in _BOOL_LOCAL_TYPES else "real", None, 0))
    if init is None:
        return None
    return Assign(Var(name), extract_expr(_only(vd, f"VarDecl '{name}'")))


def _extract_target(lhs: dict, locals_out: list[Param]) -> Var | ArrayRef:
    if lhs.get("kind") == "CXXOperatorCallExpr":
        return _extract_array_read(lhs)
    ref = lhs.get("referencedDecl", {}) if lhs.get("kind") == "DeclRefExpr" else {}
    if ref.get("kind") == "ParmVarDecl" or (
            ref.get("kind") == "VarDecl" and any(l.name == ref.get("name") for l in locals_out)):
        return Var(ref["name"])
    raise UnsupportedConstruct(
        f"assignment target must be a parameter, a declared local or an Array4 "
        f"cell; got '{lhs.get('kind')}'")


def _extract_actual(a: dict) -> Expr:
    """A call actual: a bare lvalue (a `Real&` receiver, a local) or a value."""
    if a.get("kind") == "DeclRefExpr":
        ref = a.get("referencedDecl", {})
        if ref.get("kind") in _VAR_DECL_KINDS:
            return Var(ref["name"])
    return extract_expr(a)


def _cxx_decided_false(cond: dict, assume: dict[str, bool]) -> bool:
    """The hypotheses decide a condition false: an assumed-false flag (a
    parameter or a captured local), or `&&` with such an operand."""
    cond = _unwrap_casts(cond)
    if cond.get("kind") == "DeclRefExpr":
        # Flag names are matched case-insensitively: the manifest spells them
        # once for both sides, and Fortran has no case.
        return assume.get(str(cond.get("referencedDecl", {}).get("name")).lower()) is False
    if cond.get("kind") == "ParenExpr":
        return _cxx_decided_false(_only(cond, "ParenExpr"), assume)
    if cond.get("kind") == "BinaryOperator" and cond.get("opcode") == "&&":
        return any(_cxx_decided_false(c, assume) for c in _inner(cond))
    return False


def _extract_for(n: dict, locals_out: list[Param], column: "_ColumnCtx") -> Do:
    """``for (int k = lo; k <= hi; ++k) body`` over captured integer bounds →
    a plain ``Do`` the column pass turns into a fold or a map. The exact
    shape — an int declared from a captured const, `<=` against a captured
    const, prefix or postfix `++` — is required; anything else refuses."""
    kids = _inner(n)
    if len(kids) != 4:
        raise UnsupportedConstruct(f"for statement with {len(kids)} parts (init, cond, inc, body expected)")
    init, cond, inc, body = kids
    if init.get("kind") != "DeclStmt" or len(_inner(init)) != 1:
        raise UnsupportedConstruct("for loop without a single declared loop variable")
    vd = _inner(init)[0]
    if vd.get("type", {}).get("qualType") != "int" or vd.get("init") != "c":
        raise UnsupportedConstruct("for loop variable must be an int initialized by copy")
    k = vd["name"]
    lo = _extract_index(_only(vd, "VarDecl"))
    if cond.get("kind") != "BinaryOperator" or cond.get("opcode") != "<=":
        raise UnsupportedConstruct("for loop condition must be `k <= hi`")
    lhs, rhs = _inner(cond)
    if _extract_index(lhs) != Var(k):
        raise UnsupportedConstruct("for loop condition must test the loop variable")
    hi = _extract_index(rhs)
    if inc.get("kind") != "UnaryOperator" or inc.get("opcode") != "++":
        raise UnsupportedConstruct("for loop increment must be `++k`")
    if not (isinstance(lo, Var) and isinstance(hi, Var)):
        raise UnsupportedConstruct("for loop bounds must be captured variables")
    column.bounds.update({lo.name, hi.name})
    column.loop_vars.add(k)
    stmts = tuple(_extract_stmts(body, locals_out, column=column))
    return Do((k, lo, hi), stmts)


class _ColumnCtx:
    def __init__(self, assume: dict[str, bool]):
        self.assume = assume
        self.bounds: set[str] = set()
        self.loop_vars: set[str] = set()


def _extract_if(n: dict, locals_out: list[Param], *,
                result: Optional[str] = None, tail: bool = False,
                column: Optional[_ColumnCtx] = None) -> If:
    if n.get("hasInit") or n.get("hasVar") or n.get("isConstexpr"):
        raise UnsupportedConstruct(
            "if with an init-statement / condition variable / constexpr")
    kids = _inner(n)
    has_else = bool(n.get("hasElse"))
    if len(kids) != (3 if has_else else 2):
        raise UnsupportedConstruct(f"if statement with {len(kids)} children")
    cond = extract_expr(kids[0])
    # Branches inherit the if's tail position.
    then = tuple(_extract_stmts(kids[1], locals_out, result=result, tail=tail,
                                column=column))
    orelse = tuple(_extract_stmts(kids[2], locals_out, result=result,
                                  tail=tail, column=column)) if has_else else ()
    # `else if` arrives as an IfStmt in the else slot (C++ has no elseif). An
    # else holding exactly one if IS an elseif, so it is flattened into the
    # branch list — the same IR flang's ElseIfBlock yields — so that the two
    # frontends' joins take the same shape (a nested if would merge in two
    # steps and print its tuple differently).
    if len(orelse) == 1 and isinstance(orelse[0], If):
        inner = orelse[0]
        return If(((cond, then),) + inner.branches, inner.orelse)
    return If(((cond, then),), orelse)


# --------------------------------------------------------------------------- #
# Parameters + kernel assembly
# --------------------------------------------------------------------------- #

def _extract_param(pd: dict) -> Param:
    """Intent mapping (the point-kernel calling convention): a non-const
    lvalue reference (``Real &`` / ``double &``) → inout; a const by-value
    scalar (clang prints ``const Real`` / ``const double``) → in. Anything
    else — pointers, const refs, non-real types, defaulted parameters —
    refuses."""
    name = pd.get("name")
    if _inner(pd) or pd.get("init"):
        raise UnsupportedConstruct(f"parameter '{name}' has a default argument")
    qual = pd.get("type", {}).get("qualType")
    if qual in ("Real &", "double &"):
        return Param(name, "real", "inout", 0)
    if qual in ("const Real", "const double"):
        return Param(name, "real", "in", 0)
    if qual == "const bool":
        return Param(name, "logical", "in", 0)     # a Bool input (a bare `if` guard)
    raise UnsupportedConstruct(
        f"parameter '{name}': type '{qual}' (supported: 'Real &'/'double &' "
        f"→ inout, 'const Real'/'const double' → in, 'const bool' → a "
        f"logical in)")


# Return types of the two admitted calling conventions (the function's
# qualType begins with its return type): void → outputs are the `Real &`
# parameters; a real scalar → the return value is the single output.
_VOID_RETURN = ("void (",)
_REAL_RETURN = ("Real (", "double (")


def extract_kernel_from_decl(decl: dict) -> Kernel:
    name = decl.get("name")
    ret = decl.get("type", {}).get("qualType", "")
    if ret.startswith(_VOID_RETURN):
        result = None
    elif ret.startswith(_REAL_RETURN):
        # The return value has no source name; Fortran's own default for a
        # result variable — the function's name — is the deterministic choice.
        result = name
    else:
        raise UnsupportedConstruct(
            f"{name}: kernel must return void or a real scalar (Real/double), "
            f"has '{ret}'")
    params: list[Param] = []
    body_node = None
    for c in _inner(decl):
        kind = c.get("kind", "")
        if kind == "ParmVarDecl":
            params.append(_extract_param(c))
        elif kind == "CompoundStmt":
            if body_node is not None:
                raise UnsupportedConstruct(f"{name}: multiple bodies")
            body_node = c
        elif kind.endswith("Attr"):
            # Declaration attributes (AlwaysInlineAttr from AMREX_FORCE_INLINE,
            # ...) direct codegen/optimization; they cannot change the value
            # semantics of the statement tree extracted below, which itself
            # stays fully allowlisted.
            continue
        else:
            raise UnsupportedConstruct(f"{name}: unexpected child '{kind}'")
    if body_node is None:
        raise UnsupportedConstruct(f"{name}: no function body")
    if result is not None:
        mutated = [p.name for p in params if p.intent == "inout"]
        if mutated:
            raise UnsupportedConstruct(
                f"{name}: a non-void function with reference parameters "
                f"{mutated} — two output conventions (a return value and "
                f"mutated arguments) in one kernel")
    locals_: list[Param] = []
    body = tuple(_extract_stmts(body_node, locals_, result=result, tail=True))
    param_names = {p.name for p in params}
    shadowed = [l.name for l in locals_ if l.name in param_names]
    if shadowed:
        raise UnsupportedConstruct(f"{name}: locals shadow parameters {shadowed}")
    if result is not None:
        if result in param_names or any(l.name == result for l in locals_):
            raise UnsupportedConstruct(
                f"{name}: the result name (the function's own name) collides "
                f"with a parameter or local")
        params.append(Param(result, "real", "result", 0))
    return Kernel(name, tuple(params), tuple(locals_), body)


# Function parameter types admitted in column mode, beyond the point-kernel
# scalars: AMReX arrays (per-cell or per-column, decided by how the lambda
# indexes them), const struct references (member reads become inputs), a
# `const Box &` (bounds only), and raw pointers (must go unreferenced).
def _extract_column_param(pd: dict) -> Param:
    name = pd.get("name")
    qual = pd.get("type", {}).get("qualType", "")
    if qual.startswith("const Array4<const Real> &") or qual.startswith("const Array4<const double> &"):
        return Param(name, "real", "in", 3)
    if qual.startswith("const Array4<Real> &") or qual.startswith("const Array4<double> &"):
        return Param(name, "real", "inout", 3)
    if qual in _FLAG_ARRAY_TYPES:
        return Param(name, "logical", "in", 3)     # a per-cell flag, read as `!= 0`
    if qual in ("Real", "const Real", "double", "const double"):
        return Param(name, "real", "in", 0)
    if qual in ("bool", "const bool"):
        return Param(name, "logical", "in", 0)
    if qual == "const Box &":
        return Param(name, "box", "in", 0)
    if qual.startswith("const ") and qual.endswith(" &"):
        return Param(name, "derived:" + qual[len("const "):-2].strip(), "in", 0)
    if qual.endswith("*"):
        return Param(name, "pointer:" + qual[:-1].strip(), "in", 0)
    raise UnsupportedConstruct(
        f"parameter '{name}': type '{qual}' is not an admitted column-kernel "
        f"parameter (Array4, Real, bool, const struct &, const Box &, pointer)")


def _lambdas(n: dict, acc: list[dict]) -> None:
    if n.get("kind") == "LambdaExpr":
        acc.append(n)
        return                     # nested lambdas are not separately addressable
    for c in _inner(n):
        _lambdas(c, acc)


def extract_column_kernel_from_decl(decl: dict, parallel_for: int,
                                    columns: Sequence[str],
                                    assume: dict[str, bool]) -> Kernel:
    """Column mode: the body of the lambda passed to the ``parallel_for``-th
    `ParallelFor` call (1-based, source order) in ``decl``, with the lambda's
    named parameters as the column indices (they must spell ``columns``), the
    function's parameters as the kernel's parameters, `for k` loops kept as
    ``Do`` for :func:`groundline.column.columnize`, and blocks guarded by an
    assumed-false flag pruned before modeling. Statements of the function
    outside the lambda are not modeled: a captured function-scope local may
    only be a loop bound or an assumed flag."""
    name = decl.get("name")
    params = [_extract_column_param(c) for c in _inner(decl) if c.get("kind") == "ParmVarDecl"]
    body_node = next((c for c in _inner(decl) if c.get("kind") == "CompoundStmt"), None)
    if body_node is None:
        raise UnsupportedConstruct(f"{name}: no function body")
    lams: list[dict] = []
    _lambdas(body_node, lams)
    if not 1 <= parallel_for <= len(lams):
        raise UnsupportedConstruct(
            f"{name}: ParallelFor lambda {parallel_for} requested, but the function "
            f"has {len(lams)} lambda(s)")
    lam = lams[parallel_for - 1]
    rec = next((c for c in _inner(lam) if c.get("kind") == "CXXRecordDecl"), None)
    op = next((c for c in _inner(rec) if c.get("kind") == "CXXMethodDecl"
               and c.get("name") == "operator()"), None) if rec else None
    if op is None:
        raise UnsupportedConstruct(f"{name}: lambda without an operator()")
    idx_names = [p.get("name") for p in _inner(op) if p.get("kind") == "ParmVarDecl"
                 and p.get("type", {}).get("qualType") == "int"]
    named = tuple(n for n in idx_names if n)
    if named != tuple(columns):
        raise UnsupportedConstruct(
            f"{name}: the lambda's index parameters {named} do not spell the "
            f"declared columns {tuple(columns)}")
    lbody = next((c for c in _inner(lam) if c.get("kind") == "CompoundStmt"), None)
    if lbody is None:
        raise UnsupportedConstruct(f"{name}: lambda without a body")
    ctx = _ColumnCtx(assume)
    locals_: list[Param] = []
    stmts = tuple(_extract_stmts(lbody, locals_, column=ctx))
    # Captured function-scope locals: loop bounds, or `const Real` scalars
    # declared at the function's top level from an expression over the
    # parameters (`const Real Idt = 1.0_rt / dt;`) — the C++ hoists what the
    # Fortran computes before its loops. Those the lambda reads (directly or
    # through another such local) are prepended to the body, in declaration
    # order, as the Fortran's own pre-loop assignments are. A non-const
    # captured Real refuses: its value at capture is not its declaration.
    prologue: dict[str, tuple[Param, Stmt]] = {}
    nonconst: set[str] = set()
    for c in _inner(body_node):
        if c.get("kind") != "DeclStmt":
            continue
        for vd in _inner(c):
            qual = vd.get("type", {}).get("qualType")
            if vd.get("kind") != "VarDecl" or vd.get("name") is None:
                continue
            if qual in ("const Real", "const double") and vd.get("init") == "c":
                scratch: list[Param] = []
                init = _extract_vardecl(vd, scratch)
                prologue[vd["name"]] = (scratch[0], init)
            elif qual in _REAL_LOCAL_TYPES:
                nonconst.add(vd["name"])
    from groundline.kir import _names_in_stmt
    used: set[str] = set()
    for s in stmts:
        _names_in_stmt(s, used)
    needed: set[str] = set()
    for pname in reversed(list(prologue)):          # later decls may read earlier ones
        if pname in used or pname in needed:
            needed.add(pname)
            _names_in_stmt(prologue[pname][1], needed)
    hoisted = [prologue[p] for p in prologue if p in needed]
    bad = sorted((used | needed) & nonconst - set(prologue))
    if bad:
        raise UnsupportedConstruct(
            f"{name}: the lambda captures non-const function-scope real(s) "
            f"{bad} — only `const Real` prologue locals are hoisted into the model")
    locals_ = [p for p, _ in hoisted] + locals_
    stmts = tuple(s for _, s in hoisted) + stmts
    used = set()
    for s in stmts:
        _names_in_stmt(s, used)
    known = {p.name for p in params} | {l.name for l in locals_} | set(named) \
        | ctx.loop_vars | ctx.bounds
    unknown = sorted(used - known)
    if unknown:
        raise UnsupportedConstruct(
            f"{name}: the lambda references {unknown}, which are neither "
            f"parameters, lambda-body locals, column indices, loop variables, "
            f"loop bounds, nor const Real prologue locals")
    # Loop variables and column indices are integer locals of the raw kernel
    # (the column pass consumes them); bounds are dropped.
    locals_ += [Param(k, "integer", None, 0) for k in sorted(ctx.loop_vars | set(named))]
    return Kernel(name, tuple(params), tuple(locals_), stmts)


def extract_kernel(source: Path, function: str, *, clang: str = "clang++",
                   include_dirs: Sequence[str] = ()) -> Kernel:
    """Extract ``function`` from the C++ ``source`` (header or TU) via clang."""
    return extract_kernel_from_decl(
        load_function(source, function, clang=clang, include_dirs=include_dirs))


# --------------------------------------------------------------------------- #
# The seam object (KernelFrontend)
# --------------------------------------------------------------------------- #

class ClangKernelFrontend:
    """The :class:`~groundline.frontend.kernel_base.KernelFrontend` for clang
    JSON ASTs. The clang invocation config (compiler, include dirs) travels in
    the spec — part of the kernel's address, not function kwargs. The
    module-level :func:`extract_kernel` remains the implementation and stays
    importable for tests that pin it directly."""

    def extract(self, spec: CppKernelSpec) -> Kernel:
        if spec.parallel_for is not None:
            decl = load_function(spec.source, spec.function, clang=spec.compiler,
                                 include_dirs=spec.include_dirs)
            return extract_column_kernel_from_decl(
                decl, spec.parallel_for, spec.columns, dict(spec.assume))
        return extract_kernel(spec.source, spec.function, clang=spec.compiler,
                              include_dirs=spec.include_dirs)
