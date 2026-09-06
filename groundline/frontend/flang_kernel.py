"""Kernel-IR frontend: extract one subroutine or function — or one addressed
loop nest of a subroutine (:func:`extract_loop_kernel`) — from a with-sema
flang parse-tree dump into the kernel IR (``groundline/kir.py``). A function
kernel's ``result(name)`` variable becomes its single output (a parameter of
intent ``result``; see ``kir.functionalize``). The dump is either
pre-generated (captured inside a real build, kept with provenance) or
produced on demand by running flang on a standalone source file
(:func:`dump_parse_tree`) — the mirror of how the clang frontend invokes
clang.

Below the seam (DESIGN §2.3): everything flang-dump-specific about *kernel
bodies* lives here, exactly as ``flang_dump.py`` owns the dump's *relational*
face. Trusted-base rule (VISION D6): deterministic; any construct outside the
supported subset raises :class:`~groundline.kir.UnsupportedConstruct` — the
extractor refuses rather than guesses.

The dump is parsed into a literal node tree first (one node per ``A -> B -> C``
chain element, children attached by ``|``-depth), then walked structurally.
Expression structure is taken from the *tree*, never re-parsed from the unparse
annotations.
"""

from __future__ import annotations

import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Optional

from groundline.kir import (
    ArrayRef, Assign, BinOp, Call, CallStmt, Cmp, ComponentRef, Do, DoConcurrent,
    Expr, If, IntLit, Kernel, Neg, Param, Paren, RealLit, Slice, Stmt,
    UnsupportedConstruct, Var, _names_in_stmt as _kir_names_in_stmt,
)
from groundline.frontend._flang_text import level
from groundline.frontend.kernel_base import FortranKernelSpec


# --------------------------------------------------------------------------- #
# flang invocation (source mode: generate the with-sema dump on demand)
# --------------------------------------------------------------------------- #

DUMP_FLAGS = ("-fc1", "-fdebug-dump-parse-tree")


def flang_version(flang: str = "flang") -> str:
    """First line of ``flang --version`` — stamped into generated provenance."""
    out = subprocess.run([flang, "--version"], capture_output=True, text=True,
                         check=True)
    return out.stdout.splitlines()[0].strip()


def dump_parse_tree(source: Path, *, flang: str = "flang") -> str:
    """Run flang on a standalone source file and return its with-sema
    parse-tree dump — the same text a pre-generated ``*_ptree`` file holds.

    Runs in a temporary directory so flang's ``.mod`` side products never
    land next to the source. A file that USEs modules whose ``.mod`` files
    are not built fails here: such kernels are dumped inside their real
    build and addressed as pre-generated dumps instead (``dump =`` in the
    manifest).
    """
    source = Path(source).resolve()
    with tempfile.TemporaryDirectory() as td:
        proc = subprocess.run([flang, *DUMP_FLAGS, str(source)],
                              capture_output=True, text=True, cwd=td)
    if proc.returncode != 0:
        raise RuntimeError(
            f"flang failed ({proc.returncode}): "
            f"{flang} {' '.join(DUMP_FLAGS)} {source}\n{proc.stderr}")
    return proc.stdout


# --------------------------------------------------------------------------- #
# Generic dump-tree parsing
# --------------------------------------------------------------------------- #

@dataclass
class Node:
    name: str
    payload: Optional[str] = None      # the 'value' in  Name = 'value'
    children: list["Node"] = field(default_factory=list)

    def child(self, name: str) -> "Node":
        for c in self.children:
            if c.name == name:
                return c
        raise UnsupportedConstruct(f"expected child '{name}' under '{self.name}', "
                                   f"have {[c.name for c in self.children]}")

    def children_named(self, name: str) -> list["Node"]:
        return [c for c in self.children if c.name == name]

    def only_child(self) -> "Node":
        if len(self.children) != 1:
            raise UnsupportedConstruct(
                f"expected exactly one child under '{self.name}', "
                f"have {[c.name for c in self.children]}")
        return self.children[0]


def _split_chain(content: str) -> list[Node]:
    """Turn one dump line's content into a chain of Nodes (parent → … → leaf).

    ``Foo -> Bar -> Name = 'x'`` becomes Foo ▸ Bar ▸ Name(payload='x'). The
    payload split happens at the first `` = '`` so unparse text containing
    ``->`` can't confuse the chain split.
    """
    payload = None
    head, sep, tail = content.partition(" = '")
    if sep:
        payload = tail[:-1] if tail.endswith("'") else tail
        content = head
    elif content.endswith(" = "):        # e.g.  Kind =
        content = content[:-3]
    if content.endswith(" ->"):          # e.g.  IntegerTypeSpec ->  (empty tail)
        content = content[:-3]
    parts = [p for p in content.split(" -> ") if p]
    if payload is None and parts and " = " in parts[-1]:
        # unquoted payload on the leaf, e.g.  Intent = In  /  Kind = ModuleProcedure
        name, _, payload = parts[-1].partition(" = ")
        parts[-1] = name
    chain = [Node(p) for p in parts]
    if payload is not None:
        chain[-1].payload = payload
    for a, b in zip(chain, chain[1:]):
        a.children.append(b)
    return chain


def parse_dump_lines(lines: Iterable[str]) -> Node:
    """Build the node tree of an entire dump (or any depth-consistent slice)."""
    root = Node("<root>")
    # stack[d] = the node new depth-d lines' chains attach under
    stack: list[Node] = [root]
    for raw in lines:
        line = raw.rstrip("\n")
        if not line or line.startswith("="):
            continue
        depth = level(line)
        content = line[2 * depth:] if depth else line
        if not content.strip():
            continue
        chain = _split_chain(content.strip())
        parent = stack[depth] if depth < len(stack) else stack[-1]
        parent.children.append(chain[0])
        del stack[depth + 1:]
        stack.append(chain[-1])
    return root


# Procedure kinds the frontend extracts, and the statement node that heads each.
_PROCEDURE_STMT = {"SubroutineSubprogram": "SubroutineStmt",
                   "FunctionSubprogram": "FunctionStmt"}

# Prefix keywords (dump: ``PrefixSpec -> <keyword>``) that constrain how a
# procedure may be used or called — pure, elemental, recursive, … — without
# changing what its body computes; the extractor may read past them. A
# ``DeclarationTypeSpec`` prefix (``real function f(x)``) is NOT a keyword: it
# declares the result's type outside the specification part, and dropping it
# would lose that declaration — so it refuses.
_PREFIX_KEYWORDS = {"Pure", "Elemental", "Impure", "Recursive", "Non_Recursive",
                    "Module"}


def find_procedure(root: Node, name: str) -> Node:
    """Locate the ``SubroutineSubprogram`` or ``FunctionSubprogram`` whose
    heading statement names ``name`` (its first ``Name`` child, after any
    prefix)."""
    hits: list[Node] = []

    def walk(n: Node) -> None:
        stmt_kind = _PROCEDURE_STMT.get(n.name)
        if stmt_kind is not None:
            stmt = n.child(stmt_kind)
            names = stmt.children_named("Name")
            if names and names[0].payload == name:
                hits.append(n)
                return
        for c in n.children:
            walk(c)

    walk(root)
    if len(hits) != 1:
        raise UnsupportedConstruct(
            f"subroutine or function '{name}': found {len(hits)} definitions")
    return hits[0]


@dataclass(frozen=True)
class _Signature:
    """A procedure heading: its name, dummy-argument names in source order,
    and — for a function — the result variable named by ``result(name)``."""
    name: str
    args: tuple[str, ...]
    result: Optional[str]


def _check_prefix(stmt: Node) -> None:
    for ps in stmt.children_named("PrefixSpec"):
        kid = ps.only_child()
        if kid.name not in _PREFIX_KEYWORDS:
            raise UnsupportedConstruct(
                f"prefix '{kid.name}' on '{stmt.name}' (only the keyword "
                f"prefixes {sorted(_PREFIX_KEYWORDS)} are understood — a type "
                f"prefix would declare the function result outside the "
                f"specification part)")


def _signature(sub: Node) -> _Signature:
    """Read a procedure's heading. A ``SubroutineStmt`` lists its dummies as
    ``DummyArg -> Name`` children; a ``FunctionStmt`` lists them as bare
    ``Name`` children after the function's own name, and names its result
    variable under ``Suffix -> Name``. A function *without* a ``result``
    clause — whose function name doubles as the result variable — refuses:
    that is a different declaration story, unsupported until a kernel needs
    it."""
    if sub.name == "SubroutineSubprogram":
        stmt = sub.child("SubroutineStmt")
        _check_prefix(stmt)
        name = stmt.children_named("Name")[0].payload
        args = tuple(d.child("Name").payload for d in stmt.children_named("DummyArg"))
        return _Signature(name, args, None)
    stmt = sub.child("FunctionStmt")
    _check_prefix(stmt)
    names = [n.payload for n in stmt.children_named("Name")]
    suffixes = stmt.children_named("Suffix")
    if not suffixes:
        raise UnsupportedConstruct(
            f"function '{names[0]}' has no result(name) clause — the function "
            f"name itself would be the result variable (unsupported)")
    if len(suffixes) != 1:
        raise UnsupportedConstruct(f"function '{names[0]}': several suffixes")
    res = suffixes[0].only_child()
    if res.name != "Name":
        raise UnsupportedConstruct(
            f"function '{names[0]}': suffix '{res.name}' (only result(name) "
            f"is supported)")
    return _Signature(names[0], tuple(names[1:]), res.payload)


# --------------------------------------------------------------------------- #
# Expression extraction
# --------------------------------------------------------------------------- #

_BINOPS = {"Add": "add", "Subtract": "sub", "Multiply": "mul",
           "Divide": "div", "Power": "pow"}
_CMPS = {"LT": "lt", "LE": "le", "GT": "gt", "GE": "ge", "EQ": "eq", "NE": "ne"}
_INTRINSICS = {"abs", "min", "max", "sqrt"}


def extract_expr(node: Node) -> Expr:
    """``node`` is an ``Expr`` node (with-sema: payload = unparse text)."""
    inner = node.only_child()
    return _extract_expr_inner(inner)


def _extract_expr_inner(n: Node) -> Expr:
    if n.name in ("Scalar", "Integer", "Logical"):     # transparent wrappers
        return _extract_expr_inner(n.only_child())
    if n.name == "Expr":
        return extract_expr(n)
    if n.name == "LiteralConstant":
        lit = n.only_child()
        if lit.name == "RealLiteralConstant":
            return RealLit(lit.child("Real").payload)
        if lit.name == "IntLiteralConstant":
            return IntLit(lit.payload)
        raise UnsupportedConstruct(f"literal kind '{lit.name}'")
    if n.name == "Designator":
        return _extract_dataref(n.child("DataRef"))
    if n.name == "Parentheses":
        return Paren(extract_expr(n.child("Expr")))
    if n.name == "Negate":
        return Neg(extract_expr(n.child("Expr")))
    if n.name in _BINOPS:
        lhs, rhs = n.children_named("Expr")
        return BinOp(_BINOPS[n.name], extract_expr(lhs), extract_expr(rhs))
    if n.name in _CMPS:
        lhs, rhs = n.children_named("Expr")
        return Cmp(_CMPS[n.name], extract_expr(lhs), extract_expr(rhs))
    if n.name == "FunctionReference":
        call = n.child("Call")
        fname = call.child("ProcedureDesignator").child("Name").payload
        if fname not in _INTRINSICS:
            raise UnsupportedConstruct(f"call to '{fname}' (not a supported intrinsic)")
        args = tuple(extract_expr(spec.child("ActualArg").child("Expr"))
                     for spec in call.children_named("ActualArgSpec"))
        return Call(fname, args)
    raise UnsupportedConstruct(f"expression node '{n.name}'")


def _extract_dataref(n: Node) -> Expr:
    inner = n.only_child()
    if inner.name == "Name":
        return Var(inner.payload)
    if inner.name == "StructureComponent":
        return _extract_component(inner, ())
    if inner.name == "ArrayElement":
        subs = tuple(_extract_subscript(s)
                     for s in inner.children_named("SectionSubscript"))
        base = inner.child("DataRef").only_child()
        if base.name == "Name":
            return ArrayRef(base.payload, subs)
        if base.name == "StructureComponent":
            return _extract_component(base, subs)
        raise UnsupportedConstruct(f"array-element base '{base.name}'")
    raise UnsupportedConstruct(f"data reference '{inner.name}'")


def _extract_subscript(s: Node) -> Expr:
    """One ``SectionSubscript``: an integer expression, or a bare ``:``
    (``SubscriptTriplet`` with no bounds — a whole-dimension section, kept as
    :class:`~groundline.kir.Slice` for the column pass's whole-array
    assignment; a triplet with bounds or a stride refuses)."""
    if s.children and s.children[0].name == "Integer":
        return extract_expr(s.children[0].child("Expr"))
    if s.children and s.children[0].name == "SubscriptTriplet":
        trip = s.children[0]
        if trip.children:
            raise UnsupportedConstruct(
                "array section with bounds or a stride (only a bare ':' is modeled)")
        return Slice()
    return extract_expr(_descend_subscript(s))


def _extract_component(sc: Node, subscripts: tuple[Expr, ...]) -> ComponentRef:
    """``base%comp`` (dump: ``DataRef -> StructureComponent`` holding the base
    ``DataRef`` and the component ``Name``). Single level only — a chained
    ``a%b%c`` has a StructureComponent base and refuses."""
    base = sc.child("DataRef").only_child()
    if base.name != "Name":
        raise UnsupportedConstruct(
            f"component base '{base.name}' (only single-level base%comp is supported)")
    return ComponentRef(base.payload, sc.child("Name").payload, subscripts)


def _descend_subscript(s: Node) -> Node:
    n = s
    while n.name != "Expr":
        n = n.only_child()
    return n


# --------------------------------------------------------------------------- #
# Statement extraction
# --------------------------------------------------------------------------- #

def extract_block(block: Node) -> tuple[Stmt, ...]:
    stmts: list[Stmt] = []
    for epc in block.children_named("ExecutionPartConstruct"):
        stmts.append(_extract_construct(epc.child("ExecutableConstruct")))
    return tuple(stmts)


def _extract_construct(ec: Node) -> Stmt:
    inner = ec.only_child()
    if inner.name == "ActionStmt":
        return _extract_action(inner)
    if inner.name == "IfConstruct":
        return _extract_if(inner)
    if inner.name == "DoConstruct":
        return _extract_do(inner)
    raise UnsupportedConstruct(f"executable construct '{inner.name}'")


def _extract_action(action: Node) -> Stmt:
    stmt = action.only_child()
    if stmt.name == "AssignmentStmt":
        var = stmt.child("Variable")
        target = _extract_dataref(var.child("Designator").child("DataRef"))
        value = extract_expr(stmt.child("Expr"))
        return Assign(target, value)
    if stmt.name == "IfStmt":
        # Logical IF statement (R1139): `if (cond) action` — the dump nests the
        # guarded action as a child ActionStmt of the IfStmt, alongside the
        # condition. Extracted as a single-branch If with no orelse.
        cond = extract_expr(stmt.child("Scalar").child("Logical").child("Expr"))
        return If(((cond, (_extract_action(stmt.child("ActionStmt")),)),), ())
    if stmt.name == "CallStmt":
        # `call f(a, b(i,j,k), …)` — the actuals in source order (keyword
        # actuals refuse: the column pass matches positionally). Resolved
        # against a banked callee by the column pass; refused elsewhere.
        call = stmt.child("Call")
        name = call.child("ProcedureDesignator").child("Name").payload
        args = []
        for spec in call.children_named("ActualArgSpec"):
            if spec.children_named("Keyword"):
                raise UnsupportedConstruct(
                    f"call to '{name}' with a keyword actual (positional only)")
            args.append(extract_expr(spec.child("ActualArg").child("Expr")))
        return CallStmt(name, tuple(args))
    raise UnsupportedConstruct(f"action statement '{stmt.name}'")


def _extract_if(n: Node) -> If:
    branches: list[tuple[Expr, tuple[Stmt, ...]]] = []
    orelse: tuple[Stmt, ...] = ()
    kids = n.children
    i = 0
    while i < len(kids):
        kid = kids[i]
        if kid.name == "IfThenStmt":
            cond = extract_expr(kid.child("Scalar").child("Logical").child("Expr"))
            body = extract_block(kids[i + 1])       # the following Block
            branches.append((cond, body))
            i += 2
        elif kid.name == "ElseIfBlock":             # wraps ElseIfStmt + Block
            stmt = kid.child("ElseIfStmt")
            cond = extract_expr(stmt.child("Scalar").child("Logical").child("Expr"))
            branches.append((cond, extract_block(kid.child("Block"))))
            i += 1
        elif kid.name == "ElseBlock":               # wraps ElseStmt + Block
            orelse = extract_block(kid.child("Block"))
            i += 1
        elif kid.name in ("EndIfStmt",):
            i += 1
        else:
            raise UnsupportedConstruct(f"IfConstruct child '{kid.name}'")
    return If(tuple(branches), orelse)


def _extract_do(n: Node) -> Stmt:
    do_stmt = n.child("NonLabelDoStmt")
    loop = do_stmt.child("LoopControl").only_child()
    if loop.name == "Concurrent":
        # `Concurrent` holds the header and any locality specs
        # (`local(x)`, `shared(y)`, `reduce(...)`); none is modeled yet — a
        # `local` would be harmless (the model binds locals per iteration
        # anyway) but is refused until a kernel carries one.
        extra = [c.name for c in loop.children if c.name != "ConcurrentHeader"]
        if extra:
            raise UnsupportedConstruct(
                f"do-concurrent with locality specs {extra} is unsupported")
        header = loop.child("ConcurrentHeader")
        controls = []
        mask = None
        for kid in header.children:
            if kid.name == "ConcurrentControl":
                idx = kid.child("Name").payload
                bounds = [extract_expr(_descend_subscript(sc))
                          for sc in kid.children_named("Scalar")]
                if len(bounds) != 2:
                    raise UnsupportedConstruct("do-concurrent with a stride is unsupported")
                controls.append((idx, bounds[0], bounds[1]))
            elif kid.name == "Scalar" and mask is None:
                # The scalar-mask-expr (dump: `Scalar -> Logical -> Expr`,
                # a sibling of the controls).
                mask = extract_expr(kid.child("Logical").child("Expr"))
            else:
                raise UnsupportedConstruct(f"ConcurrentHeader child '{kid.name}'")
        body = extract_block(n.child("Block"))
        return DoConcurrent(tuple(controls), body, mask)
    if loop.name == "LoopBounds":
        # Plain do (R1119): the dump lists the index and both bounds as
        # sibling Scalar nodes — `Scalar -> Name` for the loop variable,
        # then `Scalar -> Expr` for lower and upper (a third one is a stride).
        scalars = loop.children_named("Scalar")
        if not scalars or scalars[0].only_child().name != "Name":
            raise UnsupportedConstruct("LoopBounds without a leading index Name")
        idx = scalars[0].only_child().payload
        bounds = [extract_expr(_descend_subscript(sc)) for sc in scalars[1:]]
        if len(bounds) != 2:
            raise UnsupportedConstruct("plain do with a stride is unsupported")
        body = extract_block(n.child("Block"))
        return Do((idx, bounds[0], bounds[1]), body)
    raise UnsupportedConstruct(f"loop control '{loop.name}'")


# --------------------------------------------------------------------------- #
# Declarations + kernel assembly
# --------------------------------------------------------------------------- #

def _parse_type_decl(tds: Node) -> list[Param]:
    """One ``TypeDeclarationStmt`` → the Params it declares (refusing outside
    the subset)."""
    dts = tds.child("DeclarationTypeSpec").only_child()
    if dts.name == "IntrinsicTypeSpec":
        base = dts.only_child().name
        type_ = {"Real": "real", "IntegerTypeSpec": "integer",
                 "Logical": "logical"}.get(base)
        if type_ is None:
            raise UnsupportedConstruct(f"intrinsic type '{base}'")
    elif dts.name == "Type":
        type_ = "derived:" + dts.child("DerivedTypeSpec").child("Name").payload
    else:
        raise UnsupportedConstruct(f"type spec '{dts.name}'")
    intent = None
    rank = 0
    for attr in tds.children_named("AttrSpec"):
        kid = attr.only_child()
        if kid.name == "IntentSpec":
            intent = kid.child("Intent").payload.lower()
        elif kid.name == "ArraySpec":
            rank = len(kid.children_named("ExplicitShapeSpec"))
        elif kid.name == "Optional":
            # Presence is the caller's precondition: the body is modeled as a
            # function of the dummy's value whenever it runs, and a body that
            # could branch on presence — a present() call — refuses anyway.
            pass
        else:
            raise UnsupportedConstruct(f"attribute '{kid.name}'")
    # An array shape may sit on the entity (`u(0:n, m, nz)`) instead of a
    # `dimension` attribute; either way the rank is the number of extents.
    out = []
    for ent in tds.children_named("EntityDecl"):
        spec = ent.children_named("ArraySpec")
        r = len(spec[0].children_named("ExplicitShapeSpec")) if spec else rank
        out.append(Param(ent.child("Name").payload, type_, intent, r))
    return out


def _type_decls(spec: Node):
    for dc in spec.children_named("DeclarationConstruct"):
        try:
            yield dc.child("SpecificationConstruct").child("TypeDeclarationStmt")
        except UnsupportedConstruct:
            continue


def _extract_decls(spec: Node) -> list[Param]:
    decls: list[Param] = []
    for tds in _type_decls(spec):
        decls.extend(_parse_type_decl(tds))
    return decls


def _extract_decls_tolerant(spec: Node) -> tuple[list[Param], dict[str, str]]:
    """Like :func:`_extract_decls`, but a declaration outside the subset does
    not abort the extraction: its entity names are recorded as *poisoned*
    (name → reason), and the caller refuses iff the loop nest actually
    references one of them. If a failing declaration's entity names cannot
    even be harvested, the extraction refuses outright — better a spurious
    refusal than a silently missing declaration."""
    decls: list[Param] = []
    poisoned: dict[str, str] = {}
    for tds in _type_decls(spec):
        try:
            decls.extend(_parse_type_decl(tds))
        except UnsupportedConstruct as e:
            names = [ent.child("Name").payload
                     for ent in tds.children_named("EntityDecl")]
            if not names:
                raise
            for nm in names:
                poisoned[nm] = str(e)
    return decls, poisoned


def extract_kernel(dump_path: Path, subroutine: str) -> Kernel:
    """Extract ``subroutine`` from the with-sema dump at ``dump_path``."""
    with open(dump_path) as f:
        return _kernel_from_root(parse_dump_lines(f), subroutine)


def _kernel_from_root(root: Node, subroutine: str) -> Kernel:
    sub = find_procedure(root, subroutine)
    sig = _signature(sub)
    decls = _extract_decls(sub.child("SpecificationPart"))
    by_name = {d.name: d for d in decls}
    missing = [a for a in sig.args if a not in by_name]
    if missing:
        raise UnsupportedConstruct(f"{subroutine}: undeclared dummy args {missing}")
    params = [by_name[a] for a in sig.args]
    bound = set(sig.args)
    if sig.result is not None:
        # A function: its result variable is the single output. It is
        # declared like a local (no intent) in the specification part and
        # becomes a parameter of intent 'result' — appended after the dummies.
        res = by_name.get(sig.result)
        if res is None:
            raise UnsupportedConstruct(
                f"{subroutine}: result variable '{sig.result}' is not declared "
                f"in the specification part")
        mutated = [p.name for p in params if p.intent in ("inout", "out")]
        if mutated:
            raise UnsupportedConstruct(
                f"{subroutine}: a function with intent(inout)/intent(out) "
                f"dummy arguments {mutated} — two output conventions (a result "
                f"and mutated arguments) in one procedure")
        params.append(Param(res.name, res.type, "result", res.rank))
        bound.add(sig.result)
    locals_ = tuple(d for d in decls if d.name not in bound)
    body = extract_block(sub.child("ExecutionPart").child("Block"))
    # A derived-type dummy the body never references (grid/config structs
    # passed along by convention) is dropped, as pointize drops unused params
    # in loop mode; a *referenced* one survives and refuses at print.
    used: set[str] = set()
    for stmt in body:
        _names_in_stmt(stmt, used)
    params = [p for p in params
              if not (p.type.startswith("derived:") and p.name not in used)]
    return Kernel(subroutine, tuple(params), locals_, body)


# --------------------------------------------------------------------------- #
# Inline-loop addressing (rule B): extract loop nest #N of a subroutine
# --------------------------------------------------------------------------- #

def _collect_do_nests(n: Node) -> list[Node]:
    """All outermost ``DoConstruct`` nodes under ``n``, in source order (the
    dump's document order). The walk descends into every other construct —
    IF branches included — but never into a ``DoConstruct``: its inner do
    levels belong to the same nest, so each nest counts exactly once."""
    out: list[Node] = []
    for c in n.children:
        if c.name == "DoConstruct":
            out.append(c)
        else:
            out.extend(_collect_do_nests(c))
    return out


def _names_in_expr(e: Expr, out: set[str]) -> None:
    if isinstance(e, Var):
        out.add(e.name)
    elif isinstance(e, ArrayRef):
        out.add(e.name)
        for s in e.subscripts:
            _names_in_expr(s, out)
    elif isinstance(e, ComponentRef):
        out.add(e.base)          # the component name is not a variable
        for s in e.subscripts:
            _names_in_expr(s, out)
    elif isinstance(e, (Paren, Neg)):
        _names_in_expr(e.inner, out)
    elif isinstance(e, (BinOp, Cmp)):
        _names_in_expr(e.lhs, out)
        _names_in_expr(e.rhs, out)
    elif isinstance(e, Call):
        for a in e.args:
            _names_in_expr(a, out)


def _names_in_stmt(s: Stmt, out: set[str]) -> None:
    if isinstance(s, Assign):
        _names_in_expr(s.target, out)
        _names_in_expr(s.value, out)
    elif isinstance(s, If):
        for (c, body) in s.branches:
            _names_in_expr(c, out)
            for x in body:
                _names_in_stmt(x, out)
        for x in s.orelse:
            _names_in_stmt(x, out)
    elif isinstance(s, DoConcurrent):
        for (idx, lo, hi) in s.controls:
            out.add(idx)
            _names_in_expr(lo, out)
            _names_in_expr(hi, out)
        for x in s.body:
            _names_in_stmt(x, out)
    elif isinstance(s, Do):
        idx, lo, hi = s.control
        out.add(idx)
        _names_in_expr(lo, out)
        _names_in_expr(hi, out)
        for x in s.body:
            _names_in_stmt(x, out)


def extract_loop_kernel(dump_path: Path, subroutine: str, nest: int,
                        name: str) -> Kernel:
    """Extract loop nest #``nest`` (1-based, source order) of ``subroutine``
    from the with-sema dump, as a kernel named ``name``.

    Inline-loop addressing: the dump carries no line numbers, so the
    deterministic address of a loop living inside a larger subroutine is its
    source-order ordinal among the subroutine's outermost do-constructs —
    counting both do-concurrent and plain-DO nests (see
    :func:`_collect_do_nests`). The enclosing subroutine's SpecificationPart
    supplies the declarations, extracted tolerantly: a declaration outside
    the subset only poisons its own names, and extraction refuses iff the
    nest references a poisoned (or undeclared) name. The kernel's name is
    caller-supplied — an inline loop has no name of its own; the driver
    records the pairing. The whole-subroutine mode (:func:`extract_kernel`)
    is unchanged.
    """
    with open(dump_path) as f:
        return _loop_kernel_from_root(parse_dump_lines(f), subroutine, nest,
                                      name)


def _loop_kernel_from_root(root: Node, subroutine: str, nest: int,
                           name: str) -> Kernel:
    sub = find_procedure(root, subroutine)
    nests = _collect_do_nests(sub.child("ExecutionPart"))
    if not 1 <= nest <= len(nests):
        raise UnsupportedConstruct(
            f"{subroutine}: loop nest {nest} requested, but the subroutine "
            f"has {len(nests)} do-construct nest(s)")
    loop = _extract_do(nests[nest - 1])

    arg_order = _signature(sub).args
    decls, poisoned = _extract_decls_tolerant(sub.child("SpecificationPart"))
    by_name = {d.name: d for d in decls}

    used: set[str] = set()
    _names_in_stmt(loop, used)
    for n in sorted(used - by_name.keys()):
        reason = poisoned.get(n, "no declaration found")
        raise UnsupportedConstruct(
            f"{subroutine}: loop nest {nest} references '{n}' — {reason}")
    params = tuple(by_name[a] for a in arg_order if a in used)
    locals_ = tuple(d for d in decls
                    if d.name in used and d.name not in set(arg_order))
    return Kernel(name, params, locals_, (loop,))


# --------------------------------------------------------------------------- #
# Column-kernel mode: pruning under declared hypotheses, then extraction
# --------------------------------------------------------------------------- #

def _operative(n: Node) -> Node:
    """Descend the transparent wrappers of a condition (Scalar/Logical/Expr/
    Parentheses) to the node that decides it."""
    while n.name in ("Scalar", "Logical", "Expr", "Parentheses") and len(n.children) == 1:
        n = n.children[0]
    return n


def _flag_name(n: Node) -> Optional[str]:
    """The variable a designator names — `x` or the base of `x(...)` — else None."""
    n = _operative(n)
    if n.name != "Designator":
        return None
    dr = n.child("DataRef").only_child()
    if dr.name == "Name":
        return dr.payload
    if dr.name == "ArrayElement":
        base = dr.child("DataRef").only_child()
        return base.payload if base.name == "Name" else None
    return None


def _decided_false(cond: Node, assume: dict[str, bool]) -> bool:
    """A condition the hypotheses decide false: an assumed-false flag (or an
    element of an assumed-false flag array), or a conjunction with such an
    operand. Nothing else is decided — a condition the pass cannot decide is
    left for extraction to model (or refuse)."""
    n = _operative(cond)
    name = _flag_name(n)
    if name is not None:
        return assume.get(name) is False
    if n.name == "AND":
        return any(_decided_false(c, assume) for c in n.children_named("Expr"))
    return False


def _assignment_target(stmt: Node) -> Optional[str]:
    return _flag_name(stmt.child("Variable").child("Designator"))


def _prune_block(block: Node, assume: dict[str, bool], ignore: set[str],
                 dead: set[str]) -> None:
    kept = []
    for epc in block.children:
        if epc.name != "ExecutionPartConstruct":
            kept.append(epc)
            continue
        if not _prune_construct(epc.only_child().only_child(), assume, ignore, dead):
            kept.append(epc)
    block.children = kept


def _prune_construct(inner: Node, assume: dict[str, bool], ignore: set[str],
                     dead: set[str]) -> bool:
    """True iff the construct is to be dropped. Drops: calls declared
    ignorable; assignments to an assumed flag or to a dead integer local; an
    IF whose condition the hypotheses decide false (no elseif/else allowed);
    and, after pruning inside, any IF or DO left with nothing to do — its
    condition is then never modeled, which is sound because Fortran
    conditions have no side effects."""
    if inner.name == "ActionStmt":
        stmt = inner.only_child()
        if stmt.name == "CallStmt":
            name = stmt.child("Call").child("ProcedureDesignator").child("Name").payload
            return name in ignore
        if stmt.name == "AssignmentStmt":
            target = _assignment_target(stmt)
            return target is not None and (target in assume or target in dead)
        if stmt.name == "IfStmt":
            if _decided_false(stmt.child("Scalar").child("Logical").child("Expr"), assume):
                return True
            return _prune_construct(stmt.child("ActionStmt"), assume, ignore, dead)
        return False
    if inner.name == "IfConstruct":
        kids = inner.children
        cond = kids[0].child("Scalar").child("Logical").child("Expr")
        has_else = any(k.name in ("ElseIfBlock", "ElseBlock") for k in kids)
        if _decided_false(cond, assume):
            if has_else:
                raise UnsupportedConstruct(
                    "an IF construct decided false by a hypothesis, but carrying "
                    "elseif/else branches — reducing it is not yet supported")
            return True
        empty = True
        for k in kids:
            blk = k if k.name == "Block" else (k.child("Block") if k.name in ("ElseIfBlock", "ElseBlock") else None)
            if blk is not None:
                _prune_block(blk, assume, ignore, dead)
                empty = empty and not blk.children
        return empty
    if inner.name == "DoConstruct":
        blk = inner.child("Block")
        _prune_block(blk, assume, ignore, dead)
        return not blk.children
    return False


def _dead_integer_locals(sub: Node, decls: list[Param], arg_order: tuple[str, ...]) -> set[str]:
    """Integer locals whose every occurrence is an assignment target or a loop
    bound — pure address bookkeeping (`ish = LB%ish`, `nz = GV%ke`). Their
    assignments carry nothing the model reads, so the pruner drops them."""
    candidates = {d.name for d in decls
                  if d.type == "integer" and d.name not in arg_order}
    reads: set[str] = set()

    def walk(n: Node, in_bounds: bool) -> None:
        if n.name == "LoopControl":
            in_bounds = True
        if n.name == "Variable":
            # the target's base name is a write, its subscripts are reads
            des = n.child("Designator").child("DataRef").only_child()
            if des.name == "ArrayElement":
                for sub_ in des.children_named("SectionSubscript"):
                    walk(sub_, in_bounds)
            return
        if n.name == "StructureComponent":
            # `lb_in%ish`: the base is a read, the component name is not a variable
            walk(n.child("DataRef"), in_bounds)
            return
        if n.name == "Name" and n.payload and not in_bounds:
            reads.add(n.payload)
        for c in n.children:
            walk(c, in_bounds)

    walk(sub.child("ExecutionPart"), False)
    return {c for c in candidates if c not in reads}


def _column_kernel_from_root(root: Node, subroutine: str, *, assume: dict[str, bool],
                             ignore_calls: set[str]) -> Kernel:
    """Column mode: the whole subroutine, declarations inherited tolerantly (as
    in inline-loop mode), the body pruned under the manifest's hypotheses
    before any expression is extracted, then extracted with its loops intact
    for :func:`groundline.column.columnize`."""
    sub = find_procedure(root, subroutine)
    sig = _signature(sub)
    decls, poisoned = _extract_decls_tolerant(sub.child("SpecificationPart"))
    dead = _dead_integer_locals(sub, decls, sig.args)
    _prune_block(sub.child("ExecutionPart").child("Block"), assume, set(ignore_calls), dead)
    body = extract_block(sub.child("ExecutionPart").child("Block"))
    by_name = {d.name: d for d in decls}
    used: set[str] = set()
    for stmt in body:
        _kir_names_in_stmt(stmt, used)
    for n in sorted(used - by_name.keys()):
        reason = poisoned.get(n, "no declaration found")
        raise UnsupportedConstruct(f"{subroutine}: references '{n}' — {reason}")
    params = tuple(by_name[a] for a in sig.args if a in used)
    locals_ = tuple(d for d in decls if d.name in used and d.name not in set(sig.args))
    return Kernel(subroutine, params, locals_, body)


def procedure_dummies(root: Node, name: str) -> tuple[str, ...]:
    """The full dummy list of a procedure, in source order — what a caller's
    positional actuals are matched against (the callee's own extraction may
    have dropped some of these)."""
    return _signature(find_procedure(root, name)).args


# --------------------------------------------------------------------------- #
# The seam object (KernelFrontend)
# --------------------------------------------------------------------------- #

class FlangKernelFrontend:
    """The :class:`~groundline.frontend.kernel_base.KernelFrontend` for flang
    with-sema dumps: one deep method dispatching on the spec's input mode
    (a pre-generated dump vs a standalone source flang runs on now) and its
    addressing mode (whole subroutine vs rule-B inline loop). The
    module-level functions above remain the implementation — and stay
    importable for tests that pin them directly — but the spec path is the
    supported entry point."""

    def root(self, spec: FortranKernelSpec) -> Node:
        if spec.source is not None:
            text = dump_parse_tree(spec.source, flang=spec.compiler)
            return parse_dump_lines(text.splitlines())
        with open(spec.dump) as f:
            return parse_dump_lines(f)

    def extract(self, spec: FortranKernelSpec) -> Kernel:
        root = self.root(spec)
        return self.extract_from_root(root, spec)

    def extract_from_root(self, root: Node, spec: FortranKernelSpec) -> Kernel:
        if spec.columns:
            return _column_kernel_from_root(
                root, spec.subroutine, assume=dict(spec.assume),
                ignore_calls=set(spec.ignore_calls))
        if spec.nest is None:
            return _kernel_from_root(root, spec.subroutine)
        return _loop_kernel_from_root(root, spec.subroutine, spec.nest,
                                      spec.def_name)
