"""Lean printer: render a pointized, functionalized kernel as Lean 4.

The output models real arithmetic over ℝ (VISION D6) and mirrors the *source's
own* expression shapes: source parentheses are preserved (``Paren``), operator
spellings map one-to-one, and nothing is algebraically simplified — fidelity is
the printer's whole job; equivalence is the theorem prover's.

Trusted-base rule: deterministic, no I/O beyond the returned string, small
enough to audit line by line against ``kir.py``.
"""

from __future__ import annotations

from groundline.kir import (
    App, ArrayRef, BinOp, Call, Cmp, ComponentRef, Cond, Expr, Foldl, FunExpr,
    IfExpr, IntLit, Kernel, Lam, Let, Neg, Param, Paren, Proj, RealLit, Tuple_,
    UnsupportedConstruct, Var, functionalize,
)

# Lean types of the modeled parameter types: reals are ℝ (VISION D6);
# logical/bool inputs are Bool (a runtime truth value, decidable in `if`).
_LEAN_TYPE = {"real": "ℝ", "logical": "Bool", "real[k]": "κ → ℝ"}

# Precedence of an argument position: function application binds tightest, so
# an argument that is itself an application, an operator expression or a
# conditional must be parenthesized.
_ARG = 4
_INTRINSICS = ("abs", "min", "max")

# Operator spelling and precedence (higher binds tighter). Lean and Fortran
# agree on these levels for the supported subset.
_BIN = {"add": ("+", 1), "sub": ("-", 1), "mul": ("*", 2), "div": ("/", 2),
        "pow": ("^", 3)}
_CMP = {"lt": "<", "le": "≤", "gt": ">", "ge": "≥", "eq": "=", "ne": "≠"}


def _real_lit(text: str) -> str:
    """Print a Fortran real literal as a Lean numeral (``3.0`` → ``3``)."""
    if "." in text:
        whole, frac = text.split(".", 1)
        if frac.strip("0") == "":
            return whole or "0"
    return text


def _is_int_expr(e: Expr) -> bool:
    """A subexpression the source evaluates in *integer* arithmetic: built
    entirely from integer literals. (Integer-typed names never get this far —
    parameters and locals are gated in :func:`print_kernel`.)"""
    if isinstance(e, IntLit):
        return True
    if isinstance(e, (Paren, Neg)):
        return _is_int_expr(e.inner)
    if isinstance(e, BinOp):
        return _is_int_expr(e.lhs) and _is_int_expr(e.rhs)
    return False


def print_expr(e: Expr, parent_prec: int = 0, right: bool = False) -> str:
    if isinstance(e, RealLit):
        return _real_lit(e.text)
    if isinstance(e, IntLit):
        return e.text
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Paren):
        return f"({print_expr(e.inner)})"
    if isinstance(e, Neg):
        # Fortran only admits unary minus on a whole term (R1008), but Lean's
        # prefix `-` binds tighter than `*`, so a compound operand must regain
        # its grouping explicitly: Neg(2*x) prints as -(2 * x). Leaves — and
        # Paren/Call, which bring their own delimiters — stay bare.
        compound = isinstance(e.inner, (BinOp, Cmp, Cond))
        inner = f"({print_expr(e.inner)})" if compound else print_expr(e.inner)
        s = f"-{inner}"
        return f"({s})" if parent_prec > 1 else s
    if isinstance(e, BinOp):
        # Integer-valued `/` (and `**`) evaluate in integer arithmetic in the
        # source — 2/3 is 0 in Fortran and C++, 2/3 in ℝ. The real-valued
        # model cannot represent that, so it refuses rather than mismodel
        # (faithful integer semantics is roadmap — the manual's Limits page).
        # Mixed operands are fine: the integer promotes, and real division
        # is what the source computes.
        if e.op in ("div", "pow") and _is_int_expr(e.lhs) and _is_int_expr(e.rhs):
            spelled = {"div": "/", "pow": "**"}[e.op]
            raise UnsupportedConstruct(
                f"integer-valued '{spelled}': the source evaluates this in "
                f"integer arithmetic, which the model over ℝ cannot "
                f"represent — spell the operands as real literals")
        sym, prec = _BIN[e.op]
        lhs = print_expr(e.lhs, prec, right=False)
        rhs = print_expr(e.rhs, prec, right=True)
        s = f"{lhs} {sym} {rhs}"
        # Parenthesize when the source AST demands grouping the source text
        # didn't spell out (all supported ops are left-associative in both
        # languages except ^, which only takes literal exponents here).
        if prec < parent_prec or (prec == parent_prec and right):
            return f"({s})"
        return s
    if isinstance(e, Cmp):
        return f"{print_expr(e.lhs, 1)} {_CMP[e.op]} {print_expr(e.rhs, 1)}"
    if isinstance(e, Call):
        if e.name == "abs" and len(e.args) == 1:
            return f"|{print_expr(e.args[0])}|"
        if e.name in ("min", "max"):
            if len(e.args) != 2:
                raise UnsupportedConstruct(f"cannot print {e.name} with {len(e.args)} arguments")
            s = f"{e.name} ({print_expr(e.args[0])}) ({print_expr(e.args[1])})"
            return f"({s})" if parent_prec >= _ARG else s
        # A banked primitive, applied to its arguments (the column pass resolves
        # calls; an unbanked callee never reaches the printer).
        s = " ".join([e.name] + [print_expr(a, _ARG) for a in e.args])
        return f"({s})" if parent_prec >= _ARG else s
    if isinstance(e, App):
        s = f"{e.name} {e.index}"
        return f"({s})" if parent_prec >= _ARG else s
    if isinstance(e, Proj):
        return f"({print_expr(e.inner)}).{e.idx}"
    if isinstance(e, Lam):
        s = f"fun {e.index} => {print_expr(e.body)}"
        return f"({s})" if parent_prec > 0 else s
    if isinstance(e, Foldl):
        # Single-line form only (a bare step); multi-line steps are printed by
        # _print_fun when the fold is the value of a `let`.
        if not isinstance(e.step, Tuple_) or len(e.step.elems) != 1:
            raise UnsupportedConstruct(
                "a fold with a multi-line step must be bound by a let")
        s = (f"ks.foldl (fun {e.state} {e.index} => {print_expr(e.step.elems[0])}) "
             f"{print_expr(e.init, _ARG)}")
        return f"({s})" if parent_prec > 0 else s
    if isinstance(e, Cond):
        # Inline conditional from a merged control-flow join. `if then else`
        # sits below every operator in Lean, so any operand position
        # (parent_prec > 0) needs parentheses.
        # A Cond directly in the then-slot is parenthesized for readability
        # (Lean would parse the dangling else correctly, a reader might not);
        # one in the else-slot chains naturally as `else if … then …`.
        then = print_expr(e.then)
        if isinstance(e.then, Cond):
            then = f"({then})"
        s = f"if {print_expr(e.cond)} then {then} else {print_expr(e.orelse)}"
        return f"({s})" if parent_prec > 0 else s
    if isinstance(e, ArrayRef):
        raise UnsupportedConstruct(f"array reference '{e.name}' survived pointization")
    if isinstance(e, ComponentRef):
        raise UnsupportedConstruct(
            f"component reference '{e.base}%{e.comp}' survived pointization")
    raise UnsupportedConstruct(f"cannot print {type(e).__name__}")


def _print_fun(fe: FunExpr, indent: int) -> list[str]:
    ind = "  " * indent
    if isinstance(fe, Let):
        v = fe.value
        if isinstance(v, Foldl) and not (isinstance(v.step, Tuple_) and len(v.step.elems) == 1):
            # Multi-line fold step: the lambda body on its own lines, the
            # closing paren and the initial state after the last of them.
            head = f"{ind}let {fe.name} := ks.foldl (fun {v.state} {v.index} =>"
            step = _print_fun(v.step, indent + 2)
            step[-1] = f"{step[-1]}) {print_expr(v.init, _ARG)}"
            return [head] + step + _print_fun(fe.body, indent)
        return [f"{ind}let {fe.name} := {print_expr(v)}"] + \
            _print_fun(fe.body, indent)
    if isinstance(fe, Tuple_):
        return [f"{ind}{_tuple_text(fe)}"]
    if isinstance(fe, IfExpr):
        lines = [f"{ind}if {print_expr(fe.cond)} then"]
        lines += _print_fun(fe.then, indent + 1)
        lines += _print_else(fe.orelse, indent)
        return lines
    raise UnsupportedConstruct(f"cannot print {type(fe).__name__}")


def _print_else(fe: FunExpr, indent: int) -> list[str]:
    ind = "  " * indent
    if isinstance(fe, Tuple_):                       # compact: else (a, b)
        return [f"{ind}else {_tuple_text(fe)}"]
    if isinstance(fe, IfExpr):                       # chain: else if ... then
        lines = [f"{ind}else if {print_expr(fe.cond)} then"]
        lines += _print_fun(fe.then, indent + 1)
        lines += _print_else(fe.orelse, indent)
        return lines
    return [f"{ind}else"] + _print_fun(fe, indent + 1)


def _tuple_text(t: Tuple_) -> str:
    inner = ", ".join(print_expr(e) for e in t.elems)
    return f"({inner})" if len(t.elems) != 1 else inner


def print_kernel(kernel: Kernel, *, provenance: str = "") -> str:
    """Render a pointized kernel as a complete Lean ``def``.

    ``kernel`` must already be pointized (rank-0 params only); this function
    runs :func:`~groundline.kir.functionalize` itself so printing stays the
    single entry point.
    """
    params, outputs, body = functionalize(kernel)
    out_set = set(outputs)
    non_real_out = [p.name for p in params
                    if p.name in out_set and p.type not in ("real", "real[k]")]
    if non_real_out:
        raise UnsupportedConstruct(
            f"{kernel.name}: non-real output(s) {non_real_out} — the model "
            f"returns reals")
    unknown = [p.name for p in params if p.type not in _LEAN_TYPE]
    if unknown:
        raise UnsupportedConstruct(
            f"{kernel.name}: non-real, non-logical parameters survived "
            f"pointization: {unknown}")
    if not kernel.column and any(p.type == "real[k]" for p in params):
        raise UnsupportedConstruct(f"{kernel.name}: per-k arrays outside a column kernel")
    # Locals must be real: an integer local would be modeled as a real (hiding
    # the source's truncating integer arithmetic — a wrong model, not a coarse
    # one), and a logical local has no ℝ meaning at all. Loop indices never
    # get this far; pointize drops them.
    non_real_locals = [p.name for p in kernel.locals if p.type not in ("real", "real[k]")]
    if non_real_locals:
        raise UnsupportedConstruct(
            f"{kernel.name}: non-real local(s) {non_real_locals} — only real "
            f"locals are modeled (an integer local would hide truncation; a "
            f"logical local has no meaning over ℝ)")
    # A function result is an output the caller supplies no value for, so it
    # is absent from the def's binder list; an inout/out output, whose
    # incoming value the body may read, appears on both sides.
    inputs = [p for p in params if p.intent != "result"]
    if not inputs:
        raise UnsupportedConstruct(
            f"{kernel.name}: no input parameters — a kernel with nothing to "
            f"read has no arguments to model")
    # Binder groups: consecutive inputs of one type share a group, in
    # declaration order — `(a b : ℝ) (flag : Bool) (c : ℝ)`.
    groups: list[tuple[str, list[str]]] = []
    for p in inputs:
        ty = _LEAN_TYPE[p.type]
        if groups and groups[-1][0] == ty:
            groups[-1][1].append(p.name)
        else:
            groups.append((ty, [p.name]))
    binders = " ".join(f"({' '.join(names)} : {ty})" for ty, names in groups)
    if kernel.column:
        # A column kernel abstracts the vertical index type and binds its
        # enumeration in loop order: `{κ : Type*} (ks : List κ)`.
        binders = "{κ : Type*} (ks : List κ) " + binders
    out_type = {p.name: _LEAN_TYPE[p.type] for p in params}
    ret = " × ".join(f"({out_type[o]})" if "→" in out_type[o] else out_type[o]
                     for o in outputs)
    results = [p.name for p in params if p.intent == "result"]
    if results:
        what = (f"Result `{results[0]}` — the function result, modeled "
                f"functionally over ℝ.")
    else:
        # Name the outputs by their actual intents (dedup, declaration order).
        intents = []
        for p in params:
            if p.intent in ("inout", "out") and p.intent not in intents:
                intents.append(p.intent)
        kinds = "/".join(f"`intent({i})`" for i in intents)
        what = (f"Outputs `({', '.join(outputs)})` — the {kinds} arguments, "
                f"modeled functionally over ℝ.")
    doc = f"/-- Generated from {provenance}.\n{what} -/\n" if provenance else ""
    header = f"{doc}def {kernel.name} {binders} : {ret} :="
    return "\n".join([header] + _print_fun(body, 1)) + "\n"


def print_module(kernels: list[tuple[Kernel, str]], *, namespace: str,
                 blurb: str) -> str:
    """Render a full Lean module for generated kernels (imports + namespace).

    ``blurb`` is the module-header provenance text — the caller (the kernel
    bank, ``groundline/kernel_bank.py``) owns it, since provenance names the
    manifest and toolchain; the semantic rendering below is identical for
    every frontend."""
    defs = "\n".join(print_kernel(k, provenance=prov) for k, prov in kernels)
    return f"""import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
-- Generated expressions stay on one line, however wide.
set_option linter.style.longLine false
-- Outputs are also inputs; a kernel may never read an output's incoming value.
set_option linter.unusedVariables false

/-!
# GENERATED FILE — do not edit

{blurb}
-/

namespace {namespace}

noncomputable section

{defs}
end

end {namespace}
"""
