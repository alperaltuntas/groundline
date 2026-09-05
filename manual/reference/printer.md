# Printer behavior

`groundline/lean_printer.py`, exhaustively. The governing principle is
[the fidelity contract](../concepts/printer-fidelity.md): mirror the source's
shapes, simplify nothing. This page is the mechanical detail.

## Literals

- A Fortran real literal keeps its source spelling, normalized only to Lean
  numeral syntax: a trailing zero-fraction is dropped (`3.0` → `3`,
  `12.0` → `12`), anything else prints as spelled (`0.5` → `0.5`). The
  spelling comes from the dump's structured leaf, never from unparse text.
- clang reports `FloatingLiteral` values in shortest round-trip form
  (`3.0_rt` → `3`, `0.5_rt` → `0.5`), which lands on the same numerals from
  the other side — cross-language spelling fidelity through a different
  route.
- Integer literals print as spelled.

## Operators, precedence, parenthesization

Spelling map: `+ - * /` unchanged, `**` → `^`; comparisons `<` `≤` `>` `≥`
`=` `≠`. Three precedence levels are modeled (add/sub < mul/div < pow) —
Lean and Fortran agree on these levels for the supported subset.

Parentheses appear in exactly three cases:

1. **Source parentheses** (`Paren` nodes) — always printed. The source's own
   grouping is fidelity, even when redundant.
2. **AST-demanded grouping** — when a child's precedence is lower than its
   context, or equal in the right operand of a same-precedence operator
   (all supported ops are left-associative in both languages; `^` only takes
   literal exponents in the subset): `BinOp(mul, a, BinOp(add, b, c))` with
   no source parens prints `a * (b + c)`.
3. **Lean-specific bindings** —
   `Neg` of a compound operand regains its grouping (`-(2 * x)`) because
   Lean's prefix `-` binds tighter than `*` while Fortran's applies to the
   whole term; a negated operand of `*`/`/`/`^` is itself parenthesized
   (`(-x) * y`); an inline `Cond` in any operand position is parenthesized
   because `if … then … else` sits below every operator in Lean.

## Calls

- `abs(x)` prints as `|x|`.
- `min`/`max` print as binary applications with parenthesized arguments
  (`min (a) (b)`). (Printable, though no banked kernel uses them yet; the
  *frontends* currently admit only `abs` — the printer's `min`/`max` support
  is ready for the subset to grow.)
- Any other call refuses at print time (and would already have refused at
  extraction).

## Functional forms

- `Let` → `let name := value` on its own line, body continuing at the same
  indent.
- `IfExpr` → multi-line `if cond then / else` blocks; an `IfExpr` in the else
  slot chains as `else if … then` (mirroring elseif chains); a tuple in the
  else slot compacts to `else (a, b)`.
- `Tuple_` → `(a, b, …)`; a single output prints bare (return type `ℝ`, not
  a 1-tuple).

## The def and module wrappers

`print_kernel` refuses non-real parameters and any `ArrayRef`/`ComponentRef`
that survived pointization (final honesty gates), then renders:

```lean
/-- Generated from <provenance>.
Outputs `(...)` — the `intent(inout)`/`intent(out)` arguments, modeled functionally over ℝ. -/
def <name> (<params> : ℝ) : ℝ × … :=
  ...
```

Binders are grouped by type in declaration order — real inputs as `ℝ`,
logical inputs as `Bool` — so a kernel with a logical flag between two reals
prints `(… dt : ℝ) (vol_cfl : Bool) (por_face_area : ℝ)`. Outputs must be
real (the return type is `ℝ × …`), and so must locals.

The "Outputs" line **derives from the actual intents** of the kernel's output
parameters (deduplicated, declaration order) — it used to hardcode
`intent(inout)` until a kernel with `intent(out)` outputs exposed the lie.
A **function kernel** prints ``Result `r` — the function result, modeled
functionally over ℝ.`` instead, and its binder list carries only the
arguments: the caller supplies no value for the result, so it is not a
parameter of the def (a function kernel with no arguments at all refuses).

`print_module` emits: two targeted Mathlib imports (`Mathlib.Data.Real.Basic`,
`Mathlib.Tactic.Ring` — never a blanket `import Mathlib`), three linter
options each with a rationale comment (non-Mathlib header style; generated
expressions stay on one line, so no line-length lint; output binders may be
legitimately unused — a kernel like `edge_thickness_upwind` never reads an
output's incoming value), the `GENERATED FILE — do not edit` header with the
caller-supplied provenance blurb, and the defs inside
`namespace <ns> / noncomputable section`.

The blurb is owned by the caller (the kernel bank), since provenance names
the manifest and toolchain; the semantic rendering is identical for every
frontend. Regeneration is byte-stable — the one exception is the C++ blurb's
clang version line, stamped fresh each run by design.
