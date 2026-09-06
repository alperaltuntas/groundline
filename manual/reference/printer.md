# Printer behavior

`groundline/lean_printer.py`, exhaustively. The governing principle is
[the fidelity contract](../concepts/printer-fidelity.md): mirror the source's
shapes, simplify nothing. This page is the mechanical detail.

## Literals

- A real literal keeps its source spelling, normalized only to one canonical
  Lean numeral per value-as-written: a trailing zero-fraction is dropped
  (`3.0` → `3`, `12.0` → `12`), a leading `.` gains its zero (`.5` → `0.5`),
  and an exponent spelling is normalized — mantissa trailing zeros, the
  letter (`E`, Fortran's `d`), the sign and leading zeros of the exponent —
  so that `1e-6`, `1.0e-6`, `1E-06` and `1.d-6` all print `1e-6` (Lean's
  `1e-6` and `1.0e-6` are *different terms*, and a proof by unfolding needs
  the same one from both sides). Anything else prints as spelled (`0.5` →
  `0.5`, `1.5` → `1.5`). The value is never touched.
- The Fortran spelling comes from the dump's structured leaf, never from
  unparse text. The C++ spelling is the **source token** read at the JSON
  node's byte offset — clang's `FloatingLiteral.value` is the parsed number
  printed back, exact for dyadic literals (`3.0_rt` → `3`) but an
  approximation for long-double literals (`0.1_rt` →
  `0.100000000000000000001`); a literal whose token cannot be recovered
  refuses ([frontends](frontends.md)).
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
  indent; `LetPat` → `let (a, b) := value` — a fold's several states, or the
  locals of a join that read each other's prior values, whose value is then
  an `if` over `TupleExpr` branches `(x, y)`.
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
logical inputs as `Bool`, per-layer arrays as `κ → ℝ` — so a kernel with a
logical flag between two reals prints `(… dt : ℝ) (vol_cfl : Bool)
(por_face_area : ℝ)`. A [column kernel](../concepts/column-kernels.md) opens
with `{κ : Type*} (ks : List κ)`, the abstract layer type and its
enumeration. Outputs must be real or per-layer, and so must locals.

Column forms: a per-layer read prints as an application `uh k`; a call to a
banked primitive as `flux_elem (u k) (h k) … 0 0 1 dy_cu …` with compound
arguments parenthesized; a call output as a projection `(flux_elem …).1`;
a map as `let uh := fun k => …`; a fold as `ks.foldl (fun uhbt k => …) init`,
on one line when the step is a bare expression and otherwise with the step's
`let`s on their own lines and the closing `) init` after the last; a fold
with several states as `let (a, b) := ks.foldl (fun (a, b) k => …) (a₀, b₀)`
— a pattern-matching lambda and a destructuring `let`. Locals may be real or
logical (a `let` of a Bool-valued expression); integer locals refuse.

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
