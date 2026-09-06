# The printer's fidelity contract

`groundline/lean_printer.py` renders a pointized, functionalized kernel as a
Lean 4 `def` over ℝ. Its whole contract fits in one sentence:

> **Mirror the source's own shapes. Simplify nothing. Equivalence is the
> prover's job.**

## What "mirror the source" means concretely

- **Source parentheses survive.** The IR keeps a `Paren` node for every
  parenthesis the programmer wrote; the printer emits it. The C++ source's
  `(curv * curv) + (3.0_rt * (dh * dh))` prints with those parentheses, while
  the Fortran's `curv**2 + 3.0*dh**2` prints as `curv ^ 2 + 3 * dh ^ 2` —
  each generated def is recognizably *its* source, auditable line-by-line
  against it.
- **Operator spellings map one-to-one** (`**` → `^`, `<=` → `≤`, `abs(x)` →
  `|x|`), and nothing is algebraically rewritten. If the two sides compute
  the same value through different shapes, the generated defs *differ*, and
  the equivalence theorem does real work absorbing exactly the transcription
  deltas — and nothing else.
- **Literals keep their spelling**, normalized only to one canonical Lean
  numeral per spelled value: `3.0` prints as `3`, `0.5` as `0.5`, `1.0e-6`
  and `1e-6` both as `1e-6`. The Fortran frontend reads the *structured*
  literal from the dump tree (never the unparse text, where `12.0` can
  resurface as `1.2e1_8`); the C++ frontend reads the literal's *source
  token* from the file — clang's reported `value` is the parsed long double
  printed back, which for `0.1_rt` is `0.100000000000000000001` and would
  put a value in the model the source never wrote.
- **Grouping the source didn't spell out is added only where Lean's
  precedence demands it** — e.g. Lean's prefix `-` binds tighter than `*`
  while Fortran's unary minus applies to a whole term, so `Neg(2 * x)` must
  print as `-(2 * x)`; and an inline `Cond` in operand position needs
  parentheses because `if … then … else` sits below every operator. The
  [printer behavior reference](../reference/printer.md) lists these rules
  exhaustively.

## Why fidelity, rather than normalization?

Because the printer is [trusted-base code](trusted-base.md). Anyone auditing
the pipeline must be able to hold a generated def next to its Fortran or C++
source and check the correspondence *by eye, one expression at a time*. A
normalizing printer (constant-folding, flattening parentheses, canonicalizing
`a*b+c`) would be "smarter" — and would move semantic decisions into exactly
the component that must stay too simple to hide a bug. The cleverness lives
in the *theorems* instead, where the proof checker verifies it.

The payoff is measurable: when the printer regenerated the first banked
kernel from the production dump, the generated def was proved equal to the
hand-written model **by `rfl`** — definitional equality, meaning Lean's
kernel sees the two as the *same function by unfolding definitions alone*,
with zero proof steps. There is no stronger no-drift statement; the
[first case study](../case-studies/ppm-limit-pos.md) unpacks it.

## What the printed module contains

`print_module` wraps the defs with targeted Mathlib imports
(`Mathlib.Data.Real.Basic`, `Mathlib.Tactic.Ring`), a `noncomputable section`
inside the manifest's namespace, and three documented linter options
(generated expressions stay on one line; output binders may be legitimately
unused). Each def carries a doc comment naming its provenance — which symbol,
in which dump or header, via which frontend — and the module header stamps how
to regenerate it, plus (C++ side) the pinned clang version and full flag set.
The provenance text is written by the [kernel bank](../reference/manifest.md),
not the printer, so the semantic rendering is identical for every frontend.

A final honesty gate at printing time: any parameter that is not a real scalar
by this point, or any IR node that should not have survived the passes
(`ArrayRef`, `ComponentRef`), refuses rather than prints.
