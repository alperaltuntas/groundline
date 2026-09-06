# The kernel IR and its refusal discipline

`groundline/kir.py` defines the small vocabulary in which kernels are
modeled, and one rule that the whole method depends on: **any construct
outside the supported subset raises `UnsupportedConstruct` — the pipeline
refuses, it never guesses.**

## Why refusing matters so much

A proof is only as good as the model it is about. If the translator met an
unfamiliar construct and produced a *plausible* model — dropped a cast it
didn't understand, approximated a subscript, guessed an operator — every
theorem downstream would still compile, and would be **vacuous**: a correct
proof about the wrong function. That is the one failure mode this design
refuses to admit. The trade-off is deliberate: the subset grows only when a
real kernel demands a construct, each extension arrives with fixtures
pinning both the accepted and the refused shapes, and everything else fails
loudly with a message naming the construct.

The flip side of refusal is a promise: **what is accepted is modeled exactly.**
The complete inventory of refusal sites — every trigger, in every stage — is
in the [refusal catalog](../reference/refusals.md).

## The vocabulary

Expressions (frozen dataclasses, language-neutral):

| Node | Meaning |
|---|---|
| `RealLit`, `IntLit` | literals, carrying their **source spelling** (`"3.0"`, `"2"`) |
| `Var` | scalar variable read |
| `ArrayRef` | array reference with subscript expressions (only until [pointize](pointize.md)) |
| `ComponentRef` | derived-type component read `base%comp` (only until pointize) |
| `Paren` | *source* parentheses — semantically transparent, kept for fidelity |
| `Neg` | unary minus |
| `BinOp` | `add / sub / mul / div / pow` |
| `Cmp` | `lt / le / gt / ge / eq / ne` |
| `Call` | intrinsic reference (`abs`; `min`/`max` are printable) |
| `Cond` | inline conditional expression — created only by [functionalize](functionalize.md)'s join merge, never by a frontend |

| `Slice`, `App`, `Proj`, `Lam`, `Foldl` | the column vocabulary: a bare `:` subscript (whole-array assignment); a per-k array applied at the fold index (`uh k`); a tuple projection (`(f a b).1`); `fun k => …`; `ks.foldl (fun s k => …) s₀` with one or more state variables — see [Column kernels](column-kernels.md) |
| `TupleExpr` | a tuple value `(a, b)` inside an expression — the branches of a joined `if` whose locals read each other's prior values; created only by functionalize |

Statements: `Assign`, `If` (structured, with elseif branches and an else
body), `DoConcurrent` (multi-index nest, with its optional scalar mask —
refused by the point tier, admitted by the column pass), `Do` (one level of
a plain loop, no stride); and, for column kernels, `CallStmt` (a call as the frontends see
it), `CallBind` (the same call resolved against a banked callee), `MapStmt`
and `FoldStmt` (a k-loop as a map or a fold). A kernel is `Kernel(name, params, locals, body)` with each
`Param` carrying its declared type (`real`, `integer`, `logical`, a derived
type, or `real[k]` for a per-layer array — real, logical and per-layer reach
the printed def, as `ℝ`, `Bool` and `κ → ℝ` binders), intent, and rank — the intent being `in`, `inout`, `out`, or
`result` (a function's result variable / return value: the single output, for
which the caller supplies no value).

Note what is *absent*: no while loops, no function calls other than a few
intrinsics, no I/O, no pointers, no array sections, no modules or globals.
None of that is an oversight — it is the subset's boundary, and crossing it
refuses.

## Two passes shape a kernel for printing

1. **[pointize](pointize.md)** — strip the loop-nest wrapper and turn every
   array reference indexed exactly by the loop indices into a scalar. This is
   the semantic move that pairs a Fortran loop nest with a per-point C++
   kernel — and the pass where the licensing question (who says the
   iterations are independent?) lives.
2. **[functionalize](functionalize.md)** — turn the imperative body into one
   functional expression: locals become `let` bindings, writes to outputs
   thread a symbolic state, and every control-flow path ends by materializing
   the output tuple.

Pointize runs only on the Fortran side, and only on loop kernels whose
manifest entry licenses it with `pointize = true` — a per-point Fortran
subroutine, like every supported C++ function, skips it. Functionalize and
the printer are shared verbatim.

## How the refusal discipline is enforced

The refusal discipline is pinned by tests, not just asserted: the conformance
suite (`tests/f90/`, `tests/cpp/`) contains **deliberate refusal fixtures** —
a k-recurrence that must never pointize, joins with locals that must not
merge, an integer literal whose implicit cast must not silently unwrap — and
the test suite asserts the refusals fire. When an extension widens the
subset, its refusal tests keep the old boundary honest everywhere else.
