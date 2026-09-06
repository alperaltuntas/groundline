# Column kernels: folds and maps along the vertical

The point tier compares a Fortran loop body with a C++ point function, one
cell at a time. Real orchestration routines are not like that: per horizontal
cell they run a *sequence* of passes over the vertical index `k`, some of
them accumulations. groundline calls these **column kernels** and models them
with two ingredients the point tier did not have — a **fold** and a **map**
along `k` — and one rule that makes them tractable.

## The observation

Take `zonal_BT_mass_flux`. Fortran fills a 3-D temporary in one nest and sums
it in another:

```fortran
do concurrent (k=1:nz, j=jsh:jeh, I=ish-1:ieh)
  call flux_elem(u(I,j,k), h_in(I,j,k), h_in(I+1,j,k), …, uh(I,j,k), duhdu(I,j,k), …)
enddo
do k=1,nz ; do j=jsh,jeh ; do I=ish-1,ieh
  uhbt(I,j) = uhbt(I,j) + uh(I,j,k)
enddo ; enddo ; enddo
```

The C++ port does both in one loop inside a `ParallelFor` over `(i, j)`:

```cpp
for (int k = kmin; k <= kmax; ++k) {
    Real uh_val, duhdu_val;
    flux_elem_point(u(i,j,k), h_in(i,j,k), h_in(i+1,j,k), …, uh_val, duhdu_val, …);
    uhbt_val += uh_val;
}
```

Per column, **both sides walk `k` in the same order**. So the honest model of
each is a sequential fold over the layer enumeration, and equivalence is
*fold congruence* — the step functions agree, hence the folds agree. Nothing
is ever reordered; the commutativity question the [limits page](../limits.md)
reserves for true reductions does not arise.

## The generated shape

Pointizing over the manifest's **column indices** (`columns = ["j", "i"]`)
leaves a straight-line program over per-column state whose loops all run over
`k`. Each becomes one of two things:

- a **map** — a `do concurrent (k, …)` (or a plain `do k`) that writes only
  own-`k` cells: `let uh := fun k => …`, an array as a function;
- a **fold** — a plain `do k` that writes per-column state:
  `ks.foldl (fun uhbt k => uhbt + uh k) 0`.

The Fortran def for the zonal flux:

```lean
def zonal_bt_mass_flux {κ : Type*} (ks : List κ) (u h_in h_w h_e : κ → ℝ) (uhbt dt : ℝ)
    (por_face_areau h_in_ip1 h_w_ip1 h_e_ip1 : κ → ℝ) (dy_cu iareat iareat_ip1 idxt idxt_ip1 : ℝ)
    (vol_cfl : Bool) : ℝ :=
  let uh := fun k => (flux_elem (u k) (h_in k) (h_in_ip1 k) … 0 0 1 dy_cu … dt vol_cfl (por_face_areau k)).1
  let duhdu := fun k => (flux_elem (u k) … ).2
  let uhbt := ks.foldl (fun uhbt k => uhbt + uh k) 0
  uhbt
```

`κ` is an abstract layer type and `ks` its enumeration in loop order.
Per-layer inputs are `κ → ℝ`, per-column quantities `ℝ`, flags `Bool`. The
C++ def has the C++ shape — one fold whose step binds `uh_val` and
`duhdu_val` from the call and adds — and unfolding the Fortran's `let uh`
gives that fold verbatim. **Loop fusion is definitional.** The column lemma
is `simp only` with the two defs and the callee's theorem.

## Calls to banked primitives

`call flux_elem(…)` is an application of the callee's *generated def on that
side* — `flux_elem` here, `flux_elem_point` there — with the actuals matched
to the callee's dummies **positionally** (keyword actuals refuse). Actuals for
dummies the callee dropped (the grid structs) are skipped; an `intent(out)`
slot gets a `0` placeholder the callee never reads; the outputs come back as
a tuple, bound one projection at a time (`(flux_elem …).1`). The callee must
be banked in the same manifest. Composition in Lean is the callee's theorem
rewriting inside the caller's fold — the first place a generated def
references another.

On the C++ side every output is spelled `Real &`, which the frontend maps to
`inout`. A `Real &` parameter the callee **never reads before assigning** is
an output in Fortran's sense (`flux_elem_point`'s `uh`, `duhdu`), so a caller
may pass it an uninitialized receiver; the registry reclassifies such
parameters as `out` by walking the callee's body.

## Pruning under declared hypotheses

The OBC paths of the mass-flux routines are guarded by flags the C++ port
never sets (it aborts on a non-null OBC pointer). The manifest states the
hypothesis, `assume = { local_specified_bc = false, obc_in_row = false }`,
and every block guarded by an assumed-false flag — or by a conjunction
containing one — is **dropped before its body is modeled**; so are
assignments to the flag, and any `if` or `do` left empty afterwards (its
condition is never modeled, which is sound because Fortran conditions have
no side effects). `ignore_calls = ["cpu_clock_begin", "cpu_clock_end"]`
drops the timer calls as declared effect-free. Integer locals that only ever
feed loop bounds (`ish = LB%ish`, `nz = GV%ke`) are dead for the model and
dropped too.

The generated def is then the kernel **specialized** to the hypotheses, and
its doc comment says so:

```
specialized under the hypothesis `local_specified_bc = false`, `obc_in_row = false`
(guarded blocks pruned); calls to `cpu_clock_begin`, `cpu_clock_end` dropped as
declared effect-free.
```

A specialization is honest only when loud; nothing is pruned that the
manifest did not name.

## Masks, row scratch, several states, component outputs

The second stage (`set_zonal_BT_cont`, 2026-09-05) added the shapes an
orchestration routine's *inner* logic needs:

- **Masks.** `do k ; do concurrent (I=ish-1:ieh, do_I(I,j))` runs each layer
  step only where the flag holds. The mask is a per-column `Bool` input and
  the body runs under it: in a fold the step becomes `if do_i then step else
  (duR, duL)`; per-column statements become a guarded block; a masked *map*
  refuses (skipped cells stay unwritten, which `fun k => …` cannot say). The
  C++ tests `active = (do_I(i,j,0) != 0)` once and wraps both loops and the
  tail in `if (active)`. Equivalence is a case split on the Bool.
- **Row scratch.** `duL(I)`, `FAmt_L(I)`, … are 1-D locals indexed by `I`
  alone under the plain `do j`. A *local* array indexed by a strict subset
  of the column indices is a per-column scalar — sound because nobody
  outside observes the cells the columns share along `j`, the omitted index
  is bound by a plain (sequential) loop, and a value could only cross from
  one column to another through a read the column body has not yet written,
  which [functionalize](functionalize.md) refuses. The same scratch under a
  `do concurrent (j)` is a race in the source and refuses.
- **Several fold states.** A fold that accumulates five totals at once binds
  them together:

  ```lean
  let (FAmt_0, FAmt_L, FAmt_R, uhtot_L, uhtot_R) :=
    ks.foldl (fun (FAmt_0, FAmt_L, FAmt_R, uhtot_L, uhtot_R) k =>
        … (FAmt_0 + duhdu_0, FAmt_L + duhdu_L, …)) (FAmt_0, FAmt_L, FAmt_R, uhtot_L, uhtot_R)
  ```

  A pattern-matching lambda over the state tuple and a destructuring `let`
  for the result. Lean elaborates both to `match`; `simp` reduces a match on
  a pair to projections, so the two sides meet as the same term.
- **A per-column `if`.** The tail under `if (do_I(I,j))` on one side and
  `if (active) { for k … ; tail }` on the other: branches may hold
  per-column statements and whole k-nests, and functionalize joins them as
  anywhere else.
- **Component outputs.** `BT_cont%FA_u_W0(I,j) = FA_0` writes a component
  array of an `intent(inout)` derived-type dummy at the column cell — rule B
  for *outputs*: a synthesized `out` parameter named after the component.
  The C++ writes six separate `Array4`s. The Fortran def's outputs come in
  first-write order, the C++ def's in parameter order, and the theorem
  carries the permutation (`btContCppOrder`).

Two rewrites in that proof carry language semantics — `neg_mul` and
`neg_div`, the unary-minus precedence Fortran and C++ disagree on — and are
[float-exact](../limits.md#floating-point-a-readiness-ledger). Everything
else is unfolding and the case split.

## The C++ address

A column kernel's C++ side is the body of a lambda: `parallel_for = N`
selects the N-th `ParallelFor` call of the function (source order), and
`columns = ["i", "j"]` must spell the lambda's named `int` parameters.
Inside, `Array4` reads are classified by their indices — `u(i,j,k)` a
per-layer array, `dy_Cu(i,j,0)` a per-column scalar (the literal `0` is
AMReX's unit third extent for 2-D fields), `h_in(i+1,j,k)` a stencil input;
`for (int k = kmin; k <= kmax; ++k)` is the fold or map; `+=` is an
assignment; a call statement with `Real &` receivers is a call to a banked
primitive; `CS.vol_CFL` is a member read on a const struct reference — a
`Bool` input; `do_I(i,j,0) != 0` on an `Array4<const int>` is a per-cell
flag — the read *is* the Bool, and the integer array is admitted in no other
shape; `const bool active = …` is a `let`. Statements *outside* the lambda
are not modeled, with one exception: `const Real` locals of the enclosing
function that the lambda captures (`const Real Idt = 1.0_rt / dt;`) are
hoisted into the model in declaration order — the C++ computes before the
launch what the Fortran computes before its loops. Any other captured
function-scope variable may only be a loop bound or an assumed flag; a
non-const captured Real refuses. Real literals are printed from their
**source spelling**, read at the JSON node's byte offset — clang's reported
`value` is the parsed long double printed back (`0.1_rt` becomes
`0.100000000000000000001`), which is not what the source says.

## Licenses

Everything the point tier says about licenses carries over per nest. A
stencil along a column index is admitted when that index was bound by an
independence-asserting construct — `do concurrent`, or the `ParallelFor` a
lambda runs under — and the array is never written in the nest. At the
kernel level the C++ launch is the pointwise map over columns (the
assertion); a Fortran accumulation nest that is a plain DO over the columns
is modeled as `foldSeq` over the column enumeration and the
[schema lemma](pointize.md) turns it into the pointwise map.

## The boundary of the fold model

Refused today, each pinned by a fixture: a k-loop that writes both per-k
cells and per-column state (a **scan** — `zonal_flux_adjust`'s Newton
iteration lives here); a read of a per-k array at an offset in `k` (a
k-recurrence); a masked map; a mask on a nest that binds only some of the
column indices; a row scratch read before any column wrote it, or shared by
`do concurrent` columns; a component write inside a k-loop, or on a base
that is not an `intent(inout)` derived-type dummy; a call neither banked nor
declared ignorable; statements at a partial column level (inside `do
concurrent (j)` but outside the `I` nests); `do concurrent` locality specs.
The design that this page implements, with what the next stage (B3) adds,
is `docs/COLUMN_KERNELS.md`.
