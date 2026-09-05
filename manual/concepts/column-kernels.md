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
`Bool` input. Statements *outside* the lambda are not modeled: a captured
function-scope variable may only be a loop bound or an assumed flag.

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
k-recurrence); a fold with several state variables (next: `set_zonal_BT_cont`);
masks on `do concurrent`; a call neither banked nor declared ignorable;
statements at a partial column level (inside `do concurrent (j)` but outside
the `I` nests). The design that this page implements, with what the next
stages add, is `docs/COLUMN_KERNELS.md`.
