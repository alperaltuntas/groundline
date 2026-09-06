# Column kernels — design note for Tier B

> **Status:** accepted 2026-09-05; **B1 and B2 implemented** the same day
> (the barotropic mass fluxes; `set_zonal_BT_cont` — DEVLOG entries).
> Sections 1–4 and the B2 paragraph of §5 describe what now runs, with these
> implementation notes: (a) the fold/map decision reads the k-loop's *write
> set* — a scalar local written in the loop is fold state only if it was
> bound before the loop or is read before written inside it, otherwise a
> per-iteration temporary; (b) a C++ `Real &` parameter the callee never
> reads before assigning is reclassified as an output, so a caller may pass
> an uninitialized receiver; (c) two pruning rules the note did not
> anticipate were needed and are declared in the manifest like `assume`:
> `ignore_calls` (timer calls dropped as effect-free) and the automatic
> elimination of integer locals that only feed loop bounds; (d) flag names
> are matched case-insensitively on both sides; (e) B2 needed one rule the
> note did not list — **row scratch**: a *local* array indexed by a strict
> subset of the column indices under a plain loop over the rest (`duL(I)`
> under `do j`) is a per-column scalar, sound because a read before the
> column body writes it refuses in functionalize and a concurrent omitted
> index refuses as a race; (f) the masked-fold lemma of §4 was not needed as
> a lemma — a case split on the Bool and `simp` do it; (g) a fold's several
> states print as a pattern-matching lambda and a destructuring `let`, and
> the theorem for `set_zonal_BT_cont` carries the permutation between the
> Fortran's first-write output order and the C++'s parameter order; (h) the
> user manual's [Column kernels](../manual/concepts/column-kernels.md) page
> is the present-tense account. B3 in §5 remains the plan.

The point tier (Tier A, complete 2026-09-05) certifies the three primitives of
TIM PR 36 — `ratio_max`, `flux_elem`, `continuity_convergence_point` — and the
loop bodies that reduce to them. What remains of the PR is the orchestration
around those primitives: `zonal_BT_mass_flux`, `set_zonal_BT_cont`, the
j-body of `zonal_mass_flux`, and their meridional twins. These are **column
kernels**: per horizontal cell they run a *sequence* of passes over the
vertical index `k`, some of them accumulations. This note says how to model
them, how to extract them, and what the proofs look like — and lists the
decisions that are the user's.

---

## 1. The shape, and the observation that makes it tractable

`zonal_BT_mass_flux` is the smallest instance. Fortran (OBC blocks elided):

```fortran
uhbt(:,:) = 0.0
do concurrent (k=1:nz, j=jsh:jeh, I=ish-1:ieh)
  call flux_elem(u(I,j,k), h_in(I,j,k), h_in(I+1,j,k), h_W(I,j,k), h_W(I+1,j,k), h_E(I,j,k), &
                 h_E(I+1,j,k), uh(I,j,k), duhdu(I,j,k), 1.0, G%dy_Cu(I,j), G%IareaT(I,j), &
                 G%IareaT(I+1,j), G%IdxT(I,j), G%IdxT(I+1,j), dt, G, GV, US, CS%vol_CFL, &
                 por_face_areaU(I,j,k))
enddo
do k=1,nz ; do j=jsh,jeh ; do I=ish-1,ieh
  uhbt(I,j) = uhbt(I,j) + uh(I,j,k)
enddo ; enddo ; enddo
```

C++ (PR 36, OBC blocks commented out in the source):

```cpp
ParallelFor(bx2d, [=] AMREX_GPU_DEVICE (int i, int j, int) noexcept
{
    Real uhbt_val = 0.0_rt;
    for (int k = kmin; k <= kmax; ++k) {
        Real uh_val, duhdu_val;
        flux_elem_point(u(i,j,k), h_in(i,j,k), h_in(i+1,j,k), h_W(i,j,k), h_W(i+1,j,k),
                        h_E(i,j,k), h_E(i+1,j,k), uh_val, duhdu_val, 1.0_rt,
                        dy_Cu(i,j,0), IareaT(i,j,0), IareaT(i+1,j,0), IdxT(i,j,0), IdxT(i+1,j,0),
                        dt, CS.vol_CFL, por_face_areaU(i,j,k));
        uhbt_val += uh_val;
    }
    uhbt(i,j,0) = uhbt_val;
});
```

Three things to notice:

1. **Per column `(I, j)`, both sides iterate `k` in the same order.** The
   Fortran accumulation is a plain `do k` outermost; the C++ is a `for k`.
   Per column, each is a *sequential fold over k*. The honest model of both
   is `List.foldl` over the k-enumeration, and equivalence is **fold
   congruence** — the step functions agree, so the folds agree. This is *not*
   the sequential-versus-unordered question the limits page reserves for
   reductions (where ℝ-commutativity would be needed): the order is shared,
   so no reordering is ever argued.
2. **The Fortran materializes `uh(I,j,k)` as a 3-D temporary and sums it in
   a second loop; the C++ computes and sums in one loop.** In the model an
   array is a function, so the Fortran's first pass is `let uh := fun k => …`
   and its fold reads `uh k`; unfolding the `let` gives the C++'s fold
   verbatim. Loop fusion is definitional — no fusion lemma.
3. **Every other index is a column index.** `j` and `I` appear in every nest,
   every write lands in the iteration's own column cell, and the only
   cross-column reads are read-only stencils (`h_in(I+1,j,k)`). Pointizing
   over the column indices is exactly the point tier's move (rules A/B/C/D),
   applied to a *set* of indices with `k` left over.

So a column kernel is: **pointize over the column indices; what remains is a
straight-line program over per-column state whose loops are all over `k`**,
each a pure map (`fun k => …`) or a fold. The point tier's passes and printer
extend to that program with two new statement forms and one new binding
form.

---

## 2. The target: what the generated def looks like

For `zonal_BT_mass_flux`, pointized over `(j, I)`, with OBC pruned (§6):

```lean
/-- Generated from `zonal_bt_mass_flux` … columns (j, i); k-enumeration `ks`.
Specialized under the manifest hypothesis `local_specified_bc = .false.`
(2 statements pruned). Outputs `(uhbt)` … -/
def zonal_bt_mass_flux (ks : List κ)
    (u h_in h_in_ip1 h_w h_w_ip1 h_e h_e_ip1 por_face_areau : κ → ℝ)
    (uhbt dt dy_cu iareat iareat_ip1 idxt idxt_ip1 : ℝ) (vol_cfl : Bool) : ℝ :=
  let uh := fun k => (GeneratedFtn.flux_elem (u k) (h_in k) (h_in_ip1 k) (h_w k) (h_w_ip1 k)
      (h_e k) (h_e_ip1 k) 0 0 1 dy_cu iareat iareat_ip1 idxt idxt_ip1 dt vol_cfl (por_face_areau k)).1
  let uhbt := 0
  ks.foldl (fun uhbt k => uhbt + uh k) uhbt
```

and the C++ side, from the `ParallelFor` lambda:

```lean
def zonal_bt_mass_flux (ks : List κ) (u h_in h_in_ip1 … : κ → ℝ) (dt dy_cu … : ℝ) (vol_cfl : Bool) : ℝ :=
  let uhbt_val := 0
  ks.foldl (fun uhbt_val k =>
      let (uh_val, duhdu_val) := GeneratedCpp.flux_elem_point (u k) (h_in k) (h_in_ip1 k) … dt vol_cfl (por_face_areau k)
      uhbt_val + uh_val) uhbt_val
```

Reading the shapes:

- **`κ` is an abstract vertical index type** and `ks : List κ` its
  enumeration *in loop order*. Fortran counts `k = 1..nz`, AMReX boxes
  count from `kmin`; the two sides' `k` values differ, but the
  correspondence is order-preserving, and — as with the point tier's `ι` —
  the concrete map is part of the hand-written kernel-level statement, not
  the generated def. Per-k arrays are `κ → ℝ`; per-column quantities are
  `ℝ`; loop-invariant flags are `Bool`.
- **Stencils along a column index** (`h_in(I+1,j,k)`) are rule C as it
  stands: a per-k array of the *neighbor* column, `h_in_ip1 : κ → ℝ`. The
  C++ call site reads `h_in(i+1,j,k)` off the `Array4`; the mirror
  admission on the clang side maps the same literal offset to the same
  synthesized input.
- **A call to a banked primitive** is an application of its *generated def
  on that side* — `GeneratedFtn.flux_elem` here, `GeneratedCpp.flux_elem_point`
  there — with the actuals in dummy order. The two outputs come back as a
  tuple; the Fortran binds them into the per-k cells `uh(I,j,k)`,
  `duhdu(I,j,k)` (hence `.1`), the C++ into the locals `uh_val`,
  `duhdu_val`. The `intent(out)` dummies `uh`, `duhdu` have no incoming
  value at the call site; the binder slots are filled with `0`, as the
  point-tier theorems already do for unused scalar slots (the callee never
  reads them — `flux_elem`'s def ignores its `uh duhdu` binders).
- **The whole-array assignment** `uhbt(:,:) = 0.0` is, per column, the
  scalar `let uhbt := 0` — the fold's initial state.

The point lemma is then: unfold both defs, rewrite the callee with
`fluxElem_point_equiv`, and close the folds by congruence. Sketch:

```lean
theorem zonalBtMassFlux_column_equiv (ks : List κ) … :
    GeneratedCpp.zonal_bt_mass_flux ks u … = GeneratedFtn.zonal_bt_mass_flux ks u … := by
  simp only [GeneratedCpp.zonal_bt_mass_flux, GeneratedFtn.zonal_bt_mass_flux,
             fluxElem_point_equiv]   -- callee rewritten; both folds now identical
```

If `simp only` does not close it outright (the `let (a, b) := …` tuple
binding may need `Prod.fst`/`Prod.snd` unfolding), the fallback is
`List.foldl_ext` (Mathlib: folds agree when the step functions agree on the
enumeration) with the step equality by `simp only [fluxElem_point_equiv]`.
Either way the proof does no arithmetic — the same discipline as the point
tier.

The **kernel-level** theorem lifts over columns exactly as the point tier
does over cells: `do concurrent (j)` / `ParallelFor(bx2d)` over columns is
the pointwise map (assertion license); a plain `do j` around a column body
(as in `zonal_flux_adjust`) is a `foldSeq` over columns with the per-column
state and takes the schema lemma (proof license). Nothing new is needed at
that level — the column body is the point function.

---

## 3. Extraction: the column IR

The column IR is the kernel IR plus two statement forms and one binding
form. Everything else — expressions, `If`, functionalize's join, the
printer's fidelity rules, the refusal discipline — carries over.

### 3.1 Column-pointize

The manifest names the column indices explicitly:

```toml
[[kernel]]
name = "zonal_bt_mass_flux"
fortran = { dump = "MOM6/MOM_continuity_PPM.o_ptree", subroutine = "zonal_bt_mass_flux" }
cpp = { source = "mom_continuity_ppm.cpp", function = "zonal_BT_mass_flux", parallel_for = 1 }
columns = ["j", "i"]          # the pointized indices; every other loop index is a k-loop
assume = { local_specified_bc = false }   # §6
```

Explicit rather than inferred: refuse-don't-guess extends to *which* indices
are the parallel ones. The pass then walks the addressed body statement by
statement:

- a nest is **decomposed** into its column indices and its remaining
  indices. The column indices are pointized with the existing gates — every
  write at the own column cell (rule A's write gate, per nest, with the nest
  form's license: assertion for `do concurrent`, schema lemma for plain
  `do`), stencils on environment arrays only (rule C, `do concurrent`), rule
  B/D synthesis. What remains is a loop over `k`, or no loop at all;
- a remaining `do concurrent (k)` whose body writes only own-`k` cells is a
  **`Map`**: `let a := fun k => …` for each per-k array it writes (an
  array's per-k values are a function of `k`; a body writing two arrays
  yields two `let`s over one shared `fun k => (…, …)`);
- a remaining plain `do k` is a **`Fold`**: its state is the set of
  per-column names it assigns — 2-D arrays at the column cell (`uhbt(I,j)`),
  which pointize to scalars, and scalar locals it writes; the body is the
  step. Per-k reads inside the fold (`uh(I,j,k)`) are applications of the
  per-k arrays in scope. A plain `do k` that writes only own-`k` cells with
  no state dependence is a `Map` too (the schema lemma along `k` is the
  license, and the model is the same `fun k => …`);
- a **statement outside any k-loop** is a per-column scalar statement, as in
  the point tier; a whole-array assignment `a(:,:) = e` over a 2-D array of
  the column shape is the scalar assignment `a = e`.

Refused in this tier (the boundary of the fold model, each with a fixture):
a per-k write inside a fold whose right-hand side depends on the fold state
(a *scan*, e.g. `uh_aux(I,k)` in `zonal_flux_adjust` — Tier C); a read of a
per-k array at an offset in `k` (a k-recurrence, the existing frontier);
a fold state read before it is assigned in a column (undefined); a
fold-carried per-column array indexed by anything but the column indices;
two folds nested in each other.

### 3.2 Calls to banked primitives

A `CallStmt(callee, actuals)` whose callee is a banked Fortran kernel
becomes the application of that kernel's generated def. The rules:

- the callee must be in the same manifest and already extracted (its dummy
  list, intents, and *dropped* derived-type dummies are known from its own
  extraction); an unbanked callee refuses as today;
- actuals are matched to dummies **positionally**; keyword actuals refuse;
- an actual for a dummy the callee *dropped* (the grid structs `G, GV, US`)
  is skipped; an actual for a `logical` dummy must be a Bool input;
- actuals for `intent(in)` dummies are expressions, scalarized by the column
  pass (own-cell → `u k`, stencil → `h_in_ip1 k`, component → `dy_cu`);
  actuals for `intent(out)`/`inout` dummies must be *writable places* —
  per-k cells at the own `k`, per-column state, or locals — and receive the
  tuple components; an `inout` actual's current value fills its binder slot,
  an `out` actual's slot gets `0` (the callee never reads it; if the callee
  did, its own def would show the read and the by-eye audit catches it);
- the C++ mirror: a call to a banked C++ point function, with `Real&`
  actuals as the output places (uninitialized locals `uh_val, duhdu_val`
  declared for the purpose — the mutable-local rule from Tier A), bound as
  `let (uh_val, duhdu_val) := flux_elem_point …`.

The printed form is a tuple `let`; functionalize's state threading is
unchanged (the outputs are just assigned by the call). Composition in Lean is
the callee's already-proved theorem rewriting inside the caller's fold.

### 3.3 The C++ side: lambda extraction

The C++ address is a function plus the ordinal of a `ParallelFor` call in
it (`parallel_for = N`, source order — the same addressing move as
`nest = N`). The lambda's parameters `(int i, int j, int)` are the column
indices (an unnamed third one is ignored). Inside the lambda:

- `Array4` reads `a(i,j,k)` are per-k arrays applied at `k`; `a(i,j,0)`
  (2-D fields stored with a unit third extent) are per-column scalars;
  `a(i+1,j,k)` is the stencil input `a_ip1`; writes `a(i,j,0) = e` are
  per-column outputs, `a(i,j,k) = e` inside a `for k` a `Map`;
- `for (int k = kmin; k <= kmax; ++k)` over a captured integer range is the
  `Fold`/`Map` over `ks`; the bounds drop like Fortran's;
- captured function parameters are inputs (`Real dt` → scalar,
  `Array4<const Real>` → arrays); a member read on a `const` struct
  reference (`CS.vol_CFL`) is rule B's mirror — a synthesized input named
  after the member; a `const bool` local computed before the lambda is a
  Bool input under its own name (`use_visc_rem`, `local_specified_BC`);
- compound assignment `x += e` is `x = x + e`; a conditional expression
  `c ? a : b` is a `Cond` (the one node no frontend produced so far —
  that restriction is lifted here, with the printer already able to spell
  it);
- an unnamed, uninitialized local declared to receive a call's `Real&`
  outputs is the 3.2 binding.

Refused: nested `ParallelFor`s; lambdas with captured *mutable* scratch
written and read across separate `ParallelFor`s (that is inter-kernel
dataflow, §5); anything the point tier refuses.

---

## 4. Lean infrastructure: `Groundline/ColumnSchema.lean`

Small and general, proved once:

- **fold congruence** — folds over the same enumeration with step functions
  that agree on it are equal (`List.foldl_ext` or a local restatement). The
  one lemma every column theorem uses;
- **map/fold fusion is definitional** — no lemma; the generated defs bind
  per-k arrays as `fun k => …` and unfolding does the rest;
- **the masked fold** (`do concurrent (I=…, do_I(I,j))` around a k-loop, vs
  the C++'s `if (active) { for k … }`): per column, `foldl (fun s k => if m
  then f s k else s) s₀ ks` equals `if m then foldl f s₀ ks else s₀`. One
  case split;
- **conditional-init running max** (`zonal_mass_flux`): Fortran initializes
  from `k = 1` and folds `max` over `k = 2..nz`; the C++ folds over all `k`
  with `(k == kmin) ? v : max(acc, v)`. Equal for any nonempty enumeration
  whose head is `kmin`. One induction. This is also the one place an
  **index comparison** (`k == kmin`) appears as a value in a fold body; it
  needs `DecidableEq κ` and the bound as an element of `κ`, and is admitted
  as a Bool condition — addresses compared, not integer arithmetic.

The column-level lift over `(j, i)` reuses the point tier's `pointwise` and
`foldSeq`/`foldSeq_eq_pointwiseMap` unchanged.

---

## 5. Staging

Fixture first at every step; each stage banks its meridional twin as well.

**B1 — `zonal_BT_mass_flux`.** Constructs: column-pointize with explicit
`columns`; `Map` (the `do concurrent (k,j,I)` call nest); `Fold` (the
accumulation); `CallStmt` to a banked primitive (`flux_elem`); the
whole-array assignment; manifest `assume` pruning the two OBC blocks; on the
C++ side lambda addressing, `Array4` indexing, `for k`, `+=`, `Real&`
outputs into locals, `CS.vol_CFL`. Proof: `simp only` with the callee's
theorem, or fold congruence.

**B2 — `set_zonal_BT_cont`.** Adds: **masks** (`do concurrent (I…,
do_I(I,j))` → a per-column Bool input, identity when false) and the masked
fold lemma; several accumulators in one fold; three primitive calls per
step; a per-column tail with ifs writing **component-array outputs**
(`BT_cont%FA_u_W0(I,j) = FA_0` on an `intent(inout)` derived-type dummy —
rule B for *outputs*, at the column cell) which the C++ writes to separate
`Array4`s. The C++ moves `if (active)` outside both folds where the Fortran
masks each fold; the masked-fold lemma plus a case split absorbs it.

**B3 — the j-body of `zonal_mass_flux`.** Adds: `present(x)` as a Bool
input (the C++'s `.p != nullptr` flags are the same facts, so one Bool per
optional); the conditional-init running max and its lemma; `ratio_max`
calls (a banked *function* callee — the result is the call's value in an
expression, `dx_W = ratio_max(…)`); the `visc_rem_u_tmp` scratch array
(Fortran: a 3-D local written by a `Map`, C++: `visc_rem_u_tmp(i,j,k) =
vrt` inside the same fold — fusion again, definitional); several folds in
sequence under `if (use_visc_rem) / if (CS%aggress_adjust)` branches, each a
per-column `if` around a `Fold`. The Fortran's separate `visc_rem_max`
init-and-fold against the C++'s single fold with the `k == kmin` conditional
is where the running-max lemma is used.

**Out of scope for Tier B** (unchanged from the plan): `zonal_flux_adjust`
— the twenty-iteration Newton/bisection fold with per-column convergence
flags and the row-wide `exit` — is a *scan* (per-k writes depend on the fold
state) with a data-dependent iteration count; Tier C, covered by the PR's
capture tests meanwhile. The subroutine-call level — `zonal_mass_flux`
calling `present_uhbt_or_set_BT_cont` calling `zonal_flux_adjust` /
`set_zonal_BT_cont` / `zonal_flux_thickness`, mirrored by the C++'s
separate function calls with scratch `FArrayBox`es between them — is
composition of column kernels through *arrays*, not scalars; it becomes
tractable once B1–B3 exist, and is not part of this note.

---

## 6. Decisions for the user

Marked ★ where the extension asserts something about *meaning*; the rest is
parsing or bookkeeping.

1. **Explicit column indices** (`columns = [...]` in the manifest) rather than
   inference. Bookkeeping, but it is where refuse-don't-guess meets loop
   structure, so stated here.
2. ★ **Manifest-declared hypotheses that prune branches** (`assume = {
   local_specified_bc = false }`). An `if` whose condition is a declared
   logical is *dropped without modeling its body*; the generated def is the
   kernel **specialized** to the hypothesis, has no binder for the flag, and
   says so in its doc comment (`Specialized under … (N statements
   pruned)`); the Lean file's docstring repeats it. This is honest only
   because it is loud. The alternative — modeling the OBC bodies — would pull
   in chained components, integer segment indices and logical component
   reads for code the port has commented out; the port's own scope (abort on
   a non-null OBC) *is* the hypothesis. Both sides prune the same flag.
3. ★ **Calls to banked primitives** as applications of the callee's
   generated def, positional actuals, dropped derived-type actuals skipped,
   `out` slots filled with `0`. Composition through the callee's theorem.
4. ★ **Masks** — a `do concurrent` mask becomes a per-column Bool input, and
   the masked body is `if mask then body else identity`.
5. ★ **The fold model** — a plain `do k` (or `for k`) is `List.foldl` over the
   enumeration in loop order, with per-column scalar state; per-k writes
   inside a k-loop are admitted only as pure maps; a state-dependent per-k
   write (a scan) refuses.
6. ★ **`present(x)` and `.p != nullptr`** as one Bool input per optional
   argument, constant per call.
7. **Index comparisons in fold bodies** (`k == kmin`) as Bool conditions —
   needed by B3 only; listed now so it is not a surprise.
8. Parsing-only: `+=`, `?:` (a frontend-produced `Cond`), whole-array
   assignment, `parallel_for = N` addressing, `Array4` `operator()`
   indexing, struct member reads on const references, component-array
   *writes* as outputs (B2).

Item 3 is the one that changes the trust story most: today every generated
def is closed — it mentions only its own binders. With calls, a generated def
references another generated def, and the caller's theorem depends on the
callee's. That is composition working as intended, but it means the axioms
audit and the byte-stability check now cover a *dependency graph* of defs;
`groundline kernel verify` should report which banked kernels each def
depends on, and a change to a callee's def must be visible in every caller's
regeneration (it will be — the printer emits the callee's *name*, and
`verify` rebuilds the whole project).

---

## 7. What this note does not change

- Equivalence stays over ℝ; the float-readiness ledger applies to the new
  lemmas as to the old (fold congruence and the masked-fold split are
  arithmetic-free; the running-max lemma uses only that `max` is
  associative with its own identity on the first element — float-exact).
- The trusted base grows by the two statement forms, the call binding, the
  column pass, and the lambda walker — each with fixtures pinning the accepted
  shape and its neighbors, each entering by the subset-extension workflow.
- Nothing in the relational IR is touched.
