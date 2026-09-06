# groundline — Devlog

> **Status:** append-only, newest-first. Each entry is dated and records a
> roadblock and its resolution as it happened. **Do not rewrite past entries** —
> they are the historical record, true as of their date. When an entry produces a
> durable conclusion, graduate that conclusion into `VISION.md` (decisions) or
> `DESIGN.md` (architecture) as a clean statement, and leave the entry here as the
> story of how we got there.
>
> Decision IDs (D1–D5) and weakness IDs (W1–W10) refer to `VISION.md` / `DESIGN.md`.
> Entries before 2026-07-31 refer to the tool by its original name,
> **flinspect** — renamed to **groundline** on 2026-07-31 (see that entry);
> per the append-only rule they are not rewritten.

---

## 2026-09-05 (Tier B, B2) — `set_zonal_BT_cont`: masks, several fold states, component outputs — and three latent holes closed on the way

**What was banked.** `set_zonal_bt_cont` (MOM_continuity_PPM.F90, the whole
subroutine as a column kernel over `(j, I)`) against the `ParallelFor(bx2d)`
lambda of `MOM::set_zonal_BT_cont` — the fourteenth manifest entry, the
third column kernel, `lean/groundline/Groundline/SetZonalBtCont.lean`. Per
column: two test velocity corrections chosen by a masked fold with a
conditional step and two state variables; the face areas and transports of
three test velocities by a masked fold with five state variables and three
`flux_elem` calls per layer; a tail that fits `FA_u_W0 / FA_u_WW / uBT_WW`
and their easterly twins into six component arrays of the `intent(inout)`
`BT_cont`. The column lemma is `cases do_I <;> simp only [the two defs,
apply_ite btContCppOrder, btContCppOrder_mk, fluxElem_point_equiv, neg_mul,
neg_div, Bool.false_eq_true, ↓reduceIte]`; the kernel level lifts through
`foldSeq` over the columns as in B1, with a six-tuple per-column state.
Axioms audit clean.

**Semantics decisions implemented (all in the accepted design note §6, or
stated here).**

- *Masks* (§6 item 4). A `do concurrent (I=…, do_I(I,j))` mask is scalarized
  in the nest's context and the body runs under it: a fold step becomes
  `if do_i then step else state`, per-column statements a guarded block, and
  a masked **map** refuses (skipped cells stay unwritten; `fun k => …` has no
  way to say so). The Fortran masks each layer step; the C++ tests
  `active = (do_I(i,j,0) != 0)` once and puts both loops and the tail under
  `if (active)`. The proof is a case split on the Bool — arithmetic-free.
- *Row scratch* — not in the note; stated and implemented here. The
  Fortran's `duL(I)`, `FAmt_L(I)`, `uhtot_R(I)`, … are 1-D locals indexed by
  `I` alone under the plain `do j`. A **local** array indexed plainly by a
  strict subset of the column indices is a per-column scalar. Sound because
  (a) it is a local — nobody outside observes the cells the columns share
  along `j`; (b) the omitted index is bound by a plain, sequential loop (the
  same scratch under a `do concurrent (j)` is a race in the source and
  refuses); (c) the only way a value could flow from one column to another
  through the shared cell is a read before the column body wrote it, and
  functionalize refuses exactly that (`fold state 'acc' is read before it is
  assigned` — pinned). The C++ has plain lambda locals; both sides print
  `let duL := …`.
- *Several fold states.* `FoldStmt` always carried a tuple; functionalize
  and the printer now bind it: `let (duR, duL) := ks.foldl (fun (duR, duL) k
  => …) (duR, duL)` — a pattern-matching lambda over the state tuple, a
  destructuring `let` (new `LetPat` node) for the result. Lean elaborates
  both to `match`; `simp` reduces a match on a pair to projections (structure
  eta), so the two sides meet as `x.1`, `x.2` terms.
- *Column-level `if`* (the tail under `if (do_I)`, the C++ `if (active) {
  for k … }`): branches may hold per-column statements and whole k-nests;
  functionalize joins them as anywhere else.
- *Component-array outputs* (rule B for outputs). `BT_cont%FA_u_W0(I,j) =
  FA_0` on an `intent(inout)` derived-type dummy, indexed exactly by the
  columns, outside any k-loop, becomes a synthesized `out` parameter named
  after the component. Reads of such a component still refuse (the base is
  not `intent(in)`), so an output component is write-only and its incoming
  value is never read. The Fortran def's outputs come in first-write order
  `(W0, WW, uWW, E0, EE, uEE)`, the C++ def's in parameter order `(W0, E0,
  WW, EE, uWW, uEE)`; the theorem carries the permutation `btContCppOrder`.
- *C++ surface:* a per-cell flag `do_I(i,j,0) != 0` on an `Array4<const
  int>` is admitted **only in that shape** — the read *is* the Bool, the
  integer never appears as a value (`!= 1` refuses: "read as a value");
  `bool`/`const bool` locals are `let`s of Bool-valued expressions, in point
  kernels too (the join-locals fixture's `refuse_bool_local` became
  `bool_local_point`; its Fortran twin `logical_local` likewise flipped from
  a printer refusal to a supported form); `const Real` **prologue locals** of
  the enclosing function (`const Real Idt = 1.0_rt / dt;`) captured by the
  lambda are hoisted into the model, in declaration order, as the Fortran's
  own pre-loop assignments are — a non-const captured Real refuses (its
  value at capture is not its declaration); C++ `else if` is flattened into
  the branch list, the IR flang's `ElseIfBlock` already yields (below).
- *Locality specs* (`local(x)` etc.) on `do concurrent` refuse until a
  kernel carries one; MOM6's `DO_LOCALITY(local(…))` macro expands to
  nothing in this build (no `LocalitySpec` node anywhere in the dump).

**Three latent holes, found because this kernel exercised them.**

1. *The mask was silently dropped.* `_extract_do` walked
   `ConcurrentHeader`'s `ConcurrentControl` children and nothing else; a
   `scalar-mask-expr` (dump: a `Scalar -> Logical -> Expr` **sibling** of the
   controls) was never seen, so a masked nest would have been modeled
   unmasked — a wrong model, not a refusal. No banked kernel had a mask, so
   nothing banked was affected. Now: parsed into `DoConcurrent.mask`; the
   point tier refuses it (`masked_point` fixture); the column pass admits it
   as above; any other header child refuses.
2. *Variable capture in functionalize.* An output's pending value is a
   symbolic expression over the names in scope, printed where the path
   materializes it. `BT_cont%FA_u_W0(I,j) = FA_0 ; … ; FA_0 = FAmt_0` made
   the output read the *second* `FA_0` — the first extraction of this
   kernel printed exactly that, and the C++ side, with the same shape, would
   have printed the same wrong thing, and the theorem would have *held*. The
   same hazard sat in the join: merged locals are emitted as `let`s in
   first-assignment order, each value speaking of the bindings *before* the
   IF, so `then: w = u ; else: v = w` printed `let w := …; let v := if c
   then v else w` with `w` already re-bound; and `if (FA_avg > max(FA_0,
   FAmt_L)) then FA_avg = … elseif (…) then FA_0 = FA_avg endif`, whose two
   locals read each other's prior values, cannot be sequenced as `let`s at
   all. Fix, in three parts: (a) before any `let` shadows a name, every
   pending value of the path's outputs (or fold states) that mentions it is
   let-bound under its own name first (`let fa_u_w0 := fa_0`), recursively;
   (b) a join's `let`s are emitted only when no other pending value mentions
   the name, in first-assignment order among the eligible; (c) locals that
   mention each other are bound together by one destructuring `let (fa_avg,
   fa_0) := if c₁ then (…, …) else if c₂ then (…, …) else (…, …)` — every
   right-hand side evaluated before any name changes (new `TupleExpr` node).
   **Regeneration left every existing def byte-identical**, so no banked
   theorem ever rested on a captured value; the hazard was real but latent.
   Pinned on hand-built kernels in `tests/test_functionalize_capture.py`.
3. *clang's literal `value` is not the spelling.* The JSON reports the parsed
   float printed back — for a long-double literal (every `_rt` literal) an
   approximation with its own digits: `0.1_rt` → `0.100000000000000000001`,
   `1.0e-6_rt` → `1.00000000000000000004E-6`. Printing that into an ℝ model
   would state a value the source never wrote. Every literal banked so far
   was dyadic (`0`, `0.5`, `1.5`, `6`), which prints exactly, so nothing
   generated was wrong — but this kernel's `0.1_rt`, `1.0e-6_rt`,
   `1.0e-12_rt` would have been. The frontend now reads each
   `FloatingLiteral`'s **source token** at the JSON node's byte offset and
   `tokLen` (tracking clang's elided `file` keys and, for macro-expanded
   tokens, `expansionLoc` for the file — a literal that is itself
   macro-produced gets no spelling and refuses), cross-checks it against
   `value` to double precision, and refuses a literal without a recoverable
   spelling. The printer canonicalizes exponent spellings so `1e-6` (Fortran)
   and `1.0e-6` (C++) print as one Lean term (`1e-6`; they are *different*
   terms otherwise).

Also fixed: the manifest loader crashed (`TypeError`, a conditional `raise`
of `None`) on a C++-only `parallel_for` entry — the shape every C++ refusal
fixture has.

**Dump-shape notes (Q1 ledger).** flang: the mask is a `Scalar` sibling of
the `ConcurrentControl`s under `ConcurrentHeader`; `Concurrent` has no other
children in this build. clang: a node's `range.begin` carries `file` only
when it differs from the previously printed location; a macro-expanded token
has `spellingLoc` (the macro's file) and `expansionLoc` (where it landed);
`includedFrom` decorates the first location in an included file; the
`AMREX_GPU_HOST_DEVICE` macro makes the first location of every point
kernel in the header a `spellingLoc` in `AMReX_Extension.H`.

**Proof notes.** The permutation needs `apply_ite btContCppOrder`: the
Fortran tail is an `if` of two six-tuples, and `btContCppOrder (if c then
t₁ else t₂)` reduces (by structure eta) to a tuple of projections of the
`if`, not to an `if` of tuples — the C++ shape. Debugging that took a
detour: Lean's pretty printer gives up on the zeta-expanded goal ("failed to
pretty print expression"), so the localization came from a *normalized text
diff of the two generated defs* (lowercase, callee names unified, the two
known rewrites applied) — which showed only the mask placement, the `active`
alias and the output order differing, i.e. no modeling mismatch, and pointed
at the permutation. Worth remembering as a technique. The fixture pair, with
identical output order, closed with the plain simp set — the control that
made the diagnosis quick.

**Float-readiness ledger additions.** `neg_div` (`(-(x)) / v = -((x) / v)`,
IEEE-exact: negation is exact and rounding is sign-symmetric), `apply_ite`
and the Bool case split (representation only, no arithmetic), and the
literal canonicalization (spelling only, same value).

**Considered and ruled out.** Eager `let`-binding of every output assignment
would remove the capture hazard by construction but re-shape all fourteen
generated defs (and the by-eye audit of each); the lazy shield changes no
existing def. Admitting `local()` locality specs: harmless (the model binds
locals per iteration) but unneeded — refused until a kernel carries one.
Per-k masks (`do_I(I,j,k)`) on folds: would be `if m k then …`, sound, but
nothing needs it; the mask is scalarized in the nest context, so it would
work today — on a map it still refuses.

**Fixtures.** `tests/f90/test_kernel_bt_cont.f90` (supported `bt_cont`;
refusals `masked_map`, `scratch_read_first`, `scratch_racing`,
`comp_write_in_k`, point-tier `masked_point`),
`tests/cpp/test_kernel_bt_cont.cpp` (`bt_cont`; `refuse_flag_value`,
`refuse_nonconst_capture`); `tests/test_column.py::TestBtContFixture`,
`tests/test_functionalize_capture.py`. Refusal sites: 187 (from 177) across
the five trusted-base modules. Suite: 288 tests with the toolchain (from 263).

**Next.** B3 — the j-body of `zonal_mass_flux`: `present(x)` / `.p !=
nullptr` as Bool inputs, the conditional-init running max and its lemma,
`ratio_max` as a function callee inside expressions, several folds in
sequence under per-column `if`s. Then the meridional twin of B2
(`set_meridional_BT_cont`, when the PR carries it) is a manifest entry, not
a construct.

---

## 2026-09-05 (Tier B, B1) — The first column kernels: the barotropic mass fluxes, as folds calling a banked primitive

**The design, accepted.** `docs/COLUMN_KERNELS.md` went in front of the user
and was accepted as written: explicit column indices in the manifest, the
fold model (a plain `do k` is `List.foldl` over the layer enumeration in loop
order, per-column scalar state), calls to banked primitives as applications
of the callee's generated def, `present(x)` and `.p != nullptr` as one Bool
input (B3), masks as per-column Bool inputs (B2), and manifest-declared
hypotheses that prune dead branches as a loud specialization. B1 is
`zonal_BT_mass_flux` and its meridional twin: per column, a map filling
`uh(I,j,k)` from `flux_elem` and a fold summing it — against the C++ lambda
that does both in one `for k`.

**What changed, by layer.**

- *Kernel IR* (`kir.py`): five expression nodes — `Slice` (a bare `:`),
  `App` (a per-layer array applied at the fold index, `uh k`), `Proj`
  (`(f …).1`), `Lam` (`fun k => …`), `Foldl` — and four statements:
  `CallStmt` (a call as the frontends see it), `CallBind` (resolved), `MapStmt`,
  `FoldStmt`. `Kernel.column` marks a column kernel; `Param.type` gains
  `real[k]`. `functionalize` binds a call's outputs as projections, a map's
  targets as lambdas, a fold's state as `let s := ks.foldl (fun s k => step)
  init` — the step functionalized with the state as its sole output (`go`
  gained an `outs` argument for this) — always through a `let`, so the
  printer has one place to render a multi-line step.
- *The column pass* (`column.py`, new): pointizes over the declared columns
  with the point tier's rules (A–D), classifying every array reference by
  subscript shape — columns → per-column scalar, columns + k → per-layer
  array, a literal offset on a column index → rule C, on k → refuse. Loop
  nests are split into column indices and at most one k index, threading the
  set of columns already bound by enclosing loops (a lambda binds them all at
  entry; a Fortran `do concurrent (j)` around `(k, I)` nests binds them
  gradually); a k-loop is a **map** when it writes only own-k cells and a
  **fold** when it writes per-column state, and refuses as a **scan** when
  both. Fold state is the per-column arrays written plus the scalar locals
  bound before the loop or read-before-written inside it; a scalar declared
  and assigned inside the loop is a per-iteration temporary (the C++
  `uh_val`, `duhdu_val`). Stencils are licensed by the construct that bound
  the offset's column index — `do concurrent`, or the `ParallelFor` a lambda
  runs under — not by the k-loop's form, which is what makes the C++ `for k`
  reading `h_in(i+1,j,k)` admissible.
- *Calls* resolve positionally against a `Callee` (the callee's def name, its
  full dummy list, its kept parameters). Dropped dummies (grid structs) skip;
  `in` actuals scalarize with the dummy's type as the wanted type — this is
  how `CS%vol_CFL` becomes a Bool input; `out` slots get a `0` placeholder;
  `inout` slots the current value. The registries live in the kernel bank:
  every whole-procedure Fortran entry and every point-function C++ entry is a
  callable primitive. On the C++ side a `Real &` parameter the callee never
  reads before assigning is reclassified `out` (`kir.reads_before_write`,
  precise about ifs: written only when every branch writes) — without this,
  `flux_elem_point`'s `uh`/`duhdu` would be `inout` and the caller's
  uninitialized receivers would read before assignment.
- *Fortran frontend*: column mode extracts the whole subroutine with tolerant
  declarations (the OBC pointer dummy poisons only its name) after a
  **pruning pass on the dump tree**, before any expression is extracted:
  blocks guarded by an assumed-false flag or by a conjunction containing one
  (`if (OBC_in_row(j) .and. …)`), assignments to assumed flags (whole-array
  `obc_in_row(:) = .false.` included), calls in `ignore_calls`, assignments
  to integer locals that only ever feed loop bounds (`ish = LB_in%ish`,
  `nz = GV%ke`; the component name `ish` is not a read of the local), and
  any `if` or `do` left empty — its condition is then never modeled, sound
  because Fortran conditions are pure; the `if (present(LB_in))` and `if
  (associated(OBC))` blocks vanish this way without `present`/`associated`
  ever reaching the intrinsic gate. `CallStmt` extraction (positional actuals;
  keyword refuses), `SubscriptTriplet` as `Slice`, and array ranks read from
  entity declarations as well as `dimension` attributes.
- *C++ frontend*: `parallel_for = N` addresses the N-th `LambdaExpr` of the
  function; its `operator()`'s named `int` parameters must spell `columns`.
  Inside: `CXXOperatorCallExpr` on `operator()` → `ArrayRef` (a trailing
  literal `0` — AMReX's unit third extent for 2-D fields — dropped; `i+1` →
  a stencil subscript), `MemberExpr` on a struct parameter → `ComponentRef`,
  `for (int k = lo; k <= hi; ++k)` → `Do` (exact shape required),
  `CompoundAssignOperator +=` → `x = x + e`, a `CallExpr` statement →
  `CallStmt` with bare `DeclRefExpr` receivers, `if` guarded by an assumed
  flag → pruned. Function parameters: `Array4<const Real> const&` in,
  `Array4<Real> const&` inout, `const T &` a derived struct, `const Box &`
  bounds, pointers must go unreferenced. Captured function-scope locals may
  only be loop bounds or assumed flags — statements outside the lambda are
  not modeled.
- *Printer*: `{κ : Type*} (ks : List κ)` opens a column def; `κ → ℝ` binders;
  application printing for `App` and banked calls (arguments at application
  precedence); `Proj`, `Lam`; `Foldl` inline for a bare step and multi-line
  under a `let` (closing `) init` after the step's last line).
- *Manifest*: `columns`, `assume`, `ignore_calls` (kernel level), `parallel_for`
  + `columns` (cpp table); `extract_*_entry` take the manifest for the callee
  registry; the CLI passes it; parsed dumps are cached per path.

**Two decisions made here that the design note did not list**, for the
user's eye: `ignore_calls` — dropping a procedure call asserts it does not
affect the modeled values; the manifest names each call, and the doc comment
repeats it — and the dead-integer-local elimination, which drops assignments
to integer locals used only as loop bounds without modeling the conditions
around them (sound: pure conditions, values the model never reads). Also
worth knowing: assumed-flag names are matched case-insensitively on the C++
side too, since the manifest spells them once for both.

**Fixtures.** `tests/f90/test_kernel_column` (`flux_pt`, a per-point
callee; `column_sum`, the distilled shape with a timer call, a bounds-only
integer local, a whole-array init, a `do concurrent (k,j,i)` map calling
`flux_pt` with per-k `intent(out)` actuals and a stencil and a component +
offset, a pruned guarded block whose body would refuse, and a plain
`do k;j;i` fold; refusal siblings `scan`, `k_recurrence`, `unbanked_call`)
and `tests/cpp/test_kernel_column.cpp` (an AMReX-shaped prelude — `Array4`,
`Box`, `ParallelFor` — so the same JSON shapes appear; `column_sum`,
`refuse_scan`, `refuse_unbanked_call`). Tests in `tests/test_column.py` drive
both through the kernel bank (the call needs a registry); 14 tests. The
generated fixture defs: the Fortran map/fold pair and the C++ single fold —
the same term after unfolding.

**Production.** Both `*_BT_mass_flux` routines extract with `columns = ["j",
"i"]`, `assume = { local_specified_bc = false, obc_in_row = false }`,
`ignore_calls = ["cpu_clock_begin", "cpu_clock_end"]`; the C++ lambdas with
`parallel_for = 1, columns = ["i", "j"]`. No previously generated def changed.
One obstacle on the way: the PR's `mom_continuity_ppm.cpp` does not compile
standalone — `IntVect` unqualified at eight sites (two already on TURBO-ESM
main), `IArrayBox` without its include or using-declaration — with g++ 12
and clang 21 alike; the submodule's pre-PR commit compiled clean, so TIM's CI
evidently does not build this directory. With the user's OK the submodule
working tree carries the three-line fix (`using amrex::IntVect;` in the
header; `#include <AMReX_IArrayBox.H>` and `using amrex::IArrayBox;` in the
.cpp), to be relayed to the PR author; the manifest is unchanged.

**Proof** (`Groundline/BtMassFlux.lean`): the column lemmas are `simp only
[<the two defs>, fluxElem_point_equiv]` — unfold, zeta-reduce, rewrite the
callee under the fold's binder, and the folds coincide term for term. The
first generated defs that reference another generated def, and the first
theorems composed through a banked theorem. Kernel level: the C++ launch is
the pointwise map over columns; the Fortran accumulation nest is a plain DO
over `(j, I)`, modeled as `foldSeq` over the column enumeration with the
schema lemma — the map nest that precedes it is folded into the per-column
body definitionally. Stencil neighbors are explicit maps `east` / `north`.

## 2026-09-05 (later still) — Tier A item 3: the convergence update banked — read-only stencils, subset-indexed components, nest-invariant locals

**The kernels.** `continuity_zonal_convergence` and
`continuity_merdional_convergence` (the source's spelling) each hold two
`do concurrent (k,j,i)` nests — the `present(hin)` branch and the in-place
branch the source marks "untested" — all four of the shape
`h(i,j,k) = max(h_prev - dt*G%IareaT(i,j)*(flux(i,j,k) - flux(i-1,j,k)), h_min)`.
The port has **one** primitive, `continuity_convergence_point`, whose four
call sites do the stencil and pass scalars
(`continuity_convergence_point(hin(i,j,k), uh(i,j,k), uh(i-1,j,k), dt,
IareaT(i,j,0), h_min)`). So the natural unit here is not one pair but four
Fortran nests against one C++ def: the manifest carries the C++ side on the
first entry only (a def is emitted per entry, and Lean would reject a
duplicate), and `Groundline/ContinuityConvergence.lean` relates each Fortran
def to it. Tier A is complete with this: every primitive of PR 36 carries a
theorem.

**Step 0 — the refusals**, peeled in turn: `references 'hin' — attribute
'Optional'`; `array reference uh('i-1'?, …) not indexed exactly by the loop
indices`; `component read g%iareat(i, j) … indexed exactly by the loop
indices ('k', 'j', 'i')`; `h_min` surviving as a local never bound (the
read-before-assign gate); on the C++ side `kernel must return void` (already
done), then `call to 'max'`, then the cast `NoOp` and the node kinds
`ExprWithCleanups` / `MaterializeTemporaryExpr` that `amrex::max`'s
`const T&` signature produces.

**Rule C — read-only stencils** (`kir.pointize`). The user licensed the
narrow form: a literal-offset read (`index ± literal` only; `1+i` refuses as
a different spelling) of an array **the nest never writes**, in **`do
concurrent` nests only**. The write set of the nest is computed first; an
offset read of a written array refuses as a cross-iteration recurrence in
either loop form, and so does a write to a neighbor cell — which is where
the committed recurrence fixture (`p(i,K+1) = p(i,K) + …`) now refuses,
with a message that says so (`every write must land in the iteration's own
cell`) rather than at the old blanket index gate. Each offset pattern becomes
a synthesized input named after the array and the offsets index by index
(`uh(I-1,j,k)` → `uh_im1`; `a(i+1,j-1,k)` → `a_ip1_jm1`) — dimension-aware,
so `a(i-1,j)` and `a(i,j-1)` cannot collide — and collision-checked against
everything else. On soundness: the value read is loop-entry data, so the
iteration still depends only on loop-entry data; the source's independence
assertion is the license. Noted for the record: the plain-DO case appears to
be covered by the existing schema lemma already, since `foldSeq`'s point
function takes the read-only arrays through its closure (that is how
`thickness_to_dz`'s `h i` and `spv i` are threaded today) and never through
the mutable state — but admitting it is a semantics decision, so it refuses
(`do concurrent nests only`) until asked for.

**Rule B, widened — subset-indexed component arrays.** `G%IareaT(i,j)` in a
`k,j,i` nest becomes the per-cell input `iareat`. Sound because the base is
an `intent(in)` derived-type dummy: the value at `(i,j)` is the same for
every `k`, and it is read-only for the same reason the scalar components are.
The generated def quantifies over any value of the input, which includes the
actual one. A *plain* array indexed by a subset (`dt2d(i,j)`) still refuses —
not needed, not licensed.

**Rule D — nest-invariant locals.** `h_min` is set before the loop
(`h_min = 0.0 ; if (present(hmin)) h_min = hmin`) and only read inside it.
A scalar local the nest never assigns is loop-entry data: it becomes a
synthesized input under its own name and declared type; a local the nest
assigns stays a per-iteration `let` (pinned by `local_written`). How the
caller set it is outside the kernel, like a scalar argument — the same
boundary as every inline-addressed nest.

**`optional`.** Admitted as a declaration attribute in both modes: presence
is the caller's precondition, the body is modeled as a function of the
dummy's value whenever it runs, and a body that could branch on presence —
a `present()` call — refuses anyway. Here the presence guard is the `if` the
addressed nest sits under.

**C++ side.** `amrex::max` / `amrex::min` join `abs` in the callee table, in
their binary form (AMReX's three-argument overloads refuse, pinned). Their
`const T& f(const T&, const T&)` signature drags in three JSON shapes: a
`NoOp` implicit cast (`Real` → `const Real` as a prvalue binds to the
reference — qualifier-only, value untouched by definition; added to the
allowlist with that justification), `MaterializeTemporaryExpr` for the
temporary, and `ExprWithCleanups` around the full-expression. The two wrapper
kinds are unwrapped transparently (single child). The second argument
`h_min`, an lvalue, binds directly with no cast at all.

Considered and ruled out: naming stencil inputs `uh_m1` without the index
(the limits page's sketch) — ambiguous across dimensions; admitting stencils
in plain DO on the closure argument above without asking; admitting
subset-indexed *plain* arrays (no kernel needs it); the three-argument
`max`.

Dump-shape notes (Q1 ledger): the offset subscript is
`SectionSubscript -> Integer -> Expr` over `Subtract(Expr i, Expr 1_4)` with
the literal as `IntLiteralConstant = '1'` — the with-sema unparse text
`int(i-1_4,kind=8)` shows the kind conversion the tree does not carry;
`optional` is a bare `AttrSpec -> Optional`; the subset-indexed component is
the usual `ArrayElement` over `StructureComponent` with two subscripts.
clang: see the C++ paragraph; `amrex::max` resolves to a `FunctionDecl`
named `max` of type `const double &(const double &, const double &) noexcept`.

Fixtures: `tests/f90/test_kernel_stencil` (`converge` — nest 1 under its
presence guard, with the stencil, the subset component, the invariant local
and two optional dummies; `local_written`; refusal siblings
`stencil_plain_do`, `stencil_written`, `subset_plain_array`) and
`tests/cpp/test_kernel_minmax.cpp` (an AMReX-shaped prelude so the same
casts appear; `converge_point`, `clamp_point`, `refuse_max_three`,
`refuse_pow`). Hand-built tests pin the `1+i` spelling, the stencil-name
collision and the neighbor write; the old `test_offset_subscript_refused`
became `test_offset_read_in_do_concurrent_is_a_stencil_input`, and the
recurrence fixture's expected message moved to the own-cell write gate. The
manual's recurrence-refusal snippet was regenerated accordingly.

Proof: `Groundline/ContinuityConvergence.lean` — four point lemmas, all
`rfl` (the bodies are the same expression modulo argument order), and four
kernel-level lifts in which the stencil is an explicit neighbor map on the
index type (`west`, `south`), so the C++ call site's `uh(i-1,j,k)` is
`uh (west i)`. The argument correspondence is read off the call site; a
wrong pairing would fail to prove (`uh - uh_im1` is not `uh_im1 - uh`).
Retroactive check: no previously generated def changed.

## 2026-09-05 (later) — Tier A item 2: `flux_elem` banked — the generalized join, Bool inputs, mutable C++ locals

**The kernel.** `flux_elem` is the PPM face flux: for one candidate face
velocity it computes the transport `uh` and its velocity derivative `duhdu`
from the cell and edge thicknesses on both sides, the grid factors, `dt`,
`visc_rem` and the porous face fraction. Every column kernel of PR 36 calls
it once per layer, so it is the physics of the whole mass-flux family. It is
an `elemental` subroutine with 21 dummies, three of them grid structs the
body never reads, one a `logical` (`vol_CFL`). Its C++ twin
`flux_elem_point` has the same 18 arithmetic arguments in the same order.

**Step 0 — the refusals** (each peeled in turn on the production dump and
the PR header): `intrinsic type 'Logical'` / `parameter 'vol_CFL': type
'const bool'`; then the printer's non-real-parameter gate on `G`, `GV`, `US`;
then functionalize's join gates — `statements after an IF with an elseif
chain`, and locals assigned inside joined branches — and on the C++ side
`local 'CFL' without a copy-initializer` and `assignment target must be a
(reference) parameter`. Two of these were the deliberately restricted shapes
the CW84 entry reserved as semantics decisions; the user licensed both
before implementation.

**The join, generalized** (`kir.functionalize`; `merge_if` / `branch_state`).
The old rule admitted one shape — a single-branch IF assigning only to
outputs — and merged per variable as `Cond(c, then, else)`. The new rule is
the sequential semantics itself, stated once and applied recursively:

- every branch body (then, each elseif, else — an absent else is an empty
  branch) runs against a *copy* of the incoming state; assignments update
  the copy, locals assigned in the branch are tracked in the copy (later
  reads within the branch substitute them — inlining), and a nested IF
  inside the branch merges recursively against the copy, with everything
  after it (the rest of the branch, then the outer continuation) as its
  continuation;
- each variable some branch assigned becomes one conditional chain over the
  branch conditions, conditions evaluated against the pre-IF state;
- merged outputs update the state; merged locals are bound by `Let` right
  after the join, in first-assignment order, so the following statements read
  them by name — `let h_marg := if u > 0 then … else if u < 0 then … else
  0.5 * (h_l_p1 + h_r)` in the generated def.

The one genuinely new rule is for a local a branch defines and others do not.
With a prior `Let` binding, the other paths keep it (`let w := if u > 0 then
u else w` — Lean shadowing, saying exactly what the source does; pinned by
`rebound_local`). With none, the local is undefined there: if nothing after
the join reads it, it is dropped (`flux_elem`'s `CFL`, `curv_3`, `dh` —
inlined where their branch read them, dead afterwards); if something does,
functionalize refuses. The read scan (`_reads_before_redef`) is
conservative — any occurrence inside a later IF counts as a read, an
unconditional reassignment before any read ends the scan — so it can refuse
spuriously and can never mismodel. Ruled out: emitting a `Let` for every
branch-local unconditionally (a `let CFL := if u > 0 then … else <?>` would
need a value the source does not have), and keeping the old one-shape rule
with `flux_elem` special-cased (the CW84 shape is the single-branch,
outputs-only instance of the new rule, and its def came out byte-identical).

A second gate came with it: a read of a local that is not in scope now
refuses in Python (`read before it is assigned`) instead of printing an
unbound name for Lean to reject — functionalize tracks the in-scope locals
(`bound`) anyway. The manual's "one refusal delegated to Lean" is history;
the message is better and arrives earlier.

**Bool inputs.** A `logical` dummy (`IntrinsicTypeSpec -> Logical`) and a
`const bool` parameter become a parameter of type `logical`, printed as a
`Bool` binder in its own group in declaration order — `(… dt : ℝ) (vol_cfl :
Bool) (por_face_area : ℝ)` — and used as a bare guard (`if vol_cfl then`,
Lean coerces). That is the only admitted use, and it is the only one the
source type systems allow through the with-sema/clang trees anyway (a
logical in arithmetic is a sema error; a bool in a `Real` expression is an
`IntegralToFloating` cast the allowlist refuses). Logical locals and logical
outputs refuse at print. `Bool` rather than `Prop`: a runtime truth value,
decidable by construction, and the same on both sides.

**Mutable C++ locals.** `Real CFL, curv_3, h_marg, dh;` — VarDecls with no
`init` key — record the local only; `=` to a declared local is an ordinary
`Assign`; list/direct initializers still refuse. Nothing else changed on that
side: the merge machinery is shared, and `else if` — which the JSON keeps
nested in the else slot — merges recursively into the same Cond chain flang's
elseif branches produce. Both production defs came out with identical
structure.

**Dropped structs.** In whole-procedure mode a derived-type dummy the body
never references is dropped (`_kernel_from_root`), as pointize drops unused
parameters in loop mode; a referenced one still refuses at print (pinned by
`uses_grid`). This is what lines the two binder lists up positionally.

**Printer.** Binder groups by type; a `Cond` nested directly in a then-slot
is parenthesized for readability (none existed before, so no generated def
moved); output and local type gates.

Dump-shape notes (Q1 ledger): `logical, intent(in) :: vol_CFL` is
`IntrinsicTypeSpec -> Logical` + `AttrSpec -> IntentSpec -> Intent = In`; the
bare guard is `Scalar -> Logical -> Expr = 'vol_cfl'` over a plain
`Designator -> DataRef -> Name`, nothing new. clang: an uninitialized
`VarDecl` simply lacks the `init` key; `if (vol_CFL)` is an
`LValueToRValue` cast of the `DeclRefExpr` (type `bool`), so the allowlist
needed nothing.

Fixtures: `tests/f90/test_kernel_join_locals` (`face_flux`, the distilled
shape — nested joins, a merged local, a dropped local, a dropped struct,
`elemental`; `rebound_local`; refusal siblings `partial_local`,
`logical_local`, `logical_out`, `read_unset`, `uses_grid`) and
`tests/cpp/test_kernel_join_locals.cpp` (`face_flux_point`,
`rebound_local_point`, `refuse_partial_local`, `refuse_bool_local`,
`refuse_read_unset`, `refuse_list_init`). The three CW84-era join refusal
tests were retired — each of their shapes is now supported and pinned as a
golden — and replaced by the new boundary's refusal plus goldens for the
elseif chain, the bound-after-join local, the nested join, and the dropped
dead local. Manifest rows on both sides.

Proof: `Groundline/FluxElem.lean`. The two generated defs differ in exactly
one thing — the documented C++/Fortran unary-minus asymmetry in the `u < 0`
branch (`-u * dt` is `-(u * dt)` in Fortran, `(-u) * dt` in C++) — so the
point lemma is `simp only [<the two defs>, neg_mul]`, which unfolds,
zeta-reduces the lets and normalizes both spellings to `-(u * dt)`. The
kernel-level statement is the pointwise lift (per layer, `dt` and `vol_CFL`
loop-invariant), as for `ratio_max`. Retroactive check: regenerating both
modules changed no previously generated def — in particular the CW84 join
def is byte-identical under the generalized merge.

## 2026-09-05 — TIM PR 36 (the continuity mass-flux port): gap analysis, and the first construct it pulls in — function-result kernels (`ratio_max`)

**The occasion.** TIM PR 36 ("AMReX implementation of *_mass_flux") is the
merge of five sub-branches: twelve orchestration routines
(`continuity_*_convergence`, `*_flux_thickness`, `set_*_BT_cont`,
`*_flux_adjust`, `*_BT_mass_flux`, `*_mass_flux`; zonal + meridional) plus
three new per-point primitives in `mom_continuity_ppm_kernel.hpp`:
`flux_elem_point` (↔ the elemental `flux_elem`, where the PPM face-flux
physics lives), `ratio_max_point` (↔ the pure function `ratio_max`) and
`continuity_convergence_point` (↔ the convergence loop body). OBC is out of
the port's scope (it aborts on a non-null OBC pointer; every OBC branch is
commented out). Structurally the port maps Fortran's `do concurrent (j)` with
inner `do k ; do concurrent (I)` passes onto a 2-D `ParallelFor` over (i,j)
with a sequential `for k` inside, fusing several Fortran k-loops into one —
order-preserving in k, so real-number equivalence holds, but a proof has to
absorb the fusion.

**Step 0 — the refusals scoped it.** A scratch probe manifest ran both
extractors on the production dump and the PR's header. Nothing passed. First
refusal per side: `flux_elem` — `intrinsic type 'Logical'` /
`parameter 'vol_CFL': type 'const bool'`; `ratio_max` — `found 0 definitions`
(a *function*, not a subroutine) / `kernel must return void`;
`continuity_zonal_convergence` nest 1 — `references 'hin' — attribute
'Optional'` / `must return void`; `zonal_flux_thickness` nest 1 — `call to
'present'` / no point function at all (the body is inlined in the lambda);
the column kernels — `present`, `CallStmt` (calls to `flux_elem`), chained
OBC components / 2-D lambdas carrying `for k` folds.

**The plan, in tiers** (recorded here so the next entries have a frame).
*Tier A — the three primitives*, each a bank-kernel job: A1 `ratio_max`
(function results on both sides — this entry); A2 `flux_elem` (logical/bool
parameters used as bare conditions, the if/elseif join with locals assigned in
branches and read after — a widening of the deliberately restricted join,
i.e. a semantics decision for the user — and C++ declared-uninitialized locals
assigned later); A3 `continuity_convergence` (`optional` on an intent(in)
dummy, the read-only neighbor stencil `uh(I-1,j,k)` → a synthesized input as
the Limits page sketched, component arrays indexed by a *subset* of the loop
indices, nest-invariant locals set before the loop as inputs, `amrex::max`).
*Tier B — the column kernels* (`zonal_BT_mass_flux` → `set_zonal_BT_cont` →
`zonal_mass_flux`'s j-body). The key observation: **both sides iterate k
sequentially in the same order** — Fortran's `do k ; do concurrent (I)` is,
per column, a sequential fold over k, and so is the C++ `for k` — so the
honest model on both sides is a fold over k with a per-column state tuple,
and equivalence is fold-congruence from step-equivalence (plus one
fold-fusion lemma for the C++'s fused loops). That is *not* the
sequential-vs-unordered question the Limits page reserves for reductions;
the order is shared. Also needed there: calls to banked primitives as
applications of their generated defs (composition through Tier A's
theorems), masks on `do concurrent`, `present(x)` as a Bool input (constant
per call, exactly the C++'s `.p != nullptr` flags), manifest-declared
hypotheses that prune dead OBC branches and appear in the theorem, and C++
lambda extraction. *Tier C* — `*_flux_adjust`, a 20-step Newton/bisection
fold with per-column convergence flags (Fortran exits the row when no column
is active, the C++ freezes columns individually) — deferred to the PR's
capture tests. One review suggestion for the PR: factor `*_flux_thickness`'s
lambda body into a `flux_thickness_point` primitive (it is `flux_elem`'s
`h_marg` / bracket math behind a `marginal` switch); that alone makes it
provable with the existing C++ frontend.

**A1 landed — function-result kernels.** The kernel IR's second calling
convention: a Fortran `function … result(r)` and a `Real`-returning C++
point function extract as kernels whose single output is the result.

Semantics decisions, and why:

- **A result is the sole output, and the caller supplies no value for it.**
  An `inout`/`out` argument arrives holding the caller's value, which the body
  may read; a result variable starts undefined. It travels as a
  `Param` of intent `result` (appended after the dummies); `functionalize`
  starts it *unbound* rather than at `Var(r)`, so three shapes refuse that a
  plain `inout` would silently model: a read before the first assignment
  ("read before it is assigned"), a control-flow path that never assigns it
  ("not assigned on every control-flow path" — the source returns an
  undefined value there), and a joined IF assigning it on one side only. The
  read-before-assign case could have been left to Lean (an unbound name), as
  the local-read gap is; it is refused in Python because it is cheap and
  the message is better. A result alongside `inout`/`out` outputs refuses on
  both sides ("two output conventions") — one output channel per kernel,
  which keeps the theorem statement shape uniform.
- **Naming.** Fortran supplies the name (`result(ratio)`); the C++ return
  value has none, so it is named after the function — Fortran's own default
  for a result variable — and collision-checked against parameters and
  locals. The name only ever appears in the doc comment: the printed def's
  binder list carries the *inputs* only (`def ratio_max (a b maxrat : ℝ) : ℝ`),
  the first def whose signature is not "outputs are also inputs".
- **C++ `return` only in tail position** — the last statement of the body or
  of a branch of an `if` that is itself in tail position — so every path ends
  in exactly one return. An early return refuses at extraction; a tail `if`
  without `else` extracts and then refuses in `functionalize` (the
  fall-through path never assigns the result) — one gate, both languages.
- **Prefixes.** `SubroutineStmt`/`FunctionStmt` prefixes were never looked at
  (no banked kernel had one). Now an explicit allowlist: the keyword prefixes
  `Pure`, `Elemental`, `Impure`, `Recursive`, `Non_Recursive`, `Module`
  constrain how a procedure may be used without changing what its body
  computes and are read past; a `DeclarationTypeSpec` prefix
  (`real(8) function f(a) result(r)`) declares the result's type outside the
  specification part and refuses rather than being dropped. Elemental is
  admitted now because it is a keyword like the others, not because a kernel
  needs it yet (`flux_elem` will).
- **A function without a `result` clause refuses** — the function name
  doubling as the result variable is a different declaration story;
  unsupported until a kernel needs it.

Considered and ruled out: a `Kernel.result` field (a `Param` intent keeps the
`Kernel` shape and both frontends' seam unchanged; `functionalize` already
keyed outputs on intent); admitting no-`result`-clause functions
(unexercised); refusing the C++ tail-`if`-without-`else` at extraction
(functionalize's every-path gate already says exactly why).

Dump-shape notes (Q1 ledger): a `FunctionStmt` lists its dummies as **bare
`Name` children** after the function's own name, where `SubroutineStmt` wraps
them in `DummyArg -> Name`; the result sits under `Suffix -> Name`; `pure` is
`PrefixSpec -> Pure`; a type prefix is `PrefixSpec -> DeclarationTypeSpec ->
IntrinsicTypeSpec -> Real`. clang side: `ReturnStmt` has exactly one child
expression, and `return maxrat;` for a `const Real` by-value parameter
carries only `LValueToRValue` (no `NoOp` qualification cast) — the cast
allowlist needed nothing; the function's `qualType` reads
`Real (const Real, const Real, const Real) noexcept`.

Fixtures: `tests/f90/test_kernel_function` (`capped_ratio` — the supported
shape with a local — plus five refusal siblings: no result clause, type
prefix, result unassigned on a path, result read before assignment, an
`intent(inout)` dummy alongside the result) and
`tests/cpp/test_kernel_function.cpp` (`capped_ratio_point` plus `refuse_*`:
early return, tail if without else, `Real&` alongside a return value, bare
`return` in a void kernel). Regenerating the f90 corpus left every existing
dump byte-identical (same flang; only `PROVENANCE`'s timestamp moved).
Manifest rows in both `MANIFEST.md`s; 19 new tests.

Proof: `Groundline/RatioMax.lean`. The two generated defs are identical
modulo name (`if |a| > |maxrat * b| then maxrat else a / b`), so the point
lemma is `rfl`; the kernel-level statement is the pointwise lift over any
index set (`funext`), which is how the mass-flux callers use it — one
evaluation per column — and all the point subset can say about them today.
Retroactive check: regenerating both modules changed **no previously
generated def** (`GeneratedFtn.lean` and `GeneratedCpp.lean` each grew by
exactly the new def) — even though the C++ side now reads the PR's header.

Practical notes. The production manifest's C++ sources are the TIM submodule
(`submodules/infra/TIM`, remote `mwaxmonsky/TIM`, HEAD `fe721eaa`, which is
not on TURBO-ESM `main`), which predates the PR; with the user's OK the
submodule working tree was checked out at PR 36's head (`pull/36/head`,
`3f46e261`) so `generate`/`verify` see `ratio_max_point` without touching the
manifest. The submodule pointer change is deliberately *not* part of this
work's commit — revert with `git checkout fe721eaa` in the submodule, or bump
it once the PR merges. The production dump (2026-05-28) is current for
`MOM_continuity_PPM.F90` (last source change 2026-05-20).

## 2026-08-01 (later still) — A wrong-model bug found by a precedence question: integer values now refuse

A user question — "does Fortran/C++ operator precedence differ, and does the
printer account for it?" — audited well (precedence is consumed by each
compiler's own parser; the printer only owes *Lean's* precedence, which it
pays with the `_BIN` table and defensive `Neg` parens), until the "other
differences?" sweep found a real hole: **Fortran integer division inside a
real expression extracted and printed with no refusal.** `b = b + a * (2/3)`
became `b + a * (2 / 3)` over ℝ — but Fortran computes `2/3 = 0`. A
plausible-but-wrong model, the exact failure mode the refusal discipline
exists to prevent. The C++ twin was already safe: clang wraps the int result
in `IntegralToFloating`, which the cast allowlist refuses.

Fix (refuse, don't model — for now): the printer gained two gates. `div`/
`pow` with both operands built from integer literals refuses ("integer-valued
'/': the source evaluates this in integer arithmetic…"), and a non-real
*local* in the modeled body refuses like non-real params always did (an
integer local modeled as ℝ would hide truncation in its assignments).
Integers as addresses — indices, bounds, subscripts — are untouched;
pointize consumes them. Fixture `tests/f90/test_kernel_intarith` pins both
refusals end to end.

Why refuse rather than model faithfully (the user pushed on this, rightly):
Lean's `Int.div` does truncate toward zero, but faithful integers are a
modeling *project* — conversion-point placement, the MOD family, C++ signed
overflow (UB: no faithful total function exists), and mixed ℤ/ℝ defs that
break the uniform `rfl`/`ring` proof story — all for machinery no banked
kernel exercises. Unexercised semantics in the trusted base is where wrong
models hide. Recorded as a Limits roadmap item ("Integer values in kernel
bodies"), alongside a new "read-only stencils" item from the same
conversation: neighbor reads (`a(i-1)`) refuse at the array-index gate, not
the integer gate, and their admission path (synthesized per-offset inputs,
an environment-threading schema-lemma variant) is much cheaper than the
k-recurrence frontier. 199 tests green; nothing banked was affected.

## 2026-08-01 (later) — Fortran source mode: flang runs on demand, like clang; the quickstart goes all-source

Third revision pass, closing the last asymmetry the schema-v2 round left
open: the quickstart's Fortran side still pointed at a *committed* dump
(`toy_kernel_ptree` + `PROVENANCE`) while its C++ side named a source and
ran clang fresh — and the `[[kernel]]` key `file` meant "a dump" on one side
and "a source" on the other.

- **Source mode.** `FortranKernelSpec` (and the manifest) now take exactly
  one of `dump` (a pre-generated with-sema dump — for kernels inside
  codebases whose `.mod` environment must be built first) or `source` (a
  standalone Fortran file; `flang_kernel.dump_parse_tree` runs
  `flang -fc1 -fdebug-dump-parse-tree` on it in a temp cwd — no `.mod`
  litter — and parses the dump in memory). The cpp key `file` was renamed
  `source` to match; `[fortran]` gained `sources` and `compiler` mirroring
  `[cpp]`. The ambiguous `file` key is gone from the schema.
- **Provenance symmetry.** When any Fortran kernel is source-mode, the
  generated module header stamps the flang version + invocation — exactly
  the clang discipline. The dump-vs-source workflow story in
  `frontends.md` is now per-*kernel*, not per-language: standalone files
  run their compiler on demand on either side; built-codebase kernels are
  the reason dump mode exists.
- **Quickstart symmetric and pair-first.** Both sides now source mode
  (`toy_kernel.f90` / `toy_kernel.cpp`; committed dump + PROVENANCE
  deleted; requires flang like it always required clang). The loop variant
  moved out of the head-on flow entirely — its own `toy_kernel_loop.f90`
  and a closing manual section ("And when the Fortran kernel is a loop?")
  that banks it live: refusal without `pointize = true`, the extracted
  per-point def with it (both captured, both pinned by honesty tests). The
  committed manifest, generated modules, equiv theorem, and axioms audit
  carry only the point pair.
- A rank-0 fixture (`tests/f90/test_kernel_rank0`) replaced the quickstart
  dump in the pointize-gate tests, keeping them toolchain-free; the
  quickstart goldens are now flang-gated and compare defs (headers stamp
  local compiler versions). 196 tests green; both manifests verify end to
  end (801 Lean jobs); production generated files unchanged byte for byte
  under the key rename.

## 2026-08-01 — Quickstart rebuilt around symmetry; loop/point boundary made explicit; manifest schema v2

A second user-driven revision pass, this time reaching into semantics.

- **The loop/point boundary is now explicit.** Previously the Fortran side
  was always pointized — a loop kernel silently became a point function.
  New default: a loop-nest kernel *refuses* at extraction ("a loop nest is
  not the same thing as a point function"), and the manifest entry must
  carry `pointize = true` to license the reduction. The option refuses on a
  non-loop kernel. All five production kernels are loops → all five carry
  the license, stated in the manifest. Loop-vs-loop comparison (a C++ `for`
  frontend + pointize on that side) is recorded as roadmap in the manual.
- **Rank-0 Fortran kernels are now supported.** A per-point subroutine
  (scalar args, no loop) extracts as written — `kir.is_loop_nest` decides,
  and `extract_fortran_entry` skips pointize. This is what makes a genuinely
  symmetric quickstart possible.
- **The quickstart is symmetric and complete.** Fortran side is now a
  per-point subroutine `scale_clip_acc` plus a loop variant
  `scale_clip_acc_loop` (same dump, both banked; the loop entry demonstrates
  the refusal-then-license flow with a captured snippet). The C++ side is a
  plain `.cpp` with `double` — no header, no `using Real = double;` (the
  clang frontend now accepts the `double`/`const double`/`double &`
  spellings alongside amrex's `Real`), no AMReX/MPI anywhere near the page.
  The generated modules land in the Lean project
  (`Groundline/QuickstartFtn.lean`, `QuickstartCpp.lean`) with a committed
  `QuickstartEquiv.lean` (both theorems `rfl`, audited) — so `verify` in the
  quickstart now runs the FULL gate including `lake build`, and the manual
  shows the real theorem file instead of "we checked it while writing this
  page". 801 jobs green.
- **Manifest schema v2 (role-named keys).** `corpus` → `dumps`, `out` →
  `generated`, `header_dir` → `sources`, `clang` → `compiler`, `lake_dir` →
  `project`, per-kernel `dump`/`header` → uniform `file`, new per-kernel
  `pointize`. API fields renamed to match (FortranConfig.dumps/.generated,
  CppConfig.sources/.compiler/.generated, Manifest.lean_project,
  CppKernelSpec.source/.compiler, KernelEntry.fortran_label/.cpp_label/
  .pointize). Env var `GROUNDLINE_CORPUS` → `GROUNDLINE_DUMPS` (no
  back-compat, per the naming precedent). "corpus" retired from prose in
  favor of "dump directory / dump collection"; docs/ keeps the old term
  historically.
- **`verify` says what it did and didn't check.** New note when the
  manifest names no `[lean]` project ("the generated models were checked,
  but no theorems were"); the proof-check messages name the stage instead
  of just "lake build". Manifest `_path` now normalizes lexically so CLI
  output shows clean paths.
- **Manual precision pass** (from a criticized quickstart paragraph,
  generalized): the verify explanation now spells out what is regenerated,
  what it is compared against (the `generated` files on disk — version
  control recommended, not required), what happens without `[lean]`, and
  what "every theorem" means; the quickstart states plainly that the
  theorem file is the user's to write (once per kernel, patterns
  documented); "banked/corpus/committed" jargon defined or replaced at
  first use. Snippet renderer gained the pointize-refusal capture and a
  documented one-line elision of the audit replay in the verify snippet
  (lake re-prints all ~40 audit lines every build — right for CI logs,
  noise in a quickstart); `tests/test_manual.py` pins the new snippet.
- **Trim:** the printer's emitted linter-option comments lost their
  defensive tone ("…unused by design" → two matter-of-fact lines).

Suite: 188 pytest green (new: pointize-gate refusals, rank-0 extraction,
verify-note, refusal-snippet pin); production + quickstart `verify` green
end to end; `mkdocs build --strict` green.

---

## 2026-08-01 — Manual revision: "Track B" and "pilot" retired, `GeneratedFtn`, conda env, reframed related work

A user-driven revision pass over the manual and the naming it exposed.

- **"Track B" retired from all user-facing naming.** The label meant nothing
  to anyone outside the project. The user-facing name is now plain **kernel
  verification** (short form in prose: *the kernel track*, alongside *the
  relational track*); docs/ keeps "Track B" as the historical/internal term.
  CLI help, Python docstrings, fixtures' comments, the skill, mkdocs site
  name, and the manual all updated.
- **"Pilot" retired as a structural name.** The Lean project outgrew its
  pilot-era identity (5/5 kernels banked, mature no-hand-models pattern).
  Combined with the point above: `lean/pilot` → **`lean/groundline`**, module
  `Pilot` → **`Groundline`**, and every Lean namespace moved from `TrackB.*`
  to `Groundline.*` (e.g. `Groundline.GeneratedFtn.ppm_limit_pos`). The word
  "pilot" survives only as history in the PPM_limit_pos case-study narrative.
- **Symmetric generated-module names.** `Generated.lean` → `GeneratedFtn.lean`
  and `Fidelity.lean` → `FidelityFtn.lean`, mirroring `GeneratedCpp.lean` /
  `FidelityCpp.lean`; namespaces `Groundline.GeneratedFtn` and
  `Quickstart.GeneratedFtn`. Both manifests, the regenerated modules, all
  proofs, the audit, tests, the bank-kernel skill, and the snippets updated.
- **Conda distribution.** New root `environment.yml` (`conda env create -f
  environment.yml` → env `groundline`, editable pip install of the package);
  the manual, README, and PUBLISHING now lead with it, venv demoted to an
  aside with `PYTHONNOUSERSITE=1` as troubleshooting.
- **Manual reframing.** (1) Application-agnostic: concepts/how-tos/reference
  now describe the method generically; MOM6/TIM/TURBO appear as *the case
  study*, not as the definition of the tool. (2) Related work: Logos
  Research's migration-by-proof is presented as closely related parallel
  work with the shared load-bearing ideas listed (no LLM in the pipeline,
  auditable generated Lean, equivalence over ℝ) rather than as the template
  the project "follows" — much of that philosophy is the project's own
  (reals-first, VSS 2025). (3) A new frontends-reference section answers why
  the two frontends read different formats (flang has no JSON AST dump;
  clang's JSON *is* its post-sema tree; the committed-vs-on-demand workflow
  split is forced by `.mod`-ordered Fortran builds vs standalone C++
  headers — both sides consume the same thing, a post-sema syntax tree).
  (4) Tone pass throughout: installation "tiers" became plain levels, the
  slogan-y phrasings ("deliberately usable", "be honest with yourself",
  "the method's honesty made visible") rewritten in plain language,
  "honest/honestly" trimmed to its technical uses.
- **One mechanical surprise:** `lean` renders `#print axioms` messages at a
  fixed 120-column width (no option reaches it — `format.width` via
  `set_option` and `-D` were both tried and ignored for message rendering),
  and `Groundline.GeneratedCpp.thickness_to_dz_3d_nonboussinesq_point` is
  long enough to wrap. `render_snippets.sh` now rejoins indented
  continuation lines so the audit snippet keeps one declaration per line;
  `tests/test_manual.py` pins the result.

Verification after the renames: full `lake build` green (798 jobs), `kernel
verify` green end to end (byte-diffs + Lean), 184 pytest green, `mkdocs build
--strict` green.

---

## 2026-07-31 — flinspect → groundline: the rename, applied

**What:** the tool, package, and CLI are renamed **flinspect → groundline**,
applied in the manual session before its commits landed (so the manual ships
under the new name). Why the old name had to go: it hard-codes *flang* when
the pipeline has ingested clang ASTs since the Track B clang frontend, and
"inspect" undersells what Track B does. Why *groundline*: the glaciology
**grounding line** — where floating ice meets bedrock — is the boundary this
tool draws through a codebase (what floats: `assumed`/`unresolved`, untested
ports; what rests on bedrock: sema-resolved facts, Lean-proved equivalences),
and "ground graph" was already the relational track's own vocabulary. Naming
history: *soundline* was chosen first and rejected the same day (three active
software companies, an audio-polluted namespace); *groundline* verified clean
— PyPI available (unclaimed), sole collision a power-lines engineering firm.

- **Scope applied:** package dir `flinspect/` → `groundline/` (git mv) + all
  imports; pyproject name, console script (`groundline = groundline.cli:main`),
  and description (no longer "flang-based"); the CLI's `--help` description;
  env vars renamed **without back-compat** per the user's call —
  `GROUNDLINE_CORPUS` / `GROUNDLINE_KERNELS`; `FLINSPECT_*` is no longer
  honored anywhere. The checkout directory moved to `dev-utils/groundline`
  (grep confirmed zero references to the old path anywhere in the parent
  turbo-stack repo); venv recreated at the new path; the stale Jupyter
  kernelspec migrated. All URLs now `alperaltuntas/groundline` — the GitHub
  repo rename itself (auto-redirecting) is on the user, before enabling Pages.
- **Generated artifacts, regenerated not sed-trusted:** the four generated
  Lean modules (pilot + quickstart `Generated.lean`/`GeneratedCpp.lean`) carry
  provenance blurbs naming `groundline.lean_printer` and `groundline kernel
  generate`; after the code rename, `groundline kernel verify` confirmed the
  updated committed files match a fresh regeneration **byte-for-byte** on all
  four (defs untouched — the rename changed header comments only), and `lake
  build` re-checked the proofs. Manual snippets all re-rendered under the new
  CLI (`render_snippets.sh`); the manual-honesty tests re-pin them.
- **What was deliberately NOT renamed:** DEVLOG entries below this one
  (append-only; a header note now flags the old name), and the historical
  narratives inside them. `docs/VISION.md`/`DESIGN.md` are living documents
  and were updated in place.
- **Environment note (the same trap, third sighting):** the first
  `kernel verify` after the rename ran with the bare elan `lake` shim on PATH
  and failed with the home-quota error — activating the Lean env
  (`activate_lean.sh`) before the lake tier remains mandatory; the snippet
  script's temp-file guard kept the committed axioms snippet intact, as
  designed.

---

## 2026-07-31 — Track B conclusion (2 of 2): the user manual (MkDocs Material + GitHub Pages)

**What:** docs only — a comprehensive user manual for Track B, built with
MkDocs Material (site source `manual/`, config `mkdocs.yml` at the repo root;
`docs`/`VISION`/`DESIGN`/`DEVLOG` stay the engineering record, linked from
the site but not absorbed). Published via a GitHub Pages workflow
(`.github/workflows/docs.yml`: `configure-pages` → `upload-pages-artifact` →
`deploy-pages` on pushes to main); enabling Pages needs one-time repo-admin
setup, checklisted in `PUBLISHING.md` (Settings → Pages → Source = "GitHub
Actions"; repo must be public or on a paid plan). Site URL will be
https://alperaltuntas.github.io/flinspect/ — internal links are all relative,
so the URL choice can't break the site. README gained the site link + a
one-paragraph Track B blurb (nothing else touched). Packaging: a `docs`
optional extra (`mkdocs-material>=9,<10`).

- **Structure (27 pages):** Home (what the theorems mean and deliberately do
  NOT mean, prominent; Logos "migration by proof" + reals-first VSS 2025
  lineage credited) · tiered Installation (pip / +flang / +clang / +Lean,
  each tier's unlock stated) · Quickstart (the `examples/quickstart` walk,
  end to end) · six Concepts pages written for a scientific-software reader
  who hasn't seen Lean (two-IR architecture, kernel IR + refusal discipline,
  pointize with the assertion-vs-proof licensing story, functionalize + the
  join, the printer's fidelity contract, trusted base + axioms audit) · five
  How-tos (bank a pair, inline-loop addressing, extend the subset via the D7
  workflow, port to a new LLVM, wire `verify` into CI) · four Case studies
  retold from this DEVLOG as narratives with the real theorem names and
  axiom audits (the pilot & why `rfl` is the strongest no-drift statement;
  CW84's join **including the functionalize.subst aliasing bug, told
  honestly**; thickness_to_dz's assertion-vs-proof symmetry;
  edge_thickness_upwind's ordinal addressing + the find_dz_for_eta refusal
  as the boundary) · Reference (manifest schema, CLI with real `--help`
  output, kir API, both frontends, printer behavior, Lean project layout,
  and the **complete refusal catalog** — all 77 `raise UnsupportedConstruct`
  sites, grepped and organized by stage) · Limits & roadmap (reductions/
  k-recurrences/masks as the frontier, permanent scope boundaries restated)
  · a one-page relational-track stub ("documented after its CLI lands").
- **Honesty mechanics.** The site build is fully static — no flang, clang,
  Lean, or corpus at build time. Every command output shown is real,
  pre-rendered THIS session from the real pipeline into committed snippet
  files (`manual/snippets/*.txt`), embedded via `pymdownx.snippets`, and
  reproducible: `manual/snippets/render_snippets.sh` regenerates all of them
  (quickstart list/show/generate/verify, CLI help, production list + a CW84
  show, the k-recurrence refusal via a temp manifest, and the axioms audit
  from a fresh `lake build` + `lake env lean Pilot/AxiomsAudit.lean` — 798
  jobs, all 31 declarations `[propext, Classical.choice, Quot.sound]` or
  documented subsets). `tests/test_manual.py` (+5 tests; clang-gated where
  needed) pins the snippets against fresh runs: the quickstart `show` output
  byte-compares, the refusal line reproduces through the real CLI error
  path, and the axioms snippet must list exactly `AxiomsAudit.lean`'s
  declarations with only the standard axioms. The quickstart page also
  includes `Generated.lean` straight from the repo file (cannot rot vs the
  file; `verify` pins the file vs regeneration). The toy equivalence theorem
  shown in the quickstart was actually compiled (`lake env lean` on a scratch
  file; `rfl`, standard axioms) before being quoted.
- **Verification:** `mkdocs build --strict` green; suite 179 → 184 with
  gates on, bare mode 171 pass / 13 skip (gated tests still skip, never
  fail); manual quotes checked against the real MOM6 source where DEVLOG
  wasn't verbatim (CW84 loop body, upwind bounds `i=ish-1:ieh+1`,
  find_dz_for_eta's recurrence line).
- **Findings recorded, not fixed** (docs task — package untouched beyond the
  `docs` extra + honesty tests):
  - (a) `kernel verify`'s C++ tier byte-diffs the whole module, whose header
    stamps the clang version — so full C++ `verify` passes only under the
    pinned clang. Correct per the toolchain-is-provenance design, but a
    portability wart for CI on other runners (the manual documents the
    pytest-golden workaround, which compares defs only). A future
    `verify --defs-only` (or diffing below the header) may be worth it.
  - (b) `kernel list` prints unnormalized output paths from relative
    manifest entries (`.../examples/../lean/pilot/...`) — cosmetic.
  - (c) The bare-elan-shim failure mode (entry 1-of-2) bit again while
    rendering snippets: a `lake` on PATH without a provisioned toolchain
    produced an empty axioms snippet before the script was hardened to write
    through a temp file and keep the committed copy on failure.
- **Not done, deliberately:** no aspirational content — roadmap items are
  labeled roadmap on one page (`limits.md`); the relational track got a stub,
  not a manual; no package/proof changes.

---

## 2026-07-31 — Track B conclusion (1 of 2): manifest, uniform frontend seam, `flinspect kernel` CLI, bare-clone portability

**What:** packaging, not proof content — the kernel-verification pipeline is
now config-driven, uniform across the two frontends, and driven by a console
script. The load-bearing invariant, checked rather than claimed: across the
whole migration **every generated def is byte-identical**; only the module
header comments changed (the "Regenerate with ..." provenance lines now name
the new command). `lake build` green after regeneration (798 jobs, axioms
audit clean). Tests 151 → 179 with gates on (167 pass / 12 skip bare — the
gated tests skip, never fail).

- **Kernel manifest (`kernels.toml`).** The banked pairs, previously two
  differently-shaped hardcoded lists in `lean/pilot/generate.py` (now
  deleted), are a declarative TOML file parsed with stdlib `tomllib` (no new
  deps). Schema (documented in `flinspect/kernel_bank.py`): `[fortran]`
  corpus/out/namespace (+ optional blurb), `[cpp]` header_dir/include_dirs/
  clang/out/namespace (+ optional provenance_root, so header paths display
  relative to a chosen root — what keeps the generated doc comments
  byte-stable across machines), optional `[lean] lake_dir` for the verify
  gate, and one `[[kernel]]` table per pair — `fortran = { dump, subroutine
  [, nest] }` (rule-B inline loops take the entry's `name` as the generated
  def name), `cpp = { header, function }`. String values expand `${ENV_VAR}`
  (unset refuses); relative paths resolve against the manifest's directory;
  unknown keys refuse (the manifest is trusted-base adjacent: refuse, don't
  guess). Resolution order everywhere: `--kernels` flag >
  `$FLINSPECT_KERNELS` > `./kernels.toml`. **There is no built-in /glade
  default anywhere anymore** — the machine paths moved into the committed
  production instance `examples/turbo-stack.kernels.toml`, and
  `grep -rn glade --include='*.py'` is clean.
- **Uniform frontend seam.** `frontend/kernel_base.py` mirrors the relational
  `Frontend` protocol for Track B: `KernelFrontend.extract(spec) -> Kernel`,
  with typed specs — `FortranKernelSpec(dump, subroutine, nest?, def_name?)`
  (whole-subroutine and rule-B inline-loop addressing folded into one path;
  the spec validates that nest and def_name travel together) and
  `CppKernelSpec(header, function, include_dirs, clang)` (the clang
  invocation config moved out of function kwargs into the spec — the
  toolchain is part of the kernel's address). `FlangKernelFrontend` /
  `ClangKernelFrontend` implement it; the old module-level functions remain
  as the implementation and stay importable (the fixture tests pin them
  directly; equivalence of the two paths is itself pinned in
  `tests/test_kernel_bank.py`).
- **Library + CLI.** `flinspect/kernel_bank.py` owns manifest loading and the
  extract-both-sides → render-both-modules pipeline; `flinspect/cli.py` +
  `[project.scripts]` provide the `flinspect` console script (argparse only,
  widget-free — pinned by a subprocess test) with the `kernel` group:
  `list` (entries + basic status), `show NAME` (both generated defs, C++
  side skipped with a note when clang is absent), `generate`
  (`--skip-fortran/--skip-cpp`), and `verify` — regenerate, byte-diff
  against the committed files (drift → non-zero exit + a diff excerpt +
  the fresh copy parked in a temp file), then `lake build` in `[lean]
  lake_dir` when `lake` is on PATH (clear note when absent). `verify` is
  Track B's CI gate. `cli.py`'s `main()` marks where the relational track's
  `check`/`report` groups plug in as siblings (phase45_prompt.md updated
  accordingly, as was the bank-kernel skill). One environment honesty note:
  a bare elan `lake` shim on PATH without a provisioned toolchain fails the
  gate loudly (observed: elan tried to download a toolchain into the
  quota-full home dir) — activating the Lean env first (`activate_lean.sh`)
  is what makes the lake tier meaningful.
- **Quickstart (`examples/quickstart/`) — the committed portability proof.**
  A toy in-subset pair: `toy_kernel.f90` (do-concurrent point kernel) with
  its with-sema dump COMMITTED next to it (+ `PROVENANCE`, mirroring
  `tests/f90`'s convention — the Fortran side works with pip alone, no
  flang), and `toy_kernel.hpp`, a deliberately standalone header (`using
  Real = double;`, reference params, zero includes). The clang frontend
  needed **no changes** for the AMReX-free header — as hoped, the intent
  mapping keys on the `Real &`/`const Real` qualType spellings, not on
  where the alias comes from; no portability bug existed. Its generated
  Lean modules are committed and golden-tested everywhere (the C++ golden
  compares defs only — the module header stamps the local clang version by
  design). The two toy defs come out with identical bodies, which makes the
  quickstart a readable demo of what the production instance proves in Lean.
- **Bare-clone acceptance (the definition of done), executed:** the repo
  cloned to a scratch directory outside turbo-stack, a fresh venv,
  `PYTHONNOUSERSITE=1 pip install -e .`; then, in the clone's quickstart:
  `flinspect kernel list` / `show` / `generate --skip-cpp` / `verify
  --skip-cpp` all green *without* clang (the C++ side degrades to a clear
  note), and with clang 21 activated, full `generate` + `verify` green.
  Clone suite: 178 pass / 1 skip (the corpus golden, `FLINSPECT_CORPUS`
  unset — correct). Real-repo suite with gates on: **179 pass, 0 skip**;
  baseline 151 not regressed.
- **Not done here, deliberately:** no `check`/`report` CLI (relational
  Phase 4 extends this same script), no user manual (next session), no new
  proof content, no dependency changes.

---

## 2026-07-31 — Track B 5-of-5: the remaining TIM point kernels banked; plain DO licensed by proof

**What:** the three remaining TIM point kernels —
`edge_thickness_upwind_point`, `thickness_to_dz_3d_boussinesq_point`,
`thickness_to_dz_3d_nonboussinesq_point` — extracted from the production
dumps, generated into `Pilot/Generated.lean` / `Pilot/GeneratedCpp.lean`, and
proved equivalent, closing out the **current TIM kernel population (5 of 5)**.
Two extraction extensions carried the load; both widen WHERE a Fortran kernel
may live and WHAT it may reference — not what its body may compute. The two
already-banked kernels' generated output is **byte-identical** before and
after — the diff of both generated files is purely additive (checked line by
line): the appended defs, plus one new documented `set_option
linter.unusedVariables false` in the generated header (kernels like upwind
never read an output's incoming value, so its binder is unused by design —
mirroring the existing longLine rationale comment). The extensions change
nothing retroactively.

- **Rule A — plain-DO pointization, licensed by a proved schema lemma, not by
  assertion.** The two-layer design, and the layer split matters:
  * *Python side (the extraction gate, `kir.pointize`):* a plain, PERFECTLY
    nested `do` nest (each level's body exactly one inner `do` until the
    innermost) pointizes under the same check as `do concurrent` — every
    array reference indexed exactly by the loop indices — plus a write gate
    the plain path alone needs: every write must land in the iteration's own
    array cell, so an assignment to a scalar parameter (`s = s + a(i)`, the
    accumulator/reduction shape) refuses, as do imperfect nests, strides, and
    duplicate indices. The gate is NOT the semantic justification; it is what
    guarantees the lemma's setting applies.
  * *Lean side (the semantic license, `Pilot/SeqSchema.lean`):* a plain DO's
    honest semantics is a *sequential fold* of per-point updates over an
    enumeration of the index box — so that is what the kernel-level theorems
    model (`foldSeq`), and the license to equate it with the pointwise map is
    the once-and-for-all schema lemma `foldSeq_eq_pointwiseMap`: for any
    point function `f` and any duplicate-free, complete enumeration,
    `foldSeq f s₀ enum = pointwiseMap f s₀`. Proof shape as planned —
    induction over the enumeration with a frame argument (`foldSeq_frame`:
    cells not in the enumeration are never written; under `Nodup`, iteration
    `i` finds cell `i` pristine, writes land in disjoint cells, the fold
    telescopes to the map). The lemma is fully general (`f : ι → σ → σ`,
    any state type σ — no arity specialization was needed): once pointize
    has produced `f`, point-locality is baked into `f`'s *type*, so the
    hypothesis is structural, not re-checked per kernel.
  * *The symmetry worth recording:* for `do concurrent` we accept the
    source's independence assertion as the license for `pointwise`; plain DO
    gets a *proof* instead of an assertion — equal (arguably better)
    footing. Reductions and recurrences remain refused: they are not
    point-local, and their sequential-vs-unordered question is real
    mathematics reserved for a future step.
- **Rule B — inline-loop addressing + component reads.**
  * *Addressing:* `flang_kernel.extract_loop_kernel(dump, subroutine, nest,
    name)` extracts loop nest #N of a subroutine — the dump carries no line
    numbers, so the deterministic address is the source-order ordinal among
    the subroutine's outermost do-constructs (both do-concurrent and
    plain-DO nests count; the walk descends into IF branches but never into
    a do-construct). The generated def's name is driver-supplied — an inline
    loop has no name of its own — and `KERNELS` records the pairing. The
    enclosing subroutine's SpecificationPart supplies declarations,
    *tolerantly*: a declaration outside the subset (`character` message
    buffers, `optional`/`pointer` attrs, `logical` locals) poisons only its
    own names, and extraction refuses iff the nest references one. The
    whole-subroutine mode is unchanged.
  * *Component reads:* exactly two shapes become synthesized scalar `in`
    params of the pointized kernel — a loop-invariant scalar component
    (`GV%H_to_Z` → `h_to_z`; loop-invariant because the base must be an
    `intent(in)` derived-type dummy, which Fortran forbids modifying, and
    component writes refuse) and a component array indexed exactly by the
    loop indices (`tv%SpV_avg(i,j,k)` → `spv_avg`). Naming is the component's
    own name, deterministic and collision-checked (refuse, never rename);
    synthesized params append after the real params in first-use order.
    Everything else refuses (offset subscripts, non-`intent(in)` bases,
    chained `a%b%c`). The mapping rule — including that the synthesized param
    is *modeled as a real scalar*, with the by-eye audit covering the
    component's actual type — is recorded in `kir.py`'s docstring as part of
    the model's meaning. In the kernel-level theorems the mapping surfaces
    exactly as intended: `h_to_rz` is captured loop-invariantly, `spv_avg`
    is fed per cell (`spv i`).
- **The branch ↔ kernel pairings** (and two source discrepancies vs the task
  prompt, recorded per trust-the-source):
  `MOM_interface_heights.F90` lives in **`MOM6/src/core/`**, not
  `src/framework/`; and `thickness_to_dz_3d` carries **both** a
  do-concurrent and a plain-DO variant of each branch under its
  `do_offload`/`use_doconcurrent` guard (the prompt described only the plain
  ones). Nest ordinals in source order: 1 = do-concurrent non-Boussinesq,
  2 = plain-DO non-Boussinesq, 3 = do-concurrent Boussinesq, 4 = plain-DO
  Boussinesq. Banked (the plain-DO variants — the default execution path,
  `do_offload` absent/false — and the ones rule A exists for):
  * `thickness_to_dz_3d_boussinesq_point` ↔ `thickness_to_dz_3d` nest 4, the
    plain-DO loop of the else (Boussinesq or no SpV_avg) branch:
    `dz(i,j,k) = GV%H_to_Z * h(i,j,k)`.
  * `thickness_to_dz_3d_nonboussinesq_point` ↔ nest 2, the plain-DO loop of
    the `(.not.GV%Boussinesq) .and. allocated(tv%SpV_avg)` branch:
    `dz(i,j,k) = GV%H_to_RZ * h(i,j,k) * tv%SpV_avg(i,j,k)`.
  * `edge_thickness_upwind_point` ↔ `zonal_edge_thickness` nest 1 (its only
    nest), the in-subset `do concurrent` under `if (CS%upwind_1st)`:
    `h_W(i,j,k) = h_in(i,j,k) ; h_E(i,j,k) = h_in(i,j,k)`
    (`MOM_continuity_PPM.F90`; `meridional_edge_thickness` holds the
    textually identical h_S/h_N loop). This one is do-concurrent, so its
    license stays the source assertion, like the pilot kernels.
  The corpus dump `MOM6/MOM_interface_heights.o_ptree` exists and holds the
  3-D `thickness_to_dz_3d` as expected. An earlier entry (2026-07-31, second
  kernel) recorded `thickness_to_dz` as OUT of scope pending exactly this
  semantics decision; that entry stands as history — the decision has now
  been made (by the user, 2026-07-31) and this entry records it in scope
  under rule A.
- **The C++ frontend needed NOTHING** — as predicted: the new point kernels
  are assignments over `Real&`/`const Real` already in the subset. The only
  clang-side change is the driver's `CPP_KERNELS` becoming (header, function)
  pairs, since the thickness kernels live in
  `mom_interface_heights_kernel.hpp`.
- **One printer truthfulness fix:** the generated doc line hardcoded "the
  `intent(inout)` arguments"; `edge_thickness_upwind`'s outputs are
  `intent(out)`. The text now derives from the actual intents — byte-identical
  for all previously banked kernels (theirs are all inout).
- **D7 fixtures first** (`tests/f90/`, regenerated with the pinned flang 21;
  existing dumps byte-identical): `test_kernel_plaindo` (perfectly nested
  plain-DO point kernel), `test_kernel_recurrence` (REFUSAL — the
  `p(i,K+1) = p(i,K) + …` shape distilled from `find_dz_for_eta`, whose EOS
  branch is a twin of nothing; the capital-K spelling also pins dump
  lowercasing — `K` and `k` are the same index, so the refusal fires on the
  +1 offset, not on case), `test_kernel_inline_nests` (two nests in one
  subroutine, one per IF branch, extracted by ordinal — pins determinism,
  out-of-range refusal, and that whole-subroutine mode still refuses),
  `test_kernel_component` (scalar + loop-indexed component reads, plus the
  `collide` subroutine pinning the naming-collision refusal). KIR-level
  refusal tests pin the reduction shape, imperfect nests, duplicate indices,
  component writes, offset component subscripts, and non-`intent(in)` bases.
  Tests 133 → 151 (with corpus + clang).
- **Proof outcomes** (`Pilot/EdgeThicknessUpwind.lean`,
  `Pilot/ThicknessToDz.lean`): per the mature pattern there are NO new
  hand-written models — each pair's point lemma relates the two GENERATED
  defs directly, and all three are **`rfl`** (the bodies are identical up to
  parameter order). The kernel-level theorems: upwind reuses the pilot's
  `pointwise` with the CW84 dummy-scalar idiom (license: the do-concurrent
  assertion); the two thickness kernels model the Fortran side honestly as
  `foldSeq` and *instantiate the schema lemma* (license: proof). The by-eye
  audit of each generated def against its source — part of banking now that
  both sides are machine-produced — was done for all six new defs (three
  Fortran, three C++): each mirrors its source's expression shape exactly
  (`h_to_z * h`; `h_to_rz * h * spv[_avg]` left-associated; `(h_in, h_in)`).
  Axioms audit extended by 17 declarations; `lake build` compiled everything
  **on the first attempt**: the twelve kernel-side declarations (generated
  defs, point lemmas, kernel theorems) report exactly
  `[propext, Classical.choice, Quot.sound]`, and the five polymorphic
  SeqSchema declarations report strict subsets (`foldSeq`/`pointwiseMap`
  none, the induction proofs `[propext]`(+`Quot.sound` via funext) — no
  classical reasoning), which the audit file notes. One cross-iteration
  channel the plain-DO gate deliberately leaves to the checker, now recorded
  in kir.py's docstring: a local scalar read before its first write would
  carry the previous iteration's value, but `functionalize` binds locals per
  iteration, so such a read prints as an *unbound name* and the generated
  Lean fails to elaborate — refusal by Lean, loud, never a wrong model.

---

## 2026-07-31 — Track B clang frontend: both sides of the theorems are now generated

**What:** the C++ mirror of the printer chain —
`flinspect/frontend/clang_kernel.py` (clang `-ast-dump=json` → the *same*
kernel IR) plus `Pilot/GeneratedCpp.lean`, generated from the production TIM
kernel header and proved equivalent to the hand-written C++ models
(`Pilot/FidelityCpp.lean`). The last non-mechanical link is gone: for both
banked kernels, dump → Lean is machine-produced on both sides, and the
hand-written C++ models are demoted from load-bearing links to verified
references (kept, audited, no longer trusted by eye). The full picture:

```
flang with-sema dump ──▶ kernel IR ──▶ Generated.lean          (Fortran side)
clang JSON AST       ──▶ kernel IR ──▶ GeneratedCpp.lean       (C++ side)
        FidelityCpp.lean:  GeneratedCpp ≡ hand-written C++ models
        + chain theorems:  GeneratedCpp ≡ Generated  (both endpoints machine-produced)
```

- **Shared-KIR design held.** The C++ kernels are already per-point scalar
  functions, so the extractor emits a rank-0 `Kernel` directly — no
  `pointize` on this side; `functionalize` and the Lean printer are reused
  unchanged. CW84's trailing guarded pair went through the *existing*
  `merge_if` join machinery untouched — the join semantics banked last time
  turned out to be frontend-agnostic, which is the whole point of the shared
  IR. (`kir.py` unchanged; the only printer edit is a provenance-text
  parameter on `print_module` — the default keeps `Generated.lean`
  byte-identical — because the C++ header must stamp clang provenance, which
  the flang blurb couldn't express. The semantic rendering paths are
  untouched.)
- **The cast allowlist (the load-bearing refusal).** clang wraps almost every
  read in `ImplicitCastExpr`; unwrapping them wholesale would be exactly the
  plausible-but-wrong-model failure mode, since cast kinds like
  `IntegralToFloating` *change the value*. Only two kinds are allowlisted,
  each argued value-preserving: `LValueToRValue` (a variable read — the
  lvalue's storage location converts to the value it holds; pure value-category
  bookkeeping) and `FunctionToPointerDecay` (a function name decaying to a
  pointer in callee position — no data value involved). Anything else refuses,
  pinned by the `refuse_int_literal` fixture (`b + 1` → `IntegralToFloating`
  → `UnsupportedConstruct`).
- **Intent mapping:** `Real &` (non-const lvalue reference) → `inout`;
  `Real const` by value (clang prints `const Real`) → `in`. Everything else —
  pointers, const refs, plain mutable by-value `Real`, non-Real types, default
  arguments — refuses. Outputs are the `Real &` parameters in declaration
  order, so the generated def's tuple order matches the hand models' by
  construction.
- **JSON surprises** (the survey mostly matched the plan; three notes):
  (1) the callee of `amrex::Math::abs` carries **no namespace qualifier** in
  the JSON — `referencedDecl` is just the FunctionDecl `abs` (found through
  amrex's `using std::abs` shadow), so acceptance is on the referenced
  declaration's name, not the source spelling; (2) `FloatingLiteral.value` is
  the shortest round-trip form (`3.0_rt` → `'3'`, `0.5_rt` → `'0.5'`), which
  lands on the same Lean numeral the Fortran side prints — spelling fidelity
  is preserved through a different route; (3) `else if` is just an `IfStmt`
  in the else slot — kept nested (single-branch `If` with an `If` in
  `orelse`), which `functionalize` turns into the same `IfExpr` chain as
  flang's `ElseIfBlock` branches, so the printed output is identical in form.
  Also confirmed the prompt-level warning: node `id` fields are memory
  addresses — nondeterministic across runs — so the JSON is an in-memory
  intermediate only; no dump is ever committed or golden-compared (the D7
  corpus asserts on extracted KIR / printed Lean instead).
- **A genuine cross-language parse asymmetry, now pinned:** C++ unary minus
  binds tighter than `*`, so `-2.0_rt * x` is `(-2) * x`, while Fortran R1008
  makes `-2.0*x(i)` the negation of the whole term, `-(2 * x)`. The negate
  fixtures on the two sides deliberately print differently — each model
  mirrors its own source's parse, and the equivalence theorems absorb the
  difference.
- **D7 fixtures first** (`tests/cpp/`, self-contained — a 3-line prelude
  mirrors `amrex::Real`/`_rt`/`Math::abs`, so no include paths are needed):
  the composite point kernel, the guarded-join pair, negation, and a refusals
  file (`+=`, `for`, `int` parameter, int literal). Gated on `clang++` being
  on `PATH` (the C++ analogue of the `FLINSPECT_CORPUS` gate), with
  node-level allowlist tests that run everywhere off hand-built JSON dicts.
  Manifest: a **sibling `tests/cpp/MANIFEST.md`**, not a section in the f90
  one — the f90 corpus defends flang *dump-format* drift with committed
  snapshots; this corpus has no committed dumps at all (see above) and its
  drift axis is the clang JSON schema. Tests 117 → 133.
- **Determinism/provenance:** `lean/pilot/generate.py` now emits both files;
  the clang invocation is pinned (paths as constants, CLI overrides) and the
  `clang++ --version` line + full flag set are stamped into
  `GeneratedCpp.lean`'s header. Regeneration is byte-stable for both files,
  and the corpus golden tests import the driver's own lists (`KERNELS`,
  `CPP_KERNELS`, `render`, `render_cpp`) so driver and tests cannot drift.
- **Proof outcome** (`Pilot/FidelityCpp.lean`), compiled on the first
  attempt: `ppm_limit_pos_point` fidelity is **`rfl`** (function-level
  definitional equality — the printer's extra source parens and `curv > 0`
  vs `0 < curv` are notation-level, exactly as on the Fortran side).
  `ppm_limit_cw84_point` fidelity is deliberately *not* plain `rfl`, and the
  investigation says the extractor is right: `functionalize` carries the
  sequential guarded pair as merged inline `Cond`s inside the result tuple,
  while the hand model mirrors the C++ mutation order as a
  `let h_L' := ...; let h_R' := ... h_L' ...` chain, and
  `(a, if c then x else y)` vs `if c then (a, x) else (a, y)` is a
  propositional, not definitional, equality. That is the *same*
  control-flow-representation delta the Fortran-side CW84 proof absorbs, and
  the same two-line pattern closes it: `simp only [<the two defs>];
  split_ifs <;> rfl`. The chain theorems
  (`generated_cpp_matches_generated_fortran_{pos,cw84}`) rewrite through the
  fidelity lemmas into the existing pilot equivalences. Axioms audit extended
  by six declarations; all fourteen report exactly `[propext,
  Classical.choice, Quot.sound]`.

---

## 2026-07-31 — Track B second kernel banked: `PPM_limit_CW84`, and the control-flow join

**What:** the second kernel pair — Fortran `PPM_limit_CW84`
(`MOM6/src/core/MOM_continuity_PPM.F90`) / C++ `MOM::ppm_limit_cw84_point`
(`TIM/mom/cpp/mom_continuity_ppm_kernel.hpp`) — extracted from the production
dump, generated into `Pilot/Generated.lean`, and proved equivalent to the C++
port. The kernel subset widened by exactly the three constructs CW84 needs;
everything else still refuses.

- **The join semantics decision (the load-bearing one).** CW84's loop body ends
  with two *sequential* guarded assignments, and the second guard's RHS reads
  `h_L`, which the first may have just updated. `functionalize` now supports a
  statement following an `If` in exactly one shape: the `If` has a single
  branch (an elseif chain refuses — the merge formula below is binary) and
  every branch body consists solely of assignments to state (output) variables
  — no locals (a `Let` may not escape a branch), no nested `If`s. The merge is
  per variable, `state'[v] = Cond(cond, state_then[v], state_else[v])` (vars no
  branch assigned pass through), and the remaining statements run against the
  *merged* state — so the second guard's `h_l` read observes the first `If`'s
  conditional value, sequentially, as in the source. `Cond` is a new
  conditional *expression* node (inline `if c then a else b` in the printer);
  no frontend ever produces one — only `functionalize` creates it. The merge
  applies only when statements actually follow the `If`; a trailing `If` keeps
  the structured `IfExpr` path, so the pilot kernel's generated model is
  byte-identical to before. Deliberately conservative refusals, both pinned by
  tests: elseif-chain joins, and any non-state assignment inside a joined
  branch.
- **The two smaller constructs.** Logical IF statement (R1139): the dump nests
  it as `ActionStmt -> IfStmt` with the condition and a *nested* `ActionStmt`
  as children — extracted as a single-branch `If` with no orelse. Unary minus:
  flang's `Negate -> Expr`, new `Neg` node, printed `-x` with parens restored
  around compound operands (`-(2 * x)`) because Lean's prefix `-` binds tighter
  than `*` while Fortran's applies to the whole term. Both node shapes matched
  what we expected from the R1139/R1008 grammar — no dump surprises this time
  (Q1 ledger: nothing new).
- **D7 fixtures first:** `test_kernel_ifstmt_join` (two guarded assignments,
  the second reading the first's target — the golden Lean pins the merged-state
  threading visibly: `(if t > b then t - 1 else b) + t`) and
  `test_kernel_negate` (bare leaf, compound operand, negated source parens).
  Manifest rows added. Tests 111 → 116 (join + negate goldens, three join
  refusals; the old blanket join refusal test retired — that shape is now the
  supported one).
- **Proof outcome** (`Pilot/PpmLimitCw84.lean`): the maturing pattern — no
  hand-written Fortran model; the point lemma is proved directly against
  `TrackB.Generated.ppm_limit_cw84`. Only the C++ model is hand-written
  (mirroring its own shapes: the `h_i` copy, locals RLdiff/RLmean/FunFac/
  RLdiff2, and the sequential mutations as a `let h_L' := ...; let h_R' :=
  ... h_L' ...` chain). Expression shapes are identical across the two sources;
  the proof absorbs only the control-flow *representation* delta (inline
  `Cond`s in the result tuple vs sequential `let`s):
  `simp only [<the two defs>]; split_ifs <;> rfl` — every case closes by
  `rfl` once the shared guards are split. (One tactic lesson: `unfold` leaves
  the ifs buried under `have` binders where `split_ifs` cannot see them;
  unfolding via `simp only` zeta-reduces the `let`s first.) The kernel-level
  theorem reuses the pilot's
  `pointwise` schema — CW84 has no scalar argument, so the schema's scalar
  slot is filled with a dummy `0` on both sides. Axioms audit extended: all
  three new declarations report exactly `[propext, Classical.choice,
  Quot.sound]`.
- **Latent threading bug found by auditing the join against its spec:**
  `functionalize.subst` skipped substitution whenever an output's current
  symbolic value was a plain `Var` — meant to skip the identity case
  (`state[o] = Var(o)`, where substituting is a no-op anyway), but it also
  skipped *aliases*: after `b = a`, a later read of `b` would silently keep
  referring to the input `b`. No banked kernel hits it, but the join makes it
  reachable, so it is fixed (substitution is now unconditional) and pinned by
  `test_sequential_alias_read_threads_current_value`. Regenerating
  Generated.lean confirmed the fix changes nothing for the existing kernels.
- **Drift guard tightened:** the pytest corpus golden test now imports
  `KERNELS`/`render` from `lean/pilot/generate.py` instead of hardcoding one
  kernel, so the driver and the test cannot disagree about what Generated.lean
  should contain.
- **Considered and OUT of scope:** `thickness_to_dz`
  (`MOM_interface_heights.F90`). Its loops are plain nested `do`, not
  `do concurrent` — extending pointize to plain DO nests would assert an
  iteration-independence the source doesn't state, and that semantics decision
  is reserved for the user.

---

## 2026-07-30 — Track B printer: generated-from-dump model ≡ C++ port, every link machine-checked

**What:** the first milestone of Track B's printer step (DESIGN §4 "*Then:*
automate the printer") — a deterministic dump → kernel-IR → Lean pipeline whose
output is proved, in Lean, to match the pilot's hand-written model **by `rfl`**
(definitional equality: zero semantic drift). The full chain is now:

```
MOM6 production with-sema dump ──(flang_kernel)──▶ kernel IR
  ──(pointize · functionalize · lean_printer)──▶ Pilot/Generated.lean
  ──(Fidelity.lean: rfl)──▶ ≡ hand-written ppmLimitPosF
  ──(pilot's point lemma)──▶ ≡ C++ ppm_limit_pos_point      (generated_matches_cpp)
```

All five audited declarations rest on `[propext, Classical.choice, Quot.sound]`.

- **New modules** (per §2.3's two-IR rule — nothing touches `ir.py`):
  `flinspect/kir.py` — kernel-IR types + the two passes: *pointize* (strip one
  `do concurrent` nest; arrays indexed exactly by the loop indices become
  scalars; loop/bounds/grid params dropped) and *functionalize* (locals →
  `let`, inout assignments → symbolic state, paths end by materializing the
  output tuple). `flinspect/frontend/flang_kernel.py` — dump subtree → kernel
  IR, structural (expressions come from the tree, never re-parsed from unparse
  text). `flinspect/lean_printer.py` — kernel IR → Lean, preserving the
  source's own grouping (`Paren` nodes) so the model mirrors what the code
  says. Trusted-base rule enforced throughout: any construct outside the
  subset raises `UnsupportedConstruct` — refusal, never a guess (offset
  subscripts, statements after an IF join, non-intrinsic calls all refuse).
- **Driver + regeneration:** `lean/pilot/generate.py` (deterministic; same
  dump in, same Lean out). The extractor consumed the *production*
  `MOM_continuity_PPM.o_ptree` unmodified and correctly dropped `G`, `GV`, and
  the six index-range args during pointization.
- **Tests** (`tests/test_kir_lean.py`, +7 → 111 total): fixture-based
  end-to-end on the new D7 fixture `test_kernel_doconcurrent` (the supported
  kernel subset in miniature), pass-level refusal tests, and a corpus-gated
  golden test asserting `Pilot/Generated.lean` matches a fresh regeneration
  byte-for-byte (catches a stale committed file *and* dump-format drift).
- **Dump-format notes** for the kernel face (Q1 ledger): `IfConstruct` wraps
  else-branches in `ElseIfBlock`/`ElseBlock` containers; leaf payloads come
  both quoted (`Name = 'x'`) and unquoted (`Intent = In`); `12.0` appears in
  unparse text as `1.2e1_8` but the structured `Real = '12.0'` is stable —
  another reason the extractor reads the tree, not the unparse strings.

**Scope honesty:** the supported subset is exactly the pilot kernel's shape —
one mask-free `do concurrent` nest of assignments and structured ifs over
`+ - * / **`, comparisons, and `abs`. Everything else refuses loudly. Next
candidates, in order of new machinery required: the C++ side
(`clang -ast-dump=json` → the same kernel IR — closes the loop mechanically),
more point kernels (`ppm_limit_cw84_point` needs nothing new), then the hard
tail (k-recurrences → induction; masks).

---

## 2026-07-30 — Track B pilot SUCCEEDED: `PPM_limit_pos` equivalence machine-checked over ℝ

**What:** completed the Track B pilot (DESIGN §4; VISION D6) — hand-written Lean 4
models of the already-ported kernel pair `PPM_limit_pos` (Fortran,
`MOM6/src/core/MOM_continuity_PPM.F90`) / `ppm_limit_pos_point` (C++,
`TIM/mom/cpp/mom_continuity_ppm_kernel.hpp`), with machine-checked equivalence.
Everything lives in `lean/pilot/` (a `lake` project; Mathlib dependency).

- **The theorems** (`lean/pilot/Pilot/PpmLimitPos.lean`):
  `ppmLimitPos_point_equiv` — the C++ point kernel and the Fortran loop body are
  the same function ℝ⁴ → ℝ² — and `ppmLimitPos_kernel_equiv` — the AMReX
  `ParallelFor` launch and the Fortran `do concurrent` nest produce identical
  output arrays over any index box. Each model mirrors *its own* source's
  expression shapes (Fortran `curv**2 + 3.0*dh**2` vs C++
  `(curv*curv) + (3.0*(dh*dh))`), so the proof absorbs exactly the transcription
  deltas and nothing else. The whole proof is ~5 lines: `unfold`, one
  `ring`-provable bridge identity, `simp only`. **It compiled on the first
  attempt** — for kernels in the TIM point-function style, the point lemma is
  near-mechanical.
- **Trusted-base audit** (`Pilot/AxiomsAudit.lean`): `#print axioms` on both
  theorems reports exactly `[propext, Classical.choice, Quot.sound]` — Lean's
  standard axioms; no `sorryAx`.
- **Q5 answers surfaced by the pilot:** `intent(inout)` scalars modeled
  functionally (result pair) work with zero friction; the iteration schema over
  an abstract index type `ι` (arrays as `ι → ℝ`) suffices for a mask-free
  `do concurrent` and composes with the point lemma by `funext`; Mathlib's
  decidable-order instances on ℝ mean the `if`-guards need no explicit
  `Classical` opens. Still open: masks/wet-dry variants, reductions/k-recurrences,
  and the clang-side ingestion route.
- **Infrastructure** (new, reusable): elan 4.2.3 + Lean v4.32.2 under
  `/glade/work/altuntas/lean-root/` (home quota is too tight for a toolchain);
  activate with `. /glade/work/altuntas/lean-root/activate_lean.sh`. Project
  created with `lake new pilot math`, which also fetched the full Mathlib
  binary cache (8,639 prebuilt modules — no source build needed).
- **Practical lessons:** a blanket `import Mathlib` is prohibitively slow on
  GLADE (>10 min to elaborate one file); targeted imports
  (`Mathlib.Data.Real.Basic` + `Mathlib.Tactic.Ring`) bring a full rebuild of the
  file to ~2 min. Mathlib's style linters fire on non-Mathlib file headers;
  disabled per-file (`set_option linter.style.header false`) — this is project
  code, not a Mathlib contribution.

**Honest caveats:** the models are **hand-written** — source fidelity is by eye,
which is acceptable for the pilot (that was its design) but is exactly what the
next Track B step removes: the deterministic printer (dump → kernel IR → Lean)
makes fidelity mechanical and auditable. And `PPM_limit_pos` is the friendliest
kernel shape (pure point function, no reductions, no masks); the schema's reach
beyond that shape is untested.

---

## 2026-07-30 — Notebooks overhauled: a post-seam suite, and the venv made self-sufficient

**What:** replaced the pre-seam notebook collection with a four-notebook
explanatory suite (`notebooks/README.md` + `01_getting_started` →
`04_confidence_queries`) and repaired the venv so `PYTHONNOUSERSITE=1` works for
*everything*. Consumer-side work only — no frontend or IR changes.

- **The venv was not self-sufficient.** Under `PYTHONNOUSERSITE=1`,
  nbformat/nbconvert died on missing `platformdirs`/`attrs` even though
  jupyterlab is a declared dependency — pip had satisfied those transitive deps
  from the (broken) `~/.local` user site at install time, so they never landed
  in the venv. Meanwhile *without* the env var, `import flinspect.explorer`
  fails because the user site's broken pandas shadows the venv. Fix:
  `PYTHONNOUSERSITE=1 .venv/bin/pip install -e '.[dev]'` (re-resolves the tree
  without the user site; pulled in platformdirs, attrs, requests,
  python-dateutil, …). Verified: 99 tests, `jupyter nbconvert`, and headless
  notebook execution all pass under `PYTHONNOUSERSITE=1`; the bare-mode suite is
  unchanged (98 + 1 skip). `~/.local` itself untouched. Launch and install
  commands are documented in `notebooks/README.md` — the env var belongs on the
  *install* command too, or the hole reopens.
- **The old suite (7 tracked notebooks + root `test.ipynb`) is retired.** Only
  the untracked `explorer_TIM_new.ipynb` ran against the current package; the
  rest imported pre-seam APIs (`frontend._nodes`, `e.store[...]`,
  `pf.registry`, `node.program_unit.parse_tree_path`) and referenced dump
  directories that no longer exist. Every `*_TIM*` name was aspirational —
  there is still no TIM corpus (see 2026-05-28 below). Their durable ideas were
  rebuilt, not copied: the reachability analyses ("which FMS2 modules does MOM6
  actually need", the direct API surface) live in `03_module_dependencies` on
  `get_module_dependency_graph()` + IR relations. `environment.yml` went with
  them — its only content beyond `pip install -e .` was pyvis, which only the
  retired notebooks used; the venv flow above is the single documented setup.
- **Suite conventions** (spelled out in `notebooks/README.md`): seam-only
  imports (`flinspect.{ir, parse_forest, graph_view, explorer}`), one parameter
  cell per notebook, corpus root from `FLINSPECT_CORPUS` (glade default),
  outputs committed **stripped**, and every notebook must execute end-to-end
  headlessly (the 69 KB committed-outputs blob does not survive this policy).
  `01_getting_started` is fully portable — it runs off the `tests/f90` fixtures
  and demonstrates the `assumed` stratum with a small hand-built IR, since no
  self-contained fixture produces one (the known dynamic-dispatch manifest gap).
- **Findings recorded, not fixed** (this was a consumer-side pass; the package
  is untouched):
  - (a) **The IR carries no source provenance.** Corpus-level analyses want
    "which source tree defined this module"; the pre-seam notebooks read a
    `parse_tree_path` node attribute that rightly no longer exists. Workaround
    in `03`: extract each corpus subdirectory separately and attribute modules
    by where they are defined. Whether provenance becomes an IR fact is a
    deliberate decision for later, not a notebook's call.
  - (b) `ParseForest.get_call_graph()` **prints** an unresolved-count line on
    every call — noisy for library consumers; candidate cleanup.
  - (c) 84 call events originate from `program` units or module-level code and
    therefore appear in the relations but not as call-graph edges (nodes are
    subroutines/functions only) — noted where visible (`04`).
  - (d) The module dependency graph carries two **self-loops**
    (`mom_diag_buffers`, `mom_io_file` — same-module EXTENDS edges), so
    `nx.is_directed_acyclic_graph` is False even though no multi-module cycle
    exists; `03` checks strongly-connected components instead.

Corpus replay unchanged: 458 files, 0 errors, resolved 22,764 / assumed 165 /
unresolved 1,527.

---

## 2026-07-30 — Phase 3 landed: the Explorer shows what it knows (and what it doesn't)

**What:** completed Phase 3 (DESIGN §4) — Explorer correctness. W5 is closed, the
D3 confidence strata are now visible rather than merely stored, and the part of
the Explorer worth testing no longer needs a browser.

- **W5 was half-fixed and the docs didn't know it.** Phase 1a's IR rewrite already
  keyed cytoscape nodes by the scope-qualified `Entity.id` with `name` demoted to a
  display label, so the merge bug was gone; the W-table row still cited
  `explorer.py ('id': node.name)`. What was genuinely missing was a *pin* (the
  Explorer had zero tests) and any display of confidence. Verified end-to-end
  before touching anything — selector options, cytoscape node/edge data, and
  `get_call_graph()` nodes all keep three same-named routines apart — then pinned
  it. The row now reads "fixed in Phase 1a (identity) + Phase 3 (pinned,
  confidence shown)".
- **New fixture `test_name_collision`** (D7 corpus work): three modules each
  defining `apply_bc` with an *identical* signature, so the name is all they share
  and a name-keyed consumer would collapse three nodes into one. The caller reaches
  each through a different USE form — wildcard-with-rename, only-list, only-list
  with rename — which is also what keeps the file legal (three wildcard USEs would
  make the bare name ambiguous). That closes the manifest's **USE renames** gap:
  both rename forms had no fixture, only hand-built-registry unit tests.
- **Found while writing it:** the only-list rename form projects onto
  `Use(only=(), renames=(('bc_c','apply_bc'),))` — an *empty* only-list, which the
  `Use` docstring reads as "whole module". Resolution is unaffected (it follows the
  rename, and the corpus numbers are unchanged), so this is a fact-recording bug in
  the projection, not a resolution bug. Out of scope here (frontend), recorded in
  `tests/f90/MANIFEST.md`; the new test asserts the renames and deliberately not
  the only-list, so nothing pins the wrong fact.
- **Confidence rendering.** Call edges take their line style from the stratum
  (solid `resolved`, dashed `assumed`, dotted + muted `unresolved`); `defined=False`
  targets render ghosted (dashed outline, italic, low opacity) so "we never parsed
  this" reads at a glance; interface-membership edges get their own colour and
  arrowhead because they are structure, not calls, and carry no confidence. The
  pre-existing direction encoding stays on the *colour* channel, so the two
  encodings compose instead of fighting. A legend in the widget makes the whole
  scheme discoverable — the point of the phase is that partial knowledge is
  visible, which it isn't if you have to read the stylesheet to decode it.
- **Extracted `flinspect/graph_view.py`** — the pure half: IR + center entity →
  neighbourhood → list of `{'data', 'classes'}` element dicts, with no ipywidgets
  or ipycytoscape import, hence unit-testable without a kernel or browser
  (`tests/test_graph_view.py`). `explorer.py` keeps the stylesheet, the legend and
  the event wiring and nothing else; rendering is not the seam (principle #10), but
  the *content decisions* turned out to be exactly the testable part.
- **Two bugs fell out of the extraction.** (a) `classes` is a top-level cytoscape
  element attribute, not a data key — the old code passed `'classes': 'selected'`
  *inside* `data`, so the `node.selected` style (the purple border on the focused
  node) had never applied. Now set via `ipycytoscape.Node(classes=...)` and pinned.
  (b) `enclosing_module_name` returned "Unknown Module" for entities whose scope is
  named but not defined in the parsed set; module-qualified unresolved targets
  (`netcdf::nf90_open`) now group under their own module.
- **Stratum labels moved to the seam.** `RESOLVED`/`ASSUMED`/`UNRESOLVED` and a
  per-edge `IR.call_confidence(caller, callee)` lookup now live in `ir.py` as a
  *computed view* — the strata remain pure relations (D3 is untouched), but the two
  consumers that must *say* which stratum an edge came from no longer each
  re-implement three membership tests. `get_call_graph()` attaches `confidence` to
  every NetworkX edge and gained `must_only=True` (build from `calls_must`); it
  filters edges only, so `defined=False` targets remain as isolated nodes — the
  node set is still "every subroutine/function in the IR".

**Corpus replay (458 files, unchanged since 2026-05-28):** 0 file errors; the
element builder ran over all 7,108 browsable entities in ~29 s producing 45,437
resolved / 329 assumed / 3,046 unresolved call edges and 2,103 membership edges
across the neighbourhoods (edges are counted once per neighbourhood they appear
in), with 2,035 ghosted undefined node instances — 268 of them grouped under
`netcdf`, courtesy of the fallback above.

**One number doesn't reproduce, and it predates this phase.** Replaying the corpus
gives `resolved 22,764 / assumed 165 / unresolved 1,527`, whereas the Phase 2 entry
below records `22,764 / 114 / 1,578`. `resolved` matches exactly and so does
may (24,456) — the entire difference is 51 edges sitting on the
`assumed`↔`unresolved` boundary. Checked: the corpus files are untouched since
May, the split is insensitive to file order (identical sorted vs. reversed), and a
replay at `HEAD` *before* this phase's commits gives 165/1,527 too — so this is not
a Phase 3 regression but a discrepancy in how the Phase 2 figure was captured
(most likely measured before the last of that phase's frontend fixes landed).
Entries are append-only, so the number below stays as written; the reproducible
figures are these.

Suite: 99 tests green (70 → 99: name-collision IR + call-graph identity, the
graph_view element/strata/ghosting tests, the call-graph confidence attribute).
The `assumed` stratum is pinned against a hand-built IR rather than a fixture —
only genuine dynamic dispatch produces it and that construct still has no
self-contained fixture (manifest gap) — which is legitimate above the seam, where
the input is an IR, not a dump. Note `tests/test_graph_view.py` instantiates the
widget once as a smoke test, so the whole suite now wants `PYTHONNOUSERSITE=1` on
machines where a broken user-site pandas shadows the venv (documented in the test
module).

---

## 2026-07-29 — Phase 2 landed: sema's answers replace the hand-rolled resolver

**What:** completed Phase 2 (DESIGN §4) — soundness & resolution quality. The IR's
call relation is now stratified by confidence (D3), call resolution is *read from
sema* instead of re-derived, and the heuristic inference engine is gone (W1, W2,
W4, W6). Landed as two code commits (IR stratification; frontend resolution
overhaul) plus this docs pass.

- **IR (D3):** the single `calls` set became three pure relations —
  `calls_resolved` / `calls_assumed` / `calls_unresolved` — with `calls` (may)
  and `calls_must` (must) as computed union views, so existing consumers kept
  working unchanged. Unresolved *targets* are first-class entities with
  `defined=False` (scope-qualified `module::name` when the use-chain or sema's
  mangling pins the module, bare name atoms otherwise), replacing the
  `(caller, name)` `unresolved_calls` side-table. The old silent drop of `mpi_*`
  calls is gone too.
- **Attribution turned out cleaner than feared.** DESIGN Q2 warned the unparse
  annotation is per-*statement*, leaving `a = f(x) + g(y)` one string to split
  across two calls. In fact every `Expr` node carries its own annotation, and a
  `FunctionReference`'s *parent* `Expr` line is exactly the resolved text of that
  one call (`Expr = 'area_r(y)'`); `CallStmt` lines annotate themselves. The call
  pass keeps a stack of enclosing annotated `Expr`s, so each recorded call event
  gets its own resolved text and no cross-call attribution heuristic exists.
- **The mangling rule (Q1 caveat), derived empirically** from all 994 distinct
  mangled names in the corpus: always exactly three components,
  `imported$owner$specific`. One subtlety found the hard way: the middle
  component is the module that owns the specific's *symbol*, which is usually but
  not always its definition site — `fms2_io_mod$fms2_io_mod$compressed_read_2d`
  names a subroutine whose body lives in netcdf_io_mod (fms2_io_mod holds it by
  use-association), so demangled lookup follows the owner module's use-chain
  before falling back to a `defined=False` entity. Rule + fixture:
  `frontend/_flang_text.py::demangle`, `test_private_specifics`.
- **Type-bound calls:** sema resolves *static* dispatch in the unparse by
  hoisting the object into the argument list (`call obj%reset()` →
  `'CALL reset_bounds(obj)'` — even for `=>`-renamed and private impls), so those
  edges are `resolved`. *Dynamic* dispatch (polymorphic receiver, deferred
  binding) keeps the `obj%binding(...)` shape; those edges are classified through
  the declared type's binding table as `assumed` (an override may win at
  runtime), or `unresolved` when the receiver's type is unknown. Three latent
  binding-table bugs were fixed on the way: `generic :: g => a, b` was recorded
  as `g => b` (last name won), `procedure :: a, b, c` as `a => c`, and inherited
  bindings (EXTENDS chain) were never searched.
- **Retired (W1, W6):** `resolve_interface_procedures`, `_procedure_matches`,
  `_types_compatible`/`_ranks_compatible`/`_kinds_compatible`, all `_infer_*`
  call-site type/rank/kind inference, per-argument parsing in the call pass, the
  `DoublePrecision → 'r8_kind'` MOM-ism, and `get_subroutine_by_name` (the last
  `endswith` lookup, already dead). Variable *type* tracking survives — it types
  `obj%binding()` receivers — and signature parsing (types/ranks/kinds/optional)
  survives as entity facts. **No-sema input support is dropped** (decided with
  the maintainer; D4 made it redundant): nothing rejects a no-sema dump, but it
  is untested and unadvertised — generics would degrade to `assumed` fan-out.
- **Scope/visibility-correct lookup (W4):** the frontend now parses
  `AccessStmt`s (module default + per-name overrides), and `find_named_entity`
  crosses a wildcard USE only for names the used module makes public, follows
  only-lists/renames as before, and searches a routine's own USE statements
  before its enclosing unit's. Only-list imports are deliberately not
  visibility-checked (flang already validated them).

**Production corpus (458 MOM6+FMS2 with-sema dumps): 0 file errors; 42,199 call
events → resolved 22,764 / assumed 114 / unresolved 1,578** (may = 24,456,
must = 22,764; `resolved` is 93% of may). The may count sits 15% below the
Phase 1b baseline (28,931), outside the "few percent" acceptance band, so the
delta was decomposed edge-by-edge against a baseline replay rather than accepted:
- **6,655 edges removed**, of which 6,639 are fan-out siblings — edges to *other*
  members of a generic the caller invoked, i.e. exactly the W2 over-approximation
  this phase existed to eliminate. The residual 16 were inspected individually:
  all are corrected wrong edges (self-edges from dynamic dispatch resolved to the
  caller's own generic sibling, and name-coincidence binding matches like
  `reopen_mom_file → mom_io_infra::file_is_open` from the old
  search-all-types-for-a-binding heuristic).
- **2,180 edges added**: 1,578 first-class unresolved edges (the old
  `unresolved_calls` side-table, now real may-edges) plus ~600 correct edges the
  old engine could not find — demangled cross-module targets, `use`-renamed
  callees, and module-pinned externals (`netcdf::nf90_get_var_fourbyteint`,
  courtesy of the mangling).

Suite: 70 tests green (3 new fixtures: `test_external_calls`,
`test_type_bound_generic`, `test_private_specifics`; the retired engine's tests
replaced by attribution/demangle/visibility coverage, not dropped).

**Known residue, recorded not hidden:** (a) a function reference nested in
another call's argument list is still not recorded as a call site — a
long-standing under-approximation, now documented at the skip site (W2 residue);
(b) the hardcoded intrinsic list still filters function references, and names it
misses (`sqrt`, `loc`, `exp` are absent) surface as bare-name unresolved atoms —
same behaviour as the baseline, now at least visible in the unresolved stratum;
(c) dynamic dispatch lands on the *declared* type's impl as `assumed` — a later
phase could fan out over the EXTENDS overrides instead.

---

## 2026-07-29 — Phase 1b landed: fixtures and production now parse the same dump

**What:** completed Phase 1b (DESIGN §4) — tests and production consume the *same*
dump variant at last, closing the mismatch Phase 0 flagged (and W1/W3's fixture
half). Deliberately a **format adaptation only**: the hand-rolled resolution engine
and the IR's call semantics are untouched, so the diff stays reviewable. Retiring
the engine in favour of sema's answers is Phase 2.

- **Packaging first** (W10, plus a bug): `requires-python` relaxed from the
  `>=3.14,<3.15` hard pin to `>=3.11`, and `packages = ["flinspect"]` replaced with
  setuptools *discovery* — the explicit list silently omitted `flinspect.frontend`
  after the Phase 1a split, so the installed package was broken. Added a `dev`
  extra (pytest). W10 is closed.
- **Three helpers absorb the format difference** (`frontend/_flang_text.py`):
  `node_path` (match structure while ignoring an unparse annotation),
  `unparse_text`, and `splice_annotated_child` — which collapses an annotated
  `Expr` and its child back into *exactly* the single line a no-sema dump emits, so
  the existing structural matchers keep working verbatim. Three call sites changed:
  the `CallStmt` assert, argument type inference, and kind extraction (which would
  otherwise have gone silently `None` on every kind-selected declaration in real
  code — the failure mode no fixture would have caught, since none uses a kind).
- **Fixtures regenerated with-sema.** `gen_ptree_files.sh` drops `-no-sema`, writes
  through a temp file so a sema failure leaves the previous fixture intact and
  reports flang's diagnostics, cleans up the `.mod` files the dump emits as a side
  effect, and stamps `tests/f90/PROVENANCE` with `flang --version` (Q1: the format
  has no stability contract, so a format change should show up as a version delta).
- **`test_optional_args.f90` redesigned** — see the spike entry below; its two
  specifics now differ in their first argument's type, which is what makes the
  generic legal, while the optional dummies and the 3-/4-argument and keyword calls
  still exercise argument-count and keyword matching.
- **New fixture `test_generic_function`** — a generic *function* in an assignment.
  It is the only fixture exercising the `FunctionReference` path at all: the one
  named for it (`test_func_ref_array`) never contained a `FunctionReference` under
  either dump variant, since flang resolves `fields(i,:,:)` to an `ArrayElement`.
  What that fixture actually covers is rank reduction by a scalar subscript; its
  test section now says so instead of implying coverage we didn't have.

**Evidence it worked, twice over:**
- *Equivalence on fixtures* — for all six fixtures that survive sema unchanged, the
  no-sema and with-sema dumps project onto a **byte-identical IR** (entities,
  signatures, `calls`, `contains`, `uses`, `interface_members`, unresolved calls).
  The adaptation adds no facts and loses none; only the input shape changed.
- *The production corpus* — replaying the 458 surviving with-sema dumps from the D4
  run (`bin/flang_ptree/MOM6_using_FMS2`, MOM6+FMS2): **346 file errors → 0**, and
  **177 → 28,931 call edges** (1,707 unresolved, first-class per D3). The
  pre-Phase-1b frontend failed on every file containing a `CALL`, so before this
  change the production input was effectively unparseable while the tests were
  green — the exact hazard of tests and production disagreeing. Entity counts are
  identical before and after, confirming the change is confined to the call pass.

Suite: 49 tests green (37 pre-existing, unchanged in intent, + 12 new).

---

## 2026-07-29 — Phase 1b spike: what with-sema actually changes

**Context:** DESIGN §4 required spiking before switching fixtures — D4 validated
dump *generation*, not that the string-matching parser could *consume* with-sema
output.

**Findings.** Structure and interface parsing pass unchanged; `parse_calls` failed
on **every** file. Only four node types gain an unparse annotation — `CallStmt`,
`AssignmentStmt`, `Expr`, `Variable` — which is why the blast radius was small:
`SubroutineStmt`, `UseStmt`, `ModuleStmt` and friends are untouched. Two shapes to
absorb:

1. Statements carry the source they unparse to *after* resolution:
   `ActionStmt -> CallStmt = 'CALL compute_real(r,1_4)'`. The old
   `line.endswith("ActionStmt -> CallStmt")` assert fails on all of them.
2. An annotated `Expr` occupies its line, pushing its structural child one level
   deeper — so an operator that used to sit on the `Expr` line (`-> Add`) now sits
   on the child, and literals gain kind suffixes (`1_4`, `.true._4`).

**Q2 answered — yes, positively.** The unparse annotation carries the
sema-**resolved** specific procedure while the structured child still shows the
generic (`ProcedureDesignator -> Name = 'compute'`). Verified for generic
subroutine calls, generic function references, and type-bound generics. So the
textual dump is enough; `-fdebug-dump-symbols` is not needed for this.

**Caveat found later, not in the original spike:** the resolved name is *not*
always a plain identifier. Where only the generic is USE-imported (so the specific
isn't accessible by name in that scope), flang emits a mangled, fully-qualified
form — `mpp_mod$mpp_mod$mpp_error_basic`, seen throughout the FMS corpus. Phase 2
must demangle `module$module$specific` rather than assume an identifier. Phase 1b
therefore only *records* the raw text (`ParseTree.call_unparse`, below the seam,
unused) as a hook, and leaves callee extraction on the structured tree.

**`test_optional_args.f90` was invalid Fortran all along.** Sema rejects it:
"Generic 'init' may not have specific procedures 'init_simple' and 'init_advanced'
as their interfaces are not distinguishable" — `init_simple(x, n)` and
`init_advanced(x, n, tol, debug)` are ambiguous for a 2-argument call, because the
extra dummies are optional. It only ever compiled because `-no-sema` never checked.
A lesson about no-sema fixtures generally: they can encode Fortran that no compiler
would accept, so the facts derived from them can describe programs that cannot
exist.

---

## 2026-06-18 — Phase 1a landed: the IR seam

**What:** completed Phase 1a (DESIGN §4) — the structural half of the seam, as a
pure refactor with fixtures still on no-sema.

- `flinspect/ir.py`: the relational IR per DESIGN §2.1 — entities as frozen value
  objects keyed by scope-qualified `EntityId`, relations as tuple sets,
  `callees`/`callers` derived rather than stored, `unresolved_calls` first-class.
- `flinspect/frontend/` package with the `Frontend` protocol
  (`extract(sources) -> IR`); `parse_tree.py` became `frontend/flang_dump.py` and
  the node/registry/state helpers became its privates (`_nodes`, `_registry`,
  `_state`, `_flang_text`, `_variable_info`). The frontend keeps the interned node
  graph *internally* and projects onto the IR at the boundary (principle #10).
- `lfortran_asr.py` stub raising `NotImplementedError` — the forcing function that
  keeps the IR honest.
- `ParseForest`/`Explorer` rewritten to consume the IR only; per-file fault
  isolation, so one unparseable file is collected as a `FileError` instead of
  aborting the forest (W3, principle #9).
- Tests split along the seam: `tests/test_ir.py` asserts on the IR,
  `tests/frontend/test_flang_dump.py` keeps the below-seam resolution-engine tests.
  `tests/test_parse_tree.py` retired.

**Why it matters:** consumers no longer know flang exists, which is what made
Phase 1b a change to one file's line matching rather than a change everywhere.

---

## 2026-05-28 — Phase 0 landed: docs split + README reset

**What:** completed Phase 0 (DESIGN §4) — "reset expectations."
- Split the single `VISION_AND_PLAN.md` into three living docs: `VISION.md` (why /
  decisions), `DESIGN.md` (how / architecture / roadmap), `DEVLOG.md` (this
  append-only log). Old file removed.
- Rewrote `README.md` to lead with what flinspect *is today* (a structural-
  exploration prototype) and quarantined all the relational/Z3/GPU material under
  an explicit, clearly-disclaimed `# Roadmap / Vision` heading (W9). The detailed
  GPU-porting worked examples were preserved there (they exist nowhere else); the
  README now cross-links the three `docs/` files.

**Why it matters:** W9 (README ~90% aspiration stated as present tense) is closed.
Tests-vs-production dump-variant mismatch and the seam refactor remain for Phase 1.

---

## 2026-05-28 — `--gen-ptree` cannot build AMReX (TIM infra path)

**Context:** ran `./build.sh --gen-ptree --jobs 4` with no `--infra`, so it
defaulted to the **TIM** infrastructure (`libinfra-TIM.a`), which pulls in AMReX.
All prior full-coverage runs used `--infra FMS2`, which never builds AMReX.

**Symptom:** the AMReX CMake configure failed — `which: invalid option -- 'f'`
noise, then `clang: error: no such file or directory: 'testCCompiler.c.o'` during
CMake's compiler-validation step.

**Root cause (structural, not a regression):** the `ncar-flang_ptree.mk` template
is a deliberately *non-compiling, dump-only* toolchain — `CFLAGS` carries
`-Xclang -ast-dump -fsyntax-only` (no object file is ever produced), `FC = flang
-fc1`, `LD`/`AR = echo`. `amrex-utils/Makefile` does `include $(TEMPLATE)` and
builds AMReX via CMake, which begins by compiling+linking a test program. With
`-fsyntax-only` no `.o` exists, so the link fails. The `which flang -fc1`
expansion (`-DCMAKE_Fortran_COMPILER=$(shell which $(FC))`) is the harmless
`which: invalid option` noise. CMake picks up the dump-only `CFLAGS` from the
environment.

**Resolution:** none needed — this is inherent. A non-compiling compiler can't
produce a real library. Guidance: for the parse-tree corpus use `--infra FMS2`
(the proven path, AMReX is external C++/Fortran glue, not MOM6 science code). If
TIM parse trees are ever specifically needed, pre-build AMReX with a real compiler
and pass `--amrex <path>` so `--gen-ptree` skips building it (build.sh only builds
AMReX from the submodule when `--amrex` is absent). Caveat: TIM files that
`use amrex_*` would still need flang-produced `.mod` files for full sema.

---

## 2026-05-28 — FULL COVERAGE: the `FC_AUTO_R8` fix (D4 validated)

**Context:** after the FFLAGS fix, MOM6 sat at 194/340 with all remaining genuine
errors in one class — `REAL(4)`-vs-`REAL(8)` argument-kind mismatches in five
gatekeeper files (`grid`, `MOM_EOS_TEOS10`, `MOM_TFreeze`, `monin_obukhov`,
`sat_vapor_pres`).

**Root cause:** the `ncar-flang_ptree.mk` template omitted
`FC_AUTO_R8 = -fdefault-real-8 -fdefault-double-8` that every *real* MOM6 template
(e.g. `ncar-flang.mk`) uses. Without it flang treated default `real` as `REAL(4)`,
clashing with the r8 dummies in the GSW/TEOS10 equation-of-state code.

**Resolution:** added `FC_AUTO_R8` to the template's `FFLAGS`. Result: **FMS2
104/104, MOM6-infra 14/14, MOM6 340/340, zero genuine errors.** The ~140 MOM6
files previously failing were cascade behind the EOS/TEOS10 chain and resolved
along with the five gatekeepers. **This validates D4** — with-sema over the full
stack works; total enabling cost was four small foundational fixes (this r8 flag,
the FFLAGS reset, the `mpp` TRANSFER `SIZE=` patch, the `mpp_group_update`
optional-arg). D3's no-sema fallback is no longer required for coverage.

---

## 2026-05-28 — Big artificial blocker: FFLAGS pollution (64→194/340)

**Context:** MOM6 coverage was stuck at 64/340 with many `-L<colon-joined-paths>`
"unknown argument" errors. The temptation was to retreat to no-sema; instead we
investigated the `-L` error.

**Root cause:** `activate_llvm.sh` exports
`FFLAGS="-I${INCLUDE_DIR} -L${LIB_DIR}"` with colon-joined paths (invalid on a
compile line), and build.sh's MOM6-stage `mkmf -c "${FFLAGS} ..."` inherited it,
polluting CPPDEFS. A first fix (setting `FFLAGS=""` in build.sh defaults) failed
because `activate_llvm.sh` is sourced *later* and re-exports it.

**Resolution:** reset `FFLAGS=""` immediately after `source activate_llvm.sh` in
build.sh's `flang_ptree` module-load case. MOM6 jumped 64→194/340, 0 unknown-arg
errors. This proved the low coverage was a *build bug*, not flang rejecting MOM6 —
the remaining 146 failures were the r4/r8 class (next entry) plus its cascade.

**Lesson learned:** trust the build.sh-run logs, not standalone `make` probes — a
standalone probe was contaminated by ncarcompilers `-L` injection because it
wasn't run under `module reset`.

---

## 2026-05-28 — Sema scope probe: failures are sparse and foundational

**Context:** with the build plumbing fixed, needed to know whether with-sema was
tractable or an open-ended tail of incompatibilities.

**Findings:** genuine flang↔source rejections are **sparse and foundational** —
only ~4–5 files across FMS2+MOM6 (`mpp`, `grid`, `monin_obukhov`,
`sat_vapor_pres`, `MOM_domain_infra`), clustered in a few error classes sharing a
REAL r4/r8 kind / generic-resolution root. Low coverage elsewhere is *cascade*
behind these gatekeepers, not independent bugs — patching `mpp` alone took FMS2
from 26→103 of 104 files.

**Patches applied (kept):**
- `mpp/include/mpp_chksum_int.fh`: flang's sema rejected `TRANSFER(mask_val,
  i4tmp)` into an array mold ("Dimension 1 of LHS has extent 2, but RHS has extent
  1") — legal Fortran other compilers accept. Fixed with explicit
  `TRANSFER(..., SIZE(i4tmp))`. Because `mpp` is foundational, this unblocked the
  whole FMS2 stack.
- `mpp/include/mpp_group_update.fh`: MOM6 (`MOM_domain_infra`) calls
  `mpp_do_group_update` with a 4th arg `omp_offload` that the stock 3-arg specific
  lacks → generic mismatch. Added `logical, optional, intent(in) :: omp_offload`
  to the FMS template (keeping MOM6 source pristine for analysis fidelity).

**Conclusion:** with-sema is tractable. (Decision deferred to chase the r4/r8 root
cause — resolved in the FC_AUTO_R8 entry above.)

---

## 2026-05-28 — Merged parse-tree generation into `build.sh --gen-ptree`

**Context:** removing `-no-sema` to get with-sema dumps broke generation —
`mpp_mod.mod not found` etc. The standalone `gen_parse_tree.sh` was meant to mimic
`build.sh` but had drifted badly (stale `INFRA_ROOT=submodules/FMS`; real path is
`submodules/infra/FMS2`) and broken.

**Root cause of the constraint:** the with-sema dump (`-fdebug-dump-parse-tree`)
requires every USE'd module's `.mod` file to exist, and flang emits **no dump at
all** on a semantic error. So with-sema couples fact extraction to a complete,
topologically-ordered build — but the dump self-bootstraps, emitting each `.mod`
as a side effect.

**Resolution:** deleted `gen_parse_tree.sh`; merged its intent into `build.sh` as
an additive `--gen-ptree` mode (forces the `flang_ptree` template, best-effort
`make -k`, tolerant of per-file failures). Fixed along the way: the INFRA path,
`-fc1` ordering (baked `FC = flang -fc1` into the template so `-fc1` is always
first), and the MPI `mpi.mod`/`mpif.h` include paths (plain flang, not the mpifort
wrapper). Activates flang via `source .../activate_llvm.sh`.

**This is the central cost of D4:** with-sema is coupled to a full ordered build.
The two dump modes:
- `-fdebug-dump-parse-tree-no-sema` — pure syntactic, standalone on any single
  file, no deps. Names/types/generics unresolved.
- `-fdebug-dump-parse-tree` (with sema) — adds constant folding, resolved KIND
  values, typed expressions. Requires all dependency `.mod` files.
