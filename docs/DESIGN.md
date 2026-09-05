# groundline — Design

> **Status:** living document, rewritten in place as the architecture firms up.
> This is the *how*: target architecture, the IR seam, the weakness→fix mapping,
> the principles that constrain the design, and the phased roadmap.
>
> For the *why* (goals and strategic decisions D1–D5) see `VISION.md`. For the
> dated narrative of roadblocks and resolutions see `DEVLOG.md`. Decision IDs
> (D1–D5) referenced here are defined in `VISION.md`.

---

## 1. Weaknesses being addressed (prioritized)

From the review of the current codebase. Ordered by impact on the vision.

| # | Weakness | Where | Fix lands in |
|---|----------|-------|--------------|
| W1 | Re-implements semantics flang already computed, from a *no-sema* dump | whole `parse_tree.py` | **fixed in Phase 2** — resolution read from sema's unparse; the inference engine deleted |
| W2 | Facts are heuristically over- *and* under-approximate; unsound for a verification layer | `_types_compatible`, `resolve_interface_procedures` (all-procs fallback), `unfound_*` drops | **fixed in Phase 2** — confidence strata (D3); unresolved first-class. Residue: nested function references in argument lists still unrecorded (documented at the skip site) |
| W3 | Brittle text scraping: exact flang node strings, `|`-counting, `assert ...not recognized`, no per-file isolation | `parse_tree.py`, `utils.level()` | D2 (seam) + Phase 1 |
| W4 | Name-based matching ignores scope/visibility/overloading | `find_named_entity`, `get_subroutine_by_name` (`endswith`), no public/private | **fixed in Phase 2** — AccessStmt-derived visibility, use-chain lookup, `endswith` gone |
| W5 | Explorer keys cytoscape nodes by **bare name** → distinct same-named routines silently merge | `explorer.py` | **fixed in Phase 1a** (identity: the IR rewrite made nodes `EntityId`-keyed, name demoted to a display label) + **Phase 3** (pinned by `test_name_collision` end-to-end — elements, selector options, call-graph nodes — and confidence now rendered) |
| W6 | Hardcoded intrinsic list; `DoublePrecision→'r8_kind'` MOM-ism; named-kinds-only | `utils.py`, `_extract_kind_from_line` | **mostly fixed in Phase 2** — MOM-ism deleted; kinds are signature facts, not resolution inputs. The intrinsic list remains (nothing in the dump marks intrinsics); names it misses surface as unresolved atoms |
| W7 | Three full re-parse passes per file | `parse_structure/interfaces/calls` | revisit (now three passes + a classification pass; ~30 s for the 458-file corpus) |
| W8 | No CLI; notebook-only despite "CI-enforceable" claim | — | Phase 4 |
| W9 | README oversells; ~90% aspiration | `README.md` | Phase 0 |
| W10 | Python 3.14 hard pin | `pyproject.toml` | **fixed in Phase 1b** (floor `>=3.11`) |

---

## 2. Target architecture

```
┌──────────────────────┐   ┌────────────────────────┐   ┌───────────────────────────┐
│ Frontends (swappable) │   │  groundline IR          │   │ Consumers (flang-agnostic) │
│                       │   │  (the contract)        │   │                            │
│ A. flang sema dump    │──▶│  Entities + Relations  │──▶│  Graph build (ParseForest) │
│ B. LFortran ASR  (TBD)│   │  + confidence (D3)     │   │  Explorer (Jupyter)        │
│ C. flang FIR/API (TBD)│   │  groundline-owned       │   │  Relational query layer    │
└──────────────────────┘   └────────────────────────┘   └───────────────────────────┘
        leaks here              the seam — nothing            never imports flang
        stay here               flang-specific lives here    query evals the ground
                                                              graph; SMT only over
                                                              D3 unknowns
```

**The one rule that gives the plan its value:** nothing on the consumer side
imports anything flang-specific. The IR is defined by our *domain* (the vision's
universe), not by flang's parse-tree node shapes.

**Litmus test for every IR field:** *"Could an LFortran adapter populate this
without contortion?"* If no, the field is leaking flang and must be reshaped.

### 2.1 IR contract (sketch — to be refined in Phase 1)

**Ontology — everything is a set or a relation.** The IR is a small collection of
**named, typed relations over interned atoms**, in the spirit of Alloy. Atoms are
scope-qualified entity identities (never bare names). Entity *kinds* are unary
relations (sets) of atoms; structural facts are binary/n-ary relations between them.
Querying is then one closed algebra (join `.`, `&`, `+`, `-`, closure `*`, inverse
`~`) over that schema — every operation takes relations and returns a relation, so
results compose. We borrow Alloy's **ontology and algebra**, *not* its solver: we
evaluate queries over one given instance, we do not enumerate models over a bounded
scope (see Q4). This keeps the IR's interface as narrow-and-deep as it gets — "a set
of relations plus a fixed operator set" — and is engine-neutral: a relation is a
predicate in Datalog and an edge set in NetworkX, so the Q4 backend choice never
touches the model.

Entity sets (unary relations of interned, scope-qualified atoms):
- `Module`, `Program`, `Subprogram`
- `Subroutine`, `Function` (with signature: ordered args of name/type/rank/kind/optional)
- `Interface` (generic name → set of specific procedures)
- `DerivedType` (parent type, type-bound bindings)

Relations:
- `calls(caller, callee)`
- `uses(scope, module)` — with only-list / rename info
- `defined_in(entity, scope)` / `contains(scope, entity)`
- `exports(module, entity)` (requires public/private — W4)
- inverse/derived (`called_by`, `imports`) computed, not stored

**Confidence is modeled by stratified relations, not by a tuple attribute (D3).**
Rather than attach a `resolved|assumed|unresolved` tag to each tuple (which makes
every relation n+1-ary and clutters every join), each confidence-bearing relation is
split into strata — e.g. `calls_resolved` / `calls_assumed` / `calls_unresolved` —
each a *pure* relation. This keeps "everything is a relation" literally true and,
more importantly, hands us the standard sound-analysis lattice for free:
- **must** = `calls_resolved` — the under-approximation; a violation here is a
  *definite* finding.
- **may** = `calls_resolved + calls_assumed + calls_unresolved` — the
  over-approximation; a violation only here is *possible*, and is exactly what the
  optional SMT layer reasons over (∃/∀ across the unknowns; VISION §3, Q4).

`unresolved` targets are kept as first-class atoms, **not** silently dropped. The one
genuinely awkward case for a flat-relational model is the ordered, typed **signature**
(a sequence of records); model it with explicit positional relations
(`arg_at(sub, i, param)`, `param_type(param, type)`, …) at the IR boundary, while
letting the frontend keep signatures record-shaped internally (principle #10 — be
pragmatic below the seam).

### 2.2 Frontend interface (sketch)

```python
class Frontend(Protocol):
    def extract(self, sources: Iterable[Path]) -> IR: ...
```

- `frontend/flang_dump.py` — Option A; absorbs all current `parse_*`, `_infer_*`,
  `level()`, regex.
- `frontend/lfortran_asr.py` — stub with the real signature raising
  `NotImplementedError`. Its existence is a *forcing function*: it keeps the IR
  honest. The day we fill it in is the day we learn whether the seam was real.

### 2.3 A second IR for Track B (sketch — gated on the pilot)

The equivalence track (VISION D6) consumes a *different projection* of the same
dumps: a per-procedure **kernel IR** — typed expression/statement trees and loop
nests, deep exactly where the relational IR is deliberately shallow. Its only
consumer is a Lean printer. Two rules, stated now so they hold later:

- **Do not bloat the relational IR.** The two IRs share the frontend layer and
  nothing else; a field that only the Lean printer needs never appears in
  `groundline/ir.py`.
- **The kernel-IR → Lean path is trusted-base code** (VISION D6): deterministic,
  small, auditable; no LLM anywhere in it.

The concrete shape is designed *after* the Track B pilot (§4) proves the endeavor
cheap enough — hand-written Lean models come first, the printer second.

---

## 3. Design principles

These principles are ordered roughly from most to least
load-bearing.

1. **Get the IR right first.** Design its state and invariants before any behavior;
   the frontend and consumers exist only to establish or rely on them. A reasoning
   layer built on the wrong abstraction can't be rescued by good code. (D2)
2. **Everything is a set or a relation.** Model facts as named, typed relations over
   interned atoms — entity kinds are sets, structure is relations, one closed algebra
   queries them (§2.1). This is Alloy's *ontology*, not its solver: we evaluate over
   one given instance, not enumerate models over a bounded scope (Q4). Encode
   confidence as stratified must/may relations, not tuple attributes. Payoff: a tiny,
   engine-neutral interface, and the sound over-/under-approximation lattice for free.
   (D3, Q4)
3. **Deep modules, narrow interfaces.** The frontend is one method —
   `extract(sources) -> IR` — hiding all of flang's text format, depth-counting,
   regex, and resolution. The interface stays far smaller than the body; we avoid a
   crowd of shallow helpers.
4. **Pull complexity down to the frontend.** Consumers (forest, Explorer, future
   query layer) never learn that flang exists. Litmus test for every IR field:
   *could a non-flang adapter populate this without contortion?* If not, it leaks.
5. **One layer, one vocabulary.** flang parse-tree terms live below the seam; the
   domain (modules, calls, types) lives at it; graph/relation terms live above. A
   flang node-string above the seam — or a NetworkX detail below it — is a bug.
6. **Partial knowledge is a value, not an error.** Incomplete resolution is the
   normal case, so it is a first-class fact: confidence
   (`resolved | assumed | unresolved`) is part of the model — stratified per #2, never
   silently dropped or invented. (D3, W2)
7. **Identity is scope-qualified, never a bare name.** No name-only lookups or
   `endswith` matching, in the model or the Explorer. (W4, W5)
8. **Domain-shaped, not codebase-shaped.** The IR models Fortran-the-language, not
   MOM6-the-codebase — no `DoublePrecision -> 'r8_kind'` MOM-isms baked in; such
   mappings, if needed, live in a consumer. General enough for any Fortran program,
   not for speculative non-Fortran inputs. (W6)
9. **Isolate faults.** One unparseable file reports and is skipped; it must not
   abort the forest.
10. **Invest at the seam, ship everywhere else.** The IR boundary is the one line
   worth perfecting because everything compounds on it; elsewhere (rendering, CLI),
   be pragmatic.
11. **Keep `VISION.md` and `README.md` honest.** Mark roadmap as roadmap.

---

## 4. Migration plan (phased)

Each phase is independently shippable and leaves the tool working.

**Phase 0 — Reset expectations.** Trim `README.md` to what exists; move the
relational/Z3/GPU material under an explicit "Roadmap / Vision" heading. Land the
docs. *(docs only)* — **DONE 2026-05-28.**

**Phase 1 — Carve the seam (the core refactor).** Decided 2026-05-29: build the
**relational IR now** (entities + relation tuple-sets per §2.1, realizing principle
#2 — not a minimal node-graph seam), and **split into 1a/1b** so each step is
independently green and the one risky step is isolated.

*Phase 1a — structural seam (pure refactor, fixtures stay no-sema):* — **DONE
2026-06-18.**
- Define the IR (§2.1) as groundline-owned types in `groundline/ir.py` — entities as
  frozen value objects keyed by scope-qualified `EntityId`; relations as tuple-sets;
  `callees`/`callers` computed, not stored. Single `calls` relation (no confidence
  strata yet — that's Phase 2); `unresolved_calls` kept first-class.
- Create `frontend/` package + `Frontend` protocol (`extract(sources) -> IR`); move
  all of `parse_tree.py` into `frontend/flang_dump.py`. The frontend may keep the
  existing node/registry rep *internally* and project to IR at the boundary
  (principle #10 — pragmatic below the seam).
- Add the `lfortran_asr.py` stub (raises `NotImplementedError`).
- Make `ParseForest`/`Explorer` consume the IR only (graph nodes become IR entities).
- Add per-file fault isolation (W3): `extract()` collects `FileError`s, never aborts.
- Tests assert on the IR; the direct `resolve_interface_procedures`/
  `_procedure_matches` tests move to `tests/frontend/` (below-seam concerns).

*Phase 1b — with-sema switch (the one non-relocation step):* — **DONE 2026-07-29.**
Scope note: a *format adaptation only* — the frontend now accepts with-sema line
shapes (unparse annotations, the extra `Expr` nesting) and all fixtures are
regenerated with `-fdebug-dump-parse-tree`, while the hand-rolled resolution engine
and the IR's call semantics are left intact for Phase 2. Sema's resolved call text
is *recorded* below the seam and unused. Equivalence was checked both ways: the six
sema-clean fixtures project onto a byte-identical IR from either dump variant, and
the real MOM6+FMS2 corpus went from 346 unparseable files to 0. See `DEVLOG.md`.
- **Spike first** — regenerate one fixture (e.g. `test_interface_basic`) with-sema and
  run the relocated parser against it; D4 validated dump *generation*, not that the
  string-matching parser *consumes* with-sema output (resolved-symbol annotations
  change line strings; cross-module fixtures need `.mod` ordering).
- Adapt the frontend parsing as the spike reveals, then switch fixtures to
  `-fdebug-dump-parse-tree` (D4) so tests and production parse the same variant.

**Phase 2 — Soundness & resolution quality.** — **DONE 2026-07-29.**
- Consume *resolved* names from sema's unparse annotations, retiring the
  hand-rolled inference engine (W1, W6). `-fdebug-dump-symbols` was not needed
  (Q2). No-sema input support dropped (D4; maintainer decision).
- The confidence strata of §2.1 (D3): stored `calls_resolved` / `calls_assumed` /
  `calls_unresolved` relations, `calls` (may) and `calls_must` (must) as computed
  views; `unfound_*` became first-class `unresolved` edges to `defined=False`
  entities (W2).
- Scope/visibility-correct resolution (AccessStmt public/private, use-chain
  only-lists/renames, mangled-name demangling); `endswith` matching killed (W4).
- Acceptance on the production corpus: 458 files, 0 errors; resolved 22,764 /
  assumed 114 / unresolved 1,578 — the drop from the Phase 1b may-count is the
  eliminated generic fan-out, verified edge-by-edge (see `DEVLOG.md`).

**Phase 3 — Explorer correctness.** — **DONE 2026-07-30.**
- Scope-qualified node identity (W5) was already true after Phase 1a but nothing
  pinned it; `test_name_collision` (three modules, one routine name, three USE
  forms) now pins no-merge in the cytoscape elements, the selector options and
  `get_call_graph`. Its USE renames also close a D7 manifest gap.
- Confidence is rendered (D3): call-edge line style is the stratum (solid
  resolved / dashed assumed / dotted+muted unresolved), `defined=False` targets
  are ghosted, interface-membership edges are visually distinct (structure, not
  calls), and a legend makes the encoding discoverable. Direction stays the
  colour channel, so the two encodings compose.
- The graph-element construction moved out of the widget into
  `groundline/graph_view.py` — pure IR → element dicts, no ipywidgets import — and
  is unit-tested there (`tests/test_graph_view.py`); `explorer.py` keeps only the
  stylesheet, legend and event wiring (principle #10). The stratum labels
  `resolved|assumed|unresolved` and the per-edge lookup live at the seam
  (`IR.call_confidence`, a computed view — the strata stay relations, per D3), so
  no consumer re-derives set membership.
- `ParseForest.get_call_graph()` attaches `confidence` to every NetworkX edge and
  takes `must_only=True` to build from the must view (Phase 5 will want both).

**Phase 4 — Make it CI-usable.** A CLI that runs a query/invariant over a forest
and exits non-zero on violation — the minimum for the README's "CI-enforceable"
claim (W8).

**Phase 5+ — The vision proper.** The relational query layer over the IR is the
core (ground-graph evaluation: closure, difference, reachability), then the
GPU-porting frontier tooling on top of it. An SMT (Z3) layer is an *optional*
add-on scoped to reasoning over D3 unknowns (∃/∀ over `assumed`/`unresolved`
edges), not the main checker — see Q4. (Out of scope for detailed planning until
Phases 1–2 land; the IR + confidence model is the prerequisite.)

**Track B — kernel equivalence by proof (parallel, gated on a pilot; VISION D6).**
Independent of Phases 2–4 — its only input is the dumps, so it can run alongside
them — but it must not displace them (Phase 2's confidence model is what makes the
frontier-and-gate story real).
- *Pilot (timeboxed, no tooling):* — **DONE 2026-07-30, SUCCEEDED.** Hand-written
  Lean 4 / Mathlib models of `PPM_limit_pos`
  (Fortran: `submodules/MOM6/src/core/MOM_continuity_PPM.F90`;
  C++: `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp`); both the
  point lemma and the `do concurrent` ≡ `ParallelFor` iteration schema are
  machine-checked over ℝ (`lean/pilot/Pilot/PpmLimitPos.lean`; axioms audited —
  no `sorry`). The point lemma proved near-mechanical (~5 lines) for kernels in
  the TIM point-function style. See the DEVLOG entry for the Q5 answers surfaced
  and the honest caveats (hand-written models; friendliest kernel shape).
- *Then:* automate the printer (deterministic dump → kernel IR → Lean; §2.3), one
  construct at a time in the D7 corpus style (construct → golden Lean model).
  **First milestone landed 2026-07-30:** `groundline/kir.py` +
  `frontend/flang_kernel.py` + `lean_printer.py` regenerate the pilot model from
  the *production* MOM6 dump, and `Pilot/Fidelity.lean` proves generated ≡
  hand-written **by `rfl`** — so generated-from-dump ≡ C++ port, transitively,
  all machine-checked. Supported subset = the pilot kernel's shape; everything
  else refuses (`UnsupportedConstruct`). See the DEVLOG entry.
  **Second kernel banked 2026-07-31:** `PPM_limit_CW84` / `ppm_limit_cw84_point`.
  The subset widened by exactly the three constructs CW84 needs — logical IF
  statements (R1139), unary minus, and the restricted control-flow join
  (statements after an IF, supported only for a single-branch IF whose branches
  assign solely to outputs; merged per variable into inline conditionals with
  *sequentially threaded* state). The maturing pattern: no hand-written Fortran
  model anymore — the point lemma is proved directly against the GENERATED
  model (`Pilot/PpmLimitCw84.lean`). Considered and OUT of scope:
  `thickness_to_dz` (MOM_interface_heights.F90) — its loops are plain nested
  `do`, not `do concurrent`, and extending pointize to plain DO nests is a
  semantics decision reserved for the user. See the DEVLOG entry.
  **Clang side landed 2026-07-31:** `frontend/clang_kernel.py` (clang
  `-ast-dump=json` → the *same* kernel IR; the C++ point kernels are already
  per-point, so no pointize — `functionalize` and the printer are reused
  unchanged, and CW84's join reused the existing merge machinery).
  `lean/pilot/generate.py` now emits `Pilot/GeneratedCpp.lean` from the
  production TIM header with the pinned clang invocation stamped as
  provenance, and `Pilot/FidelityCpp.lean` proves generated-C++ ≡ hand-written
  C++ for both kernels, plus the fully-mechanical chain theorems
  generated-C++ ≡ generated-Fortran. **Both sides of every banked equivalence
  are now machine-produced**; the hand-written C++ models (`ppmLimitPosC`,
  `ppmLimitCw84C`) are no longer load-bearing — they remain as audited,
  machine-checked references. Retiring them entirely would mean restating the
  pilot's point lemmas directly between the two generated models (the chain
  theorems already are that statement) and rewriting the `PpmLimit*.lean`
  narrative files that cite the hand models as documentation; there is no
  verification reason to do so — they cost nothing and keep the
  human-readable anchor.
  **5-of-5 landed 2026-07-31:** the three remaining TIM point kernels —
  `edge_thickness_upwind`, `thickness_to_dz_3d_boussinesq`,
  `thickness_to_dz_3d_nonboussinesq` — banked, covering the **entire current
  TIM kernel population**, via two extraction extensions that widen where a
  kernel may live and what it may reference, not what its body may compute.
  (1) *Plain-DO pointization*, superseding the CW84-era out-of-scope note on
  `thickness_to_dz`: a plain, perfectly nested `do` nest pointizes under the
  array-index gate plus an own-cell write gate (reductions/recurrences still
  refuse), and its **standing semantic license is a proved schema lemma**
  (`Pilot/SeqSchema.lean`): the honest sequential fold of a point function
  over any duplicate-free complete enumeration of the box equals the
  pointwise map — where `do concurrent` supplies an assertion, plain DO now
  supplies a proof. (2) *Inline-loop addressing + component reads*: loop
  nest #N of a subroutine by source-order ordinal (dumps carry no line
  numbers), with driver-supplied def names recording the pairing, and
  loop-invariant scalar components / loop-indexed component arrays becoming
  synthesized scalar `in` params (`GV%H_to_Z` → `h_to_z`,
  `tv%SpV_avg(i,j,k)` → `spv_avg`; collision-checked, refuse-don't-rename).
  All three point lemmas are `rfl` between the two generated sides; the C++
  frontend needed nothing. See the DEVLOG entry for the branch↔kernel
  pairings and the two source-vs-prompt discrepancies it records.
  **Conclusion / packaging landed 2026-07-31** (no new proof content): the
  pipeline is now config-driven and portable. The banked pairs live in a
  declarative kernel manifest (`kernels.toml`; production instance
  `examples/turbo-stack.kernels.toml` — the only place machine paths exist;
  the package has no built-in defaults), both frontends sit behind a uniform
  `KernelFrontend` seam (`frontend/kernel_base.py`: typed
  `FortranKernelSpec`/`CppKernelSpec`, one `extract(spec) -> Kernel` method,
  mirroring the relational `Frontend`), and the old `lean/pilot/generate.py`
  driver is replaced by `groundline/kernel_bank.py` plus a `groundline` console
  script (`groundline kernel list/show/generate/verify`; `verify` — regenerate,
  byte-diff against the committed files, `lake build` — is the CI gate). All
  generated defs verified byte-identical across the migration.
  `examples/quickstart/` is the committed portability proof (toy pair, its
  with-sema dump committed, AMReX-free standalone C++ header), validated by a
  bare-clone + fresh-venv acceptance run outside turbo-stack. See the DEVLOG
  entry.
  **User manual landed 2026-07-31** (Track B conclusion 2 of 2): a
  comprehensive MkDocs Material site — concepts, tiered install, quickstart,
  how-tos, four case studies retold from the DEVLOG, full reference including
  the complete refusal catalog, and an honest limits page. Site source
  `manual/` + `mkdocs.yml`; deployed to GitHub Pages by
  `.github/workflows/docs.yml` (one-time Pages setup checklisted in
  `PUBLISHING.md`; URL https://alperaltuntas.github.io/groundline/). The build
  is fully static: every shown output is pre-rendered from the real pipeline
  into committed `manual/snippets/` files (regenerable via
  `render_snippets.sh`) and pinned against fresh runs by
  `tests/test_manual.py`, so the manual cannot rot silently. `docs/` remains
  the engineering record; the site links to it. See the DEVLOG entry.
  **Function-result kernels landed 2026-09-05** — the first construct pulled
  in by TIM PR 36 (the AMReX port of the continuity mass-flux family). A
  Fortran `function … result(r)` and a `Real`-returning C++ point function
  extract as kernels whose single output is the result: a `result`-intent
  parameter **the caller supplies no value for** — unbound until assigned, so a read
  before assignment, a path that never assigns it, and a one-sided join all
  refuse; a result alongside `inout`/`out` outputs refuses on both sides. C++
  `return` is admitted in tail position only. `ratio_max` /
  `ratio_max_point` banked as the sixth pair (point lemma `rfl`; no
  previously generated def changed). The PR's other primitives
  (`flux_elem_point`, `continuity_convergence_point`) and its column kernels
  are the planned next tiers (DEVLOG 2026-09-05).
  **`flux_elem` banked 2026-09-05 (later)** — the PPM face flux, the physics
  every mass-flux column kernel calls per layer; the seventh pair. Three
  constructs entered, two of them user-licensed semantics decisions: the
  **generalized control-flow join** (branches run sequentially against copies
  of the state, elseif chains and nested IFs merge recursively, locals
  assigned in branches are `Let`-bound after the join, a local undefined on
  some path is dropped when dead and refused when read — the CW84 one-shape
  rule is now a special case and its def is byte-identical), **Bool inputs**
  (logical/`const bool` parameters as bare guards, `Bool` binders), and
  **mutable C++ locals** (bare declarations assigned later). Unreferenced
  derived-type dummies are dropped in whole-procedure mode; a local read
  before assignment now refuses in Python rather than in Lean. Point lemma:
  `simp only [defs, neg_mul]` — the only delta is the documented unary-minus
  parse asymmetry.
  **The convergence update banked 2026-09-05 (later still) — Tier A
  complete:** all four Fortran nests of `continuity_{zonal,merdional}_convergence`
  against the one C++ primitive `continuity_convergence_point`, via three
  extraction rules: **rule C, read-only stencils** (`uh(I-1,j,k)` → input
  `uh_im1`; licensed narrowly — arrays the nest never writes, `do concurrent`
  nests only; a write to a neighbor cell or a read of a written array's
  neighbor refuses as a recurrence, which is where the committed recurrence
  fixture now refuses), **rule B widened** (component arrays indexed by a
  subset of the loop indices), **rule D** (nest-invariant locals as inputs);
  plus `optional` dummies, and on the C++ side `amrex::max`/`min` with the
  `NoOp` cast and temporary-materialization wrappers their `const T&`
  signature produces. Four `rfl` point lemmas; kernel-level lifts with the
  stencil as an explicit neighbor map. Every primitive of TIM PR 36 now
  carries a theorem; the column kernels (Tier B) are next.
- *Later:* kernels with cross-iteration structure (k-recurrences → induction —
  the genuinely sequential shapes the plain-DO gate refuses, e.g.
  `find_dz_for_eta`'s pressure accumulation), reductions (scalar
  accumulators), masks/wet-dry logic, and more C++ surface (e.g. `pow` calls,
  ternaries) as real kernels demand it.

**Ongoing — conformance corpus (D7).** Formalize `tests/f90/` into the corpus: a
manifest (construct → fixture → parser code path), a coverage rule (every parse
branch in the frontend has ≥1 fixture), and the two assertion tiers (dump
snapshots = early warning; IR assertions = the contract). The manifest landed
with Phase 2 (`tests/f90/MANIFEST.md`), including an honest list of parser paths
that still lack a fixture; closing those gaps is the ongoing part.

**Deferred — Frontend upgrade exploration (much later, optional).** Evaluate an
alternative frontend — LFortran ASR / fparser2 ("Option B"), or flang's own more
structured outputs / programmatic API ("Option C") — and swap it in behind the
Phase 1 seam if it improves resolution precision or removes dump-format fragility.
This is explicitly *not* near-term: with-sema already provides full-coverage facts
(D4), and the seam makes the swap localized whenever we choose to do it. Revisit
only if dump-format churn actually bites (see Q3) or we want a precision upgrade
the dump can't give. Resolves D5.

---

## 5. Open questions / to validate

- **Q1 (live):** How stable has flang's dump format been across recent LLVM
  releases? This is now the *most* relevant resilience question — it sizes how much
  fixture/format-version defense we need within Option A, and is the trigger that
  would reopen the deferred frontend-upgrade exploration. *Phase 1b sharpened this
  rather than answering it:* one dump-variant change moved resolution into an
  unparse *string*, so the facts Phase 2 will depend on are carried by a
  pretty-printer with no stability contract — including its name mangling
  (`module$module$specific`). Fixtures now record the generating `flang --version`
  (`tests/f90/PROVENANCE`) so a format shift shows up as a version delta; that is
  detection, not defense. The defense is the conformance corpus (D7): per-construct
  minimal examples that turn an LLVM upgrade into a bounded list of localized,
  independently fixable breaks. *Phase 2 update:* the mangling rule is now
  load-bearing and documented where it is implemented
  (`frontend/_flang_text.py::demangle` — `imported$owner$specific`, where the
  owner module may hold the name by use-association rather than define it) and
  pinned by the `test_private_specifics` fixture, so a mangling change breaks a
  named test rather than silently degrading resolution.
- **Q2: ANSWERED (2026-07-29) — yes, in the textual output.** The with-sema dump's
  unparse annotation on each statement carries the *resolved* specific procedure —
  for generic subroutine calls, generic function references, and type-bound
  generics alike — while the structured child still shows the generic name. So
  `-fdebug-dump-symbols` is not needed for this, and most of `_infer_*`/`resolve_*`
  becomes deletable in Phase 2. Two caveats for that work: the resolved name may be
  mangled (see Q1), and the annotation is per-*statement*, so a statement
  containing several calls yields one string to attribute across them.
  *Phase 2 postscript:* both caveats resolved better than expected — the mangling
  is a gift (it names the owning module, exactly what scope-qualified identity
  needs), and the per-statement worry dissolved because every `Expr` node carries
  its own annotation, so each function reference reads the exact resolved text of
  its *own* call from its parent `Expr` line. Static type-bound dispatch is also
  resolved in the text (the object hoisted into the argument list); only genuine
  dynamic dispatch keeps the `obj%binding(...)` shape.
- **Q3 (deferred, gates D5):** Does LFortran's ASR — or fparser2 — actually ingest
  FMS+MOM6 at current maturity? Only relevant if/when we pursue the deferred
  frontend-upgrade exploration; not near-term.
- **Q4:** The reasoning split. The facts are *one fixed ground graph*, so invariant
  checking is query *evaluation* (reachability, closure, set difference), not Alloy's
  search over a space of small models — a recursive relational engine (home-grown, or
  a Datalog/Soufflé backend) is the natural core and scales to a whole codebase. An
  SMT solver (Z3) is *not* the workhorse here and encodes the ground graph poorly;
  it earns its place only over the D3 *unknowns* — "does some / every resolution of
  the `assumed`/`unresolved` edges violate the invariant?" Open: is that residual
  SMT layer worth building, and where exactly is the Datalog↔SMT handoff? Affects
  Phase 5 design. **Sequencing:** start the query layer in-process with NetworkX +
  Python set ops (the README's relational operators map onto it almost one-to-one,
  and the facts are a single fixed graph); adopt a real Datalog engine — CozoDB
  (embedded, Python bindings) first, Soufflé (standalone, compiles to C++) only if
  scale demands — as a *localized* upgrade once invariant rules outgrow hand-written
  traversals. If the query layer consumes the IR through a thin interface, that swap
  is contained, exactly like the frontend swap (D2). So none of this needs deciding
  before Phase 1.
- **Q5 (Track B; the pilot exists to surface these):** the kernel-IR / Lean
  modeling choices. How to model `intent(inout)` scalars (state-passing vs.
  functional returns — Logos proved fold ≡ mutating loop, so both shapes are
  known-provable); whether one iteration schema covers `do concurrent` variants
  (masks, non-unit strides) or each needs its own lemma; how array arguments and
  index ranges are represented so the schema composes with the point lemma; and on
  the C++ side, `clang -ast-dump=json` vs. libclang as the ingestion route. None
  of these needs deciding before the pilot — hand-writing the `PPM_limit_pos`
  models *is* how they get answered concretely.
  *Pilot postscript (2026-07-30):* three answered — `intent(inout)` scalars as
  functional result-pairs work with zero friction; the schema over an abstract
  index type `ι` (arrays as `ι → ℝ`) covers the mask-free `do concurrent` case
  and lifts the point lemma by `funext`; ℝ's decidable-order instances make the
  `if`-guards unremarkable. Still open: masks/strides, reductions/k-recurrences
  (need induction, not a ∀-schema), and the clang-side ingestion route.

---

## 6. Glossary

- **Option A** — frontend built on flang's textual parse-tree dump (current
  direction).
- **Option B** — frontend built on a semantic-IR library (LFortran ASR / fparser2).
- **IR** — groundline's own intermediate representation; the seam between frontends
  and consumers.
- **sema / no-sema** — flang dumps *with* / *without* semantic analysis (name &
  type resolution, generic binding).
- **confidence** — `resolved | assumed | unresolved` tag on a relation (D3).
- **frontier** (vision) — `calls*(GPU_Port) − GPU_Port`; the minimal interface to
  port next.
- **Track A / Track B** — the top-down structural/relational track (Phases 0–5)
  / the bottom-up kernel-equivalence-by-proof track (D6, gated on its pilot).
- **kernel IR** — the per-procedure semantic IR (typed expression/statement
  trees) consumed only by the Track B Lean printer (§2.3); distinct from *the*
  IR, which is relational and whole-codebase.
- **conformance corpus** — per-construct minimal examples + version-stamped dump
  snapshots + IR assertions (D7); the format-stability defense for Q1.
