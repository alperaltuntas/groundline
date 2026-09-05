# What is groundline?

groundline is a **structural exploration tool for large Fortran HPC codebases**. It
consumes LLVM/flang parse-tree dumps and builds a graph-based model of a project's
modules, subprograms, interfaces, derived types, USE dependencies, and call
relationships, which you can browse and visualize interactively in Jupyter.

It is an early-stage **prototype**, currently used primarily for the TURBO project.
The longer-term ambition — to grow groundline into a relational reasoning system
that can *prove* architectural properties (e.g. for safe GPU modernization of
MOM6) — is described under [Roadmap / Vision](#roadmap--vision) below and is **not
yet implemented**.

> **Documentation.** This README describes what groundline does *today*. The
> forward-looking plan lives in `docs/`:
> - [`docs/VISION.md`](docs/VISION.md) — goals and the strategic decisions behind them.
> - [`docs/DESIGN.md`](docs/DESIGN.md) — target architecture, the IR seam, and the phased roadmap.
> - [`docs/DEVLOG.md`](docs/DEVLOG.md) — append-only log of build/parsing roadblocks and how they were resolved.
>
> **User manual:** <https://alperaltuntas.github.io/groundline/> (source under
> `manual/`; see `PUBLISHING.md`).

## Kernel verification — equivalence by proof

Alongside the structural exploration below, groundline has a second,
**working** face: it proves that TURBO's C++/AMReX (TIM) ports of MOM6
kernels compute the same mathematics as the legacy Fortran — machine-checked
in Lean 4 / Mathlib, **over the reals** (algorithmic equivalence, deliberately
not bit-for-bit floating point). Both sides of every theorem are generated
from compiler syntax trees (flang with-sema dumps, clang JSON ASTs) by a
small deterministic translator that refuses anything outside its audited
subset. The pipeline is driven by a declarative manifest and the `groundline
kernel list/show/generate/verify` CLI; today it covers six kernel pairs — the
entire pre-mass-flux TIM point-kernel population (5 of 5) plus the first
primitive of the continuity mass-flux port — each with a checked equivalence
theorem and a clean axioms audit. **The [manual](https://alperaltuntas.github.io/groundline/)
is the guided tour** — concepts, a self-contained quickstart
(`examples/quickstart/`), and case studies retold from the development log.

---

## What it does today

1. **Parse-tree analysis.** Reads flang-generated parse-tree dump files and extracts
   structural information from Fortran code:
   - modules, programs, and subprograms
   - subroutines and functions
   - interfaces and derived types
   - dependencies: USE imports, calls, and containment relationships
2. **Dependency / call graph generation.** Builds module-dependency graphs and call
   graphs as NetworkX structures, rendered as interactive network visualizations
   via ipycytoscape.
3. **Interactive explorer.** A Jupyter widget-based interface (the `Explorer` class)
   to browse and filter code elements by category (Subroutine, Function, Interface,
   Derived Type), search specific program units, and visualize their relationships.
4. **Multi-project analysis.** The `ParseForest` class analyzes multiple parse trees
   together, for codebases spanning several components (e.g. MOM6 + its libraries).

Call resolution is read from the compiler's semantic analysis (with-sema dumps),
and every call fact carries a confidence stratum — `resolved` / `assumed` /
`unresolved` — with *may* and *must* views derived from the strata. See
`docs/DESIGN.md` §2.1.

---

## Working with groundline

groundline is a prototype; the notebooks under `notebooks/` are the guided tour —
see [`notebooks/README.md`](notebooks/README.md) for the index, the launch
instructions, and the conventions. In short:

```bash
conda env create -f environment.yml    # creates the `groundline` env and installs the package
conda activate groundline
jupyter lab notebooks/
```

(A plain venv works too — `python3 -m venv .venv && .venv/bin/pip install -e '.[dev]'`;
if a broken `~/.local` user site shadows the environment, add `PYTHONNOUSERSITE=1` —
see [`notebooks/README.md`](notebooks/README.md).)

`01_getting_started.ipynb` runs anywhere off the committed `tests/f90` fixtures —
no dump collection needed. Notebooks 02–04 read a directory of parse-tree dumps: by default
the MOM6 + FMS2 one on NCAR's glade filesystem, overridable with the
`GROUNDLINE_DUMPS` environment variable (to generate dumps for your own code,
see `tests/f90/gen_ptree_files.sh` and the build pipeline notes in
`docs/DEVLOG.md`).

---

## Key classes and components

- **`groundline.ir.IR`** — the seam: entities (scope-qualified atoms) plus
  relations (tuple-sets) over them; nothing flang-specific appears in it.
- **`groundline.frontend`** — everything flang-specific, behind one method:
  `FlangDumpFrontend.extract(sources) -> IR`.
- **`ParseForest`** — flang-agnostic consumer; builds NetworkX module-dependency
  and call graphs from the IR (call edges carry their confidence stratum).
- **`groundline.graph_view`** — pure neighbourhood → renderable-elements builder
  (the testable half of the Explorer; no widget imports).
- **`Explorer`** — interactive Jupyter widget for code exploration.

## How it works

1. **Input.** Takes flang-generated with-sema parse-tree dump files as input
   (typically under a build directory such as `.../flang_ptree/`).
2. **Parsing pipeline.** The frontend scrapes each dump line by line and projects
   the result onto the groundline-owned IR at the boundary. *(Text scraping is
   inherently fragile; the IR seam contains that fragility — a format change is a
   frontend fix, invisible to consumers — and the conformance fixtures under
   `tests/f90/` localizes it to named constructs. See `docs/DESIGN.md`.)*
3. **Relationship analysis.** USE dependencies, containment, interfaces, and
   call relationships — read from the compiler's resolution and stratified by
   confidence, never silently guessed.
4. **Visualization.** Uses NetworkX for graph structures and ipycytoscape for
   interactive visualization in Jupyter.

## Dependencies

- Python >= 3.11
- NetworkX (graph analysis)
- Jupyter ecosystem: jupyterlab, ipywidgets, ipycytoscape
- z3-solver — present as a dependency for the planned reasoning layer (see Roadmap)

## Why was groundline created?

Large Fortran HPC codebases (climate models, CFD codes, etc.) often have thousands
of source files, complex module hierarchies, intricate dependencies, and legacy
code with unclear structure and sparse documentation. groundline aims to help with:

1. **Code understanding** — grasp the structure of complex Fortran codebases.
2. **Dependency analysis** — see how parts of the code interact.
3. **Refactoring support** — surface the structure needed to refactor safely.
4. **Documentation** — generate visual documentation of code architecture.
5. **Navigation** — speed up comprehension of large codebases.

Target use cases: HPC software development, systematic code review/analysis, and
planning legacy-code modernization.

---

# Roadmap / Vision

> **Everything below this line is aspirational** — it describes where groundline is
> headed, not what it does today. It is preserved here as the detailed design
> sketch for the reasoning layer; the condensed, decision-level version lives in
> [`docs/VISION.md`](docs/VISION.md), and the architecture/roadmap that gets us
> there is in [`docs/DESIGN.md`](docs/DESIGN.md). None of the query/constraint
> syntax shown below is implemented yet.

The long-term vision is to turn groundline from a structural explorer into a
**relational reasoning system over Fortran programs** — very much in the spirit of
the Alloy model checker, but grounded in real compiler-derived facts rather than
abstract models.

This will include a declarative query and constraint language over the program
graph, based on sets, relations, and quantification.

Where the universe is:

 - Modules
 - Subroutines
 - Functions
 - Interfaces
 - Derived types
 - Calls
 - USE dependencies
 - Containment relationships

And the relations are things like:

 - calls
 - called_by
 - uses
 - defined_in
 - contains
 - exports
 - imports

With relational operators:

 - `.`	relational join
 - `&`	intersection
 - `+`	union
 - `-`	difference
 - `*`	transitive closure
 - `~`	inverse relation

Example:
   ```
   s.calls            -- callees of s
   ~calls.s           -- callers of s
   s.(calls*)         -- transitive callees

   -- quantification:
   all s: Subroutine |
       some f: Function |
           f in ~calls.s
   ```

## Reasoning

The facts form **one fixed graph** (the program), so the workhorse is a **relational
query layer** that *evaluates* properties over that graph — reachability, transitive
closure, set difference — and returns the witnessing tuples (the exact subroutine /
call chain) as the counterexample. This is query evaluation, not search over a space
of models; a recursive relational engine (Datalog-style; see `docs/DESIGN.md` Q4) is
the natural fit and scales to a whole codebase.

An SMT solver (**Z3**) is an *optional* add-on, not the main engine. It earns its
place only where facts are uncertain — the `assumed` / `unresolved` edges of the
confidence model — turning those unknowns into the questions "is there *some*
resolution that violates the property?" or "does *every* resolution satisfy it?".
That residual partial-knowledge reasoning is the only part that resembles Alloy's
model-finding; the bulk is settled by the query layer.

Together this makes groundline a program-logic checker for Fortran architecture,
enabling:

 - architectural invariants
 - modernization safety checks
 - refactoring preconditions
 - GPU kernel isolation reasoning
 - CI-enforced structural properties

## Example Use Case: Code Modernization for GPU Offloading and Performance Portability

### A. Identifying GPU-Candidate Kernels (Leaf & Near-Leaf Routines)

**Question:** Which routines are structurally eligible to become AMReX GPU kernels?

**Property:** A GPU kernel candidate must:
- Not call MPI
- Not perform I/O
- Not allocate memory
- Only call other GPU-safe routines

**Specification sketch:**
```
gpu_kernel_candidate(s) iff
   no f in s.(calls*) |
      f in HostOnly
```

### B. Enforcing Host / Device Separation

**Question:** Have we accidentally introduced host-only calls into device-callable
code? (This happens all the time during incremental porting.)

**Property:**
```
no s: DeviceCallable |
    some f in s.(calls*) |
        f in HostOnly
```

**Outcome:**
- Counterexample = exact call chain
- CI-enforceable structural invariant

### C. Ensuring Kernel Call Graph Closure

**Question:** Does every GPU kernel only call routines that have been ported?

**Property:**
```
all s: GPU_Kernel |
    s.(calls*) in GPU_Port
```
This is transitive closure reasoning, which most tools cannot express.

### D. Detecting Hidden Global State Access

**Question:** Which routines access module-level state that breaks GPU execution?

**Relations:**
- accesses_global : Subroutine -> ModuleVariable
- defined_in : Variable -> Module

**Property:**
```
no s: GPU_Kernel |
    some v in s.accesses_global |
        v notin DeviceAccessible
```

This lets us identify refactoring targets and justify moving state into AMReX data
structures.

### E. Mapping Physics vs Infrastructure Boundaries

**Question:** Are physics kernels accidentally depending on infrastructure layers?
(This is architectural drift and kills performance portability.)

**Property:**
```
no s: Physics |
    some f in s.(calls*) |
        f in Infrastructure
```

### F. Ensuring AMReX-Compatibility of Call Signatures

**Question:** Do GPU-callable routines obey AMReX calling conventions?

**Relations:**
- has_argument : Subroutine -> Argument
- argument_type : Argument -> Type

**Property:**
```
all s: GPU_Kernel |
    all a in s.arguments |
        a.type in {Real, Integer, AMReXArray}
```

Now signature correctness becomes checkable, not aspirational.

### G. Detecting Accidental Synchronization Points

**Question:** Where do we accidentally force host/device sync?

**Property:**
```
some s: GPU_Kernel |
    some f in s.(calls*) |
        f in SynchronizingCall
```

**Result:** exact routine + call chain — an immediate performance red flag.

### H. Supporting Incremental Porting Strategy

**Question:** What is the minimal cut to port next? (This is a graph problem, not a
coding problem.)

**Query:**
```
frontier = calls*(GPU_Port) - GPU_Port
```

This gives us the next candidates to port and objective progress metrics.

## CI-Enforceable Structural Contracts

Once the logic layer exists, we can write architecture tests:
```
assert no_cycles_in module_dependency_graph
assert all GPU_Kernel ⊆ GPU_Port
assert no DeviceCallable calls HostOnly
```

This would let us state: *"This refactor is structurally safe"* — a new capability
in Earth system modeling software engineering. The headline framing:

> "We use a relational program logic to enforce architectural invariants during GPU
> modernization of MOM6."

## More on Supporting Incremental Porting Strategy

1. **Reframing the problem.** Incremental GPU porting is not "convert routines one
   by one." It is *a sequence of graph cuts that monotonically expand a GPU-safe
   subgraph while preserving global correctness and performance invariants.*

2. **The program as a graph with a moving frontier.** Model the codebase as a
   directed graph: nodes = subroutines/functions, edges = calls, labels =
   properties (GPU-safe, host-only, MPI, …). At any time we have `GPU_Port`
   (already ported), `HostOnly` (cannot be ported), and `Unknown` (everything
   else). The frontier is:
   ```
   frontier = calls*(GPU_Port) - GPU_Port
   ```
   the minimal interface between what is already device-safe and what still blocks
   expansion. This frontier is not heuristic — it is structurally minimal.

3. **What "minimal cut" really means here.** We are not cutting the graph
   arbitrarily; we are looking for the smallest set of routines whose transformation
   unlocks further GPU expansion. Formally: a minimal set of nodes whose inclusion
   into `GPU_Port` strictly reduces the size of the frontier — a partial order over
   refactorings.

4. **Classifying frontier nodes (the real power).** Once we compute the frontier,
   groundline + logic can classify each node:
   - **Pure blockers (easy wins)** — no MPI, no I/O, no global state, just not yet
     ported: `easy = frontier - HostOnly - GlobalAccess - SyncPoints`. Low-risk,
     high-reward.
   - **Structural blockers (refactor required)** — access module state, non-AMReX
     args, mix physics/infrastructure: `structural = frontier & GlobalAccess`. Tells
     you where to refactor, not port blindly.
   - **Hard blockers (design decisions)** — MPI, I/O, synchronization:
     `hard = frontier & HostOnly`. Identifies where architectural boundaries must be
     drawn.

5. **Stepwise refactoring strategy.**
   - **Step 0 — Baseline:** compute `calls*`, tag obvious HostOnly routines,
     establish invariants.
   - **Step 1 — Seed the GPU subgraph:** pick a small obvious kernel set, e.g.
     `GPU_Port = {tracer_update, advect_velocity}`, and verify
     `assert no s in GPU_Port calls HostOnly`.
   - **Step 2 — Compute frontier:** `frontier = calls*(GPU_Port) - GPU_Port`
     answers "what must be addressed next?"
   - **Step 3 — Rank frontier by portability cost:** with `violates(s) -> {MPI, IO,
     Global, Sync}`, define `cost(s) = |violates(s)|` for a quantitative roadmap.
   - **Step 4 — Transform one equivalence class at a time:** e.g. all routines that
     only violate GlobalAccess — refactor them together (move state into AMReX data,
     change signatures), avoiding whack-a-mole.
   - **Step 5 — Expand `GPU_Port` and recompute:** the loop
     `analyze -> refactor -> verify -> expand -> repeat`, each iteration smaller,
     safer, and provably monotonic.

6. **Comparison to traditional porting.** Traditional: pick "important" routines,
   port them, discover blockers late, backtrack. This approach: make blockers
   explicit, order work by structural necessity, prevent wasted effort.

7. **Making this CI-enforceable.** Assert `frontier_size decreases each release`, or
   `no new HostOnly edges cross into GPU_Port` — a regression test for modernization
   progress.

8. **Generalizing beyond GPUs.** The same strategy applies to OpenMP→GPU,
   Fortran→C++ kernels, monolithic→layered refactors, introducing autodiff, and
   enforcing purity/reentrancy. It is a general transformation calculus for
   scientific software.

**In summary:** we treat GPU modernization as a monotonic expansion of a verified
subgraph, guided by relational analysis.
