# The two frontends

Both frontends implement the same seam — `extract(spec) -> Kernel` — and
produce the same [kernel IR](../concepts/kernel-ir.md); everything below the
seam is format-specific, everything above it is shared. Both are trusted-base
code: deterministic, structural, refusing.

## Why two different input formats?

At first glance the asymmetry looks arbitrary: the Fortran side reads flang's
*text* parse-tree dump, while the C++ side consumes clang's *JSON* in
memory. Couldn't both use JSON, or both use with-sema dumps? The short
answer is no — and the asymmetry is each compiler met on its own terms:

- **flang simply has no JSON AST dump.** Its `-fdebug-dump-parse-tree` text
  format is the only complete serialization flang offers of the parse tree
  after semantic analysis. There is no machine-oriented alternative to
  switch to.
- **clang's JSON _is_ its semantic tree.** clang runs semantic analysis
  before dumping, so `-ast-dump=json` already gives exactly what the
  with-sema flang dump gives: a post-sema syntax tree with names and types
  resolved. clang does also have a *text* AST dump, but that one is a
  pretty-printed debugging aid for humans; the JSON form is the one meant for
  tools. Parsing the text form instead would gain no uniformity worth having
  — just a more fragile parser.

So the two frontends already consume the same *thing* — the compiler's
post-semantic-analysis syntax tree — through the best machine-readable
serialization each compiler provides. The remaining difference is **when the
compiler runs**, and that is a property of the *kernel*, not the language:

- A **standalone** file compiles on demand on either side: clang always runs
  fresh on the C++ `source` (and must — its JSON contains node IDs that are
  memory addresses, nondeterministic across runs, so saved JSON dumps are
  useless as fixtures anyway), and flang runs fresh the same way on a
  Fortran `source` entry. The quickstart works like this on both sides.
- A Fortran file that USEs other modules can only be dumped after those
  modules' `.mod` files exist — in practice, inside a full ordered build. So
  such kernels' dumps are captured once as a build side product and **kept
  with provenance** (`dump =` in the manifest), and the frontend reads the
  file. This is the production instance's mode.

Nothing is lost to this arrangement: determinism is asserted where it
actually holds (the extracted IR and the printed Lean, both address-free),
and each side's provenance story matches how its input is produced — the
generated module headers stamp the compiler version whenever a compiler ran
on demand.

## `frontend/flang_kernel.py` — Fortran, from flang with-sema dumps

**Input.** A flang **with-sema** parse-tree dump
(`flang -fc1 -fdebug-dump-parse-tree file.f90`) — read from a pre-generated
file (`dump =`), or produced on the spot by running flang on a standalone
source (`source =`; the run happens in a temp directory so flang's `.mod`
side products never litter the source tree). With-sema matters: semantic
analysis has resolved names and kinds, and — a practical constraint — flang
emits *no dump at all* on a semantic error, so dumps of real code require a
full ordered build with `.mod` files (which is what rules out `source` mode
for them).

**How it reads.** The dump text is parsed into a literal node tree first (one
node per `A -> B -> C` chain element, children attached by `|`-depth), then
walked structurally. Two format facts the parser absorbs so callers never see
them: leaf payloads come both quoted (`Name = 'x'`) and unquoted
(`Intent = In`), and expression structure is taken **from the tree, never
re-parsed from unparse text** — the unparse annotations rewrite literals
(`12.0` resurfaces as `1.2e1_8`) while the structured `Real = '12.0'` leaf is
stable.

**Two extraction modes** (one spec type, `FortranKernelSpec`):

- *whole subroutine or function* — the procedure's declarations become
  params/locals (undeclared dummies refuse), its execution part becomes the
  body. A **function**'s `result(name)` variable becomes the kernel's single
  output — a parameter of intent `result`, absent from the printed binder
  list because the caller supplies no value for it (dump shape: `FunctionStmt` lists
  the dummies as bare `Name` children and the result under `Suffix -> Name`).
  A function without a `result` clause, or with a type prefix, refuses;
  keyword prefixes (`pure`, `elemental`, …) are read past;
- *inline loop nest* (`nest = N`, `def_name`) — loop nest #N by source-order
  ordinal; the enclosing subroutine's declarations are inherited
  *tolerantly* — a declaration outside the subset poisons only its own names,
  and extraction refuses iff the nest references one.
  [How-to](../howto/inline-loops.md).

**Notable refusal boundaries** (complete list in [the catalog](refusals.md)):
non-intrinsic calls, strides in loop control, elseif-join shapes, literal
kinds beyond real/int, chained `a%b%c` component paths.

## `frontend/clang_kernel.py` — C++, from clang JSON ASTs

**Input.** The frontend invokes clang itself:
`clang++ -std=c++20 -fsyntax-only -Xclang -ast-dump=json -Xclang
-ast-dump-filter <function>`, plus the manifest's `-I` dirs. A `.cpp` source
compiles directly; a header is wrapped in a one-line translation unit
(`#include`) in a temp directory, mirroring how a real build consumes it.

**The JSON is an in-memory intermediate, never persisted.** clang's node
`id` fields are memory addresses — nondeterministic across runs — so raw
dumps must never be committed or golden-compared; assertions belong on the
extracted IR or the printed Lean, both address-free. The `clang++ --version`
line and the full flag set are stamped into the generated module's header.

**The cast allowlist — the load-bearing refusal.** clang wraps almost every
read in `ImplicitCastExpr`, and unwrapping them wholesale would be exactly
the plausible-but-wrong-model failure mode: cast kinds like
`IntegralToFloating` *change the value*. Exactly two kinds are allowlisted,
each argued value-preserving:

- `LValueToRValue` — a variable read; pure value-category bookkeeping;
- `FunctionToPointerDecay` — a function name decaying to a pointer in callee
  position; no data value involved.

Anything else refuses — pinned by a fixture where `b + 1` produces an
`IntegralToFloating` cast and must raise.

**Intent mapping.** A non-const lvalue reference (`Real &` / `double &`) →
`inout`; a const by-value scalar (`const Real` / `const double`) → `in`.
Everything else — pointers, const refs, plain mutable by-value scalars,
non-real types, default arguments — refuses. Outputs are the reference
parameters in declaration order. The mapping keys on the *qualType
spellings*: `Real` (amrex's alias, as the production headers spell it) and
plain `double` (as the quickstart's standalone `.cpp` spells it) are the two
accepted real-scalar types.

**Two calling conventions, never mixed.** A `void` function's outputs are
its `Real &` parameters, as above. A `Real`/`double`-returning function's
return value is the single output: the extractor turns each `return e` into
an assignment to a `result`-intent parameter named after the function
(Fortran's own default for a result variable), and admits `return` **only in
tail position** — the last statement of the body, or of a branch of an `if`
that is itself in tail position — so every path ends in exactly one return.
An early return refuses at extraction; a path that falls off the end refuses
in functionalize (the result is unassigned there); a non-void function that
also has `Real &` parameters refuses.

**No pointize.** The C++ kernels this frontend targets are already per-point
scalar functions, so extraction emits a rank-0 `Kernel` directly;
`functionalize` and the printer are reused unchanged — the control-flow join
machinery is frontend-agnostic.

**Format notes worth knowing** (from the original survey, all pinned):
`amrex::Math::abs`'s callee carries no namespace qualifier in the JSON
(acceptance is on the referenced declaration's name, found through amrex's
`using std::abs`); `FloatingLiteral.value` is the shortest round-trip form
(`3.0_rt` → `'3'`), which lands on the same Lean numerals as the Fortran
side; `else if` arrives as an `IfStmt` in the else slot and is kept nested,
which functionalize turns into the same if-expression chain as flang's
elseif blocks.

## One cross-language asymmetry, deliberate

C++ unary minus binds tighter than `*`, so `-2.0_rt * x` parses as
`(-2) * x`; Fortran's R1008 makes `-2.0*x(i)` the negation of the whole term,
`-(2 * x)`. The generated models on the two sides deliberately print these
*differently* — each mirrors its own source's parse — and the equivalence
theorems absorb the difference. A frontend that "harmonized" them would be
editorializing about semantics, which is the prover's job.

## Conformance corpora

- `tests/f90/` — Fortran fixtures: source + **committed dump** + PROVENANCE
  (flang version stamp); manifest `tests/f90/MANIFEST.md` maps construct →
  fixture → parser code path.
- `tests/cpp/` — C++ fixtures: source only (see above on JSON); a 3-line
  prelude mirrors `amrex::Real`/`_rt`/`Math::abs` so no include paths are
  needed; gated on `clang++` being on `PATH`; sibling `tests/cpp/MANIFEST.md`
  (its drift axis is the clang JSON schema, not a dump format).
