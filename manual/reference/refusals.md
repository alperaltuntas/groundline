# Refusal catalog

Every site in the pipeline that raises `UnsupportedConstruct`, what triggers
it, and why it refuses. Read it as the other half of the subset's contract:
anything *not* listed here is modeled exactly, and anything that hits one of
these sites fails loudly instead of producing a plausible-but-wrong model
([why that matters](../concepts/kernel-ir.md)).

The catalog is complete as of this manual's writing — it was compiled by
`grep -n "raise UnsupportedConstruct"` over the four trusted-base modules
(100 sites), and each entry's message text is greppable in the source. Related
but distinct: a malformed *manifest* raises `ManifestError`
([manifest rules](manifest.md#general-rules)), and clang/file-system failures
raise ordinary errors — neither is a subset refusal.

## Fortran extraction (`frontend/flang_kernel.py`)

### Structural guards on the dump tree

These fire when the dump's shape differs from what the construct grammar
implies — the early-warning surface for dump-format drift (see
[Port to a new LLVM](../howto/new-llvm.md)).

| Trigger | Why it refuses |
|---|---|
| an expected child node is absent (`expected child '<name>' under '<node>'`) | the dump shape moved, or the construct is a variant the walker has not been taught; guessing a different child would misread the tree |
| a node expected to have exactly one child has several (`expected exactly one child`) | same — structural ambiguity is never resolved by picking one |
| a subroutine or function is found zero or several times (`found N definitions`) | the kernel's address must be unique to be meaningful |
| a procedure prefix that is not a bare keyword (`prefix 'DeclarationTypeSpec' on 'FunctionStmt'`) | a type prefix (`real function f(x)`) declares the result's type outside the specification part — dropping it would lose a declaration. Keyword prefixes (`pure`, `elemental`, `recursive`, …) constrain how the procedure may be used without changing what its body computes, and are read past |
| a function without a `result(name)` clause (`has no result(name) clause`) | the function name would double as the result variable — a different declaration story, unsupported until a kernel needs it |
| a function whose result variable is not declared in the specification part (`result variable '<r>' is not declared`) | its type is unknown |
| a function with `intent(inout)`/`intent(out)` dummies (`two output conventions`) | a result *and* mutated arguments would give the kernel two output channels; the C++ side refuses the mirror shape |
| `LoopBounds` without a leading index name | unrecognized loop-control shape |
| an unrecognized loop control (`loop control '<node>'`) | only `do concurrent` headers and plain counted `do` loops are modeled |

### The construct subset

| Trigger | Why it refuses |
|---|---|
| literal kinds other than real/int (`literal kind '<kind>'`) | only real and integer literals are modeled (no logical/character/complex) |
| a call to anything but a supported intrinsic (`call to '<name>' (not a supported intrinsic)`; the set is `abs`) | an unmodeled callee makes the model wrong by omission; user procedures are out of scope by design |
| an unrecognized expression node (`expression node '<node>'`) | catch-all: the expression grammar outside literals, designators, parentheses, negation, binary ops, comparisons, and intrinsic calls is unmodeled |
| an array-element base that is not a plain name or single component (`array-element base`) / an unrecognized data reference (`data reference '<node>'`) | only `x`, `x(i,j,k)`, `base%comp`, `base%comp(i,j,k)` are modeled |
| a chained component path `a%b%c` (`component base '<node>' (only single-level base%comp is supported)`) | multi-level component reads have no synthesized-parameter rule ([rule B](../concepts/pointize.md#component-reads-rule-b)) |
| an unrecognized executable construct (`executable construct '<node>'`) | only assignments, IF constructs, and do-constructs may appear in a kernel body |
| an unrecognized action statement (`action statement '<node>'`) | within a body, only assignment and the one-line logical IF statement are modeled |
| an unrecognized `IfConstruct` child (`IfConstruct child '<node>'`) | if/elseif/else blocks only — no construct names, no other clauses |
| `do concurrent` with a stride / plain `do` with a stride | a strided box is not the full index box the iteration schemas model |
| an unsupported intrinsic type (`intrinsic type '<type>'`) or type spec (`type spec '<node>'`) | only `real`, `integer`, `logical`, and (as dummies) derived types are declared into kernels; a logical dummy is a `Bool` input (a bare IF guard), while logical locals and outputs refuse at print |
| an unsupported declaration attribute (`attribute '<node>'`) | `intent`, `dimension` and `optional` are understood (presence is the caller's precondition — a body that could branch on it, via `present()`, refuses anyway); `pointer`, `allocatable`, etc. change semantics the model doesn't carry |
| a dummy argument with no declaration (`undeclared dummy args`) | a parameter of unknown type/intent cannot be modeled |

### Inline-loop addressing (rule B; `extract_loop_kernel`)

| Trigger | Why it refuses |
|---|---|
| nest ordinal out of range (`loop nest N requested, but the subroutine has M`) | ordinals are the address; a silent clamp would extract the wrong loop |
| the addressed nest references a name whose declaration was rejected (`loop nest N references '<name>' — <reason>`) | declarations are inherited [tolerantly](../howto/inline-loops.md) — poison is per-name, and only a *referenced* poisoned name refuses |

## C++ extraction (`frontend/clang_kernel.py`)

### Function shape

| Trigger | Why it refuses |
|---|---|
| the function found zero or several times in the dump (`found N definitions`) | unique address, as on the Fortran side |
| a return type other than `void`, `Real`, or `double` (`must return void or a real scalar`) | two calling conventions are admitted: a `void` function returning through `Real &` parameters, or a real-returning function whose return value is the single output |
| a non-void function that also has `Real &` parameters (`two output conventions`) | a return value *and* mutated arguments — the mirror of the Fortran refusal above |
| parameter type other than `Real &`/`double &`, `const Real`/`const double`, or `const bool` (pointers, const refs, mutable by-value, other types, …) | the [intent mapping](frontends.md) accepts exactly these spellings and nothing else; `const bool` is a logical input |
| a parameter with a default argument | a defaulted parameter changes the function's arity story; does not appear in the targeted kernel shape |
| unexpected children of the function declaration, multiple bodies, or no body | structural guards on the JSON shape |
| locals shadowing parameters (`locals shadow parameters`) | shadowing would silently redirect reads in the flat `let` model |

### Statements and declarations

| Trigger | Why it refuses |
|---|---|
| any statement other than a declaration, an assignment, an `if`, or (in a non-void kernel) a tail `return` (`statement '<kind>'`) — so `for`, `while`, `+=`, … | the C++ subset mirrors the Fortran one: straight-line assignments and structured ifs |
| a `return` in a void kernel (`return statement in a void kernel`) / a `return` without a value (`return without a value`) | the return value is the output of a non-void kernel and nothing else |
| a `return` in non-tail position (`non-tail position (an early return …)`) | statements after it would run on some paths only, which the flat body cannot say; every path must end in exactly one tail return |
| a declaration that is not a `VarDecl` (`declaration '<kind>'`) | only plain local variables are modeled |
| a local of any type but `Real`/`double` (optionally const) (`local '<name>': type '<qual>'`) | only real scalars exist in the kernel IR |
| a local with a list/direct initializer (`Real w{e}`) | only the copy-initializer (`= e`, a `let`) and a bare declaration (`Real w;`, assigned later — its assignments are ordinary statements, a read before the first one refuses in functionalize) are modeled |
| a local declared more than once | C++ block scoping does not map to the flat `Let` model; renaming would break the by-eye audit |
| an assignment whose target is not a (reference) parameter or a declared local | writes go to outputs or to the kernel's own locals; anything else is outside the state-threading model |
| assignment/binary nodes with unexpected operand counts; `if` with an init-statement, condition variable, or `constexpr`; unexpected `if` child counts | structural guards on the JSON shape |

### Expressions and the cast allowlist

| Trigger | Why it refuses |
|---|---|
| **an implicit cast not on the allowlist** (`implicit cast kind '<kind>' is not on the value-preserving allowlist`) — only `LValueToRValue`, `FunctionToPointerDecay` and `NoOp` (a qualifier-only conversion, `Real` → `const Real` when a prvalue binds to a `const Real &`) pass | the load-bearing refusal: cast kinds like `IntegralToFloating` *change the value*; unwrapping them wholesale is exactly how a plausible-but-wrong model would slip in |
| a reference to anything but a parameter or local (`only parameters and locals are supported in expressions`) | globals, members, and enumerators are outside the model |
| unary operators other than prefix `-` | only negation is modeled |
| binary opcodes outside `+ - * /` and the six comparisons (so `%`, `&&`, bit-ops, …) | unmodeled arithmetic |
| calls to anything whose referenced declaration is not `abs`, `max` or `min`; calls with no callee or a non-`DeclRefExpr` callee; a wrong arity (`abs` with ≠ 1 argument, AMReX's three-argument `max`/`min`) | same intrinsic policy as Fortran; the binary `amrex::max`/`amrex::min` are the forms the kernels use |
| user-defined literal with an unexpected shape, a suffix other than `_rt`, or a non-`FloatingLiteral` operand | only AMReX's `_rt` real literals are modeled |
| any other expression node (`expression node '<kind>'`) | catch-all |

## The kernel bank (`groundline/kernel_bank.py`)

| Trigger | Why it refuses |
|---|---|
| a loop-nest kernel whose manifest entry lacks `pointize = true` (`the Fortran kernel is a loop nest, which is not the same thing as a point function`) | reducing a loop to its per-point body is a semantic step the user must license explicitly ([Pointize](../concepts/pointize.md)) |
| `pointize = true` on a kernel that is not a loop nest | the option would silently do nothing — the manifest should say what is true |

## Pointize (`groundline/kir.py`)

| Trigger | Why it refuses |
|---|---|
| the body is not exactly one do-concurrent or plain-do nest | pointize models one loop nest; prologue/epilogue statements would be silently attributed to every iteration |
| duplicate loop index in a plain-do nest | the schema lemma requires a duplicate-free enumeration |
| a do-construct inside the loop body | the nest is not perfectly nested — the pointwise model has no place for an inner loop |
| an array reference whose subscripts are not the loop indices, plainly or with a literal offset (`not indexed by the loop indices`: partial indexing of a plain array, `1+i` spellings, non-variable subscripts) | not point-local, or not a shape the model names |
| a write to a neighbor cell (`p(i,K+1) = …`; `every write must land in the iteration's own cell`) | the k-recurrence boundary: iteration `k` writes what iteration `k+1` reads ([case study](../case-studies/edge-thickness-upwind.md#the-boundary-marked-with-a-refusal-fixture)) |
| a neighbor read of an array the nest writes (`cross-iteration recurrence`) | the other face of the same boundary, refused in either loop form |
| a neighbor read in a plain-do nest (`do concurrent nests only`) | [rule C](../concepts/pointize.md#read-only-stencils-rule-c)'s license is that narrow: the plain-DO schema-lemma variant is not yet proved |
| assignment to a scalar parameter inside a plain-do nest | the accumulator/reduction shape (`s = s + a(i)`): every write must land in the iteration's own cell for the schema lemma's setting to apply |
| assignment to a derived-type component | component *writes* would break rule B's loop-invariance guarantee |
| component read whose base is not an `intent(in)` derived-type dummy | `intent(in)` is what *guarantees* loop-invariance rather than assumes it |
| component read neither a loop-invariant scalar nor an array indexed by (a subset of) the loop indices (e.g. offset subscripts) | outside the licensed shapes of rule B |
| a synthesized parameter name colliding with an existing name | refuse-don't-rename: a renamed parameter would defeat the by-eye audit of generated Lean against source |
| unsupported assignment targets, unscalarizable expression nodes, non-assignment/If statements in the loop body | catch-alls closing the pass |

## Functionalize (`groundline/kir.py`)

| Trigger | Why it refuses |
|---|---|
| no `inout`/`out`/`result` parameters | nothing to return — a kernel with no outputs has no functional meaning |
| a function result alongside other outputs (`two output conventions`) | the result is the *sole* output of a function kernel (a frontend never produces this; the gate closes the pass) |
| a function result not assigned on every control-flow path (`not assigned on every control-flow path`) | the source would return an undefined value there — unlike an `inout`/`out` argument, a result has no caller-supplied value to fall back on |
| a function result, or a local, read before it is assigned (`read before it is assigned`) | an undefined value in the source; refused here rather than left to the checker (until 2026-09-05 the local case was the one refusal delegated to Lean, as an unbound name) |
| a function result assigned in only some branches of a joined `if` (`only some branches of a joined IF`) | the merge would pair a value with an undefined one |
| a local assigned on only some paths of a joined `if`, not bound before it, and read after the join (`only some paths`) | undefined on the other paths; the read scan is conservative (any occurrence inside a later `if` counts), so this may refuse spuriously but never mismodels — a local with a prior binding takes that binding on the other paths instead, and one nothing reads afterwards is simply dropped |
| a statement inside a joined branch that is neither an assignment nor an `if` | the sequential merge is defined over assignments and nested ifs |
| assignment to a name that is neither local nor output | an unmodeled state (a global, an index) would be silently dropped |
| any other statement form | catch-all |

## Printer (`groundline/lean_printer.py`)

Two of these gates guard live semantics; the rest are final honesty gates,
reachable only if a caller bypasses the normal pipeline order:

| Trigger | Why it refuses |
|---|---|
| integer-valued `/` or `**` — both operands built from integer literals (`a * (2/3)`) | the source evaluates these in **truncating integer arithmetic** (2/3 is 0), which the model over ℝ cannot represent; a mixed real/int operand is fine (the integer promotes). The C++ twin refuses earlier, at the cast allowlist. Faithful integer semantics is [roadmap](../limits.md#integer-values-in-kernel-bodies) |
| a non-real **local** in the modeled body (`non-real local(s)`) | an integer local would be modeled as a real, hiding any truncation its assignments perform; a logical local has no meaning over ℝ. Integers as *addresses* — loop indices, bounds, subscripts — are unaffected: pointize consumes and drops them |
| a call the printer cannot spell (anything but `abs`/`min`/`max`) | no invented Lean spelling for an unmodeled callee |
| an `ArrayRef` or `ComponentRef` surviving to printing | pointization was skipped or incomplete — printing them as bare names would silently change meaning |
| a parameter that is neither real nor logical surviving to printing (`non-real, non-logical parameters`) | the generated def's binders are `ℝ` and `Bool`; a derived-type or integer parameter must have been dropped or synthesized away |
| a non-real output (`non-real output(s)`) | the model returns reals; a logical `intent(out)` has no ℝ meaning |
| a function kernel with no input parameters (`no input parameters`) | the result is not an input, so the binder list would be empty — a kernel with nothing to read has no arguments to model |
| unprintable expression/functional nodes | catch-alls |

## The refusal that used to be delegated to Lean

Until 2026-09-05 one cross-iteration channel was left to the proof checker
rather than the Python gate: a local scalar **read before its first write** in
a plain-DO body (which would carry the previous iteration's value) printed as
an unbound name, and the generated Lean failed to elaborate. With the
generalized join, functionalize now tracks which locals are in scope and
refuses such a read itself (`read before it is assigned`) — the same loud
outcome, delivered earlier — see
[Pointize](../concepts/pointize.md#one-gap-closed-by-the-checker).
