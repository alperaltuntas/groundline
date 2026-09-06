# Conformance corpus manifest (D7)

Maps each Fortran construct the frontend parses to the fixture that pins it and
the parser code path that consumes it (all paths in
`groundline/frontend/flang_dump.py` unless noted). The corpus is the
format-stability defense of VISION D7: on an LLVM upgrade, regenerate with
`./gen_ptree_files.sh` (version stamped into `PROVENANCE`) and the failures
localize which constructs' dump format moved.

Two assertion tiers per construct:
- **dump snapshot** — the committed `*_ptree` file itself; regenerate + `git diff`
  is the early-warning tier;
- **IR assertions** — `tests/test_ir.py` (above the seam) and
  `tests/frontend/test_flang_dump.py` (below it) are the contract tier.

| Construct | Fixture | Parser code path |
|---|---|---|
| Module / END module bracketing | every fixture | `parse_module_stmt`, `parse_end_module_stmt` |
| Subroutine/function definitions, dummy lists | every fixture | `parse_routine_begin`, `parse_routine_end` |
| Signature facts: arg types/ranks/kinds, OPTIONAL | `test_interface_basic`, `test_interface_rank`, `test_optional_args` | `_parse_routine_signature`, `_extract_type_from_decl`, `_parse_array_spec`, `_kind_selector_name` |
| USE with only-list | `test_private_specifics`, `test_external_calls` | `parse_use_stmt`, `parse_only_clause` |
| USE, whole-module (wildcard) | `test_interface_basic`, `test_type_bound_generic`, … | `parse_use_stmt` |
| USE renames, both forms (bare `alias => name`; inside an only-list) | `test_name_collision` | `parse_rename_clause`, `parse_only_clause` (Rename branch), the rename branch of `find_named_entity` |
| Scope-qualified identity: same routine name in three modules (W5) | `test_name_collision` | consumer-side — `parse_forest.get_call_graph`, `graph_view.subgraph_elements` |
| Generic interface block (`module procedure`) | `test_interface_basic` (types), `test_interface_rank` (ranks) | `parse_interface_stmt` |
| Generic subroutine CALL, resolved by sema | `test_interface_basic`, `test_interface_rank` | `parse_subroutine_call_stmt`, `_sema_answer`, `_classify_event` |
| Generic function reference in an expression | `test_generic_function` | `parse_function_call_stmt`, the `_expr_stack` in `parse_calls` |
| Keyword actual arguments | `test_keyword_args` | call texts via `_sema_answer` (`call_candidates` ignores `kw=`) |
| Calls omitting OPTIONAL arguments | `test_optional_args` | `parse_subroutine_call_stmt` + sema answer |
| Array-section actual argument (rank reduction) | `test_func_ref_array` | `parse_subroutine_call_stmt` (sema resolves the specific) |
| Assumed-shape declarations (explicit lower bounds) | `test_assumed_shape` | `_parse_array_spec`, `_count_explicit_dimensions` |
| Structure-component actual arguments (`cs%field`) | `test_struct_component` | `parse_subroutine_call_stmt` + sema answer |
| Derived type + type-bound bindings (specific, `=>` rename, generic) | `test_type_bound_generic` | `parse_derived_type_stmt`, `parse_type_bound_proc_binding` |
| Type-bound CALL, static dispatch (sema hoists the object) | `test_type_bound_generic` | `_extract_structure_component_name`, `_classify_type_bound` |
| Derived-type EXTENDS: same-module + cross-module extension, inherited binding (static → resolved; dynamic via `class(...)` receiver → assumed through the ancestor walk), module-dependency edges without self-loops | `test_type_extends` | `parse_derived_type_stmt` (Extends), `_binding_impls`, `_classify_type_bound`; consumer-side `parse_forest.get_module_dependency_graph` |
| PUBLIC/PRIVATE accessibility (default + per-name) | `test_private_specifics` | `parse_access_stmt`, `_exports` / `find_named_entity` |
| Mangled resolved names (`imported$owner$specific`) | `test_private_specifics` | `_flang_text.demangle`, `_edges_for_mangled` |
| Unresolved externals → first-class `defined=False` targets | `test_external_calls` | `_classify_event` unresolved branch, `_unknown_target` |
| Local variable declarations (type/rank/kind; `type(t)` / `class(t)`) | `test_interface_rank`, `test_type_bound_generic` | `parse_variable_declaration` |
| Kernel subset: `do concurrent` point kernel — assignment, if/elseif/else, arithmetic (`+ - * / **`), comparisons, `abs`, array refs at loop indices, local scalars | `test_kernel_doconcurrent` | `frontend/flang_kernel.py` (whole module), `kir.pointize`/`functionalize`, `lean_printer` |
| Kernel subset: logical IF statement (R1139, dump: `ActionStmt -> IfStmt`) + the sequential guarded control-flow join (second guard's RHS reads the first's target — merged-state threading) | `test_kernel_ifstmt_join` | `flang_kernel._extract_action` (IfStmt branch), `kir.functionalize` (`merge_if`), `lean_printer` (`Cond`) |
| Kernel subset: unary minus (dump: `Negate`) — bare leaf, compound operand needing printer parens, negated source parens | `test_kernel_negate` | `flang_kernel._extract_expr_inner` (Negate), `lean_printer` (`Neg`) |
| Rule A: plain, perfectly nested `do` nest as a point kernel (dump: `LoopControl -> LoopBounds`) — pointized under the array-index gate; semantic license is the Lean schema lemma (`Groundline/SeqSchema.lean`) | `test_kernel_plaindo` | `flang_kernel._extract_do` (LoopBounds branch), `kir.pointize` (plain-DO path) |
| Rule A REFUSAL: cross-iteration recurrence (`p(i,K+1) = p(i,K) + …`, distilled from `find_dz_for_eta`) — offset subscript fails the gate; also pins dump lowercasing (`K` ≡ `k`) | `test_kernel_recurrence` | `kir.pointize` (subscript gate) |
| Rule B: inline-loop addressing — two nests in one subroutine (do-concurrent + plain DO, inside IF branches), each extracted by source-order ordinal; whole-subroutine mode keeps refusing | `test_kernel_inline_nests` | `flang_kernel.extract_loop_kernel` (`_collect_do_nests`, tolerant decls) |
| Rule B: derived-type component reads (dump: `StructureComponent`) — loop-invariant scalar (`cfg%fac`) + loop-indexed component array (`cfg%w(i)`) → synthesized scalar in-params; naming-collision refusal (`collide`) | `test_kernel_component` | `flang_kernel._extract_dataref` (StructureComponent), `kir.pointize` (component synthesis) |
| Rank-0 (loop-free scalar) point kernel — extracts with no pointize license; `pointize = true` on it REFUSES (the loop/point boundary, both directions) | `test_kernel_rank0` | `kir.is_loop_nest`, `kernel_bank.extract_fortran_entry` (the pointize gate); pinned by `tests/test_kernel_bank.py` (`TestPointizeGate`) |
| Integer-VALUE REFUSALS: integer-literal division in a real expression (`a * (2/3)` — Fortran truncates, ℝ would not) and an integer local read in the body; both refuse at print, never mismodel. Integers as addresses (indices/bounds/subscripts) unaffected | `test_kernel_intarith` | `lean_printer._is_int_expr` (div/pow gate in `print_expr`), `print_kernel` (non-real locals gate) |
| Function-result kernel: a FUNCTION with `result(name)` (dump: `FunctionSubprogram` / `FunctionStmt` — dummies as bare `Name` children after the function name, the result under `Suffix -> Name`, `PrefixSpec -> Pure`) — the result variable is the kernel's single output, absent from the printed binder list. REFUSALS pinned by sibling functions: no result clause, a type prefix (`PrefixSpec -> DeclarationTypeSpec`), an `intent(inout)` dummy alongside the result, and — at functionalize — a result unassigned on some path or read before its first assignment | `test_kernel_function` | `flang_kernel.find_procedure`, `_signature`, `_check_prefix`, `_kernel_from_root` (result param); `kir.functionalize` (result gates); `lean_printer.print_kernel` (binder list) |
| The flux_elem construct set: a LOGICAL `intent(in)` dummy as a bare IF condition (dump: `IntrinsicTypeSpec -> Logical`; a `Bool` input); the generalized control-flow join — statements after an if/elseif/else whose branches assign locals (`w` on every path → one merged `let`; `cfl` on some paths, never read after → inlined and dropped) with nested joins inside branches; an unreferenced derived-type dummy dropped; `PrefixSpec -> Elemental` read past. REFUSALS pinned by siblings: a local assigned on some paths only, unbound before, read after the join; a logical local; a logical output; a local read before any assignment; a *referenced* derived-type dummy in a per-point kernel | `test_kernel_join_locals` | `kir.functionalize` (`merge_if`, `branch_state`, `_reads_before_redef`, the read-before-assign gate in `subst`); `flang_kernel._parse_type_decl` (Logical), `_kernel_from_root` (unreferenced derived dummies); `lean_printer.print_kernel` (binder groups, output/local type gates) |
| The continuity_convergence construct set: rule C — a read-only neighbor stencil (`flux(i-1,j,k)`, dump: `SectionSubscript -> Integer -> Expr` over `Subtract(Name, IntLiteralConstant)`) → synthesized input `flux_im1`, admitted in `do concurrent` nests only; rule B widened — a component array indexed by a SUBSET of the loop indices (`g%iarea(i,j)` in a k,j,i nest) → per-cell input; rule D — a nest-invariant local (`h_min`) → input; `AttrSpec -> Optional` dummies referenced by the addressed nest. REFUSALS pinned by siblings: the stencil in a plain DO; a neighbor read of the array the nest writes; a plain array indexed by a subset | `test_kernel_stencil` | `kir.pointize` (`parse_subscripts`, the write set, `synth_param` rules B/C/D, the own-cell write gate); `flang_kernel._parse_type_decl` (Optional) |
| **Column kernel** (docs/COLUMN_KERNELS.md): `column_sum`, pointized over the manifest's `columns` — a whole-array assignment (dump: `SectionSubscript -> SubscriptTriplet` with no bounds) as the per-column init; a `do concurrent (k,j,i)` MAP whose body is a `CallStmt` to the banked `flux_pt` (dump: `ActionStmt -> CallStmt -> Call -> ProcedureDesignator` + `ActualArgSpec`s) with per-k `intent(out)` actuals; a plain `do k;j;i` FOLD accumulating a per-column output; pruning under `assume` (an `IfStmt` guarded by the assumed flag dropped before its body — which would refuse — is modeled), `ignore_calls` (timers), and dead integer locals (bounds only). REFUSALS: a scan (per-k write depending on fold state), a k-recurrence, a call neither banked nor ignorable | `test_kernel_column` | `flang_kernel._column_kernel_from_root` (`_prune_block`, `_decided_false`, `_dead_integer_locals`), `_extract_action` (CallStmt), `_extract_subscript` (Slice); `column.columnize`; `kir.functionalize` (CallBind/MapStmt/FoldStmt); `lean_printer` (column header, App/Proj/Lam/Foldl); pinned by `tests/test_column.py` |
| **Column kernel, B2 constructs** (docs/COLUMN_KERNELS.md §5): `bt_cont` — MASKED nests (dump: a `Scalar -> Logical -> Expr` sibling of the `ConcurrentControl`s in `ConcurrentHeader`; the frontend used to walk only the controls and would have dropped the mask silently) under a plain `do k` → `if mask then step else state` in the fold, and the tail `if (do_i(i,j))` → a column-level IF; ROW SCRATCH locals `dul(i)` indexed by one column index under the plain `do j` → per-column scalars; a FOLD with two state variables → `let (fa_l, uh_l) := ks.foldl (fun (fa_l, uh_l) k => …)`; COMPONENT-ARRAY writes `cont%fa_w(i,j) = …` on an `intent(inout)` derived-type dummy → per-column outputs; an `if/elseif` join whose two locals read each other's prior values → one destructuring `let (fa_avg, fa_0) := if … then (…) else …`; an output let-bound before its local is re-assigned. REFUSALS: a masked map, a row scratch read before any column wrote it, a row scratch shared by `do concurrent` columns (a race), a component write inside a k-loop, a masked nest at the POINT tier | `test_kernel_bt_cont` | `flang_kernel._extract_do` (mask, locality specs refused); `column.columnize` (`nest_indices` mixed plain/concurrent nests, `classify` row scratch, `target_of` component outputs, column-level `If`); `kir.functionalize` (multi-state `FoldStmt`, `shield`, the destructuring join, `LetPat`/`TupleExpr`); `kir.pointize` (mask refusal); `lean_printer` (`_fold_head`/`_fold_init`, `LetPat`); pinned by `tests/test_column.py::TestBtContFixture` |
| Packaging: manifest-driven extraction end-to-end in **source mode** — no committed dump; flang runs on the standalone quickstart sources on demand, the mirror of the clang side | `examples/quickstart/toy_kernel.f90`, `toy_kernel_loop.f90` | `kernel_bank.load_manifest`/`render_fortran`, `flang_kernel.dump_parse_tree`/`FlangKernelFrontend`; pinned by `tests/test_kernel_bank.py` (`TestQuickstart`, flang-gated) |

## Known gaps (parser paths with no fixture yet)

Recorded per the D7 coverage rule — every parse branch should gain a fixture;
these don't have one yet:

- **`Use.only` for the only-list rename form** — `test_name_collision` covers the
  construct and its *resolution*, but the IR projection reports
  `Use(only=(), renames=(('bc_c','apply_bc'),))` for
  `use m, only: bc_c => apply_bc`, i.e. an empty only-list, which the `Use`
  docstring reads as "whole module". Resolution is unaffected (it follows the
  rename), so the test asserts the renames and not the only-list; the projection
  itself wants a fix in a frontend phase (DEVLOG 2026-07-30).
- **Dynamic type-bound dispatch, `unresolved` branch** — a polymorphic receiver
  whose declared type the frontend cannot determine (e.g. a component chain
  `eos%type%binding(...)`); `test_type_extends` covers the `assumed` branch, but
  the receiver-type-unknown → `unresolved` path is still covered only by the
  production corpus replay.
- **Nested (CONTAINS'd) routines** inside a routine.
- **Main PROGRAM and module-less subprogram files** — `parse_program_unit`'s
  `MainProgram` / `Subprogram` branches.
- **Scope-qualified unresolved targets** (only-list import from a module outside
  the parsed set) — cannot be fixtured self-contained (sema needs the `.mod`);
  unit-tested against a hand-built registry (`TestUseChainModule`).
