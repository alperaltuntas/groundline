# Conformance corpus manifest — C++ side (D7)

The clang-frontend sibling of `tests/f90/MANIFEST.md`, kept as a separate file
deliberately: the f90 manifest defends against *flang dump-format* drift with
committed `*_ptree` snapshots, while this corpus has **no committed dumps at
all** — clang JSON node `id` fields are memory addresses, nondeterministic
across runs, so raw dumps are never golden-compared. Here the fixtures are the
committed `.cpp` sources themselves; extraction happens at test time, and the
assertions live on the extracted kernel IR and the printed Lean
(`tests/frontend/test_clang_kernel.py`). The drift axis this corpus defends is
the **clang JSON AST schema**: on an LLVM upgrade, rerun the gated tests and
failures localize which constructs' JSON shape moved.

## Running the tests

The fixtures are self-contained (each carries a tiny prelude mirroring
`amrex::Real` / `amrex::literals` / `amrex::Math::abs`) — **no include paths
are needed**; `clang++` alone suffices. Tests are skipped unless `clang++` is
on `PATH`:

```bash
. /glade/work/altuntas/llvm-root/activate_llvm.sh   # clang 21
PYTHONNOUSERSITE=1 python -m pytest tests/frontend/test_clang_kernel.py
```

The *production* extraction (the real TIM header, which includes AMReX) is
driven by `groundline kernel generate` against the kernel manifest
`examples/turbo-stack.kernels.toml`, where the include paths are pinned; its
golden test sits in `tests/test_kir_lean.py` next to its Fortran sibling.

| Construct | Fixture / function | Extractor code path (`groundline/frontend/clang_kernel.py`) |
|---|---|---|
| Composite point kernel: `Real&`/`Real const` intent mapping, local decl-with-init, if / else if / else, `_rt` literals, `+ - * /`, comparisons, `abs` call, skipped decl attribute | `test_kernel_point.cpp` / `clamp_scale_point` | `extract_kernel_from_decl`, `_extract_param`, `_extract_vardecl`, `_extract_if`, `_extract_call`, `_extract_udl` |
| Sequential guarded pair (the `ppm_limit_cw84_point` shape): two braceless guarded assignments, the second reading the first's target — merged-state threading | `test_kernel_guard_join.cpp` / `guard_pair_point` | `_extract_if` (braceless branch), `_extract_stmts` (`=` branch); join merge in `kir.functionalize` (reused unchanged) |
| Unary minus, incl. the C++/Fortran parse asymmetry (`-2.0_rt * x` = `(-2) * x`, not R1008's `-(2 * x)`) | `test_kernel_negate.cpp` / `neg_clip_point` | `extract_expr` (UnaryOperator branch) |
| Refusal: compound assignment (`+=`) | `test_kernel_refusals.cpp` / `refuse_plus_equal` | `_extract_stmts` fall-through |
| Refusal: loop statement (`for`) | `test_kernel_refusals.cpp` / `refuse_for_loop` | `_extract_stmts` fall-through |
| Refusal: non-Real parameter (`int const`) | `test_kernel_refusals.cpp` / `refuse_int_param` | `_extract_param` |
| Refusal: value-changing implicit cast (`IntegralToFloating` from an int literal) — pins the cast allowlist itself | `test_kernel_refusals.cpp` / `refuse_int_literal` | `extract_expr` (`_TRANSPARENT_CASTS`) |
| Function-result kernel: a `Real`-returning point function whose tail `return e` statements assign the single output (a `result` param named after the function); refusals: an early (non-tail) `return`, a tail `if` without `else` (result unassigned on the fall-through path — functionalize), a `Real&` parameter alongside a return value, a bare `return` in a void kernel | `test_kernel_function.cpp` / `capped_ratio_point`, `refuse_*` | `extract_kernel_from_decl` (return-type dispatch, result param), `_extract_stmts` (`ReturnStmt`, tail tracking), `_extract_if` (branches inherit tail position) |
| The flux_elem_point construct set: a `bool const` parameter as a Bool input (bare `if` guard); locals declared WITHOUT an initializer and assigned later inside the branches of an if / else if / else that a statement follows (the generalized join; else-if merges recursively from the else slot into the same Cond chain as flang's elseif); refusals: a local defined on some paths only and read after the join, a `bool` local, a local read before any assignment, a list-initialized local | `test_kernel_join_locals.cpp` / `face_flux_point`, `rebound_local_point`, `refuse_*` | `_extract_param` (`const bool`), `_extract_vardecl` (bare declaration; list/direct init refused), `_extract_stmts` (`=` to a declared local); join merge in `kir.functionalize` (reused unchanged) |
| `amrex::max` / `amrex::min` callees (binary), with the JSON shapes their `const T&` signature produces: `ExprWithCleanups` around the returned value, `MaterializeTemporaryExpr` + `NoOp` cast binding a prvalue argument, `LValueToRValue` reading the returned reference; refusals: the three-argument `max`, a `pow` callee | `test_kernel_minmax.cpp` / `converge_point`, `clamp_point`, `refuse_*` | `extract_expr` (`_TRANSPARENT_WRAPPERS`, `NoOp` in `_TRANSPARENT_CASTS`), `_extract_call` (`_CALLEES` with arity) |
| **Column kernel**: the `ParallelFor` lambda of `column_sum` (address `parallel_for = 1`, the lambda's `int i, int j` as `columns`), with an AMReX-shaped prelude (`Array4::operator()`, `Box`, `ParallelFor`): `Array4` reads as per-k / per-column / stencil inputs (`CXXOperatorCallExpr` on `operator()`, a trailing literal `0` dropped), a `for k` (`ForStmt` init/cond/inc shape) as a FOLD, `+=` (`CompoundAssignOperator`), a call statement to the banked `flux_pt_point` with `Real&` receivers (uninitialized locals; never read by the callee, hence outputs), a member read `cs.vol_cfl` (`MemberExpr`) as a Bool input, a guarded block pruned under `assume`; refusals: a scan, an unbanked call, lambda index names not matching `columns` | `test_kernel_column.cpp` / `column_sum`, `refuse_scan`, `refuse_unbanked_call` | `extract_column_kernel_from_decl`, `_extract_column_param`, `_lambdas`, `_extract_stmts` (column branch), `_extract_for`, `_extract_array_read`, `_extract_index`, `_cxx_decided_false`; `column.columnize(columns_bound=True)`; `kernel_bank.cpp_callees` (`reads_before_write`); pinned by `tests/test_column.py` |
| Node-level allowlists (no clang needed): unlisted cast kinds, non-`abs` callees, unlisted opcodes, non-local DeclRefExpr, non-`_rt` literal suffixes | hand-built JSON dicts in `TestExprAllowlists` | `extract_expr`, `_extract_call`, `_extract_udl` |
| AMReX-free standalone header (its own `using Real = double;`, no includes) — pins that the frontend keys on the `Real &`/`const Real` qualType spellings, not on AMReX | `examples/quickstart/toy_kernel.hpp` / `scale_clip_acc_point` | `_extract_param`, `_extract_vardecl`; pinned by `tests/test_kernel_bank.py` (`TestQuickstart`, clang-gated) |

## Known gaps (extractor paths with no fixture yet)

- **`Real` by-value non-const parameter** (would be locally mutable; refused) —
  covered only by the `_extract_param` fall-through, no dedicated fixture.
- **Default arguments** — `_extract_param` refuses a `ParmVarDecl` carrying an
  initializer; no fixture.
- **`if` with init-statement / condition variable / `constexpr if`** —
  `_extract_if` refuses on the JSON flags; no fixture.
- **Local redeclaration in sibling scopes** (C++ block scoping vs the flat Let
  model; refused in `_extract_vardecl`) — no fixture.
