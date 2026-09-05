"""The C++ frontend: clang JSON AST → kernel IR (``frontend/clang_kernel.py``).

Two tiers, mirroring ``tests/test_kir_lean.py``:

- Fixture-based tests compile the ``tests/cpp/`` conformance fixtures with
  clang at test time (the fixtures are self-contained — no includes), so they
  are gated on ``clang++`` being on ``PATH``, the C++ analogue of
  the ``GROUNDLINE_DUMPS`` gate. Raw JSON dumps are never golden-compared
  (node ids are memory addresses); assertions are on the extracted kernel IR
  and the printed Lean.
- Node-level allowlist tests run everywhere: they feed hand-built JSON dicts
  to the extractor, pinning the refusal behavior (casts, callees, opcodes)
  with no clang dependency.

The production golden test (``Groundline/GeneratedCpp.lean`` byte-for-byte) lives
next to its Fortran sibling in ``tests/test_kir_lean.py``.
"""

import shutil
from pathlib import Path

import pytest

from groundline.kir import DoConcurrent, If, UnsupportedConstruct
from groundline.frontend.clang_kernel import extract_expr, extract_kernel
from groundline.lean_printer import print_kernel

CPP_DIR = Path(__file__).parent.parent / "cpp"
CLANG = shutil.which("clang++")

needs_clang = pytest.mark.skipif(
    CLANG is None, reason="clang++ not on PATH (source activate_llvm.sh)")


# =============================================================================
# Fixture-based end-to-end: clang -> extract -> print (no pointize)
# =============================================================================

@needs_clang
class TestPointKernelFixture:

    @pytest.fixture(autouse=True)
    def setup(self):
        self.kernel = extract_kernel(CPP_DIR / "test_kernel_point.cpp",
                                     "clamp_scale_point")

    def test_extraction_shape(self):
        assert [(p.name, p.intent) for p in self.kernel.params] == \
            [("x_out", "inout"), ("x_in", "in"), ("lo", "in")]
        assert [p.name for p in self.kernel.locals] == ["w"]
        assert all(p.rank == 0 for p in self.kernel.params)   # rank-0 directly
        assert not any(isinstance(s, DoConcurrent) for s in self.kernel.body)

    def test_printed_lean(self):
        text = print_kernel(self.kernel)
        expected = """\
def clamp_scale_point (x_out x_in lo : ℝ) : ℝ :=
  let w := 2 * x_in - x_out
  if |w| < lo then
    lo
  else if w * w > 4 * lo then
    x_in + w / 2
  else (w + lo) * 0.5
"""
        assert text == expected


@needs_clang
class TestGuardJoinFixture:
    """The sequential guarded pair (the ppm_limit_cw84_point shape): the body
    ends with two guarded assignments to Real& state, the second reading the
    first's target — exercises kir's existing merge_if join machinery."""

    @pytest.fixture(autouse=True)
    def setup(self):
        self.kernel = extract_kernel(CPP_DIR / "test_kernel_guard_join.cpp",
                                     "guard_pair_point")

    def test_braceless_ifs_extracted_as_single_branch(self):
        for stmt in self.kernel.body[1:]:
            assert isinstance(stmt, If)
            assert len(stmt.branches) == 1 and stmt.orelse == ()

    def test_printed_lean_threads_merged_state(self):
        # The load-bearing assertion: c's new value reads the MERGED b —
        # `(if t > b then t - 1 else b) + t` — not the input b.
        text = print_kernel(self.kernel)
        expected = """\
def guard_pair_point (b c a : ℝ) : ℝ × ℝ :=
  let t := 2 * a
  if t < c then
    (if t > b then t - 1 else b, (if t > b then t - 1 else b) + t)
  else (if t > b then t - 1 else b, c)
"""
        assert text == expected


@needs_clang
class TestNegateFixture:
    """Unary minus, with the C++/Fortran parse asymmetry pinned: C++ `-2.0_rt
    * x` is `(-2) * x` (minus binds tighter than `*`), NOT Fortran R1008's
    `-(2 * x)`. Bare leaf and negated source parens as in the f90 twin."""

    def test_printed_lean(self):
        kernel = extract_kernel(CPP_DIR / "test_kernel_negate.cpp",
                                "neg_clip_point")
        expected = """\
def neg_clip_point (y x : ℝ) : ℝ :=
  if x < -y then
    (-2) * x
  else -(x + y)
"""
        assert print_kernel(kernel) == expected


@needs_clang
class TestFunctionResultFixture:
    """A non-void point function: the return value is the single output — a
    parameter of intent 'result' named after the function (Fortran's own
    default for a result variable), absent from the printed binder list.
    Every path must end in a tail `return e`; the refuse_* siblings pin the
    neighboring shapes. The C++ mirror of tests/f90/test_kernel_function."""

    source = CPP_DIR / "test_kernel_function.cpp"

    def test_extraction_shape(self):
        k = extract_kernel(self.source, "capped_ratio_point")
        assert [(p.name, p.intent) for p in k.params] == \
            [("a", "in"), ("b", "in"), ("maxrat", "in"),
             ("capped_ratio_point", "result")]
        assert [p.name for p in k.locals] == ["q"]

    def test_printed_lean(self):
        expected = """\
def capped_ratio_point (a b maxrat : ℝ) : ℝ :=
  let q := maxrat * b
  if |a| > |q| then
    maxrat
  else a / b
"""
        assert print_kernel(extract_kernel(self.source, "capped_ratio_point")) == expected

    def _refuse(self, function, match, *, through_printer=False):
        with pytest.raises(UnsupportedConstruct, match=match):
            k = extract_kernel(self.source, function)
            if through_printer:
                print_kernel(k)

    def test_early_return_refused(self):
        self._refuse("refuse_early_return", "non-tail position")

    def test_missing_else_refused_at_functionalize(self):
        # Extraction passes (the tail if's then-branch returns); the
        # fall-through path never assigns the result — functionalize refuses.
        self._refuse("refuse_missing_else", "not assigned on every control-flow path",
                     through_printer=True)

    def test_mixed_outputs_refused(self):
        self._refuse("refuse_mixed_outputs", "two output conventions")

    def test_return_in_void_kernel_refused(self):
        self._refuse("refuse_void_return", "return statement in a void kernel")


# =============================================================================
# Refusals (trusted base: refuse, never guess)
# =============================================================================

@needs_clang
class TestRefusalFixtures:

    def _refuse(self, function, match):
        with pytest.raises(UnsupportedConstruct, match=match):
            extract_kernel(CPP_DIR / "test_kernel_refusals.cpp", function)

    def test_compound_assignment_refused(self):
        self._refuse("refuse_plus_equal", "CompoundAssignOperator")

    def test_for_loop_refused(self):
        self._refuse("refuse_for_loop", "ForStmt")

    def test_non_real_param_refused(self):
        self._refuse("refuse_int_param", "type 'const int'")

    def test_int_literal_cast_refused(self):
        # IntegralToFloating is value-changing: not on the cast allowlist.
        self._refuse("refuse_int_literal", "IntegralToFloating")


# =============================================================================
# Node-level allowlists (no clang needed: hand-built JSON dicts)
# =============================================================================

def _declref(name, kind="ParmVarDecl"):
    return {"kind": "DeclRefExpr", "referencedDecl": {"kind": kind, "name": name}}


class TestExprAllowlists:

    def test_unlisted_cast_kind_refused(self):
        node = {"kind": "ImplicitCastExpr", "castKind": "FloatingCast",
                "inner": [_declref("x")]}
        with pytest.raises(UnsupportedConstruct, match="FloatingCast"):
            extract_expr(node)

    def test_lvalue_to_rvalue_unwraps(self):
        node = {"kind": "ImplicitCastExpr", "castKind": "LValueToRValue",
                "inner": [_declref("x")]}
        from groundline.kir import Var
        assert extract_expr(node) == Var("x")

    def test_non_abs_callee_refused(self):
        node = {"kind": "CallExpr",
                "inner": [_declref("pow", kind="FunctionDecl"), _declref("x")]}
        with pytest.raises(UnsupportedConstruct, match="call to 'pow'"):
            extract_expr(node)

    def test_modulo_opcode_refused(self):
        node = {"kind": "BinaryOperator", "opcode": "%",
                "inner": [_declref("x"), _declref("y")]}
        with pytest.raises(UnsupportedConstruct, match="binary operator '%'"):
            extract_expr(node)

    def test_declref_to_global_refused(self):
        with pytest.raises(UnsupportedConstruct, match="only.*parameters and locals"):
            extract_expr(_declref("g", kind="EnumConstantDecl"))

    def test_non_real_return_type_refused(self):
        from groundline.frontend.clang_kernel import extract_kernel_from_decl
        decl = {"kind": "FunctionDecl", "name": "f",
                "type": {"qualType": "int (const Real)"},
                "inner": [{"kind": "CompoundStmt", "inner": []}]}
        with pytest.raises(UnsupportedConstruct,
                           match="must return void or a real scalar"):
            extract_kernel_from_decl(decl)

    def test_return_statement_gates(self):
        from groundline.frontend.clang_kernel import _extract_stmts
        ret = {"kind": "ReturnStmt", "inner": [_declref("x")]}
        with pytest.raises(UnsupportedConstruct, match="void kernel"):
            _extract_stmts(ret, [], result=None, tail=True)
        with pytest.raises(UnsupportedConstruct, match="non-tail position"):
            _extract_stmts(ret, [], result="f", tail=False)
        with pytest.raises(UnsupportedConstruct, match="without a value"):
            _extract_stmts({"kind": "ReturnStmt"}, [], result="f", tail=True)

    def test_non_rt_literal_suffix_refused(self):
        node = {"kind": "UserDefinedLiteral", "inner": [
            {"kind": "ImplicitCastExpr", "castKind": "FunctionToPointerDecay",
             "inner": [{"kind": "DeclRefExpr",
                        "referencedDecl": {"kind": "FunctionDecl",
                                           "name": 'operator""_km'}}]},
            {"kind": "FloatingLiteral", "value": "3"}]}
        with pytest.raises(UnsupportedConstruct, match="_km"):
            extract_expr(node)
