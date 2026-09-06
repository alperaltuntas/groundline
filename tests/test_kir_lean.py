"""Kernel-verification tests: kernel-IR extraction, passes, and the Lean printer.

Two tiers, per D7: fixture-based tests run everywhere (the
``test_kernel_doconcurrent`` / ``test_kernel_ifstmt_join`` /
``test_kernel_negate`` conformance fixtures); the production golden test —
regenerating ``lean/groundline/Groundline/GeneratedFtn.lean`` byte-for-byte from the MOM6
dump directory — is gated on ``GROUNDLINE_DUMPS``. Semantic fidelity of the generated
Lean is checked *in Lean* (``lean/groundline/Groundline/FidelityFtn.lean``), not here.
"""

import os
import shutil
from pathlib import Path

import pytest

from groundline.kir import (
    Assign, BinOp, Cmp, ComponentRef, Do, DoConcurrent, If, IntLit, Kernel,
    Param, RealLit, Tuple_, UnsupportedConstruct, Var, ArrayRef, functionalize,
    pointize,
)
from groundline.frontend.flang_kernel import extract_kernel, extract_loop_kernel
from groundline.lean_printer import print_kernel

F90_DIR = Path(__file__).parent / "f90"
REPO = Path(__file__).parent.parent


# =============================================================================
# Fixture-based end-to-end: extract -> pointize -> print
# =============================================================================

class TestKernelFixture:

    @pytest.fixture(autouse=True)
    def setup(self):
        self.kernel = extract_kernel(F90_DIR / "test_kernel_doconcurrent_ptree",
                                     "clamp_scale")

    def test_extraction_shape(self):
        assert [p.name for p in self.kernel.params] == ["x_in", "x_out", "lo", "n"]
        assert [p.name for p in self.kernel.locals] == ["w", "i"]
        assert len(self.kernel.body) == 1
        assert isinstance(self.kernel.body[0], DoConcurrent)

    def test_pointize_drops_loop_machinery(self):
        pk = pointize(self.kernel)
        assert [p.name for p in pk.params] == ["x_in", "x_out", "lo"]  # n dropped
        assert [p.name for p in pk.locals] == ["w"]                    # i dropped
        assert all(p.rank == 0 for p in pk.params)

    def test_printed_lean(self):
        text = print_kernel(pointize(self.kernel))
        expected = """\
def clamp_scale (x_in x_out lo : ℝ) : ℝ :=
  let w := 2 * x_in - x_out
  if |w| < lo then
    lo
  else if w ^ 2 > 4 * lo then
    x_in + w / 2
  else (w + lo) * 0.5
"""
        assert text == expected


class TestIfStmtJoinFixture:
    """Logical IF statements (R1139) + the sequential guarded join: the loop
    ends with two guarded assignments to state, and the second guard's RHS
    reads b, which the first IF may have just updated."""

    @pytest.fixture(autouse=True)
    def setup(self):
        self.kernel = extract_kernel(F90_DIR / "test_kernel_ifstmt_join_ptree",
                                     "guard_pair")

    def test_ifstmt_extracted_as_single_branch_if(self):
        loop = self.kernel.body[0]
        assert isinstance(loop, DoConcurrent)
        for stmt in loop.body[1:]:
            assert isinstance(stmt, If)
            assert len(stmt.branches) == 1 and stmt.orelse == ()

    def test_printed_lean_threads_merged_state(self):
        # The load-bearing assertion: c's new value reads the MERGED b —
        # `(if t > b then t - 1 else b) + t` — not the input b.
        text = print_kernel(pointize(self.kernel))
        expected = """\
def guard_pair (a b c : ℝ) : ℝ × ℝ :=
  let t := 2 * a
  if t < c then
    (if t > b then t - 1 else b, (if t > b then t - 1 else b) + t)
  else (if t > b then t - 1 else b, c)
"""
        assert text == expected


class TestNegateFixture:
    """Unary minus: bare leaf (-y), compound operand needing printer parens
    (-(2 * x)), and negated source parentheses (-(x + y))."""

    def test_printed_lean(self):
        kernel = extract_kernel(F90_DIR / "test_kernel_negate_ptree", "neg_clip")
        expected = """\
def neg_clip (x y : ℝ) : ℝ :=
  if x < -y then
    -(2 * x)
  else -(x + y)
"""
        assert print_kernel(pointize(kernel)) == expected


class TestPlainDoFixture:
    """Rule A: a plain, perfectly nested do nest as a point kernel. The Python
    gate is the same array-index check as do concurrent; the semantic license
    is the Lean schema lemma (Groundline/SeqSchema.lean), not a source assertion."""

    @pytest.fixture(autouse=True)
    def setup(self):
        self.kernel = extract_kernel(F90_DIR / "test_kernel_plaindo_ptree",
                                     "scale_clip")

    def test_extraction_shape(self):
        assert len(self.kernel.body) == 1
        outer = self.kernel.body[0]
        assert isinstance(outer, Do) and outer.control[0] == "j"
        assert len(outer.body) == 1
        inner = outer.body[0]
        assert isinstance(inner, Do) and inner.control[0] == "i"

    def test_printed_lean(self):
        expected = """\
def scale_clip (a b s : ℝ) : ℝ :=
  let w := s * a
  if w > b then
    w
  else b
"""
        assert print_kernel(pointize(self.kernel)) == expected


class TestRecurrenceRefusalFixture:
    """Rule A's load-bearing refusal, distilled from find_dz_for_eta's pressure
    accumulation: p(i,K+1) reads what the previous k-iteration wrote. The K+1
    offset fails the index gate; K vs k is NOT a name mismatch (the dump
    lowercases — Fortran is case-insensitive)."""

    def test_recurrence_refused(self):
        # Since rule C admits read-only stencils, the recurrence refuses at
        # the write: iteration k writes cell K+1 — not the iteration's own.
        kernel = extract_kernel(F90_DIR / "test_kernel_recurrence_ptree",
                                "accumulate")
        with pytest.raises(UnsupportedConstruct, match="own cell"):
            pointize(kernel)

    def test_dump_lowercases_index_names(self):
        # The fixture spells the recurrence subscript K; the dump must have
        # lowercased it, so the refusal fires on the +1 offset, never on case.
        kernel = extract_kernel(F90_DIR / "test_kernel_recurrence_ptree",
                                "accumulate")
        inner = kernel.body[0].body[0]
        target = inner.body[0].target
        assert target.name == "p"
        assert target.subscripts[0] == Var("i")
        assert target.subscripts[1] == BinOp("add", Var("k"), IntLit("1"))


class TestIntegerArithmeticRefusals:
    """Integer VALUES in a modeled body refuse at print: Fortran evaluates
    integer `/` (and `**`) in truncating integer arithmetic, and an integer
    local would be modeled as a real — either way the ℝ model would be
    plausibly wrong, never coarse. (The C++ twin of the literal-division case
    refuses earlier, at the clang cast allowlist: `IntegralToFloating`.)
    Integers as ADDRESSES — loop indices, bounds, subscripts — are unaffected;
    pointize consumes and drops them (`test_pointize_drops_loop_machinery`)."""

    def test_integer_literal_division_refused(self):
        kernel = extract_kernel(F90_DIR / "test_kernel_intarith_ptree",
                                "int_div_literals")
        with pytest.raises(UnsupportedConstruct, match="integer-valued '/'"):
            print_kernel(kernel)

    def test_integer_local_refused(self):
        kernel = extract_kernel(F90_DIR / "test_kernel_intarith_ptree",
                                "int_local")
        with pytest.raises(UnsupportedConstruct, match="non-real local"):
            print_kernel(kernel)

    def test_integer_pow_refused_and_mixed_operands_pass(self):
        # No fixture needed at the IR tier: int**int refuses; real/int (the
        # ubiquitous `w / 2`, `w ** 2`) prints — the integer promotes and
        # real arithmetic is what the source computes.
        from groundline.lean_printer import print_expr
        with pytest.raises(UnsupportedConstruct, match=r"integer-valued '\*\*'"):
            print_expr(BinOp("pow", IntLit("2"), IntLit("3")))
        assert print_expr(BinOp("div", Var("w"), IntLit("2"))) == "w / 2"
        assert print_expr(BinOp("pow", Var("w"), IntLit("2"))) == "w ^ 2"


class TestFunctionResultFixture:
    """A Fortran FUNCTION as a kernel: its `result(name)` variable is the
    single output — appended as a parameter of intent 'result', absent from
    the printed def's binder list (the caller supplies no value for it).
    Distilled from
    MOM_continuity_PPM's `ratio_max`; the sibling functions pin the refusals
    at each stage (heading, declarations, functionalize)."""

    ptree = F90_DIR / "test_kernel_function_ptree"

    def test_extraction_shape(self):
        k = extract_kernel(self.ptree, "capped_ratio")
        assert [(p.name, p.intent) for p in k.params] == \
            [("a", "in"), ("b", "in"), ("maxrat", "in"), ("ratio", "result")]
        assert [p.name for p in k.locals] == ["q"]

    def test_printed_lean(self):
        expected = """\
def capped_ratio (a b maxrat : ℝ) : ℝ :=
  let q := maxrat * b
  if |a| > |q| then
    maxrat
  else a / b
"""
        assert print_kernel(extract_kernel(self.ptree, "capped_ratio")) == expected

    def test_doc_comment_names_the_result(self):
        text = print_kernel(extract_kernel(self.ptree, "capped_ratio"),
                            provenance="p")
        assert "Result `ratio` — the function result" in text

    def test_no_result_clause_refused(self):
        with pytest.raises(UnsupportedConstruct, match=r"no result\(name\) clause"):
            extract_kernel(self.ptree, "plain_result")

    def test_type_prefix_refused(self):
        # `real(8) function f(a) result(r)`: the result's type lives in the
        # prefix, not the specification part — refused, never dropped.
        with pytest.raises(UnsupportedConstruct,
                           match="prefix 'DeclarationTypeSpec'"):
            extract_kernel(self.ptree, "typed_prefix")

    def test_result_unassigned_on_a_path_refused(self):
        with pytest.raises(UnsupportedConstruct,
                           match="not assigned on every control-flow path"):
            print_kernel(extract_kernel(self.ptree, "partial_result"))

    def test_result_read_before_assignment_refused(self):
        with pytest.raises(UnsupportedConstruct, match="read before it is assigned"):
            print_kernel(extract_kernel(self.ptree, "reads_result"))

    def test_mutated_dummy_alongside_result_refused(self):
        with pytest.raises(UnsupportedConstruct, match="two output conventions"):
            extract_kernel(self.ptree, "mixed_outputs")


class TestJoinLocalsFixture:
    """The flux_elem construct set (tests/f90/test_kernel_join_locals): a
    logical intent(in) dummy as a Bool input used as a bare IF condition; the
    generalized join with locals (one merged and bound after the join, one
    inlined and dropped as dead) and nested joins inside branches; an
    unreferenced derived-type dummy dropped; the `elemental` prefix read
    past. Siblings pin the refusals at each stage."""

    ptree = F90_DIR / "test_kernel_join_locals_ptree"

    def test_extraction_shape(self):
        k = extract_kernel(self.ptree, "face_flux")
        assert [(p.name, p.type, p.intent) for p in k.params] == [
            ("u", "real", "in"), ("h", "real", "in"), ("h_p1", "real", "in"),
            ("q", "real", "out"), ("dq", "real", "out"), ("dt", "real", "in"),
            ("vol_cfl", "logical", "in"), ("area", "real", "in")]   # g dropped
        assert [p.name for p in k.locals] == ["cfl", "w", "tmp"]

    def test_printed_lean(self):
        # cfl (assigned in two branches only, never read after) is inlined
        # and dropped; w (every path, read after) is one merged `let`; the
        # Bool input gets its own binder group in declaration order.
        expected = """\
def face_flux (u h h_p1 q dq dt : ℝ) (vol_cfl : Bool) (area : ℝ) : ℝ × ℝ :=
  let tmp := area * dt
  let w := if u > 0 then h * (1 - (if vol_cfl then u * dt else u * area)) else if u < 0 then h_p1 * (1 - (if vol_cfl then u * dt else u * area)) else 0.5 * (h + h_p1)
  (if u > 0 then tmp * u * (h * (1 - (if vol_cfl then u * dt else u * area))) else if u < 0 then tmp * u * (h_p1 * (1 - (if vol_cfl then u * dt else u * area))) else 0, tmp * w)
"""
        assert print_kernel(extract_kernel(self.ptree, "face_flux")) == expected

    def test_prior_binding_is_the_fall_through_value(self):
        expected = """\
def rebound_local (u q : ℝ) : ℝ :=
  let w := 1
  let w := if u > 0 then u else w
  q + w
"""
        assert print_kernel(extract_kernel(self.ptree, "rebound_local")) == expected

    def test_partial_local_read_after_join_refused(self):
        with pytest.raises(UnsupportedConstruct, match="only some paths"):
            print_kernel(extract_kernel(self.ptree, "partial_local"))

    def test_logical_local_is_a_let(self):
        # A logical local is a `let` of its Bool-valued expression (2026-09-05;
        # before that the printer refused it).
        expected = """\
def logical_local (u q : ℝ) : ℝ :=
  let pos := u > 0
  if pos then
    q + u
  else q
"""
        assert print_kernel(extract_kernel(self.ptree, "logical_local")) == expected

    def test_logical_output_refused(self):
        with pytest.raises(UnsupportedConstruct, match="non-real output"):
            print_kernel(extract_kernel(self.ptree, "logical_out"))

    def test_local_read_before_assignment_refused(self):
        with pytest.raises(UnsupportedConstruct, match="read before it is assigned"):
            print_kernel(extract_kernel(self.ptree, "read_unset"))

    def test_referenced_derived_dummy_still_refused(self):
        with pytest.raises(UnsupportedConstruct, match="non-real, non-logical"):
            print_kernel(extract_kernel(self.ptree, "uses_grid"))


class TestStencilFixture:
    """The continuity_convergence construct set (tests/f90/test_kernel_stencil):
    rule C — a read-only neighbor stencil `flux(i-1,j,k)` → input `flux_im1`
    (do concurrent only); rule B widened — a component array indexed by a
    subset of the loop indices `g%iarea(i,j)` → input `iarea`; rule D — the
    nest-invariant local `h_min` → input; `optional` dummies referenced by the
    nest. Siblings pin the boundary."""

    ptree = F90_DIR / "test_kernel_stencil_ptree"

    def _nest1(self, sub):
        return pointize(extract_loop_kernel(self.ptree, sub, 1, sub))

    def test_extraction_shape(self):
        pk = self._nest1("converge")
        assert [(p.name, p.intent) for p in pk.params] == [
            ("h", "inout"), ("flux", "in"), ("dt", "in"), ("h_in", "in"),
            ("iarea", "in"), ("flux_im1", "in"), ("h_min", "in")]
        assert pk.locals == ()          # h_min promoted to an input

    def test_printed_lean(self):
        expected = """\
def converge (h flux dt h_in iarea flux_im1 h_min : ℝ) : ℝ :=
  max (h_in - dt * iarea * (flux - flux_im1)) (h_min)
"""
        assert print_kernel(self._nest1("converge")) == expected

    def test_stencil_in_plain_do_refused(self):
        with pytest.raises(UnsupportedConstruct, match="do concurrent nests only"):
            self._nest1("stencil_plain_do")

    def test_stencil_on_written_array_refused(self):
        with pytest.raises(UnsupportedConstruct, match="cross-iteration recurrence"):
            self._nest1("stencil_written")

    def test_subset_indexed_plain_array_refused(self):
        with pytest.raises(UnsupportedConstruct, match="not indexed by the loop indices"):
            self._nest1("subset_plain_array")

    def test_local_assigned_in_nest_stays_a_let(self):
        expected = """\
def local_written (h flux dt : ℝ) : ℝ :=
  let w := dt * flux
  h + w
"""
        assert print_kernel(self._nest1("local_written")) == expected


class TestInlineNestsFixture:
    """Rule B addressing: loop nest #N of a subroutine, by source-order
    ordinal (counting both do-concurrent and plain-DO nests), with the
    generated def's name supplied by the caller."""

    @pytest.fixture(autouse=True)
    def setup(self):
        self.ptree = F90_DIR / "test_kernel_inline_nests_ptree"

    def test_nest1_do_concurrent(self):
        k = extract_loop_kernel(self.ptree, "two_nests", 1, "scale_branch")
        expected = """\
def scale_branch (a b q : ℝ) : ℝ :=
  q * a
"""
        assert print_kernel(pointize(k)) == expected

    def test_nest2_plain_do(self):
        k = extract_loop_kernel(self.ptree, "two_nests", 2, "shift_branch")
        expected = """\
def shift_branch (a c q : ℝ) : ℝ :=
  a - q
"""
        assert print_kernel(pointize(k)) == expected

    def test_ordinal_addressing_is_deterministic(self):
        for nest, name in ((1, "scale_branch"), (2, "shift_branch")):
            first = print_kernel(pointize(
                extract_loop_kernel(self.ptree, "two_nests", nest, name)))
            second = print_kernel(pointize(
                extract_loop_kernel(self.ptree, "two_nests", nest, name)))
            assert first == second

    def test_out_of_range_ordinal_refused(self):
        with pytest.raises(UnsupportedConstruct, match="has 2 do-construct"):
            extract_loop_kernel(self.ptree, "two_nests", 3, "x")
        with pytest.raises(UnsupportedConstruct, match="has 2 do-construct"):
            extract_loop_kernel(self.ptree, "two_nests", 0, "x")

    def test_whole_subroutine_mode_still_refuses(self):
        # The subroutine's body is an IfConstruct, not a single nest — the
        # unchanged whole-subroutine mode must keep refusing it.
        kernel = extract_kernel(self.ptree, "two_nests")
        with pytest.raises(UnsupportedConstruct, match="exactly one"):
            pointize(kernel)


class TestComponentFixture:
    """Rule B component reads: cfg%fac (loop-invariant scalar) and cfg%w(i)
    (component array at the own index) become synthesized scalar in-params,
    named after the component, appended after the real params in first-use
    order. The collide subroutine pins the naming-collision refusal."""

    def test_printed_lean_with_synthesized_params(self):
        k = extract_kernel(F90_DIR / "test_kernel_component_ptree", "apply_cfg")
        expected = """\
def apply_cfg (a b fac w : ℝ) : ℝ :=
  fac * a + w
"""
        assert print_kernel(pointize(k)) == expected

    def test_synthesized_params_are_in_intent(self):
        pk = pointize(extract_kernel(F90_DIR / "test_kernel_component_ptree",
                                     "apply_cfg"))
        by_name = {p.name: p for p in pk.params}
        assert by_name["fac"].intent == "in" and by_name["w"].intent == "in"

    def test_name_collision_refused(self):
        k = extract_kernel(F90_DIR / "test_kernel_component_ptree", "collide")
        with pytest.raises(UnsupportedConstruct, match="collides"):
            pointize(k)


# =============================================================================
# Pass-level refusals (trusted base: refuse, never guess)
# =============================================================================

def _mini_kernel(body_stmt):
    return Kernel(
        name="k",
        params=(Param("a", "real", "in", 1), Param("b", "real", "inout", 1),
                Param("n", "integer", "in", 0)),
        locals=(Param("i", "integer", None, 0),),
        body=(DoConcurrent((("i", IntLit("1"), Var("n")),), (body_stmt,)),),
    )


class TestPointizeRefusals:

    def test_offset_read_in_do_concurrent_is_a_stencil_input(self):
        # Rule C: `a` is never written in the nest, so a(i+1) is loop-entry
        # data — the synthesized input a_ip1 (do concurrent nest).
        stmt = Assign(ArrayRef("b", (Var("i"),)),
                      ArrayRef("a", (BinOp("add", Var("i"), IntLit("1")),)))
        pk = pointize(_mini_kernel(stmt))
        assert [(p.name, p.intent) for p in pk.params] == \
            [("b", "inout"), ("a_ip1", "in")]
        assert pk.body == (Assign(Var("b"), Var("a_ip1")),)

    def test_literal_first_offset_spelling_refused(self):
        # Only `index ± literal` is admitted; `1 + i` is a different spelling.
        stmt = Assign(ArrayRef("b", (Var("i"),)),
                      ArrayRef("a", (BinOp("add", IntLit("1"), Var("i")),)))
        with pytest.raises(UnsupportedConstruct, match="not indexed by the loop indices"):
            pointize(_mini_kernel(stmt))

    def test_stencil_name_collision_refused(self):
        stmt = Assign(ArrayRef("b", (Var("i"),)),
                      ArrayRef("a", (BinOp("sub", Var("i"), IntLit("1")),)))
        k = _mini_kernel(stmt)
        k = Kernel(k.name, k.params + (Param("a_im1", "real", "in", 0),),
                   k.locals, k.body)
        with pytest.raises(UnsupportedConstruct, match="collides"):
            pointize(k)

    def test_neighbor_write_refused(self):
        stmt = Assign(ArrayRef("b", (BinOp("add", Var("i"), IntLit("1")),)),
                      ArrayRef("a", (Var("i"),)))
        with pytest.raises(UnsupportedConstruct, match="own cell"):
            pointize(_mini_kernel(stmt))

    def test_non_do_concurrent_body_refused(self):
        k = Kernel("k", (Param("b", "real", "inout", 0),), (),
                   (Assign(Var("b"), RealLit("1.0")),
                    Assign(Var("b"), RealLit("2.0"))))
        with pytest.raises(UnsupportedConstruct, match="do-concurrent"):
            pointize(k)


def _plain_do_kernel(*body_stmts, extra_params=()):
    """A `do i = 1, n` kernel over a(:) in / b(:) inout, with a scalar inout s
    and an intent(in) derived cfg available for the refusal shapes."""
    return Kernel(
        name="k",
        params=(Param("a", "real", "in", 1), Param("b", "real", "inout", 1),
                Param("s", "real", "inout", 0),
                Param("cfg", "derived:cfg_t", "in", 0),
                Param("n", "integer", "in", 0)) + tuple(extra_params),
        locals=(Param("i", "integer", None, 0),
                Param("j", "integer", None, 0)),
        body=(Do(("i", IntLit("1"), Var("n")), tuple(body_stmts)),),
    )


class TestPlainDoRefusals:
    """Rule A's write gate and nest-shape gates. Reductions and recurrences
    stay refused: they are not point-local, and their sequential-vs-unordered
    question is real mathematics reserved for a future step."""

    def test_scalar_reduction_refused(self):
        # s = s + a(i): every write must land in the iteration's own cell.
        stmt = Assign(Var("s"), BinOp("add", Var("s"), ArrayRef("a", (Var("i"),))))
        with pytest.raises(UnsupportedConstruct, match="reduction"):
            pointize(_plain_do_kernel(stmt))

    def test_imperfect_nest_refused(self):
        # A statement beside the inner do: not perfectly nested.
        inner = Do(("j", IntLit("1"), Var("n")),
                   (Assign(ArrayRef("b", (Var("j"),)), RealLit("1.0")),))
        beside = Assign(Var("s"), RealLit("0.0"))
        with pytest.raises(UnsupportedConstruct, match="not perfectly nested"):
            pointize(_plain_do_kernel(inner, beside))

    def test_duplicate_loop_index_refused(self):
        k = Kernel(
            "k",
            (Param("b", "real", "inout", 1), Param("n", "integer", "in", 0)),
            (Param("i", "integer", None, 0),),
            (Do(("i", IntLit("1"), Var("n")),
                (Do(("i", IntLit("1"), Var("n")),
                    (Assign(ArrayRef("b", (Var("i"),)), RealLit("1.0")),)),)),),
        )
        with pytest.raises(UnsupportedConstruct, match="duplicate loop index"):
            pointize(k)


class TestComponentRefusals:
    """Rule B: a component read that is neither a loop-invariant scalar nor a
    component array indexed exactly by the loop indices refuses, as do writes
    to components and reads through a base outside the supported shape."""

    def test_offset_component_subscript_refused(self):
        stmt = Assign(ArrayRef("b", (Var("i"),)),
                      ComponentRef("cfg", "w",
                                   (BinOp("add", Var("i"), IntLit("1")),)))
        with pytest.raises(UnsupportedConstruct, match="neither"):
            pointize(_plain_do_kernel(stmt))

    def test_non_intent_in_base_refused(self):
        stmt = Assign(ArrayRef("b", (Var("i"),)), ComponentRef("st", "fac", ()))
        k = _plain_do_kernel(stmt,
                             extra_params=(Param("st", "derived:cfg_t",
                                                 "inout", 0),))
        with pytest.raises(UnsupportedConstruct, match="intent\\(in\\)"):
            pointize(k)

    def test_component_assignment_target_refused(self):
        stmt = Assign(ComponentRef("cfg", "fac", ()), RealLit("1.0"))
        with pytest.raises(UnsupportedConstruct, match="assignment to derived-type"):
            pointize(_plain_do_kernel(stmt))


class TestJoinShapes:
    """The generalized control-flow join (licensed 2026-09-05): statements
    after an IF merge sequentially over elseif chains, over locals assigned
    inside branches (bound by a `let` after the join), and through nested IFs
    inside branches. The one refusal left: a local defined on only some paths,
    never bound before, and read after the join. Hand-built loop kernels;
    the fixture-level pins are in TestJoinLocalsFixture."""

    def _kernel(self, if_stmt, after):
        return Kernel(
            "k",
            (Param("a", "real", "in", 1), Param("b", "real", "inout", 1),
             Param("q", "real", "in", 0), Param("n", "integer", "in", 0)),
            (Param("w", "real", None, 0), Param("i", "integer", None, 0)),
            body=(DoConcurrent((("i", IntLit("1"), Var("n")),),
                               (if_stmt, after)),),
        )

    @staticmethod
    def _b_plus(e):
        return Assign(ArrayRef("b", (Var("i"),)),
                      BinOp("add", ArrayRef("b", (Var("i"),)), e))

    def test_elseif_chain_join_merges_as_a_cond_chain(self):
        set_b = lambda lit: Assign(ArrayRef("b", (Var("i"),)), RealLit(lit))
        stmt = If(((Cmp("gt", Var("q"), RealLit("0.0")), (set_b("1.0"),)),
                   (Cmp("lt", Var("q"), RealLit("0.0")), (set_b("2.0"),))), ())
        text = print_kernel(pointize(self._kernel(stmt, self._b_plus(ArrayRef("a", (Var("i"),))))))
        assert text == """\
def k (a b q : ℝ) : ℝ :=
  (if q > 0 then 1 else if q < 0 then 2 else b) + a
"""

    def test_local_assigned_on_every_path_is_bound_after_the_join(self):
        stmt = If(((Cmp("gt", Var("q"), RealLit("0.0")),
                    (Assign(Var("w"), RealLit("1.0")),)),),
                  (Assign(Var("w"), RealLit("2.0")),))
        text = print_kernel(pointize(self._kernel(stmt, self._b_plus(Var("w")))))
        assert text == """\
def k (b q : ℝ) : ℝ :=
  let w := if q > 0 then 1 else 2
  b + w
"""

    def test_nested_if_inside_a_joined_branch_merges_recursively(self):
        set_b = Assign(ArrayRef("b", (Var("i"),)), RealLit("1.0"))
        inner = If(((Cmp("lt", Var("q"), RealLit("1.0")), (set_b,)),), ())
        stmt = If(((Cmp("gt", Var("q"), RealLit("0.0")), (inner,)),), ())
        text = print_kernel(pointize(self._kernel(stmt, self._b_plus(ArrayRef("a", (Var("i"),))))))
        assert text == """\
def k (a b q : ℝ) : ℝ :=
  (if q > 0 then (if q < 1 then 1 else b) else b) + a
"""

    def test_partial_local_read_after_the_join_refused(self):
        stmt = If(((Cmp("gt", Var("q"), RealLit("0.0")),
                    (Assign(Var("w"), RealLit("1.0")),)),), ())
        with pytest.raises(UnsupportedConstruct, match="only some paths"):
            print_kernel(pointize(self._kernel(stmt, self._b_plus(Var("w")))))

    def test_partial_local_never_read_after_is_dropped(self):
        stmt = If(((Cmp("gt", Var("q"), RealLit("0.0")),
                    (Assign(Var("w"), RealLit("1.0")),)),), ())
        text = print_kernel(pointize(self._kernel(stmt, self._b_plus(ArrayRef("a", (Var("i"),))))))
        assert text == """\
def k (a b q : ℝ) : ℝ :=
  b + a
"""


class TestFunctionResultRefusals:
    """Pass-level gates of the result convention, on hand-built kernels: a
    result is the SOLE output, starts unbound, and must be defined on every
    path that reaches the end (including both sides of a joined IF)."""

    def test_result_alongside_inout_refused(self):
        k = Kernel("k", (Param("a", "real", "in", 0), Param("x", "real", "inout", 0),
                         Param("r", "real", "result", 0)), (),
                   (Assign(Var("x"), Var("a")), Assign(Var("r"), Var("a"))))
        with pytest.raises(UnsupportedConstruct, match="two output conventions"):
            functionalize(k)

    def test_result_assigned_on_one_side_of_a_join_refused(self):
        # `if (c > 0) r = a` followed by `r = r + a`: the join would merge r
        # with an undefined value on the other side.
        k = Kernel("k", (Param("a", "real", "in", 0), Param("c", "real", "in", 0),
                         Param("r", "real", "result", 0)), (),
                   (If(((Cmp("gt", Var("c"), RealLit("0.0")),
                         (Assign(Var("r"), Var("a")),)),), ()),
                    Assign(Var("r"), BinOp("add", Var("r"), Var("a")))))
        with pytest.raises(UnsupportedConstruct, match="only some branches of a joined IF"):
            functionalize(k)

    def test_result_kernel_without_inputs_refused_at_print(self):
        k = Kernel("k", (Param("r", "real", "result", 0),), (),
                   (Assign(Var("r"), RealLit("1.0")),))
        with pytest.raises(UnsupportedConstruct, match="no input parameters"):
            print_kernel(k)


def test_sequential_alias_read_threads_current_value():
    """After `b = a`, a read of b must see a (its current value), not the
    input b — even though the current value is a plain Var. Pins the
    unconditional substitution in functionalize.subst."""
    k = Kernel(
        "k",
        (Param("a", "real", "in", 0), Param("b", "real", "inout", 0),
         Param("c", "real", "inout", 0)),
        (),
        (Assign(Var("b"), Var("a")), Assign(Var("c"), Var("b"))),
    )
    _, outputs, expr = functionalize(k)
    assert outputs == ("b", "c")
    assert expr == Tuple_((Var("a"), Var("a")))


# =============================================================================
# Production golden test (gated on the dump directory)
# =============================================================================

DUMPS = os.environ.get("GROUNDLINE_DUMPS")
MANIFEST = REPO / "examples" / "turbo-stack.kernels.toml"


@pytest.mark.skipif(not DUMPS, reason="GROUNDLINE_DUMPS not set")
def test_generated_lean_is_current():
    """lean/groundline/Groundline/GeneratedFtn.lean must match a fresh regeneration from
    the committed production manifest — the kernel list and rendering come
    from the same kernel-bank path the CLI runs, so they can't drift apart."""
    from groundline import kernel_bank
    m = kernel_bank.load_manifest(MANIFEST)
    if not m.fortran.dumps.is_dir():
        pytest.skip("manifest dump directory not present")
    text = kernel_bank.render_fortran(m)
    assert text == m.fortran.generated.read_text(), \
        ("GeneratedFtn.lean is stale — rerun `groundline kernel generate "
         "--kernels examples/turbo-stack.kernels.toml`")


@pytest.mark.skipif(shutil.which("clang++") is None,
                    reason="clang++ not on PATH (source activate_llvm.sh)")
def test_generated_cpp_lean_is_current():
    """lean/groundline/Groundline/GeneratedCpp.lean must match a fresh regeneration —
    the C++ sibling of test_generated_lean_is_current (drift alarm for the
    committed file, the TIM header, AND the pinned clang itself, whose
    version line is stamped into the output)."""
    from groundline import kernel_bank
    m = kernel_bank.load_manifest(MANIFEST)
    if not all(e.cpp.source.exists() for e in kernel_bank.cpp_entries(m)):
        pytest.skip("TIM kernel headers not present")
    if not all(Path(d).exists() for d in m.cpp.include_dirs):
        pytest.skip("pinned C++ include dirs not present")
    text = kernel_bank.render_cpp(m)
    assert text == m.cpp.generated.read_text(), \
        ("GeneratedCpp.lean is stale — rerun `groundline kernel generate "
         "--kernels examples/turbo-stack.kernels.toml`")
