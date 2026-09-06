"""Column kernels (docs/COLUMN_KERNELS.md): the column pass, the fold/map
model, calls to banked primitives, pruning under declared hypotheses, and
the C++ ParallelFor-lambda address.

The fixtures are `tests/f90/test_kernel_column` (committed dump) and
`tests/cpp/test_kernel_column.cpp` (clang at test time, so those tests are
gated on ``clang++``). Column kernels are driven through the kernel bank
because resolving a call needs the manifest's callee registry.
"""

import shutil
from pathlib import Path

import pytest

from groundline import kernel_bank as kb
from groundline.kir import Assign, FoldStmt, MapStmt, UnsupportedConstruct
from groundline.lean_printer import print_kernel

REPO = Path(__file__).parent.parent
F90 = REPO / "tests" / "f90"
CPP = REPO / "tests" / "cpp"

needs_clang = pytest.mark.skipif(
    shutil.which("clang++") is None, reason="clang++ not on PATH (source activate_llvm.sh)")

FLUX_PT = '''
[[kernel]]
name = "flux_pt"
fortran = { dump = "test_kernel_column_ptree", subroutine = "flux_pt" }
'''
FLUX_PT_BOTH = '''
[[kernel]]
name = "flux_pt"
fortran = { dump = "test_kernel_column_ptree", subroutine = "flux_pt" }
cpp = { source = "test_kernel_column.cpp", function = "flux_pt_point" }
'''
COLUMN_SUM = '''
[[kernel]]
name = "column_sum"
fortran = { dump = "test_kernel_column_ptree", subroutine = "column_sum" }
columns = ["j", "i"]
assume = { specified_bc = false }
ignore_calls = ["timer_start", "timer_end"]
'''
COLUMN_SUM_BOTH = '''
[[kernel]]
name = "column_sum"
fortran = { dump = "test_kernel_column_ptree", subroutine = "column_sum" }
cpp = { source = "test_kernel_column.cpp", function = "column_sum", parallel_for = 1, columns = ["i", "j"] }
columns = ["j", "i"]
assume = { specified_bc = false }
ignore_calls = ["timer_start", "timer_end"]
'''


def _manifest(tmp_path, kernels: str, cpp: bool = False):
    text = (f'[fortran]\ndumps = "{F90}"\ngenerated = "{tmp_path / "F.lean"}"\n'
            f'namespace = "Demo.Ftn"\n')
    if cpp:
        text += (f'\n[cpp]\nsources = "{CPP}"\ngenerated = "{tmp_path / "C.lean"}"\n'
                 f'namespace = "Demo.Cpp"\n')
    path = tmp_path / "kernels.toml"
    path.write_text(text + kernels)
    return kb.load_manifest(path)


def _fortran(m, name):
    return kb.extract_fortran_entry(m.kernel(name), m)


FORTRAN_GOLDEN = """\
def column_sum {κ : Type*} (ks : List κ) (u h : κ → ℝ) (qbt dt : ℝ) (h_ip1 : κ → ℝ) (dy iarea iarea_ip1 : ℝ) (vol_cfl : Bool) : ℝ :=
  let q := fun k => (flux_pt (u k) (h k) (h_ip1 k) 0 0 dy iarea iarea_ip1 dt vol_cfl).1
  let dq := fun k => (flux_pt (u k) (h k) (h_ip1 k) 0 0 dy iarea iarea_ip1 dt vol_cfl).2
  let qbt := ks.foldl (fun qbt k => qbt + q k) 0
  qbt
"""

CPP_GOLDEN = """\
def column_sum {κ : Type*} (ks : List κ) (u h : κ → ℝ) (qbt dt dy iarea : ℝ) (h_ip1 : κ → ℝ) (iarea_ip1 : ℝ) (vol_cfl : Bool) : ℝ :=
  let qbt_val := 0
  let qbt_val := ks.foldl (fun qbt_val k =>
      let q_val := (flux_pt_point (u k) (h k) (h_ip1 k) 0 0 dy iarea iarea_ip1 dt vol_cfl).1
      let dq_val := (flux_pt_point (u k) (h k) (h_ip1 k) 0 0 dy iarea iarea_ip1 dt vol_cfl).2
      qbt_val + q_val) qbt_val
  qbt_val
"""


class TestColumnFixtureFortran:
    """`column_sum`: a whole-array init, a `do concurrent (k,j,i)` MAP calling
    the banked `flux_pt` (two intent(out) actuals landing in per-k arrays),
    and a plain `do k;j;i` FOLD accumulating the per-column output; the timer
    calls dropped, the bounds-only integer local dropped, the OBC-style block
    pruned under `specified_bc = false` (its body reads q(i-1,j,k), which
    would refuse if modeled)."""

    def test_shape(self, tmp_path):
        k = _fortran(_manifest(tmp_path, FLUX_PT + COLUMN_SUM), "column_sum")
        assert k.column
        assert [type(s).__name__ for s in k.body] == ["Assign", "MapStmt", "FoldStmt"]
        assert isinstance(k.body[1], MapStmt) and k.body[1].index == "k"
        assert isinstance(k.body[2], FoldStmt) and k.body[2].state == ("qbt",)
        # per-k arrays, per-column scalars, stencil input, Bool input
        by = {p.name: p for p in k.params}
        assert by["u"].type == "real[k]" and by["h_ip1"].type == "real[k]"
        assert by["dy"].type == "real" and by["vol_cfl"].type == "logical"
        assert by["qbt"].intent == "out"

    def test_printed_lean(self, tmp_path):
        k = _fortran(_manifest(tmp_path, FLUX_PT + COLUMN_SUM), "column_sum")
        assert print_kernel(k) == FORTRAN_GOLDEN

    def test_provenance_states_the_hypotheses(self, tmp_path):
        m = _manifest(tmp_path, FLUX_PT + COLUMN_SUM)
        prov = kb.fortran_provenance(m.kernel("column_sum"))
        assert "column kernel over (j, i)" in prov
        assert "`specified_bc = false`" in prov and "pruned" in prov
        assert "`timer_start`" in prov and "effect-free" in prov

    def test_unbanked_callee_refused(self, tmp_path):
        # Without the flux_pt entry the call cannot be resolved.
        with pytest.raises(UnsupportedConstruct, match="not a banked primitive"):
            _fortran(_manifest(tmp_path, COLUMN_SUM), "column_sum")

    def _refuse(self, tmp_path, sub, match, extra=""):
        entry = (f'\n[[kernel]]\nname = "{sub}"\n'
                 f'fortran = {{ dump = "test_kernel_column_ptree", subroutine = "{sub}" }}\n'
                 f'columns = ["j", "i"]\n{extra}')
        with pytest.raises(UnsupportedConstruct, match=match):
            _fortran(_manifest(tmp_path, FLUX_PT + entry), sub)

    def test_scan_refused(self, tmp_path):
        self._refuse(tmp_path, "scan", "a scan")

    def test_k_recurrence_refused(self, tmp_path):
        self._refuse(tmp_path, "k_recurrence", "k-recurrence")

    def test_call_inside_loop_not_ignored_refused(self, tmp_path):
        self._refuse(tmp_path, "unbanked_call", "not a banked primitive")

    def test_columns_and_pointize_exclusive(self, tmp_path):
        with pytest.raises(kb.ManifestError, match="exclusive"):
            _manifest(tmp_path, FLUX_PT + COLUMN_SUM.replace(
                'columns = ["j", "i"]', 'columns = ["j", "i"]\npointize = true'))

    def test_column_kernel_named_after_subroutine(self, tmp_path):
        with pytest.raises(kb.ManifestError, match="named after its subroutine"):
            _manifest(tmp_path, FLUX_PT + COLUMN_SUM.replace(
                'name = "column_sum"', 'name = "renamed"'))


@needs_clang
class TestColumnFixtureCpp:
    """The ParallelFor lambda of `column_sum`: a per-column accumulator, a
    `for k` FOLD calling the banked `flux_pt_point` with two `Real&` receivers
    (never read by the callee, hence outputs), `+=`, a per-column store; the
    guarded block pruned under `specified_bc = false` (its body would refuse:
    an int literal in a Real expression)."""

    def test_printed_lean(self, tmp_path):
        m = _manifest(tmp_path, FLUX_PT_BOTH + COLUMN_SUM_BOTH, cpp=True)
        k = kb.extract_cpp_entry(m.kernel("column_sum"), m)
        assert k.column
        assert print_kernel(k) == CPP_GOLDEN

    def test_lambda_columns_must_match(self, tmp_path):
        m = _manifest(tmp_path, FLUX_PT_BOTH + COLUMN_SUM_BOTH.replace(
            'columns = ["i", "j"]', 'columns = ["i", "k"]'), cpp=True)
        with pytest.raises(UnsupportedConstruct, match="do not spell the declared columns"):
            kb.extract_cpp_entry(m.kernel("column_sum"), m)

    def _refuse(self, tmp_path, fn, match):
        entry = (f'\n[[kernel]]\nname = "{fn}"\n'
                 f'cpp = {{ source = "test_kernel_column.cpp", function = "{fn}", '
                 f'parallel_for = 1, columns = ["i", "j"] }}\ncolumns = ["j", "i"]\n')
        m = _manifest(tmp_path, FLUX_PT_BOTH + entry, cpp=True)
        with pytest.raises(UnsupportedConstruct, match=match):
            kb.extract_cpp_entry(m.kernel(fn), m)

    def test_scan_refused(self, tmp_path):
        self._refuse(tmp_path, "refuse_scan", "a scan")

    def test_unbanked_call_refused(self, tmp_path):
        self._refuse(tmp_path, "refuse_unbanked_call", "not a banked primitive")

    def test_cpp_reference_outputs_never_read_are_outputs(self, tmp_path):
        m = _manifest(tmp_path, FLUX_PT_BOTH, cpp=True)
        callee = kb.cpp_callees(m)["flux_pt_point"]
        assert [(p.name, p.intent) for p in callee.params if p.intent != "in"] == \
            [("q", "out"), ("dq", "out")]


# --------------------------------------------------------------------------- #
# B2 constructs (docs/COLUMN_KERNELS.md §5): masks, row scratch, several fold
# states, component-array outputs, a column-level IF, the destructuring join.
# Fixtures: tests/f90/test_kernel_bt_cont, tests/cpp/test_kernel_bt_cont.cpp.
# --------------------------------------------------------------------------- #

BT_FLUX_PT = '''
[[kernel]]
name = "flux_pt"
fortran = { dump = "test_kernel_bt_cont_ptree", subroutine = "flux_pt" }
'''
BT_FLUX_PT_BOTH = '''
[[kernel]]
name = "flux_pt"
fortran = { dump = "test_kernel_bt_cont_ptree", subroutine = "flux_pt" }
cpp = { source = "test_kernel_bt_cont.cpp", function = "flux_pt_point" }
'''
BT_CONT = '''
[[kernel]]
name = "bt_cont"
fortran = { dump = "test_kernel_bt_cont_ptree", subroutine = "bt_cont" }
columns = ["j", "i"]
'''
BT_CONT_BOTH = '''
[[kernel]]
name = "bt_cont"
fortran = { dump = "test_kernel_bt_cont_ptree", subroutine = "bt_cont" }
cpp = { source = "test_kernel_bt_cont.cpp", function = "bt_cont", parallel_for = 1, columns = ["i", "j"] }
columns = ["j", "i"]
'''

BT_FORTRAN_GOLDEN = """\
def bt_cont {κ : Type*} (ks : List κ) (u : κ → ℝ) (du0 dt : ℝ) (do_i : Bool) (dx : ℝ) (h_ip1 : κ → ℝ) (fa_w fa_e ubt : ℝ) : ℝ × ℝ × ℝ :=
  let idt := 1 / dt
  let cfl_min := 1e-6
  let dul := max (0) (du0 + (cfl_min * idt) * dx)
  let fa_l := 0
  let uh_l := 0
  let dul := ks.foldl (fun dul k =>
      if do_i then
        if u k + dul < 0 then
          -u k
        else dul
      else dul) dul
  let (fa_l, uh_l) := ks.foldl (fun (fa_l, uh_l) k =>
      if do_i then
        let u_l := u k + dul
        let q_l := (flux_pt u_l (h_ip1 k) 0 0 dt).1
        let dq_l := (flux_pt u_l (h_ip1 k) 0 0 dt).2
        (fa_l + dq_l, uh_l + q_l)
      else (fa_l, uh_l)) (fa_l, uh_l)
  if do_i then
    let fa_0 := fa_l
    let fa_avg := fa_l
    let fa_avg := if (dul - du0) ≠ 0 then uh_l / (dul - du0) else fa_avg
    let (fa_avg, fa_0) := if fa_avg > fa_0 then (fa_0, fa_0) else if fa_avg < 0.5 * fa_0 then (fa_avg, fa_avg) else (fa_avg, fa_0)
    let fa_w := fa_0
    let fa_0 := 0
    (fa_w, fa_avg - fa_0, 1.5 * (dul - du0))
  else (0, 0, 0)
"""

BT_CPP_GOLDEN = """\
def bt_cont {κ : Type*} (ks : List κ) (u : κ → ℝ) (fa_w fa_e ubt du0 dt dx : ℝ) (do_i : Bool) (h_ip1 : κ → ℝ) : ℝ × ℝ × ℝ :=
  let idt := 1 / dt
  let cfl_min := 1e-6
  let active := (do_i)
  let dul := max (0) (du0 + (cfl_min * idt) * dx)
  let fa_l := 0
  let uh_l := 0
  if active then
    let dul := ks.foldl (fun dul k =>
        if u k + dul < 0 then
          -u k
        else dul) dul
    let (fa_l, uh_l) := ks.foldl (fun (fa_l, uh_l) k =>
        let u_l := u k + dul
        let q_l := (flux_pt_point u_l (h_ip1 k) 0 0 dt).1
        let dq_l := (flux_pt_point u_l (h_ip1 k) 0 0 dt).2
        (fa_l + dq_l, uh_l + q_l)) (fa_l, uh_l)
    let fa_0 := fa_l
    let fa_avg := fa_l
    let fa_avg := if (dul - du0) ≠ 0 then uh_l / (dul - du0) else fa_avg
    let (fa_avg, fa_0) := if fa_avg > fa_0 then (fa_0, fa_0) else if fa_avg < 0.5 * fa_0 then (fa_avg, fa_avg) else (fa_avg, fa_0)
    let fa_w := fa_0
    let fa_0 := 0
    (fa_w, fa_avg - fa_0, 1.5 * (dul - du0))
  else (0, 0, 0)
"""


class TestBtContFixture:
    """Masks (`do concurrent (i, do_i(i,j))` under `do k` → `if do_i then step
    else state` in the fold; the tail `if (do_I)` → a column-level IF), row
    scratch (`dul(i)` under `do j` → a per-column local), two-state fold,
    component-array outputs (`cont%fa_w(i,j) = …` → output `fa_w`), the
    destructuring join, the output let-bound before its local is re-assigned;
    the C++ mirror with `do_i(i,j,0) != 0` bound to a `const bool` local,
    `const Real` prologue locals hoisted, and `if (active)` around the folds."""

    def test_fortran_golden(self, tmp_path):
        m = _manifest(tmp_path, BT_FLUX_PT + BT_CONT)
        assert print_kernel(_fortran(m, "bt_cont")) == BT_FORTRAN_GOLDEN

    @needs_clang
    def test_cpp_golden(self, tmp_path):
        m = _manifest(tmp_path, BT_FLUX_PT_BOTH + BT_CONT_BOTH, cpp=True)
        assert print_kernel(kb.extract_cpp_entry(m.kernel("bt_cont"), m)) == BT_CPP_GOLDEN

    def test_fortran_shape(self, tmp_path):
        m = _manifest(tmp_path, BT_FLUX_PT + BT_CONT)
        k = _fortran(m, "bt_cont")
        folds = [s for s in k.body if isinstance(s, FoldStmt)]
        assert [f.state for f in folds] == [("dul",), ("fa_l", "uh_l")]
        assert [p.name for p in k.params if p.intent == "out"] == ["fa_w", "fa_e", "ubt"]
        assert next(p for p in k.params if p.name == "do_i").type == "logical"

    def _refuse_fortran(self, tmp_path, subroutine, match, extra=""):
        entry = (f'\n[[kernel]]\nname = "{subroutine}"\nfortran = {{ dump = '
                 f'"test_kernel_bt_cont_ptree", subroutine = "{subroutine}" }}\n{extra}')
        m = _manifest(tmp_path, BT_FLUX_PT + entry)
        with pytest.raises(UnsupportedConstruct, match=match):
            print_kernel(_fortran(m, subroutine))

    def test_masked_map_refused(self, tmp_path):
        self._refuse_fortran(tmp_path, "masked_map", "masked map", 'columns = ["j", "i"]\n')

    def test_row_scratch_read_before_written_refused(self, tmp_path):
        self._refuse_fortran(tmp_path, "scratch_read_first",
                             "fold state 'acc' is read before it is assigned",
                             'columns = ["j", "i"]\n')

    def test_row_scratch_shared_by_concurrent_columns_refused(self, tmp_path):
        self._refuse_fortran(tmp_path, "scratch_racing", "shared by the columns along",
                             'columns = ["j", "i"]\n')

    def test_component_write_inside_k_loop_refused(self, tmp_path):
        self._refuse_fortran(tmp_path, "comp_write_in_k", "inside a k-loop",
                             'columns = ["j", "i"]\n')

    def test_masked_nest_refused_at_the_point_tier(self, tmp_path):
        self._refuse_fortran(tmp_path, "masked_point", "scalar mask", "pointize = true\n")

    @needs_clang
    def test_cpp_flag_array_read_as_value_refused(self, tmp_path):
        m = _manifest(tmp_path, BT_FLUX_PT_BOTH + '''
[[kernel]]
name = "refuse_flag_value"
cpp = { source = "test_kernel_bt_cont.cpp", function = "refuse_flag_value", parallel_for = 1, columns = ["i", "j"] }
''', cpp=True)
        with pytest.raises(UnsupportedConstruct, match="read as a value"):
            kb.extract_cpp_entry(m.kernel("refuse_flag_value"), m)

    @needs_clang
    def test_cpp_nonconst_capture_refused(self, tmp_path):
        m = _manifest(tmp_path, BT_FLUX_PT_BOTH + '''
[[kernel]]
name = "refuse_nonconst_capture"
cpp = { source = "test_kernel_bt_cont.cpp", function = "refuse_nonconst_capture", parallel_for = 1, columns = ["i", "j"] }
''', cpp=True)
        with pytest.raises(UnsupportedConstruct, match="non-const function-scope"):
            kb.extract_cpp_entry(m.kernel("refuse_nonconst_capture"), m)

    def test_literal_without_source_spelling_refused(self):
        from groundline.frontend.clang_kernel import extract_expr
        with pytest.raises(UnsupportedConstruct, match="source spelling"):
            extract_expr({"kind": "FloatingLiteral", "value": "0.100000000000000000001"})
