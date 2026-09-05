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
