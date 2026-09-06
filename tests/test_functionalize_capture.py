"""functionalize's pending-value discipline (kir.py, 2026-09-05): an output's
or fold state's value is a symbolic expression over the names in scope, and
must never be captured by a later re-binding of one of those names.

Pinned here on hand-built kernels: (1) an output that read a local is
let-bound before the local is re-assigned; (2) a joined IF whose locals read
each other's prior values is bound by one destructuring let; (3) a joined IF
whose locals can be sequenced is emitted in a capture-free order. Plus the
printer's literal canonicalization, which the two frontends' spellings of one
value rely on.
"""

import pytest

from groundline.kir import (
    Assign, BinOp, Cmp, If, Kernel, Param, RealLit, UnsupportedConstruct, Var,
)
from groundline.lean_printer import _real_lit, print_kernel


def _kernel(name, body, locals_):
    params = (Param("u", "real", "in", 0), Param("q", "real", "inout", 0))
    return Kernel(name, params, tuple(Param(l, "real", None, 0) for l in locals_), tuple(body))


def test_output_pending_value_is_let_bound_before_its_local_is_rebound():
    # q = w ; w = u + 1  — the output must keep the FIRST w.
    k = _kernel("cap", [
        Assign(Var("w"), Var("u")),
        Assign(Var("q"), Var("w")),
        Assign(Var("w"), BinOp("add", Var("u"), RealLit("1.0"))),
    ], ["w"])
    assert print_kernel(k) == """\
def cap (u q : ℝ) : ℝ :=
  let w := u
  let q := w
  let w := u + 1
  q
"""


def test_join_locals_reading_each_other_bind_by_one_destructuring_let():
    # a = u ; b = u + 1 ; if (u > 0) then a = b else b = a endif ; q = a - b
    k = _kernel("swap", [
        Assign(Var("a"), Var("u")),
        Assign(Var("b"), BinOp("add", Var("u"), RealLit("1.0"))),
        If(((Cmp("gt", Var("u"), RealLit("0.0")), (Assign(Var("a"), Var("b")),)),),
           (Assign(Var("b"), Var("a")),)),
        Assign(Var("q"), BinOp("sub", Var("a"), Var("b"))),
    ], ["a", "b"])
    assert print_kernel(k) == """\
def swap (u q : ℝ) : ℝ :=
  let a := u
  let b := u + 1
  let (a, b) := if u > 0 then (b, b) else (a, a)
  a - b
"""


def test_join_locals_are_sequenced_capture_free():
    # w = u ; v = 1 ; if (u > 0) then w = 2*u else v = w endif ; q = v + w
    # v's else value reads the PRIOR w, so v is bound before w is re-bound.
    k = _kernel("seq", [
        Assign(Var("w"), Var("u")),
        Assign(Var("v"), RealLit("1.0")),
        If(((Cmp("gt", Var("u"), RealLit("0.0")),
             (Assign(Var("w"), BinOp("mul", RealLit("2.0"), Var("u"))),)),),
           (Assign(Var("v"), Var("w")),)),
        Assign(Var("q"), BinOp("add", Var("v"), Var("w"))),
    ], ["w", "v"])
    assert print_kernel(k) == """\
def seq (u q : ℝ) : ℝ :=
  let w := u
  let v := 1
  let v := if u > 0 then v else w
  let w := if u > 0 then 2 * u else w
  v + w
"""


@pytest.mark.parametrize("text,lean", [
    ("3.0", "3"), ("0.0", "0"), (".5", "0.5"), ("0.10", "0.1"), ("1.5", "1.5"),
    ("1.0e-12", "1e-12"), ("1E-12", "1e-12"), ("1e-6", "1e-6"), ("1.d-6", "1e-6"),
    ("2.5e+03", "2.5e3"), ("2", "2"),
])
def test_real_literal_canonical_spelling(text, lean):
    assert _real_lit(text) == lean
