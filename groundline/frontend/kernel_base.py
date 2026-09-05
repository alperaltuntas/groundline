"""The kernel-IR frontend seam: anything that can turn one addressed
source kernel into a :class:`~groundline.kir.Kernel`.

The kernel-verification mirror of the relational seam in ``base.py`` (DESIGN §2.2/§2.3):
one deep method, ``extract(spec) -> Kernel``, hiding everything
format-specific — the flang dump walk on the Fortran side, the clang
invocation and JSON AST walk on the C++ side. What differs between the two
languages is only the *address* of a kernel, so each side has its own typed
spec; everything downstream (``kir``, ``functionalize``, the Lean printer) is
shared and spec-free.

Implementations: :class:`~groundline.frontend.flang_kernel.FlangKernelFrontend`
(reads a pre-generated with-sema dump, or invokes flang itself on a
standalone source) and
:class:`~groundline.frontend.clang_kernel.ClangKernelFrontend` (invokes clang
itself; the invocation config travels in the spec, not in function kwargs).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Protocol, TypeVar, runtime_checkable

from groundline.kir import Kernel

SpecT = TypeVar("SpecT", contravariant=True)


@dataclass(frozen=True)
class FortranKernelSpec:
    """Address of one Fortran kernel, in exactly one of two input modes:
    ``dump`` names a pre-generated with-sema flang parse-tree dump; ``source``
    names a standalone Fortran file the frontend runs ``compiler`` (flang) on
    to produce the same dump on demand — the mirror of how the C++ side
    invokes clang. A file that USEs unbuilt modules can only be dumped inside
    its real build, which is what the ``dump`` mode is for.

    ``nest`` selects rule-B inline-loop addressing: loop nest #``nest``
    (1-based, source order) of ``subroutine``, generated under ``def_name``
    (an inline loop has no name of its own — the spec records the pairing).
    With ``nest`` unset, the whole subroutine is the kernel and ``def_name``
    must be unset too (the def is named after the subroutine).
    """
    subroutine: str
    dump: Optional[Path] = None
    source: Optional[Path] = None
    compiler: str = "flang"
    nest: Optional[int] = None
    def_name: Optional[str] = None
    # Column-kernel addressing (docs/COLUMN_KERNELS.md): the column indices
    # (every other loop index is the vertical fold index), the manifest's
    # declared hypotheses (`assume`: flag name → value; guarded blocks are
    # pruned before modeling), and the procedure calls declared ignorable
    # (timers). `columns` set means column mode.
    columns: tuple[str, ...] = ()
    assume: tuple[tuple[str, bool], ...] = ()
    ignore_calls: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if (self.dump is None) == (self.source is None):
            raise ValueError(
                f"FortranKernelSpec({self.subroutine!r}): give exactly one of "
                f"dump (a pre-generated flang dump) or source (a Fortran file "
                f"to run flang on)")
        if (self.nest is None) != (self.def_name is None):
            raise ValueError(
                f"FortranKernelSpec({self.subroutine!r}): nest and def_name "
                f"must be given together (inline-loop addressing) or not at all")
        if self.columns and self.nest is not None:
            raise ValueError(
                f"FortranKernelSpec({self.subroutine!r}): columns (column-kernel "
                f"mode) and nest (inline-loop mode) are exclusive")


@dataclass(frozen=True)
class CppKernelSpec:
    """Address of one C++ point-kernel function in a source file (a ``.cpp``
    or a header), plus the pinned clang invocation that produces its JSON AST
    (compiler and include dirs are part of the kernel's identity — a
    different toolchain is a different dump)."""
    source: Path
    function: str
    include_dirs: tuple[str, ...] = ()
    compiler: str = "clang++"
    # Column-kernel addressing: the ordinal (1-based, source order) of the
    # `ParallelFor` call in `function` whose lambda is the kernel, the lambda's
    # column index names, and the declared hypotheses (see FortranKernelSpec).
    parallel_for: Optional[int] = None
    columns: tuple[str, ...] = ()
    assume: tuple[tuple[str, bool], ...] = ()


@runtime_checkable
class KernelFrontend(Protocol[SpecT]):
    """Extract one :class:`~groundline.kir.Kernel` from its typed spec."""

    def extract(self, spec: SpecT) -> Kernel:
        ...
