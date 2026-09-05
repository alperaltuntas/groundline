"""The ``groundline`` console script (argparse only; no click/typer).

Command groups are registered side by side in :func:`main` — today only the
kernel-verification ``kernel`` group exists; the relational track's ``check`` / ``report``
commands (DESIGN §4 Phase 4) plug in as sibling ``_add_*_group`` calls.

Import discipline: this module (and everything it pulls in) must stay
widget-free — no ipywidgets/jupyter imports — so the CLI works in a bare venv.

``groundline kernel`` — the kernel-verification pipeline, driven by a
declarative manifest (``kernels.toml``; see ``groundline/kernel_bank.py`` for
the schema). Manifest resolution: ``--kernels PATH`` > ``$GROUNDLINE_KERNELS``
> ``./kernels.toml``.

    groundline kernel list        # kernels in the manifest + basic status
    groundline kernel show NAME   # print one kernel's generated Lean defs
    groundline kernel generate    # (re)write the generated Lean modules
    groundline kernel verify      # extract fresh + compare against the
                                 # generated modules on disk, then check the
                                 # proofs (`lake build`) when the manifest
                                 # names a [lean] project (the CI gate;
                                 # non-zero exit on any mismatch or failure)
"""

from __future__ import annotations

import argparse
import difflib
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Optional

from groundline import kernel_bank as kb
from groundline.kir import UnsupportedConstruct
from groundline.lean_printer import print_kernel

_DIFF_CONTEXT_LINES = 40


def _load(args: argparse.Namespace) -> kb.Manifest:
    return kb.load_manifest(kb.resolve_manifest_path(args.kernels))


def _describe_side(label: str, detail: str, path: Path) -> str:
    status = "ok" if path.exists() else f"MISSING {path}"
    return f"    {label:8s} {detail}  [{status}]"


# --------------------------------------------------------------------------- #
# kernel subcommands
# --------------------------------------------------------------------------- #

def _cmd_list(args: argparse.Namespace) -> int:
    m = _load(args)
    print(f"manifest: {m.path}  ({len(m.kernels)} kernel(s))")
    for e in m.kernels:
        print(e.name)
        if e.fortran is not None:
            nest = f", loop nest {e.fortran.nest}" if e.fortran.nest else ""
            print(_describe_side(
                "fortran:", f"subroutine '{e.fortran.subroutine}'{nest} "
                f"in {e.fortran_label}", e.fortran.dump or e.fortran.source))
        if e.cpp is not None:
            print(_describe_side(
                "cpp:", f"function '{e.cpp.function}' in {e.cpp_label}",
                e.cpp.source))
    outs = [("fortran", m.fortran), ("cpp", m.cpp)]
    for side, cfg in outs:
        if cfg is not None:
            state = "present" if cfg.generated.exists() else "not yet generated"
            print(f"{side} generated module: {cfg.generated}  [{state}]")
    return 0


def _fortran_compiler_missing(m: kb.Manifest) -> bool:
    """True iff some Fortran kernel needs flang run fresh (source mode) and
    the manifest's flang is not on PATH. Dump-mode kernels never need it."""
    return (any(e.fortran.source is not None for e in kb.fortran_entries(m))
            and shutil.which(m.fortran.compiler) is None)


def _cmd_show(args: argparse.Namespace) -> int:
    m = _load(args)
    e = m.kernel(args.name)
    shown = []
    if e.fortran is not None:
        if e.fortran.source is not None and not shutil.which(e.fortran.compiler):
            print(f"note: '{e.fortran.compiler}' not on PATH — skipping the "
                  f"Fortran side", file=sys.stderr)
        else:
            shown.append(print_kernel(kb.extract_fortran_entry(e, m),
                                      provenance=kb.fortran_provenance(e)))
    if e.cpp is not None:
        if shutil.which(e.cpp.compiler):
            shown.append(print_kernel(kb.extract_cpp_entry(e, m),
                                      provenance=kb.cpp_provenance(e)))
        else:
            print(f"note: '{e.cpp.compiler}' not on PATH — skipping the C++ "
                  f"side", file=sys.stderr)
    print("\n".join(shown), end="")
    return 0


def _extract_verbosely(entries, extract, provenance, m) -> list:
    rendered = []
    for e in entries:
        kernel = extract(e, m)
        rendered.append((kernel, provenance(e)))
        print(f"extracted {kernel.name}: "
              f"params={[p.name for p in kernel.params]} "
              f"locals={[p.name for p in kernel.locals]}")
    return rendered


def _cmd_generate(args: argparse.Namespace) -> int:
    m = _load(args)
    if not args.skip_fortran and m.fortran is not None:
        text = kb.render_fortran(m, _extract_verbosely(
            kb.fortran_entries(m), kb.extract_fortran_entry,
            kb.fortran_provenance, m))
        m.fortran.generated.write_text(text)
        print(f"wrote {m.fortran.generated}")
    if not args.skip_cpp and m.cpp is not None:
        text = kb.render_cpp(m, _extract_verbosely(
            kb.cpp_entries(m), kb.extract_cpp_entry, kb.cpp_provenance, m))
        m.cpp.generated.write_text(text)
        print(f"wrote {m.cpp.generated}")
    return 0


def _verify_side(side: str, fresh: str, on_disk: Path) -> bool:
    """Compare one freshly rendered module against the file `generate`
    wrote (byte for byte)."""
    if not on_disk.is_file():
        print(f"DRIFT [{side}]: {on_disk} does not exist — "
              f"run `groundline kernel generate`")
        return False
    committed = on_disk.read_text()
    if fresh == committed:
        print(f"ok [{side}]: {on_disk.name} matches a fresh extraction")
        return True
    fd, tmp_name = tempfile.mkstemp(prefix=f"{on_disk.stem}.",
                                    suffix=".fresh.lean")
    os.close(fd)
    tmp = Path(tmp_name)
    tmp.write_text(fresh)
    print(f"DRIFT [{side}]: {on_disk} differs from a fresh "
          f"extraction (written to {tmp})")
    diff = list(difflib.unified_diff(
        committed.splitlines(), fresh.splitlines(),
        fromfile=str(on_disk), tofile=str(tmp), lineterm=""))
    for line in diff[:_DIFF_CONTEXT_LINES]:
        print(line)
    if len(diff) > _DIFF_CONTEXT_LINES:
        print(f"... ({len(diff) - _DIFF_CONTEXT_LINES} more diff lines)")
    return False


def _cmd_verify(args: argparse.Namespace) -> int:
    m = _load(args)
    ok = True
    if not args.skip_fortran and m.fortran is not None:
        if _fortran_compiler_missing(m):
            print(f"error: '{m.fortran.compiler}' not on PATH — cannot verify "
                  f"the Fortran side (pass --skip-fortran to verify the C++ "
                  f"side only)")
            ok = False
        else:
            ok &= _verify_side("fortran", kb.render_fortran(m),
                               m.fortran.generated)
    if not args.skip_cpp and m.cpp is not None:
        if shutil.which(m.cpp.compiler) is None:
            print(f"error: '{m.cpp.compiler}' not on PATH — cannot verify the "
                  f"C++ side (pass --skip-cpp to verify the Fortran side only)")
            ok = False
        else:
            ok &= _verify_side("cpp", kb.render_cpp(m), m.cpp.generated)
    if m.lean_project is None:
        print("note: the manifest names no [lean] project — the generated "
              "models were checked, but no theorems were")
    elif shutil.which("lake") is None:
        print("note: `lake` not on PATH — the proofs were NOT checked "
              "(activate a Lean toolchain to include them)")
    elif not ok:
        print("skipping the proof check (`lake build`) — fix the mismatch "
              "above first")
    else:
        print(f"checking the proofs: `lake build` in {m.lean_project} ...")
        proc = subprocess.run(["lake", "build"], cwd=m.lean_project)
        if proc.returncode != 0:
            print(f"FAIL: lake build exited {proc.returncode}")
            ok = False
        else:
            print("ok [lean]: every theorem in the project checked")
    return 0 if ok else 1


# --------------------------------------------------------------------------- #
# Wiring
# --------------------------------------------------------------------------- #

def _add_kernel_group(sub: argparse._SubParsersAction) -> None:
    kernel = sub.add_parser(
        "kernel", help="kernel verification: list, show, generate, verify banked kernel pairs")
    ksub = kernel.add_subparsers(dest="kernel_command", required=True,
                                 metavar="SUBCOMMAND")
    manifest_opt = argparse.ArgumentParser(add_help=False)
    manifest_opt.add_argument(
        "--kernels", metavar="PATH", default=None,
        help=f"kernel manifest (default: ${kb.MANIFEST_ENV}, "
             f"then ./{kb.MANIFEST_FILENAME})")

    p = ksub.add_parser("list", parents=[manifest_opt],
                        help="kernels in the manifest + basic status")
    p.set_defaults(func=_cmd_list)

    p = ksub.add_parser("show", parents=[manifest_opt],
                        help="print one kernel's generated Lean defs")
    p.add_argument("name", metavar="NAME")
    p.set_defaults(func=_cmd_show)

    skip_opts = argparse.ArgumentParser(add_help=False)
    skip_opts.add_argument("--skip-fortran", action="store_true")
    skip_opts.add_argument("--skip-cpp", action="store_true")

    p = ksub.add_parser("generate", parents=[manifest_opt, skip_opts],
                        help="(re)write the generated Lean modules")
    p.set_defaults(func=_cmd_generate)

    p = ksub.add_parser(
        "verify", parents=[manifest_opt, skip_opts],
        help="check the generated modules are current, then check the "
             "proofs (non-zero exit on any mismatch or failure)")
    p.set_defaults(func=_cmd_verify)


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="groundline",
        description="structural inspection and machine-checked kernel "
                    "equivalence for Fortran HPC codebases, built on "
                    "compiler syntax trees (flang/clang)")
    sub = parser.add_subparsers(dest="command", required=True,
                                metavar="COMMAND")
    _add_kernel_group(sub)
    # Relational-track groups (`check`, `report`; DESIGN §4 Phase 4) register
    # here as siblings: _add_check_group(sub), _add_report_group(sub).
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except kb.ManifestError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    except UnsupportedConstruct as e:
        print(f"error: outside the supported kernel subset — {e}",
              file=sys.stderr)
        return 2
    except FileNotFoundError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
