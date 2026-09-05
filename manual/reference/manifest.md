# The kernel manifest (`kernels.toml`)

The manifest is the single declarative home of everything site-specific:
which kernel pairs exist, where the dumps and sources live, which compiler
reads the C++ side, and where the generated modules go. The package itself
carries **no built-in paths or defaults** — the schema is implemented (and
documented) in `groundline/kernel_bank.py`.

**How to read a manifest:** the `[fortran]` and `[cpp]` sections configure
each language side *once* — its inputs, its toolchain, and the Lean module
`groundline kernel generate` writes for it. Each `[[kernel]]` table then
gives one kernel's *location* on each side. The two vocabularies meet but
don't overlap: sections say how a side works, kernel entries say where a
kernel lives.

## Resolution order

Every `groundline kernel` subcommand locates its manifest the same way, first
match wins:

1. `--kernels PATH` (CLI flag)
2. `$GROUNDLINE_KERNELS` (environment variable)
3. `./kernels.toml` (current directory)

Nothing else — no home-directory config, no fallback path.

## General rules

- Parsed with stdlib `tomllib` (no extra dependency).
- String values expand `${ENV_VAR}` from the environment; an **unset variable
  refuses** (`ManifestError`), never expands to empty.
- Relative paths resolve against **the manifest file's directory**, so a
  manifest travels with its tree.
- **Unknown keys refuse.** The manifest sits close to the trusted base: a
  typo like `namespcae` must fail loudly, not be silently ignored. Types are
  checked; missing required keys are named.
- Duplicate kernel names refuse.

## `[fortran]` — the flang side (omit to disable the side entirely)

| Key | Required | Meaning |
|---|---|---|
| `generated` | yes | the Fortran-side Lean module `kernel generate` writes (and `verify` checks) |
| `namespace` | yes | Lean namespace of the generated module (e.g. `Groundline.GeneratedFtn`) |
| `dumps` | only if any kernel uses `dump` | directory of pre-generated flang parse-tree dumps (with sema); each kernel's `dump` resolves under it |
| `sources` | no (default `.`) | directory the kernels' `source` values resolve under |
| `compiler` | no (default `flang`) | the compiler executable, run on `source` kernels to dump them on demand |
| `blurb` | no | extra lines appended to the generated module's header comment |

When any kernel is source-mode, the flang version and invocation are stamped
into the generated module's header — the same provenance discipline as the
C++ side.

## `[cpp]` — the clang side (omit to disable)

| Key | Required | Meaning |
|---|---|---|
| `generated` | yes | the C++-side Lean module `kernel generate` writes |
| `namespace` | yes | Lean namespace of the generated module |
| `sources` | no (default `.`) | directory the kernels' `source` values resolve under |
| `include_dirs` | no | pinned `-I` directories — part of the kernel identity, stamped into the generated provenance header |
| `compiler` | no (default `clang++`) | the compiler executable |
| `provenance_root` | no | source files display relative to this root in generated doc comments — what keeps them byte-stable across machines |
| `blurb` | no | extra header-comment lines |

## `[lean]` — where the proofs live (optional)

| Key | Required | Meaning |
|---|---|---|
| `project` | yes (if section present) | a `lake` project; `kernel verify` runs `lake build` here after the model check passes, re-checking every theorem in it |

Without this section, `verify` checks only that the generated models are
current — it prints a note saying no theorems were checked.

## `[[kernel]]` — one table per kernel pair

```toml
[[kernel]]
name = "ppm_limit_pos"
fortran  = { dump = "MOM6/MOM_continuity_PPM.o_ptree", subroutine = "ppm_limit_pos" }
cpp      = { source = "mom_continuity_ppm_kernel.hpp", function = "ppm_limit_pos_point" }
pointize = true
```

- `name` (required) — the entry's identity, and (for inline-loop entries) the
  generated def's name.
- `fortran = { dump | source, subroutine [, nest [, def_name]] }` —
  `subroutine` names the procedure, a subroutine *or a function* (a
  function's `result(name)` variable is the kernel's single output); and
  exactly one of:
    - `dump` — a pre-generated with-sema flang dump, resolved under
      `[fortran].dumps`. For kernels inside a real codebase, whose modules
      must be built before flang can run.
    - `source` — a standalone Fortran file, resolved under
      `[fortran].sources`; groundline runs `[fortran].compiler` on it and
      reads the dump on demand — the mirror of the C++ side.

    Without `nest`, the whole subroutine is the kernel and **the entry must
    be named after the subroutine** (enforced). With `nest = N`, loop nest
    #N of the subroutine (source-order ordinal) is extracted, generated
    under `def_name` if given, else under `name` — see
    [inline-loop addressing](../howto/inline-loops.md). `def_name` without
    `nest` refuses.
- `cpp = { source, function }` — `source` is a `.cpp` or a header, resolved
  under `[cpp].sources`; clang runs on it on demand.
- `pointize` (default `false`) — the explicit license to reduce a Fortran
  **loop nest** to its per-point body before comparing. A loop and a point
  function are different things, so a loop-shaped kernel *refuses* without
  it; the option refuses on a kernel that is not a loop. What justifies the
  reduction is the subject of [Pointize](../concepts/pointize.md).
- Either side may be omitted (a Fortran-only or C++-only entry is legal); an
  entry with neither refuses, as does a side whose section is absent.

The manifest-relative spellings of the `dump`/`source` values (the C++ one
re-rooted at `provenance_root` when set) are what appear in the generated
doc comments — resolved absolute paths never leak into generated files.

## The two committed instances

- [`examples/quickstart/kernels.toml`](https://github.com/alperaltuntas/groundline/blob/main/examples/quickstart/kernels.toml)
  — the self-contained toy pair, walked through in [the quickstart](../quickstart.md).
- [`examples/turbo-stack.kernels.toml`](https://github.com/alperaltuntas/groundline/blob/main/examples/turbo-stack.kernels.toml)
  — the production instance (the MOM6 ⇄ TIM case study): the eleven kernel
  entries, the NCAR dump directory and kernel header paths, pinned AMReX/MPI
  include dirs, and the shared `[lean]` project. On another site, copy it
  and repoint the paths — that file is the *only* thing that changes.
