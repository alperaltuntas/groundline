# Quickstart

`examples/quickstart/` is a complete, self-contained instance of the
kernel-verification pipeline: a toy Fortran kernel and its C++ port, paired
up in a manifest, rendered into two generated Lean modules, and related by a
machine-checked equivalence theorem. It runs in a bare clone — no site paths,
no external libraries. Both sources are standalone files, so each side's
compiler runs on demand: the Fortran side needs `flang` on `PATH`, the C++
side needs `clang++` ([levels 2 and 3](installation.md) of the installation);
checking the theorem at the end needs Lean (level 4).

Every command output on this page is real, captured from the pipeline (see
`manual/snippets/render_snippets.sh` in the repository for exactly how).

## The kernel pair

The Fortran side — scale `a` by `s`, clip to `lo` from below, accumulate
into `b`, for one grid point:

```fortran
--8<-- "examples/quickstart/toy_kernel.f90"
```

The C++ port has the same per-point shape — outputs are non-const references,
inputs are const values:

```cpp
--8<-- "examples/quickstart/toy_kernel.cpp"
```

The manifest, `kernels.toml`, ties the two sides together. `[fortran]` and
`[cpp]` configure each language side once — where its sources live, which
compiler reads them, and which Lean module gets generated; each `[[kernel]]`
then gives one kernel's location on each side (the full schema is in
[the manifest reference](reference/manifest.md)):

```toml
--8<-- "examples/quickstart/kernels.toml"
```

Note the symmetry: each side names its `source` file and its compiler, and
groundline runs both compilers itself — flang for the parse-tree dump, clang
for the JSON AST. (Kernels living inside a real codebase, whose modules must
be built before flang can run, name a pre-generated `dump` instead — the
production instance at the end of this page does exactly that.)

## 1. List what the manifest declares

From `examples/quickstart/` (the CLI finds `./kernels.toml` on its own; from
anywhere else, pass `--kernels path/to/kernels.toml`):

```console
$ groundline kernel list
--8<-- "quickstart_list.txt"
```

## 2. Show the generated Lean, both sides

```console
$ groundline kernel show scale_clip_acc
--8<-- "quickstart_show.txt"
```

Two things to notice. The two point-kernel bodies are **identical** — for
this toy that is the whole demonstration: two compilers, two languages, one
extraction pipeline, same function. And each def's doc comment records its
provenance — which symbol, in which file, through which frontend.

Without one of the compilers on `PATH`, that side is skipped with a note on
stderr.

## 3. Generate the Lean modules

```console
$ groundline kernel generate
--8<-- "quickstart_generate.txt"
```

`generate` writes the two generated modules to wherever the manifest's
`generated` keys point — here, into the repository's Lean proof project
(`lean/groundline/`), where the theorem can import them. (A generated module
has to live inside whichever Lean project proves things about it, and a
Mathlib-backed project is a heavyweight thing — its own toolchain, a
multi-gigabyte dependency — so the example shares the repository's one
project rather than shipping its own.) The files are meant to be kept in
version control: they change only when a kernel's source (or the pipeline)
changes, and step 5 leans on that. The full Fortran-side module, exactly as
generated:

```lean
--8<-- "lean/groundline/Groundline/QuickstartFtn.lean"
```

The defs are byte-identical no matter where you run this; only the header
comments differ across machines, because they record which flang and clang
did the extraction — the toolchain is part of the provenance.

## 4. The theorem — the actual point of all this

The two generated defs are related by a theorem in
`lean/groundline/Groundline/QuickstartEquiv.lean`, committed right next to
the generated modules:

```lean
--8<-- "lean/groundline/Groundline/QuickstartEquiv.lean"
```

`rfl` proves an equality by *definitional* equality: Lean's kernel unfolds
both definitions and sees the same function — the strongest possible way for
the proof to close (see [the fidelity contract](concepts/printer-fidelity.md)).

One honest note on the workflow: **the theorem file is yours to write.**
groundline generates the two definitions deterministically; relating them is
a proof, and a human (or a proof-searching agent) writes it once per kernel.
For shape-identical pairs like this one it is a single `rfl` line. For real
kernels, whose bodies differ in shape between the two languages, the working
patterns are documented — see [Bank a new kernel pair](howto/bank-a-kernel.md)
and the [case studies](case-studies/ppm-limit-pos.md); every kernel banked
so far closed with a handful of lines. Once written, the theorem is checked
mechanically — by the next step's command, and by every CI run after it.

## 5. Verify — the whole chain as one command

```console
$ groundline kernel verify
--8<-- "quickstart_verify.txt"
```

`verify` does two things, in order:

1. **Are the generated models current?** For each side, it extracts every
   kernel fresh from its sources and renders the Lean module in memory, then
   compares the result **byte for byte** with the module on disk from step 3.
   Any difference — an edited source, a stale module, a changed pipeline —
   fails with a diff excerpt, and the fresh copy is parked in a temp file so
   you can inspect it.
2. **Do the proofs hold?** Because this manifest names a `[lean]`
   project, `verify` then runs `lake build` there, which checks every
   theorem in that project — for the quickstart, the equivalence theorem
   above. If a manifest names no `[lean]` project, `verify` says so
   explicitly and you have only checked that the models are current, not
   that any theorem holds.

Both stages exit non-zero on failure, which is what makes `verify` a CI
gate: after any change to the Fortran, the C++, or the pipeline itself, one
command establishes that the committed models match the sources *and* the
equivalence holds. See [Wire verification into CI](howto/ci.md).

## Where the production instance differs

The production manifest,
[`examples/turbo-stack.kernels.toml`](https://github.com/alperaltuntas/groundline/blob/main/examples/turbo-stack.kernels.toml),
declares the six MOM6 ⇄ TIM kernel pairs — the five of the case studies plus
`ratio_max`, the first primitive of the continuity mass-flux port. Two
differences from the toy:

- Its Fortran kernels live inside MOM6, whose modules must be built before
  flang can process them — so each entry names a pre-generated `dump` from
  the real model build instead of a `source`, and the manifest's
  `[fortran] dumps` points at that build's dump directory.
- Its C++ sources are the real port's headers, so the manifest pins their
  include paths (`include_dirs`); the five case-study kernels are loops in
  the Fortran source, so their entries carry `pointize = true` (see the next
  section) — `ratio_max`, a per-point function, needs no license.

```console
$ groundline kernel list --kernels examples/turbo-stack.kernels.toml
--8<-- "production_list.txt"
```

Those paths are site-specific by nature (NCAR's GLADE filesystem) — the
manifest is the *only* place they exist; the package itself carries no
built-in paths. To pair up your own kernels, copy either manifest and
repoint it: see [Bank a new kernel pair](howto/bank-a-kernel.md).

## And when the Fortran kernel is a loop?

Real kernels rarely arrive as tidy per-point subroutines — in a model, the
update above would live inside a loop over the grid. The quickstart
directory has that version too, in `toy_kernel_loop.f90`:

```fortran
--8<-- "examples/quickstart/toy_kernel_loop.f90"
```

Suppose you add it to the manifest, the same way as the point kernel:

```toml
[[kernel]]
name    = "scale_clip_acc_loop"
fortran = { source = "toy_kernel_loop.f90", subroutine = "scale_clip_acc_loop" }
```

Asking for it gets a refusal, not a def:

```console
$ groundline kernel show scale_clip_acc_loop
--8<-- "quickstart_pointize_refusal.txt"
```

A loop over a column and a function of one point are different things, and
groundline will not silently treat them as the same. Adding
`pointize = true` to the entry is the explicit license: it tells groundline
to strip the loop and model its **per-point body** — which is exactly what
you want when a C++ port turned a Fortran loop into a per-point function:

```console
$ groundline kernel show scale_clip_acc_loop
--8<-- "quickstart_show_loop.txt"
```

The same function as the point subroutine — so its equivalence theorem
against the C++ port would be the same one-line `rfl`. What makes the
loop-to-point reduction legitimate (the loop's `do concurrent` independence
assertion here; a proved schema lemma for plain `do` loops) is the subject of
[the Pointize concept page](concepts/pointize.md). All five case-study
production kernels are loops banked under this license; the manifest states
it out loud each time.
