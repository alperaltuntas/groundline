# groundline — kernel equivalence by proof

!!! abstract "Why *groundline*?"

    In glaciology, the **grounding line** is where floating ice meets
    bedrock. That is the boundary this tool draws through a codebase: what
    merely *floats* — `assumed` dispatch, `unresolved` calls, untested
    ports — versus what *rests on bedrock* — facts the compiler's semantic
    analysis resolved, and kernel equivalences proved in Lean. The name marks
    the line the tool exists to find, and to push forward.

When a compute kernel is ported from legacy Fortran to C++, how do you know
the port computes the same thing? Testing helps, but a test suite samples;
it cannot rule out the quiet transcription mistake — a swapped operand, a
dropped guard, an off-by-one — that only bites on inputs nobody tried.

**groundline replaces that worry with a machine-checked proof.** It
reads both sides straight from the compilers — flang's parse tree for the
Fortran, clang's AST for the C++ — translates each into a small Lean 4
definition over the real numbers, and proves the two definitions are the same
mathematical function on *every* input. The translator is small,
deterministic, and readable; no human transcription and no language model
sits anywhere on the trusted path.

```text
flang parse tree (with sema) ──▶ kernel IR ──▶ GeneratedFtn.lean    (Fortran side)
clang AST (JSON)             ──▶ kernel IR ──▶ GeneratedCpp.lean    (C++ side)
                                    │
                                    ▼
              equivalence theorems, checked in Lean 4 / Mathlib, over ℝ
```

A declarative manifest (`kernels.toml`) says which kernel pairs to check, and
one console script drives the whole pipeline:

```console
--8<-- "quickstart_verify.txt"
```

Nothing in the pipeline is tied to any particular application — the
[quickstart](quickstart.md) runs on a self-contained toy pair, and your own
manifest can point at your own code. groundline grew inside the **TURBO**
project, though, where kernels of the MOM6 ocean model are being ported to a
new C++/AMReX infrastructure (TIM), and that port is the manual's running
case study: the five point kernels of the original port are covered, the
primitives of the continuity mass-flux port, and its first column kernels —
per-layer folds calling a banked primitive — each with a checked equivalence
theorem and a clean axioms audit. The
[case studies](case-studies/ppm-limit-pos.md) tell their stories — including
the real bug the machinery caught.

## What the theorems mean — and deliberately do not

!!! warning "Read this before citing a theorem"

    Every equivalence in this project is proved **over ℝ, the mathematical
    real numbers — not over IEEE floating point**.

    **What a theorem certifies:** *algorithmic* agreement. The Fortran loop
    body and the C++ point function are the same mathematical function on
    every input — no wrong sign, no swapped edge value, no off-by-one index,
    no dropped guard branch. Transcription errors like these are the main
    risk of a human- or LLM-driven port, and for every banked kernel they are
    ruled out entirely.

    **What a theorem does not certify:** bit-for-bit floating-point identity.
    Numerical drift from operation reordering, fused multiply-add, or
    reduction order is real, and it remains the job of the existing
    regression and ensemble-consistency testing. This division of labor is
    deliberate — the *reals-first* philosophy of Altuntas et al. (VSS 2025,
    EPTCS 432) applied to porting: where bitwise reproducibility is
    unattainable anyway, **prove the mathematics and test the numerics**.

    Two more boundaries worth knowing: the proofs cover the per-point kernel bodies
    and their iteration schemas, not the surrounding driver code; and the
    translator refuses (rather than approximates) any construct outside its
    supported subset — see [the refusal catalog](reference/refusals.md).

## Related work

The closest relative of this approach is Logos Research's **"migration by
proof"** work, which reached a very similar design: an agent may write the
port and even search for proofs, but a deterministic translator renders both
versions into Lean with floats modeled as ℝ, and a machine-checked proof
establishes they compute the same function. The ideas the two efforts share
are load-bearing in both:

- **no LLM anywhere inside the proof pipeline** — a wrong model makes every
  downstream proof vacuous, so the model-producing code must be boring,
  deterministic, and human-auditable;
- **generated Lean readable enough to audit line by line** against the
  source it came from;
- **equivalence over ℝ as the honest claim**, with floating-point behavior
  left to numerical testing.

groundline instantiates these ideas for Fortran → C++/AMReX, with compiler
syntax trees as the substrate and a strict
[refusal discipline](concepts/kernel-ir.md) at the subset boundary. The
reals-first division of labor with numerical testing comes from Altuntas et
al. (VSS 2025, EPTCS 432).

## Where to go

- **[Installation](installation.md)** — what each toolchain adds, from the
  Python package alone up to checking the proofs.
- **[Quickstart](quickstart.md)** — a self-contained toy kernel pair, end to
  end, in five minutes.
- **[Concepts](concepts/two-irs.md)** — the architecture, written for a
  scientific-software reader who has not seen Lean.
- **[Case studies](case-studies/ppm-limit-pos.md)** — the five production
  kernels, told as stories: what each one taught, including the bug the
  machine-checking found.
- **[Reference](reference/manifest.md)** — the manifest schema, the CLI, the
  API, and the complete refusal catalog.
- **[Limits & roadmap](limits.md)** — what is out of scope today, plainly
  labeled.

!!! note "The engineering record"

    This manual documents what runs today. The engineering record — vision,
    design decisions, and the append-only development log the case studies
    are drawn from — lives in the repository:
    [`docs/VISION.md`](https://github.com/alperaltuntas/groundline/blob/main/docs/VISION.md),
    [`docs/DESIGN.md`](https://github.com/alperaltuntas/groundline/blob/main/docs/DESIGN.md),
    [`docs/DEVLOG.md`](https://github.com/alperaltuntas/groundline/blob/main/docs/DEVLOG.md).
    groundline also has a second, top-down face — a relational model of
    program structure — introduced briefly in
    [The relational track](relational.md).
