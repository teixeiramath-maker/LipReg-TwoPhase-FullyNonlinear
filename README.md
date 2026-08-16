# Uniform Lipschitz Regularity for Two-Phase Singular Perturbations

This repository contains a Lean 4 and mathlib formalization accompanying the paper
*Uniform Lipschitz regularity for two-phase singularly perturbed fully nonlinear elliptic
equations* by Thialita M. Nascimento, Aelson Sobral, and Eduardo V. Teixeira.

The development covers all 55 targets extracted from the Lea-annotated LaTeX source. It includes
the structural definitions for uniformly elliptic operators and viscosity solutions, the planar
profile and compactness machinery, the reduction to transition-boundary growth, the main uniform
Lipschitz estimate, and the construction showing that the `√α` term is sharp. Deep analytic inputs
used as interfaces or hypotheses remain explicit in the corresponding Lean statements.

The principal entry points are:

- `MainLipschitzEstimate.lean` — the uniform interior Lipschitz estimate;
- `Reduction.lean` and `NormalizedEstimate.lean` — the main reduction and normalized problem;
- `propSharpnessSqrtAlpha.lean` — sharpness of the square-root dependence.

## Building

The files form the `Lea.Lipschitz2` namespace and are intended to live at
`proofs/Lea/Lipschitz2` in the Lea Lean workspace. From that workspace root, run:

```bash
lake build Lea.Lipschitz2.MainLipschitzEstimate
lake build Lea.Lipschitz2.propSharpnessSqrtAlpha
```

Both entry points compile with the workspace's pinned Lean 4/mathlib toolchain, and the source tree
contains no `sorry` placeholders.

The formalization was produced with [Lea](https://github.com/VIDA-NYU/Lea).
