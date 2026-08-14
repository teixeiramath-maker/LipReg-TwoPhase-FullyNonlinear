import Lea.Lipschitz2.propdiffuseDSS

namespace Lea.Lipschitz2

/-- The scale-invariant pointwise linear-growth estimate for shifted diffuse
solutions which vanish at the origin.  Quantifying `C` before the problem
records that it is independent of the layer thickness and shift. -/
def DiffuseGrowthStatement
    (D : StructuralDataAndNotation) (C : ℝ) : Prop :=
  ∀ P : ShiftedDiffuseProblem,
    P.D = D →
    P.domain = centeredEuclideanBall P.D 2 →
    P.w 0 = 0 →
    0 < P.gamma → P.gamma ≤ 1 →
    ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
      |P.w x| ≤
        C * (supNormOn (centeredEuclideanBall P.D 1) P.w +
          Real.sqrt P.gamma) * ‖x‖

/-- The dyadic iteration used after the diffuse decay-versus-Lipschitz
alternative.  In the decay branch it iterates
`a_{k+1} ≤ a_k / 2 + C √γ`; at the first Lipschitz branch its interior bound
controls every subsequent radius. -/
def DiffuseGrowthIterationArgument (D : StructuralDataAndNotation) : Prop :=
  ∀ theta C : ℝ,
    0 < theta → theta < 1 / 4 → 0 < C →
    DiffuseDSSStatement D theta C →
    ∃ K : ℝ, 0 < K ∧ DiffuseGrowthStatement D K

/-- **Growth from a transition point.**

A shifted diffuse solution in `B₂` which vanishes at the origin and has
`0 < γ ≤ 1` grows at most linearly in `B_{1/2}`, with coefficient bounded by
a universal multiple of its `L∞(B₁)` size plus `√γ`. -/
theorem corgrowth
    (D : StructuralDataAndNotation)
    (importedDiffuseDSSArgument : DiffuseDSSArgument D)
    (importedGrowthIteration : DiffuseGrowthIterationArgument D) :
    ∃ C : ℝ, 0 < C ∧ DiffuseGrowthStatement D C := by
  obtain ⟨theta, C, htheta, hthetaQuarter, hC, hDSS⟩ :=
    propdiffuseDSS D importedDiffuseDSSArgument
  exact importedGrowthIteration theta C htheta hthetaQuarter hC hDSS

end Lea.Lipschitz2
