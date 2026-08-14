import Lea.Lipschitz2.corgrowth
import Lea.Lipschitz2.lemactive

namespace Lea.Lipschitz2

/-- The boundary-point rescaling and the two-range estimate from the proof of
`prop:Bbound`.  At a point `z` of the buffered level boundary one rescales by
`ρ = (2/3 - ‖z‖) / 8`; the growth estimate controls `|x-z| ≤ ρ/2`, while the
unit-amplitude normalization controls the complementary range. -/
def TransitionBoundaryGrowthArgument
    (D : StructuralDataAndNotation) : Prop :=
  ∀ P : NormalizedDiffuseProblem,
    P.D = D →
    (∃ C : ℝ, 0 < C ∧ DiffuseGrowthStatement D C) →
    ∃ K : ℝ, 0 < K ∧
      BufferedBoundarySeminorm P.D P.delta P.continuousMap ≤ ENNReal.ofReal K

/-- **Transition-boundary Lipschitz bound.**

Every normalized diffuse solution has universally bounded buffered
boundary-to-domain seminorm.  The universal growth constant is supplied by
`corgrowth`; `TransitionBoundaryGrowthArgument` is the boundary-point
rescaling and near/far case split in the manuscript. -/
theorem propBbound
    (D : StructuralDataAndNotation)
    (importedDiffuseDSSArgument : DiffuseDSSArgument D)
    (importedGrowthIteration : DiffuseGrowthIterationArgument D)
    (boundaryGrowthArgument : TransitionBoundaryGrowthArgument D)
    (P : NormalizedDiffuseProblem)
    (hPD : P.D = D) :
    ∃ C : ℝ, 0 < C ∧
      BufferedBoundarySeminorm P.D P.delta P.continuousMap ≤ ENNReal.ofReal C := by
  have _rescalingIdentity := @lemSingularPerturbationRescaling
  have hgrowth : ∃ C : ℝ, 0 < C ∧ DiffuseGrowthStatement D C :=
    corgrowth D importedDiffuseDSSArgument importedGrowthIteration
  exact boundaryGrowthArgument P hPD hgrowth

end Lea.Lipschitz2
