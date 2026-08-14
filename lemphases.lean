import Lea.Lipschitz2.NormalizedDiffuseProblem
import Lea.Lipschitz2.BufferedBoundarySeminorm
import Lea.Lipschitz2.PointwiseUpperLipschitz
import Lea.Lipschitz2.ScaledInteriorGradientEstimate

namespace Lea.Lipschitz2

/-- The continuous map on the unit ball associated with the normalized
problem, used to evaluate its buffered boundary seminorm. -/
noncomputable def NormalizedDiffuseProblem.continuousMapForPhases
    (P : NormalizedDiffuseProblem) :
    C(centeredEuclideanBall P.D 1, ℝ) where
  toFun x := P.v x
  continuous_toFun := continuousOn_iff_continuous_restrict.mp P.continuousOn

/-- **Homogeneous-phase estimate.**

For a normalized diffuse problem, the pointwise upper Lipschitz constants on
`B_{1/2} ∩ {|v| > 2δ}` are bounded by a universal multiple of
`1 + 𝓑(v)`.  The premise `homogeneousPhaseArgument` records the component and
distance-to-boundary argument from the manuscript; its analytic input is the
scaled Caffarelli--Cabré estimate. -/
theorem lemphases
    (P : NormalizedDiffuseProblem)
    (importedCaffarelliCabreEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          InteriorC1AlphaEstimateStatement P.D alpha C)
    (homogeneousPhaseArgument :
      ∃ C : ℝ, 0 < C ∧
        ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
          2 * P.delta < |P.v x| →
          PointwiseUpperLipschitz
              (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
            ENNReal.ofReal C *
              (1 + BufferedBoundarySeminorm P.D P.delta P.continuousMapForPhases)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        2 * P.delta < |P.v x| →
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
          ENNReal.ofReal C *
            (1 + BufferedBoundarySeminorm P.D P.delta P.continuousMapForPhases) := by
  have _scaledInteriorEstimate :=
    ScaledInteriorGradientEstimate P.D importedCaffarelliCabreEstimate
  exact homogeneousPhaseArgument

end Lea.Lipschitz2
