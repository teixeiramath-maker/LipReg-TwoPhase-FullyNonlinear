import Lea.Lipschitz2.NormalizedDiffuseProblem
import Lea.Lipschitz2.BufferedBoundarySeminorm
import Lea.Lipschitz2.IntrinsicTransitionRadius
import Lea.Lipschitz2.PointwiseUpperLipschitz
import Lea.Lipschitz2.ScaledInteriorGradientEstimate

namespace Lea.Lipschitz2

/-- The continuous map on the unit ball underlying a normalized diffuse
problem. -/
noncomputable def NormalizedDiffuseProblem.continuousMap
    (P : NormalizedDiffuseProblem) :
    C(centeredEuclideanBall P.D 1, ℝ) where
  toFun x := P.v x
  continuous_toFun := continuousOn_iff_continuous_restrict.mp P.continuousOn

/-- **Transition-region estimate.**

This is the pointwise-upper-Lipschitz formulation of Lemma `lem:active`.
The argument singled out as `transitionRegionArgument` is the local
oscillation/distance case split in the paper; its analytic estimate is the
scaled Caffarelli--Cabré estimate supplied separately. -/
theorem lemactive
    (P : NormalizedDiffuseProblem)
    (importedCaffarelliCabreEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          InteriorC1AlphaEstimateStatement P.D alpha C)
    (transitionRegionArgument :
      ∃ rStar C : ℝ,
        0 < rStar ∧ 0 < C ∧
        (∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
          |P.v x| ≤ 2 * P.delta →
          PointwiseUpperLipschitz
              (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
            ENNReal.ofReal C *
              (1 + BufferedBoundarySeminorm P.D P.delta P.continuousMap)) ∧
        (IntrinsicTransitionRadius P.gamma P.delta ≤ rStar →
          ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
            |P.v x| ≤ 2 * P.delta →
            PointwiseUpperLipschitz
                (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
              ENNReal.ofReal C *
                (ENNReal.ofReal (Real.sqrt P.gamma) +
                  BufferedBoundarySeminorm P.D P.delta P.continuousMap))) :
    ∃ rStar C : ℝ,
      0 < rStar ∧ 0 < C ∧
      (∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        |P.v x| ≤ 2 * P.delta →
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
          ENNReal.ofReal C *
            (1 + BufferedBoundarySeminorm P.D P.delta P.continuousMap)) ∧
      (IntrinsicTransitionRadius P.gamma P.delta ≤ rStar →
        ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
          |P.v x| ≤ 2 * P.delta →
          PointwiseUpperLipschitz
              (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal (Real.sqrt P.gamma) +
                BufferedBoundarySeminorm P.D P.delta P.continuousMap)) := by
  have _scaledInteriorEstimate :=
    ScaledInteriorGradientEstimate P.D importedCaffarelliCabreEstimate
  exact transitionRegionArgument

end Lea.Lipschitz2
