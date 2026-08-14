import Lea.Lipschitz2.correduction
import Lea.Lipschitz2.propBbound

namespace Lea.Lipschitz2

/-- **Normalized Lipschitz estimate.**

A normalized diffuse solution has a universal pointwise upper-Lipschitz bound
on the half ball.  The analytic inputs are exactly the local reduction and the
transition-boundary growth argument appearing in the manuscript. -/
theorem NormalizedEstimate
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
                  BufferedBoundarySeminorm P.D P.delta P.continuousMap)))
    (homogeneousPhaseArgument :
      ∃ C : ℝ, 0 < C ∧
        ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
          2 * P.delta < |P.v x| →
          PointwiseUpperLipschitz
              (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
            ENNReal.ofReal C *
              (1 + BufferedBoundarySeminorm P.D P.delta
                P.continuousMapForPhases))
    (importedDiffuseDSSArgument : DiffuseDSSArgument P.D)
    (importedGrowthIteration : DiffuseGrowthIterationArgument P.D)
    (boundaryGrowthArgument : TransitionBoundaryGrowthArgument P.D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
          ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁, hreduction⟩ :=
    correduction P importedCaffarelliCabreEstimate transitionRegionArgument
      homogeneousPhaseArgument
  obtain ⟨C₂, hC₂, hboundary⟩ :=
    propBbound P.D importedDiffuseDSSArgument importedGrowthIteration
      boundaryGrowthArgument P rfl
  refine ⟨C₁ * (1 + C₂), mul_pos hC₁ (by linarith), ?_⟩
  intro x hx
  calc
    PointwiseUpperLipschitz
          (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
        ENNReal.ofReal C₁ *
          (1 + BufferedBoundarySeminorm P.D P.delta P.continuousMap) :=
      hreduction x hx
    _ ≤ ENNReal.ofReal C₁ * (1 + ENNReal.ofReal C₂) := by
      gcongr
    _ = ENNReal.ofReal (C₁ * (1 + C₂)) := by
      rw [ENNReal.ofReal_mul hC₁.le]
      congr 1
      rw [add_comm (1 : ENNReal), add_comm (1 : ℝ)]
      rw [ENNReal.ofReal_add hC₂.le]
      all_goals norm_num

end Lea.Lipschitz2
