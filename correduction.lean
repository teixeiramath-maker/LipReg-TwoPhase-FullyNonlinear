import Lea.Lipschitz2.lemactive
import Lea.Lipschitz2.lemphases

namespace Lea.Lipschitz2

/-- **Reduction to transition-boundary growth.**

Every normalized diffuse solution has its pointwise upper Lipschitz constant
on `B_{1/2}` bounded by a universal multiple of `1 + 𝓑(v)`. This is the
pointwise-upper-Lipschitz interpretation of the displayed gradient estimate
in Corollary `cor:reduction`. -/
theorem correduction
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
                P.continuousMapForPhases)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) P.v x ≤
          ENNReal.ofReal C *
            (1 + BufferedBoundarySeminorm P.D P.delta P.continuousMap) := by
  obtain ⟨rStar, C₁, hrStar, hC₁, hactive, hmicroscopic⟩ :=
    lemactive P importedCaffarelliCabreEstimate transitionRegionArgument
  obtain ⟨C₂, hC₂, hphases⟩ :=
    lemphases P importedCaffarelliCabreEstimate homogeneousPhaseArgument
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro x hx
  by_cases htransition : |P.v x| ≤ 2 * P.delta
  · exact (hactive x hx htransition).trans (by
      gcongr
      linarith)
  · have hphase : 2 * P.delta < |P.v x| := lt_of_not_ge htransition
    have h := hphases x hx hphase
    have hmaps : P.continuousMapForPhases = P.continuousMap := by
      ext y
      rfl
    rw [hmaps] at h
    exact h.trans (by
      gcongr
      linarith)

end Lea.Lipschitz2
