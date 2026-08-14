import Lea.Lipschitz2.InteriorC1AlphaEstimate

namespace Lea.Lipschitz2

/-- **Scaled interior gradient estimate.**

The functions `h` and `g` are the translated and naturally scaled solution
and right-hand side on the unit ball.  The hypothesis `centerSlope` records
the standard invariance of the pointwise upper Lipschitz constant under this
translation and scaling.  Thus `oscOverRadius` represents
`osc_{B_r(x₀)} w / r`, while `scaledSourceBound` represents
`r ‖f‖_{L∞(B_r(x₀))}`. -/
theorem ScaledInteriorGradientEstimate
    (D : StructuralDataAndNotation)
    (importedCaffarelliCabreEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          InteriorC1AlphaEstimateStatement D alpha C) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ (F : Sn D.n → ℝ)
        (g h : (Fin D.n → ℝ) → ℝ)
        (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
        (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n)
        (gradient : (Fin D.n → ℝ) → (Fin D.n → ℝ))
        (IsGradient : ((Fin D.n → ℝ) → ℝ) →
          ((Fin D.n → ℝ) → (Fin D.n → ℝ)) → Prop)
        (Ω : Set (Fin D.n → ℝ)) (w : (Fin D.n → ℝ) → ℝ)
        (x₀ y z : Fin D.n → ℝ) (oscOverRadius scaledSourceBound : ℝ),
        Uniformellipticity D F →
        ContinuousOn h (centeredEuclideanBall D 1) →
        ViscositySolutionOn (centeredEuclideanBall D 1) F g h IsTest hessian →
        IsGradient h gradient →
        0 ≤ oscOverRadius →
        0 ≤ scaledSourceBound →
        (∀ x ∈ centeredEuclideanBall D 1, |h x| ≤ oscOverRadius) →
        (∀ x ∈ centeredEuclideanBall D 1, |g x| ≤ scaledSourceBound) →
        y ∈ centeredEuclideanBall D (1 / 2 : ℝ) →
        z ∈ centeredEuclideanBall D (1 / 2 : ℝ) →
        y ≠ z →
        PointwiseUpperLipschitz Ω w x₀ ≤
          PointwiseUpperLipschitz (centeredEuclideanBall D 1) h 0 →
        PointwiseUpperLipschitz Ω w x₀ ≤
          ENNReal.ofReal (C * (oscOverRadius + scaledSourceBound)) := by
  obtain ⟨alpha, C, hα, hα1, hC, hEstimate⟩ :=
    InteriorC1AlphaEstimate D importedCaffarelliCabreEstimate
  refine ⟨alpha, C, hα, hα1, hC, ?_⟩
  intro F g h IsTest hessian gradient IsGradient Ω w x₀ y z
    oscOverRadius scaledSourceBound hF hcont hsol hgrad hosc hsource
    hh hg hy hz hyz centerSlope
  have estimate :=
    hEstimate F g h IsTest hessian gradient IsGradient hF hcont hsol hgrad
      oscOverRadius scaledSourceBound hosc hsource hh hg
  have atCenter := estimate.1 0 (by simp [centeredEuclideanBall, euclideanBall])
    y hy z hz hyz
  apply centerSlope.trans
  exact (by
    calc
      PointwiseUpperLipschitz (centeredEuclideanBall D 1) h 0 ≤
          PointwiseUpperLipschitz (centeredEuclideanBall D 1) h 0 +
            ENNReal.ofReal
              (‖gradient y - gradient z‖ / Real.rpow (dist y z) alpha) := by simp
      _ ≤ ENNReal.ofReal (C * (oscOverRadius + scaledSourceBound)) := atCenter)

end Lea.Lipschitz2
