import Lea.Lipschitz2.SingularPerturbationProblemData
import Lea.Lipschitz2.lemPlanarOperatorBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Lea.Lipschitz2

/-- The inverse of the planar rank-one restriction `Q_{F,ν}` on the
nonnegative real ray. -/
noncomputable def planarRankOneOperatorInverse
    (D : StructuralDataAndNotation) (F : Sn D.n → ℝ)
    (ν : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (hF : Uniformellipticity D F) (hF0 : F 0 = 0) :
    {y : ℝ // 0 ≤ y} → {t : ℝ // 0 ≤ t} :=
  Classical.choose (lemPlanarOperatorBounds D F ν hF hF0).2.2

/-- The planar transition increment
`J_{F,ν}(γ,η) = 2η ∫_{-1}^1 Q_{F,ν}⁻¹ ((γ/η) β(s)) ds` for positive
strength `γ` and thickness `η`. -/
noncomputable def PlanarTransitionIncrement
    (P : SingularPerturbationProblemData)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (γ η : {x : ℝ // 0 < x}) : ℝ :=
  2 * (η : ℝ) * ∫ s in (-1 : ℝ)..1,
    (planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic P.normalized
      ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
        mul_nonneg (div_nonneg γ.property.le η.property.le)
          (P.beta_nonnegative s)⟩ : ℝ)

end Lea.Lipschitz2
