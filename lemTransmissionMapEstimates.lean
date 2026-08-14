import Lea.Lipschitz2.lemTransmissionMapBasicEstimates
import Lea.Lipschitz2.lemTransmissionMapDirectionalEstimate

namespace Lea.Lipschitz2

/-- At slopes `b ≥ K √γ`, the planar transmission map is quadratically close
in `K⁻¹` to the identity, including its first two slope derivatives and its
dependence on the direction. -/
theorem lemTransmissionMapEstimates
    (P : SingularPerturbationProblemData)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (γ η : {x : ℝ // 0 < x})
    (Cdir : ℝ) (hCdir : 0 ≤ Cdir)
    (hdir : ∀
      (ξ ζ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (t : {t : ℝ // 0 ≤ t}),
      |PlanarRankOneOperator P.D P.F ξ t - PlanarRankOneOperator P.D P.F ζ t| ≤
        Cdir * (t : ℝ) * ‖(ξ : Fin P.D.n → ℝ) - (ζ : Fin P.D.n → ℝ)‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (μ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (K b : ℝ), 0 < K → 0 < b → K * Real.sqrt (γ : ℝ) ≤ b →
      let J := PlanarTransitionIncrement P ν γ η
      let G := PlanarTransmissionMap P ν γ η
      |G b - b| / b +
          |b / Real.sqrt (b ^ 2 + J) - 1| +
          b * |J / (Real.sqrt (b ^ 2 + J)) ^ 3| ≤ C / K ^ 2 ∧
      |PlanarTransmissionMap P ν γ η b -
          PlanarTransmissionMap P μ γ η b| ≤
        C / K ^ 2 * b *
          ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by
  rcases lemTransmissionMapBasicEstimates P ν γ η Cdir hCdir hdir with
    ⟨C₁, hC₁, hbasic⟩
  rcases lemTransmissionMapDirectionalEstimate P ν γ η Cdir hCdir hdir with
    ⟨C₂, hC₂, hdirectional⟩
  refine ⟨3 * C₁ + C₂, by positivity, ?_⟩
  intro μ K b hK hb hlarge
  dsimp only
  let J := PlanarTransitionIncrement P ν γ η
  have hbnd := hbasic b hb
  have hdirb := hdirectional μ b hb
  dsimp only at hbnd
  have hsqrt_sq : (Real.sqrt (γ : ℝ)) ^ 2 = (γ : ℝ) := by
    exact Real.sq_sqrt γ.property.le
  have hsquare : (K * Real.sqrt (γ : ℝ)) ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg hK.le (Real.sqrt_nonneg (γ : ℝ))]
  have hscale : (γ : ℝ) / b ^ 2 ≤ 1 / K ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hb) (sq_pos_of_pos hK)).2
    nlinarith [hsquare]
  constructor
  · have hfirst : |PlanarTransmissionMap P ν γ η b - b| / b ≤
        C₁ * (γ : ℝ) / b ^ 2 := by
      calc
        |PlanarTransmissionMap P ν γ η b - b| / b ≤
            (C₁ * (γ : ℝ) / b) / b :=
          div_le_div_of_nonneg_right hbnd.2.2.1 hb.le
        _ = C₁ * (γ : ℝ) / b ^ 2 := by ring
    have hthird : b * |J / (Real.sqrt (b ^ 2 + J)) ^ 3| ≤
        C₁ * (γ : ℝ) / b ^ 2 := by
      calc
        b * |J / (Real.sqrt (b ^ 2 + J)) ^ 3| ≤
            b * (C₁ * (γ : ℝ) / b ^ 3) :=
          mul_le_mul_of_nonneg_left hbnd.2.2.2.2 hb.le
        _ = C₁ * (γ : ℝ) / b ^ 2 := by field_simp
    calc
      |PlanarTransmissionMap P ν γ η b - b| / b +
            |b / Real.sqrt (b ^ 2 + J) - 1| +
            b * |J / (Real.sqrt (b ^ 2 + J)) ^ 3| ≤
          3 * (C₁ * (γ : ℝ) / b ^ 2) := by
            linarith [hbnd.2.2.2.1]
      _ = (3 * C₁) * ((γ : ℝ) / b ^ 2) := by ring
      _ ≤ (3 * C₁) * (1 / K ^ 2) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hC₁)
      _ ≤ (3 * C₁ + C₂) / K ^ 2 := by
        have hconst : 3 * C₁ ≤ 3 * C₁ + C₂ := by linarith
        rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
        exact mul_le_mul_of_nonneg_right hconst (inv_nonneg.mpr (sq_nonneg K))
  · calc
      |PlanarTransmissionMap P ν γ η b -
          PlanarTransmissionMap P μ γ η b| ≤
          C₂ * (γ : ℝ) / b *
            ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := hdirb
      _ ≤ C₂ * (1 / K ^ 2) * b *
            ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by
          have hbscale : (γ : ℝ) / b ≤ (1 / K ^ 2) * b := by
            calc
              (γ : ℝ) / b = ((γ : ℝ) / b ^ 2) * b := by field_simp
              _ ≤ (1 / K ^ 2) * b :=
                mul_le_mul_of_nonneg_right hscale hb.le
          have hcscale : C₂ * ((γ : ℝ) / b) ≤
              C₂ * ((1 / K ^ 2) * b) :=
            mul_le_mul_of_nonneg_left hbscale hC₂
          exact mul_le_mul_of_nonneg_right
            (by simpa [div_eq_mul_inv, mul_assoc] using hcscale) (norm_nonneg _)
      _ ≤ (3 * C₁ + C₂) / K ^ 2 * b *
            ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by
          have hcoef : C₂ * (1 / K ^ 2) ≤
              (3 * C₁ + C₂) / K ^ 2 := by
            have hconst : C₂ ≤ 3 * C₁ + C₂ := by linarith
            rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
            exact mul_le_mul_of_nonneg_right hconst
              (inv_nonneg.mpr (sq_nonneg K))
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef hb.le) (norm_nonneg _)

end Lea.Lipschitz2
