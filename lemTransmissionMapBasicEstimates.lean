import Lea.Lipschitz2.PlanarTransmissionMap
import Lea.Lipschitz2.lemTransitionIncrementBounds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Lea.Lipschitz2

/-- The planar transmission map has the stated first two derivatives and
approaches the identity quantitatively at positive slopes. -/
theorem lemTransmissionMapBasicEstimates
    (P : SingularPerturbationProblemData)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (γ η : {x : ℝ // 0 < x})
    (Cdir : ℝ) (hCdir : 0 ≤ Cdir)
    (hdir : ∀
      (ξ ζ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (t : {t : ℝ // 0 ≤ t}),
      |PlanarRankOneOperator P.D P.F ξ t - PlanarRankOneOperator P.D P.F ζ t| ≤
        Cdir * (t : ℝ) * ‖(ξ : Fin P.D.n → ℝ) - (ζ : Fin P.D.n → ℝ)‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b →
      let J := PlanarTransitionIncrement P ν γ η
      let G := PlanarTransmissionMap P ν γ η
      HasDerivAt G (b / Real.sqrt (b ^ 2 + J)) b ∧
      HasDerivAt (fun x : ℝ ↦ x / Real.sqrt (x ^ 2 + J))
        (J / (Real.sqrt (b ^ 2 + J)) ^ 3) b ∧
      |G b - b| ≤ C * (γ : ℝ) / b ∧
      |b / Real.sqrt (b ^ 2 + J) - 1| ≤ C * (γ : ℝ) / b ^ 2 ∧
      |J / (Real.sqrt (b ^ 2 + J)) ^ 3| ≤ C * (γ : ℝ) / b ^ 3 := by
  have hbint : 0 ≤ ∫ s in (-1 : ℝ)..1, P.D.beta s := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun s _ ↦ P.beta_nonnegative s
  let C := (2 / P.D.lambda) * ∫ s in (-1 : ℝ)..1, P.D.beta s
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (by norm_num) P.D.lambda_pos.le) hbint
  refine ⟨C, hC, ?_⟩
  intro b hb
  dsimp only
  let J := PlanarTransitionIncrement P ν γ η
  have hJbounds := (lemTransitionIncrementBounds P ν γ η Cdir hCdir hdir).1
  have hJ0 : 0 ≤ J := by
    have hLambda : 0 < P.D.Lambda := lt_of_lt_of_le P.D.lambda_pos P.D.lambda_le_Lambda
    have hcoef : 0 ≤ 2 * (γ : ℝ) / P.D.Lambda :=
      div_nonneg (mul_nonneg (by norm_num) γ.property.le) hLambda.le
    exact le_trans (mul_nonneg hcoef hbint) hJbounds.1
  have hJupper : J ≤ C * (γ : ℝ) := by
    calc
      J ≤ (2 * (γ : ℝ) / P.D.lambda) *
          ∫ s in (-1 : ℝ)..1, P.D.beta s := hJbounds.2
      _ = C * (γ : ℝ) := by dsimp [C]; ring
  have hpos : 0 < b ^ 2 + J := by positivity
  have hsqrt : 0 < Real.sqrt (b ^ 2 + J) := Real.sqrt_pos.2 hpos
  have hbsqrt : b ≤ Real.sqrt (b ^ 2 + J) := by
    nlinarith [Real.sq_sqrt hpos.le]
  have hp : HasDerivAt (fun x : ℝ ↦ x ^ 2 + J) (2 * b) b := by
    simpa [mul_comm] using (hasDerivAt_pow 2 b).add_const J
  have hs : HasDerivAt (fun x : ℝ ↦ Real.sqrt (x ^ 2 + J))
      (b / Real.sqrt (b ^ 2 + J)) b := by
    convert HasDerivAt.sqrt hp hpos.ne' using 1
    ring
  have hderiv1 : HasDerivAt (PlanarTransmissionMap P ν γ η)
      (b / Real.sqrt (b ^ 2 + J)) b := by
    simpa only [PlanarTransmissionMap, J] using hs
  have hderiv2 : HasDerivAt (fun x : ℝ ↦ x / Real.sqrt (x ^ 2 + J))
      (J / (Real.sqrt (b ^ 2 + J)) ^ 3) b := by
    convert (hasDerivAt_id b).div hs hsqrt.ne' using 1
    simp only [id_eq]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le]
  have hsq : (Real.sqrt (b ^ 2 + J)) ^ 2 = b ^ 2 + J :=
    Real.sq_sqrt hpos.le
  have hdiff0 : 0 ≤ Real.sqrt (b ^ 2 + J) - b := sub_nonneg.mpr hbsqrt
  have hrat : (Real.sqrt (b ^ 2 + J) - b) *
      (Real.sqrt (b ^ 2 + J) + b) = J := by
    nlinarith
  have hG : |PlanarTransmissionMap P ν γ η b - b| ≤ C * (γ : ℝ) / b := by
    rw [PlanarTransmissionMap, abs_of_nonneg hdiff0]
    apply (le_div_iff₀ hb).2
    calc
      (Real.sqrt (b ^ 2 + J) - b) * b ≤
          (Real.sqrt (b ^ 2 + J) - b) *
            (Real.sqrt (b ^ 2 + J) + b) := by
              apply mul_le_mul_of_nonneg_left _ hdiff0
              nlinarith [hsqrt.le]
      _ = J := hrat
      _ ≤ C * (γ : ℝ) := hJupper
  have hG' : |b / Real.sqrt (b ^ 2 + J) - 1| ≤
      C * (γ : ℝ) / b ^ 2 := by
    have hnonpos : b / Real.sqrt (b ^ 2 + J) - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hsqrt]
      exact hbsqrt
    rw [abs_of_nonpos hnonpos]
    apply (le_div_iff₀ (sq_pos_of_pos hb)).2
    have hratio : b ^ 2 / Real.sqrt (b ^ 2 + J) ≤
        Real.sqrt (b ^ 2 + J) + b := by
      apply (div_le_iff₀ hsqrt).2
      nlinarith [hsq, mul_nonneg hsqrt.le hb.le]
    calc
      -(b / Real.sqrt (b ^ 2 + J) - 1) * b ^ 2 =
          (Real.sqrt (b ^ 2 + J) - b) *
            (b ^ 2 / Real.sqrt (b ^ 2 + J)) := by
              field_simp
              ring
      _ ≤ (Real.sqrt (b ^ 2 + J) - b) *
            (Real.sqrt (b ^ 2 + J) + b) :=
        mul_le_mul_of_nonneg_left hratio hdiff0
      _ = J := hrat
      _ ≤ C * (γ : ℝ) := hJupper
  have hG'' : |J / (Real.sqrt (b ^ 2 + J)) ^ 3| ≤
      C * (γ : ℝ) / b ^ 3 := by
    rw [abs_of_nonneg (div_nonneg hJ0 (by positivity))]
    apply (le_div_iff₀ (pow_pos hb 3)).2
    have hpow : b ^ 3 ≤ (Real.sqrt (b ^ 2 + J)) ^ 3 := by
      exact pow_le_pow_left₀ hb.le hbsqrt 3
    have hratio3 : b ^ 3 / (Real.sqrt (b ^ 2 + J)) ^ 3 ≤ 1 := by
      exact (div_le_one (by positivity)).2 hpow
    calc
      J / (Real.sqrt (b ^ 2 + J)) ^ 3 * b ^ 3 =
          J * (b ^ 3 / (Real.sqrt (b ^ 2 + J)) ^ 3) := by ring
      _ ≤ J * 1 := mul_le_mul_of_nonneg_left hratio3 hJ0
      _ = J := by ring
      _ ≤ C * (γ : ℝ) := hJupper
  exact ⟨hderiv1, hderiv2, hG, hG', hG''⟩

end Lea.Lipschitz2
