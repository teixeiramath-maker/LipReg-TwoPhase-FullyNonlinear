import Lea.Lipschitz2.PlanarTransmissionMap
import Lea.Lipschitz2.lemTransitionIncrementBounds

namespace Lea.Lipschitz2

/-- The planar transmission map is Lipschitz in the normal direction, with
modulus of order `γ / b` at every positive incoming slope `b`. -/
theorem lemTransmissionMapDirectionalEstimate
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
      (b : ℝ), 0 < b →
      |PlanarTransmissionMap P ν γ η b -
          PlanarTransmissionMap P μ γ η b| ≤
        C * (γ : ℝ) / b *
          ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by
  have hbeta_int : 0 ≤ ∫ s in (-1 : ℝ)..1, P.D.beta s := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun s _ ↦ P.beta_nonnegative s
  let C := (2 * Cdir / P.D.lambda ^ 2) *
    ∫ s in (-1 : ℝ)..1, P.D.beta s
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) hCdir) (sq_nonneg P.D.lambda))
      hbeta_int
  refine ⟨C, hC, ?_⟩
  intro μ b hb
  let Jν := PlanarTransitionIncrement P ν γ η
  let Jμ := PlanarTransitionIncrement P μ γ η
  have hboundsν := lemTransitionIncrementBounds P ν γ η Cdir hCdir hdir
  have hboundsμ := lemTransitionIncrementBounds P μ γ η Cdir hCdir hdir
  have hJν : 0 ≤ Jν := by
    have hLambda : 0 < P.D.Lambda := lt_of_lt_of_le P.D.lambda_pos P.D.lambda_le_Lambda
    exact le_trans
      (mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) γ.property.le) hLambda.le)
        hbeta_int)
      hboundsν.1.1
  have hJμ : 0 ≤ Jμ := by
    have hLambda : 0 < P.D.Lambda := lt_of_lt_of_le P.D.lambda_pos P.D.lambda_le_Lambda
    exact le_trans
      (mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) γ.property.le) hLambda.le)
        hbeta_int)
      hboundsμ.1.1
  have hJdir : |Jν - Jμ| ≤ C * (γ : ℝ) *
      ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by
    convert hboundsν.2 μ using 1
    all_goals dsimp [C, Jν, Jμ]
    all_goals ring
  have hA : 0 ≤ b ^ 2 + Jν := by positivity
  have hB : 0 ≤ b ^ 2 + Jμ := by positivity
  have hsν : b ≤ Real.sqrt (b ^ 2 + Jν) := by
    calc
      b = Real.sqrt (b ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
      _ ≤ Real.sqrt (b ^ 2 + Jν) := Real.sqrt_le_sqrt (by linarith)
  have hsμ : b ≤ Real.sqrt (b ^ 2 + Jμ) := by
    calc
      b = Real.sqrt (b ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
      _ ≤ Real.sqrt (b ^ 2 + Jμ) := Real.sqrt_le_sqrt (by linarith)
  have hraw :
      (Real.sqrt (b ^ 2 + Jν) - Real.sqrt (b ^ 2 + Jμ)) *
          (Real.sqrt (b ^ 2 + Jν) + Real.sqrt (b ^ 2 + Jμ)) =
        Jν - Jμ := by
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hrat :
      |Real.sqrt (b ^ 2 + Jν) - Real.sqrt (b ^ 2 + Jμ)| *
          (Real.sqrt (b ^ 2 + Jν) + Real.sqrt (b ^ 2 + Jμ)) =
        |Jν - Jμ| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul, hraw]
  rw [PlanarTransmissionMap, PlanarTransmissionMap]
  change |Real.sqrt (b ^ 2 + Jν) - Real.sqrt (b ^ 2 + Jμ)| ≤ _
  have hden : b ≤ Real.sqrt (b ^ 2 + Jν) + Real.sqrt (b ^ 2 + Jμ) := by
    linarith
  calc
    |Real.sqrt (b ^ 2 + Jν) - Real.sqrt (b ^ 2 + Jμ)| =
        |Jν - Jμ| /
          (Real.sqrt (b ^ 2 + Jν) + Real.sqrt (b ^ 2 + Jμ)) := by
            exact (eq_div_iff (by positivity)).2 hrat
    _ ≤ |Jν - Jμ| / b := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) hb hden
    _ ≤ C * (γ : ℝ) *
          ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ / b := by
      exact div_le_div_of_nonneg_right hJdir hb.le
    _ = C * (γ : ℝ) / b *
          ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by ring

end Lea.Lipschitz2
