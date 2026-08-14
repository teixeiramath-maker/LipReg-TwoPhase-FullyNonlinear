import Lea.Lipschitz2.PlanarTransitionIncrement
import Lea.Lipschitz2.lemPlanarOperatorDirectionalBounds

namespace Lea.Lipschitz2

#check IntervalIntegrable.mono
#check Monotone.measurable

/-- The planar transition increment is comparable to the reaction strength,
uniformly in the layer thickness and direction, and is Lipschitz in the
normal direction. -/
theorem lemTransitionIncrementBounds
    (P : SingularPerturbationProblemData)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (γ η : {x : ℝ // 0 < x})
    (C : ℝ) (hC : 0 ≤ C)
    (hdir : ∀
      (ξ ζ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (t : {t : ℝ // 0 ≤ t}),
      |PlanarRankOneOperator P.D P.F ξ t - PlanarRankOneOperator P.D P.F ζ t| ≤
        C * (t : ℝ) * ‖(ξ : Fin P.D.n → ℝ) - (ζ : Fin P.D.n → ℝ)‖) :
    ((2 * (γ : ℝ) / P.D.Lambda) * ∫ s in (-1 : ℝ)..1, P.D.beta s ≤
        PlanarTransitionIncrement P ν γ η ∧
      PlanarTransitionIncrement P ν γ η ≤
        (2 * (γ : ℝ) / P.D.lambda) * ∫ s in (-1 : ℝ)..1, P.D.beta s) ∧
      ∀ μ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1},
        |PlanarTransitionIncrement P ν γ η -
            PlanarTransitionIncrement P μ γ η| ≤
          (2 * C / P.D.lambda ^ 2) * (γ : ℝ) *
            (∫ s in (-1 : ℝ)..1, P.D.beta s) *
              ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖ := by
  have hbeta_int : IntervalIntegrable P.D.beta MeasureTheory.volume (-1 : ℝ) 1 := by
    exact P.beta_continuous.intervalIntegrable (-1) 1
  have hinv_bounds (ξ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (y : {y : ℝ // 0 ≤ y}) :
      (y : ℝ) / P.D.Lambda ≤
          (planarRankOneOperatorInverse P.D P.F ξ P.uniformlyElliptic P.normalized y : ℝ) ∧
        (planarRankOneOperatorInverse P.D P.F ξ P.uniformlyElliptic P.normalized y : ℝ) ≤
          (y : ℝ) / P.D.lambda := by
    exact (Classical.choose_spec
      (lemPlanarOperatorBounds P.D P.F ξ P.uniformlyElliptic P.normalized).2.2).2 y
  have hpoint_lower : ∀ s ∈ Set.uIcc (-1 : ℝ) 1,
      ((γ : ℝ) / (η : ℝ) * P.D.beta s) / P.D.Lambda ≤
        (planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic P.normalized
          ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
            mul_nonneg (div_nonneg γ.property.le η.property.le)
              (P.beta_nonnegative s)⟩ : ℝ) := by
    intro s hs
    exact (hinv_bounds ν ⟨_, mul_nonneg
      (div_nonneg γ.property.le η.property.le) (P.beta_nonnegative s)⟩).1
  have hpoint_upper : ∀ s ∈ Set.uIcc (-1 : ℝ) 1,
      (planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic P.normalized
          ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
            mul_nonneg (div_nonneg γ.property.le η.property.le)
              (P.beta_nonnegative s)⟩ : ℝ) ≤
        ((γ : ℝ) / (η : ℝ) * P.D.beta s) / P.D.lambda := by
    intro s hs
    exact (hinv_bounds ν ⟨_, mul_nonneg
      (div_nonneg γ.property.le η.property.le) (P.beta_nonnegative s)⟩).2
  have hinv_eq (ξ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (y : {y : ℝ // 0 ≤ y}) :
      PlanarRankOneOperator P.D P.F ξ
          (planarRankOneOperatorInverse P.D P.F ξ P.uniformlyElliptic P.normalized y) =
        (y : ℝ) := by
    exact (Classical.choose_spec
      (lemPlanarOperatorBounds P.D P.F ξ P.uniformlyElliptic P.normalized).2.2).1 y
  have hinv_mono (ξ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1}) :
      Monotone (planarRankOneOperatorInverse P.D P.F ξ
        P.uniformlyElliptic P.normalized) := by
    intro y z hyz
    have hm := (lemPlanarOperatorBounds P.D P.F ξ
      P.uniformlyElliptic P.normalized).1
    exact hm.le_iff_le.mp (by simpa [hinv_eq] using hyz)
  let invR (ξ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1}) (y : ℝ) : ℝ :=
    if hy : 0 ≤ y then
      (planarRankOneOperatorInverse P.D P.F ξ P.uniformlyElliptic P.normalized
        ⟨y, hy⟩ : ℝ)
    else 0
  have hinvR_mono (ξ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1}) :
      Monotone (invR ξ) := by
    intro a b hab
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := le_trans ha hab
      simp only [invR, dif_pos ha, dif_pos hb]
      exact Subtype.coe_le_coe.mpr (hinv_mono ξ (by exact hab))
    · by_cases hb : 0 ≤ b
      · simp only [invR, dif_neg ha, dif_pos hb]
        exact (planarRankOneOperatorInverse P.D P.F ξ
          P.uniformlyElliptic P.normalized ⟨b, hb⟩).property
      · simp only [invR, dif_neg ha, dif_neg hb]
        exact le_rfl
  have htarget_int (ξ : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1}) :
      IntervalIntegrable (fun s : ℝ ↦
        (planarRankOneOperatorInverse P.D P.F ξ P.uniformlyElliptic P.normalized
          ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
            mul_nonneg (div_nonneg γ.property.le η.property.le)
              (P.beta_nonnegative s)⟩ : ℝ)) MeasureTheory.volume (-1) 1 := by
    refine IntervalIntegrable.mono_fun'
      (g := fun s : ℝ ↦ (γ : ℝ) / (η : ℝ) / P.D.lambda * P.D.beta s)
      (hbeta_int.const_mul ((γ : ℝ) / (η : ℝ) / P.D.lambda)) ?_ ?_
    · have harg : Measurable (fun s : ℝ ↦
          (γ : ℝ) / (η : ℝ) * P.D.beta s) := by
        exact (continuous_const.mul P.beta_continuous).measurable
      have hm : Measurable (fun s : ℝ ↦ invR ξ
          ((γ : ℝ) / (η : ℝ) * P.D.beta s)) :=
        (hinvR_mono ξ).measurable.comp harg
      refine hm.aestronglyMeasurable.congr ?_
      filter_upwards with s
      simp only [invR, dif_pos (mul_nonneg
        (div_nonneg γ.property.le η.property.le) (P.beta_nonnegative s))]
    · filter_upwards with s
      simp only [Real.norm_eq_abs]
      have hnonneg := (planarRankOneOperatorInverse P.D P.F ξ
        P.uniformlyElliptic P.normalized
          ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
            mul_nonneg (div_nonneg γ.property.le η.property.le)
              (P.beta_nonnegative s)⟩).property
      rw [abs_of_nonneg hnonneg]
      convert (hinv_bounds ξ ⟨_, mul_nonneg
        (div_nonneg γ.property.le η.property.le) (P.beta_nonnegative s)⟩).2 using 1
      ring
  have hlower :
      (2 * (γ : ℝ) / P.D.Lambda) * ∫ s in (-1 : ℝ)..1, P.D.beta s ≤
        PlanarTransitionIncrement P ν γ η := by
    have hi := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      (hbeta_int.const_mul ((γ : ℝ) / (η : ℝ) / P.D.Lambda))
      (htarget_int ν) (by
        intro s hs
        convert hpoint_lower s (by simpa [Set.uIcc] using hs) using 1; ring)
    rw [PlanarTransitionIncrement]
    calc
      (2 * (γ : ℝ) / P.D.Lambda) * ∫ s in (-1 : ℝ)..1, P.D.beta s =
          2 * (η : ℝ) * ∫ s in (-1 : ℝ)..1,
            ((γ : ℝ) / (η : ℝ) / P.D.Lambda) * P.D.beta s := by
              rw [intervalIntegral.integral_const_mul]
              field_simp [ne_of_gt η.property]
      _ ≤ 2 * (η : ℝ) * ∫ s in (-1 : ℝ)..1,
          (planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic P.normalized
            ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
              mul_nonneg (div_nonneg γ.property.le η.property.le)
                (P.beta_nonnegative s)⟩ : ℝ) :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num) η.property.le)
  have hupper :
      PlanarTransitionIncrement P ν γ η ≤
        (2 * (γ : ℝ) / P.D.lambda) * ∫ s in (-1 : ℝ)..1, P.D.beta s := by
    have hi := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      (htarget_int ν)
      (hbeta_int.const_mul ((γ : ℝ) / (η : ℝ) / P.D.lambda)) (by
        intro s hs
        convert hpoint_upper s (by simpa [Set.uIcc] using hs) using 1; ring)
    rw [PlanarTransitionIncrement]
    calc
      2 * (η : ℝ) * ∫ s in (-1 : ℝ)..1,
          (planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic P.normalized
            ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
              mul_nonneg (div_nonneg γ.property.le η.property.le)
                (P.beta_nonnegative s)⟩ : ℝ) ≤
          2 * (η : ℝ) * ∫ s in (-1 : ℝ)..1,
            ((γ : ℝ) / (η : ℝ) / P.D.lambda) * P.D.beta s :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num) η.property.le)
      _ = (2 * (γ : ℝ) / P.D.lambda) *
          ∫ s in (-1 : ℝ)..1, P.D.beta s := by
            rw [intervalIntegral.integral_const_mul]
            field_simp [ne_of_gt η.property]
  refine ⟨⟨hlower, hupper⟩, ?_⟩
  intro μ
  let d := ‖(ν : Fin P.D.n → ℝ) - (μ : Fin P.D.n → ℝ)‖
  let K := C / P.D.lambda ^ 2
  have hchosen_dir (y : {y : ℝ // 0 ≤ y}) :
      |(planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic
            P.normalized y : ℝ) -
          (planarRankOneOperatorInverse P.D P.F μ P.uniformlyElliptic
            P.normalized y : ℝ)| ≤ K * (y : ℝ) * d := by
    obtain ⟨invν, invμ, hνeq, hμeq, hbound⟩ :=
      (lemPlanarOperatorDirectionalBounds P.D P.F P.uniformlyElliptic
        P.normalized C hC hdir).2 ν μ
    have hν (z : {z : ℝ // 0 ≤ z}) :
        planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic
            P.normalized z = invν z := by
      apply (lemPlanarOperatorBounds P.D P.F ν P.uniformlyElliptic
        P.normalized).1.injective
      rw [hinv_eq, hνeq]
    have hμ (z : {z : ℝ // 0 ≤ z}) :
        planarRankOneOperatorInverse P.D P.F μ P.uniformlyElliptic
            P.normalized z = invμ z := by
      apply (lemPlanarOperatorBounds P.D P.F μ P.uniformlyElliptic
        P.normalized).1.injective
      rw [hinv_eq, hμeq]
    simpa [K, d, hν y, hμ y] using hbound y
  let fν : ℝ → ℝ := fun s ↦
    (planarRankOneOperatorInverse P.D P.F ν P.uniformlyElliptic P.normalized
      ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
        mul_nonneg (div_nonneg γ.property.le η.property.le)
          (P.beta_nonnegative s)⟩ : ℝ)
  let fμ : ℝ → ℝ := fun s ↦
    (planarRankOneOperatorInverse P.D P.F μ P.uniformlyElliptic P.normalized
      ⟨(γ : ℝ) / (η : ℝ) * P.D.beta s,
        mul_nonneg (div_nonneg γ.property.le η.property.le)
          (P.beta_nonnegative s)⟩ : ℝ)
  let g : ℝ → ℝ := fun s ↦
    K * ((γ : ℝ) / (η : ℝ) * P.D.beta s) * d
  have hg_int : IntervalIntegrable g MeasureTheory.volume (-1 : ℝ) 1 := by
    have hgform : g = fun s ↦
        (K * ((γ : ℝ) / (η : ℝ)) * d) * P.D.beta s := by
      funext s
      simp only [g]
      ring
    rw [hgform]
    exact hbeta_int.const_mul (K * ((γ : ℝ) / (η : ℝ)) * d)
  have hdiff_int : IntervalIntegrable (fun s ↦ fν s - fμ s)
      MeasureTheory.volume (-1 : ℝ) 1 :=
    (htarget_int ν).sub (htarget_int μ)
  have hpoint (s : ℝ) : |fν s - fμ s| ≤ g s := by
    dsimp [fν, fμ, g]
    convert hchosen_dir ⟨_, mul_nonneg
      (div_nonneg γ.property.le η.property.le) (P.beta_nonnegative s)⟩ using 1
  have hiupper :
      (∫ s in (-1 : ℝ)..1, (fν s - fμ s)) ≤
        ∫ s in (-1 : ℝ)..1, g s := by
    exact intervalIntegral.integral_mono_on (by norm_num) hdiff_int hg_int
      (fun s hs ↦ le_trans (le_abs_self _) (hpoint s))
  have hilower :
      -(∫ s in (-1 : ℝ)..1, g s) ≤
        ∫ s in (-1 : ℝ)..1, (fν s - fμ s) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_mono_on (by norm_num) hg_int.neg hdiff_int
      (fun s hs ↦ le_trans (neg_le_neg (hpoint s)) (neg_abs_le _))
  have hiabs :
      |∫ s in (-1 : ℝ)..1, (fν s - fμ s)| ≤
        ∫ s in (-1 : ℝ)..1, g s :=
    (abs_le).2 ⟨hilower, hiupper⟩
  rw [PlanarTransitionIncrement, PlanarTransitionIncrement]
  change |2 * (η : ℝ) * (∫ s in (-1 : ℝ)..1, fν s) -
      2 * (η : ℝ) * (∫ s in (-1 : ℝ)..1, fμ s)| ≤ _
  rw [← mul_sub,
    ← intervalIntegral.integral_sub (htarget_int ν) (htarget_int μ)]
  rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) η.property.le)]
  calc
    2 * (η : ℝ) * |∫ s in (-1 : ℝ)..1, (fν s - fμ s)| ≤
        2 * (η : ℝ) * ∫ s in (-1 : ℝ)..1, g s :=
      mul_le_mul_of_nonneg_left hiabs
        (mul_nonneg (by norm_num) η.property.le)
    _ = (2 * C / P.D.lambda ^ 2) * (γ : ℝ) *
          (∫ s in (-1 : ℝ)..1, P.D.beta s) * d := by
      have hg : g = fun s ↦
          (K * ((γ : ℝ) / (η : ℝ)) * d) * P.D.beta s := by
        funext s
        simp only [g]
        ring
      rw [hg, intervalIntegral.integral_const_mul]
      dsimp [K, d]
      field_simp [ne_of_gt η.property]

end Lea.Lipschitz2
