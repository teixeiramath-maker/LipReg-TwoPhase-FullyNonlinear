import Lea.Lipschitz2.RadialSharpnessFamily
import Lea.Lipschitz2.lemRadialReactionProfileGrowth
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace Lea.Lipschitz2

/-- The radial sharpness family has the stated dimension-dependent amplitude
bound on `B₁`.  With `ε = α`, the resulting bound divided by `√α` tends to
zero as `α ↓ 0`. -/
theorem lemRadialSharpnessAmplitude
    (P : SingularPerturbationProblemData) (a : ℝ) (φ : ℝ → ℝ)
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hβa : 0 < P.D.beta a)
    (hφ0 : φ 0 = a) (hφ'0 : deriv φ 0 = 0)
    (hRadialOrigin : HasDerivAt (deriv φ) (P.D.beta a / (P.D.n : ℝ)) 0)
    (hφdiff : Differentiable ℝ φ)
    (hflux : ∀ s : ℝ, 0 ≤ s →
      s ^ (P.D.n - 1) * deriv φ s =
          ∫ t in (0 : ℝ)..s, t ^ (P.D.n - 1) * P.D.beta (φ t) ∧
        0 ≤ ∫ t in (0 : ℝ)..s, t ^ (P.D.n - 1) * P.D.beta (φ t))
    (hharmonicTail : ∃ S K : ℝ, 0 ≤ S ∧ 0 ≤ K ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ S → |φ s| ≤ K) ∧
      (∀ s : ℝ, S ≤ s →
        |φ s - φ S| ≤ if P.D.n = 2 then K * Real.log (2 + s) else K)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (ε α : {t : ℝ // 0 < t}) (x : Fin P.D.n → ℝ),
        x ∈ centeredEuclideanBall P.D 1 →
        |RadialSharpnessFamily P.D φ ε α x| ≤
          if P.D.n = 2 then
            C * (ε : ℝ) *
              (1 + Real.log (2 + Real.sqrt (α : ℝ) / (ε : ℝ)))
          else C * (ε : ℝ)) ∧
      Filter.Tendsto
        (fun α : ℝ => C * Real.sqrt α *
          (if P.D.n = 2 then
            1 + Real.log (2 + 1 / Real.sqrt α)
          else 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rcases lemRadialReactionProfileGrowth P a φ ha hβa hφ0 hφ'0 hRadialOrigin
    hφdiff hflux hharmonicTail with ⟨_, C₀, hC₀, hgrowth⟩
  let C : ℝ := 3 * C₀
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ (ε α : {t : ℝ // 0 < t}) (x : Fin P.D.n → ℝ),
      x ∈ centeredEuclideanBall P.D 1 →
      |RadialSharpnessFamily P.D φ ε α x| ≤
        if P.D.n = 2 then
          C * (ε : ℝ) *
            (1 + Real.log (2 + Real.sqrt (α : ℝ) / (ε : ℝ)))
        else C * (ε : ℝ) := by
    intro ε α x hx
    unfold RadialSharpnessFamily
    have hsqrtα : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.2 α.property
    have hε : 0 < (ε : ℝ) := ε.property
    unfold centeredEuclideanBall euclideanBall at hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    let s : ℝ := (Real.sqrt (α : ℝ) / (ε : ℝ)) *
      Real.sqrt (∑ i : Fin P.D.n, (x i) ^ 2)
    have hs : 0 ≤ s := by
      dsimp [s]
      positivity
    have hg := hgrowth s hs
    rw [abs_mul, abs_of_pos hε]
    change (ε : ℝ) * |φ s| ≤ _
    by_cases hn : P.D.n = 2
    · rw [if_pos hn] at hg ⊢
      have hsumNorm := Pi.sum_norm_apply_le_norm x
      have hcoord : ∀ i : Fin P.D.n, (x i) ^ 2 ≤ 4 := by
        intro i
        have hiSum : ‖x i‖ ≤ ∑ j : Fin P.D.n, ‖x j‖ :=
          Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
        have hsumLt : (∑ j : Fin P.D.n, ‖x j‖) < 2 := by
          calc
            (∑ j : Fin P.D.n, ‖x j‖) ≤ (P.D.n : ℝ) * ‖x‖ := by
              simpa [nsmul_eq_mul] using hsumNorm
            _ = 2 * ‖x‖ := by
              have hncast : (P.D.n : ℝ) = 2 := by exact_mod_cast hn
              rw [hncast]
            _ < 2 := by nlinarith
        have hil : ‖x i‖ < 2 := lt_of_le_of_lt hiSum hsumLt
        have hupper := Real.le_norm_self (x i)
        have hlower := Real.le_norm_self (-x i)
        rw [norm_neg] at hlower
        nlinarith
      have hsum : (∑ i : Fin P.D.n, (x i) ^ 2) ≤ 8 := by
        calc
          (∑ i : Fin P.D.n, (x i) ^ 2) ≤ ∑ _i : Fin P.D.n, (4 : ℝ) :=
            Finset.sum_le_sum fun i _ => hcoord i
          _ = 8 := by norm_num [hn]
      have hsqrtSum : Real.sqrt (∑ i : Fin P.D.n, (x i) ^ 2) ≤ 3 := by
        have hnonneg : 0 ≤ ∑ i : Fin P.D.n, (x i) ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg (x i)
        nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg
          (∑ i : Fin P.D.n, (x i) ^ 2)]
      let r : ℝ := Real.sqrt (α : ℝ) / (ε : ℝ)
      have hr : 0 ≤ r := by dsimp [r]; positivity
      have hsle : s ≤ 3 * r := by
        dsimp [s, r]
        calc
          Real.sqrt (α : ℝ) / (ε : ℝ) *
              Real.sqrt (∑ i : Fin P.D.n, (x i) ^ 2) ≤
              Real.sqrt (α : ℝ) / (ε : ℝ) * 3 :=
            mul_le_mul_of_nonneg_left hsqrtSum
              (show 0 ≤ Real.sqrt (α : ℝ) / (ε : ℝ) by positivity)
          _ = 3 * (Real.sqrt (α : ℝ) / (ε : ℝ)) := by ring
      have harg : 2 + s ≤ (2 + r) ^ 3 := by nlinarith [sq_nonneg r, mul_nonneg hr (sq_nonneg r)]
      have hlog : Real.log (2 + s) ≤ 3 * Real.log (2 + r) := by
        calc
          Real.log (2 + s) ≤ Real.log ((2 + r) ^ 3) :=
            Real.strictMonoOn_log.monotoneOn
              (show 0 < 2 + s by positivity)
              (show 0 < (2 + r) ^ 3 by positivity) harg
          _ = 3 * Real.log (2 + r) := by rw [Real.log_pow]; norm_num
      have hfactor : 1 + Real.log (2 + s) ≤
          3 * (1 + Real.log (2 + r)) := by
        have : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
        linarith
      dsimp [r] at hfactor
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_left hfactor hC₀.le]
    · rw [if_neg hn] at hg ⊢
      dsimp [C]
      nlinarith
  have hlimit : Filter.Tendsto
      (fun α : ℝ => C * Real.sqrt α *
        (if P.D.n = 2 then 1 + Real.log (2 + 1 / Real.sqrt α) else 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht : Filter.Tendsto (fun α : ℝ => Real.sqrt α)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousWithinAt Real.sqrt (Set.Ioi 0) 0 :=
        Real.continuous_sqrt.continuousAt.continuousWithinAt
      simpa only [Real.sqrt_zero] using hc.tendsto
    by_cases hn : P.D.n = 2
    · simp only [if_pos hn]
      have hlog : Filter.Tendsto (fun t : ℝ => Real.log (1 + 2 * t))
          (nhds 0) (nhds 0) := by
        have hi : ContinuousAt (fun t : ℝ => 1 + 2 * t) 0 := by fun_prop
        have ho' : ContinuousAt Real.log (1 + 2 * (0 : ℝ)) :=
          Real.continuousAt_log (by norm_num)
        simpa only [Function.comp_apply, mul_zero, add_zero, Real.log_one] using
          (ContinuousAt.comp (f := fun t : ℝ => 1 + 2 * t)
            (g := Real.log) ho' hi).tendsto
      have hneg : Filter.Tendsto (fun t : ℝ => Real.negMulLog t)
          (nhds 0) (nhds 0) := by
        simpa using (Real.continuous_negMulLog.continuousAt (x := (0 : ℝ))).tendsto
      have hsum : Filter.Tendsto
          (fun α : ℝ =>
            C * Real.sqrt α +
              C * (Real.sqrt α * Real.log (1 + 2 * Real.sqrt α)) +
              C * Real.negMulLog (Real.sqrt α))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        convert (ht.const_mul C).add
          ((ht.mul (hlog.comp ht)).const_mul C) |>.add
            ((hneg.comp ht).const_mul C) using 1
        all_goals ring
      apply hsum.congr'
      filter_upwards [self_mem_nhdsWithin] with α hα
      have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
      have hrewrite : 2 + 1 / Real.sqrt α =
          (1 + 2 * Real.sqrt α) / Real.sqrt α := by
        field_simp
        ring
      rw [hrewrite, Real.log_div (by positivity) hsqrt.ne', Real.negMulLog_def]
      ring
    · simp only [if_neg hn, mul_one]
      simpa using ht.const_mul C
  exact ⟨C, hC, hbound, hlimit⟩

end Lea.Lipschitz2
