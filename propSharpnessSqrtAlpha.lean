import Lea.Lipschitz2.MainLipschitzEstimate
import Lea.Lipschitz2.lemRadialSharpnessEquationAndSlope
import Lea.Lipschitz2.lemRadialSharpnessAmplitude

namespace Lea.Lipschitz2

/-- If a family has amplitude `o(√α)` but gradient size at least `c⋆ √α`,
then no estimate with an additive `o(√α)` term can hold with a fixed positive
constant.  Applied to the smooth radial family supplied by
`lemRadialSharpnessEquationAndSlope` and `lemRadialSharpnessAmplitude`, this
says that the square-root term in `MainLipschitzEstimate` is sharp. -/
theorem propSharpnessSqrtAlpha
    (amplitude gradientSize : ℝ → ℝ) (c_star : ℝ) (hc_star : 0 < c_star)
    (hAmplitude : Filter.Tendsto
      (fun α : ℝ => amplitude α / Real.sqrt α)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hGradient : ∀ α : ℝ, 0 < α →
      c_star * Real.sqrt α ≤ gradientSize α) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ omega : ℝ → ℝ,
      Filter.Tendsto
        (fun α : ℝ => omega α / Real.sqrt α)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ α : ℝ, 0 < α →
        gradientSize α ≤ C * (amplitude α + omega α) := by
  rintro ⟨C, hC, omega, hOmega, hEstimate⟩
  have hRight : Filter.Tendsto
      (fun α : ℝ => C *
        (amplitude α / Real.sqrt α + omega α / Real.sqrt α))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (hAmplitude.add hOmega).const_mul C
  have hSmall : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0),
      C * (amplitude α / Real.sqrt α + omega α / Real.sqrt α) < c_star := by
    exact (tendsto_order.1 hRight).2 c_star hc_star
  have hBoth : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0),
      C * (amplitude α / Real.sqrt α + omega α / Real.sqrt α) < c_star ∧
        α ∈ Set.Ioi (0 : ℝ) := hSmall.and self_mem_nhdsWithin
  rcases hBoth.exists with ⟨α, hsmall, hα⟩
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hdiv : gradientSize α / Real.sqrt α ≤
      (C * (amplitude α + omega α)) / Real.sqrt α :=
    div_le_div_of_nonneg_right (hEstimate α hα) hsqrt.le
  have hlower : c_star ≤ gradientSize α / Real.sqrt α := by
    calc
      c_star = (c_star * Real.sqrt α) / Real.sqrt α := by field_simp
      _ ≤ gradientSize α / Real.sqrt α :=
        div_le_div_of_nonneg_right (hGradient α hα) hsqrt.le
  have hrearrange :
      (C * (amplitude α + omega α)) / Real.sqrt α =
        C * (amplitude α / Real.sqrt α + omega α / Real.sqrt α) := by
    field_simp
  rw [hrearrange] at hdiv
  linarith

end Lea.Lipschitz2
