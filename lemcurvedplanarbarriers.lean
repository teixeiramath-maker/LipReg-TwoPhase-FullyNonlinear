import Lea.Lipschitz2.StructuralDataAndNotation
import Mathlib.Data.Real.StarOrdered

namespace Lea.Lipschitz2

/-- Quantitative core of the curved-planar-barrier argument.

Here `r` is the unperturbed reaction, `kPlus` and `kMinus` are the second
profile derivatives, `qPlus` and `qMinus` are the first profile derivatives,
and `tracePlus` and `traceMinus` are the traces of the Hessians of the two
bending functions.  The hypotheses `hgeomPlus` and `hgeomMinus` are exactly
the pointwise estimates furnished by the Pucci difference bounds after the
chain rule.  The equalities `hplanarPlus` and `hplanarMinus` are the exact
planar-profile equations with strengths `(1+τ)γ` and `(1-τ)γ`.

Thus the conclusion is the strict lower comparison for a convex bend and the
strict upper comparison for a concave bend.  The displayed choice of `κ₀`
depends only on the ellipticity constants (and hence only on the permitted
structural data). -/
theorem lemcurvedplanarbarriers (D : StructuralDataAndNotation) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ b₀ b₁ τ r kPlus qPlus tracePlus lhsPlus
        kMinus qMinus traceMinus lhsMinus : ℝ,
        0 < b₀ → b₀ < b₁ → 0 < τ → τ < 1 / 2 → 0 ≤ r →
        0 ≤ kPlus → b₀ ≤ qPlus → 0 < tracePlus →
        D.lambda * kPlus ≤ (1 + τ) * r →
        lhsPlus ≥ (1 + τ) * r - D.Lambda * κ₀ * τ * kPlus +
          D.lambda * qPlus * tracePlus →
        0 ≤ kMinus → b₀ ≤ qMinus → traceMinus < 0 →
        D.lambda * kMinus ≤ (1 - τ) * r →
        lhsMinus ≤ (1 - τ) * r + D.Lambda * κ₀ * τ * kMinus +
          D.lambda * qMinus * traceMinus →
        r < lhsPlus ∧ lhsMinus < r := by
  refine ⟨D.lambda / (8 * D.Lambda), ?_, ?_⟩
  · have hΛ : 0 < D.Lambda := lt_of_lt_of_le D.lambda_pos D.lambda_le_Lambda
    exact div_pos D.lambda_pos (mul_pos (by norm_num) hΛ)
  · intro b₀ b₁ τ r kPlus qPlus tracePlus lhsPlus
      kMinus qMinus traceMinus lhsMinus hb₀ hb₁ hτ hτhalf hr
      hkPlus hqPlus htracePlus hkPlusBound hgeomPlus
      hkMinus hqMinus htraceMinus hkMinusBound hgeomMinus
    have hΛ : 0 < D.Lambda := lt_of_lt_of_le D.lambda_pos D.lambda_le_Lambda
    have hqPlusPos : 0 < qPlus := lt_of_lt_of_le hb₀ hqPlus
    have hqMinusPos : 0 < qMinus := lt_of_lt_of_le hb₀ hqMinus
    have hcurvPlus : 0 < D.lambda * qPlus * tracePlus :=
      mul_pos (mul_pos D.lambda_pos hqPlusPos) htracePlus
    have hcurvMinus : D.lambda * qMinus * traceMinus < 0 :=
      mul_neg_of_pos_of_neg (mul_pos D.lambda_pos hqMinusPos) htraceMinus
    have herrPlus :
        D.Lambda * (D.lambda / (8 * D.Lambda)) * τ * kPlus ≤
          τ * ((1 + τ) * r) / 8 := by
      have := mul_le_mul_of_nonneg_left hkPlusBound hτ.le
      rw [show D.Lambda * (D.lambda / (8 * D.Lambda)) = D.lambda / 8 by
        field_simp]
      nlinarith
    have herrMinus :
        D.Lambda * (D.lambda / (8 * D.Lambda)) * τ * kMinus ≤
          τ * ((1 - τ) * r) / 8 := by
      have := mul_le_mul_of_nonneg_left hkMinusBound hτ.le
      rw [show D.Lambda * (D.lambda / (8 * D.Lambda)) = D.lambda / 8 by
        field_simp]
      nlinarith
    have hcoefPlus : τ * (1 + τ) / 8 ≤ τ := by
      nlinarith [sq_nonneg τ]
    have hcoefMinus : τ * (1 - τ) / 8 ≤ τ := by
      nlinarith [sq_nonneg τ]
    have hmarginPlus :
        D.Lambda * (D.lambda / (8 * D.Lambda)) * τ * kPlus ≤ τ * r := by
      calc
        D.Lambda * (D.lambda / (8 * D.Lambda)) * τ * kPlus ≤
            τ * ((1 + τ) * r) / 8 := herrPlus
        _ = (τ * (1 + τ) / 8) * r := by ring
        _ ≤ τ * r := mul_le_mul_of_nonneg_right hcoefPlus hr
    have hmarginMinus :
        D.Lambda * (D.lambda / (8 * D.Lambda)) * τ * kMinus ≤ τ * r := by
      calc
        D.Lambda * (D.lambda / (8 * D.Lambda)) * τ * kMinus ≤
            τ * ((1 - τ) * r) / 8 := herrMinus
        _ = (τ * (1 - τ) / 8) * r := by ring
        _ ≤ τ * r := mul_le_mul_of_nonneg_right hcoefMinus hr
    constructor <;> nlinarith

end Lea.Lipschitz2
