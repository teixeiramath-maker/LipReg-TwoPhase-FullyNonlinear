import Lea.Lipschitz2.StructuralDataAndNotation

namespace Lea.Lipschitz2

/-- For a radial reaction profile `φ` and positive parameters `ε` and `α`,
`RadialSharpnessFamily D φ ε α` is the radial function
`x ↦ ε φ ((√α / ε) |x|)` on `ℝⁿ`. -/
noncomputable def RadialSharpnessFamily
    (D : StructuralDataAndNotation) (φ : ℝ → ℝ)
    (ε α : {t : ℝ // 0 < t}) : (Fin D.n → ℝ) → ℝ :=
  fun x => (ε : ℝ) *
    φ ((Real.sqrt (α : ℝ) / (ε : ℝ)) *
      Real.sqrt (∑ i : Fin D.n, (x i) ^ 2))

end Lea.Lipschitz2
