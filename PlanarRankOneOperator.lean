import Lea.Lipschitz2.StructuralDataAndNotation

namespace Lea.Lipschitz2

/-- The restriction `Q_{F,ν}(t) = F(t ν ⊗ ν)` of an operator on symmetric
matrices to the nonnegative rank-one ray determined by the Euclidean unit
vector `ν`. -/
def PlanarRankOneOperator (D : StructuralDataAndNotation)
    (F : Sn D.n → ℝ)
    (ν : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1}) :
    {t : ℝ // 0 ≤ t} → ℝ :=
  fun t ↦ F ⟨fun i j ↦ (t : ℝ) * ν.1 i * ν.1 j, by
    ext i j
    simp only [Matrix.transpose_apply]
    ring⟩

end Lea.Lipschitz2
