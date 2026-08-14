import Lea.Lipschitz2.TransitionRegion
import Lea.Lipschitz2.StructuralDataAndNotation
import Mathlib.Order.CompletePartialOrder

namespace Lea.Lipschitz2

/-- The buffered level-boundary seminorm
`𝓑(v)` associated with the enlarged transition layer `{|v| < 2 * δ}`.
It is valued in `ℝ≥0∞` so that no boundedness assumption is needed.  If the
buffered level boundary does not meet `B_{2/3}`, the outer supremum is over an
empty type and hence equals zero. -/
noncomputable def BufferedBoundarySeminorm
    (D : StructuralDataAndNotation) (δ : ℝ)
    (v : C(centeredEuclideanBall D 1, ℝ)) : ENNReal :=
  let Ω := centeredEuclideanBall D 1
  let Γ := TransitionLevelBoundary Ω v (2 * δ)
  ⨆ z : {z : Ω // z ∈ Γ ∧ (z : Fin D.n → ℝ) ∈ centeredEuclideanBall D (2 / 3)},
    ⨆ x : {x : Ω //
      (x : Fin D.n → ℝ) ∈ centeredEuclideanBall D (3 / 4) ∧
        (x : Ω) ≠ (z : Ω)},
      ENNReal.ofReal (2 / 3 - ‖(z : Fin D.n → ℝ)‖) *
        (edist (v x) (v z) / edist (x : Ω) (z : Ω))

end Lea.Lipschitz2
