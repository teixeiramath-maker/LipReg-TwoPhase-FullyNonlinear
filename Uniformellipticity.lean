import Lea.Lipschitz2.StructuralDataAndNotation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

namespace Lea.Lipschitz2

/-- A continuous operator on real symmetric matrices is uniformly elliptic
with the ellipticity constants contained in `D` when its increment in every
positive-semidefinite direction is bounded by the corresponding trace bounds. -/
def Uniformellipticity (D : StructuralDataAndNotation)
    (F : Sn D.n → ℝ) : Prop :=
  Continuous F ∧
    ∀ M N : Sn D.n,
      Matrix.PosSemidef (N : Matrix (Fin D.n) (Fin D.n) ℝ) →
      D.lambda * Matrix.trace (N : Matrix (Fin D.n) (Fin D.n) ℝ) ≤ F (M + N) - F M ∧
      F (M + N) - F M ≤
        D.Lambda * Matrix.trace (N : Matrix (Fin D.n) (Fin D.n) ℝ)

end Lea.Lipschitz2
