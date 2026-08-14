import Lea.Lipschitz2.PlanarTransitionIncrement
import Mathlib.Data.Real.Sqrt

namespace Lea.Lipschitz2

/-- The transmission map carried by a planar diffuse layer:
`G_{F,ν,γ,η}(b) = √(b² + J_{F,ν}(γ,η))`. -/
noncomputable def PlanarTransmissionMap
    (P : SingularPerturbationProblemData)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (γ η : {x : ℝ // 0 < x}) (b : ℝ) : ℝ :=
  Real.sqrt (b ^ 2 + PlanarTransitionIncrement P ν γ η)

end Lea.Lipschitz2
