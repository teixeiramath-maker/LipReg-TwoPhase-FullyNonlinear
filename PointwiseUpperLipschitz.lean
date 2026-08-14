import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Lea.Lipschitz2

/-- The pointwise upper Lipschitz constant of `v` at `x₀`, computed along the
punctured domain `Ω`. The value lies in `ℝ≥0∞` so that an unbounded upper
slope is represented by `∞`. -/
noncomputable def PointwiseUpperLipschitz
    {E : Type*} {F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (Ω : Set E) (v : E → F) (x₀ : E) : ENNReal :=
  Filter.limsup
    (fun x => edist (v x) (v x₀) / edist x x₀)
    (nhdsWithin x₀ (Ω \ {x₀}))

end Lea.Lipschitz2
