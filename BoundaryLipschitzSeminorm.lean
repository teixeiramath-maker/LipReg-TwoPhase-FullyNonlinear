import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.CompletePartialOrder

namespace Lea.Lipschitz2

/-- The boundary-to-domain Lipschitz seminorm of `v`, with one endpoint
restricted to `E ⊆ Ω`. It takes values in `ℝ≥0∞` to allow the supremum to be
infinite. -/
noncomputable def BoundaryLipschitzSeminorm
    {X : Type*} {Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (Ω : Set X) (E : Set Ω) (v : Ω → Y) : ENNReal :=
  ⨆ z : E, ⨆ x : {x : Ω // x ≠ (z : Ω)},
    edist (v x) (v z) / edist (x : Ω) (z : Ω)

end Lea.Lipschitz2
