import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Lea.Lipschitz2

/-- The transition region of a continuous function `v` on `Ω` at height `a`:
the points of `Ω` where `|v| < a`. -/
def TransitionRegion {X : Type*} [TopologicalSpace X] (Ω : Set X)
    (v : C(Ω, ℝ)) (a : ℝ) : Set Ω :=
  {x | |v x| < a}

/-- The level boundary corresponding to `TransitionRegion`, taken relative to
the ambient domain `Ω`. -/
def TransitionLevelBoundary {X : Type*} [TopologicalSpace X] (Ω : Set X)
    (v : C(Ω, ℝ)) (a : ℝ) : Set Ω :=
  frontier (TransitionRegion Ω v a)

end Lea.Lipschitz2
