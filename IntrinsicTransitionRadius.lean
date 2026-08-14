import Mathlib.Data.Real.Sqrt

namespace Lea.Lipschitz2

/-- The intrinsic spatial radius associated with a transition of height `δ`
and strength `γ`. -/
noncomputable def IntrinsicTransitionRadius (γ δ : ℝ) : ℝ :=
  δ / Real.sqrt γ

end Lea.Lipschitz2
