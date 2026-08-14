import Lea.Lipschitz2.ViscositySolutionConvention
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace Lea.Lipschitz2

/-- A transverse two-plane free-boundary test based at `x₀`.

The defining function `d` is `C²`, vanishes at `x₀`, and its gradient there
has unit length.  Positivity of both one-sided slopes records transversality. -/
structure TwoPlaneTestFunction (D : StructuralDataAndNotation) where
  d : (Fin D.n → ℝ) → ℝ
  x₀ : Fin D.n → ℝ
  a : ℝ
  b : ℝ
  contDiff_d : ContDiff ℝ 2 d
  d_at_base : d x₀ = 0
  a_pos : 0 < a
  b_pos : 0 < b
  unit_normal :
    ‖fun i : Fin D.n => fderiv ℝ d x₀ (Pi.single i 1)‖ = 1

namespace TwoPlaneTestFunction

/-- The oriented normal `ν = ∇d(x₀)` of a two-plane test. -/
noncomputable def normal {D : StructuralDataAndNotation} (P : TwoPlaneTestFunction D) :
    Fin D.n → ℝ :=
  fun i => fderiv ℝ P.d P.x₀ (Pi.single i 1)

/-- The function `P_{a,b}(d) = a d⁺ - b d⁻`. -/
def toFun {D : StructuralDataAndNotation} (P : TwoPlaneTestFunction D) :
    (Fin D.n → ℝ) → ℝ :=
  fun x => P.a * max (P.d x) 0 - P.b * max (-P.d x) 0

instance {D : StructuralDataAndNotation} : CoeFun (TwoPlaneTestFunction D)
    (fun _ => (Fin D.n → ℝ) → ℝ) :=
  ⟨toFun⟩

@[simp] theorem normal_norm {D : StructuralDataAndNotation}
    (P : TwoPlaneTestFunction D) : ‖P.normal‖ = 1 := by
  exact P.unit_normal

@[simp] theorem apply_eq {D : StructuralDataAndNotation}
    (P : TwoPlaneTestFunction D) (x : Fin D.n → ℝ) :
    P x = P.a * max (P.d x) 0 - P.b * max (-P.d x) 0 := by
  rfl

@[simp] theorem apply_base {D : StructuralDataAndNotation}
    (P : TwoPlaneTestFunction D) : P P.x₀ = 0 := by
  simp [apply_eq, P.d_at_base]

/-- A viscosity contact from below by the transverse two-plane `P`. -/
def TouchesFromBelowOn {D : StructuralDataAndNotation}
    (Ω : Set (Fin D.n → ℝ)) (u : (Fin D.n → ℝ) → ℝ)
    (P : TwoPlaneTestFunction D) : Prop :=
  Lea.Lipschitz2.TouchesFromBelowOn Ω u P P.x₀

/-- A viscosity contact from above by the transverse two-plane `P`. -/
def TouchesFromAboveOn {D : StructuralDataAndNotation}
    (Ω : Set (Fin D.n → ℝ)) (u : (Fin D.n → ℝ) → ℝ)
    (P : TwoPlaneTestFunction D) : Prop :=
  Lea.Lipschitz2.TouchesFromAboveOn Ω u P P.x₀

/-- The transmission inequality associated with the direction of contact:
from below gives `a ≤ G ν b`, and from above gives the reverse inequality. -/
def TransmissionInequality {D : StructuralDataAndNotation}
    (G : (Fin D.n → ℝ) → ℝ → ℝ) (contact : ViscosityContactDirection)
    (P : TwoPlaneTestFunction D) : Prop :=
  match contact with
  | .fromBelow => P.a ≤ G P.normal P.b
  | .fromAbove => G P.normal P.b ≤ P.a

end TwoPlaneTestFunction

end Lea.Lipschitz2
