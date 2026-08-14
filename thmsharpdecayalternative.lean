import Lea.Lipschitz2.StructuralDataAndNotation
import Lea.Lipschitz2.TwoPlaneTestFunction
import Lea.Lipschitz2.ViscositySolutionConvention
import Lea.Lipschitz2.PointwiseUpperLipschitz
import Lea.Lipschitz2.Uniformellipticity

namespace Lea.Lipschitz2

/-- The `L∞` size of a real-valued function on a set, represented by the
supremum of its absolute values. -/
noncomputable def supNormOn {X : Type*} (Ω : Set X) (u : X → ℝ) : ℝ :=
  sSup ((fun x => |u x|) '' Ω)

/-- The viscosity formulation of a two-phase equation with transmission maps
`G ν`.  The equations are imposed separately on the positive and negative
phases.  At a free-boundary point, every transverse two-plane test satisfies
the inequality dictated by whether it touches from below or from above. -/
def SharpTwoPhaseViscositySolution
    (D : StructuralDataAndNotation)
    (Fplus Fminus : Sn D.n → ℝ)
    (G : (Fin D.n → ℝ) → ℝ → ℝ)
    (z : (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n) : Prop :=
  let B2 := centeredEuclideanBall D 2
  let positivePhase := {x ∈ B2 | 0 < z x}
  let negativePhase := {x ∈ B2 | z x < 0}
  ContinuousOn z B2 ∧
    ViscositySolutionOn positivePhase Fplus 0 z IsTest hessian ∧
    ViscositySolutionOn negativePhase Fminus 0 z IsTest hessian ∧
    (∀ P : TwoPlaneTestFunction D,
      P.x₀ ∈ frontier positivePhase → z P.x₀ = 0 →
      (TwoPlaneTestFunction.TouchesFromBelowOn B2 z P →
        TwoPlaneTestFunction.TransmissionInequality G .fromBelow P) ∧
      (TwoPlaneTestFunction.TouchesFromAboveOn B2 z P →
        TwoPlaneTestFunction.TransmissionInequality G .fromAbove P))

/-- Exact formal content of the uniform sharp-interface decay alternative.

The constants precede all operators, transmission maps, and solutions, which
encodes their uniformity over every compact normalized elliptic family.  The
second conclusion uses `PointwiseUpperLipschitz`, as required for a solution
initially assumed only continuous. -/
def SharpDecayAlternativeStatement
    (D : StructuralDataAndNotation) (theta omegaStar C : ℝ) : Prop :=
  ∀ (Fplus Fminus : Sn D.n → ℝ)
    (G : (Fin D.n → ℝ) → ℝ → ℝ)
    (z : (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n),
    Uniformellipticity D Fplus → Fplus 0 = 0 →
    Uniformellipticity D Fminus → Fminus 0 = 0 →
    SharpTwoPhaseViscositySolution D Fplus Fminus G z IsTest hessian →
    z 0 = 0 →
    (∀ ν : Fin D.n → ℝ, ‖ν‖ = 1 → StrictMono (G ν)) →
    ∀ M : ℝ, 0 ≤ M →
      (∀ ν : Fin D.n → ℝ, ‖ν‖ = 1 →
        ∀ b : ℝ, M ≤ b →
          |deriv (G ν) b - 1| + b * |deriv (deriv (G ν)) b| ≤ omegaStar) →
      (∀ ν μ : Fin D.n → ℝ, ‖ν‖ = 1 → ‖μ‖ = 1 →
        ∀ b : ℝ, M ≤ b →
          |G ν b - G μ b| ≤ omegaStar * b * ‖ν - μ‖) →
      let A := supNormOn (centeredEuclideanBall D 1) z
      theta⁻¹ * supNormOn (centeredEuclideanBall D theta) z ≤
          (1 / 2 : ℝ) * A + C * M ∨
        ∀ x ∈ centeredEuclideanBall D theta,
          PointwiseUpperLipschitz (centeredEuclideanBall D theta) z x ≤
            ENNReal.ofReal (C * (A + M))

/-- **Sharp-interface decay alternative (De Silva--Savin).**

This is the imported uniform sharp-interface theorem used by the manuscript.
It provides constants depending only on the dimension and ellipticity data.
Normal-dependent transmission laws are included through the quantitative
normal-continuity hypothesis. -/
theorem thmsharpdecayalternative
    (D : StructuralDataAndNotation)
    (importedDeSilvaSavinAlternative :
      ∃ theta omegaStar C : ℝ,
        0 < theta ∧ theta < 1 / 4 ∧ 0 < omegaStar ∧ 0 < C ∧
          SharpDecayAlternativeStatement D theta omegaStar C) :
    ∃ theta omegaStar C : ℝ,
      0 < theta ∧ theta < 1 / 4 ∧ 0 < omegaStar ∧ 0 < C ∧
        SharpDecayAlternativeStatement D theta omegaStar C := by
  exact importedDeSilvaSavinAlternative

end Lea.Lipschitz2
