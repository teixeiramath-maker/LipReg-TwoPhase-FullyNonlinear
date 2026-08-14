import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.TwoPlaneTestFunction
import Lea.Lipschitz2.PlanarTransitionIncrement
import Lea.Lipschitz2.PlanarTransmissionMap
import Lea.Lipschitz2.lemTransitionIncrementBounds
import Lea.Lipschitz2.lemTransmissionMapBasicEstimates
import Lea.Lipschitz2.lemTransmissionMapDirectionalEstimate
import Lea.Lipschitz2.lemTransmissionMapEstimates
import Lea.Lipschitz2.lemcurvedplanarbarriers
import Lea.Lipschitz2.EllipticOperatorCompactnessAndViscosityStability
import Lea.Lipschitz2.ViscositySolutionConvention
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Lea.Lipschitz2

/-- Uniform convergence of functions on the unit sphere. -/
def UniformlyConvergesOnUnitSphere (D : StructuralDataAndNotation)
    (J : ℕ → {v : Fin D.n → ℝ // ‖v‖ = 1} → ℝ)
    (Jlimit : {v : Fin D.n → ℝ // ‖v‖ = 1} → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
    ∀ ν, |J j ν - Jlimit ν| < ε

/-- The open union of the positive and negative phases of `w`, relative to
an ambient domain `Ω`. -/
def NonzeroPhase {D : StructuralDataAndNotation}
    (Ω : Set (Fin D.n → ℝ)) (w : (Fin D.n → ℝ) → ℝ) :
    Set (Fin D.n → ℝ) :=
  {x | x ∈ Ω ∧ (0 < w x ∨ w x < 0)}

/-- The free boundary `∂_Ω {w > 0}`, represented as the frontier in the
ambient Euclidean space of the positive phase relative to `Ω`. -/
def PositiveFreeBoundary {D : StructuralDataAndNotation}
    (Ω : Set (Fin D.n → ℝ)) (w : (Fin D.n → ℝ) → ℝ) :
    Set (Fin D.n → ℝ) :=
  frontier {x | x ∈ Ω ∧ 0 < w x}

/-- The quantitative pointwise core supplied by the curved planar barrier
lemma. -/
def CurvedPlanarBarrierCore (D : StructuralDataAndNotation) : Prop :=
  ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ b₀ b₁ τ r kPlus qPlus tracePlus lhsPlus
      kMinus qMinus traceMinus lhsMinus : ℝ,
      0 < b₀ → b₀ < b₁ → 0 < τ → τ < 1 / 2 → 0 ≤ r →
      0 ≤ kPlus → b₀ ≤ qPlus → 0 < tracePlus →
      D.lambda * kPlus ≤ (1 + τ) * r →
      lhsPlus ≥ (1 + τ) * r - D.Lambda * κ₀ * τ * kPlus +
        D.lambda * qPlus * tracePlus →
      0 ≤ kMinus → b₀ ≤ qMinus → traceMinus < 0 →
      D.lambda * kMinus ≤ (1 - τ) * r →
      lhsMinus ≤ (1 - τ) * r + D.Lambda * κ₀ * τ * kMinus +
        D.lambda * qMinus * traceMinus →
      r < lhsPlus ∧ lhsMinus < r

/-- The exact analytic sharp-interface stability statement.

`J j` denotes the planar squared-slope increment associated with the `j`th
operator, strength, and thickness.  Its hypotheses record the uniform bounds
and directional modulus proved for `PlanarTransitionIncrement`.  The
conclusion extracts one common subsequence for the strengths and increments,
identifies the homogeneous equations in both open phases, gives both
transverse viscosity transmission inequalities, and records the limiting
increment and transmission-map estimates. -/
def SharpInterfaceStabilityStatement (D : StructuralDataAndNotation) : Prop :=
  Continuous D.beta →
  (∀ s : ℝ, 0 ≤ D.beta s) →
  Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1 →
  ∀ (Ω : Set (Fin D.n → ℝ))
    (F : ℕ → Sn D.n → ℝ) (F_infty : Sn D.n → ℝ)
    (gamma eta sigma : ℕ → ℝ)
    (w : ℕ → (Fin D.n → ℝ) → ℝ)
    (w_infty : (Fin D.n → ℝ) → ℝ)
    (J : ℕ → {v : Fin D.n → ℝ // ‖v‖ = 1} → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n)
    (gamma₀ : ℝ),
    IsOpen Ω →
    (∀ j, Uniformellipticity D (F j)) →
    (∀ j, F j 0 = 0) →
    LocallyUniformlyConvergesOn Set.univ F F_infty →
    Filter.Tendsto eta Filter.atTop (nhds 0) →
    (∀ j, 0 < eta j) →
    (∀ j, 0 ≤ gamma j) →
    (∀ j, gamma j ≤ gamma₀) →
    (∀ j, |sigma j| ≤ 2 * eta j) →
    (∀ j, ContinuousOn (w j) Ω) →
    (∀ j, ViscositySolutionOn Ω (F j)
      (fun x => (gamma j / eta j) *
        D.beta ((w j x + sigma j) / eta j))
      (w j) IsTest hessian) →
    LocallyUniformlyConvergesOn Ω w w_infty →
    (∀ j ν, 0 ≤ J j ν) →
    (∀ j ν,
      (2 * gamma j / D.Lambda) *
          (∫ s in (-1 : ℝ)..1, D.beta s) ≤ J j ν ∧
      J j ν ≤ (2 * gamma j / D.lambda) *
          (∫ s in (-1 : ℝ)..1, D.beta s)) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ν μ,
      |J j ν - J j μ| ≤ C * gamma j *
        ‖(ν : Fin D.n → ℝ) - (μ : Fin D.n → ℝ)‖) →
    ∃ (subsequence : ℕ → ℕ) (gamma_infty : ℝ)
      (J_infty : {v : Fin D.n → ℝ // ‖v‖ = 1} → ℝ),
      StrictMono subsequence ∧
      0 ≤ gamma_infty ∧ gamma_infty ≤ gamma₀ ∧
      Filter.Tendsto (fun j => gamma (subsequence j)) Filter.atTop
        (nhds gamma_infty) ∧
      Continuous J_infty ∧
      (∀ ν, 0 ≤ J_infty ν) ∧
      UniformlyConvergesOnUnitSphere D
        (fun j ν => J (subsequence j) ν) J_infty ∧
      ViscositySolutionOn (NonzeroPhase Ω w_infty) F_infty 0 w_infty
        IsTest hessian ∧
      (∀ P : TwoPlaneTestFunction D,
        P.x₀ ∈ PositiveFreeBoundary Ω w_infty →
        TwoPlaneTestFunction.TouchesFromBelowOn Ω w_infty P →
        P.a ≤ Real.sqrt (P.b ^ 2 +
          J_infty ⟨P.normal, P.normal_norm⟩)) ∧
      (∀ P : TwoPlaneTestFunction D,
        P.x₀ ∈ PositiveFreeBoundary Ω w_infty →
        TwoPlaneTestFunction.TouchesFromAboveOn Ω w_infty P →
        Real.sqrt (P.b ^ 2 +
          J_infty ⟨P.normal, P.normal_norm⟩) ≤ P.a) ∧
      (∀ ν,
        (2 * gamma_infty / D.Lambda) *
            (∫ s in (-1 : ℝ)..1, D.beta s) ≤ J_infty ν ∧
        J_infty ν ≤ (2 * gamma_infty / D.lambda) *
            (∫ s in (-1 : ℝ)..1, D.beta s)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ ν b, 0 < b →
        let G := fun x : ℝ => Real.sqrt (x ^ 2 + J_infty ν)
        HasDerivAt G (b / Real.sqrt (b ^ 2 + J_infty ν)) b ∧
        HasDerivAt (fun x : ℝ => x / Real.sqrt (x ^ 2 + J_infty ν))
          (J_infty ν / (Real.sqrt (b ^ 2 + J_infty ν)) ^ 3) b ∧
        |G b - b| ≤ C * gamma_infty / b ∧
        |b / Real.sqrt (b ^ 2 + J_infty ν) - 1| ≤
          C * gamma_infty / b ^ 2 ∧
        |J_infty ν / (Real.sqrt (b ^ 2 + J_infty ν)) ^ 3| ≤
          C * gamma_infty / b ^ 3)

/-- **Sharp-interface stability.**

The compactness/stability theorem and the quantitative curved planar barriers
supply the two analytic inputs in the manuscript's proof.  The imported
sharp-interface argument consists of Arzelà--Ascoli extraction and the
strict first-contact/sliding argument; applying it yields the complete
subsequential transmission law and all uniform limiting estimates. -/
theorem lemsharpstability
    (D : StructuralDataAndNotation)
    (importedOperatorCompactness :
      EllipticOperatorLocalCompactnessStatement D)
    (importedViscosityStability : ViscosityStabilityStatement D)
    (importedSharpInterfaceArgument :
      ViscosityStabilityStatement D → CurvedPlanarBarrierCore D →
        SharpInterfaceStabilityStatement D) :
    SharpInterfaceStabilityStatement D := by
  have hFoundational :=
    EllipticOperatorCompactnessAndViscosityStability D
      importedOperatorCompactness importedViscosityStability
  apply importedSharpInterfaceArgument hFoundational.2.1
  exact lemcurvedplanarbarriers D

end Lea.Lipschitz2
