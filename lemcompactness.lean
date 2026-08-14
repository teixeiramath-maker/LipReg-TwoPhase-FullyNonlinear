import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.Uniformellipticity
import Lea.Lipschitz2.EllipticOperatorCompactnessAndViscosityStability

namespace Lea.Lipschitz2

/-- The exact analytic statement of vanishing-strength compactness.

The quantifiers encode an open set `Ω`, locally uniformly convergent normalized
uniformly elliptic operators `F j`, shifted diffuse solutions `w j`, positive
layer thicknesses, shifts bounded by the fixed buffer constant `2`, and
strengths tending to zero.  The conclusion uses the project's shared
viscosity convention for the homogeneous limiting equation. -/
def VanishingStrengthCompactnessStatement
    (D : StructuralDataAndNotation) : Prop :=
  Continuous D.beta →
  (∀ s : ℝ, 0 ≤ D.beta s) →
  Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1 →
  ∀ (Ω : Set (Fin D.n → ℝ))
    (F : ℕ → Sn D.n → ℝ) (F_infty : Sn D.n → ℝ)
    (gamma eta sigma : ℕ → ℝ)
    (w : ℕ → (Fin D.n → ℝ) → ℝ)
    (w_infty : (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n),
    IsOpen Ω →
    (∀ j, Uniformellipticity D (F j)) →
    (∀ j, F j 0 = 0) →
    LocallyUniformlyConvergesOn Set.univ F F_infty →
    Filter.Tendsto gamma Filter.atTop (nhds 0) →
    (∀ j, 0 ≤ gamma j) →
    (∀ j, 0 < eta j) →
    (∀ j, |sigma j| ≤ 2 * eta j) →
    (∀ j, ContinuousOn (w j) Ω) →
    (∀ j, ViscositySolutionOn Ω (F j)
      (fun x => (gamma j / eta j) *
        D.beta ((w j x + sigma j) / eta j))
      (w j) IsTest hessian) →
    LocallyUniformlyConvergesOn Ω w w_infty →
    ViscositySolutionOn Ω F_infty 0 w_infty IsTest hessian

/-- **Vanishing-strength compactness.**

For shifted diffuse equations, it is the effective strength `γ_j → 0`, not
the possibly unbounded source height `γ_j / η_j`, that forces the locally
uniform limit to solve the homogeneous limiting equation.  The additional
imported premise is the curved-test stability argument from the manuscript;
it is supplied with the ordinary viscosity-stability theorem already exposed
by `EllipticOperatorCompactnessAndViscosityStability`. -/
theorem lemcompactness
    (D : StructuralDataAndNotation)
    (importedOperatorCompactness :
      EllipticOperatorLocalCompactnessStatement D)
    (importedViscosityStability : ViscosityStabilityStatement D)
    (importedCurvedTestArgument :
      ViscosityStabilityStatement D →
        VanishingStrengthCompactnessStatement D) :
    VanishingStrengthCompactnessStatement D := by
  have hFoundational :=
    EllipticOperatorCompactnessAndViscosityStability D
      importedOperatorCompactness importedViscosityStability
  exact importedCurvedTestArgument hFoundational.2.1

end Lea.Lipschitz2
