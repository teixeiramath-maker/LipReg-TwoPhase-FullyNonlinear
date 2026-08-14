import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.UniformEllipticityPucciBounds
import Lea.Lipschitz2.EllipticOperatorCompactnessAndViscosityStability
import Lea.Lipschitz2.InteriorC1AlphaEstimate
import Lea.Lipschitz2.ViscositySolutionConvention

namespace Lea.Lipschitz2

/-- Sequential local precompactness, stated directly for the normalized errors
appearing in the nondegenerate-affine compactness lemma. -/
def NondegenerateErrorLocallyPrecompact
    (D : StructuralDataAndNotation)
    (u : ℕ → (Fin D.n → ℝ) → ℝ)
    (b e : ℕ → ℝ) (p : ℕ → Fin D.n → ℝ) : Prop :=
  ∀ s : ℕ → ℕ, StrictMono s →
    ∃ t : ℕ → ℕ, ∃ zLimit : (Fin D.n → ℝ) → ℝ,
      StrictMono t ∧
        LocallyUniformlyConvergesOn (centeredEuclideanBall D 1)
          (fun j x =>
            (u (s (t j)) x -
              (b (s (t j)) + dotProduct (p (s (t j))) x)) /
              e (s (t j)))
          zLimit

/-- The exact compactness statement for errors about affine functions whose
slopes stay in a fixed nondegenerate interval.  The rescaled operators and
errors in the conclusion are the displayed `𝓕_j` and `z_j` of the paper. -/
def NondegenerateErrorCompactnessStatement
    (D : StructuralDataAndNotation) : Prop :=
  ∀ (F : ℕ → Sn D.n → ℝ) (gamma eta sigma e b : ℕ → ℝ)
    (p : ℕ → Fin D.n → ℝ)
    (u : ℕ → (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n)
    (a₀ a₁ : ℝ),
    Continuous D.beta →
    (∀ s : ℝ, 0 ≤ D.beta s) →
    Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1 →
    (∀ j, Uniformellipticity D (F j)) →
    (∀ j, F j 0 = 0) →
    (∀ j, 0 ≤ gamma j) →
    (∀ j, 0 < eta j) →
    (∀ j, |sigma j| ≤ 2 * eta j) →
    (∀ j, ContinuousOn (u j) (centeredEuclideanBall D 1)) →
    (∀ j, ViscositySolutionOn (centeredEuclideanBall D 1) (F j)
      (fun x => (gamma j / eta j) *
        D.beta ((u j x + sigma j) / eta j))
      (u j) IsTest hessian) →
    0 < a₀ →
    (∀ j, a₀ ≤ ‖p j‖ ∧ ‖p j‖ ≤ a₁) →
    (∀ j, 0 < e j) →
    Antitone e →
    Filter.Tendsto e Filter.atTop (nhds 0) →
    (∀ j x, x ∈ centeredEuclideanBall D 1 →
      |u j x - (b j + dotProduct (p j) x)| ≤ e j) →
    Filter.Tendsto (fun j => gamma j / e j) Filter.atTop (nhds 0) →
    NondegenerateErrorLocallyPrecompact D u b e p ∧
    ∃ subsequence : ℕ → ℕ, ∃ F_infty : Sn D.n → ℝ,
      ∃ z_infty : (Fin D.n → ℝ) → ℝ,
        StrictMono subsequence ∧
        Uniformellipticity D F_infty ∧
        F_infty 0 = 0 ∧
        LocallyUniformlyConvergesOn Set.univ
          (fun j M =>
            (1 / e (subsequence j)) *
              F (subsequence j) (e (subsequence j) • M))
          F_infty ∧
        LocallyUniformlyConvergesOn (centeredEuclideanBall D 1)
          (fun j x =>
            (u (subsequence j) x -
              (b (subsequence j) + dotProduct (p (subsequence j)) x)) /
              e (subsequence j))
          z_infty ∧
        ViscositySolutionOn (centeredEuclideanBall D 1)
          F_infty 0 z_infty IsTest hessian

/-- The imported sliding-paraboloid estimate together with the lifted-contact
argument.  Its hypotheses are precisely the foundational operator
compactness, ordinary viscosity stability, and interior `C¹,α` estimate used
in the manuscript proof. -/
def NondegenerateAffineLiftedContactArgument
    (D : StructuralDataAndNotation) : Prop :=
  EllipticOperatorLocalCompactnessStatement D →
  ViscosityStabilityStatement D →
  (∃ alpha C : ℝ,
    0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      InteriorC1AlphaEstimateStatement D alpha C) →
  NondegenerateErrorCompactnessStatement D

/-- **Compactness of nondegenerate affine errors.**

If shifted diffuse solutions are within `e_j ↓ 0` of affine functions with
uniformly nonzero and bounded slopes, and `γ_j / e_j → 0`, then their
normalized errors are locally precompact.  Along one subsequence both the
amplitude-rescaled operators and errors converge locally uniformly, and the
limit error solves the homogeneous limiting equation in the shared viscosity
sense. -/
theorem lemnondegenerateerrorcompactness
    (D : StructuralDataAndNotation)
    (importedOperatorCompactness :
      EllipticOperatorLocalCompactnessStatement D)
    (importedViscosityStability : ViscosityStabilityStatement D)
    (importedCaffarelliCabreEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          InteriorC1AlphaEstimateStatement D alpha C)
    (importedSlidingParaboloidAndLiftedContact :
      NondegenerateAffineLiftedContactArgument D) :
    NondegenerateErrorCompactnessStatement D := by
  have hFoundational :=
    EllipticOperatorCompactnessAndViscosityStability D
      importedOperatorCompactness importedViscosityStability
  have hInterior :=
    InteriorC1AlphaEstimate D importedCaffarelliCabreEstimate
  exact importedSlidingParaboloidAndLiftedContact
    hFoundational.1 hFoundational.2.1 hInterior

end Lea.Lipschitz2
