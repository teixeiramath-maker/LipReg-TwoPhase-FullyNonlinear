import Lea.Lipschitz2.UniformEllipticityPucciBounds
import Lea.Lipschitz2.ViscositySolutionConvention

namespace Lea.Lipschitz2

/-- Local uniform convergence on an ambient set, expressed uniformly on each
compact subset. -/
def LocallyUniformlyConvergesOn {X : Type*} [TopologicalSpace X]
    (Ω : Set X) (u : ℕ → X → ℝ) (v : X → ℝ) : Prop :=
  ∀ K : Set X, K ⊆ Ω → IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ x ∈ K, |u j x - v x| < ε

/-- The imported local compactness principle for normalized uniformly
elliptic operators on the finite-dimensional space `Sⁿ`. -/
def EllipticOperatorLocalCompactnessStatement
    (D : StructuralDataAndNotation) : Prop :=
  ∀ F : ℕ → Sn D.n → ℝ,
    (∀ j, Uniformellipticity D (F j) ∧ F j 0 = 0) →
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∃ Flimit : Sn D.n → ℝ,
        Uniformellipticity D Flimit ∧ Flimit 0 = 0 ∧
          LocallyUniformlyConvergesOn Set.univ
            (fun j => F (subsequence j)) Flimit

/-- The standard imported stability principle for viscosity solutions when
operators, sources, and solutions converge locally uniformly. -/
def ViscosityStabilityStatement (D : StructuralDataAndNotation) : Prop :=
  ∀ (Ω : Set (Fin D.n → ℝ))
    (F : ℕ → Sn D.n → ℝ) (Flimit : Sn D.n → ℝ)
    (f u : ℕ → (Fin D.n → ℝ) → ℝ)
    (flimit ulimit : (Fin D.n → ℝ) → ℝ)
    (IsTest : ((Fin D.n → ℝ) → ℝ) → Prop)
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n),
    LocallyUniformlyConvergesOn Set.univ F Flimit →
    LocallyUniformlyConvergesOn Ω f flimit →
    LocallyUniformlyConvergesOn Ω u ulimit →
    (∀ j, ViscositySolutionOn Ω (F j) (f j) (u j) IsTest hessian) →
    ViscositySolutionOn Ω Flimit flimit ulimit IsTest hessian

/-- **Compactness of elliptic operators and viscosity stability.**

The two analytic compactness/stability principles are imported foundational
results, as stipulated in the manuscript.  The Pucci-difference estimate
supplies their quantitative elliptic control: every normalized operator in
the family is trapped between the same extremal operators. -/
theorem EllipticOperatorCompactnessAndViscosityStability
    (D : StructuralDataAndNotation)
    (importedOperatorCompactness :
      EllipticOperatorLocalCompactnessStatement D)
    (importedViscosityStability : ViscosityStabilityStatement D) :
    EllipticOperatorLocalCompactnessStatement D ∧
      ViscosityStabilityStatement D ∧
      ∀ (F : Sn D.n → ℝ), Uniformellipticity D F → F 0 = 0 →
        ∀ M N : Sn D.n,
          pucciMin D (M - N) ≤ F M - F N ∧
          F M - F N ≤ pucciMax D (M - N) := by
  refine ⟨importedOperatorCompactness, importedViscosityStability, ?_⟩
  intro F hF hF0 M N
  exact (UniformEllipticityPucciBounds D F hF).1 M N

end Lea.Lipschitz2
