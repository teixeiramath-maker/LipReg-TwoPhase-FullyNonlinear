import Lea.Lipschitz2.Uniformellipticity
import Lea.Lipschitz2.ViscositySolutionConvention

namespace Lea.Lipschitz2

/-- The data and structural assumptions for the singular perturbation problem.
The type `Sn D.n → ℝ` makes the operator depend only on the Hessian, thereby
encoding the translation invariance used in the paper. -/
structure SingularPerturbationProblemData where
  D : StructuralDataAndNotation
  epsilon : ℝ
  alpha : ℝ
  F : Sn D.n → ℝ
  epsilon_pos : 0 < epsilon
  alpha_nonneg : 0 ≤ alpha
  beta_continuous : Continuous D.beta
  beta_nonnegative : ∀ s : ℝ, 0 ≤ D.beta s
  beta_nonzero : D.beta ≠ 0
  beta_support : Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1
  uniformlyElliptic : Uniformellipticity D F
  normalized : F 0 = 0

/-- The right-hand side `(α / ε) β(u / ε)` of the singular perturbation
equation associated with `P`. -/
noncomputable def SingularPerturbationProblemData.source
    (P : SingularPerturbationProblemData) (u : (Fin P.D.n → ℝ) → ℝ) :
    (Fin P.D.n → ℝ) → ℝ :=
  fun x => (P.alpha / P.epsilon) * P.D.beta (u x / P.epsilon)

/-- A continuous viscosity solution of the singular perturbation equation on
the unit ball, using the project's shared test-function and Hessian framework. -/
def SingularPerturbationProblemData.IsSolution
    (P : SingularPerturbationProblemData) (u : (Fin P.D.n → ℝ) → ℝ)
    (IsTest : ((Fin P.D.n → ℝ) → ℝ) → Prop)
    (hessian : ((Fin P.D.n → ℝ) → ℝ) → (Fin P.D.n → ℝ) → Sn P.D.n) : Prop :=
  ContinuousOn u (centeredEuclideanBall P.D 1) ∧
    ViscositySolutionOn (centeredEuclideanBall P.D 1) P.F (P.source u) u IsTest hessian

/-- The transition region `T_ε(u) = {x ∈ B₁ | |u(x)| < ε}`. -/
def SingularPerturbationProblemData.transitionRegion
    (P : SingularPerturbationProblemData) (u : (Fin P.D.n → ℝ) → ℝ) :
    Set (Fin P.D.n → ℝ) :=
  {x | x ∈ centeredEuclideanBall P.D 1 ∧ |u x| < P.epsilon}

end Lea.Lipschitz2
