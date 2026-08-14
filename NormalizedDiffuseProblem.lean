import Lea.Lipschitz2.Uniformellipticity
import Lea.Lipschitz2.ViscositySolutionConvention

namespace Lea.Lipschitz2

/-- A normalized diffuse problem on the unit ball: a continuous, normalized,
uniformly elliptic operator together with parameters `0 < γ, δ ≤ 1` and a
continuous viscosity solution of
`F(D²v) = (γ / δ) β(v / δ)` whose absolute value is at most one on `B₁`.
The test-function predicate and Hessian map make explicit the shared viscosity
framework used throughout the project. -/
structure NormalizedDiffuseProblem where
  D : StructuralDataAndNotation
  F : Sn D.n → ℝ
  gamma : ℝ
  delta : ℝ
  v : (Fin D.n → ℝ) → ℝ
  IsTest : (((Fin D.n → ℝ) → ℝ) → Prop)
  hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n
  beta_continuous : Continuous D.beta
  beta_nonnegative : ∀ s : ℝ, 0 ≤ D.beta s
  beta_nonzero : D.beta ≠ 0
  beta_support : Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1
  uniformlyElliptic : Uniformellipticity D F
  normalized : F 0 = 0
  gamma_pos : 0 < gamma
  gamma_le_one : gamma ≤ 1
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  continuousOn : ContinuousOn v (centeredEuclideanBall D 1)
  viscositySolution :
    ViscositySolutionOn (centeredEuclideanBall D 1) F
      (fun x => (gamma / delta) * D.beta (v x / delta)) v IsTest hessian
  norm_le_one : ∀ x ∈ centeredEuclideanBall D 1, |v x| ≤ 1

end Lea.Lipschitz2
