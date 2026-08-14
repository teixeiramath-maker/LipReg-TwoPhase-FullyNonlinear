import Lea.Lipschitz2.SingularPerturbationProblemData
import Lea.Lipschitz2.lemSingularPerturbationRescaling
import Lea.Lipschitz2.BufferedBoundarySeminorm

namespace Lea.Lipschitz2

/-- A shifted diffuse problem on an open domain.  It packages a normalized,
uniformly elliptic operator and a continuous viscosity solution of
`F(D²w) = (γ / η) β((w + σ) / η)`, where the effective strength is
nonnegative, the rescaled thickness is positive, and `|σ| ≤ 2 * η`.
The constant `2` is the fixed buffer constant `c₀` used for the enlarged
transition region. -/
structure ShiftedDiffuseProblem where
  D : StructuralDataAndNotation
  domain : Set (Fin D.n → ℝ)
  isOpen_domain : IsOpen domain
  F : Sn D.n → ℝ
  gamma : ℝ
  eta : ℝ
  sigma : ℝ
  w : (Fin D.n → ℝ) → ℝ
  IsTest : (((Fin D.n → ℝ) → ℝ) → Prop)
  hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n
  beta_continuous : Continuous D.beta
  beta_nonnegative : ∀ s : ℝ, 0 ≤ D.beta s
  beta_nonzero : D.beta ≠ 0
  beta_support : Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1
  uniformlyElliptic : Uniformellipticity D F
  normalized : F 0 = 0
  gamma_nonnegative : 0 ≤ gamma
  eta_pos : 0 < eta
  shift_bound : |sigma| ≤ 2 * eta
  continuousOn : ContinuousOn w domain
  viscositySolution :
    ViscositySolutionOn domain F
      (fun x => (gamma / eta) * D.beta ((w x + sigma) / eta))
      w IsTest hessian

end Lea.Lipschitz2
