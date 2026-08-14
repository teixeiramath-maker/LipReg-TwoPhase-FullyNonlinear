import Lea.Lipschitz2.lemExactPlanarEquation
import Lea.Lipschitz2.PlanarTransitionIncrement

namespace Lea.Lipschitz2

/-- Regard the structural data of a shifted diffuse problem as singular
perturbation data with thickness `η` and strength `γ`. -/
noncomputable def ShiftedDiffuseProblem.planarData (P : ShiftedDiffuseProblem) :
    SingularPerturbationProblemData where
  D := P.D
  epsilon := P.eta
  alpha := P.gamma
  F := P.F
  epsilon_pos := P.eta_pos
  alpha_nonneg := P.gamma_nonnegative
  beta_continuous := P.beta_continuous
  beta_nonnegative := P.beta_nonnegative
  beta_nonzero := P.beta_nonzero
  beta_support := P.beta_support
  uniformlyElliptic := P.uniformlyElliptic
  normalized := P.normalized

/-- An exact planar profile solves the shifted diffuse equation throughout its
transition interval, and its outgoing slope `a = q(1)` obeys the exact balance
`a² - b² = J_{F,ν}(γ,η)`. -/
theorem lemExactPlanarTransition
    (P : ShiftedDiffuseProblem) (hγ : 0 < P.gamma)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (b : ℝ) (b_pos : 0 < b)
    (E : ExactPlanarProfile P ν b b_pos)
    (hphi_first : ∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      HasDerivAt E.phi (E.q (E.sOfTime u)) u)
    (hphi_second : ∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      HasDerivAt (deriv E.phi)
        (E.Qinv (planarProfileSource P (E.sOfTime u)) : ℝ) u) :
    (∀ x : Fin P.D.n → ℝ,
      (∑ i, x i * ν.1 i) ∈ Set.Icc (E.t (-1)) (E.t 1) →
      P.F
          ⟨fun i j ↦
              deriv (deriv E.phi) (∑ k, x k * ν.1 k) * ν.1 i * ν.1 j,
            by
              ext i j
              simp only [Matrix.transpose_apply]
              ring⟩ =
        (P.gamma / P.eta) *
          P.D.beta ((E.phi (∑ i, x i * ν.1 i) + P.sigma) / P.eta)) ∧
      E.q 1 ^ 2 - b ^ 2 =
        PlanarTransitionIncrement P.planarData ν ⟨P.gamma, hγ⟩ ⟨P.eta, P.eta_pos⟩ := by
  constructor
  · exact (lemExactPlanarEquation P ν b b_pos E hphi_first hphi_second).2
  · have hq := E.q_sq 1 (by constructor <;> norm_num)
    rw [hq]
    simp only [add_sub_cancel_left]
    rw [PlanarTransitionIncrement]
    congr 2
    funext s
    have hinv :
        E.Qinv (planarProfileSource P s) =
          planarRankOneOperatorInverse P.planarData.D P.planarData.F ν
            P.planarData.uniformlyElliptic P.planarData.normalized
            ⟨(⟨P.gamma, hγ⟩ : {x : ℝ // 0 < x}) /
                (⟨P.eta, P.eta_pos⟩ : {x : ℝ // 0 < x}) *
                P.planarData.D.beta s,
              mul_nonneg (div_nonneg hγ.le P.eta_pos.le)
                (P.beta_nonnegative s)⟩ := by
      apply (lemPlanarOperatorBounds P.D P.F ν P.uniformlyElliptic
        P.normalized).1.injective
      rw [E.Qinv_right]
      exact (Classical.choose_spec
        (lemPlanarOperatorBounds P.D P.F ν P.uniformlyElliptic
          P.normalized).2.2).1 _ |>.symm
    exact congrArg Subtype.val hinv

end Lea.Lipschitz2
