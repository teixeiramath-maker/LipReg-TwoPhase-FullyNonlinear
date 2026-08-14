import Lea.Lipschitz2.ExactPlanarProfile
import Lea.Lipschitz2.lemPlanarOperatorBounds
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Lea.Lipschitz2

/-- The derivative identities for an exact planar profile imply that its
rank-one extension solves the shifted diffuse equation throughout the
transition interval. -/
theorem lemExactPlanarEquation
    (P : ShiftedDiffuseProblem)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (b : ℝ) (b_pos : 0 < b)
    (E : ExactPlanarProfile P ν b b_pos)
    (hphi_first : ∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      HasDerivAt E.phi (E.q (E.sOfTime u)) u)
    (hphi_second : ∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      HasDerivAt (deriv E.phi)
        (E.Qinv (planarProfileSource P (E.sOfTime u)) : ℝ) u) :
    (∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      deriv E.phi u = E.q (E.sOfTime u) ∧
      deriv (deriv E.phi) u =
        (E.Qinv (planarProfileSource P (E.sOfTime u)) : ℝ) ∧
      E.sOfTime u = (E.phi u + P.sigma) / P.eta) ∧
    ∀ x : Fin P.D.n → ℝ,
      (∑ i, x i * ν.1 i) ∈ Set.Icc (E.t (-1)) (E.t 1) →
      P.F
          ⟨fun i j ↦
              deriv (deriv E.phi) (∑ k, x k * ν.1 k) * ν.1 i * ν.1 j,
            by
              ext i j
              simp only [Matrix.transpose_apply]
              ring⟩ =
        (P.gamma / P.eta) *
          P.D.beta ((E.phi (∑ i, x i * ν.1 i) + P.sigma) / P.eta) := by
  constructor
  · intro u hu
    have hcoord : E.sOfTime u = (E.phi u + P.sigma) / P.eta := by
      rw [E.phi_eq u hu]
      field_simp [ne_of_gt P.eta_pos]
      ring
    exact ⟨(hphi_first u hu).deriv, (hphi_second u hu).deriv, hcoord⟩
  · intro x hx
    let u : ℝ := ∑ i, x i * ν.1 i
    have hcoord : E.sOfTime u = (E.phi u + P.sigma) / P.eta := by
      rw [E.phi_eq u hx]
      field_simp [ne_of_gt P.eta_pos]
      ring
    have hsecond : deriv (deriv E.phi) u =
        (E.Qinv (planarProfileSource P (E.sOfTime u)) : ℝ) :=
      (hphi_second u hx).deriv
    rw [show (∑ i, x i * ν.1 i) = u by rfl]
    rw [hsecond]
    change PlanarRankOneOperator P.D P.F ν
        (E.Qinv (planarProfileSource P (E.sOfTime u))) = _
    rw [E.Qinv_right]
    simp only [planarProfileSource, Subtype.coe_mk]
    rw [hcoord]

end Lea.Lipschitz2
