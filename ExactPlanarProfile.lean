import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.PlanarRankOneOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Lea.Lipschitz2

/-- The nonnegative argument of the inverse planar rank-one operator appearing
in the exact planar profile. -/
noncomputable def planarProfileSource (P : ShiftedDiffuseProblem) (τ : ℝ) :
    {y : ℝ // 0 ≤ y} :=
  ⟨(P.gamma / P.eta) * P.D.beta τ,
    mul_nonneg (div_nonneg P.gamma_nonnegative P.eta_pos.le)
      (P.beta_nonnegative τ)⟩

/-- An exact planar diffuse profile with incoming slope `b > 0`.

The fields record the positive square-root branch `q`, the increasing time
change `t`, its inverse on the transition interval, and the resulting profile
`φ(t) = η s(t) - σ`.  All integral identities are restricted to the source
interval `[-1,1]`, exactly as in the planar construction. -/
structure ExactPlanarProfile (P : ShiftedDiffuseProblem)
    (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (b : ℝ) (b_pos : 0 < b) where
  Qinv : {y : ℝ // 0 ≤ y} → {r : ℝ // 0 ≤ r}
  Qinv_right : ∀ y,
    PlanarRankOneOperator P.D P.F ν (Qinv y) = (y : ℝ)
  q : ℝ → ℝ
  q_sq : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
    (q s) ^ 2 = b ^ 2 + 2 * P.eta *
      ∫ τ in (-1 : ℝ)..s, (Qinv (planarProfileSource P τ) : ℝ)
  q_left : q (-1) = b
  q_lower : ∀ s ∈ Set.Icc (-1 : ℝ) 1, b ≤ q s
  t : ℝ → ℝ
  t_eq : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
    t s = P.eta * ∫ τ in (0 : ℝ)..s, 1 / q τ
  t_strictMono : ∀ ⦃s₁ s₂ : ℝ⦄,
    s₁ ∈ Set.Icc (-1 : ℝ) 1 →
    s₂ ∈ Set.Icc (-1 : ℝ) 1 → s₁ < s₂ → t s₁ < t s₂
  sOfTime : ℝ → ℝ
  sOfTime_mem : ∀ u ∈ Set.Icc (t (-1)) (t 1),
    sOfTime u ∈ Set.Icc (-1 : ℝ) 1
  sOfTime_left : ∀ s ∈ Set.Icc (-1 : ℝ) 1, sOfTime (t s) = s
  sOfTime_right : ∀ u ∈ Set.Icc (t (-1)) (t 1), t (sOfTime u) = u
  phi : ℝ → ℝ
  phi_eq : ∀ u ∈ Set.Icc (t (-1)) (t 1),
    phi u = P.eta * sOfTime u - P.sigma

end Lea.Lipschitz2
