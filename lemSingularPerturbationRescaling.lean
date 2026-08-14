import Lea.Lipschitz2.SingularPerturbationRescaling
import Lea.Lipschitz2.SingularPerturbationProblemData
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Lea.Lipschitz2

/-- Rescaling preserves normalization and ellipticity, and transforms the
singular perturbation equation with `γ = r² α / A²`, `δ = ε / A`, and
`σ = c / A`.  The hypothesis relating `Hu` and `Hv` is the Hessian chain
rule `D²u(x₀ + r x) = (A / r²) D²v(x)`. -/
theorem lemSingularPerturbationRescaling
    (P : SingularPerturbationProblemData)
    (u : (Fin P.D.n → ℝ) → ℝ) (x₀ : Fin P.D.n → ℝ)
    (r A : {t : ℝ // 0 < t}) (c : ℝ) :
    let v := singularPerturbationRescaledFunction P.D u P.F x₀ r A c
    let FrA := singularPerturbationRescaledOperator P.D u P.F x₀ r A c
    let gamma := (r : ℝ) ^ 2 * P.alpha / (A : ℝ) ^ 2
    let delta := P.epsilon / (A : ℝ)
    let sigma := c / (A : ℝ)
    FrA 0 = 0 ∧
      Uniformellipticity P.D FrA ∧
      ∀ (x : Fin P.D.n → ℝ) (Hu Hv : Sn P.D.n),
        Hu = ((A : ℝ) / (r : ℝ) ^ 2) • Hv →
        P.F Hu = (P.alpha / P.epsilon) *
          P.D.beta (u (x₀ + (r : ℝ) • x) / P.epsilon) →
        FrA Hv = (gamma / delta) *
          P.D.beta ((v x + sigma) / delta) := by
  dsimp
  constructor
  · simp [singularPerturbationRescaledOperator,
      SingularPerturbationRescaling, P.normalized]
  constructor
  · rcases P.uniformlyElliptic with ⟨hcont, hell⟩
    constructor
    · dsimp [singularPerturbationRescaledOperator,
        SingularPerturbationRescaling]
      fun_prop
    · intro M N hN
      have hr2 : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos r.property
      have hk : 0 ≤ (A : ℝ) / (r : ℝ) ^ 2 :=
        le_of_lt (div_pos A.property hr2)
      have hscaledN : Matrix.PosSemidef
          ((((A : ℝ) / (r : ℝ) ^ 2) • N : Sn P.D.n) :
            Matrix (Fin P.D.n) (Fin P.D.n) ℝ) := by
        exact hN.smul hk
      obtain ⟨hlower, hupper⟩ :=
        hell (((A : ℝ) / (r : ℝ) ^ 2) • M)
          (((A : ℝ) / (r : ℝ) ^ 2) • N) hscaledN
      have htrace :
          Matrix.trace
              ((((A : ℝ) / (r : ℝ) ^ 2) • N : Sn P.D.n) :
                Matrix (Fin P.D.n) (Fin P.D.n) ℝ) =
            ((A : ℝ) / (r : ℝ) ^ 2) *
              Matrix.trace (N : Matrix (Fin P.D.n) (Fin P.D.n) ℝ) := by
        rw [show ((((A : ℝ) / (r : ℝ) ^ 2) • N : Sn P.D.n) :
              Matrix (Fin P.D.n) (Fin P.D.n) ℝ) =
            ((A : ℝ) / (r : ℝ) ^ 2) •
              (N : Matrix (Fin P.D.n) (Fin P.D.n) ℝ) from rfl,
          Matrix.trace_smul]
        simp
      rw [htrace] at hlower hupper
      have hscale : 0 ≤ (r : ℝ) ^ 2 / (A : ℝ) :=
        le_of_lt (div_pos hr2 A.property)
      have hr0 : (r : ℝ) ≠ 0 := ne_of_gt r.property
      have hA0 : (A : ℝ) ≠ 0 := ne_of_gt A.property
      dsimp [singularPerturbationRescaledOperator,
        SingularPerturbationRescaling]
      constructor
      · calc
          P.D.lambda * Matrix.trace (N : Matrix (Fin P.D.n) (Fin P.D.n) ℝ) =
              ((r : ℝ) ^ 2 / (A : ℝ)) *
                (P.D.lambda * (((A : ℝ) / (r : ℝ) ^ 2) *
                  Matrix.trace (N : Matrix (Fin P.D.n) (Fin P.D.n) ℝ))) := by
                    field_simp [hr0, hA0]
          _ ≤ ((r : ℝ) ^ 2 / (A : ℝ)) *
                (P.F (((A : ℝ) / (r : ℝ) ^ 2) • M +
                    ((A : ℝ) / (r : ℝ) ^ 2) • N) -
                  P.F (((A : ℝ) / (r : ℝ) ^ 2) • M)) :=
                    mul_le_mul_of_nonneg_left hlower hscale
          _ = ((r : ℝ) ^ 2 / (A : ℝ)) *
                P.F (((A : ℝ) / (r : ℝ) ^ 2) • (M + N)) -
              ((r : ℝ) ^ 2 / (A : ℝ)) *
                P.F (((A : ℝ) / (r : ℝ) ^ 2) • M) := by
                  simp only [smul_add]
                  ring
      · calc
          ((r : ℝ) ^ 2 / (A : ℝ)) *
                P.F (((A : ℝ) / (r : ℝ) ^ 2) • (M + N)) -
              ((r : ℝ) ^ 2 / (A : ℝ)) *
                P.F (((A : ℝ) / (r : ℝ) ^ 2) • M) =
              ((r : ℝ) ^ 2 / (A : ℝ)) *
                (P.F (((A : ℝ) / (r : ℝ) ^ 2) • M +
                    ((A : ℝ) / (r : ℝ) ^ 2) • N) -
                  P.F (((A : ℝ) / (r : ℝ) ^ 2) • M)) := by
                    simp only [smul_add]
                    ring
          _ ≤ ((r : ℝ) ^ 2 / (A : ℝ)) *
                (P.D.Lambda * (((A : ℝ) / (r : ℝ) ^ 2) *
                  Matrix.trace (N : Matrix (Fin P.D.n) (Fin P.D.n) ℝ))) :=
                    mul_le_mul_of_nonneg_left hupper hscale
          _ = P.D.Lambda *
                Matrix.trace (N : Matrix (Fin P.D.n) (Fin P.D.n) ℝ) := by
                  field_simp [hr0, hA0]
  · intro x Hu Hv hessianScale equationAtPoint
    subst Hu
    dsimp [singularPerturbationRescaledOperator,
      singularPerturbationRescaledFunction, SingularPerturbationRescaling]
    rw [equationAtPoint]
    have hε0 : P.epsilon ≠ 0 := ne_of_gt P.epsilon_pos
    have hA0 : (A : ℝ) ≠ 0 := ne_of_gt A.property
    have hcoef :
        ((r : ℝ) ^ 2 / (A : ℝ)) * (P.alpha / P.epsilon) =
          ((r : ℝ) ^ 2 * P.alpha / (A : ℝ) ^ 2) /
            (P.epsilon / (A : ℝ)) := by
      field_simp [hε0, hA0]
    have harg :
        u (x₀ + (r : ℝ) • x) / P.epsilon =
          (((u (x₀ + (r : ℝ) • x) - c) / (A : ℝ) + c / (A : ℝ)) /
            (P.epsilon / (A : ℝ))) := by
      field_simp [hε0, hA0]
      ring
    calc
      ((r : ℝ) ^ 2 / (A : ℝ)) *
          ((P.alpha / P.epsilon) *
            P.D.beta (u (x₀ + (r : ℝ) • x) / P.epsilon)) =
        (((r : ℝ) ^ 2 / (A : ℝ)) * (P.alpha / P.epsilon)) *
          P.D.beta (u (x₀ + (r : ℝ) • x) / P.epsilon) := by ring
      _ = (((r : ℝ) ^ 2 * P.alpha / (A : ℝ) ^ 2) /
            (P.epsilon / (A : ℝ))) *
          P.D.beta (u (x₀ + (r : ℝ) • x) / P.epsilon) := by rw [hcoef]
      _ = (((r : ℝ) ^ 2 * P.alpha / (A : ℝ) ^ 2) /
            (P.epsilon / (A : ℝ))) *
          P.D.beta (((u (x₀ + (r : ℝ) • x) - c) / (A : ℝ) + c / (A : ℝ)) /
            (P.epsilon / (A : ℝ))) := by rw [harg]

end Lea.Lipschitz2
