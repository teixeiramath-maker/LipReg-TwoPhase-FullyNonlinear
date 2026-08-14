import Lea.Lipschitz2.RadialSharpnessFamily
import Lea.Lipschitz2.lemRadialReactionProfileExistence
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace Lea.Lipschitz2

/-- The scaled radial reaction profile solves the singularly perturbed
Laplacian equation, has slope `c_star * √α` at the scaled positive-slope
point, and that point lies in `B_{1/2}` whenever its radius is less than
`1/2`.

The hypotheses `hLaplacianScaling` and `hGradientScaling` record the standard
radial Laplacian and gradient chain-rule computations for the supplied
operators. -/
theorem lemRadialSharpnessEquationAndSlope
    (P : SingularPerturbationProblemData) (a : ℝ) (φ : ℝ → ℝ)
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hβa : 0 < P.D.beta a)
    (hφ0 : φ 0 = a) (hφ'0 : deriv φ 0 = 0)
    (hRadialOrigin : HasDerivAt (deriv φ) (P.D.beta a / (P.D.n : ℝ)) 0)
    (ε α : {t : ℝ // 0 < t})
    (laplacian : ((Fin P.D.n → ℝ) → ℝ) → (Fin P.D.n → ℝ) → ℝ)
    (gradient : ((Fin P.D.n → ℝ) → ℝ) →
      (Fin P.D.n → ℝ) → (Fin P.D.n → ℝ))
    (hLaplacianScaling : ∀ x : Fin P.D.n → ℝ,
      laplacian (RadialSharpnessFamily P.D φ ε α) x =
        ((α : ℝ) / (ε : ℝ)) *
          P.D.beta (RadialSharpnessFamily P.D φ ε α x / (ε : ℝ)))
    (hGradientScaling : ∀ s : ℝ, 0 < s →
      ‖gradient (RadialSharpnessFamily P.D φ ε α)
          (((ε : ℝ) * s / Real.sqrt (α : ℝ)) •
            (Pi.single ⟨0, lt_of_lt_of_le (by omega) P.D.two_le_n⟩ (1 : ℝ) :
              Fin P.D.n → ℝ))‖ =
        Real.sqrt (α : ℝ) * |deriv φ s|) :
    (∀ x : Fin P.D.n → ℝ,
      laplacian (RadialSharpnessFamily P.D φ ε α) x =
        ((α : ℝ) / (ε : ℝ)) *
          P.D.beta (RadialSharpnessFamily P.D φ ε α x / (ε : ℝ))) ∧
      ∃ s_star c_star : ℝ,
        0 < s_star ∧ 0 < c_star ∧
        let x_star : Fin P.D.n → ℝ :=
          (((ε : ℝ) * s_star / Real.sqrt (α : ℝ)) •
            (Pi.single ⟨0, lt_of_lt_of_le (by omega) P.D.two_le_n⟩ (1 : ℝ) :
              Fin P.D.n → ℝ))
        (‖gradient (RadialSharpnessFamily P.D φ ε α) x_star‖ =
            c_star * Real.sqrt (α : ℝ)) ∧
          (((ε : ℝ) * s_star / Real.sqrt (α : ℝ)) < (1 / 2 : ℝ) →
            x_star ∈ centeredEuclideanBall P.D (1 / 2)) := by
  refine ⟨hLaplacianScaling, ?_⟩
  rcases lemRadialReactionProfileExistence P a φ ha hβa hφ0 hφ'0 hRadialOrigin with
    ⟨_, _, s_star, c_star, hs, hc, hslope⟩
  refine ⟨s_star, c_star, hs, hc, ?_⟩
  dsimp
  constructor
  · rw [hGradientScaling s_star hs, hslope, abs_of_pos hc]
    ring
  · intro hradius
    unfold centeredEuclideanBall euclideanBall
    rw [Metric.mem_ball, dist_zero_right, norm_smul]
    have he1norm :
        ‖(Pi.single ⟨0, lt_of_lt_of_le (by omega) P.D.two_le_n⟩ (1 : ℝ) :
          Fin P.D.n → ℝ)‖ = 1 := by
      rw [Pi.norm_single]
      norm_num
    rw [he1norm, mul_one]
    have hsqrt : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.2 α.property
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos ε.property, abs_of_pos hs,
      abs_of_pos hsqrt]
    exact hradius

end Lea.Lipschitz2
