import Lea.Lipschitz2.SingularPerturbationProblemData
import Lea.Lipschitz2.Reduction
import Lea.Lipschitz2.PointwiseUpperLipschitz

namespace Lea.Lipschitz2

/-- **Uniform Lipschitz estimate.**

For a continuous viscosity solution of the singular perturbation problem, the
pointwise upper-Lipschitz constant on `B_{1/2}` is bounded by a universal
multiple of its `L∞` bound on `B₁` plus `sqrt α`.  The pointwise
upper-Lipschitz formulation is the appropriate interpretation of the gradient
norm before Lipschitz regularity has been established. -/
theorem MainLipschitzEstimate
    (P : SingularPerturbationProblemData)
    (u : (Fin P.D.n → ℝ) → ℝ)
    (IsTest : (((Fin P.D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin P.D.n → ℝ) → ℝ) → (Fin P.D.n → ℝ) → Sn P.D.n)
    (hu : P.IsSolution u IsTest hessian)
    (uBound : ℝ) (huBound_nonneg : 0 ≤ uBound)
    (huBound : ∀ x ∈ centeredEuclideanBall P.D 1, |u x| ≤ uBound)
    (normalizedEstimate :
      ∀ Q : NormalizedDiffuseProblem,
        ∃ C : ℝ, 0 < C ∧
          ∀ x ∈ centeredEuclideanBall Q.D (1 / 2 : ℝ),
            PointwiseUpperLipschitz
                (centeredEuclideanBall Q.D (3 / 4 : ℝ)) Q.v x ≤
              ENNReal.ofReal C)
    (interiorFallback :
      P.alpha = 0 ∨ P.epsilon > uBound + Real.sqrt P.alpha →
        ∃ C : ℝ, 0 < C ∧
          ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
            PointwiseUpperLipschitz
                (centeredEuclideanBall P.D (3 / 4 : ℝ)) u x ≤
              ENNReal.ofReal C *
                ENNReal.ofReal (uBound + Real.sqrt P.alpha)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) u x ≤
          ENNReal.ofReal C *
            ENNReal.ofReal (uBound + Real.sqrt P.alpha) := by
  exact Reduction P u IsTest hessian hu uBound huBound_nonneg huBound
    normalizedEstimate interiorFallback

end Lea.Lipschitz2
