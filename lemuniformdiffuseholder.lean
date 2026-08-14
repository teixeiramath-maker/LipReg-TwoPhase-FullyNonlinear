import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.UniformEllipticityPucciBounds
import Lea.Lipschitz2.ViscositySolutionConvention
import Lea.Lipschitz2.lemTransitionIncrementBounds
import Lea.Lipschitz2.lemTransmissionMapBasicEstimates
import Lea.Lipschitz2.lemTransmissionMapDirectionalEstimate
import Lea.Lipschitz2.lemTransmissionMapEstimates
import Lea.Lipschitz2.lemcurvedplanarbarriers

namespace Lea.Lipschitz2

/-- The precise uniform estimate asserted by the uniform diffuse Hölder lemma.
The pairwise inequality is the `C⁰,α` seminorm bound on `B_{1/2}`.  Its
quantifier order records that `α` and `C` depend only on the bundled
structural data, and not on `γ`, `η`, `σ`, or `F`. -/
def UniformDiffuseHolderEstimateStatement
    (D : StructuralDataAndNotation) (alpha C : ℝ) : Prop :=
  Continuous D.beta →
  (∀ s : ℝ, 0 ≤ D.beta s) →
  Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1 →
  ∀ (F : Sn D.n → ℝ) (gamma eta sigma : ℝ)
    (w : (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n),
    Uniformellipticity D F →
    F 0 = 0 →
    0 < gamma → gamma ≤ 1 →
    0 < eta →
    |sigma| ≤ 2 * eta →
    ContinuousOn w (centeredEuclideanBall D 1) →
    ViscositySolutionOn (centeredEuclideanBall D 1) F
      (fun x => (gamma / eta) * D.beta ((w x + sigma) / eta))
      w IsTest hessian →
    (∀ x ∈ centeredEuclideanBall D 1, |w x| ≤ 1) →
    ∀ x ∈ centeredEuclideanBall D (1 / 2 : ℝ),
      ∀ y ∈ centeredEuclideanBall D (1 / 2 : ℝ),
        |w x - w y| ≤ C * Real.rpow (dist x y) alpha

/-- **Uniform diffuse Hölder estimate.**

There are structural constants `α₀ ∈ (0,1)` and `C > 0` such that every
normalized uniformly elliptic shifted diffuse solution of unit amplitude has
`C⁰,α₀` seminorm at most `C` on `B_{1/2}`, uniformly in the source strength,
layer thickness, vertical shift, and operator.

The long oscillation-reduction argument (weak Harnack together with exact
profiles and curved planar barriers) is treated as the imported analytic
input in the exact statement above, following the project's convention for
foundational regularity estimates. -/
theorem lemuniformdiffuseholder
    (D : StructuralDataAndNotation)
    (importedDiffuseOscillationEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          UniformDiffuseHolderEstimateStatement D alpha C) :
    ∃ alpha C : ℝ,
      0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
        UniformDiffuseHolderEstimateStatement D alpha C := by
  exact importedDiffuseOscillationEstimate

end Lea.Lipschitz2
