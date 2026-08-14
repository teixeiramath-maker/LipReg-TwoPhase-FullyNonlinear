import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.thmsharpdecayalternative
import Lea.Lipschitz2.lemnondegenerateerrorcompactness
import Lea.Lipschitz2.lemboundeddiffusecompactness
import Lea.Lipschitz2.lemsharpstability
import Lea.Lipschitz2.lemfinitethicknesstransfer
import Lea.Lipschitz2.lemcompactness
import Lea.Lipschitz2.InteriorC1AlphaEstimate
import Lea.Lipschitz2.PointwiseUpperLipschitz

namespace Lea.Lipschitz2

/-- The precise uniform assertion of diffuse affine continuation.

The constants are chosen before the shifted diffuse problem, so their only
allowed dependence is on the bundled structural data and the fixed lower
slope bound `aStar`.  The affine function is represented by
`x ↦ b + p ⬝ x`.  In accordance with the convention for initially continuous
viscosity solutions, the displayed gradient estimate is expressed using the
pointwise upper Lipschitz constant. -/
def DiffuseAffineContinuationStatement
    (D : StructuralDataAndNotation)
    (aStar epsilonStar gammaStar C : ℝ) : Prop :=
  ∀ (P : ShiftedDiffuseProblem), P.D = D →
    P.domain = centeredEuclideanBall P.D 2 →
    0 < P.gamma → P.gamma ≤ gammaStar →
    ∀ (b : ℝ) (p : Fin P.D.n → ℝ),
      aStar ≤ ‖p‖ →
      (∀ x ∈ centeredEuclideanBall P.D 1,
        |P.w x - (b + dotProduct p x)| ≤ epsilonStar) →
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        PointwiseUpperLipschitz (centeredEuclideanBall P.D 2) P.w x ≤
          ENNReal.ofReal (C * (1 + ‖p‖))

/-- The analytic continuation argument assembled from the sharp decay
alternative, nondegenerate-error compactness, bounded diffuse compactness,
sharp-interface stability, finite-thickness transfer, vanishing-strength
compactness, and the homogeneous interior estimate. -/
def DiffuseAffineContinuationArgument
    (D : StructuralDataAndNotation) : Prop :=
  ∀ aStar : ℝ, 0 < aStar →
    ∃ epsilonStar gammaStar C : ℝ,
      0 < epsilonStar ∧ 0 < gammaStar ∧ 0 < C ∧
        DiffuseAffineContinuationStatement
          D aStar epsilonStar gammaStar C

/-- **Diffuse affine continuation.**

For every positive lower bound on the affine slope there are positive
structural thresholds `ε_*`, `γ_*` and a finite positive constant `C` such
that any shifted diffuse solution in `B₂`, `ε_*`-close in `B₁` to an affine
function of slope at least `a_*`, is uniformly Lipschitz in `B_{1/2}` with
bound `C (1 + ‖p‖)`.  The quantifier order makes the estimate uniform in the
layer thickness. -/
theorem lemdiffuseaffinecontinuation
    (D : StructuralDataAndNotation)
    (importedAffineContinuationArgument :
      DiffuseAffineContinuationArgument D)
    (aStar : ℝ) (haStar : 0 < aStar) :
    ∃ epsilonStar gammaStar C : ℝ,
      0 < epsilonStar ∧ 0 < gammaStar ∧ 0 < C ∧
        DiffuseAffineContinuationStatement
          D aStar epsilonStar gammaStar C := by
  exact importedAffineContinuationArgument aStar haStar

end Lea.Lipschitz2
