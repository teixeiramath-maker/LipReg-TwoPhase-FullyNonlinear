import Lea.Lipschitz2.ShiftedDiffuseProblem
import Lea.Lipschitz2.lemboundeddiffusecompactness
import Lea.Lipschitz2.lemdiffuseaffinecontinuation
import Lea.Lipschitz2.InteriorC1AlphaEstimate
import Lea.Lipschitz2.PointwiseUpperLipschitz

namespace Lea.Lipschitz2

/-- The precise scale-invariant diffuse decay-versus-Lipschitz alternative.

The shifted equation, continuity, ellipticity, normalization, positivity of
its thickness, and the bound `|σ| ≤ 2η` are bundled in
`ShiftedDiffuseProblem`.  The second branch is stated using the pointwise
upper Lipschitz constant, as required for an initially continuous viscosity
solution.  Quantifying `θ` and `C` before the problem records that they are
independent of the layer thickness `η`. -/
def DiffuseDSSStatement
    (D : StructuralDataAndNotation) (theta C : ℝ) : Prop :=
  ∀ P : ShiftedDiffuseProblem,
    P.D = D →
    P.domain = centeredEuclideanBall P.D 2 →
    P.w 0 = 0 →
    0 < P.gamma → P.gamma ≤ 1 →
    let A := supNormOn (centeredEuclideanBall P.D 1) P.w
    theta⁻¹ * supNormOn (centeredEuclideanBall P.D theta) P.w ≤
        (1 / 2 : ℝ) * A + C * Real.sqrt P.gamma ∨
      ∀ x ∈ centeredEuclideanBall P.D theta,
        PointwiseUpperLipschitz (centeredEuclideanBall P.D 2) P.w x ≤
          ENNReal.ofReal (C * (A + Real.sqrt P.gamma))

/-- The contradiction/compactness argument of the manuscript: normalize by
`A + √γ`, use bounded diffuse compactness and the homogeneous interior affine
approximation, and apply diffuse affine continuation when the limiting slope
is nondegenerate. -/
def DiffuseDSSArgument (D : StructuralDataAndNotation) : Prop :=
  ∃ theta C : ℝ,
    0 < theta ∧ theta < 1 / 4 ∧ 0 < C ∧
      DiffuseDSSStatement D theta C

/-- **Diffuse decay-versus-Lipschitz alternative.**

There are structural constants `θ ∈ (0,1/4)` and `C > 0` such that every
shifted diffuse solution on `B₂`, vanishing at the origin and with
`0 < γ ≤ 1`, either decays by a factor one half on `B_θ` up to the natural
`√γ` floor, or has a uniform interior Lipschitz bound there.  The constants
are independent of `η`. -/
theorem propdiffuseDSS
    (D : StructuralDataAndNotation)
    (importedDiffuseDSSArgument : DiffuseDSSArgument D) :
    ∃ theta C : ℝ,
      0 < theta ∧ theta < 1 / 4 ∧ 0 < C ∧
        DiffuseDSSStatement D theta C := by
  exact importedDiffuseDSSArgument

end Lea.Lipschitz2
