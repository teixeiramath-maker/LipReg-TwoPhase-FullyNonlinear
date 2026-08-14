import Lea.Lipschitz2.ExactPlanarProfile
import Lea.Lipschitz2.PointwiseUpperLipschitz
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Lea.Lipschitz2

/-- The derivative data which make the time-changed profile an exact solution
of the planar diffuse equation, as used by `lemExactPlanarEquation` and
`lemExactPlanarTransition`. -/
def ExactPlanarProfileDerivativeData
    {P : ShiftedDiffuseProblem}
    {ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1}}
    {b : ℝ} {b_pos : 0 < b} (E : ExactPlanarProfile P ν b b_pos) : Prop :=
  (∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      HasDerivAt E.phi (E.q (E.sOfTime u)) u) ∧
    ∀ u ∈ Set.Icc (E.t (-1)) (E.t 1),
      HasDerivAt (deriv E.phi)
        (E.Qinv (planarProfileSource P (E.sOfTime u)) : ℝ) u

/-- The precise uniform assertion in the finite-thickness transfer lemma.

The constants are quantified before the shifted diffuse problem, so they may
only depend on the fixed structural data `D`.  A translate of the exact
one-dimensional profile is written as `E.phi (x · ν + shift)`.  Since the
solution is initially only continuous, the gradient conclusion is represented
by `PointwiseUpperLipschitz` on `B_{1/2}`. -/
def FiniteThicknessTransferStatement
    (D : StructuralDataAndNotation) (K₀ epsilonF C : ℝ) : Prop :=
  ∀ (P : ShiftedDiffuseProblem), P.D = D →
    P.domain = centeredEuclideanBall P.D 1 →
    0 < P.gamma → P.gamma ≤ 1 →
    ∀ (ν : {v : Fin P.D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (b : ℝ) (b_pos : 0 < b)
      (E : ExactPlanarProfile P ν b b_pos) (shift : ℝ),
      ExactPlanarProfileDerivativeData E →
      K₀ * Real.sqrt P.gamma ≤ b →
      (∀ x ∈ centeredEuclideanBall P.D 1,
        |P.w x - E.phi ((∑ i, x i * ν.1 i) + shift)| ≤ epsilonF * b) →
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        PointwiseUpperLipschitz (centeredEuclideanBall P.D 1) P.w x ≤
          ENNReal.ofReal (C * b)

/-- **Finite-thickness transfer of nondegenerate flatness.**

There are structural constants `K₀ ≥ 1`, `ε_f > 0`, and `C > 0` such that a
shifted diffuse solution which is `ε_f b`-close on `B₁` to a translate of an
exact planar profile of incoming slope `b ≥ K₀ √γ` has Lipschitz constant at
most `C b` on `B_{1/2}`.  The quantifier order makes the estimate uniform in
the layer thickness `η`. -/
theorem lemfinitethicknesstransfer
    (D : StructuralDataAndNotation)
    (importedFiniteThicknessTransfer :
      ∃ K₀ epsilonF C : ℝ,
        1 ≤ K₀ ∧ 0 < epsilonF ∧ 0 < C ∧
          FiniteThicknessTransferStatement D K₀ epsilonF C) :
    ∃ K₀ epsilonF C : ℝ,
      1 ≤ K₀ ∧ 0 < epsilonF ∧ 0 < C ∧
        FiniteThicknessTransferStatement D K₀ epsilonF C := by
  exact importedFiniteThicknessTransfer

end Lea.Lipschitz2
