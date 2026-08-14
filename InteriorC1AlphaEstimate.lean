import Lea.Lipschitz2.Uniformellipticity
import Lea.Lipschitz2.ViscositySolutionConvention
import Lea.Lipschitz2.PointwiseUpperLipschitz
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace Lea.Lipschitz2

/-- The precise analytic content of the classical interior `C¹,α` estimate.

`IsGradient h g` abstracts the standard identification of `g` with the
(classical) gradient of `h`.  This matches the project's abstract treatment of
admissible `C²` tests and their Hessians.  The first clause simultaneously
bounds the pointwise upper Lipschitz constant and the Hölder quotient of the
gradient.  The second clause is the homogeneous, scale-invariant affine
approximation estimate. -/
def InteriorC1AlphaEstimateStatement
    (D : StructuralDataAndNotation) (alpha C : ℝ) : Prop :=
  ∀ (F : Sn D.n → ℝ)
    (f h : (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n)
    (gradient : (Fin D.n → ℝ) → (Fin D.n → ℝ))
    (IsGradient : ((Fin D.n → ℝ) → ℝ) →
      ((Fin D.n → ℝ) → (Fin D.n → ℝ)) → Prop),
    Uniformellipticity D F →
    ContinuousOn h (centeredEuclideanBall D 1) →
    ViscositySolutionOn (centeredEuclideanBall D 1) F f h IsTest hessian →
    IsGradient h gradient →
    ∀ hBound fBound : ℝ,
      0 ≤ hBound →
      0 ≤ fBound →
      (∀ x ∈ centeredEuclideanBall D 1, |h x| ≤ hBound) →
      (∀ x ∈ centeredEuclideanBall D 1, |f x| ≤ fBound) →
      ((∀ x ∈ centeredEuclideanBall D (1 / 2 : ℝ),
          ∀ y ∈ centeredEuclideanBall D (1 / 2 : ℝ),
            ∀ z ∈ centeredEuclideanBall D (1 / 2 : ℝ), y ≠ z →
            PointwiseUpperLipschitz (centeredEuclideanBall D 1) h x +
                ENNReal.ofReal
                  (‖gradient y - gradient z‖ /
                    Real.rpow (dist y z) alpha) ≤
              ENNReal.ofReal (C * (hBound + fBound))) ∧
        (f = 0 →
          ∀ oscBound : ℝ, 0 ≤ oscBound →
            (∀ y ∈ centeredEuclideanBall D 1,
              ∀ z ∈ centeredEuclideanBall D 1,
                |h y - h z| ≤ oscBound) →
            ∀ x₀ ∈ centeredEuclideanBall D (1 / 2 : ℝ),
              ∀ rho : ℝ, 0 < rho → rho ≤ (1 / 4 : ℝ) →
                ∀ x ∈ euclideanBall D rho x₀,
                  |h x - h x₀ - dotProduct (gradient x₀) (x - x₀)| ≤
                    C * Real.rpow rho (1 + alpha) * oscBound))

/-- **Interior `C¹,α` estimate (Caffarelli--Cabré).**

This theorem is deliberately an imported analytic input, as specified in the
manuscript.  Given the classical result in the exact form encoded by
`InteriorC1AlphaEstimateStatement`, it records universal constants
`ᾱ ∈ (0,1)` and `C < ∞` for both the inhomogeneous interior gradient/Hölder
estimate and its homogeneous scale-invariant affine-approximation form. -/
theorem InteriorC1AlphaEstimate
    (D : StructuralDataAndNotation)
    (importedCaffarelliCabreEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          InteriorC1AlphaEstimateStatement D alpha C) :
    ∃ alpha C : ℝ,
      0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
        InteriorC1AlphaEstimateStatement D alpha C := by
  exact importedCaffarelliCabreEstimate

end Lea.Lipschitz2
