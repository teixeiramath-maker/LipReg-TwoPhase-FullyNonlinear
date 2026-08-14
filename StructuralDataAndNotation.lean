import Mathlib.Analysis.InnerProductSpace.Basic

namespace Lea.Lipschitz2

/-- The fixed dimension, ellipticity parameters, and reaction profile used
throughout the paper. -/
structure StructuralDataAndNotation where
  n : ℕ
  two_le_n : 2 ≤ n
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  lambda_le_Lambda : lambda ≤ Lambda
  beta : ℝ → ℝ

/-- The real vector space of symmetric `n × n` matrices. -/
def symmetricMatrices (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {M | M.transpose = M}
  zero_mem' := by simp
  add_mem' := by
    intro M N hM hN
    change M.transpose = M at hM
    change N.transpose = N at hN
    simp [hM, hN]
  smul_mem' := by
    intro c M hM
    change M.transpose = M at hM
    simp [hM]

/-- The paper's notation `Sⁿ` for real symmetric `n × n` matrices. -/
abbrev Sn (n : ℕ) := symmetricMatrices n

/-- The Euclidean ball `B_r(x₀)` in `ℝⁿ`. -/
def euclideanBall (D : StructuralDataAndNotation) (r : ℝ)
    (x₀ : Fin D.n → ℝ) : Set (Fin D.n → ℝ) :=
  Metric.ball x₀ r

/-- The centered Euclidean ball `B_r = B_r(0)` in `ℝⁿ`. -/
def centeredEuclideanBall (D : StructuralDataAndNotation) (r : ℝ) :
    Set (Fin D.n → ℝ) :=
  euclideanBall D r 0

/-- A universal constant is a positive real whose assertion may depend only
on the bundled structural data `D` (dimension, ellipticity, and `beta`). -/
def UniversalConstant (D : StructuralDataAndNotation)
    (assertion : StructuralDataAndNotation → ℝ → Prop) : Prop :=
  ∃ C : ℝ, 0 < C ∧ assertion D C

end Lea.Lipschitz2
