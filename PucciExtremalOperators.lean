import Lea.Lipschitz2.StructuralDataAndNotation
import Mathlib.Analysis.Matrix.Spectrum

namespace Lea.Lipschitz2

/-- The eigenvalues of a real symmetric matrix, indexed by `Fin n`. -/
noncomputable def symmetricEigenvalues {n : ℕ} (M : Sn n) : Fin n → ℝ :=
  (show Matrix.IsHermitian (M : Matrix (Fin n) (Fin n) ℝ) by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa using congrFun (congrFun M.property i) j).eigenvalues

/-- The upper and lower Pucci extremal operators, in that order, for the
ellipticity parameters in `D`. -/
noncomputable def PucciExtremalOperators (D : StructuralDataAndNotation) :
    (Sn D.n → ℝ) × (Sn D.n → ℝ) :=
  ( fun M ↦
      let positiveSum := Finset.univ.sum (fun i ↦
        if 0 < symmetricEigenvalues M i then symmetricEigenvalues M i else 0)
      let negativeSum := Finset.univ.sum (fun i ↦
        if symmetricEigenvalues M i < 0 then symmetricEigenvalues M i else 0)
      D.Lambda * positiveSum + D.lambda * negativeSum,
    fun M ↦
      let positiveSum := Finset.univ.sum (fun i ↦
        if 0 < symmetricEigenvalues M i then symmetricEigenvalues M i else 0)
      let negativeSum := Finset.univ.sum (fun i ↦
        if symmetricEigenvalues M i < 0 then symmetricEigenvalues M i else 0)
      D.lambda * positiveSum + D.Lambda * negativeSum )

/-- The upper Pucci extremal operator `𝒫⁺_{λ,Λ}`. -/
noncomputable abbrev pucciMax (D : StructuralDataAndNotation) : Sn D.n → ℝ :=
  (PucciExtremalOperators D).1

/-- The lower Pucci extremal operator `𝒫⁻_{λ,Λ}`. -/
noncomputable abbrev pucciMin (D : StructuralDataAndNotation) : Sn D.n → ℝ :=
  (PucciExtremalOperators D).2

end Lea.Lipschitz2
