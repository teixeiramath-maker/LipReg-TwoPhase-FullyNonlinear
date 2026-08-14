import Lea.Lipschitz2.Uniformellipticity
import Lea.Lipschitz2.PucciExtremalOperators
import Mathlib.Data.Real.StarOrdered

namespace Lea.Lipschitz2

private lemma conjugate_diagonal_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℝ) (d : n → ℝ) (hd : 0 ≤ d) :
    Matrix.PosSemidef (((star U : Matrix.unitaryGroup n ℝ) : Matrix n n ℝ) * Matrix.diagonal d * (U : Matrix n n ℝ)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · intro x
    have heq :
        star x ⬝ᵥ Matrix.mulVec (((star U : Matrix.unitaryGroup n ℝ) : Matrix n n ℝ) *
          Matrix.diagonal d * (U : Matrix n n ℝ)) x =
          ∑ k, d k * (∑ i, (U : Matrix n n ℝ) k i * x i) ^ 2 := by
      simp [Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal_apply, dotProduct,
        Finset.mul_sum, Finset.sum_mul]
      conv_lhs =>
        congr
        · skip
        · ext a
          rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [heq]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hd i) (sq_nonneg _)

/-- Uniform ellipticity bounds every operator increment between the lower and
upper Pucci extremal operators; normalization at zero gives the corresponding
pointwise bounds. -/
theorem UniformEllipticityPucciBounds (D : StructuralDataAndNotation)
    (F : Sn D.n → ℝ) (hF : Uniformellipticity D F) :
    (∀ M N : Sn D.n,
      pucciMin D (M - N) ≤ F M - F N ∧
      F M - F N ≤ pucciMax D (M - N)) ∧
    (F 0 = 0 → ∀ M : Sn D.n,
      pucciMin D M ≤ F M ∧ F M ≤ pucciMax D M) := by
  have hdiff : ∀ M N : Sn D.n,
      pucciMin D (M - N) ≤ F M - F N ∧
      F M - F N ≤ pucciMax D (M - N) := by
    intro M N
    let A : Sn D.n := M - N
    have hA : Matrix.IsHermitian (A : Matrix (Fin D.n) (Fin D.n) ℝ) := by
      apply Matrix.IsHermitian.ext
      intro i j
      simpa [A] using congrFun (congrFun A.property i) j
    let U := hA.eigenvectorUnitary
    let p : Fin D.n → ℝ := fun i ↦ if 0 < hA.eigenvalues i then hA.eigenvalues i else 0
    let q : Fin D.n → ℝ := fun i ↦ if hA.eigenvalues i < 0 then -hA.eigenvalues i else 0
    let Pm : Matrix (Fin D.n) (Fin D.n) ℝ :=
      (U : Matrix _ _ ℝ) * Matrix.diagonal p *
        ((star U : Matrix.unitaryGroup (Fin D.n) ℝ) : Matrix _ _ ℝ)
    let Qm : Matrix (Fin D.n) (Fin D.n) ℝ :=
      (U : Matrix _ _ ℝ) * Matrix.diagonal q *
        ((star U : Matrix.unitaryGroup (Fin D.n) ℝ) : Matrix _ _ ℝ)
    have hp : 0 ≤ p := by
      intro i
      simp [p]
      split_ifs <;> linarith
    have hq : 0 ≤ q := by
      intro i
      simp [q]
      split_ifs <;> linarith
    have hPm : Matrix.PosSemidef Pm := by
      simpa [Pm] using conjugate_diagonal_posSemidef (star U) p hp
    have hQm : Matrix.PosSemidef Qm := by
      simpa [Qm] using conjugate_diagonal_posSemidef (star U) q hq
    let P : Sn D.n := ⟨Pm, by simpa [Matrix.IsHermitian] using hPm.1⟩
    let Q : Sn D.n := ⟨Qm, by simpa [Matrix.IsHermitian] using hQm.1⟩
    have hdecomp : A = P - Q := by
      apply Subtype.ext
      rw [hA.spectral_theorem]
      simp only [P, Q, Pm, Qm, U, Submodule.coe_sub]
      ext i j
      simp [Matrix.mul_apply, Matrix.diagonal_apply, p, q]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with hpos hneg
      · exfalso
        linarith
      · ring
      · ring
      · have hz : hA.eigenvalues k = 0 := by linarith
        simp [hz]
    have htrP : Matrix.trace Pm = ∑ i, p i := by
      simp [Pm, Matrix.trace_mul_cycle]
    have htrQ : Matrix.trace Qm = ∑ i, q i := by
      simp [Qm, Matrix.trace_mul_cycle]
    have hpos := hF.2 (N - Q) P (by simpa [P] using hPm)
    have hneg := hF.2 (N - Q) Q (by simpa [Q] using hQm)
    have hMN : M = (N - Q) + P := by
      calc
        M = N + A := by simp [A]
        _ = N + (P - Q) := by rw [hdecomp]
        _ = (N - Q) + P := by abel
    have hN : (N - Q) + Q = N := by abel
    rw [← hMN] at hpos
    rw [hN] at hneg
    have heig : symmetricEigenvalues A = hA.eigenvalues := by
      unfold symmetricEigenvalues
      congr
    let ps : ℝ := Finset.univ.sum (fun i ↦
      if 0 < hA.eigenvalues i then hA.eigenvalues i else 0)
    let ns : ℝ := Finset.univ.sum (fun i ↦
      if hA.eigenvalues i < 0 then hA.eigenvalues i else 0)
    have hpucciMin : pucciMin D A = D.lambda * ps + D.Lambda * ns := by
      simp [pucciMin, PucciExtremalOperators, ps, ns, heig]
    have hpucciMax : pucciMax D A = D.Lambda * ps + D.lambda * ns := by
      simp [pucciMax, PucciExtremalOperators, ps, ns, heig]
    have hpsum : (∑ i, p i) = ps := by simp [p, ps]
    have hqsum : (∑ i, q i) = -ns := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : hA.eigenvalues i < 0 <;> simp [q, h]
    have hmin : pucciMin D A = D.lambda * Matrix.trace Pm - D.Lambda * Matrix.trace Qm := by
      rw [hpucciMin, htrP, htrQ, hpsum, hqsum]
      ring
    have hmax : pucciMax D A = D.Lambda * Matrix.trace Pm - D.lambda * Matrix.trace Qm := by
      rw [hpucciMax, htrP, htrQ, hpsum, hqsum]
      ring
    change pucciMin D A ≤ F M - F N ∧ F M - F N ≤ pucciMax D A
    rw [hmin, hmax]
    change D.lambda * Matrix.trace (P : Matrix (Fin D.n) (Fin D.n) ℝ) -
        D.Lambda * Matrix.trace (Q : Matrix (Fin D.n) (Fin D.n) ℝ) ≤ F M - F N ∧
      F M - F N ≤ D.Lambda * Matrix.trace (P : Matrix (Fin D.n) (Fin D.n) ℝ) -
        D.lambda * Matrix.trace (Q : Matrix (Fin D.n) (Fin D.n) ℝ)
    constructor <;> linarith [hpos.1, hpos.2, hneg.1, hneg.2]
  constructor
  · exact hdiff
  · intro h0 M
    simpa [h0] using hdiff M 0

end Lea.Lipschitz2
