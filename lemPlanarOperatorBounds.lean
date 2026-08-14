import Lea.Lipschitz2.Uniformellipticity
import Lea.Lipschitz2.PlanarRankOneOperator
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Normed.Order.Lattice

namespace Lea.Lipschitz2

/-- The planar rank-one restriction of a normalized uniformly elliptic operator
is increasing onto the nonnegative reals, with quantitative bounds on it and
its inverse. -/
theorem lemPlanarOperatorBounds
    (D : StructuralDataAndNotation) (F : Sn D.n → ℝ)
    (ν : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
    (hF : Uniformellipticity D F) (hF0 : F 0 = 0) :
    StrictMono (PlanarRankOneOperator D F ν) ∧
      (∀ t : {t : ℝ // 0 ≤ t},
        D.lambda * (t : ℝ) ≤ PlanarRankOneOperator D F ν t ∧
          PlanarRankOneOperator D F ν t ≤ D.Lambda * (t : ℝ)) ∧
      ∃ inv : {y : ℝ // 0 ≤ y} → {t : ℝ // 0 ≤ t},
        (∀ y : {y : ℝ // 0 ≤ y},
          PlanarRankOneOperator D F ν (inv y) = (y : ℝ)) ∧
          ∀ y : {y : ℝ // 0 ≤ y},
            (y : ℝ) / D.Lambda ≤ (inv y : ℝ) ∧
              (inv y : ℝ) ≤ (y : ℝ) / D.lambda := by
  let A : ℝ → Sn D.n := fun t ↦
    ⟨fun i j ↦ t * ν.1 i * ν.1 j, by
      ext i j
      simp only [Matrix.transpose_apply]
      ring⟩
  have hA (t : {t : ℝ // 0 ≤ t}) :
      A t = (⟨fun i j ↦ (t : ℝ) * ν.1 i * ν.1 j, by
        ext i j
        simp only [Matrix.transpose_apply]
        ring⟩ : Sn D.n) := rfl
  have hinc (s t : ℝ) (hst : s ≤ t) :
      D.lambda * (t - s) ≤ F (A t) - F (A s) ∧
        F (A t) - F (A s) ≤ D.Lambda * (t - s) := by
    let N : Sn D.n := A (t - s)
    have hd : 0 ≤ t - s := sub_nonneg.mpr hst
    have hN : Matrix.PosSemidef (N : Matrix (Fin D.n) (Fin D.n) ℝ) := by
      constructor
      · ext i j
        simp only [Matrix.conjTranspose_apply, star_id_of_comm, N, A]
        ring
      · intro x
        simp only [N, A, star_id_of_comm, Finsupp.sum]
        have hp : 0 ≤ (t - s) *
            (Finset.sum x.support (fun i ↦ x i * ν.1 i)) ^ 2 :=
          mul_nonneg hd (sq_nonneg _)
        convert hp using 1
        rw [pow_two]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
    have hadd : A s + N = A t := by
      ext i j
      change s * ν.1 i * ν.1 j + (t - s) * ν.1 i * ν.1 j =
        t * ν.1 i * ν.1 j
      ring
    have htr : Matrix.trace (N : Matrix (Fin D.n) (Fin D.n) ℝ) = t - s := by
      change ∑ i, (t - s) * ν.1 i * ν.1 i = t - s
      simp_rw [mul_assoc, ← pow_two]
      rw [← Finset.mul_sum, ν.property, mul_one]
    have he := hF.2 (A s) N hN
    rw [hadd, htr] at he
    exact he
  have hA_zero : A 0 = 0 := by
    ext i j
    simp [A]
  have hbounds : ∀ t : {t : ℝ // 0 ≤ t},
      D.lambda * (t : ℝ) ≤ PlanarRankOneOperator D F ν t ∧
        PlanarRankOneOperator D F ν t ≤ D.Lambda * (t : ℝ) := by
    intro t
    have hi := hinc 0 t t.property
    rw [hA_zero, hF0] at hi
    simpa [PlanarRankOneOperator, A] using hi
  have hstrict : StrictMono (PlanarRankOneOperator D F ν) := by
    intro s t hst
    have hi := (hinc s t hst.le).1
    have hpos : 0 < D.lambda * ((t : ℝ) - (s : ℝ)) :=
      mul_pos D.lambda_pos (sub_pos.mpr hst)
    change F (A s) < F (A t)
    linarith
  have hsurj : ∀ y : {y : ℝ // 0 ≤ y},
      ∃ t : {t : ℝ // 0 ≤ t},
        PlanarRankOneOperator D F ν t = (y : ℝ) := by
    intro y
    let b : ℝ := (y : ℝ) / D.lambda
    have hb : 0 ≤ b := div_nonneg y.property D.lambda_pos.le
    have hcontA : Continuous A := by
      fun_prop
    have hcont : Continuous (fun x : ℝ ↦ F (A x)) := hF.1.comp hcontA
    have hzero : F (A 0) = 0 := by
      simpa [A] using hF0
    have hyb : (y : ℝ) ≤ F (A b) := by
      have hi := (hinc 0 b hb).1
      rw [hzero, sub_zero] at hi
      have hcalc : D.lambda * b = (y : ℝ) := by
        dsimp [b]
        exact mul_div_cancel₀ (y : ℝ) D.lambda_pos.ne'
      linarith
    have hymem : (y : ℝ) ∈ Set.Icc (F (A 0)) (F (A b)) := by
      refine ⟨?_, hyb⟩
      rw [hzero]
      exact y.property
    obtain ⟨t, ht, hty⟩ :=
      intermediate_value_Icc hb hcont.continuousOn hymem
    exact ⟨⟨t, ht.1⟩, by simpa [PlanarRankOneOperator, A] using hty⟩
  refine ⟨hstrict, hbounds, ?_⟩
  classical
  let inv : {y : ℝ // 0 ≤ y} → {t : ℝ // 0 ≤ t} :=
    fun y ↦ Classical.choose (hsurj y)
  refine ⟨inv, ?_, ?_⟩
  · intro y
    exact Classical.choose_spec (hsurj y)
  · intro y
    have heq : PlanarRankOneOperator D F ν (inv y) = (y : ℝ) :=
      Classical.choose_spec (hsurj y)
    have hb := hbounds (inv y)
    have hLambda : 0 < D.Lambda := lt_of_lt_of_le D.lambda_pos D.lambda_le_Lambda
    constructor
    · rw [div_le_iff₀ hLambda]
      rw [← heq]
      simpa [mul_comm] using hb.2
    · rw [le_div_iff₀ D.lambda_pos]
      rw [← heq]
      simpa [mul_comm] using hb.1

end Lea.Lipschitz2
