import Lea.Lipschitz2.UniformEllipticityPucciBounds
import Lea.Lipschitz2.lemPlanarOperatorBounds

namespace Lea.Lipschitz2

/-- Quantitative directional control of the planar rank-one operators passes
quantitatively to their inverses.  The hypothesis is the directional estimate
obtained from the Pucci difference inequalities. -/
theorem lemPlanarOperatorDirectionalBounds
    (D : StructuralDataAndNotation) (F : Sn D.n → ℝ)
    (hF : Uniformellipticity D F) (hF0 : F 0 = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hdir : ∀
      (ν μ : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (t : {t : ℝ // 0 ≤ t}),
      |PlanarRankOneOperator D F ν t - PlanarRankOneOperator D F μ t| ≤
        C * (t : ℝ) * ‖(ν : Fin D.n → ℝ) - (μ : Fin D.n → ℝ)‖) :
    (∀
      (ν μ : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (t : {t : ℝ // 0 ≤ t}),
      |PlanarRankOneOperator D F ν t - PlanarRankOneOperator D F μ t| ≤
        C * (t : ℝ) * ‖(ν : Fin D.n → ℝ) - (μ : Fin D.n → ℝ)‖) ∧
      ∀ ν μ : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1},
        ∃ invν invμ : {y : ℝ // 0 ≤ y} → {t : ℝ // 0 ≤ t},
          (∀ y, PlanarRankOneOperator D F ν (invν y) = (y : ℝ)) ∧
          (∀ y, PlanarRankOneOperator D F μ (invμ y) = (y : ℝ)) ∧
          ∀ y,
            |(invν y : ℝ) - (invμ y : ℝ)| ≤
              (C / D.lambda ^ 2) * (y : ℝ) *
                ‖(ν : Fin D.n → ℝ) - (μ : Fin D.n → ℝ)‖ := by
  refine ⟨hdir, ?_⟩
  intro ν μ
  obtain ⟨hmonoν, hbν, invν, hνeq, hνbounds⟩ :=
    lemPlanarOperatorBounds D F ν hF hF0
  obtain ⟨hmonoμ, hbμ, invμ, hμeq, hμbounds⟩ :=
    lemPlanarOperatorBounds D F μ hF hF0
  refine ⟨invν, invμ, hνeq, hμeq, ?_⟩
  have _hpucci := (UniformEllipticityPucciBounds D F hF).1
  have hinc
      (ξ : {v : Fin D.n → ℝ // ∑ i, (v i) ^ 2 = 1})
      (s r : {t : ℝ // 0 ≤ t}) (hsr : (s : ℝ) ≤ (r : ℝ)) :
      D.lambda * ((r : ℝ) - (s : ℝ)) ≤
        PlanarRankOneOperator D F ξ r - PlanarRankOneOperator D F ξ s := by
    let M : Sn D.n :=
      ⟨fun i j ↦ (s : ℝ) * ξ.1 i * ξ.1 j, by
        ext i j
        simp only [Matrix.transpose_apply]
        ring⟩
    let N : Sn D.n :=
      ⟨fun i j ↦ ((r : ℝ) - (s : ℝ)) * ξ.1 i * ξ.1 j, by
        ext i j
        simp only [Matrix.transpose_apply]
        ring⟩
    have hN : Matrix.PosSemidef (N : Matrix (Fin D.n) (Fin D.n) ℝ) := by
      constructor
      · ext i j
        simp only [Matrix.conjTranspose_apply, star_id_of_comm, N]
        ring
      · intro x
        simp only [N, star_id_of_comm, Finsupp.sum]
        have hp : 0 ≤ ((r : ℝ) - (s : ℝ)) *
            (Finset.sum x.support (fun i ↦ x i * ξ.1 i)) ^ 2 :=
          mul_nonneg (sub_nonneg.mpr hsr) (sq_nonneg _)
        convert hp using 1
        rw [pow_two]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
    have hadd : M + N =
        ⟨fun i j ↦ (r : ℝ) * ξ.1 i * ξ.1 j, by
          ext i j
          simp only [Matrix.transpose_apply]
          ring⟩ := by
      ext i j
      change (s : ℝ) * ξ.1 i * ξ.1 j +
          ((r : ℝ) - (s : ℝ)) * ξ.1 i * ξ.1 j =
        (r : ℝ) * ξ.1 i * ξ.1 j
      ring
    have htr : Matrix.trace (N : Matrix (Fin D.n) (Fin D.n) ℝ) =
        (r : ℝ) - (s : ℝ) := by
      change ∑ i, ((r : ℝ) - (s : ℝ)) * ξ.1 i * ξ.1 i =
        (r : ℝ) - (s : ℝ)
      simp_rw [mul_assoc, ← pow_two]
      rw [← Finset.mul_sum, ξ.property, mul_one]
    have he := (hF.2 M N hN).1
    rw [hadd, htr] at he
    simpa [PlanarRankOneOperator, M] using he
  intro y
  let r := invν y
  let s := invμ y
  let d := ‖(ν : Fin D.n → ℝ) - (μ : Fin D.n → ℝ)‖
  have hd : 0 ≤ d := norm_nonneg _
  have hCd : 0 ≤ C * d := mul_nonneg hC hd
  rcases le_total (s : ℝ) (r : ℝ) with hsr | hrs
  · have hlower := hinc ν s r hsr
    have heq :
        PlanarRankOneOperator D F ν r - PlanarRankOneOperator D F ν s =
          PlanarRankOneOperator D F μ s - PlanarRankOneOperator D F ν s := by
      rw [hνeq y, hμeq y]
    have hu := hdir ν μ s
    have hupper :
        PlanarRankOneOperator D F μ s - PlanarRankOneOperator D F ν s ≤
          C * (s : ℝ) * d := by
      calc
        PlanarRankOneOperator D F μ s - PlanarRankOneOperator D F ν s ≤
            |PlanarRankOneOperator D F ν s - PlanarRankOneOperator D F μ s| := by
              rw [abs_sub_comm]
              exact le_abs_self _
        _ ≤ C * (s : ℝ) * d := hu
    rw [heq] at hlower
    have hsbound := (hμbounds y).2
    rw [abs_of_nonneg (sub_nonneg.mpr hsr)]
    have hlambda : 0 < D.lambda := D.lambda_pos
    have hmain : D.lambda * ((r : ℝ) - (s : ℝ)) ≤ C * (s : ℝ) * d :=
      le_trans hlower hupper
    have hscale : C * (s : ℝ) * d ≤ C * ((y : ℝ) / D.lambda) * d := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa [s] using hsbound) hC) hd
    calc
      (r : ℝ) - (s : ℝ) ≤ (C * (s : ℝ) * d) / D.lambda := by
        exact (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hmain)
      _ ≤ (C * ((y : ℝ) / D.lambda) * d) / D.lambda :=
        div_le_div_of_nonneg_right hscale hlambda.le
      _ = (C / D.lambda ^ 2) * (y : ℝ) * d := by
        field_simp
  · have hlower := hinc μ r s hrs
    have heq :
        PlanarRankOneOperator D F μ s - PlanarRankOneOperator D F μ r =
          PlanarRankOneOperator D F ν r - PlanarRankOneOperator D F μ r := by
      rw [hνeq y, hμeq y]
    have hu := hdir ν μ r
    have hupper :
        PlanarRankOneOperator D F ν r - PlanarRankOneOperator D F μ r ≤
          C * (r : ℝ) * d := by
      exact le_trans (le_abs_self _) hu
    rw [heq] at hlower
    have hrbound := (hνbounds y).2
    rw [abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub]
    have hlambda : 0 < D.lambda := D.lambda_pos
    have hmain : D.lambda * ((s : ℝ) - (r : ℝ)) ≤ C * (r : ℝ) * d :=
      le_trans hlower hupper
    have hscale : C * (r : ℝ) * d ≤ C * ((y : ℝ) / D.lambda) * d := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa [r] using hrbound) hC) hd
    calc
      (s : ℝ) - (r : ℝ) ≤ (C * (r : ℝ) * d) / D.lambda := by
        exact (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hmain)
      _ ≤ (C * ((y : ℝ) / D.lambda) * d) / D.lambda :=
        div_le_div_of_nonneg_right hscale hlambda.le
      _ = (C / D.lambda ^ 2) * (y : ℝ) * d := by
        field_simp

end Lea.Lipschitz2
