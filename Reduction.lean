import Lea.Lipschitz2.SingularPerturbationProblemData
import Lea.Lipschitz2.NormalizedEstimate
import Lea.Lipschitz2.lemSingularPerturbationRescaling
import Lea.Lipschitz2.InteriorC1AlphaEstimate
import Lea.Lipschitz2.PointwiseUpperLipschitz
import Mathlib.Order.Filter.ENNReal
import Mathlib.Analysis.Normed.MulAction

namespace Lea.Lipschitz2

/-- Reduction of the general singular-perturbation estimate to the normalized
estimate.  `interiorFallback` is precisely the consequence of the imported
interior `C¹,α` estimate used when `α = 0` or when the normalized thickness is
larger than one. -/
theorem Reduction
    (P : SingularPerturbationProblemData)
    (u : (Fin P.D.n → ℝ) → ℝ)
    (IsTest : (((Fin P.D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin P.D.n → ℝ) → ℝ) → (Fin P.D.n → ℝ) → Sn P.D.n)
    (hu : P.IsSolution u IsTest hessian)
    (uBound : ℝ) (huBound_nonneg : 0 ≤ uBound)
    (huBound : ∀ x ∈ centeredEuclideanBall P.D 1, |u x| ≤ uBound)
    (normalizedEstimate :
      ∀ Q : NormalizedDiffuseProblem,
        ∃ C : ℝ, 0 < C ∧
          ∀ x ∈ centeredEuclideanBall Q.D (1 / 2 : ℝ),
            PointwiseUpperLipschitz
                (centeredEuclideanBall Q.D (3 / 4 : ℝ)) Q.v x ≤
              ENNReal.ofReal C)
    (interiorFallback :
      P.alpha = 0 ∨ P.epsilon > uBound + Real.sqrt P.alpha →
        ∃ C : ℝ, 0 < C ∧
          ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
            PointwiseUpperLipschitz
                (centeredEuclideanBall P.D (3 / 4 : ℝ)) u x ≤
              ENNReal.ofReal C *
                ENNReal.ofReal (uBound + Real.sqrt P.alpha)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ centeredEuclideanBall P.D (1 / 2 : ℝ),
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) u x ≤
          ENNReal.ofReal C *
            ENNReal.ofReal (uBound + Real.sqrt P.alpha) := by
  by_cases hα : P.alpha = 0
  · exact interiorFallback (Or.inl hα)
  let A : ℝ := uBound + Real.sqrt P.alpha
  have hαpos : 0 < P.alpha := lt_of_le_of_ne P.alpha_nonneg (Ne.symm hα)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  by_cases hδ : P.epsilon / A ≤ 1
  · let Apos : {t : ℝ // 0 < t} := ⟨A, hA⟩
    let onePos : {t : ℝ // 0 < t} := ⟨1, zero_lt_one⟩
    let lift : ((Fin P.D.n → ℝ) → ℝ) → ((Fin P.D.n → ℝ) → ℝ) :=
      fun φ x => A * φ x
    let IsTestV : (((Fin P.D.n → ℝ) → ℝ) → Prop) := fun φ => IsTest (lift φ)
    let hessianV : ((Fin P.D.n → ℝ) → ℝ) → (Fin P.D.n → ℝ) → Sn P.D.n :=
      fun φ x => (A⁻¹) • hessian (lift φ) x
    let v := singularPerturbationRescaledFunction P.D u P.F 0 onePos Apos 0
    let G := singularPerturbationRescaledOperator P.D u P.F 0 onePos Apos 0
    have hscale := lemSingularPerturbationRescaling P u 0 onePos Apos 0
    have hvcont : ContinuousOn v (centeredEuclideanBall P.D 1) := by
      dsimp [v, singularPerturbationRescaledFunction,
        SingularPerturbationRescaling, onePos, Apos]
      simpa using hu.1.div_const A
    have hvsol : ViscositySolutionOn (centeredEuclideanBall P.D 1) G
        (fun x => ((P.alpha / A ^ 2) / (P.epsilon / A)) *
          P.D.beta (v x / (P.epsilon / A))) v IsTestV hessianV := by
      rcases hu.2 with ⟨huSub, huSuper⟩
      constructor
      · intro φ x hφ htouch
        have htouch' : TouchesFromAboveOn (centeredEuclideanBall P.D 1)
            u (lift φ) x := by
          rcases htouch with ⟨hx, heq, hle⟩
          refine ⟨hx, ?_, ?_⟩
          · dsimp [v, lift, singularPerturbationRescaledFunction,
              SingularPerturbationRescaling, onePos, Apos] at heq ⊢
            rw [zero_add, one_smul, sub_zero] at heq
            simpa [mul_comm] using (div_eq_iff (ne_of_gt hA)).mp heq
          · filter_upwards [hle] with y hy
            dsimp [v, lift, singularPerturbationRescaledFunction,
              SingularPerturbationRescaling, onePos, Apos] at hy ⊢
            rw [zero_add, one_smul, sub_zero] at hy
            simpa [mul_comm] using (div_le_iff₀ hA).mp hy
        have horig := huSub hφ htouch'
        change (P.alpha / P.epsilon) * P.D.beta (u x / P.epsilon) ≤
          P.F (hessian (lift φ) x) at horig
        change ((P.alpha / A ^ 2) / (P.epsilon / A)) *
            P.D.beta (v x / (P.epsilon / A)) ≤ G (hessianV φ x)
        dsimp [v, G, hessianV, singularPerturbationRescaledFunction,
          singularPerturbationRescaledOperator, SingularPerturbationRescaling,
          onePos, Apos, lift]
        rw [zero_add, one_smul, sub_zero]
        have hA0 : A ≠ 0 := ne_of_gt hA
        have hε0 : P.epsilon ≠ 0 := ne_of_gt P.epsilon_pos
        have harg : (u x / A) / (P.epsilon / A) = u x / P.epsilon := by
          field_simp
        rw [harg]
        simp [hA0]
        have hcoef : (P.alpha / A ^ 2) / (P.epsilon / A) =
            (1 / A) * (P.alpha / P.epsilon) := by field_simp
        rw [hcoef]
        simpa [one_div, mul_assoc] using
          mul_le_mul_of_nonneg_left horig (le_of_lt (one_div_pos.mpr hA))
      · intro φ x hφ htouch
        have htouch' : TouchesFromBelowOn (centeredEuclideanBall P.D 1)
            u (lift φ) x := by
          rcases htouch with ⟨hx, heq, hle⟩
          refine ⟨hx, ?_, ?_⟩
          · dsimp [v, lift, singularPerturbationRescaledFunction,
              SingularPerturbationRescaling, onePos, Apos] at heq ⊢
            rw [zero_add, one_smul, sub_zero] at heq
            simpa [mul_comm] using (div_eq_iff (ne_of_gt hA)).mp heq
          · filter_upwards [hle] with y hy
            dsimp [v, lift, singularPerturbationRescaledFunction,
              SingularPerturbationRescaling, onePos, Apos] at hy ⊢
            rw [zero_add, one_smul, sub_zero] at hy
            simpa [mul_comm] using (le_div_iff₀ hA).mp hy
        have horig := huSuper hφ htouch'
        change P.F (hessian (lift φ) x) ≤
          (P.alpha / P.epsilon) * P.D.beta (u x / P.epsilon) at horig
        change G (hessianV φ x) ≤ ((P.alpha / A ^ 2) / (P.epsilon / A)) *
            P.D.beta (v x / (P.epsilon / A))
        dsimp [v, G, hessianV, singularPerturbationRescaledFunction,
          singularPerturbationRescaledOperator, SingularPerturbationRescaling,
          onePos, Apos, lift]
        rw [zero_add, one_smul, sub_zero]
        have hA0 : A ≠ 0 := ne_of_gt hA
        have harg : (u x / A) / (P.epsilon / A) = u x / P.epsilon := by
          field_simp
        rw [harg]
        simp [hA0]
        have hcoef : (P.alpha / A ^ 2) / (P.epsilon / A) =
            (1 / A) * (P.alpha / P.epsilon) := by field_simp
        rw [hcoef]
        simpa [one_div, mul_assoc] using
          mul_le_mul_of_nonneg_left horig (le_of_lt (one_div_pos.mpr hA))
    let Q : NormalizedDiffuseProblem := {
      D := P.D
      F := G
      gamma := P.alpha / A ^ 2
      delta := P.epsilon / A
      v := v
      IsTest := IsTestV
      hessian := hessianV
      beta_continuous := P.beta_continuous
      beta_nonnegative := P.beta_nonnegative
      beta_nonzero := P.beta_nonzero
      beta_support := P.beta_support
      uniformlyElliptic := hscale.2.1
      normalized := hscale.1
      gamma_pos := div_pos hαpos (sq_pos_of_pos hA)
      gamma_le_one := by
        have hs : Real.sqrt P.alpha ≤ A := by
          dsimp [A]
          linarith
        have hsq : P.alpha ≤ A ^ 2 := by
          rw [← Real.sq_sqrt P.alpha_nonneg]
          nlinarith [Real.sqrt_nonneg P.alpha]
        exact (div_le_one (sq_pos_of_pos hA)).2 hsq
      delta_pos := div_pos P.epsilon_pos hA
      delta_le_one := hδ
      continuousOn := hvcont
      viscositySolution := hvsol
      norm_le_one := by
        intro x hx
        dsimp [v, singularPerturbationRescaledFunction,
          SingularPerturbationRescaling, onePos, Apos]
        rw [zero_add, one_smul, sub_zero]
        rw [abs_div, abs_of_pos hA]
        exact (div_le_one hA).2
          (le_trans (huBound x hx) (by dsimp [A]; linarith [Real.sqrt_nonneg P.alpha])) }
    obtain ⟨C, hC, hnorm⟩ := normalizedEstimate Q
    refine ⟨C, hC, ?_⟩
    intro x hx
    have hvx := hnorm x hx
    have hLip :
        PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) u x =
          ENNReal.ofReal A *
            PointwiseUpperLipschitz
              (centeredEuclideanBall P.D (3 / 4 : ℝ)) v x := by
      unfold PointwiseUpperLipschitz
      rw [← ENNReal.limsup_const_mul_of_ne_top (by simp)]
      congr 1
      funext y
      dsimp [v, singularPerturbationRescaledFunction,
        SingularPerturbationRescaling, onePos, Apos]
      rw [zero_add, one_smul, sub_zero]
      have huy : u y = A • (u y / A) := by
        change u y = A * (u y / A)
        field_simp
      have hux : u x = A • (u x / A) := by
        change u x = A * (u x / A)
        field_simp
      have hed : edist (u y) (u x) =
          ENNReal.ofReal A * edist (u y / A) (u x / A) := by
        calc
          edist (u y) (u x) =
              edist (A • (u y / A)) (A • (u x / A)) :=
            congrArg₂ edist huy hux
          _ = ENNReal.ofReal A * edist (u y / A) (u x / A) := by
            rw [edist_smul₀, ENNReal.smul_def]
            congr 1
            rw [ENNReal.ofReal_eq_coe_nnreal]
            · norm_cast
              apply NNReal.eq
              change ‖A‖ = A
              exact abs_of_pos hA
            · exact hA.le
      rw [hed]
      simp only [zero_add, one_smul, sub_zero]
      exact mul_div_assoc _ _ _
    rw [hLip]
    calc
      ENNReal.ofReal A *
          PointwiseUpperLipschitz
            (centeredEuclideanBall P.D (3 / 4 : ℝ)) v x ≤
          ENNReal.ofReal A * ENNReal.ofReal C := by
        gcongr
      _ = ENNReal.ofReal C * ENNReal.ofReal A := by ac_rfl
  · apply interiorFallback
    right
    have hquot : 1 < P.epsilon / A := lt_of_not_ge hδ
    dsimp [A] at hA hquot ⊢
    simpa [one_mul] using (lt_div_iff₀ hA).mp hquot

end Lea.Lipschitz2
