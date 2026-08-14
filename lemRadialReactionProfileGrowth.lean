import Lea.Lipschitz2.lemRadialReactionProfileExistence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Lea.Lipschitz2

/-- Global growth of a smooth radial reaction profile.

The hypothesis `hflux` is the integrated radial ODE
` s^(n-1) φ'(s) = ∫₀ˢ t^(n-1) β(φ(t)) dt ≥ 0`.
The hypothesis `hharmonicTail` records the standard classification of the
reaction-free radial harmonic tail after the profile leaves the support of
`β`: it is bounded in dimensions at least three and has at most logarithmic
growth in dimension two. -/
theorem lemRadialReactionProfileGrowth
    (P : SingularPerturbationProblemData) (a : ℝ) (φ : ℝ → ℝ)
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hβa : 0 < P.D.beta a)
    (hφ0 : φ 0 = a) (hφ'0 : deriv φ 0 = 0)
    (hRadialOrigin : HasDerivAt (deriv φ) (P.D.beta a / (P.D.n : ℝ)) 0)
    (hφdiff : Differentiable ℝ φ)
    (hflux : ∀ s : ℝ, 0 ≤ s →
      s ^ (P.D.n - 1) * deriv φ s =
          ∫ t in (0 : ℝ)..s, t ^ (P.D.n - 1) * P.D.beta (φ t) ∧
        0 ≤ ∫ t in (0 : ℝ)..s, t ^ (P.D.n - 1) * P.D.beta (φ t))
    (hharmonicTail : ∃ S K : ℝ, 0 ≤ S ∧ 0 ≤ K ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ S → |φ s| ≤ K) ∧
      (∀ s : ℝ, S ≤ s →
        |φ s - φ S| ≤ if P.D.n = 2 then K * Real.log (2 + s) else K)) :
    MonotoneOn φ (Set.Ici 0) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
        |φ s| ≤ if P.D.n = 2 then C * (1 + Real.log (2 + s)) else C := by
  have _hexistence := lemRadialReactionProfileExistence P a φ ha hβa hφ0 hφ'0 hRadialOrigin
  have hderiv : ∀ s : ℝ, 0 ≤ s → 0 ≤ deriv φ s := by
    intro s hs
    by_cases hs0 : s = 0
    · simp [hs0, hφ'0]
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have hpow : 0 < s ^ (P.D.n - 1) := pow_pos hspos _
      have hf := (hflux s hs).1
      have hi := (hflux s hs).2
      nlinarith
  have hmono : MonotoneOn φ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact hφdiff.continuous.continuousOn
    · exact hφdiff.differentiableOn
    · intro x hx
      exact hderiv x (interior_subset hx)
  refine ⟨hmono, ?_⟩
  rcases hharmonicTail with ⟨S, K, hS, hK, hcompact, htail⟩
  let C : ℝ := 2 * K + |φ S| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg (φ S)]
  have hφSC : |φ S| ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hlog : 0 ≤ Real.log (2 + s) := by
    have : 1 ≤ 2 + s := by linarith
    exact Real.log_nonneg this
  have hfactor : 1 ≤ 1 + Real.log (2 + s) := by linarith
  have hCnonneg : 0 ≤ C := hC.le
  by_cases hsS : s ≤ S
  · have hb := hcompact s hs hsS
    split_ifs with hn
    · exact hb.trans (hKC.trans (le_mul_of_one_le_right hCnonneg hfactor))
    · exact hb.trans hKC
  · have hSs : S ≤ s := le_of_not_ge hsS
    have ht := htail s hSs
    have habs : |φ s| ≤ |φ s - φ S| + |φ S| := by
      calc
        |φ s| = |(φ s - φ S) + φ S| := by ring_nf
        _ ≤ |φ s - φ S| + |φ S| := abs_add_le _ _
    split_ifs at ht ⊢ with hn
    · have hKlog : K * Real.log (2 + s) ≤ C * Real.log (2 + s) :=
        mul_le_mul_of_nonneg_right hKC hlog
      calc
        |φ s| ≤ |φ s - φ S| + |φ S| := habs
        _ ≤ K * Real.log (2 + s) + |φ S| := add_le_add ht le_rfl
        _ ≤ C * Real.log (2 + s) + C := add_le_add hKlog hφSC
        _ = C * (1 + Real.log (2 + s)) := by ring
    · calc
        |φ s| ≤ |φ s - φ S| + |φ S| := habs
        _ ≤ K + |φ S| := add_le_add ht le_rfl
        _ ≤ C := by dsimp [C]; linarith

end Lea.Lipschitz2
