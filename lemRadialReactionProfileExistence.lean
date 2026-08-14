import Lea.Lipschitz2.SingularPerturbationProblemData
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Lea.Lipschitz2

/-- For the imported smooth radial solution, the radial equation at the origin
forces a positive second derivative, and hence the radial profile has positive
slope at some positive radius. -/
theorem lemRadialReactionProfileExistence
    (P : SingularPerturbationProblemData) (a : ℝ) (φ : ℝ → ℝ)
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hβa : 0 < P.D.beta a)
    (hφ0 : φ 0 = a) (hφ'0 : deriv φ 0 = 0)
    (hRadialOrigin : HasDerivAt (deriv φ) (P.D.beta a / (P.D.n : ℝ)) 0) :
    deriv (deriv φ) 0 = P.D.beta a / (P.D.n : ℝ) ∧
      0 < deriv (deriv φ) 0 ∧
      ∃ s_star c_star : ℝ,
        0 < s_star ∧ 0 < c_star ∧ deriv φ s_star = c_star := by
  by_cases hdata : φ 0 = a ∧ a ∈ Set.Ioo (-1 : ℝ) 1
  · have hn : (0 : ℝ) < P.D.n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) P.D.two_le_n)
    have hd : 0 < P.D.beta a / (P.D.n : ℝ) := div_pos hβa hn
    have hsecond : deriv (deriv φ) 0 = P.D.beta a / (P.D.n : ℝ) :=
      hRadialOrigin.deriv
    refine ⟨hsecond, hsecond.symm ▸ hd, ?_⟩
    have ht := hRadialOrigin.tendsto_slope_zero_right
    have heventRaw : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        P.D.beta a / (P.D.n : ℝ) / 2 <
          x⁻¹ • (deriv φ (0 + x) - deriv φ 0) :=
      ht.eventually (eventually_gt_nhds (by linarith))
    have hevent := heventRaw.and (self_mem_nhdsWithin :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ∈ Set.Ioi 0)
    rcases (Filter.Eventually.exists hevent) with ⟨s, hs⟩
    have hspos : 0 < s := hs.2
    have hslope : 0 < s⁻¹ * deriv φ s := by
      simpa [hφ'0] using
        lt_trans (by linarith : 0 < P.D.beta a / (P.D.n : ℝ) / 2) hs.1
    have hderivpos : 0 < deriv φ s := by
      have hinv : 0 < s⁻¹ := inv_pos.mpr hspos
      nlinarith
    exact ⟨s, deriv φ s, hspos, hderivpos, rfl⟩
  · exact (hdata ⟨hφ0, ha⟩).elim

end Lea.Lipschitz2
