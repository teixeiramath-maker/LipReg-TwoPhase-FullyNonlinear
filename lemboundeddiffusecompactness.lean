import Lea.Lipschitz2.lemuniformdiffuseholder
import Lea.Lipschitz2.lemcompactness
import Lea.Lipschitz2.lemsharpstability

namespace Lea.Lipschitz2

/-- Sequential local precompactness for a family of real-valued functions. -/
def LocallyPrecompactSequenceOn {X : Type*} [TopologicalSpace X]
    (Ω : Set X) (u : ℕ → X → ℝ) : Prop :=
  ∀ s : ℕ → ℕ, StrictMono s →
    ∃ t : ℕ → ℕ, ∃ ulimit : X → ℝ,
      StrictMono t ∧
        LocallyUniformlyConvergesOn Ω (fun j => u (s (t j))) ulimit

/-- The Arzelà--Ascoli extraction used in uniform diffuse compactness.  The
hypotheses expose exactly the common Hölder estimate and normalized elliptic
operator compactness on which the extraction depends. -/
def BoundedDiffuseArzelaAscoliStatement
    (D : StructuralDataAndNotation) : Prop :=
  ∀ alpha C : ℝ,
    UniformDiffuseHolderEstimateStatement D alpha C →
    EllipticOperatorLocalCompactnessStatement D →
    ∀ (F : ℕ → Sn D.n → ℝ) (gamma eta sigma : ℕ → ℝ)
      (w : ℕ → (Fin D.n → ℝ) → ℝ)
      (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
      (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n),
      Continuous D.beta →
      (∀ s : ℝ, 0 ≤ D.beta s) →
      Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1 →
      (∀ j, Uniformellipticity D (F j)) →
      (∀ j, F j 0 = 0) →
      (∀ j, 0 < gamma j) →
      (∀ j, gamma j ≤ 1) →
      (∀ j, 0 < eta j) →
      (∀ j, |sigma j| ≤ 2 * eta j) →
      (∀ j, ContinuousOn (w j) (centeredEuclideanBall D 1)) →
      (∀ j, ViscositySolutionOn (centeredEuclideanBall D 1) (F j)
        (fun x => (gamma j / eta j) *
          D.beta ((w j x + sigma j) / eta j))
        (w j) IsTest hessian) →
      (∀ j x, x ∈ centeredEuclideanBall D 1 → |w j x| ≤ 1) →
      LocallyPrecompactSequenceOn (centeredEuclideanBall D 1) w ∧
      ∃ subsequence : ℕ → ℕ, ∃ F_infty : Sn D.n → ℝ,
        ∃ w_infty : (Fin D.n → ℝ) → ℝ,
          StrictMono subsequence ∧
          Uniformellipticity D F_infty ∧ F_infty 0 = 0 ∧
          LocallyUniformlyConvergesOn Set.univ
            (fun j => F (subsequence j)) F_infty ∧
          LocallyUniformlyConvergesOn (centeredEuclideanBall D 1)
            (fun j => w (subsequence j)) w_infty

/-- **Uniform diffuse compactness.**

Normalized shifted diffuse solutions of unit amplitude are locally
precompact.  A single subsequence gives locally uniform convergence of both
operators and solutions.  Vanishing effective strength yields the homogeneous
limiting equation; collapsing thickness is governed by the sharp-interface
stability theorem. -/
theorem lemboundeddiffusecompactness
    (D : StructuralDataAndNotation)
    (importedOperatorCompactness :
      EllipticOperatorLocalCompactnessStatement D)
    (importedViscosityStability : ViscosityStabilityStatement D)
    (importedDiffuseOscillationEstimate :
      ∃ alpha C : ℝ,
        0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
          UniformDiffuseHolderEstimateStatement D alpha C)
    (importedArzelaAscoli : BoundedDiffuseArzelaAscoliStatement D)
    (importedCurvedTestArgument :
      ViscosityStabilityStatement D →
        VanishingStrengthCompactnessStatement D)
    (importedSharpInterfaceArgument :
      ViscosityStabilityStatement D → CurvedPlanarBarrierCore D →
        SharpInterfaceStabilityStatement D)
    (F : ℕ → Sn D.n → ℝ) (gamma eta sigma : ℕ → ℝ)
    (w : ℕ → (Fin D.n → ℝ) → ℝ)
    (IsTest : (((Fin D.n → ℝ) → ℝ) → Prop))
    (hessian : ((Fin D.n → ℝ) → ℝ) → (Fin D.n → ℝ) → Sn D.n)
    (hbetaContinuous : Continuous D.beta)
    (hbetaNonnegative : ∀ s : ℝ, 0 ≤ D.beta s)
    (hbetaSupport : Function.support D.beta ⊆ Set.Ioo (-1 : ℝ) 1)
    (hElliptic : ∀ j, Uniformellipticity D (F j))
    (hNormalized : ∀ j, F j 0 = 0)
    (hGammaPos : ∀ j, 0 < gamma j)
    (hGammaBound : ∀ j, gamma j ≤ 1)
    (hEtaPos : ∀ j, 0 < eta j)
    (hShift : ∀ j, |sigma j| ≤ 2 * eta j)
    (hContinuous : ∀ j,
      ContinuousOn (w j) (centeredEuclideanBall D 1))
    (hSolution : ∀ j,
      ViscositySolutionOn (centeredEuclideanBall D 1) (F j)
        (fun x => (gamma j / eta j) *
          D.beta ((w j x + sigma j) / eta j))
        (w j) IsTest hessian)
    (hBounded : ∀ j x, x ∈ centeredEuclideanBall D 1 → |w j x| ≤ 1) :
    LocallyPrecompactSequenceOn (centeredEuclideanBall D 1) w ∧
    ∃ subsequence : ℕ → ℕ, ∃ F_infty : Sn D.n → ℝ,
      ∃ w_infty : (Fin D.n → ℝ) → ℝ,
        StrictMono subsequence ∧
        Uniformellipticity D F_infty ∧ F_infty 0 = 0 ∧
        LocallyUniformlyConvergesOn Set.univ
          (fun j => F (subsequence j)) F_infty ∧
        LocallyUniformlyConvergesOn (centeredEuclideanBall D 1)
          (fun j => w (subsequence j)) w_infty ∧
        (Filter.Tendsto gamma Filter.atTop (nhds 0) →
          ViscositySolutionOn (centeredEuclideanBall D 1)
            F_infty 0 w_infty IsTest hessian) ∧
        (Filter.Tendsto eta Filter.atTop (nhds 0) →
          SharpInterfaceStabilityStatement D) := by
  obtain ⟨alpha, C, halpha, halphaOne, hC, hHolder⟩ :=
    lemuniformdiffuseholder D importedDiffuseOscillationEstimate
  have hExtraction := importedArzelaAscoli alpha C hHolder
    importedOperatorCompactness F gamma eta sigma w IsTest hessian
    hbetaContinuous hbetaNonnegative hbetaSupport hElliptic hNormalized
    hGammaPos hGammaBound hEtaPos hShift hContinuous hSolution hBounded
  rcases hExtraction with ⟨hPrecompact, subsequence, F_infty, w_infty,
    hsubsequence, hF_infty, hF_infty_zero, hFconv, hwconv⟩
  refine ⟨hPrecompact, subsequence, F_infty, w_infty, hsubsequence,
    hF_infty, hF_infty_zero, hFconv, hwconv, ?_, ?_⟩
  · intro hgamma
    have hgammaSub :
        Filter.Tendsto (fun j => gamma (subsequence j)) Filter.atTop
          (nhds 0) :=
      hgamma.comp hsubsequence.tendsto_atTop
    have hVanishing :=
      lemcompactness D importedOperatorCompactness importedViscosityStability
        importedCurvedTestArgument
    exact hVanishing hbetaContinuous hbetaNonnegative hbetaSupport
      (centeredEuclideanBall D 1) (fun j => F (subsequence j)) F_infty
      (fun j => gamma (subsequence j)) (fun j => eta (subsequence j))
      (fun j => sigma (subsequence j)) (fun j => w (subsequence j))
      w_infty IsTest hessian Metric.isOpen_ball
      (fun j => hElliptic (subsequence j))
      (fun j => hNormalized (subsequence j)) hFconv hgammaSub
      (fun j => (hGammaPos (subsequence j)).le)
      (fun j => hEtaPos (subsequence j))
      (fun j => hShift (subsequence j))
      (fun j => hContinuous (subsequence j))
      (fun j => hSolution (subsequence j)) hwconv
  · intro _heta
    exact lemsharpstability D importedOperatorCompactness
      importedViscosityStability importedSharpInterfaceArgument

end Lea.Lipschitz2
