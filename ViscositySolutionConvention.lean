import Lea.Lipschitz2.StructuralDataAndNotation

namespace Lea.Lipschitz2

/-- The two possible directions of contact of a test function with a
viscosity solution. -/
inductive ViscosityContactDirection where
  | fromAbove
  | fromBelow
  deriving DecidableEq

/-- The paper's viscosity sign convention.  An upper test has operator value
at least the source value, while a lower test has operator value at most the
source value. -/
def ViscositySolutionConvention
    (contact : ViscosityContactDirection) (operatorValue sourceValue : ℝ) : Prop :=
  match contact with
  | .fromAbove => sourceValue ≤ operatorValue
  | .fromBelow => operatorValue ≤ sourceValue

/-- `φ` touches `u` from above at `x₀`, relative to the ambient set `Ω`.
The use of `nhdsWithin` makes the ambient-domain convention explicit. -/
def TouchesFromAboveOn {X : Type*} [TopologicalSpace X]
    (Ω : Set X) (u φ : X → ℝ) (x₀ : X) : Prop :=
  x₀ ∈ Ω ∧ u x₀ = φ x₀ ∧
    ∀ᶠ x in nhdsWithin x₀ Ω, u x ≤ φ x

/-- `φ` touches `u` from below at `x₀`, relative to the ambient set `Ω`. -/
def TouchesFromBelowOn {X : Type*} [TopologicalSpace X]
    (Ω : Set X) (u φ : X → ℝ) (x₀ : X) : Prop :=
  x₀ ∈ Ω ∧ u x₀ = φ x₀ ∧
    ∀ᶠ x in nhdsWithin x₀ Ω, φ x ≤ u x

/-- Viscosity subsolution predicate for the paper's sign convention.
`IsTest φ` supplies the imported regularity requirement (normally `C²`), and
`hessian φ x` supplies its Hessian. -/
def ViscositySubsolutionOn {X : Type*} [TopologicalSpace X]
    {n : ℕ} (Ω : Set X) (F : Sn n → ℝ) (f u : X → ℝ)
    (IsTest : (X → ℝ) → Prop) (hessian : (X → ℝ) → X → Sn n) : Prop :=
  ∀ ⦃φ : X → ℝ⦄ ⦃x₀ : X⦄,
    IsTest φ → TouchesFromAboveOn Ω u φ x₀ →
      ViscositySolutionConvention .fromAbove (F (hessian φ x₀)) (f x₀)

/-- Viscosity supersolution predicate for the paper's sign convention. -/
def ViscositySupersolutionOn {X : Type*} [TopologicalSpace X]
    {n : ℕ} (Ω : Set X) (F : Sn n → ℝ) (f u : X → ℝ)
    (IsTest : (X → ℝ) → Prop) (hessian : (X → ℝ) → X → Sn n) : Prop :=
  ∀ ⦃φ : X → ℝ⦄ ⦃x₀ : X⦄,
    IsTest φ → TouchesFromBelowOn Ω u φ x₀ →
      ViscositySolutionConvention .fromBelow (F (hessian φ x₀)) (f x₀)

/-- A viscosity solution is simultaneously a subsolution and a supersolution,
with all tests interpreted relative to the same ambient domain `Ω`. -/
def ViscositySolutionOn {X : Type*} [TopologicalSpace X]
    {n : ℕ} (Ω : Set X) (F : Sn n → ℝ) (f u : X → ℝ)
    (IsTest : (X → ℝ) → Prop) (hessian : (X → ℝ) → X → Sn n) : Prop :=
  ViscositySubsolutionOn Ω F f u IsTest hessian ∧
    ViscositySupersolutionOn Ω F f u IsTest hessian

end Lea.Lipschitz2
