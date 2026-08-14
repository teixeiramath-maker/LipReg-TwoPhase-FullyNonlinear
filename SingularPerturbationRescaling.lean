import Lea.Lipschitz2.StructuralDataAndNotation

namespace Lea.Lipschitz2

/-- The spatial and amplitude rescaling
`v(x) = (u(x₀ + r x) - c) / A` together with the corresponding operator
`F_{r,A}(M) = (r² / A) F((A / r²) M)`. -/
noncomputable def SingularPerturbationRescaling (D : StructuralDataAndNotation)
    (u : (Fin D.n → ℝ) → ℝ) (F : Sn D.n → ℝ) (x₀ : Fin D.n → ℝ)
    (r A : {t : ℝ // 0 < t}) (c : ℝ) :
    ((Fin D.n → ℝ) → ℝ) × (Sn D.n → ℝ) :=
  (fun x => (u (x₀ + (r : ℝ) • x) - c) / (A : ℝ),
   fun M => ((r : ℝ) ^ 2 / (A : ℝ)) *
      F (((A : ℝ) / (r : ℝ) ^ 2) • M))

/-- The rescaled function `v` from `SingularPerturbationRescaling`. -/
noncomputable def singularPerturbationRescaledFunction (D : StructuralDataAndNotation)
    (u : (Fin D.n → ℝ) → ℝ) (F : Sn D.n → ℝ) (x₀ : Fin D.n → ℝ)
    (r A : {t : ℝ // 0 < t}) (c : ℝ) : (Fin D.n → ℝ) → ℝ :=
  (SingularPerturbationRescaling D u F x₀ r A c).1

/-- The rescaled operator `F_{r,A}` from `SingularPerturbationRescaling`. -/
noncomputable def singularPerturbationRescaledOperator (D : StructuralDataAndNotation)
    (u : (Fin D.n → ℝ) → ℝ) (F : Sn D.n → ℝ) (x₀ : Fin D.n → ℝ)
    (r A : {t : ℝ // 0 < t}) (c : ℝ) : Sn D.n → ℝ :=
  (SingularPerturbationRescaling D u F x₀ r A c).2

end Lea.Lipschitz2
