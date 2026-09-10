import LanglandsFirstMainLemma.Delta.FiniteDefinition

namespace LanglandsFirstMainLemma

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Every computational local constant is nonzero. -/
theorem deltaFinite_ne_zero
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) : deltaFinite χ ψ γ ≠ 0 := by
  rw [deltaFinite]
  exact mul_ne_zero
    (ContinuousQuasiChar.apply_ne_zero χ.character (γ : Fˣ))
    (phase_ne_zero (finiteGaussSum χ ψ γ))

end LanglandsFirstMainLemma
