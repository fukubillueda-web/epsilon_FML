import LanglandsFirstMainLemma.Parameters.PhaseReduction.StationaryData
import LanglandsFirstMainLemma.Parameters.PhaseReduction.FirstMainFactors

/-!
# Generic separation of elementary stationary factors

This module separates the additive and inverse-multiplicative halves of
local Lamprecht elementary factors and of the corresponding First-Main
numerator, denominator, and quotient. It is shared by the odd-prime and
quadratic assemblies.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Separated elementary stationary scalars -/

namespace LocalLamprechtPhaseData

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- The positive additive half of the elementary stationary factor. -/
def elementaryAdditiveFactor (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  match D with
  | .even d hm hlarge Gamma c hc =>
      (psi.character
        ((lamprechtStationaryRepresentativeUnit E chi psi
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge) Gamma c hc : Eˣ) /
          (Gamma : Eˣ) : E) : ℂ)
  | .odd d hm hlarge Gamma _delta _hdelta c hc =>
      (psi.character
        ((lamprechtStationaryRepresentativeUnit E chi psi
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge) Gamma c hc : Eˣ) /
          (Gamma : Eˣ) : E) : ℂ)

/-- The inverse multiplicative-character half of the elementary stationary
factor.  It is kept distinct from the additive value through assembly. -/
def elementaryMultiplicativeFactor
    (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  match D with
  | .even d hm hlarge Gamma c hc =>
      (chi.character
        (lamprechtStationaryRepresentativeUnit E chi psi
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge) Gamma c hc) : ℂ)⁻¹
  | .odd d hm hlarge Gamma _delta _hdelta c hc =>
      (chi.character
        (lamprechtStationaryRepresentativeUnit E chi psi
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge) Gamma c hc) : ℂ)⁻¹

/-- The elementary Lamprecht factor is exactly its positive additive phase
times its inverse multiplicative-character phase. -/
theorem elementaryFactor_eq_separated
    (D : LocalLamprechtPhaseData E chi psi) :
    D.elementaryFactor =
      D.elementaryAdditiveFactor * D.elementaryMultiplicativeFactor := by
  cases D <;> rfl

theorem elementaryAdditiveFactor_ne_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.elementaryAdditiveFactor ≠ 0 := by
  cases D <;> exact ContinuousAddChar.apply_ne_zero _ _

theorem elementaryMultiplicativeFactor_ne_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.elementaryMultiplicativeFactor ≠ 0 := by
  cases D <;> exact inv_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _)

/-- An actual stationary row exposes its positive additive elementary factor
at the literal supplied numerator and denominator. -/
@[simp]
theorem localPhaseOfStationaryClass_elementaryAdditiveFactor
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon) :
    (localPhaseOfStationaryClass h Gamma R C).elementaryAdditiveFactor =
      (psi.character
        ((R.representative : E) / ((Gamma : Eˣ) : E)) : ℂ) := by
  cases C <;> rfl

/-- An actual stationary row exposes its inverse multiplicative elementary
factor at the literal supplied numerator. -/
@[simp]
theorem localPhaseOfStationaryClass_elementaryMultiplicativeFactor
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon) :
    (localPhaseOfStationaryClass h Gamma R C).elementaryMultiplicativeFactor =
      (chi.character R.unit : ℂ)⁻¹ := by
  cases C <;> rfl

/-- Equality-only transport of proof-bearing character data leaves the
positive additive elementary factor unchanged. -/
theorem transportLocalLamprechtPhaseData_elementaryAdditiveFactor
    {chi' : LocalQuasiCharData E} {psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (S : LocalLamprechtPhaseData E chi psi) :
    (transportLocalLamprechtPhaseData hchi hpsi S).elementaryAdditiveFactor =
      S.elementaryAdditiveFactor := by
  have hc : chi = chi' := LocalQuasiCharData.ext_character E hchi
  have hp : psi = psi' := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  rfl

/-- Equality-only transport of proof-bearing character data leaves the
inverse multiplicative-character elementary factor unchanged. -/
theorem transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor
    {chi' : LocalQuasiCharData E} {psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (S : LocalLamprechtPhaseData E chi psi) :
    (transportLocalLamprechtPhaseData hchi hpsi S).elementaryMultiplicativeFactor =
      S.elementaryMultiplicativeFactor := by
  have hc : chi = chi' := LocalQuasiCharData.ext_character E hchi
  have hp : psi = psi' := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  rfl

end LocalLamprechtPhaseData

namespace LocalPhaseData

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- Endpoint rows contribute one to the additive stationary product. -/
def elementaryAdditiveFactor (D : LocalPhaseData E chi psi) : ℂ :=
  match D with
  | .endpoint _ _ => 1
  | .stationary S => S.elementaryAdditiveFactor

/-- Endpoint rows contribute one to the multiplicative stationary product. -/
def elementaryMultiplicativeFactor (D : LocalPhaseData E chi psi) : ℂ :=
  match D with
  | .endpoint _ _ => 1
  | .stationary S => S.elementaryMultiplicativeFactor

theorem elementaryFactor_eq_separated (D : LocalPhaseData E chi psi) :
    D.elementaryFactor =
      D.elementaryAdditiveFactor * D.elementaryMultiplicativeFactor := by
  cases D with
  | endpoint => simp [elementaryFactor, elementaryAdditiveFactor,
      elementaryMultiplicativeFactor]
  | stationary S => simpa [elementaryFactor, elementaryAdditiveFactor,
      elementaryMultiplicativeFactor] using S.elementaryFactor_eq_separated

theorem elementaryAdditiveFactor_ne_zero (D : LocalPhaseData E chi psi) :
    D.elementaryAdditiveFactor ≠ 0 := by
  cases D with
  | endpoint => simp [elementaryAdditiveFactor]
  | stationary S => exact S.elementaryAdditiveFactor_ne_zero

theorem elementaryMultiplicativeFactor_ne_zero
    (D : LocalPhaseData E chi psi) :
    D.elementaryMultiplicativeFactor ≠ 0 := by
  cases D with
  | endpoint => simp [elementaryMultiplicativeFactor]
  | stationary S => exact S.elementaryMultiplicativeFactor_ne_zero

end LocalPhaseData

namespace FirstMainPhaseData

variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]
  {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
  {data : FirstMainComputationalData F K chiF psiF}

/-- Additive half of the elementary numerator, before any scalar
cancellation. -/
noncomputable def elementaryAdditiveNumerator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact D.extension.elementaryAdditiveFactor *
    ∏ mu : NormCharacter F K,
      (D.normCharacter mu).elementaryAdditiveFactor

/-- Additive half of the elementary denominator. -/
noncomputable def elementaryAdditiveDenominator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ mu : NormCharacter F K,
    (D.twist mu).elementaryAdditiveFactor

/-- Multiplicative-character half of the elementary numerator. -/
noncomputable def elementaryMultiplicativeNumerator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact D.extension.elementaryMultiplicativeFactor *
    ∏ mu : NormCharacter F K,
      (D.normCharacter mu).elementaryMultiplicativeFactor

/-- Multiplicative-character half of the elementary denominator. -/
noncomputable def elementaryMultiplicativeDenominator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ mu : NormCharacter F K,
    (D.twist mu).elementaryMultiplicativeFactor

theorem elementaryNumerator_eq_separated
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.elementaryNumerator = D.elementaryAdditiveNumerator *
      D.elementaryMultiplicativeNumerator := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rw [elementaryNumerator, elementaryAdditiveNumerator,
    elementaryMultiplicativeNumerator,
    D.extension.elementaryFactor_eq_separated]
  simp_rw [LocalPhaseData.elementaryFactor_eq_separated]
  rw [Finset.prod_mul_distrib]
  ring

theorem elementaryDenominator_eq_separated
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.elementaryDenominator = D.elementaryAdditiveDenominator *
      D.elementaryMultiplicativeDenominator := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rw [elementaryDenominator, elementaryAdditiveDenominator,
    elementaryMultiplicativeDenominator]
  simp_rw [LocalPhaseData.elementaryFactor_eq_separated]
  rw [Finset.prod_mul_distrib]

theorem elementaryAdditiveDenominator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.elementaryAdditiveDenominator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Finset.prod_ne_zero_iff.mpr fun mu _ ↦
    (D.twist mu).elementaryAdditiveFactor_ne_zero

theorem elementaryMultiplicativeDenominator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.elementaryMultiplicativeDenominator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Finset.prod_ne_zero_iff.mpr fun mu _ ↦
    (D.twist mu).elementaryMultiplicativeFactor_ne_zero

/-- The positive-additive quotient of all selected quadratic rows. -/
noncomputable def elementaryAdditiveQuotient
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ :=
  D.elementaryAdditiveNumerator / D.elementaryAdditiveDenominator

/-- The inverse-multiplicative-character quotient of all selected rows. -/
noncomputable def elementaryMultiplicativeQuotient
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ :=
  D.elementaryMultiplicativeNumerator /
    D.elementaryMultiplicativeDenominator

/-- The elementary quotient is the product of its separately oriented
additive and multiplicative-character quotients. -/
theorem elementaryFactor_eq_separatedQuotients
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.factors.elementary = D.elementaryAdditiveQuotient *
      D.elementaryMultiplicativeQuotient := by
  rw [FirstMainPhaseData.factors, D.elementaryNumerator_eq_separated,
    D.elementaryDenominator_eq_separated,
    elementaryAdditiveQuotient, elementaryMultiplicativeQuotient]
  field_simp [D.elementaryAdditiveDenominator_ne_zero,
    D.elementaryMultiplicativeDenominator_ne_zero]

theorem elementaryNumerator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.elementaryNumerator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact mul_ne_zero D.extension.elementaryFactor_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun mu _ ↦
      (D.normCharacter mu).elementaryFactor_ne_zero)

end FirstMainPhaseData

end

end LanglandsFirstMainLemma
