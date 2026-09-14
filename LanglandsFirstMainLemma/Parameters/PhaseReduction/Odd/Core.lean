import LanglandsFirstMainLemma.Parameters.PhaseReduction.Range
import LanglandsFirstMainLemma.Parameters.PhaseReduction.FirstMainFactors

/-!
# Exact odd-prime phase assembly core

This module packages the exact odd-prime First-Main phase assembly, the
nonidentity norm-character indexing, character-data transport, correction
units, and the elementary scaling identities shared by the high and low
parameter tables. No finite-field phase cancellation is asserted here.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Exact odd-prime stationary assembly -/

/-- Raw data for Proposition `prop:exact-odd-assembly`.  The cancellable
pieces are supplied as separate numerator and denominator identities with a
common nonzero factor.  The norm--trace correction is derived from the two
pointwise character linearizations and the displayed definition of `X`.
The residual phase is not a field: it is definitionally the actual quotient
of the critical factors in `D`. -/
structure ExactOddPhaseAssembly
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    (chiF : ContinuousQuasiChar F) (psiF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K chiF psiF)
    (D : FirstMainPhaseData F K chiF psiF data)
    {t m : ℕ} (I : Type*) [Fintype I] where
  baseData : LocalQuasiCharData F
  baseData_eq : baseData = data.twistData 1
  baseCharacter : baseData.character = chiF
  baseConductor : baseData.conductor = m
  parameterRange : PhaseParameterRange t m
  A : F
  u : K
  n : F
  norm_u : norm F K u = n
  zZero : Fˣ
  z : I → Fˣ
  indexScalar : I → F
  normCharacterIndex : I → NormCharacter F K
  normCharacterIndexing : Option I ≃ NormCharacter F K
  normCharacterIndexing_none : normCharacterIndexing none = 1
  normCharacterIndexing_some : ∀ i,
    normCharacterIndexing (some i) = normCharacterIndex i
  normCharacterStationary : ∀ i, ∃
    (S : LocalLamprechtPhaseData F
      (data.normCharacterData (normCharacterIndex i)) data.baseAddChar),
      D.normCharacter (normCharacterIndex i) = LocalPhaseData.stationary S
  normCharacterPower : I → ContinuousQuasiChar F
  normCharacterPower_eq : ∀ i,
    normCharacterPower i = (normCharacterIndex i).1
  X : F
  X_eq : X = trace F K u + n * ((zZero : F) - 1) +
    ∑ i : I, indexScalar i * ((z i : F) - 1)
  chiLinearization : chiF zZero =
    psiF (A * n * ((zZero : F) - 1))
  powerLinearization : ∀ i, normCharacterPower i (z i) =
    psiF (A * indexScalar i * ((z i : F) - 1))
  endpointCommonFactor : ℂ
  endpointCommonFactor_ne_zero : endpointCommonFactor ≠ 0
  endpointNumerator_eq : D.endpointNumerator = endpointCommonFactor
  endpointDenominator_eq : D.endpointDenominator = endpointCommonFactor
  admissibleCommonFactor : ℂ
  admissibleCommonFactor_ne_zero : admissibleCommonFactor ≠ 0
  admissibleNumerator_eq : D.admissibleNumerator = admissibleCommonFactor
  admissibleDenominator_eq : D.admissibleDenominator = admissibleCommonFactor
  elementaryCommonFactor : ℂ
  elementaryCommonFactor_ne_zero : elementaryCommonFactor ≠ 0
  elementaryNumerator_eq : D.elementaryNumerator = elementaryCommonFactor
  elementaryDenominator_eq : D.elementaryDenominator =
    ((psiF (A * trace F K u) : ℂ) *
      (chiF zZero : ℂ) *
      ∏ i : I, (normCharacterPower i (z i) : ℂ)) *
        elementaryCommonFactor

namespace ExactOddPhaseAssembly

variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]
  {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
  {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
  {data : FirstMainComputationalData F K chiF psiF}
  {D : FirstMainPhaseData F K chiF psiF data}
  {t m : ℕ} {I : Type*} [Fintype I]

local instance : Fintype (NormCharacter F K) :=
  Fintype.ofFinite (NormCharacter F K)

/-- The residual odd phase is the quotient of the actual local critical
factors, with all denominator nonvanishing inherited from Lamprecht. -/
def residualPhase
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) : ℂ :=
  D.criticalNumerator / D.criticalDenominator

/-- The odd index type enumerates exactly the nonidentity norm characters;
no indexed stationary row can accidentally be the endpoint. -/
theorem normCharacterIndex_ne_one
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) (i : I) :
    A.normCharacterIndex i ≠ 1 := by
  intro hi
  have hEq : A.normCharacterIndexing (some i) =
      A.normCharacterIndexing none := by
    rw [A.normCharacterIndexing_some, hi,
      A.normCharacterIndexing_none]
  exact Option.some_ne_none i (A.normCharacterIndexing.injective hEq)

/-- The power occurring in the elementary bracket is the character of the
actual norm-character local datum at the same exhaustive index. -/
theorem normCharacterData_character_eq_power
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) (i : I) :
    (data.normCharacterData (A.normCharacterIndex i)).character =
      A.normCharacterPower i := by
  rw [data.normCharacterData_character, A.normCharacterPower_eq]

/-- Reindex the full norm-character critical product as its genuine identity
endpoint followed by every nonidentity stationary row exactly once. -/
theorem normCriticalProduct_reindex
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    (∏ mu : NormCharacter F K, (D.normCharacter mu).criticalFactor) =
      (D.normCharacter 1).criticalFactor *
        ∏ i : I,
          (D.normCharacter (A.normCharacterIndex i)).criticalFactor := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rw [← Equiv.prod_comp A.normCharacterIndexing
    (fun mu : NormCharacter F K ↦ (D.normCharacter mu).criticalFactor)]
  rw [Fintype.prod_option, A.normCharacterIndexing_none]
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  rw [A.normCharacterIndexing_some i]

/-- The identity norm-character row has no stationary critical factor. -/
theorem identityNorm_criticalFactor_eq_one
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    (D.normCharacter 1).criticalFactor = 1 := by
  rcases identityNormCharacterEndpoint_of_phaseData D with
    ⟨h, Gamma, hEq⟩
  rw [hEq]
  rfl

/-- The residual numerator contains the extension phase and exactly the
nonidentity norm-character phases. -/
theorem criticalNumerator_eq_indexed
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    D.criticalNumerator = D.extension.criticalFactor *
      ∏ i : I,
        (D.normCharacter (A.normCharacterIndex i)).criticalFactor := by
  simp only [FirstMainPhaseData.criticalNumerator]
  rw [A.normCriticalProduct_reindex, A.identityNorm_criticalFactor_eq_one]
  ring

/-- Reindex every twist critical factor by the same exhaustive character
equivalence, retaining the base twist at the identity index. -/
theorem twistCriticalProduct_reindex
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    (∏ mu : NormCharacter F K, (D.twist mu).criticalFactor) =
      (D.twist 1).criticalFactor *
        ∏ i : I,
          (D.twist (A.normCharacterIndex i)).criticalFactor := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rw [← Equiv.prod_comp A.normCharacterIndexing
    (fun mu : NormCharacter F K ↦ (D.twist mu).criticalFactor)]
  rw [Fintype.prod_option, A.normCharacterIndexing_none]
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  rw [A.normCharacterIndexing_some i]

/-- Exact odd residual quotient in terms of all and only the actual
nonidentity local critical phases.  No residual phase is cancelled. -/
theorem criticalFactor_eq_indexedQuotient
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    D.factors.critical =
      (D.extension.criticalFactor *
          ∏ i : I,
            (D.normCharacter (A.normCharacterIndex i)).criticalFactor) /
        ((D.twist 1).criticalFactor *
          ∏ i : I,
            (D.twist (A.normCharacterIndex i)).criticalFactor) := by
  simp only [FirstMainPhaseData.factors]
  rw [A.criticalNumerator_eq_indexed]
  simp only [FirstMainPhaseData.criticalDenominator]
  rw [A.twistCriticalProduct_reindex]

theorem residualPhase_eq_indexedQuotient
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    A.residualPhase =
      (D.extension.criticalFactor *
          ∏ i : I,
            (D.normCharacter (A.normCharacterIndex i)).criticalFactor) /
        ((D.twist 1).criticalFactor *
          ∏ i : I,
            (D.twist (A.normCharacterIndex i)).criticalFactor) := by
  simpa only [residualPhase, FirstMainPhaseData.factors] using
    A.criticalFactor_eq_indexedQuotient

theorem correctionBracket_eq_phase
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    (psiF (A.A * trace F K A.u) : ℂ) *
        (chiF A.zZero : ℂ) *
        ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ) =
      (psiF (A.A * A.X) : ℂ) := by
  have hprodUnits :
      ∏ i : I, A.normCharacterPower i (A.z i) =
        psiF (∑ i : I,
          A.A * A.indexScalar i * ((A.z i : F) - 1)) := by
    simp_rw [A.powerLinearization]
    have h := map_sum psiF.toAddChar.toAddMonoidHom
      (fun i : I ↦ A.A * A.indexScalar i * ((A.z i : F) - 1))
      Finset.univ
    exact congrArg Additive.toMul h.symm
  have hprod := congrArg (Units.val : ℂˣ → ℂ) hprodUnits
  push_cast at hprod
  rw [A.chiLinearization]
  change (psiF (A.A * trace F K A.u) : ℂ) *
      (psiF (A.A * A.n * ((A.zZero : F) - 1)) : ℂ) *
        ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ) = _
  rw [hprod]
  have hmapC (x y : F) :
      (psiF (x + y) : ℂ) = (psiF x : ℂ) * (psiF y : ℂ) :=
    congrArg (Units.val : ℂˣ → ℂ)
      (ContinuousAddChar.map_add_eq_mul psiF x y)
  rw [← hmapC, ← hmapC]
  congr 2
  rw [A.X_eq]
  simp only [mul_add, Finset.mul_sum]
  ring

theorem correctionBracket_inv_eq_phase_neg
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    ((psiF (A.A * trace F K A.u) : ℂ) *
        (chiF A.zZero : ℂ) *
        ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ))⁻¹ =
      (psiF (-A.A * A.X) : ℂ) := by
  rw [A.correctionBracket_eq_phase]
  have hneg := congrArg (Units.val : ℂˣ → ℂ)
    (AddChar.map_neg_eq_inv psiF.toAddChar (A.A * A.X))
  simpa only [ContinuousAddChar.toAddChar_apply, Units.val_inv_eq_inv_val,
    neg_mul] using hneg.symm

theorem endpointFactor_eq_one
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    D.factors.endpoint = 1 := by
  simp only [FirstMainPhaseData.factors]
  rw [A.endpointNumerator_eq, A.endpointDenominator_eq]
  exact div_self A.endpointCommonFactor_ne_zero

theorem admissibleFactor_eq_one
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    D.factors.admissibleCharacter = 1 := by
  simp only [FirstMainPhaseData.factors]
  rw [A.admissibleNumerator_eq, A.admissibleDenominator_eq]
  exact div_self A.admissibleCommonFactor_ne_zero

theorem elementaryFactor_eq_bracket_inv
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    D.factors.elementary =
      ((psiF (A.A * trace F K A.u) : ℂ) *
        (chiF A.zZero : ℂ) *
        ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ))⁻¹ := by
  simp only [FirstMainPhaseData.factors]
  rw [A.elementaryNumerator_eq, A.elementaryDenominator_eq]
  field_simp [A.elementaryCommonFactor_ne_zero,
    ContinuousAddChar.apply_ne_zero, ContinuousQuasiChar.apply_ne_zero]

/-- Proposition `prop:exact-odd-assembly` before applying the pointwise
linearizations.  The elementary correction and the actual residual critical
quotient are displayed separately. -/
theorem errorTerm_eq_stationaryCorrection
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    errorTerm F K DeltaF DeltaK chiF psiF =
      A.residualPhase *
        ((psiF (A.A * trace F K A.u) : ℂ) *
          (chiF A.zZero : ℂ) *
          ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ))⁻¹ := by
  rw [D.errorTerm_eq_assembledFactors hDeltaF hDeltaK,
    FirstMainPhaseFactors.assembled, A.endpointFactor_eq_one,
    A.admissibleFactor_eq_one, A.elementaryFactor_eq_bracket_inv]
  simp only [residualPhase, FirstMainPhaseData.factors, one_mul]
  ring

/-- Proposition `prop:exact-odd-assembly` after only the justified pointwise
linearizations.  No finite residual phase is cancelled. -/
theorem errorTerm_eq_normTraceCorrection
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    errorTerm F K DeltaF DeltaK chiF psiF =
      A.residualPhase * (psiF (-A.A * A.X) : ℂ) := by
  rw [A.errorTerm_eq_stationaryCorrection hDeltaF hDeltaK,
    A.correctionBracket_inv_eq_phase_neg]

/-- Structured output of the odd assembly, retaining every independently
assembled component as well as both exact orientations of the result. -/
structure Result
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) : Prop where
  range : PhaseParameterRange t m
  normIdentity : norm F K A.u = A.n
  endpoint : D.factors.endpoint = 1
  admissible : D.factors.admissibleCharacter = 1
  elementary : D.factors.elementary =
    ((psiF (A.A * trace F K A.u) : ℂ) *
      (chiF A.zZero : ℂ) *
      ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ))⁻¹
  residual : A.residualPhase =
    D.criticalNumerator / D.criticalDenominator
  indexedRowsAreStationary : ∀ i, ∃
    (S : LocalLamprechtPhaseData F
      (data.normCharacterData (A.normCharacterIndex i)) data.baseAddChar),
      D.normCharacter (A.normCharacterIndex i) = LocalPhaseData.stationary S
  indexedResidual : A.residualPhase =
    (D.extension.criticalFactor *
        ∏ i : I,
          (D.normCharacter (A.normCharacterIndex i)).criticalFactor) /
      ((D.twist 1).criticalFactor *
        ∏ i : I,
          (D.twist (A.normCharacterIndex i)).criticalFactor)
  stationaryAssembly : errorTerm F K DeltaF DeltaK chiF psiF =
    A.residualPhase *
      ((psiF (A.A * trace F K A.u) : ℂ) *
        (chiF A.zZero : ℂ) *
        ∏ i : I, (A.normCharacterPower i (A.z i) : ℂ))⁻¹
  normTraceAssembly : errorTerm F K DeltaF DeltaK chiF psiF =
    A.residualPhase * (psiF (-A.A * A.X) : ℂ)

theorem result
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactOddPhaseAssembly F K chiF psiF data D
      (t := t) (m := m) I) :
    A.Result hDeltaF hDeltaK where
  range := A.parameterRange
  normIdentity := A.norm_u
  endpoint := A.endpointFactor_eq_one
  admissible := A.admissibleFactor_eq_one
  elementary := A.elementaryFactor_eq_bracket_inv
  residual := rfl
  indexedRowsAreStationary := A.normCharacterStationary
  indexedResidual := A.residualPhase_eq_indexedQuotient
  stationaryAssembly := A.errorTerm_eq_stationaryCorrection hDeltaF hDeltaK
  normTraceAssembly := A.errorTerm_eq_normTraceCorrection hDeltaF hDeltaK

end ExactOddPhaseAssembly

/-! ## Canonical nonidentity indexing -/

abbrev OddNormIndex (F K : Type) [DivisionRing F] [DivisionRing K]
    [Module F K] := {j : ZMod (Module.finrank F K) // j ≠ 0}

noncomputable def oddNormCharacterIndexing
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Option (OddNormIndex F K) ≃ NormCharacter F K :=
  (Equiv.optionSubtypeNe (0 : ZMod (Module.finrank F K))).trans
    ((Multiplicative.ofAdd : ZMod (Module.finrank F K) ≃
      Multiplicative (ZMod (Module.finrank F K))).trans
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv)

@[simp]
theorem oddNormCharacterIndexing_none
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    oddNormCharacterIndexing F K ht hres pi hpi hgen none = 1 := by
  simp [oddNormCharacterIndexing]

@[simp]
theorem oddNormCharacterIndexing_some
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (j : OddNormIndex F K) :
    oddNormCharacterIndexing F K ht hres pi hpi hgen (some j) =
      ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd (j : ZMod (Module.finrank F K))) := by
  simp [oddNormCharacterIndexing]

/-- Reindex actual stationary twist rows along an exhaustive equivalence. -/
theorem allTwistsStationary_of_equiv
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {D : FirstMainPhaseData F K chiF psiF data}
    {J : Type*} (e : J ≃ NormCharacter F K)
    (hrow : ∀ j : J, ∃
      S : LocalLamprechtPhaseData F (data.twistData (e j)) data.baseAddChar,
      D.twist (e j) = LocalPhaseData.stationary S) :
    ∀ mu : NormCharacter F K, ∃
      S : LocalLamprechtPhaseData F (data.twistData mu) data.baseAddChar,
      D.twist mu = LocalPhaseData.stationary S := by
  intro mu
  let j := e.symm mu
  have hej : e j = mu := e.apply_symm_apply mu
  rw [← hej]
  exact hrow j

/-- Reindex the supplied nonidentity stationary norm rows; the missing
`none` row is exactly the identity endpoint. -/
theorem nonidentityNormStationary_of_optionEquiv
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {D : FirstMainPhaseData F K chiF psiF data}
    {I : Type*} (e : Option I ≃ NormCharacter F K)
    (enone : e none = 1)
    (hrow : ∀ i : I, ∃
      S : LocalLamprechtPhaseData F (data.normCharacterData (e (some i)))
        data.baseAddChar,
      D.normCharacter (e (some i)) = LocalPhaseData.stationary S) :
    ∀ mu : NormCharacter F K, mu ≠ 1 → ∃
      S : LocalLamprechtPhaseData F (data.normCharacterData mu)
        data.baseAddChar,
      D.normCharacter mu = LocalPhaseData.stationary S := by
  intro mu hmu
  cases hpre : e.symm mu with
  | none =>
      exfalso
      apply hmu
      calc
        mu = e (e.symm mu) := (e.apply_symm_apply mu).symm
        _ = e none := congrArg e hpre
        _ = 1 := enone
  | some i =>
      have hei : e (some i) = mu := by
        calc
          e (some i) = e (e.symm mu) := congrArg e hpre.symm
          _ = mu := e.apply_symm_apply mu
      subst mu
      exact hrow i

/-- Actual stationary extension, nonidentity norm, and twist rows force the
endpoint quotient to one.  The identity norm row is derived from the
computational datum and evaluated by the proved trivial-character formula. -/
theorem endpointFactor_eq_one_of_actual_stationary_rows
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {D : FirstMainPhaseData F K chiF psiF data}
    (extensionStationary : ∃
      S : LocalLamprechtPhaseData K data.extensionQuasiChar
        data.extensionAddChar,
      D.extension = LocalPhaseData.stationary S)
    (nonidentityNormStationary : ∀ mu : NormCharacter F K, mu ≠ 1 → ∃
      S : LocalLamprechtPhaseData F (data.normCharacterData mu)
        data.baseAddChar,
      D.normCharacter mu = LocalPhaseData.stationary S)
    (twistStationary : ∀ mu : NormCharacter F K, ∃
      S : LocalLamprechtPhaseData F (data.twistData mu) data.baseAddChar,
      D.twist mu = LocalPhaseData.stationary S) :
    D.factors.endpoint = 1 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rcases extensionStationary with ⟨Sext, hExt⟩
  rcases identityNormCharacterEndpoint_of_phaseData D with
    ⟨hOne, GammaOne, hOne⟩
  have hOneCharacter : (data.normCharacterData 1).character = 1 := by
    rw [data.normCharacterData_character]
    ext x
    simp
  have hOneEndpoint : (D.normCharacter 1).endpointFactor = 1 := by
    rw [hOne]
    exact delta_trivial_of_character_eq_one F (data.normCharacterData 1)
      hOneCharacter data.baseAddChar GammaOne
  have hNorm : D.endpointNumerator = 1 := by
    rw [FirstMainPhaseData.endpointNumerator, hExt]
    simp only [LocalPhaseData.endpointFactor, one_mul]
    apply Finset.prod_eq_one
    intro mu _hmu
    by_cases hmu : mu = 1
    · subst mu
      exact hOneEndpoint
    · rcases nonidentityNormStationary mu hmu with ⟨Smu, hSmu⟩
      simpa only [hSmu, LocalPhaseData.endpointFactor]
  have hTwist : D.endpointDenominator = 1 := by
    rw [FirstMainPhaseData.endpointDenominator]
    apply Finset.prod_eq_one
    intro mu _hmu
    rcases twistStationary mu with ⟨Smu, hSmu⟩
    simpa only [hSmu, LocalPhaseData.endpointFactor]
  rw [FirstMainPhaseData.factors, hNorm, hTwist]
  norm_num

/-- The literal Teichmüller lift attached to a nonidentity cyclic index.
This is the scalar `[j]` in the manuscript's norm--trace correction, not an
arbitrary field parameter. -/
noncomputable def oddNormIndexScalar
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (j : OddNormIndex F K) : F :=
  highIntermediateTeichmullerScalar F (Module.finrank F K)
    (residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen) (j : ZMod (Module.finrank F K))

/-- The literal nonzero Teichmüller scalar used by an odd norm-character
row, bundled as a field unit.  Its value is the displayed table scalar;
nonvanishing follows from the nonidentity index and makes no representative
choice. -/
noncomputable def oddNormIndexUnit
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (j : OddNormIndex F K) : Fˣ :=
  Units.mk0 (oddNormIndexScalar F K ht hres pi hpi hgen htpos j) (by
    apply (ord_ne_top_iff F).1
    unfold oddNormIndexScalar
    rw [highParameter_intermediate_teichmuller_ord_eq_zero F
      (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen)
      (j : ZMod (Module.finrank F K)) j.property]
    simp)

@[simp]
theorem oddNormIndexUnit_coe
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (j : OddNormIndex F K) :
    ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) =
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j :=
  rfl

/-! ## Manuscript correction units for exact odd assembly -/

/-- The Teichmüller scalar for every residue index, including zero.  The
nonidentity restriction is imposed only when a norm-character row is used. -/
noncomputable def oddNormAllIndexScalar
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (j : ZMod (Module.finrank F K)) : F :=
  highIntermediateTeichmullerScalar F (Module.finrank F K)
    (residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen) j

/-- The full Teichmüller denominator `∏_[k](n+[k])` occurring in the
exceptional odd correction. -/
noncomputable def oddNormCorrectionDenominator
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [NeZero (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (n : F) : F :=
  Finset.univ.prod (fun k : ZMod (Module.finrank F K) ↦
    n + oddNormAllIndexScalar F K ht hres pi hpi hgen htpos k)

/-- Exact nonvanishing data needed to bundle the manuscript correction
ratios as units.  The values themselves are definitions below; no arbitrary
field representative or arbitrary correction unit is a field of this
record. -/
structure OddNormCorrectionUnitData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [NeZero (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (u : K) (n : F) : Prop where
  norm_u : norm F K u = n
  zeroNumerator_ne_zero :
    norm F K (algebraMap F K n - u) ≠ 0
  zeroDenominator_ne_zero :
    oddNormCorrectionDenominator F K ht hres pi hpi hgen htpos n ≠ 0
  numerator_ne_zero : ∀ j : OddNormIndex F K,
    norm F K (u + algebraMap F K
      (oddNormIndexScalar F K ht hres pi hpi hgen htpos j)) ≠ 0
  denominator_ne_zero : ∀ j : OddNormIndex F K,
    n + oddNormIndexScalar F K ht hres pi hpi hgen htpos j ≠ 0

namespace OddNormCorrectionUnitData

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [NeZero (Module.finrank F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (htpos : 0 < t) {u : K} {n : F}
  (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos u n)

/-- The exceptional correction is literally
`N(n-u) / ∏_[k](n+[k])`, bundled only after both nonzero facts are supplied. -/
noncomputable def zZero : Fˣ :=
  Units.mk0
    (norm F K (algebraMap F K n - u) /
      oddNormCorrectionDenominator F K ht hres pi hpi hgen htpos n)
    (div_ne_zero C.zeroNumerator_ne_zero C.zeroDenominator_ne_zero)

/-- The nonzero-index correction is literally `N(u+[j])/(n+[j])`. -/
noncomputable def z (j : OddNormIndex F K) : Fˣ :=
  Units.mk0
    (norm F K (u + algebraMap F K
        (oddNormIndexScalar F K ht hres pi hpi hgen htpos j)) /
      (n + oddNormIndexScalar F K ht hres pi hpi hgen htpos j))
    (div_ne_zero (C.numerator_ne_zero j) (C.denominator_ne_zero j))

@[simp] theorem coe_zZero :
    (C.zZero ht hres pi hpi hgen htpos : F) =
      norm F K (algebraMap F K n - u) /
        oddNormCorrectionDenominator F K ht hres pi hpi hgen htpos n := rfl

@[simp] theorem coe_z (j : OddNormIndex F K) :
    (C.z ht hres pi hpi hgen htpos j : F) =
      norm F K (u + algebraMap F K
          (oddNormIndexScalar F K ht hres pi hpi hgen htpos j)) /
        (n + oddNormIndexScalar F K ht hres pi hpi hgen htpos j) := rfl

/-- The explicit upstairs unit whose norm is killed in the nonzero row
character bridge. -/
noncomputable def scaledNumeratorUnit (j : OddNormIndex F K) : Kˣ :=
  Units.mk0
      (u + algebraMap F K
        (oddNormIndexScalar F K ht hres pi hpi hgen htpos j))
      ((Algebra.norm_ne_zero_iff).1 (C.numerator_ne_zero j)) /
    Units.map (algebraMap F K)
      (oddNormIndexUnit F K ht hres pi hpi hgen htpos j)

end OddNormCorrectionUnitData

/-! ### Elementary odd-index algebra -/

/-- Splitting the zero Teichmüller index from the nonzero indices gives the
exact signed additive identity used by both odd parameter tables. -/
theorem oddNormalizedAdditiveRatioIdentity
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [NeZero (Module.finrank F K)]
    (A n : F) (u : K) (lam : ZMod (Module.finrank F K) → F)
    (hlam0 : lam 0 = 0) :
    A * (n + lam 0) +
        ∑ j : OddNormIndex F K, A * (n + lam j) =
      A * trace F K u +
        trace F K (algebraMap F K A * (algebraMap F K n - u)) +
        ∑ j : OddNormIndex F K, A * lam j := by
  have htraceScalar (a : F) (z : K) :
      trace F K (algebraMap F K a * z) = a * trace F K z := by
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul a z
  rw [← Fintype.sum_eq_add_sum_subtype_ne
    (fun j : ZMod (Module.finrank F K) ↦ A * (n + lam j)) 0]
  rw [htraceScalar, map_sub, trace_algebraMap]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card]
  have hsumlam :
      (∑ j : ZMod (Module.finrank F K), A * lam j) =
        ∑ j : OddNormIndex F K, A * lam j := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun j : ZMod (Module.finrank F K) ↦ A * lam j) 0, hlam0]
    simp
  rw [hsumlam]
  simp only [mul_zero, zero_add, nsmul_eq_mul]
  ring

/-- A common scalar in every odd linear row cancels against the norm of the
same scalar in the upstairs row. -/
theorem oddHighZZeroScalingIdentity
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [NeZero (Module.finrank F K)]
    (c n : F) (hc : c ≠ 0) (u : K)
    (lam : ZMod (Module.finrank F K) → F) :
    norm F K (algebraMap F K c * (algebraMap F K n - u)) /
        ((c * (n + lam 0)) *
          ∏ j : OddNormIndex F K, c * (n + lam j)) =
      norm F K (algebraMap F K n - u) /
        Finset.univ.prod
          (fun j : ZMod (Module.finrank F K) ↦ n + lam j) := by
  have hprod :
      (c * (n + lam 0)) *
          ∏ j : OddNormIndex F K, c * (n + lam j) =
        c ^ Module.finrank F K *
          Finset.univ.prod
            (fun j : ZMod (Module.finrank F K) ↦ n + lam j) := by
    rw [← Fintype.prod_eq_mul_prod_subtype_ne
      (fun j : ZMod (Module.finrank F K) ↦ c * (n + lam j)) 0]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ZMod.card]
  rw [map_mul, norm_algebraMap, hprod]
  field_simp [hc]

/-- In the low table the common scalar additionally contains the essential
unit `epsilon1`; its norm is retained until this exact cancellation. -/
theorem oddLowZZeroScalingIdentity
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [NeZero (Module.finrank F K)]
    (c eta n : F) (hc : c ≠ 0) (heta : eta ≠ 0)
    (epsilon1 : K) (hnormepsilon : norm F K epsilon1 = eta) (u : K)
    (lam : ZMod (Module.finrank F K) → F) (hlam0 : lam 0 = 0) :
    norm F K ((algebraMap F K c / epsilon1) *
        (algebraMap F K n - u)) /
        (((c * n) / eta) *
          ∏ j : OddNormIndex F K, c * (n + lam j)) =
      norm F K (algebraMap F K n - u) /
        Finset.univ.prod
          (fun j : ZMod (Module.finrank F K) ↦ n + lam j) := by
  have hprod :
      ((c * n) / eta) *
          ∏ j : OddNormIndex F K, c * (n + lam j) =
        (c ^ Module.finrank F K / eta) *
          Finset.univ.prod
            (fun j : ZMod (Module.finrank F K) ↦ n + lam j) := by
    have hall :
        (c * (n + lam 0)) *
            ∏ j : OddNormIndex F K, c * (n + lam j) =
          c ^ Module.finrank F K *
            Finset.univ.prod
              (fun j : ZMod (Module.finrank F K) ↦ n + lam j) := by
      rw [← Fintype.prod_eq_mul_prod_subtype_ne
        (fun j : ZMod (Module.finrank F K) ↦ c * (n + lam j)) 0]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ZMod.card]
    rw [hlam0] at hall
    simp only [add_zero] at hall
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      c * n * eta⁻¹ * ∏ j : OddNormIndex F K, c * (n + lam j) =
          eta⁻¹ * ((c * n) *
            ∏ j : OddNormIndex F K, c * (n + lam j)) := by ring
      _ = eta⁻¹ * (c ^ Module.finrank F K *
          Finset.univ.prod
            (fun j : ZMod (Module.finrank F K) ↦ n + lam j)) := by
            rw [hall]
      _ = c ^ Module.finrank F K * eta⁻¹ *
          Finset.univ.prod
            (fun j : ZMod (Module.finrank F K) ↦ n + lam j) := by ring
  rw [hprod]
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [norm_algebraMap, hnormepsilon]
  field_simp [hc, heta]

end

end LanglandsFirstMainLemma
