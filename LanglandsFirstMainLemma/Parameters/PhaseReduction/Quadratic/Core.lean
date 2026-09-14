import LanglandsFirstMainLemma.Parameters.PhaseReduction.Range
import LanglandsFirstMainLemma.Parameters.PhaseReduction.FactorSeparation
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.Core

/-!
# Exact wild-quadratic phase assembly core

This module packages the exact wild-quadratic norm-character indexing,
raw ratio coordinates, correction data, and generic complete-result assembly.
No high- or low-table provenance is selected here.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Exact wild-quadratic stationary assembly -/

/-- Reindex the two actual norm characters.  The identity character is
required to be an endpoint package, hence has no stationary class or fake
representative. -/
structure QuadraticCriticalIndexing
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
    (D : FirstMainPhaseData F K chiF psiF data) where
  tau : NormCharacter F K
  index : Bool ≃ NormCharacter F K
  index_true : index true = 1
  index_false : index false = tau

namespace QuadraticCriticalIndexing

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
  {D : FirstMainPhaseData F K chiF psiF data}

/-- The critical quotient is derived from the upper, nontrivial norm,
base-twist, and nontrivial-twist local packages themselves. -/
theorem critical_eq_four_actual_factors
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    D.factors.critical =
      (D.extension.criticalFactor *
          (D.normCharacter Q.tau).criticalFactor) /
        ((D.twist 1).criticalFactor *
          (D.twist Q.tau).criticalFactor) := by
  letI := Fintype.ofFinite (NormCharacter F K)
  have hnorm :
      (∏ mu : NormCharacter F K, (D.normCharacter mu).criticalFactor) =
        (D.normCharacter 1).criticalFactor *
          (D.normCharacter Q.tau).criticalFactor := by
    rw [← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦ (D.normCharacter mu).criticalFactor)]
    rw [Fintype.prod_bool, Q.index_true, Q.index_false]
  have htwist :
      (∏ mu : NormCharacter F K, (D.twist mu).criticalFactor) =
        (D.twist 1).criticalFactor * (D.twist Q.tau).criticalFactor := by
    rw [← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦ (D.twist mu).criticalFactor)]
    rw [Fintype.prod_bool, Q.index_true, Q.index_false]
  have hid : (D.normCharacter 1).criticalFactor = 1 := by
    rcases identityNormCharacterEndpoint_of_phaseData D with
      ⟨h, Gamma, hEq⟩
    rw [hEq]
    rfl
  simp only [FirstMainPhaseData.factors,
    FirstMainPhaseData.criticalNumerator,
    FirstMainPhaseData.criticalDenominator,
    hnorm, htwist, hid, one_mul]

theorem critical_denominator_ne_zero
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    (D.twist 1).criticalFactor * (D.twist Q.tau).criticalFactor ≠ 0 :=
  mul_ne_zero (D.twist 1).criticalFactor_ne_zero
    (D.twist Q.tau).criticalFactor_ne_zero

end QuadraticCriticalIndexing

/-- Raw quadratic norm-ratio coordinates, before either multiplicative
character is evaluated.  Both ratios retain their literal denominator
directions.  The elements `u` and `n` are parameters, so high- and low-table
wrappers can tie them definitionally to their own simultaneous stationary
data. -/
structure QuadraticRawRatioCoordinates
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (u : K) (n : Fˣ) where
  zZero : Fˣ
  zOne : Fˣ
  x : F
  y : F
  zZero_eq : (zZero : F) = 1 + x
  zOne_eq : (zOne : F) = 1 + y
  one_add_n_ne_zero : 1 + (n : F) ≠ 0
  zZero_ratio : (zZero : F) =
    norm F K (algebraMap F K (n : F) - u) /
      ((n : F) * (1 + (n : F)))
  zOne_ratio : (zOne : F) =
    norm F K (1 + u) / (1 + (n : F))

namespace QuadraticRawRatioCoordinates

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K]
  {u : K} {n : Fˣ}

/-- Cross-multiplied first raw ratio.  This is still a field identity, not
an equality of character values. -/
theorem norm_sub_eq
    (C : QuadraticRawRatioCoordinates F K u n) :
    norm F K (algebraMap F K (n : F) - u) =
      (n : F) * (1 + (n : F)) * (C.zZero : F) := by
  rw [C.zZero_ratio]
  field_simp [Units.ne_zero n, C.one_add_n_ne_zero]

/-- Cross-multiplied second raw ratio, with the manuscript's denominator
`1+n` in the same direction. -/
theorem norm_one_add_eq
    (C : QuadraticRawRatioCoordinates F K u n) :
    norm F K (1 + u) =
      (1 + (n : F)) * (C.zOne : F) := by
  rw [C.zOne_ratio]
  field_simp [C.one_add_n_ne_zero]

/-- Since `z1` and `1+n` are nonzero, the second exact ratio itself proves
that `1+u` is nonzero. -/
  theorem one_add_u_ne_zero
    (C : QuadraticRawRatioCoordinates F K u n) :
    1 + u ≠ 0 := by
  intro hu
  have hnorm : norm F K (1 + u) = 0 := by rw [hu, Algebra.norm_zero]
  rw [C.norm_one_add_eq] at hnorm
  exact mul_ne_zero C.one_add_n_ne_zero (Units.ne_zero C.zOne) hnorm

/-- The second raw norm argument bundled only after its nonvanishing has
been derived from the ratio. -/
def oneAddUUnit
    (C : QuadraticRawRatioCoordinates F K u n) : Kˣ :=
  Units.mk0 (1 + u) C.one_add_u_ne_zero

@[simp]
theorem coe_oneAddUUnit
    (C : QuadraticRawRatioCoordinates F K u n) :
    ((C.oneAddUUnit : Kˣ) : K) = 1 + u :=
  rfl

/-- Degree two gives the signed additive argument of the four normalized
stationary rows before applying the additive character. -/
theorem signedTraceSum_eq
    (hdegree : Module.finrank F K = 2) (u : K) (n : F) :
    trace F K (algebraMap F K n - u) + 1 - n - (n + 1) =
      -trace F K u := by
  rw [map_sub, trace_algebraMap, hdegree]
  ring

end QuadraticRawRatioCoordinates

/-- Raw wild-quadratic complete assembly.  The essential break-level unit is
retained in the selected twist numerator.  The admissible-character scalar
and its inverse elementary scalar remain separately visible, as do the
positive additive and inverse multiplicative-character elementary products.
The critical quotient is supplied by the four actual local packages through
`indexing`. -/
structure ExactQuadraticPhaseAssembly
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
    {t m : ℕ} where
  baseData : LocalQuasiCharData F
  baseData_eq : baseData = data.twistData 1
  baseCharacter : baseData.character = chiF
  baseConductor : baseData.conductor = m
  parameterRange : PhaseParameterRange t m
  indexing : QuadraticCriticalIndexing F K chiF psiF data D
  A : F
  u : K
  n : F
  norm_u : norm F K u = n
  s : F
  s_eq : s = trace F K u
  zZero : Fˣ
  zOne : Fˣ
  x : F
  y : F
  zZero_eq : (zZero : F) = 1 + x
  zOne_eq : (zOne : F) = 1 + y
  X : F
  X_eq : X = s + n * x + y
  breakUnit : unitFiltration F t
  stationaryScale : F
  baseStationaryNumerator : F
  twistStationaryNumerator : F
  twistStationaryNumerator_eq :
    twistStationaryNumerator = baseStationaryNumerator +
      stationaryScale * (((breakUnit : unitFiltration F t) : Fˣ) : F)
  scalarCorrection : ℂˣ
  endpointFactor_eq : D.factors.endpoint = 1
  admissibleNumerator_eq : D.admissibleNumerator =
    (scalarCorrection : ℂ)⁻¹ * D.admissibleDenominator
  additiveNumerator_eq : D.elementaryAdditiveNumerator =
    (psiF (-A * s) : ℂ) * D.elementaryAdditiveDenominator
  multiplicativeNumerator_eq : D.elementaryMultiplicativeNumerator =
    (scalarCorrection : ℂ) * (chiF zZero : ℂ)⁻¹ *
      (indexing.tau.1 zOne : ℂ)⁻¹ *
        D.elementaryMultiplicativeDenominator

namespace ExactQuadraticPhaseAssembly

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
  {t m : ℕ}

/-- With the genuine degree-two indexing, the four stationary rows force
the endpoint quotient to one.  The identity norm-character row stays an
endpoint package and is never assigned a stationary representative. -/
theorem endpointFactor_eq_one_of_quadratic_actual_rows
    (Q : QuadraticCriticalIndexing F K chiF psiF data D)
    (extensionStationary : ∃
      S : LocalLamprechtPhaseData K data.extensionQuasiChar
        data.extensionAddChar,
      D.extension = LocalPhaseData.stationary S)
    (tauStationary : ∃
      S : LocalLamprechtPhaseData F (data.normCharacterData Q.tau)
        data.baseAddChar,
      D.normCharacter Q.tau = LocalPhaseData.stationary S)
    (baseStationary : ∃
      S : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar,
      D.twist 1 = LocalPhaseData.stationary S)
    (twistStationary : ∃
      S : LocalLamprechtPhaseData F (data.twistData Q.tau) data.baseAddChar,
      D.twist Q.tau = LocalPhaseData.stationary S) :
    D.factors.endpoint = 1 := by
  apply endpointFactor_eq_one_of_actual_stationary_rows extensionStationary
  · intro mu hmu
    obtain ⟨b, rfl⟩ := Q.index.surjective mu
    cases b with
    | false =>
        rw [Q.index_false]
        exact tauStationary
    | true => exact (hmu Q.index_true).elim
  · intro mu
    obtain ⟨b, rfl⟩ := Q.index.surjective mu
    cases b with
    | false =>
        rw [Q.index_false]
        exact twistStationary
    | true =>
        rw [Q.index_true]
        exact baseStationary

/-- Reindex the admissible-character quotient by the actual extension,
nonidentity norm, base, and nonidentity twist rows. -/
theorem admissibleFactor_eq_four_actual_rows
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    D.factors.admissibleCharacter =
      (D.extension.admissibleFactor *
          (D.normCharacter Q.tau).admissibleFactor) /
        ((D.twist 1).admissibleFactor *
          (D.twist Q.tau).admissibleFactor) := by
  letI := Fintype.ofFinite (NormCharacter F K)
  have hnorm :
      (∏ mu : NormCharacter F K,
          (D.normCharacter mu).admissibleFactor) =
        (D.normCharacter 1).admissibleFactor *
          (D.normCharacter Q.tau).admissibleFactor := by
    rw [← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦
        (D.normCharacter mu).admissibleFactor)]
    rw [Fintype.prod_bool, Q.index_true, Q.index_false]
  have htwist :
      (∏ mu : NormCharacter F K, (D.twist mu).admissibleFactor) =
        (D.twist 1).admissibleFactor *
          (D.twist Q.tau).admissibleFactor := by
    rw [← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦ (D.twist mu).admissibleFactor)]
    rw [Fintype.prod_bool, Q.index_true, Q.index_false]
  have hid : (D.normCharacter 1).admissibleFactor = 1 := by
    rcases identityNormCharacterEndpoint_of_phaseData D with
      ⟨h, Gamma, hEq⟩
    rw [hEq]
    rfl
  simp only [FirstMainPhaseData.factors,
    FirstMainPhaseData.admissibleNumerator,
    FirstMainPhaseData.admissibleDenominator,
    hnorm, htwist, hid, one_mul]

/-- Reindex the positive additive elementary numerator by the actual
extension and nonidentity norm-character rows.  The identity norm-character
row is an endpoint and therefore contributes exactly one, without acquiring
a stationary representative. -/
theorem elementaryAdditiveNumerator_eq_two_actual_rows
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    D.elementaryAdditiveNumerator =
      D.extension.elementaryAdditiveFactor *
        (D.normCharacter Q.tau).elementaryAdditiveFactor := by
  letI := Fintype.ofFinite (NormCharacter F K)
  have hnorm :
      (∏ mu : NormCharacter F K,
          (D.normCharacter mu).elementaryAdditiveFactor) =
        (D.normCharacter 1).elementaryAdditiveFactor *
          (D.normCharacter Q.tau).elementaryAdditiveFactor := by
    rw [← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦
        (D.normCharacter mu).elementaryAdditiveFactor)]
    rw [Fintype.prod_bool, Q.index_true, Q.index_false]
  have hid : (D.normCharacter 1).elementaryAdditiveFactor = 1 := by
    rcases identityNormCharacterEndpoint_of_phaseData D with
      ⟨h, Gamma, hEq⟩
    rw [hEq]
    rfl
  simp only [FirstMainPhaseData.elementaryAdditiveNumerator, hnorm, hid,
    one_mul]

/-- Reindex the positive additive elementary denominator by the actual base
and nonidentity twist rows. -/
theorem elementaryAdditiveDenominator_eq_two_actual_rows
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    D.elementaryAdditiveDenominator =
      (D.twist 1).elementaryAdditiveFactor *
        (D.twist Q.tau).elementaryAdditiveFactor := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rw [FirstMainPhaseData.elementaryAdditiveDenominator,
    ← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦
        (D.twist mu).elementaryAdditiveFactor)]
  rw [Fintype.prod_bool, Q.index_true, Q.index_false]

/-- Reindex the inverse multiplicative-character elementary numerator by the
actual extension and nonidentity norm-character rows.  Again the identity
norm-character row is the genuine endpoint contribution one. -/
theorem elementaryMultiplicativeNumerator_eq_two_actual_rows
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    D.elementaryMultiplicativeNumerator =
      D.extension.elementaryMultiplicativeFactor *
        (D.normCharacter Q.tau).elementaryMultiplicativeFactor := by
  letI := Fintype.ofFinite (NormCharacter F K)
  have hnorm :
      (∏ mu : NormCharacter F K,
          (D.normCharacter mu).elementaryMultiplicativeFactor) =
        (D.normCharacter 1).elementaryMultiplicativeFactor *
          (D.normCharacter Q.tau).elementaryMultiplicativeFactor := by
    rw [← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦
        (D.normCharacter mu).elementaryMultiplicativeFactor)]
    rw [Fintype.prod_bool, Q.index_true, Q.index_false]
  have hid : (D.normCharacter 1).elementaryMultiplicativeFactor = 1 := by
    rcases identityNormCharacterEndpoint_of_phaseData D with
      ⟨h, Gamma, hEq⟩
    rw [hEq]
    rfl
  simp only [FirstMainPhaseData.elementaryMultiplicativeNumerator, hnorm,
    hid, one_mul]

/-- Reindex the inverse multiplicative-character elementary denominator by
the actual base and nonidentity twist rows. -/
theorem elementaryMultiplicativeDenominator_eq_two_actual_rows
    (Q : QuadraticCriticalIndexing F K chiF psiF data D) :
    D.elementaryMultiplicativeDenominator =
      (D.twist 1).elementaryMultiplicativeFactor *
        (D.twist Q.tau).elementaryMultiplicativeFactor := by
  letI := Fintype.ofFinite (NormCharacter F K)
  rw [FirstMainPhaseData.elementaryMultiplicativeDenominator,
    ← Equiv.prod_comp Q.index
      (fun mu : NormCharacter F K ↦
        (D.twist mu).elementaryMultiplicativeFactor)]
  rw [Fintype.prod_bool, Q.index_true, Q.index_false]

def residualHasseQuotient
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) : ℂ :=
  (D.extension.criticalFactor *
      (D.normCharacter A.indexing.tau).criticalFactor) /
    ((D.twist 1).criticalFactor *
      (D.twist A.indexing.tau).criticalFactor)

theorem endpointFactor_eq_one
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    D.factors.endpoint = 1 :=
  A.endpointFactor_eq

/-- The selected admissible-character quotient is the inverse of the
explicit scalar correction.  In the high table this scalar is `tau(c)`;
in the low table it is one. -/
theorem admissibleFactor_eq_scalarInverse
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    D.factors.admissibleCharacter = (A.scalarCorrection : ℂ)⁻¹ := by
  rw [FirstMainPhaseData.factors, A.admissibleNumerator_eq]
  field_simp [D.admissibleDenominator_ne_zero]

/-- The signed sum of the four positive additive stationary values. -/
theorem elementaryAdditiveFactor_eq_tracePhase
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    D.elementaryAdditiveQuotient = (psiF (-A.A * A.s) : ℂ) := by
  rw [FirstMainPhaseData.elementaryAdditiveQuotient,
    A.additiveNumerator_eq]
  field_simp [D.elementaryAdditiveDenominator_ne_zero]

/-- The selected inverse multiplicative-character values, including the
scalar which cancels the admissible-character quotient. -/
theorem elementaryMultiplicativeFactor_eq_characterCorrection
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    D.elementaryMultiplicativeQuotient =
      (A.scalarCorrection : ℂ) * (chiF A.zZero : ℂ)⁻¹ *
        (A.indexing.tau.1 A.zOne : ℂ)⁻¹ := by
  rw [FirstMainPhaseData.elementaryMultiplicativeQuotient,
    A.multiplicativeNumerator_eq]
  field_simp [D.elementaryMultiplicativeDenominator_ne_zero]

theorem elementaryFactor_eq_correction
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    D.factors.elementary =
      (psiF (-A.A * A.s) : ℂ) * (A.scalarCorrection : ℂ) *
        (chiF A.zZero : ℂ)⁻¹ *
          (A.indexing.tau.1 A.zOne : ℂ)⁻¹ := by
  rw [D.elementaryFactor_eq_separatedQuotients,
    A.elementaryAdditiveFactor_eq_tracePhase,
    A.elementaryMultiplicativeFactor_eq_characterCorrection]
  ring

/-- The high scalar `tau(c)` (or low scalar one) cancels only after the
admissible-character and elementary quotients are multiplied. -/
theorem admissible_mul_elementary_eq_correction
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    D.factors.admissibleCharacter * D.factors.elementary =
      (psiF (-A.A * A.s) : ℂ) * (chiF A.zZero : ℂ)⁻¹ *
        (A.indexing.tau.1 A.zOne : ℂ)⁻¹ := by
  rw [A.admissibleFactor_eq_scalarInverse,
    A.elementaryFactor_eq_correction]
  field_simp

/-- The prerequisite-only form of Proposition
`prop:quadratic-complete-assembly`.  It retains the elementary unit
corrections and the quotient of the four actual critical phases; no
quadratic refinement or finite-field cancellation is used. -/
theorem errorTerm_eq_completeAssembly
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    errorTerm F K DeltaF DeltaK chiF psiF =
      A.residualHasseQuotient * (psiF (-A.A * A.s) : ℂ) *
        (chiF A.zZero : ℂ)⁻¹ *
          (A.indexing.tau.1 A.zOne : ℂ)⁻¹ := by
  rw [D.errorTerm_eq_assembledFactors hDeltaF hDeltaK,
    FirstMainPhaseFactors.assembled, A.endpointFactor_eq_one,
    A.indexing.critical_eq_four_actual_factors]
  rw [A.admissibleFactor_eq_scalarInverse,
    A.elementaryFactor_eq_correction]
  simp only [residualHasseQuotient]
  field_simp

/-- Structured output of the quadratic assembly.  The four local critical
phases and the elementary correction remain separately visible. -/
structure Result
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) : Prop where
  range : PhaseParameterRange t m
  normIdentity : norm F K A.u = A.n
  traceIdentity : A.s = trace F K A.u
  unitCoordinates : (A.zZero : F) = 1 + A.x ∧
    (A.zOne : F) = 1 + A.y
  correctionCoordinate : A.X = A.s + A.n * A.x + A.y
  breakUnitRetained : A.twistStationaryNumerator =
    A.baseStationaryNumerator + A.stationaryScale *
      (((A.breakUnit : unitFiltration F t) : Fˣ) : F)
  endpoint : D.factors.endpoint = 1
  admissible : D.factors.admissibleCharacter =
    (A.scalarCorrection : ℂ)⁻¹
  elementaryAdditive : D.elementaryAdditiveQuotient =
    (psiF (-A.A * A.s) : ℂ)
  elementaryMultiplicative : D.elementaryMultiplicativeQuotient =
    (A.scalarCorrection : ℂ) * (chiF A.zZero : ℂ)⁻¹ *
      (A.indexing.tau.1 A.zOne : ℂ)⁻¹
  elementary : D.factors.elementary =
    (psiF (-A.A * A.s) : ℂ) * (A.scalarCorrection : ℂ) *
      (chiF A.zZero : ℂ)⁻¹ *
        (A.indexing.tau.1 A.zOne : ℂ)⁻¹
  admissibleElementary :
    D.factors.admissibleCharacter * D.factors.elementary =
      (psiF (-A.A * A.s) : ℂ) * (chiF A.zZero : ℂ)⁻¹ *
        (A.indexing.tau.1 A.zOne : ℂ)⁻¹
  residual : D.factors.critical = A.residualHasseQuotient
  criticalDenominator :
    (D.twist 1).criticalFactor *
      (D.twist A.indexing.tau).criticalFactor ≠ 0
  completeAssembly : errorTerm F K DeltaF DeltaK chiF psiF =
    A.residualHasseQuotient * (psiF (-A.A * A.s) : ℂ) *
      (chiF A.zZero : ℂ)⁻¹ *
        (A.indexing.tau.1 A.zOne : ℂ)⁻¹

theorem result
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) :
    A.Result hDeltaF hDeltaK where
  range := A.parameterRange
  normIdentity := A.norm_u
  traceIdentity := A.s_eq
  unitCoordinates := ⟨A.zZero_eq, A.zOne_eq⟩
  correctionCoordinate := A.X_eq
  breakUnitRetained := A.twistStationaryNumerator_eq
  endpoint := A.endpointFactor_eq_one
  admissible := A.admissibleFactor_eq_scalarInverse
  elementaryAdditive := A.elementaryAdditiveFactor_eq_tracePhase
  elementaryMultiplicative :=
    A.elementaryMultiplicativeFactor_eq_characterCorrection
  elementary := A.elementaryFactor_eq_correction
  admissibleElementary := A.admissible_mul_elementary_eq_correction
  residual := A.indexing.critical_eq_four_actual_factors
  criticalDenominator := A.indexing.critical_denominator_ne_zero
  completeAssembly := A.errorTerm_eq_completeAssembly hDeltaF hDeltaK

/-- The exact conjugate correction coordinate in the quadratic norm ratios:
`uᵛ = -n/u`. -/
def dualRatio
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) : K :=
  -algebraMap F K A.n / A.u

/-- The non-finite-field correction data in the quadratic complete
assembly.  The two displayed ratios retain the literal denominator `1+n`,
and the two linearizations are kept separately before they are combined. -/
structure CompleteCorrectionData
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m)) : Prop where
  one_add_n_ne_zero : 1 + A.n ≠ 0
  zZero_ratio : (A.zZero : F) =
    norm F K (1 + A.dualRatio) / (1 + A.n)
  zOne_ratio : (A.zOne : F) =
    norm F K (1 + A.u) / (1 + A.n)
  chiLinearization : chiF A.zZero =
    psiF (A.A * A.n * A.x)
  tauLinearization : A.indexing.tau.1 A.zOne =
    psiF (A.A * A.y)

namespace CompleteCorrectionData

/-- Inversion of an additive-character value is evaluation at the negative
argument. -/
private theorem additive_inverse_eq_neg
    (z : F) : (psiF z : ℂ)⁻¹ = (psiF (-z) : ℂ) := by
  have h := congrArg (Units.val : ℂˣ → ℂ)
    (AddChar.map_neg_eq_inv psiF.toAddChar z)
  simpa only [ContinuousAddChar.toAddChar_apply,
    Units.val_inv_eq_inv_val] using h.symm

/-- The base-character inverse is its own separately justified additive
correction phase. -/
theorem chiInverse_eq_phase
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m))
    (C : A.CompleteCorrectionData) :
    (chiF A.zZero : ℂ)⁻¹ =
      (psiF (-A.A * A.n * A.x) : ℂ) := by
  have hchi := congrArg (Units.val : ℂˣ → ℂ) C.chiLinearization
  change (chiF A.zZero : ℂ) =
      (psiF (A.A * A.n * A.x) : ℂ) at hchi
  rw [hchi, additive_inverse_eq_neg]
  congr 2
  ring

/-- The norm-character inverse is its own separately justified additive
correction phase. -/
theorem tauInverse_eq_phase
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m))
    (C : A.CompleteCorrectionData) :
    (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
      (psiF (-A.A * A.y) : ℂ) := by
  have htau := congrArg (Units.val : ℂˣ → ℂ) C.tauLinearization
  change (A.indexing.tau.1 A.zOne : ℂ) =
      (psiF (A.A * A.y) : ℂ) at htau
  rw [htau, additive_inverse_eq_neg]
  congr 2
  ring

/-- Combine only the two justified pointwise linearizations.  The residual
quadratic/Hasse quotient is untouched. -/
theorem elementaryCorrection_eq_phase
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m))
    (C : A.CompleteCorrectionData) :
    (psiF (-A.A * A.s) : ℂ) * (chiF A.zZero : ℂ)⁻¹ *
        (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
      (psiF (-A.A * A.X) : ℂ) := by
  rw [C.chiInverse_eq_phase A, C.tauInverse_eq_phase A]
  have hmapC (z w : F) :
      (psiF (z + w) : ℂ) = (psiF z : ℂ) * (psiF w : ℂ) :=
    congrArg (Units.val : ℂˣ → ℂ)
      (ContinuousAddChar.map_add_eq_mul psiF z w)
  rw [← hmapC, ← hmapC]
  congr 2
  rw [A.X_eq]
  ring

/-- Exact quadratic residual reduction after the norm-ratio corrections,
before any Hasse or finite-field phase cancellation. -/
theorem errorTerm_eq_residual_mul_phase
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m))
    (C : A.CompleteCorrectionData) :
    errorTerm F K DeltaF DeltaK chiF psiF =
      A.residualHasseQuotient * (psiF (-A.A * A.X) : ℂ) := by
  rw [A.errorTerm_eq_completeAssembly hDeltaF hDeltaK]
  calc
    A.residualHasseQuotient * (psiF (-A.A * A.s) : ℂ) *
          (chiF A.zZero : ℂ)⁻¹ *
            (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
        A.residualHasseQuotient *
          ((psiF (-A.A * A.s) : ℂ) * (chiF A.zZero : ℂ)⁻¹ *
            (A.indexing.tau.1 A.zOne : ℂ)⁻¹) := by ring
    _ = A.residualHasseQuotient * (psiF (-A.A * A.X) : ℂ) := by
      rw [C.elementaryCorrection_eq_phase A]

/-- Structured quadratic output exposing the exact ratio directions,
pointwise corrections, and reduced norm--trace phase while retaining the
unevaluated residual quotient. -/
structure CompleteResult
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m))
    (C : A.CompleteCorrectionData) : Prop extends
      A.Result hDeltaF hDeltaK where
  denominator : 1 + A.n ≠ 0
  dual : A.dualRatio = -algebraMap F K A.n / A.u
  exactRatios : (A.zZero : F) =
      norm F K (1 + A.dualRatio) / (1 + A.n) ∧
    (A.zOne : F) = norm F K (1 + A.u) / (1 + A.n)
  pointwiseCorrections : chiF A.zZero = psiF (A.A * A.n * A.x) ∧
    A.indexing.tau.1 A.zOne = psiF (A.A * A.y)
  baseCharacterInversePhase : (chiF A.zZero : ℂ)⁻¹ =
    (psiF (-A.A * A.n * A.x) : ℂ)
  normCharacterInversePhase :
    (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
      (psiF (-A.A * A.y) : ℂ)
  normTraceAssembly : errorTerm F K DeltaF DeltaK chiF psiF =
    A.residualHasseQuotient * (psiF (-A.A * A.X) : ℂ)

theorem completeResult
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
      (t := t) (m := m))
    (C : A.CompleteCorrectionData) :
    C.CompleteResult hDeltaF hDeltaK A where
  toResult := A.result hDeltaF hDeltaK
  denominator := C.one_add_n_ne_zero
  dual := rfl
  exactRatios := ⟨C.zZero_ratio, C.zOne_ratio⟩
  pointwiseCorrections := ⟨C.chiLinearization, C.tauLinearization⟩
  baseCharacterInversePhase := C.chiInverse_eq_phase A
  normCharacterInversePhase := C.tauInverse_eq_phase A
  normTraceAssembly := C.errorTerm_eq_residual_mul_phase hDeltaF hDeltaK A

end CompleteCorrectionData

end ExactQuadraticPhaseAssembly

end

end LanglandsFirstMainLemma
