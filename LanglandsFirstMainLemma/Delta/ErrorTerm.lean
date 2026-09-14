import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Delta.Nonvanishing

/-!
# The First-Main-Lemma error term

This file formalizes equation `eq:error-term` and Lemma
`lem:twist-invariance` from the authoritative manuscript.  The quotient is
oriented as left side divided by right side.  Its denominator and numerator
are proved nonzero from `deltaFinite_ne_zero`; no instance of the First Main
identity is assumed.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

/-- A local-constant function is computational when, on every package of
exact conductor data, it agrees with the representative-free finite local
constant.  Independence of the admissible denominator is already built into
`deltaFinite`.

This is a compatibility condition, not a nonvanishing hypothesis.
Nonvanishing is derived below from `deltaFinite_ne_zero`. -/
def IsDeltaFiniteLocalConstant
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (Δ : LocalConstantFunction E) : Prop :=
  ∀ (χ : LocalQuasiCharData E) (ψ : LocalAddCharData E)
    (γ : AdmissibleGamma E χ ψ),
      Δ χ.character ψ.character = deltaFinite χ ψ γ

/-- A computational local-constant value is nonzero, as a consequence of
the proved nonvanishing of `deltaFinite`. -/
theorem IsDeltaFiniteLocalConstant.apply_ne_zero
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {Δ : LocalConstantFunction E} (hΔ : IsDeltaFiniteLocalConstant Δ)
    (χ : LocalQuasiCharData E) (ψ : LocalAddCharData E) :
    Δ χ.character ψ.character ≠ 0 := by
  let γ : AdmissibleGamma E χ ψ :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := E))
  rw [hΔ χ ψ γ]
  exact deltaFinite_ne_zero χ ψ γ

section ComputationalData

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]

/-- Exact conductor packages for every local-constant value occurring in the
two finite products of the First Main identity.  In particular,
`normCharacterData` and `twistData` range over the full `NormCharacter` type,
so the trivial character is included.

The character equalities make this data compatible with the precise
`NormCharacter`, `normQuasiChar`, `tracePullbackAddChar`, and
`FirstMainIdentity` definitions of `FirstMainStatement.lean`. -/
structure FirstMainComputationalData
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F) where
  baseAddChar : LocalAddCharData F
  baseAddChar_character : baseAddChar.character = ψF
  extensionQuasiChar : LocalQuasiCharData K
  extensionQuasiChar_character :
    extensionQuasiChar.character = normQuasiChar F K χF
  extensionAddChar : LocalAddCharData K
  extensionAddChar_character :
    extensionAddChar.character = tracePullbackAddChar F K ψF
  normCharacterData : NormCharacter F K → LocalQuasiCharData F
  normCharacterData_character :
    ∀ μ, (normCharacterData μ).character = μ.1
  twistData : NormCharacter F K → LocalQuasiCharData F
  twistData_character :
    ∀ μ, (twistData μ).character = μ.1 * χF

/-- The denominator in equation `eq:error-term` is nonzero.  Each factor is
identified with a `deltaFinite` value and then discharged by
`deltaFinite_ne_zero`. -/
theorem errorTerm_denominator_ne_zero
    {ΔF : LocalConstantFunction F}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) :
    firstMainRightSide F K ΔF χF ψF ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  change (∏ μ : NormCharacter F K, ΔF (μ.1 * χF) ψF) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr fun μ _hμ => by
    have h := hΔF.apply_ne_zero (data.twistData μ) data.baseAddChar
    simpa only [data.twistData_character μ, data.baseAddChar_character] using h

/-- The numerator in equation `eq:error-term` is nonzero.  The product is
not cancelled: its factors and the extension-field factor are proved
nonzero first. -/
theorem errorTerm_numerator_ne_zero
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (hΔK : IsDeltaFiniteLocalConstant ΔK)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) :
    firstMainLeftSide F K ΔF ΔK χF ψF ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  change
    ΔK (normQuasiChar F K χF) (tracePullbackAddChar F K ψF) *
      (∏ μ : NormCharacter F K, ΔF μ.1 ψF) ≠ 0
  apply mul_ne_zero
  · rw [← data.extensionQuasiChar_character,
      ← data.extensionAddChar_character]
    exact hΔK.apply_ne_zero data.extensionQuasiChar data.extensionAddChar
  · exact Finset.prod_ne_zero_iff.mpr fun μ _hμ => by
      have h := hΔF.apply_ne_zero
        (data.normCharacterData μ) data.baseAddChar
      simpa only [data.normCharacterData_character μ,
        data.baseAddChar_character] using h

end ComputationalData

section ErrorTerm

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]

/-- The computational First-Main-Lemma error term, with the orientation of
equation `eq:error-term`: the left side of the First Main identity divided by
its right side. -/
def errorTerm
    (ΔF : LocalConstantFunction F) (ΔK : LocalConstantFunction K)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F) : ℂ :=
  firstMainLeftSide F K ΔF ΔK χF ψF /
    firstMainRightSide F K ΔF χF ψF

/-- The error term itself is nonzero. -/
theorem errorTerm_ne_zero
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (hΔK : IsDeltaFiniteLocalConstant ΔK)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) :
    errorTerm F K ΔF ΔK χF ψF ≠ 0 :=
  div_ne_zero
    (errorTerm_numerator_ne_zero F K hΔF hΔK χF ψF data)
    (errorTerm_denominator_ne_zero F K hΔF χF ψF data)

/-- Multiplying the error term by its denominator recovers its numerator. -/
theorem errorTerm_mul_denominator
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) :
    errorTerm F K ΔF ΔK χF ψF *
        firstMainRightSide F K ΔF χF ψF =
      firstMainLeftSide F K ΔF ΔK χF ψF := by
  rw [errorTerm, div_mul_cancel₀ _
    (errorTerm_denominator_ne_zero F K hΔF χF ψF data)]

/-- The commuted denominator identity. -/
theorem denominator_mul_errorTerm
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) :
    firstMainRightSide F K ΔF χF ψF *
        errorTerm F K ΔF ΔK χF ψF =
      firstMainLeftSide F K ΔF ΔK χF ψF := by
  rw [mul_comm]
  exact errorTerm_mul_denominator F K hΔF χF ψF data

/-- A general rearrangement of the quotient equation. -/
theorem errorTerm_eq_iff_numerator_eq_mul_denominator
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) (z : ℂ) :
    errorTerm F K ΔF ΔK χF ψF = z ↔
      firstMainLeftSide F K ΔF ΔK χF ψF =
        z * firstMainRightSide F K ΔF χF ψF := by
  rw [errorTerm, div_eq_iff
    (errorTerm_denominator_ne_zero F K hΔF χF ψF data)]

/-- The symmetric rearrangement solving for the denominator. -/
theorem errorTerm_eq_iff_denominator_mul_eq_numerator
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) (z : ℂ) :
    errorTerm F K ΔF ΔK χF ψF = z ↔
      firstMainRightSide F K ΔF χF ψF * z =
        firstMainLeftSide F K ΔF ΔK χF ψF := by
  rw [errorTerm_eq_iff_numerator_eq_mul_denominator F K hΔF χF ψF data z]
  constructor <;> intro h
  · simpa [mul_comm] using h.symm
  · simpa [mul_comm] using h.symm

/-- The error term equals one exactly when the fixed-character First Main
identity holds.  Both implications use the proved denominator
nonvanishing; the identity is not assumed. -/
theorem errorTerm_eq_one_iff_firstMainIdentity
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K χF ψF) :
    errorTerm F K ΔF ΔK χF ψF = 1 ↔
      FirstMainIdentity F K ΔF ΔK χF ψF := by
  rw [errorTerm_eq_iff_numerator_eq_mul_denominator F K hΔF χF ψF data 1]
  simp only [one_mul, FirstMainIdentity]

/-- A single exact computational product identity implies the fixed-character
First Main identity.  All three products range over the full
`NormCharacter` type, including its trivial character.  The supplied
admissible denominators may vary with the norm character.

The proof first uses computational compatibility to identify the local
constants with `deltaFinite`.  It then invokes the supplied product identity
and cancels only the already-proved nonzero denominator through
`errorTerm_eq_one_iff_firstMainIdentity`. -/
theorem firstMainIdentity_of_deltaFinite_product
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : ContinuousQuasiChar F)
    (psiF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K chiF psiF)
    (gammaK : AdmissibleGamma K
      data.extensionQuasiChar data.extensionAddChar)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.normCharacterData mu) data.baseAddChar)
    (gammaTwist : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.twistData mu) data.baseAddChar)
    (hcomp :
      (by
        letI := Fintype.ofFinite (NormCharacter F K)
        exact deltaFinite data.extensionQuasiChar data.extensionAddChar gammaK *
          ∏ mu : NormCharacter F K,
            deltaFinite (data.normCharacterData mu) data.baseAddChar
              (gammaNorm mu)) =
        (by
          letI := Fintype.ofFinite (NormCharacter F K)
          exact ∏ mu : NormCharacter F K,
            deltaFinite (data.twistData mu) data.baseAddChar
              (gammaTwist mu))) :
    FirstMainIdentity F K DeltaF DeltaK chiF psiF := by
  letI := Fintype.ofFinite (NormCharacter F K)
  have hdenominator : firstMainRightSide F K DeltaF chiF psiF ≠ 0 :=
    errorTerm_denominator_ne_zero F K hDeltaF chiF psiF data
  apply (errorTerm_eq_one_iff_firstMainIdentity
    F K hDeltaF chiF psiF data).1
  rw [errorTerm, div_eq_one_iff_eq hdenominator]
  change
    DeltaK (normQuasiChar F K chiF) (tracePullbackAddChar F K psiF) *
        (∏ mu : NormCharacter F K, DeltaF mu.1 psiF) =
      ∏ mu : NormCharacter F K, DeltaF (mu.1 * chiF) psiF
  calc
    _ = deltaFinite data.extensionQuasiChar data.extensionAddChar gammaK *
          ∏ mu : NormCharacter F K,
            deltaFinite (data.normCharacterData mu) data.baseAddChar
              (gammaNorm mu) := by
      congr 1
      · simpa only [data.extensionQuasiChar_character,
          data.extensionAddChar_character] using
          hDeltaK data.extensionQuasiChar data.extensionAddChar gammaK
      apply Finset.prod_congr rfl
      intro mu _
      simpa only [data.normCharacterData_character mu,
        data.baseAddChar_character] using
        hDeltaF (data.normCharacterData mu) data.baseAddChar (gammaNorm mu)
    _ = ∏ mu : NormCharacter F K,
          deltaFinite (data.twistData mu) data.baseAddChar
            (gammaTwist mu) := hcomp
    _ = ∏ mu : NormCharacter F K, DeltaF (mu.1 * chiF) psiF := by
      apply Finset.prod_congr rfl
      intro mu _
      simpa only [data.twistData_character mu,
        data.baseAddChar_character] using
        (hDeltaF (data.twistData mu) data.baseAddChar (gammaTwist mu)).symm

end ErrorTerm

section NormCharacterReindexing

variable (F K : Type*) [CommRing F] [CommRing K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K]
  [TopologicalSpace F] [IsTopologicalRing F]
  [TopologicalSpace K] [IsModuleTopology F K]

/-- Multiplication by two project norm characters, constructed directly on
the exact subtype used by `FirstMainStatement`. -/
def normCharacterLeftMul (ν μ : NormCharacter F K) : NormCharacter F K := by
  refine ⟨ν.1 * μ.1, ?_⟩
  change (ν.1 * μ.1).pullback (continuousNormUnits F K) = 1
  have hν := ν.property
  have hμ := μ.property
  change ν.1.pullback (continuousNormUnits F K) = 1 at hν
  change μ.1.pullback (continuousNormUnits F K) = 1 at hμ
  rw [ContinuousQuasiChar.mul_pullback, hν, hμ]
  exact one_mul (1 : ContinuousQuasiChar K)

@[simp]
theorem normCharacterLeftMul_coe (ν μ : NormCharacter F K) :
    (normCharacterLeftMul F K ν μ).1 = ν.1 * μ.1 :=
  rfl

/-- Multiplication by a fixed norm character is genuinely bijective; its
inverse is multiplication by the inverse character. -/
def normCharacterLeftMulEquiv (ν : NormCharacter F K) :
    NormCharacter F K ≃ NormCharacter F K where
  toFun := normCharacterLeftMul F K ν
  invFun μ := by
    refine ⟨ν.1⁻¹ * μ.1, ?_⟩
    change (ν.1⁻¹ * μ.1).pullback (continuousNormUnits F K) = 1
    have hν := ν.property
    have hμ := μ.property
    change ν.1.pullback (continuousNormUnits F K) = 1 at hν
    change μ.1.pullback (continuousNormUnits F K) = 1 at hμ
    rw [ContinuousQuasiChar.mul_pullback,
      ContinuousQuasiChar.inv_pullback, hν, hμ]
    simp
  left_inv μ := by
    apply NormCharacter.ext
    simp [normCharacterLeftMul]
  right_inv μ := by
    apply NormCharacter.ext
    simp [normCharacterLeftMul]

@[simp]
theorem normCharacterLeftMulEquiv_apply (ν μ : NormCharacter F K) :
    normCharacterLeftMulEquiv F K ν μ = normCharacterLeftMul F K ν μ :=
  rfl

/-- Reindexing the full finite product by a fixed norm character preserves
the product.  The product is over the whole `NormCharacter` type, including
the trivial character. -/
theorem normCharacter_fullProduct_leftMul
    [Finite (NormCharacter F K)]
    {M : Type*} [CommMonoid M] (ν : NormCharacter F K)
    (f : NormCharacter F K → M) :
    (by
      letI := Fintype.ofFinite (NormCharacter F K)
      exact ∏ μ : NormCharacter F K, f (normCharacterLeftMul F K ν μ)) =
    (by
      letI := Fintype.ofFinite (NormCharacter F K)
      exact ∏ μ : NormCharacter F K, f μ) := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Equiv.prod_comp (normCharacterLeftMulEquiv F K ν) f

end NormCharacterReindexing

section TwistInvariance

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]

omit [Finite (NormCharacter F K)] in
/-- A norm-character twist is unchanged after norm pullback. -/
theorem normQuasiChar_normCharacter_mul
    (ν : NormCharacter F K) (χF : ContinuousQuasiChar F) :
    normQuasiChar F K (ν.1 * χF) = normQuasiChar F K χF := by
  change (ν.1 * χF).pullback (continuousNormUnits F K) =
    χF.pullback (continuousNormUnits F K)
  have hν := ν.property
  change ν.1.pullback (continuousNormUnits F K) = 1 at hν
  rw [ContinuousQuasiChar.mul_pullback, hν]
  change (1 : ContinuousQuasiChar K) *
      χF.pullback (continuousNormUnits F K) =
    χF.pullback (continuousNormUnits F K)
  ext x
  simp only [ContinuousQuasiChar.mul_apply,
    ContinuousQuasiChar.one_apply, one_mul]

/-- Multiplication by a fixed norm character reindexes exactly the
denominator product used by `firstMainRightSide`. -/
theorem firstMainRightSide_normCharacter_mul
    (ΔF : LocalConstantFunction F) (ν : NormCharacter F K)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F) :
    firstMainRightSide F K ΔF (ν.1 * χF) ψF =
      firstMainRightSide F K ΔF χF ψF := by
  letI := Fintype.ofFinite (NormCharacter F K)
  change
    (∏ μ : NormCharacter F K, ΔF (μ.1 * (ν.1 * χF)) ψF) =
      ∏ μ : NormCharacter F K, ΔF (μ.1 * χF) ψF
  let f : NormCharacter F K → ℂ := fun μ => ΔF (μ.1 * χF) ψF
  have hreindex := normCharacter_fullProduct_leftMul F K ν f
  change (∏ μ : NormCharacter F K,
    f (normCharacterLeftMul F K ν μ)) = ∏ μ : NormCharacter F K, f μ at hreindex
  have hfun :
      (fun μ : NormCharacter F K => ΔF (μ.1 * (ν.1 * χF)) ψF) =
        (fun μ : NormCharacter F K => f (normCharacterLeftMul F K ν μ)) := by
    funext μ
    simp only [f, normCharacterLeftMul_coe]
    rw [← mul_assoc, mul_comm μ.1 ν.1]
  rw [hfun]
  exact hreindex

/-- The numerator of the error term is invariant under a norm-character
twist of the base quasi-character. -/
theorem firstMainLeftSide_normCharacter_mul
    (ΔF : LocalConstantFunction F) (ΔK : LocalConstantFunction K)
    (ν : NormCharacter F K) (χF : ContinuousQuasiChar F)
    (ψF : ContinuousAddChar F) :
    firstMainLeftSide F K ΔF ΔK (ν.1 * χF) ψF =
      firstMainLeftSide F K ΔF ΔK χF ψF := by
  letI := Fintype.ofFinite (NormCharacter F K)
  change
    ΔK (normQuasiChar F K (ν.1 * χF)) (tracePullbackAddChar F K ψF) *
        (∏ μ : NormCharacter F K, ΔF μ.1 ψF) =
      ΔK (normQuasiChar F K χF) (tracePullbackAddChar F K ψF) *
        ∏ μ : NormCharacter F K, ΔF μ.1 ψF
  rw [normQuasiChar_normCharacter_mul F K]

/-- Twist invariance, Lemma `lem:twist-invariance`: multiplication of the
base quasi-character by any element of the full norm-character type leaves
the error term unchanged. -/
theorem errorTerm_normCharacter_mul
    (ΔF : LocalConstantFunction F) (ΔK : LocalConstantFunction K)
    (ν : NormCharacter F K) (χF : ContinuousQuasiChar F)
    (ψF : ContinuousAddChar F) :
    errorTerm F K ΔF ΔK (ν.1 * χF) ψF =
      errorTerm F K ΔF ΔK χF ψF := by
  rw [errorTerm, errorTerm,
    firstMainLeftSide_normCharacter_mul F K,
    firstMainRightSide_normCharacter_mul F K]

/-- Exact compatibility with the proposition-valued `FirstMainStatement`:
under computational realizations of the local constants, that statement is
equivalent to saying that every defined error term is one. -/
theorem firstMainStatement_iff_errorTerm_eq_one
    {ΔF : LocalConstantFunction F} {ΔK : LocalConstantFunction K}
    (hΔF : IsDeltaFiniteLocalConstant ΔF)
    (data : ∀ (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F),
      ψF ≠ 1 → FirstMainComputationalData F K χF ψF) :
    FirstMainStatement F K ΔF ΔK ↔
      CyclicPrimeExtension F K →
        ∀ (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F),
          ψF ≠ 1 → errorTerm F K ΔF ΔK χF ψF = 1 := by
  constructor
  · intro hmain hcyc χF ψF hψ
    exact (errorTerm_eq_one_iff_firstMainIdentity F K hΔF χF ψF
      (data χF ψF hψ)).2 (hmain hcyc χF ψF hψ)
  · intro herr hcyc χF ψF hψ
    exact (errorTerm_eq_one_iff_firstMainIdentity F K hΔF χF ψF
      (data χF ψF hψ)).1 (herr hcyc χF ψF hψ)

end TwistInvariance

end

end LanglandsFirstMainLemma
