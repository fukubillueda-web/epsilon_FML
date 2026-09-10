import LanglandsFirstMainLemma.Cases.WildOdd.LowerResidualCoefficients
import LanglandsFirstMainLemma.Cases.WildOdd.UpperResidualCoefficients

/-!
# Wild odd residual coefficient table assembly

This file is the public assembly point for the two coefficient-table halves.
It imports the lower and upper tables without reproving either one, re-exports
their exact representative-translation statements, and keeps the raw
representative ratios separate from the indexed-character identities.

The only construction made here is the boundary parameter package consumed by
`FiniteField.AffinePencil`.  Its certificate has exactly four proof fields:
nonvanishing of `rho`, nonvanishing of every affine-pencil denominator, and
the two required Frobenius-power identities.  This file does not apply the
affine-pencil theorem and does not cancel a finite phase.
-/

namespace LanglandsFirstMainLemma

noncomputable section

universe u

/-! ## Boundary parameters for the affine pencil -/

/-- The four hypotheses that `affinePencil` needs from the wild-odd boundary
specialization.  The statement deliberately contains no phase identity: that
application belongs to `BoundaryPencil`. -/
structure WildOddBoundaryAffinePencilCertificate
    {p : ℕ} [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p]
    (rho sigma tau a0 b0 : k) : Prop where
  rho_ne_zero : rho ≠ 0
  one_add_index_mul_rho_ne_zero : ∀ j : ZMod p,
    1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0
  a0_pow : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹
  b0_pow : b0 ^ p = sigma - rho⁻¹ * tau

/-- The boundary ratio `dZero = eta/etaZero` is nonzero because both named
coefficient rows carry their own polar nonvanishing proofs. -/
theorem wildOddBoundaryDZero_ne_zero
    {k : Type*} [Field k]
    (generator base : WildOddNamedCoefficientPair k) :
    wildOddBoundaryDZero generator base ≠ 0 := by
  unfold wildOddBoundaryDZero
  exact div_ne_zero base.eta_ne_zero generator.eta_ne_zero

/-- The affine-pencil parameter `rho = dZero⁻¹`. -/
noncomputable def wildOddBoundaryRho
    {k : Type*} [Field k]
    (generator base : WildOddNamedCoefficientPair k) : k :=
  (wildOddBoundaryDZero generator base)⁻¹

/-- The constant affine parameter is the base-row parameter `gamma`. -/
def wildOddBoundarySigma
    {k : Type*} [Field k]
    (_generator base : WildOddNamedCoefficientPair k) : k :=
  base.gamma

/-- The varying affine parameter is `rho * gammaZero`. -/
noncomputable def wildOddBoundaryTau
    {k : Type*} [Field k]
    (generator base : WildOddNamedCoefficientPair k) : k :=
  wildOddBoundaryRho generator base * generator.gamma

/-- The inverse-Frobenius lift of the normalized upper polar coefficient.
Its `p`th power is proved in the boundary certificate below. -/
noncomputable def wildOddBoundaryA0
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F)) :
    ResidueField F :=
  (C.frobeniusEquiv hchar).symm
    (1 - wildOddBoundaryDZero generator base ^ (p - 1))

/-- The inverse-Frobenius lift of the normalized upper affine coefficient.
Its `p`th power is `gamma - gammaZero`. -/
noncomputable def wildOddBoundaryB0
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F)) :
    ResidueField F :=
  (C.frobeniusEquiv hchar).symm (base.gamma - generator.gamma)

/-- Extend the nonzero-index boundary numerators already proved by the lower
coefficient node to all prime-field indices.  At index zero this is exactly
`dZero ≠ 0`; at a nonzero index it is the imported lower-row fact. -/
theorem wildOddBoundaryPrimeFieldShift_ne_zero
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (generator base : WildOddNamedCoefficientPair k)
    (hnonzero : ∀ j : {j : ZMod p // j ≠ 0},
      ((j : ZMod p).val : k) + wildOddBoundaryDZero generator base ≠ 0) :
    ∀ j : ZMod p,
      (ZMod.castHom (dvd_refl p) k) j +
        wildOddBoundaryDZero generator base ≠ 0 := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa using wildOddBoundaryDZero_ne_zero generator base
  · have h := hnonzero ⟨j, hj⟩
    have hcast : (ZMod.castHom (dvd_refl p) k) j = (j.val : k) := by
      rw [← ZMod.natCast_zmod_val j]
      simp
    simpa only [hcast] using h

/-- The exact wild-odd boundary certificate for direct use by
`FiniteField.affinePencil`.

The lower table supplies `hnonzero` through
`wildOdd_lowBoundaryNumerator_ne_zero`.  The parameters are the manuscript
specialization
`rho = dZero⁻¹`, `sigma = gamma`, and `tau = rho * gammaZero`; `a0`
and `b0` are the inverse-Frobenius forms of the normalized upper row. -/
theorem wildOdd_boundaryAffinePencilCertificate
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (hnonzero : ∀ j : {j : ZMod p // j ≠ 0},
      ((j : ZMod p).val : ResidueField F) +
        wildOddBoundaryDZero generator base ≠ 0) :
    WildOddBoundaryAffinePencilCertificate
      (wildOddBoundaryRho generator base)
      (wildOddBoundarySigma generator base)
      (wildOddBoundaryTau generator base)
      (wildOddBoundaryA0 F p hchar C generator base)
      (wildOddBoundaryB0 F p hchar C generator base) := by
  let dZero := wildOddBoundaryDZero generator base
  have hdZero : dZero ≠ 0 := wildOddBoundaryDZero_ne_zero generator base
  have hshift : ∀ j : ZMod p,
      (ZMod.castHom (dvd_refl p) (ResidueField F)) j + dZero ≠ 0 :=
    wildOddBoundaryPrimeFieldShift_ne_zero generator base hnonzero
  refine
    { rho_ne_zero := ?_
      one_add_index_mul_rho_ne_zero := ?_
      a0_pow := ?_
      b0_pow := ?_ }
  · exact inv_ne_zero hdZero
  · intro j
    change 1 + (ZMod.castHom (dvd_refl p) (ResidueField F)) j * dZero⁻¹ ≠ 0
    rw [show 1 + (ZMod.castHom (dvd_refl p) (ResidueField F)) j * dZero⁻¹ =
        ((ZMod.castHom (dvd_refl p) (ResidueField F)) j + dZero) *
          dZero⁻¹ by
            field_simp
            ring]
    exact mul_ne_zero (hshift j) (inv_ne_zero hdZero)
  · change ((C.frobeniusEquiv hchar).symm
        (1 - dZero ^ (p - 1))) ^ p =
      1 - ((dZero⁻¹) ^ (p - 1))⁻¹
    rw [← C.frobeniusEquiv_apply hchar,
      (C.frobeniusEquiv hchar).apply_symm_apply]
    rw [inv_pow, inv_inv]
  · change ((C.frobeniusEquiv hchar).symm
        (base.gamma - generator.gamma)) ^ p =
      base.gamma - (dZero⁻¹)⁻¹ * (dZero⁻¹ * generator.gamma)
    rw [← C.frobeniusEquiv_apply hchar,
      (C.frobeniusEquiv hchar).apply_symm_apply]
    field_simp

/-! ## Public assembly of the completed tables -/

/-- Complete public wild-odd residual coefficient table.

The first two fields are the imported lower and upper table facades.  The
next two expose the already-proved source-to-selected representative
translations.  The following four fields deliberately distinguish the raw
representative ratios (which retain their inverse norm factors) from the
identities obtained only after applying the indexed norm character.  The
last three fields expose the boundary nonvanishing and four-fact affine-
pencil certificate without applying the pencil. -/
structure WildOddResidualCoefficientTable : Prop where
  lowerCoefficients : WildOddLowerResidualCoefficientAPI
  upperCoefficients : WildOddUpperResidualCoefficientsAPI.{0, 0}
  lowerRepresentativeTranslation :
    type_of% @OddRepresentativeChangeData.wildOddTranslationCertificate.{0}
  upperRepresentativeTranslation :
    type_of% @wildOdd_upperRepresentativeTranslation.{0}
  lowRawRepresentativeRatio : type_of% @wildOdd_lowRawRepresentativeRatio
  highRawRepresentativeRatio : type_of% @wildOdd_highRawRepresentativeRatio
  lowIndexedCharacterValue : type_of% @wildOdd_lowIndexedCharacter_z
  highIndexedCharacterValue : type_of% @wildOdd_highIndexedCharacter_z
  boundaryDZero_ne_zero : type_of% @wildOddBoundaryDZero_ne_zero.{0}
  boundaryPrimeFieldShift_ne_zero :
    type_of% @wildOddBoundaryPrimeFieldShift_ne_zero.{0}
  boundaryAffinePencilCertificate :
    type_of% @wildOdd_boundaryAffinePencilCertificate.{0}

/-- **Complete wild odd-prime residual coefficient table assembly**
(`prop:odd-coefficient-table`).

This theorem packages the two completed coefficient nodes and the exact
boundary inputs required downstream.  It performs no coefficient
calculation, coordinate construction, affine-pencil application, or phase
cancellation. -/
theorem wildOdd_twistCoefficients : WildOddResidualCoefficientTable where
  lowerCoefficients := wildOdd_lowerResidualCoefficients
  upperCoefficients := wildOdd_upperResidualCoefficients
  lowerRepresentativeTranslation :=
    OddRepresentativeChangeData.wildOddTranslationCertificate
  upperRepresentativeTranslation := wildOdd_upperRepresentativeTranslation
  lowRawRepresentativeRatio := wildOdd_lowRawRepresentativeRatio
  highRawRepresentativeRatio := wildOdd_highRawRepresentativeRatio
  lowIndexedCharacterValue := wildOdd_lowIndexedCharacter_z
  highIndexedCharacterValue := wildOdd_highIndexedCharacter_z
  boundaryDZero_ne_zero := wildOddBoundaryDZero_ne_zero
  boundaryPrimeFieldShift_ne_zero := wildOddBoundaryPrimeFieldShift_ne_zero
  boundaryAffinePencilCertificate :=
    wildOdd_boundaryAffinePencilCertificate

end

end LanglandsFirstMainLemma
