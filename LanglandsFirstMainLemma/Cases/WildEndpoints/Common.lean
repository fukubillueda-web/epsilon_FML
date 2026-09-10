import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.TraceIdeals
import LanglandsFirstMainLemma.Delta.ResidueFormula
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import Mathlib.FieldTheory.Finite.Basic

/-!
# Common infrastructure for the two wild endpoint cases
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section UniformizerDenominators

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- An admissible denominator chosen as the exact integer power of a fixed
uniformizer.  Negative additive conductors are handled by the integer power;
there is no positivity assumption on the exponent. -/
def uniformizerAdmissibleGamma
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    AdmissibleGamma E chi psi :=
  ⟨pi ^ ((chi.conductor : ℤ) + psi.conductor), by
    rw [Units.val_zpow_eq_zpow_val, ord_uniformizer_zpow E hpi]⟩

@[simp]
theorem uniformizerAdmissibleGamma_coe
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    (uniformizerAdmissibleGamma E chi psi pi hpi : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor) :=
  rfl

/-- The representative-independent local constant evaluated using a fixed
uniformizer denominator. -/
def endpointDelta
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) : ℂ :=
  deltaFinite chi psi (uniformizerAdmissibleGamma E chi psi pi hpi)

/-- A quasi-character value raised to an integer exponent, coerced from
`ℂˣ` only after the power has been formed. -/
def endpointCharacterPower
    (chi : LocalQuasiCharData E) (pi : Eˣ) (a : ℤ) : ℂ :=
  (((chi.character pi) ^ a : ℂˣ) : ℂ)

@[simp]
theorem endpointCharacterPower_zero
    (chi : LocalQuasiCharData E) (pi : Eˣ) :
    endpointCharacterPower E chi pi 0 = 1 := by
  simp [endpointCharacterPower]

theorem endpointCharacterPower_add
    (chi : LocalQuasiCharData E) (pi : Eˣ) (a b : ℤ) :
    endpointCharacterPower E chi pi (a + b) =
      endpointCharacterPower E chi pi a * endpointCharacterPower E chi pi b := by
  simp [endpointCharacterPower, zpow_add₀]

/-- Exact conductor zero evaluated with the uniformizer denominator. -/
theorem endpointDelta_conductor_zero
    (chi : LocalQuasiCharData E) (hchi : chi.conductor = 0)
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    endpointDelta E chi psi pi hpi =
      endpointCharacterPower E chi pi psi.conductor := by
  rw [endpointDelta, deltaFinite_conductor_zero E chi hchi]
  change ((chi.character
      (pi ^ ((chi.conductor : ℤ) + psi.conductor)) : ℂˣ) : ℂ) = _
  rw [hchi]
  norm_num [endpointCharacterPower, map_zpow]

/-- The exceptional trivial character contributes the literal factor one. -/
@[simp]
theorem endpointDelta_trivial
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    endpointDelta E (trivialQuasiCharData E) psi pi hpi = 1 :=
  delta_trivial_character E psi
    (uniformizerAdmissibleGamma E (trivialQuasiCharData E) psi pi hpi)

/-- Proof-bearing product data for a positive-conductor character twisted
by an unramified character. -/
abbrev unramifiedTwistData
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor) :
    LocalQuasiCharData E where
  character := theta.character * nu.character
  conductor := theta.conductor
  isConductor := theta.isConductor.mul_of_gt nu.isConductor (by omega)

@[simp]
theorem unramifiedTwistData_conductor
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor) :
    (unramifiedTwistData E theta nu hnu htheta).conductor = theta.conductor :=
  rfl

/-- The same denominator, transported to the unchanged-conductor product
datum. -/
def unramifiedTwistAdmissibleGamma
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    AdmissibleGamma E (unramifiedTwistData E theta nu hnu htheta) psi :=
  ⟨Gamma, by simpa using Gamma.property⟩

@[simp]
theorem unramifiedTwistAdmissibleGamma_coe
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    (unramifiedTwistAdmissibleGamma E theta nu hnu htheta psi Gamma : Eˣ) =
      (Gamma : Eˣ) :=
  rfl

/-- Direct substitution in the representative-free finite sum: an
unramified twist is one on every unit summation class. -/
theorem finiteGaussSum_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    finiteGaussSum (unramifiedTwistData E theta nu hnu htheta) psi
        (unramifiedTwistAdmissibleGamma E theta nu hnu htheta psi Gamma) =
      finiteGaussSum theta psi Gamma := by
  letI := unitFiltrationQuotientFintype E (Nat.zero_le theta.conductor)
  change (∑ z : UnitFiltrationQuotient E 0 theta.conductor (Nat.zero_le _),
      finiteGaussSummand (unramifiedTwistData E theta nu hnu htheta) psi
        (unramifiedTwistAdmissibleGamma E theta nu hnu htheta psi Gamma) z) =
    ∑ z : UnitFiltrationQuotient E 0 theta.conductor (Nat.zero_le _),
      finiteGaussSummand theta psi Gamma z
  apply Finset.sum_congr rfl
  intro z _hz
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective E (Nat.zero_le theta.conductor) z
  rw [finiteGaussSummand_mk, finiteGaussSummand_mk]
  have hnuUnit : nu.character (u : Eˣ) = 1 := by
    apply nu.isConductor.trivial
    simpa only [hnu] using u.property
  simp only [finiteGaussSummandRepresentative,
    unramifiedTwistAdmissibleGamma_coe, ContinuousQuasiChar.mul_apply,
    hnuUnit, mul_one]

/-- Direct conductor-zero twisting formula.  This is deliberately separate
from the higher-conductor Lamprecht formula: no stationary class is created
for the unramified character. -/
theorem deltaFinite_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    deltaFinite (unramifiedTwistData E theta nu hnu htheta) psi
        (unramifiedTwistAdmissibleGamma E theta nu hnu htheta psi Gamma) =
      (nu.character (Gamma : Eˣ) : ℂ) * deltaFinite theta psi Gamma := by
  rw [deltaFinite, deltaFinite,
    finiteGaussSum_unramifiedTwist E theta nu hnu htheta psi Gamma]
  have hvalue :
      (((unramifiedTwistData E theta nu hnu htheta).character
        (unramifiedTwistAdmissibleGamma E theta nu hnu htheta psi Gamma : Eˣ) :
          ℂˣ) : ℂ) =
        (theta.character (Gamma : Eˣ) : ℂ) *
          (nu.character (Gamma : Eˣ) : ℂ) := by
    exact congrArg Units.val
      (ContinuousQuasiChar.mul_apply theta.character nu.character (Gamma : Eˣ))
  rw [hvalue]
  ring

/-- Uniformizer form of the direct unramified-twist formula. -/
theorem endpointDelta_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    endpointDelta E (unramifiedTwistData E theta nu hnu htheta) psi pi hpi =
      endpointCharacterPower E nu pi
          ((theta.conductor : ℤ) + psi.conductor) *
        endpointDelta E theta psi pi hpi := by
  have hGamma :
      uniformizerAdmissibleGamma E
          (unramifiedTwistData E theta nu hnu htheta) psi pi hpi =
        unramifiedTwistAdmissibleGamma E theta nu hnu htheta psi
          (uniformizerAdmissibleGamma E theta psi pi hpi) := by
    apply Subtype.ext
    rfl
  rw [endpointDelta, hGamma]
  simpa [endpointDelta, endpointCharacterPower, map_zpow] using
    (deltaFinite_unramifiedTwist E theta nu hnu htheta psi
      (uniformizerAdmissibleGamma E theta psi pi hpi))

end UniformizerDenominators

section WildData

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

/-- The chosen upper uniformizer as a field unit. -/
def wildUpperUniformizer : Kˣ :=
  Units.mk0 (piK : K) hpiK.ne_zero

/-- The lower uniformizer is the exact norm of the chosen upper one, with the
direction used in the manuscript. -/
def wildLowerUniformizer : Fˣ :=
  normUnits F K (wildUpperUniformizer K piK hpiK)

@[simp]
theorem wildLowerUniformizer_coe :
    ((wildLowerUniformizer F K piK hpiK : Fˣ) : F) =
      norm F K (piK : K) :=
  rfl

include hres

/-- Total ramification (`f=1`) makes the norm of an upper uniformizer a
lower uniformizer. -/
theorem wildLowerUniformizer_isUniformizer :
    (ValuativeRel.valuation F).IsUniformizer
      ((wildLowerUniformizer F K piK hpiK : Fˣ) : F) := by
  rw [← ord_eq_one_iff_isUniformizer]
  rw [wildLowerUniformizer_coe, ord_norm, hres, one_nsmul,
    ord_uniformizer K hpiK]

/-- Trace pullback with its exact conductor
`[K:F] n + ([K:F]-1)(t+1)`. -/
def wildTracePullbackData (psiF : LocalAddCharData F) :
    LocalAddCharData K where
  character := psiF.character.compTrace
  conductor :=
    (Module.finrank F K : ℤ) * psiF.conductor +
      (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)
  isConductor := additiveConductor_compTrace_cyclicPrime
    F K ht hres piK hpiK hgen psiF.isConductor

@[simp]
theorem wildTracePullbackData_conductor (psiF : LocalAddCharData F) :
    (wildTracePullbackData F K ht hres piK hpiK hgen psiF).conductor =
      (Module.finrank F K : ℤ) * psiF.conductor +
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) :=
  rfl

/-- Norm pullback in the below-break range, including the two endpoints
`m=0` and `m=1` used in this file. -/
def wildNormPullbackData
    (chiF : LocalQuasiCharData F) (hchi : chiF.conductor ≤ t) :
    LocalQuasiCharData K where
  character := chiF.character.compNorm
  conductor := chiF.conductor
  isConductor := multiplicativeConductor_compNorm_belowBreak
    F K ht hres piK hpiK hgen hchi chiF.isConductor

@[simp]
theorem wildNormPullbackData_conductor
    (chiF : LocalQuasiCharData F) (hchi : chiF.conductor ≤ t) :
    (wildNormPullbackData F K ht hres piK hpiK hgen chiF hchi).conductor =
      chiF.conductor :=
  rfl

@[simp]
theorem wildNormPullbackData_character
    (chiF : LocalQuasiCharData F) (hchi : chiF.conductor ≤ t) :
    (wildNormPullbackData F K ht hres piK hpiK hgen chiF hchi).character =
      chiF.character.compNorm :=
  rfl

include ht hres piK hpiK hgen

/-- Exact proof-bearing data for every norm character.  The exceptional
identity has conductor zero; every other character has conductor `t+1`.
This definition never drops the identity from the finite group. -/
def wildNormCharacterData (mu : NormCharacter F K) :
    LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact trivialQuasiCharData F
  · exact
      { character := mu.1
        conductor := t + 1
        isConductor := ramifiedNormCharacter_conductor
          F K ht hres piK hpiK hgen mu hmu }

@[simp]
theorem wildNormCharacterData_one :
    wildNormCharacterData F K ht hres piK hpiK hgen
      (1 : NormCharacter F K) = trivialQuasiCharData F := by
  simp [wildNormCharacterData]

theorem wildNormCharacterData_of_ne
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor = t + 1 := by
  simp [wildNormCharacterData, hmu]

theorem wildNormCharacterData_character
    (mu : NormCharacter F K) :
    (wildNormCharacterData F K ht hres piK hpiK hgen mu).character = mu.1 := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    ext x
    simp [wildNormCharacterData]
  · simp [wildNormCharacterData, hmu]

/-- The exact data for the conductor-zero right-hand factor.  At the
identity norm character this is literally `chiF`; at every other character
it is the product datum of unchanged positive conductor. -/
def wildEndpointZeroTwistData
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (mu : NormCharacter F K) : LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact chiF
  · exact unramifiedTwistData F
      (wildNormCharacterData F K ht hres piK hpiK hgen mu) chiF hchiF
      (by rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu]; omega)

@[simp]
theorem wildEndpointZeroTwistData_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0) :
    wildEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF 1 = chiF := by
  simp [wildEndpointZeroTwistData]

theorem wildEndpointZeroTwistData_character
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (mu : NormCharacter F K) :
    (wildEndpointZeroTwistData F K ht hres piK hpiK hgen
      chiF hchiF mu).character = mu.1 * chiF.character := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    simp only [wildEndpointZeroTwistData, ↓reduceDIte]
    exact (one_mul chiF.character).symm
  · simp only [wildEndpointZeroTwistData, hmu, ↓reduceDIte,
      unramifiedTwistData, wildNormCharacterData_character]

/-- Direct endpoint-zero substitution for every member of the complete
norm-character group.  The identity branch uses the literal trivial
factor; the nonidentity branch uses the finite sum itself, not Lamprecht
stationary phase. -/
theorem endpointDelta_wildEndpointZeroTwist
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F)
    (mu : NormCharacter F K) :
    endpointDelta F
        (wildEndpointZeroTwistData F K ht hres piK hpiK hgen
          chiF hchiF mu) psiF
        (wildLowerUniformizer F K piK hpiK)
        (wildLowerUniformizer_isUniformizer F K hres piK hpiK) =
      endpointCharacterPower F chiF (wildLowerUniformizer F K piK hpiK)
          (((wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor : ℤ) +
            psiF.conductor) *
        endpointDelta F
          (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF
          (wildLowerUniformizer F K piK hpiK)
          (wildLowerUniformizer_isUniformizer F K hres piK hpiK) := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    rw [wildEndpointZeroTwistData_one, wildNormCharacterData_one,
      endpointDelta_trivial, mul_one,
      endpointDelta_conductor_zero F chiF hchiF]
    simp [wildNormCharacterData, endpointCharacterPower]
  · rw [show wildEndpointZeroTwistData F K ht hres piK hpiK hgen
        chiF hchiF mu =
        unramifiedTwistData F
          (wildNormCharacterData F K ht hres piK hpiK hgen mu) chiF hchiF
          (by rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu];
              omega) by
        simp [wildEndpointZeroTwistData, hmu]]
    simpa only using endpointDelta_unramifiedTwist F
      (wildNormCharacterData F K ht hres piK hpiK hgen mu) chiF hchiF
      (by rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu]; omega)
      psiF (wildLowerUniformizer F K piK hpiK)
      (wildLowerUniformizer_isUniformizer F K hres piK hpiK)

/-- Full enumeration, including the exceptional identity: the sum of the
exact norm-character conductors is `(p-1)(t+1)`. -/
theorem wildNormCharacter_conductor_sum :
    (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).sum
        (fun mu ↦
          (wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor) =
      (Module.finrank F K - 1) * (t + 1) := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let S := ramifiedNormCharacterFinset F K ht hres piK hpiK hgen
  have honeMem : (1 : NormCharacter F K) ∈ S := by
    simp [S, ramifiedNormCharacterFinset, normCharacterFinset]
  have hSCard : S.card = Module.finrank F K := by
    simpa [S, ramifiedNormCharacterFinset, normCharacterFinset,
      Nat.card_eq_fintype_card] using
      ramifiedNormCharacter_card F K ht hres piK hpiK hgen
  have hcard : (S.erase 1).card =
      Module.finrank F K - 1 := by
    rw [Finset.card_erase_of_mem honeMem, hSCard]
  calc
    S.sum (fun mu ↦
        (wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor) =
        (S.erase 1).sum (fun _ ↦ t + 1) := by
      rw [← Finset.sum_erase_add _ _ honeMem]
      simp only [wildNormCharacterData_one]
      change (S.erase 1).sum (fun mu ↦
        (wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor) + 0 = _
      rw [add_zero]
      apply Finset.sum_congr rfl
      intro mu hmu
      exact wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu
        (Finset.ne_of_mem_erase hmu)
    _ = (S.erase 1).card * (t + 1) := by simp
    _ = (Module.finrank F K - 1) * (t + 1) := by rw [hcard]

/-- The manuscript's endpoint exponent, with the additive conductor counted
once for each of the `p` norm characters. -/
theorem wildEndpointZero_totalExponent (n : ℤ) :
    (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).sum
        (fun mu ↦
          ((wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor : ℤ) + n) =
      (Module.finrank F K : ℤ) * n +
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hSCard :
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).card =
        Module.finrank F K := by
    simpa [ramifiedNormCharacterFinset, normCharacterFinset,
      Nat.card_eq_fintype_card] using
      ramifiedNormCharacter_card F K ht hres piK hpiK hgen
  rw [hSCard]
  norm_cast
  rw [wildNormCharacter_conductor_sum F K ht hres piK hpiK hgen]
  ring

end WildData

section CharacterPowerProducts

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Product of integer powers, stated after coercion from `ℂˣ`. -/
theorem endpointCharacterPower_finsetSum
    {I : Type*} (s : Finset I) (chi : LocalQuasiCharData E) (pi : Eˣ)
    (a : I → ℤ) :
    s.prod (fun i ↦ endpointCharacterPower E chi pi (a i)) =
      endpointCharacterPower E chi pi (s.sum a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        endpointCharacterPower_add]

end CharacterPowerProducts

section CriticalEndpointAlgebra

/-- The endpoint annihilator calculation in characteristic `p`.  The
Frobenius preimage `b` is retained explicitly, so the direction of the
adjoint calculation can be audited: `b^p=a`, not its inverse. -/
theorem criticalPolynomial_annihilator_of_frobeniusPreimage
    {k M : Type*} [Field k] [CommGroup M]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (psi : AddChar k M) (hpsi : psi ≠ 1)
    (hfrob : ∀ x : k, psi (x ^ p) = psi x)
    {a b lambda : k} (ha : a ≠ 0) (hb : b ^ p = a)
    (hann : ∀ z : k,
      psi (a * (z ^ p - lambda ^ (p - 1) * z)) = 1) :
    (a⁻¹) ^ (p - 1) = lambda ^ (p * (p - 1)) := by
  have hshift :
      psi.mulShift b = psi.mulShift (a * lambda ^ (p - 1)) := by
    ext z
    simp only [AddChar.mulShift_apply]
    rw [← hfrob (b * z), mul_pow, hb]
    have hz := hann z
    rw [mul_sub, AddChar.map_sub_eq_div] at hz
    exact (div_eq_one.mp hz).trans (by simp only [mul_assoc])
  have hbeq : b = a * lambda ^ (p - 1) :=
    AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hpsi) hshift
  have hpower : a ^ (p - 1) * (lambda ^ (p - 1)) ^ p = 1 := by
    have hp : p - 1 + 1 = p :=
      Nat.sub_add_cancel (Nat.Prime.pos (Fact.out : Nat.Prime p))
    rw [hbeq, mul_pow] at hb
    have hap : a ^ p = a ^ (p - 1) * a := by
      exact (congrArg (fun n : ℕ ↦ a ^ n) hp.symm).trans (pow_succ a (p - 1))
    calc
      a ^ (p - 1) * (lambda ^ (p - 1)) ^ p =
          (a ^ p * (lambda ^ (p - 1)) ^ p) * a⁻¹ := by
            rw [hap]
            field_simp [ha]
      _ = a * a⁻¹ := by rw [hb]
      _ = 1 := mul_inv_cancel₀ ha
  calc
    (a⁻¹) ^ (p - 1) = (a ^ (p - 1))⁻¹ := inv_pow a (p - 1)
    _ = (lambda ^ (p - 1)) ^ p :=
      (mul_eq_one_iff_inv_eq₀ (pow_ne_zero _ ha)).mp hpower
    _ = lambda ^ (p * (p - 1)) := by
      simpa only [Nat.mul_comm] using (pow_mul lambda (p - 1) p).symm

/-- The critical polynomial `Z^p-lambda^(p-1)Z` has exactly the reciprocal
power prescribed by the manuscript once the normalized residual additive
character annihilates its image. -/
theorem criticalPolynomial_annihilator
    {k M : Type*} [Field k] [Finite k] [CommGroup M]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (psi : AddChar k M) (hpsi : psi ≠ 1)
    (hfrob : ∀ x : k, psi (x ^ p) = psi x)
    {a lambda : k} (ha : a ≠ 0)
    (hann : ∀ z : k,
      psi (a * (z ^ p - lambda ^ (p - 1) * z)) = 1) :
    (a⁻¹) ^ (p - 1) = lambda ^ (p * (p - 1)) := by
  obtain ⟨b, hb⟩ := surjective_frobenius k p a
  rw [frobenius_def] at hb
  exact criticalPolynomial_annihilator_of_frobeniusPreimage
    psi hpsi hfrob ha hb hann

/-- Pure quotient-group algebra behind the last endpoint discriminant
congruence.  The quotient map is kept as an argument, fixing the direction
`ratio / ((-1)^p c^(p-1))` in its kernel. -/
theorem endpointDiscriminantCongruence_quotient
    {G Q : Type*} [CommGroup G] [CommGroup Q]
    (q : G →* Q) (p : ℕ)
    {A c D epsilon L ratio : G}
    (hc : q ((c / A) ^ (p - 1)) = q L)
    (hD : q D = q (epsilon * L))
    (hratio : ratio = A ^ (p - 1) * D) :
    q ratio = q (epsilon * c ^ (p - 1)) := by
  rw [hratio, map_mul, map_pow, hD, map_mul, ← hc,
    map_pow, map_div, map_mul, map_pow]
  rw [div_pow]
  calc
    q A ^ (p - 1) * (q epsilon * (q c ^ (p - 1) / q A ^ (p - 1))) =
        q epsilon * q c ^ (p - 1) *
          (q A ^ (p - 1) * (q A ^ (p - 1))⁻¹) := by
            simp only [div_eq_mul_inv]
            ac_rfl
    _ = q epsilon * q c ^ (p - 1) := by simp

end CriticalEndpointAlgebra

end

end LanglandsFirstMainLemma
