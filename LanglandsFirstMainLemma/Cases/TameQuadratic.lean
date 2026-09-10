import LanglandsFirstMainLemma.Parameters.RamifiedHasseComparison
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.FiniteField.HasseDavenportProduct
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Lamprecht.CriticalPolarCoordinate
import LanglandsFirstMainLemma.Delta.ResidueFormula
import Mathlib.RingTheory.Localization.NormTrace

/-!
# The tamely ramified quadratic case

This file proves the quadratic tame row of Langlands's First Main Lemma.
The endpoint conductors are evaluated directly by the residue formulas; no
stationary class is attached to either endpoint.  Above conductor one, the
stationary numerator is first transported in its quotient class, and the
remaining Hasse phases are reduced to exact quadratic-phase identities.

Source: Propositions `prop:tame-conductor-one-comparison` and
`prop:tame-two-new` of `references/epsilon_FML.tex`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators
open Polynomial IsLocalRing

/-! ## Finite-field identities with the manuscript's normalization -/

variable {k : Type*} [Field k] [Fintype k]

private theorem finiteQuadraticChar_orderOf_two
    (hchar : ringChar k ≠ 2) :
    orderOf (finiteQuadraticChar k) = 2 := by
  apply orderOf_eq_prime
  · exact (finiteQuadraticChar_isQuadratic k).sq_eq_one
  · exact finiteQuadraticChar_ne_one k hchar

private theorem finiteMulChar_norm_apply
    (chi : FiniteMulChar k) {a : k} (ha : a ≠ 0) :
    ‖chi a‖ = 1 := by
  classical
  let u : kˣ := Units.mk0 a ha
  have hu := chi.apply_mem_rootsOfUnity u
  simpa [u] using Complex.norm_eq_one_of_mem_rootsOfUnity hu

/-- Degree-two Hasse--Davenport, retaining the inverse character already
built into `langlandsGaussSum`. -/
private theorem hasseDavenportProduct_two
    (hchar : ringChar k ≠ 2)
    (chi : FiniteMulChar k) (psi : FiniteAddChar k) (hpsi : psi ≠ 1) :
    chi (4 : k) * langlandsGaussSum (chi ^ 2) psi *
        langlandsGaussSum (finiteQuadraticChar k) psi =
      langlandsGaussSum chi psi *
        langlandsGaussSum (chi * finiteQuadraticChar k) psi := by
  let eta := finiteQuadraticChar k
  have heta : orderOf eta = 2 := finiteQuadraticChar_orderOf_two hchar
  have hdiv : 2 ∣ Fintype.card k - 1 := by
    have h := MulChar.orderOf_dvd_card_sub_one k eta
    rwa [heta] at h
  have h := hasseDavenportProduct (k := k) 2 hdiv eta chi heta psi hpsi
  have hfour : ((2 : ℕ) : k) ^ 2 = (4 : k) := by norm_num
  rw [hfour] at h
  simpa [eta] using h

/-- Phase form of degree-two Hasse--Davenport.  Nonvanishing is used before
taking phases, so the normalized scalar remains exactly `chi(4)`. -/
private theorem hasseDavenportProduct_two_phase
    (hchar : ringChar k ≠ 2)
    (chi : FiniteMulChar k) (psi : FiniteAddChar k) (hpsi : psi ≠ 1) :
    chi (4 : k) * phase (langlandsGaussSum (chi ^ 2) psi) *
        phase (langlandsGaussSum (finiteQuadraticChar k) psi) =
      phase (langlandsGaussSum chi psi) *
        phase (langlandsGaussSum (chi * finiteQuadraticChar k) psi) := by
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : (4 : k) ≠ 0 := by
    have hfour_eq : (4 : k) = (2 : k) ^ 2 := by norm_num
    rw [hfour_eq]
    exact pow_ne_zero 2 htwo
  have hchi4 : chi (4 : k) ≠ 0 := IsUnit.ne_zero (hfour.isUnit.map chi)
  have hchi4norm : ‖chi (4 : k)‖ = 1 := finiteMulChar_norm_apply chi hfour
  have hchi2 := langlandsGaussSum_ne_zero (chi ^ 2) hpsi
  have hnu := langlandsGaussSum_ne_zero (finiteQuadraticChar k) hpsi
  have hchi := langlandsGaussSum_ne_zero chi hpsi
  have hchinu := langlandsGaussSum_ne_zero (chi * finiteQuadraticChar k) hpsi
  have hphase := congrArg phase
    (hasseDavenportProduct_two hchar chi psi hpsi)
  rw [phase_mul (mul_ne_zero hchi4 hchi2) hnu,
    phase_mul hchi4 hchi2, phase_of_norm_eq_one hchi4norm,
    phase_mul hchi hchinu] at hphase
  exact hphase

private theorem finiteQuadraticChar_map_mul (x y : k) :
    finiteQuadraticChar k (x * y) =
      finiteQuadraticChar k x * finiteQuadraticChar k y :=
  (finiteQuadraticChar k).map_mul' x y

/-- Over an odd finite field, the quadratic character is the unique
nontrivial multiplicative character whose square is one. -/
private theorem finiteMulChar_eq_finiteQuadraticChar
    (hchar : ringChar k ≠ 2)
    (chi : FiniteMulChar k) (hchi : chi ≠ 1) (hsq : chi ^ 2 = 1) :
    chi = finiteQuadraticChar k := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  apply (MulChar.eq_iff hg chi (finiteQuadraticChar k)).2
  have hchiSq : chi (g : k) ^ 2 = 1 := by
    have h := congrArg (fun eta : FiniteMulChar k ↦ eta (g : k)) hsq
    rw [chi.pow_apply' two_ne_zero, MulChar.one_apply g.isUnit] at h
    exact h
  have hchiNe : chi (g : k) ≠ 1 := by
    intro h
    apply hchi
    exact (MulChar.eq_iff hg chi 1).2 (by simpa using h)
  have hnuSq : finiteQuadraticChar k (g : k) ^ 2 = 1 :=
    finiteQuadraticChar_sq k (Units.ne_zero g)
  have hnuNe : finiteQuadraticChar k (g : k) ≠ 1 := by
    intro h
    apply finiteQuadraticChar_ne_one k hchar
    exact (MulChar.eq_iff hg (finiteQuadraticChar k) 1).2 (by simpa using h)
  exact ((sq_eq_one_iff.mp hchiSq).resolve_left hchiNe).trans
    ((sq_eq_one_iff.mp hnuSq).resolve_left hnuNe).symm

/-- The residual identity when the downstairs conductor is even.  The
upstairs coefficient is `-2*beta`, including the essential minus sign. -/
private theorem tameQuadratic_evenPhase_product
    (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {beta : k} (hbeta : beta ≠ 0) :
    quadraticPhase psi (-2 * beta) 0 * quadraticPhase psi 2 0 =
      finiteQuadraticChar k beta := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  have hnegTwoBeta : (-2 : k) * beta ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr h2) hbeta
  have hupper : quadraticPhase psi (-2 * beta) 0 =
      finiteQuadraticChar k (-2 * beta) * quadraticPhase psi 1 0 := by
    simpa using quadraticPhase_eq_basic hchar hpsi hnegTwoBeta 0
  have hmu : quadraticPhase psi 2 0 =
      finiteQuadraticChar k (2 : k) * quadraticPhase psi 1 0 := by
    simpa using quadraticPhase_eq_basic hchar hpsi h2 0
  have hq : quadraticPhase psi 1 0 ^ 2 =
      finiteQuadraticChar k (-1) := quadraticPhase_basic_sq hchar hpsi
  have hnu : finiteQuadraticChar k (-2 * beta) *
      finiteQuadraticChar k (2 : k) * finiteQuadraticChar k (-1) =
      finiteQuadraticChar k beta := by
    calc
      finiteQuadraticChar k (-2 * beta) * finiteQuadraticChar k (2 : k) *
          finiteQuadraticChar k (-1) =
          finiteQuadraticChar k (((-2 * beta) * 2) * -1) := by
            symm
            rw [finiteQuadraticChar_map_mul, finiteQuadraticChar_map_mul]
      _ = finiteQuadraticChar k ((2 * 2) * beta) := by congr 1; ring
      _ = finiteQuadraticChar k (2 * 2) * finiteQuadraticChar k beta :=
        finiteQuadraticChar_map_mul _ _
      _ = (finiteQuadraticChar k (2 : k) *
            finiteQuadraticChar k (2 : k)) * finiteQuadraticChar k beta := by
              rw [finiteQuadraticChar_map_mul (k := k) (2 : k) 2]
      _ = finiteQuadraticChar k beta := by
        rw [show finiteQuadraticChar k (2 : k) *
            finiteQuadraticChar k (2 : k) =
              finiteQuadraticChar k (2 : k) ^ 2 by ring,
          finiteQuadraticChar_sq k h2, one_mul]
  rw [hupper, hmu]
  calc
    (finiteQuadraticChar k (-2 * beta) * quadraticPhase psi 1 0) *
        (finiteQuadraticChar k (2 : k) * quadraticPhase psi 1 0) =
        finiteQuadraticChar k (-2 * beta) * finiteQuadraticChar k (2 : k) *
          quadraticPhase psi 1 0 ^ 2 := by ring
    _ = finiteQuadraticChar k beta := by rw [hq, hnu]

/-- The residual identity when the downstairs conductor is odd.  The
parameter `s` is the residue of `(-1)^d`; retaining it records the translated
linear term `2*s*c` together with the elementary stationary value. -/
private theorem tameQuadratic_oddPhase_product
    (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {beta c s : k} (hbeta : beta ≠ 0) (hs : s ^ 2 = 1) :
    quadraticPhase psi (2 * beta) (2 * s * c) * quadraticPhase psi 2 0 =
      finiteQuadraticChar k beta * quadraticPhase psi beta c ^ 2 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  have hTwoBeta : (2 : k) * beta ≠ 0 := mul_ne_zero h2 hbeta
  have harg : -(2 * s * c) ^ 2 / (2 * (2 * beta)) = -c ^ 2 / beta := by
    calc
      -(2 * s * c) ^ 2 / (2 * (2 * beta)) = -(s ^ 2 * c ^ 2) / beta := by
        field_simp [h2, hbeta]
      _ = -c ^ 2 / beta := by rw [hs, one_mul]
  have hupper : quadraticPhase psi (2 * beta) (2 * s * c) =
      finiteQuadraticChar k (2 * beta) * psi (-c ^ 2 / beta) *
        quadraticPhase psi 1 0 := by
    rw [quadraticPhase_eq_basic hchar hpsi hTwoBeta (2 * s * c), harg]
  have hmu : quadraticPhase psi 2 0 =
      finiteQuadraticChar k (2 : k) * quadraticPhase psi 1 0 := by
    simpa using quadraticPhase_eq_basic hchar hpsi h2 0
  have hq : quadraticPhase psi 1 0 ^ 2 =
      finiteQuadraticChar k (-1) := quadraticPhase_basic_sq hchar hpsi
  have hlower : quadraticPhase psi beta c ^ 2 =
      finiteQuadraticChar k (-1) * psi (-c ^ 2 / beta) :=
    quadraticPhase_sq hchar hpsi hbeta c
  have hnu : finiteQuadraticChar k (2 * beta) *
      finiteQuadraticChar k (2 : k) = finiteQuadraticChar k beta := by
    calc
      finiteQuadraticChar k (2 * beta) * finiteQuadraticChar k (2 : k) =
          finiteQuadraticChar k ((2 * beta) * 2) := by
            exact (finiteQuadraticChar_map_mul (k := k) (2 * beta) 2).symm
      _ = finiteQuadraticChar k ((2 * 2) * beta) := by congr 1; ring
      _ = finiteQuadraticChar k (2 * 2) * finiteQuadraticChar k beta :=
        finiteQuadraticChar_map_mul _ _
      _ = (finiteQuadraticChar k (2 : k) *
            finiteQuadraticChar k (2 : k)) * finiteQuadraticChar k beta := by
              rw [finiteQuadraticChar_map_mul (k := k) (2 : k) 2]
      _ = finiteQuadraticChar k beta := by
        rw [show finiteQuadraticChar k (2 : k) *
            finiteQuadraticChar k (2 : k) =
              finiteQuadraticChar k (2 : k) ^ 2 by ring,
          finiteQuadraticChar_sq k h2, one_mul]
  rw [hupper, hmu]
  calc
    (finiteQuadraticChar k (2 * beta) * psi (-c ^ 2 / beta) *
        quadraticPhase psi 1 0) *
        (finiteQuadraticChar k (2 : k) * quadraticPhase psi 1 0) =
        (finiteQuadraticChar k (2 * beta) * finiteQuadraticChar k (2 : k)) *
          psi (-c ^ 2 / beta) * quadraticPhase psi 1 0 ^ 2 := by ring
    _ = finiteQuadraticChar k beta *
        (finiteQuadraticChar k (-1) * psi (-c ^ 2 / beta)) := by
          rw [hnu, hq]
          ring
    _ = finiteQuadraticChar k beta * quadraticPhase psi beta c ^ 2 := by
      rw [hlower]

/-! ## Exact local data and denominators -/

section LocalSetup

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))

/-- The chosen upper uniformizer as a field unit. -/
private def tameQuadraticUpperUniformizer : Kˣ :=
  Units.mk0 (piK : K) hpiK.ne_zero

/-- The lower uniformizer is the exact norm of the chosen upper one. -/
private def tameQuadraticLowerUniformizer : Fˣ :=
  normUnits F K (tameQuadraticUpperUniformizer K piK hpiK)

@[simp] private theorem tameQuadraticLowerUniformizer_coe :
    ((tameQuadraticLowerUniformizer F K piK hpiK : Fˣ) : F) =
      norm F K (piK : K) :=
  rfl

/-- Total ramification makes the exact norm of `piK` a uniformizer of `F`.
This is the denominator normalization used in all three conductor ranges. -/
private theorem tameQuadraticLowerUniformizer_isUniformizer
    (hres : residueDegree F K = 1) :
    (ValuativeRel.valuation F).IsUniformizer
      ((tameQuadraticLowerUniformizer F K piK hpiK : Fˣ) : F) := by
  rw [← ord_eq_one_iff_isUniformizer]
  rw [tameQuadraticLowerUniformizer_coe, ord_norm, hres, one_nsmul,
    ord_uniformizer K hpiK]

/-- The exact integer uniformizer power of order `m+n`; negative additive
conductors are handled by `zpow`. -/
private def tameQuadraticUniformizerGamma
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    AdmissibleGamma E chi psi :=
  ⟨pi ^ ((chi.conductor : ℤ) + psi.conductor), by
    rw [Units.val_zpow_eq_zpow_val, ord_uniformizer_zpow E hpi]⟩

@[simp] private theorem tameQuadraticUniformizerGamma_coe
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    (tameQuadraticUniformizerGamma E chi psi pi hpi : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor) :=
  rfl

/-- Residue degree one identifies the two residue fields by the canonical
extension residue map. -/
private def tameQuadraticResidueEquiv : ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K, hres]
    have hdim : Module.finrank (ResidueField F) (ResidueField F) =
        Module.finrank (ResidueField F) (ResidueField K) := by
      simp [hfin]
    have hinj : Function.Injective
        (Algebra.linearMap (ResidueField F) (ResidueField K)) :=
      (algebraMap (ResidueField F) (ResidueField K)).injective
    have hsurj :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by simpa only [Algebra.linearMap_apply] using hx⟩

@[simp] private theorem tameQuadraticResidueEquiv_apply
    (x : ResidueField F) :
    tameQuadraticResidueEquiv F K hres x = extensionResidueMap F K x :=
  rfl

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

/-- Every norm character is packaged at its actual endpoint conductor:
zero for the identity and one for the unique nonidentity character. -/
private noncomputable def tameQuadraticNormCharacterData
    (mu : NormCharacter F K) : LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact
      { character := mu.1
        conductor := 0
        isConductor := by
          subst mu
          exact trivialNormCharacter_conductor F K }
  · exact
      { character := mu.1
        conductor := 1
        isConductor :=
          tameNormCharacter_conductor F K ht hres piK hpiK hgen mu hmu }

@[simp] private theorem tameQuadraticNormCharacterData_character
    (mu : NormCharacter F K) :
    (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen mu).character =
      mu.1 := by
  classical
  simp only [tameQuadraticNormCharacterData]
  split <;> rfl

private theorem tameQuadraticNormCharacterData_conductor_of_ne
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen mu).conductor =
      1 := by
  classical
  simp [tameQuadraticNormCharacterData, hmu]

private theorem tameQuadraticNormCharacterData_conductor_one :
    (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen
      (1 : NormCharacter F K)).conductor = 0 := by
  classical
  simp [tameQuadraticNormCharacterData]

/-- Exact actual-conductor data for every norm-character twist of the
whole-orbit-minimal representative. -/
private noncomputable abbrev tameQuadraticTwistData
    (chi : LocalQuasiCharData F) (mu : NormCharacter F K) :
    LocalQuasiCharData F :=
  ramifiedNormCharacterOrbitTwistData F K ht hres piK hpiK hgen chi mu

@[simp] private theorem tameQuadraticTwistData_character
    (chi : LocalQuasiCharData F) (mu : NormCharacter F K) :
    (tameQuadraticTwistData F K hres piK hpiK ht hgen chi mu).character =
      mu.1 * chi.character :=
  ramifiedNormCharacterOrbitTwistData_character
    F K ht hres piK hpiK hgen chi mu

/-- Proof-bearing character packages are equal once their character and
exact conductor fields agree. -/
private theorem localQuasiCharData_ext
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi theta : LocalQuasiCharData E}
    (hchar : chi.character = theta.character)
    (hcond : chi.conductor = theta.conductor) : chi = theta := by
  cases chi with
  | mk chiChar chiCond chiProof =>
      cases theta with
      | mk thetaChar thetaCond thetaProof =>
          dsimp only at hchar hcond
          subst thetaChar
          subst thetaCond
          rfl

/-- The unique nonidentity member of a norm-character group of cardinality
two.  The identity remains a separate element of the ensuing products. -/
private noncomputable def uniqueQuadraticNormCharacter
    (hcard : Nat.card (NormCharacter F K) = 2) : NormCharacter F K :=
  Classical.choose
    (((Nat.card_eq_two_iff' (1 : NormCharacter F K)).1 hcard).exists)

private theorem uniqueQuadraticNormCharacter_ne_one
    (hcard : Nat.card (NormCharacter F K) = 2) :
    uniqueQuadraticNormCharacter F K hcard ≠ 1 :=
  Classical.choose_spec
    (((Nat.card_eq_two_iff' (1 : NormCharacter F K)).1 hcard).exists)

private theorem normCharacter_eq_one_or_eq_unique
    (hcard : Nat.card (NormCharacter F K) = 2)
    (mu : NormCharacter F K) :
    mu = 1 ∨ mu = uniqueQuadraticNormCharacter F K hcard := by
  by_cases hmu : mu = 1
  · exact Or.inl hmu
  · exact Or.inr
      (((Nat.card_eq_two_iff' (1 : NormCharacter F K)).1 hcard).unique
        hmu (uniqueQuadraticNormCharacter_ne_one F K hcard))

end LocalSetup

/-! ## Conductor zero: direct endpoint calculation -/

section EndpointZeroGeneric

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private def endpointZeroGamma
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    AdmissibleGamma E chi psi :=
  ⟨pi ^ ((chi.conductor : ℤ) + psi.conductor), by
    rw [Units.val_zpow_eq_zpow_val, ord_uniformizer_zpow E hpi]⟩

@[simp] private theorem endpointZeroGamma_coe
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    (endpointZeroGamma E chi psi pi hpi : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor) :=
  rfl

private def endpointZeroDelta
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) : ℂ :=
  deltaFinite chi psi (endpointZeroGamma E chi psi pi hpi)

private def endpointZeroPower
    (chi : LocalQuasiCharData E) (pi : Eˣ) (a : ℤ) : ℂ :=
  (((chi.character pi) ^ a : ℂˣ) : ℂ)

private theorem endpointZeroPower_add
    (chi : LocalQuasiCharData E) (pi : Eˣ) (a b : ℤ) :
    endpointZeroPower E chi pi (a + b) =
      endpointZeroPower E chi pi a * endpointZeroPower E chi pi b := by
  simp [endpointZeroPower, zpow_add₀]

private theorem endpointZeroDelta_conductor_zero
    (chi : LocalQuasiCharData E) (hchi : chi.conductor = 0)
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    endpointZeroDelta E chi psi pi hpi =
      endpointZeroPower E chi pi psi.conductor := by
  rw [endpointZeroDelta, deltaFinite_conductor_zero E chi hchi]
  change ((chi.character
      (pi ^ ((chi.conductor : ℤ) + psi.conductor)) : ℂˣ) : ℂ) = _
  rw [hchi]
  norm_num [endpointZeroPower, map_zpow]

/-- A conductor-zero twist of a positive-conductor character. -/
private abbrev endpointZeroUnramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor) :
    LocalQuasiCharData E where
  character := theta.character * nu.character
  conductor := theta.conductor
  isConductor := theta.isConductor.mul_of_gt nu.isConductor (by omega)

private def endpointZeroTwistGamma
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    AdmissibleGamma E (endpointZeroUnramifiedTwist E theta nu hnu htheta) psi :=
  ⟨Gamma, by simpa using Gamma.property⟩

private theorem finiteGaussSum_endpointZeroUnramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    finiteGaussSum (endpointZeroUnramifiedTwist E theta nu hnu htheta) psi
        (endpointZeroTwistGamma E theta nu hnu htheta psi Gamma) =
      finiteGaussSum theta psi Gamma := by
  letI := unitFiltrationQuotientFintype E (Nat.zero_le theta.conductor)
  change (∑ z : UnitFiltrationQuotient E 0 theta.conductor (Nat.zero_le _),
      finiteGaussSummand (endpointZeroUnramifiedTwist E theta nu hnu htheta)
        psi (endpointZeroTwistGamma E theta nu hnu htheta psi Gamma) z) =
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
  simp only [finiteGaussSummandRepresentative, endpointZeroTwistGamma,
    ContinuousQuasiChar.mul_apply, hnuUnit, mul_one]

private theorem deltaFinite_endpointZeroUnramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    deltaFinite (endpointZeroUnramifiedTwist E theta nu hnu htheta) psi
        (endpointZeroTwistGamma E theta nu hnu htheta psi Gamma) =
      (nu.character (Gamma : Eˣ) : ℂ) * deltaFinite theta psi Gamma := by
  rw [deltaFinite, deltaFinite,
    finiteGaussSum_endpointZeroUnramifiedTwist E theta nu hnu htheta psi Gamma]
  have hvalue :
      (((endpointZeroUnramifiedTwist E theta nu hnu htheta).character
        (endpointZeroTwistGamma E theta nu hnu htheta psi Gamma : Eˣ) :
          ℂˣ) : ℂ) =
        (theta.character (Gamma : Eˣ) : ℂ) *
          (nu.character (Gamma : Eˣ) : ℂ) := by
    exact congrArg Units.val
      (ContinuousQuasiChar.mul_apply theta.character nu.character (Gamma : Eˣ))
  rw [hvalue]
  ring

private theorem endpointZeroDelta_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    endpointZeroDelta E (endpointZeroUnramifiedTwist E theta nu hnu htheta)
        psi pi hpi =
      endpointZeroPower E nu pi ((theta.conductor : ℤ) + psi.conductor) *
        endpointZeroDelta E theta psi pi hpi := by
  have hGamma :
      endpointZeroGamma E (endpointZeroUnramifiedTwist E theta nu hnu htheta)
          psi pi hpi =
        endpointZeroTwistGamma E theta nu hnu htheta psi
          (endpointZeroGamma E theta psi pi hpi) := by
    apply Subtype.ext
    rfl
  rw [endpointZeroDelta, hGamma]
  simpa only [endpointZeroDelta, endpointZeroPower, endpointZeroGamma_coe,
      map_zpow, Units.val_zpow_eq_zpow_val] using
    (deltaFinite_endpointZeroUnramifiedTwist E theta nu hnu htheta psi
      (endpointZeroGamma E theta psi pi hpi))

end EndpointZeroGeneric

section EndpointZeroQuadratic

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem endpointZero_quadraticPair
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (chiK : LocalQuasiCharData K) (hchiK : chiK.conductor = 0)
    (tau : LocalQuasiCharData F) (htau : tau.conductor = 1)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.conductor = 2 * psiF.conductor + 1)
    (piF : Fˣ) (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (piK : Kˣ) (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hchar : chiK.character piK = chiF.character piF) :
    endpointZeroDelta K chiK psiK piK hpiK *
        endpointZeroDelta F tau psiF piF hpiF =
      endpointZeroDelta F chiF psiF piF hpiF *
        endpointZeroDelta F
          (endpointZeroUnramifiedTwist F tau chiF hchiF (by omega))
          psiF piF hpiF := by
  have hpower (a : ℤ) :
      endpointZeroPower K chiK piK a = endpointZeroPower F chiF piF a := by
    simp only [endpointZeroPower, hchar]
  rw [endpointZeroDelta_conductor_zero K chiK hchiK,
    endpointZeroDelta_conductor_zero F chiF hchiF,
    endpointZeroDelta_unramifiedTwist F tau chiF hchiF (by omega)]
  rw [hpower, hpsi, htau]
  rw [show 2 * psiF.conductor + 1 =
      psiF.conductor + (1 + psiF.conductor) by ring,
    endpointZeroPower_add]
  ring

end EndpointZeroQuadratic

section EndpointZeroSpecialization

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

/-- The conductor-zero branch uses only endpoint finite sums.  In
particular, neither side constructs a stationary quotient class. -/
private theorem firstMain_tameQuadratic_conductor_zero
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchiF : chiF.conductor = 0)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    endpointZeroDelta K chiK psiK
        (tameQuadraticUpperUniformizer K piK hpiK)
        (by simpa [tameQuadraticUpperUniformizer] using hpiK) *
      endpointZeroDelta F
        (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau)
        psiF (tameQuadraticLowerUniformizer F K piK hpiK)
        (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres) =
      endpointZeroDelta F chiF psiF
          (tameQuadraticLowerUniformizer F K piK hpiK)
          (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres) *
        endpointZeroDelta F
          (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau)
          psiF (tameQuadraticLowerUniformizer F K piK hpiK)
          (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres) := by
  have hchiK : chiK.conductor = 0 := by
    rw [chiF.conductor_compNorm_eq_belowBreak
      F K ht hres piK hpiK hgen chiK hchi (by omega), hchiF]
  have hpsiCond : psiK.conductor = 2 * psiF.conductor + 1 := by
    have h := psiF.conductor_compTrace_eq_cyclicPrime
      F K ht hres piK hpiK hgen psiK hpsi
    rw [hdegree] at h
    norm_num at h ⊢
    exact h
  have htwistCond :
      (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau).conductor =
        1 := by
    simpa using
      (minimalOrbit_twist_conductor_eq_of_lt
        F K ht hres piK hpiK hgen chiF hminimal (by omega) tau htau)
  have htwist :
      tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau =
        endpointZeroUnramifiedTwist F
          (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau)
          chiF hchiF (by
            rw [tameQuadraticNormCharacterData_conductor_of_ne
              F K hres piK hpiK ht hgen tau htau]
            omega) := by
    apply localQuasiCharData_ext
    · simp only [tameQuadraticTwistData_character,
        tameQuadraticNormCharacterData_character]
    · change
        (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau).conductor =
          (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau).conductor
      rw [htwistCond, tameQuadraticNormCharacterData_conductor_of_ne
        F K hres piK hpiK ht hgen tau htau]
  rw [htwist]
  apply endpointZero_quadraticPair F K chiF hchiF chiK hchiK
    (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau)
    (tameQuadraticNormCharacterData_conductor_of_ne
      F K hres piK hpiK ht hgen tau htau)
    psiF psiK hpsiCond
    (tameQuadraticLowerUniformizer F K piK hpiK)
    (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres)
    (tameQuadraticUpperUniformizer K piK hpiK)
    (by simpa [tameQuadraticUpperUniformizer] using hpiK)
  change chiK.character (tameQuadraticUpperUniformizer K piK hpiK) =
    chiF.character (tameQuadraticLowerUniformizer F K piK hpiK)
  rw [hchi]
  rfl

end EndpointZeroSpecialization

/-! ## Conductor one: exact reduction to Hasse--Davenport -/

/-- Package an arbitrary unit of the exact conductor-one denominator order. -/
private def conductorOneGamma
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ)) :
    AdmissibleGamma E chi psi :=
  ⟨gamma, by
    rw [hgamma]
    congr 1
    norm_cast
    omega⟩

@[simp] private theorem conductorOneGamma_coe
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ)) :
    (conductorOneGamma chi hchi psi gamma hgamma : Eˣ) = gamma :=
  rfl

section ConductorOne

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField K) := residueFieldFintype K

/-- Canonical conductor-one denominator downstairs: the exact norm
uniformizer to exponent `n_F+1`. -/
private def tameQuadraticConductorOneGammaF
    (psiF : LocalAddCharData F) : Fˣ :=
  tameQuadraticLowerUniformizer F K piK hpiK ^ (psiF.conductor + 1)

include hres in
private theorem tameQuadraticConductorOneGammaF_order
    (psiF : LocalAddCharData F) :
    ord F (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F) =
      ((psiF.conductor + 1 : ℤ) : WithTop ℤ) := by
  rw [tameQuadraticConductorOneGammaF, Units.val_zpow_eq_zpow_val,
    ord_uniformizer_zpow F
      (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres)]

/-- The same exact denominator mapped upstairs. -/
private def tameQuadraticConductorOneGammaK
    (psiF : LocalAddCharData F) : Kˣ :=
  Units.map (algebraMap F K).toMonoidHom
    (tameQuadraticConductorOneGammaF F K piK hpiK psiF)

include ht hres hgen in
private theorem tameQuadraticConductorOneGammaK_order
    (hdegree : Module.finrank F K = 2)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace) :
    ord K (tameQuadraticConductorOneGammaK F K piK hpiK psiF : K) =
      ((psiK.conductor + 1 : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at h
    exact h.symm
  have hnK := psiF.conductor_compTrace_eq_cyclicPrime
    F K ht hres piK hpiK hgen psiK hpsi
  change ord K (algebraMap F K
    (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F)) = _
  rw [ord_algebraMap, hram,
    tameQuadraticConductorOneGammaF_order F K hres piK hpiK,
    hnK, hdegree]
  norm_cast
  ring

/-- Residual norm pullback in residue degree one is the degree power. -/
private theorem tameQuadratic_residualMulChar_compNorm_pow
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchiF : chiF.conductor ≤ 1) (hchiK : chiK.conductor ≤ 1)
    (hcomp : chiK.character = chiF.character.compNorm)
    (x : ResidueField F) :
    residualMulChar K chiK (tameQuadraticResidueEquiv F K hres x) =
      residualMulChar F chiF (x ^ Module.finrank F K) := by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero, MulChar.map_zero]
    have hp0 : Module.finrank F K ≠ 0 := Nat.ne_of_gt Module.finrank_pos
    rw [zero_pow hp0, MulChar.map_zero]
  let xu : (ResidueField F)ˣ := Units.mk0 x hx
  let uF : unitGroup F := teichmullerLocalUnits F xu
  have huFord : ord F (((uF : unitGroup F) : Fˣ) : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F (uF : Fˣ)).1 uF.property
  let uKval : Kˣ := Units.map (algebraMap F K) (uF : Fˣ)
  have huKord : ord K (uKval : K) = 0 := by
    dsimp only [uKval]
    change ord K (algebraMap F K ((((uF : unitGroup F) : Fˣ) : F))) = 0
    rw [ord_algebraMap, huFord]
    simp
  let uK : unitGroup K :=
    ⟨uKval, (mem_unitGroup_iff_ord_eq_zero K uKval).2 huKord⟩
  have hresF :
      ((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F) = x := by
    rw [residueUnits_teichmullerLocalUnits]
    rfl
  have hresKunits : residueUnits K uK =
      Units.map (extensionResidueMap F K) (residueUnits F uF) := by
    apply Units.ext
    rw [residueUnits_coe]
    change residueMap K (unitGroupMulEquivRingOfIntegers K uK) =
      extensionResidueMap F K
        (((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F))
    rw [residueUnits_coe]
    rfl
  have hresK :
      ((residueUnits K uK : (ResidueField K)ˣ) : ResidueField K) =
        tameQuadraticResidueEquiv F K hres x := by
    rw [hresKunits]
    change extensionResidueMap F K
        (((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F)) =
      tameQuadraticResidueEquiv F K hres x
    rw [hresF, tameQuadraticResidueEquiv_apply]
  have hresFpow :
      ((residueUnits F (uF ^ Module.finrank F K) : (ResidueField F)ˣ) :
          ResidueField F) = x ^ Module.finrank F K := by
    rw [map_pow]
    exact congrArg (fun z : ResidueField F ↦ z ^ Module.finrank F K) hresF
  rw [← hresK, residualMulChar_residueUnits K chiK hchiK,
    ← hresFpow, residualMulChar_residueUnits F chiF hchiF]
  have hnorm : normUnits F K (uK : Kˣ) =
      (uF : Fˣ) ^ Module.finrank F K := by
    apply Units.ext
    change norm F K (algebraMap F K (((uF : unitGroup F) : Fˣ) : F)) =
      (((uF : unitGroup F) : Fˣ) : F) ^ Module.finrank F K
    exact norm_algebraMap F K (((uF : unitGroup F) : Fˣ) : F)
  change (((chiK.character (uK : Kˣ) : ℂˣ) : ℂ)) =
    ((chiF.character ((uF : Fˣ) ^ Module.finrank F K) : ℂˣ) : ℂ)
  rw [hcomp, ContinuousQuasiChar.compNorm_apply, hnorm, map_pow]

private theorem tameQuadratic_residualMulChar_compNorm_two
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchiF : chiF.conductor ≤ 1) (hchiK : chiK.conductor ≤ 1)
    (hcomp : chiK.character = chiF.character.compNorm)
    (x : ResidueField F) :
    residualMulChar K chiK (tameQuadraticResidueEquiv F K hres x) =
      (residualMulChar F chiF ^ 2) x := by
  rw [tameQuadratic_residualMulChar_compNorm_pow F K hres chiF chiK
    hchiF hchiK hcomp, hdegree, map_pow]
  exact (residualMulChar F chiF).pow_apply' two_ne_zero x |>.symm

private theorem tameQuadratic_residualAddChar_compTrace_two
    (hdegree : Module.finrank F K = 2)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    (x : ResidueField F) :
    residualAddChar K psiK
        (tameQuadraticConductorOneGammaK F K piK hpiK psiF)
        (tameQuadraticConductorOneGammaK_order F K ht hres piK hpiK hgen
          hdegree psiF psiK hpsi)
        (tameQuadraticResidueEquiv F K hres x) =
      (residualAddChar F psiF
        (tameQuadraticConductorOneGammaF F K piK hpiK psiF)
        (tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF)).mulShift
          (2 : ResidueField F) x := by
  let a : ringOfIntegers F := teichmuller F x
  have haF : (a : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 a.property
  let aK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) a
  have haKcoe : (aK : K) = algebraMap F K (a : F) :=
    Valuation.HasExtension.val_algebraMap a
  have haK : algebraMap F K (a : F) ∈ lattice K 0 := by
    rw [← haKcoe]
    exact (mem_lattice_zero_iff K).2 aK.property
  have hreduceF : reduce F (a : F) haF = x := by
    simp [a, reduce]
  have hreduceK : reduce K (algebraMap F K (a : F)) haK =
      tameQuadraticResidueEquiv F K hres x := by
    change residueMap K aK = extensionResidueMap F K x
    rw [← hreduceF]
    change residueMap K aK = extensionResidueMap F K (residueMap F a)
    rfl
  rw [← hreduceK, residualAddChar_integral_lift]
  change ((psiK.character
      (algebraMap F K (a : F) /
        algebraMap F K
          (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F)) :
          ℂˣ) : ℂ) = _
  rw [hpsi, ContinuousAddChar.compTrace_apply, ← map_div₀,
    trace_algebraMap, hdegree]
  have hpow := congrArg Units.val
    (AddChar.map_nsmul_eq_pow psiF.character.toAddChar 2
      ((a : F) / (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F)))
  change
    ((psiF.character
      (2 • ((a : F) /
        (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F))) : ℂˣ) :
          ℂ) =
      (((psiF.character
        ((a : F) /
          (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F)) : ℂˣ) :
            ℂ) ^ 2) at hpow
  rw [hpow, AddChar.mulShift_apply]
  have htwox : (2 : ResidueField F) * x = x + x := by ring
  rw [htwox, AddChar.map_add_eq_mul, ← hreduceF,
    residualAddChar_integral_lift]
  ring

private theorem tameQuadratic_upper_langlandsGaussSum
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchiF : chiF.conductor = 1) (hchiK : chiK.conductor = 1)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    langlandsGaussSum (residualMulChar K chiK)
        (residualAddChar K psiK
          (tameQuadraticConductorOneGammaK F K piK hpiK psiF)
          (tameQuadraticConductorOneGammaK_order F K ht hres piK hpiK hgen
            hdegree psiF psiK hpsi)) =
      residualMulChar F chiF (4 : ResidueField F) *
        langlandsGaussSum ((residualMulChar F chiF) ^ 2)
          (residualAddChar F psiF
            (tameQuadraticConductorOneGammaF F K piK hpiK psiF)
            (tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF)) := by
  let e := tameQuadraticResidueEquiv F K hres
  let chiBar := residualMulChar F chiF
  let psiBar := residualAddChar F psiF
    (tameQuadraticConductorOneGammaF F K piK hpiK psiF)
    (tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF)
  let chiBarK := residualMulChar K chiK
  let psiBarK := residualAddChar K psiK
    (tameQuadraticConductorOneGammaK F K piK hpiK psiF)
    (tameQuadraticConductorOneGammaK_order F K ht hres piK hpiK hgen
      hdegree psiF psiK hpsi)
  have hpoint (x : ResidueField F) :
      chiBarK⁻¹ (e x) * psiBarK (e x) =
        (chiBar ^ 2)⁻¹ x * (psiBar.mulShift (2 : ResidueField F)) x := by
    have hmul := tameQuadratic_residualMulChar_compNorm_two F K hres hdegree
      chiF chiK (by omega) (by omega) hcomp x
    have hadd := tameQuadratic_residualAddChar_compTrace_two F K ht hres piK
      hpiK hgen hdegree psiF psiK hpsi x
    change chiBarK⁻¹ (e x) * psiBarK (e x) = _
    rw [MulChar.inv_apply_eq_inv', hmul, MulChar.inv_apply_eq_inv']
    exact congrArg (fun z : ℂ ↦ ((chiBar ^ 2) x)⁻¹ * z) hadd
  have htransport : langlandsGaussSum chiBarK psiBarK =
      langlandsGaussSum (chiBar ^ 2)
        (psiBar.mulShift (2 : ResidueField F)) := by
    rw [langlandsGaussSum_eq_neg_gaussSum_inv,
      langlandsGaussSum_eq_neg_gaussSum_inv]
    congr 1
    rw [gaussSum, gaussSum]
    calc
      (∑ y : ResidueField K, chiBarK⁻¹ y * psiBarK y) =
          ∑ x : ResidueField F, chiBarK⁻¹ (e x) * psiBarK (e x) := by
            exact (e.toEquiv.sum_comp
              (fun y : ResidueField K ↦ chiBarK⁻¹ y * psiBarK y)).symm
      _ = ∑ x : ResidueField F,
          (chiBar ^ 2)⁻¹ x * (psiBar.mulShift (2 : ResidueField F)) x := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact hpoint x
  have htwo : (2 : ResidueField F) ≠ 0 := Ring.two_ne_zero hchar
  let twoUnit : (ResidueField F)ˣ := Units.mk0 2 htwo
  have hscale := langlandsGaussSum_mulShift_unit
    (chiBar ^ 2) psiBar twoUnit
  have hfactor : (chiBar ^ 2) (2 : ResidueField F) =
      chiBar (4 : ResidueField F) := by
    rw [chiBar.pow_apply' two_ne_zero]
    calc
      chiBar (2 : ResidueField F) ^ 2 =
          chiBar ((2 : ResidueField F) * 2) := by
        rw [pow_two]
        exact (map_mul chiBar 2 2).symm
      _ = chiBar (4 : ResidueField F) := by norm_num
  change langlandsGaussSum chiBarK psiBarK =
    chiBar (4 : ResidueField F) * langlandsGaussSum (chiBar ^ 2) psiBar
  rw [htransport]
  calc
    langlandsGaussSum (chiBar ^ 2)
        (psiBar.mulShift (2 : ResidueField F)) =
        langlandsGaussSum (chiBar ^ 2)
          (psiBar.mulShift ((twoUnit : (ResidueField F)ˣ) :
            ResidueField F)) := rfl
    _ = (chiBar ^ 2) ((twoUnit : (ResidueField F)ˣ) : ResidueField F) *
        langlandsGaussSum (chiBar ^ 2) psiBar := hscale
    _ = chiBar (4 : ResidueField F) *
        langlandsGaussSum (chiBar ^ 2) psiBar := by
      change (chiBar ^ 2) (2 : ResidueField F) * _ = _
      rw [hfactor]

private theorem tameQuadratic_upper_langlandsGaussPhase
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchiF : chiF.conductor = 1) (hchiK : chiK.conductor = 1)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    phase (langlandsGaussSum (residualMulChar K chiK)
        (residualAddChar K psiK
          (tameQuadraticConductorOneGammaK F K piK hpiK psiF)
          (tameQuadraticConductorOneGammaK_order F K ht hres piK hpiK hgen
            hdegree psiF psiK hpsi))) =
      residualMulChar F chiF (4 : ResidueField F) *
        phase (langlandsGaussSum ((residualMulChar F chiF) ^ 2)
          (residualAddChar F psiF
            (tameQuadraticConductorOneGammaF F K piK hpiK psiF)
            (tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF))) := by
  let chiBar := residualMulChar F chiF
  let psiBar := residualAddChar F psiF
    (tameQuadraticConductorOneGammaF F K piK hpiK psiF)
    (tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF)
  have htwo : (2 : ResidueField F) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : (4 : ResidueField F) ≠ 0 := by
    rw [show (4 : ResidueField F) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have hchi4 : chiBar (4 : ResidueField F) ≠ 0 :=
    IsUnit.ne_zero (hfour.isUnit.map chiBar)
  have hnorm : ‖chiBar (4 : ResidueField F)‖ = 1 :=
    finiteMulChar_norm_apply chiBar hfour
  have hpsiBar : psiBar ≠ 1 := residualAddChar_ne_one F psiF
    (tameQuadraticConductorOneGammaF F K piK hpiK psiF)
    (tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF)
  have hgauss : langlandsGaussSum (chiBar ^ 2) psiBar ≠ 0 :=
    langlandsGaussSum_ne_zero (chiBar ^ 2) hpsiBar
  rw [tameQuadratic_upper_langlandsGaussSum F K ht hres piK hpiK hgen
    hdegree hchar chiF chiK psiF psiK hchiF hchiK hcomp hpsi,
    phase_mul hchi4 hgauss, phase_of_norm_eq_one hnorm]

include ht hres hpiK hgen in
private theorem tameQuadratic_normCharacter_residual_quadratic
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (normTau : LocalQuasiCharData F)
    (hnormChar : normTau.character = tau.1)
    (hnormCond : normTau.conductor = 1) :
    residualMulChar F normTau = finiteQuadraticChar (ResidueField F) := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  have htauSq : tau ^ 2 = 1 := by
    have hpow := pow_card_eq_one' (x := tau)
    rw [ramifiedNormCharacter_card F K ht hres piK hpiK hgen,
      hdegree] at hpow
    exact hpow
  have hresSq : (residualMulChar F normTau) ^ 2 = 1 := by
    ext xu
    rw [(residualMulChar F normTau).pow_apply' two_ne_zero,
      residualMulChar_apply_unit]
    have hpoint := congrArg
      (fun mu : NormCharacter F K => mu.1 (teichmullerLocalUnits F xu)) htauSq
    rw [NormCharacter.coe_pow, ContinuousQuasiChar.pow_apply,
      NormCharacter.coe_one, ContinuousQuasiChar.one_apply] at hpoint
    rw [hnormChar, MulChar.one_apply xu.isUnit]
    have hpoint' := congrArg Units.val hpoint
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hpoint'
  exact finiteMulChar_eq_finiteQuadraticChar hchar
    (residualMulChar F normTau)
    (residualMulChar_ne_one F normTau hnormCond) hresSq

private theorem tameQuadratic_residualMulChar_mul
    (theta chi prod : LocalQuasiCharData F)
    (hprod : prod.character = theta.character * chi.character) :
    residualMulChar F prod =
      residualMulChar F theta * residualMulChar F chi := by
  ext x
  rw [MulChar.mul_apply, residualMulChar_apply_unit,
    residualMulChar_apply_unit, residualMulChar_apply_unit, hprod,
    ContinuousQuasiChar.mul_apply]
  rfl

private theorem tameQuadratic_normCharacter_gammaF_eq_one
    (tau : NormCharacter F K) (psiF : LocalAddCharData F) :
    tau.1 (tameQuadraticConductorOneGammaF F K piK hpiK psiF) = 1 := by
  apply tau.eq_one_on_normRange F K
  refine ⟨tameQuadraticUpperUniformizer K piK hpiK ^
    (psiF.conductor + 1), ?_⟩
  change normUnits F K
      (tameQuadraticUpperUniformizer K piK hpiK ^ (psiF.conductor + 1)) =
    tameQuadraticConductorOneGammaF F K piK hpiK psiF
  rw [map_zpow]
  rfl

private theorem tameQuadratic_upper_characterFactor
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) :
    ((chiK.character
      (tameQuadraticConductorOneGammaK F K piK hpiK psiF) : ℂˣ) : ℂ) =
      ((chiF.character
        (tameQuadraticConductorOneGammaF F K piK hpiK psiF) : ℂˣ) : ℂ) ^ 2 := by
  rw [hcomp, ContinuousQuasiChar.compNorm_apply]
  have hnorm : Units.map (Algebra.norm F)
      (tameQuadraticConductorOneGammaK F K piK hpiK psiF) =
      tameQuadraticConductorOneGammaF F K piK hpiK psiF ^ 2 := by
    apply Units.ext
    change norm F K (algebraMap F K
      (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F)) =
      (tameQuadraticConductorOneGammaF F K piK hpiK psiF : F) ^ 2
    rw [norm_algebraMap, hdegree]
  rw [hnorm, map_pow]
  rfl

/-- Exact residue-level comparison data at conductor one.  Its three Gauss
sum fields state only the norm/trace reduction to the common residue field;
the Hasse--Davenport identity itself is proved below.  Thus the leading
minus and the inverse multiplicative character remain those of
`deltaFinite_conductor_one` and `langlandsGaussSum`. -/
structure TameQuadraticConductorOneResidualComparison
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (tau : NormCharacter F K)
    (hchiF : chiF.conductor = 1) (hchiK : chiK.conductor = 1)
    (htau : tau ≠ 1)
    (htwist : (tameQuadraticTwistData F K hres piK hpiK ht hgen
      chiF tau).conductor = 1) where
  gammaF : Fˣ
  gammaF_order : ord F (gammaF : F) =
    ((psiF.conductor + 1 : ℤ) : WithTop ℤ)
  gammaK : Kˣ
  gammaK_order : ord K (gammaK : K) =
    ((psiK.conductor + 1 : ℤ) : WithTop ℤ)
  upperCharacterFactor :
    ((chiK.character gammaK : ℂˣ) : ℂ) =
      ((chiF.character gammaF : ℂˣ) : ℂ) ^ 2
  normCharacterFactor : tau.1 gammaF = 1
  upperGaussPhase :
    phase (langlandsGaussSum (residualMulChar K chiK)
      (residualAddChar K psiK gammaK gammaK_order)) =
      residualMulChar F chiF (4 : ResidueField F) *
        phase (langlandsGaussSum ((residualMulChar F chiF) ^ 2)
          (residualAddChar F psiF gammaF gammaF_order))
  normGaussPhase :
    phase (langlandsGaussSum
      (residualMulChar F
        (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau))
      (residualAddChar F psiF gammaF gammaF_order)) =
      phase (langlandsGaussSum (finiteQuadraticChar (ResidueField F))
        (residualAddChar F psiF gammaF gammaF_order))
  twistGaussPhase :
    phase (langlandsGaussSum
      (residualMulChar F
        (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau))
      (residualAddChar F psiF gammaF gammaF_order)) =
      phase (langlandsGaussSum
        (residualMulChar F chiF * finiteQuadraticChar (ResidueField F))
        (residualAddChar F psiF gammaF gammaF_order))

include ht hres hpiK hgen in
private noncomputable def
    tameQuadraticConductorOneResidualComparison_of_intrinsic
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (tau : NormCharacter F K)
    (hchiF : chiF.conductor = 1) (hchiK : chiK.conductor = 1)
    (htau : tau ≠ 1)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (htwist : (tameQuadraticTwistData F K hres piK hpiK ht hgen
      chiF tau).conductor = 1) :
    TameQuadraticConductorOneResidualComparison
      F K ht hres piK hpiK hgen chiF chiK psiF psiK tau
        hchiF hchiK htau htwist where
  gammaF := tameQuadraticConductorOneGammaF F K piK hpiK psiF
  gammaF_order :=
    tameQuadraticConductorOneGammaF_order F K hres piK hpiK psiF
  gammaK := tameQuadraticConductorOneGammaK F K piK hpiK psiF
  gammaK_order :=
    tameQuadraticConductorOneGammaK_order F K ht hres piK hpiK hgen
      hdegree psiF psiK hpsi
  upperCharacterFactor :=
    tameQuadratic_upper_characterFactor F K piK hpiK hdegree
      chiF chiK hcomp psiF
  normCharacterFactor :=
    tameQuadratic_normCharacter_gammaF_eq_one F K piK hpiK tau psiF
  upperGaussPhase := tameQuadratic_upper_langlandsGaussPhase
    F K ht hres piK hpiK hgen hdegree hchar
      chiF chiK psiF psiK hchiF hchiK hcomp hpsi
  normGaussPhase := by
    rw [tameQuadratic_normCharacter_residual_quadratic
      F K ht hres piK hpiK hgen hdegree hchar tau htau
      (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau)
      (tameQuadraticNormCharacterData_character
        F K hres piK hpiK ht hgen tau)
      (tameQuadraticNormCharacterData_conductor_of_ne
        F K hres piK hpiK ht hgen tau htau)]
  twistGaussPhase := by
    have hnorm := tameQuadratic_normCharacter_residual_quadratic
      F K ht hres piK hpiK hgen hdegree hchar tau htau
      (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau)
      (tameQuadraticNormCharacterData_character
        F K hres piK hpiK ht hgen tau)
      (tameQuadraticNormCharacterData_conductor_of_ne
        F K hres piK hpiK ht hgen tau htau)
    have hmul := tameQuadratic_residualMulChar_mul F
      (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau) chiF
      (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau)
      (by
        rw [tameQuadraticNormCharacterData_character]
        exact tameQuadraticTwistData_character
          F K hres piK hpiK ht hgen chiF tau)
    rw [hmul, hnorm, mul_comm]

/-- The conductor-one branch.  The four local constants are reduced by
`ResidueFormula`; the two leading minus signs on each side cancel, and the
remaining equality is exactly degree-two Hasse--Davenport. -/
private theorem firstMain_tameQuadratic_conductor_one
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (tau : NormCharacter F K)
    (hchiF : chiF.conductor = 1) (hchiK : chiK.conductor = 1)
    (htau : tau ≠ 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (C : TameQuadraticConductorOneResidualComparison
      F K ht hres piK hpiK hgen chiF chiK psiF psiK tau
        hchiF hchiK htau
        (minimalOrbit_twist_conductor_eq_of_critical
          F K ht hres piK hpiK hgen chiF hminimal (by simpa using hchiF)
            tau htau)) :
    let normTau := tameQuadraticNormCharacterData
      F K hres piK hpiK ht hgen tau
    let twistTau := tameQuadraticTwistData
      F K hres piK hpiK ht hgen chiF tau
    let GammaF := conductorOneGamma chiF hchiF psiF C.gammaF C.gammaF_order
    let GammaK := conductorOneGamma chiK hchiK psiK C.gammaK C.gammaK_order
    let GammaNorm := conductorOneGamma normTau
      (tameQuadraticNormCharacterData_conductor_of_ne
        F K hres piK hpiK ht hgen tau htau) psiF C.gammaF C.gammaF_order
    let GammaTwist := conductorOneGamma twistTau
      (minimalOrbit_twist_conductor_eq_of_critical
        F K ht hres piK hpiK hgen chiF hminimal (by simpa using hchiF)
          tau htau) psiF C.gammaF C.gammaF_order
    deltaFinite chiK psiK GammaK * deltaFinite normTau psiF GammaNorm =
      deltaFinite chiF psiF GammaF * deltaFinite twistTau psiF GammaTwist := by
  let htwist := minimalOrbit_twist_conductor_eq_of_critical
    F K ht hres piK hpiK hgen chiF hminimal (by simpa using hchiF) tau htau
  let normTau := tameQuadraticNormCharacterData
    F K hres piK hpiK ht hgen tau
  let twistTau := tameQuadraticTwistData
    F K hres piK hpiK ht hgen chiF tau
  let GammaF := conductorOneGamma chiF hchiF psiF C.gammaF C.gammaF_order
  let GammaK := conductorOneGamma chiK hchiK psiK C.gammaK C.gammaK_order
  let GammaNorm := conductorOneGamma normTau
    (tameQuadraticNormCharacterData_conductor_of_ne
      F K hres piK hpiK ht hgen tau htau) psiF C.gammaF C.gammaF_order
  let GammaTwist := conductorOneGamma twistTau htwist
    psiF C.gammaF C.gammaF_order
  let psiBar := residualAddChar F psiF C.gammaF C.gammaF_order
  let chiBar := residualMulChar F chiF
  have hpsiBar : psiBar ≠ 1 :=
    residualAddChar_ne_one F psiF C.gammaF C.gammaF_order
  have hHD := hasseDavenportProduct_two_phase
    (k := ResidueField F) hchar chiBar psiBar hpsiBar
  have htwistFactor :
      (((twistTau.character C.gammaF : ℂˣ) : ℂ)) =
        ((chiF.character C.gammaF : ℂˣ) : ℂ) := by
    change ((((tau.1 * chiF.character) C.gammaF : ℂˣ) : ℂ)) = _
    rw [ContinuousQuasiChar.mul_apply, C.normCharacterFactor, one_mul]
  dsimp only
  rw [deltaFinite_conductor_one K chiK hchiK,
    deltaFinite_conductor_one F normTau
      (tameQuadraticNormCharacterData_conductor_of_ne
        F K hres piK hpiK ht hgen tau htau),
    deltaFinite_conductor_one F chiF hchiF,
    deltaFinite_conductor_one F twistTau htwist]
  change
    (-((chiK.character C.gammaK : ℂˣ) : ℂ) *
        phase (langlandsGaussSum (residualMulChar K chiK)
          (residualAddChar K psiK C.gammaK C.gammaK_order))) *
      (-((normTau.character C.gammaF : ℂˣ) : ℂ) *
        phase (langlandsGaussSum (residualMulChar F normTau) psiBar)) =
      (-((chiF.character C.gammaF : ℂˣ) : ℂ) *
        phase (langlandsGaussSum chiBar psiBar)) *
      (-((twistTau.character C.gammaF : ℂˣ) : ℂ) *
        phase (langlandsGaussSum (residualMulChar F twistTau) psiBar))
  have hnormFactor : ((normTau.character C.gammaF : ℂˣ) : ℂ) = 1 := by
    rw [show normTau.character = tau.1 by
      exact tameQuadraticNormCharacterData_character
        F K hres piK hpiK ht hgen tau]
    rw [C.normCharacterFactor]
    rfl
  rw [C.upperCharacterFactor, hnormFactor, C.upperGaussPhase,
    C.normGaussPhase, C.twistGaussPhase, htwistFactor]
  change
    ((-((chiF.character C.gammaF : ℂˣ) : ℂ) ^ 2) *
        (chiBar (4 : ResidueField F) *
          phase (langlandsGaussSum (chiBar ^ 2) psiBar))) *
      (-1 * phase (langlandsGaussSum (finiteQuadraticChar (ResidueField F))
        psiBar)) =
      (-((chiF.character C.gammaF : ℂˣ) : ℂ) *
        phase (langlandsGaussSum chiBar psiBar)) *
      (-((chiF.character C.gammaF : ℂˣ) : ℂ) *
        phase (langlandsGaussSum
          (chiBar * finiteQuadraticChar (ResidueField F)) psiBar))
  calc
    (-((chiF.character C.gammaF : ℂˣ) : ℂ) ^ 2) *
          (chiBar (4 : ResidueField F) *
            phase (langlandsGaussSum (chiBar ^ 2) psiBar)) *
        (-1 * phase (langlandsGaussSum
          (finiteQuadraticChar (ResidueField F)) psiBar)) =
        ((chiF.character C.gammaF : ℂˣ) : ℂ) ^ 2 *
          (chiBar (4 : ResidueField F) *
            phase (langlandsGaussSum (chiBar ^ 2) psiBar) *
            phase (langlandsGaussSum
              (finiteQuadraticChar (ResidueField F)) psiBar)) := by ring
    _ = ((chiF.character C.gammaF : ℂˣ) : ℂ) ^ 2 *
          (phase (langlandsGaussSum chiBar psiBar) *
            phase (langlandsGaussSum
              (chiBar * finiteQuadraticChar (ResidueField F)) psiBar)) := by
      rw [hHD]
    _ = (-((chiF.character C.gammaF : ℂˣ) : ℂ) *
          phase (langlandsGaussSum chiBar psiBar)) *
        (-((chiF.character C.gammaF : ℂˣ) : ℂ) *
          phase (langlandsGaussSum
            (chiBar * finiteQuadraticChar (ResidueField F)) psiBar)) := by ring

end ConductorOne

/-! ## The conductor-one quadratic norm-character factor -/

section QuadraticNormFactor

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Fintype (ResidueField F) := residueFieldFintype F

/-- A conductor-one quadratic norm character contributes the manuscript's
basic phase `Q(2,0)`.  The outer minus in `ResidueFormula` cancels the minus
already built into `langlandsGaussSum`. -/
private theorem deltaFinite_quadratic_conductor_one
    (hchar : ringChar (ResidueField F) ≠ 2)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F) (gamma : Fˣ)
    (hgamma : ord F (gamma : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ))
    (hresidual : residualMulChar F chi =
      finiteQuadraticChar (ResidueField F))
    (hvalue : ((chi.character gamma : ℂˣ) : ℂ) = 1) :
    deltaFinite chi psi
        (conductorOneGamma chi hchi psi gamma hgamma) =
      quadraticPhase (residualAddChar F psi gamma hgamma) 2 0 := by
  let psiBar := residualAddChar F psi gamma hgamma
  have hpsiBar : psiBar ≠ 1 :=
    residualAddChar_ne_one F psi gamma hgamma
  let nu := finiteQuadraticChar (ResidueField F)
  have hnuInv : nu⁻¹ = nu :=
    (finiteQuadraticChar_isQuadratic (ResidueField F)).inv
  have hGauss : gaussSum nu psiBar ≠ 0 := gaussSum_ne_zero hpsiBar
  have hsum : quadraticSum psiBar 2 0 = gaussSum nu psiBar := by
    rw [quadraticSum]
    simp only [zero_mul, add_zero]
    have htwo : (2 : ResidueField F) ≠ 0 := Ring.two_ne_zero hchar
    have htwoDiv : (2 : ResidueField F) / 2 = 1 := div_self htwo
    rw [htwoDiv, sum_quadratic_eq_gaussSum hchar hpsiBar one_ne_zero]
    simp [nu]
  rw [deltaFinite_conductor_one F chi hchi]
  change
    -((chi.character gamma : ℂˣ) : ℂ) *
        phase (langlandsGaussSum (residualMulChar F chi) psiBar) =
      quadraticPhase psiBar 2 0
  rw [hvalue, neg_mul, one_mul, hresidual]
  change -phase (-gaussSum nu⁻¹ psiBar) = phase (quadraticSum psiBar 2 0)
  rw [hnuInv, hsum]
  rw [show -gaussSum nu psiBar = (-1 : ℂ) * gaussSum nu psiBar by ring,
    phase_mul (neg_ne_zero.mpr one_ne_zero) hGauss,
    phase_of_norm_eq_one (by norm_num)]
  ring

end QuadraticNormFactor

/-! ## Higher conductors: common elementary factor -/

section HigherBaseFactor

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The nonresidual Lamprecht factor upstairs is exactly the square of the
downstairs one.  Both the denominator and stationary unit are literal
base-field images, so `N(a)=a^2` and `Tr(a)=2a` apply without a hidden
denominator change. -/
private theorem lamprechtBaseFactor_tameQuadratic
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom (GammaF : Fˣ))
    (betaF : Fˣ) (betaK : Kˣ)
    (hbeta : betaK = Units.map (algebraMap F K).toMonoidHom betaF) :
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor K chiK psiK GammaK betaK =
      ((((chiF.character (GammaF : Fˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor F chiF psiF GammaF betaF) ^ 2 := by
  have hnormGamma : Units.map (Algebra.norm F) (GammaK : Kˣ) =
      (GammaF : Fˣ) ^ 2 := by
    rw [hGamma]
    ext
    simp [hdegree]
  have hnormBeta : Units.map (Algebra.norm F) betaK = betaF ^ 2 := by
    rw [hbeta]
    ext
    simp [hdegree]
  unfold lamprechtElementaryFactor
  change
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ)) *
        ((((psiK.character
            ((betaK : K) / ((GammaK : Kˣ) : K)) : ℂˣ) : ℂ)) *
          ((((chiK.character betaK : ℂˣ) : ℂ))⁻¹)) = _
  rw [hchi, hpsi, ContinuousQuasiChar.compNorm_apply,
    ContinuousQuasiChar.compNorm_apply, hnormGamma, hnormBeta,
    map_pow, map_pow]
  have htrace : trace F K ((betaK : K) / ((GammaK : Kˣ) : K)) =
      2 • ((betaF : F) / ((GammaF : Fˣ) : F)) := by
    rw [hbeta, hGamma]
    change trace F K
        (algebraMap F K (betaF : F) /
          algebraMap F K ((GammaF : Fˣ) : F)) = _
    rw [← map_div₀, trace_algebraMap, hdegree]
  rw [ContinuousAddChar.compTrace_apply, htrace]
  have hpsiPower := congrArg Units.val
    (AddChar.map_nsmul_eq_pow psiF.character.toAddChar
      2 ((betaF : F) / ((GammaF : Fˣ) : F)))
  change
    (((psiF.character
      (2 • ((betaF : F) / ((GammaF : Fˣ) : F))) : ℂˣ) : ℂ)) =
      (((psiF.character ((betaF : F) / ((GammaF : Fˣ) : F)) : ℂˣ) : ℂ) ^ 2)
        at hpsiPower
  rw [hpsiPower]
  simp only [Units.val_pow_eq_pow_val, inv_pow, mul_pow]

end HigherBaseFactor

section HigherIntrinsicCommon

open Polynomial IsLocalRing

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)
  (hdegree : Module.finrank F K = 2)

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField K) := residueFieldFintype K

private noncomputable def hcSigma : Gal(K/F) :=
  PrimeCyclicExtension.generator F K

private noncomputable def hcRho : K :=
  (piK : K) - hcSigma F K (piK : K)

local instance : DecidableEq Gal(K/F) := Classical.decEq _

include hdegree in
private theorem hcSigma_sq : hcSigma F K ^ 2 = 1 := by
  have h := pow_orderOf_eq_one (hcSigma F K)
  rw [show orderOf (hcSigma F K) = 2 by
    exact (PrimeCyclicExtension.orderOf_generator F K).trans hdegree] at h
  exact h

include hdegree in
private theorem hcSigma_rho :
    hcSigma F K (hcRho F K piK) = -hcRho F K piK := by
  rw [hcRho, map_sub]
  have hsq := hcSigma_sq F K hdegree
  have hcomp : hcSigma F K (hcSigma F K (piK : K)) = (piK : K) := by
    have := DFunLike.congr_fun hsq (piK : K)
    simpa using this
  rw [hcomp]
  ring

include hdegree in
private theorem hcGal_univ :
    (Finset.univ : Finset Gal(K/F)) =
      insert (1 : Gal(K/F))
        (singleton (hcSigma F K) : Finset Gal(K/F)) := by
  classical
  have hcard : (Finset.univ : Finset Gal(K/F)).card = 2 := by
    rw [Finset.card_univ, Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank F K, hdegree]
  have hsigNe : hcSigma F K ≠ 1 := PrimeCyclicExtension.generator_ne_one F K
  have hsigNe' : (1 : Gal(K/F)) ≠ hcSigma F K := Ne.symm hsigNe
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    by_contra hnot
    have hsub : insert x
        (insert (1 : Gal(K/F))
          (singleton (hcSigma F K) : Finset Gal(K/F))) ⊆
        (Finset.univ : Finset Gal(K/F)) := by simp
    have hthree : (insert x
        (insert (1 : Gal(K/F))
          (singleton (hcSigma F K) : Finset Gal(K/F)))).card = 3 := by
      simp [hnot, hsigNe']
    have := Finset.card_le_card hsub
    rw [hthree, hcard] at this
    omega
  · rw [hcard]
    exact (Finset.card_insert_le (1 : Gal(K/F))
      (singleton (hcSigma F K) : Finset Gal(K/F))).trans_eq (by simp)

include ht hgen in
private theorem hcRho_ord :
    ord K (hcRho F K piK) = ((1 : ℤ) : WithTop ℤ) := by
  have hshell :=
    (lowerRamificationGroup_mem_and_not_mem_succ_iff_ord_sub_eq
      F K piK hgen).1
      (PrimeCyclicExtension.generator_mem_break_and_not_mem_succ F K ht)
  have hneg : hcRho F K piK =
      -(hcSigma F K (piK : K) - (piK : K)) := by
    simp [hcRho]
  rw [hneg, ord_neg]
  simpa [hcSigma] using hshell

private noncomputable def hcRhoUnit : Kˣ :=
  Units.mk0 (hcRho F K piK) <|
    (ord_ne_top_iff K).1 (by
      rw [hcRho_ord F K ht piK hgen]
      exact WithTop.coe_ne_top)

@[simp] private theorem hcRhoUnit_coe :
    (hcRhoUnit F K ht piK hgen : K) = hcRho F K piK := rfl

/-- The manuscript's exact lower uniformizer `N(rho)`. -/
private noncomputable def hcPiF : Fˣ :=
  normUnits F K (hcRhoUnit F K ht piK hgen)

@[simp] private theorem hcPiF_coe :
    (hcPiF F K ht piK hgen : F) = norm F K (hcRho F K piK) := rfl

include hres in
private theorem hcPiF_ord :
    ord F (hcPiF F K ht piK hgen : F) =
      ((1 : ℤ) : WithTop ℤ) := by
  rw [hcPiF_coe, ord_norm, hres, one_nsmul,
    hcRho_ord F K ht piK hgen]

/-- Exact lower admissible denominator `N(rho)^(m+n)`. -/
private noncomputable def hcGamma
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) :
    AdmissibleGamma F chi psi :=
  ⟨hcPiF F K ht piK hgen ^ ((chi.conductor : ℤ) + psi.conductor), by
    rw [Units.val_zpow_eq_zpow_val,
      ord_uniformizer_zpow F
        ((ord_eq_one_iff_isUniformizer F _).1
          (hcPiF_ord F K ht hres piK hgen))]⟩

private noncomputable def hcRepresentative
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi) :
    StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property := by
  let hex := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ (d : ℤ) by omega)
    (stationaryCoefficientClass F chi psi h (Gamma : Fˣ) Gamma.property)
  let c := Classical.choose hex
  have hc := Classical.choose_spec hex
  exact StationaryClassRepresentative.ofCoefficientRepresentative c hc

private noncomputable def hcResidueEquiv :
    ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K, hres]
    have hdim : Module.finrank (ResidueField F) (ResidueField F) =
        Module.finrank (ResidueField F) (ResidueField K) := by simp [hfin]
    have hinj : Function.Injective
        (Algebra.linearMap (ResidueField F) (ResidueField K)) :=
      (algebraMap (ResidueField F) (ResidueField K)).injective
    have hsurj :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by simpa only [Algebra.linearMap_apply] using hx⟩

@[simp] private theorem hcResidueEquiv_apply (x : ResidueField F) :
    hcResidueEquiv F K hres x = extensionResidueMap F K x := rfl

private noncomputable def hcDeltaEven (d : ℕ) : Kˣ :=
  hcRhoUnit F K ht piK hgen ^ (2 * d - 1)

include ht hgen in
private theorem hcDeltaEven_order (d : ℕ) :
    ord K (hcDeltaEven F K ht piK hgen d : K) =
      (((2 * d - 1 : ℕ) : ℤ) : WithTop ℤ) := by
  rw [hcDeltaEven, Units.val_pow_eq_pow_val, ord_pow,
    hcRhoUnit_coe, hcRho_ord F K ht piK hgen]
  simp

/-- Exact conductor-one denominator `N(rho)^(n+1)`. -/
private noncomputable def hcGammaNorm (psi : LocalAddCharData F) : Fˣ :=
  hcPiF F K ht piK hgen ^ (psi.conductor + 1)

include hres in
private theorem hcGammaNorm_order (psi : LocalAddCharData F) :
    ord F (hcGammaNorm F K ht piK hgen psi : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ) := by
  rw [hcGammaNorm, Units.val_zpow_eq_zpow_val,
    ord_uniformizer_zpow F
      ((ord_eq_one_iff_isUniformizer F _).1
        (hcPiF_ord F K ht hres piK hgen))]

private noncomputable def hcPsi0 (psi : LocalAddCharData F) :
    FiniteAddChar (ResidueField F) :=
  residualAddChar F psi (hcGammaNorm F K ht piK hgen psi)
    (hcGammaNorm_order F K ht hres piK hgen psi)

private theorem hcPsi0_ne_one (psi : LocalAddCharData F) :
    hcPsi0 F K ht hres piK hgen psi ≠ 1 := by
  exact residualAddChar_ne_one F psi (hcGammaNorm F K ht piK hgen psi)
    (hcGammaNorm_order F K ht hres piK hgen psi)

private theorem hcResidualAdditive (psi : LocalAddCharData F) :
    residualAddChar F psi (hcGammaNorm F K ht piK hgen psi)
        (hcGammaNorm_order F K ht hres piK hgen psi) =
      hcPsi0 F K ht hres piK hgen psi :=
  rfl

/-- The nontrivial norm character with its proved actual conductor one. -/
private noncomputable def hcNormData
    (tau : NormCharacter F K) (htau : tau ≠ 1) : LocalQuasiCharData F where
  character := tau.1
  conductor := 1
  isConductor :=
    tameNormCharacter_conductor F K ht hres piK hpiK hgen tau htau

@[simp] private theorem hcNormData_character
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    (hcNormData F K ht hres piK hpiK hgen tau htau).character = tau.1 :=
  rfl

@[simp] private theorem hcNormData_conductor
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    (hcNormData F K ht hres piK hpiK hgen tau htau).conductor = 1 :=
  rfl

private theorem hcFiniteMulChar_eq_finiteQuadraticChar
    {k : Type*} [Field k] [Fintype k]
    (hchar : ringChar k ≠ 2)
    (chi : FiniteMulChar k) (hchi : chi ≠ 1) (hsq : chi ^ 2 = 1) :
    chi = finiteQuadraticChar k := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  apply (MulChar.eq_iff hg chi (finiteQuadraticChar k)).2
  have hchiSq : chi (g : k) ^ 2 = 1 := by
    have h := congrArg (fun eta : FiniteMulChar k ↦ eta (g : k)) hsq
    rw [chi.pow_apply' two_ne_zero, MulChar.one_apply g.isUnit] at h
    exact h
  have hchiNe : chi (g : k) ≠ 1 := by
    intro h
    apply hchi
    exact (MulChar.eq_iff hg chi 1).2 (by simpa using h)
  have hnuSq : finiteQuadraticChar k (g : k) ^ 2 = 1 :=
    finiteQuadraticChar_sq k (Units.ne_zero g)
  have hnuNe : finiteQuadraticChar k (g : k) ≠ 1 := by
    intro h
    apply finiteQuadraticChar_ne_one k hchar
    exact (MulChar.eq_iff hg (finiteQuadraticChar k) 1).2 (by simpa using h)
  rcases sq_eq_one_iff.mp hchiSq with hchiOne | hchiNeg
  · exact (hchiNe hchiOne).elim
  · rcases sq_eq_one_iff.mp hnuSq with hnuOne | hnuNeg
    · exact (hnuNe hnuOne).elim
    · exact hchiNeg.trans hnuNeg.symm

include ht hres hpiK hgen hdegree in
/-- The residual character of the actual nontrivial norm datum is exactly
the normalized quadratic character. -/
private theorem hcNormData_residual
    (hchar : residueCharacteristic F ≠ 2)
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    residualMulChar F (hcNormData F K ht hres piK hpiK hgen tau htau) =
      finiteQuadraticChar (ResidueField F) := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  have htauSq : tau ^ 2 = 1 := by
    have hpow := pow_card_eq_one' (x := tau)
    rw [ramifiedNormCharacter_card F K ht hres piK hpiK hgen,
      hdegree] at hpow
    exact hpow
  have hresSq :
      (residualMulChar F
        (hcNormData F K ht hres piK hpiK hgen tau htau)) ^ 2 = 1 := by
    ext xu
    rw [(residualMulChar F
      (hcNormData F K ht hres piK hpiK hgen tau htau)).pow_apply'
        two_ne_zero,
      residualMulChar_apply_unit]
    have hpoint := congrArg
      (fun mu : NormCharacter F K ↦ mu.1 (teichmullerLocalUnits F xu))
        htauSq
    rw [NormCharacter.coe_pow, ContinuousQuasiChar.pow_apply,
      NormCharacter.coe_one, ContinuousQuasiChar.one_apply] at hpoint
    rw [hcNormData_character, MulChar.one_apply xu.isUnit]
    have hpoint' := congrArg Units.val hpoint
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hpoint'
  exact hcFiniteMulChar_eq_finiteQuadraticChar hchar
    (residualMulChar F
      (hcNormData F K ht hres piK hpiK hgen tau htau))
    (residualMulChar_ne_one F
      (hcNormData F K ht hres piK hpiK hgen tau htau) rfl) hresSq

/-- A norm character is one on the exact norm-power residual denominator. -/
private theorem hcNormData_gammaNorm_value
    (psi : LocalAddCharData F)
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    ((hcNormData F K ht hres piK hpiK hgen tau htau).character
      (hcGammaNorm F K ht piK hgen psi) : ℂˣ) = 1 := by
  rw [hcNormData_character]
  apply tau.eq_one_on_normRange F K
  refine ⟨hcRhoUnit F K ht piK hgen ^ (psi.conductor + 1), ?_⟩
  change normUnits F K
      (hcRhoUnit F K ht piK hgen ^ (psi.conductor + 1)) =
    hcGammaNorm F K ht piK hgen psi
  rw [map_zpow]
  rfl

private def hcStationaryLocalUnit
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property) : unitGroup F :=
  ⟨R.unit, (mem_unitFiltration_zero F R.unit).2 (by
    change ord F (R.representative : F) = 0
    have hord := stationaryNumeratorClass_representative_ord F chi psi
      (chi.conductor : ℤ) (stationaryDepthOfConductorDecomposition F chi h)
      (Gamma : Fˣ) Gamma.property R.toLamprecht R.toLamprecht_represents
    simpa only [StationaryClassRepresentative.toLamprecht, sub_self,
      WithTop.coe_zero] using hord)⟩

private noncomputable def hcBeta
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property) : ResidueField F :=
  (residueUnits F (hcStationaryLocalUnit F chi psi h Gamma R) :
    (ResidueField F)ˣ)

private theorem hcBeta_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property) :
    hcBeta F chi psi h Gamma R ≠ 0 :=
  Units.ne_zero _

include hdegree in
private theorem hcSigma_deltaEven
    (d : ℕ) (hd : 0 < d) :
    hcSigma F K (hcDeltaEven F K ht piK hgen d : K) =
      -(hcDeltaEven F K ht piK hgen d : K) := by
  simp only [hcDeltaEven, Units.val_pow_eq_pow_val, hcRhoUnit_coe, map_pow]
  rw [hcSigma_rho F K piK hdegree]
  have hodd : Odd (2 * d - 1) := ⟨d - 1, by omega⟩
  exact hodd.neg_pow _

include hdegree in
private theorem hcTrace_deltaEven_mul_map
    (d : ℕ) (hd : 0 < d) (z : F) :
    trace F K
      ((hcDeltaEven F K ht piK hgen d : K) * algebraMap F K z) = 0 := by
  apply (algebraMap F K).injective
  rw [trace_eq_sum_automorphisms, hcGal_univ F K hdegree]
  have hnotmem : (1 : Gal(K/F)) ∉
      (singleton (hcSigma F K) : Finset Gal(K/F)) := by
    simpa [hcSigma] using
      (Ne.symm (PrimeCyclicExtension.generator_ne_one F K))
  rw [Finset.sum_insert hnotmem, Finset.sum_singleton]
  simp only [AlgEquiv.one_apply, map_mul]
  rw [hcSigma_deltaEven F K ht piK hgen hdegree d hd]
  rw [(hcSigma F K).commutes]
  simp

include hdegree in
private theorem hcNorm_deltaEven_mul_map
    (d : ℕ) (z : F) :
    norm F K
      ((hcDeltaEven F K ht piK hgen d : K) * algebraMap F K z) =
      (hcPiF F K ht piK hgen : F) ^ (2 * d - 1) * z ^ 2 := by
  simp only [hcDeltaEven, Units.val_pow_eq_pow_val, hcRhoUnit_coe]
  rw [map_mul, map_pow, norm_algebraMap, hdegree]
  rfl

include hdegree in
private theorem hcNorm_one_add_deltaEven_mul_map
    (d : ℕ) (hd : 0 < d) (z : F) :
    norm F K
      (1 + (hcDeltaEven F K ht piK hgen d : K) * algebraMap F K z) =
      1 + (hcPiF F K ht piK hgen : F) ^ (2 * d - 1) * z ^ 2 := by
  have hexact := wildQuadratic_normPolynomialValue_eq_trace_add_norm
    F K hdegree
      ((hcDeltaEven F K ht piK hgen d : K) * algebraMap F K z)
  rw [normPolynomialValue,
    hcTrace_deltaEven_mul_map F K ht piK hgen hdegree d hd z,
    hcNorm_deltaEven_mul_map F K ht piK hgen hdegree d z] at hexact
  rw [sub_eq_iff_eq_add] at hexact
  simpa [add_comm, add_left_comm] using hexact

include hdegree in
private theorem hcRho_norm_map :
    algebraMap F K (norm F K (hcRho F K piK)) =
      -(hcRho F K piK) ^ 2 := by
  have hsigNe' : (1 : Gal(K/F)) ≠ hcSigma F K :=
    Ne.symm (PrimeCyclicExtension.generator_ne_one F K)
  have hnotmem : (1 : Gal(K/F)) ∉
      (singleton (hcSigma F K) : Finset Gal(K/F)) := by
    simpa using hsigNe'
  rw [Algebra.norm_eq_prod_automorphisms F, hcGal_univ F K hdegree]
  rw [Finset.prod_insert hnotmem, Finset.prod_singleton]
  simp only [AlgEquiv.one_apply]
  rw [hcSigma_rho F K piK hdegree]
  ring
include hdegree in
private theorem hcPiF_map :
    algebraMap F K (hcPiF F K ht piK hgen : F) =
      -(hcRhoUnit F K ht piK hgen : K) ^ 2 := by
  rw [hcPiF_coe, hcRhoUnit_coe]
  exact hcRho_norm_map F K piK hdegree
private theorem hcBeta_eq_reduce
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property) :
    hcBeta F chi psi h Gamma R =
      reduce F (R.representative : F) (by
        simpa only [sub_self] using R.representative.property) := by
  unfold hcBeta
  rw [residueUnits_coe]
  rfl

private def hcMinusOneUnit (E : Type*) [Field E] : Eˣ :=
  Units.mk0 (-1 : E) (neg_ne_zero.mpr one_ne_zero)

@[simp] private theorem hcMinusOneUnit_coe
    (E : Type*) [Field E] : (hcMinusOneUnit E : E) = -1 := rfl

include hdegree in
private theorem hcPiF_map_unit :
    Units.map (algebraMap F K).toMonoidHom
        (hcPiF F K ht piK hgen) =
      hcMinusOneUnit K * (hcRhoUnit F K ht piK hgen) ^ 2 := by
  apply Units.ext
  simp only [Units.coe_map, Units.val_mul, Units.val_pow_eq_pow_val,
    hcMinusOneUnit_coe, hcRhoUnit_coe]
  rw [neg_one_mul]
  exact hcPiF_map F K ht piK hgen hdegree

include hdegree in
private theorem hcRho_evenPower
    (d : ℕ) :
    hcRhoUnit F K ht piK hgen ^ (2 * d) =
      Units.map (algebraMap F K).toMonoidHom
        ((hcMinusOneUnit F) ^ d *
          hcPiF F K ht piK hgen ^ d) := by
  simp only [map_mul, map_pow]
  rw [hcPiF_map_unit F K ht piK hgen hdegree]
  have hminusMap : Units.map (algebraMap F K).toMonoidHom
      (hcMinusOneUnit F) = hcMinusOneUnit K := by
    apply Units.ext
    simp
  rw [hminusMap, mul_pow]
  have hminusSq : hcMinusOneUnit K ^ 2 = 1 := by
    apply Units.ext
    norm_num
  calc
    hcRhoUnit F K ht piK hgen ^ (2 * d) =
        (hcMinusOneUnit K ^ 2) ^ d *
          hcRhoUnit F K ht piK hgen ^ (2 * d) := by
            rw [hminusSq, one_pow, one_mul]
    _ = hcMinusOneUnit K ^ d *
        (hcMinusOneUnit K ^ d *
          (hcRhoUnit F K ht piK hgen ^ 2) ^ d) := by group

end HigherIntrinsicCommon

/-! ## Higher conductors: quotient transport and residual phases -/

section HigherComparison

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField K) := residueFieldFintype K

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (hdegree : Module.finrank F K = 2)
  (hchar : residueCharacteristic F ≠ 2)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

/-- Map the supplied downstairs quotient representative through the exact
denominator pair in `HighTameQuadraticParameterData`.  The existential depth
proves an equality of quotient classes; it never chooses a representative. -/
def tameQuadraticUpstairsRepresentative
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF) :
    StationaryClassRepresentative K chiK psiK H.sourceDecomposition
      (Units.map (algebraMap F K) gammaF) H.commonDenominator := by
  let cK : lattice K 0 :=
    ⟨algebraMap F K (R.representative : F), by
      rw [mem_lattice, ord_algebraMap]
      have hc := R.representative.property
      rw [mem_lattice] at hc
      simpa using nsmul_le_nsmul_right hc (ramificationIndex F K)⟩
  refine StationaryClassRepresentative.ofCoefficientRepresentative cK ?_
  rcases H.stationaryClass with ⟨hdepth, hclass⟩
  calc
    latticeQuotientMk K (Int.natCast_nonneg (chiF.conductor - 1)) cK =
        denominatorScaledAlgebraMap F K d (chiF.conductor - 1) hdepth gammaF
          (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (latticeQuotientMk F (Int.natCast_nonneg d) R.representative) := by
            rw [denominatorScaledAlgebraMap_common_mk]
    _ = denominatorScaledAlgebraMap F K d (chiF.conductor - 1) hdepth gammaF
          (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
            rw [R.represents]
    _ = stationaryCoefficientClass K chiK psiK H.sourceDecomposition
          (Units.map (algebraMap F K) gammaF) H.commonDenominator :=
      hclass.symm

/-- The actual upstairs odd phase, at depth `m_F-1`, with the same mapped
denominator and the literally mapped stationary representative. -/
def tameQuadraticUpstairsOddPhase
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ)) :
    RamifiedHasseOddStationaryPhase K chiK psiK where
  d := chiF.conductor - 1
  decomposition := H.sourceDecomposition
  denominator := ⟨Units.map (algebraMap F K) gammaF, H.commonDenominator⟩
  representative := tameQuadraticUpstairsRepresentative F K ht hres piK hpiK
    hgen chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF H R
  delta := deltaK
  delta_order := hdeltaK

private theorem hcUpperPointwise_even
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (d : ℕ)
    (hFeven : IsStationaryConductorDecomposition chiF.conductor d 0) :
    let GammaF := hcGamma F K ht hres piK hgen chiF psiF
    let H := highConductorParameter_tameQuadratic
      F K ht hres piK hpiK hgen chiF chiK psiF psiK hFeven hchi hpsi
        hdegree rfl hchar (GammaF : Fˣ) GammaF.property
    let R := hcRepresentative F K chiF psiF hFeven GammaF
    let deltaK := hcDeltaEven F K ht piK hgen d
    let hdeltaK : ord K (deltaK : K) =
        (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ) := by
      simpa [hFeven.conductor_eq] using
        (hcDeltaEven_order F K ht piK hgen d)
    let psi0 := hcPsi0 F K ht hres piK hgen psiF
    let beta := hcBeta F chiF psiF hFeven GammaF R
    ∀ x : ResidueField F,
      (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar
          (GammaF : Fˣ) GammaF.property H R deltaK hdeltaK).function
          (hcResidueEquiv F K hres x) =
        psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x) := by
  dsimp only
  intro x
  have hd : 0 < d := by
    have hlarge := hFeven.conductor_gt_one
    rw [hFeven.conductor_eq] at hlarge
    omega
  let a : ringOfIntegers F := teichmuller F x
  have haF : (a : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 a.property
  let aK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) a
  have haKcoe : (aK : K) = algebraMap F K (a : F) :=
    Valuation.HasExtension.val_algebraMap a
  have haK : algebraMap F K (a : F) ∈ lattice K 0 := by
    rw [← haKcoe]
    exact (mem_lattice_zero_iff K).2 aK.property
  have hreduceF : reduce F (a : F) haF = x := by
    simp [a, reduce]
  have hreduceK : reduce K (algebraMap F K (a : F)) haK =
      hcResidueEquiv F K hres x := by
    change residueMap K aK = extensionResidueMap F K x
    rw [← hreduceF]
    change residueMap K aK = extensionResidueMap F K (residueMap F a)
    rfl
  let GammaF := hcGamma F K ht hres piK hgen chiF psiF
  let H := highConductorParameter_tameQuadratic
    F K ht hres piK hpiK hgen chiF chiK psiF psiK hFeven hchi hpsi
      hdegree rfl hchar (GammaF : Fˣ) GammaF.property
  let R := hcRepresentative F K chiF psiF hFeven GammaF
  let deltaK := hcDeltaEven F K ht piK hgen d
  let hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ) := by
    simpa [hFeven.conductor_eq] using
      (hcDeltaEven_order F K ht piK hgen d)
  let V := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar
      (GammaF : Fˣ) GammaF.property H R deltaK hdeltaK
  let psi0 := hcPsi0 F K ht hres piK hgen psiF
  let beta := hcBeta F chiF psiF hFeven GammaF R
  change V.function (hcResidueEquiv F K hres x) =
    psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x)
  rw [← hreduceK]
  have hlift := lamprechtHasseFunction_integral_lift K chiK psiK
    V.d V.conductor_eq V.conductor_large V.denominator V.delta V.delta_order
      V.representative.toLamprecht (by
        simpa only [stationaryDepthOfConductorDecomposition] using
          V.representative.toLamprecht_represents)
      (algebraMap F K (a : F)) haK
  change V.function (reduce K (algebraMap F K (a : F)) haK) =
      lamprechtHasseValue K chiK psiK V.d V.conductor_eq V.conductor_large
        V.denominator V.delta V.delta_order V.representative.toLamprecht
          (algebraMap F K (a : F)) haK at hlift
  rw [hlift]
  unfold lamprechtHasseValue
  have hVrep : (V.representative.toLamprecht : K) =
      algebraMap F K (R.representative : F) := rfl
  have hVdelta : (V.delta : K) = (deltaK : K) := rfl
  have hVdenominator : ((V.denominator : Kˣ) : K) =
      algebraMap F K ((GammaF : Fˣ) : F) := rfl
  have haddArg :
      (V.representative.toLamprecht : K) * (V.delta : K) *
          algebraMap F K (a : F) /
            ((V.denominator : Kˣ) : K) =
        (deltaK : K) * algebraMap F K
          ((R.representative : F) * (a : F) /
            ((GammaF : Fˣ) : F)) := by
    rw [hVrep, hVdelta, hVdenominator]
    simp only [map_div₀, map_mul]
    ring
  have haddTrace : trace F K
      ((V.representative.toLamprecht : K) * (V.delta : K) *
        algebraMap F K (a : F) /
          ((V.denominator : Kˣ) : K)) = 0 := by
    rw [haddArg]
    exact hcTrace_deltaEven_mul_map F K ht piK hgen hdegree d hd
      ((R.representative : F) * (a : F) / ((GammaF : Fˣ) : F))
  have haddValue :
      (psiK.character
        ((V.representative.toLamprecht : K) * (V.delta : K) *
          algebraMap F K (a : F) /
            ((V.denominator : Kˣ) : K)) : ℂ) = 1 := by
    rw [hpsi, ContinuousAddChar.compTrace_apply, haddTrace]
    exact congrArg Units.val
      (AddChar.map_zero_eq_one psiF.character.toAddChar)
  rw [haddValue, one_mul]
  let yval : F :=
    (hcPiF F K ht piK hgen : F) ^ (2 * d - 1) * (a : F) ^ 2
  have hpiPow : (hcPiF F K ht piK hgen : F) ^ (2 * d - 1) ∈
      lattice F (((2 * d - 1 : ℕ) : ℤ)) := by
    rw [mem_lattice, ord_pow, hcPiF_ord F K ht hres piK hgen]
    norm_cast
    simp
  have haSq : (a : F) ^ 2 ∈ lattice F 0 := by
    simpa only [pow_two, add_zero] using mul_mem_lattice F haF haF
  have hyDeep : yval ∈ lattice F (((2 * d - 1 : ℕ) : ℤ)) := by
    dsimp only [yval]
    simpa only [add_zero] using mul_mem_lattice F hpiPow haSq
  have hyMem : yval ∈ lattice F (d : ℤ) := by
    exact lattice_antitone F
      (show (d : ℤ) ≤ (((2 * d - 1 : ℕ) : ℤ)) by omega) hyDeep
  let y : lattice F (d : ℤ) := ⟨yval, hyMem⟩
  have hlinear :=
    (latticeQuotientMk_eq_stationaryCoefficientClass_iff F chiF psiF
      hFeven (GammaF : Fˣ) GammaF.property R.representative).1
        R.represents y
  let uK := lamprechtHasseUnit K chiK V.d V.conductor_eq
    V.conductor_large V.delta V.delta_order (algebraMap F K (a : F)) haK
  have hnormUnit : Units.map (Algebra.norm F) (uK : Kˣ) =
      (positiveUnitOfLattice F hFeven.variableDepth_pos y : Fˣ) := by
    apply Units.ext
    simp only [uK, Units.coe_map, coe_positiveUnitOfLattice]
    rw [lamprechtHasseUnit_coe, hVdelta]
    change norm F K
      (1 + (deltaK : K) * algebraMap F K (a : F)) = 1 + yval
    rw [hcNorm_one_add_deltaEven_mul_map F K ht piK hgen hdegree d hd]
  have hchiValue :
      (chiK.character (uK : Kˣ) : ℂ) =
        (psiF.character
          ((R.representative : F) * (y : F) / ((GammaF : Fˣ) : F)) :
            ℂ) := by
    rw [hchi, ContinuousQuasiChar.compNorm_apply, hnormUnit, hlinear]
  change ((chiK.character (uK : Kˣ) : ℂ))⁻¹ =
    psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x)
  rw [hchiValue]
  let gamma0 := hcGammaNorm F K ht piK hgen psiF
  let hgamma0 := hcGammaNorm_order F K ht hres piK hgen psiF
  have hRmem : (R.representative : F) ∈ lattice F 0 :=
    R.representative.property
  let wval : F := -(R.representative : F) * (a : F) ^ 2
  have hwMem : wval ∈ lattice F 0 := by
    dsimp only [wval]
    exact mul_mem_lattice F (neg_mem hRmem) haSq
  have hbetaReduce :
      beta = reduce F (R.representative : F) hRmem := by
    dsimp only [beta]
    unfold hcBeta
    rw [residueUnits_coe]
    apply congrArg (residueMap F)
    apply Subtype.ext
    rfl
  have hwReduce : reduce F wval hwMem = -beta * x ^ 2 := by
    rw [hbetaReduce, ← hreduceF]
    let rint : ringOfIntegers F :=
      ⟨(R.representative : F), (mem_lattice_zero_iff F).1 hRmem⟩
    change residueMap F (-rint * a ^ 2) =
      -residueMap F rint * residueMap F a ^ 2
    simp only [map_mul, map_neg, map_pow]
  have hresValue := residualAddChar_integral_lift F psiF gamma0 hgamma0
    wval hwMem
  change psi0 (reduce F wval hwMem) =
      (psiF.character (wval / (gamma0 : F)) : ℂ) at hresValue
  have hpowRatio :
      hcPiF F K ht piK hgen ^ (2 * d - 1) / (GammaF : Fˣ) =
        gamma0⁻¹ := by
    have hqCast : (((2 * d - 1 : ℕ) : ℤ)) = 2 * (d : ℤ) - 1 := by
      omega
    dsimp only [GammaF, gamma0, hcGamma, hcGammaNorm]
    rw [hFeven.conductor_eq, ← zpow_natCast, hqCast]
    rw [div_eq_mul_inv, ← zpow_neg, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  have hpowRatioVal := congrArg Units.val hpowRatio
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val] at hpowRatioVal
  have harg :
      -((R.representative : F) * (y : F) / ((GammaF : Fˣ) : F)) =
        wval / (gamma0 : F) := by
    dsimp only [y, yval, wval]
    rw [div_eq_mul_inv] at hpowRatioVal
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      -((R.representative : F) *
          ((hcPiF F K ht piK hgen : F) ^ (2 * d - 1) * (a : F) ^ 2) *
            (((GammaF : Fˣ) : F))⁻¹) =
          (-(R.representative : F) * (a : F) ^ 2) *
            ((hcPiF F K ht piK hgen : F) ^ (2 * d - 1) *
              (((GammaF : Fˣ) : F))⁻¹) := by ring
      _ = (-(R.representative : F) * (a : F) ^ 2) *
            ((gamma0 : F))⁻¹ := by rw [hpowRatioVal]
  have hneg := AddChar.map_neg_eq_inv psiF.character.toAddChar
    ((R.representative : F) * (y : F) / ((GammaF : Fˣ) : F))
  have hnegC :
    (psiF.character
      (-((R.representative : F) * (y : F) / ((GammaF : Fˣ) : F))) : ℂ) =
      ((psiF.character
        ((R.representative : F) * (y : F) / ((GammaF : Fˣ) : F)) : ℂ))⁻¹ := by
    simpa only [ContinuousAddChar.toAddChar_apply,
      Units.val_inv_eq_inv_val] using congrArg Units.val hneg
  have htwo : (2 : ResidueField F) ≠ 0 := Ring.two_ne_zero hchar
  have hpoly : ((-2 * beta) / 2) * x ^ 2 + 0 * x = -beta * x ^ 2 := by
    field_simp [htwo]
    ring
  calc
    ((psiF.character
      ((R.representative : F) * (y : F) / ((GammaF : Fˣ) : F)) : ℂ))⁻¹ =
        (psiF.character
          (-((R.representative : F) * (y : F) /
            ((GammaF : Fˣ) : F))) : ℂ) := hnegC.symm
    _ = (psiF.character (wval / (gamma0 : F)) : ℂ) := by rw [harg]
    _ = psi0 (reduce F wval hwMem) := hresValue.symm
    _ = psi0 (-beta * x ^ 2) := by rw [hwReduce]
    _ = psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x) := by rw [hpoly]

/-- The even upper normal form is exactly `Q(-2*beta,0)`. -/
private theorem tameQuadratic_upperCritical_even
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ))
    (e : ResidueField F ≃+* ResidueField K)
    (psi0 : FiniteAddChar (ResidueField F)) (beta : ResidueField F)
    (hpoint : ∀ x : ResidueField F,
      (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF
          H R deltaK hdeltaK).function (e x) =
        psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x)) :
    (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK).localPhase.criticalFactor =
      quadraticPhase psi0 (-2 * beta) 0 := by
  let upper := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF
      H R deltaK hdeltaK
  rw [← upper.phase_eq_localCriticalFactor, upper.phase_eq_functionPhase]
  calc
    ramifiedHasseFunctionPhase
        (fun x : ResidueField K ↦ upper.function x) =
        ramifiedHasseFunctionPhase
          (fun x : ResidueField F ↦ upper.function (e x)) :=
      (ramifiedHasseFunctionPhase_equiv e.toEquiv
        (fun x : ResidueField K ↦ upper.function x)).symm
    _ = ramifiedHasseFunctionPhase
          (fun x : ResidueField F ↦
            psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x)) :=
      ramifiedHasseFunctionPhase_congr hpoint
    _ = quadraticPhase psi0 (-2 * beta) 0 := by
      unfold ramifiedHasseFunctionPhase quadraticPhase quadraticSum
      rfl

/-- The odd downstairs phase retains the translated term and is `Q(beta,c)`. -/
private theorem tameQuadratic_lowerCritical_odd
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (R : StationaryClassRepresentative F chiF psiF hFodd gammaF hgammaF)
    (deltaF : Fˣ) (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (beta c : ResidueField F)
    (hpoint : ∀ x : ResidueField F,
      (RamifiedHasseOddStationaryPhase.function
        ({ d := d
           decomposition := hFodd
           denominator := ⟨gammaF, hgammaF⟩
           representative := R
           delta := deltaF
           delta_order := hdeltaF } :
          RamifiedHasseOddStationaryPhase F chiF psiF)) x =
        psi0 ((beta / 2) * x ^ 2 + c * x)) :
    (LocalLamprechtPhaseData.oddOfStationaryClass
      d hFodd ⟨gammaF, hgammaF⟩ deltaF hdeltaF R).criticalFactor =
      quadraticPhase psi0 beta c := by
  let lower : RamifiedHasseOddStationaryPhase F chiF psiF :=
    { d := d
      decomposition := hFodd
      denominator := ⟨gammaF, hgammaF⟩
      representative := R
      delta := deltaF
      delta_order := hdeltaF }
  change lower.localPhase.criticalFactor = _
  rw [← lower.phase_eq_localCriticalFactor, lower.phase_eq_functionPhase]
  calc
    ramifiedHasseFunctionPhase (fun x : ResidueField F ↦ lower.function x) =
        ramifiedHasseFunctionPhase
          (fun x : ResidueField F ↦ psi0 ((beta / 2) * x ^ 2 + c * x)) :=
      ramifiedHasseFunctionPhase_congr hpoint
    _ = quadraticPhase psi0 beta c := by
      unfold ramifiedHasseFunctionPhase quadraticPhase quadraticSum
      rfl

/-- The odd upstairs phase is `Q(2*beta,2*s*c)`; the translation sign `s`
is not separated from its elementary stationary value. -/
private theorem tameQuadratic_upperCritical_odd
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ))
    (e : ResidueField F ≃+* ResidueField K)
    (psi0 : FiniteAddChar (ResidueField F))
    (beta c s : ResidueField F)
    (hpoint : ∀ x : ResidueField F,
      (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF
          H R deltaK hdeltaK).function (e x) =
        psi0 (((2 * beta) / 2) * x ^ 2 + (2 * s * c) * x)) :
    (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK).localPhase.criticalFactor =
      quadraticPhase psi0 (2 * beta) (2 * s * c) := by
  let upper := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hF hchi hpsi hdegree hchar gammaF hgammaF
      H R deltaK hdeltaK
  rw [← upper.phase_eq_localCriticalFactor, upper.phase_eq_functionPhase]
  calc
    ramifiedHasseFunctionPhase
        (fun x : ResidueField K ↦ upper.function x) =
        ramifiedHasseFunctionPhase
          (fun x : ResidueField F ↦ upper.function (e x)) :=
      (ramifiedHasseFunctionPhase_equiv e.toEquiv
        (fun x : ResidueField K ↦ upper.function x)).symm
    _ = ramifiedHasseFunctionPhase
          (fun x : ResidueField F ↦
            psi0 (((2 * beta) / 2) * x ^ 2 + (2 * s * c) * x)) :=
      ramifiedHasseFunctionPhase_congr hpoint
    _ = quadraticPhase psi0 (2 * beta) (2 * s * c) := by
      unfold ramifiedHasseFunctionPhase quadraticPhase quadraticSum
      rfl

/-! ### Mapped elementary factor and exact stable twist -/

/-- In the even downstairs branch the complete nonresidual upper factor is
the square of the lower one, for the same literal quotient representative. -/
private theorem tameQuadratic_mappedBaseFactor_even
    (hFeven : IsStationaryConductorDecomposition chiF.conductor d 0)
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hFeven gammaF hgammaF)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ)) :
    let lower := LocalLamprechtPhaseData.evenOfStationaryClass
      d hFeven ⟨gammaF, hgammaF⟩ R
    let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK).localPhase
    upper.admissibleFactor * upper.elementaryFactor =
      (lower.admissibleFactor * lower.elementaryFactor) ^ 2 := by
  dsimp only
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF, H.commonDenominator⟩
  let RK := tameQuadraticUpstairsRepresentative F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar gammaF hgammaF H R
  have hbeta : RK.unit =
      Units.map (algebraMap F K).toMonoidHom R.unit := by
    ext
    rfl
  change
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor K chiK psiK GammaK RK.unit =
      ((((chiF.character (GammaF : Fˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor F chiF psiF GammaF R.unit) ^ 2
  exact lamprechtBaseFactor_tameQuadratic F K chiF psiF chiK psiK hchi hpsi
    hdegree GammaF GammaK rfl R.unit RK.unit hbeta

/-- The odd downstairs branch has the same squared nonresidual factor; its
translated critical phase stays outside this equality. -/
private theorem tameQuadratic_mappedBaseFactor_odd
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hFodd gammaF hgammaF)
    (deltaF : Fˣ) (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ)) :
    let lower := LocalLamprechtPhaseData.oddOfStationaryClass
      d hFodd ⟨gammaF, hgammaF⟩ deltaF hdeltaF R
    let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK).localPhase
    upper.admissibleFactor * upper.elementaryFactor =
      (lower.admissibleFactor * lower.elementaryFactor) ^ 2 := by
  dsimp only
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF, H.commonDenominator⟩
  let RK := tameQuadraticUpstairsRepresentative F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF H R
  have hbeta : RK.unit =
      Units.map (algebraMap F K).toMonoidHom R.unit := by
    ext
    rfl
  change
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor K chiK psiK GammaK RK.unit =
      ((((chiF.character (GammaF : Fˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor F chiF psiF GammaF R.unit) ^ 2
  exact lamprechtBaseFactor_tameQuadratic F K chiF psiF chiK psiK hchi hpsi
    hdegree GammaF GammaK rfl R.unit RK.unit hbeta

/-- The stationary unit supplied to `stableTwist`; the underlying field
element is exactly the representative already stored in `R`. -/
def tameQuadraticStableBeta
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ)
    (h : IsStationaryConductorDecomposition theta.conductor d epsilon)
    (Gamma : AdmissibleGamma F theta psi)
    (R : StationaryClassRepresentative F theta psi h
      (Gamma : Fˣ) Gamma.property) : Fˣ :=
  stableStationaryRepresentativeUnit F theta psi
    (stableTwist_stationaryDepth F theta d epsilon h.epsilon_le_one
      (by simpa using h.conductor_eq) h.conductor_gt_one)
    Gamma R.toLamprecht (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R.toLamprecht_represents)

private theorem hcStableBeta_eq_unit
    (nu chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property) :
    tameQuadraticStableBeta F nu chi psi d epsilon h Gamma R = R.unit := by
  apply Units.ext
  simp only [tameQuadraticStableBeta,
    stableStationaryRepresentativeUnit_coe,
    StationaryClassRepresentative.coe_unit,
    StationaryClassRepresentative.toLamprecht]

/-- The exact stable-twist value in the manuscript's direction
`tau(Gamma / beta)`.  Inversion does not change the normalized quadratic
residue value. -/
private theorem hcNormData_stableValue
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (R : StationaryClassRepresentative F chi psi h
      (hcGamma F K ht hres piK hgen chi psi : Fˣ)
      (hcGamma F K ht hres piK hgen chi psi).property) :
    (((hcNormData F K ht hres piK hpiK hgen tau htau).character
      ((hcGamma F K ht hres piK hgen chi psi : Fˣ) /
        tameQuadraticStableBeta F
          (hcNormData F K ht hres piK hpiK hgen tau htau)
          chi psi d epsilon h (hcGamma F K ht hres piK hgen chi psi) R) :
        ℂˣ) : ℂ) =
      finiteQuadraticChar (ResidueField F)
        (hcBeta F chi psi h (hcGamma F K ht hres piK hgen chi psi) R) := by
  let normData := hcNormData F K ht hres piK hpiK hgen tau htau
  let Gamma := hcGamma F K ht hres piK hgen chi psi
  let u := hcStationaryLocalUnit F chi psi h Gamma R
  let beta := hcBeta F chi psi h Gamma R
  have hGamma : normData.character (Gamma : Fˣ) = 1 := by
    change tau.1
      (hcPiF F K ht piK hgen ^ ((chi.conductor : ℤ) + psi.conductor)) = 1
    apply tau.eq_one_on_normRange F K
    refine ⟨hcRhoUnit F K ht piK hgen ^
      ((chi.conductor : ℤ) + psi.conductor), ?_⟩
    change normUnits F K
        (hcRhoUnit F K ht piK hgen ^
          ((chi.conductor : ℤ) + psi.conductor)) =
      hcPiF F K ht piK hgen ^ ((chi.conductor : ℤ) + psi.conductor)
    rw [map_zpow]
    rfl
  have hresChar := congrArg
    (fun eta : FiniteMulChar (ResidueField F) ↦ eta beta)
    (hcNormData_residual F K ht hres piK hpiK hgen hdegree hchar tau htau)
  have hunit :
      residualMulChar F normData beta =
        (normData.character (u : Fˣ) : ℂ) := by
    exact residualMulChar_residueUnits F normData (by simp [normData]) u
  have hbetaValue :
      ((normData.character (R.unit : Fˣ) : ℂˣ) : ℂ) =
        finiteQuadraticChar (ResidueField F) beta := by
    rw [← hresChar]
    simpa only [u, hcStationaryLocalUnit] using hunit.symm
  rw [hcStableBeta_eq_unit]
  rw [_root_.map_div, hGamma, one_div]
  rw [Units.val_inv_eq_inv_val]
  rw [hbetaValue]
  let q : ℂ := finiteQuadraticChar (ResidueField F) beta
  have hsq := finiteQuadraticChar_sq (ResidueField F)
    (hcBeta_ne_zero F chi psi h Gamma R)
  have hqne : q ≠ 0 := by
    exact IsUnit.ne_zero
      ((hcBeta_ne_zero F chi psi h Gamma R).isUnit.map
        (finiteQuadraticChar (ResidueField F)))
  have hinv : q⁻¹ = q := by
    rw [← one_div]
    apply (div_eq_iff hqne).2
    simpa [q, pow_two] using hsq.symm
  simpa only [q, beta, Gamma] using hinv

/-- Algebraic assembly of a higher quadratic pair.  In particular the
stable-twist factor occurs in the manuscript's direction `nu(Gamma/beta)`. -/
private theorem tameQuadratic_stablePair_of_exact_factors
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ)
    (h : IsStationaryConductorDecomposition theta.conductor d epsilon)
    (hnu : nu.conductor ≤ d)
    (Gamma : AdmissibleGamma F theta psi)
    (R : StationaryClassRepresentative F theta psi h
      (Gamma : Fˣ) Gamma.property)
    (lower : LocalLamprechtPhaseData F theta psi)
    (hlowerGamma : lower.gamma = Gamma)
    (upper : LocalLamprechtPhaseData K chiK psiK)
    (GammaNu : AdmissibleGamma F nu psi)
    (normPhase stableValue : ℂ)
    (hnorm : deltaFinite nu psi GammaNu = normPhase)
    (hstableValue :
      ((nu.character ((Gamma : Fˣ) /
        tameQuadraticStableBeta F nu theta psi d epsilon h Gamma R) : ℂˣ) :
          ℂ) = stableValue)
    (hbase :
      upper.admissibleFactor * upper.elementaryFactor =
        (lower.admissibleFactor * lower.elementaryFactor) ^ 2)
    (hcritical :
      upper.criticalFactor * normPhase =
        stableValue * lower.criticalFactor ^ 2) :
    let hcond : nu.conductor < theta.conductor := by
      have hlarge := h.conductor_gt_one
      rw [h.conductor_eq]
      rw [h.conductor_eq] at hlarge
      omega
    deltaFinite chiK psiK upper.gamma * deltaFinite nu psi GammaNu =
      deltaFinite theta psi Gamma *
        deltaFinite (stableTwistData F nu theta hcond) psi
          (stableTwistAdmissibleGamma F nu theta psi hcond Gamma) := by
  dsimp only
  have hR : latticeQuotientMk F
      (sub_le_sub_left
        (stableTwist_stationaryDepth F theta d epsilon h.epsilon_le_one
          (by simpa using h.conductor_eq) h.conductor_gt_one).int_le_conductor
        (theta.conductor : ℤ)) R.toLamprecht =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        (stableTwist_stationaryDepth F theta d epsilon h.epsilon_le_one
          (by simpa using h.conductor_eq) h.conductor_gt_one)
        Gamma Gamma.property := by
    simpa only [stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  have htwist := stableTwist F nu theta psi d epsilon h.epsilon_le_one
    (by simpa using h.conductor_eq) h.conductor_gt_one hnu Gamma
      R.toLamprecht hR
  dsimp only at htwist
  have hlower := lower.deltaFinite_eq_completeFactor
  rw [hlowerGamma] at hlower
  rw [upper.deltaFinite_eq_completeFactor, hnorm, htwist, hlower]
  unfold LocalLamprechtPhaseData.completeFactor
    LocalLamprechtPhaseData.stationaryFactor
  change
    (upper.admissibleFactor *
        (upper.elementaryFactor * upper.criticalFactor)) * normPhase =
      (lower.admissibleFactor *
          (lower.elementaryFactor * lower.criticalFactor)) *
        (((nu.character ((Gamma : Fˣ) /
          tameQuadraticStableBeta F nu theta psi d epsilon h Gamma R) : ℂˣ) :
            ℂ) *
          (lower.admissibleFactor *
            (lower.elementaryFactor * lower.criticalFactor)))
  rw [hstableValue]
  calc
    (upper.admissibleFactor *
        (upper.elementaryFactor * upper.criticalFactor)) * normPhase =
        (upper.admissibleFactor * upper.elementaryFactor) *
          (upper.criticalFactor * normPhase) := by ring
    _ = (lower.admissibleFactor * lower.elementaryFactor) ^ 2 *
          (stableValue * lower.criticalFactor ^ 2) := by
      rw [hbase, hcritical]
    _ = (lower.admissibleFactor *
          (lower.elementaryFactor * lower.criticalFactor)) *
        (stableValue *
          (lower.admissibleFactor *
            (lower.elementaryFactor * lower.criticalFactor))) := by ring

/-! ### Parity-separated higher pair -/

/-- Exact higher pair for `m=2d`.  The upper phase is `Q(-2*beta,0)` and
the nontrivial norm-character endpoint is `Q(2,0)`. -/
private theorem firstMain_tameQuadratic_higher_even
    (hFeven : IsStationaryConductorDecomposition chiF.conductor d 0)
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hFeven gammaF hgammaF)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ))
    (e : ResidueField F ≃+* ResidueField K)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : ResidueField F) (hbeta : beta ≠ 0)
    (hupperPoint : ∀ x : ResidueField F,
      (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar gammaF hgammaF
          H R deltaK hdeltaK).function (e x) =
        psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x))
    (nu : LocalQuasiCharData F) (hnu : nu.conductor ≤ d)
    (GammaNu : AdmissibleGamma F nu psiF)
    (hnorm : deltaFinite nu psiF GammaNu = quadraticPhase psi0 2 0)
    (hstableValue :
      ((nu.character (gammaF /
        tameQuadraticStableBeta F nu chiF psiF d 0 hFeven
          ⟨gammaF, hgammaF⟩ R) : ℂˣ) : ℂ) =
        finiteQuadraticChar (ResidueField F) beta) :
    let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
    let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK).localPhase
    let hcond : nu.conductor < chiF.conductor := by
      have hlarge := hFeven.conductor_gt_one
      rw [hFeven.conductor_eq]
      rw [hFeven.conductor_eq] at hlarge
      omega
    deltaFinite chiK psiK upper.gamma * deltaFinite nu psiF GammaNu =
      deltaFinite chiF psiF GammaF *
        deltaFinite (stableTwistData F nu chiF hcond) psiF
          (stableTwistAdmissibleGamma F nu chiF psiF hcond GammaF) := by
  dsimp only
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let lower := LocalLamprechtPhaseData.evenOfStationaryClass
    d hFeven GammaF R
  let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar gammaF hgammaF
      H R deltaK hdeltaK).localPhase
  have hupperCritical : upper.criticalFactor =
      quadraticPhase psi0 (-2 * beta) 0 :=
    tameQuadratic_upperCritical_even F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK e psi0 beta hupperPoint
  have hlowerCritical : lower.criticalFactor = 1 := by rfl
  have hquadratic := tameQuadratic_evenPhase_product hchar hpsi0 hbeta
  have hcritical : upper.criticalFactor * quadraticPhase psi0 2 0 =
      finiteQuadraticChar (ResidueField F) beta *
        lower.criticalFactor ^ 2 := by
    rw [hupperCritical, hquadratic, hlowerCritical]
    ring
  simpa only using
    (tameQuadratic_stablePair_of_exact_factors F K chiK psiK nu chiF psiF
      d 0 hFeven hnu GammaF R lower rfl upper GammaNu
      (quadraticPhase psi0 2 0)
      (finiteQuadraticChar (ResidueField F) beta) hnorm hstableValue
      (tameQuadratic_mappedBaseFactor_even F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hchi hpsi hdegree hchar gammaF hgammaF
          hFeven H R deltaK hdeltaK)
      hcritical)

/-- Exact higher pair for `m=2d+1`.  The linear term is transported as
`2*s*c`, so the elementary value and residual Hasse translation remain
together throughout the proof. -/
private theorem firstMain_tameQuadratic_higher_odd
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree rfl hchar gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hFodd gammaF hgammaF)
    (deltaF : Fˣ) (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ))
    (e : ResidueField F ≃+* ResidueField K)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta c s : ResidueField F) (hbeta : beta ≠ 0) (hs : s ^ 2 = 1)
    (hlowerPoint : ∀ x : ResidueField F,
      (RamifiedHasseOddStationaryPhase.function
        ({ d := d
           decomposition := hFodd
           denominator := ⟨gammaF, hgammaF⟩
           representative := R
           delta := deltaF
           delta_order := hdeltaF } :
          RamifiedHasseOddStationaryPhase F chiF psiF)) x =
        psi0 ((beta / 2) * x ^ 2 + c * x))
    (hupperPoint : ∀ x : ResidueField F,
      (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
          H R deltaK hdeltaK).function (e x) =
        psi0 (((2 * beta) / 2) * x ^ 2 + (2 * s * c) * x))
    (nu : LocalQuasiCharData F) (hnu : nu.conductor ≤ d)
    (GammaNu : AdmissibleGamma F nu psiF)
    (hnorm : deltaFinite nu psiF GammaNu = quadraticPhase psi0 2 0)
    (hstableValue :
      ((nu.character (gammaF /
        tameQuadraticStableBeta F nu chiF psiF d 1 hFodd
          ⟨gammaF, hgammaF⟩ R) : ℂˣ) : ℂ) =
        finiteQuadraticChar (ResidueField F) beta) :
    let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
    let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK).localPhase
    let hcond : nu.conductor < chiF.conductor := by
      have hlarge := hFodd.conductor_gt_one
      rw [hFodd.conductor_eq]
      rw [hFodd.conductor_eq] at hlarge
      omega
    deltaFinite chiK psiK upper.gamma * deltaFinite nu psiF GammaNu =
      deltaFinite chiF psiF GammaF *
        deltaFinite (stableTwistData F nu chiF hcond) psiF
          (stableTwistAdmissibleGamma F nu chiF psiF hcond GammaF) := by
  dsimp only
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let lower := LocalLamprechtPhaseData.oddOfStationaryClass
    d hFodd GammaF deltaF hdeltaF R
  let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
      H R deltaK hdeltaK).localPhase
  have hlowerCritical : lower.criticalFactor = quadraticPhase psi0 beta c :=
    tameQuadratic_lowerCritical_odd F chiF psiF gammaF hgammaF hFodd R
      deltaF hdeltaF psi0 beta c hlowerPoint
  have hupperCritical : upper.criticalFactor =
      quadraticPhase psi0 (2 * beta) (2 * s * c) :=
    tameQuadratic_upperCritical_odd F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK e psi0 beta c s hupperPoint
  have hquadratic := tameQuadratic_oddPhase_product hchar hpsi0
    (beta := beta) (c := c) (s := s) hbeta hs
  have hcritical : upper.criticalFactor * quadraticPhase psi0 2 0 =
      finiteQuadraticChar (ResidueField F) beta *
        lower.criticalFactor ^ 2 := by
    rw [hupperCritical, hlowerCritical]
    exact hquadratic
  simpa only using
    (tameQuadratic_stablePair_of_exact_factors F K chiK psiK nu chiF psiF
      d 1 hFodd hnu GammaF R lower rfl upper GammaNu
      (quadraticPhase psi0 2 0)
      (finiteQuadraticChar (ResidueField F) beta) hnorm hstableValue
      (tameQuadratic_mappedBaseFactor_odd F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hchi hpsi hdegree hchar gammaF hgammaF
          hFodd H R deltaF hdeltaF deltaK hdeltaK)
      hcritical)


/-! ### Auditable computational normal forms -/

/-- Exact data left by the field calculation in the even higher branch.
Every equality mentions the actual stationary quotient representative,
mapped denominator, conductor-one norm datum, and stable quotient
`gammaF / beta`. -/
structure TameQuadraticHigherEvenNormalForm
    (hFeven : IsStationaryConductorDecomposition chiF.conductor d 0)
    (tau : NormCharacter F K) where
  gammaF : Fˣ
  gammaF_order : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)
  parameters : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFeven hchi hpsi hdegree rfl hchar
      gammaF gammaF_order
  representative : StationaryClassRepresentative F chiF psiF hFeven
    gammaF gammaF_order
  deltaK : Kˣ
  deltaK_order : ord K (deltaK : K) =
    (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ)
  psi0 : FiniteAddChar (ResidueField F)
  psi0_ne_one : psi0 ≠ 1
  beta : ResidueField F
  beta_ne_zero : beta ≠ 0
  normData : LocalQuasiCharData F
  normData_character : normData.character = tau.1
  normData_conductor : normData.conductor = 1
  gammaNorm : Fˣ
  gammaNorm_order : ord F (gammaNorm : F) =
    ((psiF.conductor + 1 : ℤ) : WithTop ℤ)
  normResidual : residualMulChar F normData =
    finiteQuadraticChar (ResidueField F)
  normGammaValue : ((normData.character gammaNorm : ℂˣ) : ℂ) = 1
  residualAdditive : residualAddChar F psiF gammaNorm gammaNorm_order = psi0
  upperPointwise : ∀ x : ResidueField F,
    (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar
        gammaF gammaF_order parameters representative deltaK
          deltaK_order).function (tameQuadraticResidueEquiv F K hres x) =
      psi0 (((-2 * beta) / 2) * x ^ 2 + 0 * x)
  stableValue :
    ((normData.character (gammaF /
      tameQuadraticStableBeta F normData chiF psiF d 0 hFeven
        ⟨gammaF, gammaF_order⟩ representative) : ℂˣ) : ℂ) =
      finiteQuadraticChar (ResidueField F) beta

/-- Exact normal forms in the odd higher branch.  The coefficient `c` and
sign `s` occur simultaneously in both actual Hasse functions. -/
structure TameQuadraticHigherOddNormalForm
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (tau : NormCharacter F K) where
  gammaF : Fˣ
  gammaF_order : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)
  parameters : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFodd hchi hpsi hdegree rfl hchar
      gammaF gammaF_order
  representative : StationaryClassRepresentative F chiF psiF hFodd
    gammaF gammaF_order
  deltaF : Fˣ
  deltaF_order : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ)
  deltaK : Kˣ
  deltaK_order : ord K (deltaK : K) =
    (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ)
  psi0 : FiniteAddChar (ResidueField F)
  psi0_ne_one : psi0 ≠ 1
  beta : ResidueField F
  c : ResidueField F
  s : ResidueField F
  beta_ne_zero : beta ≠ 0
  sign_sq : s ^ 2 = 1
  normData : LocalQuasiCharData F
  normData_character : normData.character = tau.1
  normData_conductor : normData.conductor = 1
  gammaNorm : Fˣ
  gammaNorm_order : ord F (gammaNorm : F) =
    ((psiF.conductor + 1 : ℤ) : WithTop ℤ)
  normResidual : residualMulChar F normData =
    finiteQuadraticChar (ResidueField F)
  normGammaValue : ((normData.character gammaNorm : ℂˣ) : ℂ) = 1
  residualAdditive : residualAddChar F psiF gammaNorm gammaNorm_order = psi0
  lowerPointwise : ∀ x : ResidueField F,
    (RamifiedHasseOddStationaryPhase.function
      ({ d := d
         decomposition := hFodd
         denominator := ⟨gammaF, gammaF_order⟩
         representative := representative
         delta := deltaF
         delta_order := deltaF_order } :
        RamifiedHasseOddStationaryPhase F chiF psiF)) x =
      psi0 ((beta / 2) * x ^ 2 + c * x)
  upperPointwise : ∀ x : ResidueField F,
    (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar
        gammaF gammaF_order parameters representative deltaK
          deltaK_order).function (tameQuadraticResidueEquiv F K hres x) =
      psi0 (((2 * beta) / 2) * x ^ 2 + (2 * s * c) * x)
  stableValue :
    ((normData.character (gammaF /
      tameQuadraticStableBeta F normData chiF psiF d 1 hFodd
        ⟨gammaF, gammaF_order⟩ representative) : ℂˣ) : ℂ) =
      finiteQuadraticChar (ResidueField F) beta

include ht hres hpiK hgen hdegree in
private noncomputable def hcHigherEvenNormalForm
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (d : ℕ)
    (hFeven : IsStationaryConductorDecomposition chiF.conductor d 0) :
    TameQuadraticHigherEvenNormalForm F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hchi hpsi hdegree hchar hFeven tau := by
  let GammaF := hcGamma F K ht hres piK hgen chiF psiF
  let H := highConductorParameter_tameQuadratic
    F K ht hres piK hpiK hgen chiF chiK psiF psiK hFeven hchi hpsi
      hdegree rfl hchar (GammaF : Fˣ) GammaF.property
  let R := hcRepresentative F K chiF psiF hFeven GammaF
  let deltaK := hcDeltaEven F K ht piK hgen d
  let hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ) := by
    simpa [hFeven.conductor_eq] using
      (hcDeltaEven_order F K ht piK hgen d)
  let normData := hcNormData F K ht hres piK hpiK hgen tau htau
  let gammaNorm := hcGammaNorm F K ht piK hgen psiF
  let psi0 := hcPsi0 F K ht hres piK hgen psiF
  let beta := hcBeta F chiF psiF hFeven GammaF R
  refine
    { gammaF := (GammaF : Fˣ)
      gammaF_order := GammaF.property
      parameters := H
      representative := R
      deltaK := deltaK
      deltaK_order := hdeltaK
      psi0 := psi0
      psi0_ne_one := hcPsi0_ne_one F K ht hres piK hgen psiF
      beta := beta
      beta_ne_zero := hcBeta_ne_zero F chiF psiF hFeven GammaF R
      normData := normData
      normData_character := rfl
      normData_conductor := rfl
      gammaNorm := gammaNorm
      gammaNorm_order := hcGammaNorm_order F K ht hres piK hgen psiF
      normResidual := hcNormData_residual F K ht hres piK hpiK hgen hdegree
        hchar tau htau
      normGammaValue := ?_
      residualAdditive := rfl
      upperPointwise := hcUpperPointwise_even F K ht hres piK hpiK hgen
        hdegree hchar chiF chiK psiF psiK hchi hpsi d hFeven
      stableValue := hcNormData_stableValue F K ht hres piK hpiK hgen
        hdegree hchar tau htau chiF psiF hFeven R }
  exact congrArg Units.val
    (hcNormData_gammaNorm_value F K ht hres piK hpiK hgen psiF tau htau)

private theorem TameQuadraticHigherEvenNormalForm.pair
    (hFeven : IsStationaryConductorDecomposition chiF.conductor d 0)
    (tau : NormCharacter F K)
    (D : TameQuadraticHigherEvenNormalForm F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hchi hpsi hdegree hchar hFeven tau) :
    let GammaF : AdmissibleGamma F chiF psiF :=
      ⟨D.gammaF, D.gammaF_order⟩
    let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFeven hchi hpsi hdegree hchar
        D.gammaF D.gammaF_order D.parameters D.representative D.deltaK
          D.deltaK_order).localPhase
    let GammaNorm := conductorOneGamma D.normData D.normData_conductor psiF
      D.gammaNorm D.gammaNorm_order
    let hcond : D.normData.conductor < chiF.conductor := by
      rw [D.normData_conductor, hFeven.conductor_eq]
      have := hFeven.conductor_gt_one
      rw [hFeven.conductor_eq] at this
      omega
    deltaFinite chiK psiK upper.gamma *
        deltaFinite D.normData psiF GammaNorm =
      deltaFinite chiF psiF GammaF *
        deltaFinite (stableTwistData F D.normData chiF hcond) psiF
          (stableTwistAdmissibleGamma F D.normData chiF psiF hcond GammaF) := by
  dsimp only
  have hd : D.normData.conductor ≤ d := by
    rw [D.normData_conductor]
    have hlarge := hFeven.conductor_gt_one
    rw [hFeven.conductor_eq] at hlarge
    omega
  have hnorm := deltaFinite_quadratic_conductor_one F hchar
    D.normData D.normData_conductor psiF D.gammaNorm D.gammaNorm_order
      D.normResidual D.normGammaValue
  rw [D.residualAdditive] at hnorm
  exact firstMain_tameQuadratic_higher_even F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hchi hpsi hdegree hchar D.gammaF D.gammaF_order
      hFeven D.parameters D.representative D.deltaK D.deltaK_order
      (tameQuadraticResidueEquiv F K hres) D.psi0 D.psi0_ne_one
      D.beta D.beta_ne_zero D.upperPointwise D.normData hd
      (conductorOneGamma D.normData D.normData_conductor psiF
        D.gammaNorm D.gammaNorm_order) hnorm D.stableValue

private theorem TameQuadraticHigherOddNormalForm.pair
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (tau : NormCharacter F K)
    (D : TameQuadraticHigherOddNormalForm F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hchi hpsi hdegree hchar hFodd tau) :
    let GammaF : AdmissibleGamma F chiF psiF :=
      ⟨D.gammaF, D.gammaF_order⟩
    let upper := (tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar
        D.gammaF D.gammaF_order D.parameters D.representative D.deltaK
          D.deltaK_order).localPhase
    let GammaNorm := conductorOneGamma D.normData D.normData_conductor psiF
      D.gammaNorm D.gammaNorm_order
    let hcond : D.normData.conductor < chiF.conductor := by
      rw [D.normData_conductor, hFodd.conductor_eq]
      have hlarge := hFodd.conductor_gt_one
      rw [hFodd.conductor_eq] at hlarge
      omega
    deltaFinite chiK psiK upper.gamma *
        deltaFinite D.normData psiF GammaNorm =
      deltaFinite chiF psiF GammaF *
        deltaFinite (stableTwistData F D.normData chiF hcond) psiF
          (stableTwistAdmissibleGamma F D.normData chiF psiF hcond GammaF) := by
  dsimp only
  have hd : D.normData.conductor ≤ d := by
    rw [D.normData_conductor]
    have hlarge := hFodd.conductor_gt_one
    rw [hFodd.conductor_eq] at hlarge
    omega
  have hnorm := deltaFinite_quadratic_conductor_one F hchar
    D.normData D.normData_conductor psiF D.gammaNorm D.gammaNorm_order
      D.normResidual D.normGammaValue
  rw [D.residualAdditive] at hnorm
  exact firstMain_tameQuadratic_higher_odd F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hchi hpsi hdegree hchar D.gammaF D.gammaF_order
      hFodd D.parameters D.representative D.deltaF D.deltaF_order
      D.deltaK D.deltaK_order (tameQuadraticResidueEquiv F K hres)
      D.psi0 D.psi0_ne_one D.beta D.c D.s D.beta_ne_zero D.sign_sq
      D.lowerPointwise D.upperPointwise D.normData hd
      (conductorOneGamma D.normData D.normData_conductor psiF
        D.gammaNorm D.gammaNorm_order) hnorm D.stableValue

end HigherComparison


open scoped BigOperators

private noncomputable def hasseToCriticalPolar
    {k : Type*} [Field k] [Fintype k]
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    {theta : FiniteAddChar k} (phi : HasseFunction k theta) :
    CriticalPolarFunction k psi0
      (finiteAddCharCoefficient psi0 hpsi0 theta) where
  toFun := phi
  ne_zero' := phi.ne_zero
  map_add' x y := by
    rw [phi.map_add]
    congr 1
    exact (finiteAddCharCoefficient_apply psi0 hpsi0 theta (x * y)).symm

@[simp] private theorem hasseToCriticalPolar_apply
    {k : Type*} [Field k] [Fintype k]
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    {theta : FiniteAddChar k} (phi : HasseFunction k theta) (x : k) :
    hasseToCriticalPolar psi0 hpsi0 phi x = phi x := rfl

private noncomputable def hasseToCriticalPolarOfCoefficient
    {k : Type*} [Field k] [Fintype k]
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    {theta : FiniteAddChar k} (phi : HasseFunction k theta)
    (A : k) (hA : finiteAddCharCoefficient psi0 hpsi0 theta = A) :
    CriticalPolarFunction k psi0 A where
  toFun := phi
  ne_zero' := phi.ne_zero
  map_add' x y := by
    rw [phi.map_add]
    congr 1
    rw [← hA]
    exact (finiteAddCharCoefficient_apply psi0 hpsi0 theta (x * y)).symm

@[simp] private theorem hasseToCriticalPolarOfCoefficient_apply
    {k : Type*} [Field k] [Fintype k]
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    {theta : FiniteAddChar k} (phi : HasseFunction k theta)
    (A : k) (hA : finiteAddCharCoefficient psi0 hpsi0 theta = A)
    (x : k) :
    hasseToCriticalPolarOfCoefficient psi0 hpsi0 phi A hA x = phi x := rfl

/-- Every genuine odd Lamprecht function has an intrinsic pointwise
quadratic normal form relative to any fixed nontrivial residue character.
The polar and affine coefficients are extracted from the complete function,
so no translation or elementary factor is discarded. -/
private theorem lowerPointwise_of_criticalPolar
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (V : RamifiedHasseOddStationaryPhase E chi psi)
    (hchar : residueCharacteristic E ≠ 2)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1) :
    letI := residueFieldFintype E
    let beta := finiteAddCharCoefficient psi0 hpsi0
      (lamprechtResidualAddChar E chi psi V.d V.conductor_eq
        V.conductor_large V.denominator V.delta V.delta_order)
    let c := (hasseToCriticalPolar psi0 hpsi0 V.function).affineCoefficient
      hchar hpsi0
    ∀ x : ResidueField E,
      V.function x = psi0 ((beta / 2) * x ^ 2 + c * x) := by
  letI : Fintype (ResidueField E) := residueFieldFintype E
  dsimp only
  intro x
  exact (hasseToCriticalPolar psi0 hpsi0 V.function).eq_quadratic
    hchar hpsi0 x

private theorem lamprechtResidualAddChar_eq_criticalPolarAddChar
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    lamprechtResidualAddChar E chi psi d hm hlarge Gamma delta hdelta =
      criticalPolarAddChar E chi psi d hm hlarge Gamma delta hdelta := by
  rfl

private theorem criticalPolarResidueScale_eq_one_of_uniformizerPowers
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma E chi psi)
    (pi : Eˣ)
    (hGamma : (Gamma : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor))
    (delta : Eˣ) (hdelta : delta = pi ^ d)
    (gamma0 : Eˣ) (hgamma0 : gamma0 = pi ^ (psi.conductor + 1)) :
    criticalPolarResidueScale E chi psi d hm Gamma delta gamma0 = 1 := by
  unfold criticalPolarResidueScale
  rw [hdelta, hgamma0, hGamma]
  rw [← zpow_natCast]
  group
  have hmZ : (chi.conductor : ℤ) = 2 * (d : ℤ) + 1 := by
    exact_mod_cast hm
  rw [show (1 : ℤ) + (d : ℤ) * 2 + psi.conductor =
      psi.conductor + chi.conductor by omega]
  simp

private theorem criticalPolarResidue_eq_reduce_of_uniformizerPowers
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma E chi psi)
    (pi : Eˣ)
    (hGamma : (Gamma : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor))
    (delta : Eˣ)
    (hdeltaOrd : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (hdelta : delta = pi ^ d)
    (gamma0 : Eˣ)
    (hgamma0Ord : ord E (gamma0 : E) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ))
    (hgamma0 : gamma0 = pi ^ (psi.conductor + 1))
    (beta : lattice E ((chi.conductor : ℤ) - chi.conductor)) :
    criticalPolarResidueOfRepresentative E chi psi d hm Gamma delta
        hdeltaOrd gamma0 hgamma0Ord beta =
      reduce E (beta : E) (by
        simpa only [sub_self] using beta.property) := by
  unfold criticalPolarResidueOfRepresentative
  unfold reduce
  apply congrArg (residueMap E)
  apply Subtype.ext
  change
    (criticalPolarResidueScale E chi psi d hm Gamma delta gamma0 : E) *
        (beta : E) = beta
  rw [criticalPolarResidueScale_eq_one_of_uniformizerPowers E chi psi d hm
    Gamma pi hGamma delta hdelta gamma0 hgamma0]
  simp

/-- Canonical odd lower normal form.  With `Gamma=pi^(m+n)`,
`delta=pi^d`, and `gamma0=pi^(n+1)`, the polar coefficient is literally the
residue of the already selected stationary representative. -/
private theorem lowerPointwise_of_uniformizerPowers
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ)
    (hodd : IsStationaryConductorDecomposition chi.conductor d 1)
    (hchar : residueCharacteristic E ≠ 2)
    (Gamma : AdmissibleGamma E chi psi)
    (pi : Eˣ)
    (hGamma : (Gamma : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor))
    (R : StationaryClassRepresentative E chi psi hodd
      (Gamma : Eˣ) Gamma.property)
    (delta : Eˣ)
    (hdeltaOrd : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (hdelta : delta = pi ^ d)
    (gamma0 : Eˣ)
    (hgamma0Ord : ord E (gamma0 : E) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ))
    (hgamma0 : gamma0 = pi ^ (psi.conductor + 1)) :
    letI := residueFieldFintype E
    let V : RamifiedHasseOddStationaryPhase E chi psi :=
      { d := d
        decomposition := hodd
        denominator := Gamma
        representative := R
        delta := delta
        delta_order := hdeltaOrd }
    let psi0 := residualAddChar E psi gamma0 hgamma0Ord
    let hpsi0 : psi0 ≠ 1 :=
      residualAddChar_ne_one E psi gamma0 hgamma0Ord
    let beta := reduce E (R.representative : E) (by
      simpa only [sub_self] using R.representative.property)
    ∃ c : ResidueField E, ∀ x : ResidueField E,
      V.function x = psi0 ((beta / 2) * x ^ 2 + c * x) := by
  letI : Fintype (ResidueField E) := residueFieldFintype E
  dsimp only
  let V : RamifiedHasseOddStationaryPhase E chi psi :=
    { d := d
      decomposition := hodd
      denominator := Gamma
      representative := R
      delta := delta
      delta_order := hdeltaOrd }
  let psi0 := residualAddChar E psi gamma0 hgamma0Ord
  let hpsi0 : psi0 ≠ 1 :=
    residualAddChar_ne_one E psi gamma0 hgamma0Ord
  let beta0 : lattice E ((chi.conductor : ℤ) - chi.conductor) :=
    ⟨(R.representative : E), by
      simpa only [sub_self] using R.representative.property⟩
  have hbeta0 : beta0 = R.toLamprecht := by
    apply Subtype.ext
    rfl
  have hrep : latticeQuotientMk E
      (sub_le_sub_left
        (criticalPolar_stationaryDepth E chi d hodd.conductor_eq
          hodd.conductor_gt_one).int_le_conductor
        (chi.conductor : ℤ)) beta0 =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hodd.conductor_eq
          hodd.conductor_gt_one) Gamma Gamma.property := by
    rw [hbeta0]
    simpa only [stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  have hcoef : finiteAddCharCoefficient psi0 hpsi0
      (lamprechtResidualAddChar E chi psi d hodd.conductor_eq
        hodd.conductor_gt_one Gamma delta hdeltaOrd) =
      reduce E (R.representative : E) (by
        simpa only [sub_self] using R.representative.property) := by
    rw [lamprechtResidualAddChar_eq_criticalPolarAddChar E chi psi d
      hodd.conductor_eq hodd.conductor_gt_one Gamma delta hdeltaOrd]
    change criticalPolarCoefficient E chi psi d hodd.conductor_eq
        hodd.conductor_gt_one Gamma delta hdeltaOrd psi0 hpsi0 = _
    rw [criticalPolarCoefficient_eq_residue E chi psi d hodd.conductor_eq
      hodd.conductor_gt_one Gamma delta hdeltaOrd psi0 hpsi0 gamma0
        hgamma0Ord rfl beta0 hrep]
    exact criticalPolarResidue_eq_reduce_of_uniformizerPowers E chi psi d
      hodd.conductor_eq Gamma pi hGamma delta hdeltaOrd hdelta gamma0
        hgamma0Ord hgamma0 beta0
  let phi := hasseToCriticalPolarOfCoefficient psi0 hpsi0 V.function
    (reduce E (R.representative : E) (by
      simpa only [sub_self] using R.representative.property)) hcoef
  refine ⟨phi.affineCoefficient hchar hpsi0, ?_⟩
  intro x
  exact phi.eq_quadratic hchar hpsi0 x

/-! The field-level identity needed in the tame quadratic odd branch.  The
upper critical unit is the base-field image of the lower critical unit after
the residual sign rescaling.  Pullback by norm and trace therefore squares
the *complete* lower Hasse value. -/

private theorem mappedOddHasseFunction_sq
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2)
    (dF dK : ℕ)
    (hmF : chiF.conductor = 2 * dF + 1)
    (hmK : chiK.conductor = 2 * dK + 1)
    (hlargeF : 1 < chiF.conductor)
    (hlargeK : 1 < chiK.conductor)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom (GammaF : Fˣ))
    (cF : lattice F ((chiF.conductor : ℤ) - chiF.conductor))
    (hcF : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chiF dF 1
            (by omega) hmF hlargeF).int_le_conductor
          (chiF.conductor : ℤ)) cF =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF dF 1
          (by omega) hmF hlargeF) GammaF GammaF.property)
    (cK : lattice K ((chiK.conductor : ℤ) - chiK.conductor))
    (hcK : latticeQuotientMk K
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth K chiK dK 1
            (by omega) hmK hlargeK).int_le_conductor
          (chiK.conductor : ℤ)) cK =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK dK 1
          (by omega) hmK hlargeK) GammaK GammaK.property)
    (hcMap : (cK : K) = algebraMap F K (cF : F))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((dF : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((0 : ℤ) : WithTop ℤ))
    (hdeltaMap : deltaK =
      Units.map (algebraMap F K).toMonoidHom (u * deltaF))
    (x : ResidueField F) :
    lamprechtHasseFunction K chiK psiK dK hmK hlargeK GammaK deltaK
        hdeltaK cK hcK (extensionResidueMap F K x) =
      lamprechtHasseFunction F chiF psiF dF hmF hlargeF GammaF deltaF
        hdeltaF cF hcF
          (reduce F ((u : F) * (teichmuller F x : F)) (by
            rw [mem_lattice, ord_mul, hu]
            have hx := (teichmuller F x).property
            rw [← mem_lattice_zero_iff] at hx
            rw [mem_lattice] at hx
            simpa using hx)) ^ 2 := by
  let tx : F := (teichmuller F x : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  have hmaptx : algebraMap F K tx ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    rw [mem_lattice] at htx
    simpa using nsmul_le_nsmul_right htx (ramificationIndex F K)
  have hredMap : reduce K (algebraMap F K tx) hmaptx =
      extensionResidueMap F K x := by
    change residueMap K
        (⟨algebraMap F K tx, (mem_lattice_zero_iff K).1 hmaptx⟩ :
          ringOfIntegers K) = _
    change extensionResidueMap F K
        (residueMap F
          (⟨tx, (mem_lattice_zero_iff F).1 htx⟩ : ringOfIntegers F)) = _
    simp [tx]
  have huInt : (u : F) ∈ lattice F 0 := by
    rw [mem_lattice, hu]
  have hutx : (u : F) * tx ∈ lattice F 0 := by
    simpa using mul_mem_lattice F huInt htx
  rw [← hredMap,
    lamprechtHasseFunction_integral_lift K chiK psiK dK hmK hlargeK
      GammaK deltaK hdeltaK cK hcK (algebraMap F K tx) hmaptx,
    lamprechtHasseFunction_integral_lift F chiF psiF dF hmF hlargeF
      GammaF deltaF hdeltaF cF hcF ((u : F) * tx) hutx]
  rw [lamprechtHasseValue, lamprechtHasseValue]
  have harg :
      (cK : K) * (deltaK : K) * algebraMap F K tx /
          ((GammaK : Kˣ) : K) =
        algebraMap F K
          ((cF : F) * (deltaF : F) * ((u : F) * tx) /
            ((GammaF : Fˣ) : F)) := by
    rw [hcMap, hdeltaMap, hGamma]
    simp only [Units.coe_map, Units.val_mul]
    rw [map_mul]
    change
      algebraMap F K (cF : F) *
          (algebraMap F K (u : F) * algebraMap F K (deltaF : F)) *
          algebraMap F K tx /
          algebraMap F K ((GammaF : Fˣ) : F) = _
    simp only [map_div₀, map_mul]
    ring
  have hunit :
      (lamprechtHasseUnit K chiK dK hmK hlargeK deltaK hdeltaK
        (algebraMap F K tx) hmaptx : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom
        (lamprechtHasseUnit F chiF dF hmF hlargeF deltaF hdeltaF
          ((u : F) * tx) hutx : Fˣ) := by
    apply Units.ext
    simp only [Units.coe_map]
    rw [lamprechtHasseUnit_coe, lamprechtHasseUnit_coe, hdeltaMap]
    simp only [Units.coe_map, Units.val_mul]
    rw [map_mul]
    change
      1 + (algebraMap F K (u : F) * algebraMap F K (deltaF : F)) *
          algebraMap F K tx =
        algebraMap F K (1 + (deltaF : F) * ((u : F) * tx))
    simp only [map_add, map_one, map_mul]
    ring
  rw [hchi, hpsi, ContinuousAddChar.compTrace_apply,
    ContinuousQuasiChar.compNorm_apply, harg, hunit]
  have htrace : trace F K (algebraMap F K
      ((cF : F) * (deltaF : F) * ((u : F) * tx) /
        ((GammaF : Fˣ) : F))) =
      2 • ((cF : F) * (deltaF : F) * ((u : F) * tx) /
        ((GammaF : Fˣ) : F)) := by
    rw [trace_algebraMap, hdegree]
  rw [htrace]
  have hnorm : Units.map (Algebra.norm F)
      (Units.map (algebraMap F K).toMonoidHom
        (lamprechtHasseUnit F chiF dF hmF hlargeF deltaF hdeltaF
          ((u : F) * tx) hutx : Fˣ)) =
      (lamprechtHasseUnit F chiF dF hmF hlargeF deltaF hdeltaF
        ((u : F) * tx) hutx : Fˣ) ^ 2 := by
    ext
    change norm F K
        (algebraMap F K
          (1 + (deltaF : F) * ((u : F) * tx))) =
      (1 + (deltaF : F) * ((u : F) * tx)) ^ 2
    rw [norm_algebraMap, hdegree]
  rw [hnorm, map_pow]
  have hpsiPow := congrArg Units.val
    (AddChar.map_nsmul_eq_pow psiF.character.toAddChar 2
      ((cF : F) * (deltaF : F) * ((u : F) * tx) /
        ((GammaF : Fˣ) : F)))
  change
    ((psiF.character
      (2 • ((cF : F) * (deltaF : F) * ((u : F) * tx) /
        ((GammaF : Fˣ) : F))) : ℂˣ) : ℂ) =
      ((psiF.character
        ((cF : F) * (deltaF : F) * ((u : F) * tx) /
          ((GammaF : Fˣ) : F)) : ℂˣ) : ℂ) ^ 2 at hpsiPow
  rw [hpsiPow]
  simp only [Units.val_pow_eq_pow_val, inv_pow, mul_pow]

/-- Residue-coordinate form of `mappedOddHasseFunction_sq`. -/
private theorem mappedOddHasseFunction_sq_residue
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2)
    (dF dK : ℕ)
    (hmF : chiF.conductor = 2 * dF + 1)
    (hmK : chiK.conductor = 2 * dK + 1)
    (hlargeF : 1 < chiF.conductor)
    (hlargeK : 1 < chiK.conductor)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom (GammaF : Fˣ))
    (cF : lattice F ((chiF.conductor : ℤ) - chiF.conductor))
    (hcF : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chiF dF 1
            (by omega) hmF hlargeF).int_le_conductor
          (chiF.conductor : ℤ)) cF =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF dF 1
          (by omega) hmF hlargeF) GammaF GammaF.property)
    (cK : lattice K ((chiK.conductor : ℤ) - chiK.conductor))
    (hcK : latticeQuotientMk K
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth K chiK dK 1
            (by omega) hmK hlargeK).int_le_conductor
          (chiK.conductor : ℤ)) cK =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK dK 1
          (by omega) hmK hlargeK) GammaK GammaK.property)
    (hcMap : (cK : K) = algebraMap F K (cF : F))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((dF : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((0 : ℤ) : WithTop ℤ))
    (hdeltaMap : deltaK =
      Units.map (algebraMap F K).toMonoidHom (u * deltaF)) :
    let huInt : (u : F) ∈ lattice F 0 := by rw [mem_lattice, hu]
    let s := reduce F (u : F) huInt
    ∀ x : ResidueField F,
      lamprechtHasseFunction K chiK psiK dK hmK hlargeK GammaK deltaK
          hdeltaK cK hcK (extensionResidueMap F K x) =
        lamprechtHasseFunction F chiF psiF dF hmF hlargeF GammaF deltaF
          hdeltaF cF hcF (s * x) ^ 2 := by
  dsimp only
  intro x
  have huInt : (u : F) ∈ lattice F 0 := by rw [mem_lattice, hu]
  let tx : F := (teichmuller F x : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  have hutx : (u : F) * tx ∈ lattice F 0 := by
    simpa using mul_mem_lattice F huInt htx
  have hred : reduce F ((u : F) * tx) hutx =
      reduce F (u : F) huInt * x := by
    change residueMap F
        (⟨(u : F) * tx, (mem_lattice_zero_iff F).1 hutx⟩ :
          ringOfIntegers F) = _
    change residueMap F
        ((⟨(u : F), (mem_lattice_zero_iff F).1 huInt⟩ :
            ringOfIntegers F) *
          ⟨tx, (mem_lattice_zero_iff F).1 htx⟩) = _
    rw [map_mul]
    congr 1
    simp [tx]
  simpa only [tx, hred] using
    mappedOddHasseFunction_sq F K chiF psiF chiK psiK hchi hpsi hdegree
      dF dK hmF hmK hlargeF hlargeK GammaF GammaK hGamma cF hcF cK hcK
        hcMap deltaF hdeltaF deltaK hdeltaK u hu hdeltaMap x

/-- Exact specialization to the actual tame-quadratic phases in the target
file.  Only the elementary equality between the selected powers `deltaK`
and `u*deltaF` remains for the intrinsic constructor to supply. -/
private theorem tameQuadraticUpstairsOddPhase_function_sq
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (d : ℕ)
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree rfl hchar
        gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hFodd
      gammaF hgammaF)
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((0 : ℤ) : WithTop ℤ))
    (hdeltaMap : deltaK =
      Units.map (algebraMap F K).toMonoidHom (u * deltaF)) :
    let lower : RamifiedHasseOddStationaryPhase F chiF psiF :=
      { d := d
        decomposition := hFodd
        denominator := ⟨gammaF, hgammaF⟩
        representative := R
        delta := deltaF
        delta_order := hdeltaF }
    let upper := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
        H R deltaK hdeltaK
    let huInt : (u : F) ∈ lattice F 0 := by rw [mem_lattice, hu]
    let s := reduce F (u : F) huInt
    ∀ x : ResidueField F,
      upper.function (extensionResidueMap F K x) =
        lower.function (s * x) ^ 2 := by
  dsimp only
  let lower : RamifiedHasseOddStationaryPhase F chiF psiF :=
    { d := d
      decomposition := hFodd
      denominator := ⟨gammaF, hgammaF⟩
      representative := R
      delta := deltaF
      delta_order := hdeltaF }
  let upper := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar gammaF hgammaF
      H R deltaK hdeltaK
  have hcF : latticeQuotientMk F
      (sub_le_sub_left
        (lamprechtFormula_stationaryDepth F chiF d 1 (by omega)
          hFodd.conductor_eq hFodd.conductor_gt_one).int_le_conductor
        (chiF.conductor : ℤ)) R.toLamprecht =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF d 1 (by omega)
          hFodd.conductor_eq hFodd.conductor_gt_one)
        lower.denominator lower.denominator.property := by
    simpa only [lower, stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  have hcK : latticeQuotientMk K
      (sub_le_sub_left
        (lamprechtFormula_stationaryDepth K chiK upper.d 1 (by omega)
          upper.conductor_eq upper.conductor_large).int_le_conductor
        (chiK.conductor : ℤ)) upper.representative.toLamprecht =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK upper.d 1 (by omega)
          upper.conductor_eq upper.conductor_large)
        upper.denominator upper.denominator.property := by
    simpa only [upper, tameQuadraticUpstairsOddPhase,
      stationaryDepthOfConductorDecomposition] using
        upper.representative.toLamprecht_represents
  have hcMap : (upper.representative.toLamprecht : K) =
      algebraMap F K (R.toLamprecht : F) := by
    rfl
  exact mappedOddHasseFunction_sq_residue F K chiF psiF chiK psiK hchi
    hpsi hdegree d upper.d hFodd.conductor_eq upper.conductor_eq
      hFodd.conductor_gt_one upper.conductor_large lower.denominator
      upper.denominator rfl R.toLamprecht hcF upper.representative.toLamprecht
      hcK hcMap deltaF hdeltaF deltaK hdeltaK u hu hdeltaMap


private theorem stationaryClassRepresentative_reduce_ne_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    reduce E (R.representative : E) (by
      simpa only [sub_self] using R.representative.property) ≠ 0 := by
  have hord : ord E (R.representative : E) =
      ((0 : ℤ) : WithTop ℤ) := by
    change ord E (R.toLamprecht : E) = ((0 : ℤ) : WithTop ℤ)
    simpa only [sub_self] using
      stationaryNumeratorClass_representative_ord E chi psi
        (chi.conductor : ℤ) (stationaryDepthOfConductorDecomposition E chi h)
        (Gamma : Eˣ) Gamma.property R.toLamprecht R.toLamprecht_represents
  intro hz
  unfold reduce at hz
  rw [residueMap_eq_zero_iff, mem_lattice, hord] at hz
  have hnot : ¬ (((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)) := by
    norm_num
  exact hnot hz

private theorem upperPointwise_of_lowerPointwise_sq_core
    {k : Type*} [Field k] [Fintype k]
    (hchar : ringChar k ≠ 2)
    (psi0 : FiniteAddChar k)
    (beta c s : k) (hs : s ^ 2 = 1)
    (lower upper : k → ℂ)
    (hlower : ∀ x, lower x =
      psi0 ((beta / 2) * x ^ 2 + c * x))
    (hsquare : ∀ x, upper x = lower (s * x) ^ 2) :
    ∀ x, upper x =
      psi0 (((2 * beta) / 2) * x ^ 2 + (2 * s * c) * x) := by
  intro x
  rw [hsquare, hlower, pow_two, ← psi0.map_add_eq_mul]
  congr 1
  calc
    beta / 2 * (s * x) ^ 2 + c * (s * x) +
          (beta / 2 * (s * x) ^ 2 + c * (s * x)) =
        beta * s ^ 2 * x ^ 2 + 2 * s * c * x := by
          field_simp [Ring.two_ne_zero hchar]
          ring
    _ = beta * x ^ 2 + 2 * s * c * x := by rw [hs]; ring
    _ = 2 * beta / 2 * x ^ 2 + 2 * s * c * x := by
      field_simp [Ring.two_ne_zero hchar]

/-- Fully assembled odd pointwise fields, with the same literal `beta` in
the lower function, upper function, nonvanishing certificate, and stable
residue interpretation. -/
private theorem tameQuadraticOddPointwise_of_uniformizerPowers
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (d : ℕ)
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (piF : Fˣ)
    (GammaF : AdmissibleGamma F chiF psiF)
    (hGamma : (GammaF : Fˣ) =
      piF ^ ((chiF.conductor : ℤ) + psiF.conductor))
    (H : HighTameQuadraticParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree rfl hchar
        (GammaF : Fˣ) GammaF.property)
    (R : StationaryClassRepresentative F chiF psiF hFodd
      (GammaF : Fˣ) GammaF.property)
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (hdeltaPower : deltaF = piF ^ d)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ))
    (u : Fˣ) (hu : ord F (u : F) = ((0 : ℤ) : WithTop ℤ))
    (hdeltaMap : deltaK =
      Units.map (algebraMap F K).toMonoidHom (u * deltaF))
    (gamma0 : Fˣ)
    (hgamma0 : ord F (gamma0 : F) =
      ((psiF.conductor + 1 : ℤ) : WithTop ℤ))
    (hgamma0Power : gamma0 = piF ^ (psiF.conductor + 1))
    (hsign : (reduce F (u : F) (by rw [mem_lattice, hu])) ^ 2 = 1) :
    let lower : RamifiedHasseOddStationaryPhase F chiF psiF :=
      { d := d
        decomposition := hFodd
        denominator := GammaF
        representative := R
        delta := deltaF
        delta_order := hdeltaF }
    let upper := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar
        (GammaF : Fˣ) GammaF.property H R deltaK hdeltaK
    let psi0 := residualAddChar F psiF gamma0 hgamma0
    let beta := reduce F (R.representative : F) (by
      simpa only [sub_self] using R.representative.property)
    let s := reduce F (u : F) (by rw [mem_lattice, hu])
    beta ≠ 0 ∧ s ^ 2 = 1 ∧
      ∃ c : ResidueField F,
        (∀ x, lower.function x =
          psi0 ((beta / 2) * x ^ 2 + c * x)) ∧
        (∀ x, upper.function (extensionResidueMap F K x) =
          psi0 (((2 * beta) / 2) * x ^ 2 + (2 * s * c) * x)) := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  dsimp only
  let lower : RamifiedHasseOddStationaryPhase F chiF psiF :=
    { d := d
      decomposition := hFodd
      denominator := GammaF
      representative := R
      delta := deltaF
      delta_order := hdeltaF }
  let upper := tameQuadraticUpstairsOddPhase F K ht hres piK hpiK hgen
    chiF chiK psiF psiK hFodd hchi hpsi hdegree hchar
      (GammaF : Fˣ) GammaF.property H R deltaK hdeltaK
  let psi0 := residualAddChar F psiF gamma0 hgamma0
  let hpsi0 : psi0 ≠ 1 := residualAddChar_ne_one F psiF gamma0 hgamma0
  let beta := reduce F (R.representative : F) (by
    simpa only [sub_self] using R.representative.property)
  let s := reduce F (u : F) (by rw [mem_lattice, hu])
  have hbeta : beta ≠ 0 := by
    exact stationaryClassRepresentative_reduce_ne_zero F chiF psiF hFodd
      GammaF R
  obtain ⟨c, hlower⟩ := lowerPointwise_of_uniformizerPowers F chiF psiF
    d hFodd hchar GammaF piF hGamma R deltaF hdeltaF hdeltaPower gamma0
      hgamma0 hgamma0Power
  have hsquare := tameQuadraticUpstairsOddPhase_function_sq F K ht hres piK
    hpiK hgen chiF chiK psiF psiK d hFodd hchi hpsi hdegree hchar
      (GammaF : Fˣ) GammaF.property H R deltaF hdeltaF deltaK hdeltaK u hu
        hdeltaMap
  have hupper := upperPointwise_of_lowerPointwise_sq_core hchar psi0 beta c s hsign
    (fun x ↦ lower.function x)
    (fun x ↦ upper.function (extensionResidueMap F K x)) hlower hsquare
  exact ⟨hbeta, hsign, c, hlower, hupper⟩

/-- The intrinsic odd higher normal form.  The sign is the residue of
`(-1)^d`, and the same quotient representative supplies the lower polar
coefficient, the upper polar coefficient, and the stable-twist value. -/
private noncomputable def hcHigherOddNormalForm
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (d : ℕ)
    (hFodd : IsStationaryConductorDecomposition chiF.conductor d 1) :
    TameQuadraticHigherOddNormalForm F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hchi hpsi hdegree hchar hFodd tau := by
  let piF := hcPiF F K ht piK hgen
  let GammaF := hcGamma F K ht hres piK hgen chiF psiF
  let H := highConductorParameter_tameQuadratic
    F K ht hres piK hpiK hgen chiF chiK psiF psiK hFodd hchi hpsi
      hdegree rfl hchar (GammaF : Fˣ) GammaF.property
  let R := hcRepresentative F K chiF psiF hFodd GammaF
  let deltaF : Fˣ := piF ^ d
  have hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ) := by
    simp only [deltaF, Units.val_pow_eq_pow_val, ord_pow, piF,
      hcPiF_ord F K ht hres piK hgen]
    norm_cast
    simp
  let deltaK : Kˣ := hcRhoUnit F K ht piK hgen ^ (2 * d)
  have hdeltaK : ord K (deltaK : K) =
      (((chiF.conductor - 1 : ℕ) : ℤ) : WithTop ℤ) := by
    have hpower : ord K (deltaK : K) =
        (((2 * d : ℕ) : ℤ) : WithTop ℤ) := by
      change ord K
        ((hcRhoUnit F K ht piK hgen ^ (2 * d) : Kˣ) : K) =
          (((2 * d : ℕ) : ℤ) : WithTop ℤ)
      rw [Units.val_pow_eq_pow_val, ord_pow, hcRhoUnit_coe,
        hcRho_ord F K ht piK hgen]
      simp
      norm_cast
    simpa [hFodd.conductor_eq] using hpower
  let u : Fˣ := hcMinusOneUnit F ^ d
  have hu : ord F (u : F) = ((0 : ℤ) : WithTop ℤ) := by
    simp [u, hcMinusOneUnit_coe]
  have hdeltaMap : deltaK =
      Units.map (algebraMap F K).toMonoidHom (u * deltaF) := by
    simpa only [deltaK, u, deltaF, piF] using
      (hcRho_evenPower F K ht piK hgen hdegree d)
  have huSq : u ^ 2 = 1 := by
    let a : Fˣ := hcMinusOneUnit F
    have ha : a ^ 2 = 1 := by
      apply Units.ext
      norm_num [a, hcMinusOneUnit_coe]
    calc
      u ^ 2 = a ^ (d * 2) := by simp only [u, a, pow_mul]
      _ = a ^ (2 * d) := by rw [Nat.mul_comm]
      _ = (a ^ 2) ^ d := by rw [pow_mul]
      _ = 1 := by rw [ha, one_pow]
  have hsign :
      (reduce F (u : F) (by rw [mem_lattice, hu])) ^ 2 = 1 := by
    unfold reduce
    rw [← map_pow]
    have huSqVal := congrArg Units.val huSq
    change residueMap F
        ((⟨(u : F), (mem_lattice_zero_iff F).1 (by
          rw [mem_lattice, hu])⟩ : ringOfIntegers F) ^ 2) = 1
    rw [show (⟨(u : F), (mem_lattice_zero_iff F).1 (by
      rw [mem_lattice, hu])⟩ : ringOfIntegers F) ^ 2 = 1 by
        apply Subtype.ext
        simpa using huSqVal]
    exact map_one (residueMap F)
  let gammaNorm := hcGammaNorm F K ht piK hgen psiF
  let hgammaNorm := hcGammaNorm_order F K ht hres piK hgen psiF
  have P := tameQuadraticOddPointwise_of_uniformizerPowers
    F K ht hres piK hpiK hgen chiF chiK psiF psiK d hFodd hchi hpsi
      hdegree hchar piF GammaF rfl H R deltaF hdeltaF rfl deltaK
        hdeltaK u hu hdeltaMap gammaNorm hgammaNorm rfl hsign
  dsimp only at P
  have hbetaEq := hcBeta_eq_reduce F chiF psiF hFodd GammaF R
  rw [← hbetaEq] at P
  have hbeta := P.1
  have hs := P.2.1
  let c : ResidueField F := Classical.choose P.2.2
  have hc := Classical.choose_spec P.2.2
  have hlower := hc.1
  have hupper := hc.2
  let normData := hcNormData F K ht hres piK hpiK hgen tau htau
  let psi0 := hcPsi0 F K ht hres piK hgen psiF
  let beta := hcBeta F chiF psiF hFodd GammaF R
  let s := reduce F (u : F) (by rw [mem_lattice, hu])
  refine
    { gammaF := (GammaF : Fˣ)
      gammaF_order := GammaF.property
      parameters := H
      representative := R
      deltaF := deltaF
      deltaF_order := hdeltaF
      deltaK := deltaK
      deltaK_order := hdeltaK
      psi0 := psi0
      psi0_ne_one := hcPsi0_ne_one F K ht hres piK hgen psiF
      beta := beta
      c := c
      s := s
      beta_ne_zero := hbeta
      sign_sq := hs
      normData := normData
      normData_character := rfl
      normData_conductor := rfl
      gammaNorm := gammaNorm
      gammaNorm_order := hgammaNorm
      normResidual := hcNormData_residual F K ht hres piK hpiK hgen
        hdegree hchar tau htau
      normGammaValue := ?_
      residualAdditive := rfl
      lowerPointwise := hlower
      upperPointwise := by
        intro x
        simpa only [tameQuadraticResidueEquiv_apply, psi0, hcPsi0, beta, s, c]
          using hupper x
      stableValue := hcNormData_stableValue F K ht hres piK hpiK hgen
        hdegree hchar tau htau chiF psiF hFodd R }
  exact congrArg Units.val
    (hcNormData_gammaNorm_value F K ht hres piK hpiK hgen psiF tau htau)

/-! ## Complete quadratic tame product -/

section FinalAssembly

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField K) := residueFieldFintype K

/-- The exact upper uniformizer-power denominator `piK^(m+n)` used in the
final product. -/
private def tameQuadraticUpperGamma
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (chi : LocalQuasiCharData K) (psi : LocalAddCharData K) :
    AdmissibleGamma K chi psi :=
  endpointZeroGamma K chi psi (tameQuadraticUpperUniformizer K piK hpiK)
    (by simpa [tameQuadraticUpperUniformizer] using hpiK)

/-- The exact lower norm-uniformizer denominator `N(piK)^(m+n)` used in
every factor over `F`. -/
private def tameQuadraticLowerGamma
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) :
    AdmissibleGamma F chi psi :=
  endpointZeroGamma F chi psi
    (tameQuadraticLowerUniformizer F K piK hpiK)
    (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres)

/-- Simultaneously change the proof-bearing character package and its
admissible denominator, while keeping the actual character fixed. -/
private theorem tameQuadratic_deltaFinite_eq_of_character_eq
    (chi omega : LocalQuasiCharData F)
    (hchar : chi.character = omega.character)
    (psi : LocalAddCharData F)
    (gammaChi : AdmissibleGamma F chi psi)
    (gammaOmega : AdmissibleGamma F omega psi) :
    deltaFinite chi psi gammaChi = deltaFinite omega psi gammaOmega := by
  have hdata : chi = omega := LocalQuasiCharData.ext_character F hchar
  subst omega
  exact (deltaFinite_gamma_independent chi psi gammaChi gammaOmega).symm

/-- The nonidentity pair in the quadratic norm-character product.  The
endpoint branches are direct; the higher branches construct the exact
stationary quotient normal forms and then use the stable-twist theorem in
the direction `tau * chiF`. -/
private theorem firstMain_tameQuadratic_pair
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    deltaFinite chiK psiK
        (tameQuadraticUpperGamma K piK hpiK chiK psiK) *
        deltaFinite
          (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau)
          psiF (tameQuadraticLowerGamma F K hres piK hpiK
            (tameQuadraticNormCharacterData
              F K hres piK hpiK ht hgen tau) psiF) =
      deltaFinite chiF psiF
          (tameQuadraticLowerGamma F K hres piK hpiK chiF psiF) *
        deltaFinite
          (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau)
          psiF (tameQuadraticLowerGamma F K hres piK hpiK
            (tameQuadraticTwistData
              F K hres piK hpiK ht hgen chiF tau) psiF) := by
  let normTau :=
    tameQuadraticNormCharacterData F K hres piK hpiK ht hgen tau
  let twistTau :=
    tameQuadraticTwistData F K hres piK hpiK ht hgen chiF tau
  let GammaK := tameQuadraticUpperGamma K piK hpiK chiK psiK
  let GammaF := tameQuadraticLowerGamma F K hres piK hpiK chiF psiF
  let GammaNorm := tameQuadraticLowerGamma F K hres piK hpiK normTau psiF
  let GammaTwist := tameQuadraticLowerGamma F K hres piK hpiK twistTau psiF
  change deltaFinite chiK psiK GammaK * deltaFinite normTau psiF GammaNorm =
    deltaFinite chiF psiF GammaF * deltaFinite twistTau psiF GammaTwist
  by_cases hchiF0 : chiF.conductor = 0
  · let gammaK0 := endpointZeroGamma K chiK psiK
      (tameQuadraticUpperUniformizer K piK hpiK)
      (by simpa [tameQuadraticUpperUniformizer] using hpiK)
    let gammaF0 := endpointZeroGamma F chiF psiF
      (tameQuadraticLowerUniformizer F K piK hpiK)
      (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres)
    let gammaNorm0 := endpointZeroGamma F normTau psiF
      (tameQuadraticLowerUniformizer F K piK hpiK)
      (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres)
    let gammaTwist0 := endpointZeroGamma F twistTau psiF
      (tameQuadraticLowerUniformizer F K piK hpiK)
      (tameQuadraticLowerUniformizer_isUniformizer F K piK hpiK hres)
    have hp :
        deltaFinite chiK psiK gammaK0 *
            deltaFinite normTau psiF gammaNorm0 =
          deltaFinite chiF psiF gammaF0 *
            deltaFinite twistTau psiF gammaTwist0 := by
      simpa only [endpointZeroDelta, normTau, twistTau, gammaK0, gammaF0,
        gammaNorm0, gammaTwist0] using
        (firstMain_tameQuadratic_conductor_zero F K ht hres piK hpiK hgen
          hdegree chiF chiK psiF psiK hchiF0 hminimal hchi hpsi tau htau)
    calc
      deltaFinite chiK psiK GammaK * deltaFinite normTau psiF GammaNorm =
          deltaFinite chiK psiK gammaK0 *
            deltaFinite normTau psiF gammaNorm0 := by
        rw [deltaFinite_gamma_independent chiK psiK gammaK0 GammaK,
          deltaFinite_gamma_independent normTau psiF gammaNorm0 GammaNorm]
      _ = deltaFinite chiF psiF gammaF0 *
          deltaFinite twistTau psiF gammaTwist0 := hp
      _ = deltaFinite chiF psiF GammaF *
          deltaFinite twistTau psiF GammaTwist := by
        rw [← deltaFinite_gamma_independent chiF psiF gammaF0 GammaF,
          ← deltaFinite_gamma_independent twistTau psiF gammaTwist0 GammaTwist]
  · by_cases hchiF1 : chiF.conductor = 1
    · have hchiK1 : chiK.conductor = 1 :=
        (minimalOrbit_compNorm_conductor_eq_of_leCritical
          F K ht hres piK hpiK hgen chiF hminimal chiK hchi
            (by simpa [hchiF1])).trans hchiF1
      let htwist : twistTau.conductor = 1 := by
        exact minimalOrbit_twist_conductor_eq_of_critical
          F K ht hres piK hpiK hgen chiF hminimal (by simpa using hchiF1)
            tau htau
      let C := tameQuadraticConductorOneResidualComparison_of_intrinsic
        F K ht hres piK hpiK hgen hdegree hchar chiF chiK psiF psiK tau
          hchiF1 hchiK1 htau hchi hpsi htwist
      let gammaF1 := conductorOneGamma chiF hchiF1 psiF C.gammaF C.gammaF_order
      let gammaK1 := conductorOneGamma chiK hchiK1 psiK C.gammaK C.gammaK_order
      let gammaNorm1 := conductorOneGamma normTau
        (tameQuadraticNormCharacterData_conductor_of_ne
          F K hres piK hpiK ht hgen tau htau)
        psiF C.gammaF C.gammaF_order
      let gammaTwist1 := conductorOneGamma twistTau htwist
        psiF C.gammaF C.gammaF_order
      have hp :
          deltaFinite chiK psiK gammaK1 *
              deltaFinite normTau psiF gammaNorm1 =
            deltaFinite chiF psiF gammaF1 *
              deltaFinite twistTau psiF gammaTwist1 := by
        simpa only [normTau, twistTau, gammaF1, gammaK1, gammaNorm1,
          gammaTwist1, htwist, C] using
          (firstMain_tameQuadratic_conductor_one F K ht hres piK hpiK hgen
            hchar chiF chiK psiF psiK tau hchiF1 hchiK1 htau hminimal C)
      calc
        deltaFinite chiK psiK GammaK * deltaFinite normTau psiF GammaNorm =
            deltaFinite chiK psiK gammaK1 *
              deltaFinite normTau psiF gammaNorm1 := by
          rw [deltaFinite_gamma_independent chiK psiK gammaK1 GammaK,
            deltaFinite_gamma_independent normTau psiF gammaNorm1 GammaNorm]
        _ = deltaFinite chiF psiF gammaF1 *
            deltaFinite twistTau psiF gammaTwist1 := hp
        _ = deltaFinite chiF psiF GammaF *
            deltaFinite twistTau psiF GammaTwist := by
          rw [← deltaFinite_gamma_independent chiF psiF gammaF1 GammaF,
            ← deltaFinite_gamma_independent twistTau psiF gammaTwist1 GammaTwist]
    · have hlarge : 1 < chiF.conductor := by omega
      rcases Nat.even_or_odd chiF.conductor with heven | hodd
      · obtain ⟨d, hd⟩ := heven
        have hFeven :
            IsStationaryConductorDecomposition chiF.conductor d 0 :=
          ⟨hlarge, by omega, by omega⟩
        let D := hcHigherEvenNormalForm F K ht hres piK hpiK hgen hdegree
          hchar chiF chiK psiF psiK hchi hpsi tau htau d hFeven
        let gammaFD : AdmissibleGamma F chiF psiF :=
          ⟨D.gammaF, D.gammaF_order⟩
        let upper := (tameQuadraticUpstairsOddPhase
          F K ht hres piK hpiK hgen chiF chiK psiF psiK hFeven
            hchi hpsi hdegree hchar D.gammaF D.gammaF_order D.parameters
              D.representative D.deltaK D.deltaK_order).localPhase
        let gammaNormD := conductorOneGamma D.normData D.normData_conductor
          psiF D.gammaNorm D.gammaNorm_order
        let hcond : D.normData.conductor < chiF.conductor := by
          rw [D.normData_conductor]
          exact hlarge
        let gammaTwistD := stableTwistAdmissibleGamma
          F D.normData chiF psiF hcond gammaFD
        have hp :
            deltaFinite chiK psiK upper.gamma *
                deltaFinite D.normData psiF gammaNormD =
              deltaFinite chiF psiF gammaFD *
                deltaFinite (stableTwistData F D.normData chiF hcond)
                  psiF gammaTwistD := by
          simpa only [D, gammaFD, upper, gammaNormD, hcond, gammaTwistD] using
            (TameQuadraticHigherEvenNormalForm.pair
              F K ht hres piK hpiK hgen chiF chiK psiF psiK hchi hpsi
                hdegree hchar hFeven tau D)
        have hnormChar : normTau.character = D.normData.character := by
          simp only [normTau, tameQuadraticNormCharacterData_character,
            D.normData_character]
        have htwistChar : twistTau.character =
            (stableTwistData F D.normData chiF hcond).character := by
          simp only [twistTau, tameQuadraticTwistData_character,
            stableTwistData_character, D.normData_character]
        calc
          deltaFinite chiK psiK GammaK * deltaFinite normTau psiF GammaNorm =
              deltaFinite chiK psiK upper.gamma *
                deltaFinite D.normData psiF gammaNormD := by
            rw [deltaFinite_gamma_independent chiK psiK upper.gamma GammaK,
              tameQuadratic_deltaFinite_eq_of_character_eq F normTau D.normData
                hnormChar psiF GammaNorm gammaNormD]
          _ = deltaFinite chiF psiF gammaFD *
              deltaFinite (stableTwistData F D.normData chiF hcond)
                psiF gammaTwistD := hp
          _ = deltaFinite chiF psiF GammaF *
              deltaFinite twistTau psiF GammaTwist := by
            rw [← deltaFinite_gamma_independent chiF psiF gammaFD GammaF,
              ← tameQuadratic_deltaFinite_eq_of_character_eq F twistTau
                (stableTwistData F D.normData chiF hcond) htwistChar
                  psiF GammaTwist gammaTwistD]
      · obtain ⟨d, hd⟩ := hodd
        have hFodd :
            IsStationaryConductorDecomposition chiF.conductor d 1 :=
          ⟨hlarge, by omega, by omega⟩
        let D := hcHigherOddNormalForm F K ht hres piK hpiK hgen hdegree
          hchar chiF chiK psiF psiK hchi hpsi tau htau d hFodd
        let gammaFD : AdmissibleGamma F chiF psiF :=
          ⟨D.gammaF, D.gammaF_order⟩
        let upper := (tameQuadraticUpstairsOddPhase
          F K ht hres piK hpiK hgen chiF chiK psiF psiK hFodd
            hchi hpsi hdegree hchar D.gammaF D.gammaF_order D.parameters
              D.representative D.deltaK D.deltaK_order).localPhase
        let gammaNormD := conductorOneGamma D.normData D.normData_conductor
          psiF D.gammaNorm D.gammaNorm_order
        let hcond : D.normData.conductor < chiF.conductor := by
          rw [D.normData_conductor]
          exact hlarge
        let gammaTwistD := stableTwistAdmissibleGamma
          F D.normData chiF psiF hcond gammaFD
        have hp :
            deltaFinite chiK psiK upper.gamma *
                deltaFinite D.normData psiF gammaNormD =
              deltaFinite chiF psiF gammaFD *
                deltaFinite (stableTwistData F D.normData chiF hcond)
                  psiF gammaTwistD := by
          simpa only [D, gammaFD, upper, gammaNormD, hcond, gammaTwistD] using
            (TameQuadraticHigherOddNormalForm.pair
              F K ht hres piK hpiK hgen chiF chiK psiF psiK hchi hpsi
                hdegree hchar hFodd tau D)
        have hnormChar : normTau.character = D.normData.character := by
          simp only [normTau, tameQuadraticNormCharacterData_character,
            D.normData_character]
        have htwistChar : twistTau.character =
            (stableTwistData F D.normData chiF hcond).character := by
          simp only [twistTau, tameQuadraticTwistData_character,
            stableTwistData_character, D.normData_character]
        calc
          deltaFinite chiK psiK GammaK * deltaFinite normTau psiF GammaNorm =
              deltaFinite chiK psiK upper.gamma *
                deltaFinite D.normData psiF gammaNormD := by
            rw [deltaFinite_gamma_independent chiK psiK upper.gamma GammaK,
              tameQuadratic_deltaFinite_eq_of_character_eq F normTau D.normData
                hnormChar psiF GammaNorm gammaNormD]
          _ = deltaFinite chiF psiF gammaFD *
              deltaFinite (stableTwistData F D.normData chiF hcond)
                psiF gammaTwistD := hp
          _ = deltaFinite chiF psiF GammaF *
              deltaFinite twistTau psiF GammaTwist := by
            rw [← deltaFinite_gamma_independent chiF psiF gammaFD GammaF,
              ← tameQuadratic_deltaFinite_eq_of_character_eq F twistTau
                (stableTwistData F D.normData chiF hcond) htwistChar
                  psiF GammaTwist gammaTwistD]

/-- A two-element norm-character group is the identity together with its
unique nonidentity character.  This lemma retains both terms in each full
product and reduces the product identity to the nonidentity pair. -/
private theorem tameQuadratic_ramified_pair_product_assembly
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (upper base : ℂ)
    (normDelta twistDelta : NormCharacter F K → ℂ)
    (hnormOne : normDelta 1 = 1)
    (htwistOne : twistDelta 1 = base)
    (hpair : upper * normDelta tau = base * twistDelta tau) :
    upper *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          normDelta =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        twistDelta := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  have hcard : Fintype.card (NormCharacter F K) = 2 := by
    rw [← Nat.card_eq_fintype_card,
      ramifiedNormCharacter_card F K ht hres piK hpiK hgen, hdegree]
  have hS : (Finset.univ : Finset (NormCharacter F K)) = {1, tau} := by
    have hcardNat : Nat.card (NormCharacter F K) = 2 := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    ext mu
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    by_cases hmu : mu = 1
    · exact Or.inl hmu
    · exact Or.inr
        (((Nat.card_eq_two_iff' (1 : NormCharacter F K)).1 hcardNat).unique
          hmu htau)
  change upper * (Finset.univ : Finset (NormCharacter F K)).prod normDelta =
    (Finset.univ : Finset (NormCharacter F K)).prod twistDelta
  rw [hS]
  simpa [htau, Ne.symm htau, hnormOne, htwistOne] using hpair

/-- **First Main Lemma, tamely ramified quadratic case.**

The full products include the identity norm character.  Conductors zero and
one are discharged without stationary classes.  Above conductor one the two
parities construct exact quotient-level normal forms retaining the chosen
representatives, mapped denominator pair, and pointwise Hasse functions used
by `RamifiedHasseComparison`. -/
theorem firstMain_tameQuadratic
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    deltaFinite chiK psiK
        (tameQuadraticUpperGamma K piK hpiK chiK psiK) *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu => deltaFinite
            (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen mu)
            psiF (tameQuadraticLowerGamma F K hres piK hpiK
              (tameQuadraticNormCharacterData
                F K hres piK hpiK ht hgen mu) psiF)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF mu)
          psiF (tameQuadraticLowerGamma F K hres piK hpiK
            (tameQuadraticTwistData
              F K hres piK hpiK ht hgen chiF mu) psiF)) := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  have hcard : Nat.card (NormCharacter F K) = 2 := by
    rw [ramifiedNormCharacter_card F K ht hres piK hpiK hgen, hdegree]
  let tau := uniqueQuadraticNormCharacter F K hcard
  have htau : tau ≠ 1 := uniqueQuadraticNormCharacter_ne_one F K hcard
  let upper := deltaFinite chiK psiK
    (tameQuadraticUpperGamma K piK hpiK chiK psiK)
  let base := deltaFinite chiF psiF
    (tameQuadraticLowerGamma F K hres piK hpiK chiF psiF)
  let normDelta : NormCharacter F K → ℂ := fun mu => deltaFinite
    (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen mu) psiF
      (tameQuadraticLowerGamma F K hres piK hpiK
        (tameQuadraticNormCharacterData F K hres piK hpiK ht hgen mu) psiF)
  let twistDelta : NormCharacter F K → ℂ := fun mu => deltaFinite
    (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF mu) psiF
      (tameQuadraticLowerGamma F K hres piK hpiK
        (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF mu) psiF)
  have hnormOne : normDelta 1 = 1 := by
    dsimp only [normDelta]
    apply delta_trivial_of_character_eq_one
    exact tameQuadraticNormCharacterData_character
      F K hres piK hpiK ht hgen 1
  have htwistChar :
      (tameQuadraticTwistData
        F K hres piK hpiK ht hgen chiF 1).character = chiF.character := by
    rw [tameQuadraticTwistData_character, NormCharacter.coe_one]
    exact one_mul chiF.character
  have htwistOne : twistDelta 1 = base := by
    dsimp only [twistDelta, base]
    exact tameQuadratic_deltaFinite_eq_of_character_eq F
      (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF 1) chiF
        htwistChar psiF
        (tameQuadraticLowerGamma F K hres piK hpiK
          (tameQuadraticTwistData F K hres piK hpiK ht hgen chiF 1) psiF)
        (tameQuadraticLowerGamma F K hres piK hpiK chiF psiF)
  have hpair : upper * normDelta tau = base * twistDelta tau := by
    exact firstMain_tameQuadratic_pair F K ht hres piK hpiK hgen hdegree
      hchar chiF chiK psiF psiK hminimal hchi hpsi tau htau
  change upper *
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        normDelta =
    (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod twistDelta
  exact tameQuadratic_ramified_pair_product_assembly
    F K ht hres piK hpiK hgen hdegree tau htau upper base
      normDelta twistDelta hnormOne htwistOne hpair

end FinalAssembly

end

end LanglandsFirstMainLemma
