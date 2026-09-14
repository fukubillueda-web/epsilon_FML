import LanglandsFirstMainLemma.Delta.ErrorTerm
import LanglandsFirstMainLemma.Lamprecht.StationaryClassCalculus
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.PullbackConductors

/-!
# Minimal norm-character orbits and their stationary classes

Let `K/F` be ramified cyclic of prime degree, let `t` be its lower break, and
put `T = t + 1`.  Every nontrivial norm character has exact conductor `T`.
This file combines that fact with minimality in the *whole* norm-character
orbit.  It proves that a nontrivial twist of a minimal representative has
exact conductor `max m T`; in particular the possible leading cancellation
when `m = T` cannot occur.

The boundary statement is formulated in the final leading coefficient
quotient.  No representative of a stationary class is selected.  Separate
interfaces below cover the only situation in which cancellation can occur
before minimality is imposed: if the actual product conductor drops and is
still greater than one, its stationary class is first constructed at its own
conductor and minimal depth.  At conductor zero or one there is no stationary
class.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

/-! ## The full orbit and its minimal representative -/

/-- A packaged character is minimal in its whole norm-character orbit.  The
quantifiers range over every norm character, including the trivial one, and
over every exact conductor proof for the corresponding twist. -/
def IsMinimalNormCharacterOrbitRepresentative
    (chi : LocalQuasiCharData F) : Prop :=
  ∀ (mu : NormCharacter F K) (q : ℕ),
    IsMultiplicativeConductor F (mu.1 * chi.character) q →
      chi.conductor ≤ q

/-- The actual least-conductor data for the twist by `mu`.  Its conductor is
constructed as a least unit-filtration depth; it is not supplied by the
caller. -/
noncomputable def ramifiedNormCharacterOrbitTwistData
    (chi : LocalQuasiCharData F) (mu : NormCharacter F K) :
    LocalQuasiCharData F :=
  normCharacterTwistData F K chi (t + 1)
    (ramifiedNormCharacter_trivialOn_break_succ
      F K ht hres pi hpi hgen) mu

@[simp]
theorem ramifiedNormCharacterOrbitTwistData_character
    (chi : LocalQuasiCharData F) (mu : NormCharacter F K) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).character =
        mu.1 * chi.character :=
  normCharacterTwistData_character F K chi (t + 1)
    (ramifiedNormCharacter_trivialOn_break_succ
      F K ht hres pi hpi hgen) mu

/-- Choose a representative of minimal conductor in the whole
norm-character orbit. -/
noncomputable def minimalOrbitRepresentative
    (chi : LocalQuasiCharData F) : LocalQuasiCharData F :=
  minimalConductorTwistData F K chi (t + 1)
    (ramifiedNormCharacter_trivialOn_break_succ
      F K ht hres pi hpi hgen)

@[simp]
theorem minimalOrbitRepresentative_character
    (chi : LocalQuasiCharData F) :
    (minimalOrbitRepresentative F K ht hres pi hpi hgen chi).character =
      (minimalConductorTwist F K chi (t + 1)
          (ramifiedNormCharacter_trivialOn_break_succ
            F K ht hres pi hpi hgen)).1 * chi.character :=
  normCharacterTwistData_character F K chi (t + 1)
    (ramifiedNormCharacter_trivialOn_break_succ
      F K ht hres pi hpi hgen)
    (minimalConductorTwist F K chi (t + 1)
      (ramifiedNormCharacter_trivialOn_break_succ
        F K ht hres pi hpi hgen))

/-- The selected representative retains its exact, least conductor proof. -/
theorem minimalOrbitRepresentative_isConductor
    (chi : LocalQuasiCharData F) :
    IsMultiplicativeConductor F
      (minimalOrbitRepresentative F K ht hres pi hpi hgen chi).character
      (minimalOrbitRepresentative F K ht hres pi hpi hgen chi).conductor :=
  minimalConductorTwist_isConductor F K chi (t + 1)
    (ramifiedNormCharacter_trivialOn_break_succ
      F K ht hres pi hpi hgen)

/-- The selected representative is a member of the original orbit. -/
theorem minimalOrbitRepresentative_mem_orbit
    (chi : LocalQuasiCharData F) :
    ∃ mu : NormCharacter F K,
      (minimalOrbitRepresentative F K ht hres pi hpi hgen chi).character =
        mu.1 * chi.character := by
  exact ⟨minimalConductorTwist F K chi (t + 1)
      (ramifiedNormCharacter_trivialOn_break_succ
        F K ht hres pi hpi hgen),
    minimalOrbitRepresentative_character F K ht hres pi hpi hgen chi⟩

/-- Minimality is genuinely universal over the complete orbit, rather than
over a list of nontrivial characters. -/
theorem minimalOrbitRepresentative_isMinimal
    (chi : LocalQuasiCharData F) :
    IsMinimalNormCharacterOrbitRepresentative F K
      (minimalOrbitRepresentative F K ht hres pi hpi hgen chi) := by
  intro mu q hq
  exact minimalConductorTwist_actualMinimal F K chi (t + 1)
    (ramifiedNormCharacter_trivialOn_break_succ
      F K ht hres pi hpi hgen) mu q hq

/-- Error-term twist invariance permits reduction from `chi` to the selected
minimal representative.  This is only the proved equality
`Err(mu * chi) = Err(chi)`; no First Main identity is assumed. -/
theorem errorTerm_minimalOrbitRepresentative
    [Finite (NormCharacter F K)]
    (DeltaF : LocalConstantFunction F) (DeltaK : LocalConstantFunction K)
    (chi : LocalQuasiCharData F) (psi : ContinuousAddChar F) :
    errorTerm F K DeltaF DeltaK
        (minimalOrbitRepresentative F K ht hres pi hpi hgen chi).character psi =
      errorTerm F K DeltaF DeltaK chi.character psi := by
  simpa only [minimalOrbitRepresentative_character] using
    errorTerm_normCharacter_mul F K DeltaF DeltaK
      (minimalConductorTwist F K chi (t + 1)
        (ramifiedNormCharacter_trivialOn_break_succ
          F K ht hres pi hpi hgen)) chi.character psi

/-! ## Exact conductors throughout a minimal orbit -/

/-- Every nontrivial norm-character twist of a whole-orbit-minimal
representative has the manuscript's exact conductor `max m (t+1)`. -/
theorem minimalOrbit_nontrivialTwist_isConductor
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    IsMultiplicativeConductor F (mu.1 * chi.character)
      (max chi.conductor (t + 1)) := by
  have hmuConductor := ramifiedNormCharacter_conductor
    F K ht hres pi hpi hgen mu hmu
  rcases lt_trichotomy chi.conductor (t + 1) with hbelow | hcritical | habove
  · have hprod := hmuConductor.mul_of_gt chi.isConductor hbelow
    simpa only [Nat.max_eq_right (Nat.le_of_lt hbelow)] using hprod
  · let prod := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu
    have hprod : IsMultiplicativeConductor F (mu.1 * chi.character)
        prod.conductor := by
      simpa only [prod, ramifiedNormCharacterOrbitTwistData_character] using
        prod.isConductor
    have hupper : prod.conductor ≤ t + 1 := by
      have := hmuConductor.mul_conductor_le_max chi.isConductor hprod
      omega
    have hlower : t + 1 ≤ prod.conductor := by
      have := hminimal mu prod.conductor hprod
      omega
    have hprodEq : prod.conductor = t + 1 := Nat.le_antisymm hupper hlower
    rw [hprodEq] at hprod
    simpa only [hcritical, max_self] using hprod
  · have hprod := hmuConductor.mul_of_lt chi.isConductor habove
    simpa only [Nat.max_eq_left (Nat.le_of_lt habove)] using hprod

/-- The constructed actual twist data stores exactly the conductor proved
above. -/
theorem ramifiedNormCharacterOrbitTwistData_conductor_eq
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).conductor =
        max chi.conductor (t + 1) := by
  have htarget := minimalOrbit_nontrivialTwist_isConductor
    F K ht hres pi hpi hgen chi hminimal mu hmu
  have hstored :=
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).isConductor
  have hstored' : IsMultiplicativeConductor F (mu.1 * chi.character)
      (ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen chi mu).conductor := by
    simpa only [ramifiedNormCharacterOrbitTwistData_character] using hstored
  exact (htarget.unique hstored').symm

/-- The piecewise conductor index for the complete orbit.  It explicitly
retains the trivial character. -/
noncomputable def minimalOrbitTwistConductor
    (chi : LocalQuasiCharData F) (mu : NormCharacter F K) : ℕ := by
  classical
  exact if mu = 1 then chi.conductor else max chi.conductor (t + 1)

/-- The trivial norm character remains in the orbit and leaves the conductor
unchanged; every nontrivial element has the `max` conductor. -/
theorem ramifiedNormCharacterOrbitTwistData_conductor_eq_ite
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (mu : NormCharacter F K) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).conductor =
      minimalOrbitTwistConductor (t := t) F K chi mu := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    have hstored :=
      (ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen chi 1).isConductor
    have hstored' : IsMultiplicativeConductor F chi.character
        (ramifiedNormCharacterOrbitTwistData
          F K ht hres pi hpi hgen chi 1).conductor := by
      have hchar :
          (ramifiedNormCharacterOrbitTwistData
            F K ht hres pi hpi hgen chi 1).character = chi.character := by
        rw [ramifiedNormCharacterOrbitTwistData_character]
        apply ContinuousMonoidHom.ext
        intro x
        simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
          ContinuousQuasiChar.one_apply, one_mul]
      rw [← hchar]
      exact hstored
    simp only [minimalOrbitTwistConductor]
    exact hstored'.unique chi.isConductor
  · rw [minimalOrbitTwistConductor, if_neg hmu]
    exact ramifiedNormCharacterOrbitTwistData_conductor_eq
      F K ht hres pi hpi hgen chi hminimal mu hmu

/-- Below the critical norm-character conductor, every nontrivial twist has
strictly larger conductor `t+1`. -/
theorem minimalOrbit_twist_conductor_eq_of_lt
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hbelow : chi.conductor < t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).conductor = t + 1 := by
  rw [ramifiedNormCharacterOrbitTwistData_conductor_eq
    F K ht hres pi hpi hgen chi hminimal mu hmu,
    Nat.max_eq_right (Nat.le_of_lt hbelow)]

/-- At the critical boundary, whole-orbit minimality prevents conductor
drop. -/
theorem minimalOrbit_twist_conductor_eq_of_critical
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).conductor = t + 1 := by
  rw [ramifiedNormCharacterOrbitTwistData_conductor_eq
    F K ht hres pi hpi hgen chi hminimal mu hmu, hcritical, max_self]

/-- Above the critical norm-character conductor, a nontrivial twist has the
same conductor as the minimal representative. -/
theorem minimalOrbit_twist_conductor_eq_of_gt
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (habove : t + 1 < chi.conductor)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).conductor = chi.conductor := by
  rw [ramifiedNormCharacterOrbitTwistData_conductor_eq
    F K ht hres pi hpi hgen chi hminimal mu hmu,
    Nat.max_eq_left (Nat.le_of_lt habove)]

/-- The manuscript's statement for every nonidentity power of a chosen norm
character is the preceding theorem applied to that power. -/
theorem minimalOrbit_nontrivialPower_isConductor
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (tau : NormCharacter F K) (j : ℕ) (hj : tau ^ j ≠ 1) :
    IsMultiplicativeConductor F ((tau ^ j).1 * chi.character)
      (max chi.conductor (t + 1)) :=
  minimalOrbit_nontrivialTwist_isConductor
    F K ht hres pi hpi hgen chi hminimal (tau ^ j) hj

/-! ## Exact norm-pullback conductors for the chosen representative -/

/-- In the below and critical ranges, norm pullback preserves the exact
conductor of a whole-orbit-minimal representative. -/
theorem minimalOrbit_compNorm_conductor_eq_of_leCritical
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : chiF.conductor ≤ t + 1) :
    chiK.conductor = chiF.conductor :=
  chiF.conductor_compNorm_eq_of_minimalOrbit
    F K ht hres pi hpi hgen chiK hcomp hm hminimal

/-- At or above the critical conductor, the exact pullback formula includes
the minimal critical endpoint. -/
theorem minimalOrbit_compNorm_conductor_eq_atOrAboveCritical
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : t + 1 ≤ chiF.conductor) :
    (chiK.conductor : ℤ) =
      (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) -
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) :=
  chiF.conductor_compNorm_eq_atOrAboveCritical_of_minimalOrbit
    F K ht hres pi hpi hgen chiK hcomp hm hminimal

/-- The corresponding exact denominator-valuation identity transports the
multiplicative and additive conductor together. -/
theorem minimalOrbit_compNorm_add_compTrace_conductor_eq
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : t + 1 ≤ chiF.conductor) :
    (chiK.conductor : ℤ) + psiK.conductor =
      (Module.finrank F K : ℤ) *
        ((chiF.conductor : ℤ) + psiF.conductor) :=
  compNorm_add_compTrace_conductor_eq_atOrAboveCritical_of_minimalOrbit
    F K ht hres pi hpi hgen chiF chiK psiF psiK
      hcomp hpsi hm hminimal

/-! ## Complete finite-orbit and cyclic-index interfaces -/

/-- The finite orbit used by the parameter tables is the complete ramified
norm-character group. -/
noncomputable def minimalOrbitNormCharacterFinset :
    Finset (NormCharacter F K) :=
  ramifiedNormCharacterFinset F K ht hres pi hpi hgen

@[simp]
theorem one_mem_minimalOrbitNormCharacterFinset :
    (1 : NormCharacter F K) ∈
      minimalOrbitNormCharacterFinset F K ht hres pi hpi hgen := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  simp [minimalOrbitNormCharacterFinset, ramifiedNormCharacterFinset,
    normCharacterFinset]

/-- The cyclic enumeration retains its identity index, which maps to the
trivial norm character. -/
@[simp]
theorem minimalOrbitZMod_zero_eq_one :
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K))) = 1 :=
  ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen

/-- Every nonidentity cyclic index gives the exact nontrivial-twist
conductor. -/
theorem minimalOrbitZMod_twist_conductor_eq
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (j : Multiplicative (ZMod (Module.finrank F K))) (hj : j ≠ 1) :
    (ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chi
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen j)).conductor =
        max chi.conductor (t + 1) := by
  apply ramifiedNormCharacterOrbitTwistData_conductor_eq
    F K ht hres pi hpi hgen chi hminimal
  exact (ramifiedNormCharacterZModEquiv_ne_one_iff
    F K ht hres pi hpi hgen j).2 hj

/-- Reindex any full finite-orbit product by the complete cyclic index set;
the identity/trivial factor is retained. -/
theorem minimalOrbit_fullProduct_eq_zmodProduct
    {A : Type*} [CommMonoid A] (f : NormCharacter F K → A) :
    (minimalOrbitNormCharacterFinset F K ht hres pi hpi hgen).prod f =
      (primeDegreeZModFinset F K).prod
        (fun j ↦ f
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen j)) := by
  exact ramifiedNormCharacterProduct_eq_zmodProduct
    F K ht hres pi hpi hgen f

/-! ## The critical leading quotient class -/

/-- At `m = t+1 > 1`, the sum of the stationary quotient classes of a
nontrivial norm character and a whole-orbit-minimal representative has
nonzero projection to the last possibly nontrivial layer.  This is the
representative-free form of `b + j*a` having nonvanishing leading class. -/
theorem minimalOrbit_stationary
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryLeadingClassProjection F M hr
      (stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psi M hr Gamma hGamma +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chi.character (t + 1) (by
            simpa only [hcritical] using chi.isConductor))
          psi M hr Gamma hGamma) ≠ 0 := by
  have hmuConductor := ramifiedNormCharacter_conductor
    F K ht hres pi hpi hgen mu hmu
  have hchiConductor : IsMultiplicativeConductor F chi.character (t + 1) := by
    simpa only [hcritical] using chi.isConductor
  have hprodConductor : IsMultiplicativeConductor F
      (mu.1 * chi.character) (t + 1) := by
    have h := minimalOrbit_nontrivialTwist_isConductor
      F K ht hres pi hpi hgen chi hminimal mu hmu
    simpa only [hcritical, max_self] using h
  intro hzero
  have hdrop :=
    (stationaryLeadingClassCancellation_iff F (t + 1) (t + 1)
      hmuConductor hchiConductor hprodConductor psi M hr Gamma hGamma).2 hzero
  exact (Nat.lt_irrefl (t + 1)) hdrop

/-- On a critical common layer, the stationary quotient class of a
nonidentity natural power is exactly the corresponding multiple of the
generator's class.  This is an equality of quotient classes, not of chosen
field representatives. -/
theorem normCharacterPower_stationaryClass_eq_nsmul
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (j : ℕ) (hj : tau ^ j ≠ 1)
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F (tau ^ j).1 (t + 1)
          (ramifiedNormCharacter_conductor
            F K ht hres pi hpi hgen (tau ^ j) hj))
        psi M hr Gamma hGamma =
      j • stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor
            F K ht hres pi hpi hgen tau htau))
        psi M hr Gamma hGamma := by
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let powerData := quasiCharDataOfIsConductor F (tau ^ j).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen (tau ^ j) hj)
  let s := stationaryNumeratorClass F tauData psi M hr Gamma hGamma
  have hs : IsStationaryRestrictionClass F tau.1 psi M hr.pos
      hr.le_conductor Gamma s :=
    stationaryNumeratorClass_isRestriction F tauData
      psi M hr Gamma hGamma
  have hz := IsStationaryRestrictionClass.zpow F psi M hr.pos
    hr.le_conductor Gamma hGamma s hs (j : ℤ)
  have hpowChar : tau.1 ^ (j : ℤ) = (tau ^ j).1 := by
    simpa using
      (NormCharacter.coe_pow (F := F) (K := K) tau j).symm
  have hsmul : (j : ℤ) • s = j • s := by simp
  rw [hpowChar, hsmul] at hz
  have hz' : IsStationaryNumeratorClass F powerData psi M hr Gamma (j • s) := by
    exact hz
  change stationaryNumeratorClass F powerData psi M hr Gamma hGamma = j • s
  exact (stationaryNumeratorClass_unique F powerData psi M hr Gamma hGamma
    (j • s) hz').symm

/-- Power-indexed form of the leading-class theorem.  The first summand is
the honest quotient multiple `j` times the class of `tau`. -/
theorem minimalOrbit_power_stationary
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hcritical : chi.conductor = t + 1)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (j : ℕ) (hj : tau ^ j ≠ 1)
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryLeadingClassProjection F M hr
      (j • stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen tau htau))
          psi M hr Gamma hGamma +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chi.character (t + 1) (by
            simpa only [hcritical] using chi.isConductor))
          psi M hr Gamma hGamma) ≠ 0 := by
  have hnonzero := minimalOrbit_stationary F K ht hres pi hpi hgen
    chi hminimal hcritical (tau ^ j) hj psi M hr Gamma hGamma
  rw [normCharacterPower_stationaryClass_eq_nsmul
    F K ht hres pi hpi hgen tau htau j hj psi M hr Gamma hGamma] at hnonzero
  exact hnonzero

/-- Chosen representatives satisfy the manuscript's ideal-membership
noncancellation statement.  Both representatives are explicit arguments;
the theorem does not promote either quotient class to a canonical element
of `F`. -/
theorem minimalOrbit_stationary_representatives
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (a b : lattice F (M - ((t + 1 : ℕ) : ℤ)))
    (ha : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor M) a =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F mu.1 (t + 1)
          (ramifiedNormCharacter_conductor
            F K ht hres pi hpi hgen mu hmu))
        psi M hr Gamma hGamma)
    (hb : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor M) b =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F chi.character (t + 1) (by
          simpa only [hcritical] using chi.isConductor))
        psi M hr Gamma hGamma) :
    (a : F) + (b : F) ∉ lattice F (M - ((t + 1 : ℕ) : ℤ) + 1) := by
  have hmuConductor := ramifiedNormCharacter_conductor
    F K ht hres pi hpi hgen mu hmu
  have hchiConductor : IsMultiplicativeConductor F chi.character (t + 1) := by
    simpa only [hcritical] using chi.isConductor
  have hprodConductor : IsMultiplicativeConductor F
      (mu.1 * chi.character) (t + 1) := by
    have h := minimalOrbit_nontrivialTwist_isConductor
      F K ht hres pi hpi hgen chi hminimal mu hmu
    simpa only [hcritical, max_self] using h
  intro hcancel
  have hdrop :=
    (stationaryLeadingCancellation_iff F (t + 1) (t + 1)
      hmuConductor hchiConductor hprodConductor psi M hr Gamma hGamma
      a b ha hb).2 hcancel
  exact (Nat.lt_irrefl (t + 1)) hdrop

/-! ## The only pre-minimality drop, reconstructed at its actual depth -/

/-- Before minimality is imposed, a product of two critical-conductor
characters can only retain conductor `t+1` or drop below it. -/
theorem criticalNormCharacterTwist_conductor_eq_or_drop
    (chi : LocalQuasiCharData F) (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (prod : LocalQuasiCharData F)
    (hprod : prod.character = mu.1 * chi.character) :
    prod.conductor = t + 1 ∨ prod.conductor < t + 1 := by
  have hmuConductor := ramifiedNormCharacter_conductor
    F K ht hres pi hpi hgen mu hmu
  have hchiConductor : IsMultiplicativeConductor F chi.character (t + 1) := by
    simpa only [hcritical] using chi.isConductor
  have hprodConductor : IsMultiplicativeConductor F
      (mu.1 * chi.character) prod.conductor := by
    rw [← hprod]
    exact prod.isConductor
  have hle := hmuConductor.mul_conductor_le_max
    hchiConductor hprodConductor
  have hle' : prod.conductor ≤ t + 1 := by
    simpa only [max_self] using hle
  exact hle'.eq_or_lt

/-- If a critical product really drops to an actual conductor `q' > 1`,
construct its stationary class at `q'` and `ceil(q'/2)` first, then compare
only its restriction with the two old critical classes. -/
theorem criticalNormCharacterTwist_stationaryClass_afterDrop
    (chi : LocalQuasiCharData F) (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (q' : ℕ)
    (hprod : IsMultiplicativeConductor F (mu.1 * chi.character) q')
    (hdrop : q' < t + 1) (hq' : 1 < q')
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    droppedStationaryClassRestriction F
        (quasiCharDataOfIsConductor F (mu.1 * chi.character) q' hprod)
        psi M hr hdrop hq' Gamma hGamma =
      stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psi M hr Gamma hGamma +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chi.character (t + 1) (by
            simpa only [hcritical] using chi.isConductor))
          psi M hr Gamma hGamma := by
  apply stationaryClass_afterConductorDrop F (t + 1) q'
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
    (by simpa only [hcritical] using chi.isConductor)
    hprod hdrop hq' psi M hr Gamma hGamma

/-- If the actual product conductor is zero or one, there is no admissible
stationary depth and no stationary object is constructed. -/
theorem normCharacterTwist_noStationaryClass_of_endpoint
    (prod : LocalQuasiCharData F) (hprod : prod.conductor ≤ 1) :
    ¬ ∃ r : ℕ, IsLamprechtStationaryDepth prod.conductor r :=
  noStationaryClass_of_conductor_le_one hprod

end

end LanglandsFirstMainLemma
