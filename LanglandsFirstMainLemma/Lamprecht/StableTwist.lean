import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.StationaryClassCalculus
import LanglandsFirstMainLemma.Delta.Elementary

/-!
# Exact stable twists

This file formalizes Lemma `lem:stable-twist-new`.  If the exact conductor of
`theta` is `2 * d + epsilon > 1`, where `epsilon` is zero or one, and the
conductor of `nu` is at most `d`, then `nu * theta` has the same conductor and
the same stationary numerator class at the minimal Lamprecht depth
`d + epsilon`.  The stable-twist factor is evaluated on an arbitrary
representative of that quotient class; no representative is selected by the
construction.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem stableTwist_conductor_lt
    (nu theta : LocalQuasiCharData F) (d epsilon : ℕ)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) (hnu : nu.conductor ≤ d) :
    nu.conductor < theta.conductor := by
  omega

/-- The proof-bearing product datum used in the stable range.  Its stored
conductor is definitionally the conductor of `theta`. -/
abbrev stableTwistData (nu theta : LocalQuasiCharData F)
    (hcond : nu.conductor < theta.conductor) : LocalQuasiCharData F where
  character := nu.character * theta.character
  conductor := theta.conductor
  isConductor := nu.isConductor.mul_of_lt theta.isConductor hcond

@[simp]
theorem stableTwistData_character
    (nu theta : LocalQuasiCharData F)
    (hcond : nu.conductor < theta.conductor) :
    (stableTwistData F nu theta hcond).character =
      nu.character * theta.character :=
  rfl

@[simp]
theorem stableTwistData_conductor
    (nu theta : LocalQuasiCharData F)
    (hcond : nu.conductor < theta.conductor) :
    (stableTwistData F nu theta hcond).conductor = theta.conductor :=
  rfl

/-- For `q = 2d+epsilon`, with `epsilon` equal to zero or one, the minimal
stationary depth is exactly `d+epsilon`.  This single statement keeps the
even depth `d` and odd depth `d+1` separate without changing either bound. -/
theorem stableTwist_stationaryDepth
    (theta : LocalQuasiCharData F) (d epsilon : ℕ)
    (hepsilon : epsilon ≤ 1)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) :
    IsLamprechtStationaryDepth theta.conductor (d + epsilon) := by
  refine ⟨hlarge, ?_, ?_⟩ <;> omega

/-- A low-conductor twist is trivial on the minimal stationary unit layer. -/
theorem stableTwist_trivialOnStationaryLayer
    (nu : LocalQuasiCharData F) (d epsilon : ℕ)
    (hnu : nu.conductor ≤ d) :
    QuasiCharTrivialOnUnitFiltration F nu.character (d + epsilon) :=
  nu.isConductor.trivialOnUnitFiltration_iff.2
    (hnu.trans (Nat.le_add_right d epsilon))

/-- The stationary quotient class of the twisted datum is the stationary
class of `theta`.  The proof uses the same denominator and quantifies over
every representative of the original class. -/
theorem stationaryNumeratorClass_stableTwist
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) (hnu : nu.conductor ≤ d)
    (M : ℤ) (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    let hcond := stableTwist_conductor_lt F nu theta d epsilon htheta hlarge hnu
    let hr := stableTwist_stationaryDepth F theta d epsilon
      hepsilon htheta hlarge
    stationaryNumeratorClass F (stableTwistData F nu theta hcond)
        psi M hr Gamma hGamma =
      stationaryNumeratorClass F theta psi M hr Gamma hGamma := by
  dsimp only
  let hcond := stableTwist_conductor_lt F nu theta d epsilon htheta hlarge hnu
  let hr := stableTwist_stationaryDepth F theta d epsilon
    hepsilon htheta hlarge
  symm
  apply stationaryNumeratorClass_unique F (stableTwistData F nu theta hcond)
    psi M hr Gamma hGamma
  intro c hc x
  have hthetaLinear := stationaryNumeratorClass_linearization
    F theta psi M hr Gamma hGamma c hc x
  have hnuOne := stableTwist_trivialOnStationaryLayer
    F nu d epsilon hnu
      (positiveUnitOfLattice F hr.pos x)
      (positiveUnitOfLattice F hr.pos x).property
  rw [stableTwistData_character, ContinuousQuasiChar.mul_apply, hnuOne, one_mul]
  exact hthetaLinear

/-- Bundle an arbitrary representative of the stationary numerator class as
a field unit.  Exact order, rather than an unrecorded choice, proves that the
representative is nonzero. -/
def stableStationaryRepresentativeUnit
    (theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth theta.conductor r)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        hr Gamma Gamma.property) : Fˣ :=
  Units.mk0 (c : F) (by
    apply (ord_ne_top_iff F).1
    rw [stationaryNumeratorClass_representative_ord
      F theta psi (theta.conductor : ℤ) hr Gamma Gamma.property c hc]
    simp)

@[simp]
theorem stableStationaryRepresentativeUnit_coe
    (theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth theta.conductor r)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        hr Gamma Gamma.property) :
    ((stableStationaryRepresentativeUnit F theta psi hr Gamma c hc : Fˣ) : F) =
      (c : F) :=
  rfl

/-- The manuscript's value `nu(Gamma/c)` is independent of the arbitrary
representative `c` of the stationary quotient class.  The denominator depth
is exactly `d`, in both the even and odd branches. -/
theorem stableTwist_characterFactor_representative_independent
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) (hnu : nu.conductor ≤ d)
    (Gamma : AdmissibleGamma F theta psi)
    (c c' : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge).int_le_conductor
          (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma Gamma.property)
    (hc' : latticeQuotientMk F
        (sub_le_sub_left
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge).int_le_conductor
          (theta.conductor : ℤ)) c' =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma Gamma.property) :
    nu.character ((Gamma : Fˣ) /
        stableStationaryRepresentativeUnit F theta psi
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge) Gamma c hc) =
      nu.character ((Gamma : Fˣ) /
        stableStationaryRepresentativeUnit F theta psi
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge) Gamma c' hc') := by
  let hr := stableTwist_stationaryDepth F theta d epsilon
    hepsilon htheta hlarge
  let beta := stableStationaryRepresentativeUnit F theta psi hr Gamma c hc
  let beta' := stableStationaryRepresentativeUnit F theta psi hr Gamma c' hc'
  have hclasses : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ)) c =
      latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ)) c' :=
    hc.trans hc'.symm
  have hcongRaw := (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
    (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ))).1 hclasses
  have hdepth : (theta.conductor : ℤ) - (d + epsilon : ℕ) = (d : ℤ) := by
    omega
  rw [hdepth] at hcongRaw
  have hcong : CongruentAtDepth (d : ℤ) (beta' : F) (beta : F) := by
    apply (congruentAtDepth_iff_sub_mem_lattice F (d : ℤ)
      (beta' : F) (beta : F)).2
    have hrawMem := (congruentAtDepth_iff_sub_mem_lattice F (d : ℤ)
      (c : F) (c' : F)).1 hcongRaw
    have hneg := (lattice F (d : ℤ)).neg_mem hrawMem
    simpa only [beta, beta', stableStationaryRepresentativeUnit_coe,
      neg_sub] using hneg
  have hbeta0 : ord F (beta : F) = 0 := by
    dsimp only [beta]
    rw [stableStationaryRepresentativeUnit_coe,
      stationaryNumeratorClass_representative_ord
        F theta psi (theta.conductor : ℤ) hr Gamma Gamma.property c hc]
    simp
  have hbeta'0 : ord F (beta' : F) = 0 := by
    dsimp only [beta']
    rw [stableStationaryRepresentativeUnit_coe,
      stationaryNumeratorClass_representative_ord
        F theta psi (theta.conductor : ℤ) hr Gamma Gamma.property c' hc']
    simp
  have hratio : beta' / beta ∈ unitFiltration F d :=
    (div_mem_unitFiltration_iff_congruentAtDepth F d beta' beta
      (unitFiltration_le_unitGroup F 0
        ((mem_unitFiltration_zero F beta').2 hbeta'0))
      (unitFiltration_le_unitGroup F 0
        ((mem_unitFiltration_zero F beta).2 hbeta0))).2 hcong
  have hnuRatio : nu.character (beta' / beta) = 1 :=
    nu.isConductor.trivial _ (unitFiltration_antitone F hnu hratio)
  have hnuBeta : nu.character beta' = nu.character beta := by
    apply div_eq_one.mp
    rw [← map_div]
    exact hnuRatio
  change nu.character ((Gamma : Fˣ) / beta) =
    nu.character ((Gamma : Fˣ) / beta')
  rw [map_div, map_div, hnuBeta]

/-! ## Stationary localization of the finite Gauss sum -/

/-- Inclusion of a positive unit layer in the zeroth unit layer. -/
private def unitFiltrationToZero (r : ℕ) :
    unitFiltration F r →* unitFiltration F 0 where
  toFun u := ⟨(u : Fˣ), unitFiltration_antitone F (Nat.zero_le r) u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A class in `U^r/U^q`, viewed in `U^0/U^q`. -/
private noncomputable def stableTwistDeepClassInFull
    {q r : ℕ} (hrq : r ≤ q) :
    UnitFiltrationQuotient F r q hrq →*
      UnitFiltrationQuotient F 0 q (Nat.zero_le q) :=
  QuotientGroup.lift (unitFiltrationInside F hrq)
    ((unitFiltrationQuotientMk F (Nat.zero_le q)).comp
      (unitFiltrationToZero F r)) (by
        intro u hu
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
          unitFiltrationQuotientMk_eq_one_iff]
        exact (mem_unitFiltrationInside F hrq u).1 hu)

@[simp]
private theorem stableTwistDeepClassInFull_mk
    {q r : ℕ} (hrq : r ≤ q) (u : unitFiltration F r) :
    stableTwistDeepClassInFull F hrq
        (unitFiltrationQuotientMk F hrq u) =
      unitFiltrationQuotientMk F (Nat.zero_le q)
        (unitFiltrationToZero F r u) :=
  rfl

/-- A character of conductor at most `q`, descended to `U^0/U^q`. -/
private noncomputable def stableTwistLowCharacter
    (nu : LocalQuasiCharData F) (q : ℕ) (hnuq : nu.conductor ≤ q) :
    UnitFiltrationQuotient F 0 q (Nat.zero_le q) →* ℂˣ :=
  QuotientGroup.lift (unitFiltrationInside F (Nat.zero_le q))
    (nu.character.toMonoidHom.comp (unitFiltration F 0).subtype) (by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact nu.isConductor.trivial _ (unitFiltration_antitone F hnuq
        ((mem_unitFiltrationInside F (Nat.zero_le q) u).1 hu)))

@[simp]
private theorem stableTwistLowCharacter_mk
    (nu : LocalQuasiCharData F) (q : ℕ) (hnuq : nu.conductor ≤ q)
    (u : unitFiltration F 0) :
    stableTwistLowCharacter F nu q hnuq
        (unitFiltrationQuotientMk F (Nat.zero_le q) u) =
      nu.character (u : Fˣ) :=
  rfl

/-- The coefficient `[u-c]` controlling the orbit sum.  Its denominator is
`p^(q-r)`, exactly `p^d` for the stable-twist depth. -/
private noncomputable def stableTwistCoefficientClass
    {q r : ℕ} (hrq : r ≤ q)
    (c : lattice F ((q : ℤ) - (q : ℤ))) :
    UnitFiltrationQuotient F 0 q (Nat.zero_le q) →
      LamprechtCoefficientQuotient F (q : ℤ) (q : ℤ) (r : ℤ)
        (by exact_mod_cast hrq) :=
  unitFiltrationQuotientLift F (Nat.zero_le q)
    (fun u ↦ latticeQuotientMk F
      (sub_le_sub_left (by exact_mod_cast hrq) (q : ℤ))
      ⟨((u : Fˣ) : F) - (c : F), by
        have hu0 : ((u : Fˣ) : F) ∈ lattice F 0 := by
          rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
          simp
        have huq : ((u : Fˣ) : F) ∈ lattice F ((q : ℤ) - (q : ℤ)) := by
          simpa using hu0
        exact sub_mem huq c.property⟩)
    (by
      intro u v huv
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        (sub_le_sub_left (by exact_mod_cast hrq) (q : ℤ))).2
      apply (congruentAtDepth_iff_sub_mem_lattice F
        ((q : ℤ) - (r : ℤ))
        (((u : Fˣ) : F) - (c : F))
        (((v : Fˣ) : F) - (c : F))).2
      have huvMem := (congruentAtDepth_iff_sub_mem_lattice F (q : ℤ)
        ((u : Fˣ) : F) ((v : Fˣ) : F)).1 huv
      apply lattice_antitone F (by omega : (q : ℤ) - (r : ℤ) ≤ q)
      simpa only [sub_sub_sub_cancel_right] using huvMem)

@[simp]
private theorem stableTwistCoefficientClass_mk
    {q r : ℕ} (hrq : r ≤ q)
    (c : lattice F ((q : ℤ) - (q : ℤ)))
    (u : unitFiltration F 0) :
    stableTwistCoefficientClass F hrq c
        (unitFiltrationQuotientMk F (Nat.zero_le q) u) =
      latticeQuotientMk F
        (sub_le_sub_left (by exact_mod_cast hrq) (q : ℤ))
        ⟨((u : Fˣ) : F) - (c : F), by
          have hu0 : ((u : Fˣ) : F) ∈ lattice F 0 := by
            rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
            simp
          have huq : ((u : Fˣ) : F) ∈ lattice F ((q : ℤ) - (q : ℤ)) := by
            simpa using hu0
          exact sub_mem huq c.property⟩ :=
  rfl

/-- Multiplication by a deep unit changes the Gauss summand by the additive
character paired with `[u-c]`.  The sign here is the manuscript's positive
stationary sign; the inverse occurs only in the multiplicative-character
factor of the Gauss summand. -/
private theorem finiteGaussSummand_stationaryOrbit
    (theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth theta.conductor r)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        hr Gamma Gamma.property)
    (a : UnitFiltrationQuotient F r theta.conductor hr.le_conductor)
    (u : UnitFiltrationQuotient F 0 theta.conductor
      (Nat.zero_le theta.conductor)) :
    finiteGaussSummand theta psi Gamma
        (stableTwistDeepClassInFull F hr.le_conductor a * u) =
      (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
        (stableTwistCoefficientClass F hr.le_conductor c u))
          ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
            hr.le_conductor hr.half_le a).toAdd) *
        finiteGaussSummand theta psi Gamma u := by
  obtain ⟨a, rfl⟩ := unitFiltrationQuotientMk_surjective F hr.le_conductor a
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le theta.conductor) u
  rw [stableTwistDeepClassInFull_mk, ← unitFiltrationQuotientMk_mul,
    finiteGaussSummand_mk, finiteGaussSummand_mk]
  change finiteGaussSummandRepresentative theta psi Gamma
      (unitFiltrationToZero F r a * u) =
    (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (stableTwistCoefficientClass F hr.le_conductor c
        (unitFiltrationQuotientMk F (Nat.zero_le theta.conductor) u)))
        (latticeQuotientMk F hr.int_le_conductor
          (positiveUnitDisplacement F hr.pos a)) *
      finiteGaussSummandRepresentative theta psi Gamma u
  rw [stableTwistCoefficientClass_mk,
    lamprechtPairingLeft_apply, lamprechtPairing_mk_mk]
  let x := positiveUnitDisplacement F hr.pos a
  have htheta := stationaryNumeratorClass_linearization
    F theta psi (theta.conductor : ℤ) hr Gamma Gamma.property c hc x
  have hunit : (positiveUnitOfLattice F hr.pos x : Fˣ) = (a : Fˣ) := by
    apply Units.ext
    simp [x]
  rw [hunit] at htheta
  have hthetaC := congrArg (Units.val : Units ℂ → ℂ) htheta
  have hthetaC' : (theta.character (a : Fˣ) : ℂ) =
      (psi.character ((c : F) * (((a : Fˣ) : F) - 1) /
        ((Gamma : Fˣ) : F)) : ℂ) := by
    simpa only [x, coe_positiveUnitDisplacement] using hthetaC
  have hthetaMul : (theta.character ((a : Fˣ) * (u : Fˣ)) : ℂ) =
      (theta.character (a : Fˣ) : ℂ) *
        (theta.character (u : Fˣ) : ℂ) :=
    congrArg Units.val (map_mul theta.character (a : Fˣ) (u : Fˣ))
  have harg :
      (((a : Fˣ) : F) * ((u : Fˣ) : F)) / ((Gamma : Fˣ) : F) =
        (((u : Fˣ) : F) - (c : F)) *
              (((a : Fˣ) : F) - 1) / ((Gamma : Fˣ) : F) +
          (c : F) * (((a : Fˣ) : F) - 1) / ((Gamma : Fˣ) : F) +
          ((u : Fˣ) : F) / ((Gamma : Fˣ) : F) := by
    field_simp [AdmissibleGamma.coe_ne_zero Gamma]
    ring
  rw [finiteGaussSummandRepresentative, finiteGaussSummandRepresentative]
  change (psi.character
        ((((a : Fˣ) : F) * ((u : Fˣ) : F)) / ((Gamma : Fˣ) : F)) : ℂ) *
      (theta.character ((a : Fˣ) * (u : Fˣ)) : ℂ)⁻¹ =
    (psi.character ((((u : Fˣ) : F) - (c : F)) *
        (((a : Fˣ) : F) - 1) / ((Gamma : Fˣ) : F)) : ℂ) *
      ((psi.character (((u : Fˣ) : F) / ((Gamma : Fˣ) : F)) : ℂ) *
        (theta.character (u : Fˣ) : ℂ)⁻¹)
  rw [hthetaMul, hthetaC']
  rw [harg, ContinuousAddChar.map_add_eq_mul,
    ContinuousAddChar.map_add_eq_mul]
  have hc0 : (psi.character ((c : F) * (((a : Fˣ) : F) - 1) /
      ((Gamma : Fˣ) : F)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  field_simp
  push_cast
  ring

/-- The low-conductor character is constant on every deep stationary orbit. -/
private theorem stableTwistLowCharacter_deep_mul
    (nu : LocalQuasiCharData F) {q r : ℕ} (hrq : r ≤ q)
    (hnur : nu.conductor ≤ r) (hnuq : nu.conductor ≤ q)
    (a : UnitFiltrationQuotient F r q hrq)
    (u : UnitFiltrationQuotient F 0 q (Nat.zero_le q)) :
    stableTwistLowCharacter F nu q hnuq
        (stableTwistDeepClassInFull F hrq a * u) =
      stableTwistLowCharacter F nu q hnuq u := by
  obtain ⟨a, rfl⟩ := unitFiltrationQuotientMk_surjective F hrq a
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F (Nat.zero_le q) u
  rw [stableTwistDeepClassInFull_mk, map_mul,
    stableTwistLowCharacter_mk, stableTwistLowCharacter_mk]
  change nu.character (a : Fˣ) * nu.character (u : Fˣ) =
    nu.character (u : Fˣ)
  have hnua : nu.character (a : Fˣ) = 1 :=
    nu.isConductor.trivial _ (unitFiltration_antitone F hnur a.property)
  rw [hnua, one_mul]

/-- If the orbit coefficient `[u-c]` vanishes, then the low-conductor
character takes the stationary value `nu(c)` at `u`. -/
private theorem stableTwistLowCharacter_eq_stationary_of_coefficient_eq_zero
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) (hnu : nu.conductor ≤ d)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge).int_le_conductor
          (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma Gamma.property)
    (u : UnitFiltrationQuotient F 0 theta.conductor
      (Nat.zero_le theta.conductor))
    (hu : stableTwistCoefficientClass F
      (stableTwist_stationaryDepth F theta d epsilon
        hepsilon htheta hlarge).le_conductor c u = 0) :
    stableTwistLowCharacter F nu theta.conductor
        (Nat.le_of_lt (stableTwist_conductor_lt F nu theta d epsilon
          htheta hlarge hnu)) u =
      nu.character (stableStationaryRepresentativeUnit F theta psi
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma c hc) := by
  let hr := stableTwist_stationaryDepth F theta d epsilon
    hepsilon htheta hlarge
  let beta := stableStationaryRepresentativeUnit F theta psi hr Gamma c hc
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le theta.conductor) u
  rw [stableTwistCoefficientClass_mk, latticeQuotientMk_eq_zero_iff] at hu
  have hdepth : (theta.conductor : ℤ) - (d + epsilon : ℕ) = (d : ℤ) := by
    omega
  rw [hdepth] at hu
  have hbeta0 : ord F (beta : F) = 0 := by
    dsimp only [beta]
    rw [stableStationaryRepresentativeUnit_coe,
      stationaryNumeratorClass_representative_ord
        F theta psi (theta.conductor : ℤ) hr Gamma Gamma.property c hc]
    simp
  have hu0 : ord F ((u : Fˣ) : F) = 0 :=
    (mem_unitFiltration_zero F (u : Fˣ)).1 u.property
  have hcong : CongruentAtDepth (d : ℤ) ((u : Fˣ) : F) (beta : F) := by
    apply (congruentAtDepth_iff_sub_mem_lattice F (d : ℤ)
      ((u : Fˣ) : F) (beta : F)).2
    simpa only [beta, stableStationaryRepresentativeUnit_coe] using hu
  have hratio : (u : Fˣ) / beta ∈ unitFiltration F d :=
    (div_mem_unitFiltration_iff_congruentAtDepth F d (u : Fˣ) beta
      (unitFiltration_le_unitGroup F 0 u.property)
      (unitFiltration_le_unitGroup F 0
        ((mem_unitFiltration_zero F beta).2 hbeta0))).2 hcong
  have hnuRatio : nu.character ((u : Fˣ) / beta) = 1 :=
    nu.isConductor.trivial _ (unitFiltration_antitone F hnu hratio)
  rw [stableTwistLowCharacter_mk]
  apply div_eq_one.mp
  rw [← map_div]
  exact hnuRatio

/-- A nonzero orbit coefficient gives a nontrivial additive character, hence
its complete sum over `U^r/U^q` vanishes. -/
private theorem stableTwist_orbitSum_eq_zero
    (theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth theta.conductor r)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (u : UnitFiltrationQuotient F 0 theta.conductor
      (Nat.zero_le theta.conductor))
    (hu : stableTwistCoefficientClass F hr.le_conductor c u ≠ 0) :
    letI := unitFiltrationQuotientFintype F hr.le_conductor
    ∑ a : UnitFiltrationQuotient F r theta.conductor hr.le_conductor,
      (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
        (stableTwistCoefficientClass F hr.le_conductor c u))
          ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
            hr.le_conductor hr.half_le a).toAdd) = 0 := by
  letI := unitFiltrationQuotientFintype F hr.le_conductor
  letI := latticeQuotientFintype F hr.int_le_conductor
  let chi := lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
    (stableTwistCoefficientClass F hr.le_conductor c u)
  have hchi : chi ≠ 1 := by
    intro htriv
    apply hu
    apply lamprechtPairingLeft_injective F psi hr.int_le_conductor
      Gamma Gamma.property
    change chi = lamprechtPairingLeft F psi hr.int_le_conductor
      Gamma Gamma.property 0
    rw [map_zero]
    calc
      chi = 1 := htriv
      _ = 0 := by
        ext x
        simp
  change ∑ a : UnitFiltrationQuotient F r theta.conductor hr.le_conductor,
    chi ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
      hr.le_conductor hr.half_le a).toAdd) = 0
  calc
    _ = ∑ x : Multiplicative
        (LamprechtVariableQuotient F (theta.conductor : ℤ) (r : ℤ)
          hr.int_le_conductor), chi x.toAdd :=
      (positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
        hr.le_conductor hr.half_le).toEquiv.sum_comp (fun x ↦ chi x.toAdd)
    _ = ∑ x : LamprechtVariableQuotient F (theta.conductor : ℤ) (r : ℤ)
        hr.int_le_conductor, chi x :=
      Multiplicative.toAdd.sum_comp chi
    _ = 0 := AddChar.sum_eq_zero_of_ne_one hchi

/-- The unchanged-conductor denominator, regarded as admissible for the
proof-bearing twisted datum. -/
abbrev stableTwistAdmissibleGamma
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hcond : nu.conductor < theta.conductor)
    (Gamma : AdmissibleGamma F theta psi) :
    AdmissibleGamma F (stableTwistData F nu theta hcond) psi :=
  ⟨(Gamma : Fˣ), by simpa using Gamma.property⟩

@[simp]
theorem stableTwistAdmissibleGamma_coe
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hcond : nu.conductor < theta.conductor)
    (Gamma : AdmissibleGamma F theta psi) :
    (stableTwistAdmissibleGamma F nu theta psi hcond Gamma : Fˣ) =
      (Gamma : Fˣ) :=
  rfl

/-- At each full unit class, the twisted Gauss summand is the original
summand times the inverse low-character value. -/
private theorem finiteGaussSummand_stableTwist
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hcond : nu.conductor < theta.conductor)
    (Gamma : AdmissibleGamma F theta psi)
    (u : UnitFiltrationQuotient F 0 theta.conductor
      (Nat.zero_le theta.conductor)) :
    finiteGaussSummand (stableTwistData F nu theta hcond) psi
        (stableTwistAdmissibleGamma F nu theta psi hcond Gamma) u =
      (stableTwistLowCharacter F nu theta.conductor
        (Nat.le_of_lt hcond) u : ℂ)⁻¹ *
        finiteGaussSummand theta psi Gamma u := by
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le theta.conductor) u
  rw [finiteGaussSummand_mk, finiteGaussSummand_mk,
    finiteGaussSummandRepresentative, finiteGaussSummandRepresentative,
    stableTwistLowCharacter_mk]
  have hmul :
      ((stableTwistData F nu theta hcond).character (u : Fˣ) : ℂ) =
        (nu.character (u : Fˣ) : ℂ) *
          (theta.character (u : Fˣ) : ℂ) :=
    congrArg Units.val
      (ContinuousQuasiChar.mul_apply nu.character theta.character (u : Fˣ))
  rw [stableTwistAdmissibleGamma_coe, hmul, mul_inv_rev]
  ring

/-- Exact stable twisting for the unnormalised finite Gauss sum.  The proof
averages over `U^(d+epsilon)/U^q`; perfect stationary duality kills every
orbit except `[u]=[c]` modulo `p^d`, where the low character has value
`nu(c)`. -/
theorem finiteGaussSum_stableTwist
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) (hnu : nu.conductor ≤ d)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge).int_le_conductor
          (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma Gamma.property) :
    let hcond := stableTwist_conductor_lt F nu theta d epsilon htheta hlarge hnu
    finiteGaussSum (stableTwistData F nu theta hcond) psi
        (stableTwistAdmissibleGamma F nu theta psi hcond Gamma) =
      (nu.character (stableStationaryRepresentativeUnit F theta psi
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma c hc) : ℂ)⁻¹ *
        finiteGaussSum theta psi Gamma := by
  dsimp only
  let hcond := stableTwist_conductor_lt F nu theta d epsilon htheta hlarge hnu
  let hr := stableTwist_stationaryDepth F theta d epsilon
    hepsilon htheta hlarge
  let beta := stableStationaryRepresentativeUnit F theta psi hr Gamma c hc
  let mu := stableTwistLowCharacter F nu theta.conductor (Nat.le_of_lt hcond)
  let f := finiteGaussSummand theta psi Gamma
  let coeff := stableTwistCoefficientClass F hr.le_conductor c
  let lambda := fun
      (u : UnitFiltrationQuotient F 0 theta.conductor
        (Nat.zero_le theta.conductor))
      (a : UnitFiltrationQuotient F (d + epsilon) theta.conductor
        hr.le_conductor) ↦
    (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (coeff u))
        ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
          hr.le_conductor hr.half_le a).toAdd)
  letI := unitFiltrationQuotientFintype F (Nat.zero_le theta.conductor)
  letI := unitFiltrationQuotientFintype F hr.le_conductor
  have hweighted :
      (∑ u : UnitFiltrationQuotient F 0 theta.conductor
          (Nat.zero_le theta.conductor),
        (((mu u : ℂ)⁻¹ - (nu.character beta : ℂ)⁻¹) * f u)) = 0 := by
    have havg :
        (Fintype.card (UnitFiltrationQuotient F (d + epsilon)
            theta.conductor hr.le_conductor) : ℂ) *
          (∑ u : UnitFiltrationQuotient F 0 theta.conductor
              (Nat.zero_le theta.conductor),
            (((mu u : ℂ)⁻¹ - (nu.character beta : ℂ)⁻¹) * f u)) = 0 := by
      calc
        _ = ∑ a : UnitFiltrationQuotient F (d + epsilon)
              theta.conductor hr.le_conductor,
            ∑ u : UnitFiltrationQuotient F 0 theta.conductor
                (Nat.zero_le theta.conductor),
              (((mu u : ℂ)⁻¹ - (nu.character beta : ℂ)⁻¹) * f u) := by
          simp
        _ = ∑ a : UnitFiltrationQuotient F (d + epsilon)
              theta.conductor hr.le_conductor,
            ∑ u : UnitFiltrationQuotient F 0 theta.conductor
                (Nat.zero_le theta.conductor),
              (((mu (stableTwistDeepClassInFull F hr.le_conductor a * u) : ℂ)⁻¹ -
                  (nu.character beta : ℂ)⁻¹) *
                f (stableTwistDeepClassInFull F hr.le_conductor a * u)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact (sum_unitFiltrationQuotient_mul_left F
            (Nat.zero_le theta.conductor)
            (stableTwistDeepClassInFull F hr.le_conductor a)
            (fun u ↦ (((mu u : ℂ)⁻¹ -
              (nu.character beta : ℂ)⁻¹) * f u))).symm
        _ = ∑ a : UnitFiltrationQuotient F (d + epsilon)
              theta.conductor hr.le_conductor,
            ∑ u : UnitFiltrationQuotient F 0 theta.conductor
                (Nat.zero_le theta.conductor),
              (((mu u : ℂ)⁻¹ - (nu.character beta : ℂ)⁻¹) *
                (lambda u a * f u)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro u _hu
          have hmu := stableTwistLowCharacter_deep_mul F nu
            hr.le_conductor
            (hnu.trans (Nat.le_add_right d epsilon))
            (Nat.le_of_lt hcond) a u
          have hf := finiteGaussSummand_stationaryOrbit
            F theta psi hr Gamma c hc a u
          change f (stableTwistDeepClassInFull F hr.le_conductor a * u) =
            lambda u a * f u at hf
          change (((mu (stableTwistDeepClassInFull F hr.le_conductor a * u) : ℂ)⁻¹ -
              (nu.character beta : ℂ)⁻¹) *
              f (stableTwistDeepClassInFull F hr.le_conductor a * u)) = _
          rw [hmu, hf]
        _ = ∑ u : UnitFiltrationQuotient F 0 theta.conductor
              (Nat.zero_le theta.conductor),
            ((((mu u : ℂ)⁻¹ - (nu.character beta : ℂ)⁻¹) * f u) *
              ∑ a : UnitFiltrationQuotient F (d + epsilon)
                theta.conductor hr.le_conductor, lambda u a) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u _hu
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _ha
          ring
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro u _hu
          by_cases hu : coeff u = 0
          · have hmu :=
              stableTwistLowCharacter_eq_stationary_of_coefficient_eq_zero
                F nu theta psi d epsilon hepsilon htheta hlarge hnu
                Gamma c hc u hu
            change mu u = nu.character beta at hmu
            rw [hmu]
            simp
          · have hsum := stableTwist_orbitSum_eq_zero
              F theta psi hr Gamma c u hu
            change (∑ a : UnitFiltrationQuotient F (d + epsilon)
              theta.conductor hr.le_conductor, lambda u a) = 0 at hsum
            rw [hsum, mul_zero]
    have hcard :
        (Fintype.card (UnitFiltrationQuotient F (d + epsilon)
          theta.conductor hr.le_conductor) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp havg).resolve_left hcard
  have hweighted' :
      (∑ u : UnitFiltrationQuotient F 0 theta.conductor
          (Nat.zero_le theta.conductor), (mu u : ℂ)⁻¹ * f u) =
        (nu.character beta : ℂ)⁻¹ *
          ∑ u : UnitFiltrationQuotient F 0 theta.conductor
            (Nat.zero_le theta.conductor), f u := by
    simp_rw [sub_mul] at hweighted
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hweighted
    exact sub_eq_zero.mp hweighted
  change (∑ u : UnitFiltrationQuotient F 0 theta.conductor
      (Nat.zero_le theta.conductor),
        finiteGaussSummand (stableTwistData F nu theta hcond) psi
          (stableTwistAdmissibleGamma F nu theta psi hcond Gamma) u) = _
  calc
    _ = ∑ u : UnitFiltrationQuotient F 0 theta.conductor
          (Nat.zero_le theta.conductor), (mu u : ℂ)⁻¹ * f u := by
      apply Finset.sum_congr rfl
      intro u _hu
      exact finiteGaussSummand_stableTwist F nu theta psi hcond Gamma u
    _ = _ := hweighted'

/-! ## The exact local-constant formula -/

/-- **Exact stable twist** (Lemma `lem:stable-twist-new`).

If `m(theta)=2d+epsilon>1`, `epsilon` is zero or one, and `m(nu)≤d`,
then for every representative `c` of the stationary quotient class,

`Delta(nu*theta,psi) = nu(Gamma/c) Delta(theta,psi)`.

The same admissible denominator is used on both sides, the inverse of `c`
has the manuscript's direction, and representative independence is the
separate theorem `stableTwist_characterFactor_representative_independent`. -/
theorem stableTwist
    (nu theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (htheta : theta.conductor = 2 * d + epsilon)
    (hlarge : 1 < theta.conductor) (hnu : nu.conductor ≤ d)
    (Gamma : AdmissibleGamma F theta psi)
    (c : lattice F ((theta.conductor : ℤ) - (theta.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge).int_le_conductor
          (theta.conductor : ℤ)) c =
      stationaryNumeratorClass F theta psi (theta.conductor : ℤ)
        (stableTwist_stationaryDepth F theta d epsilon
          hepsilon htheta hlarge) Gamma Gamma.property) :
    let hcond := stableTwist_conductor_lt F nu theta d epsilon htheta hlarge hnu
    deltaFinite (stableTwistData F nu theta hcond) psi
        (stableTwistAdmissibleGamma F nu theta psi hcond Gamma) =
      (nu.character ((Gamma : Fˣ) /
        stableStationaryRepresentativeUnit F theta psi
          (stableTwist_stationaryDepth F theta d epsilon
            hepsilon htheta hlarge) Gamma c hc) : ℂ) *
        deltaFinite theta psi Gamma := by
  dsimp only
  let hcond := stableTwist_conductor_lt F nu theta d epsilon htheta hlarge hnu
  let hr := stableTwist_stationaryDepth F theta d epsilon
    hepsilon htheta hlarge
  let beta := stableStationaryRepresentativeUnit F theta psi hr Gamma c hc
  have hGauss := finiteGaussSum_stableTwist F nu theta psi d epsilon
    hepsilon htheta hlarge hnu Gamma c hc
  have hbeta0 : ord F (beta : F) = 0 := by
    dsimp only [beta]
    rw [stableStationaryRepresentativeUnit_coe,
      stationaryNumeratorClass_representative_ord
        F theta psi (theta.conductor : ℤ) hr Gamma Gamma.property c hc]
    simp
  let beta0 : unitFiltration F 0 :=
    ⟨beta, (mem_unitFiltration_zero F beta).2 hbeta0⟩
  have hnorm : ‖(nu.character beta : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv]
    change ‖(nu.character (beta0 : Fˣ) : ℂ)‖⁻¹ = 1
    rw [quasiChar_norm_eq_one_of_mem_unitFiltration_zero nu beta0, inv_one]
  have hG : finiteGaussSum theta psi Gamma ≠ 0 :=
    finiteGaussSum_ne_zero theta psi Gamma
  have hphase :
      phase (finiteGaussSum (stableTwistData F nu theta hcond) psi
        (stableTwistAdmissibleGamma F nu theta psi hcond Gamma)) =
        (nu.character beta : ℂ)⁻¹ * phase (finiteGaussSum theta psi Gamma) := by
    rw [hGauss, phase_mul_of_norm_eq_one hnorm hG]
  have hprodGamma :
      ((stableTwistData F nu theta hcond).character (Gamma : Fˣ) : ℂ) =
        (nu.character (Gamma : Fˣ) : ℂ) *
          (theta.character (Gamma : Fˣ) : ℂ) :=
    congrArg Units.val
      (ContinuousQuasiChar.mul_apply nu.character theta.character (Gamma : Fˣ))
  have hfactor :
      (nu.character ((Gamma : Fˣ) / beta) : ℂ) =
        (nu.character (Gamma : Fˣ) : ℂ) *
          (nu.character beta : ℂ)⁻¹ := by
    rw [map_div]
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [deltaFinite, deltaFinite, stableTwistAdmissibleGamma_coe,
    hprodGamma, hphase, hfactor]
  ring

end

end LanglandsFirstMainLemma
