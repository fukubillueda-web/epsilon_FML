import LanglandsFirstMainLemma.Cases.WildEndpoints.One.ResidualGauss
import Mathlib.NumberTheory.Wilson

/-!
# Cyclic enumeration and Wilson products at the wild endpoint
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section
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
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

local notation "p" => Module.finrank F K
local notation "e" => ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen

local instance endpointDegreeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance endpointDegreeNeZero : NeZero p :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

noncomputable def endpointTau : NormCharacter F K :=
  e (Multiplicative.ofAdd (1 : ZMod p))

lemma endpointTau_ne_one : endpointTau F K ht hres piK hpiK hgen ≠ 1 := by
  rw [endpointTau]
  exact (ramifiedNormCharacterZModEquiv_ne_one_iff
    F K ht hres piK hpiK hgen _).2 (by simp)

lemma endpoint_enum_eq_tau_pow (j : ℕ) :
    e (Multiplicative.ofAdd (j : ZMod p)) =
      endpointTau F K ht hres piK hpiK hgen ^ j := by
  rw [endpointTau]
  rw [← map_pow]
  congr 1
  change (j : ZMod p) = j • (1 : ZMod p)
  simp

lemma endpoint_enum_eq_tau_pow_val
    (a : Multiplicative (ZMod p)) :
    e a = endpointTau F K ht hres piK hpiK hgen ^ a.toAdd.val := by
  rw [← endpoint_enum_eq_tau_pow F K ht hres piK hpiK hgen]
  congr 1
  change a.toAdd = (a.toAdd.val : ZMod p)
  exact (ZMod.natCast_zmod_val a.toAdd).symm

lemma endpoint_enum_nat_ne_one {j : ℕ} (hjpos : 0 < j) (hjlt : j < p) :
    e (Multiplicative.ofAdd (j : ZMod p)) ≠ 1 := by
  apply (ramifiedNormCharacterZModEquiv_ne_one_iff
    F K ht hres piK hpiK hgen _).2
  intro hmul
  have hz : (j : ZMod p) = 0 :=
    congrArg (fun x : Multiplicative (ZMod p) ↦ x.toAdd) hmul
  have hv := congrArg ZMod.val hz
  apply hjpos.ne'
  simpa [ZMod.val_cast_of_lt hjlt] using hv

/-- The chosen generator norm character, packaged with its exact common
conductor. -/
def endpointTauData : LocalQuasiCharData F where
  character := (endpointTau F K ht hres piK hpiK hgen).1
  conductor := t + 1
  isConductor := ramifiedNormCharacter_conductor
    F K ht hres piK hpiK hgen _
      (endpointTau_ne_one F K ht hres piK hpiK hgen)

@[simp] lemma endpointTauData_character :
    (endpointTauData F K ht hres piK hpiK hgen).character =
      (endpointTau F K ht hres piK hpiK hgen).1 := rfl

@[simp] lemma endpointTauData_conductor :
    (endpointTauData F K ht hres piK hpiK hgen).conductor = t + 1 := rfl

/-- The exact conductor-`t+1` data attached to the explicitly enumerated
nonzero index.  The conductor is definitionally common across indices. -/
def endpointIndexedNormData (j : ℕ)
    (hmu : e (Multiplicative.ofAdd (j : ZMod p)) ≠ 1) :
    LocalQuasiCharData F where
  character := (e (Multiplicative.ofAdd (j : ZMod p))).1
  conductor := t + 1
  isConductor := ramifiedNormCharacter_conductor
    F K ht hres piK hpiK hgen _ hmu

@[simp] lemma endpointIndexedNormData_character (j : ℕ)
    (hmu : e (Multiplicative.ofAdd (j : ZMod p)) ≠ 1) :
    (endpointIndexedNormData F K ht hres piK hpiK hgen j hmu).character =
      (e (Multiplicative.ofAdd (j : ZMod p))).1 := rfl

@[simp] lemma endpointIndexedNormData_conductor (j : ℕ)
    (hmu : e (Multiplicative.ofAdd (j : ZMod p)) ≠ 1) :
    (endpointIndexedNormData F K ht hres piK hpiK hgen j hmu).conductor =
      t + 1 := rfl

/-- The representative `j b_tau` is exactly the stationary representative
for the character `tau^j`; this uses integer-power stationary calculus and
uniqueness, not an independent choice for each factor. -/
theorem endpointIndexed_stationaryRepresentative
    (htpos : 0 < t) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hbreak : t + 1 = 2 * d + epsilon)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (cTau : lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (hcTau :
      let thetaTau := endpointTauData F K ht hres piK hpiK hgen
      let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
        (by change t + 1 = 2 * d + epsilon; exact hbreak)
        (by change 1 < t + 1; omega)
      latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)) cTau =
        stationaryNumeratorClass F thetaTau psi ((t + 1 : ℕ) : ℤ)
          hrTau Gamma (by simpa using hGamma))
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < p) :
    let hmuJ := endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hjpos hjlt
    let thetaJ := endpointIndexedNormData F K ht hres piK hpiK hgen j hmuJ
    let hrJ := stableTwist_stationaryDepth F thetaJ d epsilon hepsilon
      (by change t + 1 = 2 * d + epsilon; exact hbreak)
      (by change 1 < t + 1; omega)
    latticeQuotientMk F
        (sub_le_sub_left hrJ.int_le_conductor ((t + 1 : ℕ) : ℤ))
        ((j : ℤ) • cTau) =
      stationaryNumeratorClass F thetaJ psi ((t + 1 : ℕ) : ℤ)
        hrJ Gamma (by simpa using hGamma) := by
  dsimp only
  let thetaTau := endpointTauData F K ht hres piK hpiK hgen
  let hthetaTau : thetaTau.conductor = 2 * d + epsilon := by
    simp only [thetaTau, endpointTauData_conductor]
    omega
  let hlargeTau : 1 < thetaTau.conductor := by
    simp only [thetaTau, endpointTauData_conductor]
    omega
  let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
    hthetaTau hlargeTau
  let hmuJ := endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hjpos hjlt
  let thetaJ := endpointIndexedNormData F K ht hres piK hpiK hgen j hmuJ
  let hthetaJ : thetaJ.conductor = 2 * d + epsilon := by
    simp only [thetaJ, endpointIndexedNormData_conductor]
    omega
  let hlargeJ : 1 < thetaJ.conductor := by
    simp only [thetaJ, endpointIndexedNormData_conductor]
    omega
  let hrJ := stableTwist_stationaryDepth F thetaJ d epsilon hepsilon
    hthetaJ hlargeJ
  have hchar : thetaJ.character = thetaTau.character ^ (j : ℤ) := by
    simp only [thetaJ, thetaTau, endpointIndexedNormData_character,
      endpointTauData_character]
    rw [endpoint_enum_eq_tau_pow F K ht hres piK hpiK hgen]
    ext u
    simpa using congrFun
      (NormCharacter.coe_pow F K
        (endpointTau F K ht hres piK hpiK hgen) j) u
  have hsTau := stationaryNumeratorClass_isRestriction F thetaTau psi
    ((t + 1 : ℕ) : ℤ) hrTau Gamma (by simpa using hGamma)
  have hsPow := IsStationaryRestrictionClass.zpow F psi
    ((t + 1 : ℕ) : ℤ) hrTau.pos hrTau.le_conductor Gamma
    (by simpa using hGamma)
    (stationaryNumeratorClass F thetaTau psi ((t + 1 : ℕ) : ℤ)
      hrTau Gamma (by simpa using hGamma)) hsTau (j : ℤ)
  have hclasses :
      (j : ℤ) • stationaryNumeratorClass F thetaTau psi
          ((t + 1 : ℕ) : ℤ) hrTau Gamma (by simpa using hGamma) =
        stationaryNumeratorClass F thetaJ psi ((t + 1 : ℕ) : ℤ)
          hrJ Gamma (by simpa using hGamma) := by
    apply stationaryNumeratorClass_unique F thetaJ psi
      ((t + 1 : ℕ) : ℤ) hrJ Gamma (by simpa using hGamma)
    intro c hc x
    rw [hchar]
    exact hsPow c hc x
  calc
    latticeQuotientMk F
        (sub_le_sub_left hrJ.int_le_conductor ((t + 1 : ℕ) : ℤ))
        ((j : ℤ) • cTau) =
        (j : ℤ) • latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)) cTau := by
      exact (map_zsmul
        (latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)))
        (j : ℤ) cTau).symm
    _ = _ := by
      rw [hcTau]
      exact hclasses

/-- Stable twisting for every explicit nonzero cyclic index, with the
reciprocal factor built from `j b_tau`.  There is no family of independent
stationary choices. -/
theorem endpointIndexed_stableTwistFactor
    (htpos : 0 < t)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hbreak : t + 1 = 2 * d + epsilon)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (cTau : lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (hcTau :
      let thetaTau := endpointTauData F K ht hres piK hpiK hgen
      let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
        (by change t + 1 = 2 * d + epsilon; exact hbreak)
        (by change 1 < t + 1; omega)
      latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)) cTau =
        stationaryNumeratorClass F thetaTau psi ((t + 1 : ℕ) : ℤ)
          hrTau Gamma (by simpa using hGamma))
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < p) :
    let hmuJ := endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hjpos hjlt
    let thetaJ := endpointIndexedNormData F K ht hres piK hpiK hgen j hmuJ
    let hthetaJ : thetaJ.conductor = 2 * d + epsilon := by
      change t + 1 = 2 * d + epsilon
      exact hbreak
    let hlargeJ : 1 < thetaJ.conductor := by
      change 1 < t + 1
      omega
    let hrJ := stableTwist_stationaryDepth F thetaJ d epsilon hepsilon
      hthetaJ hlargeJ
    let gammaJ : AdmissibleGamma F thetaJ psi := ⟨Gamma, by
      change ord F (Gamma : F) =
        ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ)
      exact hGamma⟩
    let cJ : lattice F
        ((thetaJ.conductor : ℤ) - (thetaJ.conductor : ℤ)) :=
      (j : ℤ) • cTau
    let hcJ : latticeQuotientMk F
          (sub_le_sub_left hrJ.int_le_conductor (thetaJ.conductor : ℤ)) cJ =
        stationaryNumeratorClass F thetaJ psi (thetaJ.conductor : ℤ)
          hrJ gammaJ gammaJ.property := by
      exact endpointIndexed_stationaryRepresentative
        F K ht hres piK hpiK hgen htpos psi d epsilon hepsilon hbreak
          Gamma hGamma cTau hcTau hjpos hjlt
    let hcond : chi.conductor < thetaJ.conductor := by
      change chi.conductor < t + 1
      omega
    deltaFinite (stableTwistData F chi thetaJ hcond) psi
        (stableTwistAdmissibleGamma F chi thetaJ psi hcond gammaJ) =
      (chi.character (gammaJ /
        stableStationaryRepresentativeUnit F thetaJ psi hrJ gammaJ cJ hcJ) : ℂ) *
        deltaFinite thetaJ psi gammaJ := by
  dsimp only
  let hmuJ := endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hjpos hjlt
  let thetaJ := endpointIndexedNormData F K ht hres piK hpiK hgen j hmuJ
  let hthetaJ : thetaJ.conductor = 2 * d + epsilon := by
    simp only [thetaJ, endpointIndexedNormData_conductor]
    omega
  let hlargeJ : 1 < thetaJ.conductor := by
    simp only [thetaJ, endpointIndexedNormData_conductor]
    omega
  let hrJ := stableTwist_stationaryDepth F thetaJ d epsilon hepsilon
    hthetaJ hlargeJ
  let gammaJ : AdmissibleGamma F thetaJ psi := ⟨Gamma, by
    change ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ)
    exact hGamma⟩
  let cJ : lattice F
      ((thetaJ.conductor : ℤ) - (thetaJ.conductor : ℤ)) :=
    (j : ℤ) • cTau
  let hcJ : latticeQuotientMk F
        (sub_le_sub_left hrJ.int_le_conductor (thetaJ.conductor : ℤ)) cJ =
      stationaryNumeratorClass F thetaJ psi (thetaJ.conductor : ℤ)
        hrJ gammaJ gammaJ.property := by
    exact endpointIndexed_stationaryRepresentative
      F K ht hres piK hpiK hgen htpos psi d epsilon hepsilon hbreak
        Gamma hGamma cTau hcTau hjpos hjlt
  let hcond : chi.conductor < thetaJ.conductor := by
    simp only [thetaJ, endpointIndexedNormData_conductor, hchi]
    omega
  have hnu : chi.conductor ≤ d := by
    rw [hchi]
    omega
  exact stableTwist F chi thetaJ psi d epsilon hepsilon hthetaJ hlargeJ
    hnu gammaJ cJ hcJ

/-- The canonical natural index `1,…,p-1` of a nontrivial norm character. -/
noncomputable def endpointNormCharacterIndex (mu : NormCharacter F K) : ℕ :=
  (((ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).symm mu).toAdd).val

theorem endpointNormCharacterIndex_pos (mu : NormCharacter F K)
    (hmu : mu ≠ 1) :
    0 < endpointNormCharacterIndex F K ht hres piK hpiK hgen mu := by
  rw [endpointNormCharacterIndex, ZMod.val_pos]
  intro hz
  apply hmu
  calc
    mu = e ((ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).symm mu) :=
      ((ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).apply_symm_apply mu).symm
    _ = e 1 := by
      congr 1
    _ = 1 :=
      (ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).map_one

theorem endpointNormCharacterIndex_lt (mu : NormCharacter F K) :
    endpointNormCharacterIndex F K ht hres piK hpiK hgen mu < p := by
  exact ZMod.val_lt _

theorem endpoint_enum_index (mu : NormCharacter F K) :
    e (Multiplicative.ofAdd
      (endpointNormCharacterIndex F K ht hres piK hpiK hgen mu : ZMod p)) = mu := by
  calc
    e (Multiplicative.ofAdd
        (endpointNormCharacterIndex F K ht hres piK hpiK hgen mu : ZMod p)) =
        e ((ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).symm mu) := by
      congr 1
      apply Multiplicative.ext
      exact ZMod.natCast_zmod_val
        ((ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).symm mu).toAdd
    _ = mu :=
      (ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).apply_symm_apply mu

/-- The complete norm-character finset with the identity removed. -/
noncomputable def endpointNontrivialNormCharacterFinset :
    Finset (NormCharacter F K) := by
  classical
  exact (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).erase 1

/-- Reindexing the nontrivial norm-character product by the literal Wilson
interval `1,…,p-1`. -/
theorem ramifiedNontrivialProduct_eq_IcoProduct
    {M : Type*} [CommMonoid M] (f : NormCharacter F K → M) :
    (endpointNontrivialNormCharacterFinset
      F K ht hres piK hpiK hgen).prod f =
      (Finset.Ico 1 p).prod (fun j ↦
        f (e (Multiplicative.ofAdd (j : ZMod p)))) := by
  classical
  let S := endpointNontrivialNormCharacterFinset F K ht hres piK hpiK hgen
  apply Finset.prod_bij
    (fun mu _ ↦ endpointNormCharacterIndex F K ht hres piK hpiK hgen mu)
  · intro mu hmuS
    have hmu : mu ≠ 1 := (Finset.mem_erase.mp hmuS).1
    exact Finset.mem_Ico.mpr ⟨
      endpointNormCharacterIndex_pos F K ht hres piK hpiK hgen mu hmu,
      endpointNormCharacterIndex_lt F K ht hres piK hpiK hgen mu⟩
  · intro mu hmuS nu hnuS hindex
    rw [← endpoint_enum_index F K ht hres piK hpiK hgen mu,
      ← endpoint_enum_index F K ht hres piK hpiK hgen nu,
      hindex]
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    let mu := e (Multiplicative.ofAdd (j : ZMod p))
    have hmu : mu ≠ 1 :=
      endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hj'.1 hj'.2
    have hmem : mu ∈ S := by
      apply Finset.mem_erase.mpr
      refine ⟨hmu, ?_⟩
      simp [S, endpointNontrivialNormCharacterFinset,
        ramifiedNormCharacterFinset, normCharacterFinset]
    refine ⟨mu, hmem, ?_⟩
    simp [endpointNormCharacterIndex, mu, ZMod.val_cast_of_lt hj'.2]
  · intro mu hmuS
    exact congrArg f
      (endpoint_enum_index F K ht hres piK hpiK hgen mu).symm

end
section WilsonLift

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "pF" => residueCharacteristic F

local instance endpointResidueCharacteristicFact :
    Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩

/-- The natural scalar `j`, bundled as a field unit on the Wilson interval;
outside that interval it is harmlessly defined to be one. -/
noncomputable def endpointNatUnit (j : ℕ) : Fˣ := by
  by_cases hj : 0 < j ∧ j < pF
  · exact Units.mk0 (j : F) ((ord_ne_top_iff F).1 (by
      rw [ord_natCast_eq_zero_of_lt_residueCharacteristic F hj.1 hj.2]
      simp))
  · exact 1

@[simp] theorem endpointNatUnit_coe {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    (endpointNatUnit F j : F) = (j : F) := by
  simp [endpointNatUnit, hjpos, hjlt]

theorem endpointNatUnit_order {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    ord F (endpointNatUnit F j : F) = 0 := by
  rw [endpointNatUnit_coe F hjpos hjlt]
  exact ord_natCast_eq_zero_of_lt_residueCharacteristic F hjpos hjlt

/-- The same scalar as an element of `O_F^x`. -/
noncomputable def endpointNatLocalUnit (j : ℕ) : unitGroup F := by
  by_cases hj : 0 < j ∧ j < pF
  · exact ⟨endpointNatUnit F j,
      (mem_unitGroup_iff_ord_eq_zero F _).2
        (endpointNatUnit_order F hj.1 hj.2)⟩
  · exact 1

@[simp] theorem endpointNatLocalUnit_coe {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    ((endpointNatLocalUnit F j : unitGroup F) : Fˣ) = endpointNatUnit F j := by
  simp [endpointNatLocalUnit, hjpos, hjlt]

/-- The nonzero residue scalar corresponding to a Wilson index. -/
noncomputable def endpointResidueNatUnit (j : ℕ) : (ResidueField F)ˣ := by
  by_cases hj : 0 < j ∧ j < pF
  · exact Units.mk0 (j : ResidueField F) (by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hj.1 hj.2)
        ((CharP.cast_eq_zero_iff (ResidueField F) pF j).mp hz))
  · exact 1

@[simp] theorem endpointResidueNatUnit_coe {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    (endpointResidueNatUnit F j : ResidueField F) = (j : ResidueField F) := by
  simp [endpointResidueNatUnit, hjpos, hjlt]

/-- Reduction of the natural local unit is the corresponding nonzero
residue scalar. -/
theorem residueUnits_endpointNatLocalUnit {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    residueUnits F (endpointNatLocalUnit F j) = endpointResidueNatUnit F j := by
  apply Units.ext
  rw [residueUnits_coe]
  simp only [endpointNatLocalUnit, hjpos, hjlt, and_self, dif_pos,
    endpointResidueNatUnit_coe F hjpos hjlt]
  have hcoe :
      ((unitGroupMulEquivRingOfIntegers F
        (⟨endpointNatUnit F j,
          (mem_unitGroup_iff_ord_eq_zero F _).2
            (endpointNatUnit_order F hjpos hjlt)⟩ : unitGroup F) :
          (ringOfIntegers F)ˣ) : ringOfIntegers F) =
        (j : ringOfIntegers F) := by
    apply Subtype.ext
    exact endpointNatUnit_coe F hjpos hjlt
  rw [hcoe]
  exact map_natCast (residueMap F) j

/-- The Teichmuller lift used to compare a stationary scalar with its
residue class. -/
noncomputable def endpointTeichmullerIndexUnit (j : ℕ) : unitGroup F :=
  teichmullerLocalUnits F (endpointResidueNatUnit F j)

@[simp] theorem residueUnits_endpointTeichmullerIndexUnit (j : ℕ) :
    residueUnits F (endpointTeichmullerIndexUnit F j) =
      endpointResidueNatUnit F j :=
  residueUnits_teichmullerLocalUnits F _

/-- The natural scalar and its Teichmuller lift have the same residue; the
quotient is therefore in `U_F^1`. -/
theorem endpointNatUnit_div_teichmuller_mem_one {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    (endpointNatUnit F j) /
        ((endpointTeichmullerIndexUnit F j : unitGroup F) : Fˣ) ∈
      unitFiltration F 1 := by
  let a : unitGroup F := endpointNatLocalUnit F j
  let b : unitGroup F := endpointTeichmullerIndexUnit F j
  have hker : a / b ∈ (residueUnits F).ker := by
    rw [MonoidHom.mem_ker, map_div,
      residueUnits_endpointNatLocalUnit F hjpos hjlt,
      residueUnits_endpointTeichmullerIndexUnit]
    simp
  rw [residueUnits_ker] at hker
  have hmem := (mem_unitFiltrationInside F (show 0 ≤ 1 by omega) (a / b)).1 hker
  simpa only [a, b, endpointNatLocalUnit_coe F hjpos hjlt,
    Subgroup.coe_div] using hmem

/-- Wilson's product after reduction: the product of the natural local
units is the residue sign `(-1)^p`.  This formulation covers `p=2` as well
as odd residue characteristic. -/
theorem residueUnits_endpointNatLocalUnit_product :
    residueUnits F
        ((Finset.Ico 1 pF).prod (endpointNatLocalUnit F)) =
      (-1 : (ResidueField F)ˣ) ^ pF := by
  have hprod :
      residueUnits F ((Finset.Ico 1 pF).prod (endpointNatLocalUnit F)) =
        (Finset.Ico 1 pF).prod (endpointResidueNatUnit F) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    exact residueUnits_endpointNatLocalUnit F hj'.1 hj'.2
  rw [hprod]
  apply Units.ext
  have hleft :
      (((Finset.Ico 1 pF).prod (endpointResidueNatUnit F) :
          (ResidueField F)ˣ) : ResidueField F) =
        ∏ j ∈ Finset.Ico 1 pF, (j : ResidueField F) := by
    calc
      _ = ∏ j ∈ Finset.Ico 1 pF,
          (endpointResidueNatUnit F j : ResidueField F) :=
        map_prod (Units.coeHom (ResidueField F)) _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        exact endpointResidueNatUnit_coe F hj'.1 hj'.2
  have hright :
      (((-1 : (ResidueField F)ˣ) ^ pF : (ResidueField F)ˣ) :
          ResidueField F) = (-1 : ResidueField F) ^ pF := by
    simpa using map_pow (Units.coeHom (ResidueField F))
      (-1 : (ResidueField F)ˣ) pF
  rw [hleft, hright]
  have hwZ := ZMod.prod_Ico_one_prime pF
  have hw := congrArg (ZMod.castHom (dvd_refl pF) (ResidueField F)) hwZ
  simp only [map_prod, map_neg, map_one, ZMod.castHom_apply,
    ZMod.cast_natCast (dvd_refl pF)] at hw
  rw [hw]
  rcases (residueCharacteristic_prime F).eq_two_or_odd' with hp2 | hpodd
  · have htwo : (2 : ResidueField F) = 0 := by
      have hc : (residueCharacteristic F : ResidueField F) = 0 :=
        CharP.cast_eq_zero (ResidueField F) (residueCharacteristic F)
      simpa [hp2] using hc
    have hneg : (-1 : ResidueField F) = 1 := by
      apply eq_of_sub_eq_zero
      linear_combination -htwo
    rw [hp2]
    simp [hneg]
  · exact hpodd.neg_one_pow.symm

/-- The Wilson scalar product as a field unit. -/
noncomputable def endpointWilsonScalarProduct : Fˣ :=
  (Finset.Ico 1 pF).prod (endpointNatUnit F)

/-- Minus one, regarded as a valuation-ring unit. -/
noncomputable def endpointNegOneLocalUnit : unitGroup F :=
  ⟨(-1 : Fˣ), (mem_unitGroup_iff_ord_eq_zero F _).2 (by simp)⟩

@[simp] theorem endpointNegOneLocalUnit_coe :
    ((endpointNegOneLocalUnit F : unitGroup F) : Fˣ) = (-1 : Fˣ) := rfl

@[simp] theorem residueUnits_endpointNegOneLocalUnit :
    residueUnits F (endpointNegOneLocalUnit F) =
      (-1 : (ResidueField F)ˣ) := by
  apply Units.ext
  rw [residueUnits_coe]
  have hcoe :
      ((unitGroupMulEquivRingOfIntegers F (endpointNegOneLocalUnit F) :
          (ringOfIntegers F)ˣ) : ringOfIntegers F) =
        (-1 : ringOfIntegers F) := by
    apply Subtype.ext
    rfl
  rw [hcoe, map_neg, map_one]
  rfl

/-- The lifted Wilson congruence, in the precise quotient direction used by
the endpoint product calculation. -/
theorem endpointWilsonScalarProduct_div_sign_mem_one :
    endpointWilsonScalarProduct F /
        ((-1 : Fˣ) ^ pF) ∈ unitFiltration F 1 := by
  let A0 : unitGroup F :=
    (Finset.Ico 1 pF).prod (endpointNatLocalUnit F)
  let s0 : unitGroup F := endpointNegOneLocalUnit F ^ pF
  have hker : A0 / s0 ∈ (residueUnits F).ker := by
    rw [MonoidHom.mem_ker, map_div, map_pow,
      residueUnits_endpointNegOneLocalUnit,
      residueUnits_endpointNatLocalUnit_product]
    simp
  rw [residueUnits_ker] at hker
  have hmem := (mem_unitFiltrationInside F (show 0 ≤ 1 by omega) (A0 / s0)).1 hker
  have hA : ((A0 : unitGroup F) : Fˣ) = endpointWilsonScalarProduct F := by
    calc
      _ = (Finset.Ico 1 pF).prod
          (fun j ↦ ((endpointNatLocalUnit F j : unitGroup F) : Fˣ)) :=
        map_prod (unitGroup F).subtype _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        exact endpointNatLocalUnit_coe F hj'.1 hj'.2
  have hs : ((s0 : unitGroup F) : Fˣ) = (-1 : Fˣ) ^ pF := by
    simp [s0, ← map_pow]
  simpa only [Subgroup.coe_div, hA, hs] using hmem

/-- The product of reciprocal stationary factors.  If the representative
at index `j` is literally `j b_tau`, Wilson's theorem supplies the complete
sign, including residue characteristic two. -/
theorem endpointReciprocalFactorProduct_mod_one
    (Gamma bTau : Fˣ) (b : ℕ → Fˣ)
    (hb : ∀ j ∈ Finset.Ico 1 pF,
      b j = endpointNatUnit F j * bTau) :
    ((Finset.Ico 1 pF).prod (fun j ↦ Gamma / b j)) /
        (((-1 : Fˣ) ^ pF) *
          (Gamma / bTau) ^ (pF - 1)) ∈
      unitFiltration F 1 := by
  let A := endpointWilsonScalarProduct F
  let C := Gamma / bTau
  have hcard : (Finset.Ico 1 pF).card = pF - 1 := by
    simp
  have hbprod :
      (Finset.Ico 1 pF).prod b = A * bTau ^ (pF - 1) := by
    calc
      (Finset.Ico 1 pF).prod b =
          (Finset.Ico 1 pF).prod
            (fun j ↦ endpointNatUnit F j * bTau) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hb j hj
      _ = (Finset.Ico 1 pF).prod (endpointNatUnit F) *
          (Finset.Ico 1 pF).prod (fun _ ↦ bTau) :=
        Finset.prod_mul_distrib
      _ = A * bTau ^ (pF - 1) := by
        rw [Finset.prod_const, hcard]
        rfl
  have hfactor :
      (Finset.Ico 1 pF).prod (fun j ↦ Gamma / b j) =
        C ^ (pF - 1) / A := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hcard, hbprod]
    dsimp only [C]
    rw [div_pow]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ac_rfl
  have hw := endpointWilsonScalarProduct_div_sign_mem_one F
  have hwinv := (unitFiltration F 1).inv_mem hw
  have hsignInv : (((-1 : Fˣ) ^ pF)⁻¹) = (-1 : Fˣ) ^ pF := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_pow]
    have h : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by
      apply Units.ext
      simp
    rw [h, one_pow]
  rw [hfactor]
  change (C ^ (pF - 1) / A) /
      (((-1 : Fˣ) ^ pF) * C ^ (pF - 1)) ∈ unitFiltration F 1
  change (A / ((-1 : Fˣ) ^ pF))⁻¹ ∈ unitFiltration F 1 at hwinv
  convert hwinv using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [hsignInv]
  rw [hsignInv]
  calc
    C ^ (pF - 1) * A⁻¹ * ((C ^ (pF - 1))⁻¹ * (-1 : Fˣ) ^ pF) =
        (C ^ (pF - 1) * (C ^ (pF - 1))⁻¹) *
          (((-1 : Fˣ) ^ pF) * A⁻¹) := by ac_rfl
    _ = ((-1 : Fˣ) ^ pF) * A⁻¹ := by simp

/-- The literal scalar multiple `j b` as a field unit. -/
noncomputable def endpointScaledStationaryUnit
    (b : F) (hb : b ≠ 0) (j : ℕ) : Fˣ := by
  by_cases hj : 0 < j ∧ j < pF
  · exact Units.mk0 ((j : F) * b)
      (mul_ne_zero (by
        exact (ord_ne_top_iff F).1 (by
          rw [ord_natCast_eq_zero_of_lt_residueCharacteristic F hj.1 hj.2]
          simp)) hb)
  · exact 1

@[simp] theorem endpointScaledStationaryUnit_coe
    (b : F) (hb : b ≠ 0) {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    (endpointScaledStationaryUnit F b hb j : F) = (j : F) * b := by
  simp [endpointScaledStationaryUnit, hjpos, hjlt]

/-- The scaled representative is exactly the natural local scalar times
the generator representative. -/
theorem endpointScaledStationaryUnit_eq_mul
    (b : F) (hb : b ≠ 0) {j : ℕ}
    (hjpos : 0 < j) (hjlt : j < pF) :
    endpointScaledStationaryUnit F b hb j =
      endpointNatUnit F j * Units.mk0 b hb := by
  apply Units.ext
  rw [endpointScaledStationaryUnit_coe F b hb hjpos hjlt,
    Units.val_mul, endpointNatUnit_coe F hjpos hjlt, Units.val_mk0]

end WilsonLift
/-- Reduction identifies the additive lattice quotient `p^0/p^1` with the
residue field. -/
noncomputable def latticeZeroOneResidueAddHom
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    LatticeGradedPiece E 0 →+ ResidueField E where
  toFun := latticeQuotientLift E (show (0 : ℤ) ≤ 0 + 1 by omega)
    (fun x ↦ reduce E (x : E) x.property)
    (fun x y hxy ↦
      (reduce_eq_reduce_iff E x.property y.property).2 hxy)
  map_zero' := by
    change latticeQuotientLift E (show (0 : ℤ) ≤ 0 + 1 by omega)
      (fun x ↦ reduce E (x : E) x.property) _
      (latticeQuotientMk E (show (0 : ℤ) ≤ 0 + 1 by omega) 0) = 0
    rw [latticeQuotientLift_mk]
    rfl
  map_add' := by
    intro x y
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective E
      (show (0 : ℤ) ≤ 0 + 1 by omega) x
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E
      (show (0 : ℤ) ≤ 0 + 1 by omega) y
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk]
    change residueMap E _ = residueMap E _ + residueMap E _
    convert (residueMap E).map_add
      ⟨(x : E), (mem_lattice_zero_iff E).1 x.property⟩
      ⟨(y : E), (mem_lattice_zero_iff E).1 y.property⟩ using 1 <;> rfl

@[simp]
theorem latticeZeroOneResidueAddHom_mk
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (x : lattice E 0) :
    latticeZeroOneResidueAddHom E
        (latticeQuotientMk E (show (0 : ℤ) ≤ 0 + 1 by omega) x) =
      reduce E (x : E) x.property :=
  rfl

/-- Divide a depth-`n+1` additive graded class by the matching uniformizer
power and reduce. -/
noncomputable def latticeGradedResidueCoordinateAddHom
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (n : ℕ) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    LatticeGradedPiece E (((n + 1 : ℕ) : ℤ)) →+ ResidueField E := by
  let r : ℤ := ((n + 1 : ℕ) : ℤ)
  let a : E := (pi : E) ^ r
  have ha : ord E a = (r : WithTop ℤ) := by
    exact ord_uniformizer_zpow E hpi r
  let f : lattice E r → ResidueField E := fun x ↦
    reduce E ((x : E) / a)
      ((div_mem_lattice_iff E a (x : E) r 0 ha).2 (by
        simpa only [add_zero] using x.property))
  have hf : ∀ (x y : lattice E r),
      CongruentAtDepth (r + 1) (x : E) (y : E) → f x = f y := by
    intro x y hxy
    apply (reduce_eq_reduce_iff E _ _).2
    apply (congruentAtDepth_iff_sub_mem_lattice E 1
      ((x : E) / a) ((y : E) / a)).2
    rw [← sub_div]
    apply (div_mem_lattice_iff E a ((x : E) - (y : E)) r 1 ha).2
    simpa only [add_comm] using
      (congruentAtDepth_iff_sub_mem_lattice E (r + 1)
        (x : E) (y : E)).1 hxy
  refine
    { toFun := latticeQuotientLift E (show r ≤ r + 1 by omega) f hf
      map_zero' := ?_
      map_add' := ?_ }
  · change latticeQuotientLift E (show r ≤ r + 1 by omega) f hf
      (latticeQuotientMk E (show r ≤ r + 1 by omega) 0) = 0
    rw [latticeQuotientLift_mk]
    change residueMap E _ = 0
    rw [residueMap_eq_zero_iff]
    change (0 / a : E) ∈ lattice E 1
    simp
  · intro x y
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective E
      (show r ≤ r + 1 by omega) x
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E
      (show r ≤ r + 1 by omega) y
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk]
    change residueMap E _ = residueMap E _ + residueMap E _
    convert (residueMap E).map_add
      ⟨(x : E) / a, (mem_lattice_zero_iff E).1
        ((div_mem_lattice_iff E a (x : E) r 0 ha).2 (by
          simpa only [add_zero] using x.property))⟩
      ⟨(y : E) / a, (mem_lattice_zero_iff E).1
        ((div_mem_lattice_iff E a (y : E) r 0 ha).2 (by
          simpa only [add_zero] using y.property))⟩ using 1
    congr 1
    apply Subtype.ext
    exact add_div (x : E) (y : E) a

@[simp]
theorem latticeGradedResidueCoordinateAddHom_mk
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (n : ℕ) (pi : ringOfIntegers E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E))
    (x : lattice E (((n + 1 : ℕ) : ℤ))) :
    latticeGradedResidueCoordinateAddHom E n pi hpi
        (latticeQuotientMk E
          (show (((n + 1 : ℕ) : ℤ)) ≤ (((n + 1 : ℕ) : ℤ)) + 1 by omega) x) =
      reduce E ((x : E) / (pi : E) ^ (((n + 1 : ℕ) : ℤ)))
        ((div_mem_lattice_iff E ((pi : E) ^ (((n + 1 : ℕ) : ℤ)))
          (x : E) (((n + 1 : ℕ) : ℤ)) 0
          (ord_uniformizer_zpow E hpi (((n + 1 : ℕ) : ℤ)))).2 (by
            simpa only [add_zero] using x.property)) :=
  rfl

/-- The public ramification graded hom, written in the normalized residual
displacement coordinate used in the derivative product. -/
noncomputable def ramificationResidueCoordinateAddHom
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (n : ℕ) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Additive (LowerRamificationGraded F K (((n + 1 : ℕ) : ℤ))) →+
      ResidueField K :=
  (latticeGradedResidueCoordinateAddHom K n pi hpi).comp
    ((positiveUnitGradedAddEquivLattice K n).toAddMonoidHom.comp
      (MonoidHom.toAdditive
        (ramificationUnitGradedHom F K (n + 1) pi hpi hgen)))

@[simp]
theorem ramificationResidueCoordinateAddHom_mk
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (n : ℕ) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (sigma : lowerRamificationGroup F K (((n + 1 : ℕ) : ℤ))) :
    ramificationResidueCoordinateAddHom F K n pi hpi hgen
        (Additive.ofMul
          (lowerRamificationGradedMk F K (((n + 1 : ℕ) : ℤ)) sigma)) =
      lowerRamificationResidueDisplacement F K sigma (pi : K) hpi := by
  change latticeGradedResidueCoordinateAddHom K n pi hpi
      ((positiveUnitGradedAddEquivLattice K n)
        (Additive.ofMul
          (ramificationUnitGradedHom F K (n + 1) pi hpi hgen
            (lowerRamificationGradedMk F K (((n + 1 : ℕ) : ℤ)) sigma)))) = _
  rw [ramificationUnitGradedHom_mk]
  change latticeGradedResidueCoordinateAddHom K n pi hpi
      (latticeQuotientMk K _
        (unitFiltrationDisplacement K n
          ⟨ramificationRatioUnit F K (n + 1) sigma (pi : K) hpi,
            ramificationRatioUnit_mem F K (n + 1) sigma (pi : K) hpi⟩)) = _
  rw [latticeGradedResidueCoordinateAddHom_mk]
  simp only [lowerRamificationResidueDisplacement,
    lowerRamificationNormalizedDisplacement]
  apply (reduce_eq_reduce_iff K _ _).2
  apply (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).2
  have hpi0 : (pi : K) ≠ 0 := hpi.ne_zero
  have heq :
      (((sigma : Gal(K/F)) (pi : K) / (pi : K) - 1) /
          (pi : K) ^ (((n + 1 : ℕ) : ℤ))) =
        ((sigma : Gal(K/F)) (pi : K) - (pi : K)) /
          (pi : K) ^ ((((n + 1 : ℕ) : ℤ)) + 1) := by
    rw [div_sub_one hpi0, div_div, zpow_add₀ hpi0]
    congr 1
    simp [mul_comm]
  change (((sigma : Gal(K/F)) (pi : K) / (pi : K) - 1) /
      (pi : K) ^ (((n + 1 : ℕ) : ℤ))) -
      ((sigma : Gal(K/F)) (pi : K) - (pi : K)) /
        (pi : K) ^ ((((n + 1 : ℕ) : ℤ)) + 1) ∈ lattice K 1
  rw [heq, sub_self]
  exact (lattice K 1).zero_mem

/-- Wilson's product with precisely the endpoint sign convention: each
derivative factor is the negative of a nonzero ramification displacement. -/
theorem endpointWilsonProduct
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (lambda : k) :
    (∏ u : (ZMod p)ˣ,
      (-ZMod.castHom (dvd_refl p) k (u : ZMod p)) * lambda) =
      (-1 : k) ^ p * lambda ^ (p - 1) := by
  classical
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hWilsonZ : (∏ u : (ZMod p)ˣ, (u : ZMod p)) = -1 := by
    calc
      (∏ u : (ZMod p)ˣ, (u : ZMod p)) =
          Units.coeHom (ZMod p) (∏ u : (ZMod p)ˣ, u) := by
            exact (map_prod (Units.coeHom (ZMod p))
              (fun u : (ZMod p)ˣ ↦ u) Finset.univ).symm
      _ = Units.coeHom (ZMod p) (-1 : (ZMod p)ˣ) := by
        rw [FiniteField.prod_univ_units_id_eq_neg_one]
      _ = -1 := rfl
  rw [Finset.prod_mul_distrib, Finset.prod_neg, Finset.prod_const,
    Finset.card_univ, hcard]
  have hcast :
      (∏ u : (ZMod p)ˣ, ZMod.castHom (dvd_refl p) k (u : ZMod p)) = -1 := by
    rw [← map_prod, hWilsonZ, map_neg, map_one]
  rw [hcast]
  have hp : p - 1 + 1 = p :=
    Nat.sub_add_cancel (Nat.Prime.pos (Fact.out : Nat.Prime p))
  have hsign : (-1 : k) ^ (p - 1) * (-1) = (-1 : k) ^ p := by
    rw [← pow_succ, hp]
  rw [hsign]

section PrimeCyclicEnumeration

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

variable (n : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K (n + 1))
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

local instance endpointDegreePrimeFact :
    Fact (Nat.Prime (Module.finrank F K)) :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The cyclic generator identifies the additive group of `ZMod p` with the
Galois group. -/
noncomputable def endpointGaloisZModEquiv :
    Multiplicative (ZMod (Module.finrank F K)) ≃* Gal(K/F) :=
  zmodMulEquivOfGenerator
    (PrimeCyclicExtension.generator_mem_zpowers F K)
    (PrimeCyclicExtension.galoisCard_eq_degree F K)

/-- Under the cyclic enumeration, nonzero residues are exactly the
nonidentity Galois automorphisms. -/
noncomputable def endpointNonidentityEquivZModUnits :
    (ZMod (Module.finrank F K))ˣ ≃
      {sigma : Gal(K/F) // sigma ≠ 1} where
  toFun u := ⟨endpointGaloisZModEquiv F K (Multiplicative.ofAdd (u : ZMod _)), by
    intro hsigma
    have hpre : Multiplicative.ofAdd (u : ZMod (Module.finrank F K)) = 1 :=
      (endpointGaloisZModEquiv F K).injective
        (hsigma.trans (endpointGaloisZModEquiv F K).map_one.symm)
    exact u.ne_zero (ofAdd_eq_one.mp hpre)⟩
  invFun sigma := Units.mk0
    ((endpointGaloisZModEquiv F K).symm sigma.1).toAdd (by
      intro hz
      apply sigma.2
      calc
        sigma.1 = endpointGaloisZModEquiv F K
            ((endpointGaloisZModEquiv F K).symm sigma.1) :=
          ((endpointGaloisZModEquiv F K).apply_symm_apply sigma.1).symm
        _ = endpointGaloisZModEquiv F K (Multiplicative.ofAdd 0) := by
          apply congrArg (endpointGaloisZModEquiv F K)
          simpa using congrArg Multiplicative.ofAdd hz
        _ = 1 := (endpointGaloisZModEquiv F K).map_one)
  left_inv u := by
    apply Units.ext
    exact congrArg Multiplicative.toAdd
      ((endpointGaloisZModEquiv F K).symm_apply_apply
        (Multiplicative.ofAdd (u : ZMod (Module.finrank F K))))
  right_inv sigma := by
    apply Subtype.ext
    exact (endpointGaloisZModEquiv F K).apply_symm_apply sigma.1

noncomputable def endpointLowerBreakElement (sigma : Gal(K/F)) :
    lowerRamificationGroup F K (((n + 1 : ℕ) : ℤ)) :=
  ⟨sigma, by rw [ht.1]; trivial⟩

noncomputable def endpointGradedGenerator :
    LowerRamificationGraded F K (((n + 1 : ℕ) : ℤ)) :=
  lowerRamificationGradedMk F K (((n + 1 : ℕ) : ℤ))
    (endpointLowerBreakElement F K n ht (PrimeCyclicExtension.generator F K))

/-- The residual displacement of the fixed cyclic generator. -/
noncomputable def endpointRamificationLambda : ResidueField K :=
  ramificationResidueCoordinateAddHom F K n pi hpi hgen
    (Additive.ofMul (endpointGradedGenerator F K n ht))

/-- The base-field version of the residual ramification displacement used
by the derivative calculation. -/
noncomputable def endpointNormalizedDerivativeCriticalLambda
    (hres : residueDegree F K = 1) : ResidueField F :=
  (endpointResidueEquiv F K hres).symm
    (endpointRamificationLambda F K n ht pi hpi hgen)

@[simp] theorem endpointResidueEquiv_normalizedDerivativeCriticalLambda
    (hres : residueDegree F K = 1) :
    endpointResidueEquiv F K hres
        (endpointNormalizedDerivativeCriticalLambda F K n ht pi hpi hgen hres) =
      endpointRamificationLambda F K n ht pi hpi hgen :=
  (endpointResidueEquiv F K hres).apply_symm_apply _

theorem endpointGaloisZModEquiv_apply_val
    (u : ZMod (Module.finrank F K)) :
    endpointGaloisZModEquiv F K (Multiplicative.ofAdd u) =
      PrimeCyclicExtension.generator F K ^ (u.val : ℤ) := by
  letI : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
  calc
    endpointGaloisZModEquiv F K (Multiplicative.ofAdd u) =
        endpointGaloisZModEquiv F K
          (Multiplicative.ofAdd ((u.val : ℤ) : ZMod (Module.finrank F K))) := by
      congr 2
      simpa using (ZMod.natCast_zmod_val u).symm
    _ = PrimeCyclicExtension.generator F K ^ (u.val : ℤ) :=
      zmodMulEquivOfGenerator_apply_ofAdd_intCast
        (PrimeCyclicExtension.generator_mem_zpowers F K)
        (PrimeCyclicExtension.galoisCard_eq_degree F K) (u.val : ℤ)

theorem endpointGradedClass_zmod
    (u : ZMod (Module.finrank F K)) :
    lowerRamificationGradedMk F K (((n + 1 : ℕ) : ℤ))
        (endpointLowerBreakElement F K n ht
          (endpointGaloisZModEquiv F K (Multiplicative.ofAdd u))) =
      endpointGradedGenerator F K n ht ^ u.val := by
  rw [endpointGaloisZModEquiv_apply_val]
  change lowerRamificationGradedMk F K (((n + 1 : ℕ) : ℤ))
      (endpointLowerBreakElement F K n ht
        (PrimeCyclicExtension.generator F K ^ (u.val : ℤ))) = _
  have hlower : endpointLowerBreakElement F K n ht
      (PrimeCyclicExtension.generator F K ^ (u.val : ℤ)) =
      (endpointLowerBreakElement F K n ht
        (PrimeCyclicExtension.generator F K)) ^ (u.val : ℤ) := by
    apply Subtype.ext
    rfl
  rw [hlower, map_zpow]
  rfl

theorem endpointResidueDisplacement_zmod
    (u : ZMod (Module.finrank F K)) :
    lowerRamificationResidueDisplacement F K
        (endpointLowerBreakElement F K n ht
          (endpointGaloisZModEquiv F K (Multiplicative.ofAdd u)))
        (pi : K) hpi =
      (u.val : ResidueField K) *
        endpointRamificationLambda F K n ht pi hpi hgen := by
  rw [← ramificationResidueCoordinateAddHom_mk F K n pi hpi hgen]
  rw [endpointGradedClass_zmod F K n ht u]
  change ramificationResidueCoordinateAddHom F K n pi hpi hgen
      (Additive.ofMul (endpointGradedGenerator F K n ht ^ u.val)) = _
  rw [ofMul_pow, map_nsmul]
  change u.val • endpointRamificationLambda F K n ht pi hpi hgen = _
  rw [nsmul_eq_mul]

end PrimeCyclicEnumeration

end

end LanglandsFirstMainLemma
