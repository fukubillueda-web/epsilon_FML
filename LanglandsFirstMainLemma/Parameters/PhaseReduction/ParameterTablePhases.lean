import LanglandsFirstMainLemma.Parameters.High
import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Parameters.PhaseReduction.StationaryData

/-!
# Stable-high and low parameter-table phase adapters

This module contains source-faithful compatible representatives for the
stable high table, the intermediate odd and wild-quadratic phase adapters,
and the high/low parameter-table nonemptiness bridges. No representative
or normalization is changed.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Stable high compatible representatives

The stable odd row of the high parameter table is an equality of quotient
classes for the common denominator pair.  The following adapter starts with
an explicitly supplied downstairs representative and maps that same field
element upstairs.  The existential depth in the Prop-valued table is used
only to prove the resulting quotient equality; it is never eliminated to
choose data. -/

namespace HighStableOddParameterData

variable (F K : Type)
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
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (hd : t + 1 ≤ d)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

/-- Map a supplied downstairs representative through the stable high row.
For the common denominator pair the explicit denominator-scaled map is
ordinary base-field inclusion.  In particular, no representative is chosen
from either quotient class. -/
def upstairsRepresentative
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF) :
    StationaryClassRepresentative K chiK psiK hK
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
    latticeQuotientMk K (Int.natCast_nonneg dK) cK =
        denominatorScaledAlgebraMap F K d dK hdepth gammaF
          (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (latticeQuotientMk F (Int.natCast_nonneg d) R.representative) := by
            rw [denominatorScaledAlgebraMap_common_mk]
    _ = denominatorScaledAlgebraMap F K d dK hdepth gammaF
          (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
            rw [R.represents]
    _ = stationaryCoefficientClass K chiK psiK hK
          (Units.map (algebraMap F K) gammaF) H.commonDenominator := by
            exact hclass.symm

/-- The compatible upstairs representative is literally the supplied
downstairs field element viewed in `K`. -/
@[simp]
theorem upstairsRepresentative_coe
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF) :
    ((upstairsRepresentative F K ht hres pi hpi hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R).representative : K) =
      algebraMap F K (R.representative : F) :=
  rfl

/-- Insert the compatible upstairs representative into Lamprecht's formula
at the actual upstairs conductor and depth.  In the odd branch the critical
coordinate remains part of the complete phase. -/
def upstairsPhase
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    LocalLamprechtPhaseData K chiK psiK := by
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF, H.commonDenominator⟩
  exact localPhaseOfStationaryClass hK Gamma
    (upstairsRepresentative F K ht hres pi hpi hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R) C

/-- The two complete Lamprecht phases built from one supplied stable-row
representative.  The fields retain their separate actual conductors, depths,
and critical coordinates. -/
structure CompatiblePhasePair
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF) where
  downstairs : LocalLamprechtPhaseData F chiF psiF
  upstairs : LocalLamprechtPhaseData K chiK psiK

/-- Build the stable high pair without identifying the two quotient types
or discarding either parity-specific critical factor. -/
def compatiblePhasePair
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK) :
    CompatiblePhasePair F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK
      hchi hpsi hodd hd gammaF hgammaF H := by
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  exact
    { downstairs := localPhaseOfStationaryClass hF GammaF R CF
      upstairs := upstairsPhase F K ht hres pi hpi hgen chiF chiK psiF psiK
        hF hK hchi hpsi hodd hd gammaF hgammaF H R CK }

end HighStableOddParameterData

/-- The field value underlying an element of `U_E^0` is integral. -/
theorem unitFiltrationZeroIntegral
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (u : unitFiltration E 0) :
    (((u : unitFiltration E 0) : Eˣ) : E) ∈ lattice E 0 := by
  rw [mem_lattice]
  have hu := (mem_unitFiltration_zero E (u : Eˣ)).1 u.property
  rw [hu]
  simp

/-! The following adapters expose the representatives selected by the high
tables as literal inputs to Lamprecht. -/

namespace OddIntermediateHighProductData

variable (F K : Type)
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
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (htpos : 0 < t)
  (hlower : t + 1 ≤ chiF.conductor)
  (hupper : chiF.conductor < 2 * (t + 1))
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

/-- Each lower factor selected by the odd high-product table is retained at
that twist's actual decomposition and quotient depth. -/
def factorRepresentative
    (Q : OddIntermediateHighProductData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    StationaryClassRepresentative F twist psiF
      (Q.factorDecomposition j) gammaF (Q.factorDenominator j) := by
  dsimp only
  exact StationaryClassRepresentative.ofCoefficientRepresentative
    ⟨(((Q.quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F),
      unitFiltrationZeroIntegral F (Q.quotientProduct.factors j)⟩
    (Q.factor_class j)

/-- The selected upstairs high-product factor is retained as its quotient
class representative, with the proved common denominator. -/
def upstairsRepresentative
    (Q : OddIntermediateHighProductData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF) :
    StationaryClassRepresentative K chiK psiK hK
      (Units.map (algebraMap F K) gammaF)
      (highParameter_intermediate_commonDenominator F K ht hres pi hpi hgen
        chiF chiK psiF psiK hminimal hchi hpsi hlower gammaF hgammaF) :=
  StationaryClassRepresentative.ofCoefficientRepresentative
    ⟨(((Q.quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K),
      unitFiltrationZeroIntegral K Q.quotientProduct.upstairs⟩
    Q.upstairs_class

/-- Insert the selected upstairs representative into its actual Lamprecht
parity branch. -/
def upstairsPhase
    (Q : OddIntermediateHighProductData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    LocalLamprechtPhaseData K chiK psiK := by
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF,
      highParameter_intermediate_commonDenominator F K ht hres pi hpi hgen
        chiF chiK psiF psiK hminimal hchi hpsi hlower gammaF hgammaF⟩
  exact localPhaseOfStationaryClass hK Gamma (Q.upstairsRepresentative) C

/-- Insert one selected lower factor into Lamprecht at the new conductor
carried by `factorDecomposition`; no old-layer class is reused. -/
def factorPhase
    (Q : OddIntermediateHighProductData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    LocalLamprechtPhaseData F twist psiF := by
  dsimp only
  let Gamma : AdmissibleGamma F
      (ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chiF
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))) psiF :=
    ⟨gammaF, Q.factorDenominator j⟩
  exact localPhaseOfStationaryClass (Q.factorDecomposition j) Gamma
    (factorRepresentative F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK
      hminimal hchi hpsi hodd htpos hlower hupper gammaF hgammaF Q j) C

end OddIntermediateHighProductData

/-! The high odd table's norm-character rows use the generator numerator
before the denominator change.  The following adapter keeps that supplied
quotient witness and performs the exact change to `gammaF / N(alpha1)`.
The subcritical target `alpha` is never silently identified with that exact
norm. -/

section HighOddNormPowerPhase

variable (F K : Type)
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
  (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (htpos : 0 < t)
  (hlower : t + 1 ≤ chiF.conductor)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

/-- Starting with the index-one numerator from one destructured high-table
witness, construct every nonidentity norm-character phase.  The resulting
representative is the Teichmüller scalar, the denominator is exactly
`gammaF / N(alpha1)`, and the class is at conductor `t+1`; nothing is
selected canonically from a quotient, and no equality `alpha = N(alpha1)`
is invented. -/
def highOddNormCharacterPowerPhase
    (a : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (alpha : Fˣ) (hacoe : (a : F) = (alpha : F))
    (alpha1 : Kˣ)
    (halpha1 : IsSubcriticalNormRepresentative F K
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
      ((t + 1) / 2) alpha alpha1)
    (ha : latticeQuotientMk F
        (sub_le_sub_left
          (highParameter_intermediate_normCharacterDepth
            F K ht hres pi hpi hgen htpos).int_le_conductor
          (chiF.conductor : ℤ)) a =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (1 : ZMod (Module.finrank F K)))).1
          (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _
            (highParameter_intermediate_indexOne_ne_one
              F K ht hres pi hpi hgen)))
        psiF (chiF.conductor : ℤ)
        (highParameter_intermediate_normCharacterDepth
          F K ht hres pi hpi hgen htpos)
        gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let hmu : mu ≠ 1 := by
      apply (ramifiedNormCharacterZModEquiv_ne_one_iff
        F K ht hres pi hpi hgen _).2
      intro h
      apply hj
      have h' := congrArg Multiplicative.toAdd h
      simpa using h'
    let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
    LocalLamprechtPhaseData F muData psiF := by
  dsimp only
  let p := Module.finrank F K
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod p))
  have htau : tau ≠ 1 := by
    simpa only [p, tau] using
      (highParameter_intermediate_indexOne_ne_one
        F K ht hres pi hpi hgen)
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    apply hj
    have h' := congrArg Multiplicative.toAdd h
    simpa using h'
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  have hT : 2 ≤ t + 1 := by omega
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let alphaNorm : Fˣ := normUnits F K alpha1
  have halphaOrd : ord F (alphaNorm : F) =
      ((((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ)) :
        WithTop ℤ) := by
    simpa only [alphaNorm, coe_normUnits] using halpha1.norm_order
  let gammaTau : Fˣ := gammaF / alphaNorm
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) := by
    dsimp only [gammaTau]
    rw [Units.val_div_eq_div_val, ord_div, hgammaF, halphaOrd]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    congr 1
    omega
  have hOne : (1 : F) ∈ lattice F 0 := by
    rw [mem_lattice, ord_one]
    exact le_rfl
  let oneRep : lattice F 0 := ⟨(1 : F), hOne⟩
  have hm : chiF.conductor = t + 1 + (chiF.conductor - (t + 1)) :=
    (Nat.add_sub_of_le hlower).symm
  have hselectedLinearization :=
    highParameter_intermediate_selectedAlpha_linearization
      F K ht hres pi hpi hgen htpos chiF psiF hm tau htau gammaF
        hgammaF a alpha hacoe alpha1 halpha1 (by
          simpa only [tau, p] using ha)
  have hTauClass : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        oneRep =
      stationaryCoefficientClass F tauData psiF hCrit gammaTau hgammaTau := by
    apply (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
      tauData psiF hCrit gammaTau hgammaTau oneRep).2
    intro x
    have hdepth : lowCriticalFloorDepth t + lowCriticalParity t =
        (t + 2) / 2 := by
      simp only [lowCriticalFloorDepth, lowCriticalParity]
      omega
    let xs : lattice F (((t + 2) / 2 : ℕ) : ℤ) :=
      ⟨(x : F), by
        rw [← hdepth]
        exact x.property⟩
    have hunit :
        (positiveUnitOfLattice F hCrit.variableDepth_pos x : Fˣ) =
          positiveUnitOfLattice F (by omega : 0 < (t + 2) / 2) xs := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, xs]
    change tau.1 (positiveUnitOfLattice F hCrit.variableDepth_pos x) = _
    rw [hunit, hselectedLinearization xs]
    apply congrArg psiF.character
    dsimp only [oneRep, gammaTau]
    simp only [Units.val_div_eq_div_val, alphaNorm, coe_normUnits, xs]
    have hnormNe : norm F K (alpha1 : K) ≠ 0 := by
      simpa only [← coe_normUnits] using
        (Units.ne_zero (normUnits F K alpha1))
    field_simp [hnormNe, Units.ne_zero gammaF]
  have hMuCoefficient :
      j.val • stationaryCoefficientClass F tauData psiF hCrit
          gammaTau hgammaTau =
        stationaryCoefficientClass F muData psiF hCrit
          gammaTau hgammaTau := by
    apply (stationaryCoefficientLamprechtEquivAtConductor F hCrit).injective
    rw [map_nsmul]
    calc
      j.val • (stationaryCoefficientLamprechtEquivAtConductor F hCrit)
          (stationaryCoefficientClass F tauData psiF hCrit
            gammaTau hgammaTau) =
          j.val • stationaryNumeratorClass F tauData psiF
            ((t + 1 : ℕ) : ℤ)
            (stationaryDepthOfConductorDecomposition F tauData hCrit)
            gammaTau hgammaTau := congrArg (fun z ↦ j.val • z)
              (stationaryCoefficientClass_toLamprecht
                F tauData psiF hCrit gammaTau hgammaTau)
      _ = stationaryNumeratorClass F muData psiF ((t + 1 : ℕ) : ℤ)
            (stationaryDepthOfConductorDecomposition F muData hCrit)
            gammaTau hgammaTau := by
        simpa only [tau, mu, tauData, muData, p, hCrit] using
          (highParameter_intermediate_normCharacterClass_eq_nsmul
            F K ht hres pi hpi hgen j hmu psiF ((t + 1 : ℕ) : ℤ)
              (stationaryDepthOfConductorDecomposition F tauData hCrit)
              gammaTau hgammaTau).symm
      _ = (stationaryCoefficientLamprechtEquivAtConductor F hCrit)
          (stationaryCoefficientClass F muData psiF hCrit
            gammaTau hgammaTau) :=
        (stationaryCoefficientClass_toLamprecht
          F muData psiF hCrit gammaTau hgammaTau).symm
  let hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  let lam := highIntermediateTeichmullerScalar F p hchar j
  have hlamInt : lam ∈ lattice F 0 := by
    rw [mem_lattice_zero_iff F]
    exact highParameter_intermediate_teichmuller_mem_integer F p hchar j
  let rep : lattice F 0 := ⟨lam, hlamInt⟩
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have hteich : lam - (j.val : F) ∈
      lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
    simpa only [lam, p, hchar] using
      (highParameter_intermediate_teichmuller_congruent
        F K (Module.finrank F K) (t + 1)
          (residueCharacteristic_eq_degree_of_positive_break
            F K ht htpos pi hpi hgen) rfl htrace j)
  have hTeichClass : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      j.val • latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        oneRep := by
    rw [← map_nsmul]
    apply (latticeQuotientMk_eq_mk_iff F
      (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)).2
    have honeSmul : ((j.val • oneRep : lattice F 0) : F) =
        (j.val : F) := by
      change j.val • (1 : F) = (j.val : F)
      simp only [nsmul_eq_mul, mul_one]
    rw [honeSmul]
    simpa only [rep, lam, Submodule.coe_mk,
      lowCriticalFloorDepth] using hteich
  have hclass : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F muData psiF hCrit
        gammaTau hgammaTau := by
    calc
      latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
          j.val • latticeQuotientMk F
            (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
            oneRep := hTeichClass
      _ = j.val • stationaryCoefficientClass F tauData psiF hCrit
          gammaTau hgammaTau := congrArg (fun z ↦ j.val • z) hTauClass
      _ = stationaryCoefficientClass F muData psiF hCrit
          gammaTau hgammaTau := hMuCoefficient
  let Gamma : AdmissibleGamma F muData psiF := ⟨gammaTau, hgammaTau⟩
  let R : StationaryClassRepresentative F muData psiF hCrit
      (Gamma : Fˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  exact localPhaseOfStationaryClass hCrit Gamma R C

end HighOddNormPowerPhase

namespace WildQuadraticHighProductData

variable (F K : Type)
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
  (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
  (hhigh : t + 1 ≤ chiF.conductor)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (tau : NormCharacter F K) (htau : tau ≠ 1)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

def baseRepresentative
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF) :
    StationaryClassRepresentative F chiF psiF hF gammaF hgammaF :=
  StationaryClassRepresentative.ofCoefficientRepresentative
    ⟨(((Q.quotientProduct.factors true : unitFiltration F 0) : Fˣ) : F),
      unitFiltrationZeroIntegral F (Q.quotientProduct.factors true)⟩
    Q.beta_factor_class

def twistRepresentative
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF) :
    let hTw := wildQuadraticHighTwistDecomposition
      F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau
    let hgammaTw := highParameter_wildQuadratic_twistDenominator
      F K ht hres pi hpi hgen chiF psiF hminimal hhigh tau htau
        gammaF hgammaF
    StationaryClassRepresentative F
      (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau)
      psiF hTw gammaF hgammaTw := by
  dsimp only
  exact StationaryClassRepresentative.ofCoefficientRepresentative
    ⟨(((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F),
      unitFiltrationZeroIntegral F (Q.quotientProduct.factors false)⟩
    Q.twist_factor_class

def upstairsRepresentative
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF) :
    StationaryClassRepresentative K chiK psiK hK
      (Units.map (algebraMap F K) gammaF) Q.parameters.commonDenominator :=
  StationaryClassRepresentative.ofCoefficientRepresentative
    ⟨(((Q.quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K),
      unitFiltrationZeroIntegral K Q.quotientProduct.upstairs⟩
    Q.upstairs_class

/-- The selected high quadratic twist literally retains the essential
break-level unit from the upstream parameter package. -/
theorem selectedTwist_retains_breakUnit
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF) :
    (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) =
      (Q.parameters.representatives.beta : F) +
        (((normUnits F K Q.parameters.representatives.alpha1) *
          (Q.parameters.representatives.delta : Fˣ) : Fˣ) : F) :=
  Q.correction_unit_retained

/-- The nontrivial norm-character row uses the representative `1` supplied
by the same high-quadratic parameter package, with its changed denominator
`gammaF / cF`.  The datum remains a quotient-class representative at the
actual conductor `t + 1`. -/
def tauRepresentative
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF) :
    let tauData := wildQuadraticHighTauData
      F K ht hres pi hpi hgen tau htau
    let hTau := wildQuadraticHighTauDecomposition
      F K ht hres pi hpi hgen htpos tau htau
    StationaryClassRepresentative F tauData psiF hTau
      Q.parameters.representatives.gammaTau
      Q.parameters.representatives.gammaTau_order := by
  dsimp only
  exact StationaryClassRepresentative.ofCoefficientRepresentative
    ⟨(1 : F), by rw [mem_lattice, ord_one]; exact le_rfl⟩
    Q.parameters.representatives.tau_unit_class

def upstairsPhase
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    LocalLamprechtPhaseData K chiK psiK := by
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF, Q.parameters.commonDenominator⟩
  exact localPhaseOfStationaryClass hK Gamma Q.upstairsRepresentative C

def basePhase
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F chiF psiF := by
  let Gamma : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  exact localPhaseOfStationaryClass hF Gamma Q.baseRepresentative C

/-- Insert the actual nontrivial norm-character quotient class at conductor
`t + 1`; in particular this does not reuse the base-character class. -/
def tauPhase
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF)
    (C : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2)) :
    LocalLamprechtPhaseData F
      (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF := by
  let hTau := wildQuadraticHighTauDecomposition
    F K ht hres pi hpi hgen htpos tau htau
  let Gamma : AdmissibleGamma F
      (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF :=
    ⟨Q.parameters.representatives.gammaTau,
      Q.parameters.representatives.gammaTau_order⟩
  exact localPhaseOfStationaryClass hTau Gamma Q.tauRepresentative C

def twistPhase
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi
        tau htau gammaF hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F
      (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau) psiF := by
  let hTw := wildQuadraticHighTwistDecomposition
    F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau
  let hgammaTw := highParameter_wildQuadratic_twistDenominator
    F K ht hres pi hpi hgen chiF psiF hminimal hhigh tau htau
      gammaF hgammaF
  let Gamma : AdmissibleGamma F
      (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau) psiF :=
    ⟨gammaF, hgammaTw⟩
  exact localPhaseOfStationaryClass hTw Gamma Q.twistRepresentative C

end WildQuadraticHighProductData

section HighTablePhaseAdapters

variable (F K : Type)
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

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The public high table supplies one simultaneous odd-product choice, and
that same choice yields the upstairs phase and every actual-conductor twist
phase. -/
theorem highTableOddPhases_nonempty
    (H : HighConductorParameterTable)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hstrict : t + 1 < chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1))
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CFactor : ∀ _j : ZMod (Module.finrank F K),
      LamprechtCriticalCoordinate F d epsilon) :
    ∃ Q : OddIntermediateHighProductData F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
          hstrict.le hupper gammaF hgammaF,
      Nonempty (LocalLamprechtPhaseData K chiK psiK) ∧
      ∀ j : ZMod (Module.finrank F K),
        let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j)
        let twist := ramifiedNormCharacterOrbitTwistData
          F K ht hres pi hpi hgen chiF mu
        Nonempty (LocalLamprechtPhaseData F twist psiF) := by
  obtain ⟨Q⟩ := (H.highProduct F K ht hres pi hpi hgen).oddIntermediate
    chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper
      gammaF hgammaF
  refine ⟨Q, ⟨OddIntermediateHighProductData.upstairsPhase
    F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hminimal hchi hpsi
      hodd htpos hstrict.le hupper gammaF hgammaF Q CUp⟩, ?_⟩
  intro j
  exact ⟨OddIntermediateHighProductData.factorPhase
    F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hminimal hchi hpsi
      hodd htpos hstrict.le hupper gammaF hgammaF Q j (CFactor j)⟩

/-- The public high table supplies all three stationary wild-quadratic
Lamprecht packages from the same choice.  Its selected twist equation still
contains the table's essential break-level unit. -/
theorem highTableQuadraticPhases_nonempty
    (H : HighConductorParameterTable)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hstrict : t + 1 < chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CDown : LamprechtCriticalCoordinate F d epsilon)
    (CTau : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2)) :
    ∃ Q : WildQuadraticHighProductData F K ht hres pi hpi hgen
        hdegree htpos chiF chiK psiF psiK hF hK hminimal hstrict.le hchi hpsi
          tau htau gammaF hgammaF,
      Nonempty (LocalLamprechtPhaseData K chiK psiK) ∧
      Nonempty (LocalLamprechtPhaseData F chiF psiF) ∧
      Nonempty (LocalLamprechtPhaseData F
        (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau)
          psiF) ∧
      Nonempty (LocalLamprechtPhaseData F
        (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau)
          psiF) ∧
      (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) =
        (Q.parameters.representatives.beta : F) +
          (((normUnits F K Q.parameters.representatives.alpha1) *
            (Q.parameters.representatives.delta : Fˣ) : Fˣ) : F) := by
  obtain ⟨Q⟩ := (H.highProduct F K ht hres pi hpi hgen).wildQuadratic
    hdegree htpos chiF chiK psiF psiK hF hK hminimal hstrict.le hchi hpsi
      tau htau gammaF hgammaF
  refine ⟨Q,
    ⟨WildQuadraticHighProductData.upstairsPhase
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK hF hK
        hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q CUp⟩,
    ⟨WildQuadraticHighProductData.basePhase
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK hF hK
        hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q CDown⟩,
    ⟨WildQuadraticHighProductData.tauPhase
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK hF hK
        hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q CTau⟩,
    ⟨WildQuadraticHighProductData.twistPhase
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK hF hK
        hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q CDown⟩,
    Q.correction_unit_retained⟩

end HighTablePhaseAdapters

/-! Low-table representatives are inserted only after the table has supplied
them.  The two representatives explicitly contained in `P` give Type-valued
packages.  The upstairs and nonzero-twist representatives occur under
existentials in a Prop-valued table, so their adapters correctly return
`Nonempty` rather than choosing representatives. -/

section LowPhaseAdapters

variable (F K : Type)
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

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

variable {d epsilon : ℕ}
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (hLow : chiF.conductor ≤ t + 1)
  (delta : Fˣ) (epsilon₁ : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
  (hepsilon₁ : ord K (epsilon₁ : K) =
    (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ))
  (hT : 2 ≤ t + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon₁ : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
  (hgammaK : ord K (lowGammaK F K delta epsilon₁ : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth t) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
    (stationaryCoefficientClass F chiF psiF hF
      (lowGammaF F K delta epsilon₁) hgammaF))
  (D : LowConductorParameterTableData F K ht hres pi hpi hgen
    chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon₁
      hdelta hepsilon₁ hT hgammaF hgammaK P)

/-- Insert the exact base representative `beta=N(beta₁)` supplied by the
low table. -/
def lowBasePhase
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F chiF psiF := by
  let Gamma : AdmissibleGamma F chiF psiF :=
    ⟨lowGammaF F K delta epsilon₁, hgammaF⟩
  let R : StationaryClassRepresentative F chiF psiF hF
      (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
      represents := by simpa only [Gamma] using D.beta_native_class }
  exact localPhaseOfStationaryClass hF Gamma R C

/-- Insert the low table's exact norm-character generator representative
`alpha=N(alpha₁)` at conductor `t+1` and its actual half-depth. -/
def lowNormCharacterGeneratorPhase
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      psiF := by
  let tauData := quasiCharDataOfIsConductor F
    (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (lowNormCharacterGenerator F K ht hres pi hpi hgen)
      (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F tauData psiF := ⟨delta, hdelta⟩
  let R : StationaryClassRepresentative F tauData psiF hCrit
      (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
      represents := by
        simpa only [tauData, hCrit, Gamma] using D.alpha_native_class }
  exact localPhaseOfStationaryClass hCrit Gamma R C

/-- Every nonzero power of the low-table generator gets its actual
conductor-`t+1` stationary class.  The representative is the table-supplied
`alpha` multiplied by the corresponding Teichmüller scalar; both the scalar
class computation and the character-power class computation are proved at
the critical half-depth. -/
def lowNormCharacterPowerPhase
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    let hpow := lowGeneratorPower_ne_one F K ht hres pi hpi hgen j hj
    let powerData := quasiCharDataOfIsConductor F (tau ^ j.val).1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (tau ^ j.val) hpow)
    LocalLamprechtPhaseData F powerData psiF := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 :=
    lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  have hpow : tau ^ j.val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen j hj
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let powerData := quasiCharDataOfIsConductor F (tau ^ j.val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ j.val) hpow)
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F powerData psiF := ⟨delta, hdelta⟩
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
      (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
  let omegaF : F :=
    ((primeTeichmuller F (Module.finrank F K) hchar j :
      ringOfIntegers F) : F)
  have halphaOrd : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  have hrep : omegaF * (P.alpha : F) ∈ lattice F 0 :=
    mul_mem_lattice F
      ((mem_lattice_zero_iff F).2
        (primeTeichmuller F (Module.finrank F K) hchar j).property)
      ((mem_lattice_and_not_mem_succ_iff F).2 halphaOrd).1
  let rep : lattice F 0 := ⟨omegaF * (P.alpha : F), hrep⟩
  have hteich : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      j.val • latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
          lattice F 0) := by
    simpa only [omegaF, rep] using
      (lowTeichmuller_nsmul_class F K (Module.finrank F K)
        ht hres pi hpi hgen rfl hchar j P.alpha halphaOrd)
  have hpowerClass :
      j.val • stationaryCoefficientClass F tauData psiF hCrit delta hdelta =
        stationaryCoefficientClass F powerData psiF hCrit delta hdelta := by
    apply (stationaryCoefficientLamprechtEquivAtConductor F hCrit).injective
    rw [map_nsmul]
    calc
      j.val • (stationaryCoefficientLamprechtEquivAtConductor F hCrit)
          (stationaryCoefficientClass F tauData psiF hCrit delta hdelta) =
          j.val • stationaryNumeratorClass F tauData psiF
            ((t + 1 : ℕ) : ℤ)
            (stationaryDepthOfConductorDecomposition F tauData hCrit)
            delta hdelta := congrArg (fun x ↦ j.val • x)
              (stationaryCoefficientClass_toLamprecht
                F tauData psiF hCrit delta hdelta)
      _ = stationaryNumeratorClass F powerData psiF ((t + 1 : ℕ) : ℤ)
            (stationaryDepthOfConductorDecomposition F powerData hCrit)
            delta hdelta := by
        simpa [tauData, powerData, hCrit] using
          (normCharacterPower_stationaryClass_eq_nsmul
            F K ht hres pi hpi hgen tau htau j.val hpow psiF
              ((t + 1 : ℕ) : ℤ)
              (stationaryDepthOfConductorDecomposition F tauData hCrit)
              delta hdelta).symm
      _ = (stationaryCoefficientLamprechtEquivAtConductor F hCrit)
          (stationaryCoefficientClass F powerData psiF hCrit delta hdelta) :=
        (stationaryCoefficientClass_toLamprecht
          F powerData psiF hCrit delta hdelta).symm
  have hclass : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F powerData psiF hCrit delta hdelta := by
    calc
      latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
          j.val • latticeQuotientMk F
            (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
            (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
              lattice F 0) := hteich
      _ = j.val • stationaryCoefficientClass F tauData psiF hCrit
          delta hdelta := congrArg (fun x ↦ j.val • x) P.alpha_norm_class
      _ = stationaryCoefficientClass F powerData psiF hCrit delta hdelta :=
        hpowerClass
  let R : StationaryClassRepresentative F powerData psiF hCrit
      (Gamma : Fˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  exact localPhaseOfStationaryClass hCrit Gamma R C

/-- Insert the existential upstairs representative at the source
decomposition's actual conductor and depth.  No Type-valued choice is
extracted from the Prop-valued table. -/
theorem lowUpstairsPhase_nonempty
    (table : LowConductorParameterTableData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon₁
        hdelta hepsilon₁ hT hgammaF hgammaK P)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    Nonempty (LocalLamprechtPhaseData K chiK psiK) := by
  let hK := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    chiF hminimal chiK hchi hF hLow).sourceDecomposition
  obtain ⟨hcand, hc⟩ := table.upstairs_class
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon₁, hgammaK⟩
  let R : StationaryClassRepresentative K chiK psiK hK
      (Gamma : Kˣ) Gamma.property :=
    { representative := ⟨lowUpstairsCandidate F K epsilon₁ P, hcand⟩
      represents := by simpa only [hK, Gamma] using hc }
  exact ⟨localPhaseOfStationaryClass hK Gamma R C⟩

/-- For a nonzero norm-character index, insert the affine representative
supplied existentially by the low table.  Its decomposition is the newly
proved conductor-`t+1` decomposition, including at the boundary. -/
theorem lowNonzeroTwistPhase_nonempty
    (table : LowConductorParameterTableData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon₁
        hdelta hepsilon₁ hT hgammaF hgammaK P)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    Nonempty (LocalLamprechtPhaseData F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        chiF hminimal hLow j hj) psiF) := by
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
      (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
  let omegaF : F :=
    ((primeTeichmuller F (Module.finrank F K) hchar j :
      ringOfIntegers F) : F)
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    chiF hminimal hLow j hj
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  obtain ⟨haff, hc⟩ := table.nonzero_twist_class j hj
  let Gamma : AdmissibleGamma F twist psiF := ⟨delta, hdelta⟩
  let R : StationaryClassRepresentative F twist psiF hCrit
      (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨omegaF * (P.alpha : F) +
          (lowEpsilon F K epsilon₁ : F) * (P.beta : F), haff⟩
      represents := by
        simpa only [hchar, omegaF, twist, hCrit, Gamma] using hc }
  exact ⟨localPhaseOfStationaryClass hCrit Gamma R C⟩

end LowPhaseAdapters


/-! ## Shared low base admissible factor -/

section SharedLowBaseAdmissibleFactor

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hLow : (data.twistData 1).conductor ≤ t + 1)
  (delta : Fˣ) (epsilon1 : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hepsilon1 : ord K (epsilon1 : K) =
    (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ))
  (hT : 2 ≤ t + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth t) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
        delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF))
  (table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The low base twist retains its longer denominator `lowGammaF`. -/
theorem lowBasePhase_admissibleFactor
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table C).admissibleFactor =
      (data.twistData 1).character
        (lowGammaF F K delta epsilon1) := by
  unfold lowBasePhase
  apply localPhaseOfStationaryClass_admissibleFactor

end SharedLowBaseAdmissibleFactor

end

end LanglandsFirstMainLemma
