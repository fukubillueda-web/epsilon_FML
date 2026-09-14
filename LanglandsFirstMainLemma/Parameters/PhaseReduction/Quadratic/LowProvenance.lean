import LanglandsFirstMainLemma.Parameters.PhaseReduction.Quadratic.Core
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ParameterTablePhases

/-!
# Low-table provenance for wild-quadratic assembly

This module contains the proof-bearing low-table source, phase,
correction, and complete-result data for the wild-quadratic assembly.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Low-table provenance for the wild-quadratic assembly -/

section QuadraticLowProvenance

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
  (hdegree : Module.finrank F K = 2)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (D : FirstMainPhaseData F K globalChi globalPsi data)
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

/-- In the quadratic branch, residue index one is genuinely nonzero. -/
theorem lowQuadratic_one_ne_zero :
    (1 : ZMod (Module.finrank F K)) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_one, ZMod.val_zero] at hv
  omega

/-- The actual two-element norm-character indexing.  Boolean `true` is the
identity endpoint (residue index zero), while `false` is the low-table
generator (residue index one). -/
def lowQuadraticNormCharacterIndex : Bool ≃ NormCharacter F K :=
  Equiv.boolNot.trans <|
    finTwoEquiv.symm.trans <|
      (ZMod.finEquiv 2).toEquiv.trans <|
        (ZMod.ringEquivCongr hdegree.symm).toEquiv.trans <|
          Multiplicative.ofAdd.trans <|
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv

@[simp]
theorem lowQuadraticNormCharacterIndex_true :
    lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen hdegree true =
      1 := by
  dsimp only [lowQuadraticNormCharacterIndex, Equiv.trans_apply]
  rw [show Equiv.boolNot true = false by rfl]
  rw [show finTwoEquiv.symm false = (0 : Fin 2) by rfl]
  simp

@[simp]
theorem lowQuadraticNormCharacterIndex_false :
    lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen hdegree false =
      lowNormCharacterGenerator F K ht hres pi hpi hgen := by
  dsimp only [lowQuadraticNormCharacterIndex, Equiv.trans_apply]
  rw [show Equiv.boolNot false = true by rfl]
  rw [show finTwoEquiv.symm true = (1 : Fin 2) by rfl]
  change (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen)
      (Multiplicative.ofAdd
        ((ZMod.ringEquivCongr hdegree.symm)
          ((ZMod.finEquiv 2) (1 : Fin 2)))) =
    lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hinput : Multiplicative.ofAdd
        ((ZMod.ringEquivCongr hdegree.symm)
          ((ZMod.finEquiv 2) (1 : Fin 2))) =
      Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)) := by
    apply Multiplicative.ofAdd.injective
    simp
  rw [hinput, lowNormCharacterGenerator]

/-- An explicit witness for the low table's existential upstairs stationary
class.  It is data supplied by the caller, not a selected representative. -/
structure LowQuadraticUpstairsWitness where
  source_table : table = table
  representative : lattice K 0
  representative_eq : (representative : K) =
    lowUpstairsCandidate F K epsilon1 P
  represents : latticeQuotientMk K (by omega) representative =
    stationaryCoefficientClass K chiK psiK
      (lowNormPolynomialPrecision F K ht hres pi hpi hgen
        (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
      (lowGammaK F K delta epsilon1) hgammaK

/-- The table proves existence of the explicit upstairs witness without
turning the Prop-valued existential into a canonical field element. -/
theorem lowQuadraticUpstairsWitness_nonempty :
    Nonempty (LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) := by
  obtain ⟨hcand, hc⟩ := table.upstairs_class
  exact ⟨
    { source_table := rfl
      representative := ⟨lowUpstairsCandidate F K epsilon1 P, hcand⟩
      representative_eq := rfl
      represents := hc }⟩

/-- The explicit upstairs witness bundled as the stationary representative
of its actual source conductor and low denominator. -/
def lowQuadraticUpstairsStationaryRepresentative
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) :
    StationaryClassRepresentative K chiK psiK
      (lowNormPolynomialPrecision F K ht hres pi hpi hgen
        (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
      (lowGammaK F K delta epsilon1) hgammaK :=
  StationaryClassRepresentative.ofCoefficientRepresentative
    W.representative W.represents

/-- Unit associated to the explicitly supplied upstairs witness.  Its
nonvanishing is derived from the stationary quotient class. -/
def lowQuadraticUpstairsUnit
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) : Kˣ :=
  (lowQuadraticUpstairsStationaryRepresentative F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table W).unit

@[simp]
theorem lowQuadraticUpstairsUnit_coe
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) :
    (lowQuadraticUpstairsUnit F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W : K) = (W.representative : K) :=
  rfl

/-- Insert one explicitly supplied upstairs witness at its actual source
decomposition and low denominator. -/
def lowQuadraticUpstairsPhaseFromWitness
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    LocalLamprechtPhaseData K chiK psiK := by
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon1, hgammaK⟩
  exact localPhaseOfStationaryClass hSource Gamma
    (lowQuadraticUpstairsStationaryRepresentative F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W) C

/-- Transport the explicitly supplied low quadratic upstairs row to the
global computational package without changing its representative or exact
low denominator. -/
def lowQuadraticUpstairsPhaseForComputationalData
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar := by
  have hchiData : chiK.character = data.extensionQuasiChar.character := by
    rw [data.extensionQuasiChar_character, hchi,
      data.twistData_character]
    exact normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi
  have hpsiData : psiK.character = data.extensionAddChar.character := by
    rw [data.extensionAddChar_character, hpsi,
      data.baseAddChar_character]
    rfl
  exact transportLocalLamprechtPhaseData hchiData hpsiData
    (lowQuadraticUpstairsPhaseFromWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table W C)

/-- An explicit witness for the unique nonidentity low twist.  Its literal
common-denominator numerator is `alpha + epsilon*beta`. -/
structure LowQuadraticTwistWitness where
  source_table : table = table
  representative : lattice F 0
  representative_eq : (representative : F) =
    (P.alpha : F) + (lowEpsilon F K epsilon1 : F) * (P.beta : F)
  represents : latticeQuotientMk F (by omega) representative =
    stationaryCoefficientClass F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
        delta hdelta

/-- The nonzero-twist existential in the same low table gives the literal
`alpha + epsilon*beta` witness at residue index one. -/
theorem lowQuadraticTwistWitness_nonempty :
    Nonempty (LowQuadraticTwistWitness F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table) := by
  let hj := lowQuadratic_one_ne_zero (F := F) (K := K)
  obtain ⟨haff, hc⟩ := table.nonzero_twist_class
    (1 : ZMod (Module.finrank F K)) hj
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht (by omega) pi hpi hgen
  have homegaROI :
      primeTeichmuller F (Module.finrank F K) hchar
          (1 : ZMod (Module.finrank F K)) = 1 :=
    map_one (primeTeichmuller F (Module.finrank F K) hchar)
  have homega :
      ((primeTeichmuller F (Module.finrank F K) hchar
        (1 : ZMod (Module.finrank F K)) : ringOfIntegers F) : F) = 1 := by
    exact congrArg (fun z : ringOfIntegers F ↦ (z : F)) homegaROI
  have haff' : (P.alpha : F) +
      (lowEpsilon F K epsilon1 : F) * (P.beta : F) ∈ lattice F 0 := by
    simpa only [hchar, homega, one_mul] using haff
  exact ⟨
    { source_table := rfl
      representative := ⟨(P.alpha : F) +
          (lowEpsilon F K epsilon1 : F) * (P.beta : F), haff'⟩
      representative_eq := rfl
      represents := by simpa only [hchar, homega, one_mul] using hc }⟩

/-- The explicit nonidentity twist witness bundled at its newly constructed
conductor-`t+1` stationary class. -/
def lowQuadraticTwistStationaryRepresentative
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :
    StationaryClassRepresentative F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
      delta hdelta :=
  StationaryClassRepresentative.ofCoefficientRepresentative
    W.representative W.represents

/-- Unit associated to the explicit nonidentity twist witness. -/
def lowQuadraticTwistUnit
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) : Fˣ :=
  (lowQuadraticTwistStationaryRepresentative F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table W).unit

@[simp]
theorem lowQuadraticTwistUnit_coe
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :
    (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W : F) = (W.representative : F) :=
  rfl

/-- The actual source phase for the unique nonidentity low twist, before
transport to the proof-bearing global twist datum. -/
def lowQuadraticTwistPhaseSource
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K)))
      data.baseAddChar := by
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  have hgammaTw : ord F (delta : F) =
      ((((lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K))).conductor : ℤ) +
            data.baseAddChar.conductor : ℤ) : WithTop ℤ) := by
    simpa only [lowNonzeroTwistDatum_conductor] using hdelta
  let Gamma : AdmissibleGamma F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K)))
      data.baseAddChar := ⟨delta, hgammaTw⟩
  exact localPhaseOfStationaryClass hCrit Gamma
    (lowQuadraticTwistStationaryRepresentative F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table W) C

/-- The actual low norm-character row at residue index one.  This definition
calls `lowNormCharacterPowerPhase` at `j=1`; only the proof-bearing local
quasi-character datum is transported to the global computational package. -/
def lowQuadraticNormPhaseForComputationalData
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (data.normCharacterData
        (lowNormCharacterGenerator F K ht hres pi hpi hgen))
      data.baseAddChar := by
  let j : ZMod (Module.finrank F K) := 1
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hj : j ≠ 0 := lowQuadratic_one_ne_zero (F := F) (K := K)
  have hpow : tau ^ j.val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen j hj
  let powerData := quasiCharDataOfIsConductor F (tau ^ j.val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ j.val) hpow)
  have hpower_eq : tau ^ j.val = tau := by
    simpa only [tau, j, lowNormCharacterGenerator] using
      (lowNormCharacterGenerator_pow F K ht hres pi hpi hgen j).symm
  have hdata : powerData = data.normCharacterData tau := by
    apply LocalQuasiCharData.ext_character F
    rw [quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
    exact congrArg (fun mu : NormCharacter F K ↦ mu.1) hpower_eq
  let sourcePhase := lowNormCharacterPowerPhase F K ht hres pi hpi hgen
    (data.twistData 1) data.baseAddChar hF delta epsilon1 hdelta hT hgammaF
      P j hj C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- The manuscript's normalized denominator for the nonidentity low norm
row.  The simultaneous low table supplies `alpha` as an exact norm, but the
displayed Lamprecht pair is literally `(delta / alpha, 1)`. -/
def lowQuadraticNormalizedTauGamma : Fˣ :=
  delta / P.alpha

/-- The normalized denominator remains admissible because the exact norm
`alpha` has depth zero. -/
theorem lowQuadraticNormalizedTauGamma_order :
    ord F
        (lowQuadraticNormalizedTauGamma F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
  have halphaOrd : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  rw [lowQuadraticNormalizedTauGamma, Units.val_div_eq_div_val, ord_div,
    hdelta, halphaOrd, sub_zero]

/-- The normalized low norm row before transport to the proof-bearing
computational datum.  Its stationary coefficient is the literal lattice
representative `1`; this is proved by change of denominator from the table's
quotient class and does not choose a representative of a quotient. -/
def lowQuadraticNormalizedTauPhaseSource
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
      (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let gamma' := lowQuadraticNormalizedTauGamma F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P
  have hgamma' : ord F (gamma' : F) =
      (((tauData.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    simpa only [tauData, quasiCharDataOfIsConductor_conductor, gamma'] using
      (lowQuadraticNormalizedTauGamma_order F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P)
  let Gamma' : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨gamma', hgamma'⟩
  let oneRep : lattice F 0 := ⟨1, by simp⟩
  have hclass : latticeQuotientMk F (by omega) oneRep =
      stationaryCoefficientClass F tauData data.baseAddChar hCrit
        gamma' hgamma' := by
    rw [stationaryCoefficientClass_changeDenominator F tauData
      data.baseAddChar hCrit delta gamma' hdelta hgamma']
    rw [← P.alpha_norm_class, stationaryCoefficientScale_mk]
    congr 1
    apply Subtype.ext
    change (1 : F) =
      denominatorChangeRatio F delta gamma' * (P.alpha : F)
    symm
    simp only [gamma', lowQuadraticNormalizedTauGamma,
      denominatorChangeRatio, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero]
  let R : StationaryClassRepresentative F tauData data.baseAddChar hCrit
      (Gamma' : Fˣ) Gamma'.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative oneRep hclass
  simpa only [tauData] using
    (localPhaseOfStationaryClass hCrit Gamma' R C)

/-- The exact normalized low norm row, transported only across equality of
the proof-bearing quasi-character data. -/
def lowQuadraticNormalizedTauPhaseForComputationalData
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (data.normCharacterData
        (lowNormCharacterGenerator F K ht hres pi hpi hgen))
      data.baseAddChar := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
      (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))
  have hdata : tauData = data.normCharacterData tau := by
    apply LocalQuasiCharData.ext_character F
    rw [quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
  let sourcePhase := lowQuadraticNormalizedTauPhaseSource F K ht hres pi
    hpi hgen data hF delta epsilon1 hdelta hT hgammaF P C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- Insert the explicit unique nonidentity twist witness at the newly built
conductor-`t+1` stationary class and transport only its proof-bearing datum. -/
def lowQuadraticTwistPhaseForComputationalData
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (data.twistData
        (lowNormCharacterGenerator F K ht hres pi hpi hgen))
      data.baseAddChar := by
  let j : ZMod (Module.finrank F K) := 1
  have hj : j ≠ 0 := lowQuadratic_one_ne_zero (F := F) (K := K)
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow j hj
  have hdata : twist = data.twistData tau := by
    rw [show twist = ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen (data.twistData 1) tau by
      simpa only [twist, tau, j, lowNormCharacterGenerator] using
        (lowNonzeroTwistDatum_eq_actual F K ht hres pi hpi hgen
          (data.twistData 1) hminimal hLow j hj)]
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  let sourcePhase := lowQuadraticTwistPhaseSource F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table W C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- The low table's normalized norm ratio bundled as a field unit. -/
def lowQuadraticNormalizedNormUnit : Fˣ :=
  lowEpsilon F K epsilon1 * P.beta / P.alpha

@[simp]
theorem lowQuadraticNormalizedNormUnit_coe :
    (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P : F) =
      (lowEpsilon F K epsilon1 : F) * (P.beta : F) / (P.alpha : F) :=
  by
    unfold lowQuadraticNormalizedNormUnit
    simp only [Units.val_div_eq_div_val, Units.val_mul]

/-- The normalized norm row exposes the manuscript's literal admissible
denominator `delta / alpha`. -/
theorem lowQuadraticNormalizedTauPhase_admissibleFactor
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi
      hgen data hF delta epsilon1 hdelta hT hgammaF P C).admissibleFactor =
      ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
        (delta / P.alpha) : ℂ) := by
  calc
    _ = (lowQuadraticNormalizedTauPhaseSource F K ht hres pi hpi hgen data
        hF delta epsilon1 hdelta hT hgammaF P C).admissibleFactor := by
      unfold lowQuadraticNormalizedTauPhaseForComputationalData
      exact transportLocalLamprechtPhaseData_admissibleFactor _ _ _
    _ = _ := by
      unfold lowQuadraticNormalizedTauPhaseSource
      rw [localPhaseOfStationaryClass_admissibleFactor,
        quasiCharDataOfIsConductor_character]
      simp only [lowQuadraticNormalizedTauGamma]

/-- The normalized norm row's positive additive value is exactly the value
at `1 / (delta / alpha)`. -/
theorem lowQuadraticNormalizedTauPhase_elementaryAdditiveFactor
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData.elementaryAdditiveFactor
      (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi
        hgen data hF delta epsilon1 hdelta hT hgammaF P C) =
      (globalPsi
        ((1 : F) / ((delta / P.alpha : Fˣ) : F)) : ℂ) := by
  calc
    _ = LocalLamprechtPhaseData.elementaryAdditiveFactor
        (lowQuadraticNormalizedTauPhaseSource F K ht hres pi hpi hgen data
          hF delta epsilon1 hdelta hT hgammaF P C) := by
      unfold lowQuadraticNormalizedTauPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor _ _ _
    _ = _ := by
      unfold lowQuadraticNormalizedTauPhaseSource
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
        data.baseAddChar_character]
      rfl

/-- The normalized norm row's inverse multiplicative value is the value at
the literal representative `1`, hence is one. -/
theorem lowQuadraticNormalizedTauPhase_elementaryMultiplicativeFactor
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData.elementaryMultiplicativeFactor
      (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi
        hgen data hF delta epsilon1 hdelta hT hgammaF P C) = 1 := by
  calc
    _ = LocalLamprechtPhaseData.elementaryMultiplicativeFactor
        (lowQuadraticNormalizedTauPhaseSource F K ht hres pi hpi hgen data
          hF delta epsilon1 hdelta hT hgammaF P C) := by
      unfold lowQuadraticNormalizedTauPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor _ _ _
    _ = _ := by
      unfold lowQuadraticNormalizedTauPhaseSource
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor,
        quasiCharDataOfIsConductor_character]
      rw [show (1 : ℂ) =
          (((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
            (1 : Fˣ) : ℂ))⁻¹ by simp]
      congr 3
      apply Units.ext
      rw [StationaryClassRepresentative.coe_unit]
      rfl

/-- Changing from the table pair `(delta, alpha)` to the manuscript pair
`(delta / alpha, 1)` transports the elementary and critical phases together:
their complete Lamprecht factors agree. -/
theorem lowQuadraticNormalizedTauPhase_completeFactor_eq_normPhase
    (CNormalized CTable : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData.completeFactor
      (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi
        hgen data hF delta epsilon1 hdelta hT hgammaF P CNormalized) =
      (lowQuadraticNormPhaseForComputationalData F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hT hgammaF P CTable).completeFactor := by
  let newPhase := lowQuadraticNormalizedTauPhaseForComputationalData F K ht
    hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P CNormalized
  let oldPhase := lowQuadraticNormPhaseForComputationalData F K ht hres pi
    hpi hgen data hF delta epsilon1 hdelta hT hgammaF P CTable
  calc
    newPhase.completeFactor =
        deltaFinite (data.normCharacterData
          (lowNormCharacterGenerator F K ht hres pi hpi hgen))
          data.baseAddChar newPhase.gamma :=
      newPhase.deltaFinite_eq_completeFactor.symm
    _ = deltaFinite (data.normCharacterData
          (lowNormCharacterGenerator F K ht hres pi hpi hgen))
          data.baseAddChar oldPhase.gamma :=
      deltaFinite_gamma_independent
        (data.normCharacterData
          (lowNormCharacterGenerator F K ht hres pi hpi hgen))
        data.baseAddChar oldPhase.gamma newPhase.gamma
    _ = oldPhase.completeFactor := oldPhase.deltaFinite_eq_completeFactor

/-- The exact norm supplied by the simultaneous table is killed by every
norm character. -/
theorem lowQuadraticNormCharacterGenerator_alpha_eq_one :
    (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 P.alpha = 1 := by
  exact NormCharacter.eq_one_on_normRange F K
    (lowNormCharacterGenerator F K ht hres pi hpi hgen) P.alpha
      ⟨P.alpha₁, rfl⟩

/-- The additive ratio of the normalized pair is literally `alpha/delta`,
with the manuscript's denominator direction preserved before simplification. -/
theorem lowQuadraticNormalizedTau_additiveRatio :
    (1 : F) / ((delta / P.alpha : Fˣ) : F) =
      (P.alpha : F) / (delta : F) := by
  simp only [Units.val_div_eq_div_val]
  field_simp [Units.ne_zero delta, Units.ne_zero P.alpha]

/-- Although its literal denominator is `delta/alpha`, the normalized
admissible row has the same character value as the old `delta` row because
`alpha` is an exact norm. -/
theorem lowQuadraticNormalizedTauPhase_admissibleFactor_eq_delta
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi
      hgen data hF delta epsilon1 hdelta hT hgammaF P C).admissibleFactor =
      ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1 delta : ℂ) := by
  rw [lowQuadraticNormalizedTauPhase_admissibleFactor F K ht hres pi hpi
    hgen data hF delta epsilon1 hdelta hT hgammaF P C, map_div,
    lowQuadraticNormCharacterGenerator_alpha_eq_one F K ht hres pi hpi
      hgen data hF delta epsilon1 hdelta hT hgammaF P]
  simp

include hdegree in
/-- The actual low upstairs row retains `delta/epsilon₁`; after norm and
degree-two expansion its admissible factor is the product of the two
displayed base-character values. -/
theorem lowQuadraticUpstairsPhase_admissibleFactor
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W C).admissibleFactor =
      (globalChi (delta / lowEpsilon F K epsilon1) : ℂ) *
        (globalChi delta : ℂ) := by
  unfold lowQuadraticUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon1, hgammaK⟩
  change LocalLamprechtPhaseData.admissibleFactor
    (localPhaseOfStationaryClass hSource Gamma
      (lowQuadraticUpstairsStationaryRepresentative F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table W) C) = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  rw [hchi, ContinuousQuasiChar.compNorm_apply,
    data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  have hnormGamma :
      normUnits F K (lowGammaK F K delta epsilon1) =
        (delta / lowEpsilon F K epsilon1) * delta := by
    ext
    simp only [lowGammaK, map_div, coe_normUnits, Units.coe_map,
      Units.val_div_eq_div_val, Units.val_mul, lowEpsilon]
    change norm F K (algebraMap F K (delta : F)) /
        norm F K (epsilon1 : K) =
      (delta : F) / norm F K (epsilon1 : K) * (delta : F)
    rw [norm_algebraMap, hdegree]
    field_simp [Units.ne_zero epsilon1]
  rw [hnormGamma, map_mul]
  exact Units.val_mul _ _

/-- The actual index-one twist evaluates the twisted character at the new
denominator `delta`. -/
theorem lowQuadraticTwistPhase_admissibleFactor
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W C).admissibleFactor =
      ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1 delta : ℂ) *
        (globalChi delta : ℂ) := by
  let j : ZMod (Module.finrank F K) := 1
  have hj : j ≠ 0 := lowQuadratic_one_ne_zero (F := F) (K := K)
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow j hj
  have hdata : twist = data.twistData tau := by
    rw [show twist = ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen (data.twistData 1) tau by
      simpa only [twist, tau, j, lowNormCharacterGenerator] using
        (lowNonzeroTwistDatum_eq_actual F K ht hres pi hpi hgen
          (data.twistData 1) hminimal hLow j hj)]
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  unfold lowQuadraticTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  have hgammaTw : ord F (delta : F) =
      (((twist.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    simpa only [twist, lowNonzeroTwistDatum_conductor] using hdelta
  let Gamma : AdmissibleGamma F twist data.baseAddChar :=
    ⟨delta, hgammaTw⟩
  change LocalLamprechtPhaseData.admissibleFactor
    (localPhaseOfStationaryClass hCrit Gamma
      (lowQuadraticTwistStationaryRepresentative F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table W) C) = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  change (twist.character delta : ℂ) = _
  rw [hdata, data.twistData_character]
  simp only [tau, ContinuousQuasiChar.mul_apply]
  exact Units.val_mul _ _

/-- Positive additive value of the explicitly supplied low upstairs row. -/
theorem lowQuadraticUpstairsPhase_elementaryAdditiveFactor
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W C).elementaryAdditiveFactor =
      (globalPsi
        (trace F K ((W.representative : K) /
          (lowGammaK F K delta epsilon1 : K))) : ℂ) := by
  calc
    _ = (lowQuadraticUpstairsPhaseFromWitness F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table W C).elementaryAdditiveFactor := by
      unfold lowQuadraticUpstairsPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor _ _ _
    _ = _ := by
      let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
        (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
      let Gamma : AdmissibleGamma K chiK psiK :=
        ⟨lowGammaK F K delta epsilon1, hgammaK⟩
      change LocalLamprechtPhaseData.elementaryAdditiveFactor
        (localPhaseOfStationaryClass hSource Gamma
          (lowQuadraticUpstairsStationaryRepresentative F K ht hres pi hpi
            hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
              hdelta hepsilon1 hT hgammaF hgammaK P table W) C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
      rw [hpsi, ContinuousAddChar.compTrace_apply,
        data.baseAddChar_character]
      rfl

/-- Positive additive value of the literal low base representative `beta`. -/
theorem lowQuadraticBasePhase_elementaryAdditiveFactor
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table C).elementaryAdditiveFactor =
      (globalPsi ((P.beta : F) /
        (lowGammaF F K delta epsilon1 : F)) : ℂ) := by
  unfold lowBasePhase
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
    data.baseAddChar_character]

/-- Positive additive value of the explicit nonidentity low twist row. -/
theorem lowQuadraticTwistPhase_elementaryAdditiveFactor
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W C).elementaryAdditiveFactor =
      (globalPsi ((W.representative : F) / (delta : F)) : ℂ) := by
  calc
    _ = (lowQuadraticTwistPhaseSource F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table W C).elementaryAdditiveFactor := by
      unfold lowQuadraticTwistPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor _ _ _
    _ = _ := by
      let hCrit := lowCriticalConductorDecomposition (t := t) hT
      let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K))
      have hgammaTw : ord F (delta : F) =
          (((twist.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
            WithTop ℤ) := by
        simpa only [twist, lowNonzeroTwistDatum_conductor] using hdelta
      let Gamma : AdmissibleGamma F twist data.baseAddChar :=
        ⟨delta, hgammaTw⟩
      change LocalLamprechtPhaseData.elementaryAdditiveFactor
        (localPhaseOfStationaryClass hCrit Gamma
          (lowQuadraticTwistStationaryRepresentative F K ht hres pi hpi hgen
            data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table W) C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
        data.baseAddChar_character]
      rfl

/-- Inverse multiplicative value of the explicit low upstairs row. -/
theorem lowQuadraticUpstairsPhase_elementaryMultiplicativeFactor
    (W : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W C).elementaryMultiplicativeFactor =
      (globalChi (normUnits F K
        (lowQuadraticUpstairsUnit F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table W)) : ℂ)⁻¹ := by
  calc
    _ = (lowQuadraticUpstairsPhaseFromWitness F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table W C).elementaryMultiplicativeFactor := by
      unfold lowQuadraticUpstairsPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor _ _ _
    _ = _ := by
      let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
        (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
      let Gamma : AdmissibleGamma K chiK psiK :=
        ⟨lowGammaK F K delta epsilon1, hgammaK⟩
      change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
        (localPhaseOfStationaryClass hSource Gamma
          (lowQuadraticUpstairsStationaryRepresentative F K ht hres pi hpi
            hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
              hdelta hepsilon1 hT hgammaF hgammaK P table W) C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
      rw [hchi, ContinuousQuasiChar.compNorm_apply,
        data.twistData_character]
      simp
      rfl

/-- Inverse multiplicative value of the low base row. -/
theorem lowQuadraticBasePhase_elementaryMultiplicativeFactor
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table C).elementaryMultiplicativeFactor =
      (globalChi P.beta : ℂ)⁻¹ := by
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨lowGammaF F K delta epsilon1, hgammaF⟩
  let R : StationaryClassRepresentative F (data.twistData 1)
      data.baseAddChar hF (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
      represents := by simpa only [Gamma] using table.beta_native_class }
  change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
    (localPhaseOfStationaryClass hF Gamma R C) = _
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor,
    data.twistData_character]
  simp
  have hunit : R.unit = P.beta := by
    apply Units.ext
    rw [StationaryClassRepresentative.coe_unit]
  rw [hunit]

/-- Inverse multiplicative value of the explicit low twist row, with its
norm and base characters separated. -/
theorem lowQuadraticTwistPhase_elementaryMultiplicativeFactor
    (W : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table W C).elementaryMultiplicativeFactor =
      (((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
            hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
              hgammaF hgammaK P table W) : ℂ) *
        (globalChi
          (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
            hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
              hgammaF hgammaK P table W) : ℂ))⁻¹ := by
  let j : ZMod (Module.finrank F K) := 1
  have hj : j ≠ 0 := lowQuadratic_one_ne_zero (F := F) (K := K)
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow j hj
  have hdata : twist = data.twistData tau := by
    rw [show twist = ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen (data.twistData 1) tau by
      simpa only [twist, tau, j, lowNormCharacterGenerator] using
        (lowNonzeroTwistDatum_eq_actual F K ht hres pi hpi hgen
          (data.twistData 1) hminimal hLow j hj)]
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  calc
    _ = (lowQuadraticTwistPhaseSource F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table W C).elementaryMultiplicativeFactor := by
      unfold lowQuadraticTwistPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor _ _ _
    _ = _ := by
      let hCrit := lowCriticalConductorDecomposition (t := t) hT
      let twistSource := lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K))
          (lowQuadratic_one_ne_zero (F := F) (K := K))
      have hgammaTw : ord F (delta : F) =
          (((twistSource.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
            WithTop ℤ) := by
        simpa only [twistSource, lowNonzeroTwistDatum_conductor] using hdelta
      let Gamma : AdmissibleGamma F twistSource data.baseAddChar :=
        ⟨delta, hgammaTw⟩
      change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
        (localPhaseOfStationaryClass hCrit Gamma
          (lowQuadraticTwistStationaryRepresentative F K ht hres pi hpi hgen
            data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table W) C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
      change (twist.character _ : ℂ)⁻¹ = _
      rw [hdata, data.twistData_character]
      simp only [tau, ContinuousQuasiChar.mul_apply, Units.val_mul]
      rfl

include hdegree in
/-- Exact field-level additive relation of the four low-table rows.  The
base common-denominator numerator is `epsilon*beta`, while the twist
numerator is `alpha+epsilon*beta`. -/
theorem lowQuadratic_additiveArgument_eq
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) :
    trace F K ((WUp.representative : K) /
        (lowGammaK F K delta epsilon1 : K)) +
        (P.alpha : F) / (delta : F) =
      -(((P.alpha / delta : Fˣ) : F)) *
          trace F K (lowNormalizedRatio F K epsilon1 P) +
        (P.beta : F) / (lowGammaF F K delta epsilon1 : F) +
        (WTwist.representative : F) / (delta : F) := by
  let eta := lowEpsilon F K epsilon1
  let u := lowNormalizedRatio F K epsilon1 P
  have htraceScalar (a : F) (z : K) :
      trace F K (algebraMap F K a * z) = a * trace F K z := by
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul a z
  have hup :
      (WUp.representative : K) /
          (lowGammaK F K delta epsilon1 : K) =
        algebraMap F K (((P.alpha / delta : Fˣ) : F)) *
          (algebraMap F K
            ((eta : F) * (P.beta : F) / (P.alpha : F)) - u) := by
    rw [WUp.representative_eq,
      lowUpstairsCandidate_eq_normalized,
      lowNormalizedUpstairsCandidate, lowGammaK]
    simp only [u, eta, Units.val_div_eq_div_val, Units.coe_map, map_div₀]
    rw [lowNormalizedRatio_norm]
    simp only [map_div₀, map_mul]
    field_simp [Units.ne_zero epsilon1, Units.ne_zero delta,
      Units.ne_zero P.alpha]
    rfl
  rw [hup, htraceScalar, map_sub, trace_algebraMap, hdegree,
    WTwist.representative_eq]
  simp only [two_nsmul, lowGammaF, eta, u, Units.val_div_eq_div_val]
  field_simp [Units.ne_zero delta, Units.ne_zero P.alpha,
    Units.ne_zero eta]
  ring

include hdegree in
/-- The first raw ratio becomes an equality of the actual low upstairs,
base, and nonidentity twist units. -/
theorem lowQuadratic_zZero_mul_rows_eq_norm
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (C : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K epsilon1 P)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P)) :
    C.zZero * P.beta *
        (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table WTwist) =
      normUnits F K
        (lowQuadraticUpstairsUnit F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table WUp) := by
  have hnormSub := C.norm_sub_eq
  dsimp only [lowQuadraticNormalizedNormUnit] at hnormSub
  simp only [Units.val_div_eq_div_val, Units.val_mul] at hnormSub
  apply Units.ext
  simp only [Units.val_mul, coe_normUnits,
    lowQuadraticTwistUnit_coe, lowQuadraticUpstairsUnit_coe]
  rw [WUp.representative_eq, lowUpstairsCandidate_eq_normalized,
    norm_lowNormalizedUpstairsCandidate, hdegree,
    table.normalized_ratio_norm]
  rw [hnormSub, WTwist.representative_eq]
  field_simp [Units.ne_zero P.alpha,
    Units.ne_zero (lowEpsilon F K epsilon1)]

/-- The second low raw ratio says `z1` times the literal twist unit is
`alpha` times a genuine norm. -/
theorem lowQuadratic_zOne_mul_twist_eq_alpha_mul_norm
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (C : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K epsilon1 P)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P)) :
    C.zOne *
        (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table WTwist) =
      P.alpha * normUnits F K C.oneAddUUnit := by
  apply Units.ext
  simp only [Units.val_mul, coe_normUnits, lowQuadraticTwistUnit_coe,
    C.coe_oneAddUUnit]
  rw [WTwist.representative_eq, C.norm_one_add_eq]
  simp only [lowQuadraticNormalizedNormUnit_coe]
  field_simp [Units.ne_zero P.alpha]

include hdegree in
/-- The two raw low ratios imply the multiplicative correction with scalar
one; the norm-row factor `tau(alpha)^{-1}` is retained on the numerator side. -/
theorem lowQuadratic_multiplicativeRatio_eq
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (C : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K epsilon1 P)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P)) :
    (globalChi (normUnits F K
        (lowQuadraticUpstairsUnit F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table WUp)) : ℂ)⁻¹ *
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          P.alpha : ℂ)⁻¹ =
      (globalChi C.zZero : ℂ)⁻¹ *
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          C.zOne : ℂ)⁻¹ *
          ((globalChi P.beta : ℂ)⁻¹ *
            (((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
                (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK
                  psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                    hepsilon1 hT hgammaF hgammaK P table WTwist) : ℂ) *
              (globalChi
                (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK
                  psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                    hepsilon1 hT hgammaF hgammaK P table WTwist) : ℂ))⁻¹) := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hzUnits := lowQuadratic_zZero_mul_rows_eq_norm F K ht hres pi hpi hgen
    (hdegree := hdegree) data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp WTwist C
  have hoUnits := lowQuadratic_zOne_mul_twist_eq_alpha_mul_norm F K ht hres
    pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table WTwist C
  have hz := congrArg (Units.val : ℂˣ → ℂ)
    (congrArg globalChi hzUnits)
  simp only [map_mul, Units.val_mul] at hz
  have ho := congrArg (Units.val : ℂˣ → ℂ)
    (congrArg tau.1 hoUnits)
  simp only [map_mul, Units.val_mul] at ho
  have hnorm : tau.1 (normUnits F K C.oneAddUUnit) = 1 :=
    tau.eq_one_on_normRange F K _ ⟨C.oneAddUUnit, rfl⟩
  have hnormC := congrArg (Units.val : ℂˣ → ℂ) hnorm
  simp only [Units.val_one] at hnormC
  have ho' :
      (tau.1 C.zOne : ℂ) *
          (tau.1 (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK
            psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
              hT hgammaF hgammaK P table WTwist) : ℂ) =
        (tau.1 P.alpha : ℂ) := by
    calc
      _ = (tau.1 P.alpha : ℂ) *
          (tau.1 (normUnits F K C.oneAddUUnit) : ℂ) := ho
      _ = (tau.1 P.alpha : ℂ) * 1 := by rw [hnormC]
      _ = _ := mul_one _
  rw [← hz]
  field_simp [ContinuousQuasiChar.apply_ne_zero]
  exact ho'

include hdegree in
/-- With the normalized `(delta/alpha,1)` norm row, the norm-character
elementary numerator is literally one.  The same two raw ratios give the
remaining `chi(z0)^{-1} tau(z1)^{-1}` correction; `tau(alpha)=1` is derived
from the table's exact norm, not assumed. -/
theorem lowQuadratic_normalizedMultiplicativeRatio_eq
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (C : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K epsilon1 P)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P)) :
    (globalChi (normUnits F K
        (lowQuadraticUpstairsUnit F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table WUp)) : ℂ)⁻¹ * 1 =
      (globalChi C.zZero : ℂ)⁻¹ *
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          C.zOne : ℂ)⁻¹ *
          ((globalChi P.beta : ℂ)⁻¹ *
            (((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
                (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK
                  psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                    hepsilon1 hT hgammaF hgammaK P table WTwist) : ℂ) *
              (globalChi
                (lowQuadraticTwistUnit F K ht hres pi hpi hgen data chiK
                  psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                    hepsilon1 hT hgammaF hgammaK P table WTwist) : ℂ))⁻¹) := by
  have h := lowQuadratic_multiplicativeRatio_eq F K ht hres pi hpi hgen
    (hdegree := hdegree) data chiK psiK hF hminimal hchi hpsi hLow delta
      epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist C
  rw [lowQuadraticNormCharacterGenerator_alpha_eq_one F K ht hres pi hpi
    hgen data hF delta epsilon1 hdelta hT hgammaF P] at h
  simpa using h

include hdegree in
/-- The positive additive low numerator identity is proved from the four
actual table rows. -/
theorem lowQuadratic_additiveNumerator_eq_of_actual_rows
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm CTwist : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : D.normCharacter
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P CNorm))
    (hTwist : D.twist
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
          data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WTwist CTwist))
    (indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D)
    (hindex : indexing.tau =
      lowNormCharacterGenerator F K ht hres pi hpi hgen) :
    D.elementaryAdditiveNumerator =
      (globalPsi
        (-(((P.alpha / delta : Fˣ) : F)) *
          trace F K (lowNormalizedRatio F K epsilon1 P)) : ℂ) *
        D.elementaryAdditiveDenominator := by
  rw [ExactQuadraticPhaseAssembly.elementaryAdditiveNumerator_eq_two_actual_rows indexing,
    ExactQuadraticPhaseAssembly.elementaryAdditiveDenominator_eq_two_actual_rows indexing,
    hindex]
  rw [hExtension, hNorm, hBase, hTwist]
  simp only [LocalPhaseData.elementaryAdditiveFactor]
  rw [lowQuadraticUpstairsPhase_elementaryAdditiveFactor F K ht hres pi hpi
    hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table WUp CUp]
  rw [lowQuadraticNormalizedTauPhase_elementaryAdditiveFactor F K ht hres pi
    hpi hgen data hF delta epsilon1 hdelta hT hgammaF P CNorm,
    lowQuadraticNormalizedTau_additiveRatio F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P]
  rw [lowQuadraticBasePhase_elementaryAdditiveFactor F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table CBase]
  rw [lowQuadraticTwistPhase_elementaryAdditiveFactor F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WTwist CTwist]
  have hadd (a b : F) :
      (globalPsi a : ℂ) * (globalPsi b : ℂ) =
        (globalPsi (a + b) : ℂ) := by
    exact (congrArg (Units.val : ℂˣ → ℂ)
      (ContinuousAddChar.map_add_eq_mul globalPsi a b)).symm
  rw [hadd, hadd, hadd]
  congr 2
  rw [lowQuadratic_additiveArgument_eq F K ht hres pi hpi hgen
    (hdegree := hdegree) data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp WTwist]
  ring

include hdegree in
/-- The inverse multiplicative low numerator identity is proved from the
four actual table rows and the two raw field ratios. -/
theorem lowQuadratic_multiplicativeNumerator_eq_of_actual_rows
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm CTwist : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : D.normCharacter
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P CNorm))
    (hTwist : D.twist
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
          data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WTwist CTwist))
    (indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D)
    (hindex : indexing.tau =
      lowNormCharacterGenerator F K ht hres pi hpi hgen)
    (C : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K epsilon1 P)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P)) :
    D.elementaryMultiplicativeNumerator =
      (globalChi C.zZero : ℂ)⁻¹ *
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          C.zOne : ℂ)⁻¹ * D.elementaryMultiplicativeDenominator := by
  rw [ExactQuadraticPhaseAssembly.elementaryMultiplicativeNumerator_eq_two_actual_rows indexing,
    ExactQuadraticPhaseAssembly.elementaryMultiplicativeDenominator_eq_two_actual_rows indexing,
    hindex]
  rw [hExtension, hNorm, hBase, hTwist]
  simp only [LocalPhaseData.elementaryMultiplicativeFactor]
  rw [lowQuadraticUpstairsPhase_elementaryMultiplicativeFactor F K ht hres
    pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta
      epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp CUp]
  rw [lowQuadraticNormalizedTauPhase_elementaryMultiplicativeFactor F K ht
    hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P CNorm]
  rw [lowQuadraticBasePhase_elementaryMultiplicativeFactor F K ht hres pi
    hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table CBase]
  rw [lowQuadraticTwistPhase_elementaryMultiplicativeFactor F K ht hres pi
    hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table WTwist CTwist]
  rw [lowQuadratic_normalizedMultiplicativeRatio_eq F K ht hres pi hpi hgen
    (hdegree := hdegree) data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp WTwist C]

/-- A low wild-quadratic assembly backed by one simultaneous low table and
the two explicit witnesses for its Prop-valued upstairs and twist rows.
Every other local row is the literal base or index-one norm phase above. -/
structure LowTableBackedExactQuadraticAssembly
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) where
  assembly : ExactQuadraticPhaseAssembly F K globalChi globalPsi data D
    (t := t) (m := (data.twistData 1).conductor)
  upstairsCriticalCoordinate : LamprechtCriticalCoordinate K d epsilon
  baseCriticalCoordinate : LamprechtCriticalCoordinate F d epsilon
  normCriticalCoordinate : LamprechtCriticalCoordinate F
    (lowCriticalFloorDepth t) (lowCriticalParity t)
  twistCriticalCoordinate : LamprechtCriticalCoordinate F
    (lowCriticalFloorDepth t) (lowCriticalParity t)
  extensionPhase : D.extension = LocalPhaseData.stationary
    (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table WUp
          upstairsCriticalCoordinate)
  basePhase : D.twist 1 = LocalPhaseData.stationary
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table baseCriticalCoordinate)
  nontrivialNormPhase : D.normCharacter
      (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
    LocalPhaseData.stationary
      (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hT hgammaF P normCriticalCoordinate)
  nontrivialTwistPhase : D.twist
      (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
    LocalPhaseData.stationary
      (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WTwist
            twistCriticalCoordinate)
  indexing_source : assembly.indexing.index =
    lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen hdegree
  indexing_tau : assembly.indexing.tau =
    lowNormCharacterGenerator F K ht hres pi hpi hgen
  scalarCorrection_source : assembly.scalarCorrection = 1
  range_is_low : assembly.parameterRange = .low hLow
  breakUnit_source : assembly.breakUnit = 1
  stationaryScale_source : assembly.stationaryScale = (P.alpha : F)
  baseNumerator_source : assembly.baseStationaryNumerator =
    (lowEpsilon F K epsilon1 : F) * (P.beta : F)
  twistNumerator_source : assembly.twistStationaryNumerator =
    (P.alpha : F) + (lowEpsilon F K epsilon1 : F) * (P.beta : F)
  twistWitnessNumerator_source : (WTwist.representative : F) =
    (P.alpha : F) + (lowEpsilon F K epsilon1 : F) * (P.beta : F)
  ratio_u_source : assembly.u = lowNormalizedRatio F K epsilon1 P
  ratio_n_source : assembly.n =
    (lowEpsilon F K epsilon1 : F) * (P.beta : F) / (P.alpha : F)
  normalizedRatio_order : ord K (assembly.u : K) =
    (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ)
  normalizedRatio_norm : norm F K assembly.u = assembly.n

set_option maxHeartbeats 4000000 in
/-- Legacy low-table-backed constructor.  It derives endpoint and admissible
quotients from the actual rows but accepts the two already-assembled
elementary numerator identities.  New code should use
`lowTableBackedExactQuadraticAssemblyFromActualRows`. -/
def lowTableBackedExactQuadraticAssembly
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm CTwist : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : D.normCharacter
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P CNorm))
    (hTwist : D.twist
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
          data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WTwist CTwist))
    (zZero zOne : Fˣ) (x y : F)
    (zZero_eq : (zZero : F) = 1 + x)
    (zOne_eq : (zOne : F) = 1 + y)
    (additiveNumerator_eq : D.elementaryAdditiveNumerator =
      (globalPsi
        (-(((P.alpha / delta : Fˣ) : F)) * trace F K
          (lowNormalizedRatio F K epsilon1 P)) : ℂ) *
        D.elementaryAdditiveDenominator)
    (multiplicativeNumerator_eq : D.elementaryMultiplicativeNumerator =
      (globalChi zZero : ℂ)⁻¹ *
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1 zOne : ℂ)⁻¹ *
          D.elementaryMultiplicativeDenominator) :
    LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen hdegree
      data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table WUp WTwist := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let index := lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen hdegree
  let indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D :=
    { tau := tau
      index := index
      index_true := by
        exact lowQuadraticNormCharacterIndex_true F K ht hres pi hpi hgen
          hdegree
      index_false := by
        exact lowQuadraticNormCharacterIndex_false F K ht hres pi hpi hgen
          hdegree }
  let eta : F := (lowEpsilon F K epsilon1 : F)
  let coeff : F := ((P.alpha / delta : Fˣ) : F)
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := eta * (P.beta : F) / (P.alpha : F)
  let s : F := trace F K u
  let X : F := s + n * x + y
  have hEndpoint : D.factors.endpoint = 1 := by
    apply ExactQuadraticPhaseAssembly.endpointFactor_eq_one_of_quadratic_actual_rows
      indexing
    · exact ⟨_, hExtension⟩
    · simpa only [indexing, tau] using
        (⟨_, hNorm⟩ : ∃ S, D.normCharacter
          (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
            LocalPhaseData.stationary S)
    · exact ⟨_, hBase⟩
    · simpa only [indexing, tau] using
        (⟨_, hTwist⟩ : ∃ S, D.twist
          (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
            LocalPhaseData.stationary S)
  have hAdmissibleFactor : D.factors.admissibleCharacter = 1 := by
    rw [ExactQuadraticPhaseAssembly.admissibleFactor_eq_four_actual_rows
      indexing]
    change
      (D.extension.admissibleFactor *
          (D.normCharacter tau).admissibleFactor) /
        ((D.twist 1).admissibleFactor *
          (D.twist tau).admissibleFactor) = 1
    rw [hExtension, hNorm, hBase, hTwist]
    simp only [LocalPhaseData.admissibleFactor]
    rw [lowQuadraticUpstairsPhase_admissibleFactor F K ht hres pi hpi hgen
      (hdegree := hdegree) data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp CUp]
    rw [lowQuadraticNormalizedTauPhase_admissibleFactor_eq_delta F K ht hres
      pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P CNorm]
    rw [lowBasePhase_admissibleFactor F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table CBase]
    rw [lowQuadraticTwistPhase_admissibleFactor F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WTwist CTwist]
    rw [data.twistData_character]
    simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
      ContinuousQuasiChar.one_apply, one_mul, lowGammaF]
    field_simp [ContinuousQuasiChar.apply_ne_zero]
  have hAdmissibleNumerator : D.admissibleNumerator =
      ((1 : ℂˣ) : ℂ)⁻¹ * D.admissibleDenominator := by
    have h := hAdmissibleFactor
    simp only [FirstMainPhaseData.factors] at h
    have hraw := (div_eq_iff D.admissibleDenominator_ne_zero).mp h
    simpa using hraw
  let A : ExactQuadraticPhaseAssembly F K globalChi globalPsi data D
      (t := t) (m := (data.twistData 1).conductor) :=
    { baseData := data.twistData 1
      baseData_eq := rfl
      baseCharacter := by
        rw [data.twistData_character]
        ext z
        simp
      baseConductor := rfl
      parameterRange := .low hLow
      indexing := indexing
      A := coeff
      u := u
      n := n
      norm_u := by
        simpa only [u, n, eta] using table.normalized_ratio_norm
      s := s
      s_eq := rfl
      zZero := zZero
      zOne := zOne
      x := x
      y := y
      zZero_eq := zZero_eq
      zOne_eq := zOne_eq
      X := X
      X_eq := rfl
      breakUnit := 1
      stationaryScale := (P.alpha : F)
      baseStationaryNumerator := eta * (P.beta : F)
      twistStationaryNumerator :=
        (P.alpha : F) + eta * (P.beta : F)
      twistStationaryNumerator_eq := by
        rw [show (((1 : unitFiltration F t) : Fˣ) : F) = 1 by rfl]
        ring
      scalarCorrection := 1
      endpointFactor_eq := hEndpoint
      admissibleNumerator_eq := hAdmissibleNumerator
      additiveNumerator_eq := by
        simpa only [coeff, u, s] using additiveNumerator_eq
      multiplicativeNumerator_eq := by
        simpa only [indexing, tau, Units.val_one, one_mul] using
          multiplicativeNumerator_eq }
  exact
    { assembly := A
      upstairsCriticalCoordinate := CUp
      baseCriticalCoordinate := CBase
      normCriticalCoordinate := CNorm
      twistCriticalCoordinate := CTwist
      extensionPhase := hExtension
      basePhase := hBase
      nontrivialNormPhase := hNorm
      nontrivialTwistPhase := hTwist
      indexing_source := rfl
      indexing_tau := rfl
      scalarCorrection_source := rfl
      range_is_low := rfl
      breakUnit_source := rfl
      stationaryScale_source := rfl
      baseNumerator_source := rfl
      twistNumerator_source := rfl
      twistWitnessNumerator_source := WTwist.representative_eq
      ratio_u_source := rfl
      ratio_n_source := rfl
      normalizedRatio_order := by
        simpa only [u] using table.normalized_ratio_order
      normalizedRatio_norm := by
        simpa only [u, n, eta] using table.normalized_ratio_norm }

set_option maxHeartbeats 4000000 in
/-- Preferred low-table quadratic constructor.  The source-tied raw norm
ratios are its only elementary coordinate input; both aggregate numerator
identities are derived from the four actual low stationary rows. -/
def lowTableBackedExactQuadraticAssemblyFromActualRows
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm CTwist : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : D.normCharacter
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticNormalizedTauPhaseForComputationalData F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P CNorm))
    (hTwist : D.twist
        (lowNormCharacterGenerator F K ht hres pi hpi hgen) =
      LocalPhaseData.stationary
        (lowQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
          data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WTwist CTwist))
    (C : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K epsilon1 P)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P)) :
    LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen hdegree
      data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table WUp WTwist := by
  let index := lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen hdegree
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D :=
    { tau := tau
      index := index
      index_true := lowQuadraticNormCharacterIndex_true F K ht hres pi hpi
        hgen hdegree
      index_false := lowQuadraticNormCharacterIndex_false F K ht hres pi hpi
        hgen hdegree }
  apply lowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen hdegree
    data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp WTwist CUp CBase CNorm CTwist
        hExtension hBase hNorm hTwist C.zZero C.zOne C.x C.y C.zZero_eq
          C.zOne_eq
  · exact lowQuadratic_additiveNumerator_eq_of_actual_rows F K ht hres pi
      hpi hgen (hdegree := hdegree) data D chiK psiK hF hminimal hchi hpsi hLow delta
        epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist CUp
          CBase CNorm CTwist hExtension hBase hNorm hTwist indexing rfl
  · exact lowQuadratic_multiplicativeNumerator_eq_of_actual_rows F K ht hres
      pi hpi hgen (hdegree := hdegree) data D chiK psiK hF hminimal hchi hpsi hLow delta
        epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist CUp
          CBase CNorm CTwist hExtension hBase hNorm hTwist indexing rfl C

/-- The low denominator is forced nonzero by the explicit index-one twist
representative.  Its stationary class is at the actual conductor `t+1`, so
its representative has order zero; factoring its literal numerator
`alpha + epsilon*beta` gives the required denominator `1 + epsilon*beta/alpha`.
No noncancellation hypothesis is added here. -/
theorem lowTableBacked_one_add_n_ne_zero
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (B : LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist) :
    1 + B.assembly.n ≠ 0 := by
  let hj := lowQuadratic_one_ne_zero (F := F) (K := K)
  have hsumOrd : ord F (WTwist.representative : F) =
      (0 : WithTop ℤ) := by
    exact stationaryCoefficientClass_representative_ord_zero F K F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (1 : ZMod (Module.finrank F K)) hj)
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
        delta hdelta WTwist.representative WTwist.represents
  have hsumNe : (WTwist.representative : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (hsumOrd.trans_ne WithTop.coe_ne_top)
  rw [B.ratio_n_source]
  intro hzero
  apply hsumNe
  rw [WTwist.representative_eq]
  calc
    (P.alpha : F) +
          (lowEpsilon F K epsilon1 : F) * (P.beta : F) =
        (P.alpha : F) *
          (1 + (lowEpsilon F K epsilon1 : F) *
            (P.beta : F) / (P.alpha : F)) := by
      field_simp [Units.ne_zero P.alpha]
    _ = 0 := by rw [hzero, mul_zero]

/-- The downstream norm/trace correction attached to one low-table-backed
assembly.  Only the two literal ratios and the two separate character
linearizations remain as inputs; the denominator is proved above from the
actual index-one stationary row. -/
structure LowTableBackedQuadraticCompleteCorrection
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (B : LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist) : Prop where
  zZero_ratio : (B.assembly.zZero : F) =
    norm F K (1 + B.assembly.dualRatio) / (1 + B.assembly.n)
  zOne_ratio : (B.assembly.zOne : F) =
    norm F K (1 + B.assembly.u) / (1 + B.assembly.n)
  chiLinearization : globalChi B.assembly.zZero =
    globalPsi (B.assembly.A * B.assembly.n * B.assembly.x)
  tauLinearization : B.assembly.indexing.tau.1 B.assembly.zOne =
    globalPsi (B.assembly.A * B.assembly.y)

namespace LowTableBackedQuadraticCompleteCorrection

/-- Package the four downstream correction identities with the denominator
proved from the selected low-table twist witness. -/
theorem toCompleteCorrectionData
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (B : LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist)
    (C : LowTableBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist B) :
    B.assembly.CompleteCorrectionData where
  one_add_n_ne_zero := lowTableBacked_one_add_n_ne_zero F K ht hres pi hpi
    hgen hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist B
  zZero_ratio := C.zZero_ratio
  zOne_ratio := C.zOne_ratio
  chiLinearization := C.chiLinearization
  tauLinearization := C.tauLinearization

/-- Exact low quadratic residual reduction after the explicit norm-ratio
corrections.  The residual Hasse quotient is deliberately not evaluated. -/
theorem errorTerm_eq_residual_mul_phase
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table)
    (B : LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist)
    (C : LowTableBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist B) :
    errorTerm F K DeltaF DeltaK globalChi globalPsi =
      B.assembly.residualHasseQuotient *
        (globalPsi (-B.assembly.A * B.assembly.X) : ℂ) :=
  (C.toCompleteCorrectionData F K ht hres pi hpi hgen hdegree data D chiK
    psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table WUp WTwist B).errorTerm_eq_residual_mul_phase
        hDeltaF hDeltaK B.assembly

/-- Compact eliminator type for a fully table-backed low quadratic assembly
and its already-proved complete correction data. -/
def LowTableBackedQuadraticCompleteResultEliminator : Prop :=
  ∀ {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K},
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF) →
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) →
    (WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) →
    (WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) →
    (B : LowTableBackedExactQuadraticAssembly F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist) →
    (C : LowTableBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp WTwist B) →
    (C.toCompleteCorrectionData F K ht hres pi hpi hgen hdegree data D chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WUp WTwist B).CompleteResult
          hDeltaF hDeltaK B.assembly

/-- The low quadratic complete-result eliminator is inhabited by the
already-proved generic structured result. -/
theorem lowTableBackedQuadraticCompleteResult :
    LowTableBackedQuadraticCompleteResultEliminator F K ht hres pi hpi hgen
      hdegree data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table := by
  intro DeltaF DeltaK hDeltaF hDeltaK WUp WTwist B C
  exact (C.toCompleteCorrectionData F K ht hres pi hpi hgen hdegree data D
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table WUp WTwist B).completeResult hDeltaF hDeltaK
        B.assembly

end LowTableBackedQuadraticCompleteCorrection

end QuadraticLowProvenance

end

end LanglandsFirstMainLemma
