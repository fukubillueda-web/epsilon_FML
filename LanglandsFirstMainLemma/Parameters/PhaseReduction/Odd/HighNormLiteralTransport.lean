import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.HighResidualRows

/-!
# Literal high norm-power transport

This module carries the literal high norm-power representatives,
representative changes, affine translations, and complete critical-function
power identities.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

section HighNormLiteralTransport

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
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (htpos : 0 < t)
  (hstrict : t + 1 < (data.twistData 1).conductor)
  (hupper : (data.twistData 1).conductor < 2 * (t + 1))
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

variable
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF)

/-- The actual High norm-row denominator after the conductor drop. -/
noncomputable def highNormGamma : Fˣ :=
  gammaF / normUnits F K source.normRows.alpha1

theorem highNormGamma_order :
    ord F (highNormGamma F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) := by
  unfold highNormGamma
  rw [Units.val_div_eq_div_val, ord_div, hgammaF]
  have halphaOrd : ord F (norm F K (source.normRows.alpha1 : K)) =
      ((((data.twistData 1).conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) :
        WithTop ℤ) := by
    simpa only [Int.ofNat_sub hstrict.le] using
      source.normRows.alpha_choice.norm_order
  rw [coe_normUnits, halphaOrd]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  omega

/-- The High table proves that the literal representative `1` is the
generator stationary coefficient class at the dropped conductor. -/
theorem highNormGenerator_one_class :
    let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
    let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
        (highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen))
    let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
    let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source
    let oneRep : lattice F 0 := ⟨1, by simp [mem_lattice]⟩
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) oneRep =
      stationaryCoefficientClass F tauData data.baseAddChar hCrit gammaTau
        (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source) := by
  dsimp only
  let p := Module.finrank F K
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod p))
  have htau : tau ≠ 1 := by
    simpa only [p, tau] using
      (highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen)
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  let alphaNorm : Fˣ := normUnits F K source.normRows.alpha1
  let gammaTau : Fˣ := gammaF / alphaNorm
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) := by
    simpa only [gammaTau, alphaNorm, highNormGamma] using
      highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  have hOne : (1 : F) ∈ lattice F 0 := by
    rw [mem_lattice, ord_one]
    exact le_rfl
  let oneRep : lattice F 0 := ⟨(1 : F), hOne⟩
  have hm : (data.twistData 1).conductor =
      t + 1 + ((data.twistData 1).conductor - (t + 1)) :=
    (Nat.add_sub_of_le hstrict.le).symm
  have hselectedLinearization :=
    highParameter_intermediate_selectedAlpha_linearization
      F K ht hres pi hpi hgen htpos (data.twistData 1) data.baseAddChar hm
        tau htau gammaF hgammaF source.normRows.a source.normRows.alpha
          source.normRows.a_coe source.normRows.alpha1
            source.normRows.alpha_choice source.normRows.a_class
  apply (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    tauData data.baseAddChar hCrit gammaTau hgammaTau oneRep).2
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
  apply congrArg data.baseAddChar.character
  dsimp only [oneRep, gammaTau]
  simp only [Units.val_div_eq_div_val, alphaNorm, coe_normUnits, xs]
  have hnormNe : norm F K (source.normRows.alpha1 : K) ≠ 0 := by
    simpa only [← coe_normUnits] using
      (Units.ne_zero (normUnits F K source.normRows.alpha1))
  field_simp [hnormNe, Units.ne_zero gammaF]

/-- The literal natural multiple `j.val • 1` represents the actual indexed
norm-character class at the same dropped conductor and half-depth. -/
theorem highNormLiteral_class (j : OddNormIndex F K) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
    let hmu : mu ≠ 1 := by
      apply (ramifiedNormCharacterZModEquiv_ne_one_iff
        F K ht hres pi hpi hgen _).2
      intro h
      exact j.property (by
        have h' := congrArg Multiplicative.toAdd h
        simpa using h')
    let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
    let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
    let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source
    let oneRep : lattice F 0 := ⟨1, by simp⟩
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        ((j : ZMod (Module.finrank F K)).val • oneRep) =
      stationaryCoefficientClass F muData data.baseAddChar hCrit gammaTau
        (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source) := by
  dsimp only
  let p := Module.finrank F K
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod p))
  have htau : tau ≠ 1 := by
    simpa only [p, tau] using
      (highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen)
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod p))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    exact j.property (by
      have h' := congrArg Multiplicative.toAdd h
      simpa using h')
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) :=
    highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let oneRep : lattice F 0 := ⟨1, by simp⟩
  have hTauClass : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) oneRep =
      stationaryCoefficientClass F tauData data.baseAddChar hCrit gammaTau
        hgammaTau := by
    simpa only [tau, tauData, hCrit, gammaTau, oneRep, p] using
      highNormGenerator_one_class F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source
  have hMuCoefficient :
      (j : ZMod p).val • stationaryCoefficientClass F tauData
          data.baseAddChar hCrit gammaTau hgammaTau =
        stationaryCoefficientClass F muData data.baseAddChar hCrit gammaTau
          hgammaTau := by
    apply (stationaryCoefficientLamprechtEquivAtConductor F hCrit).injective
    rw [map_nsmul]
    calc
      _ = (j : ZMod p).val • stationaryNumeratorClass F tauData
          data.baseAddChar ((t + 1 : ℕ) : ℤ)
          (stationaryDepthOfConductorDecomposition F tauData hCrit)
          gammaTau hgammaTau := congrArg
            (fun z ↦ (j : ZMod p).val • z)
            (stationaryCoefficientClass_toLamprecht F tauData
              data.baseAddChar hCrit gammaTau hgammaTau)
      _ = stationaryNumeratorClass F muData data.baseAddChar
          ((t + 1 : ℕ) : ℤ)
          (stationaryDepthOfConductorDecomposition F muData hCrit)
          gammaTau hgammaTau := by
        simpa only [tau, mu, tauData, muData, p, hCrit] using
          (highParameter_intermediate_normCharacterClass_eq_nsmul
            F K ht hres pi hpi hgen (j : ZMod p) hmu data.baseAddChar
              ((t + 1 : ℕ) : ℤ)
              (stationaryDepthOfConductorDecomposition F tauData hCrit)
              gammaTau hgammaTau).symm
      _ = _ := (stationaryCoefficientClass_toLamprecht F muData
        data.baseAddChar hCrit gammaTau hgammaTau).symm
  calc
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        ((j : ZMod p).val • oneRep) =
      (j : ZMod p).val • latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) oneRep := by
          rw [map_nsmul]
    _ = (j : ZMod p).val • stationaryCoefficientClass F tauData
        data.baseAddChar hCrit gammaTau hgammaTau := congrArg _ hTauClass
    _ = _ := hMuCoefficient

/-- The actual Teichmüller representative supplied by the High construction
and the literal natural multiple represent the same indexed stationary
class, at exactly the dropped half-depth. -/
theorem highNormTeichmuller_class (j : OddNormIndex F K) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
    let hmu : mu ≠ 1 := by
      apply (ramifiedNormCharacterZModEquiv_ne_one_iff
        F K ht hres pi hpi hgen _).2
      intro h
      exact j.property (by
        have h' := congrArg Multiplicative.toAdd h
        simpa using h')
    let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
    let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
    let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
        hgen
    let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
      hchar (j : ZMod (Module.finrank F K))
    let rep : lattice F 0 := ⟨lam, by
      rw [mem_lattice_zero_iff F]
      exact highParameter_intermediate_teichmuller_mem_integer F
        (Module.finrank F K) hchar (j : ZMod (Module.finrank F K))⟩
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F muData data.baseAddChar hCrit gammaTau
        (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source) := by
  dsimp only
  let p := Module.finrank F K
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod p))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    exact j.property (by
      have h' := congrArg Multiplicative.toAdd h
      simpa using h')
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) :=
    highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  let lam := highIntermediateTeichmullerScalar F p hchar (j : ZMod p)
  have hlamInt : lam ∈ lattice F 0 := by
    rw [mem_lattice_zero_iff F]
    exact highParameter_intermediate_teichmuller_mem_integer F p hchar
      (j : ZMod p)
  let rep : lattice F 0 := ⟨lam, hlamInt⟩
  let oneRep : lattice F 0 := ⟨1, by simp⟩
  have hliteral : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        ((j : ZMod p).val • oneRep) =
      stationaryCoefficientClass F muData data.baseAddChar hCrit gammaTau
        hgammaTau := by
    simpa only [mu, muData, hCrit, gammaTau, oneRep, p] using
      highNormLiteral_class F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source j
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have hteich : lam - ((j : ZMod p).val : F) ∈
      lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
    simpa only [lam, p, hchar] using
      (highParameter_intermediate_teichmuller_congruent
        F K (Module.finrank F K) (t + 1)
          (residueCharacteristic_eq_degree_of_positive_break
            F K ht htpos pi hpi hgen) rfl htrace
              (j : ZMod (Module.finrank F K)))
  calc
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        ((j : ZMod p).val • oneRep) := by
      apply (latticeQuotientMk_eq_mk_iff F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)).2
      have honeSmul : ((((j : ZMod p).val • oneRep : lattice F 0) : F)) =
          ((j : ZMod p).val : F) := by
        change (j : ZMod p).val • (1 : F) = ((j : ZMod p).val : F)
        simp only [nsmul_eq_mul, mul_one]
      rw [honeSmul]
      simpa only [rep, lam, Submodule.coe_mk, lowCriticalFloorDepth] using
        hteich
    _ = _ := hliteral

/-- Fixed High norm-character generator at the source-forced lower
coordinate, with literal representative `1`. -/
noncomputable def highNormGeneratorPhase
    (hparity : lowCriticalParity t = 1) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (1 : ZMod (Module.finrank F K)))).1
        (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _
          (highParameter_intermediate_indexOne_ne_one
            F K ht hres pi hpi hgen)))
      data.baseAddChar := by
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  have htau : tau ≠ 1 :=
    highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  have hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  rw [hparity] at hCrit
  let hTau : IsStationaryConductorDecomposition tauData.conductor
      (lowCriticalFloorDepth t) 1 := by
    simpa only [tauData, quasiCharDataOfIsConductor_conductor] using hCrit
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) :=
    highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨gammaTau, by
      simpa only [tauData, quasiCharDataOfIsConductor_conductor] using
        hgammaTau⟩
  let rep : lattice F 0 := ⟨1, by simp⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F tauData data.baseAddChar hTau gammaTau
        Gamma.property := by
    simpa only [tau, tauData, hTau, gammaTau, Gamma, rep, hparity] using
      highNormGenerator_one_class F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source
  let R : StationaryClassRepresentative F tauData data.baseAddChar hTau
      gammaTau Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let coordinate := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hcoordinate : ord F (coordinate : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  exact LocalLamprechtPhaseData.oddOfStationaryClass
    (lowCriticalFloorDepth t) hTau Gamma coordinate hcoordinate R

/-- Literal `j.val` multiple of the High generator representative, for the
actual indexed norm character and unchanged source coordinate. -/
noncomputable def highNormLiteralPowerPhase
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))).1
        (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _
          (by
            apply (ramifiedNormCharacterZModEquiv_ne_one_iff
              F K ht hres pi hpi hgen _).2
            intro h
            exact j.property (by
              have h' := congrArg Multiplicative.toAdd h
              simpa using h'))))
      data.baseAddChar := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    exact j.property (by
      have h' := congrArg Multiplicative.toAdd h
      simpa using h')
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  have hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  rw [hparity] at hCrit
  let hPower : IsStationaryConductorDecomposition muData.conductor
      (lowCriticalFloorDepth t) 1 := by
    simpa only [muData, quasiCharDataOfIsConductor_conductor] using hCrit
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) :=
    highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let Gamma : AdmissibleGamma F muData data.baseAddChar :=
    ⟨gammaTau, by
      simpa only [muData, quasiCharDataOfIsConductor_conductor] using
        hgammaTau⟩
  let oneRep : lattice F 0 := ⟨1, by simp⟩
  let rep : lattice F 0 :=
    (j : ZMod (Module.finrank F K)).val • oneRep
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F muData data.baseAddChar hPower gammaTau
        Gamma.property := by
    simpa only [mu, muData, hPower, gammaTau, Gamma, rep, oneRep,
      hparity] using
      highNormLiteral_class F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source j
  let R : StationaryClassRepresentative F muData data.baseAddChar hPower
      gammaTau Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let coordinate := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hcoordinate : ord F (coordinate : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  exact LocalLamprechtPhaseData.oddOfStationaryClass
    (lowCriticalFloorDepth t) hPower Gamma coordinate hcoordinate R

/-- The same actual indexed High row, retaining the Teichmüller
representative constructed by the parameter theorem. -/
noncomputable def highNormActualTeichmullerPhase
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))).1
        (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _
          (by
            apply (ramifiedNormCharacterZModEquiv_ne_one_iff
              F K ht hres pi hpi hgen _).2
            intro h
            exact j.property (by
              have h' := congrArg Multiplicative.toAdd h
              simpa using h'))))
      data.baseAddChar := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    exact j.property (by
      have h' := congrArg Multiplicative.toAdd h
      simpa using h')
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  have hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  rw [hparity] at hCrit
  let hPower : IsStationaryConductorDecomposition muData.conductor
      (lowCriticalFloorDepth t) 1 := by
    simpa only [muData, quasiCharDataOfIsConductor_conductor] using hCrit
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  have hgammaTau : ord F (gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) :=
    highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let Gamma : AdmissibleGamma F muData data.baseAddChar :=
    ⟨gammaTau, by
      simpa only [muData, quasiCharDataOfIsConductor_conductor] using
        hgammaTau⟩
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
    hchar (j : ZMod (Module.finrank F K))
  let rep : lattice F 0 := ⟨lam, by
    rw [mem_lattice_zero_iff F]
    exact highParameter_intermediate_teichmuller_mem_integer F
      (Module.finrank F K) hchar (j : ZMod (Module.finrank F K))⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F muData data.baseAddChar hPower gammaTau
        Gamma.property := by
    simpa only [mu, muData, hPower, gammaTau, Gamma, hchar, lam, rep,
      hparity] using
      highNormTeichmuller_class F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j
  let R : StationaryClassRepresentative F muData data.baseAddChar hPower
      gammaTau Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let coordinate := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hcoordinate : ord F (coordinate : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  exact LocalLamprechtPhaseData.oddOfStationaryClass
    (lowCriticalFloorDepth t) hPower Gamma coordinate hcoordinate R

/-- The named public High source function is the critical function of the
underlying High power phase before proof-data transport. -/
theorem highSourceNormFunction_eq_originalPowerPhase
    (j : OddNormIndex F K) (x : ResidueField F) :
    highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j x =
      (highOddNormCharacterPowerPhase F K ht hres pi hpi hgen
        (data.twistData 1) data.baseAddChar htpos hstrict.le gammaF hgammaF
          source.normRows.a source.normRows.alpha source.normRows.a_coe
            source.normRows.alpha1 source.normRows.alpha_choice
              source.normRows.a_class
                (j : ZMod (Module.finrank F K)) j.property
                (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
                  (lowCriticalConductorDecomposition (t := t)
                    (by omega)).epsilon_le_one
                  (phaseReductionResidualCoordinateSource F K hres pi
                    hpi).lowerUniformizer
                  (phaseReductionResidualCoordinateSource F K hres pi
                    hpi).lower_order)).criticalFunction x := by
  unfold highSourceNormFunction highSourceNormPhase
    LocalLamprechtPhaseData.sourceTiedRow
  unfold highOddNormPhaseForComputationalData
  dsimp only
  exact congrFun
    (transportLocalLamprechtPhaseData_criticalFunction _ _ _) x

/-- The public High source function is the raw polar function built from the
actual Teichmüller representative and the common lower source coordinate. -/
theorem highSourceNormFunction_eq_actualRawPolar
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (x : ResidueField F) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
    let hmu : mu ≠ 1 := by
      apply (ramifiedNormCharacterZModEquiv_ne_one_iff
        F K ht hres pi hpi hgen _).2
      intro h
      exact j.property (by
        have h' := congrArg Multiplicative.toAdd h
        simpa using h')
    let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
    let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
    let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source
    let Gamma : AdmissibleGamma F muData data.baseAddChar :=
      ⟨gammaTau, highNormGamma_order F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source⟩
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
        hgen
    let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
      hchar (j : ZMod (Module.finrank F K))
    let rep : lattice F 0 := ⟨lam, by
      rw [mem_lattice_zero_iff F]
      exact highParameter_intermediate_teichmuller_mem_integer F
        (Module.finrank F K) hchar (j : ZMod (Module.finrank F K))⟩
    let R : StationaryClassRepresentative F muData data.baseAddChar hCrit
        (Gamma : Fˣ) Gamma.property :=
      StationaryClassRepresentative.ofCoefficientRepresentative rep (by
        simpa only [mu, muData, hCrit, gammaTau, Gamma, hchar, lam, rep] using
          highNormTeichmuller_class F K ht hres pi hpi hgen data chiK
            psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
              hgammaF source j)
    highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j x =
      criticalPolarFunction F muData data.baseAddChar
        (lowCriticalFloorDepth t)
        (by simpa only [muData, quasiCharDataOfIsConductor_conductor,
          hparity] using hCrit.conductor_eq)
        hCrit.conductor_gt_one Gamma
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (lowCriticalFloorDepth t))
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
          (lowCriticalFloorDepth t))
        R.toLamprecht x := by
  dsimp only
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    exact j.property (by
      have h' := congrArg Multiplicative.toAdd h
      simpa using h')
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  let Gamma : AdmissibleGamma F muData data.baseAddChar :=
    ⟨gammaTau, highNormGamma_order F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source⟩
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
    hchar (j : ZMod (Module.finrank F K))
  let rep : lattice F 0 := ⟨lam, by
    rw [mem_lattice_zero_iff F]
    exact highParameter_intermediate_teichmuller_mem_integer F
      (Module.finrank F K) hchar (j : ZMod (Module.finrank F K))⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F muData data.baseAddChar hCrit gammaTau
        Gamma.property := by
    simpa only [mu, muData, hCrit, gammaTau, Gamma, hchar, lam, rep] using
      highNormTeichmuller_class F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j
  let R : StationaryClassRepresentative F muData data.baseAddChar hCrit
      (Gamma : Fˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  unfold highSourceNormFunction highSourceNormPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold highOddNormPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold highOddNormCharacterPowerPhase
  have hraw := sourceTiedStationary_odd_criticalFunction hCrit
    hparity Gamma R
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order x
  unfold LocalLamprechtPhaseData.sourceTiedRow at hraw
  convert hraw using 1 <;>
    simp only [mu, hmu, muData, hCrit, gammaTau, Gamma, hchar, lam, rep, R]
  congr 1

/-- The explicitly reconstructed actual Teichmüller row has the same raw
polar description. -/
theorem highActualTeichmuller_criticalFunction_eq_rawPolar
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (x : ResidueField F) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
    let hmu : mu ≠ 1 := by
      apply (ramifiedNormCharacterZModEquiv_ne_one_iff
        F K ht hres pi hpi hgen _).2
      intro h
      exact j.property (by
        have h' := congrArg Multiplicative.toAdd h
        simpa using h')
    let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
    let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
    let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source
    let Gamma : AdmissibleGamma F muData data.baseAddChar :=
      ⟨gammaTau, highNormGamma_order F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source⟩
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
        hgen
    let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
      hchar (j : ZMod (Module.finrank F K))
    let rep : lattice F 0 := ⟨lam, by
      rw [mem_lattice_zero_iff F]
      exact highParameter_intermediate_teichmuller_mem_integer F
        (Module.finrank F K) hchar (j : ZMod (Module.finrank F K))⟩
    let R : StationaryClassRepresentative F muData data.baseAddChar hCrit
        (Gamma : Fˣ) Gamma.property :=
      StationaryClassRepresentative.ofCoefficientRepresentative rep (by
        simpa only [mu, muData, hCrit, gammaTau, Gamma, hchar, lam, rep] using
          highNormTeichmuller_class F K ht hres pi hpi hgen data chiK
            psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
              hgammaF source j)
    (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source j hparity).criticalFunction x =
      criticalPolarFunction F muData data.baseAddChar
        (lowCriticalFloorDepth t)
        (by simpa only [muData, quasiCharDataOfIsConductor_conductor,
          hparity] using hCrit.conductor_eq)
        hCrit.conductor_gt_one Gamma
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (lowCriticalFloorDepth t))
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
          (lowCriticalFloorDepth t))
        R.toLamprecht x := by
  dsimp only
  unfold highNormActualTeichmullerPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  rw [LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction]
  rfl

/-- Public source tie: the named High norm-row function is exactly the
actual Teichmüller-row function at the common source coordinate. -/
theorem highSourceNormFunction_eq_actualTeichmuller
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (x : ResidueField F) :
    highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j x =
      (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j hparity).criticalFunction x := by
  rw [highSourceNormFunction_eq_actualRawPolar F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source j hparity x]
  exact (highActualTeichmuller_criticalFunction_eq_rawPolar F K ht
    hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
      hstrict hupper gammaF hgammaF source j hparity x).symm

/-- Exact change datum from the literal natural multiple to the actual High
Teichmüller representative at the unchanged dropped conductor and source
coordinate. -/
noncomputable def highTeichmullerLiteralRepresentativeChange
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    OddRepresentativeChangeData
      (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j hparity)
      (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j hparity) := by
  unfold highNormLiteralPowerPhase
    highNormActualTeichmullerPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  exact {
    d := lowCriticalFloorDepth t
    hm := _
    hlarge := _
    Gamma := _
    delta := _
    hdelta := _
    beta := _
    beta' := _
    hbeta := _
    hbeta' := _
    source_eq := rfl
    selected_eq := rfl }

/-- Exact complete-function transport from the literal High row to the
actual Teichmüller row, retaining the affine translation factor. -/
theorem highActualTeichmuller_criticalFunction_eq_exact_translation
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (x : ResidueField F) :
    (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source j hparity).criticalFunction x =
      (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j hparity).criticalFunction x *
        psi0
          (OddRepresentativeChangeData.translationCoefficient
            (highTeichmullerLiteralRepresentativeChange F K ht hres
              pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
                htpos hstrict hupper gammaF hgammaF source j hparity)
              psi0 hpsi0 * x) :=
  OddRepresentativeChangeData.criticalFunction_eq_mul_translation
    (highTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source j hparity) psi0 hpsi0 x

/-- Changing the High stationary representative preserves the polar
coefficient; the difference is purely affine. -/
theorem highActualTeichmuller_polarCoefficient_eq_literal
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source j hparity).polarCoefficient psi0 hpsi0 =
      (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j hparity).polarCoefficient psi0 hpsi0 := by
  unfold highNormActualTeichmullerPhase
    highNormLiteralPowerPhase
  dsimp only
  rfl

/-- In the common source coordinate, the literal indexed High row is the
pointwise `j.val`-th power of the literal index-one generator row. -/
theorem highNormLiteralPower_criticalFunction_eq_pow
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (x : ResidueField F) :
    (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source j hparity).criticalFunction x =
      ((highNormGeneratorPhase F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source hparity).criticalFunction x) ^
        (j : ZMod (Module.finrank F K)).val := by
  unfold highNormLiteralPowerPhase highNormGeneratorPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  rw [LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction,
    LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction]
  apply criticalPolarFunction_pow_of_literal_nsmul
  · simp only [quasiCharDataOfIsConductor_character]
    exact congrArg (fun z : NormCharacter F K ↦ (z.1 : ContinuousQuasiChar F))
      (highParameter_intermediate_index_eq_power F K ht hres pi hpi hgen
        (j : ZMod (Module.finrank F K)))
  · simp only [StationaryClassRepresentative.toLamprecht,
      StationaryClassRepresentative.ofCoefficientRepresentative]
    simp [nsmul_eq_mul]

end HighNormLiteralTransport


end

end LanglandsFirstMainLemma
