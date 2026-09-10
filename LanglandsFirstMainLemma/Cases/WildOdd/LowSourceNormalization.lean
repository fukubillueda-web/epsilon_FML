import LanglandsFirstMainLemma.Cases.WildOdd.LowerResidualCoefficients
import LanglandsFirstMainLemma.Cases.WildOdd.UpperResidualCoefficients

namespace LanglandsFirstMainLemma

noncomputable section

section LowActual

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
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
  (hLow : (data.twistData 1).conductor ≤ s + 1 + 1)
  (delta : Fˣ) (epsilon1 : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((s + 1 + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) :
      WithTop ℤ))
  (hepsilon1 : ord K (epsilon1 : K) =
    (((s + 1 + 1 - (data.twistData 1).conductor : ℕ) : ℤ) :
      WithTop ℤ))
  (hT : 2 ≤ s + 1 + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth (s + 1)) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (s + 1 + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := s + 1) hT)
        delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF))
  (table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)

local instance lowSourceNormalization_neZero :
    NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance lowSourceNormalization_degreePrime :
    Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance lowSourceNormalization_residueFintype :
    Fintype (ResidueField F) := residueFieldFintype F

/-- Branch-uniform normalization of the retained actual Low source. -/
noncomputable def lowActualNormalization
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    WildOddUpperPolarNormalization (ResidueField F) (Module.finrank F K) := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a := s + 1 - 2 * d
  let u : K := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have hLow' := hLow
  rw [hc] at hLow'
  have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
    dsimp only [a]
    omega
  let hu : ord K u = ((a : ℤ) : WithTop ℤ) := by
    rw [show (((a : ℕ) : ℤ) : WithTop ℤ) = (a : WithTop ℤ) by
      norm_num]
    simpa only [u, ha] using
      (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (a : ℤ) u hu
  let zeta :=
    (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm zetaK
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega : 0 < s + 1) pi hpi hgen
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  exact wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
    hchar C etaZero zeta

theorem lowActualNormalization_eq_strict
    (hepsilon : epsilon = 1)
    (hstrict : (data.twistData 1).conductor < s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    lowActualNormalization F K ht hres pi hpi hgen data hF hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF P hepsilon C =
      lowActualNormalization_strict F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon hstrict C := by
  unfold lowActualNormalization lowActualNormalization_strict
  congr

/-- At boundary depth zero, the source-initial-residue definition is exactly
the coordinate stored in the actual boundary norm package. -/
private theorem lowBoundary_sourceInitialResidue_eq_zeta
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let a : ℕ := s + 1 - 2 * d
    let u : K := lowNormalizedRatio F K epsilon1 P
    let hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
      have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
        dsimp only [a]
        have hc := hF.conductor_eq
        rw [hepsilon, hboundary] at hc
        rw [hboundary]
        omega
      change ord K (lowNormalizedRatio F K epsilon1 P) = _
      rw [lowNormalizedRatio_order F K epsilon1 hepsilon1 P, ha]
      norm_num
    let e := PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) hres
    let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    e.symm (sourceInitialResidue K S.upperUniformizer S.upper_order
      (a : ℤ) u hu) = B.zeta := by
  dsimp only
  have ha : s + 1 - 2 * d = 0 := by
    have hc := hF.conductor_eq
    rw [hepsilon, hboundary] at hc
    omega
  unfold wildOddLowBoundaryNormNormalization
    WildOddBoundaryNormNormalization.of_order_zero sourceInitialResidue
  dsimp only
  congr 2
  simp only [ha, Nat.cast_zero, zpow_zero, div_one]

theorem lowActualNormalization_eq_boundary
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    lowActualNormalization F K ht hres pi hpi hgen data hF hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF P hepsilon C =
      wildOddUpperPolarNormalizationOfSource F (Module.finrank F K) hchar C
        etaZero B.zeta := by
  dsimp only
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a : ℕ := s + 1 - 2 * d
  let u : K := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have hLow' := hLow
  rw [hc] at hLow'
  have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
    dsimp only [a]
    omega
  let hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    rw [show ((((a : ℕ) : ℤ) : WithTop ℤ)) = (a : WithTop ℤ) by
      norm_num]
    simpa only [u, ha] using
      (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (a : ℤ) u hu
  let zeta :=
    (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm zetaK
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega : 0 < s + 1) pi hpi hgen
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  change wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
      hchar C etaZero zeta =
    wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
      hchar C etaZero B.zeta
  congr 1
  simpa only [S, a, u, hu, zetaK, zeta, B] using
    (lowBoundary_sourceInitialResidue_eq_zeta F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon
        hboundary)

theorem lowActualNormalization_dZero_ne_zero
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow delta
      epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    N.dZero ≠ 0 := by
  dsimp only
  by_cases hboundary : (data.twistData 1).conductor = s + 1 + 1
  · let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    have hN := lowActualNormalization_eq_boundary F K ht hres pi hpi hgen
      data hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon
        hboundary C
    dsimp only at hN
    rw [hN]
    simpa only [wildOddUpperPolarNormalizationOfSource, B] using
      (pow_ne_zero (Module.finrank F K) B.zeta_ne_zero)
  have hstrict : (data.twistData 1).conductor < s + 1 + 1 := by omega
  have hN := lowActualNormalization_eq_strict F K ht hres pi hpi hgen data
    hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon hstrict C
  rw [hN]
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a : ℕ := s + 1 - 2 * d
  let u : K := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
    dsimp only [a]
    omega
  have hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    rw [show ((((a : ℕ) : ℤ) : WithTop ℤ)) = (a : WithTop ℤ) by
      norm_num]
    simpa only [u, ha] using
      (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (a : ℤ) u hu
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  have hzetaK : zetaK ≠ 0 :=
    sourceInitialResidue_ne_zero K S.upperUniformizer S.upper_order
      (a : ℤ) u hu
  have hzeta : e.symm zetaK ≠ 0 := by
    intro hz
    apply hzetaK
    have hz' := congrArg e hz
    simpa only [map_zero, e.apply_symm_apply] using hz'
  simpa only [lowActualNormalization_strict,
    wildOddUpperPolarNormalizationOfSource, S, a, u, hu, zetaK, e] using
      (pow_ne_zero (Module.finrank F K) hzeta)

/-- On the boundary branch the uniform normalization retains the source
coordinate carried by the existing boundary norm package. -/
theorem lowActual_boundaryZeta_eq_sourceResidue
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    N.zeta = B.zeta := by
  dsimp only
  have hN := lowActualNormalization_eq_boundary F K ht hres pi hpi hgen
    data hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon
      hboundary C
  dsimp only at hN
  rw [hN]
  rfl

include hF hLow hepsilon1 in
theorem lowActualSourceUx_mem_lattice
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let z := (C.frobeniusEquiv hchar).symm X
    let x := phaseReductionUpperSourceDisplacement F K pi d z
    let u := lowNormalizedRatio F K epsilon1 P
    u * x ∈ lattice K (((s + 1 - d : ℕ) : ℤ)) := by
  dsimp only
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let z := (C.frobeniusEquiv hchar).symm X
  let x := phaseReductionUpperSourceDisplacement F K pi d z
  let u := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have hLow' := hLow
  rw [hc] at hLow'
  have h2d : 2 * d ≤ s + 1 := by omega
  let a := s + 1 - 2 * d
  have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
    dsimp only [a]
    omega
  have hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    rw [show ((((a : ℕ) : ℤ) : WithTop ℤ)) = (a : WithTop ℤ) by
      norm_num]
    simpa only [u, ha] using
      (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)
  have hx : (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x := by
    rw [← mem_lattice]
    exact phaseReductionUpperSourceDisplacement_mem F K pi hpi d z
  rw [mem_lattice, ord_mul, hu]
  have hdepth : a + d = s + 1 - d := by
    dsimp only [a]
    omega
  calc
    ((((s + 1 - d : ℕ) : ℤ)) : WithTop ℤ) =
        ((((a + d : ℕ) : ℤ)) : WithTop ℤ) := by rw [hdepth]
    _ = (((a : ℕ) : ℤ) : WithTop ℤ) +
        (((d : ℕ) : ℤ) : WithTop ℤ) := by norm_num
    _ ≤ (((a : ℕ) : ℤ) : WithTop ℤ) + ord K x := by
      simpa only [add_comm] using
        add_le_add_left hx (((a : ℕ) : ℤ) : WithTop ℤ)

include hLow hepsilon1 in
noncomputable def lowActualSourceUnit
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F) : Kˣ := by
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let z := (C.frobeniusEquiv hchar).symm X
  let x := phaseReductionUpperSourceDisplacement F K pi d z
  let u := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have hd : 0 < d := by
    have hm := hF.conductor_gt_one
    rw [hc] at hm
    omega
  have hLow' := hLow
  rw [hc] at hLow'
  have h2d : 2 * d ≤ s + 1 := by omega
  have hdepth : 0 < s + 1 - d := by omega
  let ux : lattice K (((s + 1 - d : ℕ) : ℤ)) :=
    ⟨u * x, by
      simpa only [hchar, z, x, u] using
        lowActualSourceUx_mem_lattice F K ht hres pi hpi hgen data hF
          hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C X⟩
  exact (positiveUnitOfLattice K hdepth ux : Kˣ)

@[simp]
theorem lowActualSourceUnit_coe
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let z := (C.frobeniusEquiv hchar).symm X
    let x := phaseReductionUpperSourceDisplacement F K pi d z
    let u := lowNormalizedRatio F K epsilon1 P
    (lowActualSourceUnit F K ht hres pi hpi hgen data hF hLow delta
      epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C X : K) =
        1 + u * x := by
  dsimp only
  simp only [lowActualSourceUnit, coe_positiveUnitOfLattice]

/-- Core normalized-generator calculation. -/
private theorem lowNormalizedNormGeneratorPolar_eq_etaZero
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    (lowNormalizedNormGeneratorPhase F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P hparity).polarCoefficient
        C.lower C.lower_ne_one = etaZero := by
  dsimp only
  unfold lowNormalizedNormGeneratorPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  dsimp only [LocalLamprechtPhaseData.polarCoefficient]
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  change finiteAddCharCoefficient C.lower C.lower_ne_one _ = etaZero
  apply finiteAddCharCoefficient_unique
  apply AddChar.ext
  intro z
  rw [AddChar.mulShift_apply]
  symm
  rw [← wildOddUpperEtaZero_spec S data.baseAddChar A (s + 1) hA C z]
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 :=
    lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (s + 1 + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  have hCrit := lowCriticalConductorDecomposition (t := s + 1) hT
  rw [hparity] at hCrit
  let hTau : IsStationaryConductorDecomposition tauData.conductor
      (lowCriticalFloorDepth (s + 1)) 1 := by
    simpa only [tauData, quasiCharDataOfIsConductor_conductor] using hCrit
  let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨delta, by
      simpa only [tauData, quasiCharDataOfIsConductor_conductor] using hdelta⟩
  let coordinate := phaseReductionSourceCoordinate F S.lowerUniformizer
    (lowCriticalFloorDepth (s + 1))
  have hcoordinate : ord F (coordinate : F) =
      ((lowCriticalFloorDepth (s + 1) : ℤ) : WithTop ℤ) := by
    exact phaseReductionSourceCoordinate_order F S.lowerUniformizer
      S.lower_order (lowCriticalFloorDepth (s + 1))
  let rep : lattice F 0 :=
    ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F tauData data.baseAddChar hTau delta
        Gamma.property := by
    simpa only [tau, tauData, hTau, Gamma, rep, hparity] using
      P.alpha_norm_class
  let R : StationaryClassRepresentative F tauData data.baseAddChar hTau
      delta Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let c : lattice F
      ((tauData.conductor : ℤ) - (tauData.conductor : ℤ)) :=
    R.toLamprecht
  have hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F tauData
            (lowCriticalFloorDepth (s + 1)) 1 (by omega)
              hTau.conductor_eq hTau.conductor_gt_one).int_le_conductor
          (tauData.conductor : ℤ)) c =
      stationaryNumeratorClass F tauData data.baseAddChar
        (tauData.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F tauData
          (lowCriticalFloorDepth (s + 1)) 1 (by omega)
            hTau.conductor_eq hTau.conductor_gt_one) Gamma Gamma.property := by
    simpa only [c, stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  have hzmem : (teichmuller F z : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  change lamprechtResidualAddChar F tauData data.baseAddChar
      (lowCriticalFloorDepth (s + 1)) hTau.conductor_eq
      hTau.conductor_gt_one Gamma coordinate hcoordinate z = _
  calc
    _ = lamprechtResidualAddChar F tauData data.baseAddChar
        (lowCriticalFloorDepth (s + 1)) hTau.conductor_eq
        hTau.conductor_gt_one Gamma coordinate hcoordinate
          (reduce F (teichmuller F z : F) hzmem) := by
            congr 1
            simp [reduce]
    _ = (data.baseAddChar.character
          ((rep : F) * (coordinate : F) ^ 2 * (teichmuller F z : F) /
            ((Gamma : Fˣ) : F)) : ℂ) := by
      exact lamprechtResidualAddChar_integral_lift F tauData
        data.baseAddChar (lowCriticalFloorDepth (s + 1))
        hTau.conductor_eq hTau.conductor_gt_one Gamma coordinate hcoordinate
          c hc (teichmuller F z : F) hzmem
    _ = _ := by
      congr 2
      dsimp only [rep, coordinate, Gamma, A,
        wildOddLowNormalizationCoefficient]
      simp only [phaseReductionSourceCoordinate_coe,
        Units.val_div_eq_div_val]
      have hdepth : 2 * lowCriticalFloorDepth (s + 1) = s + 1 := by
        have hdec := lowCriticalConductor_eq (t := s + 1)
        rw [hparity] at hdec
        omega
      have hdepth' : lowCriticalFloorDepth (s + 1) * 2 = s + 1 := by
        omega
      rw [← pow_mul, hdepth']
      field_simp [Units.ne_zero delta]

private theorem lowPolarCoefficient_eq_of_function_eq
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi₁ chi₂ : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D₁ : LocalLamprechtPhaseData E chi₁ psi)
    (D₂ : LocalLamprechtPhaseData E chi₂ psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hfun : ∀ x, D₁.criticalFunction x = D₂.criticalFunction x) :
    D₁.polarCoefficient psi0 hpsi0 = D₂.polarCoefficient psi0 hpsi0 := by
  let phi₁ := D₁.toCriticalPolarFunction psi0 hpsi0
  let phi₂ := D₂.toCriticalPolarFunction psi0 hpsi0
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (AddChar.IsPrimitive.of_ne_one hpsi0)
  apply AddChar.ext
  intro z
  rw [AddChar.mulShift_apply, AddChar.mulShift_apply]
  have h₁ := phi₁.map_add 1 z
  have h₂ := phi₂.map_add 1 z
  have hphi : ∀ x, phi₁ x = phi₂ x := by
    intro x
    simpa only [phi₁, phi₂,
      LocalLamprechtPhaseData.toCriticalPolarFunction_apply] using hfun x
  rw [hphi, hphi, hphi] at h₁
  have hcommon : phi₂ 1 * phi₂ z ≠ 0 :=
    mul_ne_zero (phi₂.ne_zero 1) (phi₂.ne_zero z)
  apply mul_left_cancel₀ hcommon
  simpa using h₁.symm.trans h₂

private theorem lowLiteralOne_polar_eq_generator
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
    (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient
        C.lower C.lower_ne_one =
      (lowNormalizedNormGeneratorPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P hparity).polarCoefficient
          C.lower C.lower_ne_one := by
  dsimp only
  apply lowPolarCoefficient_eq_of_function_eq _ _ C.lower C.lower_ne_one
  intro X
  simpa only [ZMod.val_one, pow_one] using
    (lowNormalizedLiteralPower_criticalFunction_eq_pow F K ht hres pi hpi
      hgen data hF delta epsilon1 hdelta hT hgammaF P
        (⟨(1 : ZMod (Module.finrank F K)), one_ne_zero⟩ : OddNormIndex F K)
        hparity X)

private theorem lowSourceOne_polar_eq_generator
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
    (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
      hdelta hT hgammaF P j).polarCoefficient C.lower C.lower_ne_one =
      (lowNormalizedNormGeneratorPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P hparity).polarCoefficient
          C.lower C.lower_ne_one := by
  dsimp only
  let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
  calc
    (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j).polarCoefficient C.lower C.lower_ne_one =
        (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient
            C.lower C.lower_ne_one := by
      apply lowPolarCoefficient_eq_of_function_eq _ _ C.lower
        C.lower_ne_one
      intro X
      simpa only [lowSourceNormFunction] using
        (lowSourceNormFunction_eq_actualTeichmuller F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P j hparity X)
    _ = (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient
            C.lower C.lower_ne_one :=
      lowActualTeichmullerPower_polarCoefficient_eq_literal F K ht hres pi
        hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity
          C.lower C.lower_ne_one
    _ = _ := by
      simpa only [j] using
        lowLiteralOne_polar_eq_generator F K ht hres pi hpi hgen data
          hF delta epsilon1 hdelta hT hgammaF P hparity C

private theorem lowSourceOne_polar_eq_etaZero
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
      hdelta hT hgammaF P j).polarCoefficient C.lower C.lower_ne_one =
        etaZero := by
  dsimp only
  rw [lowSourceOne_polar_eq_generator F K ht hres pi hpi hgen data
    hF delta epsilon1 hdelta hT hgammaF P hparity C]
  exact lowNormalizedNormGeneratorPolar_eq_etaZero F K ht hres pi hpi
    hgen data hF delta epsilon1 hdelta hT hgammaF P hparity C

/-- The actual retained norm-generator row at index one has the elementary
post-drop polar coefficient `etaZero`.  The proof evaluates `P.alpha` at
the new conductor and then transports through the literal and selected
Teichmuller representatives without changing the polar term. -/
theorem lowActual_normGeneratorPolar_eq_etaZero
    (hepsilon : epsilon = 1)
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
      hdelta hT hgammaF P j).polarCoefficient C.lower C.lower_ne_one =
        N.etaZero := by
  dsimp only
  rw [lowSourceOne_polar_eq_etaZero F K ht hres pi hpi hgen data hF
    delta epsilon1 hdelta hT hgammaF P hparity C]
  unfold lowActualNormalization
  rfl

private theorem lowActual_zsmul_one (a : ℤ) :
    a • ((1 : ℤ) : WithTop ℤ) = (a : WithTop ℤ) := by
  cases a with
  | ofNat n => simp
  | negSucc n => rw [negSucc_zsmul]; norm_num [Int.negSucc_eq]

/-- The actual Low base phase has polar coefficient `eta = etaZero*dZero`.
The proof retains `P.beta`, rewrites its exact denominator ratio as
`(P.alpha / delta) * norm(u)`, and transports the actual source initial
residue downstairs with no extra uniformizer scalar. -/
theorem lowActual_basePolar_eq_eta
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let N := lowActualNormalization (F := F) (K := K) (ht := ht)
      (hres := hres) (pi := pi) (hpi := hpi) (hgen := hgen) (data := data)
      (hF := hF) (hLow := hLow) (delta := delta) (epsilon1 := epsilon1)
      (hdelta := hdelta) (hepsilon1 := hepsilon1) (hT := hT)
      (hgammaF := hgammaF) (P := P) hepsilon C
    (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table).polarCoefficient C.lower C.lower_ne_one = N.eta := by
  subst epsilon
  dsimp only
  unfold lowSourceBasePhase LocalLamprechtPhaseData.sourceTiedRow
  rw [show PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      (d := d) (epsilon := 1) hF.epsilon_le_one
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order =
      .odd (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d)
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d) by
    unfold PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
    simp]
  unfold lowBasePhase
  dsimp only
  unfold localPhaseOfStationaryClass LocalLamprechtPhaseData.oddOfStationaryClass
  dsimp only [LocalLamprechtPhaseData.polarCoefficient]
  let p := Module.finrank F K
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := norm F K u
  have hconductor : (data.twistData 1).conductor = 2 * d + 1 :=
    hF.conductor_eq
  have hLow' := hLow
  rw [hconductor] at hLow'
  let aNat : ℕ := s + 1 - 2 * d
  have haNat : s + 1 + 1 - (data.twistData 1).conductor = aNat := by
    dsimp only [aNat]
    omega
  let huNat : ord K u = (((aNat : ℕ) : ℤ) : WithTop ℤ) := by
    rw [show ((((aNat : ℕ) : ℤ) : WithTop ℤ)) =
        ((aNat : ℕ) : WithTop ℤ) by norm_num]
    simpa only [u, haNat] using
      lowNormalizedRatio_order F K epsilon1 hepsilon1 P
  let a : ℤ := (aNat : ℤ)
  have hu : ord K u = (a : WithTop ℤ) := by
    simpa only [a] using huNat
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (aNat : ℤ) u huNat
  let zeta := e.symm zetaK
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  unfold lowActualNormalization
  dsimp only [wildOddUpperPolarNormalizationOfSource]
  change finiteAddCharCoefficient C.lower C.lower_ne_one _ =
    etaZero * zeta ^ p
  apply finiteAddCharCoefficient_unique
  apply AddChar.ext
  intro X
  rw [AddChar.mulShift_apply]
  symm
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨lowGammaF F K delta epsilon1, hgammaF⟩
  let coordinate := phaseReductionSourceCoordinate F S.lowerUniformizer d
  have hcoordinate : ord F (coordinate : F) = ((d : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F S.lowerUniformizer S.lower_order d
  let R : StationaryClassRepresentative F (data.twistData 1)
      data.baseAddChar hF (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
      represents := by simpa only [Gamma] using table.beta_native_class }
  let c := R.toLamprecht
  have hc := R.toLamprecht_represents
  have hXmem : (teichmuller F X : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F X).property
  change lamprechtResidualAddChar F (data.twistData 1) data.baseAddChar d
      hF.conductor_eq hF.conductor_gt_one Gamma coordinate hcoordinate X = _
  calc
    _ = lamprechtResidualAddChar F (data.twistData 1) data.baseAddChar d
        hF.conductor_eq hF.conductor_gt_one Gamma coordinate hcoordinate
          (reduce F (teichmuller F X : F) hXmem) := by
            congr 1
            simp [reduce]
    _ = (data.baseAddChar.character
          ((c : F) * (coordinate : F) ^ 2 * (teichmuller F X : F) /
            ((Gamma : Fˣ) : F)) : ℂ) := by
      exact lamprechtResidualAddChar_integral_lift F (data.twistData 1)
        data.baseAddChar d hF.conductor_eq hF.conductor_gt_one Gamma
          coordinate hcoordinate c hc (teichmuller F X : F) hXmem
    _ = _ := by
      have hn : ord F n = (a : WithTop ℤ) := by
        dsimp only [n]
        rw [ord_norm, hres, one_nsmul, hu]
      let n0 : F := n / (S.lowerUniformizer : F) ^ a
      have hn0ord : ord F n0 = (0 : WithTop ℤ) := by
        dsimp only [n0]
        rw [ord_div, hn, ord_zpow, S.lower_order, lowActual_zsmul_one]
        simp
      have hn0mem : n0 ∈ lattice F 0 := by
        rw [mem_lattice, hn0ord]
        exact le_rfl
      have hn0res : reduce F n0 hn0mem = zeta ^ p := by
        have hb := sourceInitialResidue_norm_downstairs_eq_pow F K ht
          (by omega) hres S a u hu
        dsimp only at hb
        simpa only [sourceInitialResidue, n0, n, zeta, zetaK, e, p] using hb
      let x0 : F := n0 * (teichmuller F X : F)
      have hx0mem : x0 ∈ lattice F 0 := by
        dsimp only [x0]
        simpa using mul_mem_lattice F hn0mem hXmem
      have hx0res : reduce F x0 hx0mem = zeta ^ p * X := by
        change residueMap F
            (⟨x0, (mem_lattice_zero_iff F).1 hx0mem⟩ :
              ringOfIntegers F) = _
        change residueMap F
            ((⟨n0, (mem_lattice_zero_iff F).1 hn0mem⟩ :
                ringOfIntegers F) *
              ⟨(teichmuller F X : F),
                (mem_lattice_zero_iff F).1 hXmem⟩) = _
        rw [map_mul]
        change reduce F n0 hn0mem * residueMap F (teichmuller F X) = _
        rw [hn0res, residueMap_teichmuller]
      have hcRatio :
          (c : F) / (lowGammaF F K delta epsilon1 : F) =
            (A : F) * n := by
        have hnorm : n = lowOddNormalizedNorm
            (F := F) (K := K) (P := P) (hT := hT) := by
          dsimp only [n, u]
          simpa only [lowOddNormalizedNorm] using
            lowNormalizedRatio_norm F K epsilon1 P
        rw [hnorm]
        dsimp only [c, R, StationaryClassRepresentative.toLamprecht,
          StationaryClassRepresentative.coe_unit]
        simp only [A, wildOddLowNormalizationCoefficient,
          lowOddNormalizedNorm, lowGammaF, Units.val_div_eq_div_val]
        field_simp [Units.ne_zero delta, Units.ne_zero P.alpha,
          Units.ne_zero (lowEpsilon F K epsilon1)]
      have hdepth : a + 2 * (d : ℤ) = ((s + 1 : ℕ) : ℤ) := by
        have hdepthNat : aNat + 2 * d = s + 1 := by
          dsimp only [aNat]
          omega
        dsimp only [a]
        exact_mod_cast hdepthNat
      have hpow : (S.lowerUniformizer : F) ^ (s + 1) =
          (S.lowerUniformizer : F) ^ a *
            ((S.lowerUniformizer : F) ^ d) ^ 2 := by
        calc
          (S.lowerUniformizer : F) ^ (s + 1) =
              (S.lowerUniformizer : F) ^ ((s + 1 : ℕ) : ℤ) := by
                rw [zpow_natCast]
          _ = (S.lowerUniformizer : F) ^ (a + 2 * (d : ℤ)) := by
                rw [hdepth]
          _ = (S.lowerUniformizer : F) ^ a *
              (S.lowerUniformizer : F) ^ (2 * (d : ℤ)) :=
                zpow_add₀ (Units.ne_zero S.lowerUniformizer) _ _
          _ = (S.lowerUniformizer : F) ^ a *
              ((S.lowerUniformizer : F) ^ d) ^ 2 := by
                rw [show (S.lowerUniformizer : F) ^ (2 * (d : ℤ)) =
                    (S.lowerUniformizer : F) ^ (2 * d) by
                  rw [← zpow_natCast]
                  congr 2]
                rw [← pow_mul]
                congr 2
                omega
      have harg :
          (c : F) * (coordinate : F) ^ 2 * (teichmuller F X : F) /
              ((Gamma : Fˣ) : F) =
            (A : F) * (S.lowerUniformizer : F) ^ (s + 1) * x0 := by
        have hgamma : ((Gamma : Fˣ) : F) =
            (lowGammaF F K delta epsilon1 : F) := rfl
        rw [hgamma]
        rw [show (c : F) * (coordinate : F) ^ 2 *
              (teichmuller F X : F) /
                (lowGammaF F K delta epsilon1 : F) =
            ((c : F) / (lowGammaF F K delta epsilon1 : F)) *
              (coordinate : F) ^ 2 * (teichmuller F X : F) by ring]
        rw [hcRatio]
        dsimp only [coordinate, x0, n0]
        simp only [phaseReductionSourceCoordinate_coe]
        rw [hpow]
        field_simp [Units.ne_zero S.lowerUniformizer]
      rw [harg]
      have hcompact := wildOddCompactEta_integral F K S data.baseAddChar A
        (s + 1) hA C x0 hx0mem
      rw [hx0res] at hcompact
      calc
        _ = C.lower (etaZero * (zeta ^ p * X)) := by
          simpa only [etaZero] using hcompact.symm
        _ = _ := by
          congr 1
          ring

/-- The named generator inherits `etaZero` from the actual source row at
`j = 1`; the retained affine translation does not alter its polar term. -/
theorem lowActual_generatorNamedEta_eq_etaZero
    (hepsilon : epsilon = 1)
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    let generator := wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hT hgammaF P hparity C.lower
        C.lower_ne_one hcharOdd
    generator.eta = N.etaZero := by
  dsimp only
  letI : Fact (1 < Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).one_lt⟩
  let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
  let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
    delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
  let generator := wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P hparity C.lower
      C.lower_ne_one hcharOdd
  have hrow := congrArg WildOddCoefficientPair.polar
    (wildOdd_lowSourceNormCoefficients F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j hparity C.lower C.lower_ne_one
        hcharOdd)
  have heta :
      (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j).polarCoefficient C.lower C.lower_ne_one =
          generator.eta := by
    simpa [generator, j, wildOddTauPowerPair, ZMod.val_one] using hrow
  have hactual := lowActual_normGeneratorPolar_eq_etaZero F K ht hres pi hpi
    hgen data hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon
      hparity C
  exact heta.symm.trans (by simpa only [j, N] using hactual)

/-- The actual named base row inherits the source-faithful base polar
coefficient `eta`. -/
theorem lowActual_baseNamedEta_eq_eta
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let hbaseOdd : Odd (data.twistData 1).conductor := ⟨d, by
      simpa [hepsilon] using hF.conductor_eq⟩
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    let base := wildOddLowBaseNamedPair F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table C.lower C.lower_ne_one hcharOdd hbaseOdd
    base.eta = N.eta := by
  dsimp only
  simpa only [wildOddLowBaseNamedPair, wildOddNamedPairOfPhase,
    WildOddNamedCoefficientPair.ofPair, wildOddCoefficientPair] using
      (lowActual_basePolar_eq_eta F K ht hres pi hpi hgen data chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table hepsilon C)

/-- Boundary notation for the base row preserves the same actual `eta`. -/
theorem lowActual_boundaryBaseNamedEta_eq_eta
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    let base := wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table hboundary hparity C.lower
          C.lower_ne_one hcharOdd
    base.eta = N.eta := by
  dsimp only
  simpa only [wildOddLowBoundaryBaseNamedPair, wildOddLowBaseNamedPair,
    wildOddNamedPairOfPhase, WildOddNamedCoefficientPair.ofPair,
    wildOddCoefficientPair] using
      (lowActual_basePolar_eq_eta F K ht hres pi hpi hgen data chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table hepsilon C)

/-- On the boundary the named ratio is precisely the `dZero` belonging to
the actual source normalization. -/
theorem lowActual_boundaryDZero_eq
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
    let generator := wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hT hgammaF P hparity C.lower
        C.lower_ne_one hcharOdd
    let base := wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table hboundary hparity C.lower
          C.lower_ne_one hcharOdd
    wildOddBoundaryDZero generator base = N.dZero := by
  dsimp only
  let N := lowActualNormalization F K ht hres pi hpi hgen data hF hLow
    delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon C
  let generator := wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P hparity C.lower
      C.lower_ne_one hcharOdd
  let base := wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table hboundary hparity C.lower C.lower_ne_one
        hcharOdd
  have hgeneratorEta : generator.eta = N.etaZero := by
    simpa only [generator, N] using
      (lowActual_generatorNamedEta_eq_etaZero F K ht hres pi hpi hgen data
        hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon
          hparity C hcharOdd)
  have hbaseEta : base.eta = N.eta := by
    simpa only [base, N] using
      (lowActual_boundaryBaseNamedEta_eq_eta F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table hepsilon hboundary hparity C
            hcharOdd)
  have hetaZero : N.etaZero ≠ 0 := by
    rw [← hgeneratorEta]
    exact generator.eta_ne_zero
  change wildOddBoundaryDZero generator base = N.dZero
  unfold wildOddBoundaryDZero
  rw [hbaseEta, hgeneratorEta, N.eta_eq]
  field_simp [hetaZero]


end LowActual

/-! ## Public source-normalization facade -/

/-- Compact facade for the actual Low normalization, canonical source unit,
two polar identifications, named rows, and boundary compatibility consumed by
the later phase assembly. -/
structure WildOddLowSourceNormalizationAPI : Prop where
  strictComparison : type_of% @lowActualNormalization_eq_strict
  boundaryComparison : type_of% @lowActualNormalization_eq_boundary
  dZeroNonzero : type_of% @lowActualNormalization_dZero_ne_zero
  boundarySource : type_of% @lowActual_boundaryZeta_eq_sourceResidue
  sourceDisplacement : type_of% @lowActualSourceUx_mem_lattice
  sourceUnitCoe : type_of% @lowActualSourceUnit_coe
  generatorPolar : type_of% @lowActual_normGeneratorPolar_eq_etaZero
  basePolar : type_of% @lowActual_basePolar_eq_eta
  generatorNamedEta : type_of% @lowActual_generatorNamedEta_eq_etaZero
  baseNamedEta : type_of% @lowActual_baseNamedEta_eq_eta
  boundaryBaseNamedEta :
    type_of% @lowActual_boundaryBaseNamedEta_eq_eta
  boundaryDZero : type_of% @lowActual_boundaryDZero_eq

/-- Principal exported package for the WildOdd actual Low source bridge. -/
theorem wildOdd_lowSourceNormalization : WildOddLowSourceNormalizationAPI where
  strictComparison := lowActualNormalization_eq_strict
  boundaryComparison := lowActualNormalization_eq_boundary
  dZeroNonzero := lowActualNormalization_dZero_ne_zero
  boundarySource := lowActual_boundaryZeta_eq_sourceResidue
  sourceDisplacement := lowActualSourceUx_mem_lattice
  sourceUnitCoe := lowActualSourceUnit_coe
  generatorPolar := lowActual_normGeneratorPolar_eq_etaZero
  basePolar := lowActual_basePolar_eq_eta
  generatorNamedEta := lowActual_generatorNamedEta_eq_etaZero
  baseNamedEta := lowActual_baseNamedEta_eq_eta
  boundaryBaseNamedEta := lowActual_boundaryBaseNamedEta_eq_eta
  boundaryDZero := lowActual_boundaryDZero_eq

end

end LanglandsFirstMainLemma
