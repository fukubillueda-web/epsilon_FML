import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.LowAssembly

/-!
# Named low odd-prime residual rows

This module exposes the source-tied low residual rows and completes the
low table-backed endpoint theorem while preserving the exact section
parameters of the original monolithic file.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

section LowTableBacked

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

/-! ### Named source-tied low residual rows -/

/-- Actual low-range upstairs row at the upper coordinate forced by the
common source and the explicitly supplied table witness. -/
noncomputable def lowSourceUpstairsPhase
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :
    LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table WUp)
    hF.epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).upper_order

/-- Complete residual function of the actual low-range upstairs row. -/
noncomputable def lowSourceUpstairsFunction
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) : ResidueField K → ℂ :=
  (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table WUp).criticalFunction

/-- Actual `j=0` base row at its own conductor and the common lower source
coordinate. -/
noncomputable def lowSourceBasePhase :
    LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table)
    hF.epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order

/-- Complete residual function of the actual low `j=0` base row. -/
noncomputable def lowSourceBaseFunction : ResidueField F → ℂ :=
  (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
    hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
      table).criticalFunction

/-- Actual nonidentity norm row at conductor `t+1` and its newly constructed
critical depth. -/
noncomputable def lowSourceNormPhase
    (j : OddNormIndex F K) :
    LocalLamprechtPhaseData F
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))))
      data.baseAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j)
    (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order

/-- Complete residual function of the actual low nonidentity norm row. -/
noncomputable def lowSourceNormFunction
    (j : OddNormIndex F K) : ResidueField F → ℂ :=
  (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1 hdelta
    hT hgammaF P j).criticalFunction

/-- The named source-tied norm function is the complete function of the
actual powered norm-character phase inserted by the low parameter table. -/
theorem lowSourceNormFunction_eq_powerPhase
    (j : OddNormIndex F K) (x : ResidueField F) :
    lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j x =
      (lowNormCharacterPowerPhase F K ht hres pi hpi hgen
        (data.twistData 1) data.baseAddChar hF delta epsilon1 hdelta hT
          hgammaF P (j : ZMod (Module.finrank F K)) j.property
            (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
              (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
              (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
              (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)).criticalFunction x := by
  unfold lowSourceNormFunction lowSourceNormPhase
    LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddNormPhaseForComputationalData
  dsimp only
  exact congrFun
    (transportLocalLamprechtPhaseData_criticalFunction _ _ _) x

/-- Actual nonidentity low twist row at conductor `t+1`, using its explicit
table witness and the same lower source coordinate as the norm row. -/
noncomputable def lowSourceTwistPhase
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (j : OddNormIndex F K) :
    LocalLamprechtPhaseData F
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))))
      data.baseAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j (WTwist j))
    (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order

/-- Complete residual function of the actual low nonidentity twist row. -/
noncomputable def lowSourceTwistFunction
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (j : OddNormIndex F K) : ResidueField F → ℂ :=
  (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
    hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
      table WTwist j).criticalFunction


/-- Complete critical functions multiply at one common coordinate when the
three actual stationary numerator/denominator ratios add literally. -/
private theorem criticalPolarFunction_mul_of_literal_ratios
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi chi1 chi2 : LocalQuasiCharData E)
    (psi : LocalAddCharData E)
    (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hm1 : chi1.conductor = 2 * d + 1)
    (hm2 : chi2.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (hlarge1 : 1 < chi1.conductor)
    (hlarge2 : 1 < chi2.conductor)
    (hchar : chi.character = chi1.character * chi2.character)
    (gamma gamma1 gamma2 : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma1 : ord E (gamma1 : E) =
      (((chi1.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma2 : ord E (gamma2 : E) =
      (((chi2.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (beta1 : lattice E ((chi1.conductor : ℤ) - (chi1.conductor : ℤ)))
    (beta2 : lattice E ((chi2.conductor : ℤ) - (chi2.conductor : ℤ)))
    (hratio : (beta : E) / (gamma : E) =
      (beta1 : E) / (gamma1 : E) +
        (beta2 : E) / (gamma2 : E))
    (x : ResidueField E) :
    criticalPolarFunction E chi psi d hm hlarge ⟨gamma, hgamma⟩
        delta hdelta beta x =
      criticalPolarFunction E chi1 psi d hm1 hlarge1 ⟨gamma1, hgamma1⟩
          delta hdelta beta1 x *
        criticalPolarFunction E chi2 psi d hm2 hlarge2 ⟨gamma2, hgamma2⟩
          delta hdelta beta2 x := by
  unfold criticalPolarFunction criticalPolarValue
  rw [hchar, ContinuousQuasiChar.mul_apply]
  have hu1 :
      criticalPolarUnit E chi d hm hlarge delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
        criticalPolarUnit E chi1 d hm1 hlarge1 delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hu2 :
      criticalPolarUnit E chi d hm hlarge delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
        criticalPolarUnit E chi2 d hm2 hlarge2 delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hchi1 := congrArg
    (fun u : unitFiltration E d => chi1.character (u : Eˣ)) hu1
  have hchi2 := congrArg
    (fun u : unitFiltration E d => chi2.character (u : Eˣ)) hu2
  have hpsi :
      psi.character
          ((beta : E) * (delta : E) * (teichmuller E x : E) /
            (gamma : E)) =
        psi.character
            ((beta1 : E) * (delta : E) * (teichmuller E x : E) /
              (gamma1 : E)) *
          psi.character
            ((beta2 : E) * (delta : E) * (teichmuller E x : E) /
              (gamma2 : E)) := by
    rw [← psi.character.map_add_eq_mul]
    congr 1
    calc
      (beta : E) * (delta : E) * (teichmuller E x : E) / (gamma : E) =
          ((beta : E) / (gamma : E)) * (delta : E) *
            (teichmuller E x : E) := by ring
      _ = ((beta1 : E) / (gamma1 : E) +
          (beta2 : E) / (gamma2 : E)) * (delta : E) *
            (teichmuller E x : E) := by rw [hratio]
      _ = (beta1 : E) * (delta : E) * (teichmuller E x : E) /
            (gamma1 : E) +
          (beta2 : E) * (delta : E) * (teichmuller E x : E) /
            (gamma2 : E) := by ring
  rw [hpsi, hchi1, hchi2]
  push_cast
  rw [mul_inv]
  ring

/-- Below the boundary, the actual base character linearizes on the common
post-drop Low critical coordinate with its transported stationary ratio. -/
private theorem lowBase_linearization_on_lowCriticalCoordinate
    (hstrict : (data.twistData 1).conductor < t + 1)
    (hparity : lowCriticalParity t = 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    let hpow := lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
    let powerData := quasiCharDataOfIsConductor F
      (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
    let source := phaseReductionSourceCoordinate F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (lowCriticalFloorDepth t)
    let z : F := (teichmuller F X : F)
    ((data.twistData 1).character
      (criticalPolarUnit F powerData (lowCriticalFloorDepth t)
        (by
          simp only [powerData, quasiCharDataOfIsConductor_conductor]
          exact (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
            |>.trans (by rw [hparity]))
        (by
          simp only [powerData, quasiCharDataOfIsConductor_conductor]
          exact (lowCriticalConductorDecomposition (t := t) hT).conductor_gt_one)
        source
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
          (lowCriticalFloorDepth t))
        z ((mem_lattice_zero_iff F).2 (teichmuller F X).property) : Fˣ) : ℂ) =
      (data.baseAddChar.character
        ((lowEpsilon F K epsilon1 : F) * (P.beta : F) * (source : F) * z /
          (delta : F)) : ℂ) := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  let source := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  let z : F := (teichmuller F X : F)
  let y : F := (source : F) * z
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨lowGammaF F K delta epsilon1, hgammaF⟩
  let R : StationaryClassRepresentative F (data.twistData 1)
      data.baseAddChar hF (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
      represents := by simpa only [Gamma] using P.beta_norm_class }
  have hdepth : d + epsilon ≤ lowCriticalFloorDepth t := by
    have hbase := hF.conductor_eq
    have hcrit := (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
    have he := hF.epsilon_le_one
    rw [hparity] at hcrit
    omega
  have hyFloor : y ∈ lattice F ((lowCriticalFloorDepth t : ℕ) : ℤ) := by
    exact mul_mem_lattice F (by
      rw [mem_lattice]
      exact (phaseReductionSourceCoordinate_order F
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
        (lowCriticalFloorDepth t)).ge)
      ((mem_lattice_zero_iff F).2 (teichmuller F X).property)
  have hy : y ∈ lattice F ((d + epsilon : ℕ) : ℤ) := by
    exact lattice_antitone F (by exact_mod_cast hdepth) hyFloor
  let unit : Fˣ :=
    criticalPolarUnit F powerData (lowCriticalFloorDepth t)
      (by
        simp only [powerData, quasiCharDataOfIsConductor_conductor]
        exact (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
          |>.trans (by rw [hparity]))
      (by
        simp only [powerData, quasiCharDataOfIsConductor_conductor]
        exact (lowCriticalConductorDecomposition (t := t) hT).conductor_gt_one)
      source
      (phaseReductionSourceCoordinate_order F
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
        (lowCriticalFloorDepth t))
      z ((mem_lattice_zero_iff F).2 (teichmuller F X).property)
  have hunit : (unit : F) = 1 + y := by rfl
  have hraw := stationaryRawFactor_eq_one hF
    (lowGammaF F K delta epsilon1) hgammaF R y hy unit hunit
  have hraw' := hraw
  field_simp [ContinuousQuasiChar.apply_ne_zero] at hraw'
  have harg :
      ((P.beta : F) * y / (lowGammaF F K delta epsilon1 : F)) =
        (lowEpsilon F K epsilon1 : F) * (P.beta : F) * (source : F) * z /
          (delta : F) := by
    dsimp only [y]
    simp only [lowGammaF, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero delta, Units.ne_zero (lowEpsilon F K epsilon1)]
  have hraw'' :
      (data.baseAddChar.character
        ((P.beta : F) * y / (lowGammaF F K delta epsilon1 : F)) : ℂ) =
        ((data.twistData 1).character unit : ℂ) := by
    simpa only [R] using hraw'
  change ((data.twistData 1).character unit : ℂ) = _
  rw [← hraw'', harg]

/-- The named Low norm function is the raw polar function of its actual
powered norm character and actual Teichmüller stationary representative. -/
private theorem lowSourceNormFunction_eq_rawPolar
    (hparity : lowCriticalParity t = 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    let htau : tau ≠ 1 :=
      lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
    let hpow := lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
    let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
    let powerData := quasiCharDataOfIsConductor F
      (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
    let hCrit := lowCriticalConductorDecomposition (t := t) hT
    let Gamma : AdmissibleGamma F powerData data.baseAddChar := ⟨delta, hdelta⟩
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    let omegaF : F :=
      ((primeTeichmuller F (Module.finrank F K) hchar
        (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)
    let rep : lattice F 0 :=
      ⟨omegaF * (P.alpha : F), by
        exact mul_mem_lattice F
          ((mem_lattice_zero_iff F).2
            (primeTeichmuller F (Module.finrank F K) hchar
              (j : ZMod (Module.finrank F K))).property)
          P.alphaRepresentative.norm_exactDepth.1⟩
    let R : StationaryClassRepresentative F powerData data.baseAddChar hCrit
        (Gamma : Fˣ) Gamma.property := by
      have halphaOrd : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
        simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
          P.alphaRepresentative.norm_order
      have hteich : latticeQuotientMk F
            (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
          (j : ZMod (Module.finrank F K)).val • latticeQuotientMk F
            (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
            (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
              lattice F 0) := by
        simpa only [omegaF, rep] using
          (lowTeichmuller_nsmul_class F K (Module.finrank F K)
            ht hres pi hpi hgen rfl hchar
              (j : ZMod (Module.finrank F K)) P.alpha halphaOrd)
      have hpowerClass :
          (j : ZMod (Module.finrank F K)).val •
              stationaryCoefficientClass F tauData data.baseAddChar hCrit
                delta hdelta =
            stationaryCoefficientClass F powerData data.baseAddChar hCrit
              delta hdelta := by
        apply (stationaryCoefficientLamprechtEquivAtConductor F hCrit).injective
        rw [map_nsmul]
        calc
          _ = (j : ZMod (Module.finrank F K)).val •
              stationaryNumeratorClass F tauData data.baseAddChar
                ((t + 1 : ℕ) : ℤ)
                (stationaryDepthOfConductorDecomposition F tauData hCrit)
                delta hdelta := congrArg
                  (fun x => (j : ZMod (Module.finrank F K)).val • x)
                  (stationaryCoefficientClass_toLamprecht F tauData
                    data.baseAddChar hCrit delta hdelta)
          _ = stationaryNumeratorClass F powerData data.baseAddChar
              ((t + 1 : ℕ) : ℤ)
              (stationaryDepthOfConductorDecomposition F powerData hCrit)
              delta hdelta := by
            simpa [tauData, powerData, hCrit] using
              (normCharacterPower_stationaryClass_eq_nsmul
                F K ht hres pi hpi hgen tau htau
                  (j : ZMod (Module.finrank F K)).val hpow data.baseAddChar
                  ((t + 1 : ℕ) : ℤ)
                  (stationaryDepthOfConductorDecomposition F tauData hCrit)
                  delta hdelta).symm
          _ = _ := (stationaryCoefficientClass_toLamprecht F powerData
            data.baseAddChar hCrit delta hdelta).symm
      have hclass : latticeQuotientMk F
            (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
          stationaryCoefficientClass F powerData data.baseAddChar hCrit
            delta hdelta := by
        calc
          _ = (j : ZMod (Module.finrank F K)).val • latticeQuotientMk F
              (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
              (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
                lattice F 0) := hteich
          _ = (j : ZMod (Module.finrank F K)).val •
              stationaryCoefficientClass F tauData data.baseAddChar hCrit
                delta hdelta := congrArg _ P.alpha_norm_class
          _ = _ := hpowerClass
      exact StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
    lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j X =
      criticalPolarFunction F powerData data.baseAddChar
        (lowCriticalFloorDepth t)
        (by simpa only [powerData, quasiCharDataOfIsConductor_conductor,
          hparity] using hCrit.conductor_eq)
        hCrit.conductor_gt_one Gamma
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (lowCriticalFloorDepth t))
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
          (lowCriticalFloorDepth t))
        R.toLamprecht X := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 :=
    lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F powerData data.baseAddChar := ⟨delta, hdelta⟩
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
      (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
  let omegaF : F :=
    ((primeTeichmuller F (Module.finrank F K) hchar
      (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)
  have halphaOrd : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  have hrep : omegaF * (P.alpha : F) ∈ lattice F 0 :=
    mul_mem_lattice F
      ((mem_lattice_zero_iff F).2
        (primeTeichmuller F (Module.finrank F K) hchar
          (j : ZMod (Module.finrank F K))).property)
      ((mem_lattice_and_not_mem_succ_iff F).2 halphaOrd).1
  let rep : lattice F 0 := ⟨omegaF * (P.alpha : F), hrep⟩
  have hteich : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      (j : ZMod (Module.finrank F K)).val • latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
          lattice F 0) := by
    simpa only [omegaF, rep] using
      (lowTeichmuller_nsmul_class F K (Module.finrank F K)
        ht hres pi hpi hgen rfl hchar (j : ZMod (Module.finrank F K))
          P.alpha halphaOrd)
  have hpowerClass :
      (j : ZMod (Module.finrank F K)).val •
          stationaryCoefficientClass F tauData data.baseAddChar hCrit delta
            hdelta =
        stationaryCoefficientClass F powerData data.baseAddChar hCrit delta
          hdelta := by
    apply (stationaryCoefficientLamprechtEquivAtConductor F hCrit).injective
    rw [map_nsmul]
    calc
      _ = (j : ZMod (Module.finrank F K)).val •
          stationaryNumeratorClass F tauData data.baseAddChar
            ((t + 1 : ℕ) : ℤ)
            (stationaryDepthOfConductorDecomposition F tauData hCrit)
            delta hdelta := congrArg
              (fun x => (j : ZMod (Module.finrank F K)).val • x)
              (stationaryCoefficientClass_toLamprecht F tauData
                data.baseAddChar hCrit delta hdelta)
      _ = stationaryNumeratorClass F powerData data.baseAddChar
          ((t + 1 : ℕ) : ℤ)
          (stationaryDepthOfConductorDecomposition F powerData hCrit)
          delta hdelta := by
        simpa [tauData, powerData, hCrit] using
          (normCharacterPower_stationaryClass_eq_nsmul
            F K ht hres pi hpi hgen tau htau
              (j : ZMod (Module.finrank F K)).val hpow data.baseAddChar
              ((t + 1 : ℕ) : ℤ)
              (stationaryDepthOfConductorDecomposition F tauData hCrit)
              delta hdelta).symm
      _ = _ := (stationaryCoefficientClass_toLamprecht F powerData
        data.baseAddChar hCrit delta hdelta).symm
  have hclass : latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F powerData data.baseAddChar hCrit delta
        hdelta := by
    calc
      _ = (j : ZMod (Module.finrank F K)).val • latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
          (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
            lattice F 0) := hteich
      _ = (j : ZMod (Module.finrank F K)).val •
          stationaryCoefficientClass F tauData data.baseAddChar hCrit delta
            hdelta := congrArg _ P.alpha_norm_class
      _ = _ := hpowerClass
  let R : StationaryClassRepresentative F powerData data.baseAddChar hCrit
      (Gamma : Fˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  unfold lowSourceNormFunction lowSourceNormPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddNormPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold lowNormCharacterPowerPhase
  have hraw := sourceTiedStationary_odd_criticalFunction hCrit hparity
    Gamma R
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order X
  unfold LocalLamprechtPhaseData.sourceTiedRow at hraw
  convert hraw using 1 <;>
    simp only [tau, htau, hpow, tauData, powerData, hCrit, Gamma, hchar,
      omegaF, rep, R]
  congr 1

/-- The named Low norm function is pointwise the complete function of the
actual Teichmüller representative used by the representative-transport
package.  Thus the source row and the selected row in that package cannot be
rescaled independently. -/
theorem lowSourceNormFunction_eq_actualTeichmuller
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (X : ResidueField F) :
    lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j X =
      (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P j hparity).criticalFunction X := by
  have hraw := lowSourceNormFunction_eq_rawPolar F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P hparity j X
  dsimp only at hraw
  rw [hraw]
  unfold lowActualTeichmullerPowerPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  rw [LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction]
  rfl

/-- The named Low twist function is the raw polar function attached to the
actual table witness at the common post-drop coordinate. -/
private theorem lowSourceTwistFunction_eq_rawPolar
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hparity : lowCriticalParity t = 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
      (data.twistData 1) hminimal hLow
        (j : ZMod (Module.finrank F K)) j.property
    let hCrit := lowCriticalConductorDecomposition (t := t) hT
    let Gamma : AdmissibleGamma F twist data.baseAddChar := ⟨delta, hdelta⟩
    let R : StationaryClassRepresentative F twist data.baseAddChar hCrit
        (Gamma : Fˣ) Gamma.property :=
      { representative := (WTwist j).representative
        represents := by
          simpa only [twist, hCrit, Gamma] using (WTwist j).represents }
    lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j X =
      criticalPolarFunction F twist data.baseAddChar (lowCriticalFloorDepth t)
        (by simpa only [twist, lowNonzeroTwistDatum_conductor, hparity] using
          hCrit.conductor_eq)
        hCrit.conductor_gt_one Gamma
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (lowCriticalFloorDepth t))
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
          (lowCriticalFloorDepth t))
        R.toLamprecht X := by
  dsimp only
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F twist data.baseAddChar := ⟨delta, hdelta⟩
  let R : StationaryClassRepresentative F twist data.baseAddChar hCrit
      (Gamma : Fˣ) Gamma.property :=
    { representative := (WTwist j).representative
      represents := by
        simpa only [twist, hCrit, Gamma] using (WTwist j).represents }
  unfold lowSourceTwistFunction lowSourceTwistPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  have hraw := sourceTiedStationary_odd_criticalFunction hCrit hparity
    Gamma R
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order X
  unfold LocalLamprechtPhaseData.sourceTiedRow at hraw
  simpa only [twist, hCrit, Gamma, R] using hraw

/-- The named Low base function is its actual stationary polar function at
the source-forced lower coordinate. -/
private theorem lowSourceBaseFunction_eq_rawPolar
    (hepsilon : epsilon = 1) (X : ResidueField F) :
    let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
      ⟨lowGammaF F K delta epsilon1, hgammaF⟩
    let R : StationaryClassRepresentative F (data.twistData 1)
        data.baseAddChar hF (Gamma : Fˣ) Gamma.property :=
      { representative :=
          ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
        represents := by simpa only [Gamma] using P.beta_norm_class }
    lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table X =
      criticalPolarFunction F (data.twistData 1) data.baseAddChar d
        (by rw [hF.conductor_eq, hepsilon]) hF.conductor_gt_one Gamma
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d)
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d)
        R.toLamprecht X := by
  dsimp only
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨lowGammaF F K delta epsilon1, hgammaF⟩
  let R : StationaryClassRepresentative F (data.twistData 1)
      data.baseAddChar hF (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
      represents := by simpa only [Gamma] using P.beta_norm_class }
  unfold lowSourceBaseFunction lowSourceBasePhase
  exact sourceTiedStationary_odd_criticalFunction hF hepsilon Gamma R
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order X

/-- At odd critical parity in the strict Low range, the actual nonidentity
twist and norm rows have the same complete function at the common source. -/
theorem lowSourceTwistFunction_eq_norm_of_strict_of_odd
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hstrict : (data.twistData 1).conductor < t + 1)
    (hparity : lowCriticalParity t = 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j X =
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j X := by
  rw [lowSourceTwistFunction_eq_rawPolar F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WTwist hparity j X,
    lowSourceNormFunction_eq_rawPolar F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P hparity j X]
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  have htwistActual : twist = data.twistData mu := by
    rw [show twist = ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen (data.twistData 1) mu by
      simpa only [twist, mu] using
        (lowNonzeroTwistDatum_eq_actual F K ht hres pi hpi hgen
          (data.twistData 1) hminimal hLow
            (j : ZMod (Module.finrank F K)) j.property)]
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  have hmuPower : mu = tau ^ (j : ZMod (Module.finrank F K)).val := by
    dsimp only [mu, tau]
    exact lowNormCharacterGenerator_pow F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K))
  have hpowerActual : powerData = data.normCharacterData mu := by
    apply LocalQuasiCharData.ext_character F
    rw [quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
    exact congrArg (fun z : NormCharacter F K => z.1) hmuPower.symm
  have hchar : twist.character =
      powerData.character * (data.twistData 1).character := by
    calc
      twist.character = (data.twistData mu).character :=
        congrArg LocalQuasiCharData.character htwistActual
      _ = (data.normCharacterData mu).character *
          (data.twistData 1).character :=
        lowOddTwistCharacter_eq_norm_mul_base F K ht hres pi hpi hgen data j
      _ = powerData.character * (data.twistData 1).character :=
        congrArg (fun q : ContinuousQuasiChar F =>
          q * (data.twistData 1).character)
            (congrArg LocalQuasiCharData.character hpowerActual).symm
  have hmTwist : twist.conductor =
      2 * lowCriticalFloorDepth t + 1 := by
    rw [show twist.conductor = t + 1 by
      simpa only [twist] using lowNonzeroTwistDatum_conductor F K ht hres
        pi hpi hgen (data.twistData 1) hminimal hLow
          (j : ZMod (Module.finrank F K)) j.property]
    simpa only [hparity] using hCrit.conductor_eq
  have hmPower : powerData.conductor =
      2 * lowCriticalFloorDepth t + 1 := by
    simp only [powerData, quasiCharDataOfIsConductor_conductor]
    simpa only [hparity] using hCrit.conductor_eq
  have hlargeTwist : 1 < twist.conductor := by
    rw [hmTwist]
    have hEq := hCrit.conductor_eq
    rw [hparity] at hEq
    omega
  have hlargePower : 1 < powerData.conductor := by
    rw [hmPower]
    have hEq := hCrit.conductor_eq
    rw [hparity] at hEq
    omega
  have hgammaTwist : ord F (delta : F) =
      (((twist.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    rw [show twist.conductor = t + 1 by
      simpa only [twist] using lowNonzeroTwistDatum_conductor F K ht hres
        pi hpi hgen (data.twistData 1) hminimal hLow
          (j : ZMod (Module.finrank F K)) j.property]
    exact hdelta
  have hgammaPower : ord F (delta : F) =
      (((powerData.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    simpa only [powerData, quasiCharDataOfIsConductor_conductor] using hdelta
  let source := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hsource : ord F (source : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  apply criticalPolarFunction_eq_of_linearized_factor twist powerData
    (data.twistData 1).character data.baseAddChar
      (lowCriticalFloorDepth t) hmTwist hmPower hlargeTwist hlargePower
      hchar delta hgammaTwist hgammaPower source hsource _ _
        ((lowEpsilon F K epsilon1 : F) * (P.beta : F))
  · change ((WTwist j).representative : F) = _
    rw [(WTwist j).representative_eq]
    rfl
  · intro Y
    have hlin := lowBase_linearization_on_lowCriticalCoordinate
      F K ht hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P
        hstrict hparity j Y
    simpa only [twist, powerData, source, criticalPolarUnit] using hlin

/-- On the Low conductor boundary of odd critical parity, the actual twist
function is the product of the actual norm-row and base functions at their
common source coordinate. -/
theorem lowSourceTwistFunction_eq_norm_mul_base_of_boundary_of_odd
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hboundary : (data.twistData 1).conductor = t + 1)
    (hparity : lowCriticalParity t = 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j X =
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
          hdelta hT hgammaF P j X *
        lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table X := by
  have hd : d = lowCriticalFloorDepth t := by
    have hbase := hF.conductor_eq
    have hcrit := (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
    have he := hF.epsilon_le_one
    rw [hboundary] at hbase
    rw [hparity] at hcrit
    omega
  have hepsilon : epsilon = 1 := by
    have hbase := hF.conductor_eq
    have hcrit := (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
    have he := hF.epsilon_le_one
    rw [hboundary] at hbase
    rw [hparity] at hcrit
    omega
  subst epsilon
  subst d
  rw [lowSourceTwistFunction_eq_rawPolar F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WTwist hparity j X,
    lowSourceNormFunction_eq_rawPolar F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P hparity j X,
    lowSourceBaseFunction_eq_rawPolar F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table rfl X]
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  have htwistActual : twist = data.twistData mu := by
    rw [show twist = ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen (data.twistData 1) mu by
      simpa only [twist, mu] using
        (lowNonzeroTwistDatum_eq_actual F K ht hres pi hpi hgen
          (data.twistData 1) hminimal hLow
            (j : ZMod (Module.finrank F K)) j.property)]
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  have hmuPower : mu = tau ^ (j : ZMod (Module.finrank F K)).val := by
    dsimp only [mu, tau]
    exact lowNormCharacterGenerator_pow F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K))
  have hpowerActual : powerData = data.normCharacterData mu := by
    apply LocalQuasiCharData.ext_character F
    rw [quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
    exact congrArg (fun z : NormCharacter F K => z.1) hmuPower.symm
  have hchar : twist.character =
      powerData.character * (data.twistData 1).character := by
    calc
      twist.character = (data.twistData mu).character :=
        congrArg LocalQuasiCharData.character htwistActual
      _ = (data.normCharacterData mu).character *
          (data.twistData 1).character :=
        lowOddTwistCharacter_eq_norm_mul_base F K ht hres pi hpi hgen data j
      _ = powerData.character * (data.twistData 1).character :=
        congrArg (fun q : ContinuousQuasiChar F =>
          q * (data.twistData 1).character)
            (congrArg LocalQuasiCharData.character hpowerActual).symm
  have hmTwist : twist.conductor =
      2 * lowCriticalFloorDepth t + 1 := by
    rw [show twist.conductor = t + 1 by
      simpa only [twist] using lowNonzeroTwistDatum_conductor F K ht hres
        pi hpi hgen (data.twistData 1) hminimal hLow
          (j : ZMod (Module.finrank F K)) j.property]
    simpa only [hparity] using hCrit.conductor_eq
  have hmPower : powerData.conductor =
      2 * lowCriticalFloorDepth t + 1 := by
    simp only [powerData, quasiCharDataOfIsConductor_conductor]
    simpa only [hparity] using hCrit.conductor_eq
  have hmBase : (data.twistData 1).conductor =
      2 * lowCriticalFloorDepth t + 1 := hF.conductor_eq
  have hlargeTwist : 1 < twist.conductor := by
    rw [hmTwist]
    have hEq := hCrit.conductor_eq
    rw [hparity] at hEq
    omega
  have hlargePower : 1 < powerData.conductor := by
    rw [hmPower]
    have hEq := hCrit.conductor_eq
    rw [hparity] at hEq
    omega
  have hgammaTwist : ord F (delta : F) =
      (((twist.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    rw [show twist.conductor = t + 1 by
      simpa only [twist] using lowNonzeroTwistDatum_conductor F K ht hres
        pi hpi hgen (data.twistData 1) hminimal hLow
          (j : ZMod (Module.finrank F K)) j.property]
    exact hdelta
  have hgammaPower : ord F (delta : F) =
      (((powerData.conductor : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    simpa only [powerData, quasiCharDataOfIsConductor_conductor] using hdelta
  let source := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hsource : ord F (source : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  apply criticalPolarFunction_mul_of_literal_ratios twist powerData
    (data.twistData 1) data.baseAddChar (lowCriticalFloorDepth t) hmTwist
      hmPower hmBase hlargeTwist hlargePower hF.conductor_gt_one hchar delta
        delta (lowGammaF F K delta epsilon1) hgammaTwist hgammaPower hgammaF
          source hsource _ _ _
  change ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) / (delta : F) =
    ((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j : Fˣ) : F) / (delta : F) +
      (P.beta : F) / (lowGammaF F K delta epsilon1 : F)
  rw [lowOddTwistRepresentative_eq_norm_add_base F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table j (WTwist j)]
  simp only [lowGammaF, Units.val_div_eq_div_val]
  field_simp [Units.ne_zero delta, Units.ne_zero (lowEpsilon F K epsilon1)]

/-- At even parity the source supplies the unique coordinate-free
Lamprecht coordinate. -/
private theorem criticalCoordinateOfParity_zero
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (hparity : (0 : ℕ) ≤ 1) (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) (depth : ℕ) :
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        (d := depth) (epsilon := 0) hparity varpi hvarpi = .even := by
  unfold PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
  simp

/-- At even base conductor parity, the actual source-tied Low base function is
the manuscript's literal constant-one Lamprecht function. -/
theorem lowSourceBaseFunction_eq_one_of_even
    (hepsilon : epsilon = 0) (X : ResidueField F) :
    lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table X = 1 := by
  unfold lowSourceBaseFunction lowSourceBasePhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold lowBasePhase
  dsimp only
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hepsilon

/-- At even Low critical parity, the actual source-tied norm-row function is
the literal constant-one Lamprecht function. -/
theorem lowSourceNormFunction_eq_one_of_even
    (hparity : lowCriticalParity t = 0)
    (j : OddNormIndex F K) (X : ResidueField F) :
    lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j X = 1 := by
  unfold lowSourceNormFunction lowSourceNormPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddNormPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold lowNormCharacterPowerPhase
  dsimp only
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hparity

/-- At even Low critical parity, the actual source-tied twist-row function is
the literal constant-one Lamprecht function. -/
theorem lowSourceTwistFunction_eq_one_of_even
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hparity : lowCriticalParity t = 0)
    (j : OddNormIndex F K) (X : ResidueField F) :
    lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j X = 1 := by
  unfold lowSourceTwistFunction lowSourceTwistPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  dsimp only
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hparity

/-- On the Low conductor boundary, the actual twist function is the product
of the actual norm-row and base functions at their common source coordinate,
at either permitted critical parity. -/
theorem lowSourceTwistFunction_eq_norm_mul_base_of_boundary
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hboundary : (data.twistData 1).conductor = t + 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j X =
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
          hdelta hT hgammaF P j X *
        lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table X := by
  by_cases hzero : lowCriticalParity t = 0
  · have hepsilon : epsilon = 0 := by
      have hcrit := (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
      have hFcond := hF.conductor_eq
      have hle := hF.epsilon_le_one
      omega
    rw [lowSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WTwist hzero j X,
      lowSourceNormFunction_eq_one_of_even F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P hzero j X,
      lowSourceBaseFunction_eq_one_of_even F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table hepsilon X]
    simp
  · have hone : lowCriticalParity t = 1 := by
      have hle := (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
      omega
    exact lowSourceTwistFunction_eq_norm_mul_base_of_boundary_of_odd F K ht
      hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta
        epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WTwist hboundary
          hone j X

/-- In the strict Low range, the actual nonidentity twist and norm rows have
the same complete critical function at either permitted conductor parity. -/
theorem lowSourceTwistFunction_eq_norm_of_strict
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hstrict : (data.twistData 1).conductor < t + 1)
    (j : OddNormIndex F K) (X : ResidueField F) :
    lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j X =
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j X := by
  by_cases hzero : lowCriticalParity t = 0
  · rw [lowSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table WTwist hzero j X,
      lowSourceNormFunction_eq_one_of_even F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P hzero j X]
  · have hone : lowCriticalParity t = 1 := by
      have hle := (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
      omega
    exact lowSourceTwistFunction_eq_norm_of_strict_of_odd F K ht hres pi
      hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WTwist hstrict hone j X

/-- The actual low upstairs residual function, equipped with the polar
coefficient extracted from that same source-tied function. -/
noncomputable def lowSourceUpstairsCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :
    CriticalPolarFunction (ResidueField K) (C.upper hres)
      ((lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WUp).polarCoefficient
            (C.upper hres) (C.upper_ne_one hres)) :=
  (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table WUp).toCriticalPolarFunction
        (C.upper hres) (C.upper_ne_one hres)

@[simp] theorem lowSourceUpstairsCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) (x : ResidueField K) :
    lowSourceUpstairsCriticalPolarFunction F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table p C WUp x =
      lowSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WUp x := by
  exact LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _

/-- The actual low upstairs row displayed in the lower residue coordinate,
using the upper character and inverse-Frobenius reindexing derived from the
same lower residual character used by every low lower row. -/
noncomputable def lowSourceDisplayedUpstairsCriticalPolarFunction
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :=
  (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table WUp).displayedInLowerCoordinate p hchar hres C

@[simp]
theorem lowSourceDisplayedUpstairsCriticalPolarFunction_apply
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) (x : ResidueField F) :
    lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table p hchar C WUp x =
      lowSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WUp
            (PhaseReductionResidualCoordinateSource.residueEquiv hres
              ((C.frobeniusEquiv hchar).symm x)) :=
  LocalLamprechtPhaseData.displayedInLowerCoordinate_apply _ _ _ _ _ _

private theorem localPhaseOfStationaryClass_odd_apply_integral
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (y : E) (hy : y / (delta : E) ∈ lattice E 0) :
    let onePlusY : Eˣ :=
      (lamprechtHasseUnit E chi d h.conductor_eq h.conductor_gt_one delta
        hdelta (y / (delta : E)) hy : Eˣ)
    (onePlusY : E) = 1 + y ∧
      (localPhaseOfStationaryClass h Gamma R (.odd delta hdelta)).criticalFunction
          (reduce E (y / (delta : E)) hy) =
        (psi.character
          (((R.unit : Eˣ) : E) / ((Gamma : Eˣ) : E) * y) : ℂ) *
          (chi.character onePlusY : ℂ)⁻¹ := by
  simpa only [localPhaseOfStationaryClass,
    LocalLamprechtPhaseData.oddOfStationaryClass,
    lamprechtStationaryRepresentativeUnit_coe,
    StationaryClassRepresentative.toLamprecht,
    StationaryClassRepresentative.coe_unit] using
      LocalLamprechtPhaseData.odd_criticalFunction_integral_div_coordinate
        chi psi d h.conductor_eq h.conductor_gt_one Gamma delta hdelta
          R.toLamprecht
          (by
            simpa only [stationaryDepthOfConductorDecomposition] using
              R.toLamprecht_represents) y hy

private theorem criticalCoordinateOfParity_eq_cast_odd
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d epsilon : ℕ} (hparity : epsilon = 1) (hepsilon : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        hepsilon varpi hvarpi =
      hparity.symm ▸
        LamprechtCriticalCoordinate.odd
          (phaseReductionSourceCoordinate E varpi d)
          (phaseReductionSourceCoordinate_order E varpi hvarpi d) := by
  subst epsilon
  simp [PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity]

private theorem localPhaseOfStationaryClass_cast_odd
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ} (hparity : epsilon = 1)
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
    let hOne : IsStationaryConductorDecomposition chi.conductor d 1 :=
      hparity ▸ h
    let ROne : StationaryClassRepresentative E chi psi hOne
        (Gamma : Eˣ) Gamma.property := hparity ▸ R
    localPhaseOfStationaryClass h Gamma R
        (hparity.symm ▸ LamprechtCriticalCoordinate.odd delta hdelta) =
      localPhaseOfStationaryClass hOne Gamma ROne
        (LamprechtCriticalCoordinate.odd delta hdelta) := by
  subst epsilon
  rfl

theorem phaseReductionUpperSourceDisplacement_div_mem
    (z : ResidueField F) :
    phaseReductionUpperSourceDisplacement F K pi d z /
        (phaseReductionSourceCoordinate K
          (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
            d : K) ∈ lattice K 0 := by
  unfold phaseReductionUpperSourceDisplacement
  simp only [phaseReductionSourceCoordinate_coe]
  rw [show
    ((phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer : K) =
      (pi : K) by rfl]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero d hpi.ne_zero)]
  exact (mem_lattice_zero_iff K).2
    (algebraMap (ringOfIntegers F) (ringOfIntegers K)
      (teichmuller F z)).property

theorem phaseReductionUpperSourceDisplacement_reduces
    (z : ResidueField F) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let sourceDelta := phaseReductionSourceCoordinate K S.upperUniformizer d
    let x := phaseReductionUpperSourceDisplacement F K pi d z
    let hx : x / (sourceDelta : K) ∈ lattice K 0 := by
      unfold x sourceDelta S phaseReductionUpperSourceDisplacement
        phaseReductionResidualCoordinateSource
      simp only [phaseReductionSourceCoordinate_coe,
        phaseReductionUpperUniformizer_coe]
      rw [mul_div_cancel_right₀ _
        (pow_ne_zero d hpi.ne_zero)]
      exact (mem_lattice_zero_iff K).2
        (algebraMap (ringOfIntegers F) (ringOfIntegers K)
          (teichmuller F z)).property
    reduce K (x / (sourceDelta : K)) hx =
      PhaseReductionResidualCoordinateSource.residueEquiv hres z := by
  dsimp only
  let a : K := algebraMap F K (teichmuller F z : F)
  have ha : a ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)
        (teichmuller F z)).property
  have hxEq :
      phaseReductionUpperSourceDisplacement F K pi d z /
          (phaseReductionSourceCoordinate K
            (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
              d : K) = a := by
    unfold phaseReductionUpperSourceDisplacement a
    simp only [phaseReductionSourceCoordinate_coe]
    rw [show
      ((phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer : K) =
        (pi : K) by rfl]
    exact mul_div_cancel_right₀ _ (pow_ne_zero d hpi.ne_zero)
  have hx0 :
      phaseReductionUpperSourceDisplacement F K pi d z /
          (phaseReductionSourceCoordinate K
            (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
              d : K) ∈ lattice K 0 := by
    rw [hxEq]
    exact ha
  change reduce K
      (phaseReductionUpperSourceDisplacement F K pi d z /
        (phaseReductionSourceCoordinate K
          (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
            d : K)) hx0 = _
  have hsame : reduce K
        (phaseReductionUpperSourceDisplacement F K pi d z /
          (phaseReductionSourceCoordinate K
            (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
              d : K)) hx0 = reduce K a ha := by
    apply (reduce_eq_reduce_iff (F := K) hx0 ha).2
    rw [congruentAtDepth_iff_sub_mem_lattice, hxEq, sub_self]
    exact zero_mem _
  rw [hsame]
  unfold reduce
  rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
  unfold a
  change residueMap K
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)
        (teichmuller F z)) =
    extensionResidueMap F K z
  calc
    _ = extensionResidueMap F K (residueMap F (teichmuller F z)) :=
      (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation F) (ValuativeRel.valuation K)
          (teichmuller F z)).symm
    _ = _ := congrArg (extensionResidueMap F K)
      (residueMap_teichmuller F z)

theorem lowSourceDisplayedUpstairsFunction_displacement_apply_eq_raw
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (pResid : ℕ) (hchar : residueCharacteristic F = pResid)
    (C : FrobeniusResidualAddCharData F pResid)
    (X : ResidueField F) :
    let z := (C.frobeniusEquiv hchar).symm X
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let sourceDelta := phaseReductionSourceCoordinate K S.upperUniformizer d
    let x := phaseReductionUpperSourceDisplacement F K pi d z
    let hx : x / (sourceDelta : K) ∈ lattice K 0 :=
      phaseReductionUpperSourceDisplacement_div_mem F K hres pi hpi z
    let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
      (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
    let upperUnit : Kˣ :=
      (lamprechtHasseUnit K chiK d (by simpa [hepsilon] using
          hSource.conductor_eq) hSource.conductor_gt_one sourceDelta
        (phaseReductionSourceCoordinate_order K S.upperUniformizer
          S.upper_order d) (x / (sourceDelta : K)) hx : Kˣ)
    lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table pResid hchar C WUp X =
      (psiK.character
        ((((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WUp : Kˣ) : K) /
          (lowGammaK F K delta epsilon1 : K)) * x) : ℂ) *
        (chiK.character upperUnit : ℂ)⁻¹ := by
  subst epsilon
  dsimp only
  let z := (C.frobeniusEquiv hchar).symm X
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let sourceDelta := phaseReductionSourceCoordinate K S.upperUniformizer d
  let x := phaseReductionUpperSourceDisplacement F K pi d z
  have hx : x / (sourceDelta : K) ∈ lattice K 0 :=
    phaseReductionUpperSourceDisplacement_div_mem F K hres pi hpi z
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon1, hgammaK⟩
  let R : StationaryClassRepresentative K chiK psiK hSource
      (Gamma : Kˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative
      WUp.representative (by
        simpa only [hSource, Gamma] using WUp.represents)
  have hraw := localPhaseOfStationaryClass_odd_apply_integral hSource Gamma R
    sourceDelta
      (phaseReductionSourceCoordinate_order K S.upperUniformizer
        S.upper_order d) x hx
  have hchiData : chiK.character = data.extensionQuasiChar.character := by
    rw [data.extensionQuasiChar_character, hchi,
      data.twistData_character]
    exact normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi
  have hpsiData : psiK.character = data.extensionAddChar.character := by
    rw [data.extensionAddChar_character, hpsi,
      data.baseAddChar_character]
    rfl
  have htransport := transportLocalLamprechtPhaseData_criticalFunction
    hchiData hpsiData
      (lowOddUpstairsPhaseFromWitness F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp
            (.odd sourceDelta
              (phaseReductionSourceCoordinate_order K S.upperUniformizer
                S.upper_order d)))
  rw [lowSourceDisplayedUpstairsCriticalPolarFunction_apply]
  unfold lowSourceUpstairsFunction lowSourceUpstairsPhase
    LocalLamprechtPhaseData.sourceTiedRow
    lowOddUpstairsPhaseForComputationalData
  rw [show
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        hF.epsilon_le_one S.upperUniformizer S.upper_order =
      LamprechtCriticalCoordinate.odd sourceDelta
        (phaseReductionSourceCoordinate_order K S.upperUniformizer
          S.upper_order d) by
    simp [PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity,
      sourceDelta]]
  rw [congrFun htransport
    (PhaseReductionResidualCoordinateSource.residueEquiv hres z)]
  rw [← phaseReductionUpperSourceDisplacement_reduces
    F K hres pi hpi z]
  simpa only [lowOddUpstairsPhaseFromWitness,
    lowOddUpstairsRepresentativeUnit, R, Gamma, hSource,
    StationaryClassRepresentative.ofCoefficientRepresentative,
    StationaryClassRepresentative.coe_unit,
    sourceDelta, S, x, z] using hraw.2

theorem lowSourceBaseFunction_apply_eq_raw
    (hepsilon : epsilon = 1)
    (y : F) (hy : y ∈ lattice F (d : ℤ))
    (baseUnit : Fˣ) (hBaseUnit : (baseUnit : F) = 1 + y) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let sourceDelta := phaseReductionSourceCoordinate F S.lowerUniformizer d
    let hyDiv : y / (sourceDelta : F) ∈ lattice F 0 :=
      (div_mem_lattice_iff F (sourceDelta : F) y (d : ℤ) 0 (by
        rw [phaseReductionSourceCoordinate_order F S.lowerUniformizer
          S.lower_order d])).2 (by simpa using hy)
    lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table (reduce F (y / (sourceDelta : F)) hyDiv) =
      (data.baseAddChar.character
        (((P.beta : F) / (lowGammaF F K delta epsilon1 : F)) * y) : ℂ) *
        ((data.twistData 1).character baseUnit : ℂ)⁻¹ := by
  subst epsilon
  dsimp only
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let sourceDelta := phaseReductionSourceCoordinate F S.lowerUniformizer d
  have hSourceDelta := phaseReductionSourceCoordinate_order F
    S.lowerUniformizer S.lower_order d
  have hyDiv : y / (sourceDelta : F) ∈ lattice F 0 :=
    (div_mem_lattice_iff F (sourceDelta : F) y (d : ℤ) 0 (by
      rw [hSourceDelta])).2 (by simpa using hy)
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨lowGammaF F K delta epsilon1, hgammaF⟩
  let R : StationaryClassRepresentative F (data.twistData 1)
      data.baseAddChar hF (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
      represents := by simpa only [Gamma] using table.beta_native_class }
  have hraw := localPhaseOfStationaryClass_odd_apply_integral hF Gamma R
    sourceDelta hSourceDelta y hyDiv
  let actualUnit : Fˣ :=
    (lamprechtHasseUnit F (data.twistData 1) d hF.conductor_eq
      hF.conductor_gt_one sourceDelta hSourceDelta
        (y / (sourceDelta : F)) hyDiv : Fˣ)
  have hActualUnit : (actualUnit : F) = 1 + y := hraw.1
  have hunit : actualUnit = baseUnit := by
    apply Units.ext
    exact hActualUnit.trans hBaseUnit.symm
  unfold lowSourceBaseFunction lowSourceBasePhase
    LocalLamprechtPhaseData.sourceTiedRow lowBasePhase
  rw [show
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        hF.epsilon_le_one S.lowerUniformizer S.lower_order =
      LamprechtCriticalCoordinate.odd sourceDelta hSourceDelta by
    simp [PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity,
      sourceDelta]]
  rw [← hunit]
  simpa only [R, Gamma, actualUnit,
    StationaryClassRepresentative.coe_unit,
    Units.val_div_eq_div_val, mul_assoc] using hraw.2

theorem lowTauRaw_eq_one
    (x : K) (upperUxUnit : Kˣ)
    (hUpperUxUnit : (upperUxUnit : K) =
      1 + lowNormalizedRatio F K epsilon1 P * x)
    (hPux : phaseReductionNormPolynomial F K
        (lowNormalizedRatio F K epsilon1 P * x) ∈
      lattice F ((lowCriticalFloorDepth t + lowCriticalParity t : ℕ) : ℤ)) :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    (data.baseAddChar.character
          (((P.alpha : F) / (delta : F)) *
            phaseReductionNormPolynomial F K
              (lowNormalizedRatio F K epsilon1 P * x)) : ℂ) *
        (tau.1 (normUnits F K upperUxUnit) : ℂ)⁻¹ = 1 := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
      (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨delta, by simpa only [tauData, quasiCharDataOfIsConductor_conductor]
      using hdelta⟩
  let R : StationaryClassRepresentative F tauData data.baseAddChar hCrit
      (Gamma : Fˣ) Gamma.property :=
    { representative :=
        ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
      represents := by
        simpa only [tauData, hCrit, Gamma] using P.alpha_norm_class }
  have hNormUnit : ((normUnits F K upperUxUnit : Fˣ) : F) =
      1 + phaseReductionNormPolynomial F K
        (lowNormalizedRatio F K epsilon1 P * x) := by
    rw [coe_normUnits, hUpperUxUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  have hraw := stationaryRawFactor_eq_one (h := hCrit) delta
    (by simpa only [tauData, Gamma,
      quasiCharDataOfIsConductor_conductor] using hdelta) R
      (phaseReductionNormPolynomial F K
        (lowNormalizedRatio F K epsilon1 P * x)) hPux
      (normUnits F K upperUxUnit) hNormUnit
  simpa only [R, Gamma, tauData, quasiCharDataOfIsConductor_character,
    StationaryClassRepresentative.coe_unit, div_mul_eq_mul_div] using hraw

include ht hres hpi hgen in
theorem phaseReductionLowStrictTauPolynomial_stationaryLayer
    (htpos : 0 < t) (hstrictDepth : 2 * d < t)
    (a : ℕ) (ha : a + 2 * d = t)
    (u : K) (hu : ord K u = ((a : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    normPolynomialValue F K
        (u * phaseReductionUpperSourceDisplacement F K pi d z) ∈
      lattice F ((lowCriticalFloorDepth t + lowCriticalParity t : ℕ) : ℤ) := by
  let q := a + d
  have hq : q ≤ t + 1 := by dsimp only [q]; omega
  have hqLayer : lowCriticalFloorDepth t + lowCriticalParity t ≤ q := by
    have hc := lowCriticalConductor_eq (t := t)
    have heps := lowCriticalParity_le_one (t := t)
    dsimp only [q]
    omega
  have hx : ((q : ℕ) : WithTop ℤ) ≤
      ord K (u * phaseReductionUpperSourceDisplacement F K pi d z) := by
    rw [ord_mul, hu]
    have hz := phaseReductionUpperSourceDisplacement_mem F K pi hpi d z
    rw [mem_lattice] at hz
    change (((a + d : ℕ) : ℤ) : WithTop ℤ) ≤ _
    simpa only [Nat.cast_add, WithTop.coe_add, add_comm] using
      add_le_add_left hz ((a : ℤ) : WithTop ℤ)
  have hchar := residueCharacteristic_eq_degree_of_positive_break
    F K ht htpos pi hpi hgen
  have hP := wild_norm_one_add_sub_one_mem_lattice F K ht htpos hq hres
    hchar pi hpi hgen _ hx
  apply lattice_antitone F (m :=
    ((lowCriticalFloorDepth t + lowCriticalParity t : ℕ) : ℤ))
      (n := (q : ℤ))
  · exact_mod_cast hqLayer
  · exact hP

theorem lowSourceDisplayed_exactCriticalTransport_strict
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hstrict : (data.twistData 1).conductor < t + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F)
    (upperUxUnit : Kˣ)
    (hUpperUxUnit :
      let hchar : residueCharacteristic F = Module.finrank F K :=
        residueCharacteristic_eq_degree_of_positive_break F K ht
          (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
      let z := (C.frobeniusEquiv hchar).symm X
      let x := phaseReductionUpperSourceDisplacement F K pi d z
      let u := lowNormalizedRatio F K epsilon1 P
      (upperUxUnit : K) = 1 + u * x) :
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_break F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    let z := (C.frobeniusEquiv hchar).symm X
    let x := phaseReductionUpperSourceDisplacement F K pi d z
    let A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
    let u := lowNormalizedRatio F K epsilon1 P
    let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
    let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
    lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K) hchar C
            WUp X =
      lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table X *
        (lowSourceNormFunction F K ht hres pi hpi hgen data hF delta
          epsilon1 hdelta hT hgammaF P jOne 0)⁻¹ *
        (data.baseAddChar.character
          (A * (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x)) : ℂ) := by
  dsimp only at hUpperUxUnit ⊢
  have htpos : 0 < t := by omega
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  let z := (C.frobeniusEquiv hchar).symm X
  let x := phaseReductionUpperSourceDisplacement F K pi d z
  let A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
  let u := lowNormalizedRatio F K epsilon1 P
  let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let sourceDelta := phaseReductionSourceCoordinate K S.upperUniformizer d
  have hxDiv : x / (sourceDelta : K) ∈ lattice K 0 :=
    phaseReductionUpperSourceDisplacement_div_mem F K hres pi hpi z
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let upperUnit : Kˣ :=
    (lamprechtHasseUnit K chiK d (by simpa [hepsilon] using
        hSource.conductor_eq) hSource.conductor_gt_one sourceDelta
      (phaseReductionSourceCoordinate_order K S.upperUniformizer
        S.upper_order d) (x / (sourceDelta : K)) hxDiv : Kˣ)
  have hUpperUnit : (upperUnit : K) = 1 + x := by
    dsimp only [upperUnit]
    rw [lamprechtHasseUnit_coe]
    field_simp [Units.ne_zero sourceDelta]
  have hraw := lowOdd_actualStationaryRatios_exactCriticalTransport
    F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp x
        upperUnit upperUxUnit hUpperUnit hUpperUxUnit
  let baseRaw : ℂ :=
    (data.baseAddChar.character
      (((P.beta : F) / (lowGammaF F K delta epsilon1 : F)) *
        phaseReductionNormPolynomial F K x) : ℂ) *
      ((data.twistData 1).character (normUnits F K upperUnit) : ℂ)⁻¹
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let tauRaw : ℂ :=
    (data.baseAddChar.character
      (((P.alpha : F) / (delta : F)) *
        phaseReductionNormPolynomial F K (u * x)) : ℂ) *
      (tau.1 (normUnits F K upperUxUnit) : ℂ)⁻¹
  let upperRatio : K :=
    ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WUp : Kˣ) : K) /
      (lowGammaK F K delta epsilon1 : K)
  let upperRaw : ℂ :=
    (psiK.character (upperRatio * x) : ℂ) *
      (chiK.character upperUnit : ℂ)⁻¹
  let correction : ℂ :=
    (data.baseAddChar.character
      (A * (phaseReductionNormHigherPart F K (u * x) -
        n * phaseReductionNormHigherPart F K x)) : ℂ)
  have hraw' : baseRaw * tauRaw⁻¹ * correction = upperRaw := by
    have hrawC := congrArg (Units.val : ℂˣ → ℂ) hraw
    push_cast at hrawC
    dsimp only [baseRaw, tauRaw, upperRaw, correction, upperRatio, tau,
      A, u, n]
    simpa only using hrawC
  have hdisplay :
      lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi
          hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
            hdelta hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K)
              hchar C WUp X = upperRaw := by
    exact lowSourceDisplayedUpstairsFunction_displacement_apply_eq_raw
      F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow
        delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp
          hepsilon (Module.finrank F K) hchar C X
  have hxDepth : x ∈ lattice K (d : ℤ) := by
    simpa only [x] using
      phaseReductionUpperSourceDisplacement_mem F K pi hpi d z
  have hPx : phaseReductionNormPolynomial F K x ∈ lattice F (d : ℤ) := by
    change norm F K (1 + x) - 1 ∈ lattice F (d : ℤ)
    exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos (by
      have hdle := (lowConductor_subcriticalDepths (t := t) hF hLow).2
      omega) hres hchar pi hpi hgen x (by
        change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x
        simpa only [mem_lattice] using hxDepth)
  let baseUnit := normUnits F K upperUnit
  have hBaseUnit : (baseUnit : F) =
      1 + phaseReductionNormPolynomial F K x := by
    rw [show (baseUnit : F) = norm F K (upperUnit : K) by rfl,
      hUpperUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  have hbaseEval := lowSourceBaseFunction_apply_eq_raw F K ht hres pi hpi
    hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table hepsilon
        (phaseReductionNormPolynomial F K x) hPx baseUnit hBaseUnit
  let yBase : lattice F (d : ℤ) :=
    ⟨phaseReductionNormPolynomial F K x, hPx⟩
  have hbaseClass : phaseReductionResidualClass F S.lowerUniformizer
      S.lower_order d yBase = X := by
    have hclass := phaseReductionLowBaseResidualClass (t := t) (d := d)
      F K ht htpos
      (by have hm := hF.conductor_eq; rw [hepsilon] at hm; omega) hres pi hpi
        hgen z
    have hzpow : z ^ Module.finrank F K = X := by
      rw [← C.frobeniusEquiv_apply hchar z]
      exact (C.frobeniusEquiv hchar).apply_symm_apply X
    have hclass' : phaseReductionResidualClass F S.lowerUniformizer
        S.lower_order d yBase = z ^ Module.finrank F K := by
      change phaseReductionResidualClass F
        (phaseReductionLowerUniformizer F K pi hpi)
        (phaseReductionLowerUniformizer_order F K hres pi hpi) d yBase = _
      simpa only [yBase, x,
        phaseReductionNormPolynomial_eq_normPolynomialValue] using hclass
    exact hclass'.trans hzpow
  have hbase :
      lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table X = baseRaw := by
    have hyDiv : phaseReductionNormPolynomial F K x /
        (phaseReductionSourceCoordinate F S.lowerUniformizer d : F) ∈
          lattice F 0 :=
      (div_mem_lattice_iff F
        (phaseReductionSourceCoordinate F S.lowerUniformizer d : F)
        (phaseReductionNormPolynomial F K x) (d : ℤ) 0 (by
          rw [phaseReductionSourceCoordinate_order F S.lowerUniformizer
            S.lower_order d])).2 (by simpa using hPx)
    have hreduce :
        reduce F
          (phaseReductionNormPolynomial F K x /
            (phaseReductionSourceCoordinate F S.lowerUniformizer d : F))
              hyDiv =
          X := by
      change phaseReductionResidualClass F S.lowerUniformizer S.lower_order d
        yBase = X
      exact hbaseClass
    have hreduceAll (hp : phaseReductionNormPolynomial F K x /
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            d : F) ∈ lattice F 0) :
        reduce F
          (phaseReductionNormPolynomial F K x /
            (phaseReductionSourceCoordinate F
              (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
                d : F)) hp = X := by
      simpa only [S] using hreduce
    dsimp only at hbaseEval
    simpa only [hreduceAll, baseRaw, baseUnit] using hbaseEval
  let a := t + 1 - (data.twistData 1).conductor
  have ha : a + 2 * d = t := by
    have hm := hF.conductor_eq
    rw [hepsilon] at hm
    dsimp only [a]
    omega
  have hu : ord K u = ((a : ℤ) : WithTop ℤ) := by
    dsimp only [u, a]
    convert lowNormalizedRatio_order F K epsilon1 hepsilon1 P using 1 <;>
      norm_num
  have hPux : phaseReductionNormPolynomial F K (u * x) ∈
      lattice F ((lowCriticalFloorDepth t + lowCriticalParity t : ℕ) : ℤ) := by
    simpa only [phaseReductionNormPolynomial_eq_normPolynomialValue, u, x]
      using phaseReductionLowStrictTauPolynomial_stationaryLayer
        F K ht hres pi hpi hgen htpos
          (by have hm := hF.conductor_eq; rw [hepsilon] at hm; omega)
          a ha (lowNormalizedRatio F K epsilon1 P) hu z
  have htau : tauRaw = 1 := by
    exact lowTauRaw_eq_one F K ht hres pi hpi hgen data hF delta epsilon1
      hdelta hT hgammaF P x upperUxUnit hUpperUxUnit hPux
  let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
  have hnormZero :
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P jOne 0 = 1 :=
    LocalLamprechtPhaseData.criticalFunction_zero
      (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P jOne)
  rw [hdisplay, ← hraw', ← hbase, htau, hnormZero]

theorem localPhaseOfStationaryClass_source_odd_apply_integral
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hparity : epsilon = 1)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (y : E)
    (hy : y /
      (phaseReductionSourceCoordinate E varpi d : E) ∈ lattice E 0)
    (unit : Eˣ) (hunit : (unit : E) = 1 + y) :
    (localPhaseOfStationaryClass h Gamma R
      (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        h.epsilon_le_one varpi hvarpi)).criticalFunction
          (reduce E
            (y / (phaseReductionSourceCoordinate E varpi d : E)) hy) =
      (psi.character
        (((R.unit : Eˣ) : E) / ((Gamma : Eˣ) : E) * y) : ℂ) *
        (chi.character unit : ℂ)⁻¹ := by
  subst epsilon
  have hraw := localPhaseOfStationaryClass_odd_apply_integral h Gamma R
    (phaseReductionSourceCoordinate E varpi d)
      (phaseReductionSourceCoordinate_order E varpi hvarpi d) y hy
  let actualUnit : Eˣ :=
    (lamprechtHasseUnit E chi d h.conductor_eq h.conductor_gt_one
      (phaseReductionSourceCoordinate E varpi d)
        (phaseReductionSourceCoordinate_order E varpi hvarpi d)
          (y / (phaseReductionSourceCoordinate E varpi d : E)) hy : Eˣ)
  have hactual : actualUnit = unit := by
    apply Units.ext
    exact hraw.1.trans hunit.symm
  rw [show
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        h.epsilon_le_one varpi hvarpi =
      LamprechtCriticalCoordinate.odd
        (phaseReductionSourceCoordinate E varpi d)
        (phaseReductionSourceCoordinate_order E varpi hvarpi d) by
      simp [PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity]]
  rw [← hactual]
  simpa only [actualUnit] using hraw.2

theorem lowSourceNormFunction_one_apply_eq_raw
    (hoddT : Odd (t + 1))
    (y : F) (hy : y ∈ lattice F (lowCriticalFloorDepth t : ℤ))
    (normUnit : Fˣ) (hNormUnit : (normUnit : F) = 1 + y) :
    let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let dTau := lowCriticalFloorDepth t
    let sourceDelta := phaseReductionSourceCoordinate F S.lowerUniformizer dTau
    let hyDiv : y / (sourceDelta : F) ∈ lattice F 0 :=
      (div_mem_lattice_iff F (sourceDelta : F) y (dTau : ℤ) 0 (by
        rw [phaseReductionSourceCoordinate_order F S.lowerUniformizer
          S.lower_order dTau])).2 (by simpa using hy)
    lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P jOne
          (reduce F (y / (sourceDelta : F)) hyDiv) =
      (data.baseAddChar.character
        (((P.alpha : F) / (delta : F)) * y) : ℂ) *
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen).1 normUnit : ℂ)⁻¹ := by
  dsimp only
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let dTau := lowCriticalFloorDepth t
  let sourceDelta := phaseReductionSourceCoordinate F S.lowerUniformizer dTau
  have hSourceDelta := phaseReductionSourceCoordinate_order F
    S.lowerUniformizer S.lower_order dTau
  have hyDiv : y / (sourceDelta : F) ∈ lattice F 0 :=
    (div_mem_lattice_iff F (sourceDelta : F) y (dTau : ℤ) 0 (by
      rw [hSourceDelta])).2 (by simpa only [dTau, add_zero] using hy)
  have hparity : lowCriticalParity t = 1 := by
    obtain ⟨k, hk⟩ := hoddT
    unfold lowCriticalParity
    omega
  rw [lowSourceNormFunction_eq_powerPhase]
  unfold lowNormCharacterPowerPhase
  dsimp only
  simp only [id_eq]
  rw [localPhaseOfStationaryClass_source_odd_apply_integral
    (hparity := hparity) (unit := normUnit) (hunit := hNormUnit)]
  letI : Fact (1 < Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).one_lt⟩
  have hval : ZMod.val (1 : ZMod (Module.finrank F K)) = 1 :=
    ZMod.val_one (Module.finrank F K)
  have homegaROI :
      primeTeichmuller F (Module.finrank F K)
          (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
            (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
          (1 : ZMod (Module.finrank F K)) = 1 :=
    map_one (primeTeichmuller F (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen))
  have homega :
      ((primeTeichmuller F (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
          (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
          (1 : ZMod (Module.finrank F K)) : ringOfIntegers F) : F) = 1 :=
    congrArg (fun z : ringOfIntegers F => (z : F)) homegaROI
  simp only [StationaryClassRepresentative.coe_unit,
    StationaryClassRepresentative.ofCoefficientRepresentative,
    Units.val_div_eq_div_val, homega, one_mul,
    quasiCharDataOfIsConductor_character]
  rw [hval, pow_one]

include ht hgen in
theorem phaseReductionLowBoundaryTauResidualClass
    (htpos : 0 < t) (hd : d < t)
    (u : Kˣ) (hu : ord K (u : K) = (0 : WithTop ℤ))
    (z : ResidueField F)
    (hy : phaseReductionNormPolynomial F K
      ((u : K) * phaseReductionUpperSourceDisplacement F K pi d z) ∈
        lattice F (d : ℤ)) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let nO : ringOfIntegers F :=
      ⟨norm F K (u : K), by
        rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
          one_nsmul, hu]
        exact le_rfl⟩
    let y : lattice F (d : ℤ) :=
      ⟨phaseReductionNormPolynomial F K
        ((u : K) * phaseReductionUpperSourceDisplacement F K pi d z), hy⟩
    phaseReductionResidualClass F S.lowerUniformizer S.lower_order d y =
      residueMap F nO * z ^ Module.finrank F K := by
  dsimp only
  apply phaseReductionResidualClass_eq_source_of_sub_mem F
    (phaseReductionLowerUniformizer F K pi hpi)
    (phaseReductionLowerUniformizer_order F K hres pi hpi) d
    (residueMap F
      (⟨norm F K (u : K), by
        rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
          one_nsmul, hu]
        exact le_rfl⟩ : ringOfIntegers F) *
      z ^ Module.finrank F K)
  simpa only [phaseReductionNormPolynomial_eq_normPolynomialValue,
    phaseReductionLowerUniformizer_coe] using
      phaseReductionLowBoundaryTauPolynomial_congruent F K ht htpos hd hres
        pi hpi hgen u hu z

theorem lowSourceDisplayed_exactCriticalTransport_boundary
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = t + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F)
    (upperUxUnit : Kˣ)
    (hUpperUxUnit :
      let hchar : residueCharacteristic F = Module.finrank F K :=
        residueCharacteristic_eq_degree_of_positive_break F K ht
          (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
      let z := (C.frobeniusEquiv hchar).symm X
      let x := phaseReductionUpperSourceDisplacement F K pi d z
      let u := lowNormalizedRatio F K epsilon1 P
      (upperUxUnit : K) = 1 + u * x) :
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_break F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    let z := (C.frobeniusEquiv hchar).symm X
    let x := phaseReductionUpperSourceDisplacement F K pi d z
    let A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
    let u := lowNormalizedRatio F K epsilon1 P
    let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
    let hu : ord K u = (0 : WithTop ℤ) := by
      simpa only [hboundary, Nat.sub_self, Nat.cast_zero, WithTop.coe_zero]
        using lowNormalizedRatio_order F K epsilon1 hepsilon1 P
    let nO : ringOfIntegers F :=
      ⟨norm F K u, by
        rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
          one_nsmul, hu]
        exact le_rfl⟩
    let tauX := residueMap F nO * X
    let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
    lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K) hchar C
            WUp X =
      lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table X *
        (lowSourceNormFunction F K ht hres pi hpi hgen data hF delta
          epsilon1 hdelta hT hgammaF P jOne tauX)⁻¹ *
        (data.baseAddChar.character
          (A * (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x)) : ℂ) := by
  dsimp only at hUpperUxUnit ⊢
  have htEq : t = 2 * d := by
    have hm := hF.conductor_eq
    rw [hepsilon, hboundary] at hm
    omega
  have htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    rw [hboundary] at hm
    omega
  have hd : d < t := by omega
  have hoddT : Odd (t + 1) := by
    refine ⟨d, ?_⟩
    omega
  have hdFloor : lowCriticalFloorDepth t = d := by
    simp only [lowCriticalFloorDepth, htEq]
    omega
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  let z := (C.frobeniusEquiv hchar).symm X
  let x := phaseReductionUpperSourceDisplacement F K pi d z
  let A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
  let u := lowNormalizedRatio F K epsilon1 P
  let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  have hu : ord K u = (0 : WithTop ℤ) := by
    dsimp only [u]
    simpa only [hboundary, Nat.sub_self, Nat.cast_zero, WithTop.coe_zero]
      using lowNormalizedRatio_order F K epsilon1 hepsilon1 P
  let uUnit : Kˣ := Units.mk0 u (by
    apply (ord_ne_top_iff K).1
    rw [hu]
    exact WithTop.coe_ne_top)
  let nO : ringOfIntegers F :=
    ⟨norm F K u, by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
        one_nsmul, hu]
      exact le_rfl⟩
  let tauX := residueMap F nO * X
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let sourceDelta := phaseReductionSourceCoordinate K S.upperUniformizer d
  have hxDiv : x / (sourceDelta : K) ∈ lattice K 0 :=
    phaseReductionUpperSourceDisplacement_div_mem F K hres pi hpi z
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let upperUnit : Kˣ :=
    (lamprechtHasseUnit K chiK d (by simpa [hepsilon] using
        hSource.conductor_eq) hSource.conductor_gt_one sourceDelta
      (phaseReductionSourceCoordinate_order K S.upperUniformizer
        S.upper_order d) (x / (sourceDelta : K)) hxDiv : Kˣ)
  have hUpperUnit : (upperUnit : K) = 1 + x := by
    dsimp only [upperUnit]
    rw [lamprechtHasseUnit_coe]
    field_simp [Units.ne_zero sourceDelta]
  have hraw := lowOdd_actualStationaryRatios_exactCriticalTransport
    F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp x
        upperUnit upperUxUnit hUpperUnit hUpperUxUnit
  let baseRaw : ℂ :=
    (data.baseAddChar.character
      (((P.beta : F) / (lowGammaF F K delta epsilon1 : F)) *
        phaseReductionNormPolynomial F K x) : ℂ) *
      ((data.twistData 1).character (normUnits F K upperUnit) : ℂ)⁻¹
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let tauRaw : ℂ :=
    (data.baseAddChar.character
      (((P.alpha : F) / (delta : F)) *
        phaseReductionNormPolynomial F K (u * x)) : ℂ) *
      (tau.1 (normUnits F K upperUxUnit) : ℂ)⁻¹
  let upperRatio : K :=
    ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WUp : Kˣ) : K) /
      (lowGammaK F K delta epsilon1 : K)
  let upperRaw : ℂ :=
    (psiK.character (upperRatio * x) : ℂ) *
      (chiK.character upperUnit : ℂ)⁻¹
  let correction : ℂ :=
    (data.baseAddChar.character
      (A * (phaseReductionNormHigherPart F K (u * x) -
        n * phaseReductionNormHigherPart F K x)) : ℂ)
  have hraw' : baseRaw * tauRaw⁻¹ * correction = upperRaw := by
    have hrawC := congrArg (Units.val : ℂˣ → ℂ) hraw
    push_cast at hrawC
    dsimp only [baseRaw, tauRaw, upperRaw, correction, upperRatio, tau,
      A, u, n]
    simpa only using hrawC
  have hdisplay :
      lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi
          hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
            hdelta hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K)
              hchar C WUp X = upperRaw := by
    exact lowSourceDisplayedUpstairsFunction_displacement_apply_eq_raw
      F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow
        delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table WUp
          hepsilon (Module.finrank F K) hchar C X
  have hxDepth : x ∈ lattice K (d : ℤ) := by
    simpa only [x] using
      phaseReductionUpperSourceDisplacement_mem F K pi hpi d z
  have hPx : phaseReductionNormPolynomial F K x ∈ lattice F (d : ℤ) := by
    change norm F K (1 + x) - 1 ∈ lattice F (d : ℤ)
    exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos (by omega)
      hres hchar pi hpi hgen x (by
        change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x
        simpa only [mem_lattice] using hxDepth)
  let baseUnit := normUnits F K upperUnit
  have hBaseUnit : (baseUnit : F) =
      1 + phaseReductionNormPolynomial F K x := by
    rw [show (baseUnit : F) = norm F K (upperUnit : K) by rfl,
      hUpperUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  have hbaseEval := lowSourceBaseFunction_apply_eq_raw F K ht hres pi hpi
    hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table hepsilon
        (phaseReductionNormPolynomial F K x) hPx baseUnit hBaseUnit
  let yBase : lattice F (d : ℤ) :=
    ⟨phaseReductionNormPolynomial F K x, hPx⟩
  have hbaseClass : phaseReductionResidualClass F S.lowerUniformizer
      S.lower_order d yBase = X := by
    have hclass := phaseReductionLowBaseResidualClass (t := t) (d := d)
      F K ht htpos hd hres pi hpi hgen z
    have hzpow : z ^ Module.finrank F K = X := by
      rw [← C.frobeniusEquiv_apply hchar z]
      exact (C.frobeniusEquiv hchar).apply_symm_apply X
    have hclass' : phaseReductionResidualClass F S.lowerUniformizer
        S.lower_order d yBase = z ^ Module.finrank F K := by
      change phaseReductionResidualClass F
        (phaseReductionLowerUniformizer F K pi hpi)
        (phaseReductionLowerUniformizer_order F K hres pi hpi) d yBase = _
      simpa only [yBase, x,
        phaseReductionNormPolynomial_eq_normPolynomialValue] using hclass
    exact hclass'.trans hzpow
  have hbase :
      lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table X = baseRaw := by
    have hyDiv : phaseReductionNormPolynomial F K x /
        (phaseReductionSourceCoordinate F S.lowerUniformizer d : F) ∈
          lattice F 0 :=
      (div_mem_lattice_iff F
        (phaseReductionSourceCoordinate F S.lowerUniformizer d : F)
        (phaseReductionNormPolynomial F K x) (d : ℤ) 0 (by
          rw [phaseReductionSourceCoordinate_order F S.lowerUniformizer
            S.lower_order d])).2 (by simpa using hPx)
    have hreduce :
        reduce F
          (phaseReductionNormPolynomial F K x /
            (phaseReductionSourceCoordinate F S.lowerUniformizer d : F))
              hyDiv = X := by
      change phaseReductionResidualClass F S.lowerUniformizer S.lower_order d
        yBase = X
      exact hbaseClass
    have hreduceAll (hp : phaseReductionNormPolynomial F K x /
        (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            d : F) ∈ lattice F 0) :
        reduce F
          (phaseReductionNormPolynomial F K x /
            (phaseReductionSourceCoordinate F
              (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
                d : F)) hp = X := by
      simpa only [S] using hreduce
    dsimp only at hbaseEval
    simpa only [hreduceAll, baseRaw, baseUnit] using hbaseEval
  have huxDepth : u * x ∈ lattice K (d : ℤ) := by
    rw [mem_lattice, ord_mul, hu]
    simpa only [zero_add, mem_lattice] using hxDepth
  have hPux : phaseReductionNormPolynomial F K (u * x) ∈
      lattice F (d : ℤ) := by
    change norm F K (1 + u * x) - 1 ∈ lattice F (d : ℤ)
    exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos (by omega)
      hres hchar pi hpi hgen (u * x) (by
        change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K (u * x)
        simpa only [mem_lattice] using huxDepth)
  let tauUnit := normUnits F K upperUxUnit
  have hTauUnit : (tauUnit : F) =
      1 + phaseReductionNormPolynomial F K (u * x) := by
    rw [show (tauUnit : F) = norm F K (upperUxUnit : K) by rfl,
      hUpperUxUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  let yTau : lattice F (d : ℤ) :=
    ⟨phaseReductionNormPolynomial F K (u * x), hPux⟩
  have htauClass : phaseReductionResidualClass F S.lowerUniformizer
      S.lower_order d yTau = tauX := by
    have hclass := phaseReductionLowBoundaryTauResidualClass
      F K ht hres pi hpi hgen htpos hd uUnit
        (by simpa [uUnit] using hu) z
          (by simpa [uUnit] using hPux)
    have hzpow : z ^ Module.finrank F K = X := by
      rw [← C.frobeniusEquiv_apply hchar z]
      exact (C.frobeniusEquiv hchar).apply_symm_apply X
    have hclass' : phaseReductionResidualClass F S.lowerUniformizer
        S.lower_order d yTau = residueMap F nO *
          z ^ Module.finrank F K := by
      simpa [S, nO, yTau, uUnit, u, x] using hclass
    exact hclass'.trans (by simpa only [tauX, hzpow])
  have htauEval := lowSourceNormFunction_one_apply_eq_raw
    F K ht hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P
      hoddT (phaseReductionNormPolynomial F K (u * x))
        (by simpa only [hdFloor] using hPux) tauUnit hTauUnit
  have hyTauDiv : phaseReductionNormPolynomial F K (u * x) /
      (phaseReductionSourceCoordinate F S.lowerUniformizer d : F) ∈
        lattice F 0 :=
    (div_mem_lattice_iff F
      (phaseReductionSourceCoordinate F S.lowerUniformizer d : F)
      (phaseReductionNormPolynomial F K (u * x)) (d : ℤ) 0 (by
        rw [phaseReductionSourceCoordinate_order F S.lowerUniformizer
          S.lower_order d])).2 (by simpa using hPux)
  have hreduceTau :
      reduce F
        (phaseReductionNormPolynomial F K (u * x) /
          (phaseReductionSourceCoordinate F S.lowerUniformizer d : F))
            hyTauDiv = tauX := by
    change phaseReductionResidualClass F S.lowerUniformizer S.lower_order d
      yTau = tauX
    exact htauClass
  have hreduceTauAll (hp : phaseReductionNormPolynomial F K (u * x) /
      (phaseReductionSourceCoordinate F
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (lowCriticalFloorDepth t) : F) ∈ lattice F 0) :
      reduce F
        (phaseReductionNormPolynomial F K (u * x) /
          (phaseReductionSourceCoordinate F
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
              (lowCriticalFloorDepth t) : F)) hp = tauX := by
    simpa only [hdFloor, S] using hreduceTau
  let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
  have htau :
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
          hdelta hT hgammaF P jOne tauX = tauRaw := by
    dsimp only at htauEval
    simpa only [hreduceTauAll, tauRaw, tauUnit, tau, jOne] using htauEval
  rw [hdisplay, ← hraw', ← hbase, ← htau]

/-- At even base conductor parity, the actual Low upstairs function is the
manuscript's literal constant-one Lamprecht function. -/
theorem lowSourceUpstairsFunction_eq_one_of_even
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 0) (X : ResidueField K) :
    lowSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WUp X = 1 := by
  unfold lowSourceUpstairsFunction lowSourceUpstairsPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold lowOddUpstairsPhaseFromWitness
  dsimp only
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hepsilon

/-- At even base conductor parity, the same actual Low upstairs function is
constant one after the source-forced inverse-Frobenius display. -/
theorem lowSourceDisplayedUpstairsFunction_eq_one_of_even
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 0) (X : ResidueField F) :
    lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table p hchar C WUp X = 1 := by
  rw [lowSourceDisplayedUpstairsCriticalPolarFunction_apply]
  apply lowSourceUpstairsFunction_eq_one_of_even F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp hepsilon

/-- The actual low identity/base residual function, equipped with the polar
coefficient extracted from that same source-tied function. -/
noncomputable def lowSourceBaseCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p) :
    CriticalPolarFunction (ResidueField F) C.lower
      ((lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table).polarCoefficient C.lower C.lower_ne_one) :=
  (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
    hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
      table).toCriticalPolarFunction C.lower C.lower_ne_one

@[simp] theorem lowSourceBaseCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (x : ResidueField F) :
    lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table p C x =
      lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table x := by
  exact LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _

/-- The actual low nonidentity norm-row residual function, equipped with the
polar coefficient extracted from that same source-tied function. -/
noncomputable def lowSourceNormCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (j : OddNormIndex F K) :
    CriticalPolarFunction (ResidueField F) C.lower
      ((lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j).polarCoefficient C.lower C.lower_ne_one) :=
  (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1 hdelta
    hT hgammaF P j).toCriticalPolarFunction C.lower C.lower_ne_one

@[simp] theorem lowSourceNormCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (j : OddNormIndex F K) (x : ResidueField F) :
    lowSourceNormCriticalPolarFunction F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P p C j x =
      lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j x := by
  exact LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _

/-- The actual low nonidentity twist-row residual function, equipped with the
polar coefficient extracted from that same source-tied function. -/
noncomputable def lowSourceTwistCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (j : OddNormIndex F K) :
    CriticalPolarFunction (ResidueField F) C.lower
      ((lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j).polarCoefficient C.lower
            C.lower_ne_one) :=
  (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
    hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
      table WTwist j).toCriticalPolarFunction C.lower C.lower_ne_one

@[simp] theorem lowSourceTwistCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (j : OddNormIndex F K) (x : ResidueField F) :
    lowSourceTwistCriticalPolarFunction F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table p C WTwist j x =
      lowSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j x := by
  exact LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _

/-- The public low odd eliminator with all four residual row families tied to
the one supplied uniformizer source.  The identity row remains at its actual
base conductor, while nonidentity norm and twist rows use the newly
constructed conductor-`t+1` coordinate. -/
theorem lowSourceCoordinateConstructedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (R : LowOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table hodd WUp WTwist)
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
            hdelta hT hgammaF P j))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
            hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
              hgammaF hgammaK P table WTwist j)) :
    LowSourceTiedExactOddResultEliminator (DeltaF := DeltaF)
      (DeltaK := DeltaK) F K ht hres pi hpi hgen data D chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table hodd WUp WTwist
            (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF
              hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
                hgammaF hgammaK P table hodd WUp WTwist)
            (lowActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
              data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
                hdelta hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R
                  (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
                    hF.epsilon_le_one
                      (phaseReductionResidualCoordinateSource F K hres pi
                        hpi).upperUniformizer
                      (phaseReductionResidualCoordinateSource F K hres pi
                        hpi).upper_order)
                  (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
                    hF.epsilon_le_one
                    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
                    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)
                  (fun _ ↦
                    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
                      (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
                      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
                      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)
                  (fun _ ↦
                    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
                      (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
                      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
                      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)
                  hExtension hBase hNorm hTwist) :=
  lowActualRowsConstructedExactOddResultEliminator F K ht hres pi hpi hgen
    data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R
        (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
          hF.epsilon_le_one
            (PhaseReductionResidualCoordinateSource.upperUniformizer
              (phaseReductionResidualCoordinateSource F K hres pi hpi))
            (PhaseReductionResidualCoordinateSource.upper_order
              (phaseReductionResidualCoordinateSource F K hres pi hpi)))
        (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
          hF.epsilon_le_one
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)
        (fun _ ↦
          PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
            (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)
        (fun _ ↦
          PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
            (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)
        hExtension hBase hNorm hTwist

namespace LowTableBackedExactOddAssembly

/-- The low table's actual extension, base twist, nonidentity norm, and
nonidentity twist rows force the endpoint quotient to one.  The proof does
not use the raw endpoint fields of `OddGlobalScalarInput`. -/
theorem endpointFactor_eq_one
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (B : LowTableBackedExactOddAssembly F K ht hres pi hpi hgen data D chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WUp WTwist) :
    D.factors.endpoint = 1 := by
  apply endpointFactor_eq_one_of_actual_stationary_rows
  · exact ⟨_, B.extensionPhase⟩
  · refine nonidentityNormStationary_of_optionEquiv
      (oddNormCharacterIndexing F K ht hres pi hpi hgen)
      (oddNormCharacterIndexing_none F K ht hres pi hpi hgen) ?_
    intro j
    rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen j]
    exact ⟨_, B.nonidentityNormPhase j⟩
  · refine allTwistsStationary_of_equiv
      (oddNormCharacterIndexing F K ht hres pi hpi hgen) ?_
    intro index
    cases index with
    | none =>
        rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
        exact ⟨_, B.baseTwistPhase⟩
    | some j =>
        rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen j]
        exact ⟨_, B.nonidentityTwistPhase j⟩

end LowTableBackedExactOddAssembly

end LowTableBacked

end

end LanglandsFirstMainLemma
