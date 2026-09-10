import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.HighAssembly
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.ResidualRowCore

/-!
# Named high odd-prime residual rows

This module exposes the source-tied high residual rows and completes the
high table-backed endpoint theorem while preserving the exact section
parameters of the original monolithic file.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

section HighTableBacked

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

/-! ### Named source-tied high residual rows -/

/-- Actual upstairs high row at the upper coordinate forced by the common
source. -/
noncomputable def highSourceUpstairsPhase
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) :
    LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows)
    hK.epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).upper_order

/-- Complete residual function of the actual source-tied upstairs high row. -/
noncomputable def highSourceUpstairsFunction
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) : ResidueField K → ℂ :=
  (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source).criticalFunction

/-- Actual nonidentity norm row at its post-drop conductor and depth, using
the lower coordinate forced by the same source. -/
noncomputable def highSourceNormPhase
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : OddNormIndex F K) :
    LocalLamprechtPhaseData F
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))))
      data.baseAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      htpos hstrict.le gammaF hgammaF source.normRows j)
    (lowCriticalConductorDecomposition (t := t) (by omega)).epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order

/-- Complete residual function of that actual nonidentity norm row. -/
noncomputable def highSourceNormFunction
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : OddNormIndex F K) : ResidueField F → ℂ :=
  (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
      j).criticalFunction

/-- Actual high twist row, including `j=0`, at its genuine base conductor
and the lower source coordinate. -/
noncomputable def highSourceTwistPhase
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : ZMod (Module.finrank F K)) :
    LocalLamprechtPhaseData F
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))) data.baseAddChar :=
  LocalLamprechtPhaseData.sourceTiedRow
    (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source.productRows j)
    hF.epsilon_le_one
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order

/-- Complete residual function of the actual high twist row. -/
noncomputable def highSourceTwistFunction
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : ZMod (Module.finrank F K)) : ResidueField F → ℂ :=
  (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
      j).criticalFunction

/-- The actual source-tied upper function bundled with the polar coefficient
extracted from that same upper row. -/
noncomputable def highSourceUpstairsCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) :
    CriticalPolarFunction (ResidueField K) (C.upper hres)
      ((highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source).polarCoefficient (C.upper hres) (C.upper_ne_one hres)) :=
  (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source).toCriticalPolarFunction (C.upper hres) (C.upper_ne_one hres)

@[simp]
theorem highSourceUpstairsCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) (x : ResidueField K) :
    highSourceUpstairsCriticalPolarFunction F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF p C source x =
      highSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source x :=
  LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _

/-- The actual high upstairs row displayed in the lower residue coordinate.
Its upper additive character, residue equivalence, and inverse-Frobenius
reindexing are all derived from the single lower datum `C`. -/
noncomputable def highSourceDisplayedUpstairsCriticalPolarFunction
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) :=
  (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source).displayedInLowerCoordinate p hchar hres C

@[simp]
theorem highSourceDisplayedUpstairsCriticalPolarFunction_apply
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) (x : ResidueField F) :
    highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF p hchar C source x =
      highSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          (PhaseReductionResidualCoordinateSource.residueEquiv hres
            ((C.frobeniusEquiv hchar).symm x)) :=
  LocalLamprechtPhaseData.displayedInLowerCoordinate_apply _ _ _ _ _ _

/-- The actual source-tied nonidentity norm function bundled with its own
post-drop polar coefficient. -/
noncomputable def highSourceNormCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : OddNormIndex F K) :
    CriticalPolarFunction (ResidueField F) C.lower
      ((highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source j).polarCoefficient C.lower C.lower_ne_one) :=
  (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source j).toCriticalPolarFunction C.lower C.lower_ne_one

@[simp]
theorem highSourceNormCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : OddNormIndex F K) (x : ResidueField F) :
    highSourceNormCriticalPolarFunction F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        p C source j x =
      highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j x :=
  LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _

/-- The actual source-tied twist function, including `j = 0`, bundled with
the polar coefficient extracted from that same row. -/
noncomputable def highSourceTwistCriticalPolarFunction
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : ZMod (Module.finrank F K)) :
    CriticalPolarFunction (ResidueField F) C.lower
      ((highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source j).polarCoefficient C.lower C.lower_ne_one) :=
  (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
    hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source j).toCriticalPolarFunction C.lower C.lower_ne_one

@[simp]
theorem highSourceTwistCriticalPolarFunction_apply
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : ZMod (Module.finrank F K)) (x : ResidueField F) :
    highSourceTwistCriticalPolarFunction F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        p C source j x =
      highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j x :=
  LocalLamprechtPhaseData.toCriticalPolarFunction_apply _ _ _ _


/-- The upper and lower stationary decompositions supplied by the actual
high table have the same parity. -/
theorem highActual_epsilon_eq
    (_source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) : epsilonK = epsilon := by
  have hmrel := highParameter_intermediate_conductor_relation
    F K ht hres pi hpi hgen (data.twistData 1) chiK hminimal hchi hstrict.le
  have hmK := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen (data.twistData 1) chiK hminimal hchi hstrict.le
  have hpThree : 3 ≤ Module.finrank F K := by
    have hpTwo := (PrimeCyclicExtension.degree_prime F K).two_le
    by_contra hnot
    have hpEq : Module.finrank F K = 2 := by omega
    rw [hpEq] at hodd
    norm_num at hodd
  have harith := highParameter_intermediate_depthArithmetic
    F K ht hres pi hpi hgen
      (p := Module.finrank F K) (T := t + 1)
      hodd hpThree (by omega) hF hK hstrict.le hupper hmrel hmK
  exact harith.epsilon_eq

/-- Before inverse-Frobenius display, the named source-tied upstairs
function is the literal raw Lamprecht function at the single upper source
coordinate. -/
theorem highSourceUpstairsFunction_apply_eq_raw
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilonK : epsilonK = 1) (y : ResidueField K) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
    let z : K := (teichmuller K y : K)
    let x : K := (delta : K) * z
    let upperRatio : K :=
      ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows : Kˣ) : K) /
        algebraMap F K (gammaF : F)
    let upperUnit := lamprechtHasseUnit K chiK dK
      (by rw [hK.conductor_eq, hepsilonK]) hK.conductor_gt_one delta
        (phaseReductionSourceCoordinate_order K S.upperUniformizer
          S.upper_order dK) z
        (by exact (mem_lattice_zero_iff K).2 (teichmuller K y).property)
    highSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source y =
      (psiK.character (upperRatio * x) : ℂ) *
        (chiK.character upperUnit : ℂ)⁻¹ := by
  subst epsilonK
  dsimp only
  unfold highSourceUpstairsFunction highSourceUpstairsPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  rw [criticalCoordinateOfParity_one]
  unfold highOddUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold highOddUpstairsPhaseSource OddIntermediateHighProductData.upstairsPhase
  unfold localPhaseOfStationaryClass LocalLamprechtPhaseData.criticalFunction
  change
    (psiK.character
          (((OddIntermediateHighProductData.upstairsRepresentative
            F K ht hres pi hpi hgen (data.twistData 1) chiK
              data.baseAddChar psiK hF hK hminimal hchi hpsi hodd htpos
                hstrict.le hupper gammaF hgammaF
                  source.productRows).representative : K) *
            (phaseReductionSourceCoordinate K
              (phaseReductionResidualCoordinateSource F K hres pi hpi).upperUniformizer
                dK : K) * (teichmuller K y : K) /
              algebraMap F K (gammaF : F)) : ℂ) *
        (chiK.character _ : ℂ)⁻¹ = _
  congr 1
  · congr 1
    unfold highOddUpstairsRepresentativeUnit
    rw [StationaryClassRepresentative.coe_unit]
    ring

/-- Displayed raw evaluation of the actual upstairs function.  The unit is
only a witness for `1+x` at the common source-forced displayed lift. -/
theorem highSourceDisplayedUpstairsFunction_apply_eq_raw
    (pResid : ℕ) (hchar : residueCharacteristic F = pResid)
    (C : FrobeniusResidualAddCharData F pResid)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilonK : epsilonK = 1) (X : ResidueField F)
    (upperUnit : Kˣ)
    (hUpperUnit :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
        ((C.frobeniusEquiv hchar).symm X)
      let x : K :=
        (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
          (teichmuller K y : K)
      (upperUnit : K) = 1 + x) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
      ((C.frobeniusEquiv hchar).symm X)
    let x : K :=
      (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
        (teichmuller K y : K)
    let upperRatio : K :=
      ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows : Kˣ) : K) /
        algebraMap F K (gammaF : F)
    highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF pResid hchar C source X =
      (psiK.character (upperRatio * x) : ℂ) *
        (chiK.character upperUnit : ℂ)⁻¹ := by
  dsimp only at hUpperUnit ⊢
  rw [highSourceDisplayedUpstairsCriticalPolarFunction_apply]
  rw [highSourceUpstairsFunction_apply_eq_raw
    F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
      htpos hstrict hupper gammaF hgammaF source hepsilonK]
  congr 2
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
    ((C.frobeniusEquiv hchar).symm X)
  let naturalUnit : Kˣ := (lamprechtHasseUnit K chiK dK
    (by rw [hK.conductor_eq, hepsilonK]) hK.conductor_gt_one
      (phaseReductionSourceCoordinate K S.upperUniformizer dK)
      (phaseReductionSourceCoordinate_order K S.upperUniformizer S.upper_order
        dK) (teichmuller K y : K)
      ((mem_lattice_zero_iff K).2 (teichmuller K y).property) : Kˣ)
  have hnatural : (naturalUnit : K) =
      1 + (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
        (teichmuller K y : K) := by
    rfl
  have hunit : naturalUnit = upperUnit := by
    apply Units.ext
    rw [hnatural, hUpperUnit]
  exact congrArg (fun z : Kˣ ↦ (chiK.character z : ℂ)) hunit

/-- The actual high base row evaluates to one on any norm-polynomial value
lying in its genuine stationary linearization layer. -/
theorem highOdd_baseRaw_eq_one
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (x : K) (upperUnit : Kˣ)
    (hUpperUnit : (upperUnit : K) = 1 + x)
    (hPx : phaseReductionNormPolynomial F K x ∈
      lattice F ((d + epsilon : ℕ) : ℤ)) :
    (data.baseAddChar.character
          ((((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF source.productRows 0 : Fˣ) : F) /
              (gammaF : F)) * phaseReductionNormPolynomial F K x) : ℂ) *
        ((data.twistData 1).character (normUnits F K upperUnit) : ℂ)⁻¹ =
      1 := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K)))
  let twist := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
    (data.twistData 1) mu
  let R := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows 0
  have hmuOne : mu = 1 := by
    dsimp only [mu]
    change ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen 1 = 1
    exact map_one _
  have hchar : twist.character = (data.twistData 1).character := by
    dsimp only [twist]
    rw [ramifiedNormCharacterOrbitTwistData_character]
    rw [hmuOne, NormCharacter.coe_one]
    exact one_mul (data.twistData 1).character
  have hBaseUnit : ((normUnits F K upperUnit : Fˣ) : F) =
      1 + phaseReductionNormPolynomial F K x := by
    rw [coe_normUnits, hUpperUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  have hraw := stationaryRawFactor_eq_one
    (h := source.productRows.factorDecomposition 0) gammaF
      (source.productRows.factorDenominator 0) R
      (phaseReductionNormPolynomial F K x) hPx
        (normUnits F K upperUnit) hBaseUnit
  rw [hchar] at hraw
  simpa only [R, highOddLinearTwistUnit,
    StationaryClassRepresentative.coe_unit, div_mul_eq_mul_div] using hraw

/-- The actual index-one high norm row evaluates to one on `P(u*x)` once
that value lies on its true conductor-`t+1` stationary layer.  The norm
character is killed only after applying selected-alpha linearization. -/
theorem highOdd_tauRaw_eq_one
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (x : K) (upperUxUnit : Kˣ)
    (hUpperUxUnit : (upperUxUnit : K) =
      1 + highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows * x)
    (hPux : phaseReductionNormPolynomial F K
        (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows * x) ∈
      lattice F ((((t + 2) / 2 : ℕ) : ℤ))) :
    let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
    let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    let tauRatio : F :=
      1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))
    (data.baseAddChar.character
          (tauRatio * phaseReductionNormPolynomial F K (u * x)) : ℂ) *
        (tau.1 (normUnits F K upperUxUnit) : ℂ)⁻¹ = 1 := by
  dsimp only
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  have htau : tau ≠ 1 := by
    exact highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen
  have hm : (data.twistData 1).conductor =
      t + 1 + ((data.twistData 1).conductor - (t + 1)) :=
    (Nat.add_sub_of_le hstrict.le).symm
  have hselected := highParameter_intermediate_selectedAlpha_linearization
    F K ht hres pi hpi hgen htpos (data.twistData 1) data.baseAddChar hm
      tau htau gammaF hgammaF source.normRows.a source.normRows.alpha
        source.normRows.a_coe source.normRows.alpha1
          source.normRows.alpha_choice source.normRows.a_class
  let y : F := phaseReductionNormPolynomial F K
    (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows * x)
  let ylat : lattice F ((((t + 2) / 2 : ℕ) : ℤ)) := ⟨y, hPux⟩
  have hlinear := hselected ylat
  have hunitCoe : ((normUnits F K upperUxUnit : Fˣ) : F) = 1 + y := by
    rw [coe_normUnits, hUpperUxUnit]
    simp only [y, phaseReductionNormPolynomial]
    ring
  have hpositiveUnit : normUnits F K upperUxUnit =
      positiveUnitOfLattice F (by omega : 0 < (t + 2) / 2) ylat := by
    apply Units.ext
    rw [hunitCoe]
    rfl
  have htauNorm : tau.1 (normUnits F K upperUxUnit) = 1 :=
    NormCharacter.eq_one_on_normRange F K tau _ ⟨upperUxUnit, rfl⟩
  rw [← hpositiveUnit] at hlinear
  rw [htauNorm] at hlinear
  have hpsiOne : data.baseAddChar.character
      (norm F K (source.normRows.alpha1 : K) * y / (gammaF : F)) = 1 :=
    hlinear.symm
  have hratio :
      1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F)) =
        norm F K (source.normRows.alpha1 : K) / (gammaF : F) := by
    simp only [Units.val_div_eq_div_val, coe_normUnits]
    field_simp [Units.ne_zero gammaF,
      (Algebra.norm_ne_zero_iff).2 (Units.ne_zero source.normRows.alpha1)]
  rw [htauNorm]
  rw [hratio]
  have hpsiOneC := congrArg (Units.val : ℂˣ → ℂ) hpsiOne
  rw [show
    norm F K (source.normRows.alpha1 : K) / (gammaF : F) *
        phaseReductionNormPolynomial F K
          (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
            hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
              hgammaF source.productRows * x) =
      norm F K (source.normRows.alpha1 : K) * y / (gammaF : F) by ring]
  simpa using hpsiOneC

/-- The two polynomial-depth facts for the literal displayed high source.
The lift is the source coordinate times its Teichmuller residue input, and
the multiplier is the normalized ratio from the same high table witness. -/
theorem highSourceDisplayed_polynomialDepths
    (pResid : ℕ) (hchar : residueCharacteristic F = pResid)
    (C : FrobeniusResidualAddCharData F pResid)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1) (X : ResidueField F) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
      ((C.frobeniusEquiv hchar).symm X)
    let x : K :=
      (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
        (teichmuller K y : K)
    let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    phaseReductionNormPolynomial F K x ∈
        lattice F ((d + epsilon : ℕ) : ℤ) ∧
      phaseReductionNormPolynomial F K (u * x) ∈
        lattice F ((((t + 2) / 2 : ℕ) : ℤ)) := by
  dsimp only
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
    ((C.frobeniusEquiv hchar).symm X)
  let x : K := (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
    (teichmuller K y : K)
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let v := (data.twistData 1).conductor - (t + 1)
  have hv : 0 < v := by dsimp only [v]; omega
  have hm : 2 * d + 1 = t + 1 + v := by
    have hFc := hF.conductor_eq
    rw [hepsilon] at hFc
    dsimp only [v]
    omega
  have hepsilonK : epsilonK = 1 :=
    (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source).trans hepsilon
  have hmKconductor := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen (data.twistData 1) chiK hminimal hchi hstrict.le
  have hmK : 2 * dK + 1 = t + 1 + Module.finrank F K * v := by
    have hKc := hK.conductor_eq
    rw [hepsilonK] at hKc
    dsimp only [v]
    omega
  have hx : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x := by
    simpa only [x] using
      phaseReductionSourceTeichmullerLift_order_ge K S.upperUniformizer
        S.upper_order dK y
  have hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [u, v] using
      highOddNormalizedRatio_order F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
  constructor
  · have hbase := phaseReductionHighBasePolynomial_deep_of_order F K ht
      htpos rfl hm hv hmK hodd hres pi hpi hgen x hx
    simpa only [hepsilon,
      phaseReductionNormPolynomial_eq_normPolynomialValue] using hbase
  · have htau := phaseReductionHighTauPolynomial_deep_of_order F K ht
      htpos rfl hv hmK hodd hres pi hpi hgen u x hu hx
    simpa only [phaseReductionNormPolynomial_eq_normPolynomialValue] using htau

/-- Actual high specialization of the manuscript's displayed complete
critical-function transport.  The two lattice hypotheses are precisely the
class-depth facts for `P(x)` and `P(u*x)` at their genuine stationary
conductors; every coordinate, function, representative, and ratio in the
conclusion is otherwise constructed from the single high source. -/
theorem highSourceDisplayed_exactCriticalTransport_above
    (pResid : ℕ) (hchar : residueCharacteristic F = pResid)
    (C : FrobeniusResidualAddCharData F pResid)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1) (X : ResidueField F)
    (upperUxUnit : Kˣ)
    (hUpperUxUnit :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
        ((C.frobeniusEquiv hchar).symm X)
      let x : K :=
        (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
          (teichmuller K y : K)
      let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
      (upperUxUnit : K) = 1 + u * x)
    (hPx :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
        ((C.frobeniusEquiv hchar).symm X)
      let x : K :=
        (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
          (teichmuller K y : K)
      phaseReductionNormPolynomial F K x ∈
        lattice F ((d + epsilon : ℕ) : ℤ))
    (hPux :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
        ((C.frobeniusEquiv hchar).symm X)
      let x : K :=
        (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
          (teichmuller K y : K)
      let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
      phaseReductionNormPolynomial F K (u * x) ∈
        lattice F ((((t + 2) / 2 : ℕ) : ℤ))) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
      ((C.frobeniusEquiv hchar).symm X)
    let x : K :=
      (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
        (teichmuller K y : K)
    let A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
    highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF pResid hchar C source X =
      highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
            0 0 *
        (highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
            jOne 0)⁻¹ *
        (data.baseAddChar.character
          (A * (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x)) : ℂ) := by
  dsimp only at hUpperUxUnit hPx hPux ⊢
  have hepsilonK : epsilonK = 1 :=
    (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source).trans hepsilon
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
    ((C.frobeniusEquiv hchar).symm X)
  let x : K := (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
    (teichmuller K y : K)
  let A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let upperUnit : Kˣ := (lamprechtHasseUnit K chiK dK
    (by rw [hK.conductor_eq, hepsilonK]) hK.conductor_gt_one
      (phaseReductionSourceCoordinate K S.upperUniformizer dK)
      (phaseReductionSourceCoordinate_order K S.upperUniformizer S.upper_order
        dK) (teichmuller K y : K)
      ((mem_lattice_zero_iff K).2 (teichmuller K y).property) : Kˣ)
  have hUpperUnit : (upperUnit : K) = 1 + x := by rfl
  have hraw := highOdd_actualStationaryRatios_exactCriticalTransport
    F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
      htpos hstrict hupper gammaF hgammaF source x upperUnit upperUxUnit
        hUpperUnit hUpperUxUnit
  let baseRaw : ℂ :=
    (data.baseAddChar.character
      ((((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows 0 : Fˣ) : F) / (gammaF : F)) *
            phaseReductionNormPolynomial F K x) : ℂ) *
      ((data.twistData 1).character (normUnits F K upperUnit) : ℂ)⁻¹
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  let tauRaw : ℂ :=
    (data.baseAddChar.character
      ((1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))) *
        phaseReductionNormPolynomial F K (u * x)) : ℂ) *
      (tau.1 (normUnits F K upperUxUnit) : ℂ)⁻¹
  let upperRatio : K :=
    ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows : Kˣ) : K) /
      algebraMap F K (gammaF : F)
  let upperRaw : ℂ :=
    (psiK.character (upperRatio * x) : ℂ) *
      (chiK.character upperUnit : ℂ)⁻¹
  let correction : ℂ :=
    (data.baseAddChar.character
      (A * (phaseReductionNormHigherPart F K (u * x) -
        n * phaseReductionNormHigherPart F K x)) : ℂ)
  have hrawC := congrArg (Units.val : ℂˣ → ℂ) hraw
  push_cast at hrawC
  have hraw' : baseRaw * tauRaw⁻¹ * correction = upperRaw := by
    dsimp only [baseRaw, tauRaw, upperRaw, correction, upperRatio, tau, A, u, n]
    simpa only [Units.val_div_eq_div_val] using hrawC
  have hbase : baseRaw = 1 := by
    exact highOdd_baseRaw_eq_one F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        x upperUnit hUpperUnit hPx
  have htau : tauRaw = 1 := by
    exact highOdd_tauRaw_eq_one F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        x upperUxUnit hUpperUxUnit hPux
  have hdisplay :
      highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi
          hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
            hupper gammaF hgammaF pResid hchar C source X = upperRaw := by
    exact highSourceDisplayedUpstairsFunction_apply_eq_raw
      F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
        htpos hstrict hupper gammaF hgammaF pResid hchar C source hepsilonK X
          upperUnit hUpperUnit
  have htransport :
      highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi
          hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
            hupper gammaF hgammaF pResid hchar C source X = correction := by
    rw [hdisplay, ← hraw', hbase, htau]
    simp
  let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
  have htwistZero :
      highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          0 0 = 1 :=
    LocalLamprechtPhaseData.criticalFunction_zero
      (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0)
  have hnormZero :
      highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          jOne 0 = 1 :=
    LocalLamprechtPhaseData.criticalFunction_zero
      (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          jOne)
  rw [htransport, htwistZero, hnormZero]
  simp only [one_mul, inv_one]
  simp only [correction, A, u, n, x, y, S,
    phaseReductionSourceCoordinate_coe,
    PhaseReductionResidualCoordinateSource.residueEquiv_apply]

theorem highOdd_normCharacter_linearization_on_criticalCoordinate
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1)
    (j : ZMod (Module.finrank F K)) (X : ResidueField F) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let lam := oddNormAllIndexScalar F K ht hres pi hpi hgen htpos j
    let delta := phaseReductionSourceCoordinate F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d
    let z : F := (teichmuller F X : F)
    (mu.1
      (criticalPolarUnit F (data.twistData 1) d
        (by rw [hF.conductor_eq, hepsilon])
        (by rw [hF.conductor_eq, hepsilon] at hstrict ⊢; omega)
        delta
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d)
        z ((mem_lattice_zero_iff F).2 (teichmuller F X).property) : Fˣ) : ℂ) =
      (data.baseAddChar.character
        (lam * norm F K (source.productRows.alpha1 : K) *
          (delta : F) * z / (gammaF : F)) : ℂ) := by
  dsimp only
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  let lam := oddNormAllIndexScalar F K ht hres pi hpi hgen htpos j
  let delta := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d
  let z : F := (teichmuller F X : F)
  let y : F := (delta : F) * z
  have htauNe : tau ≠ 1 := by
    exact highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen
  have hm : (data.twistData 1).conductor =
      t + 1 + ((data.twistData 1).conductor - (t + 1)) :=
    (Nat.add_sub_of_le hstrict.le).symm
  have halphaLinear := highParameter_intermediate_selectedAlpha_linearization
    F K ht hres pi hpi hgen htpos (data.twistData 1) data.baseAddChar hm tau
      htauNe gammaF hgammaF source.normRows.a source.normRows.alpha
        source.normRows.a_coe source.normRows.alpha1
          source.normRows.alpha_choice source.normRows.a_class
  have hsd : (t + 2) / 2 ≤ d := by
    rw [hF.conductor_eq, hepsilon] at hstrict
    omega
  have hyD : y ∈ lattice F (d : ℤ) := by
    have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
      rw [mem_lattice]
      exact (phaseReductionSourceCoordinate_order F
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d).ge
    exact mul_mem_lattice F hdeltaMem
      ((mem_lattice_zero_iff F).2 (teichmuller F X).property)
  let ys0 : lattice F (((t + 2) / 2 : ℕ) : ℤ) :=
    ⟨y, lattice_antitone F (by exact_mod_cast hsd) hyD⟩
  have htauEval := halphaLinear ys0
  have heqPower : mu = tau ^ j.val := by
    dsimp only [mu, tau]
    exact highParameter_intermediate_index_eq_power
      F K ht hres pi hpi hgen j
  have hpowChar : tau.1 ^ (j.val : ℤ) = mu.1 := by
    calc
      tau.1 ^ (j.val : ℤ) = tau.1 ^ j.val := by
        exact zpow_natCast tau.1 j.val
      _ = (tau ^ j.val).1 := by
        simpa using (NormCharacter.coe_pow (F := F) (K := K) tau j.val).symm
      _ = mu.1 := congrArg (fun q : NormCharacter F K ↦ q.1) heqPower.symm
  have hmuNat :
      mu.1 (positiveUnitOfLattice F (by omega : 0 < (t + 2) / 2) ys0) =
        data.baseAddChar.character
          ((j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) := by
    rw [← hpowChar,
      IsStationaryRestrictionClass.continuousQuasiChar_zpow_apply,
      htauEval]
    let arg : F := norm F K (source.normRows.alpha1 : K) * y /
      (gammaF : F)
    calc
      data.baseAddChar.character.toAddChar arg ^ (j.val : ℤ) =
          data.baseAddChar.character.toAddChar ((j.val : ℤ) • arg) :=
        (AddChar.map_zsmul_eq_zpow data.baseAddChar.character.toAddChar
          (j.val : ℤ) arg).symm
      _ = data.baseAddChar.character.toAddChar
          ((j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) := by
        apply congrArg data.baseAddChar.character.toAddChar
        dsimp only [arg]
        simp only [zsmul_eq_mul]
        push_cast
        ring
      _ = _ := rfl
  have halphaNorm : ord F (norm F K (source.normRows.alpha1 : K)) =
      ((((data.twistData 1).conductor - (t + 1) : ℕ) : ℤ) : WithTop ℤ) := by
    simpa only [Int.ofNat_sub hstrict.le] using
      source.normRows.alpha_choice.norm_order
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have hteich : lam - (j.val : F) ∈
      lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
    simpa only [lam, oddNormAllIndexScalar] using
      highParameter_intermediate_teichmuller_congruent
        F K (Module.finrank F K) (t + 1)
          (residueCharacteristic_eq_degree_of_positive_break
            F K ht htpos pi hpi hgen) rfl htrace j
  have hdiffNumerator :
      (lam - (j.val : F)) * norm F K (source.normRows.alpha1 : K) * y ∈
        lattice F ((data.twistData 1).conductor : ℤ) := by
    have hmul1 := mul_mem_lattice F hteich (by
      rw [mem_lattice, halphaNorm])
    have hmul2 := mul_mem_lattice F hmul1 hyD
    apply lattice_antitone F
      (m := ((data.twistData 1).conductor : ℤ))
      (n := (((t + 1) / 2 : ℕ) : ℤ) +
        ((data.twistData 1).conductor - (t + 1) : ℕ) + (d : ℤ))
    · exact_mod_cast (show (data.twistData 1).conductor ≤
        (t + 1) / 2 + ((data.twistData 1).conductor - (t + 1)) + d by
          rw [hF.conductor_eq, hepsilon]
          omega)
    · exact hmul2
  have hscaled :
      ((lam - (j.val : F)) * norm F K (source.normRows.alpha1 : K) * y) /
          (gammaF : F) ∈ lattice F (-data.baseAddChar.conductor) := by
    apply (div_mem_lattice_iff F (gammaF : F) _
      (((data.twistData 1).conductor : ℤ) + data.baseAddChar.conductor)
      (-data.baseAddChar.conductor) hgammaF).2
    simpa [add_assoc] using hdiffNumerator
  have hmuEval :
      (mu.1 (positiveUnitOfLattice F
        (by omega : 0 < (t + 2) / 2) ys0) : ℂ) =
        (data.baseAddChar.character
          (lam * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) : ℂ) := by
    have hmuNatC := congrArg (Units.val : ℂˣ → ℂ) hmuNat
    rw [hmuNatC]
    have harg :
        lam * norm F K (source.normRows.alpha1 : K) * y / (gammaF : F) -
          (j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F) =
        ((lam - (j.val : F)) * norm F K (source.normRows.alpha1 : K) * y) /
          (gammaF : F) := by ring
    have hdiv :
        data.baseAddChar.character
          (lam * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) /
        data.baseAddChar.character
          ((j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) = 1 := by
      calc
        data.baseAddChar.character
            (lam * norm F K (source.normRows.alpha1 : K) * y /
              (gammaF : F)) /
          data.baseAddChar.character
            ((j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
              (gammaF : F)) =
          data.baseAddChar.character.toAddChar
            (lam * norm F K (source.normRows.alpha1 : K) * y /
                (gammaF : F) -
              (j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
                (gammaF : F)) :=
          (data.baseAddChar.character.toAddChar.map_sub_eq_div _ _).symm
        _ = 1 := by
          rw [harg]
          exact data.baseAddChar.isConductor.trivial _ hscaled
    have hdivC := congrArg (Units.val : ℂˣ → ℂ) hdiv
    have hdivC' :
        (data.baseAddChar.character
          (lam * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) : ℂ) /
        (data.baseAddChar.character
          ((j.val : F) * norm F K (source.normRows.alpha1 : K) * y /
            (gammaF : F)) : ℂ) = 1 := by
      simpa only [Units.val_div_eq_div_val, Units.val_one] using hdivC
    symm
    exact (div_eq_one_iff_eq (ContinuousAddChar.apply_ne_zero _ _)).1 hdivC'
  have hunit :
      (criticalPolarUnit F (data.twistData 1) d
        (by rw [hF.conductor_eq, hepsilon])
        (by rw [hF.conductor_eq, hepsilon] at hstrict ⊢; omega)
        delta
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d)
        z ((mem_lattice_zero_iff F).2 (teichmuller F X).property) : Fˣ) =
      positiveUnitOfLattice F (by omega : 0 < (t + 2) / 2) ys0 := by
    apply Units.ext
    rfl
  rw [hunit, hmuEval, source.alpha1_eq]
  congr 1
  dsimp only [lam, y, delta, z]
  ring

/-- Raw critical-polar equality for the actual High linear twist
representatives.  The indexed norm character and the representative
translation are transported together. -/
theorem highOdd_twistCriticalPolarFunction_eq_base
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1)
    (j : ZMod (Module.finrank F K)) (X : ResidueField F) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
      (data.twistData 1) mu
    let mu0 := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K)))
    let twist0 := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
      (data.twistData 1) mu0
    let delta := phaseReductionSourceCoordinate F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d
    let Rj := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows j
    let R0 := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows 0
    criticalPolarFunction F twist data.baseAddChar d
        (by
          rw [highParameter_intermediate_twist_conductor_eq F K ht hres pi
            hpi hgen (data.twistData 1) hminimal hstrict.le mu,
            hF.conductor_eq, hepsilon])
        (by
          rw [highParameter_intermediate_twist_conductor_eq F K ht hres pi
            hpi hgen (data.twistData 1) hminimal hstrict.le mu]
          rw [hF.conductor_eq, hepsilon] at hstrict ⊢
          omega)
        ⟨gammaF, source.productRows.factorDenominator j⟩ delta
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d)
        Rj.toLamprecht X =
      criticalPolarFunction F twist0 data.baseAddChar d
        (by
          rw [highParameter_intermediate_twist_conductor_eq F K ht hres pi
            hpi hgen (data.twistData 1) hminimal hstrict.le mu0,
            hF.conductor_eq, hepsilon])
        (by
          rw [highParameter_intermediate_twist_conductor_eq F K ht hres pi
            hpi hgen (data.twistData 1) hminimal hstrict.le mu0]
          rw [hF.conductor_eq, hepsilon] at hstrict ⊢
          omega)
        ⟨gammaF, source.productRows.factorDenominator 0⟩ delta
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d)
        R0.toLamprecht X := by
  dsimp only
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  let twist := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
    (data.twistData 1) mu
  let mu0 := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K)))
  let twist0 := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
    (data.twistData 1) mu0
  let lam := oddNormAllIndexScalar F K ht hres pi hpi hgen htpos j
  let delta := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d
  let Rj := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows j
  let R0 := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows 0
  have hcond : twist.conductor = (data.twistData 1).conductor := by
    dsimp only [twist, mu]
    exact highParameter_intermediate_twist_conductor_eq F K ht hres pi hpi
      hgen (data.twistData 1) hminimal hstrict.le _
  have hmBase : (data.twistData 1).conductor = 2 * d + 1 := by
    rw [hF.conductor_eq, hepsilon]
  have hmTwist : twist.conductor = 2 * d + 1 := hcond.trans hmBase
  have hcond0 : twist0.conductor = (data.twistData 1).conductor := by
    dsimp only [twist0]
    exact highParameter_intermediate_twist_conductor_eq F K ht hres pi hpi
      hgen (data.twistData 1) hminimal hstrict.le _
  have hmTwist0 : twist0.conductor = 2 * d + 1 := hcond0.trans hmBase
  have hlargeBase : 1 < (data.twistData 1).conductor := by
    rw [hF.conductor_eq, hepsilon] at hstrict ⊢
    omega
  have hlargeTwist : 1 < twist.conductor := by
    rw [hcond]
    exact hlargeBase
  have hlargeTwist0 : 1 < twist0.conductor := by
    rw [hcond0]
    exact hlargeBase
  have hmu0 : mu0 = 1 := by
    dsimp only [mu0]
    change ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen 1 = 1
    exact map_one _
  have hchar0 : twist0.character = (data.twistData 1).character := by
    rw [ramifiedNormCharacterOrbitTwistData_character, hmu0,
      NormCharacter.coe_one]
    exact one_mul (data.twistData 1).character
  have hchar : twist.character =
      twist0.character * mu.1 := by
    calc
      twist.character = mu.1 * (data.twistData 1).character :=
        ramifiedNormCharacterOrbitTwistData_character F K ht hres pi hpi hgen
          (data.twistData 1) mu
      _ = (data.twistData 1).character * mu.1 :=
        mul_comm (mu.1 : ContinuousQuasiChar F)
          (data.twistData 1).character
      _ = twist0.character * mu.1 :=
        congrArg (fun q : ContinuousQuasiChar F ↦ q * mu.1) hchar0.symm
  have hzero :
      oddNormAllIndexScalar F K ht hres pi hpi hgen htpos 0 = 0 := by
    exact (highParameter_intermediate_teichmuller_eq_zero_iff F
      (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen) 0).2 rfl
  have hrep : (Rj.toLamprecht : F) =
      (R0.toLamprecht : F) +
        lam * norm F K (source.productRows.alpha1 : K) := by
    change highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows j =
      highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows 0 +
        lam * norm F K (source.productRows.alpha1 : K)
    simp only [highOddLinearTwistValue]
    rw [hzero]
    dsimp only [lam]
    ring
  apply criticalPolarFunction_eq_of_linearized_factor twist twist0 mu.1
    data.baseAddChar d hmTwist hmTwist0 hlargeTwist hlargeTwist0 hchar gammaF
      (source.productRows.factorDenominator j)
        (source.productRows.factorDenominator 0) delta
          (phaseReductionSourceCoordinate_order F
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d)
          R0.toLamprecht Rj.toLamprecht
            (lam * norm F K (source.productRows.alpha1 : K)) hrep
  · intro Y
    have hlin :=
      highOdd_normCharacter_linearization_on_criticalCoordinate
      F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
        htpos hstrict hupper gammaF hgammaF source hepsilon j Y
    simpa only [criticalPolarUnit] using hlin

/-- The actual named High twist function at every index is the actual
zero-twist/base function at the common source coordinate when the base
conductor is odd and strictly above the break. -/
theorem highSourceTwistFunction_eq_base_of_odd
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1)
    (j : ZMod (Module.finrank F K)) (X : ResidueField F) :
    highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j X =
      highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          0 X := by
  subst epsilon
  unfold highSourceTwistFunction highSourceTwistPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  rw [criticalCoordinateOfParity_one]
  unfold highOddLinearTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction,
    transportLocalLamprechtPhaseData_criticalFunction]
  unfold localPhaseOfStationaryClass
  simp only [LocalLamprechtPhaseData.oddOfStationaryClass]
  rw [LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction]
  exact highOdd_twistCriticalPolarFunction_eq_base
    F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
      htpos hstrict hupper gammaF hgammaF source rfl j X

/-- At even post-drop parity, every actual source-tied High norm-row function
is the manuscript's literal constant-one Lamprecht function. -/
theorem highSourceNormFunction_eq_one_of_even
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hparity : lowCriticalParity t = 0)
    (j : OddNormIndex F K) (X : ResidueField F) :
    highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j X = 1 := by
  unfold highSourceNormFunction highSourceNormPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold highOddNormPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold highOddNormCharacterPowerPhase
  dsimp only
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hparity

/-- At even base conductor parity, every actual source-tied High twist-row
function is the manuscript's literal constant-one Lamprecht function. -/
theorem highSourceTwistFunction_eq_one_of_even
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 0)
    (j : ZMod (Module.finrank F K)) (X : ResidueField F) :
    highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j X = 1 := by
  unfold highSourceTwistFunction highSourceTwistPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold highOddLinearTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hepsilon

/-- At either permitted base conductor parity, every actual source-tied High
twist function is the actual zero-twist/base function at the common source
coordinate. -/
theorem highSourceTwistFunction_eq_base
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : ZMod (Module.finrank F K)) (X : ResidueField F) :
    highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j X =
      highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          0 X := by
  by_cases hzero : epsilon = 0
  · rw [highSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source hzero j X,
      highSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source hzero 0 X]
  · have hone : epsilon = 1 := by
      have hle := hF.epsilon_le_one
      omega
    exact highSourceTwistFunction_eq_base_of_odd F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source hone j X

/-- At even base conductor parity, the actual source-tied High upstairs
function is the manuscript's literal constant-one Lamprecht function. -/
theorem highSourceUpstairsFunction_eq_one_of_even
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 0) (X : ResidueField K) :
    highSourceUpstairsFunction F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source X = 1 := by
  have hepsilonK : epsilonK = 0 :=
    (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source).trans hepsilon
  unfold highSourceUpstairsFunction highSourceUpstairsPhase
  unfold LocalLamprechtPhaseData.sourceTiedRow
  unfold highOddUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_criticalFunction]
  unfold highOddUpstairsPhaseSource OddIntermediateHighProductData.upstairsPhase
  dsimp only
  apply localPhaseOfStationaryClass_criticalFunction_eq_one_of_even _ hepsilonK

/-- At even base conductor parity, the same actual High upstairs function is
constant one after the source-forced inverse-Frobenius display. -/
theorem highSourceDisplayedUpstairsFunction_eq_one_of_even
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 0) (X : ResidueField F) :
    highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi
        hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
          hupper gammaF hgammaF p hchar C source X = 1 := by
  rw [highSourceDisplayedUpstairsCriticalPolarFunction_apply]
  apply highSourceUpstairsFunction_eq_one_of_even F K ht hres pi hpi hgen
    data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source hepsilon

/-- The public high odd eliminator with every residual coordinate forced by
the one uniformizer source already supplied to the parameter theorem.  The
upper row uses `pi^dK`; all lower norm rows use the norm uniformizer at the
post-drop depth; and all twist rows use that same lower uniformizer at their
actual depth.  There are no independently rescalable coordinate arguments. -/
theorem highSourceCoordinateConstructedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
            hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source j))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
            hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source j)) :
    HighActualRowsExactOddResultEliminator (DeltaF := DeltaF)
      (DeltaK := DeltaK) F K ht hres pi hpi hgen data D chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source R
          (highActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
            data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source R
                (PhaseReductionResidualCoordinateSource.upperCriticalCoordinate
                  (phaseReductionResidualCoordinateSource F K hres pi hpi)
                  hK)
                (fun _ ↦
                  PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
                      (IsStationaryConductorDecomposition.epsilon_le_one
                        (lowCriticalConductorDecomposition (t := t)
                          (by omega)))
                      (PhaseReductionResidualCoordinateSource.lowerUniformizer
                        (phaseReductionResidualCoordinateSource F K hres pi
                          hpi))
                      (PhaseReductionResidualCoordinateSource.lower_order
                        (phaseReductionResidualCoordinateSource F K hres pi
                          hpi)))
                (fun _ ↦
                  PhaseReductionResidualCoordinateSource.lowerCriticalCoordinate
                    (phaseReductionResidualCoordinateSource F K hres pi hpi)
                    hF)
                hExtension hNorm hTwist) :=
  highActualRowsConstructedExactOddResultEliminator F K ht hres pi hpi hgen
    data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source R
        (PhaseReductionResidualCoordinateSource.upperCriticalCoordinate
          (phaseReductionResidualCoordinateSource F K hres pi hpi) hK)
        (fun _ ↦
          PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
            (IsStationaryConductorDecomposition.epsilon_le_one
              (lowCriticalConductorDecomposition (t := t) (by omega)))
            (PhaseReductionResidualCoordinateSource.lowerUniformizer
              (phaseReductionResidualCoordinateSource F K hres pi hpi))
            (PhaseReductionResidualCoordinateSource.lower_order
              (phaseReductionResidualCoordinateSource F K hres pi hpi)))
        (fun _ ↦
          PhaseReductionResidualCoordinateSource.lowerCriticalCoordinate
            (phaseReductionResidualCoordinateSource F K hres pi hpi) hF)
        hExtension hNorm hTwist

namespace HighTableBackedExactOddAssembly

/-- The high table's actual extension, nonidentity norm, and full twist rows
force the endpoint quotient to one; no global endpoint common factor is an
input to this proof. -/
theorem endpointFactor_eq_one
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (B : HighTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF S Q) :
    D.factors.endpoint = 1 := by
  apply endpointFactor_eq_one_of_actual_stationary_rows
  · exact ⟨_, B.extensionPhase⟩
  · refine nonidentityNormStationary_of_optionEquiv
      (oddNormCharacterIndexing F K ht hres pi hpi hgen)
      (oddNormCharacterIndexing_none F K ht hres pi hpi hgen) ?_
    intro j
    rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen j]
    exact ⟨_, B.nonidentityNormPhase j⟩
  · let e : ZMod (Module.finrank F K) ≃ NormCharacter F K :=
      (Multiplicative.ofAdd : ZMod (Module.finrank F K) ≃
        Multiplicative (ZMod (Module.finrank F K))).trans
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv
    refine allTwistsStationary_of_equiv e ?_
    intro j
    simpa only [e] using ⟨_, B.twistPhase j⟩

end HighTableBackedExactOddAssembly

end HighTableBacked

end

end LanglandsFirstMainLemma
