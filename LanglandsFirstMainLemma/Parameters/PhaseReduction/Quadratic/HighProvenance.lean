import LanglandsFirstMainLemma.Parameters.PhaseReduction.Quadratic.Core
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ParameterTablePhases

/-!
# High-table provenance for wild-quadratic assembly

This module contains the proof-bearing high-table source, phase,
correction, and complete-result data for the wild-quadratic assembly.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## High-table provenance for the wild-quadratic assembly -/

section QuadraticHighProvenance

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
  (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
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
  (hstrict : t + 1 < (data.twistData 1).conductor)
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (tau : NormCharacter F K) (htau : tau ≠ 1)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The exact simultaneous high-quadratic package specialized to the base
computational datum. -/
abbrev QuadraticHighPhaseSource := WildQuadraticHighProductData
  F K ht hres pi hpi hgen hdegree htpos
  (data.twistData 1) chiK data.baseAddChar psiK hF hK hminimal
  hstrict.le hchi hpsi tau htau gammaF hgammaF

/-- Transport the actual high-table norm-character phase only across the
proof-bearing quasi-character datum.  Its representative remains literal
`1`, and its denominator, conductor, and depth remain those of `Q`. -/
def highQuadraticTauPhaseForComputationalData
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2)) :
    LocalLamprechtPhaseData F (data.normCharacterData tau)
      data.baseAddChar := by
  have hdata : wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau =
      data.normCharacterData tau := by
    apply LocalQuasiCharData.ext_character F
    rw [wildQuadraticHighTauData, quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
  let sourcePhase := WildQuadraticHighProductData.tauPhase
    F K ht hres pi hpi hgen
    hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
    hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- Transport the selected high-table nontrivial twist phase to the
computational datum with the same character.  The stationary representative
and its essential correction unit are unchanged. -/
def highQuadraticTwistPhaseForComputationalData
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F (data.twistData tau) data.baseAddChar := by
  have hdata : wildQuadraticHighTwistData F K ht hres pi hpi hgen
      (data.twistData 1) tau = data.twistData tau := by
    apply LocalQuasiCharData.ext_character F
    rw [wildQuadraticHighTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  let sourcePhase := WildQuadraticHighProductData.twistPhase
    F K ht hres pi hpi hgen
    hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
    hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

def highQuadraticUpstairsPhaseSource
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    LocalLamprechtPhaseData K chiK psiK :=
  WildQuadraticHighProductData.upstairsPhase F K ht hres pi hpi hgen
    hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
    hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C

/-- Transport the high quadratic upstairs row only across equality of the
proof-bearing character data.  Its quotient representative, denominator,
conductor, and critical coordinate remain those selected by `Q`. -/
def highQuadraticUpstairsPhaseForComputationalData
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
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
    (highQuadraticUpstairsPhaseSource F K ht hres pi hpi hgen hdegree
      htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau
        gammaF hgammaF Q C)

def highQuadraticBasePhaseSource
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar :=
  WildQuadraticHighProductData.basePhase F K ht hres pi hpi hgen
    hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
    hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C

/-- The actual high upstairs row evaluates at the mapped common
denominator; in degree two this is the square of the base-character value. -/
theorem highQuadraticUpstairsPhase_admissibleFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).admissibleFactor =
      (globalChi gammaF : ℂ) * (globalChi gammaF : ℂ) := by
  unfold highQuadraticUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF, Q.parameters.commonDenominator⟩
  change LocalLamprechtPhaseData.admissibleFactor
    (localPhaseOfStationaryClass hK Gamma Q.upstairsRepresentative C) = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  rw [hchi, ContinuousQuasiChar.compNorm_apply,
    data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  have hnormMap :
      normUnits F K (Units.map (algebraMap F K) gammaF) = gammaF ^ 2 := by
    ext
    simp [hdegree]
  rw [hnormMap, map_pow]
  rw [pow_two]
  exact Units.val_mul _ _

/-- The actual high base row keeps the literal denominator `gammaF`. -/
theorem highQuadraticBasePhase_admissibleFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos data
      chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF hgammaF Q
        C).admissibleFactor = (globalChi gammaF : ℂ) := by
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨gammaF, hgammaF⟩
  change LocalLamprechtPhaseData.admissibleFactor
    (localPhaseOfStationaryClass hF Gamma Q.baseRepresentative C) = _
  rw [localPhaseOfStationaryClass_admissibleFactor,
    data.twistData_character]
  simp
  rfl

/-- The actual post-drop norm row uses `gammaF / cF`, not the old high
denominator. -/
theorem highQuadraticTauPhase_admissibleFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2)) :
    (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).admissibleFactor =
      (tau.1 (gammaF / Q.parameters.representatives.cF) : ℂ) := by
  unfold highQuadraticTauPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  let tauData := wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau
  let hTau := wildQuadraticHighTauDecomposition F K ht hres pi hpi hgen
    htpos tau htau
  let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨Q.parameters.representatives.gammaTau,
      Q.parameters.representatives.gammaTau_order⟩
  change LocalLamprechtPhaseData.admissibleFactor
    (localPhaseOfStationaryClass hTau Gamma Q.tauRepresentative C) = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  rw [show tauData.character = tau.1 by
    simp only [tauData, wildQuadraticHighTauData,
      quasiCharDataOfIsConductor_character]]
  change (tau.1 Q.parameters.representatives.gammaTau : ℂ) = _
  rfl

/-- The actual high twist row evaluates the full twisted character at the
unchanged high denominator. -/
theorem highQuadraticTwistPhase_admissibleFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).admissibleFactor =
      (tau.1 gammaF : ℂ) * (globalChi gammaF : ℂ) := by
  unfold highQuadraticTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  let twistData := wildQuadraticHighTwistData F K ht hres pi hpi hgen
    (data.twistData 1) tau
  let hTw := wildQuadraticHighTwistDecomposition F K ht hres pi hpi hgen
    (data.twistData 1) hF hminimal hstrict.le tau htau
  let hgammaTw := highParameter_wildQuadratic_twistDenominator F K ht hres
    pi hpi hgen (data.twistData 1) data.baseAddChar hminimal hstrict.le tau
      htau gammaF hgammaF
  let Gamma : AdmissibleGamma F twistData data.baseAddChar :=
    ⟨gammaF, hgammaTw⟩
  change LocalLamprechtPhaseData.admissibleFactor
    (localPhaseOfStationaryClass hTw Gamma Q.twistRepresentative C) = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  rw [wildQuadraticHighTwistData_character,
    data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  change (((tau.1 gammaF) * (globalChi gammaF) : ℂˣ) : ℂ) = _
  exact Units.val_mul _ _

/-- Positive additive value of the actual high upstairs row, displayed at
its selected numerator and mapped common denominator. -/
theorem highQuadraticUpstairsPhase_elementaryAdditiveFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).elementaryAdditiveFactor =
      (globalPsi
        (trace F K
          ((((Q.quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K) /
            algebraMap F K (gammaF : F))) : ℂ) := by
  calc
    _ = (highQuadraticUpstairsPhaseSource F K ht hres pi hpi hgen hdegree
        htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau
          gammaF hgammaF Q C).elementaryAdditiveFactor := by
      unfold highQuadraticUpstairsPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor _ _ _
    _ = _ := by
      let Gamma : AdmissibleGamma K chiK psiK :=
        ⟨Units.map (algebraMap F K) gammaF,
          Q.parameters.commonDenominator⟩
      change LocalLamprechtPhaseData.elementaryAdditiveFactor
        (localPhaseOfStationaryClass hK Gamma Q.upstairsRepresentative C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
      rw [hpsi, ContinuousAddChar.compTrace_apply,
        data.baseAddChar_character]
      rfl

/-- Positive additive value of the high base row at the literal selected
stationary numerator. -/
theorem highQuadraticBasePhase_elementaryAdditiveFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos data
      chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF hgammaF Q
        C).elementaryAdditiveFactor =
      (globalPsi
        (((((Q.quotientProduct.factors true : unitFiltration F 0) : Fˣ) : F) /
          (gammaF : F))) : ℂ) := by
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨gammaF, hgammaF⟩
  change LocalLamprechtPhaseData.elementaryAdditiveFactor
    (localPhaseOfStationaryClass hF Gamma Q.baseRepresentative C) = _
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor hF Gamma
      Q.baseRepresentative C,
    data.baseAddChar_character]
  rfl

/-- Positive additive value of the post-drop norm row.  Its representative
is literally one and its denominator is `gammaF/cF`. -/
theorem highQuadraticTauPhase_elementaryAdditiveFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2)) :
    (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).elementaryAdditiveFactor =
      (globalPsi
        (1 / (Q.parameters.representatives.gammaTau : F)) : ℂ) := by
  calc
    _ = (WildQuadraticHighProductData.tauPhase F K ht hres pi hpi hgen
        hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
          hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C).elementaryAdditiveFactor := by
      unfold highQuadraticTauPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor _ _ _
    _ = _ := by
      let tauData := wildQuadraticHighTauData F K ht hres pi hpi hgen tau
        htau
      let hTau := wildQuadraticHighTauDecomposition F K ht hres pi hpi hgen
        htpos tau htau
      let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
        ⟨Q.parameters.representatives.gammaTau,
          Q.parameters.representatives.gammaTau_order⟩
      change LocalLamprechtPhaseData.elementaryAdditiveFactor
        (localPhaseOfStationaryClass hTau Gamma Q.tauRepresentative C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
        data.baseAddChar_character]
      rfl

/-- Positive additive value of the selected high twist row, retaining its
actual break-unit-corrected numerator. -/
theorem highQuadraticTwistPhase_elementaryAdditiveFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).elementaryAdditiveFactor =
      (globalPsi
        (((((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) /
          (gammaF : F))) : ℂ) := by
  calc
    _ = (WildQuadraticHighProductData.twistPhase F K ht hres pi hpi hgen
        hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
          hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C).elementaryAdditiveFactor := by
      unfold highQuadraticTwistPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor _ _ _
    _ = _ := by
      let twistData := wildQuadraticHighTwistData F K ht hres pi hpi hgen
        (data.twistData 1) tau
      let hTw := wildQuadraticHighTwistDecomposition F K ht hres pi hpi hgen
        (data.twistData 1) hF hminimal hstrict.le tau htau
      let hgammaTw := highParameter_wildQuadratic_twistDenominator F K ht
        hres pi hpi hgen (data.twistData 1) data.baseAddChar hminimal
          hstrict.le tau htau gammaF hgammaF
      let Gamma : AdmissibleGamma F twistData data.baseAddChar :=
        ⟨gammaF, hgammaTw⟩
      change LocalLamprechtPhaseData.elementaryAdditiveFactor
        (localPhaseOfStationaryClass hTw Gamma Q.twistRepresentative C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
        data.baseAddChar_character]
      have hrep : (Q.twistRepresentative.representative : F) =
          (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) :=
        rfl
      rw [hrep]

/-- Inverse multiplicative value of the actual high upstairs row. -/
theorem highQuadraticUpstairsPhase_elementaryMultiplicativeFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).elementaryMultiplicativeFactor =
      (globalChi
        (normUnits F K
          (Q.quotientProduct.upstairs : Kˣ)) : ℂ)⁻¹ := by
  calc
    _ = (highQuadraticUpstairsPhaseSource F K ht hres pi hpi hgen hdegree
        htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau
          gammaF hgammaF Q C).elementaryMultiplicativeFactor := by
      unfold highQuadraticUpstairsPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor _ _ _
    _ = _ := by
      let Gamma : AdmissibleGamma K chiK psiK :=
        ⟨Units.map (algebraMap F K) gammaF,
          Q.parameters.commonDenominator⟩
      change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
        (localPhaseOfStationaryClass hK Gamma Q.upstairsRepresentative C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
      rw [hchi, ContinuousQuasiChar.compNorm_apply,
        data.twistData_character]
      simp
      have hunit : Q.upstairsRepresentative.unit =
          (Q.quotientProduct.upstairs : Kˣ) := by
        apply Units.ext
        rw [StationaryClassRepresentative.coe_unit]
        rfl
      rw [hunit]

/-- Inverse multiplicative value of the actual high base row. -/
theorem highQuadraticBasePhase_elementaryMultiplicativeFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos data
      chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF hgammaF Q
        C).elementaryMultiplicativeFactor =
      (globalChi
        (Q.quotientProduct.factors true : Fˣ) : ℂ)⁻¹ := by
  let Gamma : AdmissibleGamma F (data.twistData 1) data.baseAddChar :=
    ⟨gammaF, hgammaF⟩
  change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
    (localPhaseOfStationaryClass hF Gamma Q.baseRepresentative C) = _
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor hF Gamma
      Q.baseRepresentative C,
    data.twistData_character]
  simp
  have hunit : Q.baseRepresentative.unit =
      (Q.quotientProduct.factors true : Fˣ) := by
    apply Units.ext
    rw [StationaryClassRepresentative.coe_unit]
    rfl
  rw [hunit]

/-- The post-drop norm row's selected representative is one, so its inverse
multiplicative elementary value is one. -/
theorem highQuadraticTauPhase_elementaryMultiplicativeFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2)) :
    (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).elementaryMultiplicativeFactor = 1 := by
  calc
    _ = (WildQuadraticHighProductData.tauPhase F K ht hres pi hpi hgen
        hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
          hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C).elementaryMultiplicativeFactor := by
      unfold highQuadraticTauPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor _ _ _
    _ = _ := by
      let tauData := wildQuadraticHighTauData F K ht hres pi hpi hgen tau
        htau
      let hTau := wildQuadraticHighTauDecomposition F K ht hres pi hpi hgen
        htpos tau htau
      let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
        ⟨Q.parameters.representatives.gammaTau,
          Q.parameters.representatives.gammaTau_order⟩
      change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
        (localPhaseOfStationaryClass hTau Gamma Q.tauRepresentative C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
      have hunit : Q.tauRepresentative.unit = (1 : Fˣ) := by
        apply Units.ext
        rw [StationaryClassRepresentative.coe_unit]
        rfl
      rw [hunit]
      simp

/-- Inverse multiplicative value of the selected high twist row, with the
norm character and base character kept as separate factors. -/
theorem highQuadraticTwistPhase_elementaryMultiplicativeFactor
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q C).elementaryMultiplicativeFactor =
      ((tau.1 (Q.quotientProduct.factors false : Fˣ) : ℂ) *
        (globalChi (Q.quotientProduct.factors false : Fˣ) : ℂ))⁻¹ := by
  calc
    _ = (WildQuadraticHighProductData.twistPhase F K ht hres pi hpi hgen
        hdegree htpos (data.twistData 1) chiK data.baseAddChar psiK hF hK
          hminimal hstrict.le hchi hpsi tau htau gammaF hgammaF Q C).elementaryMultiplicativeFactor := by
      unfold highQuadraticTwistPhaseForComputationalData
      exact LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor _ _ _
    _ = _ := by
      let twistData := wildQuadraticHighTwistData F K ht hres pi hpi hgen
        (data.twistData 1) tau
      let hTw := wildQuadraticHighTwistDecomposition F K ht hres pi hpi hgen
        (data.twistData 1) hF hminimal hstrict.le tau htau
      let hgammaTw := highParameter_wildQuadratic_twistDenominator F K ht
        hres pi hpi hgen (data.twistData 1) data.baseAddChar hminimal
          hstrict.le tau htau gammaF hgammaF
      let Gamma : AdmissibleGamma F twistData data.baseAddChar :=
        ⟨gammaF, hgammaTw⟩
      change LocalLamprechtPhaseData.elementaryMultiplicativeFactor
        (localPhaseOfStationaryClass hTw Gamma Q.twistRepresentative C) = _
      rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
      rw [wildQuadraticHighTwistData_character,
        data.twistData_character]
      simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
        ContinuousQuasiChar.one_apply, one_mul, Units.val_mul]
      have hunit : Q.twistRepresentative.unit =
          (Q.quotientProduct.factors false : Fˣ) := by
        apply Units.ext
        rw [StationaryClassRepresentative.coe_unit]
        rfl
      rw [hunit]

/-- Exact field-level additive argument supplied by the four high-table
representatives.  No additive character or elementary product has yet been
evaluated in this identity. -/
theorem highQuadratic_additiveArgument_eq
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF) :
    trace F K
        ((((Q.quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K) /
          algebraMap F K (gammaF : F)) +
        1 / (Q.parameters.representatives.gammaTau : F) =
      -(((Q.parameters.representatives.cF / gammaF : Fˣ) : F)) *
          trace F K (Q.parameters.representatives.u : K) +
        (((Q.quotientProduct.factors true : unitFiltration F 0) : Fˣ) : F) /
            (gammaF : F) +
        (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) /
            (gammaF : F) := by
  let R := Q.parameters.representatives
  have htraceScalar (a : F) (z : K) :
      trace F K (algebraMap F K a * z) = a * trace F K z := by
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul a z
  have hup :
      (((Q.quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K) /
          algebraMap F K (gammaF : F) =
        algebraMap F K (((R.cF / gammaF : Fˣ) : F)) *
          (algebraMap F K (R.n : F) - (R.u : K)) := by
    rw [Q.upstairs_formula, R.betaK_eq_cF_mul_sub]
    simp only [Units.val_div_eq_div_val, map_div]
    field_simp [Units.ne_zero gammaF]
    rw [map_div₀ (algebraMap F K)]
    have hgammaMap : algebraMap F K (gammaF : F) ≠ 0 := by
      simpa using (algebraMap F K).injective.ne (Units.ne_zero gammaF)
    field_simp [hgammaMap] <;> ring
  have hbase :
      (((Q.quotientProduct.factors true : unitFiltration F 0) : Fˣ) : F) =
        (R.cF : F) * (R.n : F) := by
    rw [Q.beta_factor_formula]
    exact congrArg Units.val R.cF_mul_n.symm
  have htwist :
      (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) =
        (R.cF : F) * ((R.n : F) + 1) := by
    rw [Q.twist_factor_formula, R.betaTwist_eq_cF_mul_add_one]
  rw [hup, htraceScalar, map_sub, trace_algebraMap, hdegree, hbase, htwist]
  simp only [two_nsmul, WildQuadraticHighRepresentatives.gammaTau,
    Units.val_div_eq_div_val]
  field_simp [Units.ne_zero gammaF, Units.ne_zero R.cF]
  ring

/-- The first raw ratio, specialized to the actual high representatives,
is an equality of field units before applying the base character. -/
theorem highQuadratic_zZero_mul_rows_eq_norm
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : QuadraticRawRatioCoordinates F K
      (Q.parameters.representatives.u : K)
      Q.parameters.representatives.n) :
    C.zZero * (Q.quotientProduct.factors true : Fˣ) *
        (Q.quotientProduct.factors false : Fˣ) =
      normUnits F K (Q.quotientProduct.upstairs : Kˣ) := by
  let R := Q.parameters.representatives
  apply Units.ext
  simp only [Units.val_mul, coe_normUnits]
  rw [Q.upstairs_formula, R.betaK_eq_cF_mul_sub, map_mul,
    norm_algebraMap, hdegree, C.norm_sub_eq,
    Q.beta_factor_formula, Q.twist_factor_formula,
    R.betaTwist_eq_cF_mul_add_one]
  have hbase := congrArg Units.val R.cF_mul_n
  change (R.cF : F) * (R.n : F) = (R.beta : F) at hbase
  rw [← hbase]
  ring

/-- The second raw ratio says that `z1` times the actual twist numerator is
`cF` times a genuine norm.  This is the precise source of the high scalar
`tau(cF)`. -/
theorem highQuadratic_zOne_mul_twist_eq_cF_mul_norm
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : QuadraticRawRatioCoordinates F K
      (Q.parameters.representatives.u : K)
      Q.parameters.representatives.n) :
    C.zOne * (Q.quotientProduct.factors false : Fˣ) =
      Q.parameters.representatives.cF *
        normUnits F K C.oneAddUUnit := by
  let R := Q.parameters.representatives
  apply Units.ext
  simp only [Units.val_mul, coe_normUnits, C.coe_oneAddUUnit]
  rw [Q.twist_factor_formula, R.betaTwist_eq_cF_mul_add_one,
    C.norm_one_add_eq]
  ring

/-- The two raw unit ratios imply the multiplicative-character correction
with the high scalar in its positive orientation. -/
theorem highQuadratic_multiplicativeRatio_eq
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (C : QuadraticRawRatioCoordinates F K
      (Q.parameters.representatives.u : K)
      Q.parameters.representatives.n) :
    (globalChi (normUnits F K
        (Q.quotientProduct.upstairs : Kˣ)) : ℂ)⁻¹ =
      (tau.1 Q.parameters.representatives.cF : ℂ) *
        (globalChi C.zZero : ℂ)⁻¹ *
          (tau.1 C.zOne : ℂ)⁻¹ *
            ((globalChi (Q.quotientProduct.factors true : Fˣ) : ℂ)⁻¹ *
              (((tau.1 (Q.quotientProduct.factors false : Fˣ) : ℂ) *
                (globalChi
                  (Q.quotientProduct.factors false : Fˣ) : ℂ))⁻¹)) := by
  have hzUnits := highQuadratic_zZero_mul_rows_eq_norm F K ht hres pi hpi
    hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
      htau gammaF hgammaF Q C
  have hoUnits := highQuadratic_zOne_mul_twist_eq_cF_mul_norm F K ht hres pi
    hpi hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi
      tau htau gammaF hgammaF Q C
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
  rw [hnormC, mul_one] at ho
  rw [← hz]
  field_simp [ContinuousQuasiChar.apply_ne_zero]
  exact ho

/-- The positive additive numerator identity is derived from the four actual
high stationary rows and their literal field arguments. -/
theorem highQuadratic_additiveNumerator_eq_of_actual_rows
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (Ctau : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2))
    (CTwist : LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos
        data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
          hgammaF Q CBase))
    (hNormTau : D.normCharacter tau = LocalPhaseData.stationary
      (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q Ctau))
    (hTwistTau : D.twist tau = LocalPhaseData.stationary
      (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CTwist))
    (indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D)
    (hindex : indexing.tau = tau) :
    D.elementaryAdditiveNumerator =
      (globalPsi
        (-(((Q.parameters.representatives.cF / gammaF : Fˣ) : F)) *
          trace F K (Q.parameters.representatives.u : K)) : ℂ) *
        D.elementaryAdditiveDenominator := by
  rw [ExactQuadraticPhaseAssembly.elementaryAdditiveNumerator_eq_two_actual_rows indexing,
    ExactQuadraticPhaseAssembly.elementaryAdditiveDenominator_eq_two_actual_rows indexing,
    hindex]
  rw [hExtension, hNormTau, hBase, hTwistTau]
  simp only [LocalPhaseData.elementaryAdditiveFactor]
  rw [highQuadraticUpstairsPhase_elementaryAdditiveFactor F K ht hres pi hpi
    hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
      htau gammaF hgammaF Q CUp]
  rw [highQuadraticTauPhase_elementaryAdditiveFactor F K ht hres pi hpi hgen
    hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau
      gammaF hgammaF Q Ctau]
  rw [highQuadraticBasePhase_elementaryAdditiveFactor F K ht hres pi hpi hgen
    hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau
      gammaF hgammaF Q CBase]
  rw [highQuadraticTwistPhase_elementaryAdditiveFactor F K ht hres pi hpi
    hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
      htau gammaF hgammaF Q CTwist]
  have hadd (a b : F) :
      (globalPsi a : ℂ) * (globalPsi b : ℂ) =
        (globalPsi (a + b) : ℂ) := by
    exact (congrArg (Units.val : ℂˣ → ℂ)
      (ContinuousAddChar.map_add_eq_mul globalPsi a b)).symm
  rw [hadd, hadd, hadd]
  congr 2
  rw [highQuadratic_additiveArgument_eq F K ht hres pi hpi hgen hdegree
    htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
      hgammaF Q]
  ring

/-- The inverse multiplicative numerator identity is derived from the same
four actual high rows and the two raw field ratios. -/
theorem highQuadratic_multiplicativeNumerator_eq_of_actual_rows
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (Ctau : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2))
    (CTwist : LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos
        data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
          hgammaF Q CBase))
    (hNormTau : D.normCharacter tau = LocalPhaseData.stationary
      (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q Ctau))
    (hTwistTau : D.twist tau = LocalPhaseData.stationary
      (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CTwist))
    (indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D)
    (hindex : indexing.tau = tau)
    (C : QuadraticRawRatioCoordinates F K
      (Q.parameters.representatives.u : K)
      Q.parameters.representatives.n) :
    D.elementaryMultiplicativeNumerator =
      (tau.1 Q.parameters.representatives.cF : ℂ) *
        (globalChi C.zZero : ℂ)⁻¹ * (tau.1 C.zOne : ℂ)⁻¹ *
          D.elementaryMultiplicativeDenominator := by
  rw [ExactQuadraticPhaseAssembly.elementaryMultiplicativeNumerator_eq_two_actual_rows indexing,
    ExactQuadraticPhaseAssembly.elementaryMultiplicativeDenominator_eq_two_actual_rows indexing,
    hindex]
  rw [hExtension, hNormTau, hBase, hTwistTau]
  simp only [LocalPhaseData.elementaryMultiplicativeFactor]
  rw [highQuadraticUpstairsPhase_elementaryMultiplicativeFactor F K ht hres
    pi hpi hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi
      hpsi tau htau gammaF hgammaF Q CUp]
  rw [highQuadraticTauPhase_elementaryMultiplicativeFactor F K ht hres pi
    hpi hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi
      tau htau gammaF hgammaF Q Ctau]
  rw [highQuadraticBasePhase_elementaryMultiplicativeFactor F K ht hres pi
    hpi hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi
      tau htau gammaF hgammaF Q CBase]
  rw [highQuadraticTwistPhase_elementaryMultiplicativeFactor F K ht hres pi
    hpi hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi
      tau htau gammaF hgammaF Q CTwist]
  rw [highQuadratic_multiplicativeRatio_eq F K ht hres pi hpi hgen hdegree
    htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
      hgammaF Q C]
  ring

/-- A wild-quadratic assembly whose break unit, stationary scale, selected
numerators, and norm/trace ratios are all tied definitionally to one
simultaneous high-table package. -/
structure QBackedExactQuadraticAssembly
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF) where
  assembly : ExactQuadraticPhaseAssembly F K globalChi globalPsi data D
    (t := t) (m := (data.twistData 1).conductor)
  upstairsCriticalCoordinate : LamprechtCriticalCoordinate K dK epsilonK
  baseCriticalCoordinate : LamprechtCriticalCoordinate F d epsilon
  tauCriticalCoordinate : LamprechtCriticalCoordinate F
    (wildQuadraticHighNormPrecision t) ((t + 1) % 2)
  twistCriticalCoordinate : LamprechtCriticalCoordinate F d epsilon
  extensionPhase : D.extension = LocalPhaseData.stationary
    (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF Q upstairsCriticalCoordinate)
  basePhase : D.twist 1 = LocalPhaseData.stationary
    (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF Q baseCriticalCoordinate)
  nontrivialNormPhase : D.normCharacter tau = LocalPhaseData.stationary
    (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q tauCriticalCoordinate)
  nontrivialTwistPhase : D.twist tau = LocalPhaseData.stationary
    (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q twistCriticalCoordinate)
  indexing_tau : assembly.indexing.tau = tau
  scalarCorrection_source : assembly.scalarCorrection =
    tau.1 Q.parameters.representatives.cF
  breakUnit_source : assembly.breakUnit = Q.parameters.representatives.delta
  stationaryScale_source : assembly.stationaryScale =
    ((normUnits F K Q.parameters.representatives.alpha1 : Fˣ) : F)
  baseNumerator_source : assembly.baseStationaryNumerator =
    (Q.parameters.representatives.beta : F)
  twistNumerator_source : assembly.twistStationaryNumerator =
    (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F)
  ratio_u_source : assembly.u = (Q.parameters.representatives.u : K)
  ratio_n_source : assembly.n = (Q.parameters.representatives.n : F)

set_option maxHeartbeats 4000000 in
/-- Legacy high-backed constructor.  It derives endpoint and admissible
quotients from the actual rows but accepts the two already-assembled
elementary numerator identities.  New code should use
`qBackedExactQuadraticAssemblyFromActualRows`. -/
def qBackedExactQuadraticAssembly
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (Ctau : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2))
    (CTwist : LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension =
      (LocalPhaseData.stationary
        (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi
          hgen hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi
            tau htau gammaF hgammaF Q CUp)))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos
        data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
          hgammaF Q CBase))
    (hNormTau : D.normCharacter tau = LocalPhaseData.stationary
      (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q Ctau))
    (hTwistTau : D.twist tau = LocalPhaseData.stationary
      (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CTwist))
    (index : Bool ≃ NormCharacter F K)
    (index_true : index true = 1) (index_false : index false = tau)
    (zZero zOne : Fˣ) (x y : F)
    (zZero_eq : (zZero : F) = 1 + x)
    (zOne_eq : (zOne : F) = 1 + y)
    (additiveNumerator_eq : D.elementaryAdditiveNumerator =
      (globalPsi
        (-(((Q.parameters.representatives.cF / gammaF : Fˣ) : F)) *
          trace F K (Q.parameters.representatives.u : K)) : ℂ) *
        D.elementaryAdditiveDenominator)
    (multiplicativeNumerator_eq : D.elementaryMultiplicativeNumerator =
      (tau.1 Q.parameters.representatives.cF : ℂ) *
        (globalChi zZero : ℂ)⁻¹ * (tau.1 zOne : ℂ)⁻¹ *
          D.elementaryMultiplicativeDenominator) :
    QBackedExactQuadraticAssembly (F := F) (K := K) (data := data) (D := D)
      (chiK := chiK) (psiK := psiK) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (hdegree := hdegree) (htpos := htpos)
      (hF := hF) (hK := hK) (hminimal := hminimal) (hstrict := hstrict)
      (hchi := hchi) (hpsi := hpsi) (tau := tau) (htau := htau)
      (gammaF := gammaF) (hgammaF := hgammaF) Q := by
  let indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D :=
    { tau := tau
      index := index
      index_true := index_true
      index_false := index_false }
  let R := Q.parameters.representatives
  let coeff : F := ((R.cF / gammaF : Fˣ) : F)
  let u : K := (R.u : K)
  let n : F := (R.n : F)
  let s : F := trace F K u
  let X : F := s + n * x + y
  have hEndpoint : D.factors.endpoint = 1 := by
    apply ExactQuadraticPhaseAssembly.endpointFactor_eq_one_of_quadratic_actual_rows
      indexing
    · exact ⟨_, hExtension⟩
    · simpa only [indexing] using
        (⟨_, hNormTau⟩ : ∃ S, D.normCharacter tau =
          LocalPhaseData.stationary S)
    · exact ⟨_, hBase⟩
    · simpa only [indexing] using
        (⟨_, hTwistTau⟩ : ∃ S, D.twist tau =
          LocalPhaseData.stationary S)
  have hAdmissibleFactor : D.factors.admissibleCharacter =
      (tau.1 R.cF : ℂ)⁻¹ := by
    rw [ExactQuadraticPhaseAssembly.admissibleFactor_eq_four_actual_rows
      indexing]
    change
      (D.extension.admissibleFactor *
          (D.normCharacter tau).admissibleFactor) /
        ((D.twist 1).admissibleFactor *
          (D.twist tau).admissibleFactor) = _
    rw [hExtension, hNormTau, hBase, hTwistTau]
    simp only [LocalPhaseData.admissibleFactor]
    rw [highQuadraticUpstairsPhase_admissibleFactor F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q CUp]
    rw [highQuadraticTauPhase_admissibleFactor F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q Ctau]
    rw [highQuadraticBasePhase_admissibleFactor F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q CBase]
    rw [highQuadraticTwistPhase_admissibleFactor F K ht hres pi hpi hgen
      hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q CTwist]
    have htauDiv := congrArg (Units.val : ℂˣ → ℂ)
      (map_div tau.1 gammaF R.cF)
    simp only [Units.val_div_eq_div_val] at htauDiv
    rw [htauDiv]
    field_simp [ContinuousQuasiChar.apply_ne_zero]
  have hAdmissibleNumerator : D.admissibleNumerator =
      (tau.1 R.cF : ℂ)⁻¹ * D.admissibleDenominator := by
    have h := hAdmissibleFactor
    simp only [FirstMainPhaseData.factors] at h
    exact (div_eq_iff D.admissibleDenominator_ne_zero).mp h
  let A : ExactQuadraticPhaseAssembly F K globalChi globalPsi data D
      (t := t) (m := (data.twistData 1).conductor) :=
    { baseData := data.twistData 1
      baseData_eq := rfl
      baseCharacter := by
        rw [data.twistData_character]
        ext z
        simp
      baseConductor := rfl
      parameterRange := .high hstrict
      indexing := indexing
      A := coeff
      u := u
      n := n
      norm_u := by
        simpa only [u, n, coe_normUnits] using
          congrArg Units.val R.norm_u_eq_n
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
      breakUnit := R.delta
      stationaryScale := ((normUnits F K R.alpha1 : Fˣ) : F)
      baseStationaryNumerator := (R.beta : F)
      twistStationaryNumerator :=
        (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F)
      twistStationaryNumerator_eq := by
        change
          (((Q.quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) =
            (R.beta : F) + (((normUnits F K R.alpha1) *
              (R.delta : Fˣ) : Fˣ) : F)
        exact Q.correction_unit_retained
      scalarCorrection := tau.1 R.cF
      endpointFactor_eq := hEndpoint
      admissibleNumerator_eq := hAdmissibleNumerator
      additiveNumerator_eq := by
        simpa only [coeff, s, u] using additiveNumerator_eq
      multiplicativeNumerator_eq := by
        simpa only [indexing] using multiplicativeNumerator_eq }
  exact
    { assembly := A
      upstairsCriticalCoordinate := CUp
      baseCriticalCoordinate := CBase
      tauCriticalCoordinate := Ctau
      twistCriticalCoordinate := CTwist
      extensionPhase := hExtension
      basePhase := hBase
      nontrivialNormPhase := hNormTau
      nontrivialTwistPhase := hTwistTau
      indexing_tau := rfl
      scalarCorrection_source := rfl
      breakUnit_source := rfl
      stationaryScale_source := rfl
      baseNumerator_source := rfl
      twistNumerator_source := rfl
      ratio_u_source := rfl
      ratio_n_source := rfl }

set_option maxHeartbeats 4000000 in
/-- Preferred high-table quadratic constructor.  Its only elementary scalar
input is the pair of literal field norm ratios `C`; both aggregate elementary
numerator identities are proved from the four actual stationary rows. -/
def qBackedExactQuadraticAssemblyFromActualRows
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (Ctau : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2))
    (CTwist : LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highQuadraticUpstairsPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree htpos
        data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
          hgammaF Q CBase))
    (hNormTau : D.normCharacter tau = LocalPhaseData.stationary
      (highQuadraticTauPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q Ctau))
    (hTwistTau : D.twist tau = LocalPhaseData.stationary
      (highQuadraticTwistPhaseForComputationalData F K ht hres pi hpi hgen
        hdegree htpos data chiK psiK hF hK hminimal hstrict hchi hpsi tau
          htau gammaF hgammaF Q CTwist))
    (index : Bool ≃ NormCharacter F K)
    (index_true : index true = 1) (index_false : index false = tau)
    (C : QuadraticRawRatioCoordinates F K
      (Q.parameters.representatives.u : K)
      Q.parameters.representatives.n) :
    QBackedExactQuadraticAssembly (F := F) (K := K) (data := data) (D := D)
      (chiK := chiK) (psiK := psiK) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (hdegree := hdegree) (htpos := htpos)
      (hF := hF) (hK := hK) (hminimal := hminimal) (hstrict := hstrict)
      (hchi := hchi) (hpsi := hpsi) (tau := tau) (htau := htau)
      (gammaF := gammaF) (hgammaF := hgammaF) Q := by
  let indexing : QuadraticCriticalIndexing F K globalChi globalPsi data D :=
    { tau := tau
      index := index
      index_true := index_true
      index_false := index_false }
  apply qBackedExactQuadraticAssembly F K ht hres pi hpi hgen hdegree htpos
    data D chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
      hgammaF Q CUp CBase Ctau CTwist hExtension hBase hNormTau hTwistTau
      index index_true index_false C.zZero C.zOne C.x C.y C.zZero_eq
        C.zOne_eq
  · exact highQuadratic_additiveNumerator_eq_of_actual_rows F K ht hres pi
      hpi hgen hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi
        hpsi tau htau gammaF hgammaF Q CUp CBase Ctau CTwist hExtension hBase
          hNormTau hTwistTau indexing rfl
  · exact highQuadratic_multiplicativeNumerator_eq_of_actual_rows F K ht
      hres pi hpi hgen hdegree htpos data D chiK psiK hF hK hminimal hstrict
        hchi hpsi tau htau gammaF hgammaF Q CUp CBase Ctau CTwist hExtension
          hBase hNormTau hTwistTau indexing rfl C

/-- The complete non-finite quadratic correction over one Q-backed
assembly.  The denominator condition is derived below from the same `Q`;
the fields retain the two literal ratios and their separate character
linearizations. -/
structure QBackedQuadraticCompleteCorrection
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (B : QBackedExactQuadraticAssembly (F := F) (K := K)
      (data := data) (D := D) (chiK := chiK) (psiK := psiK)
      (ht := ht) (hres := hres) (pi := pi) (hpi := hpi) (hgen := hgen)
      (hdegree := hdegree) (htpos := htpos) (hF := hF) (hK := hK)
      (hminimal := hminimal) (hstrict := hstrict) (hchi := hchi)
      (hpsi := hpsi) (tau := tau) (htau := htau) (gammaF := gammaF)
      (hgammaF := hgammaF) Q) : Prop where
  zZero_ratio : (B.assembly.zZero : F) =
    norm F K (1 + B.assembly.dualRatio) / (1 + B.assembly.n)
  zOne_ratio : (B.assembly.zOne : F) =
    norm F K (1 + B.assembly.u) / (1 + B.assembly.n)
  chiLinearization : globalChi B.assembly.zZero =
    globalPsi (B.assembly.A * B.assembly.n * B.assembly.x)
  tauLinearization : B.assembly.indexing.tau.1 B.assembly.zOne =
    globalPsi (B.assembly.A * B.assembly.y)

namespace QBackedQuadraticCompleteCorrection

/-- The denominator `1+n` is the high table's proved denominator,
transported along the sourced value of `n`; it is not a new hypothesis. -/
theorem one_add_n_ne_zero
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (B : QBackedExactQuadraticAssembly (F := F) (K := K)
      (data := data) (D := D) (chiK := chiK) (psiK := psiK)
      (ht := ht) (hres := hres) (pi := pi) (hpi := hpi) (hgen := hgen)
      (hdegree := hdegree) (htpos := htpos) (hF := hF) (hK := hK)
      (hminimal := hminimal) (hstrict := hstrict) (hchi := hchi)
      (hpsi := hpsi) (tau := tau) (htau := htau) (gammaF := gammaF)
      (hgammaF := hgammaF) Q)
    (_C : QBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q B) :
    1 + B.assembly.n ≠ 0 := by
  rw [B.ratio_n_source]
  exact Q.parameters.denominator_ne_zero

def toCompleteCorrectionData
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (B : QBackedExactQuadraticAssembly (F := F) (K := K)
      (data := data) (D := D) (chiK := chiK) (psiK := psiK)
      (ht := ht) (hres := hres) (pi := pi) (hpi := hpi) (hgen := hgen)
      (hdegree := hdegree) (htpos := htpos) (hF := hF) (hK := hK)
      (hminimal := hminimal) (hstrict := hstrict) (hchi := hchi)
      (hpsi := hpsi) (tau := tau) (htau := htau) (gammaF := gammaF)
      (hgammaF := hgammaF) Q)
    (C : QBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q B) :
    B.assembly.CompleteCorrectionData where
  one_add_n_ne_zero := C.one_add_n_ne_zero F K ht hres pi hpi hgen
    hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi hpsi tau
      htau gammaF hgammaF Q B
  zZero_ratio := C.zZero_ratio
  zOne_ratio := C.zOne_ratio
  chiLinearization := C.chiLinearization
  tauLinearization := C.tauLinearization

theorem errorTerm_eq_residual_mul_phase
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF)
    (B : QBackedExactQuadraticAssembly (F := F) (K := K)
      (data := data) (D := D) (chiK := chiK) (psiK := psiK)
      (ht := ht) (hres := hres) (pi := pi) (hpi := hpi) (hgen := hgen)
      (hdegree := hdegree) (htpos := htpos) (hF := hF) (hK := hK)
      (hminimal := hminimal) (hstrict := hstrict) (hchi := hchi)
      (hpsi := hpsi) (tau := tau) (htau := htau) (gammaF := gammaF)
      (hgammaF := hgammaF) Q)
    (C : QBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q B) :
    errorTerm F K DeltaF DeltaK globalChi globalPsi =
      B.assembly.residualHasseQuotient *
        (globalPsi (-B.assembly.A * B.assembly.X) : ℂ) :=
  (C.toCompleteCorrectionData F K ht hres pi hpi hgen hdegree htpos data D
    chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF hgammaF Q
      B).errorTerm_eq_residual_mul_phase hDeltaF hDeltaK B.assembly

/-- Compact eliminator type for a fully sourced high quadratic assembly and
its already-proved complete correction data. -/
def QBackedQuadraticCompleteResultEliminator : Prop :=
  ∀ {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K},
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF) →
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) →
    (Q : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree htpos
      data chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
        hgammaF) →
    (B : QBackedExactQuadraticAssembly (F := F) (K := K)
      (data := data) (D := D) (chiK := chiK) (psiK := psiK)
      (ht := ht) (hres := hres) (pi := pi) (hpi := hpi) (hgen := hgen)
      (hdegree := hdegree) (htpos := htpos) (hF := hF) (hK := hK)
      (hminimal := hminimal) (hstrict := hstrict) (hchi := hchi)
      (hpsi := hpsi) (tau := tau) (htau := htau) (gammaF := gammaF)
      (hgammaF := hgammaF) Q) →
    (C : QBackedQuadraticCompleteCorrection F K ht hres pi hpi hgen
      hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF Q B) →
    (C.toCompleteCorrectionData F K ht hres pi hpi hgen hdegree htpos data D
      chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF hgammaF Q
        B).CompleteResult hDeltaF hDeltaK B.assembly

/-- The high quadratic complete-result eliminator is inhabited by the
already-proved generic structured result. -/
theorem qBackedQuadraticCompleteResult :
    QBackedQuadraticCompleteResultEliminator F K ht hres pi hpi hgen
      hdegree htpos data D chiK psiK hF hK hminimal hstrict hchi hpsi tau
        htau gammaF hgammaF := by
  intro DeltaF DeltaK hDeltaF hDeltaK Q B C
  exact (C.toCompleteCorrectionData F K ht hres pi hpi hgen hdegree htpos
    data D chiK psiK hF hK hminimal hstrict hchi hpsi tau htau gammaF
      hgammaF Q B).completeResult hDeltaF hDeltaK B.assembly

end QBackedQuadraticCompleteCorrection

end QuadraticHighProvenance

end

end LanglandsFirstMainLemma
