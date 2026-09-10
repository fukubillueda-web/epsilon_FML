import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.AssemblyInputs
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ResidualTransport

/-!
# High-table-backed odd-prime assembly

This module contains the exact high-table-backed odd-prime assembly up
to, but not including, the named residual-row API.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## High-table-backed exact odd assembly -/

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

/-- One simultaneous high-product witness supplies the extension row and
all twist rows at their actual decompositions. -/
abbrev HighOddPhaseSource := OddIntermediateHighProductData
  F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF

/-- The preferred high source: norm rows and extension/twist product rows
are obtained from one destructuring of the high parameter theorem. -/
abbrev HighOddSimultaneousSource := HighOddCoherentPhaseSource
  F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF

def highOddUpstairsPhaseSource
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    LocalLamprechtPhaseData K chiK psiK :=
  OddIntermediateHighProductData.upstairsPhase
    F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF
        Q C

/-- Transport the actual high-table upstairs phase to the proof-bearing
extension data used by the global computational package.  The stationary
representative and denominator are unchanged. -/
def highOddUpstairsPhaseForComputationalData
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
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
    (highOddUpstairsPhaseSource F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q C)

/-- Transport a `Q.factorPhase` only across the proof-bearing twist datum;
the representative and actual factor decomposition remain those in `Q`. -/
def highOddTwistPhaseForComputationalData
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))) data.baseAddChar := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  have hdata : ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen (data.twistData 1) mu =
      data.twistData mu := by
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  let sourcePhase := OddIntermediateHighProductData.factorPhase
    F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF
        Q j C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- The manuscript's normalized high twist numerator
`N(beta1) + [j] N(alpha1) = N(alpha1) (n + [j])`.  This is the linear
representative congruent to the exact norm selected by the high product. -/
noncomputable def highOddLinearTwistValue
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) : F :=
  norm F K (Q.beta1 : K) +
    oddNormAllIndexScalar F K ht hres pi hpi hgen htpos j *
      norm F K (Q.alpha1 : K)

/-- The high product's proved depth-`d` congruence puts the linear twist
value in the integral lattice. -/
theorem highOddLinearTwistValue_mem
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j ∈
        lattice F 0 := by
  have hcong := Q.factor_linear_congruence j
  have hdiff :
      (((Q.quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F) -
        highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
            j ∈ lattice F (d : ℤ) := by
    simpa only [highOddLinearTwistValue, oddNormAllIndexScalar] using
      ((congruentAtDepth_iff_sub_mem_lattice F (d : ℤ) _ _).1 hcong)
  have hdiff0 := lattice_antitone F (Int.natCast_nonneg d) hdiff
  have hexact :
      (((Q.quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F) ∈
        lattice F 0 :=
    unitFiltrationZeroIntegral F (Q.quotientProduct.factors j)
  have hsub := sub_mem_lattice F hexact hdiff0
  convert hsub using 1 <;> ring

/-- Replace the exact-norm high twist representative by its congruent
linear table representative at the same actual conductor and quotient
depth. -/
noncomputable def highOddLinearTwistRepresentative
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen (data.twistData 1) mu
    StationaryClassRepresentative F twist data.baseAddChar
      (Q.factorDecomposition j) gammaF (Q.factorDenominator j) := by
  dsimp only
  let linear : lattice F 0 :=
    ⟨highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j,
      highOddLinearTwistValue_mem F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j⟩
  refine StationaryClassRepresentative.ofCoefficientRepresentative linear ?_
  calc
    latticeQuotientMk F (Int.natCast_nonneg d) linear =
        latticeQuotientMk F (Int.natCast_nonneg d)
          ⟨(((Q.quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F),
            unitFiltrationZeroIntegral F
              (Q.quotientProduct.factors j)⟩ := by
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        (Int.natCast_nonneg d)).2
      simpa only [linear, highOddLinearTwistValue,
        oddNormAllIndexScalar] using (Q.factor_linear_congruence j).symm
    _ = stationaryCoefficientClass F
        (ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
          (data.twistData 1)
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j))) data.baseAddChar
          (Q.factorDecomposition j) gammaF (Q.factorDenominator j) :=
      Q.factor_class j

/-- Unit carried by the linear high twist representative. -/
noncomputable def highOddLinearTwistUnit
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) : Fˣ :=
  (highOddLinearTwistRepresentative F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j).unit

@[simp] theorem highOddLinearTwistUnit_coe
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j : F) =
      highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j := rfl

/-- The preferred high twist phase inserts the linear table representative;
in odd conductor this transports the elementary value and Hasse phase
together. -/
def highOddLinearTwistPhaseForComputationalData
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    LocalLamprechtPhaseData F
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))) data.baseAddChar := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  let twist := ramifiedNormCharacterOrbitTwistData
    F K ht hres pi hpi hgen (data.twistData 1) mu
  have hdata : twist = data.twistData mu := by
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  let Gamma : AdmissibleGamma F twist data.baseAddChar :=
    ⟨gammaF, Q.factorDenominator j⟩
  let sourcePhase := localPhaseOfStationaryClass
    (Q.factorDecomposition j) Gamma
      (highOddLinearTwistRepresentative F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF Q j) C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- Coherence between the independently Prop-produced high norm-row and
high product witnesses.  Both the subcritical coefficient and its exact
norm representative must come from the same parameter choice before the
odd correction coordinate is assembled. -/
structure HighOddSourceCoherence
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) : Prop where
  alpha_eq : S.alpha = Q.alpha
  alpha1_eq : S.alpha1 = Q.alpha1

/-- The exact coefficient `A=N(alpha1)/gammaF` from the coherent high
product source. -/
noncomputable def highOddExactCoefficient
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) : F :=
  (((normUnits F K Q.alpha1) / gammaF : Fˣ) : F)

/-- The normalized upstairs coordinate `u=beta1/alpha1` from the same high
product witness. -/
noncomputable def highOddNormalizedRatio
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) : K :=
  (Q.beta1 : K) / (Q.alpha1 : K)

/-- The normalized coordinate from the actual high-table source has exactly
the negative conductor-excess order used in the residual class table. -/
theorem highOddNormalizedRatio_order
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) :
    ord K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q) =
      (((-((data.twistData 1).conductor - (t + 1) : ℕ) : ℤ) : ℤ) :
        WithTop ℤ) := by
  unfold highOddNormalizedRatio
  rw [ord_div, Q.beta_choice.source_order, Q.alpha_choice.source_order]
  norm_num
  change (((t : ℤ) + 1 - ((data.twistData 1).conductor : ℤ) : ℤ) :
      WithTop ℤ) =
    ((-(((data.twistData 1).conductor - (t + 1) : ℕ) : ℤ) : ℤ) :
      WithTop ℤ)
  congr 1
  omega

/-- The exact norm of the normalized high coordinate. -/
noncomputable def highOddNormalizedNorm
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) : F :=
  norm F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q)

/-- The literal unit carried by the high table's upstairs quotient-class
representative. -/
noncomputable def highOddUpstairsRepresentativeUnit
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) : Kˣ :=
  (OddIntermediateHighProductData.upstairsRepresentative
    F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF
        Q).unit

/-- The literal unit carried by one high twist quotient-class
representative. -/
noncomputable def highOddTwistRepresentativeUnit
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) : Fˣ :=
  (OddIntermediateHighProductData.factorRepresentative
    F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF
        Q j).unit

/-- The transported high upstairs row exposes the literal positive additive
factor from `Q`, with the extension additive character written downstairs
through trace. -/
theorem highOddUpstairsPhase_elementaryAdditiveFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q C).elementaryAdditiveFactor =
      (globalPsi (trace F K
        (((OddIntermediateHighProductData.upstairsRepresentative
          F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar
            psiK hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper
              gammaF hgammaF Q).representative : K) /
          algebraMap F K (gammaF : F))) : ℂ) := by
  unfold highOddUpstairsPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  unfold highOddUpstairsPhaseSource OddIntermediateHighProductData.upstairsPhase
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [hpsi, ContinuousAddChar.compTrace_apply]
  rw [data.baseAddChar_character]
  rfl

/-- The transported high upstairs row exposes the inverse base-character
value at the norm of its literal supplied numerator unit. -/
theorem highOddUpstairsPhase_elementaryMultiplicativeFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q C).elementaryMultiplicativeFactor =
      (globalChi (normUnits F K
        (highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF Q)) : ℂ)⁻¹ := by
  unfold highOddUpstairsPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  unfold highOddUpstairsPhaseSource OddIntermediateHighProductData.upstairsPhase
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [hchi, ContinuousQuasiChar.compNorm_apply,
    data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  rfl

/-- One transported high twist row exposes the positive additive factor at
its literal table numerator and the unchanged high denominator. -/
theorem highOddTwistPhase_elementaryAdditiveFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q j C).elementaryAdditiveFactor =
      (globalPsi
        (((OddIntermediateHighProductData.factorRepresentative
          F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar
            psiK hF hK hminimal hchi hpsi hodd htpos hstrict.le hupper
              gammaF hgammaF Q j).representative : F) / (gammaF : F)) :
        ℂ) := by
  unfold highOddTwistPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  unfold OddIntermediateHighProductData.factorPhase
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [data.baseAddChar_character]

/-- One transported high twist row exposes the inverse of the full literal
twist character at its table numerator unit. -/
theorem highOddTwistPhase_elementaryMultiplicativeFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q j C).elementaryMultiplicativeFactor =
      ((data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))).character
            (highOddTwistRepresentativeUnit F K ht hres pi hpi hgen data
              chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                gammaF hgammaF Q j) : ℂ)⁻¹ := by
  unfold highOddTwistPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  unfold OddIntermediateHighProductData.factorPhase
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [ramifiedNormCharacterOrbitTwistData_character,
    data.twistData_character, data.twistData_character]
  unfold highOddTwistRepresentativeUnit
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]

/-- A preferred high twist row exposes the additive value at the linear
table representative.  This is the representative transported together
with its Hasse phase, rather than the unrelated exact-norm representative. -/
theorem highOddLinearTwistPhase_elementaryAdditiveFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF Q j C).elementaryAdditiveFactor =
      (globalPsi
        (((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            Q j : Fˣ) : F) / (gammaF : F)) : ℂ) := by
  unfold highOddLinearTwistPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [data.baseAddChar_character]
  rfl

/-- A preferred high twist row exposes the inverse full twist character at
the same linear representative used by its transported odd Hasse phase. -/
theorem highOddLinearTwistPhase_elementaryMultiplicativeFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF Q j C).elementaryMultiplicativeFactor =
      ((data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))).character
            (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF Q j) : ℂ)⁻¹ := by
  unfold highOddLinearTwistPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [ramifiedNormCharacterOrbitTwistData_character,
    data.twistData_character, data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  rfl

/-- One actual high norm-character row exposes the literal Teichmüller
numerator divided by the changed denominator `gammaF/N(alpha1)`. -/
theorem highOddNormPhase_elementaryAdditiveFactor
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      htpos hstrict.le gammaF hgammaF S j C).elementaryAdditiveFactor =
      (globalPsi
        (oddNormIndexScalar F K ht hres pi hpi hgen htpos j /
          (((gammaF / normUnits F K S.alpha1 : Fˣ) : F))) : ℂ) := by
  unfold highOddNormPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  unfold highOddNormCharacterPowerPhase
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [data.baseAddChar_character]
  unfold oddNormIndexScalar
  rfl

/-- One actual high norm-character row exposes the inverse character value
at its literal nonzero Teichmüller numerator unit. -/
theorem highOddNormPhase_elementaryMultiplicativeFactor
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      htpos hstrict.le gammaF hgammaF S j C).elementaryMultiplicativeFactor =
      ((data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character
              (oddNormIndexUnit F K ht hres pi hpi hgen htpos j) : ℂ)⁻¹ := by
  unfold highOddNormPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  unfold highOddNormCharacterPowerPhase
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [quasiCharDataOfIsConductor_character,
    data.normCharacterData_character]
  congr 2

/-- The actual high upstairs row evaluates at the table denominator
`map gammaF`; transport to the computational data changes no phase. -/
theorem highOddUpstairsPhase_admissibleFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (C : LamprechtCriticalCoordinate K dK epsilonK) :
    (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q C).admissibleFactor =
      (data.extensionQuasiChar.character
        (Units.map (algebraMap F K) gammaF) : ℂ) := by
  have hchiData : chiK.character = data.extensionQuasiChar.character := by
    rw [data.extensionQuasiChar_character, hchi,
      data.twistData_character]
    exact normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi
  rw [← hchiData]
  unfold highOddUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  unfold highOddUpstairsPhaseSource OddIntermediateHighProductData.upstairsPhase
  apply localPhaseOfStationaryClass_admissibleFactor

/-- Each actual high norm row evaluates at its exact changed denominator
`gammaF / N(alpha1)`. -/
theorem highOddNormPhase_admissibleFactor
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      htpos hstrict.le gammaF hgammaF S j C).admissibleFactor =
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character
        (gammaF / normUnits F K S.alpha1) := by
  unfold highOddNormPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  rw [data.normCharacterData_character]
  unfold highOddNormCharacterPowerPhase
  apply localPhaseOfStationaryClass_admissibleFactor

/-- Each actual high twist row evaluates at the common table denominator
`gammaF`. -/
theorem highOddTwistPhase_admissibleFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q j C).admissibleFactor =
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))).character gammaF := by
  unfold highOddTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  unfold OddIntermediateHighProductData.factorPhase
  change (localPhaseOfStationaryClass _ _ _ C).admissibleFactor = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  rw [ramifiedNormCharacterOrbitTwistData_character,
    data.twistData_character, data.twistData_character]
  simp

/-- Changing a high twist numerator to the proved congruent linear
representative changes neither its actual denominator nor its admissible
character factor. -/
theorem highOddLinearTwistPhase_admissibleFactor
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K))
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF Q j C).admissibleFactor =
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))).character gammaF := by
  unfold highOddLinearTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  rw [localPhaseOfStationaryClass_admissibleFactor]
  rw [ramifiedNormCharacterOrbitTwistData_character,
    data.twistData_character, data.twistData_character]
  simp

/-- Derive the complete high admissible-character shape solely from the
literal extension, norm, and twist rows. -/
theorem highOddAdmissibleShapeOfActualRows
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF Q CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF S j (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF Q j (CTwist j))) :
    HighOddAdmissibleShape data gammaF S.alpha1 D := by
  refine
    { extension_factor := ?_
      identity_norm_factor := ?_
      nonidentity_norm_factor := ?_
      twist_factor := ?_ }
  · rw [hExtension, LocalPhaseData.admissibleFactor]
    exact highOddUpstairsPhase_admissibleFactor F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q CUp
  · rcases identityNormCharacterEndpoint_of_phaseData D with ⟨h, G, hEq⟩
    rw [hEq]
    rfl
  · intro mu hmu
    let indexing := oddNormCharacterIndexing F K ht hres pi hpi hgen
    generalize hindexValue : indexing.symm mu = index
    have hindex : indexing index = mu := by
      rw [← hindexValue]
      exact indexing.apply_symm_apply mu
    cases index with
    | none =>
        dsimp only [indexing] at hindex
        rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen] at hindex
        exact (hmu hindex.symm).elim
    | some j =>
        dsimp only [indexing] at hindex
        rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen] at hindex
        subst mu
        rw [hNorm j, LocalPhaseData.admissibleFactor]
        exact highOddNormPhase_admissibleFactor F K ht hres pi hpi hgen data
          hF htpos hstrict gammaF hgammaF S j (CNorm j)
  · intro mu
    let e : ZMod (Module.finrank F K) ≃ NormCharacter F K :=
      (Multiplicative.ofAdd : ZMod (Module.finrank F K) ≃
        Multiplicative (ZMod (Module.finrank F K))).trans
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv
    let j := e.symm mu
    have hj : e j = mu := e.apply_symm_apply mu
    rw [← hj]
    have hrow := hTwist j
    change
      (D.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j))).admissibleFactor = _
    rw [hrow, LocalPhaseData.admissibleFactor]
    exact highOddLinearTwistPhase_admissibleFactor F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q j (CTwist j)

/-- Source-tied raw correction coordinates for the exact intermediate-high
odd assembly.  There are no free `A`, `u`, or `n` fields: they are fixed to
`N(Q.alpha1)/gammaF`, `Q.beta1/Q.alpha1`, and its exact norm.  The two
independently Prop-produced high witnesses are explicitly coherent.  Only
the raw field-ratio identity and pointwise character linearizations remain
inputs; no aggregate elementary-product equality is assumed. -/
structure HighOddRawCorrectionCoordinates
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) where
  coherence : HighOddSourceCoherence F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF S Q
  zZero : Fˣ
  z : OddNormIndex F K → Fˣ
  X : F
  X_eq : X =
    trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q) +
    highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q *
        ((zZero : F) - 1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
        ((z j : F) - 1)
  additive_ratio_eq :
    ((highOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
          0 : Fˣ) : F) / (gammaF : F) +
      ∑ j : OddNormIndex F K,
        ((highOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF Q (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
              (gammaF : F) =
    highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q *
        trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF Q) +
      trace F K
        (((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF Q : Kˣ) : K) /
              algebraMap F K (gammaF : F)) +
      ∑ j : OddNormIndex F K,
        ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
          (((gammaF / normUnits F K S.alpha1 : Fˣ) : F))
  zZero_eq : zZero =
    normUnits F K
      (highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF Q) /
      (highOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
          0 *
        ∏ j : OddNormIndex F K,
          highOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
            psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
              hgammaF Q (j : ZMod (Module.finrank F K)))
  z_eq : ∀ j : OddNormIndex F K, z j =
    oddNormIndexUnit F K ht hres pi hpi hgen htpos j /
      highOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
          (j : ZMod (Module.finrank F K))
  chiLinearization : globalChi zZero =
    globalPsi
      (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q *
      highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q *
          ((zZero : F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1 (z j) =
      globalPsi
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q *
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          ((z j : F) - 1))

/-- Preferred source-tied odd correction input.  Unlike the legacy raw
coordinates above, the correction units are definitionally the manuscript
norm ratios and the high twist rows use the linear representatives supplied
by `factor_linear_congruence`.  The exact row identity retains the norm
factor which is killed only after applying a norm character. -/
structure HighOddSourceTiedCorrectionCoordinates
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) where
  correctionUnits : OddNormCorrectionUnitData F K ht hres pi hpi hgen
    htpos
    (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows)
    (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows)
  X : F
  X_eq : X =
    trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows) +
    highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows *
      (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
        correctionUnits : Fˣ) : F) - 1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
        (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
          correctionUnits j : Fˣ) : F) - 1)
  additive_ratio_eq :
    ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows 0 : Fˣ) : F) / (gammaF : F) +
      ∑ j : OddNormIndex F K,
        ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
              (gammaF : F) =
    highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows *
      trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows) +
    trace F K
      (((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows : Kˣ) : K) /
            algebraMap F K (gammaF : F)) +
    ∑ j : OddNormIndex F K,
      ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
        (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))
  zZero_selected_eq :
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
      correctionUnits =
    normUnits F K
      (highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows) /
      (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows 0 *
        ∏ j : OddNormIndex F K,
          highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
            hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source.productRows (j : ZMod (Module.finrank F K)))
  rowRatio_eq : ∀ j : OddNormIndex F K,
    oddNormIndexUnit F K ht hres pi hpi hgen htpos j /
      highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows (j : ZMod (Module.finrank F K)) =
    (normUnits F K
      (source.productRows.alpha1 *
        OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
          htpos correctionUnits j))⁻¹ *
      OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
        correctionUnits j
  chiLinearization :
    globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
      correctionUnits) =
    globalPsi
      (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows *
      highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
          correctionUnits : Fˣ) : F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1
          (OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
            correctionUnits j) =
      globalPsi
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows *
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
            correctionUnits j : Fˣ) : F) - 1))

namespace HighOddSourceTiedCorrectionCoordinates

noncomputable def zZero
    {source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF}
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source) : Fˣ :=
  OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos R.correctionUnits

noncomputable def z
    {source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF}
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source)
    (j : OddNormIndex F K) : Fˣ :=
  OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos R.correctionUnits j

/-- Applying the actual indexed norm character kills the retained norm
factor and only then identifies the selected row ratio with manuscript
`z_j`. -/
theorem powerCharacterBridge
    {source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF}
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source)
    (j : OddNormIndex F K) :
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))).1
        (OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
          R.correctionUnits j) =
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))).1
        (oddNormIndexUnit F K ht hres pi hpi hgen htpos j /
          highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
            hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source.productRows (j : ZMod (Module.finrank F K))) := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hnorm : mu.1
      (normUnits F K
        (source.productRows.alpha1 *
          OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
            htpos R.correctionUnits j)) = 1 :=
    NormCharacter.eq_one_on_normRange F K mu _ ⟨_, rfl⟩
  rw [R.rowRatio_eq j, map_mul, map_inv, hnorm, inv_one, one_mul]

end HighOddSourceTiedCorrectionCoordinates

/-- The retained high row-ratio identity is forced by the simultaneous
source and the literal manuscript correction unit.  No character
cancellation is used here. -/
theorem highOddSourceTied_rowRatio_eq
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows)
      (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows))
    (j : OddNormIndex F K) :
    oddNormIndexUnit F K ht hres pi hpi hgen htpos j /
      highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows (j : ZMod (Module.finrank F K)) =
    (normUnits F K
      (source.productRows.alpha1 *
        OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
          htpos C j))⁻¹ *
      OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j := by
  have hlinear :
      highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows (j : ZMod (Module.finrank F K)) =
      norm F K (source.productRows.alpha1 : K) *
        (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows +
          oddNormIndexScalar F K ht hres pi hpi hgen htpos j) := by
    simp only [highOddLinearTwistValue, highOddNormalizedNorm,
      highOddNormalizedRatio, oddNormAllIndexScalar, oddNormIndexScalar]
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv]
    field_simp [(Algebra.norm_ne_zero_iff).2
      (Units.ne_zero source.productRows.alpha1)]
  have hscaled :
      ((OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
        htpos C j : Kˣ) : K) =
        (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows +
          algebraMap F K
            (oddNormIndexScalar F K ht hres pi hpi hgen htpos j)) /
        algebraMap F K
          (oddNormIndexScalar F K ht hres pi hpi hgen htpos j) := by
    unfold OddNormCorrectionUnitData.scaledNumeratorUnit
    simp only [Units.val_div_eq_div_val, Units.val_mk0, Units.coe_map,
      MonoidHom.coe_coe, oddNormIndexUnit_coe]
  have hscalar_ne :
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j ≠ 0 := by
    rw [← oddNormIndexUnit_coe F K ht hres pi hpi hgen htpos j]
    exact Units.ne_zero _
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul,
    Units.val_inv_eq_inv_val]
  rw [oddNormIndexUnit_coe F K ht hres pi hpi hgen htpos j]
  rw [highOddLinearTwistUnit_coe]
  rw [hlinear]
  rw [OddNormCorrectionUnitData.coe_z]
  simp only [coe_normUnits, Units.val_mul, hscaled]
  rw [map_mul]
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [norm_algebraMap]
  unfold oddNormIndexScalar
  rw [highParameter_intermediate_teichmuller_pow F (Module.finrank F K)
    (residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen) (j : ZMod (Module.finrank F K))]
  have hnum : norm F K
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows +
        algebraMap F K
          (highIntermediateTeichmullerScalar F (Module.finrank F K)
            (residueCharacteristic_eq_degree_of_positive_break
              F K ht htpos pi hpi hgen)
              (j : ZMod (Module.finrank F K)))) ≠ 0 := by
    simpa only [oddNormIndexScalar] using C.numerator_ne_zero j
  have hden :
      highIntermediateTeichmullerScalar F (Module.finrank F K)
          (residueCharacteristic_eq_degree_of_positive_break
            F K ht htpos pi hpi hgen)
            (j : ZMod (Module.finrank F K)) +
        highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows ≠ 0 := by
    simpa only [oddNormIndexScalar, add_comm] using C.denominator_ne_zero j
  field_simp [hnum, hden] <;> ring

/-- The linear high twist representative is exactly
`N(alpha1) * (n + [j])`. -/
theorem highOddLinearTwistValue_eq_normalized
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j =
    norm F K (Q.alpha1 : K) *
      (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q +
      oddNormAllIndexScalar F K ht hres pi hpi hgen htpos j) := by
  simp only [highOddLinearTwistValue, highOddNormalizedNorm,
    highOddNormalizedRatio]
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  field_simp [(Algebra.norm_ne_zero_iff).2 (Units.ne_zero Q.alpha1)]

/-- The high upstairs representative supplied by the simultaneous product
is exactly `N(alpha1) * (n-u)` before taking its norm. -/
theorem highOddUpstairsRepresentative_eq_normalized
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) :
    ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q : Kˣ) : K) =
    algebraMap F K (norm F K (Q.alpha1 : K)) *
      (algebraMap F K
        (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q) -
        highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q) := by
  unfold highOddUpstairsRepresentativeUnit
  rw [StationaryClassRepresentative.coe_unit]
  change (((Q.quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K) = _
  rw [Q.upstairs_formula]
  simp only [highOddNormalizedNorm, highOddNormalizedRatio]
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_inv₀]
  field_simp [(Algebra.norm_ne_zero_iff).2 (Units.ne_zero Q.alpha1),
    Units.ne_zero Q.alpha1]

/-- High-table specialization of the exact complete-function transport at
the raw field-character level.  All three stationary ratios are derived
from one simultaneous High source: the generator row is `A`, the base row
is `A*n`, and the upstairs row is `A*(n-u)`.  The norm character disappears
only on the actual norm of `1+u*x`. -/
theorem highOdd_actualStationaryRatios_exactCriticalTransport
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (x : K) (upperUnit upperUxUnit : Kˣ)
    (hUpperUnit : (upperUnit : K) = 1 + x)
    (hUpperUxUnit : (upperUxUnit : K) =
      1 + highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows * x) :
    let Q := source.productRows
    let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
    let A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
    let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
    let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
    let tauRatio : F :=
      1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))
    let baseRatio : F :=
      ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q 0 :
          Fˣ) : F) / (gammaF : F)
    let upperRatio : K :=
      ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF Q : Kˣ) : K) / algebraMap F K (gammaF : F)
    (data.baseAddChar.character
          (baseRatio * phaseReductionNormPolynomial F K x) *
        ((data.twistData 1).character (normUnits F K upperUnit))⁻¹) *
      (data.baseAddChar.character
          (tauRatio * phaseReductionNormPolynomial F K (u * x)) *
        (tau.1 (normUnits F K upperUxUnit))⁻¹)⁻¹ *
      data.baseAddChar.character
        (A * (phaseReductionNormHigherPart F K (u * x) -
          n * phaseReductionNormHigherPart F K x)) =
    psiK.character (upperRatio * x) * (chiK.character upperUnit)⁻¹ := by
  dsimp only
  let Q := source.productRows
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  let A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let tauRatio : F :=
    1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))
  let baseRatio : F :=
    ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q 0 : Fˣ) :
        F) / (gammaF : F)
  let upperRatio : K :=
    ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF Q : Kˣ) : K) / algebraMap F K (gammaF : F)
  have hn : norm F K u = n := rfl
  have hTauRatio : tauRatio = A := by
    change
      1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F)) =
        (((normUnits F K Q.alpha1 / gammaF : Fˣ) : F))
    rw [source.alpha1_eq]
    simp only [Units.val_div_eq_div_val, coe_normUnits]
    field_simp [Units.ne_zero gammaF,
      (Algebra.norm_ne_zero_iff).2 (Units.ne_zero Q.alpha1)]
    rfl
  have hzero :
      oddNormAllIndexScalar F K ht hres pi hpi hgen htpos 0 = 0 := by
    exact (highParameter_intermediate_teichmuller_eq_zero_iff F
      (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen) 0).2 rfl
  have hBaseRatio : baseRatio = A * n := by
    change
      ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q 0 :
          Fˣ) : F) / (gammaF : F) =
        (((normUnits F K Q.alpha1 / gammaF : Fˣ) : F)) * n
    rw [highOddLinearTwistUnit_coe]
    rw [highOddLinearTwistValue_eq_normalized, hzero]
    simp only [add_zero, Units.val_div_eq_div_val, coe_normUnits]
    field_simp [Units.ne_zero gammaF]
    rfl
  have hUpperRatio : upperRatio =
      algebraMap F K A * (algebraMap F K n - u) := by
    change
      ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF Q : Kˣ) : K) / algebraMap F K (gammaF : F) =
        algebraMap F K (((normUnits F K Q.alpha1 / gammaF : Fˣ) : F)) *
          (algebraMap F K n - u)
    rw [highOddUpstairsRepresentative_eq_normalized]
    simp only [Units.val_div_eq_div_val, coe_normUnits, map_div₀]
    field_simp [Units.ne_zero gammaF]
    rfl
  let baseUnit := normUnits F K upperUnit
  let tauUnit := normUnits F K upperUxUnit
  have hBaseUnit : (baseUnit : F) =
      1 + phaseReductionNormPolynomial F K x := by
    simp only [baseUnit, coe_normUnits, hUpperUnit,
      phaseReductionNormPolynomial]
    ring
  have hTauUnit : (tauUnit : F) =
      1 + phaseReductionNormPolynomial F K (u * x) := by
    simp only [tauUnit, coe_normUnits, hUpperUxUnit,
      phaseReductionNormPolynomial]
    ring
  exact phaseReductionExactCriticalTransport_of_stationaryRatios F K
    data.baseAddChar.character psiK.character (data.twistData 1).character
      chiK.character tau hpsi hchi A n u x hn tauRatio baseRatio upperRatio
        hTauRatio hBaseRatio hUpperRatio upperUnit upperUxUnit baseUnit tauUnit
          hUpperUnit hUpperUxUnit hBaseUnit hTauUnit

/-- The signed additive row identity is forced by the simultaneous high
source.  It is the zero/nonzero split of the literal linear table rows. -/
theorem highOddSourceTied_additive_ratio_eq
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) :
    ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows 0 : Fˣ) : F) / (gammaF : F) +
      ∑ j : OddNormIndex F K,
        ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
              (gammaF : F) =
    highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows *
      trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows) +
    trace F K
      (((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows : Kˣ) : K) /
            algebraMap F K (gammaF : F)) +
    ∑ j : OddNormIndex F K,
      ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
        (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F)) := by
  let Q := source.productRows
  let c : F := norm F K (Q.alpha1 : K)
  let A : F := c / (gammaF : F)
  let u : K := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let n : F := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let lam : ZMod (Module.finrank F K) → F :=
    oddNormAllIndexScalar F K ht hres pi hpi hgen htpos
  have hlam0 : lam 0 = 0 := by
    exact (highParameter_intermediate_teichmuller_eq_zero_iff F
      (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen) 0).2 rfl
  have hlinear (j : ZMod (Module.finrank F K)) :
      ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q j :
          Fˣ) : F) / (gammaF : F) = A * (n + lam j) := by
    rw [highOddLinearTwistUnit_coe,
      highOddLinearTwistValue_eq_normalized]
    simp only [A, c, n, lam, div_eq_mul_inv]
    ring
  have hup :
      trace F K
        (((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF Q : Kˣ) : K) /
              algebraMap F K (gammaF : F)) =
        trace F K (algebraMap F K A * (algebraMap F K n - u)) := by
    apply congrArg (trace F K)
    rw [highOddUpstairsRepresentative_eq_normalized]
    simp only [A, c, n, u, div_eq_mul_inv, map_mul, map_inv₀]
    ring
  have hnorm (j : OddNormIndex F K) :
      ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
          (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F)) =
        A * lam j := by
    rw [oddNormIndexUnit_coe, source.alpha1_eq]
    simp only [A, c, lam, oddNormIndexScalar, oddNormAllIndexScalar,
      Units.val_div_eq_div_val, coe_normUnits]
    field_simp [Units.ne_zero gammaF]
    ring
  have hsumlinear :
      (∑ j : OddNormIndex F K,
        ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
            (j : ZMod (Module.finrank F K)) : Fˣ) : F) / (gammaF : F)) =
        ∑ j : OddNormIndex F K, A * (n + lam j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hlinear j
  rw [hlinear 0, hsumlinear]
  rw [oddNormalizedAdditiveRatioIdentity F K A n u lam hlam0]
  rw [hup]
  have hA : A =
      highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows := by
    simp only [A, c, Q, highOddExactCoefficient,
      Units.val_div_eq_div_val, coe_normUnits]
  rw [hA]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← hA]
  exact (hnorm j).symm

/-- The exceptional high correction unit is forced by the literal upstairs
row and all linear twist rows.  This is an equality of units before either
character is evaluated. -/
theorem highOddSourceTied_zZero_selected_eq
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows)
      (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows)) :
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C =
    normUnits F K
      (highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows) /
      (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows 0 *
        ∏ j : OddNormIndex F K,
          highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
            hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source.productRows (j : ZMod (Module.finrank F K))) := by
  let Q := source.productRows
  let c : F := norm F K (Q.alpha1 : K)
  let u : K := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let n : F := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let lam : ZMod (Module.finrank F K) → F :=
    oddNormAllIndexScalar F K ht hres pi hpi hgen htpos
  have hc : c ≠ 0 :=
    (Algebra.norm_ne_zero_iff).2 (Units.ne_zero Q.alpha1)
  apply Units.ext
  simp only [OddNormCorrectionUnitData.coe_zZero, Units.val_div_eq_div_val,
    coe_normUnits, Units.val_mul, Units.coe_prod,
    highOddLinearTwistUnit_coe]
  rw [highOddUpstairsRepresentative_eq_normalized]
  simp_rw [highOddLinearTwistValue_eq_normalized]
  simpa only [Q, c, u, n, lam, oddNormCorrectionDenominator,
    oddNormIndexScalar, oddNormAllIndexScalar] using
    (oddHighZZeroScalingIdentity F K c n hc u lam).symm

/-- Preferred constructor for high correction coordinates.  Callers supply
only the literal nonvanishing correction units and the later pointwise
linearizations; all three table-row algebra identities are proved here. -/
def highOddSourceTiedCorrectionCoordinatesOfActualRows
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows)
      (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows))
    (X : F)
    (hX : X =
      trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows) +
      highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C :
          Fˣ) : F) - 1) +
      ∑ j : OddNormIndex F K,
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j :
            Fˣ) : F) - 1))
    (hChi :
      globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
        C) =
      globalPsi
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows *
        highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows *
          (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C :
            Fˣ) : F) - 1)))
    (hPower : ∀ j : OddNormIndex F K,
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd
          (j : ZMod (Module.finrank F K)))).1
            (OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j) =
        globalPsi
          (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
            hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
              hgammaF source.productRows *
          oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
            (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j :
              Fˣ) : F) - 1))) :
    HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source :=
  { correctionUnits := C
    X := X
    X_eq := hX
    additive_ratio_eq := highOddSourceTied_additive_ratio_eq F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source
    zZero_selected_eq := highOddSourceTied_zZero_selected_eq F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source C
    rowRatio_eq := highOddSourceTied_rowRatio_eq F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source C
    chiLinearization := hChi
    powerLinearization := hPower }

/-- The literal high stationary rows and the raw field-ratio identity imply
the oriented positive-additive elementary product; no aggregate elementary
equality is an input. -/
theorem highOddActualRows_additiveDenominator_eq
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF source.normRows j
              (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source.productRows j (CTwist j))) :
    D.elementaryAdditiveDenominator =
      (globalPsi
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows *
        trace F K
          (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
            hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
              hgammaF source.productRows)) : ℂ) *
        D.elementaryAdditiveNumerator := by
  have hzero : ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K))) = 1 := by
    simp
  have hTwistZeroFactor : (D.twist 1).elementaryAdditiveFactor =
      (globalPsi
        (((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source.productRows 0 : Fˣ) : F) / (gammaF : F)) : ℂ) := by
    conv_lhs => rw [← hzero]
    rw [hTwist 0]
    exact highOddLinearTwistPhase_elementaryAdditiveFactor F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source.productRows 0 (CTwist 0)
  have hDen : D.elementaryAdditiveDenominator =
      (globalPsi (
        ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source.productRows 0 : Fˣ) : F) / (gammaF : F)) : ℂ) *
        (globalPsi (∑ j : OddNormIndex F K,
          ((highOddLinearTwistUnit F K ht hres pi hpi hgen data
            chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
              gammaF hgammaF source.productRows
                (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
                (gammaF : F)) : ℂ) := by
    rw [D.oddElementaryAdditiveDenominator_reindex ht hres pi hpi hgen,
      hTwistZeroFactor]
    congr 1
    calc
      (∏ j : OddNormIndex F K,
        (D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))).elementaryAdditiveFactor) =
          ∏ j : OddNormIndex F K, (globalPsi
            (((highOddLinearTwistUnit F K ht hres pi hpi hgen data
              chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                gammaF hgammaF source.productRows
                  (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
                  (gammaF : F)) : ℂ) := by
            apply Finset.prod_congr rfl
            intro j _
            rw [hTwist j]
            exact highOddLinearTwistPhase_elementaryAdditiveFactor F K ht hres pi
              hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
                hstrict hupper gammaF hgammaF source.productRows _ (CTwist j)
      _ = _ := continuousAddChar_prod_apply_eq_apply_sum globalPsi _
  have hNum : D.elementaryAdditiveNumerator =
      (globalPsi (trace F K
        (((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source.productRows : Kˣ) : K) /
              algebraMap F K (gammaF : F))) : ℂ) *
        (globalPsi (∑ j : OddNormIndex F K,
          ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
            (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))) : ℂ) := by
    rw [D.oddElementaryAdditiveNumerator_reindex ht hres pi hpi hgen,
      hExtension]
    simp only [LocalPhaseData.elementaryAdditiveFactor]
    rw [highOddUpstairsPhase_elementaryAdditiveFactor F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source.productRows CUp]
    congr 1
    calc
      (∏ j : OddNormIndex F K,
        (D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))).elementaryAdditiveFactor) =
          ∏ j : OddNormIndex F K, (globalPsi
            (((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
              (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F))) : ℂ) := by
            apply Finset.prod_congr rfl
            intro j _
            rw [hNorm j]
            exact highOddNormPhase_elementaryAdditiveFactor F K ht hres pi
              hpi hgen data hF htpos hstrict gammaF hgammaF source.normRows
                j (CNorm j)
      _ = _ := continuousAddChar_prod_apply_eq_apply_sum globalPsi _
  rw [hDen, hNum]
  have hadd (x y : F) :
      (globalPsi (x + y) : ℂ) =
        (globalPsi x : ℂ) * (globalPsi y : ℂ) := by
    exact congrArg Units.val (ContinuousAddChar.map_add_eq_mul globalPsi x y)
  calc
    (globalPsi
        (((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source.productRows 0 : Fˣ) : F) / (gammaF : F)) : ℂ) *
      (globalPsi (∑ j : OddNormIndex F K,
        ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source.productRows
              (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
              (gammaF : F)) : ℂ) =
        (globalPsi
          ((((highOddLinearTwistUnit F K ht hres pi hpi hgen data
            chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
              gammaF hgammaF source.productRows 0 : Fˣ) : F) /
                (gammaF : F)) +
            ∑ j : OddNormIndex F K,
              ((highOddLinearTwistUnit F K ht hres pi hpi hgen data
                chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                  gammaF hgammaF source.productRows
                    (j : ZMod (Module.finrank F K)) : Fˣ) : F) /
                    (gammaF : F)) : ℂ) := (hadd _ _).symm
    _ = (globalPsi
          (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
            hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source.productRows * trace F K
                (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
                  psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                    gammaF hgammaF source.productRows) +
            (trace F K
              (((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen
                data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
                  hupper gammaF hgammaF source.productRows : Kˣ) : K) /
                    algebraMap F K (gammaF : F)) +
              ∑ j : OddNormIndex F K,
                ((oddNormIndexUnit F K ht hres pi hpi hgen htpos j : Fˣ) : F) /
                  (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F)))) : ℂ) := by
          apply congrArg (fun x : F ↦ (globalPsi x : ℂ))
          rw [R.additive_ratio_eq]
          ring
    _ = _ := by
      rw [hadd, hadd]

/-- The literal high stationary rows and the raw unit-ratio identities imply
the inverse-character elementary product in the manuscript's denominator
orientation. -/
theorem highOddActualRows_multiplicativeDenominator_eq
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF source.normRows j
              (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source.productRows j (CTwist j))) :
    D.elementaryMultiplicativeDenominator =
      ((globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
        htpos R.correctionUnits) : ℂ) *
        ∏ j : OddNormIndex F K,
          ((ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))).1
                (OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
                  R.correctionUnits j) : ℂ)) *
        D.elementaryMultiplicativeNumerator := by
  let mu : OddNormIndex F K → NormCharacter F K := fun j ↦
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hzero : ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K))) = 1 := by simp
  have hTwistZeroFactor : (D.twist 1).elementaryMultiplicativeFactor =
      (globalChi
        (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source.productRows 0) : ℂ)⁻¹ := by
    conv_lhs => rw [← hzero]
    rw [hTwist 0]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [highOddLinearTwistPhase_elementaryMultiplicativeFactor F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source.productRows 0 (CTwist 0)]
    rw [data.twistData_character]
    simp
  have hDen : D.elementaryMultiplicativeDenominator =
      (globalChi
        (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source.productRows 0) : ℂ)⁻¹ *
        ∏ j : OddNormIndex F K,
          (((globalChi
              (highOddLinearTwistUnit F K ht hres pi hpi hgen data
                chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                  gammaF hgammaF source.productRows
                    (j : ZMod (Module.finrank F K))) : ℂ) *
            (mu j).1
              (highOddLinearTwistUnit F K ht hres pi hpi hgen data
                chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                  gammaF hgammaF source.productRows
                    (j : ZMod (Module.finrank F K))) : ℂ))⁻¹ := by
    rw [D.oddElementaryMultiplicativeDenominator_reindex ht hres pi hpi hgen,
      hTwistZeroFactor]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hTwist j]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [highOddLinearTwistPhase_elementaryMultiplicativeFactor F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source.productRows _ (CTwist j)]
    rw [data.twistData_character]
    simp only [mu, ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
      ContinuousQuasiChar.one_apply, one_mul]
    simp only [Units.val_mul, mul_inv_rev]
    ring
  have hNum : D.elementaryMultiplicativeNumerator =
      (globalChi (normUnits F K
        (highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source.productRows)) : ℂ)⁻¹ *
        ∏ j : OddNormIndex F K,
          ((mu j).1 (oddNormIndexUnit F K ht hres pi hpi hgen htpos j) : ℂ)⁻¹ := by
    rw [D.oddElementaryMultiplicativeNumerator_reindex ht hres pi hpi hgen,
      hExtension]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [highOddUpstairsPhase_elementaryMultiplicativeFactor F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source.productRows CUp]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hNorm j]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [highOddNormPhase_elementaryMultiplicativeFactor F K ht hres pi hpi
      hgen data hF htpos hstrict gammaF hgammaF source.normRows j (CNorm j)]
    rw [data.normCharacterData_character]
  rw [hDen, hNum, R.zZero_selected_eq]
  simp_rw [HighOddSourceTiedCorrectionCoordinates.powerCharacterBridge
    (F := F) (K := K) (R := R)]
  simp only [mu, map_div, map_mul, map_prod, Units.val_div_eq_div_val,
    Units.val_mul]
  simp_rw [mul_inv_rev]
  rw [Finset.prod_mul_distrib]
  simp_rw [Finset.prod_inv_distrib, Finset.prod_div_distrib,
    Units.coe_prod]
  field_simp [ContinuousQuasiChar.apply_ne_zero, Finset.prod_ne_zero_iff]

/-- A high odd assembly backed by both actual table sources.  `S` is one
destructured `parameters` witness for all nonidentity norm rows; `Q` is one
simultaneous high-product witness for the extension and every twist row.
The only other input used to build `assembly` is `OddGlobalScalarInput`. -/
structure HighTableBackedExactOddAssembly
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF) where
  assembly : ExactOddPhaseAssembly F K globalChi globalPsi data D
    (t := t) (m := (data.twistData 1).conductor) (OddNormIndex F K)
  upstairsCriticalCoordinate : LamprechtCriticalCoordinate K dK epsilonK
  normCriticalCoordinate : OddNormIndex F K →
    LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)
  twistCriticalCoordinate : ZMod (Module.finrank F K) →
    LamprechtCriticalCoordinate F d epsilon
  extensionPhase : D.extension = LocalPhaseData.stationary
    (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
        upstairsCriticalCoordinate)
  nonidentityNormPhase : ∀ j : OddNormIndex F K,
    D.normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
          data hF htpos hstrict.le gammaF hgammaF S j
            (normCriticalCoordinate j))
  twistPhase : ∀ j : ZMod (Module.finrank F K),
    D.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j)) =
      LocalPhaseData.stationary
        (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
          data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF Q j (twistCriticalCoordinate j))
  range_is_high : assembly.parameterRange = .high hstrict

/-- Preferred source-tied intermediate-high odd result.  It wraps the
literal table-backed phase rows while exposing that the exact correction
coefficient, normalized coordinate, norm, and correction units are the
ones fixed by one simultaneous source and the raw ratio identities. -/
structure HighSourceTiedTableBackedExactOddAssembly
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source) where
  tableBacked : HighTableBackedExactOddAssembly F K ht hres pi hpi hgen
    data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source.normRows source.productRows
  coefficient_source : tableBacked.assembly.A =
    highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
  normalizedRatio_source : tableBacked.assembly.u =
    highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
  normalizedNorm_source : tableBacked.assembly.n =
    highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
  zZero_source : tableBacked.assembly.zZero =
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
      R.correctionUnits
  z_source : tableBacked.assembly.z = fun j ↦
    OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
      R.correctionUnits j
  correctionCoordinate_source : tableBacked.assembly.X = R.X
  source_alpha : source.normRows.alpha = source.productRows.alpha
  source_alpha1 : source.normRows.alpha1 = source.productRows.alpha1

/-- Specialized high constructor: range dispatch is definitionally high,
and the stationary row of the exact odd assembly is the current target's
exact-norm `highOddNormCharacterPowerPhase` adapter. -/
def highTableBackedExactOddAssembly
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
          CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF S j (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
              gammaF hgammaF Q j (CTwist j)))
    (R : OddGlobalScalarInput F K ht hres pi hpi hgen htpos
      globalChi globalPsi data D) :
    HighTableBackedExactOddAssembly F K ht hres pi hpi hgen data D chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        S Q := by
  let A := exactOddAssemblyOfActualNormRows F K ht hres pi hpi hgen htpos
    data D
    (.high hstrict)
    (fun j ↦ highOddNormPhaseForComputationalData
      F K ht hres pi hpi hgen data hF htpos hstrict.le gammaF hgammaF S j
        (CNorm j)) hNorm R
  exact
    { assembly := A
      upstairsCriticalCoordinate := CUp
      normCriticalCoordinate := CNorm
      twistCriticalCoordinate := CTwist
      extensionPhase := hExtension
      nonidentityNormPhase := hNorm
      twistPhase := hTwist
      range_is_high := rfl }

/-- Legacy lower-level high-table constructor.  It still accepts the two
aggregate separated elementary identities; source-tied callers should use
`highSourceTiedTableBackedExactOddAssembly`. -/
def highTableBackedExactOddAssemblySeparated
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (Q : HighOddPhaseSource F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF Q CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF S j (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF Q j (CTwist j)))
    (R : OddSeparatedScalarInput F K ht hres pi hpi hgen htpos
      globalChi globalPsi data D) :
    HighTableBackedExactOddAssembly F K ht hres pi hpi hgen data D chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        S Q := by
  have hEndpoint : D.factors.endpoint = 1 := by
    apply endpointFactor_eq_one_of_actual_stationary_rows
    · exact ⟨_, hExtension⟩
    · refine nonidentityNormStationary_of_optionEquiv
        (oddNormCharacterIndexing F K ht hres pi hpi hgen)
        (oddNormCharacterIndexing_none F K ht hres pi hpi hgen) ?_
      intro j
      rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen j]
      exact ⟨_, hNorm j⟩
    · let e : ZMod (Module.finrank F K) ≃ NormCharacter F K :=
        (Multiplicative.ofAdd : ZMod (Module.finrank F K) ≃
          Multiplicative (ZMod (Module.finrank F K))).trans
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv
      refine allTwistsStationary_of_equiv e ?_
      intro j
      simpa only [e] using ⟨_, hTwist j⟩
  have hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm := by
    rw [data.extensionQuasiChar_character, data.twistData_character]
    exact (normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi).symm
  let shape := highOddAdmissibleShapeOfActualRows F K ht hres pi hpi hgen
    data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF S Q CUp CNorm CTwist hExtension hNorm hTwist
  have hAdmissible : D.factors.admissibleCharacter = 1 :=
    HighOddAdmissibleShape.factor_eq_one data ht hres pi hpi hgen hchiArg
      shape
  let A := exactOddAssemblyOfActualNormRowsSeparated F K ht hres pi hpi hgen
    htpos data D (.high hstrict)
      (fun j ↦ highOddNormPhaseForComputationalData
        F K ht hres pi hpi hgen data hF htpos hstrict.le gammaF hgammaF S j
          (CNorm j)) hNorm R hEndpoint hAdmissible
  exact
    { assembly := A
      upstairsCriticalCoordinate := CUp
      normCriticalCoordinate := CNorm
      twistCriticalCoordinate := CTwist
      extensionPhase := hExtension
      nonidentityNormPhase := hNorm
      twistPhase := hTwist
      range_is_high := rfl }

/-- Preferred intermediate-high odd constructor.  It consumes one
simultaneous high source and raw field/unit correction identities.  Both
aggregate elementary products are proved above from the literal stationary
rows, rather than accepted as hypotheses. -/
def highSourceTiedTableBackedExactOddAssembly
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF source.normRows j
              (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source.productRows j (CTwist j)))
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source) :
    HighSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source R := by
  let scalar : OddSeparatedScalarInput F K ht hres pi hpi hgen htpos
      globalChi globalPsi data D :=
    { A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
      u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
      n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
      norm_u := rfl
      zZero := OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
        R.correctionUnits
      z := fun j ↦ OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
        R.correctionUnits j
      X := R.X
      X_eq := R.X_eq
      chiLinearization := R.chiLinearization
      powerLinearization := R.powerLinearization
      additiveDenominator_eq := highOddActualRows_additiveDenominator_eq
        F K ht hres pi hpi hgen data D chiK psiK hF hK hminimal hchi hpsi
          hodd htpos hstrict hupper gammaF hgammaF source R CUp CNorm CTwist
            hExtension hNorm hTwist
      multiplicativeDenominator_eq :=
        highOddActualRows_multiplicativeDenominator_eq F K ht hres pi hpi
          hgen data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
            hupper gammaF hgammaF source R CUp CNorm CTwist hExtension hNorm
              hTwist }
  let B := highTableBackedExactOddAssemblySeparated F K ht hres pi hpi hgen
    data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source.normRows source.productRows CUp CNorm CTwist
        hExtension hNorm hTwist scalar
  exact
    { tableBacked := B
      coefficient_source := rfl
      normalizedRatio_source := rfl
      normalizedNorm_source := rfl
      zZero_source := rfl
      z_source := rfl
      correctionCoordinate_source := rfl
      source_alpha := source.alpha_eq
      source_alpha1 := source.alpha1_eq }

/-- Result eliminator type for a strengthened high source-tied odd assembly. -/
def HighSourceTiedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source)
    (B : HighSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen
      data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source R) : Prop :=
  ∀ (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK),
    B.tableBacked.assembly.Result hDeltaF hDeltaK

/-- Every strengthened high source-tied odd assembly has the full structured
odd result, with no residual cancellation. -/
theorem highSourceTiedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source)
    (B : HighSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen
      data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source R) :
    HighSourceTiedExactOddResultEliminator (DeltaF := DeltaF)
      (DeltaK := DeltaK) F K ht hres pi hpi hgen data D
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source R B := by
  intro hDeltaF hDeltaK
  exact B.tableBacked.assembly.result hDeltaF hDeltaK

/-- The remaining high odd correction input after all algebra forced by the
actual parameter-table rows has been removed.  It contains only the literal
correction units, their norm--trace coordinate, and the two pointwise
character linearizations used after the exact stationary assembly. -/
structure HighOddActualRowsCorrectionInput
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) where
  correctionUnits : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos
    (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows)
    (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows)
  X : F
  X_eq : X =
    trace F K (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows) +
    highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows *
      (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
        correctionUnits : Fˣ) : F) - 1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
        (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
          correctionUnits j : Fˣ) : F) - 1)
  chiLinearization :
    globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
      correctionUnits) =
    globalPsi
      (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows *
      highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos
          correctionUnits : Fˣ) : F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1
          (OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
            correctionUnits j) =
      globalPsi
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows *
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos
            correctionUnits j : Fˣ) : F) - 1))

/-- High odd correction coordinates pinned definitionally to the constructor
which derives every raw row identity from the simultaneous high source. -/
def HighOddActualRowsCorrectionInput.toSourceTied
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source) :
    HighOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source :=
  highOddSourceTiedCorrectionCoordinatesOfActualRows F K ht hres pi hpi hgen
    data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source R.correctionUnits R.X R.X_eq R.chiLinearization
        R.powerLinearization

/-- Public high odd wrapper whose correction coordinates can only be those
derived from the actual stationary rows. -/
abbrev HighActualRowsTableBackedExactOddAssembly
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source) :=
  HighSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source)

/-- Construct the public high odd wrapper from the actual local phase rows;
no raw additive, exceptional-unit, or indexed row-ratio equality is an
argument. -/
def highActualRowsTableBackedExactOddAssembly
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF source.normRows j
              (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source.productRows j (CTwist j))) :
    HighActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source R :=
  highSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source CUp CNorm CTwist hExtension hNorm hTwist
        (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source)

/-- Result eliminator type for a high odd assembly whose row algebra is
definitionally sourced from the parameter table. -/
def HighActualRowsExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source)
    (B : HighActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
      data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source R) : Prop :=
  HighSourceTiedExactOddResultEliminator (DeltaF := DeltaF)
    (DeltaK := DeltaK) F K ht hres pi hpi hgen data D chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source) B

/-- Every actual-row-pinned high odd assembly has the structured exact odd
result, without a residual finite-phase cancellation. -/
theorem highActualRowsExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source)
    (B : HighActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
      data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source R) :
    HighActualRowsExactOddResultEliminator (DeltaF := DeltaF)
      (DeltaK := DeltaK) F K ht hres pi hpi hgen data D chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source R B :=
  highSourceTiedExactOddResultEliminator F K ht hres pi hpi hgen data D
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
        (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source) B

/-- Public high odd result obtained directly from the actual stationary rows.
The table-backed assembly is constructed internally, so no caller-supplied
assembly or raw row-algebra proof occurs in this interface. -/
theorem highActualRowsConstructedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (R : HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source)
    (CUp : LamprechtCriticalCoordinate K dK epsilonK)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon)
    (hExtension : D.extension = LocalPhaseData.stationary
      (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows CUp))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen
            data hF htpos hstrict.le gammaF hgammaF source.normRows j
              (CNorm j)))
    (hTwist : ∀ j : ZMod (Module.finrank F K),
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) =
        LocalPhaseData.stationary
          (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source.productRows j (CTwist j))) :
    HighActualRowsExactOddResultEliminator (DeltaF := DeltaF)
      (DeltaK := DeltaK) F K ht hres pi hpi hgen data D chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source R
          (highActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
            data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source R CUp CNorm CTwist hExtension hNorm
                hTwist) :=
  highActualRowsExactOddResultEliminator F K ht hres pi hpi hgen data D
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source R
        (highActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
          data D chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source R CUp CNorm CTwist hExtension hNorm hTwist)

end HighTableBacked

end

end LanglandsFirstMainLemma
