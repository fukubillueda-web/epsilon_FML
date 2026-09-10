import LanglandsFirstMainLemma.Parameters.HighIntermediate
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Cases.WildOdd.LowerResidualCoefficients
import LanglandsFirstMainLemma.Cases.WildOdd.ScalarPhaseProducts
import LanglandsFirstMainLemma.Cases.WildOdd.BoundaryPencil

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

namespace OddRepresentativeChangeData

/-- The actual source-to-selected stationary representative difference.
This is `beta' - beta`, still bundled in its permitted critical lattice. -/
def representativeDifference
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected) :
    lattice E (R.d : ℤ) :=
  criticalStationaryRepresentativeDifference E chi psi R.d R.hm R.hlarge
    R.Gamma R.beta R.beta' R.hbeta R.hbeta'

/-- A representative change one layer deeper than the critical depth has
zero residual affine coefficient.  The proof keeps the exact difference,
the source representative in the denominator, and the chosen critical
uniformizer until reduction modulo the maximal ideal. -/
theorem translationCoefficient_eq_zero_of_difference_mem_succ
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hdeep : (R.representativeDifference : E) ∈
      lattice E ((R.d + 1 : ℕ) : ℤ)) :
    R.translationCoefficient psi0 hpsi0 = 0 := by
  rw [translationCoefficient,
    criticalRepresentativeAffineCoefficient_eq_polar_mul_parameter]
  suffices hparameter :
      criticalRepresentativeTranslationParameter E chi psi R.d R.hm
        R.hlarge R.Gamma R.delta R.hdelta R.beta R.beta' R.hbeta R.hbeta' =
          0 by
    rw [hparameter, mul_zero]
  unfold criticalRepresentativeTranslationParameter
  apply (residueMap_eq_zero_iff E _).2
  change criticalRepresentativeTranslationField E (R.beta : E)
      (R.beta' : E) R.delta ∈ lattice E 1
  have hbetaOrd := criticalStationaryRepresentative_ord_zero E chi psi R.d
    R.hm R.hlarge R.Gamma R.beta R.hbeta
  have hdenom : ord E ((R.beta : E) * (R.delta : E)) =
      ((R.d : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hbetaOrd, R.hdelta]
    simp
  apply (div_mem_lattice_iff E ((R.beta : E) * (R.delta : E))
    ((R.beta' : E) - (R.beta : E)) (R.d : ℤ) 1 hdenom).2
  simpa only [representativeDifference,
    criticalStationaryRepresentativeDifference, Nat.cast_add, Nat.cast_one,
    add_comm] using hdeep

end OddRepresentativeChangeData

/-- Pointwise equality of complete critical functions gives equality of
their actual critical factors. -/
theorem LocalLamprechtPhaseData.criticalFactor_eq_of_criticalFunction_eq
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi₁ chi₂ : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D₁ : LocalLamprechtPhaseData E chi₁ psi)
    (D₂ : LocalLamprechtPhaseData E chi₂ psi)
    (hfun : ∀ x, D₁.criticalFunction x = D₂.criticalFunction x) :
    D₁.criticalFactor = D₂.criticalFactor := by
  letI := residueFieldFintype E
  rw [D₁.criticalFactor_eq_criticalFunctionPhase,
    D₂.criticalFactor_eq_criticalFunctionPhase]
  unfold LocalLamprechtPhaseData.criticalFunctionPhase
  apply congrArg phase
  apply Finset.sum_congr rfl
  intro x _hx
  exact hfun x

/-! ## The actual High Teichmüller row -/

section HighTranslation

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

/-- The exact High Teichmüller-minus-literal difference lies one layer
deeper than the critical half-depth. -/
theorem wildOdd_highRepresentativeDifference_mem_succ
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    let R := highTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source j hparity
    (R.representativeDifference : F) ∈
      lattice F ((R.d + 1 : ℕ) : ℤ) := by
  dsimp only
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  have hTodd : Odd (t + 1) := by
    refine ⟨lowCriticalFloorDepth t, ?_⟩
    simpa only [hparity] using
      (lowCriticalConductorDecomposition (t := t) (by omega)).conductor_eq
  have htrace : TraceIdealLowerBound F K (Module.finrank F K)
      ((((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) := by
    exact traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hteich :=
    highParameter_intermediate_teichmuller_congruent_succ_of_odd
      F K (Module.finrank F K) (t + 1) hchar rfl htrace hodd hTodd
        (by omega) (j : ZMod (Module.finrank F K))
  unfold OddRepresentativeChangeData.representativeDifference
  unfold highTeichmullerLiteralRepresentativeChange
  dsimp only [criticalStationaryRepresentativeDifference,
    StationaryClassRepresentative.toLamprecht,
    StationaryClassRepresentative.ofCoefficientRepresentative]
  simp only [id_eq]
  let oneRep : lattice F 0 := ⟨1, by simp⟩
  have honeSmul :
      ((((j : ZMod (Module.finrank F K)).val • oneRep : lattice F 0) : F)) =
        ((j : ZMod (Module.finrank F K)).val : F) := by
    change (j : ZMod (Module.finrank F K)).val • (1 : F) = _
    simp only [nsmul_eq_mul, mul_one]
  change
    highIntermediateTeichmullerScalar F (Module.finrank F K) hchar
        (j : ZMod (Module.finrank F K)) -
      ((((j : ZMod (Module.finrank F K)).val • oneRep : lattice F 0) : F)) ∈
        lattice F ((lowCriticalFloorDepth t + 1 : ℕ) : ℤ)
  rw [honeSmul]
  simpa only [lowCriticalFloorDepth] using hteich

/-- The affine translation of every actual nonidentity High norm row is
zero; the datum remains the source-tied Teichmüller representative change. -/
theorem wildOdd_highTranslationCoefficient_eq_zero
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    (highTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source j hparity).translationCoefficient
          psi0 hpsi0 = 0 := by
  apply OddRepresentativeChangeData.translationCoefficient_eq_zero_of_difference_mem_succ
  exact wildOdd_highRepresentativeDifference_mem_succ F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source j hparity

/-- The product of the actual High critical factors is the clean product
of the literal natural-power rows.  This bridge only removes the already
proved zero translations; it does not recompute the scalar pencil. -/
theorem wildOdd_highActualNormCriticalProduct_eq_clean
    (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    (∏ j : OddNormIndex F K,
      (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source j hparity).criticalFactor) =
      ∏ j : OddNormIndex F K,
        (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source j hparity).criticalFactor := by
  classical
  apply Finset.prod_congr rfl
  intro j _hj
  apply LocalLamprechtPhaseData.criticalFactor_eq_of_criticalFunction_eq
  intro x
  rw [highActualTeichmuller_criticalFunction_eq_exact_translation F K ht
    hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
      hstrict hupper gammaF hgammaF source j hparity psi0 hpsi0 x]
  rw [wildOdd_highTranslationCoefficient_eq_zero F K ht hres pi hpi hgen
    data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source j hparity psi0 hpsi0]
  simp

end HighTranslation

/-! ## The actual Low and boundary rows -/

section LowTranslation

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
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (delta : Fˣ) (epsilon1 : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hT : 2 ≤ t + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
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

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The exact Low Teichmüller-minus-literal difference, including
multiplication by the supplied unit `alpha`, lies at successor depth. -/
theorem wildOdd_lowRepresentativeDifference_mem_succ
    (hodd : Odd (Module.finrank F K))
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    let R := lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
      hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity
    (R.representativeDifference : F) ∈
      lattice F ((R.d + 1 : ℕ) : ℤ) := by
  dsimp only
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
      (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
  have hTodd : Odd (t + 1) := by
    refine ⟨lowCriticalFloorDepth t, ?_⟩
    simpa only [hparity] using
      (lowCriticalConductorDecomposition (t := t) hT).conductor_eq
  have htrace : TraceIdealLowerBound F K (Module.finrank F K)
      ((((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) := by
    exact traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hteich :=
    highParameter_intermediate_teichmuller_congruent_succ_of_odd
      F K (Module.finrank F K) (t + 1) hchar rfl htrace hodd hTodd hT
        (j : ZMod (Module.finrank F K))
  have halpha : (P.alpha : F) ∈ lattice F 0 :=
    P.alphaRepresentative.norm_exactDepth.1
  have hmul := mul_mem_lattice F hteich halpha
  unfold OddRepresentativeChangeData.representativeDifference
  unfold lowTeichmullerLiteralRepresentativeChange
  dsimp only [criticalStationaryRepresentativeDifference,
    StationaryClassRepresentative.toLamprecht,
    StationaryClassRepresentative.ofCoefficientRepresentative]
  simp only [id_eq]
  let alphaRep : lattice F 0 := ⟨(P.alpha : F), halpha⟩
  have hsource :
      ((((j : ZMod (Module.finrank F K)).val • alphaRep : lattice F 0) : F)) =
        ((j : ZMod (Module.finrank F K)).val : F) * (P.alpha : F) := by
    change (j : ZMod (Module.finrank F K)).val • (P.alpha : F) = _
    simp only [nsmul_eq_mul]
  rw [hsource]
  rw [lowOddNormRepresentative_eq_teichmuller_mul F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P j]
  have hprime :
      (((primeTeichmuller F (Module.finrank F K) hchar
        (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)) =
        highIntermediateTeichmullerScalar F (Module.finrank F K) hchar
          (j : ZMod (Module.finrank F K)) := by
    simp [highIntermediateTeichmullerScalar, primeTeichmuller]
    rfl
  rw [hprime]
  simpa only [lowCriticalFloorDepth, add_zero, sub_mul] using hmul

/-- The actual Low norm-row representative change has zero translation. -/
theorem wildOdd_lowNormTranslationCoefficient_eq_zero
    (hodd : Odd (Module.finrank F K))
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    OddRepresentativeChangeData.translationCoefficient
      (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hT hgammaF P j hparity)
      psi0 hpsi0 = 0 := by
  apply OddRepresentativeChangeData.translationCoefficient_eq_zero_of_difference_mem_succ
  exact wildOdd_lowRepresentativeDifference_mem_succ F K ht hres pi hpi
    hgen data hF delta epsilon1 hdelta hT hgammaF P hodd j hparity

/-- The actual Low boundary twist row carries the same positive
source-to-selected translation exposed by `wildOdd_lowBoundaryTwistCoefficients`;
that translation is separately certified to vanish. -/
theorem wildOdd_lowTwistTranslationCoefficient_eq_zero
    (hodd : Odd (Module.finrank F K))
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    OddRepresentativeChangeData.translationCoefficient
      (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hT hgammaF P j hparity)
      psi0 hpsi0 = 0 := by
  exact wildOdd_lowNormTranslationCoefficient_eq_zero F K ht hres pi hpi
    hgen data hF delta epsilon1 hdelta hT hgammaF P hodd j hparity psi0
      hpsi0

/-- Compact public name for the Low source-to-selected vanishing. -/
theorem wildOdd_lowTranslationCoefficient_eq_zero
    (hodd : Odd (Module.finrank F K))
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    OddRepresentativeChangeData.translationCoefficient
      (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hT hgammaF P j hparity)
      psi0 hpsi0 = 0 :=
  wildOdd_lowNormTranslationCoefficient_eq_zero F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P hodd j hparity psi0 hpsi0

/-- The quotient built from the actual positively translated norm and
boundary-twist rows is the untranslated quotient used by the boundary
pencil.  The two translations are simplified only after their individual
zero certificates have been invoked. -/
theorem wildOdd_lowBoundaryTranslatedCriticalQuotient_eq_untranslated
    (hodd : Odd (Module.finrank F K))
    (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (upperFactor zeroTwistFactor : ℂ) :
    letI := residueFieldFintype F
    let translationR := fun j : OddNormIndex F K ↦
      OddRepresentativeChangeData.translationCoefficient
        (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P j hparity) psi0 hpsi0
    let translationT := fun j : OddNormIndex F K ↦
      OddRepresentativeChangeData.translationCoefficient
        (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
          data hF delta epsilon1 hdelta hT hgammaF P j hparity) psi0 hpsi0
    (upperFactor * ∏ j : OddNormIndex F K,
        let row := WildOddCoefficientPair.translateAffine
          (wildOddTauPowerPair generator
            ((j : ZMod (Module.finrank F K)).val : ResidueField F))
          (translationR j)
        quadraticPhase psi0 row.polar row.affine) /
      (zeroTwistFactor * ∏ j : OddNormIndex F K,
        let row := WildOddCoefficientPair.translateAffine
          (wildOddBoundaryPair generator base
            ((j : ZMod (Module.finrank F K)).val : ResidueField F))
          (translationT j)
        quadraticPhase psi0 row.polar row.affine) =
    (upperFactor * ∏ j : OddNormIndex F K,
        let row := wildOddTauPowerPair generator
          ((j : ZMod (Module.finrank F K)).val : ResidueField F)
        quadraticPhase psi0 row.polar row.affine) /
      (zeroTwistFactor * ∏ j : OddNormIndex F K,
        let row := wildOddBoundaryPair generator base
          ((j : ZMod (Module.finrank F K)).val : ResidueField F)
        quadraticPhase psi0 row.polar row.affine) := by
  classical
  dsimp only
  have hnorm (j : OddNormIndex F K) :=
    wildOdd_lowNormTranslationCoefficient_eq_zero F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hT hgammaF P hodd j hparity psi0 hpsi0
  have htwist (j : OddNormIndex F K) :=
    wildOdd_lowTwistTranslationCoefficient_eq_zero F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hT hgammaF P hodd j hparity psi0 hpsi0
  have hnormPair (j : OddNormIndex F K) :
      (wildOddTauPowerPair generator
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)).translateAffine
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
            psi0 hpsi0) =
        wildOddTauPowerPair generator
          ((j : ZMod (Module.finrank F K)).val : ResidueField F) := by
    rw [hnorm]
    apply WildOddCoefficientPair.ext <;> simp
  have htwistPair (j : OddNormIndex F K) :
      (wildOddBoundaryPair generator base
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)).translateAffine
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
            psi0 hpsi0) =
        wildOddBoundaryPair generator base
          ((j : ZMod (Module.finrank F K)).val : ResidueField F) := by
    rw [htwist]
    apply WildOddCoefficientPair.ext <;> simp
  simp_rw [hnormPair, htwistPair]

end LowTranslation

/-- The compact public facade for the source-faithful affine-translation
bridge. -/
structure WildOddAffineTranslationBridgeAPI : Prop where
  genericZero : type_of%
    @OddRepresentativeChangeData.translationCoefficient_eq_zero_of_difference_mem_succ.{0}
  highZero : type_of% @wildOdd_highTranslationCoefficient_eq_zero
  lowZero : type_of% @wildOdd_lowTranslationCoefficient_eq_zero
  highProduct : type_of% @wildOdd_highActualNormCriticalProduct_eq_clean
  lowBoundaryQuotient : type_of%
    @wildOdd_lowBoundaryTranslatedCriticalQuotient_eq_untranslated

/-- Public assembly of the completed High and Low affine-translation bridge. -/
theorem wildOdd_affineTranslationBridge : WildOddAffineTranslationBridgeAPI where
  genericZero :=
    OddRepresentativeChangeData.translationCoefficient_eq_zero_of_difference_mem_succ
  highZero := wildOdd_highTranslationCoefficient_eq_zero
  lowZero := wildOdd_lowTranslationCoefficient_eq_zero
  highProduct := wildOdd_highActualNormCriticalProduct_eq_clean
  lowBoundaryQuotient :=
    wildOdd_lowBoundaryTranslatedCriticalQuotient_eq_untranslated

end

end LanglandsFirstMainLemma
