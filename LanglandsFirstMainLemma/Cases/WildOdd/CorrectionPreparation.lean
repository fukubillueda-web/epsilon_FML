import LanglandsFirstMainLemma.Cases.WildOdd.PhasePreparation
import LanglandsFirstMainLemma.Cases.WildOdd.CorrectionValuation
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Ramification.TraceIdeals
import LanglandsFirstMainLemma.Cases.WildOdd.Main

/-!
# Correction preparation for the wild odd-prime branch

This module converts `WildOddPhasePrepared` into the exact correction package
used by the nonstable dispatch.  The High branch is strict above `t + 1`; the
Low branch contains both the strict and genuine boundary cases.  In each
branch, the actual selected representatives first give correction units and a
closed correction datum.  `wildOddCorrectionIndexEquiv` bridges the phase and
correction indexings, while `wildOdd_phaseCorrectionCoordinate_eq` and the
branch linearization results identify the assembled critical coordinate and
characters.

For the public construction path, read `wildOddHighCorrectionData` and
`wildOddLowCorrectionData`, the coordinate and tau-linearization theorems,
then `wildOddHighActualRowsCorrectionInput` and
`wildOddLowActualRowsCorrectionInput`.  These feed
`WildOddCorrectionPrepared` and `wildOddCorrectionPrepared`;
`wildOddNonstableHigherData` finally transports the degree-indexed residual
data to residue-characteristic indexing and is the dispatch-facing entry
point.  The remaining index and projection transports form implementation API
supporting that final route.
-/

namespace LanglandsFirstMainLemma
noncomputable section
open scoped BigOperators
section High
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
local instance : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance : Fact (Module.finrank F K).Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
/-- The four nonvanishing fields of the high correction-unit package follow from the literal unit representatives already carried by the simultaneous source. -/
noncomputable def wildOddHighCorrectionUnits
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) :
    OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows)
      (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows) := by
  let Q := source.productRows
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  refine
    { norm_u := rfl
      zeroNumerator_ne_zero := ?_
      zeroDenominator_ne_zero := ?_
      numerator_ne_zero := ?_
      denominator_ne_zero := ?_ }
  · have hunit :
        ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF Q : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have hrep := highOddUpstairsRepresentative_eq_normalized F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF Q
    rw [hrep] at hunit
    apply (Algebra.norm_ne_zero_iff).2
    intro hz
    apply hunit
    rw [hz, mul_zero]
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _hj
    have hunit :
        (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
            j : F) ≠ 0 := Units.ne_zero _
    rw [highOddLinearTwistUnit_coe,
      highOddLinearTwistValue_eq_normalized] at hunit
    exact (mul_ne_zero_iff.mp hunit).2
  · intro j
    have hfactorUnit :
        ((((Q.quotientProduct.factors
          (j : ZMod (Module.finrank F K)) : unitFiltration F 0) : Fˣ) : F))
            ≠ 0 := Units.ne_zero _
    rw [Q.factor_formula (j : ZMod (Module.finrank F K))] at hfactorUnit
    have hfactor :
        norm F K ((Q.beta1 : K) + algebraMap F K
          (oddNormIndexScalar F K ht hres pi hpi hgen htpos j) *
            (Q.alpha1 : K)) ≠ 0 := by
      simpa only [oddNormIndexScalar] using hfactorUnit
    have heq :
        (Q.beta1 : K) + algebraMap F K
            (oddNormIndexScalar F K ht hres pi hpi hgen htpos j) *
              (Q.alpha1 : K) =
          (Q.alpha1 : K) *
            (u + algebraMap F K
              (oddNormIndexScalar F K ht hres pi hpi hgen htpos j)) := by
      dsimp only [u, Q, highOddNormalizedRatio]
      field_simp [Units.ne_zero Q.alpha1]
    rw [heq, map_mul] at hfactor
    exact (mul_ne_zero_iff.mp hfactor).2
  · intro j
    have hunit :
        (highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
            (j : ZMod (Module.finrank F K)) : F) ≠ 0 := Units.ne_zero _
    rw [highOddLinearTwistUnit_coe,
      highOddLinearTwistValue_eq_normalized] at hunit
    exact (mul_ne_zero_iff.mp hunit).2
end High
section Low
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
  (hodd : Odd (Module.finrank F K))
  (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table)
  (WTwist : ∀ j : OddNormIndex F K,
    LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table j)
local instance : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance : Fact (Module.finrank F K).Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
/-- The low actual rows also force all nonvanishing fields of the correction unit package. -/
noncomputable def wildOddLowCorrectionUnits :
    OddNormCorrectionUnitData F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega)
      (lowNormalizedRatio F K epsilon1 P)
      (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)) := by
  let htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    omega
  let u := lowNormalizedRatio F K epsilon1 P
  let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  have hden : ∀ j : OddNormIndex F K,
      n + oddNormIndexScalar F K ht hres pi hpi hgen htpos j ≠ 0 := by
    intro j
    have hunit :
        ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) ≠ 0 :=
      Units.ne_zero _
    rw [lowOddTwistRepresentative_eq_normalized] at hunit
    exact (mul_ne_zero_iff.mp hunit).2
  refine
    { norm_u := ?_
      zeroNumerator_ne_zero := ?_
      zeroDenominator_ne_zero := ?_
      numerator_ne_zero := ?_
      denominator_ne_zero := ?_ }
  · exact lowNormalizedRatio_norm F K epsilon1 P
  · have hunit :
        ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WUp : Kˣ) : K) ≠ 0 :=
      Units.ne_zero _
    rw [lowOddUpstairsRepresentative_eq_normalized] at hunit
    apply (Algebra.norm_ne_zero_iff).2
    intro hz
    apply hunit
    rw [hz, mul_zero]
  · unfold oddNormCorrectionDenominator
    apply Finset.prod_ne_zero_iff.mpr
    intro j _hj
    by_cases hj : j = 0
    · subst j
      have hn : n ≠ 0 := by
        dsimp only [n, lowOddNormalizedNorm]
        exact div_ne_zero
          (mul_ne_zero (Units.ne_zero (lowEpsilon F K epsilon1))
            (Units.ne_zero P.beta))
          (Units.ne_zero P.alpha)
      simpa only [oddNormAllIndexScalar,
        (highParameter_intermediate_teichmuller_eq_zero_iff F
          (Module.finrank F K)
          (residueCharacteristic_eq_degree_of_positive_break F K ht htpos
            pi hpi hgen) 0).2 rfl, add_zero] using hn
    · simpa only [oddNormIndexScalar, oddNormAllIndexScalar] using
        hden ⟨j, hj⟩
  · intro j
    apply (Algebra.norm_ne_zero_iff).2
    intro hzero
    have hu : u = -algebraMap F K
        (oddNormIndexScalar F K ht hres pi hpi hgen htpos j) := by
      exact eq_neg_of_add_eq_zero_left hzero
    have hnormNeg (x : K) : norm F K (-x) = -norm F K x := by
      rw [show -x = algebraMap F K (-1 : F) * x by simp, map_mul,
        norm_algebraMap, hodd.neg_one_pow, neg_one_mul]
    have hnEq : n =
        -oddNormIndexScalar F K ht hres pi hpi hgen htpos j := by
      have hnu : norm F K u = n := lowNormalizedRatio_norm F K epsilon1 P
      rw [hu, hnormNeg, norm_algebraMap] at hnu
      unfold oddNormIndexScalar at hnu
      rw [highParameter_intermediate_teichmuller_pow F
        (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_break F K ht htpos
          pi hpi hgen)
        (j : ZMod (Module.finrank F K))] at hnu
      exact hnu.symm
    exact hden j (by rw [hnEq]; simp)
  · exact hden
end Low
section IndexBridge
variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [NeZero (Module.finrank F K)]
  [Fact (Module.finrank F K).Prime]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (htpos : 0 < t)
local instance : Fact (residueCharacteristic F).Prime := ⟨residueCharacteristic_prime F⟩
/-- The correction-formula unit index viewed as the phase-reduction nonidentity index. -/
noncomputable def wildOddCorrectionIndexToPhase
    (j : (ZMod (residueCharacteristic F))ˣ) : OddNormIndex F K :=
  ⟨(ZMod.ringEquivCongr
      (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
        hpi hgen)) (j : ZMod (residueCharacteristic F)), by
    intro hz
    let e := ZMod.ringEquivCongr
      (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
        hpi hgen)
    have hz' : e (j : ZMod (residueCharacteristic F)) = e 0 := by
      simpa only [map_zero] using hz
    exact Units.ne_zero j (e.injective hz')⟩
/-- The full canonical equivalence behind the correction/phase reindexing. -/
noncomputable def wildOddCorrectionIndexEquiv :
    (ZMod (residueCharacteristic F))ˣ ≃ OddNormIndex F K :=
  unitsEquivNeZero.trans
    ((ZMod.ringEquivCongr
      (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
        hpi hgen)).toEquiv.subtypeEquiv (fun j => by
          constructor
          · intro hj hz
            exact hj ((ZMod.ringEquivCongr
              (residueCharacteristic_eq_degree_of_positive_break F K ht
                htpos pi hpi hgen)).injective (by simpa using hz))
          · intro hj hz
            apply hj
            change (ZMod.ringEquivCongr
              (residueCharacteristic_eq_degree_of_positive_break F K ht
                htpos pi hpi hgen)) j = 0
            rw [hz]
            exact map_zero _))
@[simp]
theorem wildOddCorrectionIndexEquiv_apply
    (j : (ZMod (residueCharacteristic F))ˣ) :
    wildOddCorrectionIndexEquiv (F := F) (K := K) (ht := ht) (pi := pi)
      (hpi := hpi) (hgen := hgen) (htpos := htpos) j =
    wildOddCorrectionIndexToPhase (F := F) (K := K) (ht := ht) (pi := pi)
      (hpi := hpi) (hgen := hgen) (htpos := htpos) j := by
  apply Subtype.ext
  rfl
/-- The two independently defined Teichmüller index scalars are literal equals after the canonical degree/characteristic transport. -/
theorem wildOdd_indexScalar_eq_primeFieldLift
    (j : (ZMod (residueCharacteristic F))ˣ) :
    oddNormIndexScalar F K ht hres pi hpi hgen htpos
        (wildOddCorrectionIndexToPhase (F := F) (K := K) (ht := ht) (pi := pi)
          (hpi := hpi) (hgen := hgen) (htpos := htpos) j) =
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) := by
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  unfold oddNormIndexScalar wildOddCorrectionIndexToPhase
  unfold highIntermediateTeichmullerScalar wildOddPrimeFieldLift
  change
    ((teichmuller F
      (ZMod.cast ((ZMod.ringEquivCongr hchar)
        (j : ZMod (residueCharacteristic F))) : ResidueField F) :
          ringOfIntegers F) : F) =
      ((teichmuller F
        (ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F)
          (j : ZMod (residueCharacteristic F))) : ringOfIntegers F) : F)
  congr 2
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val,
    ZMod.ringEquivCongr_val]
/-- Full-index version of the same canonical Teichmüller bridge. -/
theorem wildOdd_allIndexScalar_eq_primeFieldLift
    (j : ZMod (residueCharacteristic F)) :
    oddNormAllIndexScalar F K ht hres pi hpi hgen htpos
        ((ZMod.ringEquivCongr
          (residueCharacteristic_eq_degree_of_positive_break F K ht htpos
            pi hpi hgen)) j) =
      wildOddPrimeFieldLift F j := by
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  unfold oddNormAllIndexScalar
  unfold highIntermediateTeichmullerScalar wildOddPrimeFieldLift
  change
    ((teichmuller F
      (ZMod.cast ((ZMod.ringEquivCongr hchar) j) : ResidueField F) :
          ringOfIntegers F) : F) =
      ((teichmuller F
        (ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F)
          j) : ringOfIntegers F) : F)
  congr 2
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val,
    ZMod.ringEquivCongr_val]
end IndexBridge
section HighConstructor
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
local instance : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance : Fact (Module.finrank F K).Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
/-- The High normalized ratio supplies the correction datum directly; its boundary clause is vacuous because this branch is strict above `t+1`. -/
noncomputable def wildOddHighCorrectionData
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF) :
    WildOddCorrectionData F K (t + 1) := by
  let m := (data.twistData 1).conductor
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  refine
    { m := m
      u := u
      odd_residueCharacteristic := ?_
      two_le_T := by omega
      two_le_m := by
        have hm := hF.conductor_gt_one
        dsimp only [m]
        omega
      m_le := by
        dsimp only [m]
        omega
      degree_eq := hchar.symm
      residueDegree_eq_one := hres
      traceLowerBound := ?_
      ord_u := ?_
      boundary_noncancellation := ?_ }
  · intro hp2
    obtain ⟨k, hk⟩ := hodd
    rw [hp2] at hchar
    omega
  · simpa only [hchar] using
      (traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen)
  · rw [highOddNormalizedRatio_order]
    congr 2
    dsimp only [wildOddCorrectionOffset, m]
    omega
  · intro ha
    dsimp only [wildOddCorrectionOffset, m] at ha
    omega
end HighConstructor
section LowConstructor
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
  (hodd : Odd (Module.finrank F K))
  (WTwist : ∀ j : OddNormIndex F K,
    LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table j)
local instance : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance : Fact (Module.finrank F K).Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
local instance : Fact (residueCharacteristic F).Prime := ⟨residueCharacteristic_prime F⟩
/-- The Low normalized ratio supplies the correction datum. At its genuine boundary, actual stationary twist representatives prove the unit valuation of every transported nonzero denominator. -/
noncomputable def wildOddLowCorrectionData :
    WildOddCorrectionData F K (t + 1) := by
  let m := (data.twistData 1).conductor
  let htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    omega
  let u := lowNormalizedRatio F K epsilon1 P
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  refine
    { m := m
      u := u
      odd_residueCharacteristic := ?_
      two_le_T := hT
      two_le_m := by
        have hm := hF.conductor_gt_one
        dsimp only [m]
        omega
      m_le := by
        dsimp only [m]
        omega
      degree_eq := hchar.symm
      residueDegree_eq_one := hres
      traceLowerBound := ?_
      ord_u := ?_
      boundary_noncancellation := ?_ }
  · intro hp2
    obtain ⟨k, hk⟩ := hodd
    rw [hp2] at hchar
    omega
  · simpa only [hchar] using
      (traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen)
  · rw [lowNormalizedRatio_order F K epsilon1 hepsilon1 P]
    norm_cast
    dsimp only [wildOddCorrectionOffset, m]
    omega
  · intro ha j
    have hboundary : m = t + 1 := by
      dsimp only [wildOddCorrectionOffset] at ha
      omega
    have hboundary' : (data.twistData 1).conductor = t + 1 := by
      simpa only [m] using hboundary
    by_cases hj : j = 0
    · subst j
      rw [wildOddPrimeFieldLift_zero, add_zero, ord_norm, hres, one_nsmul]
      simpa only [u, hboundary', Nat.sub_self, Nat.cast_zero,
        WithTop.coe_zero] using
          (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)
    · let ju : (ZMod (residueCharacteristic F))ˣ := Units.mk0 j hj
      let idx : OddNormIndex F K :=
        wildOddCorrectionIndexToPhase (F := F) (K := K) (ht := ht) (pi := pi)
          (hpi := hpi) (hgen := hgen) (htpos := htpos) ju
      let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (idx : ZMod (Module.finrank F K)) idx.property
      let hCrit := lowCriticalConductorDecomposition (t := t) hT
      have hrepOrd : ord F ((WTwist idx).representative : F) =
          (0 : WithTop ℤ) := by
        exact stationaryCoefficientClass_representative_ord_zero F K F
          twist data.baseAddChar hCrit delta hdelta
            (WTwist idx).representative (by
            simpa only [twist, hCrit] using (WTwist idx).represents)
      have hunitOrd : ord F
          (((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table idx (WTwist idx) : Fˣ) :
                F)) = (0 : WithTop ℤ) := by
        unfold lowOddTwistRepresentativeUnit
        rw [StationaryClassRepresentative.coe_unit]
        simpa using hrepOrd
      have halphaOrd : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
        simp only [LowStationaryNormRepresentativePair.alpha, coe_normUnits]
        rw [ord_norm, hres, one_nsmul,
          P.alphaRepresentative.source_order]
        rfl
      have heq := lowOddTwistRepresentative_eq_normalized F K ht hres pi
        hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table idx (WTwist idx)
      have hordEq := congrArg (ord F) heq
      rw [hunitOrd, ord_mul, halphaOrd, zero_add] at hordEq
      have hdenOrd : ord F
          (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) +
            oddNormIndexScalar F K ht hres pi hpi hgen htpos idx) =
            (0 : WithTop ℤ) := hordEq.symm
      change ord F
        (norm F K (lowNormalizedRatio F K epsilon1 P) +
          wildOddPrimeFieldLift F j) = (0 : WithTop ℤ)
      rw [lowNormalizedRatio_norm F K epsilon1 P]
      change ord F
        (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) +
          wildOddPrimeFieldLift F j) = (0 : WithTop ℤ)
      have hscalar :
          oddNormIndexScalar F K ht hres pi hpi hgen htpos idx =
            wildOddPrimeFieldLift F j := by
        simpa only [idx, ju, Units.val_mk0] using
          (wildOdd_indexScalar_eq_primeFieldLift F K ht hres pi
            hpi hgen htpos ju)
      rw [← hscalar]
      exact hdenOrd
end LowConstructor
section UnitBridge
variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [NeZero (Module.finrank F K)]
  [Fact (Module.finrank F K).Prime]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (htpos : 0 < t)
  {u : K} {n : F}
  (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos u n)
  (D : WildOddCorrectionData F K (t + 1))
  (hDu : D.u = u)
local instance : Fact (residueCharacteristic F).Prime := ⟨residueCharacteristic_prime F⟩
include C hDu
/-- The full exceptional denominator agrees after reindexing by the degree/characteristic equality. -/
theorem wildOdd_phaseCorrectionDenominator_eq :
    oddNormCorrectionDenominator F K ht hres pi hpi hgen htpos n =
      D.primeFieldProduct := by
  have hDn : D.n = n := by
    rw [WildOddCorrectionData.n, hDu, C.norm_u]
  let e := ZMod.ringEquivCongr
    (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen)
  unfold oddNormCorrectionDenominator WildOddCorrectionData.primeFieldProduct
  rw [← Equiv.prod_comp e.toEquiv
    (fun k : ZMod (Module.finrank F K) ↦
      n + oddNormAllIndexScalar F K ht hres pi hpi hgen htpos k)]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [hDn]
  congr 1
  exact wildOdd_allIndexScalar_eq_primeFieldLift F K ht hres pi
    hpi hgen htpos j
/-- Every nonzero-index correction unit is definitionally the same unit in the phase and correction APIs after canonical index transport. -/
theorem wildOdd_phaseCorrection_z_eq
    (j : (ZMod (residueCharacteristic F))ˣ) :
    OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C
        (wildOddCorrectionIndexToPhase (F := F) (K := K) (ht := ht) (pi := pi)
          (hpi := hpi) (hgen := hgen) (htpos := htpos) j) =
      D.z j := by
  have hDn : D.n = n := by
    rw [WildOddCorrectionData.n, hDu, C.norm_u]
  apply Units.ext
  simp only [OddNormCorrectionUnitData.coe_z, WildOddCorrectionData.coe_z,
    WildOddCorrectionData.zValue, WildOddCorrectionData.denominator]
  rw [hDu, hDn,
    wildOdd_indexScalar_eq_primeFieldLift F K ht hres pi hpi
      hgen htpos j]
/-- The exceptional correction unit also agrees; its product denominator is transported before using the correction formula's exact norm identity. -/
theorem wildOdd_phaseCorrection_zZero_eq :
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C =
      D.zZero := by
  have hDn : D.n = n := by
    rw [WildOddCorrectionData.n, hDu, C.norm_u]
  apply Units.ext
  rw [OddNormCorrectionUnitData.coe_zZero, WildOddCorrectionData.coe_zZero]
  rw [wildOdd_phaseCorrectionDenominator_eq
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi) (hpi := hpi)
      (hgen := hgen) (htpos := htpos) (C := C) (D := D) hDu]
  have hnorm := D.norm_sub_eq_primeFieldProduct_mul
  rw [hDu, hDn] at hnorm
  rw [hnorm]
  simp only [WildOddCorrectionData.coe_zZero]
  field_simp [D.primeFieldProduct_ne_zero]
/-- The exact phase coordinate assembled from the actual correction units is the closed correction coordinate, after the sole canonical reindexing. -/
theorem wildOdd_phaseCorrectionCoordinate_eq :
    wildOddCorrectionX D =
      trace F K u + n *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C :
          Fˣ) : F) - 1) +
      ∑ j : OddNormIndex F K,
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j :
            Fˣ) : F) - 1) := by
  classical
  have hDn : D.n = n := by
    rw [WildOddCorrectionData.n, hDu, C.norm_u]
  rw [wildOddCorrectionX, hDu, hDn, D.xZero_eq]
  simp only [D.x_eq]
  rw [wildOdd_phaseCorrection_zZero_eq
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi) (hpi := hpi)
      (hgen := hgen) (htpos := htpos) (C := C) (D := D) hDu]
  congr 1
  let e := wildOddCorrectionIndexEquiv (F := F) (K := K) (ht := ht) (pi := pi)
    (hpi := hpi) (hgen := hgen) (htpos := htpos)
  calc
    (∑ j : (ZMod (residueCharacteristic F))ˣ,
        wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) *
          ((D.z j : F) - 1)) =
      ∑ j : (ZMod (residueCharacteristic F))ˣ,
        oddNormIndexScalar F K ht hres pi hpi hgen htpos (e j) *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C
            (e j) : Fˣ) : F) - 1) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [wildOddCorrectionIndexEquiv_apply]
              rw [wildOdd_indexScalar_eq_primeFieldLift
                F K ht hres pi hpi hgen htpos j]
              rw [wildOdd_phaseCorrection_z_eq
                (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
                  (hpi := hpi) (hgen := hgen) (htpos := htpos) (C := C)
                    (D := D) hDu j]
    _ = ∑ j : OddNormIndex F K,
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j :
            Fˣ) : F) - 1) :=
      by
        simpa only using (Equiv.sum_comp e
          (fun j : OddNormIndex F K =>
            oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
              (((OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C j :
                Fˣ) : F) - 1)))
end UnitBridge
local instance wildOddCorrectionPreparation_residuePrimeFact
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩
theorem wildOdd_unit_sub_one_mem_lattice
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {r : ℕ} (hr : 0 < r) (z : Fˣ) (hz : z ∈ unitFiltration F r) :
    (z : F) - 1 ∈ lattice F (r : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  exact (mem_unitFiltration_succ_iff_sub_mem_lattice F k z).1 hz
theorem wildOdd_positiveUnit_sub_one
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {r : ℕ} (hr : 0 < r) (z : Fˣ) (hz : z ∈ unitFiltration F r) :
    positiveUnitOfLattice F hr
        (⟨(z : F) - 1, wildOdd_unit_sub_one_mem_lattice F hr z hz⟩ :
          lattice F (r : ℤ)) = z := by
  apply Units.ext
  simp only [coe_positiveUnitOfLattice]
  ring
section High
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
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF)
local instance : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance : Fact (Module.finrank F K).Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
theorem wildOdd_highTauLinearization :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    ∀ x : lattice F (lowCriticalVariableDepth t : ℤ),
      tau.1 (positiveUnitOfLattice F (by
        have hT : 2 ≤ t + 1 := by omega
        exact (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos) x) =
      data.baseAddChar.character
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows * (x : F)) := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 :=
    lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  have htauEq : tau = ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K))) := by
    rfl
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK psiK hF
    hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let oneRep : lattice F 0 := ⟨1, by simp⟩
  have hclass : latticeQuotientMk F
      (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) oneRep =
      stationaryCoefficientClass F tauData data.baseAddChar hCrit gammaTau
        (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source) := by
    simpa only [tau, tauData, hCrit, gammaTau, oneRep, htauEq] using
      highNormGenerator_one_class F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  have hlinear := (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    tauData data.baseAddChar hCrit gammaTau
      (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source)
      oneRep).1 hclass
  intro x
  have hx := hlinear x
  have hx' :
      (lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          (positiveUnitOfLattice F hCrit.variableDepth_pos x) =
        data.baseAddChar.character ((oneRep : F) * (x : F) /
          (gammaTau : F)) := by
    simpa only [tauData, quasiCharDataOfIsConductor_character, tau,
      lowCriticalVariableDepth] using hx
  refine hx'.trans (congrArg data.baseAddChar.character ?_)
  dsimp only [oneRep, gammaTau, highOddExactCoefficient, highNormGamma]
  simp only [Units.val_div_eq_div_val, coe_normUnits]
  rw [source.alpha1_eq]
  field_simp [(Algebra.norm_ne_zero_iff).2
    (Units.ne_zero source.productRows.alpha1), Units.ne_zero gammaF]
theorem wildOdd_highPowerLinearization (j : OddNormIndex F K) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
    ∀ x : lattice F (lowCriticalVariableDepth t : ℤ),
      mu.1 (positiveUnitOfLattice F (by
        have hT : 2 ≤ t + 1 := by omega
        exact (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos) x) =
      data.baseAddChar.character
        (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows *
          oddNormIndexScalar F K ht hres pi hpi hgen htpos j * (x : F)) := by
  dsimp only
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro hz
    exact j.property (by
      have hz' := congrArg Multiplicative.toAdd hz
      simpa using hz')
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  let hCrit := lowCriticalConductorDecomposition (t := t) (by omega)
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK psiK hF
    hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
    hchar (j : ZMod (Module.finrank F K))
  let rep : lattice F 0 := ⟨lam, by
    rw [mem_lattice_zero_iff F]
    exact highParameter_intermediate_teichmuller_mem_integer F
      (Module.finrank F K) hchar (j : ZMod (Module.finrank F K))⟩
  have hclass : latticeQuotientMk F
      (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F muData data.baseAddChar hCrit gammaTau
        (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source) := by
    simpa only [mu, muData, hCrit, gammaTau, hchar, lam, rep] using
      highNormTeichmuller_class F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source j
  have hlinear := (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    muData data.baseAddChar hCrit gammaTau
      (highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source)
      rep).1 hclass
  intro x
  have hx := hlinear x
  have hx' : mu.1 (positiveUnitOfLattice F hCrit.variableDepth_pos x) =
      data.baseAddChar.character ((rep : F) * (x : F) /
        (gammaTau : F)) := by
    simpa only [muData, quasiCharDataOfIsConductor_character,
      lowCriticalVariableDepth] using hx
  refine hx'.trans (congrArg data.baseAddChar.character ?_)
  dsimp only [rep, lam, gammaTau, highNormGamma, highOddExactCoefficient,
    oddNormIndexScalar]
  simp only [Units.val_div_eq_div_val, coe_normUnits]
  rw [source.alpha1_eq]
  field_simp [(Algebra.norm_ne_zero_iff).2
    (Units.ne_zero source.productRows.alpha1), Units.ne_zero gammaF]
theorem wildOdd_highBaseLinearization :
    ∀ x : lattice F ((d + epsilon : ℕ) : ℤ),
      (data.twistData 1).character
          (positiveUnitOfLattice F hF.variableDepth_pos x) =
        data.baseAddChar.character
          (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF source.productRows *
            highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF source.productRows * (x : F)) := by
  let mu0 := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K)))
  let twist0 := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
    (data.twistData 1) mu0
  have hmu0 : mu0 = 1 := by
    dsimp only [mu0]
    rw [show Multiplicative.ofAdd (0 : ZMod (Module.finrank F K)) = 1 by
      rfl, map_one]
  have htwistChar : twist0.character = (data.twistData 1).character := by
    rw [show twist0.character = mu0.1 * (data.twistData 1).character by
      exact ramifiedNormCharacterOrbitTwistData_character F K ht hres pi hpi
        hgen (data.twistData 1) mu0, hmu0]
    ext z
    simp
  let h0 := source.productRows.factorDecomposition
    (0 : ZMod (Module.finrank F K))
  let hg0 := source.productRows.factorDenominator
    (0 : ZMod (Module.finrank F K))
  let R0 := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows (0 : ZMod (Module.finrank F K))
  let rep0 : lattice F 0 := R0.representative
  have hlinear := (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    twist0 data.baseAddChar h0 gammaF hg0 rep0).1 (by
      simpa only [twist0, h0, hg0, R0, rep0] using R0.represents)
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  have hscalar0 : highIntermediateTeichmullerScalar F
      (Module.finrank F K) hchar (0 : ZMod (Module.finrank F K)) = 0 :=
    (highParameter_intermediate_teichmuller_eq_zero_iff F
      (Module.finrank F K) hchar 0).2 rfl
  have hrep0 : (rep0 : F) = norm F K (source.productRows.beta1 : K) := by
    change highOddLinearTwistValue F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows 0 = _
    unfold highOddLinearTwistValue oddNormAllIndexScalar
    have hs : highIntermediateTeichmullerScalar F (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
          hpi hgen) (0 : ZMod (Module.finrank F K)) = 0 := by
      simpa only [hchar] using hscalar0
    rw [hs]
    ring
  intro x
  have hx := hlinear x
  have hunit :
      positiveUnitOfLattice F h0.variableDepth_pos x =
        positiveUnitOfLattice F hF.variableDepth_pos x := by
    rfl
  have hx' : (data.twistData 1).character
      (positiveUnitOfLattice F hF.variableDepth_pos x) =
      data.baseAddChar.character ((rep0 : F) * (x : F) / (gammaF : F)) := by
    rw [← htwistChar, ← hunit]
    exact hx
  refine hx'.trans (congrArg data.baseAddChar.character ?_)
  rw [hrep0]
  dsimp only [highOddExactCoefficient, highOddNormalizedNorm,
    highOddNormalizedRatio]
  simp only [Units.val_div_eq_div_val, coe_normUnits]
  rw [WildOddCorrectionData.norm_div (F := F) (K := K)]
  field_simp [(Algebra.norm_ne_zero_iff).2
      (Units.ne_zero source.productRows.alpha1),
    Units.ne_zero gammaF, Units.ne_zero source.productRows.alpha1]
end High
section Low
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
local instance : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance : Fact (Module.finrank F K).Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
theorem wildOdd_lowTauLinearization :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    ∀ x : lattice F (lowCriticalVariableDepth t : ℤ),
      tau.1 (positiveUnitOfLattice F
        (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos x) =
      data.baseAddChar.character
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
          (x : F)) := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 :=
    lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let rep : lattice F 0 :=
    ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
  have hclass : latticeQuotientMk F
      (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F tauData data.baseAddChar hCrit delta
        hdelta := by
    simpa only [tauData, tau, hCrit, rep] using P.alpha_norm_class
  have hlinear := (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    tauData data.baseAddChar hCrit delta hdelta rep).1 hclass
  intro x
  have hx := hlinear x
  have hx' : tau.1 (positiveUnitOfLattice F hCrit.variableDepth_pos x) =
      data.baseAddChar.character ((rep : F) * (x : F) / (delta : F)) := by
    simpa only [tauData, quasiCharDataOfIsConductor_character,
      lowCriticalVariableDepth] using hx
  refine hx'.trans (congrArg data.baseAddChar.character ?_)
  dsimp only [rep, lowOddExactCoefficient]
  simp only [Units.val_div_eq_div_val]
  ring
theorem wildOdd_lowPowerLinearization (j : OddNormIndex F K) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
    ∀ x : lattice F (lowCriticalVariableDepth t : ℤ),
      mu.1 (positiveUnitOfLattice F
        (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos x) =
      data.baseAddChar.character
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
          oddNormIndexScalar F K ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) j * (x : F)) := by
  dsimp only
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let rep : lattice F 0 :=
    ⟨((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j : Fˣ) : F),
      (mem_lattice_and_not_mem_succ_iff F).2 (by
        unfold lowOddNormRepresentativeUnit oddNormIndexUnit
          oddNormIndexScalar
        simp only [Units.val_mul, Units.val_mk0]
        rw [ord_mul,
          highParameter_intermediate_teichmuller_ord_eq_zero F
            (Module.finrank F K)
            (residueCharacteristic_eq_degree_of_positive_break F K ht
              (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
            (j : ZMod (Module.finrank F K)) j.property]
        simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits]
          using P.alphaRepresentative.norm_order) |>.1⟩
  have hclass : latticeQuotientMk F
      (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep =
      stationaryCoefficientClass F powerData data.baseAddChar hCrit delta
        hdelta := by
    simpa only [tau, powerData, hCrit, rep] using
      (lowOddNormRepresentative_class_eq_powerCharacter F K ht hres pi hpi
        hgen data hF delta epsilon1 hdelta hT hgammaF P j)
  have hlinear := (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    powerData data.baseAddChar hCrit delta hdelta rep).1 hclass
  intro x
  have hx := hlinear x
  have hmu : ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K))) =
      tau ^ (j : ZMod (Module.finrank F K)).val :=
    lowNormCharacterGenerator_pow F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K))
  have hx' :
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))).1
          (positiveUnitOfLattice F hCrit.variableDepth_pos x) =
      data.baseAddChar.character ((rep : F) * (x : F) / (delta : F)) := by
    rw [hmu]
    simpa only [powerData, quasiCharDataOfIsConductor_character,
      lowCriticalVariableDepth] using hx
  refine hx'.trans (congrArg data.baseAddChar.character ?_)
  dsimp only [rep, lowOddNormRepresentativeUnit, oddNormIndexUnit,
    lowOddExactCoefficient]
  simp only [Units.val_mul, Units.val_mk0, Units.val_div_eq_div_val]
  ring
theorem wildOdd_lowBaseLinearization :
    ∀ x : lattice F ((d + epsilon : ℕ) : ℤ),
      (data.twistData 1).character
          (positiveUnitOfLattice F hF.variableDepth_pos x) =
      data.baseAddChar.character
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
          lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
          (x : F)) := by
  let rep : lattice F 0 :=
    ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
  have hclass : latticeQuotientMk F (Int.natCast_nonneg d) rep =
      stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
        (lowGammaF F K delta epsilon1) hgammaF := by
    simpa only [rep] using P.beta_norm_class
  have hlinear := (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    (data.twistData 1) data.baseAddChar hF (lowGammaF F K delta epsilon1)
      hgammaF rep).1 hclass
  intro x
  have hx := hlinear x
  refine hx.trans (congrArg data.baseAddChar.character ?_)
  dsimp only [rep, lowGammaF, lowEpsilon, lowOddExactCoefficient,
    lowOddNormalizedNorm]
  simp only [Units.val_div_eq_div_val, coe_normUnits]
  field_simp [Units.ne_zero P.alpha, Units.ne_zero delta,
    (Algebra.norm_ne_zero_iff).2 (Units.ne_zero epsilon1)]
end Low
open scoped BigOperators
local instance wildOddCorrectionPreparation_degreePrime
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩
local instance wildOddCorrectionPreparation_degreeNeZero
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] : NeZero (Module.finrank F K) :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩
local instance wildOddCorrectionPreparation_residuePrime
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩
theorem wildOdd_stationaryVariableDepth_eq_ceilDiv
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon) :
    d + epsilon = m ⌈/⌉ 2 := by
  have he : epsilon = 0 ∨ epsilon = 1 := by
    have := h.epsilon_le_one
    omega
  rcases he with rfl | rfl
  · rw [h.conductor_eq, Nat.ceilDiv_eq_add_pred_div]
    simp only [Nat.add_zero]
    rw [show 2 * d + 2 - 1 = 1 + 2 * d by omega,
      Nat.add_mul_div_left 1 d (by omega : 0 < 2)]
    norm_num
  · rw [h.conductor_eq, Nat.ceilDiv_eq_add_pred_div]
    rw [show 2 * d + 1 + 2 - 1 = (d + 1) * 2 by omega,
      Nat.mul_div_left (d + 1) (by omega : 0 < 2)]
section UnitFiltrationBridge
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
  (htpos : 0 < t)
  {u : K} {n : F}
  (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos u n)
  (D : WildOddCorrectionData F K (t + 1))
  (hDu : D.u = u)
include D hDu
theorem wildOdd_phaseCorrectionUnit_mem_halfFiltration
    (idx : OddNormIndex F K) :
    OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx ∈
      unitFiltration F ((t + 1) ⌈/⌉ 2) := by
  let e := wildOddCorrectionIndexEquiv (F := F) (K := K) (ht := ht) (pi := pi)
    (hpi := hpi) (hgen := hgen) (htpos := htpos)
  let j := e.symm idx
  have hz := WildOddCorrectionData.z_mem_halfFiltration D j
  have heq : OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx =
      D.z j := by
    rw [show idx = e j by exact (e.apply_symm_apply idx).symm]
    rw [wildOddCorrectionIndexEquiv_apply]
    exact wildOdd_phaseCorrection_z_eq F K ht hres pi hpi hgen
      htpos C D hDu j
  rwa [heq]
end UnitFiltrationBridge
section HighActualInput
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
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF)
/-- Assemble the strict High branch's actual correction units, closed
coordinate, and character linearizations into the input required by the
table-backed odd phase assembly. -/
noncomputable def wildOddHighActualRowsCorrectionInput :
    HighOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source := by
  let C := wildOddHighCorrectionUnits F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let Corr := wildOddHighCorrectionData F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  refine
    { correctionUnits := C
      X := wildOddCorrectionX Corr
      X_eq := ?_
      chiLinearization := ?_
      powerLinearization := ?_ }
  · exact wildOdd_phaseCorrectionCoordinate_eq F K ht hres pi hpi hgen
      htpos C Corr (by rfl)
  · have hdepth : d + epsilon = Corr.m ⌈/⌉ 2 := by
      rw [show Corr.m = (data.twistData 1).conductor by rfl]
      exact wildOdd_stationaryVariableDepth_eq_ceilDiv hF
    have hz : OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C ∈
        unitFiltration F (d + epsilon) := by
      rw [hdepth]
      rw [wildOdd_phaseCorrection_zZero_eq F K ht hres pi hpi
        hgen htpos C Corr (by rfl)]
      exact Corr.zZero_mem_conductorHalfFiltration
    let x : lattice F ((d + epsilon : ℕ) : ℤ) :=
      ⟨(OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C : F) - 1,
        wildOdd_unit_sub_one_mem_lattice F hF.variableDepth_pos _ hz⟩
    have hb := wildOdd_highBaseLinearization F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source x
    have hunit := wildOdd_positiveUnit_sub_one F hF.variableDepth_pos _ hz
    rw [hunit, data.twistData_character, data.baseAddChar_character] at hb
    simpa only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
      ContinuousQuasiChar.one_apply, one_mul, x] using hb
  · intro idx
    have hz : OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx ∈
        unitFiltration F (lowCriticalVariableDepth t) := by
      rw [lowCriticalVariableDepth_eq_ceilDiv]
      exact wildOdd_phaseCorrectionUnit_mem_halfFiltration F K ht hres pi hpi
        hgen htpos C Corr (by rfl) idx
    let hcrit := (lowCriticalConductorDecomposition (t := t) (by omega)).variableDepth_pos
    let x : lattice F (lowCriticalVariableDepth t : ℤ) :=
      ⟨(OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx : F) - 1,
        wildOdd_unit_sub_one_mem_lattice F hcrit _ hz⟩
    have hp := wildOdd_highPowerLinearization F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source idx x
    have hunit : positiveUnitOfLattice F
        (lowCriticalConductorDecomposition (t := t) (by omega)).variableDepth_pos
          x = OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, x]
      ring
    rw [data.baseAddChar_character] at hp
    calc
      _ = (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (idx : ZMod (Module.finrank F K)))).1
          (positiveUnitOfLattice F
            (lowCriticalConductorDecomposition (t := t) (by omega)).variableDepth_pos
              x) := congrArg _ hunit.symm
      _ = globalPsi
          (highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF source.productRows *
            oddNormIndexScalar F K ht hres pi hpi hgen htpos idx * (x : F)) :=
        hp
      _ = _ := by rfl
end HighActualInput
section LowActualInput
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
  (hodd : Odd (Module.finrank F K))
  (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table)
  (WTwist : ∀ j : OddNormIndex F K,
    LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table j)
/-- Assemble the Low strict-or-boundary branch's actual correction units,
closed coordinate, and character linearizations into the input required by
the table-backed odd phase assembly. -/
noncomputable def wildOddLowActualRowsCorrectionInput :
    LowOddActualRowsCorrectionInput F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table hodd WUp WTwist := by
  let htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    omega
  let C := wildOddLowCorrectionUnits F K ht hres pi hpi hgen data chiK psiK
    hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table hodd WUp WTwist
  let Corr := wildOddLowCorrectionData F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table hodd WTwist
  refine
    { correctionUnits := C
      X := wildOddCorrectionX Corr
      X_eq := ?_
      chiLinearization := ?_
      powerLinearization := ?_ }
  · exact wildOdd_phaseCorrectionCoordinate_eq F K ht hres pi hpi hgen
      htpos C Corr (by rfl)
  · have hdepth : d + epsilon = Corr.m ⌈/⌉ 2 := by
      rw [show Corr.m = (data.twistData 1).conductor by rfl]
      exact wildOdd_stationaryVariableDepth_eq_ceilDiv hF
    have hz : OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C ∈
        unitFiltration F (d + epsilon) := by
      rw [hdepth]
      rw [wildOdd_phaseCorrection_zZero_eq F K ht hres pi hpi
        hgen htpos C Corr (by rfl)]
      exact WildOddCorrectionData.zZero_mem_conductorHalfFiltration Corr
    let x : lattice F ((d + epsilon : ℕ) : ℤ) :=
      ⟨(OddNormCorrectionUnitData.zZero ht hres pi hpi hgen htpos C : F) - 1,
        wildOdd_unit_sub_one_mem_lattice F hF.variableDepth_pos _ hz⟩
    have hb := wildOdd_lowBaseLinearization F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P x
    have hunit := wildOdd_positiveUnit_sub_one F hF.variableDepth_pos _ hz
    rw [hunit, data.twistData_character, data.baseAddChar_character] at hb
    simpa only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
      ContinuousQuasiChar.one_apply, one_mul, x] using hb
  · intro idx
    have hz : OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx ∈
        unitFiltration F (lowCriticalVariableDepth t) := by
      rw [lowCriticalVariableDepth_eq_ceilDiv]
      exact wildOdd_phaseCorrectionUnit_mem_halfFiltration F K ht hres pi hpi
        hgen htpos C Corr (by rfl) idx
    let hcrit := (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos
    let x : lattice F (lowCriticalVariableDepth t : ℤ) :=
      ⟨(OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx : F) - 1,
        wildOdd_unit_sub_one_mem_lattice F hcrit _ hz⟩
    have hp := wildOdd_lowPowerLinearization F K ht hres pi hpi hgen data
      hF delta epsilon1 hdelta hT hgammaF P idx x
    have hunit : positiveUnitOfLattice F
        (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos x =
          OddNormCorrectionUnitData.z ht hres pi hpi hgen htpos C idx := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, x]
      ring
    rw [data.baseAddChar_character] at hp
    calc
      _ = (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (idx : ZMod (Module.finrank F K)))).1
          (positiveUnitOfLattice F
            (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos
              x) := congrArg _ hunit.symm
      _ = globalPsi
          (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
            oddNormIndexScalar F K ht hres pi hpi hgen htpos idx * (x : F)) :=
        hp
      _ = _ := by rfl
end LowActualInput
/-- Branch-independent correction package retaining the exact phase assembly,
closed correction coordinate, complete residual-phase quotient, and
nontrivial norm-character linearization prepared from `WildOddPhasePrepared`. -/
structure WildOddCorrectionPrepared
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (P : WildOddPhasePrepared F K t ht hres pi hpi hgen chiF psiF) where
  assembly : ExactOddPhaseAssembly F K chiF.character psiF.character P.data
    P.phases (t := t) (m := (P.data.twistData 1).conductor)
      (OddNormIndex F K)
  correction : WildOddCorrectionData F K (t + 1)
  correction_conductor : correction.m = (P.data.twistData 1).conductor
  correction_element : correction.u = assembly.u
  correctionCoordinate : assembly.X = wildOddCorrectionX correction
  residualPhase_eq : assembly.residualPhase =
    wildOddCompleteResidualPhaseQuotient F (Module.finrank F K)
      P.degree_eq.symm P.residualAddChar P.parity
  linearizationDepth : ℕ
  linearizationDepth_pos : 0 < linearizationDepth
  linearizationDepth_le : linearizationDepth ≤ t + 1
  tau : NormCharacter F K
  tau_ne_one : tau ≠ 1
  tauLinearization : ∀ x : lattice F (linearizationDepth : ℤ),
    tau.1 (positiveUnitOfLattice F linearizationDepth_pos x) =
      P.data.baseAddChar.character (assembly.A * (x : F))
/-- Construct the common correction package by following the actual High or
Low branch data while preserving its selected rows and correction coordinate. -/
noncomputable def wildOddCorrectionPrepared
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (P : WildOddPhasePrepared F K t ht hres pi hpi hgen chiF psiF) :
    WildOddCorrectionPrepared F K t ht hres pi hpi hgen chiF psiF P := by
  let depth := lowCriticalVariableDepth t
  have hT : 2 ≤ t + 1 := by
    have hd := P.conductorDecomposition.floorDepth_pos
    have hn := P.nonstable
    omega
  have hdepthPos : 0 < depth := by
    exact (lowCriticalConductorDecomposition (t := t) hT).variableDepth_pos
  have hdepthLe : depth ≤ t + 1 := by
    have hv := (lowCriticalConductorDecomposition (t := t) hT).variableDepth_le_conductor
    simpa only [depth, lowCriticalVariableDepth] using hv
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 :=
    lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  cases P.branch with
  | high H =>
      let R := wildOddHighActualRowsCorrectionInput F K ht hres pi hpi hgen
        P.data H.chiK H.psiK P.dataConductorDecomposition H.hK H.hminimal
          H.hchi H.hpsi H.hodd H.htpos H.hstrict H.hupper H.gammaF H.hgammaF
            H.source
      let B := highActualRowsTableBackedExactOddAssembly F K ht hres pi hpi
        hgen P.data P.phases H.chiK H.psiK P.dataConductorDecomposition H.hK
          H.hminimal H.hchi H.hpsi H.hodd H.htpos H.hstrict H.hupper H.gammaF
            H.hgammaF H.source R H.CUp H.CNorm H.CTwist H.hExtension H.hNorm
              H.hTwist
      let Corr := wildOddHighCorrectionData F K ht hres pi hpi hgen
        P.data H.chiK H.psiK P.dataConductorDecomposition H.hK H.hminimal
          H.hchi H.hpsi H.hodd H.htpos H.hstrict H.hupper H.gammaF H.hgammaF
            H.source
      refine
        { assembly := B.tableBacked.assembly
          correction := Corr
          correction_conductor := by rfl
          correction_element := ?_
          correctionCoordinate := ?_
          residualPhase_eq := ?_
          linearizationDepth := depth
          linearizationDepth_pos := hdepthPos
          linearizationDepth_le := hdepthLe
          tau := tau
          tau_ne_one := htau
          tauLinearization := ?_ }
      · exact B.normalizedRatio_source.symm
      · exact B.correctionCoordinate_source
      · change P.phases.criticalNumerator / P.phases.criticalDenominator = _
        exact P.rawResidualPhase_eq
      · intro x
        have hx := wildOdd_highTauLinearization F K ht hres pi hpi hgen
          P.data H.chiK H.psiK P.dataConductorDecomposition H.hK H.hminimal
            H.hchi H.hpsi H.hodd H.htpos H.hstrict H.hupper H.gammaF
              H.hgammaF H.source x
        rw [B.coefficient_source]
        exact hx
  | low L =>
      let R := wildOddLowActualRowsCorrectionInput F K ht hres pi hpi hgen
        P.data L.chiK L.psiK P.dataConductorDecomposition L.hminimal L.hchi
          L.hpsi L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT
            L.hgammaF L.hgammaK L.P L.table L.hodd L.WUp L.WTwist
      let B := lowActualRowsTableBackedExactOddAssembly F K ht hres pi hpi
        hgen P.data P.phases L.chiK L.psiK P.dataConductorDecomposition
          L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
            L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.hodd L.WUp
              L.WTwist R L.CUp L.CBase L.CNorm L.CTwist L.hExtension L.hBase
                L.hNorm L.hTwist
      let Corr := wildOddLowCorrectionData F K ht hres pi hpi hgen
        P.data L.chiK L.psiK P.dataConductorDecomposition L.hminimal L.hchi
          L.hpsi L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT
            L.hgammaF L.hgammaK L.P L.table L.hodd L.WTwist
      refine
        { assembly := B.tableBacked.assembly
          correction := Corr
          correction_conductor := by rfl
          correction_element := ?_
          correctionCoordinate := ?_
          residualPhase_eq := ?_
          linearizationDepth := depth
          linearizationDepth_pos := hdepthPos
          linearizationDepth_le := hdepthLe
          tau := tau
          tau_ne_one := htau
          tauLinearization := ?_ }
      · exact B.normalizedRatio_source.symm
      · exact B.correctionCoordinate_source
      · change P.phases.criticalNumerator / P.phases.criticalDenominator = _
        exact P.rawResidualPhase_eq
      · intro x
        have hx := wildOdd_lowTauLinearization F K ht hres pi hpi hgen
          P.data P.dataConductorDecomposition L.delta L.epsilon1 L.hdelta L.hT
            L.hgammaF L.P x
        rw [B.coefficient_source]
        exact hx
section TransportAssembly
variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]
  {chi : ContinuousQuasiChar F} {psi : ContinuousAddChar F}
  {data : FirstMainComputationalData F K chi psi}
  {phases : FirstMainPhaseData F K chi psi data}
  {t m m' : ℕ} {I : Type*} [Fintype I]
noncomputable def wildOdd_transportExactOddAssembly
    (hm : m = m')
    (A : ExactOddPhaseAssembly F K chi psi data phases
      (t := t) (m := m) I) :
    ExactOddPhaseAssembly F K chi psi data phases
      (t := t) (m := m') I := by
  subst m'
  exact A
@[simp] theorem wildOdd_transportExactOddAssembly_A
    (hm : m = m')
    (A : ExactOddPhaseAssembly F K chi psi data phases
      (t := t) (m := m) I) :
    (wildOdd_transportExactOddAssembly hm A).A = A.A := by
  subst m'
  rfl
@[simp] theorem wildOdd_transportExactOddAssembly_u
    (hm : m = m')
    (A : ExactOddPhaseAssembly F K chi psi data phases
      (t := t) (m := m) I) :
    (wildOdd_transportExactOddAssembly hm A).u = A.u := by
  subst m'
  rfl
@[simp] theorem wildOdd_transportExactOddAssembly_X
    (hm : m = m')
    (A : ExactOddPhaseAssembly F K chi psi data phases
      (t := t) (m := m) I) :
    (wildOdd_transportExactOddAssembly hm A).X = A.X := by
  subst m'
  rfl
@[simp] theorem wildOdd_transportExactOddAssembly_residualPhase
    (hm : m = m')
    (A : ExactOddPhaseAssembly F K chi psi data phases
      (t := t) (m := m) I) :
    (wildOdd_transportExactOddAssembly hm A).residualPhase = A.residualPhase := by
  subst m'
  rfl
end TransportAssembly
noncomputable def wildOdd_transportParityReductionData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p q : ℕ)
    (hp : Fact p.Prime) (hcp : CharP (ResidueField F) p)
    (hq : Fact q.Prime) (hcq : CharP (ResidueField F) q)
    (h : p = q)
    (D : @WildOddParityReductionData F _ _ _ _ p hp hcp) :
    @WildOddParityReductionData F _ _ _ _ q hq hcq := by
  subst q
  exact D
noncomputable def wildOdd_transportResidualAddCharData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p q : ℕ) (h : p = q)
    (C : FrobeniusResidualAddCharData F p) :
    FrobeniusResidualAddCharData F q := by
  subst q
  exact C
theorem wildOdd_transportCompleteResidualPhaseQuotient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p q : ℕ)
    (hp : Fact p.Prime) (hcp : CharP (ResidueField F) p)
    (hq : Fact q.Prime) (hcq : CharP (ResidueField F) q)
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (D : @WildOddParityReductionData F _ _ _ _ p hp hcp)
    (h : p = q) :
    @wildOddCompleteResidualPhaseQuotient F _ _ _ _ q hq hcq
        (hchar.trans h)
        (wildOdd_transportResidualAddCharData F p q h C)
        (wildOdd_transportParityReductionData F p q hp hcp hq hcq h D) =
      @wildOddCompleteResidualPhaseQuotient F _ _ _ _ p hp hcp hchar C D := by
  subst q
  rfl
/-- Principal dispatch-facing wild-odd result: transport the prepared
degree-indexed assembly and residual data to residue-characteristic indexing
and package them with the exact correction and norm-character linearization. -/
noncomputable def wildOddNonstableHigherData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (P : WildOddPhasePrepared F K t ht hres pi hpi hgen chiF psiF) :
    WildOddNonstableHigherData F K t ht hres pi hpi hgen chiF psiF := by
  let C := wildOddCorrectionPrepared F K t ht hres pi hpi hgen chiF
    psiF P
  let hm : (P.data.twistData 1).conductor = chiF.conductor :=
    congrArg LocalQuasiCharData.conductor P.data_twist_one
  let assembly := wildOdd_transportExactOddAssembly hm C.assembly
  let residualAddChar := wildOdd_transportResidualAddCharData F
    (Module.finrank F K) (residueCharacteristic F) P.degree_eq
      P.residualAddChar
  let hpDegree : Fact (Module.finrank F K).Prime := inferInstance
  let hcpDegree : CharP (ResidueField F) (Module.finrank F K) := inferInstance
  let parityDegree := P.parity
  let hdegree := P.degree_eq
  let parity := wildOdd_transportParityReductionData F
    (Module.finrank F K) (residueCharacteristic F) hpDegree hcpDegree
      ⟨residueCharacteristic_prime F⟩ (ringChar.of_eq rfl) hdegree parityDegree
  refine
    { d := P.d
      epsilon := P.epsilon
      conductorDecomposition := P.conductorDecomposition
      nonstable := P.nonstable
      data := P.data
      phases := P.phases
      assembly := assembly
      residualAddChar := residualAddChar
      parity := parity
      residualPhase_eq := ?_
      correction := C.correction
      correction_conductor := C.correction_conductor.trans hm
      correction_element := ?_
      correctionCoordinate := ?_
      linearizationDepth := C.linearizationDepth
      linearizationDepth_pos := C.linearizationDepth_pos
      linearizationDepth_le := C.linearizationDepth_le
      tau := C.tau
      tau_ne_one := C.tau_ne_one
      tauLinearization := ?_ }
  · rw [wildOdd_transportExactOddAssembly_residualPhase]
    calc
      C.assembly.residualPhase =
          wildOddCompleteResidualPhaseQuotient F (Module.finrank F K)
            P.degree_eq.symm P.residualAddChar P.parity :=
        C.residualPhase_eq
      _ = @wildOddCompleteResidualPhaseQuotient F _ _ _ _
          (residueCharacteristic F) ⟨residueCharacteristic_prime F⟩
            (ringChar.of_eq rfl) rfl residualAddChar parity := by
        symm
        simpa only [residualAddChar, parity, hpDegree, hcpDegree, hdegree,
          parityDegree] using
          (wildOdd_transportCompleteResidualPhaseQuotient F
            (Module.finrank F K) (residueCharacteristic F) hpDegree hcpDegree
              ⟨residueCharacteristic_prime F⟩ (ringChar.of_eq rfl)
                P.degree_eq.symm P.residualAddChar P.parity P.degree_eq)
  · simpa only [assembly, wildOdd_transportExactOddAssembly_u] using
      C.correction_element
  · simpa only [assembly, wildOdd_transportExactOddAssembly_X] using
      C.correctionCoordinate
  · intro x
    have hbase : P.data.baseAddChar.character = psiF.character :=
      congrArg LocalAddCharData.character P.data_baseAddChar
    calc
      (wildNormCharacterData F K ht hres pi hpi hgen C.tau).character
          (positiveUnitOfLattice F C.linearizationDepth_pos x) =
        C.tau.1 (positiveUnitOfLattice F C.linearizationDepth_pos x) :=
          congrArg (fun q : ContinuousQuasiChar F =>
            q (positiveUnitOfLattice F C.linearizationDepth_pos x))
              (wildNormCharacterData_character F K ht hres pi hpi hgen C.tau)
      _ = P.data.baseAddChar.character (C.assembly.A * (x : F)) :=
        C.tauLinearization x
      _ = psiF.character (C.assembly.A * (x : F)) :=
        congrArg (fun q : ContinuousAddChar F => q (C.assembly.A * (x : F)))
          hbase
      _ = psiF.character (assembly.A * (x : F)) := by
        rw [wildOdd_transportExactOddAssembly_A]
end
end LanglandsFirstMainLemma
