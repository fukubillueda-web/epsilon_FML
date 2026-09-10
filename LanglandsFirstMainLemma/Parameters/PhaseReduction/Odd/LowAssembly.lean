import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.AssemblyInputs
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.ResidualRowCore
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ResidualTransport

/-!
# Low-table-backed odd-prime assembly

This module contains the exact low-table-backed odd-prime assembly up
to, but not including, the named residual-row API.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Low-table-backed exact odd assembly -/

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

/-- An explicitly destructured witness for the low table's existential
upstairs quotient class.  The field representative is carried as data; no
choice operation is hidden in the phase constructor. -/
structure LowOddUpstairsWitness where
  source_table : table = table
  representative : lattice K 0
  representative_eq : (representative : K) =
    lowUpstairsCandidate F K epsilon1 P
  represents : latticeQuotientMk K (by omega) representative =
    stationaryCoefficientClass K chiK psiK
      (lowNormPolynomialPrecision F K ht hres pi hpi hgen
        (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
      (lowGammaK F K delta epsilon1) hgammaK

/-- The Prop-valued table proves that an explicit upstairs witness may be
supplied, but this theorem deliberately does not select one. -/
theorem lowOddUpstairsWitness_nonempty :
    Nonempty (LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) := by
  obtain ⟨hcand, hc⟩ := table.upstairs_class
  exact ⟨
    { source_table := rfl
      representative := ⟨lowUpstairsCandidate F K epsilon1 P, hcand⟩
      representative_eq := rfl
      represents := hc }⟩

/-- Insert one explicitly supplied upstairs class witness at the source
decomposition and exact low denominator. -/
def lowOddUpstairsPhaseFromWitness
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    LocalLamprechtPhaseData K chiK psiK := by
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon1, hgammaK⟩
  let R : StationaryClassRepresentative K chiK psiK hSource
      (Gamma : Kˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative
      W.representative (by simpa only [hSource, Gamma] using W.represents)
  exact localPhaseOfStationaryClass hSource Gamma R C

/-- Transport the explicitly supplied low-table upstairs phase to the
proof-bearing extension data of the global computational package.  The
quotient representative and low denominator are unchanged. -/
def lowOddUpstairsPhaseForComputationalData
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
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
    (lowOddUpstairsPhaseFromWitness F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W C)

/-- An explicitly destructured affine-class witness for one nonidentity low
twist row.  Its literal affine value is retained as provenance. -/
structure LowOddTwistWitness
    (j : OddNormIndex F K) where
  source_table : table = table
  representative : lattice F 0
  representative_eq :
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    let omegaF : F :=
      ((primeTeichmuller F (Module.finrank F K) hchar
        (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)
    (representative : F) = omegaF * (P.alpha : F) +
      (lowEpsilon F K epsilon1 : F) * (P.beta : F)
  represents : latticeQuotientMk F (by omega) representative =
    stationaryCoefficientClass F
      (lowNonzeroTwistDatum F K ht hres pi hpi hgen
        (data.twistData 1) hminimal hLow
          (j : ZMod (Module.finrank F K)) j.property)
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
        delta hdelta


/-- Every table row can be destructured into an explicit affine witness;
the result remains pointwise `Nonempty`, so no family of representatives is
chosen behind the caller's back. -/
theorem lowOddTwistWitness_nonempty (j : OddNormIndex F K) :
    Nonempty (LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j) := by
  obtain ⟨haff, hc⟩ := table.nonzero_twist_class
    (j : ZMod (Module.finrank F K)) j.property
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
  let omegaF : F :=
    ((primeTeichmuller F (Module.finrank F K) hchar
      (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)
  exact ⟨
    { source_table := rfl
      representative :=
        ⟨omegaF * (P.alpha : F) +
          (lowEpsilon F K epsilon1 : F) * (P.beta : F), haff⟩
      representative_eq := rfl
      represents := by simpa only [hchar, omegaF] using hc }⟩

/-- Insert one explicit affine low-table witness and transport only its
proof-bearing twist datum to the computational datum. -/
def lowOddTwistPhaseForComputationalData
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))) data.baseAddChar := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  have hdata : twist = data.twistData mu := by
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
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F twist data.baseAddChar := ⟨delta, hdelta⟩
  let R : StationaryClassRepresentative F twist data.baseAddChar hCrit
      (Gamma : Fˣ) Gamma.property :=
    { representative := W.representative
      represents := by simpa only [twist, hCrit, Gamma] using W.represents }
  let sourcePhase := localPhaseOfStationaryClass hCrit Gamma R C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- The exact low coefficient `A=alpha/delta` from the simultaneous pair. -/
noncomputable def lowOddExactCoefficient : F :=
  (((P.alpha / delta : Fˣ) : F))

/-- The exact norm `n=N(epsilon1*beta1/alpha1)` displayed in the low table. -/
noncomputable def lowOddNormalizedNorm : F :=
  (lowEpsilon F K epsilon1 : F) * (P.beta : F) / (P.alpha : F)

/-- The literal unit carried by the explicitly supplied low upstairs
quotient-class representative. -/
noncomputable def lowOddUpstairsRepresentativeUnit
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) : Kˣ := by
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon1, hgammaK⟩
  let R : StationaryClassRepresentative K chiK psiK hSource
      (Gamma : Kˣ) Gamma.property :=
    { representative := W.representative
      represents := by simpa only [hSource, Gamma] using W.represents }
  exact R.unit

/-- The literal unit carried by one explicitly supplied nonidentity low
twist quotient-class representative. -/
noncomputable def lowOddTwistRepresentativeUnit
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j) : Fˣ := by
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  let hCrit := lowCriticalConductorDecomposition (t := t) hT
  let Gamma : AdmissibleGamma F twist data.baseAddChar := ⟨delta, hdelta⟩
  let R : StationaryClassRepresentative F twist data.baseAddChar hCrit
      (Gamma : Fˣ) Gamma.property :=
    { representative := W.representative
      represents := by simpa only [twist, hCrit, Gamma] using W.represents }
  exact R.unit

/-- The literal low norm-row unit `[j]·alpha`. -/
noncomputable def lowOddNormRepresentativeUnit
    (j : OddNormIndex F K) : Fˣ :=
  oddNormIndexUnit F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) j * P.alpha

/-- The supplied low upstairs representative is exactly the normalized
manuscript row, including its essential `epsilon1` denominator. -/
theorem lowOddUpstairsRepresentative_eq_normalized
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :
    ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table W : Kˣ) : K) =
      (algebraMap F K (P.alpha : F) / (epsilon1 : K)) *
        (algebraMap F K
          (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)) -
          lowNormalizedRatio F K epsilon1 P) := by
  unfold lowOddUpstairsRepresentativeUnit
  rw [StationaryClassRepresentative.coe_unit]
  change (W.representative : K) = _
  rw [W.representative_eq, lowUpstairsCandidate_eq_normalized,
    lowNormalizedUpstairsCandidate, lowNormalizedRatio_norm]
  rfl

/-- Low-table specialization of the exact complete-function transport at
the raw field-character level.  The actual supplied Low representatives
give the three literal ratios `A`, `A*n`, and `A*(n-u)`; in particular the
essential `epsilon1` correction remains present in the upstairs row. -/
theorem lowOdd_actualStationaryRatios_exactCriticalTransport
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (x : K) (upperUnit upperUxUnit : Kˣ)
    (hUpperUnit : (upperUnit : K) = 1 + x)
    (hUpperUxUnit : (upperUxUnit : K) =
      1 + lowNormalizedRatio F K epsilon1 P * x) :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    let A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
    let u := lowNormalizedRatio F K epsilon1 P
    let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
    let tauRatio : F := (P.alpha : F) / (delta : F)
    let baseRatio : F := (P.beta : F) /
      (lowGammaF F K delta epsilon1 : F)
    let upperRatio : K :=
      ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table W : Kˣ) : K) /
        (lowGammaK F K delta epsilon1 : K)
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
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
  let u := lowNormalizedRatio F K epsilon1 P
  let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let tauRatio : F := (P.alpha : F) / (delta : F)
  let baseRatio : F := (P.beta : F) /
    (lowGammaF F K delta epsilon1 : F)
  let upperRatio : K :=
    ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table W : Kˣ) : K) /
      (lowGammaK F K delta epsilon1 : K)
  have hn : norm F K u = n := by
    exact lowNormalizedRatio_norm F K epsilon1 P
  have hTauRatio : tauRatio = A := by
    simp only [tauRatio, A, lowOddExactCoefficient,
      Units.val_div_eq_div_val]
  have hBaseRatio : baseRatio = A * n := by
    dsimp only [baseRatio, A, n, lowOddExactCoefficient,
      lowOddNormalizedNorm, lowGammaF]
    simp only [Units.val_div_eq_div_val]
    field_simp [Units.ne_zero delta, Units.ne_zero P.alpha,
      Units.ne_zero (lowEpsilon F K epsilon1)]
  have hUpperRatio : upperRatio =
      algebraMap F K A * (algebraMap F K n - u) := by
    dsimp only [upperRatio, A, n, u, lowOddExactCoefficient,
      lowOddNormalizedNorm, lowGammaK]
    rw [lowOddUpstairsRepresentative_eq_normalized]
    simp only [Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
      map_div₀]
    unfold lowOddNormalizedNorm
    simp only [map_div₀, map_mul]
    field_simp [Units.ne_zero delta, Units.ne_zero epsilon1,
      Units.ne_zero P.alpha]
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

/-- Every supplied nonidentity low twist representative is the literal
linear row `alpha * (n + [j])`. -/
theorem lowOddTwistRepresentative_eq_normalized
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j) :
    ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j W : Fˣ) : F) =
      (P.alpha : F) *
        (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) +
          oddNormIndexScalar F K ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) j) := by
  unfold lowOddTwistRepresentativeUnit
  rw [StationaryClassRepresentative.coe_unit]
  change (W.representative : F) = _
  rw [W.representative_eq]
  have hteich :
      (((primeTeichmuller F (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
          (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
            (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)) =
      oddNormIndexScalar F K ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) j := by
    simp [oddNormIndexScalar, highIntermediateTeichmullerScalar,
      primeTeichmuller]
    rfl
  rw [hteich]
  simp only [lowOddNormalizedNorm]
  field_simp [Units.ne_zero P.alpha]
  ring

/-- The actual low twist representative is the literal sum of the actual
indexed norm representative and the base representative transported to the
common conductor-`t+1` denominator. -/
theorem lowOddTwistRepresentative_eq_norm_add_base
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j) :
    ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j W : Fˣ) : F) =
      ((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P j : Fˣ) : F) +
        (lowEpsilon F K epsilon1 : F) * (P.beta : F) := by
  rw [lowOddTwistRepresentative_eq_normalized]
  unfold lowOddNormRepresentativeUnit lowOddNormalizedNorm
  simp only [Units.val_mul]
  rw [show ((oddNormIndexUnit F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) j : Fˣ) : F) =
      oddNormIndexScalar F K ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) j by
    rfl]
  field_simp [Units.ne_zero P.alpha]
  ring

/-- The computational low twist character is the actual indexed norm-row
character times the base character. -/
theorem lowOddTwistCharacter_eq_norm_mul_base
    (j : OddNormIndex F K) :
    (data.twistData
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd
          (j : ZMod (Module.finrank F K))))).character =
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character *
        (data.twistData 1).character := by
  rw [data.twistData_character, data.normCharacterData_character,
    data.twistData_character]
  ext z
  simp

/-- The actual indexed low norm representative is its literal
Teichmüller index times the fixed generator representative. -/
theorem lowOddNormRepresentative_eq_teichmuller_mul
    (j : OddNormIndex F K) :
    ((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j : Fˣ) : F) =
      (((primeTeichmuller F (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht
          (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
            (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F) *
        (P.alpha : F)) := by
  unfold lowOddNormRepresentativeUnit oddNormIndexUnit
  simp [oddNormIndexScalar, highIntermediateTeichmullerScalar,
    primeTeichmuller]
  rfl

/-- Keeping that actual Teichmüller representative, its quotient class at
the genuine post-drop depth is the indexed power of the generator class. -/
theorem lowOddNormRepresentative_class_eq_power
    (j : OddNormIndex F K) :
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (⟨((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data hF
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
            simpa [LowStationaryNormRepresentativePair.alpha,
              coe_normUnits] using P.alphaRepresentative.norm_order) |>.1⟩ :
            lattice F 0) =
      (j : ZMod (Module.finrank F K)).val •
        stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F
            (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
            (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
              (lowNormCharacterGenerator F K ht hres pi hpi hgen)
              (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
          data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
            delta hdelta := by
  let hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
  let rep : lattice F 0 :=
    ⟨(((primeTeichmuller F (Module.finrank F K) hchar
      (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F) *
        (P.alpha : F)),
      mul_mem_lattice F
        ((mem_lattice_zero_iff F).2
          (primeTeichmuller F (Module.finrank F K) hchar
            (j : ZMod (Module.finrank F K))).property)
        P.alphaRepresentative.norm_exactDepth.1⟩
  have hteich := lowTeichmuller_nsmul_class F K (Module.finrank F K)
    ht hres pi hpi hgen rfl hchar (j : ZMod (Module.finrank F K)) P.alpha
      (by
        simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits]
          using P.alphaRepresentative.norm_order)
  apply Eq.trans (b := latticeQuotientMk F
    (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) rep)
  · apply congrArg
    apply Subtype.ext
    exact lowOddNormRepresentative_eq_teichmuller_mul F K ht hres pi
      hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j
  · calc
    _ = (j : ZMod (Module.finrank F K)).val •
        latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
          (⟨(P.alpha : F),
            P.alphaRepresentative.norm_exactDepth.1⟩ : lattice F 0) := by
      simpa only [rep] using hteich
    _ = _ := congrArg
      (fun z => (j : ZMod (Module.finrank F K)).val • z)
      P.alpha_norm_class

/-- The actual Teichmüller representative represents the stationary
coefficient class of the actual powered norm character, at conductor `t+1`
and its newly constructed critical depth. -/
theorem lowOddNormRepresentative_class_eq_powerCharacter
    (j : OddNormIndex F K) :
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    let hpow := lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
    let powerData := quasiCharDataOfIsConductor F
      (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (⟨((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data hF
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
            simpa [LowStationaryNormRepresentativePair.alpha,
              coe_normUnits] using P.alphaRepresentative.norm_order) |>.1⟩ :
            lattice F 0) =
      stationaryCoefficientClass F powerData data.baseAddChar
        (lowCriticalConductorDecomposition (t := t) hT) delta hdelta := by
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
  rw [lowOddNormRepresentative_class_eq_power F K ht hres pi hpi hgen data
    hF delta epsilon1 hdelta hT hgammaF P j]
  apply (stationaryCoefficientLamprechtEquivAtConductor F hCrit).injective
  rw [map_nsmul]
  calc
    _ = (j : ZMod (Module.finrank F K)).val •
        stationaryNumeratorClass F tauData data.baseAddChar
          ((t + 1 : ℕ) : ℤ)
          (stationaryDepthOfConductorDecomposition F tauData hCrit)
          delta hdelta := congrArg _
            (stationaryCoefficientClass_toLamprecht F tauData
              data.baseAddChar hCrit delta hdelta)
    _ = stationaryNumeratorClass F powerData data.baseAddChar
        ((t + 1 : ℕ) : ℤ)
        (stationaryDepthOfConductorDecomposition F powerData hCrit)
        delta hdelta := by
      simpa [tauData, powerData, hCrit] using
        (normCharacterPower_stationaryClass_eq_nsmul F K ht hres pi hpi
          hgen tau htau (j : ZMod (Module.finrank F K)).val hpow
          data.baseAddChar ((t + 1 : ℕ) : ℤ)
          (stationaryDepthOfConductorDecomposition F tauData hCrit)
          delta hdelta).symm
    _ = _ := (stationaryCoefficientClass_toLamprecht F powerData
      data.baseAddChar hCrit delta hdelta).symm

/-- The fixed low norm-character generator in the common lower source
coordinate, in the odd critical-conductor branch. -/
noncomputable def lowNormalizedNormGeneratorPhase
    (hparity : lowCriticalParity t = 1) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar := by
  let tauData := quasiCharDataOfIsConductor F
    (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (lowNormCharacterGenerator F K ht hres pi hpi hgen)
      (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))
  have hCrit := lowCriticalConductorDecomposition (t := t) hT
  rw [hparity] at hCrit
  let hTau : IsStationaryConductorDecomposition tauData.conductor
      (lowCriticalFloorDepth t) 1 := by
    simpa only [tauData, quasiCharDataOfIsConductor_conductor] using hCrit
  let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨delta, by simpa only [tauData, quasiCharDataOfIsConductor_conductor]
      using hdelta⟩
  let rep : lattice F 0 :=
    ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F tauData data.baseAddChar hTau delta
        Gamma.property := by
    convert P.alpha_norm_class using 1 <;>
      simp only [rep, tauData, hTau, Gamma,
        quasiCharDataOfIsConductor_conductor, hparity]
  let R : StationaryClassRepresentative F tauData data.baseAddChar hTau
      delta Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let source := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hsource : ord F (source : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  exact LocalLamprechtPhaseData.oddOfStationaryClass
    (lowCriticalFloorDepth t) hTau Gamma source hsource R

/-- The actual powered norm character in the common lower source coordinate,
using the normalized literal representative `j.val • alpha`. -/
noncomputable def lowNormalizedLiteralPowerPhase
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen) ^
          (j : ZMod (Module.finrank F K)).val).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          ((lowNormCharacterGenerator F K ht hres pi hpi hgen) ^
            (j : ZMod (Module.finrank F K)).val)
          (lowGeneratorPower_ne_one F K ht hres pi hpi hgen
            (j : ZMod (Module.finrank F K)) j.property)))
      data.baseAddChar := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  have hCrit := lowCriticalConductorDecomposition (t := t) hT
  rw [hparity] at hCrit
  let hPower : IsStationaryConductorDecomposition powerData.conductor
      (lowCriticalFloorDepth t) 1 := by
    simpa only [powerData, quasiCharDataOfIsConductor_conductor] using hCrit
  let Gamma : AdmissibleGamma F powerData data.baseAddChar :=
    ⟨delta, by simpa only [powerData, quasiCharDataOfIsConductor_conductor]
      using hdelta⟩
  let alphaRep : lattice F 0 :=
    ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
  let rep : lattice F 0 :=
    (j : ZMod (Module.finrank F K)).val • alphaRep
  let hdepth : (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) := by omega
  have hclass : latticeQuotientMk F hdepth rep =
      stationaryCoefficientClass F powerData data.baseAddChar hPower delta
        Gamma.property := by
    calc
      _ = (j : ZMod (Module.finrank F K)).val •
          latticeQuotientMk F hdepth alphaRep := by
        change latticeQuotientMk F hdepth
          ((j : ZMod (Module.finrank F K)).val • alphaRep) = _
        rw [map_nsmul]
      _ = (j : ZMod (Module.finrank F K)).val •
          stationaryCoefficientClass F
            (quasiCharDataOfIsConductor F
              (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
              (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
                (lowNormCharacterGenerator F K ht hres pi hpi hgen)
                (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
            data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
              delta hdelta := congrArg _ P.alpha_norm_class
      _ = _ := by
        calc
          _ = latticeQuotientMk F
              hdepth
              (⟨((lowOddNormRepresentativeUnit F K ht hres pi hpi hgen data
                hF delta epsilon1 hdelta hT hgammaF P j : Fˣ) : F),
                (mem_lattice_and_not_mem_succ_iff F).2 (by
                  unfold lowOddNormRepresentativeUnit oddNormIndexUnit
                    oddNormIndexScalar
                  simp only [Units.val_mul, Units.val_mk0]
                  rw [ord_mul,
                    highParameter_intermediate_teichmuller_ord_eq_zero F
                      (Module.finrank F K)
                      (residueCharacteristic_eq_degree_of_positive_break F K
                        ht (by have hm := hF.conductor_gt_one; omega) pi hpi
                          hgen)
                      (j : ZMod (Module.finrank F K)) j.property]
                  simpa [LowStationaryNormRepresentativePair.alpha,
                    coe_normUnits] using
                      P.alphaRepresentative.norm_order) |>.1⟩ : lattice F 0) :=
            (lowOddNormRepresentative_class_eq_power F K ht hres pi hpi hgen
              data hF delta epsilon1 hdelta hT hgammaF P j).symm
          _ = _ := by
            simpa only [powerData, hPower, Gamma, hparity] using
              (lowOddNormRepresentative_class_eq_powerCharacter F K ht hres
                pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j)
  let R : StationaryClassRepresentative F powerData data.baseAddChar hPower
      delta Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let source := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hsource : ord F (source : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  exact LocalLamprechtPhaseData.oddOfStationaryClass
    (lowCriticalFloorDepth t) hPower Gamma source hsource R

/-- The same actual powered norm character and source coordinate, retaining
the parameter table's Teichmüller representative. -/
noncomputable def lowActualTeichmullerPowerPhase
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    LocalLamprechtPhaseData F
      (quasiCharDataOfIsConductor F
        ((lowNormCharacterGenerator F K ht hres pi hpi hgen) ^
          (j : ZMod (Module.finrank F K)).val).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          ((lowNormCharacterGenerator F K ht hres pi hpi hgen) ^
            (j : ZMod (Module.finrank F K)).val)
          (lowGeneratorPower_ne_one F K ht hres pi hpi hgen
            (j : ZMod (Module.finrank F K)) j.property)))
      data.baseAddChar := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K)) j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      (tau ^ (j : ZMod (Module.finrank F K)).val) hpow)
  have hCrit := lowCriticalConductorDecomposition (t := t) hT
  rw [hparity] at hCrit
  let hPower : IsStationaryConductorDecomposition powerData.conductor
      (lowCriticalFloorDepth t) 1 := by
    simpa only [powerData, quasiCharDataOfIsConductor_conductor] using hCrit
  let Gamma : AdmissibleGamma F powerData data.baseAddChar :=
    ⟨delta, by simpa only [powerData, quasiCharDataOfIsConductor_conductor]
      using hdelta⟩
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
        simpa [LowStationaryNormRepresentativePair.alpha,
          coe_normUnits] using P.alphaRepresentative.norm_order) |>.1⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F powerData data.baseAddChar hPower delta
        Gamma.property := by
    simpa only [rep, powerData, hPower, Gamma, hparity] using
      (lowOddNormRepresentative_class_eq_powerCharacter F K ht hres pi hpi
        hgen data hF delta epsilon1 hdelta hT hgammaF P j)
  let R : StationaryClassRepresentative F powerData data.baseAddChar hPower
      delta Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let source := phaseReductionSourceCoordinate F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (lowCriticalFloorDepth t)
  have hsource : ord F (source : F) =
      ((lowCriticalFloorDepth t : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      (lowCriticalFloorDepth t)
  exact LocalLamprechtPhaseData.oddOfStationaryClass
    (lowCriticalFloorDepth t) hPower Gamma source hsource R


/-- The literal natural-multiple representative is the source and the actual
Teichmüller representative is the selected row in this exact change datum. -/
noncomputable def lowTeichmullerLiteralRepresentativeChange
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1) :
    OddRepresentativeChangeData
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P j hparity)
      (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P j hparity) := by
  unfold lowNormalizedLiteralPowerPhase lowActualTeichmullerPowerPhase
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

/-- Exact Teichmüller-to-literal representative transport with the literal
row as source.  Its exposed coefficient is definitionally
`criticalAffineTranslationCoefficient` applied to the exact
`criticalStationaryRepresentativeDifference`. -/
theorem lowActualTeichmullerPower_criticalFunction_eq_exact_translation
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (x : ResidueField F) :
    (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j hparity).criticalFunction x =
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P j hparity).criticalFunction x *
        psi0
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
              psi0 hpsi0 * x) :=
  OddRepresentativeChangeData.criticalFunction_eq_mul_translation
    (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen data
      hF delta epsilon1 hdelta hT hgammaF P j hparity) psi0 hpsi0 x

/-- Representative change preserves the polar coefficient: the literal and
actual Teichmüller rows differ only in the affine coordinate. -/
theorem lowActualTeichmullerPower_polarCoefficient_eq_literal
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient psi0 hpsi0 =
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient
          psi0 hpsi0 := by
  unfold lowActualTeichmullerPowerPhase lowNormalizedLiteralPowerPhase
  dsimp only
  rfl

/-- Exact complete-function transport from the literal natural-multiple
representative to the actual Teichmüller representative.  The complete
Lamprecht function is transported with its affine factor; no finite-field
cancellation is performed here. -/
theorem lowActualTeichmullerPower_criticalFunction_eq_literal_mul_translation
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) (x : ResidueField F) :
    (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j hparity).criticalFunction x =
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P j hparity).criticalFunction x *
        psi0
          ((LocalLamprechtPhaseData.affineCoefficient
              (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data
                hF delta epsilon1 hdelta hT hgammaF P j hparity)
                psi0 hpsi0 hchar -
            LocalLamprechtPhaseData.affineCoefficient
              (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data
                hF delta epsilon1 hdelta hT hgammaF P j hparity)
                psi0 hpsi0 hchar) * x) := by
  rw [(lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j hparity).criticalFunction_eq_quadratic
        psi0 hpsi0 hchar,
    (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j hparity).criticalFunction_eq_quadratic
        psi0 hpsi0 hchar]
  rw [lowActualTeichmullerPower_polarCoefficient_eq_literal F K ht hres pi
    hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity psi0
      hpsi0]
  have harg :
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
          epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient psi0
            hpsi0 / 2 * x ^ 2 +
          (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF
            delta epsilon1 hdelta hT hgammaF P j hparity).affineCoefficient
              psi0 hpsi0 hchar * x =
        ((lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
            delta epsilon1 hdelta hT hgammaF P j hparity).polarCoefficient
              psi0 hpsi0 / 2 * x ^ 2 +
          (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
            delta epsilon1 hdelta hT hgammaF P j hparity).affineCoefficient
              psi0 hpsi0 hchar * x) +
          ((lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF
              delta epsilon1 hdelta hT hgammaF P j hparity).affineCoefficient
                psi0 hpsi0 hchar -
            (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
              delta epsilon1 hdelta hT hgammaF P j hparity).affineCoefficient
                psi0 hpsi0 hchar) * x := by
    ring
  rw [harg, psi0.map_add_eq_mul]

/-- The normalized literal powered row is pointwise the corresponding
natural power of the fixed generator's complete critical function. -/
theorem lowNormalizedLiteralPower_criticalFunction_eq_pow
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (x : ResidueField F) :
    (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF delta
      epsilon1 hdelta hT hgammaF P j hparity).criticalFunction x =
      ((lowNormalizedNormGeneratorPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P hparity).criticalFunction x) ^
        (j : ZMod (Module.finrank F K)).val := by
  unfold lowNormalizedLiteralPowerPhase lowNormalizedNormGeneratorPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  rw [LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction,
    LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction]
  apply criticalPolarFunction_pow_of_literal_nsmul
  · rfl
  · simp only [StationaryClassRepresentative.toLamprecht,
      StationaryClassRepresentative.ofCoefficientRepresentative]
    simp [nsmul_eq_mul]

/-- The actual low upstairs row exposes the positive additive value of its
explicitly supplied quotient-class representative at `lowGammaK`. -/
theorem lowOddUpstairsPhase_elementaryAdditiveFactor
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table W C).elementaryAdditiveFactor =
      (globalPsi (trace F K
        (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table W : Kˣ) : K) /
              (lowGammaK F K delta epsilon1 : K))) : ℂ) := by
  unfold lowOddUpstairsPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  unfold lowOddUpstairsPhaseFromWitness
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [hpsi, ContinuousAddChar.compTrace_apply,
    data.baseAddChar_character]
  unfold lowOddUpstairsRepresentativeUnit
  simp only [StationaryClassRepresentative.coe_unit]
  rfl

/-- The actual low upstairs row exposes the inverse base-character value at
the norm of its supplied numerator unit. -/
theorem lowOddUpstairsPhase_elementaryMultiplicativeFactor
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table W C).elementaryMultiplicativeFactor =
      (globalChi (normUnits F K
        (lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table W)) : ℂ)⁻¹ := by
  unfold lowOddUpstairsPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  unfold lowOddUpstairsPhaseFromWitness
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [hchi, ContinuousQuasiChar.compNorm_apply,
    data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  unfold lowOddUpstairsRepresentativeUnit
  rfl

/-- The identity low twist uses the literal base numerator `beta` and the
longer denominator `lowGammaF`. -/
theorem lowBasePhase_elementaryAdditiveFactor
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table C).elementaryAdditiveFactor =
      (globalPsi ((P.beta : F) /
        (lowGammaF F K delta epsilon1 : F)) : ℂ) := by
  unfold lowBasePhase
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [data.baseAddChar_character]

/-- The identity low twist's multiplicative elementary value is the inverse
base character at the literal numerator `beta`. -/
theorem lowBasePhase_elementaryMultiplicativeFactor
    (C : LamprechtCriticalCoordinate F d epsilon) :
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table C).elementaryMultiplicativeFactor =
      (globalChi P.beta : ℂ)⁻¹ := by
  unfold lowBasePhase
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  apply congrArg (fun z : ℂ ↦ z⁻¹)
  apply congrArg (fun z : ℂˣ ↦ (z : ℂ))
  apply congrArg (fun z : Fˣ ↦ globalChi z)
  apply Units.ext
  simp only [StationaryClassRepresentative.coe_unit]

/-- One actual post-drop norm row exposes `[j]·alpha` over the actual
denominator `delta`. -/
theorem lowOddNormPhase_elementaryAdditiveFactor
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j C).elementaryAdditiveFactor =
      (globalPsi
        (((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
          (hT := hT) (j := j) : Fˣ) : F) / (delta : F)) : ℂ) := by
  unfold lowOddNormPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  unfold lowNormCharacterPowerPhase
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [data.baseAddChar_character]
  unfold lowOddNormRepresentativeUnit oddNormIndexUnit
  rfl

/-- One actual post-drop norm row exposes the inverse norm-character value
at its literal `[j]·alpha` unit. -/
theorem lowOddNormPhase_elementaryMultiplicativeFactor
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j C).elementaryMultiplicativeFactor =
      ((data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character
          (lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
            (hT := hT) (j := j)) : ℂ)⁻¹ := by
  unfold lowOddNormPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  unfold lowNormCharacterPowerPhase
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [quasiCharDataOfIsConductor_character,
    data.normCharacterData_character]
  rw [lowNormCharacterGenerator_pow F K ht hres pi hpi hgen
    (j : ZMod (Module.finrank F K))]
  unfold lowOddNormRepresentativeUnit oddNormIndexUnit
  apply congrArg (fun z : ℂ ↦ z⁻¹)
  apply congrArg (fun z : ℂˣ ↦ (z : ℂ))
  apply congrArg (fun z : Fˣ ↦
    (lowNormCharacterGenerator F K ht hres pi hpi hgen ^
      (j : ZMod (Module.finrank F K)).val).1 z)
  apply Units.ext
  simp only [StationaryClassRepresentative.coe_unit, Units.val_mul,
    Units.val_mk0]
  simp [oddNormIndexScalar, highIntermediateTeichmullerScalar,
    primeTeichmuller]
  rfl

/-- One supplied nonidentity low twist row exposes its positive additive
value over the actual post-drop denominator `delta`. -/
theorem lowOddTwistPhase_elementaryAdditiveFactor
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j W C).elementaryAdditiveFactor =
      (globalPsi
        (((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j W : Fˣ) : F) / (delta : F)) : ℂ) := by
  unfold lowOddTwistPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryAdditiveFactor]
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
  rw [data.baseAddChar_character]
  unfold lowOddTwistRepresentativeUnit
  simp only [StationaryClassRepresentative.coe_unit]

/-- One supplied nonidentity low twist row exposes the inverse full twist
character at its literal numerator unit. -/
theorem lowOddTwistPhase_elementaryMultiplicativeFactor
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j W C).elementaryMultiplicativeFactor =
      ((data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character
          (lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
            psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
              hT hgammaF hgammaK P table j W) : ℂ)⁻¹ := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  have hdata : twist = data.twistData mu := by
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
  unfold lowOddTwistPhaseForComputationalData
  rw [LocalLamprechtPhaseData.transportLocalLamprechtPhaseData_elementaryMultiplicativeFactor]
  dsimp only [id]
  rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [show twist.character = (data.twistData mu).character by
    exact congrArg LocalQuasiCharData.character hdata]
  unfold lowOddTwistRepresentativeUnit
  simp only [mu, twist]

/-- The actual low upstairs row evaluates at the exact table denominator
`lowGammaK`. -/
theorem lowOddUpstairsPhase_admissibleFactor
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (C : LamprechtCriticalCoordinate K d epsilon) :
    (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table W C).admissibleFactor =
      (data.extensionQuasiChar.character
        (lowGammaK F K delta epsilon1) : ℂ) := by
  have hchiData : chiK.character = data.extensionQuasiChar.character := by
    rw [data.extensionQuasiChar_character, hchi,
      data.twistData_character]
    exact normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi
  rw [← hchiData]
  unfold lowOddUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  unfold lowOddUpstairsPhaseFromWitness
  apply localPhaseOfStationaryClass_admissibleFactor

/-- Every nonidentity low norm row evaluates at the actual post-drop
denominator `delta`. -/
theorem lowOddNormPhase_admissibleFactor
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P j C).admissibleFactor =
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character delta := by
  unfold lowOddNormPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  rw [data.normCharacterData_character]
  unfold lowNormCharacterPowerPhase
  change (localPhaseOfStationaryClass _ _ _ C).admissibleFactor = _
  rw [localPhaseOfStationaryClass_admissibleFactor,
    quasiCharDataOfIsConductor_character]
  exact congrArg (fun mu : NormCharacter F K ↦ (mu.1 delta : ℂ))
    (lowNormCharacterGenerator_pow F K ht hres pi hpi hgen
      (j : ZMod (Module.finrank F K))).symm

/-- Every nonidentity low twist row evaluates at the actual denominator
`delta`. -/
theorem lowOddTwistPhase_admissibleFactor
    (j : OddNormIndex F K)
    (W : LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table j)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table j W C).admissibleFactor =
      (data.twistData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K))))).character delta := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  have hdata : twist = data.twistData mu := by
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
  unfold lowOddTwistPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_admissibleFactor]
  change (localPhaseOfStationaryClass _ _ _ C).admissibleFactor = _
  rw [localPhaseOfStationaryClass_admissibleFactor]
  exact congrArg
    (fun q : LocalQuasiCharData F ↦ (q.character delta : ℂ)) hdata

/-- Derive the complete low admissible-character shape from the literal
table rows, including the distinct identity-twist denominator. -/
theorem lowOddAdmissibleShapeOfActualRows
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
          hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
              (CTwist j))) :
    LowOddAdmissibleShape data delta epsilon1 D := by
  refine
    { extension_factor := ?_
      identity_norm_factor := ?_
      nonidentity_norm_factor := ?_
      identity_twist_factor := ?_
      nonidentity_twist_factor := ?_ }
  · rw [hExtension, LocalPhaseData.admissibleFactor]
    exact lowOddUpstairsPhase_admissibleFactor F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table WUp CUp
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
        exact lowOddNormPhase_admissibleFactor F K ht hres pi hpi hgen data
          hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)
  · rw [hBase, LocalPhaseData.admissibleFactor]
    exact lowBasePhase_admissibleFactor F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table CBase
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
        rw [hTwist j, LocalPhaseData.admissibleFactor]
        exact lowOddTwistPhase_admissibleFactor F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table j (WTwist j) (CTwist j)

/-- Source-tied raw correction coordinates for the exact low odd-prime
assembly.  Odd degree is an explicit parameter of the type.  The coefficient,
normalized coordinate, norm, and every representative unit are the literal
objects supplied by `P`, `table`, `WUp`, and `WTwist`; no aggregate elementary
product equality is a field. -/
structure LowOddRawCorrectionCoordinates
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j) where
  zZero : Fˣ
  z : OddNormIndex F K → Fˣ
  X : F
  X_eq : X = trace F K (lowNormalizedRatio F K epsilon1 P) +
    lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
      ((zZero : F) - 1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j * ((z j : F) - 1)
  additive_ratio_eq :
    (P.beta : F) / (lowGammaF F K delta epsilon1 : F) +
      ∑ j : OddNormIndex F K,
        ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) / (delta : F) =
    lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
      trace F K (lowNormalizedRatio F K epsilon1 P) +
      trace F K
        (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WUp : Kˣ) : K) /
              (lowGammaK F K delta epsilon1 : K)) +
      ∑ j : OddNormIndex F K,
        ((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
          (hT := hT) (j := j) : Fˣ) : F) /
          (delta : F)
  zZero_eq : zZero =
    normUnits F K
      (lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp) /
      (P.beta * ∏ j : OddNormIndex F K,
        lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j))
  z_eq : ∀ j : OddNormIndex F K, z j =
    lowOddNormRepresentativeUnit (F := F) (K := K) (P := P) (hT := hT)
      (j := j) /
      lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table j (WTwist j)
  chiLinearization : globalChi zZero = globalPsi
    (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
      lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
        ((zZero : F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1 (z j) = globalPsi
      (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
        oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j * ((z j : F) - 1))

/-- Preferred low odd correction input.  Its correction units are the
literal manuscript norm ratios; the selected stationary representatives
remain exactly `WUp` and `WTwist`.  The retained norm factor in `rowRatio_eq`
is removed only by the character bridge below. -/
structure LowOddSourceTiedCorrectionCoordinates
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j) where
  correctionUnits : OddNormCorrectionUnitData F K ht hres pi hpi hgen
    (by have hm := hF.conductor_gt_one; omega)
      (lowNormalizedRatio F K epsilon1 P)
      (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT))
  X : F
  X_eq : X = trace F K (lowNormalizedRatio F K epsilon1 P) +
    lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
      (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) correctionUnits : Fˣ) : F) -
          1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j *
        (((OddNormCorrectionUnitData.z ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) correctionUnits j : Fˣ) :
            F) - 1)
  additive_ratio_eq :
    (P.beta : F) / (lowGammaF F K delta epsilon1 : F) +
      ∑ j : OddNormIndex F K,
        ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) / (delta : F) =
    lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
      trace F K (lowNormalizedRatio F K epsilon1 P) +
    trace F K
      (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp : Kˣ) : K) /
            (lowGammaK F K delta epsilon1 : K)) +
    ∑ j : OddNormIndex F K,
      ((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
        (hT := hT) (j := j) : Fˣ) : F) / (delta : F)
  zZero_selected_eq :
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) correctionUnits =
    normUnits F K
      (lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp) /
      (P.beta * ∏ j : OddNormIndex F K,
        lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j))
  rowRatio_eq : ∀ j : OddNormIndex F K,
    lowOddNormRepresentativeUnit (F := F) (K := K) (P := P) (hT := hT)
        (j := j) /
      lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table j (WTwist j) =
    (normUnits F K
      (OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) correctionUnits j))⁻¹ *
      OddNormCorrectionUnitData.z ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) correctionUnits j
  chiLinearization :
    globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) correctionUnits) =
    globalPsi
      (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
      lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) correctionUnits : Fˣ) :
            F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1
          (OddNormCorrectionUnitData.z ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) correctionUnits j) =
      globalPsi
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
        oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) correctionUnits j : Fˣ) :
              F) - 1))

namespace LowOddSourceTiedCorrectionCoordinates

/-- Applying the actual indexed norm character kills the retained norm of
`(u+[j])/[j]` and only then identifies the low row quotient with manuscript
`z_j`. -/
theorem powerCharacterBridge
    {hodd : Odd (Module.finrank F K)}
    {WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table}
    {WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j}
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist)
    (j : OddNormIndex F K) :
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))).1
        (OddNormCorrectionUnitData.z ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) R.correctionUnits j) =
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))).1
        (lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
            (hT := hT) (j := j) /
          lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
            psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
              hT hgammaF hgammaK P table j (WTwist j)) := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hnorm : mu.1
      (normUnits F K
        (OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) R.correctionUnits j)) =
        1 := NormCharacter.eq_one_on_normRange F K mu _ ⟨_, rfl⟩
  rw [R.rowRatio_eq j, map_mul, map_inv, hnorm, inv_one, one_mul]

end LowOddSourceTiedCorrectionCoordinates

/-- The literal low table row forces the retained normalized row-ratio
identity.  The right-hand norm factor is kept until the indexed norm
character is applied. -/
theorem lowOddSourceTied_rowRatio_eq
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega)
        (lowNormalizedRatio F K epsilon1 P)
        (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)))
    (j : OddNormIndex F K) :
    lowOddNormRepresentativeUnit (F := F) (K := K) (P := P) (hT := hT)
        (j := j) /
      lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table j (WTwist j) =
    (normUnits F K
      (OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) C j))⁻¹ *
      OddNormCorrectionUnitData.z ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) C j := by
  have htwist :
      ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) =
      (P.alpha : F) *
        (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) +
          oddNormIndexScalar F K ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) j) := by
    exact lowOddTwistRepresentative_eq_normalized F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
  have hscaled :
      ((OddNormCorrectionUnitData.scaledNumeratorUnit ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) C j : Kˣ) : K) =
      (lowNormalizedRatio F K epsilon1 P +
          algebraMap F K (oddNormIndexScalar F K ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) j)) /
        algebraMap F K (oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j) := by
    unfold OddNormCorrectionUnitData.scaledNumeratorUnit
    simp only [Units.val_div_eq_div_val, Units.val_mk0, Units.coe_map,
      MonoidHom.coe_coe, oddNormIndexUnit_coe]
  have hscalar_ne :
      oddNormIndexScalar F K ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) j ≠ 0 := by
    rw [← oddNormIndexUnit_coe F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) j]
    exact Units.ne_zero _
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul,
    Units.val_inv_eq_inv_val]
  unfold lowOddNormRepresentativeUnit
  rw [Units.val_mul, oddNormIndexUnit_coe]
  rw [htwist, OddNormCorrectionUnitData.coe_z]
  simp only [coe_normUnits, hscaled]
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [norm_algebraMap]
  unfold oddNormIndexScalar
  rw [highParameter_intermediate_teichmuller_pow F (Module.finrank F K)
    (residueCharacteristic_eq_degree_of_positive_break F K ht
      (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
        (j : ZMod (Module.finrank F K))]
  have hnum : norm F K
      (lowNormalizedRatio F K epsilon1 P + algebraMap F K
        (highIntermediateTeichmullerScalar F (Module.finrank F K)
          (residueCharacteristic_eq_degree_of_positive_break F K ht
            (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
            (j : ZMod (Module.finrank F K)))) ≠ 0 := by
    simpa only [oddNormIndexScalar] using C.numerator_ne_zero j
  have hden :
      highIntermediateTeichmullerScalar F (Module.finrank F K)
          (residueCharacteristic_eq_degree_of_positive_break F K ht
            (by have hm := hF.conductor_gt_one; omega) pi hpi hgen)
            (j : ZMod (Module.finrank F K)) +
        lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) ≠ 0 := by
    simpa only [oddNormIndexScalar, add_comm] using C.denominator_ne_zero j
  field_simp [hnum, hden] <;> ring

/-- The low table's base row and nonidentity linear rows force the signed
additive identity.  No aggregate elementary equality is assumed. -/
theorem lowOddSourceTied_additive_ratio_eq
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j) :
    (P.beta : F) / (lowGammaF F K delta epsilon1 : F) +
      ∑ j : OddNormIndex F K,
        ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) / (delta : F) =
    lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
      trace F K (lowNormalizedRatio F K epsilon1 P) +
    trace F K
      (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp : Kˣ) : K) /
            (lowGammaK F K delta epsilon1 : K)) +
    ∑ j : OddNormIndex F K,
      ((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
        (hT := hT) (j := j) : Fˣ) : F) / (delta : F) := by
  let c : F := (P.alpha : F)
  let eta : F := (lowEpsilon F K epsilon1 : F)
  let A : F := c / (delta : F)
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let lam : ZMod (Module.finrank F K) → F :=
    oddNormAllIndexScalar F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega)
  have hlam0 : lam 0 = 0 := by
    exact (highParameter_intermediate_teichmuller_eq_zero_iff F
      (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen) 0).2 rfl
  have hbase :
      (P.beta : F) / (lowGammaF F K delta epsilon1 : F) =
        A * (n + lam 0) := by
    rw [hlam0]
    simp only [A, n, c, eta, lowOddNormalizedNorm, lowGammaF,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val,
      add_zero, div_eq_mul_inv]
    field_simp [Units.ne_zero delta, Units.ne_zero P.alpha,
      Units.ne_zero (lowEpsilon F K epsilon1)]
  have htwist (j : OddNormIndex F K) :
      ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) / (delta : F) =
        A * (n + lam j) := by
    rw [lowOddTwistRepresentative_eq_normalized]
    simp only [A, n, c, lam, oddNormIndexScalar, oddNormAllIndexScalar,
      div_eq_mul_inv]
    ring
  have hup :
      trace F K
        (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WUp : Kˣ) : K) /
              (lowGammaK F K delta epsilon1 : K)) =
        trace F K (algebraMap F K A * (algebraMap F K n - u)) := by
    apply congrArg (trace F K)
    rw [lowOddUpstairsRepresentative_eq_normalized]
    simp only [A, n, u, c, lowGammaK, Units.val_div_eq_div_val,
      Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val, map_div₀,
      div_eq_mul_inv, map_mul, map_inv₀]
    field_simp [Units.ne_zero delta, Units.ne_zero epsilon1]
    rfl
  have hnorm (j : OddNormIndex F K) :
      ((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
        (hT := hT) (j := j) : Fˣ) : F) / (delta : F) = A * lam j := by
    unfold lowOddNormRepresentativeUnit
    rw [Units.val_mul, oddNormIndexUnit_coe]
    simp only [A, c, lam, oddNormIndexScalar, oddNormAllIndexScalar,
      div_eq_mul_inv]
    ring
  rw [hbase]
  simp_rw [htwist]
  rw [oddNormalizedAdditiveRatioIdentity F K A n u lam hlam0]
  rw [hup]
  simp_rw [hnorm]
  simp only [A, c, n, u, lowOddExactCoefficient,
    Units.val_div_eq_div_val]

/-- The literal low upstairs, base, and nonidentity twist rows force the
exceptional manuscript correction unit, retaining the essential unit
`epsilon1` until its norm is canceled. -/
theorem lowOddSourceTied_zZero_selected_eq
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega)
        (lowNormalizedRatio F K epsilon1 P)
        (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT))) :
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) C =
    normUnits F K
      (lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp) /
      (P.beta * ∏ j : OddNormIndex F K,
        lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j)) := by
  let c : F := (P.alpha : F)
  let eta : F := (lowEpsilon F K epsilon1 : F)
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let lam : ZMod (Module.finrank F K) → F :=
    oddNormAllIndexScalar F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega)
  have hlam0 : lam 0 = 0 := by
    exact (highParameter_intermediate_teichmuller_eq_zero_iff F
      (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen) 0).2 rfl
  have hbase : (P.beta : F) = (c * n) / eta := by
    simp only [c, n, eta, lowOddNormalizedNorm]
    field_simp [Units.ne_zero P.alpha,
      Units.ne_zero (lowEpsilon F K epsilon1)]
  apply Units.ext
  simp only [OddNormCorrectionUnitData.coe_zZero,
    Units.val_div_eq_div_val, coe_normUnits, Units.val_mul, Units.coe_prod]
  rw [lowOddUpstairsRepresentative_eq_normalized, hbase]
  simp_rw [lowOddTwistRepresentative_eq_normalized]
  simpa only [c, eta, u, n, lam, oddNormCorrectionDenominator,
    oddNormIndexScalar, oddNormAllIndexScalar] using
    (oddLowZZeroScalingIdentity F K c eta n (Units.ne_zero P.alpha)
      (Units.ne_zero (lowEpsilon F K epsilon1)) (epsilon1 : K) rfl u lam
        hlam0).symm

/-- Preferred constructor for low correction coordinates.  The exact base,
upstairs, and nonidentity row identities are derived from `P`, `WUp`, and
`WTwist`; callers retain only the later pointwise linearizations. -/
def lowOddSourceTiedCorrectionCoordinatesOfActualRows
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega)
        (lowNormalizedRatio F K epsilon1 P)
        (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)))
    (X : F)
    (hX : X = trace F K (lowNormalizedRatio F K epsilon1 P) +
      lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) C : Fˣ) : F) - 1) +
      ∑ j : OddNormIndex F K,
        oddNormIndexScalar F K ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) C j : Fˣ) : F) - 1))
    (hChi :
      globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) C) =
      globalPsi
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
        lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
          (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) C : Fˣ) : F) - 1)))
    (hPower : ∀ j : OddNormIndex F K,
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd
          (j : ZMod (Module.finrank F K)))).1
            (OddNormCorrectionUnitData.z ht hres pi hpi hgen
              (by have hm := hF.conductor_gt_one; omega) C j) =
        globalPsi
          (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
          oddNormIndexScalar F K ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) j *
            (((OddNormCorrectionUnitData.z ht hres pi hpi hgen
              (by have hm := hF.conductor_gt_one; omega) C j : Fˣ) : F) -
                1))) :
    LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist :=
  { correctionUnits := C
    X := X
    X_eq := hX
    additive_ratio_eq := lowOddSourceTied_additive_ratio_eq F K ht hres pi
      hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist
    zZero_selected_eq := lowOddSourceTied_zZero_selected_eq F K ht hres pi
      hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist C
    rowRatio_eq := lowOddSourceTied_rowRatio_eq F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist C
    chiLinearization := hChi
    powerLinearization := hPower }

/-- The four families of actual low rows prove the oriented additive
elementary product in the odd assembly. -/
theorem lowOddActualRows_additiveDenominator_eq
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
                (CTwist j))) :
    D.elementaryAdditiveDenominator =
      (globalPsi
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
          trace F K (lowNormalizedRatio F K epsilon1 P)) : ℂ) *
        D.elementaryAdditiveNumerator := by
  have hDen : D.elementaryAdditiveDenominator =
      (globalPsi ((P.beta : F) /
        (lowGammaF F K delta epsilon1 : F)) : ℂ) *
      (globalPsi (∑ j : OddNormIndex F K,
        ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) /
              (delta : F)) : ℂ) := by
    rw [D.oddElementaryAdditiveDenominator_reindex ht hres pi hpi hgen,
      hBase]
    simp only [LocalPhaseData.elementaryAdditiveFactor]
    rw [lowBasePhase_elementaryAdditiveFactor F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table CBase]
    congr 1
    calc
      (∏ j : OddNormIndex F K,
        (D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))).elementaryAdditiveFactor) =
          ∏ j : OddNormIndex F K, (globalPsi
            (((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data
              chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                hepsilon1 hT hgammaF hgammaK P table j (WTwist j) : Fˣ) :
                  F) / (delta : F)) : ℂ) := by
            apply Finset.prod_congr rfl
            intro j _
            rw [hTwist j]
            exact lowOddTwistPhase_elementaryAdditiveFactor F K ht hres pi
              hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta
                epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table j
                  (WTwist j) (CTwist j)
      _ = _ := continuousAddChar_prod_apply_eq_apply_sum globalPsi _
  have hNum : D.elementaryAdditiveNumerator =
      (globalPsi (trace F K
        (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table WUp : Kˣ) : K) /
              (lowGammaK F K delta epsilon1 : K))) : ℂ) *
      (globalPsi (∑ j : OddNormIndex F K,
        ((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
          (hT := hT) (j := j) : Fˣ) : F) / (delta : F)) : ℂ) := by
    rw [D.oddElementaryAdditiveNumerator_reindex ht hres pi hpi hgen,
      hExtension]
    simp only [LocalPhaseData.elementaryAdditiveFactor]
    rw [lowOddUpstairsPhase_elementaryAdditiveFactor F K ht hres pi hpi
      hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table WUp CUp]
    congr 1
    calc
      (∏ j : OddNormIndex F K,
        (D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))).elementaryAdditiveFactor) =
          ∏ j : OddNormIndex F K, (globalPsi
            (((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
              (hT := hT) (j := j) : Fˣ) : F) / (delta : F)) : ℂ) := by
            apply Finset.prod_congr rfl
            intro j _
            rw [hNorm j]
            exact lowOddNormPhase_elementaryAdditiveFactor F K ht hres pi
              hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j
                (CNorm j)
      _ = _ := continuousAddChar_prod_apply_eq_apply_sum globalPsi _
  rw [hDen, hNum]
  have hadd (x y : F) :
      (globalPsi (x + y) : ℂ) =
        (globalPsi x : ℂ) * (globalPsi y : ℂ) := by
    exact congrArg Units.val (ContinuousAddChar.map_add_eq_mul globalPsi x y)
  calc
    (globalPsi ((P.beta : F) /
        (lowGammaF F K delta epsilon1 : F)) : ℂ) *
      (globalPsi (∑ j : OddNormIndex F K,
        ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table j (WTwist j) : Fˣ) : F) /
              (delta : F)) : ℂ) =
        (globalPsi
          ((P.beta : F) / (lowGammaF F K delta epsilon1 : F) +
            ∑ j : OddNormIndex F K,
              ((lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data
                chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                  hepsilon1 hT hgammaF hgammaK P table j (WTwist j) : Fˣ) :
                    F) / (delta : F)) : ℂ) := (hadd _ _).symm
    _ = (globalPsi
          (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
              trace F K (lowNormalizedRatio F K epsilon1 P) +
            (trace F K
              (((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen
                data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
                  hdelta hepsilon1 hT hgammaF hgammaK P table WUp : Kˣ) :
                    K) / (lowGammaK F K delta epsilon1 : K)) +
              ∑ j : OddNormIndex F K,
                ((lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
                  (hT := hT) (j := j) : Fˣ) : F) / (delta : F))) : ℂ) := by
          apply congrArg (fun x : F ↦ (globalPsi x : ℂ))
          rw [R.additive_ratio_eq]
          ring
    _ = _ := by rw [hadd, hadd]

/-- The actual low rows prove the inverse-character elementary product in
the exact denominator orientation. -/
theorem lowOddActualRows_multiplicativeDenominator_eq
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
                (CTwist j))) :
    D.elementaryMultiplicativeDenominator =
      ((globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) R.correctionUnits) : ℂ) *
        ∏ j : OddNormIndex F K,
          ((ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))).1
                (OddNormCorrectionUnitData.z ht hres pi hpi hgen
                  (by have hm := hF.conductor_gt_one; omega)
                    R.correctionUnits j) : ℂ)) *
        D.elementaryMultiplicativeNumerator := by
  let mu : OddNormIndex F K → NormCharacter F K := fun j ↦
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hDen : D.elementaryMultiplicativeDenominator =
      (globalChi P.beta : ℂ)⁻¹ *
        ∏ j : OddNormIndex F K,
          (((globalChi
              (lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data
                chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                  hepsilon1 hT hgammaF hgammaK P table j (WTwist j)) : ℂ) *
            (mu j).1
              (lowOddTwistRepresentativeUnit F K ht hres pi hpi hgen data
                chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
                  hepsilon1 hT hgammaF hgammaK P table j (WTwist j)) : ℂ))⁻¹ := by
    rw [D.oddElementaryMultiplicativeDenominator_reindex ht hres pi hpi hgen,
      hBase]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [lowBasePhase_elementaryMultiplicativeFactor F K ht hres pi hpi hgen
      data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table CBase]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hTwist j]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [lowOddTwistPhase_elementaryMultiplicativeFactor F K ht hres pi hpi
      hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table j (WTwist j) (CTwist j)]
    rw [data.twistData_character]
    simp only [mu, ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
      ContinuousQuasiChar.one_apply, one_mul, Units.val_mul, mul_inv_rev]
    ring
  have hNum : D.elementaryMultiplicativeNumerator =
      (globalChi (normUnits F K
        (lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table WUp)) : ℂ)⁻¹ *
        ∏ j : OddNormIndex F K,
          ((mu j).1
            (lowOddNormRepresentativeUnit (F := F) (K := K) (P := P)
              (hT := hT) (j := j)) : ℂ)⁻¹ := by
    rw [D.oddElementaryMultiplicativeNumerator_reindex ht hres pi hpi hgen,
      hExtension]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [lowOddUpstairsPhase_elementaryMultiplicativeFactor F K ht hres pi
      hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table WUp CUp]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hNorm j]
    simp only [LocalPhaseData.elementaryMultiplicativeFactor]
    rw [lowOddNormPhase_elementaryMultiplicativeFactor F K ht hres pi hpi
      hgen data hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)]
    rw [data.normCharacterData_character]
  rw [hDen, hNum, R.zZero_selected_eq]
  simp_rw [LowOddSourceTiedCorrectionCoordinates.powerCharacterBridge
    (F := F) (K := K) (R := R)]
  simp only [mu, map_div, map_mul, map_prod, Units.val_div_eq_div_val,
    Units.val_mul]
  simp_rw [mul_inv_rev]
  rw [Finset.prod_mul_distrib]
  simp_rw [Finset.prod_inv_distrib, Finset.prod_div_distrib,
    Units.coe_prod]
  field_simp [ContinuousQuasiChar.apply_ne_zero, Finset.prod_ne_zero_iff]

/-- A low odd assembly tied to `P`, the table, and explicit witnesses for
exactly the table fields that are existential.  Identity and nonidentity
twist rows are kept separate, matching the table's case split. -/
structure LowTableBackedExactOddAssembly
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j) where
  assembly : ExactOddPhaseAssembly F K globalChi globalPsi data D
    (t := t) (m := (data.twistData 1).conductor) (OddNormIndex F K)
  upstairsCriticalCoordinate : LamprechtCriticalCoordinate K d epsilon
  baseCriticalCoordinate : LamprechtCriticalCoordinate F d epsilon
  normCriticalCoordinate : OddNormIndex F K →
    LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)
  twistCriticalCoordinate : OddNormIndex F K →
    LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)
  extensionPhase : D.extension = LocalPhaseData.stationary
    (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table WUp upstairsCriticalCoordinate)
  baseTwistPhase : D.twist 1 = LocalPhaseData.stationary
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table baseCriticalCoordinate)
  nonidentityNormPhase : ∀ j : OddNormIndex F K,
    D.normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
          hF delta epsilon1 hdelta hT hgammaF P j
            (normCriticalCoordinate j))
  nonidentityTwistPhase : ∀ j : OddNormIndex F K,
    D.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
            (twistCriticalCoordinate j))
  range_is_low : assembly.parameterRange = .low hLow

/-- Preferred low odd-prime result wrapper.  Unlike the legacy low table
record, its type explicitly carries odd degree and its correction coordinates
are tied to the literal simultaneous pair/table witnesses. -/
structure LowSourceTiedTableBackedExactOddAssembly
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist) where
  tableBacked : LowTableBackedExactOddAssembly F K ht hres pi hpi hgen data
    D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table WUp WTwist
  odd_degree : Odd (Module.finrank F K)
  coefficient_source : tableBacked.assembly.A =
    lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
  normalizedRatio_source : tableBacked.assembly.u =
    lowNormalizedRatio F K epsilon1 P
  normalizedNorm_source : tableBacked.assembly.n =
    lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  zZero_source : tableBacked.assembly.zZero =
    OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) R.correctionUnits
  z_source : tableBacked.assembly.z = fun j ↦
    OddNormCorrectionUnitData.z ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) R.correctionUnits j
  correctionCoordinate_source : tableBacked.assembly.X = R.X

/-- Result eliminator type for a strengthened low source-tied odd assembly. -/
def LowSourceTiedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist)
    (B : LowSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen
      data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R) : Prop :=
  ∀ (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK),
    B.tableBacked.assembly.Result hDeltaF hDeltaK

/-- Every strengthened low source-tied odd assembly has the full structured
odd result, with no residual cancellation. -/
theorem lowSourceTiedExactOddResultEliminator
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist)
    (B : LowSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen
      data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R) :
    LowSourceTiedExactOddResultEliminator (DeltaF := DeltaF)
      (DeltaK := DeltaK) F K ht hres pi hpi hgen data D
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist R B := by
  intro hDeltaF hDeltaK
  exact B.tableBacked.assembly.result hDeltaF hDeltaK

/-- Specialized low constructor: range dispatch is definitionally low;
all norm rows use `lowNormCharacterPowerPhase`, while extension/nonzero
twist rows use explicit witnesses destructured from the Prop-valued table. -/
def lowTableBackedExactOddAssembly
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
              (CTwist j)))
    (R : OddGlobalScalarInput F K ht hres pi hpi hgen
      (by omega : 0 < t)
      globalChi globalPsi data D) :
    LowTableBackedExactOddAssembly F K ht hres pi hpi hgen data D chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table WUp WTwist := by
  let A := exactOddAssemblyOfActualNormRows F K ht hres pi hpi hgen
    (by omega : 0 < t) data D
    (.low hLow)
    (fun j ↦ lowOddNormPhaseForComputationalData
      F K ht hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j
        (CNorm j)) hNorm R
  exact
    { assembly := A
      upstairsCriticalCoordinate := CUp
      baseCriticalCoordinate := CBase
      normCriticalCoordinate := CNorm
      twistCriticalCoordinate := CTwist
      extensionPhase := hExtension
      baseTwistPhase := hBase
      nonidentityNormPhase := hNorm
      nonidentityTwistPhase := hTwist
      range_is_low := rfl }

/-- Preferred low-table constructor.  Endpoint and admissible-character
cancellation are derived from the actual low rows; only separated additive
and multiplicative scalar identities remain inputs. -/
def lowTableBackedExactOddAssemblySeparated
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
          hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
              (CTwist j)))
    (R : OddSeparatedScalarInput F K ht hres pi hpi hgen
      (by omega : 0 < t) globalChi globalPsi data D) :
    LowTableBackedExactOddAssembly F K ht hres pi hpi hgen data D chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table WUp WTwist := by
  have hEndpoint : D.factors.endpoint = 1 := by
    apply endpointFactor_eq_one_of_actual_stationary_rows
    · exact ⟨_, hExtension⟩
    · refine nonidentityNormStationary_of_optionEquiv
        (oddNormCharacterIndexing F K ht hres pi hpi hgen)
        (oddNormCharacterIndexing_none F K ht hres pi hpi hgen) ?_
      intro j
      rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen j]
      exact ⟨_, hNorm j⟩
    · refine allTwistsStationary_of_equiv
        (oddNormCharacterIndexing F K ht hres pi hpi hgen) ?_
      intro index
      cases index with
      | none =>
          rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
          exact ⟨_, hBase⟩
      | some j =>
          rw [oddNormCharacterIndexing_some F K ht hres pi hpi hgen j]
          exact ⟨_, hTwist j⟩
  have hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm := by
    rw [data.extensionQuasiChar_character, data.twistData_character]
    exact (normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi).symm
  let shape := lowOddAdmissibleShapeOfActualRows F K ht hres pi hpi hgen
    data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp WTwist CUp CBase CNorm CTwist
        hExtension hBase hNorm hTwist
  have hAdmissible : D.factors.admissibleCharacter = 1 :=
    LowOddAdmissibleShape.factor_eq_one data ht hres pi hpi hgen hchiArg
      shape
  let A := exactOddAssemblyOfActualNormRowsSeparated F K ht hres pi hpi hgen
    (by omega : 0 < t) data D (.low hLow)
      (fun j ↦ lowOddNormPhaseForComputationalData
        F K ht hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j
          (CNorm j)) hNorm R hEndpoint hAdmissible
  exact
    { assembly := A
      upstairsCriticalCoordinate := CUp
      baseCriticalCoordinate := CBase
      normCriticalCoordinate := CNorm
      twistCriticalCoordinate := CTwist
      extensionPhase := hExtension
      baseTwistPhase := hBase
      nonidentityNormPhase := hNorm
      nonidentityTwistPhase := hTwist
      range_is_low := rfl }

/-- Preferred low odd-prime constructor.  Its separated elementary
identities are derived from the literal table representatives, and the
degree-parity hypothesis is part of the resulting API. -/
def lowSourceTiedTableBackedExactOddAssembly
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
                (CTwist j)))
    (R : LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist) :
    LowSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist R := by
  let scalar : OddSeparatedScalarInput F K ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) globalChi globalPsi data D :=
    { A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
      u := lowNormalizedRatio F K epsilon1 P
      n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
      norm_u := lowNormalizedRatio_norm F K epsilon1 P
      zZero := OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) R.correctionUnits
      z := fun j ↦ OddNormCorrectionUnitData.z ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) R.correctionUnits j
      X := R.X
      X_eq := R.X_eq
      chiLinearization := R.chiLinearization
      powerLinearization := R.powerLinearization
      additiveDenominator_eq := lowOddActualRows_additiveDenominator_eq F K
        ht hres pi hpi hgen data D chiK psiK hF hminimal hchi hpsi hLow
          delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table hodd
            WUp WTwist R CUp CBase CNorm CTwist hExtension hBase hNorm hTwist
      multiplicativeDenominator_eq :=
        lowOddActualRows_multiplicativeDenominator_eq F K ht hres pi hpi
          hgen data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
            hdelta hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R
              CUp CBase CNorm CTwist hExtension hBase hNorm hTwist }
  let B := lowTableBackedExactOddAssemblySeparated F K ht hres pi hpi hgen
    data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp WTwist CUp CBase CNorm CTwist
        hExtension hBase hNorm hTwist scalar
  exact
    { tableBacked := B
      odd_degree := hodd
      coefficient_source := rfl
      normalizedRatio_source := rfl
      normalizedNorm_source := rfl
      zZero_source := rfl
      z_source := rfl
      correctionCoordinate_source := rfl }

/-- The remaining low odd correction input after all algebra forced by the
actual parameter-table rows has been removed.  It contains only the literal
correction units, their norm--trace coordinate, and the two pointwise
character linearizations used after the exact stationary assembly. -/
structure LowOddActualRowsCorrectionInput
    (hodd : Odd (Module.finrank F K))
    (WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j) where
  correctionUnits : OddNormCorrectionUnitData F K ht hres pi hpi hgen
    (by have hm := hF.conductor_gt_one; omega)
      (lowNormalizedRatio F K epsilon1 P)
      (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT))
  X : F
  X_eq : X = trace F K (lowNormalizedRatio F K epsilon1 P) +
    lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
      (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
        (by have hm := hF.conductor_gt_one; omega) correctionUnits : Fˣ) : F) -
          1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j *
        (((OddNormCorrectionUnitData.z ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) correctionUnits j : Fˣ) :
            F) - 1)
  chiLinearization :
    globalChi (OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
      (by have hm := hF.conductor_gt_one; omega) correctionUnits) =
    globalPsi
      (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
      lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) *
        (((OddNormCorrectionUnitData.zZero ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) correctionUnits : Fˣ) :
            F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1
          (OddNormCorrectionUnitData.z ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) correctionUnits j) =
      globalPsi
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
        oddNormIndexScalar F K ht hres pi hpi hgen
          (by have hm := hF.conductor_gt_one; omega) j *
          (((OddNormCorrectionUnitData.z ht hres pi hpi hgen
            (by have hm := hF.conductor_gt_one; omega) correctionUnits j : Fˣ) :
              F) - 1))

/-- Low odd correction coordinates pinned definitionally to the constructor
which derives every raw row identity from the actual low witnesses. -/
def LowOddActualRowsCorrectionInput.toSourceTied
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
        hgammaF hgammaK P table hodd WUp WTwist) :
    LowOddSourceTiedCorrectionCoordinates F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist :=
  lowOddSourceTiedCorrectionCoordinatesOfActualRows F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R.correctionUnits
        R.X R.X_eq R.chiLinearization R.powerLinearization

/-- Public low odd wrapper whose correction coordinates can only be those
derived from the actual low stationary rows. -/
abbrev LowActualRowsTableBackedExactOddAssembly
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
        hgammaF hgammaK P table hodd WUp WTwist) :=
  LowSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table hodd WUp WTwist
        (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF hminimal
          hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
            table hodd WUp WTwist)

/-- Construct the public low odd wrapper from the actual four local phase
rows; no raw additive, exceptional-unit, or indexed row-ratio equality is an
argument. -/
def lowActualRowsTableBackedExactOddAssembly
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
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
                (CTwist j))) :
    LowActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
        hT hgammaF hgammaK P table hodd WUp WTwist R :=
  lowSourceTiedTableBackedExactOddAssembly F K ht hres pi hpi hgen data D
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table hodd WUp WTwist CUp CBase CNorm CTwist
        hExtension hBase hNorm hTwist
          (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF hminimal
            hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK
              P table hodd WUp WTwist)

/-- Public low odd result obtained directly from the actual stationary rows.
The table-backed assembly is constructed internally, so no caller-supplied
assembly or raw row-algebra proof occurs in this interface. -/
theorem lowActualRowsConstructedExactOddResultEliminator
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
    (CUp : LamprechtCriticalCoordinate K d epsilon)
    (CBase : LamprechtCriticalCoordinate F d epsilon)
    (CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t))
    (hExtension : D.extension = LocalPhaseData.stationary
      (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WUp CUp))
    (hBase : D.twist 1 = LocalPhaseData.stationary
      (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
        data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table CBase))
    (hNorm : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
            hF delta epsilon1 hdelta hT hgammaF P j (CNorm j)))
    (hTwist : ∀ j : OddNormIndex F K,
      D.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary
          (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table j (WTwist j)
                (CTwist j))) :
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
                  CUp CBase CNorm CTwist hExtension hBase hNorm hTwist) :=
  lowSourceTiedExactOddResultEliminator F K ht hres pi hpi hgen data D chiK
    psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table hodd WUp WTwist
        (R.toSourceTied F K ht hres pi hpi hgen data chiK psiK hF hminimal
          hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
            table hodd WUp WTwist)
        (lowActualRowsTableBackedExactOddAssembly F K ht hres pi hpi hgen
          data D chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table hodd WUp WTwist R CUp CBase
              CNorm CTwist hExtension hBase hNorm hTwist)

end LowTableBacked

end

end LanglandsFirstMainLemma
