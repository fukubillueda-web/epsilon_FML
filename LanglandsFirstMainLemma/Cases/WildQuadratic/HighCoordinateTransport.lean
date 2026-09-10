import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Cases.WildQuadratic.CoordinateTransport
import LanglandsFirstMainLemma.Cases.WildQuadratic.LowProductCoordinateTransport

namespace LanglandsFirstMainLemma

noncomputable section

/-!
# Strict-high coordinate transport for the wild quadratic case

This file transports the original simultaneous high parameter choice into
q-polymorphic upper and lower-product coordinates.  In particular its public
constructor receives the original `WildQuadraticHighParameterData`: the
identity `beta = delta * N(beta1)` is retained, and `beta` is never replaced
by a bare norm.
-/

section HighBranchMatrix

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ}

/-- Strict-high upper-coordinate eliminator.  Its only source-bearing
hypotheses are exactly `aboveMEvenTOdd` and `aboveMOddTOdd`; the low and
boundary critical rows contradict the strict-high conductor range. -/
theorem wildQuadraticHigh_upperCoordinates_of_consumers
    (V : WildQuadraticCommonCoefficientView F K t m)
    (hhigh : t + 1 < m)
    (hAboveEven : ∀
      (tau : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .aboveMEvenTOdd tau)
      (q : CharTwoRefinement (ResidueField F)),
      Nonempty (ActualUpperCoordinateCertificate F K V.correction q
        V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF))
    (hAboveOdd : ∀
      (tau chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .aboveMOddTOdd tau chiF)
      (q : CharTwoRefinement (ResidueField F)),
      Nonempty (ActualUpperCoordinateCertificate F K V.correction q
        V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF)) :
    ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (V.criticalInputs.toCoefficientData q).affineCoefficient .chiK =
          some lambda →
        Nonempty (ActualUpperCoordinateCertificate F K V.correction q
          V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF) := by
  intro q lambda haff
  generalize hI : V.criticalInputs = I at haff ⊢
  cases I with
  | belowMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMEvenTOdd tau =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMOddTEven chiF =>
      have hrange := congrArg WildQuadraticCoefficientRow.range
        (show (.belowMOddTEven : WildQuadraticCoefficientRow) =
          WildQuadraticCoefficientRow.ofConductors (m - 1) t by
            simpa only [hI, WildQuadraticCoefficientInputs.row] using
              V.criticalInputs_row)
      rw [WildQuadraticCoefficientRow.ofConductors_range_above (by omega)] at hrange
      simp [WildQuadraticCoefficientRow.range] at hrange
  | belowMOddTOdd tau chiF =>
      have hrange := congrArg WildQuadraticCoefficientRow.range
        (show (.belowMOddTOdd : WildQuadraticCoefficientRow) =
          WildQuadraticCoefficientRow.ofConductors (m - 1) t by
            simpa only [hI, WildQuadraticCoefficientInputs.row] using
              V.criticalInputs_row)
      rw [WildQuadraticCoefficientRow.ofConductors_range_above (by omega)] at hrange
      simp [WildQuadraticCoefficientRow.range] at hrange
  | boundaryEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | boundaryOdd rho hrho hden tau chiF =>
      have hrange := congrArg WildQuadraticCoefficientRow.range
        (show (.boundaryOdd : WildQuadraticCoefficientRow) =
          WildQuadraticCoefficientRow.ofConductors (m - 1) t by
            simpa only [hI, WildQuadraticCoefficientInputs.row] using
              V.criticalInputs_row)
      rw [WildQuadraticCoefficientRow.ofConductors_range_above (by omega)] at hrange
      simp [WildQuadraticCoefficientRow.range] at hrange
  | aboveMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMEvenTOdd tau =>
      simpa only [hI] using hAboveEven tau hI q
  | aboveMOddTEven chiF =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMOddTOdd tau chiF =>
      simpa only [hI] using hAboveOdd tau chiF hI q

end HighBranchMatrix

namespace ActualProductCoordinateCertificate

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- Construct an above-range product certificate from the exact normalized
delta ratio, together with the genuine even-tau stationary factor at the
common unit. -/
noncomputable def ofAboveNormalizedDeltaRatio
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (product chiF : QuotientDerivedNormalizedCriticalFunction F)
    (product_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F product S.tauChiF)
    (product_character : product.chi.character =
      tauData.character * chiFData.character)
    (product_psi : product.psi = psiF)
    (product_ratio_sum : S.tauChiF.ratio = S.tau.ratio + S.chiF.ratio)
    (hrange : (I.toCoefficientData q).range = .above)
    (chiF_source : I.chiFSource = some chiF)
    (chiF_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F chiF S.chiF)
    (chiF_character : chiF.chi.character = chiFData.character)
    (chiF_psi : chiF.psi = psiF)
    (hconductor : chiF.chi.conductor = product.chi.conductor)
    (hargument : ∀ z, (I.toCoefficientData q).lowerProductScale z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        chiF product hconductor *
          (I.toCoefficientData q).lowerChiArgument z)
    (stable_factor : ∀ z,
      stationaryUnitFactor tauData.character psiF S.tau
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift product
          (QuotientDerivedNormalizedCriticalFunction.normalizedCommonProductLift
            ((I.toCoefficientData q).lowerProductScale z))) = 1) :
    ActualProductCoordinateCertificate F K q I S tauData chiFData psiF where
  product := product
  product_pair := product_pair
  product_character := product_character
  product_psi := product_psi
  product_ratio_sum := product_ratio_sum
  rangeCoordinates := .above hrange
    { chiF := chiF
      chiF_source := chiF_source
      chiF_pair := chiF_pair
      chiF_character := chiF_character
      chiF_psi := chiF_psi
      coordinates := ProductDominantCoordinates.ofNormalizedDeltaRatio
        product chiF _ _ hconductor hargument
      stable_factor := stable_factor }

end ActualProductCoordinateCertificate

/-- Any primitive upper certificate uses the exact local characters and
selected pair of the retained extension row, hence it carries that row's
complete normalized finite-sum phase. -/
private theorem wildQuadraticPreparation_upperCertificate_rowPhase
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ}
    {V : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {phaseData : FirstMainPhaseData F K V.chiFData.character
      V.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data phaseData (t := t) (m := m)}
    {rows : WildQuadraticActualPhaseRows V data phaseData assembly}
    {q : CharTwoRefinement (ResidueField F)}
    (C : ActualUpperCoordinateCertificate F K V.correction q
      V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF) :
    rows.extension.criticalFactor =
      QuotientDerivedNormalizedCriticalFunction.phase K C.upper := by
  have hchi : C.upper.chi = data.extensionQuasiChar := by
    apply LocalQuasiCharData.ext_character K
    rw [C.upper_character]
    exact data.extensionQuasiChar_character.symm
  have hpsi : C.upper.psi = data.extensionAddChar := by
    apply LocalAddCharData.ext_character
    rw [C.upper_additive]
    exact data.extensionAddChar_character.symm
  have hpair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair K
        C.upper rows.extension.selectedStationaryPair := by
    rw [rows.extension_pair]
    exact C.upper_pair
  have hphase :=
    rows.extension.criticalFactor_eq_quotientSourcePhase_of_matches C.upper
      ⟨hchi, hpsi⟩ hpair
  simpa only [quotientSourcePhase] using hphase

/-- Parity of the actual conductor determines the constructor of a supplied
stationary Lamprecht row. -/
private theorem wildQuadraticHigh_isEven_of_even_conductor
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (S : LocalLamprechtPhaseData E chi psi) (h : Even chi.conductor) :
    S.IsEven := by
  cases S with
  | even => trivial
  | odd d hm =>
      obtain ⟨j, hj⟩ := h
      simp only [LocalLamprechtPhaseData.IsEven]
      omega

/-- A genuine even local row is stationary-linear on its actual half-depth
lattice.  This is the stable factor used in the strict below/above product
certificates. -/
private theorem wildQuadraticPreparation_evenRow_stationaryUnitFactor_eq_one
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (row : LocalLamprechtPhaseData E chi psi) (heven : Even chi.conductor)
    (P : WildQuadraticStationaryPair E)
    (hpair : row.selectedStationaryPair = P)
    (y : E) (hy : y ∈ lattice E ((chi.conductor / 2 : ℕ) : ℤ))
    (unit : Eˣ) (hunit : (unit : E) = 1 + y) :
    stationaryUnitFactor chi.character psi P unit = 1 := by
  cases row with
  | odd d hm =>
      obtain ⟨j, hj⟩ := heven
      omega
  | even d hm hlarge Gamma c hc =>
      have hd : chi.conductor / 2 = d := by omega
      let ylat : lattice E (d : ℤ) := ⟨y, by simpa only [hd] using hy⟩
      have hlin := stationaryNumeratorClass_linearization E chi psi
        (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 0
          (by omega) (by simpa using hm) hlarge)
        Gamma Gamma.property c hc ylat
      have hunit' : unit = positiveUnitOfLattice E
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge).pos ylat := by
        apply Units.ext
        rw [hunit]
        rfl
      rw [hunit']
      have hlinC := congrArg (Units.val : ℂˣ → ℂ) hlin
      have harg :
          (c : E) / ((Gamma : Eˣ) : E) *
                (((positiveUnitOfLattice E
                    (lamprechtFormula_stationaryDepth E chi d 0
                      (by omega) (by simpa using hm) hlarge).pos ylat : Eˣ) : E) - 1) =
            (c : E) * (ylat : E) / ((Gamma : Eˣ) : E) := by
        change (c : E) / ((Gamma : Eˣ) : E) *
          ((1 + (ylat : E)) - 1) = _
        field_simp [AdmissibleGamma.coe_ne_zero]
        ring
      rw [stationaryUnitFactor, ← hpair]
      dsimp only [LocalLamprechtPhaseData.selectedStationaryPair,
        WildQuadraticStationaryPair.ratio]
      rw [harg, hlinC]
      field_simp [ContinuousAddChar.apply_ne_zero]

/- The selected stationary factor of either parity is one on the actual
ceiling-half-depth lattice. -/

/-- One producer serves both strict-above positive product rows. -/
private noncomputable def wildQuadraticPreparation_strictAboveProductCertificate
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ}
    {V : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {phaseData : FirstMainPhaseData F K V.chiFData.character
      V.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data phaseData (t := t) (m := m)}
    {rows : WildQuadraticActualPhaseRows V data phaseData assembly}
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (q : CharTwoRefinement (ResidueField F))
    (product chiF : QuotientDerivedNormalizedCriticalFunction F)
    (product_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F product
        (data.twistData assembly.indexing.tau) data.baseAddChar)
    (product_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product rows.twist.selectedStationaryPair)
    (chiF_source : V.criticalInputs.chiFSource = some chiF)
    (chiF_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F chiF
        V.stationaryPairs.chiF)
    (chiF_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F chiF
        V.chiFData V.psiF)
    (hrange : (V.criticalInputs.toCoefficientData q).range = .above)
    (habove : t + 1 < m)
    (hconductor : chiF.chi.conductor = product.chi.conductor)
    (hlower : V.tauData.conductor < product.chi.conductor) :
    { C : ActualProductCoordinateCertificate F K q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF //
      rows.twist.criticalFactor =
        QuotientDerivedNormalizedCriticalFunction.phase F C.product } := by
  have hninvMem : ((V.correction.n : F)⁻¹) ∈ lattice F 1 := by
    rw [mem_lattice, ord_inv, V.correction.target_order]
    change ((1 : ℤ) : WithTop ℤ) ≤
      -(((((t + 1 : ℕ) : ℤ) - (m : ℤ) : ℤ) : WithTop ℤ))
    rw [show ((t + 1 : ℕ) : ℤ) - (m : ℤ) =
      -((m - (t + 1) : ℕ) : ℤ) by omega]
    norm_cast
    omega
  let u : unitGroup F :=
    wildQuadratic_oneAddLocalUnit ((V.correction.n : F)⁻¹) hninvMem
  have hpsi : chiF.psi = product.psi := by
    rw [chiF_local.2, product_local.2, coordinates.baseAddData_eq]
  have hproductPair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product V.stationaryPairs.tauChiF := by
    rw [← rows.twist_pair]
    exact product_pair
  have hratio : (product.beta : F) / ((product.Gamma : Fˣ) : F) =
      (((u : unitGroup F) : Fˣ) : F) *
        ((chiF.beta : F) / ((chiF.Gamma : Fˣ) : F)) := by
    calc
      (product.beta : F) / ((product.Gamma : Fˣ) : F) =
          V.stationaryPairs.tauChiF.ratio := by
            rw [hproductPair.1, hproductPair.2]
            rfl
      _ = V.stationaryPairs.tau.ratio *
          ((V.correction.n : F) + 1) := V.tauChiF_ratio
      _ = (((u : unitGroup F) : Fˣ) : F) *
          ((chiF.beta : F) / ((chiF.Gamma : Fˣ) : F)) := by
            rw [chiF_pair.1, chiF_pair.2]
            simp only [u, wildQuadratic_oneAddLocalUnit_coe]
            change V.stationaryPairs.tau.ratio *
              ((V.correction.n : F) + 1) =
                (1 + (V.correction.n : F)⁻¹) *
                  V.stationaryPairs.chiF.ratio
            rw [V.chiF_ratio]
            field_simp [Units.ne_zero V.correction.n]
  have hresidue : ((residueUnits F u : (ResidueField F)ˣ) :
      ResidueField F) = (1 : ResidueField F) ^ 2 := by
    rw [wildQuadratic_oneAddLocalUnit_residue]
    simp
  have hratioResidue :
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        chiF product hconductor = 1 :=
    QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_eq_of_scale
      chiF product hpsi hconductor u hratio 1 hresidue
  have hargument : ∀ z,
      (V.criticalInputs.toCoefficientData q).lowerProductScale z =
        QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
          chiF product hconductor *
            (V.criticalInputs.toCoefficientData q).lowerChiArgument z := by
    intro z
    rw [hratioResidue, one_mul]
    generalize hD : V.criticalInputs.toCoefficientData q = D at hrange ⊢
    cases D <;>
      simp_all [WildQuadraticCoefficientData.range,
        WildQuadraticCoefficientData.row,
        WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientData.lowerProductScale,
        WildQuadraticCoefficientData.lowerChiArgument]
  let rangeCoordinates : ProductRangeCoordinates F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF product :=
    .above hrange
      { chiF := chiF
        chiF_source := chiF_source
        chiF_pair := chiF_pair
        chiF_character := congrArg LocalQuasiCharData.character chiF_local.1
        chiF_psi := chiF_local.2
        coordinates := ProductDominantCoordinates.ofNormalizedDeltaRatio
          product chiF _ _ hconductor hargument
        stable_factor := fun z ↦ by
          have hlt :
              (data.normCharacterData assembly.indexing.tau).conductor <
                product.chi.conductor := by
            rw [coordinates.tauData_eq]
            exact hlower
          have hs :=
            wildQuadratic_lowerRow_stable_on_productCriticalUnit
              product (data.normCharacterData assembly.indexing.tau) rows.tau
                V.stationaryPairs.tau rows.tau_pair hlt
                ((ProductDominantCoordinates.ofNormalizedDeltaRatio product chiF
                  (V.criticalInputs.toCoefficientData q).lowerProductScale
                  (V.criticalInputs.toCoefficientData q).lowerChiArgument
                  hconductor hargument).productLift z)
          rw [congrArg LocalQuasiCharData.character coordinates.tauData_eq,
            coordinates.baseAddData_eq] at hs
          exact hs }
  exact wildQuadratic_productCertificate_ofActualTwist coordinates q
    product product_local product_pair rangeCoordinates



/-! The strict-high normalization is most cleanly separated from the
field-level residual calculation.  This lemma is the exact characteristic-two
argument used after that calculation has produced the natural scalar. -/
private theorem wildQuadraticPreparation_high_normalized_scalar_eq_one
    {k : Type} [Field k] [Fintype k] [CharP k 2]
    (upper tau : CriticalPolarFunction k (absoluteTraceChar k) 1)
    (lambda : k)
    (htransport : ∀ z : k,
      upper z = tau (lambda * z ^ 2) *
        absoluteTraceChar k (lambda * z ^ 2)) :
    lambda = 1 := by
  have hpolar (x y : k) :
      absoluteTraceChar k (x * y) =
        absoluteTraceChar k (lambda * (x * y)) := by
    have hu := upper.map_add x y
    have ht := tau.map_add (lambda * x ^ 2) (lambda * y ^ 2)
    rw [htransport (x + y), htransport x, htransport y] at hu
    have hsq : (x + y) ^ 2 = x ^ 2 + y ^ 2 := CharTwo.add_sq x y
    rw [hsq, mul_add, ht] at hu
    have hsquare :
        absoluteTraceChar k
            ((lambda * x ^ 2) * (lambda * y ^ 2)) =
          absoluteTraceChar k (lambda * (x * y)) := by
      calc
        absoluteTraceChar k
            ((lambda * x ^ 2) * (lambda * y ^ 2)) =
            absoluteTraceChar k ((lambda * (x * y)) ^ 2) := by
              congr 1
              ring
        _ = absoluteTraceChar k (lambda * (x * y)) :=
          absoluteTraceChar_sq k _
    simp only [one_mul] at hu
    rw [(absoluteTraceChar k).map_add_eq_mul, hsquare] at hu
    have hchar_ne (z : k) : absoluteTraceChar k z ≠ 0 := by
      intro hz
      have hzneg := (absoluteTraceChar k).map_add_eq_mul z (-z)
      rw [add_neg_cancel, (absoluteTraceChar k).map_zero_eq_one, hz,
        zero_mul] at hzneg
      exact one_ne_zero hzneg
    let common : ℂ := tau (lambda * x ^ 2) * tau (lambda * y ^ 2) *
      absoluteTraceChar k (lambda * x ^ 2) *
        absoluteTraceChar k (lambda * y ^ 2)
    have hcommon_ne : common ≠ 0 := by
      dsimp only [common]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (tau.ne_zero _) (tau.ne_zero _)) (hchar_ne _))
        (hchar_ne _)
    have hcancel : common * absoluteTraceChar k (lambda * (x * y)) =
        common * absoluteTraceChar k (x * y) := by
      dsimp only [common]
      simpa only [one_mul, mul_assoc, mul_left_comm, mul_comm] using hu
    exact (mul_left_cancel₀ hcommon_ne hcancel).symm
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (AddChar.IsPrimitive.of_ne_one (absoluteTraceChar_ne_one k))
  apply AddChar.ext
  intro z
  simp only [AddChar.mulShift_apply, one_mul]
  simpa only [one_mul] using (hpolar 1 z).symm

private theorem wildQuadraticPreparation_wildQuadraticHigh_tauTrace_deep
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t r v dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hdK : dK = v + r)
    (u deltaK : K)
    (hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (hdeltaK : ord K deltaK = ((dK : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    trace F K (u * (deltaK * algebraMap F K (teichmuller F z : F))) ∈
      lattice F ((r + 1 : ℕ) : ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  have hdiff : differentExponent F K = t + 1 :=
    differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen
  have hzF : (0 : WithTop ℤ) ≤ ord F (teichmuller F z : F) :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  have hzK : (0 : WithTop ℤ) ≤
      ord K (algebraMap F K (teichmuller F z : F)) := by
    rw [ord_algebraMap, hram]
    exact nsmul_nonneg hzF 2
  have hy :
      u * (deltaK * algebraMap F K (teichmuller F z : F)) ∈
        lattice K (r : ℤ) := by
    rw [mem_lattice, ord_mul, ord_mul, hu, hdeltaK, hdK]
    calc
      (((r : ℕ) : ℤ) : WithTop ℤ) =
          ((-(v : ℤ) : ℤ) : WithTop ℤ) +
            (((v + r : ℕ) : ℤ) : WithTop ℤ) + 0 := by
              norm_num
      _ ≤ ((-(v : ℤ) : ℤ) : WithTop ℤ) +
            (((v + r : ℕ) : ℤ) : WithTop ℤ) +
              ord K (algebraMap F K (teichmuller F z : F)) :=
        by simpa only [add_comm] using
          add_le_add_left hzK
            (((-(v : ℤ) : ℤ) : WithTop ℤ) +
              (((v + r : ℕ) : ℤ) : WithTop ℤ))
      _ = ((-(v : ℤ) : ℤ) : WithTop ℤ) +
            ((((v + r : ℕ) : ℤ) : WithTop ℤ) +
              ord K (algebraMap F K (teichmuller F z : F))) := by
        rw [add_assoc]
  have htrace := trace_mem_lattice_floor F K pi hpi hgen (r : ℤ) hy
  rw [hdiff, hram] at htrace
  apply lattice_antitone F (n :=
      (((r : ℤ) + ((t + 1 : ℕ) : ℤ)) / (2 : ℤ)))
  · have hrpos : 0 < r := by omega
    omega
  · exact htrace

/-! Explicit strict-high post-drop coordinate.  The scalar retains the
original normalized ratio `u` through the certified identity `N(u)=n`; no
replacement of the manuscript representative `beta` by a bare norm is used.
The returned lift is the one consumed by `ActualLowerStationaryCoordinate`. -/
private theorem wildQuadraticPreparation_wildQuadraticHigh_tauCoordinate
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t r v dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hdK : dK = v + r)
    (u : Kˣ) (n : Fˣ) (hnormu : normUnits F K u = n)
    (hu : ord K (u : K) = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((r : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    ∃ scalar0 : unitGroup F,
      ((scalar0 : Fˣ) : F) =
          (n : F) * norm F K (deltaK : K) / (deltaF : F) ∧
      ∃ tauLift : lattice F 0,
        (tauLift : F) =
            phaseReductionNormPolynomial F K
                ((u : K) * ((deltaK : K) *
                  algebraMap F K (teichmuller F z : F))) /
              (deltaF : F) ∧
        reduce F (tauLift : F) tauLift.property =
          ((residueUnits F scalar0 : (ResidueField F)ˣ) : ResidueField F) *
            z ^ 2 := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  let zF : F := (teichmuller F z : F)
  let y : K := (u : K) * ((deltaK : K) * algebraMap F K zF)
  have hzF : (0 : WithTop ℤ) ≤ ord F zF :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  have hzK : (0 : WithTop ℤ) ≤ ord K (algebraMap F K zF) := by
    rw [ord_algebraMap, hram]
    exact nsmul_nonneg hzF 2
  have hy : y ∈ lattice K (r : ℤ) := by
    rw [mem_lattice]
    dsimp only [y]
    rw [ord_mul, ord_mul, hu, hdeltaK, hdK]
    calc
      (((r : ℕ) : ℤ) : WithTop ℤ) =
          ((-(v : ℤ) : ℤ) : WithTop ℤ) +
            (((v + r : ℕ) : ℤ) : WithTop ℤ) + 0 := by norm_num
      _ ≤ ((-(v : ℤ) : ℤ) : WithTop ℤ) +
            (((v + r : ℕ) : ℤ) : WithTop ℤ) + ord K (algebraMap F K zF) :=
        by simpa only [add_comm] using
          add_le_add_left hzK
            (((-(v : ℤ) : ℤ) : WithTop ℤ) +
              (((v + r : ℕ) : ℤ) : WithTop ℤ))
      _ = ((-(v : ℤ) : ℤ) : WithTop ℤ) +
            ((((v + r : ℕ) : ℤ) : WithTop ℤ) +
              ord K (algebraMap F K zF)) := by rw [add_assoc]
  have htraceDeep : trace F K y ∈ lattice F ((r + 1 : ℕ) : ℤ) := by
    simpa only [y, zF] using wildQuadraticPreparation_wildQuadraticHigh_tauTrace_deep
      F K ht hres pi hpi hgen hdegree htpos hT hdK (u : K) (deltaK : K)
        hu hdeltaK z
  have htrace : trace F K y ∈ lattice F (r : ℤ) :=
    lattice_antitone F (by omega) htraceDeep
  have hnorm : norm F K y ∈ lattice F (r : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    simpa only [mem_lattice] using hy
  have hpoly : phaseReductionNormPolynomial F K y ∈ lattice F (r : ℤ) := by
    rw [wildQuadratic_phaseReductionNormPolynomial_eq_trace_add_norm
      F K hdegree]
    exact add_mem_lattice F htrace hnorm
  have hpolyDiv : phaseReductionNormPolynomial F K y / (deltaF : F) ∈
      lattice F 0 := by
    exact (div_mem_lattice_iff F (deltaF : F)
      (phaseReductionNormPolynomial F K y) (r : ℤ) 0 hdeltaF).2
        (by simpa using hpoly)
  let scalar : Fˣ := n * normUnits F K deltaK / deltaF
  have hscalarOrd : ord F (scalar : F) = (0 : WithTop ℤ) := by
    dsimp only [scalar]
    rw [Units.val_div_eq_div_val, Units.val_mul, ord_div, ord_mul,
      coe_normUnits, ord_norm, hres, one_nsmul, hdeltaK, hdeltaF, hdK]
    have hnord : ord F (n : F) =
        ((-(v : ℤ) : ℤ) : WithTop ℤ) := by
      have hnormuOrd := congrArg (fun a : Fˣ ↦ ord F (a : F)) hnormu
      simpa only [coe_normUnits, ord_norm, hres, one_nsmul, hu] using
        hnormuOrd.symm
    rw [hnord]
    norm_num
  let scalar0 : unitGroup F :=
    ⟨scalar, (mem_unitGroup_iff_ord_eq_zero F scalar).2 hscalarOrd⟩
  refine ⟨scalar0, ?_, ?_⟩
  · simp only [scalar0, scalar, Units.val_div_eq_div_val, Units.val_mul,
      coe_normUnits]
  let tauLift : lattice F 0 :=
    ⟨phaseReductionNormPolynomial F K y / (deltaF : F), hpolyDiv⟩
  refine ⟨tauLift, rfl, ?_⟩
  let rhs : F := (scalar : F) * (teichmuller F (z ^ 2) : F)
  have hscalarInt : (scalar : F) ∈ lattice F 0 := by
    rw [mem_lattice, hscalarOrd]
    exact le_rfl
  have hrhs : rhs ∈ lattice F 0 := by
    exact mul_mem_lattice F hscalarInt
      ((mem_lattice_zero_iff F).2 (teichmuller F (z ^ 2)).property)
  have hnormExact : norm F K y / (deltaF : F) =
      (scalar : F) * zF ^ 2 := by
    have hnormuVal := congrArg (Units.val : Fˣ → F) hnormu
    simp only [coe_normUnits] at hnormuVal
    dsimp only [y, scalar]
    simp only [map_mul, Algebra.norm_algebraMap, hdegree, Units.val_div_eq_div_val,
      Units.val_mul, coe_normUnits]
    rw [hnormuVal]
    field_simp [Units.ne_zero deltaF]
  have hdiff : phaseReductionNormPolynomial F K y / (deltaF : F) -
      (scalar : F) * zF ^ 2 ∈ lattice F 1 := by
    have htraceDiv : trace F K y / (deltaF : F) ∈ lattice F 1 := by
      exact (div_mem_lattice_iff F (deltaF : F) (trace F K y)
        (r : ℤ) 1 hdeltaF).2 (by simpa using htraceDeep)
    rw [wildQuadratic_phaseReductionNormPolynomial_eq_trace_add_norm
      F K hdegree, add_div, hnormExact]
    simpa only [add_sub_cancel_right] using htraceDiv
  have hteichDiff : zF ^ 2 - (teichmuller F (z ^ 2) : F) ∈ lattice F 1 := by
    let aO : ringOfIntegers F := (teichmuller F z) ^ 2
    let bO : ringOfIntegers F := teichmuller F (z ^ 2)
    have hab : residueMap F aO = residueMap F bO := by
      dsimp only [aO, bO]
      rw [map_pow, residueMap_teichmuller, residueMap_teichmuller]
    have hmem := (residueMap_eq_residueMap_iff (F := F) aO bO).1 hab
    dsimp only [zF]
    change (((teichmuller F z) ^ 2 : ringOfIntegers F) : F) -
        (teichmuller F (z ^ 2) : F) ∈ lattice F 1
    simpa only [aO, bO] using hmem
  have hscaleDiff : (scalar : F) * zF ^ 2 - rhs ∈ lattice F 1 := by
    have hs := mul_mem_lattice F hscalarInt hteichDiff
    dsimp only [rhs]
    simpa [mul_sub] using hs
  have htotal : phaseReductionNormPolynomial F K y / (deltaF : F) - rhs ∈
      lattice F 1 := by
    have hs := add_mem_lattice F hdiff hscaleDiff
    convert hs using 1 <;> ring
  have hreduced : reduce F (tauLift : F) tauLift.property =
      reduce F rhs hrhs := by
    apply (reduce_eq_reduce_iff (F := F) _ _).2
    rw [congruentAtDepth_iff_sub_mem_lattice]
    exact htotal
  rw [hreduced]
  change residueMap F
      (⟨rhs, (mem_lattice_zero_iff F).1 hrhs⟩ : ringOfIntegers F) = _
  have hrhsEq :
      (⟨rhs, (mem_lattice_zero_iff F).1 hrhs⟩ : ringOfIntegers F) =
      (unitGroupMulEquivRingOfIntegers F scalar0 : ringOfIntegers F) *
        teichmuller F (z ^ 2) := by
    apply Subtype.ext
    rfl
  rw [hrhsEq, map_mul, ← residueUnits_coe, residueMap_teichmuller]

private theorem wildQuadraticPreparation_wildQuadraticHigh_tauCoordinates
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t r v dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hdK : dK = v + r)
    (u : Kˣ) (n : Fˣ) (hnormu : normUnits F K u = n)
    (hu : ord K (u : K) = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((r : ℤ) : WithTop ℤ)) :
    ∃ scalar0 : unitGroup F,
      ((scalar0 : Fˣ) : F) =
          (n : F) * norm F K (deltaK : K) / (deltaF : F) ∧
      ∀ z : ResidueField F,
        ∃ tauLift : lattice F 0,
          (tauLift : F) =
              phaseReductionNormPolynomial F K
                  ((u : K) * ((deltaK : K) *
                    algebraMap F K (teichmuller F z : F))) /
                (deltaF : F) ∧
          reduce F (tauLift : F) tauLift.property =
            ((residueUnits F scalar0 : (ResidueField F)ˣ) :
                ResidueField F) * z ^ 2 := by
  obtain ⟨scalar0, hscalar0, lift0, hlift0, hreduce0⟩ :=
    wildQuadraticPreparation_wildQuadraticHigh_tauCoordinate F K ht hres pi hpi hgen hdegree
      htpos hT hdK u n hnormu hu deltaK hdeltaK deltaF hdeltaF 0
  refine ⟨scalar0, hscalar0, ?_⟩
  intro z
  obtain ⟨scalar1, hscalar1, lift1, hlift1, hreduce1⟩ :=
    wildQuadraticPreparation_wildQuadraticHigh_tauCoordinate F K ht hres pi hpi hgen hdegree
      htpos hT hdK u n hnormu hu deltaK hdeltaK deltaF hdeltaF z
  have hscalar : scalar1 = scalar0 := by
    apply Subtype.ext
    apply Units.ext
    exact hscalar1.trans hscalar0.symm
  subst scalar1
  exact ⟨lift1, hlift1, hreduce1⟩

private theorem wildQuadraticPreparation_wildQuadratic_actualTauCoordinate_of_lift
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW : QuotientDerivedNormalizedCriticalFunction F)

    (tau_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F tauW S.tau)
    (tau_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F tauW tauData psiF)
    (upperLift : lattice K 0)
    (upper_mem :
      (C.u : K) * ((upper.delta : K) * (upperLift : K)) ∈ lattice K 1)
    (target : ResidueField F)
    (tauLift : lattice F 0)
    (tauLift_coe : (tauLift : F) =
      phaseReductionNormPolynomial F K
          ((C.u : K) * ((upper.delta : K) * (upperLift : K))) /
        (tauW.delta : F))
    (tau_reduce : reduce F (tauLift : F) tauLift.property = target) :
    ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau
      target
      (normUnits F K
        (wildQuadraticTwistedCriticalUnit C upper upperLift upper_mem)) := by
  refine .critical tauW rfl tau_pair tau_local tauLift tau_reduce ?_
  apply Units.ext
  rw [QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_coe,
    wildQuadratic_norm_twistedCriticalUnit_coe (F := F), tauLift_coe]
  field_simp [Units.ne_zero tauW.delta]

private noncomputable def wildQuadraticPreparation_wildQuadratic_upperTeichLift
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (z : ResidueField F) : lattice K 0 :=
  let zK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) (teichmuller F z)
  ⟨(zK : K), (mem_lattice_zero_iff K).2 zK.property⟩

@[simp] theorem wildQuadraticPreparation_wildQuadratic_upperTeichLift_coe
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (z : ResidueField F) :
    (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z : K) =
      algebraMap F K (teichmuller F z : F) := by
  rfl

private theorem wildQuadraticPreparation_wildQuadratic_upperTeichLift_reduce
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (z : ResidueField F) :
    reduce K (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z : K)
        (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z).property =
      wildQuadraticResidueEquiv F K C z := by
  unfold reduce wildQuadraticPreparation_wildQuadratic_upperTeichLift
  rw [wildQuadraticResidueEquiv_apply]
  change residueMap K
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)
        (teichmuller F z)) = extensionResidueMap F K z
  calc
    _ = extensionResidueMap F K (residueMap F (teichmuller F z)) :=
      (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation F) (ValuativeRel.valuation K)
          (teichmuller F z)).symm
    _ = _ := congrArg (extensionResidueMap F K)
      (residueMap_teichmuller F z)

private theorem wildQuadraticPreparation_stationaryUnitFactor_eq_one_of_representative
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (R : StationaryClassRepresentative E chi psi h gamma hgamma)
    (P : WildQuadraticStationaryPair E)
    (hP : P.ratio = (R.representative : E) / (gamma : E))
    (y : E) (hy : y ∈ lattice E ((d + epsilon : ℕ) : ℤ))
    (unit : Eˣ) (hunit : (unit : E) = 1 + y) :
    stationaryUnitFactor chi.character psi P unit = 1 := by
  have hraw := stationaryRawFactor_eq_one h gamma hgamma R y hy unit hunit
  unfold stationaryUnitFactor
  rw [hP]
  have hyEq : (unit : E) - 1 = y := by rw [hunit]; ring
  rw [hyEq]
  exact hraw

private theorem wildQuadraticPreparation_reduce_div_eq_zero_of_mem_succ
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)]
    (d : ℕ) (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (y : E) (hy : y ∈ lattice E ((d + 1 : ℕ) : ℤ)) :
    ∃ hdiv : y / (delta : E) ∈ lattice E 0,
      reduce E (y / (delta : E)) hdiv = 0 := by
  have hdiv0 : y / (delta : E) ∈ lattice E 0 :=
    (div_mem_lattice_iff E (delta : E) y (d : ℤ) 0 hdelta).2
      (lattice_antitone E (by omega) hy)
  have hdiv1 : y / (delta : E) ∈ lattice E 1 :=
    (div_mem_lattice_iff E (delta : E) y (d : ℤ) 1 hdelta).2
      (by simpa using hy)
  refine ⟨hdiv0, ?_⟩
  have hzero : (0 : E) ∈ lattice E 0 := zero_mem _
  have hreduce : reduce E (y / (delta : E)) hdiv0 = reduce E 0 hzero := by
    apply (reduce_eq_reduce_iff (F := E) hdiv0 hzero).2
    rw [congruentAtDepth_iff_sub_mem_lattice, sub_zero]
    exact hdiv1
  rw [hreduce]
  rfl

private theorem wildQuadraticPreparation_wildQuadraticHigh_twistedDisplacement_mem_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {t r v dK : ℕ} (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hdK : dK = v + r)
    (u deltaK : Kˣ)
    (hu : ord K (u : K) = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (lift : lattice K 0) :
    (u : K) * ((deltaK : K) * (lift : K)) ∈ lattice K 1 := by
  have hlift := lift.property
  rw [mem_lattice] at hlift
  rw [mem_lattice, ord_mul, ord_mul, hu, hdeltaK, hdK]
  have hrpos : 0 < r := by omega
  calc
    ((1 : ℤ) : WithTop ℤ) ≤ ((r : ℤ) : WithTop ℤ) := by
      exact_mod_cast hrpos
    _ = ((-(v : ℤ) : ℤ) : WithTop ℤ) +
          ((((v + r : ℕ) : ℤ) : WithTop ℤ) + 0) := by norm_num
    _ ≤ ((-(v : ℤ) : ℤ) : WithTop ℤ) +
          ((((v + r : ℕ) : ℤ) : WithTop ℤ) + ord K (lift : K)) :=
      by
        gcongr
        simpa using hlift

/-! In degree two the strict-high base polynomial has the exact branch depth
needed by the actual lower coordinate.  These replace the old odd-degree
lemmas, whose `Odd (finrank F K)` hypothesis cannot hold here. -/
private theorem wildQuadraticPreparation_wildQuadraticHigh_basePolynomial_deep_odd
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t r v d dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hv : 0 < v)
    (hm : 2 * d + 1 = (t + 1) + v) (hdK : dK = v + r)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    phaseReductionNormPolynomial F K
        ((deltaK : K) * algebraMap F K (teichmuller F z : F)) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  have hdiff : differentExponent F K = t + 1 :=
    differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen
  let zF : F := (teichmuller F z : F)
  let x : K := (deltaK : K) * algebraMap F K zF
  have hzF : (0 : WithTop ℤ) ≤ ord F zF :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  have hzK : (0 : WithTop ℤ) ≤ ord K (algebraMap F K zF) := by
    rw [ord_algebraMap, hram]
    exact nsmul_nonneg hzF 2
  have hx : x ∈ lattice K (dK : ℤ) := by
    rw [mem_lattice]
    dsimp only [x]
    rw [ord_mul, hdeltaK]
    simpa only [zero_add, add_comm] using
      add_le_add_left hzK (((dK : ℕ) : ℤ) : WithTop ℤ)
  have htrace0 := trace_mem_lattice_floor F K pi hpi hgen (dK : ℤ) hx
  rw [hdiff, hram] at htrace0
  have htrace : trace F K x ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    apply lattice_antitone F (n :=
      (((dK : ℤ) + ((t + 1 : ℕ) : ℤ)) / (2 : ℤ)))
    · omega
    · exact htrace0
  have hnorm0 : norm F K x ∈ lattice F (dK : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    simpa only [mem_lattice] using hx
  have hnorm : norm F K x ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    apply lattice_antitone F (n := (dK : ℤ))
    · omega
    · exact hnorm0
  rw [wildQuadratic_phaseReductionNormPolynomial_eq_trace_add_norm
    F K hdegree]
  exact add_mem_lattice F htrace hnorm

private theorem wildQuadraticPreparation_wildQuadraticHigh_basePolynomial_mem_even
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t r v d dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hv : 0 < v)
    (hm : 2 * d = (t + 1) + v) (hdK : dK = v + r)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    phaseReductionNormPolynomial F K
        ((deltaK : K) * algebraMap F K (teichmuller F z : F)) ∈
      lattice F (d : ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  have hdiff : differentExponent F K = t + 1 :=
    differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen
  let zF : F := (teichmuller F z : F)
  let x : K := (deltaK : K) * algebraMap F K zF
  have hzF : (0 : WithTop ℤ) ≤ ord F zF :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  have hzK : (0 : WithTop ℤ) ≤ ord K (algebraMap F K zF) := by
    rw [ord_algebraMap, hram]
    exact nsmul_nonneg hzF 2
  have hx : x ∈ lattice K (dK : ℤ) := by
    rw [mem_lattice]
    dsimp only [x]
    rw [ord_mul, hdeltaK]
    simpa only [zero_add, add_comm] using
      add_le_add_left hzK (((dK : ℕ) : ℤ) : WithTop ℤ)
  have htrace0 := trace_mem_lattice_floor F K pi hpi hgen (dK : ℤ) hx
  rw [hdiff, hram] at htrace0
  have htrace : trace F K x ∈ lattice F (d : ℤ) := by
    apply lattice_antitone F (n :=
      (((dK : ℤ) + ((t + 1 : ℕ) : ℤ)) / (2 : ℤ)))
    · omega
    · exact htrace0
  have hnorm0 : norm F K x ∈ lattice F (dK : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    simpa only [mem_lattice] using hx
  have hnorm : norm F K x ∈ lattice F (d : ℤ) := by
    apply lattice_antitone F (n := (dK : ℤ))
    · omega
    · exact hnorm0
  rw [wildQuadratic_phaseReductionNormPolynomial_eq_trace_add_norm
    F K hdegree]
  exact add_mem_lattice F htrace hnorm

private theorem wildQuadraticPreparation_wildQuadraticHigh_evenBase_factor
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t r v d dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hv : 0 < v)
    (hm : 2 * d = (t + 1) + v) (hdK : dK = v + r)
    (chiFData : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hF : IsStationaryConductorDecomposition chiFData.conductor d 0)
    (gamma : Fˣ)
    (hgamma : ord F (gamma : F) =
      (((chiFData.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (R : StationaryClassRepresentative F chiFData psiF hF gamma hgamma)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (hpair : S.chiF.ratio = (R.representative : F) / (gamma : F))
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (upper_delta : ord K (upper.delta : K) = ((dK : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    stationaryUnitFactor chiFData.character psiF S.chiF
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift upper
            (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z))) = 1 := by
  let lift := wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z
  let x : K := (upper.delta : K) * (lift : K)
  let y : F := phaseReductionNormPolynomial F K x
  have hy : y ∈ lattice F (d : ℤ) := by
    simpa only [y, x, lift, wildQuadraticPreparation_wildQuadratic_upperTeichLift_coe] using
      wildQuadraticPreparation_wildQuadraticHigh_basePolynomial_mem_even F K ht hres pi hpi
        hgen hdegree htpos hT hv hm hdK upper.delta upper_delta z
  let unit : Fˣ := normUnits F K
    (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift upper lift)
  have hunit : (unit : F) = 1 + y := by
    simpa only [unit, y, x] using
      wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper lift
  exact wildQuadraticPreparation_stationaryUnitFactor_eq_one_of_representative hF gamma hgamma
    R S.chiF hpair y (by simpa only [Nat.add_zero] using hy) unit hunit

private theorem wildQuadraticPreparation_wildQuadraticHigh_oddBase_coordinate
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t r v d dK : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (hT : t + 1 = 2 * r + 1) (hv : 0 < v)
    (hm : 2 * d + 1 = (t + 1) + v) (hdK : dK = v + r)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (chiFData : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (chiW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_delta : ord K (upper.delta : K) = ((dK : ℤ) : WithTop ℤ))
    (chi_delta : ord F (chiW.delta : F) = ((d : ℤ) : WithTop ℤ))
    (chi_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F chiW S.chiF)
    (chi_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F chiW chiFData psiF)
    (z : ResidueField F) :
    ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF 0
      (normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift upper
          (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z))) := by
  let lift := wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z
  let x : K := (upper.delta : K) * (lift : K)
  let y : F := phaseReductionNormPolynomial F K x
  have hy : y ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    simpa only [y, x, lift, wildQuadraticPreparation_wildQuadratic_upperTeichLift_coe] using
      wildQuadraticPreparation_wildQuadraticHigh_basePolynomial_deep_odd F K ht hres pi hpi
        hgen hdegree htpos hT hv hm hdK upper.delta upper_delta z
  obtain ⟨hdiv, hreduce⟩ :=
    wildQuadraticPreparation_reduce_div_eq_zero_of_mem_succ F d chiW.delta chi_delta y hy
  let unit : Fˣ := normUnits F K
    (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift upper lift)
  have hunit : (unit : F) = 1 + y := by
    simpa only [unit, y, x] using
      wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper lift
  exact wildQuadratic_actualLowerCritical_of_displacement chiW chiFData psiF
    S.chiF chi_pair chi_local 0 y hdiv hreduce unit hunit


/-! Primitive strict-high certificate constructors.  Their hypotheses are
exactly the field-level reductions left after normalizing the three actual
rows; no table-level function identity is assumed. -/
private theorem wildQuadraticPreparation_absoluteTraceChar_ringEquiv
    {k k' : Type} [Field k] [Fintype k] [CharP k 2]
    [Field k'] [Fintype k'] [CharP k' 2]
    (e : k ≃+* k') (x : k) :
    absoluteTraceChar k' (e x) = absoluteTraceChar k x := by
  letI : Algebra (ZMod 2) k := ZMod.algebra k 2
  letI : Algebra (ZMod 2) k' := ZMod.algebra k' 2
  let eAlg : k ≃ₐ[ZMod 2] k' :=
    AlgEquiv.ofRingEquiv (f := e) (by
      intro a
      have heq : e.toRingHom.comp (algebraMap (ZMod 2) k) =
          algebraMap (ZMod 2) k' := Subsingleton.elim _ _
      exact DFunLike.congr_fun heq a)
  simp only [absoluteTraceChar_apply]
  rw [show absoluteTraceTwo k' (e x) = absoluteTraceTwo k x by
    exact Algebra.trace_eq_of_algEquiv eAlg x]

/-! Pull back an upstairs normalized positive-polar function through a
residue-field equivalence. -/
private noncomputable def wildQuadraticPreparation_pullbackCriticalPolarFunction
    {k k' : Type} [Field k] [Fintype k] [CharP k 2]
    [Field k'] [Fintype k'] [CharP k' 2]
    (e : k ≃+* k')
    (upper : CriticalPolarFunction k' (absoluteTraceChar k') 1) :
    CriticalPolarFunction k (absoluteTraceChar k) 1 where
  toFun z := upper (e z)
  ne_zero' z := upper.ne_zero (e z)
  map_add' x y := by
    rw [map_add, upper.map_add]
    simpa only [one_mul, map_mul] using congrArg
      (fun c : ℂ ↦ upper (e x) * upper (e y) * c)
      (wildQuadraticPreparation_absoluteTraceChar_ringEquiv e (x * y))

@[simp] theorem wildQuadraticPreparation_pullbackCriticalPolarFunction_apply
    {k k' : Type} [Field k] [Fintype k] [CharP k 2]
    [Field k'] [Fintype k'] [CharP k' 2]
    (e : k ≃+* k')
    (upper : CriticalPolarFunction k' (absoluteTraceChar k') 1) (z : k) :
    wildQuadraticPreparation_pullbackCriticalPolarFunction e upper z = upper (e z) := rfl

private theorem wildQuadraticPreparation_high_normalized_scalar_eq_one_of_residueEquiv
    {k k' : Type} [Field k] [Fintype k] [CharP k 2]
    [Field k'] [Fintype k'] [CharP k' 2]
    (e : k ≃+* k')
    (upper : CriticalPolarFunction k' (absoluteTraceChar k') 1)
    (tau : CriticalPolarFunction k (absoluteTraceChar k) 1)
    (lambda : k)
    (htransport : ∀ z : k,
      upper (e z) = tau (lambda * z ^ 2) *
        absoluteTraceChar k (lambda * z ^ 2)) :
    lambda = 1 := by
  exact wildQuadraticPreparation_high_normalized_scalar_eq_one
    (wildQuadraticPreparation_pullbackCriticalPolarFunction e upper) tau lambda htransport

/-! The strict-high scalar gate derived directly from primitive coordinates.
The base factor is evaluated at zero, while the post-drop norm row is retained
at its actual scaled square.  No table transport theorem is used in the
hypotheses, so this can be applied before the final certificate exists. -/
private theorem wildQuadraticPreparation_wildQuadraticHigh_scalar_eq_one_of_coordinates
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
    (tau_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F tauW S.tau)
    (tau_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F tauW tauData psiF)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (lambda : ResidueField F)
    (upperLift : ResidueField F → lattice K 0)
    (upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z)
    (upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1)
    (base_factor : ∀ z,
      stationaryUnitFactor chiFData.character psiF S.chiF
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))) = 1)
    (tau_coordinate : ∀ z,
      ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau
        (lambda * z ^ 2)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z)))) :
    lambda = 1 := by
  apply wildQuadraticPreparation_high_normalized_scalar_eq_one_of_residueEquiv
    (wildQuadraticResidueEquiv F K C)
      upper.toCriticalPolarFunction tauW.toCriticalPolarFunction
  intro z
  let upperUnit : Kˣ :=
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift upper
      (upperLift z)
  let twistedUnit : Kˣ :=
    wildQuadraticTwistedCriticalUnit C upper (upperLift z) (upper_mem z)
  have hupperFactor :
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction K
          upper (wildQuadraticResidueEquiv F K C z) =
        stationaryUnitFactor upper.chi.character upper.psi S.chiK
          upperUnit := by
    rw [← upper_reduce z,
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce]
    exact
      QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
        upper S.chiK upper_pair (upperLift z)
  have hstationary := stationaryUnitFactor_compNorm_exact C S tau chiFData
    upper.chi psiF upper.psi upper_character upper_additive chiK_ratio
      chiF_ratio upperUnit twistedUnit
        ((upper.delta : K) * (upperLift z : K))
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_coe
          upper (upperLift z))
        (wildQuadraticTwistedCriticalUnit_coe C upper (upperLift z)
          (upper_mem z))
  have htauFactor :
      stationaryUnitFactor tau.1 psiF S.tau
          (normUnits F K twistedUnit) =
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F
          tauW (lambda * z ^ 2) := by
    rw [tau_character]
    simpa only [actualSourceFunction] using
      (tau_coordinate z).factor_eq_actualSourceFunction
  rw [hupperFactor, hstationary, base_factor z, one_mul, htauFactor]
  exact QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_inv
    tauW (lambda * z ^ 2)

/-! End-to-end strict-high even/odd certificate at odd `T`.  All normalizing
coordinates are those of the actual quotient rows; the natural tau scalar is
first retained, proved equal to one by the preceding non-circular gate, and
only then rewritten to the table coordinate `z²`. -/
private noncomputable def wildQuadraticPreparation_wildQuadratic_aboveMEvenTOdd_from_normalizedRows
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m r v dK : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (hT : t + 1 = 2 * r + 1) (hdK : dK = v + r)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hu : ord K (C.u : K) = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_delta : ord K (upper.delta : K) = ((dK : ℤ) : WithTop ℤ))
    (tau_delta : ord F (tauW.delta : F) = ((r : ℤ) : WithTop ℤ))
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
    (tau_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F tauW S.tau)
    (tau_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F tauW tauData psiF)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (base_factor : ∀ z,
      stationaryUnitFactor chiFData.character psiF S.chiF
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z))) = 1)
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q (.aboveMEvenTOdd tauW) S
      tauData chiFData psiF := by
  classical
  let upperLift : ResidueField F → lattice K 0 :=
    wildQuadraticPreparation_wildQuadratic_upperTeichLift F K
  have upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z := by
    exact wildQuadraticPreparation_wildQuadratic_upperTeichLift_reduce F K C
  have upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1 := by
    intro z
    exact wildQuadraticPreparation_wildQuadraticHigh_twistedDisplacement_mem_one K htpos hT
      hdK C.u upper.delta hu upper_delta (upperLift z)
  let hcoords :=
    wildQuadraticPreparation_wildQuadraticHigh_tauCoordinates F K ht hres pi hpi hgen hdegree
      htpos hT hdK C.u C.n C.norm_u hu upper.delta upper_delta tauW.delta
        tau_delta
  let scalar0 : unitGroup F := Classical.choose hcoords
  have hcoordsSpec := Classical.choose_spec hcoords
  have hscalar0 := hcoordsSpec.1
  have htauLifts := hcoordsSpec.2
  let lambda : ResidueField F :=
    ((residueUnits F scalar0 : (ResidueField F)ˣ) : ResidueField F)
  let tauLift (z : ResidueField F) : lattice F 0 :=
    Classical.choose (htauLifts z)
  have tauLift_coe (z : ResidueField F) :
      (tauLift z : F) =
        phaseReductionNormPolynomial F K
            ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
          (tauW.delta : F) := by
    simpa only [tauLift, upperLift,
      wildQuadraticPreparation_wildQuadratic_upperTeichLift_coe] using
        (Classical.choose_spec (htauLifts z)).1
  have tauLift_reduce (z : ResidueField F) :
      reduce F (tauLift z : F) (tauLift z).property = lambda * z ^ 2 := by
    exact (Classical.choose_spec (htauLifts z)).2
  have tau_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau
        (lambda * z ^ 2)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) :=
    wildQuadraticPreparation_wildQuadratic_actualTauCoordinate_of_lift F K C S tauData psiF
      upper tauW tau_pair tau_local (upperLift z) (upper_mem z)
        (lambda * z ^ 2) (tauLift z) (tauLift_coe z) (tauLift_reduce z)
  have hlambda : lambda = 1 :=
    wildQuadraticPreparation_wildQuadraticHigh_scalar_eq_one_of_coordinates F K C S tauData
      chiFData psiF upper tauW upper_pair upper_character upper_additive
        tau_pair tau_local tau tau_character chiK_ratio chiF_ratio lambda
          upperLift upper_reduce upper_mem (by simpa only [upperLift] using
            base_factor) tau_coordinate
  refine

    { upper := upper
      upper_pair := upper_pair
      upper_character := upper_character
      upper_additive := upper_additive
      tau := tau
      tau_character := tau_character
      chiK_ratio := chiK_ratio
      chiF_ratio := chiF_ratio
      point := fun z ↦ ?_ }
  have hchi : ActualLowerStationaryCoordinate F none chiFData psiF S.chiF 0
      (normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper (upperLift z))) :=
    .constant rfl (by simpa only [upperLift] using base_factor z)
  have htau : ActualLowerStationaryCoordinate F (some tauW) tauData psiF
      S.tau (z ^ 2)
      (normUnits F K
        (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
          (upper_mem z))) := by
    simpa only [hlambda, one_mul] using tau_coordinate z
  simpa only [WildQuadraticCoefficientInputs.toCoefficientData,
    WildQuadraticCoefficientData.aboveMEvenTOddComputed,
    WildQuadraticCoefficientData.commonScale,
    WildQuadraticCoefficientData.pTransport,
    WildQuadraticCoefficientData.qTransport,
    WildQuadraticCoefficientData.range,
    WildQuadraticCoefficientData.row,
    WildQuadraticCoefficientRow.range, inv_one, one_mul] using
    (ActualUpperCoordinatePoint.ofTwistedCriticalUnit C S
      (.aboveMEvenTOdd tauW) tauData chiFData psiF upper
        (wildQuadraticResidueEquiv F K C z) 0 (z ^ 2)
        (upperLift z) (upper_reduce z) (upper_mem z) hchi htau)

private noncomputable def wildQuadraticPreparation_wildQuadratic_aboveMOddTOdd_from_normalizedRows
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m r v dK : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (hT : t + 1 = 2 * r + 1) (hdK : dK = v + r)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hu : ord K (C.u : K) = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW chiW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_delta : ord K (upper.delta : K) = ((dK : ℤ) : WithTop ℤ))
    (tau_delta : ord F (tauW.delta : F) = ((r : ℤ) : WithTop ℤ))
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
    (tau_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F tauW S.tau)
    (tau_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F tauW tauData psiF)
    (chi_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F chiW S.chiF)
    (chi_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F chiW chiFData psiF)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (base_coordinate : ∀ z,
      ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF 0
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z))))
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q (.aboveMOddTOdd tauW chiW) S
      tauData chiFData psiF := by
  classical
  let upperLift : ResidueField F → lattice K 0 :=
    wildQuadraticPreparation_wildQuadratic_upperTeichLift F K
  have upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z := by
    exact wildQuadraticPreparation_wildQuadratic_upperTeichLift_reduce F K C
  have upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1 := by
    intro z
    exact wildQuadraticPreparation_wildQuadraticHigh_twistedDisplacement_mem_one K htpos hT
      hdK C.u upper.delta hu upper_delta (upperLift z)
  let hcoords :=
    wildQuadraticPreparation_wildQuadraticHigh_tauCoordinates F K ht hres pi hpi hgen hdegree
      htpos hT hdK C.u C.n C.norm_u hu upper.delta upper_delta tauW.delta
        tau_delta
  let scalar0 : unitGroup F := Classical.choose hcoords
  have hcoordsSpec := Classical.choose_spec hcoords
  have hscalar0 := hcoordsSpec.1
  have htauLifts := hcoordsSpec.2
  let lambda : ResidueField F :=
    ((residueUnits F scalar0 : (ResidueField F)ˣ) : ResidueField F)
  let tauLift (z : ResidueField F) : lattice F 0 :=
    Classical.choose (htauLifts z)
  have tauLift_coe (z : ResidueField F) :
      (tauLift z : F) =
        phaseReductionNormPolynomial F K
            ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
          (tauW.delta : F) := by
    simpa only [tauLift, upperLift,
      wildQuadraticPreparation_wildQuadratic_upperTeichLift_coe] using
        (Classical.choose_spec (htauLifts z)).1
  have tauLift_reduce (z : ResidueField F) :
      reduce F (tauLift z : F) (tauLift z).property = lambda * z ^ 2 := by
    exact (Classical.choose_spec (htauLifts z)).2
  have tau_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau
        (lambda * z ^ 2)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) :=
    wildQuadraticPreparation_wildQuadratic_actualTauCoordinate_of_lift F K C S tauData psiF
      upper tauW tau_pair tau_local (upperLift z) (upper_mem z)
        (lambda * z ^ 2) (tauLift z) (tauLift_coe z) (tauLift_reduce z)
  have base_factor (z : ResidueField F) :
      stationaryUnitFactor chiFData.character psiF S.chiF
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))) = 1 := by
    calc
      _ = actualSourceFunction F (some chiW) 0 :=
        (by simpa only [upperLift] using
          (base_coordinate z).factor_eq_actualSourceFunction)
      _ = 1 := by
        exact CriticalPolarFunction.map_zero chiW.toCriticalPolarFunction
  have hlambda : lambda = 1 :=
    wildQuadraticPreparation_wildQuadraticHigh_scalar_eq_one_of_coordinates F K C S tauData
      chiFData psiF upper tauW upper_pair upper_character upper_additive
        tau_pair tau_local tau tau_character chiK_ratio chiF_ratio lambda
          upperLift upper_reduce upper_mem base_factor tau_coordinate
  refine
    { upper := upper
      upper_pair := upper_pair
      upper_character := upper_character
      upper_additive := upper_additive
      tau := tau
      tau_character := tau_character
      chiK_ratio := chiK_ratio
      chiF_ratio := chiF_ratio
      point := fun z ↦ ?_ }
  have hchi : ActualLowerStationaryCoordinate F (some chiW) chiFData psiF
      S.chiF 0
      (normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper (upperLift z))) := by
    simpa only [upperLift] using base_coordinate z
  have htau : ActualLowerStationaryCoordinate F (some tauW) tauData psiF
      S.tau (z ^ 2)
      (normUnits F K
        (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
          (upper_mem z))) := by
    simpa only [hlambda, one_mul] using tau_coordinate z
  simpa only [WildQuadraticCoefficientInputs.toCoefficientData,
    WildQuadraticCoefficientData.aboveMOddTOddComputed,
    WildQuadraticCoefficientData.commonScale,
    WildQuadraticCoefficientData.pTransport,
    WildQuadraticCoefficientData.qTransport,
    WildQuadraticCoefficientData.range,
    WildQuadraticCoefficientData.row,
    WildQuadraticCoefficientRow.range, inv_one, one_mul] using
    (ActualUpperCoordinatePoint.ofTwistedCriticalUnit C S
      (.aboveMOddTOdd tauW chiW) tauData chiFData psiF upper
        (wildQuadraticResidueEquiv F K C z) 0 (z ^ 2)
        (upperLift z) (upper_reduce z) (upper_mem z) hchi htau)

section StrictHighProductCallback

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ}
  {V : WildQuadraticCommonCoefficientView F K t m}
  {data : FirstMainComputationalData F K V.chiFData.character
    V.psiF.character}
  {phaseData : FirstMainPhaseData F K V.chiFData.character
    V.psiF.character data}
  {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character
    V.psiF.character data phaseData (t := t) (m := m)}
  {rows : WildQuadraticActualPhaseRows V data phaseData assembly}

/-- Strict-high callback in the exact shape expected by the continuation
assembler.  Only the two product-bearing strict-high rows reach the producer. -/
private noncomputable def wildQuadraticPreparation_strictHighProductCallback
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (hstrict : t + 1 < m)
    (htauConductor : V.tauData.conductor = t + 1)
    (htwistConductor :
      (data.twistData assembly.indexing.tau).conductor = max m (t + 1)) :
    ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF =
          some lambda →
        ∃ C : ActualProductCoordinateCertificate F K q V.criticalInputs
            V.stationaryPairs V.tauData V.chiFData V.psiF,
          rows.twist.criticalFactor =
            QuotientDerivedNormalizedCriticalFunction.phase F C.product := by
  have hbaseConductor : V.chiFData.conductor = m := by
    calc
      V.chiFData.conductor = (data.twistData 1).conductor := by
        rw [coordinates.baseData_eq]
      _ = assembly.baseData.conductor := by rw [assembly.baseData_eq]
      _ = m := assembly.baseConductor
  have hviewRange : V.criticalInputs.row.range = .above := by
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_range_above (by omega)]
  have hnotBelow : V.criticalInputs.row.range ≠ .below := by
    rw [hviewRange]
    decide
  have hnotBoundary : V.criticalInputs.row.range ≠ .boundary := by
    rw [hviewRange]
    decide
  have buildAbove : ∀
      (chiF : QuotientDerivedNormalizedCriticalFunction F),
      V.criticalInputs.chiFSource = some chiF →
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F chiF
        V.stationaryPairs.chiF →
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F chiF
        V.chiFData V.psiF →
      ∀ q : CharTwoRefinement (ResidueField F),
      (V.criticalInputs.toCoefficientData q).range = .above →
      ∃ C : ActualProductCoordinateCertificate F K q V.criticalInputs
          V.stationaryPairs V.tauData V.chiFData V.psiF,
        rows.twist.criticalFactor =
          QuotientDerivedNormalizedCriticalFunction.phase F C.product := by
    intro chiF hsource hpair hlocal q hrange
    have hsourceConductor : chiF.chi.conductor = m := by
      calc
        chiF.chi.conductor = V.chiFData.conductor :=
          congrArg LocalQuasiCharData.conductor hlocal.1
        _ = m := hbaseConductor
    have htwistOdd :
        Odd (data.twistData assembly.indexing.tau).conductor := by
      rw [htwistConductor, max_eq_left hstrict.le, ← hsourceConductor,
        chiF.conductor_eq]
      exact ⟨chiF.d, by omega⟩
    obtain ⟨product, productLocal, productPair, _productPhase⟩ :=
      rows.twist.exists_normalizedQuotientDerivedCriticalFunction htwistOdd
    have hproductConductor : product.chi.conductor = m := by
      calc
        product.chi.conductor =
            (data.twistData assembly.indexing.tau).conductor :=
          congrArg LocalQuasiCharData.conductor productLocal.1
        _ = max m (t + 1) := htwistConductor
        _ = m := max_eq_left hstrict.le
    have hsameConductor : chiF.chi.conductor = product.chi.conductor :=
      hsourceConductor.trans hproductConductor.symm
    have hlower : V.tauData.conductor < product.chi.conductor := by
      rw [htauConductor, hproductConductor]
      exact hstrict
    let cert := wildQuadraticPreparation_strictAboveProductCertificate
      coordinates q product chiF productLocal productPair hsource hpair hlocal
        hrange hstrict hsameConductor hlower
    exact ⟨cert.1, cert.2⟩
  intro q lambda haff
  generalize hI : V.criticalInputs = I at haff ⊢
  cases I with
  | belowMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMEvenTOdd tau =>
      exact (hnotBelow (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim
  | belowMOddTEven chiF =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.belowMOddTEvenComputed,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMOddTOdd tau chiF =>
      exact (hnotBelow (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim
  | boundaryEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | boundaryOdd rho hrho hden tau chiF =>
      exact (hnotBoundary (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim
  | aboveMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMEvenTOdd tau =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.aboveMEvenTOddComputed,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMOddTEven chiF =>
      have hpairs := V.criticalInputs_stationaryPairs
      rw [hI] at hpairs
      have hlocal := V.criticalInputs_localData
      rw [hI] at hlocal
      have result := buildAbove chiF
        (by simp only [hI, WildQuadraticCoefficientInputs.chiFSource])
        hpairs hlocal q (by simp only [hI,
          WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.range,
          WildQuadraticCoefficientData.row,
          WildQuadraticCoefficientRow.range])
      rw [hI] at result
      exact result
  | aboveMOddTOdd tau chiF =>
      have hpairs := V.criticalInputs_stationaryPairs
      rw [hI] at hpairs
      have hlocal := V.criticalInputs_localData
      rw [hI] at hlocal
      have result := buildAbove chiF
        (by simp only [hI, WildQuadraticCoefficientInputs.chiFSource])
        hpairs.2 hlocal.2 q (by simp only [hI,
          WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.aboveMOddTOddComputed,
          WildQuadraticCoefficientData.range,
          WildQuadraticCoefficientData.row,
          WildQuadraticCoefficientRow.range])
      rw [hI] at result
      exact result

end StrictHighProductCallback


namespace WildQuadraticHighParameterData

set_option maxHeartbeats 4000000 in
/-- Transport the original simultaneous strict-high parameter choice to the
q-polymorphic upper-coordinate certificate.  The receiver is the original
parameter package selected by the high product table, never its proof-index
transport used to construct the phase rows. -/
noncomputable def coordinateTransport
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (D : WildQuadraticHighParameterData F K ht hres pi hpi hgen hdegree
      htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
        gammaF hgammaF)
    (hstrict : t + 1 < chiF.conductor)
    (V : WildQuadraticCommonCoefficientView F K t chiF.conductor)
    (hcorrection : V.correction =
      highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree htpos
        chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
          gammaF hgammaF D)
    (hpairs : V.stationaryPairs =
      highWildQuadraticSelectedStationaryPairs D.representatives)
    (htauData : V.tauData =
      wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau)
    (hchiData : V.chiFData = chiF)
    (hpsiData : V.psiF = psiF)
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {phaseData : FirstMainPhaseData F K V.chiFData.character
      V.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data phaseData
        (t := t) (m := chiF.conductor)}
    (rows : WildQuadraticActualPhaseRows V data phaseData assembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly) :
    WildQuadraticPositivePolarCoordinateTransport F K V rows := by
  classical
  let C := highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree
    htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
      gammaF hgammaF D
  have hcorrectionC : V.correction = C := by
    simpa only [C] using hcorrection
  let extension := rows.extension
  let base := rows.base
  have hExtension :
      phaseData.extension = LocalPhaseData.stationary extension :=
    rows.extension_eq
  have extensionPair :
      extension.selectedStationaryPair = V.stationaryPairs.chiK :=
    rows.extension_pair
  have basePair :
      base.selectedStationaryPair = V.stationaryPairs.chiF :=
    rows.base_pair
  have hbase : data.twistData 1 = chiF :=
    coordinates.baseData_eq.trans hchiData
  have hadd : psiF = data.baseAddChar :=
    (coordinates.baseAddData_eq.trans hpsiData).symm
  have hmindata : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1) := by
    rw [hbase]
    exact hminimal
  have hExtensionChi : data.extensionQuasiChar = chiK := by
    apply LocalQuasiCharData.ext_character K
    rw [data.extensionQuasiChar_character, hchiData]
    exact hchi.symm
  have hExtensionPsi : data.extensionAddChar = psiK := by
    apply LocalAddCharData.ext_character
    rw [data.extensionAddChar_character, hpsiData]
    exact hpsi.symm
  let v := wildQuadraticHighShift t chiF.conductor
  let r := wildQuadraticHighNormPrecision t
  let dK := chiK.conductor / 2
  have hconductorRelation :
      chiK.conductor + (t + 1) = 2 * chiF.conductor :=
    highParameter_wildQuadratic_conductor_relation F K ht hres pi hpi hgen
      hdegree chiF chiK hminimal hchi hhigh
  have hdepth := wildQuadraticHigh_depth_relations htpos hhigh hF hK
    hconductorRelation
  have hdK : dK = v + r := by
    have hKconductor := hK.conductor_eq
    have hepsilonK := hK.epsilon_le_one
    have hdepthK := hdepth.1
    dsimp only [dK, v, r]
    omega
  have hepsilonK :
      chiK.conductor % 2 = (t + 1) % 2 := by
    have hKconductor := hK.conductor_eq
    have hepsilonK := hK.epsilon_le_one
    have hdepthParity := hdepth.2.1
    omega
  have hu : ord K (C.u : K) =
      ((-(v : ℤ) : ℤ) : WithTop ℤ) := by
    rw [C.source_order]
    simp only [v, wildQuadraticHighShift]
    congr 1
    omega
  have htauConductor : V.tauData.conductor = t + 1 := by
    rw [htauData]
    rw [wildQuadraticHighTauData, quasiCharDataOfIsConductor_conductor]
  have htauCharacter : tau.1 = V.tauData.character := by
    rw [htauData]
    rw [wildQuadraticHighTauData, quasiCharDataOfIsConductor_character]
  have hAboveEven : ∀
      (tauW : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .aboveMEvenTOdd tauW)
      (q : CharTwoRefinement (ResidueField F)),
      Nonempty (ActualUpperCoordinateCertificate F K V.correction q
        V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF) := by
    intro tauW hI q
    have hrowI := V.criticalInputs_row
    rw [hI] at hrowI
    have hTParity0 := congrArg WildQuadraticCoefficientRow.TParity hrowI
    rw [WildQuadraticCoefficientRow.ofConductors_TParity] at hTParity0
    have hTParity :
        WildQuadraticConductorParity.ofConductor (t + 1) = .odd := by
      simpa only [WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.TParity] using hTParity0.symm
    have hTOdd : Odd (t + 1) :=
      (WildQuadraticConductorParity.ofConductor_eq_odd_iff (t + 1)).mp
        hTParity
    have hT : t + 1 = 2 * r + 1 := by
      simpa only [r, wildQuadraticHighNormPrecision] using
        (Nat.two_mul_div_two_add_one_of_odd hTOdd).symm
    have hmPred : chiF.conductor - 1 + 1 = chiF.conductor := by omega
    have hmParity0 := congrArg WildQuadraticCoefficientRow.mParity hrowI
    rw [WildQuadraticCoefficientRow.ofConductors_mParity] at hmParity0
    rw [hmPred] at hmParity0
    have hmParity :
        WildQuadraticConductorParity.ofConductor chiF.conductor = .even := by
      simpa only [WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.mParity] using hmParity0.symm
    have hmEven : Even chiF.conductor :=
      (WildQuadraticConductorParity.ofConductor_eq_even_iff
        chiF.conductor).mp hmParity
    have hTmod : (t + 1) % 2 = 1 := by omega
    have hKmod : chiK.conductor % 2 = 1 := hepsilonK.trans hTmod
    have hKOdd : Odd chiK.conductor := by
      apply Nat.not_even_iff_odd.mp
      intro hEven
      obtain ⟨j, hj⟩ := hEven
      omega
    obtain ⟨upper, upperLocal, upperPair0, _upperPhase⟩ :=
      extension.exists_normalizedQuotientDerivedCriticalFunction
        (by simpa only [extension, hExtensionChi] using hKOdd)
    have upperPair :
        QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair K
          upper V.stationaryPairs.chiK := by
      rw [← extensionPair]
      exact upperPair0
    have upperCharacter :
        upper.chi.character = V.chiFData.character.compNorm := by
      rw [upperLocal.1]
      exact data.extensionQuasiChar_character
    have upperAdditive :
        upper.psi.character = V.psiF.character.compTrace := by
      rw [upperLocal.2]
      exact data.extensionAddChar_character
    have upperDepth : upper.d = dK := by
      have hc := upper.conductor_eq
      have hl := congrArg LocalQuasiCharData.conductor upperLocal.1
      rw [hExtensionChi] at hl
      have hk := hK.conductor_eq
      dsimp only [dK]
      omega
    have upperDelta : ord K (upper.delta : K) =
        ((dK : ℤ) : WithTop ℤ) := by
      rw [upper.delta_order, upperDepth]
    have tauPairI := V.criticalInputs_stationaryPairs
    rw [hI] at tauPairI
    have tauLocalI := V.criticalInputs_localData
    rw [hI] at tauLocalI
    have tauDepth : tauW.d = r := by
      have hc := tauW.conductor_eq
      have hl := congrArg LocalQuasiCharData.conductor tauLocalI.1
      rw [htauConductor] at hl
      omega
    have tauDelta : ord F (tauW.delta : F) =
        ((r : ℤ) : WithTop ℤ) := by
      rw [tauW.delta_order, tauDepth]
    have hmDepth : 2 * (chiF.conductor / 2) = (t + 1) + v := by
      calc
        2 * (chiF.conductor / 2) = chiF.conductor :=
          Nat.two_mul_div_two_of_even hmEven
        _ = (t + 1) + v := by
          simpa only [v, wildQuadraticHighShift] using
            (Nat.add_sub_of_le hstrict.le).symm
    have baseFactor : ∀ z : ResidueField F,
        stationaryUnitFactor V.chiFData.character V.psiF
          V.stationaryPairs.chiF
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper
                (wildQuadraticPreparation_wildQuadratic_upperTeichLift
                  F K z))) = 1 := by
      intro z
      let upperLift :=
        wildQuadraticPreparation_wildQuadratic_upperTeichLift F K z
      let y := phaseReductionNormPolynomial F K
        ((upper.delta : K) * (upperLift : K))
      have hy : y ∈ lattice F ((chiF.conductor / 2 : ℕ) : ℤ) := by
        simpa only [y, upperLift,
          wildQuadraticPreparation_wildQuadratic_upperTeichLift_coe] using
          wildQuadraticPreparation_wildQuadraticHigh_basePolynomial_mem_even
            F K ht hres pi hpi hgen hdegree htpos hT (by
              simp only [v, wildQuadraticHighShift]
              omega) hmDepth hdK upper.delta upperDelta z
      have hyData :
          y ∈ lattice F (((data.twistData 1).conductor / 2 : ℕ) : ℤ) := by
        rwa [hbase]
      let unit : Fˣ := normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper upperLift)
      have hunit : (unit : F) = 1 + y := by
        simpa only [unit, y] using
          wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper upperLift
      have hbaseEven : Even (data.twistData 1).conductor := by
        rw [hbase]
        exact hmEven
      have hfactor :=
        wildQuadraticPreparation_evenRow_stationaryUnitFactor_eq_one base
          hbaseEven V.stationaryPairs.chiF basePair y hyData unit hunit
      simpa only [unit, hbase, ← hadd, hchiData, hpsiData] using hfactor
    have cert : ActualUpperCoordinateCertificate F K C q
        (.aboveMEvenTOdd tauW) V.stationaryPairs V.tauData V.chiFData
          V.psiF :=
      wildQuadraticPreparation_wildQuadratic_aboveMEvenTOdd_from_normalizedRows
        F K ht htpos hres pi hpi hgen hdegree hT hdK C hu
          V.stationaryPairs V.tauData V.chiFData V.psiF upper tauW
            upperDelta tauDelta upperPair upperCharacter upperAdditive
              tauPairI tauLocalI tau htauCharacter
                (by simpa only [← hcorrectionC] using V.chiK_ratio)
                (by simpa only [← hcorrectionC] using V.chiF_ratio)
                  baseFactor q
    rw [hcorrection, hI]
    exact ⟨cert⟩
  have hAboveOdd : ∀
      (tauW chiW : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .aboveMOddTOdd tauW chiW)
      (q : CharTwoRefinement (ResidueField F)),
      Nonempty (ActualUpperCoordinateCertificate F K V.correction q
        V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF) := by
    intro tauW chiW hI q
    have hrowI := V.criticalInputs_row
    rw [hI] at hrowI
    have hTParity0 := congrArg WildQuadraticCoefficientRow.TParity hrowI
    rw [WildQuadraticCoefficientRow.ofConductors_TParity] at hTParity0
    have hTParity :
        WildQuadraticConductorParity.ofConductor (t + 1) = .odd := by
      simpa only [WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.TParity] using hTParity0.symm
    have hTOdd : Odd (t + 1) :=
      (WildQuadraticConductorParity.ofConductor_eq_odd_iff (t + 1)).mp
        hTParity
    have hT : t + 1 = 2 * r + 1 := by
      simpa only [r, wildQuadraticHighNormPrecision] using
        (Nat.two_mul_div_two_add_one_of_odd hTOdd).symm
    have hmPred : chiF.conductor - 1 + 1 = chiF.conductor := by omega
    have hmParity0 := congrArg WildQuadraticCoefficientRow.mParity hrowI
    rw [WildQuadraticCoefficientRow.ofConductors_mParity] at hmParity0
    rw [hmPred] at hmParity0
    have hmParity :
        WildQuadraticConductorParity.ofConductor chiF.conductor = .odd := by
      simpa only [WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.mParity] using hmParity0.symm
    have hmOdd : Odd chiF.conductor :=
      (WildQuadraticConductorParity.ofConductor_eq_odd_iff
        chiF.conductor).mp hmParity
    have hTmod : (t + 1) % 2 = 1 := by omega
    have hKmod : chiK.conductor % 2 = 1 := hepsilonK.trans hTmod
    have hKOdd : Odd chiK.conductor := by
      apply Nat.not_even_iff_odd.mp
      intro hEven
      obtain ⟨j, hj⟩ := hEven
      omega
    obtain ⟨upper, upperLocal, upperPair0, _upperPhase⟩ :=
      extension.exists_normalizedQuotientDerivedCriticalFunction
        (by simpa only [extension, hExtensionChi] using hKOdd)
    have upperPair :
        QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair K
          upper V.stationaryPairs.chiK := by
      rw [← extensionPair]
      exact upperPair0
    have upperCharacter :
        upper.chi.character = V.chiFData.character.compNorm := by
      rw [upperLocal.1]
      exact data.extensionQuasiChar_character
    have upperAdditive :
        upper.psi.character = V.psiF.character.compTrace := by
      rw [upperLocal.2]
      exact data.extensionAddChar_character
    have upperDepth : upper.d = dK := by
      have hc := upper.conductor_eq
      have hl := congrArg LocalQuasiCharData.conductor upperLocal.1
      rw [hExtensionChi] at hl
      have hk := hK.conductor_eq
      dsimp only [dK]
      omega
    have upperDelta : ord K (upper.delta : K) =
        ((dK : ℤ) : WithTop ℤ) := by
      rw [upper.delta_order, upperDepth]
    have pairsI := V.criticalInputs_stationaryPairs
    rw [hI] at pairsI
    have localI := V.criticalInputs_localData
    rw [hI] at localI
    have tauDepth : tauW.d = r := by
      have hc := tauW.conductor_eq
      have hl := congrArg LocalQuasiCharData.conductor localI.1.1
      rw [htauConductor] at hl
      omega
    have tauDelta : ord F (tauW.delta : F) =
        ((r : ℤ) : WithTop ℤ) := by
      rw [tauW.delta_order, tauDepth]
    have hmDepth :
        2 * (chiF.conductor / 2) + 1 = (t + 1) + v := by
      calc
        2 * (chiF.conductor / 2) + 1 = chiF.conductor :=
          Nat.two_mul_div_two_add_one_of_odd hmOdd
        _ = (t + 1) + v := by
          simpa only [v, wildQuadraticHighShift] using
            (Nat.add_sub_of_le hstrict.le).symm
    have chiDepth : chiW.d = chiF.conductor / 2 := by
      have hc := chiW.conductor_eq
      have hl := congrArg LocalQuasiCharData.conductor localI.2.1
      rw [hchiData] at hl
      have hoddDepth := Nat.two_mul_div_two_add_one_of_odd hmOdd
      have heq : 2 * chiW.d + 1 =
          2 * (chiF.conductor / 2) + 1 := by
        calc
          2 * chiW.d + 1 = chiW.chi.conductor := hc.symm
          _ = chiF.conductor := hl
          _ = 2 * (chiF.conductor / 2) + 1 := hoddDepth.symm
      exact Nat.mul_left_cancel (by omega : 0 < 2)
        (Nat.add_right_cancel heq)
    have chiDelta : ord F (chiW.delta : F) =
        (((chiF.conductor / 2 : ℕ) : ℤ) : WithTop ℤ) := by
      rw [chiW.delta_order, chiDepth]
    have baseCoordinate : ∀ z : ResidueField F,
        ActualLowerStationaryCoordinate F (some chiW) V.chiFData V.psiF
          V.stationaryPairs.chiF 0
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper
                (wildQuadraticPreparation_wildQuadratic_upperTeichLift
                  F K z))) := by
      intro z
      exact
        wildQuadraticPreparation_wildQuadraticHigh_oddBase_coordinate
          F K ht hres pi hpi hgen hdegree htpos hT (by
            simp only [v, wildQuadraticHighShift]
            omega) hmDepth hdK V.stationaryPairs V.chiFData V.psiF
              upper chiW upperDelta chiDelta pairsI.2 localI.2 z
    have cert : ActualUpperCoordinateCertificate F K C q
        (.aboveMOddTOdd tauW chiW) V.stationaryPairs V.tauData
          V.chiFData V.psiF :=
      wildQuadraticPreparation_wildQuadratic_aboveMOddTOdd_from_normalizedRows
        F K ht htpos hres pi hpi hgen hdegree hT hdK C hu
          V.stationaryPairs V.tauData V.chiFData V.psiF upper tauW chiW
            upperDelta tauDelta upperPair upperCharacter upperAdditive
              pairsI.1 localI.1 pairsI.2 localI.2 tau htauCharacter
                (by simpa only [← hcorrectionC] using V.chiK_ratio)
                (by simpa only [← hcorrectionC] using V.chiF_ratio)
                  baseCoordinate q
    rw [hcorrection, hI]
    exact ⟨cert⟩
  have hupper : ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (V.criticalInputs.toCoefficientData q).affineCoefficient .chiK =
          some lambda →
        ∃ C0 : ActualUpperCoordinateCertificate F K V.correction q
            V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF,
          rows.extension.criticalFactor =
            QuotientDerivedNormalizedCriticalFunction.phase K C0.upper := by
    intro q lambda haff
    obtain ⟨C0⟩ :=
      wildQuadraticHigh_upperCoordinates_of_consumers F K V hstrict
        hAboveEven hAboveOdd q haff
    exact ⟨C0, wildQuadraticPreparation_upperCertificate_rowPhase C0⟩
  have hinputAbove : V.criticalInputs.row.range = .above := by
    have habove : t < chiF.conductor - 1 := by
      have hstrict := hstrict
      omega
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_range_above habove]
  have hTParityOfRow :
      V.criticalInputs.row.TParity =
        WildQuadraticConductorParity.ofConductor (t + 1) := by
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_TParity]
  have hmPred : chiF.conductor - 1 + 1 = chiF.conductor := by omega
  have hmParityOfRow :
      V.criticalInputs.row.mParity =
        WildQuadraticConductorParity.ofConductor chiF.conductor := by
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_mParity, hmPred]
  have hrowsExtension : rows.extension = extension := by
    apply LocalPhaseData.stationary.inj
    exact rows.extension_eq.symm.trans hExtension
  have hExtensionEven (hTEven : Even (t + 1)) :
      rows.extension.criticalFactor = 1 := by
    have hTmod : (t + 1) % 2 = 0 := by
      obtain ⟨j, hj⟩ := hTEven
      omega
    have hKmod : chiK.conductor % 2 = 0 := hepsilonK.trans hTmod
    have hKEven : Even chiK.conductor := by
      refine ⟨chiK.conductor / 2, ?_⟩
      have hk := hK.conductor_eq
      omega
    rw [hrowsExtension]
    exact extension.criticalFactor_eq_one_of_isEven
      (wildQuadraticHigh_isEven_of_even_conductor extension
        (by simpa only [extension, hExtensionChi] using hKEven))
  have hTauEvenPhase (hTEven : Even (t + 1)) :
      rows.tau.criticalFactor = quotientSourcePhase F none := by
    have hEven : Even
        (data.normCharacterData assembly.indexing.tau).conductor := by
      rw [coordinates.tauData_eq, htauConductor]
      exact hTEven
    simpa only [quotientSourcePhase] using
      rows.tau.criticalFactor_eq_one_of_isEven
        (wildQuadraticHigh_isEven_of_even_conductor rows.tau hEven)
  have hBaseEvenPhase (hmEven : Even chiF.conductor) :
      rows.base.criticalFactor = quotientSourcePhase F none := by
    have hEven : Even (data.twistData 1).conductor := by
      rw [coordinates.baseData_eq, hchiData]
      exact hmEven
    simpa only [quotientSourcePhase] using
      rows.base.criticalFactor_eq_one_of_isEven
        (wildQuadraticHigh_isEven_of_even_conductor rows.base hEven)
  have hmatch : ∀ q : CharTwoRefinement (ResidueField F),
      WildQuadraticCoefficientData.MatchesCorrection F K V.correction
        (V.criticalInputs.toCoefficientData q) := by
    apply wildQuadratic_matchesCorrection_of_boundary_source F K V
    intro rho hrho hden tauW chiW hI
    have hbad := hinputAbove
    rw [hI] at hbad
    simp only [WildQuadraticCoefficientInputs.row,
      WildQuadraticCoefficientRow.range] at hbad
    cases hbad
  have hupperNone : ∀ q : CharTwoRefinement (ResidueField F),
      (V.criticalInputs.toCoefficientData q).affineCoefficient .chiK = none →
        rows.extension.criticalFactor = 1 := by
    intro q hnone
    cases hI : V.criticalInputs with
    | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven | belowMOddTOdd |
        boundaryEven | boundaryOdd =>
        have hbad := hinputAbove
        rw [hI] at hbad
        simp only [WildQuadraticCoefficientInputs.row,
          WildQuadraticCoefficientRow.range] at hbad
        cases hbad
    | aboveMEvenTEven =>
        have hp := hTParityOfRow
        rw [hI] at hp
        have hTEven :
            Even (t + 1) :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            (t + 1)).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.TParity] using hp.symm)
        exact hExtensionEven hTEven
    | aboveMEvenTOdd tauW =>
        rw [hI] at hnone
        simp [WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.aboveMEvenTOddComputed,
          WildQuadraticCoefficientData.affineCoefficient] at hnone
    | aboveMOddTEven chiW =>
        have hp := hTParityOfRow
        rw [hI] at hp
        have hTEven :
            Even (t + 1) :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            (t + 1)).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.TParity] using hp.symm)
        exact hExtensionEven hTEven
    | aboveMOddTOdd tauW chiW =>
        rw [hI] at hnone
        simp [WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.aboveMOddTOddComputed,
          WildQuadraticCoefficientData.affineCoefficient] at hnone
  exact
    { matchesCorrection := hmatch
      upperCoordinates := by
        intro q lambda haff
        obtain ⟨C0, _hphase⟩ := hupper q haff
        exact ⟨C0⟩
      extension_phase := by
        intro q
        cases haff :
            (V.criticalInputs.toCoefficientData q).affineCoefficient .chiK with
        | none =>
            rw [WildQuadraticCoefficientData.phaseFactor, haff]
            exact hupperNone q haff
        | some lambda =>
            obtain ⟨C0, hphase⟩ := hupper q haff
            exact hphase.trans (C0.phase_eq_table haff) }

end WildQuadraticHighParameterData


/-- Complete a strict-high coordinate transport with the actual product row
and the retained tau/base source phases.  The result remains polymorphic in
the later quadratic refinement. -/
noncomputable def wildQuadraticHighContinuationFromCoordinate
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ}
    {V : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {phaseData : FirstMainPhaseData F K V.chiFData.character
      V.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows V data phaseData assembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (hstrict : t + 1 < m)
    (htauConductor : V.tauData.conductor = t + 1)
    (htwistConductor :
      (data.twistData assembly.indexing.tau).conductor = max m (t + 1))
    (coordinate : WildQuadraticPositivePolarCoordinateTransport F K V rows) :
    ∀ source : V.criticalInputs.PositivePolarSource,
      WildQuadraticPositivePolarContinuation F K V source rows := by
  intro source
  have hbaseConductor : V.chiFData.conductor = m := by
    calc
      V.chiFData.conductor = (data.twistData 1).conductor := by
        rw [coordinates.baseData_eq]
      _ = assembly.baseData.conductor := by rw [assembly.baseData_eq]
      _ = m := assembly.baseConductor
  have hinputAbove : V.criticalInputs.row.range = .above := by
    have habove : t < m - 1 := by
      have hstrict := hstrict
      omega
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_range_above habove]
  have hTParityOfRow :
      V.criticalInputs.row.TParity =
        WildQuadraticConductorParity.ofConductor (t + 1) := by
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_TParity]
  have hmPred : m - 1 + 1 = m := by omega
  have hmParityOfRow :
      V.criticalInputs.row.mParity =
        WildQuadraticConductorParity.ofConductor m := by
    rw [V.criticalInputs_row,
      WildQuadraticCoefficientRow.ofConductors_mParity, hmPred]
  have hTauEvenPhase (hTEven : Even (t + 1)) :
      rows.tau.criticalFactor = quotientSourcePhase F none := by
    have hEven : Even
        (data.normCharacterData assembly.indexing.tau).conductor := by
      rw [coordinates.tauData_eq, htauConductor]
      exact hTEven
    simpa only [quotientSourcePhase] using
      rows.tau.criticalFactor_eq_one_of_isEven
        (wildQuadraticHigh_isEven_of_even_conductor rows.tau hEven)
  have hBaseEvenPhase (hmEven : Even m) :
      rows.base.criticalFactor = quotientSourcePhase F none := by
    have hEven : Even (data.twistData 1).conductor := by
      rw [coordinates.baseData_eq, hbaseConductor]
      exact hmEven
    simpa only [quotientSourcePhase] using
      rows.base.criticalFactor_eq_one_of_isEven
        (wildQuadraticHigh_isEven_of_even_conductor rows.base hEven)
  have hproduct : ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF =
          some lambda →
        ∃ C0 : ActualProductCoordinateCertificate F K q V.criticalInputs
            V.stationaryPairs V.tauData V.chiFData V.psiF,
          rows.twist.criticalFactor =
            QuotientDerivedNormalizedCriticalFunction.phase F C0.product :=
    wildQuadraticPreparation_strictHighProductCallback coordinates hstrict
      htauConductor htwistConductor
  have hTwistEven (hmEven : Even m) :
      rows.twist.criticalFactor = 1 := by
    have hEven : Even (data.twistData assembly.indexing.tau).conductor := by
      rw [htwistConductor, max_eq_left hstrict.le]
      exact hmEven
    exact rows.twist.criticalFactor_eq_one_of_isEven
      (wildQuadraticHigh_isEven_of_even_conductor rows.twist hEven)
  have hproductNone : ∀ q : CharTwoRefinement (ResidueField F),
      (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF = none →
        rows.twist.criticalFactor = 1 := by
    intro q hnone
    cases hI : V.criticalInputs with
    | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven | belowMOddTOdd |
        boundaryEven | boundaryOdd =>
        have hbad := hinputAbove
        rw [hI] at hbad
        simp only [WildQuadraticCoefficientInputs.row,
          WildQuadraticCoefficientRow.range] at hbad
        cases hbad
    | aboveMEvenTEven =>
        have hp := hmParityOfRow
        rw [hI] at hp
        have hmEven : Even m :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            m).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.mParity] using hp.symm)
        exact hTwistEven hmEven
    | aboveMEvenTOdd tauW =>
        have hp := hmParityOfRow
        rw [hI] at hp
        have hmEven : Even m :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            m).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.mParity] using hp.symm)
        exact hTwistEven hmEven
    | aboveMOddTEven chiW =>
        rw [hI] at hnone
        simp [WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.affineCoefficient] at hnone
    | aboveMOddTOdd tauW chiW =>
        rw [hI] at hnone
        simp [WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.aboveMOddTOddComputed,
          WildQuadraticCoefficientData.affineCoefficient] at hnone
  have hsourcePhases :
      rows.tau.criticalFactor =
          quotientSourcePhase F V.criticalInputs.tauSource ∧
        rows.base.criticalFactor =
          quotientSourcePhase F V.criticalInputs.chiFSource := by
    cases hI : V.criticalInputs with
    | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven | belowMOddTOdd |
        boundaryEven | boundaryOdd =>
        have hbad := hinputAbove
        rw [hI] at hbad
        simp only [WildQuadraticCoefficientInputs.row,
          WildQuadraticCoefficientRow.range] at hbad
        cases hbad
    | aboveMEvenTEven =>
        have hTp := hTParityOfRow
        have hmp := hmParityOfRow
        rw [hI] at hTp hmp
        have hTEven : Even (t + 1) :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            (t + 1)).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.TParity] using hTp.symm)
        have hmEven : Even m :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            m).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.mParity] using hmp.symm)
        simpa only [hI, WildQuadraticCoefficientInputs.tauSource,
          WildQuadraticCoefficientInputs.chiFSource] using
            And.intro (hTauEvenPhase hTEven) (hBaseEvenPhase hmEven)
    | aboveMEvenTOdd tauW =>
        have hmp := hmParityOfRow
        rw [hI] at hmp
        have hmEven : Even m :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            m).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.mParity] using hmp.symm)
        have hp := V.criticalInputs_stationaryPairs
        have hl := V.criticalInputs_localData
        rw [hI] at hp hl
        have hpRow :
            QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
              F tauW rows.tau.selectedStationaryPair := by
          rw [rows.tau_pair]
          exact hp
        have hlRow :
            QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F tauW
              (data.normCharacterData assembly.indexing.tau) data.baseAddChar := by
          rw [coordinates.tauData_eq, coordinates.baseAddData_eq]
          exact hl
        have htauPhase :=
          rows.tau.criticalFactor_eq_quotientSourcePhase_of_matches tauW hlRow
            hpRow
        simpa only [hI, WildQuadraticCoefficientInputs.tauSource,
          WildQuadraticCoefficientInputs.chiFSource] using
            And.intro htauPhase (hBaseEvenPhase hmEven)
    | aboveMOddTEven chiW =>
        have hTp := hTParityOfRow
        rw [hI] at hTp
        have hTEven : Even (t + 1) :=
          (WildQuadraticConductorParity.ofConductor_eq_even_iff
            (t + 1)).mp (by
              simpa only [WildQuadraticCoefficientInputs.row,
                WildQuadraticCoefficientRow.TParity] using hTp.symm)
        have hp := V.criticalInputs_stationaryPairs
        have hl := V.criticalInputs_localData
        rw [hI] at hp hl
        have hpRow :
            QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
              F chiW rows.base.selectedStationaryPair := by
          rw [rows.base_pair]
          exact hp
        have hlRow :
            QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F chiW
              (data.twistData 1) data.baseAddChar := by
          rw [coordinates.baseData_eq, coordinates.baseAddData_eq]
          exact hl
        have hbasePhase :=
          rows.base.criticalFactor_eq_quotientSourcePhase_of_matches chiW hlRow
            hpRow
        simpa only [hI, WildQuadraticCoefficientInputs.tauSource,
          WildQuadraticCoefficientInputs.chiFSource] using
            And.intro (hTauEvenPhase hTEven) hbasePhase
    | aboveMOddTOdd tauW chiW =>
        have hp := V.criticalInputs_stationaryPairs
        have hl := V.criticalInputs_localData
        rw [hI] at hp hl
        have hpTau :
            QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
              F tauW rows.tau.selectedStationaryPair := by
          rw [rows.tau_pair]
          exact hp.1
        have hpBase :
            QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
              F chiW rows.base.selectedStationaryPair := by
          rw [rows.base_pair]
          exact hp.2
        have hlTau :
            QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F tauW
              (data.normCharacterData assembly.indexing.tau) data.baseAddChar := by
          rw [coordinates.tauData_eq, coordinates.baseAddData_eq]
          exact hl.1
        have hlBase :
            QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F chiW
              (data.twistData 1) data.baseAddChar := by
          rw [coordinates.baseData_eq, coordinates.baseAddData_eq]
          exact hl.2
        have htauPhase :=
          rows.tau.criticalFactor_eq_quotientSourcePhase_of_matches tauW hlTau
            hpTau
        have hbasePhase :=
          rows.base.criticalFactor_eq_quotientSourcePhase_of_matches chiW hlBase
            hpBase
        simpa only [hI, WildQuadraticCoefficientInputs.tauSource,
          WildQuadraticCoefficientInputs.chiFSource] using
            And.intro htauPhase hbasePhase
  have htauPhase :
      rows.tau.criticalFactor =
        quotientSourcePhase F V.criticalInputs.tauSource := by
    exact hsourcePhases.1
  have hbasePhase :
      rows.base.criticalFactor =
        quotientSourcePhase F V.criticalInputs.chiFSource := by
    exact hsourcePhases.2
  exact
    { coordinate := coordinate
      lowerProduct := by
        intro q lambda haff
        obtain ⟨C0, _hphase⟩ := hproduct q haff
        exact ⟨C0⟩
      tau_phase := fun _q ↦ htauPhase
      base_phase := fun _q ↦ hbasePhase
      twist_phase := by
        intro q
        cases haff :
            (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF with
        | none =>
            rw [WildQuadraticCoefficientData.phaseFactor, haff]
            exact hproductNone q haff
        | some lambda =>
            obtain ⟨C0, hphase⟩ := hproduct q haff
            exact hphase.trans (C0.phase_eq_table haff) }


end

end LanglandsFirstMainLemma
