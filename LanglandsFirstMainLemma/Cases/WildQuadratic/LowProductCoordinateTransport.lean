import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Cases.WildQuadratic.CoordinateTransport
import LanglandsFirstMainLemma.Cases.WildQuadratic.LowCoordinateTransport

namespace LanglandsFirstMainLemma

noncomputable section

/-!
# Low lower-product coordinate transport

This node transports the strict-low and odd-boundary lower product.  It
depends on the completed low upper package only for the q-free boundary
source witness, so the selected-coordinate proof behind MatchesCorrection is
never duplicated.  Every refinement remains universally quantified.
-/

namespace ProductBoundaryCoordinates

/-- Construct the three boundary lift families from the two exact normalized
delta ratios. Both lower sources use one literal product lift. -/
noncomputable def ofNormalizedDeltaRatios
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)] [CharP (ResidueField E) 2]
    (product tau chiF : QuotientDerivedNormalizedCriticalFunction E)
    (productArg tauArg chiArg : ResidueField E → ResidueField E)
    (htauConductor : tau.chi.conductor = product.chi.conductor)
    (hchiConductor : chiF.chi.conductor = product.chi.conductor)
    (htauArgument : ∀ z, productArg z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        tau product htauConductor * tauArg z)
    (hchiArgument : ∀ z, productArg z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        chiF product hchiConductor * chiArg z) :
    ProductBoundaryCoordinates E product tau chiF productArg tauArg chiArg where
  productLift := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonProductLift
      (productArg z)
  tauLift := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonSourceLift
      tau product htauConductor (productArg z)
  chiLift := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonSourceLift
      chiF product hchiConductor (productArg z)
  product_reduce := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonProductLift_reduce
      (productArg z)
  tau_reduce := by
    intro z
    rw [QuotientDerivedNormalizedCriticalFunction.normalizedCommonSourceLift_reduce,
      htauArgument z]
    field_simp [
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_ne_zero
        tau product htauConductor]
  chi_reduce := by
    intro z
    rw [QuotientDerivedNormalizedCriticalFunction.normalizedCommonSourceLift_reduce,
      hchiArgument z]
    field_simp [
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_ne_zero
        chiF product hchiConductor]
  tau_commonUnit := fun z =>
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_normalizedCommonSourceLift
      tau product htauConductor (productArg z)
  chi_commonUnit := fun z =>
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_normalizedCommonSourceLift
      chiF product hchiConductor (productArg z)

end ProductBoundaryCoordinates

section ProductCertificateConstructors

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

noncomputable def ActualProductCoordinateCertificate.ofBelowNormalizedDeltaRatio
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (product tau : QuotientDerivedNormalizedCriticalFunction F)
    (product_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F product S.tauChiF)
    (product_character : product.chi.character =
      tauData.character * chiFData.character)
    (product_psi : product.psi = psiF)
    (product_ratio_sum : S.tauChiF.ratio = S.tau.ratio + S.chiF.ratio)
    (hrange : (I.toCoefficientData q).range = .below)
    (tau_source : I.tauSource = some tau)
    (tau_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F tau S.tau)
    (tau_character : tau.chi.character = tauData.character)
    (tau_psi : tau.psi = psiF)
    (hconductor : tau.chi.conductor = product.chi.conductor)
    (hargument : ∀ z, (I.toCoefficientData q).lowerProductScale z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        tau product hconductor *
          (I.toCoefficientData q).lowerTauArgument z)
    (stable_factor : ∀ z,
      stationaryUnitFactor chiFData.character psiF S.chiF
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift product
          (QuotientDerivedNormalizedCriticalFunction.normalizedCommonProductLift
            ((I.toCoefficientData q).lowerProductScale z))) = 1) :
    ActualProductCoordinateCertificate F K q I S tauData chiFData psiF where
  product := product
  product_pair := product_pair
  product_character := product_character
  product_psi := product_psi
  product_ratio_sum := product_ratio_sum
  rangeCoordinates := .below hrange
    { tau := tau
      tau_source := tau_source
      tau_pair := tau_pair
      tau_character := tau_character
      tau_psi := tau_psi
      coordinates := ProductDominantCoordinates.ofNormalizedDeltaRatio
        product tau _ _ hconductor hargument
      stable_factor := stable_factor }
noncomputable def ActualProductCoordinateCertificate.ofBoundaryNormalizedDeltaRatios
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (product tau chiF : QuotientDerivedNormalizedCriticalFunction F)
    (product_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F product S.tauChiF)
    (product_character : product.chi.character =
      tauData.character * chiFData.character)
    (product_psi : product.psi = psiF)
    (product_ratio_sum : S.tauChiF.ratio = S.tau.ratio + S.chiF.ratio)
    (hrange : (I.toCoefficientData q).range = .boundary)
    (tau_source : I.tauSource = some tau)
    (chiF_source : I.chiFSource = some chiF)
    (tau_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F tau S.tau)
    (chiF_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F chiF S.chiF)
    (tau_character : tau.chi.character = tauData.character)
    (chiF_character : chiF.chi.character = chiFData.character)
    (tau_psi : tau.psi = psiF) (chiF_psi : chiF.psi = psiF)
    (htauConductor : tau.chi.conductor = product.chi.conductor)
    (hchiConductor : chiF.chi.conductor = product.chi.conductor)
    (htauArgument : ∀ z, (I.toCoefficientData q).lowerProductScale z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        tau product htauConductor *
          (I.toCoefficientData q).lowerTauArgument z)
    (hchiArgument : ∀ z, (I.toCoefficientData q).lowerProductScale z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        chiF product hchiConductor *
          (I.toCoefficientData q).lowerChiArgument z) :
    ActualProductCoordinateCertificate F K q I S tauData chiFData psiF where
  product := product
  product_pair := product_pair
  product_character := product_character
  product_psi := product_psi
  product_ratio_sum := product_ratio_sum
  rangeCoordinates := .boundary hrange
    { tau := tau
      chiF := chiF
      tau_source := tau_source
      chiF_source := chiF_source
      tau_pair := tau_pair
      chiF_pair := chiF_pair
      tau_character := tau_character
      chiF_character := chiF_character
      tau_psi := tau_psi
      chiF_psi := chiF_psi
      coordinates := ProductBoundaryCoordinates.ofNormalizedDeltaRatios
        product tau chiF _ _ _ htauConductor hchiConductor
          htauArgument hchiArgument }

end ProductCertificateConstructors

section LowProductProofs

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ} {V : WildQuadraticCommonCoefficientView F K t m}
  {data : FirstMainComputationalData F K V.chiFData.character V.psiF.character}
  {phaseData : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
  {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character V.psiF.character
    data phaseData (t := t) (m := m)}
  {rows : WildQuadraticActualPhaseRows V data phaseData assembly}

local macro "solve_stationary_factor" epsilon:term : tactic =>
  set_option hygiene false in `(tactic| (
    let ylat : lattice E ((d + $epsilon : ℕ) : ℤ) :=
      ⟨y, by simpa only [hd] using hy⟩
    have hlin := stationaryNumeratorClass_linearization E chi psi
      (chi.conductor : ℤ)
      (lamprechtFormula_stationaryDepth E chi d $epsilon
        (by omega) (by simpa using hm) hlarge)
      Gamma Gamma.property c hc ylat
    have hunit' : unit = positiveUnitOfLattice E
        (lamprechtFormula_stationaryDepth E chi d $epsilon
          (by omega) (by simpa using hm) hlarge).pos ylat := by
      apply Units.ext
      rw [hunit]
      rfl
    rw [hunit']
    have hlinC := congrArg (Units.val : ℂˣ → ℂ) hlin
    have harg :
        (c : E) / ((Gamma : Eˣ) : E) *
              (((positiveUnitOfLattice E
                  (lamprechtFormula_stationaryDepth E chi d $epsilon
                    (by omega) (by simpa using hm) hlarge).pos ylat : Eˣ) : E) - 1) =
          (c : E) * (ylat : E) / ((Gamma : Eˣ) : E) := by
      change (c : E) / ((Gamma : Eˣ) : E) * ((1 + (ylat : E)) - 1) = _
      field_simp [AdmissibleGamma.coe_ne_zero]
      ring
    rw [stationaryUnitFactor, ← hpair]
    dsimp only [LocalLamprechtPhaseData.selectedStationaryPair,
      WildQuadraticStationaryPair.ratio]
    rw [harg, hlinC]
    field_simp [ContinuousAddChar.apply_ne_zero]))

/-- The selected stationary factor of either parity is one on the actual
ceiling-half-depth lattice. -/
theorem wildQuadratic_stationaryUnitFactor_eq_one_of_mem_ceilingHalf
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (row : LocalLamprechtPhaseData E chi psi)
    (P : WildQuadraticStationaryPair E)
    (hpair : row.selectedStationaryPair = P)
    (y : E)
    (hy : y ∈ lattice E (((chi.conductor + 1) / 2 : ℕ) : ℤ))
    (unit : Eˣ) (hunit : (unit : E) = 1 + y) :
    stationaryUnitFactor chi.character psi P unit = 1 := by
  cases row with
  | even d hm hlarge Gamma c hc =>
      have hd : (chi.conductor + 1) / 2 = d + 0 := by omega
      solve_stationary_factor 0
  | odd d hm hlarge Gamma delta hdelta c hc =>
      have hd : (chi.conductor + 1) / 2 = d + 1 := by omega
      solve_stationary_factor 1

/-- Strict-range stability at the literal critical unit supplied by the
normalized product coordinate. -/
theorem wildQuadratic_lowerRow_stable_on_productCriticalUnit
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)] [CharP (ResidueField E) 2]
    {psi : LocalAddCharData E}
    (product : QuotientDerivedNormalizedCriticalFunction E)
    (lower : LocalQuasiCharData E)
    (row : LocalLamprechtPhaseData E lower psi)
    (P : WildQuadraticStationaryPair E)
    (hpair : row.selectedStationaryPair = P)
    (hlower : lower.conductor < product.chi.conductor)
    (x : lattice E 0) :
    stationaryUnitFactor lower.character psi P
      (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift product x) = 1 := by
  have hmem : (product.delta : E) * (x : E) ∈
      lattice E (((lower.conductor + 1) / 2 : ℕ) : ℤ) := by
    have hdepth : (lower.conductor + 1) / 2 ≤ product.d := by
      have hproduct := product.conductor_eq
      omega
    apply lattice_antitone E
      (show (((lower.conductor + 1) / 2 : ℕ) : ℤ) ≤ (product.d : ℤ) by
        exact_mod_cast hdepth)
    have hdelta : (product.delta : E) ∈ lattice E (product.d : ℤ) := by
      rw [mem_lattice, product.delta_order]
    simpa only [add_zero] using mul_mem_lattice E hdelta x.property
  apply wildQuadratic_stationaryUnitFactor_eq_one_of_mem_ceilingHalf
    row P hpair ((product.delta : E) * (x : E)) hmem
  exact QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_coe
    product x

/-- The two literal boundary units, with the residue classes forced by the
selected source coordinate. -/
structure WildQuadraticBoundaryProductUnits (rho : ResidueField F) where
  nUnit : unitGroup F
  denUnit : unitGroup F
  n_coe : (((nUnit : unitGroup F) : Fˣ) : F) = (V.correction.n : F)
  den_coe : (((denUnit : unitGroup F) : Fˣ) : F) = V.correction.denominator
  n_residue : ((residueUnits F nUnit : (ResidueField F)ˣ) : ResidueField F) = rho ^ 2
  den_residue : ((residueUnits F denUnit : (ResidueField F)ˣ) : ResidueField F) =
    (1 + rho) ^ 2

noncomputable def wildQuadratic_boundaryProductUnits
    (rho : ResidueField F) (hden : 1 + rho ≠ 0)
    (hboundary : m = t + 1)
    (hnorm : WildQuadraticCoefficientData.boundaryNResidue F K V.correction
      hboundary = rho ^ 2) :
    WildQuadraticBoundaryProductUnits (F := F) (K := K) (V := V) rho := by
  have hnOrder : ord F (V.correction.n : F) = (0 : WithTop ℤ) := by
    rw [V.correction.target_order, hboundary]
    simp
  let nUnit : unitGroup F :=
    ⟨V.correction.n, (mem_unitGroup_iff_ord_eq_zero F V.correction.n).2 hnOrder⟩
  let nO : ringOfIntegers F :=
    ⟨(V.correction.n : F), (mem_lattice_zero_iff F).1 (by
      rw [mem_lattice, hnOrder]
      exact le_rfl)⟩
  have hnResidue : residueMap F nO = rho ^ 2 := by
    change reduce F (V.correction.n : F) (by
      rw [mem_lattice, hnOrder]
      exact le_rfl) = rho ^ 2
    simpa only [WildQuadraticCoefficientData.boundaryNResidue] using hnorm
  have hdenResidue : residueMap F (1 + nO) = (1 + rho) ^ 2 := by
    rw [map_add, map_one, hnResidue, CharTwo.add_sq, one_pow]
  have hdenUnit : IsUnit (1 + nO) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (1 + nO)).1 (by
      rw [hdenResidue]
      exact pow_ne_zero 2 hden)
  let denUnit : unitGroup F :=
    (unitGroupMulEquivRingOfIntegers F).symm hdenUnit.unit
  exact
    { nUnit := nUnit
      denUnit := denUnit
      n_coe := rfl
      den_coe := by rfl
      n_residue := by
        rw [residueUnits_coe]
        exact hnResidue
      den_residue := by
        rw [residueUnits_coe]
        exact hdenResidue }

/-- The principal local unit `1+x` attached to a first-lattice element. -/
noncomputable def wildQuadratic_oneAddLocalUnit
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (x : E) (hx : x ∈ lattice E 1) : unitGroup E := by
  have hxord : ((1 : ℤ) : WithTop ℤ) ≤ ord E x := by
    simpa only [mem_lattice] using hx
  have hne : ord E (1 : E) ≠ ord E x := by
    rw [ord_one]
    exact ne_of_lt (lt_of_lt_of_le (by norm_num) hxord)
  have hord : ord E ((1 : E) + x) = 0 := by
    rw [ord_add_eq_min E hne, ord_one, min_eq_left]
    exact le_trans (by norm_num) hxord
  let u : Eˣ := Units.mk0 (1 + x) ((ord_ne_top_iff E).1 (by
    rw [hord]
    exact WithTop.coe_ne_top))
  exact ⟨u, (mem_unitGroup_iff_ord_eq_zero E u).2 hord⟩

@[simp]
theorem wildQuadratic_oneAddLocalUnit_coe
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (x : E) (hx : x ∈ lattice E 1) :
    (((wildQuadratic_oneAddLocalUnit x hx : unitGroup E) : Eˣ) : E) = 1 + x :=
  rfl

theorem wildQuadratic_oneAddLocalUnit_residue
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (x : E) (hx : x ∈ lattice E 1) :
    ((residueUnits E (wildQuadratic_oneAddLocalUnit x hx) :
      (ResidueField E)ˣ) : ResidueField E) = 1 := by
  rw [residueUnits_coe]
  rw [← map_one (residueMap E)]
  apply (residueMap_eq_residueMap_iff E _ _).2
  change ((1 : E) + x) - 1 ∈ lattice E 1
  simpa using hx

/-- Recover the complete actual product certificate, including its row phase,
from range-separated primitive coordinates. -/
noncomputable def wildQuadratic_productCertificate_ofActualTwist
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (q : CharTwoRefinement (ResidueField F))
    (product : QuotientDerivedNormalizedCriticalFunction F)
    (product_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F product
        (data.twistData assembly.indexing.tau) data.baseAddChar)
    (product_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product rows.twist.selectedStationaryPair)
    (rangeCoordinates : ProductRangeCoordinates F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF product) :
    { C : ActualProductCoordinateCertificate F K q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF //
      rows.twist.criticalFactor =
        QuotientDerivedNormalizedCriticalFunction.phase F C.product } := by
  have htauChar := congrArg LocalQuasiCharData.character
    coordinates.tauData_eq
  have hbaseChar := congrArg LocalQuasiCharData.character
    coordinates.baseData_eq
  have hproductCharacter : product.chi.character =
      V.tauData.character * V.chiFData.character := by
    rw [product_local.1]
    calc
      (data.twistData assembly.indexing.tau).character =
          assembly.indexing.tau.1 * V.chiFData.character :=
        data.twistData_character assembly.indexing.tau
      _ = (data.normCharacterData assembly.indexing.tau).character *
          V.chiFData.character := by rw [data.normCharacterData_character]
      _ = V.tauData.character * V.chiFData.character := by rw [htauChar]
  let C : ActualProductCoordinateCertificate F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF :=
    { product := product
      product_pair := by
        rw [← rows.twist_pair]
        exact product_pair
      product_character := hproductCharacter
      product_psi := product_local.2.trans coordinates.baseAddData_eq
      product_ratio_sum := product_ratio_sum_of_common_n F K V.stationaryPairs
        (V.correction.n : F) V.chiF_ratio V.tauChiF_ratio
      rangeCoordinates := rangeCoordinates }
  have hphase :=
    rows.twist.criticalFactor_eq_quotientSourcePhase_of_matches product
      product_local product_pair
  exact ⟨C, by simpa only [quotientSourcePhase] using hphase⟩

/-- One producer serves both strict-below positive product rows. -/
noncomputable def wildQuadratic_strictBelowProductCertificate
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (q : CharTwoRefinement (ResidueField F))
    (product tau : QuotientDerivedNormalizedCriticalFunction F)
    (product_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F product
        (data.twistData assembly.indexing.tau) data.baseAddChar)
    (product_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product rows.twist.selectedStationaryPair)
    (tau_source : V.criticalInputs.tauSource = some tau)
    (tau_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F tau
        V.stationaryPairs.tau)
    (tau_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F tau
        V.tauData V.psiF)
    (hrange : (V.criticalInputs.toCoefficientData q).range = .below)
    (hbelow : m < t + 1)
    (hconductor : tau.chi.conductor = product.chi.conductor)
    (hlower : V.chiFData.conductor < product.chi.conductor) :
    { C : ActualProductCoordinateCertificate F K q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF //
      rows.twist.criticalFactor =
        QuotientDerivedNormalizedCriticalFunction.phase F C.product } := by
  have hnmem : (V.correction.n : F) ∈ lattice F 1 := by
    rw [mem_lattice, V.correction.target_order]
    change ((1 : ℤ) : WithTop ℤ) ≤
      (((((t + 1 : ℕ) : ℤ) - (m : ℤ)) : ℤ) : WithTop ℤ)
    rw [show ((t + 1 : ℕ) : ℤ) - (m : ℤ) =
      ((t + 1 - m : ℕ) : ℤ) by omega]
    norm_cast
    omega
  let u : unitGroup F :=
    wildQuadratic_oneAddLocalUnit (V.correction.n : F) hnmem
  have hpsi : tau.psi = product.psi := by
    rw [tau_local.2, product_local.2, coordinates.baseAddData_eq]
  have hproductPair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product V.stationaryPairs.tauChiF := by
    rw [← rows.twist_pair]
    exact product_pair
  have hratio : (product.beta : F) / ((product.Gamma : Fˣ) : F) =
      (((u : unitGroup F) : Fˣ) : F) *
        ((tau.beta : F) / ((tau.Gamma : Fˣ) : F)) := by
    calc
      (product.beta : F) / ((product.Gamma : Fˣ) : F) =
          V.stationaryPairs.tauChiF.ratio := by
            rw [hproductPair.1, hproductPair.2]
            rfl
      _ = V.stationaryPairs.tau.ratio *
          ((V.correction.n : F) + 1) := V.tauChiF_ratio
      _ = (((u : unitGroup F) : Fˣ) : F) *
          ((tau.beta : F) / ((tau.Gamma : Fˣ) : F)) := by
            rw [tau_pair.1, tau_pair.2]
            simp only [u, wildQuadratic_oneAddLocalUnit_coe]
            change V.stationaryPairs.tau.ratio *
              ((V.correction.n : F) + 1) =
                (1 + (V.correction.n : F)) *
                  V.stationaryPairs.tau.ratio
            ring
  have hresidue : ((residueUnits F u : (ResidueField F)ˣ) :
      ResidueField F) = (1 : ResidueField F) ^ 2 := by
    rw [wildQuadratic_oneAddLocalUnit_residue]
    simp
  have hratioResidue :
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        tau product hconductor = 1 :=
    QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_eq_of_scale
      tau product hpsi hconductor u hratio 1 hresidue
  have hargument : ∀ z,
      (V.criticalInputs.toCoefficientData q).lowerProductScale z =
        QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
          tau product hconductor *
            (V.criticalInputs.toCoefficientData q).lowerTauArgument z := by
    intro z
    rw [hratioResidue, one_mul]
    generalize hD : V.criticalInputs.toCoefficientData q = D at hrange ⊢
    cases D <;>
      simp_all [WildQuadraticCoefficientData.range,
        WildQuadraticCoefficientData.row,
        WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientData.lowerProductScale,
        WildQuadraticCoefficientData.lowerTauArgument]
  let rangeCoordinates : ProductRangeCoordinates F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF product :=
    .below hrange
      { tau := tau
        tau_source := tau_source
        tau_pair := tau_pair
        tau_character := congrArg LocalQuasiCharData.character tau_local.1
        tau_psi := tau_local.2
        coordinates := ProductDominantCoordinates.ofNormalizedDeltaRatio
          product tau _ _ hconductor hargument
        stable_factor := fun z ↦ by
          have hlt : (data.twistData 1).conductor <
              product.chi.conductor := by
            rw [coordinates.baseData_eq]
            exact hlower
          have hs :=
            wildQuadratic_lowerRow_stable_on_productCriticalUnit
              product (data.twistData 1) rows.base V.stationaryPairs.chiF
                rows.base_pair hlt
                ((ProductDominantCoordinates.ofNormalizedDeltaRatio product tau
                  (V.criticalInputs.toCoefficientData q).lowerProductScale
                  (V.criticalInputs.toCoefficientData q).lowerTauArgument
                  hconductor hargument).productLift z)
          rw [congrArg LocalQuasiCharData.character coordinates.baseData_eq,
            coordinates.baseAddData_eq] at hs
          exact hs }
  exact wildQuadratic_productCertificate_ofActualTwist coordinates q
    product product_local product_pair rangeCoordinates

/-- One producer serves both strict-above positive product rows. -/
noncomputable def wildQuadratic_boundaryProductCertificate
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (q : CharTwoRefinement (ResidueField F))
    (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
    (product tau chiF : QuotientDerivedNormalizedCriticalFunction F)
    (hI : V.criticalInputs = .boundaryOdd rho hrho hden tau chiF)
    (product_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F product
        (data.twistData assembly.indexing.tau) data.baseAddChar)
    (product_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product rows.twist.selectedStationaryPair)
    (tau_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F tau
        V.stationaryPairs.tau)
    (chiF_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F chiF
        V.stationaryPairs.chiF)
    (tau_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F tau
        V.tauData V.psiF)
    (chiF_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F chiF
        V.chiFData V.psiF)
    (hboundary : m = t + 1)
    (hnormResidue :
      WildQuadraticCoefficientData.boundaryNResidue F K V.correction
        hboundary = rho ^ 2)
    (htauConductor : tau.chi.conductor = product.chi.conductor)
    (hchiConductor : chiF.chi.conductor = product.chi.conductor) :
    { C : ActualProductCoordinateCertificate F K q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF //
      rows.twist.criticalFactor =
        QuotientDerivedNormalizedCriticalFunction.phase F C.product } := by
  let U := wildQuadratic_boundaryProductUnits (F := F) (K := K) (V := V)
    rho hden hboundary hnormResidue
  let nUnit : unitGroup F := U.nUnit
  let denUnit : unitGroup F := U.denUnit
  let chiScaleUnit : unitGroup F := denUnit / nUnit
  have hnResidue : ((residueUnits F nUnit : (ResidueField F)ˣ) :
      ResidueField F) = rho ^ 2 := U.n_residue
  have hdenResidue : ((residueUnits F denUnit : (ResidueField F)ˣ) :
      ResidueField F) = (1 + rho) ^ 2 := U.den_residue
  have hchiScaleResidue :
      ((residueUnits F chiScaleUnit : (ResidueField F)ˣ) :
        ResidueField F) = ((1 + rho) / rho) ^ 2 := by
    simp only [chiScaleUnit, map_div, Units.val_div_eq_div_val,
      hdenResidue, hnResidue]
    rw [div_pow]
  have hproductPair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F
        product V.stationaryPairs.tauChiF := by
    rw [← rows.twist_pair]
    exact product_pair
  have htauPsi : tau.psi = product.psi := by
    rw [tau_local.2, product_local.2, coordinates.baseAddData_eq]
  have hchiPsi : chiF.psi = product.psi := by
    rw [chiF_local.2, product_local.2, coordinates.baseAddData_eq]
  have hchiScaleCoe :
      (((chiScaleUnit : unitGroup F) : Fˣ) : F) =
        V.correction.denominator / (V.correction.n : F) := by
    change ((((denUnit / nUnit : unitGroup F) : Fˣ) : F)) = _
    rw [show ((denUnit / nUnit : unitGroup F) : Fˣ) =
      (denUnit : Fˣ) / (nUnit : Fˣ) by rfl]
    rw [Units.val_div_eq_div_val, show ((denUnit : unitGroup F) : Fˣ) =
      U.denUnit by rfl, show ((nUnit : unitGroup F) : Fˣ) = U.nUnit by rfl,
      U.den_coe, U.n_coe]
  have htauRatio : (product.beta : F) / ((product.Gamma : Fˣ) : F) =
      (((denUnit : unitGroup F) : Fˣ) : F) *
        ((tau.beta : F) / ((tau.Gamma : Fˣ) : F)) := by
    calc
      (product.beta : F) / ((product.Gamma : Fˣ) : F) =
          V.stationaryPairs.tauChiF.ratio := by
            rw [hproductPair.1, hproductPair.2]
            rfl
      _ = V.stationaryPairs.tau.ratio *
          ((V.correction.n : F) + 1) := V.tauChiF_ratio
      _ = (((denUnit : unitGroup F) : Fˣ) : F) *
          ((tau.beta : F) / ((tau.Gamma : Fˣ) : F)) := by
            rw [tau_pair.1, tau_pair.2]
            simp only [denUnit, U.den_coe,
              WildQuadraticCommonCorrectionData.denominator]
            change V.stationaryPairs.tau.ratio *
              ((V.correction.n : F) + 1) =
                (1 + (V.correction.n : F)) *
                  V.stationaryPairs.tau.ratio
            ring
  have hchiRatio : (product.beta : F) / ((product.Gamma : Fˣ) : F) =
      (((chiScaleUnit : unitGroup F) : Fˣ) : F) *
        ((chiF.beta : F) / ((chiF.Gamma : Fˣ) : F)) := by
    calc
      (product.beta : F) / ((product.Gamma : Fˣ) : F) =
          V.stationaryPairs.tauChiF.ratio := by
            rw [hproductPair.1, hproductPair.2]
            rfl
      _ = V.stationaryPairs.tau.ratio *
          ((V.correction.n : F) + 1) := V.tauChiF_ratio
      _ = (((chiScaleUnit : unitGroup F) : Fˣ) : F) *
          V.stationaryPairs.chiF.ratio := by
            rw [hchiScaleCoe, V.chiF_ratio,
              WildQuadraticCommonCorrectionData.denominator]
            field_simp [Units.ne_zero V.correction.n]
            ring
      _ = (((chiScaleUnit : unitGroup F) : Fˣ) : F) *
          ((chiF.beta : F) / ((chiF.Gamma : Fˣ) : F)) := by
            rw [chiF_pair.1, chiF_pair.2]
            rfl
  have htauScale :
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        tau product htauConductor = 1 + rho :=
    QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_eq_of_scale
      tau product htauPsi htauConductor denUnit htauRatio (1 + rho)
        hdenResidue
  have hchiScale :
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        chiF product hchiConductor = (1 + rho) / rho :=
    QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_eq_of_scale
      chiF product hchiPsi hchiConductor chiScaleUnit hchiRatio
        ((1 + rho) / rho) hchiScaleResidue
  have htauArgument : ∀ z,
      (V.criticalInputs.toCoefficientData q).lowerProductScale z =
        QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
          tau product htauConductor *
            (V.criticalInputs.toCoefficientData q).lowerTauArgument z := by
    intro z
    rw [htauScale]
    simp only [hI, WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.lowerProductScale,
      WildQuadraticCoefficientData.lowerTauArgument,
      WildQuadraticCoefficientData.range,
      WildQuadraticCoefficientData.row,
      WildQuadraticCoefficientRow.range]
  have hchiArgument : ∀ z,
      (V.criticalInputs.toCoefficientData q).lowerProductScale z =
        QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
          chiF product hchiConductor *
            (V.criticalInputs.toCoefficientData q).lowerChiArgument z := by
    intro z
    rw [hchiScale]
    simp only [hI, WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.lowerProductScale,
      WildQuadraticCoefficientData.lowerChiArgument,
      WildQuadraticCoefficientData.range,
      WildQuadraticCoefficientData.row,
      WildQuadraticCoefficientRow.range]
    field_simp [hrho]
  let rangeCoordinates : ProductRangeCoordinates F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF product :=
    .boundary (by
      simp only [hI, WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.boundaryOddComputed,
        WildQuadraticCoefficientData.range,
        WildQuadraticCoefficientData.row,
        WildQuadraticCoefficientRow.range])
      { tau := tau
        chiF := chiF
        tau_source := by
          simp only [hI, WildQuadraticCoefficientInputs.tauSource]
        chiF_source := by
          simp only [hI, WildQuadraticCoefficientInputs.chiFSource]
        tau_pair := tau_pair
        chiF_pair := chiF_pair
        tau_character := congrArg LocalQuasiCharData.character tau_local.1
        chiF_character := congrArg LocalQuasiCharData.character chiF_local.1
        tau_psi := tau_local.2
        chiF_psi := chiF_local.2
        coordinates := ProductBoundaryCoordinates.ofNormalizedDeltaRatios
          product tau chiF _ _ _ htauConductor hchiConductor
            htauArgument hchiArgument }
  exact wildQuadratic_productCertificate_ofActualTwist coordinates q
    product product_local product_pair rangeCoordinates


noncomputable def wildQuadratic_lowBoundaryProductCallback
    (coordinates : WildQuadraticCommonCoordinateCompatibility V data
      phaseData assembly)
    (hlow : m ≤ t + 1)
    (htauConductor : V.tauData.conductor = t + 1)
    (htwistConductor :
      (data.twistData assembly.indexing.tau).conductor = max m (t + 1))
    (hBoundary : ∀
      (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
      (tau chiF : QuotientDerivedNormalizedCriticalFunction F),
      V.criticalInputs = .boundaryOdd rho hrho hden tau chiF →
        ∃ hboundary : m = t + 1,
          WildQuadraticCoefficientData.boundaryNResidue F K V.correction
            hboundary = rho ^ 2) :
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
  have hnotAbove : V.criticalInputs.row.range ≠ .above := by
    rw [V.criticalInputs_row]
    have hb : m - 1 ≤ t := by omega
    rcases lt_or_eq_of_le hb with hlt | heq
    · rw [WildQuadraticCoefficientRow.ofConductors_range_below hlt]
      decide
    · rw [WildQuadraticCoefficientRow.ofConductors_range_boundary heq]
      decide
  have hbelowOfRange
      (hrange : V.criticalInputs.row.range = .below) : m < t + 1 := by
    by_contra hnot
    have hpred : m - 1 = t := by omega
    have hrow := congrArg WildQuadraticCoefficientRow.range
      V.criticalInputs_row
    rw [hrange,
      WildQuadraticCoefficientRow.ofConductors_range_boundary hpred] at hrow
    contradiction
  have buildBelow : ∀
      (tau : QuotientDerivedNormalizedCriticalFunction F),
      V.criticalInputs.tauSource = some tau →
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F tau
        V.stationaryPairs.tau →
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F tau
        V.tauData V.psiF →
      ∀ q : CharTwoRefinement (ResidueField F),
      (V.criticalInputs.toCoefficientData q).range = .below →
      ∃ C : ActualProductCoordinateCertificate F K q V.criticalInputs
          V.stationaryPairs V.tauData V.chiFData V.psiF,
        rows.twist.criticalFactor =
          QuotientDerivedNormalizedCriticalFunction.phase F C.product := by
    intro tau hsource hpair hlocal q hrange
    have hirange : V.criticalInputs.row.range = .below := by
      rw [← WildQuadraticCoefficientInputs.toCoefficientData_row
        V.criticalInputs q]
      exact hrange
    have hbelow : m < t + 1 := hbelowOfRange hirange
    have hsourceConductor : tau.chi.conductor = t + 1 := by
      calc
        tau.chi.conductor = V.tauData.conductor :=
          congrArg LocalQuasiCharData.conductor hlocal.1
        _ = t + 1 := htauConductor
    have htwistOdd :
        Odd (data.twistData assembly.indexing.tau).conductor := by
      rw [htwistConductor, max_eq_right hlow, ← hsourceConductor,
        tau.conductor_eq]
      exact ⟨tau.d, by omega⟩
    obtain ⟨product, productLocal, productPair, _productPhase⟩ :=
      rows.twist.exists_normalizedQuotientDerivedCriticalFunction htwistOdd
    have hproductConductor : product.chi.conductor = t + 1 := by
      calc
        product.chi.conductor =
            (data.twistData assembly.indexing.tau).conductor :=
          congrArg LocalQuasiCharData.conductor productLocal.1
        _ = max m (t + 1) := htwistConductor
        _ = t + 1 := max_eq_right hlow
    have hsameConductor : tau.chi.conductor = product.chi.conductor :=
      hsourceConductor.trans hproductConductor.symm
    have hlower : V.chiFData.conductor < product.chi.conductor := by
      rw [hbaseConductor, hproductConductor]
      exact hbelow
    let cert := wildQuadratic_strictBelowProductCertificate coordinates q product tau
      productLocal productPair hsource hpair hlocal hrange hbelow
        hsameConductor hlower
    exact ⟨cert.1, cert.2⟩
  intro q lambda haff
  generalize hI : V.criticalInputs = I at haff ⊢
  cases I with
  | belowMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMEvenTOdd tau =>
      have hpairs := V.criticalInputs_stationaryPairs
      rw [hI] at hpairs
      have hlocal := V.criticalInputs_localData
      rw [hI] at hlocal
      have result := buildBelow tau
        (by simp only [hI, WildQuadraticCoefficientInputs.tauSource])
        hpairs hlocal q (by simp only [hI,
          WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.range,
          WildQuadraticCoefficientData.row,
          WildQuadraticCoefficientRow.range])
      rw [hI] at result
      exact result
  | belowMOddTEven chiF =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.belowMOddTEvenComputed,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMOddTOdd tau chiF =>
      have hpairs := V.criticalInputs_stationaryPairs
      rw [hI] at hpairs
      have hlocal := V.criticalInputs_localData
      rw [hI] at hlocal
      have result := buildBelow tau
        (by simp only [hI, WildQuadraticCoefficientInputs.tauSource])
        hpairs.1 hlocal.1 q (by simp only [hI,
          WildQuadraticCoefficientInputs.toCoefficientData,
          WildQuadraticCoefficientData.belowMOddTOddComputed,
          WildQuadraticCoefficientData.range,
          WildQuadraticCoefficientData.row,
          WildQuadraticCoefficientRow.range])
      rw [hI] at result
      exact result
  | boundaryEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | boundaryOdd rho hrho hden tau chiF =>
      have hpairs := V.criticalInputs_stationaryPairs
      rw [hI] at hpairs
      have hlocal := V.criticalInputs_localData
      rw [hI] at hlocal
      obtain ⟨hboundary, hnormResidue⟩ :=
        hBoundary rho hrho hden tau chiF hI
      have htauSourceConductor : tau.chi.conductor = t + 1 := by
        calc
          tau.chi.conductor = V.tauData.conductor :=
            congrArg LocalQuasiCharData.conductor hlocal.1.1
          _ = t + 1 := htauConductor
      have hchiSourceConductor : chiF.chi.conductor = t + 1 := by
        calc
          chiF.chi.conductor = V.chiFData.conductor :=
            congrArg LocalQuasiCharData.conductor hlocal.2.1
          _ = m := hbaseConductor
          _ = t + 1 := hboundary
      have htwistOdd :
          Odd (data.twistData assembly.indexing.tau).conductor := by
        rw [htwistConductor, max_eq_right hlow,
          ← htauSourceConductor, tau.conductor_eq]
        exact ⟨tau.d, by omega⟩
      obtain ⟨product, productLocal, productPair, _productPhase⟩ :=
        rows.twist.exists_normalizedQuotientDerivedCriticalFunction htwistOdd
      have hproductConductor : product.chi.conductor = t + 1 := by
        calc
          product.chi.conductor =
              (data.twistData assembly.indexing.tau).conductor :=
            congrArg LocalQuasiCharData.conductor productLocal.1
          _ = max m (t + 1) := htwistConductor
          _ = t + 1 := max_eq_right hlow
      have htauSame : tau.chi.conductor = product.chi.conductor :=
        htauSourceConductor.trans hproductConductor.symm
      have hchiSame : chiF.chi.conductor = product.chi.conductor :=
        hchiSourceConductor.trans hproductConductor.symm
      let cert := wildQuadratic_boundaryProductCertificate coordinates q rho hrho hden
        product tau chiF hI productLocal productPair hpairs.1 hpairs.2
          hlocal.1 hlocal.2 hboundary hnormResidue htauSame hchiSame
      have result : ∃ C : ActualProductCoordinateCertificate F K q
          V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF,
          rows.twist.criticalFactor =
            QuotientDerivedNormalizedCriticalFunction.phase F C.product :=
        ⟨cert.1, cert.2⟩
      rw [hI] at result
      exact result
  | aboveMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMEvenTOdd tau =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.aboveMEvenTOddComputed,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMOddTEven chiF =>
      exact (hnotAbove (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim
  | aboveMOddTOdd tau chiF =>
      exact (hnotAbove (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim

end LowProductProofs


structure WildQuadraticLowProductCoordinateTransport
    (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ} (V : WildQuadraticCommonCoefficientView F K t m)
    (source : V.criticalInputs.PositivePolarSource)
    {data : FirstMainComputationalData F K V.chiFData.character V.psiF.character}
    {phaseData : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character V.psiF.character
      data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows V data phaseData assembly) : Prop where
  lowerProduct :
    ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF =
          some lambda →
        Nonempty (ActualProductCoordinateCertificate F K q V.criticalInputs
          V.stationaryPairs V.tauData V.chiFData V.psiF)
  tau_phase : rows.tau.criticalFactor =
    quotientSourcePhase F V.criticalInputs.tauSource
  base_phase : rows.base.criticalFactor =
    quotientSourcePhase F V.criticalInputs.chiFSource
  twist_phase :
    ∀ q : CharTwoRefinement (ResidueField F),
      rows.twist.criticalFactor =
        (V.criticalInputs.toCoefficientData q).phaseFactor q .tauChiF

/-- Exact implementation inputs for the lower-product node.  `upper` is the
output of the low-coordinate node, fixing dependency direction B. -/
structure WildQuadraticLowProductCoordinateTransportSource
    (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ} (V : WildQuadraticCommonCoefficientView F K t m)
    {data : FirstMainComputationalData F K V.chiFData.character V.psiF.character}
    {phaseData : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character V.psiF.character
      data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows V data phaseData assembly) : Prop where
  upper : WildQuadraticLowCoordinateTransport F K V rows
  coordinates : WildQuadraticCommonCoordinateCompatibility V data phaseData
    assembly
  low : m ≤ t + 1
  tau_conductor : V.tauData.conductor = t + 1
  twist_conductor :
    (data.twistData assembly.indexing.tau).conductor = max m (t + 1)
  tau_phase : rows.tau.criticalFactor =
    quotientSourcePhase F V.criticalInputs.tauSource
  base_phase : rows.base.criticalFactor =
    quotientSourcePhase F V.criticalInputs.chiFSource

section LowProductAssembly

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ} {V : WildQuadraticCommonCoefficientView F K t m}
  {data : FirstMainComputationalData F K V.chiFData.character V.psiF.character}
  {phaseData : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
  {assembly : ExactQuadraticPhaseAssembly F K V.chiFData.character V.psiF.character
    data phaseData (t := t) (m := m)}
  {rows : WildQuadraticActualPhaseRows V data phaseData assembly}

/-- In a low positive row, the lower-product phase is constant only in the
odd/even strict-below consumer. -/
theorem wildQuadratic_lowProduct_none
    (source : V.criticalInputs.PositivePolarSource)
    (hlow : m ≤ t + 1)
    (hBelowEven : ∀
      (chiF : QuotientDerivedNormalizedCriticalFunction F),
      V.criticalInputs = .belowMOddTEven chiF →
        rows.twist.criticalFactor = 1) :
    ∀ q : CharTwoRefinement (ResidueField F),
      (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF =
          none →
        rows.twist.criticalFactor = 1 := by
  have hnotAbove : V.criticalInputs.row.range ≠ .above := by
    rw [V.criticalInputs_row]
    have hb : m - 1 ≤ t := by omega
    rcases lt_or_eq_of_le hb with hlt | heq
    · rw [WildQuadraticCoefficientRow.ofConductors_range_below hlt]
      decide
    · rw [WildQuadraticCoefficientRow.ofConductors_range_boundary heq]
      decide
  intro q haff
  generalize hI : V.criticalInputs = I at haff ⊢
  cases I with
  | belowMEvenTEven =>
      exact (WildQuadraticCoefficientInputs.isAllEven_positivePolarSource_disjoint
        (by rw [hI]; exact .belowMEvenTEven) source).elim
  | belowMEvenTOdd tau =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | belowMOddTEven chiF => exact hBelowEven chiF hI
  | belowMOddTOdd tau chiF =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.belowMOddTOddComputed,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | boundaryEven =>
      exact (WildQuadraticCoefficientInputs.isAllEven_positivePolarSource_disjoint
        (by rw [hI]; exact .boundaryEven) source).elim
  | boundaryOdd rho hrho hden tau chiF =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.boundaryOddComputed,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMEvenTEven =>
      exact (WildQuadraticCoefficientInputs.isAllEven_positivePolarSource_disjoint
        (by rw [hI]; exact .aboveMEvenTEven) source).elim
  | aboveMEvenTOdd tau =>
      exact (hnotAbove (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim
  | aboveMOddTEven chiF =>
      exact (hnotAbove (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim
  | aboveMOddTOdd tau chiF =>
      exact (hnotAbove (by simpa only [hI,
        WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.range])).elim

/-- Exact public-constructor shape for the low lower-product node.  No
refinement is selected: every occurrence of `q` is universally quantified. -/
noncomputable def wildQuadraticLowProductCoordinateTransport
    (P : WildQuadraticLowProductCoordinateTransportSource F K V rows)
    (source : V.criticalInputs.PositivePolarSource) :
    WildQuadraticLowProductCoordinateTransport F K V source rows := by
  let hproduct := wildQuadratic_lowBoundaryProductCallback (rows := rows)
    P.coordinates P.low
    P.tau_conductor P.twist_conductor (fun rho hrho hden tau chiF hI => by
      obtain ⟨hboundary, _hsource, hnorm⟩ :=
        P.upper.boundary_source rho hrho hden tau chiF hI
      exact ⟨hboundary, hnorm⟩)
  have hTwistConstant : ∀
      (chiF : QuotientDerivedNormalizedCriticalFunction F),
      V.criticalInputs = .belowMOddTEven chiF →
        rows.twist.criticalFactor = 1 := by
    intro chiF hI
    have hTParity :
        WildQuadraticConductorParity.ofConductor (t + 1) = .even := by
      rw [← WildQuadraticCoefficientRow.ofConductors_TParity (m - 1) t,
        ← V.criticalInputs_row, hI]
      rfl
    have hTEven : Even (t + 1) :=
      (WildQuadraticConductorParity.ofConductor_eq_even_iff (t + 1)).mp
        hTParity
    have htwistEven : Even (data.twistData assembly.indexing.tau).conductor := by
      rw [P.twist_conductor, max_eq_right P.low]
      exact hTEven
    apply rows.twist.criticalFactor_eq_one_of_isEven
    cases rows.twist with
    | even => trivial
    | odd d hm =>
        obtain ⟨j, hj⟩ := htwistEven
        simp only [LocalLamprechtPhaseData.IsEven]
        omega
  refine
    { lowerProduct := ?_
      tau_phase := P.tau_phase
      base_phase := P.base_phase
      twist_phase := ?_ }
  · intro q lambda haff
    obtain ⟨C, _hphase⟩ := hproduct q haff
    exact ⟨C⟩
  · intro q
    cases haff :
        (V.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF with
    | none =>
        rw [WildQuadraticCoefficientData.phaseFactor, haff]
        exact wildQuadratic_lowProduct_none source P.low hTwistConstant q haff
    | some lambda =>
        obtain ⟨C, hphase⟩ := hproduct q haff
        exact hphase.trans (C.phase_eq_table haff)

/-- PhasePreparation's complete low transport glue. -/
noncomputable def wildQuadraticLowContinuation
    (upper : WildQuadraticLowCoordinateTransport F K V rows)
    (product : WildQuadraticLowProductCoordinateTransport F K V source
      rows) :
    WildQuadraticPositivePolarContinuation F K V source rows where
  coordinate := upper.coordinate
  lowerProduct := product.lowerProduct
  tau_phase := fun _q => product.tau_phase
  base_phase := fun _q => product.base_phase
  twist_phase := product.twist_phase


end LowProductAssembly

end

end LanglandsFirstMainLemma
