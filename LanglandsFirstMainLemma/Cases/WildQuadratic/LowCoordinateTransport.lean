import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Cases.WildQuadratic.CoordinateTransport

namespace LanglandsFirstMainLemma

noncomputable section

/-!
# Low and boundary upper-coordinate transport

This node retains the actual low stationary representatives and transports
only the strict-low and boundary upper coordinates.  It never selects a
characteristic-two refinement and contains no lower-product package.
-/

/-! ## Boundary norm residue -/

/-- In a totally ramified extension, all conjugates of an integral unit
have the same residue.  Thus the residue of its norm is the corresponding
power.  The proof retains the actual unit and does not choose a quotient
representative. -/
theorem wildQuadratic_reduce_norm_unit_pow
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (v : K) (hvord : ord K v = (0 : WithTop ℤ)) :
    let hv : v ∈ lattice K 0 := by rw [mem_lattice, hvord]; exact le_rfl
    let hn : algebraMap F K (norm F K v) ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap, ord_norm, hres, one_nsmul, hvord,
        nsmul_zero]
      exact le_rfl
    reduce K (algebraMap F K (norm F K v)) hn =
      (reduce K v hv) ^ Module.finrank F K := by
  dsimp only
  classical
  have hv : v ∈ lattice K 0 := by rw [mem_lattice, hvord]; exact le_rfl
  let vO : ringOfIntegers K :=
    ⟨v, (mem_lattice_zero_iff K).1 hv⟩
  let cO : Gal(K/F) → ringOfIntegers K := fun sigma ↦
    ⟨sigma v, by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_galoisConjugate, hvord]
      exact le_rfl⟩
  let nO : ringOfIntegers K :=
    ⟨algebraMap F K (norm F K v), by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_algebraMap, ord_norm,
        hres, one_nsmul, hvord, nsmul_zero]
      exact le_rfl⟩
  have hnO : nO = ∏ sigma : Gal(K/F), cO sigma := by
    apply Subtype.ext
    dsimp only [nO, cO]
    change algebraMap F K (norm F K v) =
      algebraMap (ringOfIntegers K) K
        (∏ sigma : Gal(K/F),
          (⟨sigma v, _⟩ : ringOfIntegers K))
    rw [map_prod]
    change algebraMap F K (norm F K v) = ∏ sigma : Gal(K/F), sigma v
    exact Algebra.norm_eq_prod_automorphisms F v
  have hconj (sigma : Gal(K/F)) :
      residueMap K (cO sigma) = residueMap K vO := by
    apply (residueMap_eq_residueMap_iff K _ _).2
    have htop : lowerRamificationGroup F K (0 : ℤ) = ⊤ :=
      PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break
        F K ht (by omega)
    have hsigma : sigma ∈ lowerRamificationGroup F K (0 : ℤ) := by
      rw [htop]
      trivial
    rw [← congruentAtDepth_iff_sub_mem_lattice]
    simpa only [cO, vO, zero_add] using
      (mem_lowerRamificationGroup F K sigma (0 : ℤ)).1 hsigma
        (⟨v, (mem_lattice_zero_iff K).1 hv⟩ : ringOfIntegers K)
  change residueMap K nO = (residueMap K vO) ^ Module.finrank F K
  rw [hnO, map_prod]
  calc
    ∏ sigma : Gal(K/F), residueMap K (cO sigma) =
        ∏ _sigma : Gal(K/F), residueMap K vO := by
      apply Finset.prod_congr rfl
      intro sigma _
      exact hconj sigma
    _ = (residueMap K vO) ^ Fintype.card Gal(K/F) := by simp
    _ = (residueMap K vO) ^ Module.finrank F K := by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

/-- At the quadratic boundary, the retained common lower coordinate and the
exact norm identity determine the residue of the selected correction unit.
The square identity is an explicit input from that retained coordinate, so
the residue is never reconstructed from the norm alone. -/
theorem wildQuadratic_boundary_selected_unit_residue
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hboundary : m = t + 1) (rho : ResidueField F)
    (hnrho : WildQuadraticCoefficientData.boundaryNResidue F K C
      hboundary = rho ^ 2) :
    residueMap K
        (wildQuadraticBoundaryRingUnit F K C hboundary :
          ringOfIntegers K) = extensionResidueMap F K rho := by
  have huord : ord K (C.u : K) = (0 : WithTop ℤ) := by
    rw [C.source_order, hboundary]
    simp
  have hpow := wildQuadratic_reduce_norm_unit_pow F K ht
    C.residueDegree_eq_one (C.u : K) huord
  have hu : (C.u : K) ∈ lattice K (0 : ℤ) := by
    rw [mem_lattice, huord]
    exact le_rfl
  have hnF : (C.n : F) ∈ lattice F (0 : ℤ) := by
    rw [mem_lattice, C.target_order, hboundary]
    simp
  have hnK : algebraMap F K (C.n : F) ∈ lattice K (0 : ℤ) := by
    rw [mem_lattice, ord_algebraMap, C.target_order, hboundary]
    simp
  have hmap : reduce K (algebraMap F K (C.n : F)) hnK =
      extensionResidueMap F K
        (WildQuadraticCoefficientData.boundaryNResidue F K C hboundary) := by
    unfold WildQuadraticCoefficientData.boundaryNResidue
    unfold reduce
    exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (ValuativeRel.valuation F) (ValuativeRel.valuation K)
        (⟨(C.n : F), (mem_lattice_zero_iff F).1 hnF⟩ : ringOfIntegers F)
  have hsq :
      (residueMap K
          (wildQuadraticBoundaryRingUnit F K C hboundary :
            ringOfIntegers K)) ^ 2 =
        (extensionResidueMap F K rho) ^ 2 := by
    have hpow' : reduce K (algebraMap F K (C.n : F)) hnK =
        (reduce K (C.u : K) hu) ^ 2 := by
      simpa only [C.degree_eq_two, C.norm_u_field] using hpow
    calc
      (residueMap K
          (wildQuadraticBoundaryRingUnit F K C hboundary :
            ringOfIntegers K)) ^ 2 =
          (reduce K (C.u : K) hu) ^ 2 := by rfl
      _ = reduce K (algebraMap F K (C.n : F)) hnK := hpow'.symm
      _ = extensionResidueMap F K
          (WildQuadraticCoefficientData.boundaryNResidue F K C
            hboundary) := hmap
      _ = extensionResidueMap F K (rho ^ 2) := by rw [hnrho]
      _ = (extensionResidueMap F K rho) ^ 2 := map_pow _ rho 2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

section BoundaryScalars

variable {k : Type*} [Field k] [CharP k 2]

/-- The exact two residual scalars in the displayed common boundary
coordinate.  In particular, the normalization by the upper scale `1+r` is
retained on both the base and norm-character coordinates. -/
theorem wildQuadratic_boundary_transport_scalars
    (rho r gamma0 gamma gammaPrime : k)
    (hrho : rho ≠ 0) (hr : r ^ 2 = rho) (hden : 1 + rho ≠ 0)
    (hgamma : gammaPrime ^ 2 =
      (gamma + rho * gamma0 + rho + r) / (1 + rho))
    (z : k) :
    let D : WildQuadraticCoefficientData k :=
      .boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hgamma
    D.pTransport ((((D.commonScale .chiK)⁻¹) * z) ^ 2) =
        ((1 + r)⁻¹) ^ 2 * z ^ 2 ∧
      D.qTransport ((((D.commonScale .chiK)⁻¹) * z) ^ 2) =
        rho * ((1 + r)⁻¹) ^ 2 * z ^ 2 := by
  dsimp only [WildQuadraticCoefficientData.commonScale,
    WildQuadraticCoefficientData.pTransport,
    WildQuadraticCoefficientData.qTransport,
    WildQuadraticCoefficientData.range,
    WildQuadraticCoefficientData.row,
    WildQuadraticCoefficientRow.range]
  constructor <;> ring

/-- The boundary norm-character scalar divided by the boundary base scalar is
exactly the retained common-coordinate residue `rho`. -/
theorem wildQuadratic_boundary_transport_scalar_ratio
    (rho r : k) (hden : 1 + rho ≠ 0) (hr : r ^ 2 = rho) :
    (rho * ((1 + r)⁻¹) ^ 2) / (((1 + r)⁻¹) ^ 2) = rho := by
  have hscale : 1 + r ≠ 0 := by
    intro hz
    apply hden
    calc
      1 + rho = (1 + r) ^ 2 := by
        rw [← hr]
        have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
        rw [show (1 + r) ^ 2 = 1 + (2 : k) * r + r ^ 2 by ring, htwo]
        simp
      _ = 0 := by rw [hz]; simp
  field_simp [hscale]

end BoundaryScalars

section BranchMatrix

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
/-- Low and boundary upper-coordinate eliminator.  Its only source-bearing
hypotheses are exactly the three actual consumers
`belowMOddTEven`, `belowMOddTOdd`, and `boundaryOdd`; all other rows are
vacuous either from the absent upper affine coefficient or from the low-range
inequality. -/
theorem wildQuadraticLow_upperCoordinates_of_consumers
    (V : WildQuadraticCommonCoefficientView F K t m)
    (hlow : m ≤ t + 1)
    (hBelowEven : ∀
      (chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .belowMOddTEven chiF)
      (q : CharTwoRefinement (ResidueField F)),
      Nonempty (ActualUpperCoordinateCertificate F K V.correction q
        V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF))
    (hBelowOdd : ∀
      (tau chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .belowMOddTOdd tau chiF)
      (q : CharTwoRefinement (ResidueField F)),
      Nonempty (ActualUpperCoordinateCertificate F K V.correction q
        V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF))
    (hBoundary : ∀
      (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
      (tau chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .boundaryOdd rho hrho hden tau chiF)
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
      simpa only [hI] using hBelowEven chiF hI q
  | belowMOddTOdd tau chiF =>
      simpa only [hI] using hBelowOdd tau chiF hI q
  | boundaryEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | boundaryOdd rho hrho hden tau chiF =>
      simpa only [hI] using hBoundary rho hrho hden tau chiF hI q
  | aboveMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMEvenTOdd tau =>
      have hrange := V.criticalInputs_row
      rw [hI] at hrange
      have hmgt := V.conductor_gt_one
      have hb : m - 1 ≤ t := by omega
      have hnotAbove :
          (WildQuadraticCoefficientRow.ofConductors (m - 1) t).range ≠
            .above := by
        rcases lt_or_eq_of_le hb with hlt | heq
        · rw [WildQuadraticCoefficientRow.ofConductors_range_below hlt]
          decide
        · rw [WildQuadraticCoefficientRow.ofConductors_range_boundary heq]
          decide
      apply (hnotAbove (congrArg WildQuadraticCoefficientRow.range
        hrange).symm).elim
  | aboveMOddTEven chiF =>
      simp [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.affineCoefficient] at haff
  | aboveMOddTOdd tau chiF =>
      have hrange := V.criticalInputs_row
      rw [hI] at hrange
      have hmgt := V.conductor_gt_one
      have hb : m - 1 ≤ t := by omega
      have hnotAbove :
          (WildQuadraticCoefficientRow.ofConductors (m - 1) t).range ≠
            .above := by
        rcases lt_or_eq_of_le hb with hlt | heq
        · rw [WildQuadraticCoefficientRow.ofConductors_range_below hlt]
          decide
        · rw [WildQuadraticCoefficientRow.ofConductors_range_boundary heq]
          decide
      apply (hnotAbove (congrArg WildQuadraticCoefficientRow.range
        hrange).symm).elim

end BranchMatrix

section PrimitiveLowUpperCertificates

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- Assemble the strict-low odd/even upper certificate from the actual
normalized upper and base rows.  The only residual obligations are the
source-theoretic norm-polynomial reduction and the genuine even-tau
linearization at the same twisted unit. -/
noncomputable def wildQuadratic_belowMOddTEven_upperCertificate
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (chiF : QuotientDerivedNormalizedCriticalFunction F)
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
    (chiF_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F chiF S.chiF)
    (chiF_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F chiF chiFData psiF)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (upperLift : ResidueField F → lattice K 0)
    (upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z)
    (upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1)
    (base_mem : ∀ z,
      phaseReductionNormPolynomial F K
          ((upper.delta : K) * (upperLift z : K)) /
            (chiF.delta : F) ∈ lattice F 0)
    (base_reduce : ∀ z,
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiF.delta : F))
          (base_mem z) = z ^ 2)
    (tau_factor : ∀ z,
      stationaryUnitFactor tauData.character psiF S.tau
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) = 1)
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q (.belowMOddTEven chiF) S
      tauData chiFData psiF where
  upper := upper
  upper_pair := upper_pair
  upper_character := upper_character
  upper_additive := upper_additive
  tau := tau
  tau_character := tau_character
  chiK_ratio := chiK_ratio
  chiF_ratio := chiF_ratio
  point := fun z ↦ by
    let x : K := (upper.delta : K) * (upperLift z : K)
    let y : F := phaseReductionNormPolynomial F K x
    have hnorm : ((normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper (upperLift z)) : Fˣ) : F) = 1 + y := by
      simpa only [x, y] using
        wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper (upperLift z)
    have hchi : ActualLowerStationaryCoordinate F (some chiF)
        chiFData psiF S.chiF (z ^ 2)
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper (upperLift z))) :=
      wildQuadratic_actualLowerCritical_of_displacement chiF chiFData psiF
        S.chiF chiF_pair chiF_local (z ^ 2) y (base_mem z) (base_reduce z)
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper (upperLift z))) hnorm
    have htau : ActualLowerStationaryCoordinate F none tauData psiF S.tau 0
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) :=
      .constant rfl (tau_factor z)
    simpa only [WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.belowMOddTEvenComputed,
      WildQuadraticCoefficientData.commonScale,
      WildQuadraticCoefficientData.pTransport,
      WildQuadraticCoefficientData.qTransport,
      WildQuadraticCoefficientData.range,
      WildQuadraticCoefficientData.row,
      WildQuadraticCoefficientRow.range, inv_one, one_mul] using
      (ActualUpperCoordinatePoint.ofTwistedCriticalUnit C S
        (.belowMOddTEven chiF) tauData chiFData psiF upper
          (wildQuadraticResidueEquiv F K C z) (z ^ 2) 0
          (upperLift z) (upper_reduce z) (upper_mem z) hchi htau)

/-- Assemble the strict-low odd/odd upper certificate.  Its tau coordinate
is constructed at the actual post-drop depth and reduces to zero there; no
cancelled value from the old layer is reused. -/
noncomputable def wildQuadratic_belowMOddTOdd_upperCertificate
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW chiF : QuotientDerivedNormalizedCriticalFunction F)
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
    (chiF_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F chiF S.chiF)
    (chiF_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F chiF chiFData psiF)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (upperLift : ResidueField F → lattice K 0)
    (upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z)
    (upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1)
    (base_mem : ∀ z,
      phaseReductionNormPolynomial F K
          ((upper.delta : K) * (upperLift z : K)) /
            (chiF.delta : F) ∈ lattice F 0)
    (base_reduce : ∀ z,
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiF.delta : F))
          (base_mem z) = z ^ 2)
    (tau_mem : ∀ z,
      phaseReductionNormPolynomial F K
          ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F) ∈ lattice F 0)
    (tau_reduce : ∀ z,
      reduce F
          (phaseReductionNormPolynomial F K
              ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F))
          (tau_mem z) = 0)
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q (.belowMOddTOdd tauW chiF) S
      tauData chiFData psiF where
  upper := upper
  upper_pair := upper_pair
  upper_character := upper_character
  upper_additive := upper_additive
  tau := tau
  tau_character := tau_character
  chiK_ratio := chiK_ratio
  chiF_ratio := chiF_ratio
  point := fun z ↦ by
    let x : K := (upper.delta : K) * (upperLift z : K)
    let yBase : F := phaseReductionNormPolynomial F K x
    let yTau : F := phaseReductionNormPolynomial F K ((C.u : K) * x)
    have hnorm : ((normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper (upperLift z)) : Fˣ) : F) = 1 + yBase := by
      simpa only [x, yBase] using
        wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper (upperLift z)
    have hnormTwisted : ((normUnits F K
        (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
          (upper_mem z)) : Fˣ) : F) = 1 + yTau := by
      simpa only [x, yTau] using
        wildQuadratic_norm_twistedCriticalUnit_coe (F := F) C upper
          (upperLift z) (upper_mem z)
    have hchi : ActualLowerStationaryCoordinate F (some chiF)
        chiFData psiF S.chiF (z ^ 2)
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper (upperLift z))) :=
      wildQuadratic_actualLowerCritical_of_displacement chiF chiFData psiF
        S.chiF chiF_pair chiF_local (z ^ 2) yBase (base_mem z)
          (base_reduce z)
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper (upperLift z))) hnorm
    have htau : ActualLowerStationaryCoordinate F (some tauW)
        tauData psiF S.tau 0
          (normUnits F K
            (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
              (upper_mem z))) :=
      wildQuadratic_actualLowerCritical_of_displacement tauW tauData psiF
        S.tau tau_pair tau_local 0 yTau (tau_mem z) (tau_reduce z)
          (normUnits F K
            (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
              (upper_mem z))) hnormTwisted
    simpa only [WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.belowMOddTOddComputed,
      WildQuadraticCoefficientData.commonScale,
      WildQuadraticCoefficientData.pTransport,
      WildQuadraticCoefficientData.qTransport,
      WildQuadraticCoefficientData.range,
      WildQuadraticCoefficientData.row,
      WildQuadraticCoefficientRow.range, inv_one, one_mul] using
      (ActualUpperCoordinatePoint.ofTwistedCriticalUnit C S
        (.belowMOddTOdd tauW chiF) tauData chiFData psiF upper
          (wildQuadraticResidueEquiv F K C z) (z ^ 2) 0
          (upperLift z) (upper_reduce z) (upper_mem z) hchi htau)

/-- Assemble the odd-boundary upper certificate.  Both residual targets
retain the exact common-coordinate scale `1 + sqrt rho`; the tau target is
the base target multiplied by the retained common lower residue `rho`. -/
noncomputable def wildQuadratic_boundaryOdd_upperCertificate
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (rho : ResidueField F) (rho_ne_zero : rho ≠ 0)
    (denominator_ne_zero : 1 + rho ≠ 0)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW chiF : QuotientDerivedNormalizedCriticalFunction F)
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
    (chiF_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F chiF S.chiF)
    (chiF_local :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F chiF chiFData psiF)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (upperLift : ResidueField F → lattice K 0)
    (upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z)
    (upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1)
    (base_mem : ∀ z,
      phaseReductionNormPolynomial F K
          ((upper.delta : K) * (upperLift z : K)) /
            (chiF.delta : F) ∈ lattice F 0)
    (base_reduce : ∀ z,
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiF.delta : F))
          (base_mem z) =
        ((1 + WildQuadraticRefinement.squareRoot rho)⁻¹ * z) ^ 2)
    (tau_mem : ∀ z,
      phaseReductionNormPolynomial F K
          ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F) ∈ lattice F 0)
    (tau_reduce : ∀ z,
      reduce F
          (phaseReductionNormPolynomial F K
              ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F))
          (tau_mem z) =
        rho * ((1 + WildQuadraticRefinement.squareRoot rho)⁻¹ * z) ^ 2)
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q
      (.boundaryOdd rho rho_ne_zero denominator_ne_zero tauW chiF) S
        tauData chiFData psiF where
  upper := upper
  upper_pair := upper_pair
  upper_character := upper_character
  upper_additive := upper_additive
  tau := tau
  tau_character := tau_character
  chiK_ratio := chiK_ratio
  chiF_ratio := chiF_ratio
  point := fun z ↦ by
    let x : K := (upper.delta : K) * (upperLift z : K)
    let yBase : F := phaseReductionNormPolynomial F K x
    let yTau : F := phaseReductionNormPolynomial F K ((C.u : K) * x)
    let pz : ResidueField F :=
      ((1 + WildQuadraticRefinement.squareRoot rho)⁻¹ * z) ^ 2
    let qz : ResidueField F := rho * pz
    have hnorm : ((normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper (upperLift z)) : Fˣ) : F) = 1 + yBase := by
      simpa only [x, yBase] using
        wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper (upperLift z)
    have hnormTwisted : ((normUnits F K
        (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
          (upper_mem z)) : Fˣ) : F) = 1 + yTau := by
      simpa only [x, yTau] using
        wildQuadratic_norm_twistedCriticalUnit_coe (F := F) C upper
          (upperLift z) (upper_mem z)
    have hchi : ActualLowerStationaryCoordinate F (some chiF)
        chiFData psiF S.chiF pz
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper (upperLift z))) :=
      wildQuadratic_actualLowerCritical_of_displacement chiF chiFData psiF
        S.chiF chiF_pair chiF_local pz yBase (base_mem z)
          (by simpa only [pz] using base_reduce z)
          (normUnits F K
            (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
              upper (upperLift z))) hnorm
    have htau : ActualLowerStationaryCoordinate F (some tauW)
        tauData psiF S.tau qz
          (normUnits F K
            (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
              (upper_mem z))) :=
      wildQuadratic_actualLowerCritical_of_displacement tauW tauData psiF
        S.tau tau_pair tau_local qz yTau (tau_mem z)
          (by simpa only [qz, pz] using tau_reduce z)
          (normUnits F K
            (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
              (upper_mem z))) hnormTwisted
    simpa only [WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.commonScale,
      WildQuadraticCoefficientData.pTransport,
      WildQuadraticCoefficientData.qTransport,
      WildQuadraticCoefficientData.range,
      WildQuadraticCoefficientData.row,
      WildQuadraticCoefficientRow.range, pz, qz] using
      (ActualUpperCoordinatePoint.ofTwistedCriticalUnit C S
        (.boundaryOdd rho rho_ne_zero denominator_ne_zero tauW chiF)
          tauData chiFData psiF upper
          (wildQuadraticResidueEquiv F K C z) pz qz
          (upperLift z) (upper_reduce z) (upper_mem z) hchi htau)

end PrimitiveLowUpperCertificates

section NormalizedUpperLift

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- The lower residue scalar of the exact source-to-normalized upper
coordinate. -/
noncomputable def wildQuadratic_lowUpperTransportScalar
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    {d : ℕ} (delta : Kˣ)
    (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ)) :
    ResidueField F :=
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    (((residueUnits K
      (PhaseReductionResidualCoordinateSource.transportUnit
        (LamprechtCriticalCoordinate.odd delta hdelta)
        S.upperUniformizer S.upper_order) : (ResidueField K)ˣ) :
          ResidueField K))

/-- Undo the source-to-normalized unit in the lift while multiplying its
Teichmüller argument by the same residue.  The normalized lift therefore
still reduces to the requested upper residue coordinate, while its exact
field displacement is in the original PhaseReduction source coordinate. -/
noncomputable def wildQuadratic_lowNormalizedUpperLift
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    {d : ℕ} (delta : Kˣ)
    (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ))
    (z : ResidueField F) : lattice K 0 := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a := PhaseReductionResidualCoordinateSource.transportUnit
    (LamprechtCriticalCoordinate.odd delta hdelta)
      S.upperUniformizer S.upper_order
  let s := wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta
  let aInv : unitGroup K := a⁻¹
  let aInvK : K := ((aInv : Kˣ) : K)
  let tzK : K := algebraMap F K (teichmuller F (s * z) : F)
  have haInv : aInvK ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2
      (((unitGroupMulEquivRingOfIntegers K aInv : (ringOfIntegers K)ˣ) :
        ringOfIntegers K).property)
  have htz : tzK ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)
        (teichmuller F (s * z))).property
  exact ⟨aInvK * tzK, mul_mem_lattice K haInv htz⟩


theorem wildQuadratic_lowNormalizedUpperLift_reduce
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    {d : ℕ} (delta : Kˣ)
    (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    reduce K
        (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi delta hdelta z : K)
        (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi delta hdelta z).property =
      PhaseReductionResidualCoordinateSource.residueEquiv hres z := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a := PhaseReductionResidualCoordinateSource.transportUnit
    (LamprechtCriticalCoordinate.odd delta hdelta)
      S.upperUniformizer S.upper_order
  let sK : ResidueField K :=
    ((residueUnits K a : (ResidueField K)ˣ) : ResidueField K)
  let s := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm sK
  change residueMap K
      (((unitGroupMulEquivRingOfIntegers K (a⁻¹) :
          (ringOfIntegers K)ˣ) : ringOfIntegers K) *
        algebraMap (ringOfIntegers F) (ringOfIntegers K)
          (teichmuller F (s * z))) = _
  rw [map_mul, ← residueUnits_coe, map_inv, Units.val_inv_eq_inv_val]
  have halg : residueMap K
      (algebraMap (ringOfIntegers F) (ringOfIntegers K)
        (teichmuller F (s * z))) =
      PhaseReductionResidualCoordinateSource.residueEquiv hres (s * z) := by
    rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
    calc
      _ = extensionResidueMap F K
          (residueMap F (teichmuller F (s * z))) :=
        (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
          (ValuativeRel.valuation F) (ValuativeRel.valuation K)
            (teichmuller F (s * z))).symm
      _ = _ := congrArg (extensionResidueMap F K)
        (residueMap_teichmuller F (s * z))
  rw [halg]
  change sK⁻¹ *
      PhaseReductionResidualCoordinateSource.residueEquiv hres (s * z) =
    PhaseReductionResidualCoordinateSource.residueEquiv hres z
  rw [map_mul]
  have hs : PhaseReductionResidualCoordinateSource.residueEquiv hres s =
      sK :=
    (PhaseReductionResidualCoordinateSource.residueEquiv hres).apply_symm_apply sK
  rw [hs]
  calc
    sK⁻¹ * (sK * PhaseReductionResidualCoordinateSource.residueEquiv hres z) =
        (sK⁻¹ * sK) *
          PhaseReductionResidualCoordinateSource.residueEquiv hres z := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ (Units.ne_zero (residueUnits K a)), one_mul]

theorem wildQuadratic_lowNormalizedUpperLift_displacement
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    {d : ℕ} (delta : Kˣ)
    (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    (delta : K) *
        (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi delta hdelta z : K) =
      phaseReductionUpperSourceDisplacement F K pi d
        (wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta * z) := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a := PhaseReductionResidualCoordinateSource.transportUnit
    (LamprechtCriticalCoordinate.odd delta hdelta)
      S.upperUniformizer S.upper_order
  have hscaled := PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq
    delta hdelta S.upperUniformizer S.upper_order
  have hdeltaEq : (delta : K) = (a : Kˣ) *
      (phaseReductionSourceCoordinate K S.upperUniformizer d : K) := by
    simpa only [criticalPolarScaledCoordinate, Units.val_mul] using
      congrArg (Units.val : Kˣ → K) hscaled.symm
  have hlift :
      (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi delta hdelta z : K) =
        (((a⁻¹ : unitGroup K) : Kˣ) : K) *
          algebraMap F K
            (teichmuller F
              (wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta * z) : F) := by
    rfl
  rw [hlift, hdeltaEq]
  calc
    ((a : Kˣ) : K) *
          (phaseReductionSourceCoordinate K S.upperUniformizer d : K) *
        ((((a⁻¹ : unitGroup K) : Kˣ) : K) *
          algebraMap F K
            (teichmuller F
              (wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta * z) : F)) =
        (phaseReductionSourceCoordinate K S.upperUniformizer d : K) *
          algebraMap F K
            (teichmuller F
              (wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta * z) : F) := by
      have haUnit : (a : Kˣ) * ((a⁻¹ : unitGroup K) : Kˣ) = 1 := by
        exact congrArg (fun b : unitGroup K ↦ (b : Kˣ)) (mul_inv_cancel a)
      have haVal : ((a : Kˣ) : K) *
          ((((a⁻¹ : unitGroup K) : Kˣ) : K)) = 1 :=
        congrArg (Units.val : Kˣ → K) haUnit
      calc
        _ = (((a : Kˣ) : K) *
              ((((a⁻¹ : unitGroup K) : Kˣ) : K))) *
            ((phaseReductionSourceCoordinate K S.upperUniformizer d : K) *
              algebraMap F K
                (teichmuller F
                  (wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta * z) : F)) := by
              ring
        _ = _ := by rw [haVal, one_mul]
    _ = phaseReductionUpperSourceDisplacement F K pi d
          (wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta * z) := by
      unfold phaseReductionUpperSourceDisplacement
        phaseReductionSourceCoordinate S phaseReductionResidualCoordinateSource
      simp only [Units.val_pow_eq_pow_val]
      change (pi : K) ^ d * _ = _ * (pi : K) ^ d
      ring

end NormalizedUpperLift

section ScaledLowerReduction

variable (F : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]

/-- Exact denominator membership for a depth-`d` displacement divided by
any actual normalized depth-`d` critical coordinate. -/
theorem wildQuadratic_lowScaledLowerDiv_mem
    {d : ℕ} (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (y : F) (hy : y ∈ lattice F (d : ℤ)) :
    y / (delta : F) ∈ lattice F 0 := by
  exact (div_mem_lattice_iff F (delta : F) y (d : ℤ) 0 hdelta).2
    (by simpa using hy)

/-- Changing the lower source denominator by its exact integral unit scales
the residual class by the inverse of that unit's residue. -/
theorem wildQuadratic_lowScaledLowerDiv_reduce
    {d : ℕ} (varpi : Fˣ)
    (hvarpi : ord F (varpi : F) = ((1 : ℤ) : WithTop ℤ))
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (y : F) (hy : y ∈ lattice F (d : ℤ))
    (w : ResidueField F)
    (hclass : phaseReductionResidualClass F varpi hvarpi d
      ⟨y, hy⟩ = w) :
    reduce F (y / (delta : F))
        (wildQuadratic_lowScaledLowerDiv_mem F delta hdelta y hy) =
      (PhaseReductionResidualCoordinateSource.transportScalar
          (LamprechtCriticalCoordinate.odd delta hdelta) varpi hvarpi)⁻¹ * w := by
  let source := phaseReductionSourceCoordinate F varpi d
  let a := PhaseReductionResidualCoordinateSource.transportUnit
    (LamprechtCriticalCoordinate.odd delta hdelta) varpi hvarpi
  let aInv : unitGroup F := a⁻¹
  have hscaled := PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq
    delta hdelta varpi hvarpi
  have hdeltaEq : (delta : F) = ((a : Fˣ) : F) * (source : F) := by
    simpa only [criticalPolarScaledCoordinate, Units.val_mul, source] using
      congrArg (Units.val : Fˣ → F) hscaled.symm
  have hsourceOrd : ord F (source : F) = ((d : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F varpi hvarpi d
  have hySource : y / (source : F) ∈ lattice F 0 :=
    (div_mem_lattice_iff F (source : F) y (d : ℤ) 0 hsourceOrd).2
      (by simpa using hy)
  have haInv : ((aInv : Fˣ) : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2
      (((unitGroupMulEquivRingOfIntegers F aInv : (ringOfIntegers F)ˣ) :
        ringOfIntegers F).property)
  have hprod : ((aInv : Fˣ) : F) * (y / (source : F)) ∈ lattice F 0 :=
    mul_mem_lattice F haInv hySource
  have heq : y / (delta : F) =
      ((aInv : Fˣ) : F) * (y / (source : F)) := by
    rw [hdeltaEq]
    change y / (((a : Fˣ) : F) * (source : F)) =
      ((((a⁻¹ : unitGroup F) : Fˣ) : F)) * (y / (source : F))
    have haInvVal : ((((a⁻¹ : unitGroup F) : Fˣ) : F)) =
        (((a : Fˣ) : F))⁻¹ := by
      have hu : ((a⁻¹ : unitGroup F) : Fˣ) = (a : Fˣ)⁻¹ := by
        apply Units.ext
        rfl
      rw [hu, Units.val_inv_eq_inv_val]
    rw [haInvVal]
    field_simp [Units.ne_zero (a : Fˣ), Units.ne_zero source]
  have hreduceEq :
      reduce F (y / (delta : F))
          (wildQuadratic_lowScaledLowerDiv_mem F delta hdelta y hy) =
        reduce F (((aInv : Fˣ) : F) * (y / (source : F))) hprod := by
    apply (reduce_eq_reduce_iff (F := F) _ _).2
    rw [congruentAtDepth_iff_sub_mem_lattice, heq, sub_self]
    exact zero_mem _
  rw [hreduceEq]
  have haReduce :
      reduce F ((aInv : Fˣ) : F) haInv =
        (PhaseReductionResidualCoordinateSource.transportScalar
          (LamprechtCriticalCoordinate.odd delta hdelta) varpi hvarpi)⁻¹ := by
    change residueMap F
        (unitGroupMulEquivRingOfIntegers F aInv : ringOfIntegers F) = _
    rw [← residueUnits_coe]
    change (((residueUnits F (a⁻¹) : (ResidueField F)ˣ) :
      ResidueField F)) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  have hyReduce : reduce F (y / (source : F)) hySource = w := by
    simpa only [phaseReductionResidualClass, source,
      phaseReductionSourceCoordinate, Units.val_pow_eq_pow_val] using hclass
  have hmul : reduce F (((aInv : Fˣ) : F) * (y / (source : F))) hprod =
      reduce F ((aInv : Fˣ) : F) haInv *
        reduce F (y / (source : F)) hySource := by
    change residueMap F
      ((⟨((aInv : Fˣ) : F), (mem_lattice_zero_iff F).1 haInv⟩ :
          ringOfIntegers F) *
        ⟨y / (source : F), (mem_lattice_zero_iff F).1 hySource⟩) = _
    rw [map_mul]
    rfl
  rw [hmul, haReduce, hyReduce]

end ScaledLowerReduction

section LowBaseCoordinate

variable (F K : Type)
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

theorem wildQuadratic_lowUpperTransportScalar_ne_zero
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    {d : ℕ} (delta : Kˣ)
    (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ)) :
    wildQuadratic_lowUpperTransportScalar F K hres pi hpi delta hdelta ≠ 0 := by
  unfold wildQuadratic_lowUpperTransportScalar
  intro hz
  have hz' := congrArg
    (PhaseReductionResidualCoordinateSource.residueEquiv hres) hz
  rw [(PhaseReductionResidualCoordinateSource.residueEquiv hres).apply_symm_apply,
    map_zero] at hz'
  exact Units.ne_zero _ hz'

/-- Raw normalized-base coordinate before the polar-law scalar gate.  Both
normalization scalars are those of the actual selected rows. -/
theorem wildQuadratic_lowBaseCoordinate_raw
    {t d : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (upperDelta : Kˣ)
    (hupperDelta : ord K (upperDelta : K) = ((d : ℤ) : WithTop ℤ))
    (baseDelta : Fˣ)
    (hbaseDelta : ord F (baseDelta : F) = ((d : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    ∃ hmem : phaseReductionNormPolynomial F K
          ((upperDelta : K) *
            (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
              hupperDelta z : K)) /
            (baseDelta : F) ∈ lattice F 0,
      reduce F
          (phaseReductionNormPolynomial F K
              ((upperDelta : K) *
                (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
                  hupperDelta z : K)) /
            (baseDelta : F)) hmem =
        ((PhaseReductionResidualCoordinateSource.transportScalar
            (LamprechtCriticalCoordinate.odd baseDelta hbaseDelta)
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)⁻¹ *
          wildQuadratic_lowUpperTransportScalar F K hres pi hpi upperDelta
              hupperDelta ^ 2) * z ^ 2 := by
  let s := wildQuadratic_lowUpperTransportScalar F K hres pi hpi upperDelta
    hupperDelta
  let w : ResidueField F := s * z
  let x := phaseReductionUpperSourceDisplacement F K pi d w
  have hdisp : (upperDelta : K) *
      (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
        hupperDelta z : K) = x :=
    wildQuadratic_lowNormalizedUpperLift_displacement F K hres pi hpi upperDelta
      hupperDelta z
  have hxDepth : x ∈ lattice K (d : ℤ) :=
    phaseReductionUpperSourceDisplacement_mem F K pi hpi d w
  have hy : phaseReductionNormPolynomial F K x ∈ lattice F (d : ℤ) := by
    change norm F K (1 + x) - 1 ∈ lattice F (d : ℤ)
    exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos (by omega)
      hres (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen) pi hpi hgen x (by
          change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x
          simpa only [mem_lattice] using hxDepth)
  have hclass := phaseReductionLowBaseResidualClass F K ht htpos hd hres pi
    hpi hgen w
  have hclass' : phaseReductionResidualClass F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d
      ⟨phaseReductionNormPolynomial F K x, hy⟩ = w ^ 2 := by
    rw [hdegree] at hclass
    change phaseReductionResidualClass F
      (phaseReductionLowerUniformizer F K pi hpi)
      (phaseReductionLowerUniformizer_order F K hres pi hpi) d
        ⟨phaseReductionNormPolynomial F K x, hy⟩ = w ^ 2
    simpa only [phaseReductionNormPolynomial_eq_normPolynomialValue, x] using hclass
  let hmem := wildQuadratic_lowScaledLowerDiv_mem F baseDelta hbaseDelta
    (phaseReductionNormPolynomial F K x) hy
  refine ⟨by simpa only [hdisp] using hmem, ?_⟩
  have hreduce := wildQuadratic_lowScaledLowerDiv_reduce F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      baseDelta hbaseDelta (phaseReductionNormPolynomial F K x) hy (w ^ 2)
        hclass'
  have halgebra :
      (PhaseReductionResidualCoordinateSource.transportScalar
          (LamprechtCriticalCoordinate.odd baseDelta hbaseDelta)
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)⁻¹ *
        w ^ 2 =
      ((PhaseReductionResidualCoordinateSource.transportScalar
          (LamprechtCriticalCoordinate.odd baseDelta hbaseDelta)
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)⁻¹ *
        s ^ 2) * z ^ 2 := by
    dsimp only [w]
    ring
  simpa only [hdisp, s] using hreduce.trans halgebra



end LowBaseCoordinate

section LowTauCoordinates

variable (F K : Type)
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

/-- Positive-depth of the selected twisted upper displacement, proved from
the actual normalized upper delta and an arbitrary integral lift. -/
theorem wildQuadratic_lowTwistedDisplacement_mem_one
    {d a : ℕ} (u : K) (hu : ord K u = ((a : ℤ) : WithTop ℤ))
    (delta : Kˣ)
    (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ))
    (had : 1 ≤ a + d) (lift : lattice K 0) :
    u * ((delta : K) * (lift : K)) ∈ lattice K 1 := by
  have hlift := lift.property
  rw [mem_lattice] at hlift
  rw [mem_lattice, ord_mul, ord_mul, hu, hdelta]
  calc
    ((1 : ℤ) : WithTop ℤ) ≤ (((a + d : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast had
    _ = ((a : ℤ) : WithTop ℤ) + (((d : ℤ) : WithTop ℤ) + 0) := by
      norm_num
    _ ≤ ((a : ℤ) : WithTop ℤ) +
        (((d : ℤ) : WithTop ℤ) + ord K (lift : K)) := by
      gcongr
      simpa using hlift

/-- Strict-low odd/odd tau coordinate at the actual post-drop depth. -/
theorem wildQuadratic_lowStrictTauCoordinate
    {t d dTau a : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hstrict : 2 * d < t)
    (htau : t = 2 * dTau) (ha : a + 2 * d = t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : K) (hu : ord K u = ((a : ℤ) : WithTop ℤ))
    (upperDelta : Kˣ)
    (hupperDelta : ord K (upperDelta : K) = ((d : ℤ) : WithTop ℤ))
    (tauDelta : Fˣ)
    (htauDelta : ord F (tauDelta : F) = ((dTau : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    ∃ hmem : phaseReductionNormPolynomial F K
          (u * ((upperDelta : K) *
            (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
              hupperDelta z : K))) /
            (tauDelta : F) ∈ lattice F 0,
      reduce F
          (phaseReductionNormPolynomial F K
              (u * ((upperDelta : K) *
                (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
                  hupperDelta z : K))) /
            (tauDelta : F)) hmem = 0 := by
  let s := wildQuadratic_lowUpperTransportScalar F K hres pi hpi upperDelta
    hupperDelta
  let w : ResidueField F := s * z
  let x := phaseReductionUpperSourceDisplacement F K pi d w
  have hdisp : (upperDelta : K) *
      (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
        hupperDelta z : K) = x :=
    wildQuadratic_lowNormalizedUpperLift_displacement F K hres pi hpi upperDelta
      hupperDelta z
  have hdeep : phaseReductionNormPolynomial F K (u * x) ∈
      lattice F ((dTau + 1 : ℕ) : ℤ) := by
    simpa only [phaseReductionNormPolynomial_eq_normPolynomialValue] using
      phaseReductionLowStrictTauPolynomial_deep F K ht htpos hstrict htau ha
        hres pi hpi hgen u hu w
  have hy : phaseReductionNormPolynomial F K (u * x) ∈
      lattice F (dTau : ℤ) :=
    lattice_antitone F (by omega) hdeep
  have hclass : phaseReductionResidualClass F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      dTau ⟨phaseReductionNormPolynomial F K (u * x), hy⟩ = 0 := by
    exact phaseReductionResidualClass_eq_zero_of_mem_succ F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
        dTau ⟨phaseReductionNormPolynomial F K (u * x), hy⟩ hdeep
  let hmem := wildQuadratic_lowScaledLowerDiv_mem F tauDelta htauDelta
    (phaseReductionNormPolynomial F K (u * x)) hy
  refine ⟨by simpa only [hdisp] using hmem, ?_⟩
  have hreduce := wildQuadratic_lowScaledLowerDiv_reduce F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      tauDelta htauDelta (phaseReductionNormPolynomial F K (u * x)) hy 0
        hclass
  simpa only [hdisp, mul_zero] using hreduce

/-- Boundary odd tau coordinate before rewriting its scalar through the
retained `rho` source.  This exposes exactly the three factors that must be
identified: normalized tau scale, selected-unit norm residue, and normalized
upper scale. -/
theorem wildQuadratic_lowBoundaryTauCoordinate_raw
    {t d : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (u : Kˣ) (hu : ord K (u : K) = (0 : WithTop ℤ))
    (upperDelta : Kˣ)
    (hupperDelta : ord K (upperDelta : K) = ((d : ℤ) : WithTop ℤ))
    (tauDelta : Fˣ)
    (htauDelta : ord F (tauDelta : F) = ((d : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    ∃ hmem : phaseReductionNormPolynomial F K
          ((u : K) * ((upperDelta : K) *
            (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
              hupperDelta z : K))) /
            (tauDelta : F) ∈ lattice F 0,
      reduce F
          (phaseReductionNormPolynomial F K
              ((u : K) * ((upperDelta : K) *
                (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
                  hupperDelta z : K))) /
            (tauDelta : F)) hmem =
        (PhaseReductionResidualCoordinateSource.transportScalar
            (LamprechtCriticalCoordinate.odd tauDelta htauDelta)
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
            (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order)⁻¹ *
          residueMap F
            (⟨norm F K (u : K), by
              rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
                one_nsmul, hu]
              exact le_rfl⟩ : ringOfIntegers F) *
          (wildQuadratic_lowUpperTransportScalar F K hres pi hpi upperDelta
            hupperDelta * z) ^ 2 := by
  let s := wildQuadratic_lowUpperTransportScalar F K hres pi hpi upperDelta
    hupperDelta
  let w : ResidueField F := s * z
  let x := phaseReductionUpperSourceDisplacement F K pi d w
  have hdisp : (upperDelta : K) *
      (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upperDelta
        hupperDelta z : K) = x :=
    wildQuadratic_lowNormalizedUpperLift_displacement F K hres pi hpi upperDelta
      hupperDelta z
  have hxDepth : x ∈ lattice K (d : ℤ) :=
    phaseReductionUpperSourceDisplacement_mem F K pi hpi d w
  have huxDepth : (u : K) * x ∈ lattice K (d : ℤ) := by
    rw [mem_lattice, ord_mul, hu]
    simpa only [zero_add, mem_lattice] using hxDepth
  have hy : phaseReductionNormPolynomial F K ((u : K) * x) ∈
      lattice F (d : ℤ) := by
    change norm F K (1 + (u : K) * x) - 1 ∈ lattice F (d : ℤ)
    exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos (by omega)
      hres (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen) pi hpi hgen ((u : K) * x) (by
          change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K ((u : K) * x)
          simpa only [mem_lattice] using huxDepth)
  have hclass := phaseReductionLowBoundaryTauResidualClass F K ht hres pi
    hpi hgen htpos hd u hu w hy
  have hclass' : phaseReductionResidualClass F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d
      ⟨phaseReductionNormPolynomial F K ((u : K) * x), hy⟩ =
        residueMap F
            (⟨norm F K (u : K), by
              rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
                one_nsmul, hu]
              exact le_rfl⟩ : ringOfIntegers F) * w ^ 2 := by
    rw [hdegree] at hclass
    simpa only [w] using hclass
  let hmem := wildQuadratic_lowScaledLowerDiv_mem F tauDelta htauDelta
    (phaseReductionNormPolynomial F K ((u : K) * x)) hy
  refine ⟨by simpa only [hdisp] using hmem, ?_⟩
  have hreduce := wildQuadratic_lowScaledLowerDiv_reduce F
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
    (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
      tauDelta htauDelta (phaseReductionNormPolynomial F K ((u : K) * x))
        hy _ hclass'
  simpa only [hdisp, w, mul_assoc] using hreduce

end LowTauCoordinates

section BoundaryScalarIdentities

variable (F : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]

/-- A retained exact scaling between two normalized lower deltas induces
the same scaling between their source-relative residual transport scalars. -/
theorem wildQuadratic_transportScalar_eq_mul_of_coordinate_eq
    {d : ℕ} (varpi : Fˣ)
    (hvarpi : ord F (varpi : F) = ((1 : ℤ) : WithTop ℤ))
    (tauDelta chiDelta : Fˣ)
    (htauDelta : ord F (tauDelta : F) = ((d : ℤ) : WithTop ℤ))
    (hchiDelta : ord F (chiDelta : F) = ((d : ℤ) : WithTop ℤ))
    (rhoLift : unitGroup F)
    (hcoordinate : tauDelta =
      criticalPolarScaledCoordinate F rhoLift chiDelta) :
    PhaseReductionResidualCoordinateSource.transportScalar
        (LamprechtCriticalCoordinate.odd tauDelta htauDelta) varpi hvarpi =
      ((residueUnits F rhoLift : (ResidueField F)ˣ) : ResidueField F) *
        PhaseReductionResidualCoordinateSource.transportScalar
          (LamprechtCriticalCoordinate.odd chiDelta hchiDelta) varpi hvarpi := by
  let aTau := PhaseReductionResidualCoordinateSource.transportUnit
    (LamprechtCriticalCoordinate.odd tauDelta htauDelta) varpi hvarpi
  let aChi := PhaseReductionResidualCoordinateSource.transportUnit
    (LamprechtCriticalCoordinate.odd chiDelta hchiDelta) varpi hvarpi
  have ha : aTau = rhoLift * aChi := by
    apply Subtype.ext
    dsimp only [aTau, aChi]
    rw [Subgroup.coe_mul]
    rw [PhaseReductionResidualCoordinateSource.transportUnit_odd_coe,
      PhaseReductionResidualCoordinateSource.transportUnit_odd_coe]
    change tauDelta / phaseReductionSourceCoordinate F varpi d =
      (rhoLift : Fˣ) *
        (chiDelta / phaseReductionSourceCoordinate F varpi d)
    rw [hcoordinate]
    simp only [criticalPolarScaledCoordinate]
    rw [mul_div_assoc]
  have hr := congrArg
    (fun b : unitGroup F ↦
      ((residueUnits F b : (ResidueField F)ˣ) : ResidueField F)) ha
  simpa only [aTau, aChi, map_mul, Units.val_mul,
    PhaseReductionResidualCoordinateSource.transportScalar] using hr

end BoundaryScalarIdentities

section NormalizedLowScalarGates

private theorem wildQuadratic_low_absoluteTraceChar_ringEquiv
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

private noncomputable def wildQuadratic_low_pullbackCriticalPolarFunction
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
      (wildQuadratic_low_absoluteTraceChar_ringEquiv e (x * y))

/-- A normalized upper function and normalized lower function related by a
pure Frobenius-square coordinate have no residual scalar freedom. -/
theorem wildQuadratic_low_normalizedScalar_eq_one
    {k : Type} [Field k] [Fintype k] [CharP k 2]
    (upper base : CriticalPolarFunction k (absoluteTraceChar k) 1)
    (lambda : k)
    (htransport : ∀ z : k, upper z = base (lambda * z ^ 2)) :
    lambda = 1 := by
  have hpolar (x y : k) :
      absoluteTraceChar k (x * y) =
        absoluteTraceChar k (lambda * (x * y)) := by
    have hu := upper.map_add x y
    have hb := base.map_add (lambda * x ^ 2) (lambda * y ^ 2)
    rw [htransport (x + y), htransport x, htransport y] at hu
    have hsq : (x + y) ^ 2 = x ^ 2 + y ^ 2 := CharTwo.add_sq x y
    rw [hsq, mul_add, hb] at hu
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
    rw [hsquare] at hu
    have hcommon_ne : base (lambda * x ^ 2) *
        base (lambda * y ^ 2) ≠ 0 :=
      mul_ne_zero (base.ne_zero _) (base.ne_zero _)
    exact (mul_left_cancel₀ hcommon_ne hu).symm
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (AddChar.IsPrimitive.of_ne_one (absoluteTraceChar_ne_one k))
  apply AddChar.ext
  intro z
  simp only [AddChar.mulShift_apply, one_mul]
  simpa only [one_mul] using (hpolar 1 z).symm

/-- Residue-field form of `wildQuadratic_low_normalizedScalar_eq_one`. -/
theorem wildQuadratic_low_normalizedScalar_eq_one_of_residueEquiv
    {k k' : Type} [Field k] [Fintype k] [CharP k 2]
    [Field k'] [Fintype k'] [CharP k' 2]
    (e : k ≃+* k')
    (upper : CriticalPolarFunction k' (absoluteTraceChar k') 1)
    (base : CriticalPolarFunction k (absoluteTraceChar k) 1)
    (lambda : k)
    (htransport : ∀ z : k, upper (e z) = base (lambda * z ^ 2)) :
    lambda = 1 := by
  exact wildQuadratic_low_normalizedScalar_eq_one
    (wildQuadratic_low_pullbackCriticalPolarFunction e upper) base lambda htransport

/-- At the odd boundary, the two normalized lower square-coordinate
scalars add to the normalized upper scalar one. -/
theorem wildQuadratic_boundary_normalizedScalars_add_eq_one
    {k : Type} [Field k] [Fintype k] [CharP k 2]
    (upper base tau : CriticalPolarFunction k (absoluteTraceChar k) 1)
    (lambda mu : k)
    (htransport : ∀ z : k,
      upper z = base (lambda * z ^ 2) * (tau (mu * z ^ 2))⁻¹) :
    lambda + mu = 1 := by
  have hpolar (x y : k) :
      absoluteTraceChar k (x * y) =
        absoluteTraceChar k ((lambda + mu) * (x * y)) := by
    have hu := upper.map_add x y
    have hb := base.map_add (lambda * x ^ 2) (lambda * y ^ 2)
    have ht := tau.map_add (mu * x ^ 2) (mu * y ^ 2)
    rw [htransport (x + y), htransport x, htransport y] at hu
    have hsq : (x + y) ^ 2 = x ^ 2 + y ^ 2 := CharTwo.add_sq x y
    rw [hsq, mul_add, mul_add, hb, ht] at hu
    simp only [one_mul] at hu
    have hcommon_ne :
        base (lambda * x ^ 2) * base (lambda * y ^ 2) *
            (tau (mu * x ^ 2))⁻¹ * (tau (mu * y ^ 2))⁻¹ ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (base.ne_zero _) (base.ne_zero _))
          (inv_ne_zero (tau.ne_zero _)))
        (inv_ne_zero (tau.ne_zero _))
    have hphase :
        absoluteTraceChar k
              ((lambda * x ^ 2) * (lambda * y ^ 2)) *
            (absoluteTraceChar k
              ((mu * x ^ 2) * (mu * y ^ 2)))⁻¹ =
          absoluteTraceChar k (x * y) := by
      apply mul_left_cancel₀ hcommon_ne
      calc
        (base (lambda * x ^ 2) * base (lambda * y ^ 2) *
              (tau (mu * x ^ 2))⁻¹ * (tau (mu * y ^ 2))⁻¹) *
            (absoluteTraceChar k
                ((lambda * x ^ 2) * (lambda * y ^ 2)) *
              (absoluteTraceChar k
                ((mu * x ^ 2) * (mu * y ^ 2)))⁻¹) =
            base (lambda * x ^ 2) * base (lambda * y ^ 2) *
                absoluteTraceChar k
                  ((lambda * x ^ 2) * (lambda * y ^ 2)) *
              (tau (mu * x ^ 2) * tau (mu * y ^ 2) *
                absoluteTraceChar k
                  ((mu * x ^ 2) * (mu * y ^ 2)))⁻¹ := by
              simp only [mul_inv_rev]
              ring
        _ = (base (lambda * x ^ 2) * (tau (mu * x ^ 2))⁻¹) *
              (base (lambda * y ^ 2) * (tau (mu * y ^ 2))⁻¹) *
                absoluteTraceChar k (x * y) := hu
        _ = (base (lambda * x ^ 2) * base (lambda * y ^ 2) *
              (tau (mu * x ^ 2))⁻¹ * (tau (mu * y ^ 2))⁻¹) *
                absoluteTraceChar k (x * y) := by ring
    have hlambda :
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
    have hmu :
        absoluteTraceChar k ((mu * x ^ 2) * (mu * y ^ 2)) =
          absoluteTraceChar k (mu * (x * y)) := by
      calc
        absoluteTraceChar k ((mu * x ^ 2) * (mu * y ^ 2)) =
            absoluteTraceChar k ((mu * (x * y)) ^ 2) := by
              congr 1
              ring
        _ = absoluteTraceChar k (mu * (x * y)) :=
          absoluteTraceChar_sq k _
    have hinv :
        (absoluteTraceChar k (mu * (x * y)))⁻¹ =
          absoluteTraceChar k (mu * (x * y)) := by
      calc
        (absoluteTraceChar k (mu * (x * y)))⁻¹ =
            absoluteTraceChar k (-(mu * (x * y))) :=
          (AddChar.map_neg_eq_inv (absoluteTraceChar k) _).symm
        _ = absoluteTraceChar k (mu * (x * y)) := by
          rw [CharTwo.neg_eq]
    rw [hlambda, hmu, hinv] at hphase
    calc
      absoluteTraceChar k (x * y) =
          absoluteTraceChar k (lambda * (x * y)) *
            absoluteTraceChar k (mu * (x * y)) := hphase.symm
      _ = absoluteTraceChar k ((lambda + mu) * (x * y)) := by
        rw [← (absoluteTraceChar k).map_add_eq_mul]
        congr 1
        ring
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (AddChar.IsPrimitive.of_ne_one (absoluteTraceChar_ne_one k))
  apply AddChar.ext
  intro z
  simp only [AddChar.mulShift_apply, one_mul]
  simpa only [one_mul] using (hpolar 1 z).symm

theorem wildQuadratic_boundary_normalizedScalars_add_eq_one_of_residueEquiv
    {k k' : Type} [Field k] [Fintype k] [CharP k 2]
    [Field k'] [Fintype k'] [CharP k' 2]
    (e : k ≃+* k')
    (upper : CriticalPolarFunction k' (absoluteTraceChar k') 1)
    (base tau : CriticalPolarFunction k (absoluteTraceChar k) 1)
    (lambda mu : k)
    (htransport : ∀ z : k,
      upper (e z) = base (lambda * z ^ 2) * (tau (mu * z ^ 2))⁻¹) :
    lambda + mu = 1 := by
  exact wildQuadratic_boundary_normalizedScalars_add_eq_one
    (wildQuadratic_low_pullbackCriticalPolarFunction e upper) base tau lambda mu
      htransport

/-- Boundary algebra converting the retained `rho` relation into the exact
two coefficient-table scalars. -/
theorem wildQuadratic_boundary_normalizedScalars
    {k : Type} [Field k] [CharP k 2]
    (lambda mu rho r : k)
    (hsum : lambda + mu = 1)
    (hmu : mu = rho * lambda)
    (hsquare : r ^ 2 = rho)
    (hden : 1 + rho ≠ 0) :
    lambda = ((1 + r)⁻¹) ^ 2 ∧
      mu = rho * ((1 + r)⁻¹) ^ 2 := by
  have hdenSquare : (1 + r) ^ 2 = 1 + rho := by
    rw [CharTwo.add_sq, one_pow, hsquare]
  have hdenr : 1 + r ≠ 0 := by
    intro hz
    apply hden
    rw [← hdenSquare, hz]
    norm_num
  have hlinear : lambda + rho * lambda = 1 := by
    rw [← hmu]
    exact hsum
  have hfactor : lambda * (1 + r) ^ 2 = 1 := by
    rw [hdenSquare]
    calc
      lambda * (1 + rho) = lambda + rho * lambda := by ring
      _ = 1 := hlinear
  have hlambda : lambda = ((1 + r)⁻¹) ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hdenr)
    calc
      lambda * (1 + r) ^ 2 = 1 := hfactor
      _ = ((1 + r)⁻¹ * (1 + r)) ^ 2 := by
        rw [inv_mul_cancel₀ hdenr, one_pow]
      _ = ((1 + r)⁻¹) ^ 2 * (1 + r) ^ 2 := by rw [mul_pow]
  exact ⟨hlambda, hmu.trans (congrArg (rho * ·) hlambda)⟩

/-- The strict-low raw base scalar is forced to one by the exact stationary
factor identity and the normalized polar laws. -/
theorem wildQuadratic_low_scalar_eq_one_of_coordinates
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
    (chiW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
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
    (lambda : ResidueField F)
    (upperLift : ResidueField F → lattice K 0)
    (upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z)
    (upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1)
    (base_coordinate : ∀ z,
      ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF
        (lambda * z ^ 2)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))))
    (tau_factor : ∀ z,
      stationaryUnitFactor tauData.character psiF S.tau
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) = 1) :
    lambda = 1 := by
  apply wildQuadratic_low_normalizedScalar_eq_one_of_residueEquiv
    (wildQuadraticResidueEquiv F K C)
      upper.toCriticalPolarFunction chiW.toCriticalPolarFunction
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
  have hbaseFactor :
      stationaryUnitFactor chiFData.character psiF S.chiF
          (normUnits F K upperUnit) =
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F
          chiW (lambda * z ^ 2) := by
    simpa only [actualSourceFunction] using
      (base_coordinate z).factor_eq_actualSourceFunction
  rw [hupperFactor, hstationary, hbaseFactor, tau_character, tau_factor z,
    inv_one, mul_one]

/-- Coordinate-level boundary scalar gate.  It consumes only the exact
stationary-factor identity and the two actual normalized lower coordinates. -/
theorem wildQuadratic_boundary_scalars_add_eq_one_of_coordinates
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
    (tauW chiW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
    (tau : NormCharacter F K)
    (tau_character : tau.1 = tauData.character)
    (chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
      (algebraMap F K (C.n : F) - (C.u : K)))
    (chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (lambda mu : ResidueField F)
    (upperLift : ResidueField F → lattice K 0)
    (upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z)
    (upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1)
    (base_coordinate : ∀ z,
      ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF
        (lambda * z ^ 2)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))))
    (tau_coordinate : ∀ z,
      ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau
        (mu * z ^ 2)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z)))) :
    lambda + mu = 1 := by
  apply wildQuadratic_boundary_normalizedScalars_add_eq_one_of_residueEquiv
    (wildQuadraticResidueEquiv F K C) upper.toCriticalPolarFunction
      chiW.toCriticalPolarFunction tauW.toCriticalPolarFunction
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
  have hbaseFactor :
      stationaryUnitFactor chiFData.character psiF S.chiF
          (normUnits F K upperUnit) =
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F
          chiW (lambda * z ^ 2) := by
    simpa only [actualSourceFunction] using
      (base_coordinate z).factor_eq_actualSourceFunction
  have htauFactor :
      stationaryUnitFactor tau.1 psiF S.tau
          (normUnits F K twistedUnit) =
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F
          tauW (mu * z ^ 2) := by
    rw [tau_character]
    simpa only [actualSourceFunction] using
      (tau_coordinate z).factor_eq_actualSourceFunction
  rw [hupperFactor, hstationary, hbaseFactor, htauFactor]

end NormalizedLowScalarGates

section StrictLowCertificates

/-- End-to-end strict-low odd/odd upper certificate from the three actual
normalized quotient rows and the PhaseReduction source coordinate. -/
noncomputable def wildQuadratic_belowMOddTOdd_from_normalizedRows
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
    {t m d dTau a : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hstrict : 2 * d < t)
    (htauDepth : t = 2 * dTau) (ha : a + 2 * d = t)
    (had : 1 ≤ a + d)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hu : ord K (C.u : K) = ((a : ℤ) : WithTop ℤ))
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW chiW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_delta : ord K (upper.delta : K) = ((d : ℤ) : WithTop ℤ))
    (tau_delta : ord F (tauW.delta : F) = ((dTau : ℤ) : WithTop ℤ))
    (chi_delta : ord F (chiW.delta : F) = ((d : ℤ) : WithTop ℤ))
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
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q (.belowMOddTOdd tauW chiW) S
      tauData chiFData psiF := by
  classical
  let upperLift : ResidueField F → lattice K 0 := fun z ↦
    wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upper.delta upper_delta z
  have upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z := by
    intro z
    exact wildQuadratic_lowNormalizedUpperLift_reduce F K hres pi hpi upper.delta
      upper_delta z
  have upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1 := by
    intro z
    exact wildQuadratic_lowTwistedDisplacement_mem_one K (C.u : K) hu
      upper.delta upper_delta had (upperLift z)
  let baseScalar : ResidueField F :=
    PhaseReductionResidualCoordinateSource.transportScalar
      (LamprechtCriticalCoordinate.odd chiW.delta chi_delta)
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
  let upperScalar : ResidueField F :=
    wildQuadratic_lowUpperTransportScalar F K hres pi hpi upper.delta upper_delta
  let lambda : ResidueField F := baseScalar⁻¹ * upperScalar ^ 2
  let baseRaw (z : ResidueField F) :=
    wildQuadratic_lowBaseCoordinate_raw F K ht htpos (by omega) hres pi hpi hgen
      hdegree upper.delta upper_delta chiW.delta chi_delta z
  let base_mem (z : ResidueField F) := Classical.choose (baseRaw z)
  have base_reduce_raw (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiW.delta : F)) (base_mem z) = lambda * z ^ 2 := by
    simpa only [baseRaw, base_mem, upperLift, lambda, baseScalar, upperScalar]
      using Classical.choose_spec (baseRaw z)
  have base_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF
        (lambda * z ^ 2)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))) := by
    apply wildQuadratic_actualLowerCritical_of_displacement chiW chiFData
      psiF S.chiF chi_pair chi_local (lambda * z ^ 2)
        (phaseReductionNormPolynomial F K
          ((upper.delta : K) * (upperLift z : K)))
        (base_mem z) (base_reduce_raw z)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z)))
    exact wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper
      (upperLift z)
  let tauRaw (z : ResidueField F) :=
    wildQuadratic_lowStrictTauCoordinate F K ht htpos hstrict htauDepth ha hres pi
      hpi hgen (C.u : K) hu upper.delta upper_delta tauW.delta tau_delta z
  let tau_mem (z : ResidueField F) := Classical.choose (tauRaw z)
  have tau_reduce (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F)) (tau_mem z) = 0 := by
    simpa only [tauRaw, tau_mem, upperLift] using
      Classical.choose_spec (tauRaw z)
  have tau_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau 0
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) := by
    apply wildQuadratic_actualLowerCritical_of_displacement tauW tauData psiF
      S.tau tau_pair tau_local 0
        (phaseReductionNormPolynomial F K
          ((C.u : K) * ((upper.delta : K) * (upperLift z : K))))
        (tau_mem z) (tau_reduce z)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z)))
    exact wildQuadratic_norm_twistedCriticalUnit_coe (F := F) C upper
      (upperLift z) (upper_mem z)
  have tau_factor (z : ResidueField F) :
      stationaryUnitFactor tauData.character psiF S.tau
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) = 1 := by
    calc
      _ = actualSourceFunction F (some tauW) 0 :=
        (tau_coordinate z).factor_eq_actualSourceFunction
      _ = 1 := CriticalPolarFunction.map_zero tauW.toCriticalPolarFunction
  have hlambda : lambda = 1 :=
    wildQuadratic_low_scalar_eq_one_of_coordinates F K C S tauData chiFData psiF
      upper chiW upper_pair upper_character upper_additive chi_pair chi_local
        tau tau_character chiK_ratio chiF_ratio lambda upperLift upper_reduce
          upper_mem base_coordinate tau_factor
  exact wildQuadratic_belowMOddTOdd_upperCertificate F K C S tauData
    chiFData psiF upper tauW chiW upper_pair upper_character upper_additive
      tau_pair tau_local chi_pair chi_local tau tau_character chiK_ratio
        chiF_ratio upperLift upper_reduce upper_mem base_mem (fun z ↦ by
          simpa only [hlambda, one_mul] using base_reduce_raw z)
            tau_mem tau_reduce q

/-- End-to-end strict-low odd/even certificate.  The caller supplies the
even norm-character stationary factor proved from `lowTauRaw_eq_one`; all
coordinate normalization and the remaining scalar are derived here. -/
noncomputable def wildQuadratic_belowMOddTEven_from_normalizedRows
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
    {t m d a : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t) (had : 1 ≤ a + d)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hu : ord K (C.u : K) = ((a : ℤ) : WithTop ℤ))
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (chiW : QuotientDerivedNormalizedCriticalFunction F)
    (upper_delta : ord K (upper.delta : K) = ((d : ℤ) : WithTop ℤ))
    (chi_delta : ord F (chiW.delta : F) = ((d : ℤ) : WithTop ℤ))
    (upper_pair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        K upper S.chiK)
    (upper_character : upper.chi.character = chiFData.character.compNorm)
    (upper_additive : upper.psi.character = psiF.character.compTrace)
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
    (tau_factor : ∀ z,
      stationaryUnitFactor tauData.character psiF S.tau
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper
            (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upper.delta
              upper_delta z)
            (wildQuadratic_lowTwistedDisplacement_mem_one K (C.u : K) hu
              upper.delta upper_delta had
                (wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upper.delta
                  upper_delta z)))) = 1)
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q (.belowMOddTEven chiW) S
      tauData chiFData psiF := by
  classical
  let upperLift : ResidueField F → lattice K 0 := fun z ↦
    wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upper.delta upper_delta z
  have upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z := by
    intro z
    exact wildQuadratic_lowNormalizedUpperLift_reduce F K hres pi hpi upper.delta
      upper_delta z
  have upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1 := by
    intro z
    exact wildQuadratic_lowTwistedDisplacement_mem_one K (C.u : K) hu
      upper.delta upper_delta had (upperLift z)
  let baseScalar : ResidueField F :=
    PhaseReductionResidualCoordinateSource.transportScalar
      (LamprechtCriticalCoordinate.odd chiW.delta chi_delta)
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
  let upperScalar : ResidueField F :=
    wildQuadratic_lowUpperTransportScalar F K hres pi hpi upper.delta upper_delta
  let lambda : ResidueField F := baseScalar⁻¹ * upperScalar ^ 2
  let baseRaw (z : ResidueField F) :=
    wildQuadratic_lowBaseCoordinate_raw F K ht htpos hd hres pi hpi hgen hdegree
      upper.delta upper_delta chiW.delta chi_delta z
  let base_mem (z : ResidueField F) := Classical.choose (baseRaw z)
  have base_reduce_raw (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiW.delta : F)) (base_mem z) = lambda * z ^ 2 := by
    simpa only [baseRaw, base_mem, upperLift, lambda, baseScalar, upperScalar]
      using Classical.choose_spec (baseRaw z)
  have base_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF
        (lambda * z ^ 2)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))) := by
    apply wildQuadratic_actualLowerCritical_of_displacement chiW chiFData
      psiF S.chiF chi_pair chi_local (lambda * z ^ 2)
        (phaseReductionNormPolynomial F K
          ((upper.delta : K) * (upperLift z : K)))
        (base_mem z) (base_reduce_raw z)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z)))
    exact wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper
      (upperLift z)
  have tau_factor' (z : ResidueField F) :
      stationaryUnitFactor tauData.character psiF S.tau
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) = 1 := by
    simpa only [upperLift] using tau_factor z
  have hlambda : lambda = 1 :=
    wildQuadratic_low_scalar_eq_one_of_coordinates F K C S tauData chiFData psiF
      upper chiW upper_pair upper_character upper_additive chi_pair chi_local
        tau tau_character chiK_ratio chiF_ratio lambda upperLift upper_reduce
          upper_mem base_coordinate tau_factor'
  exact wildQuadratic_belowMOddTEven_upperCertificate F K C S tauData
    chiFData psiF upper chiW upper_pair upper_character upper_additive
      chi_pair chi_local tau tau_character chiK_ratio chiF_ratio upperLift
        upper_reduce upper_mem base_mem (fun z ↦ by
          simpa only [hlambda, one_mul] using base_reduce_raw z)
            tau_factor' q

/-- End-to-end odd-boundary upper certificate.  The common lower coordinate
is the retained `rhoLift`; its exact coordinate equality fixes the tau/base
transport-scalar ratio, while `hnormResidue` identifies the selected
correction unit without manufacturing `rho` from its norm. -/
noncomputable def wildQuadratic_boundaryOdd_from_normalizedRows
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
    {t m d : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t) (hdpos : 0 < d)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hu : ord K (C.u : K) = (0 : WithTop ℤ))
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (rho : ResidueField F) (rho_ne_zero : rho ≠ 0)
    (denominator_ne_zero : 1 + rho ≠ 0)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (tauW chiW : QuotientDerivedNormalizedCriticalFunction F)
    (common :
      WildQuadraticCoefficientInputs.WildQuadraticBoundaryCommonCoordinate
        (F := F) rho tauW chiW)
    (upper_delta : ord K (upper.delta : K) = ((d : ℤ) : WithTop ℤ))
    (tau_delta : ord F (tauW.delta : F) = ((d : ℤ) : WithTop ℤ))
    (chi_delta : ord F (chiW.delta : F) = ((d : ℤ) : WithTop ℤ))
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
    (hnormResidue :
      residueMap F
        (⟨norm F K (C.u : K), by
          rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
            one_nsmul, hu]
          exact le_rfl⟩ : ringOfIntegers F) = rho ^ 2)
    (q : CharTwoRefinement (ResidueField F)) :
    ActualUpperCoordinateCertificate F K C q
      (.boundaryOdd rho rho_ne_zero denominator_ne_zero tauW chiW) S
        tauData chiFData psiF := by
  classical
  let upperLift : ResidueField F → lattice K 0 := fun z ↦
    wildQuadratic_lowNormalizedUpperLift F K hres pi hpi upper.delta upper_delta z
  have upper_reduce : ∀ z,
      reduce K (upperLift z : K) (upperLift z).property =
        wildQuadraticResidueEquiv F K C z := by
    intro z
    exact wildQuadratic_lowNormalizedUpperLift_reduce F K hres pi hpi upper.delta
      upper_delta z
  have upper_mem : ∀ z,
      (C.u : K) * ((upper.delta : K) * (upperLift z : K)) ∈ lattice K 1 := by
    intro z
    exact wildQuadratic_lowTwistedDisplacement_mem_one K (C.u : K) hu
      upper.delta upper_delta (by omega)
        (upperLift z)
  let baseScalar : ResidueField F :=
    PhaseReductionResidualCoordinateSource.transportScalar
      (LamprechtCriticalCoordinate.odd chiW.delta chi_delta)
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
  let tauScalar : ResidueField F :=
    PhaseReductionResidualCoordinateSource.transportScalar
      (LamprechtCriticalCoordinate.odd tauW.delta tau_delta)
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
  let upperScalar : ResidueField F :=
    wildQuadratic_lowUpperTransportScalar F K hres pi hpi upper.delta upper_delta
  let normResidue : ResidueField F :=
    residueMap F
      (⟨norm F K (C.u : K), by
        rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
          one_nsmul, hu]
        exact le_rfl⟩ : ringOfIntegers F)
  let lambda : ResidueField F := baseScalar⁻¹ * upperScalar ^ 2
  let mu : ResidueField F := tauScalar⁻¹ * normResidue * upperScalar ^ 2
  let baseRaw (z : ResidueField F) :=
    wildQuadratic_lowBaseCoordinate_raw F K ht htpos hd hres pi hpi hgen hdegree
      upper.delta upper_delta chiW.delta chi_delta z
  let base_mem (z : ResidueField F) := Classical.choose (baseRaw z)
  have base_reduce_raw (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiW.delta : F)) (base_mem z) = lambda * z ^ 2 := by
    simpa only [baseRaw, base_mem, upperLift, lambda, baseScalar, upperScalar]
      using Classical.choose_spec (baseRaw z)
  have base_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some chiW) chiFData psiF S.chiF
        (lambda * z ^ 2)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z))) := by
    apply wildQuadratic_actualLowerCritical_of_displacement chiW chiFData
      psiF S.chiF chi_pair chi_local (lambda * z ^ 2)
        (phaseReductionNormPolynomial F K
          ((upper.delta : K) * (upperLift z : K)))
        (base_mem z) (base_reduce_raw z)
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper (upperLift z)))
    exact wildQuadratic_norm_criticalUnitAtLift_coe (F := F) upper
      (upperLift z)
  let tauRaw (z : ResidueField F) :=
    wildQuadratic_lowBoundaryTauCoordinate_raw F K ht htpos hd hres pi hpi hgen
      hdegree C.u hu upper.delta upper_delta tauW.delta tau_delta z
  let tau_mem (z : ResidueField F) := Classical.choose (tauRaw z)
  have tau_reduce_raw (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F)) (tau_mem z) = mu * z ^ 2 := by
    have hraw := Classical.choose_spec (tauRaw z)
    have halgebra :
        tauScalar⁻¹ * normResidue * (upperScalar * z) ^ 2 =
          mu * z ^ 2 := by
      dsimp only [mu]
      ring
    simpa only [tauRaw, tau_mem, upperLift, tauScalar, normResidue,
      upperScalar] using hraw.trans halgebra
  have tau_coordinate (z : ResidueField F) :
      ActualLowerStationaryCoordinate F (some tauW) tauData psiF S.tau
        (mu * z ^ 2)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z))) := by
    apply wildQuadratic_actualLowerCritical_of_displacement tauW tauData psiF
      S.tau tau_pair tau_local (mu * z ^ 2)
        (phaseReductionNormPolynomial F K
          ((C.u : K) * ((upper.delta : K) * (upperLift z : K))))
        (tau_mem z) (tau_reduce_raw z)
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper (upperLift z)
            (upper_mem z)))
    exact wildQuadratic_norm_twistedCriticalUnit_coe (F := F) C upper
      (upperLift z) (upper_mem z)
  have hsum : lambda + mu = 1 :=
    wildQuadratic_boundary_scalars_add_eq_one_of_coordinates F K C S tauData
      chiFData psiF upper tauW chiW upper_pair upper_character upper_additive
        tau tau_character chiK_ratio chiF_ratio lambda mu upperLift
          upper_reduce upper_mem base_coordinate tau_coordinate
  have htauScalar : tauScalar = rho * baseScalar := by
    have h := wildQuadratic_transportScalar_eq_mul_of_coordinate_eq F
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
      (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order
        tauW.delta chiW.delta tau_delta chi_delta common.rhoLift
          common.coordinate_eq
    simpa only [tauScalar, baseScalar, common.rhoLift_residue] using h
  have hbaseScalar : baseScalar ≠ 0 := by
    dsimp only [baseScalar,
      PhaseReductionResidualCoordinateSource.transportScalar]
    exact Units.ne_zero _
  have hmu : mu = rho * lambda := by
    dsimp only [mu, lambda]
    rw [htauScalar]
    change (rho * baseScalar)⁻¹ * normResidue * upperScalar ^ 2 =
      rho * (baseScalar⁻¹ * upperScalar ^ 2)
    rw [show normResidue = rho ^ 2 by
      simpa only [normResidue] using hnormResidue]
    field_simp [rho_ne_zero, hbaseScalar]
  have hscalars := wildQuadratic_boundary_normalizedScalars lambda mu rho
    (WildQuadraticRefinement.squareRoot rho) hsum hmu
      (WildQuadraticRefinement.squareRoot_sq rho) denominator_ne_zero
  have base_reduce (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((upper.delta : K) * (upperLift z : K)) /
            (chiW.delta : F)) (base_mem z) =
        ((1 + WildQuadraticRefinement.squareRoot rho)⁻¹ * z) ^ 2 := by
    rw [base_reduce_raw z, hscalars.1]
    ring
  have tau_reduce (z : ResidueField F) :
      reduce F
          (phaseReductionNormPolynomial F K
              ((C.u : K) * ((upper.delta : K) * (upperLift z : K))) /
            (tauW.delta : F)) (tau_mem z) =
        rho * ((1 + WildQuadraticRefinement.squareRoot rho)⁻¹ * z) ^ 2 := by
    rw [tau_reduce_raw z, hscalars.2]
    ring
  exact wildQuadratic_boundaryOdd_upperCertificate F K C S tauData chiFData
    psiF rho rho_ne_zero denominator_ne_zero upper tauW chiW upper_pair
      upper_character upper_additive tau_pair tau_local chi_pair chi_local
        tau tau_character chiK_ratio chiF_ratio upperLift upper_reduce upper_mem
          base_mem base_reduce tau_mem tau_reduce q

end StrictLowCertificates

/-! ## Public low-coordinate package -/

section PublicLowCoordinateTransport

variable (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
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
  (rows : WildQuadraticActualPhaseRows V data phaseData assembly)

/-- Exact q-free provenance consumed by the low coordinate transport. -/
structure WildQuadraticLowCoordinateTransportSource where
  conductor_eq : m = V.chiFData.conductor
  stationaryDepth : ℕ
  conductorRemainder : ℕ
  ht : PrimeCyclicExtension.IsLowerBreak F K t
  hres : residueDegree F K = 1
  pi : ringOfIntegers K
  hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)
  hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤
  hdegree : Module.finrank F K = 2
  chiK : LocalQuasiCharData K
  psiK : LocalAddCharData K
  baseData_eq : data.twistData 1 = V.chiFData
  baseAddData_eq : data.baseAddChar = V.psiF
  hminimal : IsMinimalNormCharacterOrbitRepresentative F K (data.twistData 1)
  hchi : chiK.character = (data.twistData 1).character.compNorm
  hpsi : psiK.character = data.baseAddChar.character.compTrace
  hF : IsStationaryConductorDecomposition (data.twistData 1).conductor stationaryDepth
    conductorRemainder
  hLow : (data.twistData 1).conductor ≤ t + 1
  delta : Fˣ
  epsilon1 : Kˣ
  hdelta : ord F (delta : F) = ((((t + 1 : ℕ) : ℤ) +
    data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  hepsilon1 : ord K (epsilon1 : K) = (((t + 1 -
    (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ)
  hT : 2 ≤ t + 1
  hgammaF : ord F (lowGammaF F K delta epsilon1 : F) = ((((data.twistData 1).conductor : ℤ) +
    data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  hgammaK : ord K (lowGammaK F K delta epsilon1 : K) = (((chiK.conductor : ℤ) +
    psiK.conductor : ℤ) : WithTop ℤ)
  selected : LowStationaryNormRepresentativePair F K (lowCriticalFloorDepth t)
    stationaryDepth
    (stationaryCoefficientClass F (quasiCharDataOfIsConductor F
      (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (lowNormCharacterGenerator F K ht hres pi hpi hgen)
        (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF)
  table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK selected
  WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data chiK psiK
    hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK selected table
  stationaryPairs_eq : lowWildQuadraticSelectedStationaryPairs delta epsilon1
    selected = V.stationaryPairs
  correction_u : lowNormalizedRatio F K epsilon1 selected = (V.correction.u : K)
  correction_n : lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hF
    delta epsilon1 hdelta hT hgammaF selected = V.correction.n
  coordinates : WildQuadraticCommonCoordinateCompatibility V data phaseData assembly
  tau_phase : rows.tau.criticalFactor = quotientSourcePhase F V.criticalInputs.tauSource
  base_phase : rows.base.criticalFactor = quotientSourcePhase F V.criticalInputs.chiFSource

/-- Q-free low upper-coordinate output. -/
structure WildQuadraticLowCoordinateTransport : Prop where
  coordinate : WildQuadraticPositivePolarCoordinateTransport F K V rows
  boundary_source : ∀ (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
    (tau chiF : QuotientDerivedNormalizedCriticalFunction F),
    V.criticalInputs = .boundaryOdd rho hrho hden tau chiF →
      ∃ hboundary : m = t + 1, residueMap K
          (wildQuadraticBoundaryRingUnit F K V.correction hboundary :
            ringOfIntegers K) = extensionResidueMap F K rho ∧
        WildQuadraticCoefficientData.boundaryNResidue F K V.correction hboundary = rho ^ 2

/-- Recover the selected boundary residue from the retained common source
coordinate; the norm identity is used only after that source has fixed rho. -/
private theorem wildQuadratic_lowBoundarySource
    (P : WildQuadraticLowCoordinateTransportSource F K V rows) : ∀
    (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
    (tau chiF : QuotientDerivedNormalizedCriticalFunction F),
    V.criticalInputs = .boundaryOdd rho hrho hden tau chiF →
      ∃ hboundary : m = t + 1, residueMap K
          (wildQuadraticBoundaryRingUnit F K V.correction hboundary :
            ringOfIntegers K) = extensionResidueMap F K rho ∧
        WildQuadraticCoefficientData.boundaryNResidue F K V.correction hboundary = rho ^ 2 := by
  intro rho hrho hden tau chiF hI
  have hboundary : m = t + 1 := by
    have hr := congrArg WildQuadraticCoefficientRow.range V.criticalInputs_row
    rw [hI] at hr
    rcases lt_trichotomy (m - 1) t with h | h | h
    · rw [WildQuadraticCoefficientRow.ofConductors_range_below h] at hr
      cases hr
    · have := V.conductor_gt_one; omega
    · rw [WildQuadraticCoefficientRow.ofConductors_range_above h] at hr
      cases hr
  obtain ⟨common⟩ := by
    have hc := V.criticalInputs_boundaryCoordinates
    rwa [hI] at hc
  have hp := V.criticalInputs_stationaryPairs
  have hl := V.criticalInputs_localData
  rw [hI] at hp hl
  have hcond : tau.chi.conductor = chiF.chi.conductor := by
    have hd := tau.delta_order
    rw [common.coordinate_eq, criticalPolarScaledCoordinate_ord F chiF.d
      common.rhoLift chiF.delta chiF.delta_order] at hd
    rw [tau.conductor_eq, chiF.conductor_eq]
    exact congrArg (fun d : ℕ ↦ 2 * d + 1) (by exact_mod_cast hd.symm)
  have hnord : ord F (V.correction.n : F) = (0 : WithTop ℤ) := by
    rw [V.correction.target_order, hboundary]
    simp
  let n0 : unitGroup F :=
    ⟨V.correction.n, (mem_unitGroup_iff_ord_eq_zero F _).2 hnord⟩
  have hratio : (chiF.beta : F) / ((chiF.Gamma : Fˣ) : F) = ((n0 : Fˣ) : F) *
      ((tau.beta : F) / ((tau.Gamma : Fˣ) : F)) := by
    calc
      _ = V.stationaryPairs.chiF.ratio := by rw [hp.2.1, hp.2.2]; rfl
      _ = V.stationaryPairs.tau.ratio * (V.correction.n : F) := V.chiF_ratio
      _ = _ := by
        rw [hp.1.1, hp.1.2, WildQuadraticStationaryPair.ratio]
        change _ * (V.correction.n : F) = (V.correction.n : F) * _
        ring
  have hunit : QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioUnit tau chiF hcond =
      common.rhoLift := by
    apply Subtype.ext
    apply Units.ext
    rw [QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioUnit_coe]
    apply (div_eq_iff (Units.ne_zero chiF.delta)).2
    simpa only [criticalPolarScaledCoordinate, Units.val_mul] using
      congrArg (Units.val : Fˣ → F) common.coordinate_eq
  have hrho' : QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue tau chiF hcond = rho := by
    unfold QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
    rw [hunit, common.rhoLift_residue]
  have hs :=
    QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_sq_of_stationaryRatio_scale
      tau chiF (hl.1.2.trans hl.2.2.symm) hcond n0 hratio
  have hn : WildQuadraticCoefficientData.boundaryNResidue F K V.correction hboundary = rho ^ 2 := by
    rw [hrho'] at hs
    change residueMap F (⟨V.correction.n, _⟩ : ringOfIntegers F) = rho ^ 2
    calc
      _ = ((residueUnits F n0 : (ResidueField F)ˣ) : ResidueField F) := by
        rw [residueUnits_coe]
        rfl
      _ = rho ^ 2 := hs.symm
  exact ⟨hboundary, wildQuadratic_boundary_selected_unit_residue F K P.ht
    V.correction hboundary rho hn, hn⟩

private theorem wildQuadratic_lowUpperSource
    (P : WildQuadraticLowCoordinateTransportSource F K V rows) (hm : Odd m) :
    ∃ upper : QuotientDerivedNormalizedCriticalFunction K,
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair K upper V.stationaryPairs.chiK ∧
      upper.chi.character = V.chiFData.character.compNorm ∧
      upper.psi.character = V.psiF.character.compTrace ∧
      upper.d = P.stationaryDepth := by
  have hchiK : P.chiK.conductor = m := by
    rw [lowCompNorm_conductor_eq F K P.ht P.hres P.pi P.hpi P.hgen
      (data.twistData 1) P.hminimal P.chiK P.hchi P.hLow, P.baseData_eq,
      ← P.conductor_eq]
  have hext : data.extensionQuasiChar = P.chiK := by
    apply LocalQuasiCharData.ext_character K
    rw [data.extensionQuasiChar_character, ← P.baseData_eq]
    exact P.hchi.symm
  obtain ⟨upper, hlocal, pair, _⟩ := rows.extension.exists_normalizedQuotientDerivedCriticalFunction
    (by rw [hext, hchiK]; exact hm)
  refine ⟨upper, ?_, ?_, ?_, ?_⟩
  · rw [← rows.extension_pair]; exact pair
  · rw [hlocal.1]; exact data.extensionQuasiChar_character
  · rw [hlocal.2]; exact data.extensionAddChar_character
  · have hu := upper.conductor_eq
    have hl := congrArg LocalQuasiCharData.conductor hlocal.1
    have hf := P.hF.conductor_eq
    have heps := P.hF.epsilon_le_one
    obtain ⟨j, hj⟩ := hm
    rw [hext, hchiK] at hl
    rw [P.baseData_eq, ← P.conductor_eq] at hf
    omega

private theorem wildQuadratic_lowUpperCertificateRowPhase
    {q : CharTwoRefinement (ResidueField F)}
    (C : ActualUpperCoordinateCertificate F K V.correction q V.criticalInputs V.stationaryPairs
      V.tauData V.chiFData V.psiF) : rows.extension.criticalFactor =
      QuotientDerivedNormalizedCriticalFunction.phase K C.upper := by
  apply rows.extension.criticalFactor_eq_quotientSourcePhase_of_matches
    C.upper ⟨?_, ?_⟩ (by rw [rows.extension_pair]; exact C.upper_pair)
  · apply LocalQuasiCharData.ext_character K
    rw [C.upper_character]; exact data.extensionQuasiChar_character.symm
  · apply LocalAddCharData.ext_character
    rw [C.upper_additive]; exact data.extensionAddChar_character.symm

set_option maxHeartbeats 4000000 in
/-- Construct the complete wild-quadratic Low coordinate transport from the
retained Low source package, preserving the actual stationary representatives,
boundary coordinate, and four-phase assembly. -/
noncomputable def wildQuadraticLowCoordinateTransport
    (P : WildQuadraticLowCoordinateTransportSource F K V rows) :
    WildQuadraticLowCoordinateTransport F K V rows := by
  classical
  have hbase : (data.twistData 1).conductor = m := by
    rw [P.baseData_eq, ← P.conductor_eq]
  have hlow : m ≤ t + 1 := by rw [← hbase]; exact P.hLow
  have htpos : 0 < t := by have := P.hT; omega
  let a := t + 1 - m
  have hu : ord K (V.correction.u : K) = ((a : ℤ) : WithTop ℤ) := by
    rw [← P.correction_u, lowNormalizedRatio_order F K P.epsilon1 P.hepsilon1 P.selected]
    dsimp only [a]
    rw [hbase]
    norm_cast
  let tau0 := lowNormCharacterGenerator F K P.ht P.hres P.pi P.hpi P.hgen
  have htau0 : tau0 ≠ 1 := lowNormCharacterGenerator_ne_one F K P.ht P.hres P.pi P.hpi P.hgen
  have htauEq : assembly.indexing.tau = tau0 := by
    obtain ⟨b, hb⟩ := assembly.indexing.index.surjective tau0
    cases b with
    | false => simpa only [assembly.indexing.index_false] using hb
    | true => exact (htau0 (by simpa only [assembly.indexing.index_true] using hb.symm)).elim
  have htauCharacter : assembly.indexing.tau.1 = V.tauData.character := by
    rw [← P.coordinates.tauData_eq, data.normCharacterData_character, htauEq]
  have htauConductor : V.tauData.conductor = t + 1 := by
    rw [← P.coordinates.tauData_eq]
    apply Eq.symm
    apply (data.normCharacterData assembly.indexing.tau).conductor_eq_of_isConductor
    rw [data.normCharacterData_character]
    simpa only [htauEq] using ramifiedNormCharacter_conductor F K P.ht P.hres P.pi
      P.hpi P.hgen tau0 htau0
  have hmPred : m - 1 + 1 = m := by have := V.conductor_gt_one; omega
  have hmParity : V.criticalInputs.row.mParity =
      WildQuadraticConductorParity.ofConductor m := by
    rw [V.criticalInputs_row, WildQuadraticCoefficientRow.ofConductors_mParity, hmPred]
  have hTParity : V.criticalInputs.row.TParity =
      WildQuadraticConductorParity.ofConductor (t + 1) := by
    rw [V.criticalInputs_row, WildQuadraticCoefficientRow.ofConductors_TParity]
  have hbelow (hr : V.criticalInputs.row.range = .below) : m - 1 < t := by
    rcases lt_trichotomy (m - 1) t with h | h | h
    · exact h
    · rw [V.criticalInputs_row, WildQuadraticCoefficientRow.ofConductors_range_boundary h] at hr
      cases hr
    · rw [V.criticalInputs_row, WildQuadraticCoefficientRow.ofConductors_range_above h] at hr
      cases hr
  have hoddData (hm : Odd m) : P.conductorRemainder = 1 ∧
      m = 2 * P.stationaryDepth + 1 := by
    have hf := P.hF.conductor_eq; have he := P.hF.epsilon_le_one
    obtain ⟨j, hj⟩ := hm
    rw [hbase] at hf
    omega
  have hBelowEven : ∀ (chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .belowMOddTEven chiF) q, Nonempty
      (ActualUpperCoordinateCertificate F K V.correction q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF) := by
    intro chiF hI q
    have hm : Odd m := (WildQuadraticConductorParity.ofConductor_eq_odd_iff m).mp
      (hmParity.symm.trans (by rw [hI]; rfl))
    have hb := hbelow (by rw [hI]; rfl); have hd := (hoddData hm).2
    obtain ⟨upper, upPair, upChar, upAdd, upDepth⟩ := wildQuadratic_lowUpperSource F K V rows P hm
    have hp := V.criticalInputs_stationaryPairs; have hl := V.criticalInputs_localData
    rw [hI] at hp hl
    have chiDepth : chiF.d = P.stationaryDepth := by
      have hc := chiF.conductor_eq; have he := congrArg LocalQuasiCharData.conductor hl.1
      have hv := P.conductor_eq; omega
    have upDelta : ord K (upper.delta : K) = ((P.stationaryDepth : ℤ) : WithTop ℤ) := by rw [upper.delta_order, upDepth]
    have chiDelta : ord F (chiF.delta : F) = ((P.stationaryDepth : ℤ) : WithTop ℤ) := by rw [chiF.delta_order, chiDepth]
    have ha : a + 2 * P.stationaryDepth = t := by dsimp only [a]; omega
    have tauFactor : ∀ z, stationaryUnitFactor V.tauData.character V.psiF
        V.stationaryPairs.tau (normUnits F K (wildQuadraticTwistedCriticalUnit
          V.correction upper (wildQuadratic_lowNormalizedUpperLift F K P.hres P.pi P.hpi upper.delta upDelta z)
          (wildQuadratic_lowTwistedDisplacement_mem_one K V.correction.u hu upper.delta upDelta (by omega) _))) = 1 := by
      intro z
      let lift := wildQuadratic_lowNormalizedUpperLift F K P.hres P.pi P.hpi upper.delta upDelta z
      have hmem := wildQuadratic_lowTwistedDisplacement_mem_one K V.correction.u hu upper.delta upDelta (by omega) lift
      let unit := wildQuadraticTwistedCriticalUnit V.correction upper lift hmem
      have hunit : (unit : K) = 1 + lowNormalizedRatio F K P.epsilon1 P.selected * ((upper.delta : K) * (lift : K)) := by
        dsimp only [unit]; rw [P.correction_u, wildQuadraticTwistedCriticalUnit_coe]
      have hlayer : phaseReductionNormPolynomial F K (lowNormalizedRatio F K P.epsilon1 P.selected *
          ((upper.delta : K) * (lift : K))) ∈ lattice F ((lowCriticalFloorDepth t + lowCriticalParity t : ℕ) : ℤ) := by
        rw [wildQuadratic_lowNormalizedUpperLift_displacement F K P.hres P.pi P.hpi upper.delta upDelta]
        exact phaseReductionLowStrictTauPolynomial_stationaryLayer F K P.ht P.hres P.pi P.hpi P.hgen
          htpos (by omega) a ha _ (by rw [P.correction_u]; exact hu) _
      have raw := lowTauRaw_eq_one F K P.ht P.hres P.pi P.hpi P.hgen data P.hF P.delta
        P.epsilon1 P.hdelta P.hT P.hgammaF P.selected _ unit hunit hlayer
      simpa only [stationaryUnitFactor, ← P.baseAddData_eq, ← htauCharacter,
        htauEq, P.correction_u,
        ← P.stationaryPairs_eq, (lowWildQuadraticSelectedStationaryPairs_ratios P.delta P.epsilon1 P.selected).2.1,
        unit, wildQuadratic_norm_twistedCriticalUnit_coe, add_sub_cancel_left] using raw
    let C := wildQuadratic_belowMOddTEven_from_normalizedRows F K P.ht htpos (by omega)
      (by omega) P.hres P.pi P.hpi P.hgen P.hdegree V.correction hu V.stationaryPairs
      V.tauData V.chiFData V.psiF upper chiF upDelta chiDelta upPair upChar upAdd hp hl
      assembly.indexing.tau htauCharacter V.chiK_ratio V.chiF_ratio tauFactor q
    rw [hI]; exact ⟨C⟩
  have hBelowOdd : ∀ (tauW chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .belowMOddTOdd tauW chiF) q, Nonempty
      (ActualUpperCoordinateCertificate F K V.correction q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF) := by
    intro tauW chiF hI q
    have hm := (WildQuadraticConductorParity.ofConductor_eq_odd_iff m).mp
      (hmParity.symm.trans (by rw [hI]; rfl))
    have hTo := (WildQuadraticConductorParity.ofConductor_eq_odd_iff (t + 1)).mp
      (hTParity.symm.trans (by rw [hI]; rfl))
    have hb := hbelow (by rw [hI]; rfl); have hd := (hoddData hm).2
    obtain ⟨upper, upPair, upChar, upAdd, upDepth⟩ := wildQuadratic_lowUpperSource F K V rows P hm
    have hp := V.criticalInputs_stationaryPairs; have hl := V.criticalInputs_localData
    rw [hI] at hp hl
    have td : t = 2 * tauW.d := by have hc := tauW.conductor_eq; have he := congrArg LocalQuasiCharData.conductor hl.1.1; rw [htauConductor] at he; omega
    have cd : chiF.d = P.stationaryDepth := by have hc := chiF.conductor_eq; have he := congrArg LocalQuasiCharData.conductor hl.2.1; have hv := P.conductor_eq; omega
    let C := wildQuadratic_belowMOddTOdd_from_normalizedRows (d := P.stationaryDepth)
      (dTau := tauW.d) (a := a) F K P.ht htpos (by omega) td
      (by dsimp only [a]; omega) (by omega) P.hres P.pi P.hpi P.hgen P.hdegree V.correction hu
      V.stationaryPairs V.tauData V.chiFData V.psiF upper tauW chiF (by rw [upper.delta_order, upDepth])
      (by rw [tauW.delta_order]) (by rw [chiF.delta_order, cd]) upPair upChar upAdd hp.1 hl.1 hp.2 hl.2
      assembly.indexing.tau htauCharacter V.chiK_ratio V.chiF_ratio q
    rw [hI]; exact ⟨C⟩
  have hBoundary : ∀ (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
      (tauW chiF : QuotientDerivedNormalizedCriticalFunction F)
      (hI : V.criticalInputs = .boundaryOdd rho hrho hden tauW chiF) q, Nonempty
      (ActualUpperCoordinateCertificate F K V.correction q V.criticalInputs
        V.stationaryPairs V.tauData V.chiFData V.psiF) := by
    intro rho hrho hden tauW chiF hI q
    obtain ⟨hb, hs, hn⟩ := wildQuadratic_lowBoundarySource F K V rows P rho hrho hden tauW chiF hI
    have hm := (WildQuadraticConductorParity.ofConductor_eq_odd_iff m).mp
      (hmParity.symm.trans (by rw [hI]; rfl)); have hd := (hoddData hm).2
    obtain ⟨upper, upPair, upChar, upAdd, upDepth⟩ := wildQuadratic_lowUpperSource F K V rows P hm
    have hp := V.criticalInputs_stationaryPairs; have hl := V.criticalInputs_localData
    have hc := V.criticalInputs_boundaryCoordinates; rw [hI] at hp hl hc; obtain ⟨common⟩ := hc
    have td : tauW.d = P.stationaryDepth := by have h := tauW.conductor_eq; have e := congrArg LocalQuasiCharData.conductor hl.1.1; rw [htauConductor, ← hb] at e; omega
    have cd : chiF.d = P.stationaryDepth := by have h := chiF.conductor_eq; have e := congrArg LocalQuasiCharData.conductor hl.2.1; have hv := P.conductor_eq; omega
    have hnorm : residueMap F (⟨norm F K (V.correction.u : K), by rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, P.hres, one_nsmul, V.correction.source_order, hb]; simp⟩ : ringOfIntegers F) = rho ^ 2 := by
      rw [← hn]
      exact congrArg (residueMap F) (Subtype.ext V.correction.norm_u_field)
    let C := wildQuadratic_boundaryOdd_from_normalizedRows (d := P.stationaryDepth)
      F K P.ht htpos (by omega) (by omega)
      P.hres P.pi P.hpi P.hgen P.hdegree V.correction (by rw [V.correction.source_order, hb]; simp)
      V.stationaryPairs V.tauData V.chiFData V.psiF rho hrho hden upper tauW chiF common
      (by rw [upper.delta_order, upDepth]) (by rw [tauW.delta_order, td]) (by rw [chiF.delta_order, cd])
      upPair upChar upAdd hp.1 hl.1 hp.2 hl.2 assembly.indexing.tau htauCharacter V.chiK_ratio V.chiF_ratio hnorm q
    rw [hI]; exact ⟨C⟩
  let upper := wildQuadraticLow_upperCoordinates_of_consumers F K V hlow hBelowEven hBelowOdd hBoundary
  have hsource := wildQuadratic_lowBoundarySource F K V rows P
  refine ⟨⟨wildQuadratic_matchesCorrection_of_boundary_source F K V hsource,
    upper, ?_⟩, hsource⟩
  intro q
  cases ha : (V.criticalInputs.toCoefficientData q).affineCoefficient .chiK with
  | some l => obtain ⟨C⟩ := upper q ha; exact (wildQuadratic_lowUpperCertificateRowPhase F K V rows C).trans (C.phase_eq_table ha)
  | none =>
      rw [WildQuadraticCoefficientData.phaseFactor, ha]
      cases hI : V.criticalInputs with
      | belowMEvenTEven | belowMEvenTOdd | boundaryEven =>
          have hp := hmParity; rw [hI] at hp
          have he := (WildQuadraticConductorParity.ofConductor_eq_even_iff m).mp (hp.symm.trans rfl)
          have hext : Even data.extensionQuasiChar.conductor := by
            rw [show data.extensionQuasiChar = P.chiK by
              apply LocalQuasiCharData.ext_character K
              rw [data.extensionQuasiChar_character, ← P.baseData_eq]
              exact P.hchi.symm, lowCompNorm_conductor_eq F K P.ht P.hres P.pi P.hpi P.hgen
                (data.twistData 1) P.hminimal P.chiK P.hchi P.hLow, P.baseData_eq, ← P.conductor_eq]
            exact he
          apply rows.extension.criticalFactor_eq_one_of_isEven
          cases rows.extension <;> simp_all [LocalLamprechtPhaseData.IsEven] <;> omega
      | belowMOddTEven | belowMOddTOdd | boundaryOdd =>
          rw [hI] at ha
          simp [WildQuadraticCoefficientInputs.toCoefficientData,
            WildQuadraticCoefficientData.belowMOddTEvenComputed,
            WildQuadraticCoefficientData.belowMOddTOddComputed,
            WildQuadraticCoefficientData.boundaryOddComputed,
            WildQuadraticCoefficientData.affineCoefficient] at ha
      | aboveMEvenTEven | aboveMEvenTOdd | aboveMOddTEven | aboveMOddTOdd =>
          have hr : V.criticalInputs.row.range = .above := by rw [hI]; rfl
          have hb : m - 1 ≤ t := by omega
          rcases lt_or_eq_of_le hb with h | h
          · rw [V.criticalInputs_row, WildQuadraticCoefficientRow.ofConductors_range_below h] at hr; cases hr
          · rw [V.criticalInputs_row, WildQuadraticCoefficientRow.ofConductors_range_boundary h] at hr; cases hr

end PublicLowCoordinateTransport

end

end LanglandsFirstMainLemma
