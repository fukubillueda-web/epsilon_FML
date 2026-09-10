import LanglandsFirstMainLemma.Cases.WildQuadratic.PhasePreparation
import LanglandsFirstMainLemma.Cases.WildQuadratic.QuadraticRefinement
import LanglandsFirstMainLemma.Cases.WildQuadratic.Boundary
import LanglandsFirstMainLemma.Cases.WildQuadratic.EqualCharacteristicBreak
import LanglandsFirstMainLemma.Cases.WildQuadratic.ErrorFormula

namespace LanglandsFirstMainLemma

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Refining an actual retained positive-polar source -/

/-- A correction record built from an actual normalized quotient source.
The selected quotient numerator and denominator are retained literally, and
the refinement occurs in the positive orientation used by the coefficient
table. -/
private noncomputable def wildQuadraticCorrectionOfActualSource
    {F : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F))
    (c : F) (hc : c / (W.delta : F) ∈ lattice F 0)
    (hone : 1 + c ≠ 0) :
    WildQuadraticRefinementCorrection F (ResidueField F) W.psi W.chi q where
  depth := W.d
  conductorDecomposition :=
    { conductor_gt_one := W.conductor_gt_one
      epsilon_le_one := by omega
      conductor_eq := W.conductor_eq }
  Gamma := W.Gamma
  beta := W.beta
  correction := c
  one_add_correction_ne_zero := hone
  normalizedClass := reduce F (c / (W.delta : F)) hc
  affineCoefficient := W.affineCoefficient F q
  inverseCharacter_eq := by
    let x : F := c / (W.delta : F)
    have hdelta : (W.delta : F) ≠ 0 := Units.ne_zero W.delta
    have hunit :
        criticalPolarUnit F W.chi W.d W.conductor_eq W.conductor_gt_one
            W.delta W.delta_order x hc = Units.mk0 (1 + c) hone := by
      apply Units.ext
      simp only [criticalPolarUnit_coe, Units.val_mk0, x]
      field_simp [hdelta]
    have hvalue :
        WildQuadraticRefinement.correctionValue q (W.affineCoefficient F q)
            (reduce F x hc) = W.liftValue x hc := by
      rw [WildQuadraticRefinement.correctionValue_eq_criticalFunction]
      rw [← QuotientDerivedNormalizedCriticalFunction.function_eq_critical F W q]
      exact W.toCriticalPolarFunction_reduce x hc
    unfold QuotientDerivedNormalizedCriticalFunction.liftValue at hvalue
    rw [criticalPolarValue, hunit] at hvalue
    have harg :
        (W.beta : F) * (W.delta : F) * x / ((W.Gamma : Fˣ) : F) =
          (W.beta : F) * c / ((W.Gamma : Fˣ) : F) := by
      dsimp only [x]
      field_simp
    rw [harg] at hvalue
    change
      (W.chi.character (Units.mk0 (1 + c) hone) : ℂ)⁻¹ =
        (W.psi.character (-((W.beta : F) * c /
          ((W.Gamma : Fˣ) : F))) : ℂ) *
          WildQuadraticRefinement.correctionValue q
            (W.affineCoefficient F q) (reduce F x hc)
    rw [hvalue, ← mul_assoc]
    have hcancel :
        (W.psi.character (-((W.beta : F) * c /
            ((W.Gamma : Fˣ) : F))) : ℂ) *
          (W.psi.character ((W.beta : F) * c /
            ((W.Gamma : Fˣ) : F)) : ℂ) = 1 := by
      have hmap := ContinuousAddChar.map_add_eq_mul W.psi.character
        (-((W.beta : F) * c / ((W.Gamma : Fˣ) : F)))
        ((W.beta : F) * c / ((W.Gamma : Fˣ) : F))
      have hmapC := congrArg (Units.val : ℂˣ → ℂ) hmap
      simpa using hmapC.symm
    rw [hcancel, one_mul]

/-- Transport the full correction record only along the exact local-data
equalities carried by the retained quotient source. -/
private noncomputable def wildQuadraticCorrectionForLocalData
    {F : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F))
    (theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (htheta : W.chi = theta) (hpsi : W.psi = psi)
    (c : F) (hc : c / (W.delta : F) ∈ lattice F 0)
    (hone : 1 + c ≠ 0) :
    WildQuadraticRefinementCorrection F (ResidueField F) psi theta q := by
  subst theta
  subst psi
  exact wildQuadraticCorrectionOfActualSource W q c hc hone

private theorem wildQuadraticCorrectionForLocalData_spec
    {F : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F))
    (theta : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (htheta : W.chi = theta) (hpsi : W.psi = psi)
    (c : F) (hc : c / (W.delta : F) ∈ lattice F 0)
    (hone : 1 + c ≠ 0) :
    let C := wildQuadraticCorrectionForLocalData W q theta psi htheta hpsi
      c hc hone
    C.correction = c ∧
      (C.Gamma : Fˣ) = W.Gamma ∧
      C.beta = (W.beta : F) ∧
      C.normalizedClass = reduce F (c / (W.delta : F)) hc ∧
      C.affineCoefficient = W.affineCoefficient F q := by
  subst theta
  subst psi
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The source-tied refined view -/

private noncomputable def wildQuadraticRefinementDerivedSources
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
    (view : WildQuadraticCommonCoefficientView F K t m)
    (source : view.criticalInputs.PositivePolarSource)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view data phaseData assembly)
    (continuation : WildQuadraticPositivePolarContinuation F K view source
      rows)
    (q : CharTwoRefinement (ResidueField F)) :
    WildQuadraticDerivedCriticalSources F K view.correction q
      view.criticalInputs view.stationaryPairs view.tauData view.chiFData
        view.psiF where
  tauChiF := continuation.lowerProduct q
  chiK := continuation.coordinate.upperCoordinates q

private noncomputable def wildQuadraticRefinedView
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
    (view : WildQuadraticCommonCoefficientView F K t m)
    (source : view.criticalInputs.PositivePolarSource)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view data phaseData assembly)
    (continuation : WildQuadraticPositivePolarContinuation F K view source
      rows)
    (q : CharTwoRefinement (ResidueField F)) :
    WildQuadraticCoefficientView F K q t m where
  conductor_gt_one := view.conductor_gt_one
  correction := view.correction
  oppositeNoncancellation := view.oppositeNoncancellation
  stationaryPairs := view.stationaryPairs
  chiK_ratio := view.chiK_ratio
  chiF_ratio := view.chiF_ratio
  tauChiF_ratio := view.tauChiF_ratio
  tauData := view.tauData
  chiFData := view.chiFData
  psiF := view.psiF
  criticalInputs := view.criticalInputs
  criticalInputs_row := view.criticalInputs_row
  criticalInputs_stationaryPairs := view.criticalInputs_stationaryPairs
  criticalInputs_localData := view.criticalInputs_localData
  criticalInputs_boundaryCoordinates := view.criticalInputs_boundaryCoordinates
  derivedCriticalSources :=
    wildQuadraticRefinementDerivedSources view source rows continuation q
  boundaryCoordinate := continuation.coordinate.matchesCorrection q

@[simp]
private theorem wildQuadraticRefinedView_toCommon
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
    (view : WildQuadraticCommonCoefficientView F K t m)
    (source : view.criticalInputs.PositivePolarSource)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view data phaseData assembly)
    (continuation : WildQuadraticPositivePolarContinuation F K view source
      rows)
    (q : CharTwoRefinement (ResidueField F)) :
    (wildQuadraticRefinedView view source rows continuation q).toCommon =
      view := by
  rfl

private noncomputable def wildQuadraticRefinedRows
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
    (view : WildQuadraticCommonCoefficientView F K t m)
    (source : view.criticalInputs.PositivePolarSource)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view data phaseData assembly)
    (continuation : WildQuadraticPositivePolarContinuation F K view source
      rows)
    (q : CharTwoRefinement (ResidueField F)) :
    WildQuadraticPhaseRowCompatibility
      (wildQuadraticRefinedView view source rows continuation q)
        data phaseData assembly where
  extensionRow := ⟨rows.extension, rows.extension_eq, rows.extension_pair,
    continuation.coordinate.extension_phase q⟩
  tauRow := ⟨rows.tau, rows.tau_eq, rows.tau_pair,
    continuation.tau_phase q⟩
  baseRow := ⟨rows.base, rows.base_eq, rows.base_pair,
    continuation.base_phase q⟩
  twistRow := ⟨rows.twist, rows.twist_eq, rows.twist_pair,
    continuation.twist_phase q⟩

/-! ## Rows with no selected lower correction -/

private theorem wildQuadraticRow_ne_boundary_of_tauClass_none
    {k : Type} [Field k] [Fintype k] [CharP k 2]
    (D : WildQuadraticCoefficientData k)
    (h : D.tauCorrectionClass = none) :
    D.row ≠ .boundaryOdd := by
  cases D <;> simp_all [WildQuadraticCoefficientData.row,
    WildQuadraticCoefficientData.tauCorrectionClass]

private theorem wildQuadratic_m_even_of_above_chiClass_none
    {k : Type} [Field k] [Fintype k] [CharP k 2]
    {t m : ℕ}
    (D : WildQuadraticCoefficientData.AtConductors k m t)
    (habove : t + 1 < m)
    (hchi : D.1.chiCorrectionClass = none) :
    Even m := by
  rcases D with ⟨D, hD⟩
  have hpred : t < m - 1 := by omega
  have hrange : D.row.range = .above := by
    rw [hD, WildQuadraticCoefficientRow.ofConductors_range_above hpred]
  have hmParity : D.row.mParity = .even := by
    cases D <;>
      simp_all [WildQuadraticCoefficientData.row,
        WildQuadraticCoefficientData.chiCorrectionClass,
        WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.mParity]
  apply (WildQuadraticConductorParity.ofConductor_eq_even_iff m).mp
  rw [← show m - 1 + 1 = m by omega,
    ← WildQuadraticCoefficientRow.ofConductors_mParity (m - 1) t,
    ← hD]
  exact hmParity

/-- In every positive-polar row selecting neither lower correction, the
actual common corrections lie in the ceiling-half lattices required for
pure stationary linearization. -/
private theorem wildQuadraticNoCorrection_xy_mem
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
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    (source : view.criticalInputs.PositivePolarSource)
    (hchiClass : view.coefficients.1.chiCorrectionClass = none)
    (htauClass : view.coefficients.1.tauCorrectionClass = none) :
    view.correction.x ∈ lattice F (((m + 1) / 2 : ℕ) : ℤ) ∧
      view.correction.y ∈
        lattice F ((((t + 1) + 1) / 2 : ℕ) : ℤ) := by
  have hrow : view.coefficients.1.row ≠ .boundaryOdd :=
    wildQuadraticRow_ne_boundary_of_tauClass_none view.coefficients.1
      htauClass
  have hcase := wildQuadratic_nonboundary_depthCase view.conductor_gt_one
    view.coefficients hrow
  let T : ℕ := t + 1
  let a : ℤ := (T : ℤ) - (m : ℤ)
  have hu : (view.correction.u : K) ∈ lattice K a := by
    rw [mem_lattice, view.correction.source_order]
  have hs : view.correction.s ∈ lattice F ((a + (T : ℤ)) / 2) := by
    have hs' := trace_mem_lattice_floor F K pi hpi hgen a hu
    rw [view.correction.differentExponent_eq,
      view.correction.ramificationIndex_eq_two] at hs'
    norm_num at hs'
    rw [mem_lattice]
    simpa only [WildQuadraticCommonCorrectionData.s, T, Nat.cast_add,
      Nat.cast_one] using hs'
  cases hcase with
  | below hbelow =>
      have ha : 0 < a := by dsimp only [a, T]; omega
      have hne : ord F (1 : F) ≠ ord F (view.correction.n : F) := by
        rw [ord_one, view.correction.target_order]
        change (0 : WithTop ℤ) ≠ (a : WithTop ℤ)
        exact ne_of_lt (by exact_mod_cast ha)
      have hden : ord F view.correction.denominator =
          (0 : WithTop ℤ) := by
        rw [WildQuadraticCommonCorrectionData.denominator,
          ord_add_eq_min F hne, ord_one, view.correction.target_order,
          min_eq_left]
        change (0 : WithTop ℤ) ≤ (a : WithTop ℤ)
        exact_mod_cast ha.le
      constructor
      · rw [view.correction.x_eq]
        apply (div_mem_lattice_iff F view.correction.denominator
          (-view.correction.s) 0 (((m + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          (0 : ℤ) + ((m + 1) / 2 : ℕ) ≤ (a + (T : ℤ)) / 2 by
            dsimp only [a, T]
            omega)
        exact neg_mem_lattice F hs
      · rw [view.correction.y_eq]
        apply (div_mem_lattice_iff F view.correction.denominator
          view.correction.s 0 ((((t + 1) + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          (0 : ℤ) + (((T + 1) / 2 : ℕ) : ℤ) ≤
              (a + (T : ℤ)) / 2 by
            dsimp only [a, T]
            omega)
        exact hs
  | boundaryEven hboundary hTEven =>
      have hpred : m - 1 = t := by omega
      have hparity : WildQuadraticConductorParity.ofConductor (t + 1) =
          .even :=
        (WildQuadraticConductorParity.ofConductor_eq_even_iff (t + 1)).mpr
          hTEven
      have hboundaryRow : view.coefficients.1.row = .boundaryEven := by
        rw [view.coefficients.2, hpred]
        simp [WildQuadraticCoefficientRow.ofConductors, hparity]
      have hpositive : view.coefficients.1.row.IsPositivePolar := by
        have hrowInput : view.coefficients.1.row =
            view.criticalInputs.row := by
          change (view.criticalInputs.toCoefficientData q).row = _
          exact WildQuadraticCoefficientInputs.toCoefficientData_row
            view.criticalInputs q
        rw [hrowInput]
        exact source.row_isPositivePolar
      rw [hboundaryRow] at hpositive
      cases hpositive
  | above habove =>
      have ha : a < 0 := by dsimp only [a, T]; omega
      have hne : ord F (1 : F) ≠ ord F (view.correction.n : F) := by
        rw [ord_one, view.correction.target_order]
        change (0 : WithTop ℤ) ≠ (a : WithTop ℤ)
        exact Ne.symm (ne_of_lt (by exact_mod_cast ha))
      have hden : ord F view.correction.denominator =
          (a : WithTop ℤ) := by
        rw [WildQuadraticCommonCorrectionData.denominator,
          ord_add_eq_min F hne, ord_one, view.correction.target_order,
          min_eq_right]
        change (a : WithTop ℤ) ≤ (0 : WithTop ℤ)
        exact_mod_cast ha.le
      have hmEven : Even m :=
        wildQuadratic_m_even_of_above_chiClass_none view.coefficients habove
          hchiClass
      obtain ⟨jm, hjm⟩ := hmEven
      constructor
      · rw [view.correction.x_eq]
        apply (div_mem_lattice_iff F view.correction.denominator
          (-view.correction.s) a (((m + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          a + (((m + 1) / 2 : ℕ) : ℤ) ≤
              (a + (T : ℤ)) / 2 by
            dsimp only [a, T]
            omega)
        exact neg_mem_lattice F hs
      · rw [view.correction.y_eq]
        apply (div_mem_lattice_iff F view.correction.denominator
          view.correction.s a ((((t + 1) + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          a + (((T + 1) / 2 : ℕ) : ℤ) ≤
              (a + (T : ℤ)) / 2 by
            dsimp only [a, T]
            omega)
        exact hs

private theorem wildQuadraticNoCorrection_inverseIdentities
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
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view.toCommon data phaseData assembly)
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (source : view.criticalInputs.PositivePolarSource)
    (hchiClass : view.coefficients.1.chiCorrectionClass = none)
    (htauClass : view.coefficients.1.tauCorrectionClass = none) :
    (view.chiFData.character assembly.zZero : ℂ)⁻¹ =
        (view.psiF.character
          (-assembly.A * assembly.n * assembly.x) : ℂ) ∧
      (view.tauData.character assembly.zOne : ℂ)⁻¹ =
        (view.psiF.character (-assembly.A * assembly.y) : ℂ) := by
  have hxy := wildQuadraticNoCorrection_xy_mem pi hpi hgen view source
    hchiClass htauClass
  have hx : assembly.x ∈ lattice F
      ((((data.twistData 1).conductor + 1) / 2 : ℕ) : ℤ) := by
    rw [coordinates.baseData_eq,
      wildQuadratic_base_conductor_eq coordinates, coordinates.x_eq]
    exact hxy.1
  have hy : assembly.y ∈ lattice F
      ((((data.normCharacterData assembly.indexing.tau).conductor + 1) / 2 : ℕ) : ℤ) := by
    rw [wildQuadratic_tau_conductor_eq ht hres pi hpi hgen,
      coordinates.y_eq]
    exact hxy.2
  have hbaseFactor :=
    wildQuadratic_stationaryUnitFactor_eq_one_of_mem_ceilingHalf
      rows.base view.stationaryPairs.chiF rows.base_pair assembly.x hx
        assembly.zZero assembly.zZero_eq
  have htauFactor :=
    wildQuadratic_stationaryUnitFactor_eq_one_of_mem_ceilingHalf
      rows.tau view.stationaryPairs.tau rows.tau_pair assembly.y hy
        assembly.zOne assembly.zOne_eq
  constructor
  · unfold stationaryUnitFactor at hbaseFactor
    rw [coordinates.baseData_eq, coordinates.baseAddData_eq,
      view.chiF_ratio, ← coordinates.A_eq, ← coordinates.n_eq,
      assembly.zZero_eq] at hbaseFactor
    have hfactor :
        (view.psiF.character
            (assembly.A * assembly.n * assembly.x) : ℂ) *
          (view.chiFData.character assembly.zZero : ℂ)⁻¹ = 1 := by
      simpa only [add_sub_cancel_left, mul_assoc] using hbaseFactor
    have hinv :
        (view.chiFData.character assembly.zZero : ℂ)⁻¹ =
          (view.psiF.character
            (assembly.A * assembly.n * assembly.x) : ℂ)⁻¹ :=
      eq_inv_of_mul_eq_one_right hfactor
    rw [hinv]
    have hneg := congrArg (Units.val : ℂˣ → ℂ)
      (AddChar.map_neg_eq_inv view.psiF.character.toAddChar
        (assembly.A * assembly.n * assembly.x))
    calc
      (view.psiF.character
          (assembly.A * assembly.n * assembly.x) : ℂ)⁻¹ =
          (view.psiF.character
            (-(assembly.A * assembly.n * assembly.x)) : ℂ) := by
        simpa only [ContinuousAddChar.toAddChar_apply,
          Units.val_inv_eq_inv_val] using hneg.symm
      _ = (view.psiF.character
          (-assembly.A * assembly.n * assembly.x) : ℂ) := by ring_nf
  · unfold stationaryUnitFactor at htauFactor
    rw [coordinates.tauData_eq, coordinates.baseAddData_eq,
      ← coordinates.A_eq, assembly.zOne_eq] at htauFactor
    have hfactor :
        (view.psiF.character (assembly.A * assembly.y) : ℂ) *
          (view.tauData.character assembly.zOne : ℂ)⁻¹ = 1 := by
      simpa only [add_sub_cancel_left] using htauFactor
    have hinv :
        (view.tauData.character assembly.zOne : ℂ)⁻¹ =
          (view.psiF.character (assembly.A * assembly.y) : ℂ)⁻¹ :=
      eq_inv_of_mul_eq_one_right hfactor
    rw [hinv]
    have hneg := congrArg (Units.val : ℂˣ → ℂ)
      (AddChar.map_neg_eq_inv view.psiF.character.toAddChar
        (assembly.A * assembly.y))
    calc
      (view.psiF.character (assembly.A * assembly.y) : ℂ)⁻¹ =
          (view.psiF.character (-(assembly.A * assembly.y)) : ℂ) := by
        simpa only [ContinuousAddChar.toAddChar_apply,
          Units.val_inv_eq_inv_val] using hneg.symm
      _ = (view.psiF.character (-assembly.A * assembly.y) : ℂ) := by
        ring_nf

/-- Complete assembly for the four positive-polar rows in which neither
lower correction is selected. -/
private noncomputable def wildQuadraticNoCorrectionAssembly
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
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view.toCommon data phaseData assembly)
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (source : view.criticalInputs.PositivePolarSource)
    (hchiClass : view.coefficients.1.chiCorrectionClass = none)
    (htauClass : view.coefficients.1.tauCorrectionClass = none) :
    WildQuadraticRefinementAssembly view data phaseData assembly coordinates :=
  let identities := wildQuadraticNoCorrection_inverseIdentities ht hres pi
    hpi hgen view rows coordinates source hchiClass htauClass
  { chiCorrection := none
    tauCorrection := none
    chi_selection := by
      simpa only [Option.map_none] using hchiClass.symm
    tau_selection := by
      simpa only [Option.map_none] using htauClass.symm
    chi_absent := fun _ ↦ identities.1
    tau_absent := fun _ ↦ identities.2
    chi_present := by simp
    tau_present := by simp }

/-! ## Completed correction payload -/

/-- The two objects that remain after the refined view and its actual rows
have been constructed.  Packaging them together ensures that the corrections
exhibited at the odd boundary are literally those selected by the assembly. -/
private structure WildQuadraticRefinementCompletion
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
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (view : WildQuadraticCoefficientView F K q t m)
    (data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character)
    (phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data)
    (assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m))
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly) where
  refinements : WildQuadraticRefinementAssembly view data phaseData assembly
    coordinates
  mixedBoundary : (2 : F) ≠ 0 →
    view.coefficients.1.row = .boundaryOdd →
      ∃ (boundary : WildQuadraticBoundaryData (ResidueField F))
        (chiCorrection : WildQuadraticRefinementCorrection F
          (ResidueField F) view.psiF view.chiFData q)
        (tauCorrection : WildQuadraticRefinementCorrection F
          (ResidueField F) view.psiF view.tauData q),
        WildQuadraticBoundaryCompatibility
            (V := view) (A := assembly) boundary ∧
          refinements.chiCorrection = some chiCorrection ∧
          refinements.tauCorrection = some tauCorrection

private noncomputable def wildQuadraticNoCorrectionCompletion
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
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view.toCommon data phaseData assembly)
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (source : view.criticalInputs.PositivePolarSource)
    (hchiClass : view.coefficients.1.chiCorrectionClass = none)
    (htauClass : view.coefficients.1.tauCorrectionClass = none) :
    WildQuadraticRefinementCompletion view data phaseData assembly
      coordinates := by
  let refinements := wildQuadraticNoCorrectionAssembly ht hres pi hpi hgen
    view rows coordinates source hchiClass htauClass
  refine ⟨refinements, ?_⟩
  intro _ hboundary
  exact (wildQuadraticRow_ne_boundary_of_tauClass_none view.coefficients.1
    htauClass hboundary).elim

/-! The remaining construction is the exact branch-sensitive correction
assembly and mixed-boundary compatibility. -/

section BoundaryCompletion

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

private theorem boundaryUnit_mem (u : unitGroup F) :
    ((u : Fˣ) : F) ∈ lattice F 0 :=
  (mem_lattice_zero_iff F).2
    (((unitGroupMulEquivRingOfIntegers F u : (ringOfIntegers F)ˣ) :
      ringOfIntegers F).property)

private theorem boundaryReduce_mul (x : F) (hx : x ∈ lattice F 0)
    (u : unitGroup F) :
    reduce F (x * ((u : Fˣ) : F))
        (mul_mem_lattice F hx (boundaryUnit_mem u)) =
      reduce F x hx *
        ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) := by
  let xO : ringOfIntegers F := ⟨x, (mem_lattice_zero_iff F).1 hx⟩
  change residueMap F
    (xO * (unitGroupMulEquivRingOfIntegers F u : (ringOfIntegers F)ˣ)) = _
  rw [map_mul, ← residueUnits_coe]
  rfl

private theorem boundaryReduce_mul_two (x : F) (hx : x ∈ lattice F 0)
    (u v : unitGroup F) :
    reduce F (x * ((u : Fˣ) : F) * ((v : Fˣ) : F))
        (mul_mem_lattice F (mul_mem_lattice F hx (boundaryUnit_mem u))
          (boundaryUnit_mem v)) =
      reduce F x hx *
        ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) *
          ((residueUnits F v : (ResidueField F)ˣ) : ResidueField F) := by
  let xO : ringOfIntegers F := ⟨x, (mem_lattice_zero_iff F).1 hx⟩
  change residueMap F
    (xO * (unitGroupMulEquivRingOfIntegers F u : (ringOfIntegers F)ˣ) *
      (unitGroupMulEquivRingOfIntegers F v : (ringOfIntegers F)ˣ)) = _
  rw [map_mul, map_mul, ← residueUnits_coe, ← residueUnits_coe]
  rfl

private theorem boundaryNormDelta_residue_one
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {t m : ℕ} (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (tau : NormCharacter F K) (htheta : W.chi.character = tau.1)
    (hT : ((t + 1 : ℕ) : ℤ) = 2 * (W.d : ℤ) + 1)
    (h2 : (2 : F) ≠ 0) :
    let two : Fˣ := Units.mk0 (2 : F) h2
    let ratio : Fˣ := W.delta / two
    let hratio : ord F (ratio : F) = (0 : WithTop ℤ) := by
      simp only [ratio, Units.val_div_eq_div_val]
      rw [ord_div, W.delta_order]
      change ((W.d : ℤ) : WithTop ℤ) - ord F (2 : F) = 0
      rw [quadratic_ord_two F K pi hpi hgen C.ramificationIndex_eq_two
        C.degree_eq_two (by rw [C.differentExponent_eq]; exact hT)]
      simp
    let u : unitGroup F :=
      ⟨ratio, (mem_unitGroup_iff_ord_eq_zero F ratio).2 hratio⟩
    ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) = 1 := by
  dsimp only
  let two : Fˣ := Units.mk0 (2 : F) h2
  have htwo : ord F (two : F) = ((W.d : ℤ) : WithTop ℤ) := by
    change ord F (2 : F) = ((W.d : ℤ) : WithTop ℤ)
    apply quadratic_ord_two F K pi hpi hgen C.ramificationIndex_eq_two
      C.degree_eq_two
    rw [C.differentExponent_eq]
    exact hT
  let phi := criticalPolarAddChar F W.chi W.psi W.d W.conductor_eq
    W.conductor_gt_one W.Gamma two htwo
  have hdpos : 0 < W.d := by
    have hm := W.conductor_eq
    have hlarge := W.conductor_gt_one
    omega
  have hAS : ∀ c : ResidueField F, phi (c + c ^ 2) = 1 := by
    intro c
    let aO : ringOfIntegers F := teichmuller F c
    let z : F := (aO : F) + (aO : F) ^ 2
    have hz : z ∈ lattice F 0 := by
      apply add_mem_lattice F
      · exact (mem_lattice_zero_iff F).2 aO.property
      · have ha := (mem_lattice_zero_iff F).2 aO.property
        simpa only [pow_two, zero_add] using mul_mem_lattice F ha ha
    have hzred : reduce F z hz = c + c ^ 2 := by
      change residueMap F (aO + aO ^ 2) = _
      rw [map_add, map_pow, residueMap_teichmuller]
    have hval := criticalPolarAddChar_integral_lift F W.chi W.psi W.d
      W.conductor_eq W.conductor_gt_one W.Gamma two htwo W.beta
      W.beta_class z hz
    rw [hzred] at hval
    rw [hval]
    let hr := criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
      W.conductor_gt_one
    let xv : F := (two : F) ^ 2 * z
    have hxv : xv ∈ lattice F ((W.d + 1 : ℕ) : ℤ) := by
      have hd : (two : F) ∈ lattice F (W.d : ℤ) := by
        rw [mem_lattice, htwo]
      apply lattice_antitone F (show ((W.d + 1 : ℕ) : ℤ) ≤
        (W.d : ℤ) + W.d + 0 by
          have := hr.pos
          omega)
      simpa [xv, pow_two] using mul_mem_lattice F
        (mul_mem_lattice F hd hd) hz
    let x : lattice F ((W.d + 1 : ℕ) : ℤ) := ⟨xv, hxv⟩
    have hlin := stationaryNumeratorClass_linearization F W.chi W.psi
      W.chi.conductor hr W.Gamma W.Gamma.property W.beta W.beta_class x
    have hnorm : (positiveUnitOfLattice F hr.pos x : Fˣ) ∈
        (normUnits F K).range := by
      let xa : lattice F 1 := ⟨(2 : F) * (aO : F), by
        apply lattice_antitone F (show (1 : ℤ) ≤ (W.d : ℤ) + 0 by
          omega)
        exact mul_mem_lattice F (by
          rw [mem_lattice]
          simpa only [two, Units.val_mk0] using htwo.ge)
          ((mem_lattice_zero_iff F).2 aO.property)⟩
      let lower : Fˣ := positiveUnitOfLattice F (by omega : 0 < 1) xa
      refine ⟨Units.map (algebraMap F K) lower, ?_⟩
      apply Units.ext
      simp only [coe_normUnits, Units.coe_map, coe_positiveUnitOfLattice,
        lower, xa, x, xv, two, Units.val_mk0, z]
      change norm F K (algebraMap F K (1 + 2 * (aO : F))) = _
      rw [norm_algebraMap, C.degree_eq_two]
      ring
    have hone := tau.eq_one_on_normRange F K
      (positiveUnitOfLattice F hr.pos x) hnorm
    have hchi : W.chi.character (positiveUnitOfLattice F hr.pos x) = 1 := by
      rw [htheta]
      exact hone
    have hpsi := congrArg (Units.val : ℂˣ → ℂ) (hlin.symm.trans hchi)
    have harg : (W.beta : F) * (x : F) / ((W.Gamma : Fˣ) : F) =
        (W.beta : F) * (two : F) ^ 2 * z / ((W.Gamma : Fˣ) : F) := by
      simp only [x, xv]
      ring
    rw [harg] at hpsi
    simpa using hpsi
  have hphi : phi = absoluteTraceChar (ResidueField F) :=
    absoluteTraceChar_eq_of_artinSchreier_trivial (ResidueField F)
      (criticalPolarAddChar_ne_one F W.chi W.psi W.d W.conductor_eq
        W.conductor_gt_one W.Gamma two htwo) hAS
  have hcanonical : criticalPolarCoefficient F W.chi W.psi W.d
      W.conductor_eq W.conductor_gt_one W.Gamma two htwo
      (absoluteTraceChar (ResidueField F))
      (absoluteTraceChar_ne_one (ResidueField F)) = 1 := by
    change finiteAddCharCoefficient (absoluteTraceChar (ResidueField F))
      (absoluteTraceChar_ne_one (ResidueField F)) phi = 1
    apply finiteAddCharCoefficient_unique
    rw [hphi, AddChar.mulShift_one]
  let ratio : Fˣ := W.delta / two
  have hratio : ord F (ratio : F) = (0 : WithTop ℤ) := by
    simp only [ratio, Units.val_div_eq_div_val]
    rw [ord_div, W.delta_order, htwo]
    simp
  let u : unitGroup F :=
    ⟨ratio, (mem_unitGroup_iff_ord_eq_zero F ratio).2 hratio⟩
  have hcoord : W.delta = criticalPolarScaledCoordinate F u two := by
    apply Units.ext
    simp only [criticalPolarScaledCoordinate, u, ratio, two, Units.val_mul,
      Units.val_div_eq_div_val, Units.val_mk0]
    field_simp [h2]
  have hs := criticalPolarCoefficient_scaleCoordinate F W.chi W.psi W.d
    W.conductor_eq W.conductor_gt_one W.Gamma two htwo
    (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F)) u
  have hsq :
      ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2 = 1 := by
    have hscaled :
        criticalPolarCoefficient F W.chi W.psi W.d W.conductor_eq
          W.conductor_gt_one W.Gamma
          (criticalPolarScaledCoordinate F u two)
          (criticalPolarScaledCoordinate_ord F W.d u two htwo)
          (absoluteTraceChar (ResidueField F))
          (absoluteTraceChar_ne_one (ResidueField F)) = 1 := by
      simpa only [hcoord] using W.polar_eq_one
    rw [hs, hcanonical, mul_one] at hscaled
    exact hscaled
  apply CharTwo.sq_injective
  simpa using hsq

private theorem boundaryCore
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {t m : ℕ} (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (rho : ResidueField F) (hden : 1 + rho ≠ 0)
    (Wtau Wchi : QuotientDerivedNormalizedCriticalFunction F)
    (BC : WildQuadraticBoundaryCorrectionCoordinate F K C rho Wtau Wchi)
    (tau : NormCharacter F K) (htheta : Wtau.chi.character = tau.1)
    (hT : ((t + 1 : ℕ) : ℤ) = 2 * (Wtau.d : ℤ) + 1)
    (h2 : (2 : F) ≠ 0) (A X : F)
    (hA : A = (Wtau.beta : F) / ((Wtau.Gamma : Fˣ) : F))
    (hX : X = 2 * C.y) :
    ∃ (hy : C.y / (Wtau.delta : F) ∈ lattice F 0)
      (hx : C.x / (Wchi.delta : F) ∈ lattice F 0),
      reduce F (C.y / (Wtau.delta : F)) hy = rho / (1 + rho ^ 2) ∧
      reduce F (C.x / (Wchi.delta : F)) hx = rho ^ 2 / (1 + rho ^ 2) ∧
      (Wtau.psi.character (-A * X) : ℂ) =
        absoluteTraceChar (ResidueField F) (rho / (1 + rho ^ 2)) := by
  have htwo : ord F (2 : F) = ((Wtau.d : ℤ) : WithTop ℤ) := by
    apply quadratic_ord_two F K pi hpi hgen C.ramificationIndex_eq_two
      C.degree_eq_two
    rw [C.differentExponent_eq]
    exact hT
  have hnmem : (C.n : F) ∈ lattice F 0 := by
    rw [mem_lattice, C.target_order, BC.boundary]
    simp
  let nO : ringOfIntegers F :=
    ⟨(C.n : F), (mem_lattice_zero_iff F).1 hnmem⟩
  have hnred : residueMap F nO = rho ^ 2 := by
    change reduce F (C.n : F) hnmem = rho ^ 2
    simpa only [WildQuadraticCoefficientData.boundaryNResidue] using
      BC.norm_residue
  have hdenSq : 1 + rho ^ 2 ≠ 0 := by
    rw [show 1 + rho ^ 2 = (1 + rho) ^ 2 by
      rw [CharTwo.add_sq, one_pow]]
    exact pow_ne_zero 2 hden
  have hdenmem : C.denominator ∈ lattice F 0 :=
    add_mem_lattice F (by simp) hnmem
  let denO : ringOfIntegers F :=
    ⟨C.denominator, (mem_lattice_zero_iff F).1 hdenmem⟩
  have hdenred : residueMap F denO = 1 + rho ^ 2 := by
    change residueMap F (1 + nO) = _
    rw [map_add, map_one, hnred]
  have hdenUnit : IsUnit denO :=
    (IsLocalRing.residue_ne_zero_iff_isUnit denO).1 (by
      rw [hdenred]
      exact hdenSq)
  let du : unitGroup F :=
    (unitGroupMulEquivRingOfIntegers F).symm hdenUnit.unit
  have hdu : ((du : Fˣ) : F) = C.denominator := by
    change (((hdenUnit.unit : (ringOfIntegers F)ˣ) :
      ringOfIntegers F) : F) = C.denominator
    rw [hdenUnit.unit_spec]
  have hdured :
      ((residueUnits F du : (ResidueField F)ˣ) : ResidueField F) =
        1 + rho ^ 2 := by
    change residueMap F
      ((unitGroupMulEquivRingOfIntegers F du : (ringOfIntegers F)ˣ) :
        ringOfIntegers F) = _
    rw [show unitGroupMulEquivRingOfIntegers F du = hdenUnit.unit by
      exact (unitGroupMulEquivRingOfIntegers F).apply_symm_apply _]
    rw [hdenUnit.unit_spec]
    exact hdenred
  let wO : ringOfIntegers F := teichmuller F rho
  have htrace := wildQuadraticBoundary_trace_congr F K pi hpi hgen C
    BC.boundary hT wO (by
      change residueMap K
        (wildQuadraticBoundaryRingUnit F K C BC.boundary :
          ringOfIntegers K) =
        extensionResidueMap F K (residueMap F (teichmuller F rho))
      rw [residueMap_teichmuller]
      simpa only [BC.common.rhoLift_residue] using BC.source_residue)
  have htwoMem : (2 : F) ∈ lattice F (Wtau.d : ℤ) := by
    rw [mem_lattice, htwo]
  have hwMem : (wO : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 wO.property
  have htwoW : 2 * (wO : F) ∈ lattice F (Wtau.d : ℤ) := by
    simpa only [add_zero] using mul_mem_lattice F htwoMem hwMem
  have herrorD : C.s - 2 * (wO : F) ∈ lattice F (Wtau.d : ℤ) :=
    lattice_antitone F (by omega) htrace
  have hsMem : C.s ∈ lattice F (Wtau.d : ℤ) := by
    have hadd := add_mem_lattice F herrorD htwoW
    convert hadd using 1
    ring
  have hsover : C.s / (2 : F) ∈ lattice F 0 :=
    (div_mem_lattice_iff F (2 : F) C.s (Wtau.d : ℤ) 0 htwo).2
      (by simpa only [add_zero] using hsMem)
  have hsoverRed : reduce F (C.s / (2 : F)) hsover = rho := by
    have hd : C.s / (2 : F) - (wO : F) ∈ lattice F 1 := by
      have h := (div_mem_lattice_iff F (2 : F)
        (C.s - (2 : F) * (wO : F)) (Wtau.d : ℤ) 1 htwo).2
          (by simpa only [add_comm] using htrace)
      convert h using 1
      field_simp [h2]
    rw [(reduce_eq_reduce_iff (F := F) hsover
      hwMem).2
        ((congruentAtDepth_iff_sub_mem_lattice F 1 _ _).2 hd)]
    exact residueMap_teichmuller F rho
  let two : Fˣ := Units.mk0 (2 : F) h2
  let ratio : Fˣ := Wtau.delta / two
  have hratio : ord F (ratio : F) = (0 : WithTop ℤ) := by
    simp only [ratio, Units.val_div_eq_div_val]
    rw [ord_div, Wtau.delta_order]
    change ((Wtau.d : ℤ) : WithTop ℤ) - ord F (2 : F) = 0
    rw [htwo]
    simp
  let ru : unitGroup F :=
    ⟨ratio, (mem_unitGroup_iff_ord_eq_zero F ratio).2 hratio⟩
  have hrured :
      ((residueUnits F ru : (ResidueField F)ˣ) : ResidueField F) = 1 := by
    simpa only [two, ratio, hratio, ru] using
      boundaryNormDelta_residue_one pi hpi hgen C Wtau tau htheta hT h2
  have hduInv : (((du⁻¹ : unitGroup F) : Fˣ) : F) =
      C.denominator⁻¹ := by
    have : ((du⁻¹ : unitGroup F) : Fˣ) = ((du : unitGroup F) : Fˣ)⁻¹ := rfl
    rw [this, Units.val_inv_eq_inv_val, hdu]
  have hruInv : (((ru⁻¹ : unitGroup F) : Fˣ) : F) =
      ((Wtau.delta : F) / (2 : F))⁻¹ := by
    have : ((ru⁻¹ : unitGroup F) : Fˣ) = ((ru : unitGroup F) : Fˣ)⁻¹ := rfl
    rw [this, Units.val_inv_eq_inv_val]
    simp only [ru, ratio, two, Units.val_div_eq_div_val, Units.val_mk0]
  let y0 := (C.s / (2 : F)) * (((du⁻¹ : unitGroup F) : Fˣ) : F) *
    (((ru⁻¹ : unitGroup F) : Fˣ) : F)
  have hy0 : y0 ∈ lattice F 0 := mul_mem_lattice F
    (mul_mem_lattice F hsover (boundaryUnit_mem du⁻¹))
    (boundaryUnit_mem ru⁻¹)
  have hyEq : C.y / (Wtau.delta : F) = y0 := by
    rw [C.y_eq]
    dsimp only [y0]
    rw [hduInv, hruInv]
    field_simp [h2, C.denominator_ne_zero', Units.ne_zero Wtau.delta]
  have hyReduce0 : reduce F y0 hy0 = rho / (1 + rho ^ 2) := by
    have h := boundaryReduce_mul_two (C.s / (2 : F)) hsover du⁻¹ ru⁻¹
    rw [h]
    simp only [map_inv, Units.val_inv_eq_inv_val, hsoverRed, hdured,
      hrured, inv_one, mul_one]
    simp [div_eq_mul_inv]
  let hy : C.y / (Wtau.delta : F) ∈ lattice F 0 := by
    rw [hyEq]
    exact hy0
  have hyred : reduce F (C.y / (Wtau.delta : F)) hy =
      rho / (1 + rho ^ 2) := by
    simpa only [hy, hyEq] using hyReduce0
  have hcoord := congrArg Units.val BC.common.coordinate_eq
  simp only [criticalPolarScaledCoordinate, Units.val_mul] at hcoord
  let x0 := (-(C.y / (Wtau.delta : F))) *
    (((BC.common.rhoLift : unitGroup F) : Fˣ) : F)
  have hnegY : -(C.y / (Wtau.delta : F)) ∈ lattice F 0 :=
    neg_mem_lattice F hy
  have hx0 : x0 ∈ lattice F 0 := mul_mem_lattice F
    hnegY (boundaryUnit_mem BC.common.rhoLift)
  have hxEq : C.x / (Wchi.delta : F) = x0 := by
    have hxy : C.x = -C.y := by rw [C.x_eq, C.y_eq]; ring
    rw [hxy]
    dsimp only [x0]
    rw [hcoord]
    field_simp [Units.ne_zero Wtau.delta, Units.ne_zero Wchi.delta,
      Units.ne_zero (BC.common.rhoLift : Fˣ)]
  have hxReduce0 : reduce F x0 hx0 = rho ^ 2 / (1 + rho ^ 2) := by
    have hred := boundaryReduce_mul (-(C.y / (Wtau.delta : F))) hnegY
      BC.common.rhoLift
    change reduce F x0 hx0 = _
    rw [hred]
    have hneg : reduce F (-(C.y / (Wtau.delta : F)))
        hnegY = -(rho / (1 + rho ^ 2)) := by
      change residueMap F (-⟨C.y / (Wtau.delta : F),
        (mem_lattice_zero_iff F).1 hy⟩) = _
      rw [map_neg]
      exact congrArg Neg.neg hyred
    rw [hneg, BC.common.rhoLift_residue]
    have hchar : (2 : ResidueField F) = 0 :=
      CharP.cast_eq_zero (ResidueField F) 2
    have hnegRho : -(rho / (1 + rho ^ 2)) = rho / (1 + rho ^ 2) := by
      apply neg_eq_of_add_eq_zero_right
      rw [← two_mul, hchar, zero_mul]
    rw [hnegRho]
    field_simp [hdenSq]
  let hx : C.x / (Wchi.delta : F) ∈ lattice F 0 := by
    rw [hxEq]
    exact hx0
  have hxred : reduce F (C.x / (Wchi.delta : F)) hx =
      rho ^ 2 / (1 + rho ^ 2) := by
    simpa only [hx, hxEq] using hxReduce0
  let z := (-(C.y / (Wtau.delta : F))) *
    (((ru⁻¹ : unitGroup F) : Fˣ) : F)
  have hz : z ∈ lattice F 0 := mul_mem_lattice F
    hnegY (boundaryUnit_mem ru⁻¹)
  have hzred : reduce F z hz = rho / (1 + rho ^ 2) := by
    have hred := boundaryReduce_mul (-(C.y / (Wtau.delta : F))) hnegY ru⁻¹
    change reduce F z hz = _
    rw [hred]
    have hn : reduce F (-(C.y / (Wtau.delta : F)))
        hnegY = -(rho / (1 + rho ^ 2)) := by
      change residueMap F (-⟨C.y / (Wtau.delta : F),
        (mem_lattice_zero_iff F).1 hy⟩) = _
      rw [map_neg]
      exact congrArg Neg.neg hyred
    rw [hn, map_inv, Units.val_inv_eq_inv_val, hrured, inv_one, mul_one]
    have hchar : (2 : ResidueField F) = 0 :=
      CharP.cast_eq_zero (ResidueField F) 2
    apply neg_eq_of_add_eq_zero_right
    rw [← two_mul, hchar, zero_mul]
  have harg : (Wtau.beta : F) * (Wtau.delta : F) ^ 2 * z /
      ((Wtau.Gamma : Fˣ) : F) = -A * X := by
    rw [hA, hX]
    dsimp only [z]
    rw [hruInv]
    field_simp [h2, Units.ne_zero Wtau.delta,
      AdmissibleGamma.coe_ne_zero Wtau.Gamma]
  have hp := criticalPolarCoefficient_integral_lift F Wtau.chi Wtau.psi
    Wtau.d Wtau.conductor_eq Wtau.conductor_gt_one Wtau.Gamma Wtau.delta
    Wtau.delta_order (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F)) Wtau.beta Wtau.beta_class z hz
  rw [Wtau.polar_eq_one, one_mul, hzred, harg] at hp
  exact ⟨hy, hx, hyred, hxred, hp.symm⟩

private noncomputable def wildQuadraticBoundaryCompletion
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
    (Wtau Wchi : QuotientDerivedNormalizedCriticalFunction F)
    (hinputs : view.criticalInputs = .boundaryOdd rho hrho hden Wtau Wchi)
    (h2 : (2 : F) ≠ 0) :
    WildQuadraticRefinementCompletion view data phaseData assembly
      coordinates := by
  have hpairs := view.criticalInputs_stationaryPairs
  have hlocal := view.criticalInputs_localData
  rw [hinputs] at hpairs hlocal
  have htauNe : assembly.indexing.tau ≠ 1 := by
    intro heq
    apply Bool.false_ne_true
    apply assembly.indexing.index.injective
    rw [assembly.indexing.index_false, assembly.indexing.index_true, heq]
  have htauIsConductor : IsMultiplicativeConductor F
      (data.normCharacterData assembly.indexing.tau).character (t + 1) := by
    rw [data.normCharacterData_character]
    exact ramifiedNormCharacter_conductor F K ht
      view.correction.residueDegree_eq_one pi hpi hgen _ htauNe
  have htauConductor :
      (data.normCharacterData assembly.indexing.tau).conductor = t + 1 :=
    (LocalQuasiCharData.conductor_eq_of_isConductor _ htauIsConductor).symm
  have hWtauConductor : Wtau.chi.conductor = t + 1 := by
    rw [hlocal.1.1, ← coordinates.tauData_eq, htauConductor]
  have hTnat : t + 1 = 2 * Wtau.d + 1 := by
    rw [← hWtauConductor, Wtau.conductor_eq]
  have hT : ((t + 1 : ℕ) : ℤ) = 2 * (Wtau.d : ℤ) + 1 := by
    exact_mod_cast hTnat
  have htheta : Wtau.chi.character = assembly.indexing.tau.1 := by
    rw [hlocal.1.1, ← coordinates.tauData_eq,
      data.normCharacterData_character]
  have hBC0 := view.boundaryCorrectionCoordinate
  rw [hinputs] at hBC0
  let BC := Classical.choice hBC0
  have htauRatio : (Wtau.beta : F) / ((Wtau.Gamma : Fˣ) : F) =
      assembly.A := by
    rw [hpairs.1.1, hpairs.1.2]
    exact coordinates.A_eq.symm
  have hX : view.correction.X = 2 * view.correction.y := by
    rw [view.correction.X_eq, view.correction.y_eq]
    ring
  let hcore := boundaryCore pi hpi hgen view.correction rho hden Wtau Wchi
    BC assembly.indexing.tau htheta hT h2 assembly.A view.correction.X
      htauRatio.symm hX
  let hy := hcore.choose
  let hx := hcore.choose_spec.choose
  have hyred := hcore.choose_spec.choose_spec.1
  have hxred := hcore.choose_spec.choose_spec.2.1
  have helemW := hcore.choose_spec.choose_spec.2.2
  let r := WildQuadraticRefinement.squareRoot rho
  let gammaZero := Wtau.affineCoefficient F q
  let gamma := Wchi.affineCoefficient F q
  let gammaPrime := WildQuadraticRefinement.squareRoot
    ((gamma + rho * gammaZero + rho + r) / (1 + rho))
  let boundary : WildQuadraticBoundaryData (ResidueField F) :=
    { rho := rho
      r := r
      gammaZero := gammaZero
      gamma := gamma
      gammaPrime := gammaPrime
      rho_ne_zero := hrho
      r_sq := WildQuadraticRefinement.squareRoot_sq rho
      one_add_rho_ne_zero := hden
      gammaPrime_sq := WildQuadraticRefinement.squareRoot_sq _ }
  have hcoeff : view.coefficients.1 = boundary.coefficientData := by
    change view.criticalInputs.toCoefficientData q = boundary.coefficientData
    rw [hinputs]
    rfl
  have hchiOne : 1 + view.correction.x ≠ 0 := by
    intro hz
    apply view.correction.z0_ne_zero view.oppositeNoncancellation
    rw [show view.correction.z0 = 1 + view.correction.x by
      rw [WildQuadraticCommonCorrectionData.x]; ring, hz]
  have htauOne : 1 + view.correction.y ≠ 0 := by
    intro hz
    apply view.correction.z1_ne_zero view.oppositeNoncancellation
    rw [show view.correction.z1 = 1 + view.correction.y by
      rw [WildQuadraticCommonCorrectionData.y]; ring, hz]
  let chiCorrection := wildQuadraticCorrectionForLocalData Wchi q
    view.chiFData view.psiF hlocal.2.1 hlocal.2.2 view.correction.x hx
      hchiOne
  let tauCorrection := wildQuadraticCorrectionForLocalData Wtau q
    view.tauData view.psiF hlocal.1.1 hlocal.1.2 view.correction.y hy
      htauOne
  have hchiSpec := wildQuadraticCorrectionForLocalData_spec Wchi q
    view.chiFData view.psiF hlocal.2.1 hlocal.2.2 view.correction.x hx
      hchiOne
  have htauSpec := wildQuadraticCorrectionForLocalData_spec Wtau q
    view.tauData view.psiF hlocal.1.1 hlocal.1.2 view.correction.y hy
      htauOne
  have hchiRatio : (Wchi.beta : F) / ((Wchi.Gamma : Fˣ) : F) =
      assembly.A * assembly.n := by
    rw [hpairs.2.1, hpairs.2.2]
    change view.stationaryPairs.chiF.ratio = _
    rw [view.chiF_ratio,
      coordinates.A_eq, coordinates.n_eq]
  let refinements : WildQuadraticRefinementAssembly view data phaseData
      assembly coordinates :=
    { chiCorrection := some chiCorrection
      tauCorrection := some tauCorrection
      chi_selection := by
        simp only [Option.map_some]
        rw [hcoeff, WildQuadraticBoundaryData.coefficientData_chiCorrectionClass]
        congr 1
        exact hchiSpec.2.2.2.1.trans hxred
      tau_selection := by
        simp only [Option.map_some]
        rw [hcoeff, WildQuadraticBoundaryData.coefficientData_tauCorrectionClass]
        congr 1
        exact htauSpec.2.2.2.1.trans hyred
      chi_absent := by simp
      tau_absent := by simp
      chi_present := by
        intro C hC
        have hEq : chiCorrection = C := Option.some.inj hC
        subst C
        refine ⟨hchiSpec.1.trans coordinates.x_eq.symm,
          hchiSpec.2.1.trans hpairs.2.1,
          hchiSpec.2.2.1.trans hpairs.2.2, ?_, ?_, ?_⟩
        · rw [hchiSpec.2.2.1, hchiSpec.2.1]
          exact hchiRatio
        · rw [hcoeff]
          change some boundary.gamma = some chiCorrection.affineCoefficient
          congr 1
          simpa only [boundary, gamma] using hchiSpec.2.2.2.2.symm
        · rw [hcoeff]
          change some boundary.B = some chiCorrection.normalizedClass
          congr 1
          exact (hchiSpec.2.2.2.1.trans hxred).symm
      tau_present := by
        intro C hC
        have hEq : tauCorrection = C := Option.some.inj hC
        subst C
        refine ⟨htauSpec.1.trans coordinates.y_eq.symm,
          htauSpec.2.1.trans hpairs.1.1,
          htauSpec.2.2.1.trans hpairs.1.2, ?_, ?_, ?_⟩
        · rw [htauSpec.2.2.1, htauSpec.2.1]
          exact htauRatio
        · rw [hcoeff]
          change some boundary.gammaZero = some tauCorrection.affineCoefficient
          congr 1
          simpa only [boundary, gammaZero] using htauSpec.2.2.2.2.symm
        · rw [hcoeff]
          change some boundary.C = some tauCorrection.normalizedClass
          congr 1
          exact (htauSpec.2.2.2.1.trans hyred).symm }
  have helem : (view.psiF.character
      (-assembly.A * view.correction.X) : ℂ) =
      absoluteTraceChar (ResidueField F) boundary.C := by
    rw [hlocal.1.2] at helemW
    simpa only [boundary, WildQuadraticBoundaryData.C] using helemW
  exact
    { refinements := refinements
      mixedBoundary := by
        intro _ _
        exact ⟨boundary, chiCorrection, tauCorrection,
          ⟨hcoeff, helem⟩, rfl, rfl⟩ }

end BoundaryCompletion

/-! ## Strict-high odd-conductor correction -/

section StrictHighOddCompletion

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- Exact stationary linearization at the ceiling-half depth, for either
parity of the actual retained Lamprecht row. -/
private theorem wildQuadraticLocalPhase_character_linearization
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (S : LocalLamprechtPhaseData E chi psi)
    (x : E) (hx : x ∈ lattice E (((chi.conductor + 1) / 2 : ℕ) : ℤ))
    (v : Eˣ) (hv : (v : E) = 1 + x) :
    chi.character v =
      psi.character (S.selectedStationaryPair.ratio * x) := by
  cases S with
  | even d hm hlarge Gamma beta hbeta =>
      have hd : (chi.conductor + 1) / 2 = d := by omega
      let xlat : lattice E (d : ℤ) := ⟨x, by simpa only [hd] using hx⟩
      have hlin := stationaryNumeratorClass_linearization E chi psi
        (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 0
          (by omega) (by simpa using hm) hlarge)
        Gamma Gamma.property beta hbeta xlat
      have hunit : v = positiveUnitOfLattice E
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge).pos xlat := by
        apply Units.ext
        rw [hv]
        rfl
      rw [hunit, hlin]
      apply congrArg psi.character
      dsimp only [LocalLamprechtPhaseData.selectedStationaryPair,
        WildQuadraticStationaryPair.ratio, xlat]
      field_simp [Units.ne_zero (Gamma : Eˣ)]
  | odd d hm hlarge Gamma delta hdelta beta hbeta =>
      have hd : (chi.conductor + 1) / 2 = d + 1 := by omega
      let xlat : lattice E ((d + 1 : ℕ) : ℤ) :=
        ⟨x, by simpa only [hd] using hx⟩
      have hlin := stationaryNumeratorClass_linearization E chi psi
        (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1
          (by omega) hm hlarge)
        Gamma Gamma.property beta hbeta xlat
      have hunit : v = positiveUnitOfLattice E
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge).pos xlat := by
        apply Units.ext
        rw [hv]
        rfl
      rw [hunit, hlin]
      apply congrArg psi.character
      dsimp only [LocalLamprechtPhaseData.selectedStationaryPair,
        WildQuadraticStationaryPair.ratio, xlat]
      field_simp [Units.ne_zero (Gamma : Eˣ)]

private noncomputable def wildQuadraticLocalPhaseDataTransport
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi = chi') (hpsi : psi = psi')
    (S : LocalLamprechtPhaseData E chi psi) :
    LocalLamprechtPhaseData E chi' psi' := by
  subst chi'
  subst psi'
  exact S

@[simp] private theorem
    wildQuadraticLocalPhaseDataTransport_selectedStationaryPair
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi = chi') (hpsi : psi = psi')
    (S : LocalLamprechtPhaseData E chi psi) :
    (wildQuadraticLocalPhaseDataTransport hchi hpsi S).selectedStationaryPair =
      S.selectedStationaryPair := by
  subst chi'
  subst psi'
  rfl

/-- The auxiliary high odd trace coordinate has polar coefficient one
because its Artin--Schreier translates are actual norm-character phases. -/
private theorem wildQuadraticStrictHighOdd_cChi_polar_eq_one
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hT : 1 < T) (hstrict : T < m)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (tauData : LocalQuasiCharData F)
    (tau : NormCharacter F K)
    (htauCharacter : tauData.character = tau.1)
    (htauConductor : tauData.conductor = T)
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (tauRow : LocalLamprechtPhaseData F tauData W.psi)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (htauPair : tauRow.selectedStationaryPair = S.tau)
    (hWPair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F W S.chiF)
    (hm : m = 2 * W.d + 1)
    (hratio : S.chiF.ratio = S.tau.ratio * (C.n : F)) :
    let hcOrder := wildQuadraticHighOdd_cChi_order F K pi hpi hgen C
      hm hstrict
    let hcNe : C.cChi ≠ 0 := (ord_ne_top_iff F).1 (by
      rw [hcOrder]
      simp)
    let cUnit : Fˣ := Units.mk0 C.cChi hcNe
    criticalPolarCoefficient F W.chi W.psi W.d W.conductor_eq
        W.conductor_gt_one W.Gamma cUnit
        (by change ord F C.cChi = ((W.d : ℤ) : WithTop ℤ); exact hcOrder)
        (absoluteTraceChar (ResidueField F))
        (absoluteTraceChar_ne_one (ResidueField F)) = 1 := by
  classical
  have hcOrder : ord F C.cChi = ((W.d : ℤ) : WithTop ℤ) :=
    wildQuadraticHighOdd_cChi_order F K pi hpi hgen C hm hstrict
  have hcNe : C.cChi ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hcOrder]; simp)
  let cUnit : Fˣ := Units.mk0 C.cChi hcNe
  have hcUnitOrder : ord F (cUnit : F) =
      ((W.d : ℤ) : WithTop ℤ) := by
    simpa only [cUnit, Units.val_mk0] using hcOrder
  let phi : FiniteAddChar (ResidueField F) :=
    criticalPolarAddChar F W.chi W.psi W.d W.conductor_eq
      W.conductor_gt_one W.Gamma cUnit hcUnitOrder
  have hphiNe : phi ≠ 1 :=
    criticalPolarAddChar_ne_one F W.chi W.psi W.d W.conductor_eq
      W.conductor_gt_one W.Gamma cUnit hcUnitOrder
  have hAS : ∀ z : ResidueField F, phi (z + z ^ 2) = 1 := by
    intro z
    let zF : F := (teichmuller F z : F)
    have hzF : zF ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 (teichmuller F z).property
    let zAS : F := zF + zF ^ 2
    have hzFSq : zF ^ 2 ∈ lattice F 0 := by
      simpa only [pow_two, zero_add] using mul_mem_lattice F hzF hzF
    have hzAS : zAS ∈ lattice F 0 := add_mem_lattice F hzF hzFSq
    have hreduceAS : reduce F zAS hzAS = z + z ^ 2 := by
      let zO : ringOfIntegers F := teichmuller F z
      let zASO : ringOfIntegers F := zO + zO ^ 2
      have hfield : (zASO : F) = zAS := by rfl
      have hreduce : reduce F (zASO : F)
          ((mem_lattice_zero_iff F).2 zASO.property) = z + z ^ 2 := by
        rw [reduce_mk]
        simp only [zASO, zO, map_add, map_pow, residueMap_teichmuller]
      simpa only [hfield] using hreduce
    let disp : F := (C.n : F) * C.cChi ^ 2 * zAS
    have hnMem : (C.n : F) ∈ lattice F ((T : ℤ) - (m : ℤ)) := by
      rw [mem_lattice, C.target_order]
    have hcMem : C.cChi ∈ lattice F (W.d : ℤ) := by
      rw [mem_lattice, hcOrder]
    have hcSqMem : C.cChi ^ 2 ∈ lattice F ((W.d : ℤ) + W.d) := by
      simpa only [pow_two] using mul_mem_lattice F hcMem hcMem
    have hdisp0 : disp ∈ lattice F
        (((T : ℤ) - (m : ℤ)) + (W.d : ℤ) + W.d + 0) := by
      simpa only [disp, add_assoc] using
        mul_mem_lattice F (mul_mem_lattice F hnMem hcSqMem) hzAS
    have hdispDepth : disp ∈ lattice F ((T : ℤ) - 1) := by
      have hdepth : (((T : ℤ) - (m : ℤ)) + (W.d : ℤ) +
          W.d + 0) = (T : ℤ) - 1 := by
        omega
      rw [← hdepth]
      exact hdisp0
    have hlinearDepth : (((tauData.conductor + 1) / 2 : ℕ) : ℤ) ≤
        (T : ℤ) - 1 := by
      have hnat : (tauData.conductor + 1) / 2 ≤ T - 1 := by
        rw [htauConductor]
        omega
      have hcast : ((T - 1 : ℕ) : ℤ) = (T : ℤ) - 1 := by omega
      rw [← hcast]
      exact_mod_cast hnat
    have hdisp : disp ∈
        lattice F (((tauData.conductor + 1) / 2 : ℕ) : ℤ) :=
      lattice_antitone F hlinearDepth hdispDepth
    let scalar : F := (C.n : F) * C.cChi * zF
    have hscalar : scalar ∈
        lattice F (((T : ℤ) - (m : ℤ)) + W.d + 0) := by
      simpa only [scalar, add_assoc] using
        mul_mem_lattice F (mul_mem_lattice F hnMem hcMem) hzF
    have hmapScalar : algebraMap F K scalar ∈ lattice K
        ((((T : ℤ) - (m : ℤ)) + W.d + 0) +
          (((T : ℤ) - (m : ℤ)) + W.d + 0)) := by
      rw [mem_lattice] at hscalar ⊢
      rw [ord_algebraMap, C.ramificationIndex_eq_two]
      simpa only [two_nsmul, WithTop.coe_add] using add_le_add hscalar hscalar
    let a : K := -(algebraMap F K scalar) * C.reciprocal
    have ha0 : a ∈ lattice K
        (((((T : ℤ) - (m : ℤ)) + W.d + 0) +
            (((T : ℤ) - (m : ℤ)) + W.d + 0)) +
          ((m : ℤ) - (T : ℤ))) := by
      exact mul_mem_lattice K (neg_mem_lattice K hmapScalar) C.reciprocal_mem
    have haDepth : a ∈ lattice K ((T : ℤ) - 1) := by
      have hdepth :
          ((((T : ℤ) - (m : ℤ)) + W.d + 0) +
            (((T : ℤ) - (m : ℤ)) + W.d + 0)) +
            ((m : ℤ) - (T : ℤ)) = (T : ℤ) - 1 := by
        omega
      rw [← hdepth]
      exact ha0
    have haOne : a ∈ lattice K 1 :=
      lattice_antitone K (by omega) haDepth
    let aUnit : unitGroup K := wildQuadratic_oneAddLocalUnit a haOne
    have htraceReciprocal : trace F K C.reciprocal = -C.cChi := by
      dsimp only [WildQuadraticCommonCorrectionData.cChi]
      ring
    have hnormReciprocal : norm F K C.reciprocal = (C.n : F)⁻¹ := by
      change ((normUnits F K (C.u⁻¹) : Fˣ) : F) = (C.n : F)⁻¹
      rw [map_inv, C.norm_u]
      simp
    have htraceA : trace F K a = (C.n : F) * C.cChi ^ 2 * zF := by
      have hmap : trace F K
          (algebraMap F K (-scalar) * C.reciprocal) =
          (-scalar) * trace F K C.reciprocal := by
        rw [← Algebra.smul_def, map_smul]
        rfl
      rw [show a = algebraMap F K (-scalar) * C.reciprocal by
        dsimp only [a]; rw [map_neg], hmap, htraceReciprocal]
      dsimp only [scalar]
      ring
    have hnormA : norm F K a = (C.n : F) * C.cChi ^ 2 * zF ^ 2 := by
      rw [show a = algebraMap F K (-scalar) * C.reciprocal by
        dsimp only [a]; rw [map_neg], map_mul, norm_algebraMap,
        C.degree_eq_two, hnormReciprocal]
      dsimp only [scalar]
      field_simp [Units.ne_zero C.n]
    have hnormOne : norm F K (1 + a) = 1 + disp := by
      have hpoly := wildQuadratic_normPolynomialValue_eq_trace_add_norm
        F K C.degree_eq_two a
      rw [normPolynomialValue, htraceA, hnormA] at hpoly
      dsimp only [disp, zAS]
      linear_combination hpoly
    have hnormUnit : ((normUnits F K (aUnit : Kˣ) : Fˣ) : F) =
        1 + disp := by
      rw [coe_normUnits, wildQuadratic_oneAddLocalUnit_coe, hnormOne]
    have htauNorm : tau.1 (normUnits F K (aUnit : Kˣ)) = 1 :=
      tau.eq_one_on_normRange F K _ ⟨(aUnit : Kˣ), rfl⟩
    have htauDataNorm :
        tauData.character (normUnits F K (aUnit : Kˣ)) = 1 := by
      rw [htauCharacter]
      exact htauNorm
    have hlinear := wildQuadraticLocalPhase_character_linearization tauRow
      disp hdisp (normUnits F K (aUnit : Kˣ)) hnormUnit
    have hpsiDisp : W.psi.character (S.tau.ratio * disp) = 1 := by
      rw [← htauPair]
      exact hlinear.symm.trans htauDataNorm
    have hpolar := criticalPolarAddChar_integral_lift F W.chi W.psi W.d
      W.conductor_eq W.conductor_gt_one W.Gamma cUnit hcUnitOrder W.beta
        W.beta_class zAS hzAS
    rw [hreduceAS] at hpolar
    change phi (z + z ^ 2) = 1
    calc
      phi (z + z ^ 2) =
          (W.psi.character
            ((W.beta : F) * (cUnit : F) ^ 2 * zAS /
              ((W.Gamma : Fˣ) : F)) : ℂ) := hpolar
      _ = (W.psi.character (S.tau.ratio * disp) : ℂ) := by
        congr 2
        rcases hWPair with ⟨hGamma, hbeta⟩
        rw [hGamma, hbeta]
        simp only [cUnit, Units.val_mk0]
        calc
          S.chiF.beta * C.cChi ^ 2 * zAS / (S.chiF.gamma : F) =
              S.chiF.ratio * C.cChi ^ 2 * zAS := by
            dsimp only [WildQuadraticStationaryPair.ratio]
            field_simp [Units.ne_zero S.chiF.gamma]
          _ = S.tau.ratio * disp := by
            rw [hratio]
            dsimp only [disp]
            ring
      _ = 1 := by simpa using congrArg (Units.val : ℂˣ → ℂ) hpsiDisp
  have hphi : phi = absoluteTraceChar (ResidueField F) :=
    absoluteTraceChar_eq_of_artinSchreier_trivial (ResidueField F) hphiNe hAS
  change finiteAddCharCoefficient (absoluteTraceChar (ResidueField F))
      (absoluteTraceChar_ne_one (ResidueField F)) phi = 1
  apply finiteAddCharCoefficient_unique
  rw [AddChar.mulShift_one]
  exact hphi.symm

private theorem wildQuadraticStrictHighOdd_x_div_cChi_reduce
    {T m d : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hm : m = 2 * d + 1) (hstrict : T < m) :
    ∃ hx : C.x / C.cChi ∈ lattice F 0,
      reduce F (C.x / C.cChi) hx = 1 := by
  have hnord : ord F (C.n : F) =
      ((((T : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
    C.target_order
  have hneg : (T : ℤ) - (m : ℤ) < 0 := by omega
  have hne : ord F (1 : F) ≠ ord F (C.n : F) := by
    rw [ord_one, hnord]
    exact Ne.symm (ne_of_lt (by exact_mod_cast hneg))
  have hdenord : ord F C.denominator =
      ((((T : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [WildQuadraticCommonCorrectionData.denominator,
      ord_add_eq_min F hne, ord_one, hnord, min_eq_right]
    exact_mod_cast hneg.le
  have hratioord : ord F ((C.n : F) / C.denominator) = 0 := by
    rw [ord_div, hnord, hdenord]
    simp
  have hratio : C.x / C.cChi = (C.n : F) / C.denominator :=
    wildQuadraticHighOdd_x_div_cChi_eq F K pi hpi hgen C hm hstrict
  have hx : C.x / C.cChi ∈ lattice F 0 := by
    rw [mem_lattice, hratio, hratioord]
    norm_num
  refine ⟨hx, ?_⟩
  let ratioUnit : unitGroup F := by
    let u : Fˣ := Units.mk0 ((C.n : F) / C.denominator)
      (div_ne_zero (Units.ne_zero C.n) C.denominator_ne_zero')
    exact ⟨u, (mem_unitGroup_iff_ord_eq_zero F u).2 hratioord⟩
  have hratioCoe : (((ratioUnit : unitGroup F) : Fˣ) : F) =
      (C.n : F) / C.denominator := rfl
  have hinvMem : ((C.n : F)⁻¹) ∈ lattice F 1 := by
    rw [mem_lattice, ord_inv, hnord]
    have hdiff : (T : ℤ) - (m : ℤ) = -((m - T : ℕ) : ℤ) := by omega
    rw [hdiff, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    simp only [neg_neg]
    norm_cast
    omega
  let denScaled : unitGroup F :=
    wildQuadratic_oneAddLocalUnit ((C.n : F)⁻¹) hinvMem
  have hratioUnit : ratioUnit = denScaled⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    change (C.n : F) / C.denominator = (1 + (C.n : F)⁻¹)⁻¹
    dsimp only [WildQuadraticCommonCorrectionData.denominator]
    field_simp [Units.ne_zero C.n]
    ring
  have hresidue : ((residueUnits F ratioUnit : (ResidueField F)ˣ) :
      ResidueField F) = 1 := by
    have hdenResidue := wildQuadratic_oneAddLocalUnit_residue
      ((C.n : F)⁻¹) hinvMem
    rw [hratioUnit, map_inv]
    simp only [Units.val_inv_eq_inv_val]
    rw [show ((residueUnits F denScaled : (ResidueField F)ˣ) :
      ResidueField F) = 1 by simpa only [denScaled] using hdenResidue]
    simp
  let ratioInt : ringOfIntegers F :=
    ⟨C.x / C.cChi, (mem_lattice_zero_iff F).1 hx⟩
  let ratioUnitInt : ringOfIntegers F :=
    ((unitGroupMulEquivRingOfIntegers F ratioUnit :
      (ringOfIntegers F)ˣ) : ringOfIntegers F)
  have hring : ratioInt = ratioUnitInt := by
    apply Subtype.ext
    exact hratio.trans hratioCoe.symm
  change residueMap F ratioInt = 1
  rw [hring]
  change ((residueUnits F ratioUnit : (ResidueField F)ˣ) :
    ResidueField F) = 1
  exact hresidue

/-- Equality of the source-tied polar coefficient forces the auxiliary
coordinate to differ from the actual retained coordinate by residue one. -/
private theorem wildQuadraticCorrectionRatio_reduce_of_polar_eq_one
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (c : F) (hcNe : c ≠ 0)
    (hcOrder : ord F c = ((W.d : ℤ) : WithTop ℤ))
    (hcPolar :
      criticalPolarCoefficient F W.chi W.psi W.d W.conductor_eq
        W.conductor_gt_one W.Gamma (Units.mk0 c hcNe)
        (by simpa only [Units.val_mk0] using hcOrder)
        (absoluteTraceChar (ResidueField F))
        (absoluteTraceChar_ne_one (ResidueField F)) = 1) :
    ∃ hc : c / (W.delta : F) ∈ lattice F 0,
      reduce F (c / (W.delta : F)) hc = 1 := by
  let cUnit : Fˣ := Units.mk0 c hcNe
  let ratio : Fˣ := cUnit / W.delta
  have hratioCoe : (ratio : F) = c / (W.delta : F) := by
    simp only [ratio, cUnit, Units.val_div_eq_div_val, Units.val_mk0]
  have hratioOrd : ord F (ratio : F) = (0 : WithTop ℤ) := by
    rw [hratioCoe, ord_div, hcOrder, W.delta_order]
    simp
  let ratioUnit : unitGroup F :=
    ⟨ratio, (mem_unitGroup_iff_ord_eq_zero F ratio).2 hratioOrd⟩
  have hcoordinate : cUnit =
      criticalPolarScaledCoordinate F ratioUnit W.delta := by
    apply Units.ext
    simp only [criticalPolarScaledCoordinate, ratioUnit, ratio,
      Units.val_mul, Units.val_div_eq_div_val, cUnit, Units.val_mk0]
    field_simp [Units.ne_zero W.delta]
  have hscale := criticalPolarCoefficient_scaleCoordinate F W.chi W.psi W.d
    W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
      (absoluteTraceChar (ResidueField F))
      (absoluteTraceChar_ne_one (ResidueField F)) ratioUnit
  have hsq :
      ((residueUnits F ratioUnit : (ResidueField F)ˣ) :
        ResidueField F) ^ 2 = 1 := by
    have hscaled :
        criticalPolarCoefficient F W.chi W.psi W.d W.conductor_eq
          W.conductor_gt_one W.Gamma
          (criticalPolarScaledCoordinate F ratioUnit W.delta)
          (criticalPolarScaledCoordinate_ord F W.d ratioUnit W.delta
            W.delta_order)
          (absoluteTraceChar (ResidueField F))
          (absoluteTraceChar_ne_one (ResidueField F)) = 1 := by
      let PolarCoordinate := {u : Fˣ //
        ord F (u : F) = ((W.d : ℤ) : WithTop ℤ)}
      let coeff (u : PolarCoordinate) : ResidueField F :=
        criticalPolarCoefficient F W.chi W.psi W.d W.conductor_eq
          W.conductor_gt_one W.Gamma u.1 u.2
          (absoluteTraceChar (ResidueField F))
          (absoluteTraceChar_ne_one (ResidueField F))
      let scaled : PolarCoordinate :=
        ⟨criticalPolarScaledCoordinate F ratioUnit W.delta,
          criticalPolarScaledCoordinate_ord F W.d ratioUnit W.delta
            W.delta_order⟩
      let actual : PolarCoordinate :=
        ⟨Units.mk0 c hcNe, by simpa only [Units.val_mk0] using hcOrder⟩
      have heq : scaled = actual := by
        apply Subtype.ext
        exact hcoordinate.symm
      exact (congrArg coeff heq).trans hcPolar
    rw [hscale, W.polar_eq_one, mul_one] at hscaled
    exact hscaled
  have hresidue :
      ((residueUnits F ratioUnit : (ResidueField F)ˣ) :
        ResidueField F) = 1 := by
    apply CharTwo.sq_injective
    simpa using hsq
  have hc : c / (W.delta : F) ∈ lattice F 0 := by
    rw [mem_lattice, ← hratioCoe, hratioOrd]
    norm_num
  refine ⟨hc, ?_⟩
  let ratioInt : ringOfIntegers F :=
    ⟨c / (W.delta : F), (mem_lattice_zero_iff F).1 hc⟩
  let ratioUnitInt : ringOfIntegers F :=
    ((unitGroupMulEquivRingOfIntegers F ratioUnit :
      (ringOfIntegers F)ˣ) : ringOfIntegers F)
  have hring : ratioInt = ratioUnitInt := by
    apply Subtype.ext
    change c / (W.delta : F) = ((ratioUnit : Fˣ) : F)
    rw [← hratioCoe]
  change residueMap F ratioInt = 1
  rw [hring]
  exact hresidue

private theorem wildQuadraticCorrectionRatio_mul_reduce_one
    (x c delta : F) (hcNe : c ≠ 0) (hdeltaNe : delta ≠ 0)
    (hx : x / c ∈ lattice F 0)
    (hc : c / delta ∈ lattice F 0)
    (hxred : reduce F (x / c) hx = 1)
    (hcred : reduce F (c / delta) hc = 1) :
    ∃ h : x / delta ∈ lattice F 0, reduce F (x / delta) h = 1 := by
  have hfield : x / delta = (x / c) * (c / delta) := by
    field_simp [hcNe, hdeltaNe]
  have h : x / delta ∈ lattice F 0 := by
    rw [hfield]
    simpa only [zero_add] using mul_mem_lattice F hx hc
  refine ⟨h, ?_⟩
  let xO : ringOfIntegers F :=
    ⟨x / delta, (mem_lattice_zero_iff F).1 h⟩
  let xcO : ringOfIntegers F :=
    ⟨x / c, (mem_lattice_zero_iff F).1 hx⟩
  let cdO : ringOfIntegers F :=
    ⟨c / delta, (mem_lattice_zero_iff F).1 hc⟩
  have hring : xO = xcO * cdO := by
    apply Subtype.ext
    exact hfield
  change residueMap F xO = 1
  rw [hring, map_mul]
  change reduce F (x / c) hx * reduce F (c / delta) hc = 1
  rw [hxred, hcred, one_mul]

private theorem wildQuadraticStrictHighOdd_y_mem_ceilingHalf
    {T m d : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hm : m = 2 * d + 1) (hstrict : T < m) :
    C.y ∈ lattice F (((T + 1) / 2 : ℕ) : ℤ) := by
  let a : ℤ := (T : ℤ) - (m : ℤ)
  have ha : a < 0 := by dsimp only [a]; omega
  have hu : (C.u : K) ∈ lattice K a := by
    rw [mem_lattice, C.source_order]
  have hs : C.s ∈ lattice F ((a + (T : ℤ)) / 2) := by
    have hs' := trace_mem_lattice_floor F K pi hpi hgen a hu
    rw [C.differentExponent_eq, C.ramificationIndex_eq_two] at hs'
    norm_num at hs'
    rw [mem_lattice]
    simpa only [WildQuadraticCommonCorrectionData.s] using hs'
  have hnord : ord F (C.n : F) = (a : WithTop ℤ) := by
    simpa only [a] using C.target_order
  have hne : ord F (1 : F) ≠ ord F (C.n : F) := by
    rw [ord_one, hnord]
    exact Ne.symm (ne_of_lt (by exact_mod_cast ha))
  have hden : ord F C.denominator = (a : WithTop ℤ) := by
    rw [WildQuadraticCommonCorrectionData.denominator,
      ord_add_eq_min F hne, ord_one, hnord, min_eq_right]
    exact_mod_cast ha.le
  rw [C.y_eq]
  apply (div_mem_lattice_iff F C.denominator C.s a
    (((T + 1) / 2 : ℕ) : ℤ) hden).2
  apply lattice_antitone F (show
    a + (((T + 1) / 2 : ℕ) : ℤ) ≤ (a + (T : ℤ)) / 2 by
      dsimp only [a]
      omega)
  exact hs

private theorem wildQuadraticStrictHighOdd_tau_inverseIdentity
    {q : CharTwoRefinement (ResidueField F)} {t m d : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view.toCommon data phaseData assembly)
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (hm : m = 2 * d + 1) (hstrict : t + 1 < m) :
    (view.tauData.character assembly.zOne : ℂ)⁻¹ =
      (view.psiF.character (-assembly.A * assembly.y) : ℂ) := by
  have hy : assembly.y ∈ lattice F
      ((((data.normCharacterData assembly.indexing.tau).conductor + 1) / 2 : ℕ) : ℤ) := by
    rw [wildQuadratic_tau_conductor_eq ht hres pi hpi hgen,
      coordinates.y_eq]
    exact wildQuadraticStrictHighOdd_y_mem_ceilingHalf pi hpi hgen
      view.correction hm hstrict
  have htauFactor :=
    wildQuadratic_stationaryUnitFactor_eq_one_of_mem_ceilingHalf
      rows.tau view.stationaryPairs.tau rows.tau_pair assembly.y hy
        assembly.zOne assembly.zOne_eq
  unfold stationaryUnitFactor at htauFactor
  rw [coordinates.tauData_eq, coordinates.baseAddData_eq,
    ← coordinates.A_eq, assembly.zOne_eq] at htauFactor
  have hfactor :
      (view.psiF.character (assembly.A * assembly.y) : ℂ) *
        (view.tauData.character assembly.zOne : ℂ)⁻¹ = 1 := by
    simpa only [add_sub_cancel_left] using htauFactor
  have hinv :
      (view.tauData.character assembly.zOne : ℂ)⁻¹ =
        (view.psiF.character (assembly.A * assembly.y) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hfactor
  rw [hinv]
  have hneg := congrArg (Units.val : ℂˣ → ℂ)
    (AddChar.map_neg_eq_inv view.psiF.character.toAddChar
      (assembly.A * assembly.y))
  calc
    (view.psiF.character (assembly.A * assembly.y) : ℂ)⁻¹ =
        (view.psiF.character (-(assembly.A * assembly.y)) : ℂ) := by
      simpa only [ContinuousAddChar.toAddChar_apply,
        Units.val_inv_eq_inv_val] using hneg.symm
    _ = (view.psiF.character (-assembly.A * assembly.y) : ℂ) := by
      ring_nf

/-- The actual base correction has normalized class one relative to the
actual retained positive-polar `chiF` coordinate. -/
private theorem wildQuadraticStrictHighOdd_x_div_actualDelta_reduce
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view.toCommon data phaseData assembly)
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (Wchi : QuotientDerivedNormalizedCriticalFunction F)
    (hWPair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F Wchi view.stationaryPairs.chiF)
    (hWLocal : QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
      F Wchi view.chiFData view.psiF)
    (hstrict : t + 1 < m) :
    ∃ hx : assembly.x / (Wchi.delta : F) ∈ lattice F 0,
      reduce F (assembly.x / (Wchi.delta : F)) hx = 1 := by
  have hm : m = 2 * Wchi.d + 1 := by
    calc
      m = view.chiFData.conductor :=
        (wildQuadratic_base_conductor_eq coordinates).symm
      _ = Wchi.chi.conductor := by rw [hWLocal.1]
      _ = 2 * Wchi.d + 1 := Wchi.conductor_eq
  have htauConductor : view.tauData.conductor = t + 1 := by
    calc
      view.tauData.conductor =
          (data.normCharacterData assembly.indexing.tau).conductor := by
        rw [coordinates.tauData_eq]
      _ = t + 1 := wildQuadratic_tau_conductor_eq ht hres pi hpi hgen
  let tauRow : LocalLamprechtPhaseData F view.tauData Wchi.psi :=
    wildQuadraticLocalPhaseDataTransport coordinates.tauData_eq
      (coordinates.baseAddData_eq.trans hWLocal.2.symm) rows.tau
  have htauPair : tauRow.selectedStationaryPair =
      view.stationaryPairs.tau := by
    rw [show tauRow.selectedStationaryPair =
      rows.tau.selectedStationaryPair by
        exact wildQuadraticLocalPhaseDataTransport_selectedStationaryPair
          _ _ _]
    exact rows.tau_pair
  have hcOrder : ord F view.correction.cChi =
      ((Wchi.d : ℤ) : WithTop ℤ) :=
    wildQuadraticHighOdd_cChi_order F K pi hpi hgen view.correction hm hstrict
  have hcNe : view.correction.cChi ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hcOrder]; simp)
  have hcPolar := wildQuadraticStrictHighOdd_cChi_polar_eq_one
    view.correction (by omega) hstrict pi hpi hgen view.tauData
      assembly.indexing.tau coordinates.tauCharacter_eq htauConductor Wchi
        tauRow view.stationaryPairs htauPair hWPair hm view.chiF_ratio
  obtain ⟨hxc, hxcRed⟩ := wildQuadraticStrictHighOdd_x_div_cChi_reduce
    pi hpi hgen view.correction hm hstrict
  obtain ⟨hcd, hcdRed⟩ :=
    wildQuadraticCorrectionRatio_reduce_of_polar_eq_one Wchi
      view.correction.cChi hcNe hcOrder hcPolar
  obtain ⟨hx, hxred⟩ := wildQuadraticCorrectionRatio_mul_reduce_one
    view.correction.x view.correction.cChi (Wchi.delta : F) hcNe
      (Units.ne_zero Wchi.delta) hxc hcd hxcRed hcdRed
  rw [coordinates.x_eq]
  exact ⟨hx, hxred⟩

/-- Complete strict-high odd-`m` correction package.  The selected base
correction is tied to the actual retained `chiF` source; the norm-character
correction is absent and its exact inverse identity comes from the actual
tau row. -/
private noncomputable def wildQuadraticStrictHighOddCompletion
    {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (view : WildQuadraticCoefficientView F K q t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
      view.psiF.character data phaseData (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view.toCommon data phaseData assembly)
    (coordinates : WildQuadraticCoordinateCompatibility view data phaseData
      assembly)
    (Wchi : QuotientDerivedNormalizedCriticalFunction F)
    (hinputs : view.criticalInputs = .aboveMOddTEven Wchi ∨
      ∃ Wtau : QuotientDerivedNormalizedCriticalFunction F,
        view.criticalInputs = .aboveMOddTOdd Wtau Wchi)
    (hstrict : t + 1 < m) :
    WildQuadraticRefinementCompletion view data phaseData assembly
      coordinates := by
  have hWPair :
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F Wchi view.stationaryPairs.chiF := by
    rcases hinputs with hI | ⟨Wtau, hI⟩
    · have hp := view.criticalInputs_stationaryPairs
      rw [hI] at hp
      exact hp
    · have hp := view.criticalInputs_stationaryPairs
      rw [hI] at hp
      exact hp.2
  have hWLocal :
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F Wchi view.chiFData view.psiF := by
    rcases hinputs with hI | ⟨Wtau, hI⟩
    · have hl := view.criticalInputs_localData
      rw [hI] at hl
      exact hl
    · have hl := view.criticalInputs_localData
      rw [hI] at hl
      exact hl.2
  let hxData := wildQuadraticStrictHighOdd_x_div_actualDelta_reduce ht htpos
    hres pi hpi hgen view rows coordinates Wchi hWPair hWLocal hstrict
  let hx := Classical.choose hxData
  have hxred := Classical.choose_spec hxData
  have hone : 1 + assembly.x ≠ 0 := by
    rw [coordinates.x_eq]
    have hz : 1 + view.correction.x = view.correction.z0 := by
      dsimp only [WildQuadraticCommonCorrectionData.x]
      ring
    rw [hz]
    exact view.correction.z0_ne_zero view.oppositeNoncancellation
  let Cchi := wildQuadraticCorrectionForLocalData Wchi q view.chiFData
    view.psiF hWLocal.1 hWLocal.2 assembly.x hx hone
  have hCspec := wildQuadraticCorrectionForLocalData_spec Wchi q
    view.chiFData view.psiF hWLocal.1 hWLocal.2 assembly.x hx hone
  have hCClass : Cchi.normalizedClass = 1 :=
    hCspec.2.2.2.1.trans hxred
  have hchiClass :
      view.coefficients.1.chiCorrectionClass = some 1 := by
    rcases hinputs with hI | ⟨Wtau, hI⟩
    · change (view.criticalInputs.toCoefficientData q).chiCorrectionClass =
        some 1
      rw [hI]
      rfl
    · change (view.criticalInputs.toCoefficientData q).chiCorrectionClass =
        some 1
      rw [hI]
      rfl
  have htauClass :
      view.coefficients.1.tauCorrectionClass = none := by
    rcases hinputs with hI | ⟨Wtau, hI⟩
    · change (view.criticalInputs.toCoefficientData q).tauCorrectionClass =
        none
      rw [hI]
      rfl
    · change (view.criticalInputs.toCoefficientData q).tauCorrectionClass =
        none
      rw [hI]
      rfl
  have hchiAffine :
      view.coefficients.1.affineCoefficient .chiF =
        some (Wchi.affineCoefficient F q) := by
    rcases hinputs with hI | ⟨Wtau, hI⟩
    · change (view.criticalInputs.toCoefficientData q).affineCoefficient
        .chiF = some (Wchi.affineCoefficient F q)
      rw [WildQuadraticCoefficientInputs.chiFCoefficient_from_quotient, hI]
      rfl
    · change (view.criticalInputs.toCoefficientData q).affineCoefficient
        .chiF = some (Wchi.affineCoefficient F q)
      rw [WildQuadraticCoefficientInputs.chiFCoefficient_from_quotient, hI]
      rfl
  have hratio :
      Cchi.beta / ((Cchi.Gamma : Fˣ) : F) = assembly.A * assembly.n := by
    calc
      Cchi.beta / ((Cchi.Gamma : Fˣ) : F) =
          (Wchi.beta : F) / ((Wchi.Gamma : Fˣ) : F) := by
        rw [hCspec.2.2.1, hCspec.2.1]
      _ = view.stationaryPairs.chiF.ratio := by
        rw [hWPair.1, hWPair.2]
        rfl
      _ = view.stationaryPairs.tau.ratio * (view.correction.n : F) :=
        view.chiF_ratio
      _ = assembly.A * assembly.n := by
        rw [coordinates.A_eq, coordinates.n_eq]
  have htauInverse := wildQuadraticStrictHighOdd_tau_inverseIdentity ht hres
    pi hpi hgen view rows coordinates (d := Wchi.d) (by
      calc
        m = view.chiFData.conductor :=
          (wildQuadratic_base_conductor_eq coordinates).symm
        _ = Wchi.chi.conductor := by rw [hWLocal.1]
        _ = 2 * Wchi.d + 1 := Wchi.conductor_eq) hstrict
  let refinements : WildQuadraticRefinementAssembly view data phaseData
      assembly coordinates :=
    { chiCorrection := some Cchi
      tauCorrection := none
      chi_selection := by
        simpa only [Option.map_some, hCClass] using hchiClass.symm
      tau_selection := by
        simpa only [Option.map_none] using htauClass.symm
      chi_absent := by simp
      tau_absent := fun _ ↦ htauInverse
      chi_present := by
        intro C hC
        have hEq : Cchi = C := Option.some.inj hC
        subst C
        exact ⟨hCspec.1, hCspec.2.1.trans hWPair.1,
          hCspec.2.2.1.trans hWPair.2, hratio, by
            rw [hchiAffine, hCspec.2.2.2.2], by
            rw [hchiClass, hCClass]⟩
      tau_present := by simp }
  refine ⟨refinements, ?_⟩
  intro _ hboundary
  have hne : view.coefficients.1.row ≠ .boundaryOdd := by
    rcases hinputs with hI | ⟨Wtau, hI⟩
    · change (view.criticalInputs.toCoefficientData q).row ≠ .boundaryOdd
      rw [WildQuadraticCoefficientInputs.toCoefficientData_row, hI]
      intro h
      cases h
    · change (view.criticalInputs.toCoefficientData q).row ≠ .boundaryOdd
      rw [WildQuadraticCoefficientInputs.toCoefficientData_row, hI]
      intro h
      cases h
  exact (hne hboundary).elim

end StrictHighOddCompletion

/-- Refine exactly the seven positive-polar phase-preparation branches.  The
three all-even branches pass through literally and never choose a refinement. -/
noncomputable def wildQuadraticHigherData
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    WildQuadraticHigherData F K t chiF psiF := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  cases wildQuadraticPhasePreparation ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal hm with
  | allEven view common rows correction =>
      exact .allEven view common rows correction
  | needsRefinement view source common rows continuation =>
      let normalization :=
        WildQuadraticNormalizedRefinementSource.ofPositivePolarSource
          (F := F) source
      let q := normalization.1
      let refinedView :=
        wildQuadraticRefinedView view source rows continuation q
      let refinedRows :=
        wildQuadraticRefinedRows view source rows continuation q
      let coordinates : WildQuadraticCoordinateCompatibility refinedView
          common.data common.phaseData common.assembly :=
        WildQuadraticCoordinateCompatibility.ofCommon common.coordinates
      let actualRows : WildQuadraticActualPhaseRows refinedView.toCommon
          common.data common.phaseData common.assembly :=
        { extension := rows.extension
          tau := rows.tau
          base := rows.base
          twist := rows.twist
          extension_eq := rows.extension_eq
          tau_eq := rows.tau_eq
          base_eq := rows.base_eq
          twist_eq := rows.twist_eq
          extension_pair := rows.extension_pair
          tau_pair := rows.tau_pair
          base_pair := rows.base_pair
          twist_pair := rows.twist_pair }
      let finish
          (C : WildQuadraticRefinementCompletion refinedView common.data
            common.phaseData common.assembly coordinates) :
          WildQuadraticHigherData F K t chiF psiF :=
        .refined q refinedView normalization.2 common refinedRows
          C.refinements C.mixedBoundary
      let noCorrection
          (hchi : refinedView.coefficients.1.chiCorrectionClass = none)
          (htau : refinedView.coefficients.1.tauCorrectionClass = none) :
          WildQuadraticHigherData F K t chiF psiF :=
        finish (wildQuadraticNoCorrectionCompletion ht hres pi hpi hgen
          refinedView actualRows coordinates source hchi htau)
      have hstrictOfAbove
          (habove : view.criticalInputs.row.range = .above) :
          t + 1 < chiF.conductor := by
        have hpred : t < chiF.conductor - 1 := by
          by_contra hnot
          rcases lt_or_eq_of_le (Nat.le_of_not_gt hnot) with hbelow | hboundary
          · have hrange :=
              WildQuadraticCoefficientRow.ofConductors_range_below hbelow
            rw [← view.criticalInputs_row, habove] at hrange
            cases hrange
          · have hrange :=
              WildQuadraticCoefficientRow.ofConductors_range_boundary
                hboundary
            rw [← view.criticalInputs_row, habove] at hrange
            cases hrange
        omega
      cases hI : view.criticalInputs with
      | belowMEvenTEven =>
          exact (False.elim <| by simpa [hI,
            WildQuadraticCoefficientInputs.tauSource,
            WildQuadraticCoefficientInputs.chiFSource] using source.retained)
      | belowMEvenTOdd tau =>
          apply noCorrection
          · change WildQuadraticCoefficientData.chiCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
          · change WildQuadraticCoefficientData.tauCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
      | belowMOddTEven Wchi =>
          apply noCorrection
          · change WildQuadraticCoefficientData.chiCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
          · change WildQuadraticCoefficientData.tauCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
      | belowMOddTOdd Wtau Wchi =>
          apply noCorrection
          · change WildQuadraticCoefficientData.chiCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
          · change WildQuadraticCoefficientData.tauCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
      | boundaryEven =>
          exact (False.elim <| by simpa [hI,
            WildQuadraticCoefficientInputs.tauSource,
            WildQuadraticCoefficientInputs.chiFSource] using source.retained)
      | boundaryOdd rho hrho hden Wtau Wchi =>
          by_cases h2 : (2 : F) = 0
          · letI : CharP F 2 :=
              (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
            have htOdd := quadraticBreak_odd_equalCharacteristic F K hdegree
              hres t ht.1 ht.2
            have hTParity :
                WildQuadraticConductorParity.ofConductor (t + 1) = .odd := by
              rw [← WildQuadraticCoefficientRow.ofConductors_TParity
                (chiF.conductor - 1) t, ← view.criticalInputs_row, hI]
              rfl
            exact ((Nat.odd_add_one.mp
              ((WildQuadraticConductorParity.ofConductor_eq_odd_iff _).mp
                hTParity)) htOdd).elim
          · apply finish
            apply wildQuadraticBoundaryCompletion ht pi hpi hgen refinedView
              coordinates rho hrho hden Wtau Wchi
            · change view.criticalInputs = _
              exact hI
            · exact h2
      | aboveMEvenTEven =>
          exact (False.elim <| by simpa [hI,
            WildQuadraticCoefficientInputs.tauSource,
            WildQuadraticCoefficientInputs.chiFSource] using source.retained)
      | aboveMEvenTOdd Wtau =>
          apply noCorrection
          · change WildQuadraticCoefficientData.chiCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
          · change WildQuadraticCoefficientData.tauCorrectionClass
              (view.criticalInputs.toCoefficientData q) = none
            rw [hI]
            rfl
      | aboveMOddTEven Wchi =>
          apply finish
          apply wildQuadraticStrictHighOddCompletion ht htpos hres pi hpi
            hgen refinedView actualRows coordinates Wchi
          · left
            change view.criticalInputs = _
            exact hI
          · apply hstrictOfAbove
            rw [hI]
            rfl
      | aboveMOddTOdd Wtau Wchi =>
          apply finish
          apply wildQuadraticStrictHighOddCompletion ht htpos hres pi hpi
            hgen refinedView actualRows coordinates Wchi
          · right
            exact ⟨Wtau, by
              change view.criticalInputs = _
              exact hI⟩
          · apply hstrictOfAbove
            rw [hI]
            rfl

end

end LanglandsFirstMainLemma
