import LanglandsFirstMainLemma.Cases.WildQuadratic.ErrorFormula
import LanglandsFirstMainLemma.Ramification.PullbackConductors

namespace LanglandsFirstMainLemma

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The exact nine-row nonboundary range -/

/-- The signed-depth alternatives outside the odd quadratic boundary. The
strict inequalities are the manuscript's `b < t` and `t < b`, rewritten
with `m = b + 1` and `T = t + 1`; equality is admitted only for even `T`. -/
inductive WildQuadraticNonboundaryDepthCase (T m : ℕ) : Prop where
  | below (h : m < T)
  | boundaryEven (h : m = T) (hT : Even T)
  | above (h : T < m)

/-- Exactly the nine coefficient-table rows other than the exceptional odd
boundary occur in the nonboundary theorem. -/
theorem wildQuadratic_nonboundary_rows
    {k : Type*} [Field k]
    (D : WildQuadraticCoefficientData k) (hD : D.row ≠ .boundaryOdd) :
    D.row = .belowMEvenTEven ∨
      D.row = .belowMEvenTOdd ∨
      D.row = .belowMOddTEven ∨
      D.row = .belowMOddTOdd ∨
      D.row = .boundaryEven ∨
      D.row = .aboveMEvenTEven ∨
      D.row = .aboveMEvenTOdd ∨
      D.row = .aboveMOddTEven ∨
      D.row = .aboveMOddTOdd := by
  cases D <;> simp_all [WildQuadraticCoefficientData.row]

/-- The conductor-indexed coefficient row yields exactly one of the two
strict ranges or the even boundary. -/
theorem wildQuadratic_nonboundary_depthCase
    {k : Type*} [Field k] {t m : ℕ}
    (hm : 1 < m)
    (D : WildQuadraticCoefficientData.AtConductors k m t)
    (hD : D.1.row ≠ .boundaryOdd) :
    WildQuadraticNonboundaryDepthCase (t + 1) m := by
  rcases lt_trichotomy m (t + 1) with hbelow | heq | habove
  · exact .below hbelow
  · have hmPred : m - 1 = t := by omega
    have hclass : WildQuadraticCoefficientRow.ofConductors (m - 1) t ≠
        .boundaryOdd := by
      intro hodd
      apply hD
      exact D.2.trans hodd
    have heven : Even (t + 1) := by
      by_contra hnotEven
      have hoddRow :
          WildQuadraticCoefficientRow.ofConductors (m - 1) t =
            .boundaryOdd := by
        rw [hmPred]
        simp [WildQuadraticCoefficientRow.ofConductors,
          WildQuadraticConductorParity.ofConductor, hnotEven]
      exact hclass hoddRow
    exact .boundaryEven heq heven
  · exact .above habove

/-! ## Orders supplied by the actual Lamprecht rows -/

namespace LocalLamprechtPhaseData

variable {E : Type*}
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- The numerator in an actual selected Lamprecht row has exact order zero.
This is a statement about the supplied representative of its quotient class,
not a choice of a canonical representative. -/
theorem selectedStationaryPair_beta_order
    (S : LocalLamprechtPhaseData E chi psi) :
    ord E S.selectedStationaryPair.beta = (0 : WithTop ℤ) := by
  cases S with
  | even d hm hlarge Gamma c hc =>
      simpa [selectedStationaryPair] using
        stationaryNumeratorClass_representative_ord E chi psi
          (chi.conductor : ℤ)
          (lamprechtFormula_stationaryDepth E chi d 0 (by omega)
            (by simpa using hm) hlarge)
          Gamma Gamma.property c hc
  | odd d hm hlarge Gamma delta hdelta c hc =>
      simpa [selectedStationaryPair] using
        stationaryNumeratorClass_representative_ord E chi psi
          (chi.conductor : ℤ)
          (lamprechtFormula_stationaryDepth E chi d 1 (by omega)
            hm hlarge)
          Gamma Gamma.property c hc

/-- Consequently the exact selected stationary ratio has order
`-(m(theta)+n(psi))`. -/
theorem selectedStationaryPair_ratio_order
    (S : LocalLamprechtPhaseData E chi psi) :
    ord E S.selectedStationaryPair.ratio =
      ((-((chi.conductor : ℤ) + psi.conductor) : ℤ) : WithTop ℤ) := by
  rw [WildQuadraticStationaryPair.ratio, ord_div,
    S.selectedStationaryPair_beta_order, S.selectedStationaryPair_gamma,
    S.gamma.property]
  norm_num

end LocalLamprechtPhaseData

/-! ## Trace depth for the retained common correction -/

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- Lemma `lem:quadratic-depth` in signed-depth form.  The boundary-unit
hypothesis is separated because it is derived below from the two actual
stationary rows and whole-orbit minimality. -/
theorem wildQuadratic_correction_mem
    [IsGalois F K]
    {T m : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hcase : WildQuadraticNonboundaryDepthCase T m)
    (hboundaryUnit : m = T → Even T →
      ord F C.denominator = (0 : WithTop ℤ)) :
    C.X ∈ lattice F (T : ℤ) := by
  by_cases htwo : (2 : F) = 0
  · rw [C.X_eq, htwo, zero_mul, zero_div]
    exact (lattice F (T : ℤ)).zero_mem
  · let a : ℤ := (T : ℤ) - (m : ℤ)
    have hsource : ord K (C.u : K) = (a : WithTop ℤ) := by
      simpa only [a] using C.source_order
    have htarget : ord F (C.n : F) = (a : WithTop ℤ) := by
      simpa only [a] using C.target_order
    have hu : (C.u : K) ∈ lattice K a := by
      rw [mem_lattice, hsource]
    have hs : C.s ∈ lattice F ((a + (T : ℤ)) / 2) := by
      have hs' := trace_mem_lattice_floor F K pi hpi hgen a hu
      rw [C.differentExponent_eq, C.ramificationIndex_eq_two] at hs'
      norm_num at hs'
      rw [mem_lattice]
      simpa only [WildQuadraticCommonCorrectionData.s] using hs'
    have hone : (1 : K) ∈ lattice K 0 := by simp
    have htwoMem : (2 : F) ∈ lattice F ((T : ℤ) / 2) := by
      have htrace := trace_mem_lattice_floor F K pi hpi hgen 0 hone
      have htraceOne : trace F K (1 : K) = (2 : F) := by
        rw [← map_one (algebraMap F K), trace_algebraMap, C.degree_eq_two]
        norm_num
      rw [htraceOne, C.differentExponent_eq,
        C.ramificationIndex_eq_two] at htrace
      norm_num at htrace
      exact htrace
    have hnum : (2 : F) * C.s ∈
        lattice F ((T : ℤ) / 2 + (a + (T : ℤ)) / 2) :=
      mul_mem_lattice F htwoMem hs
    rw [C.X_eq]
    cases hcase with
    | below hbelow =>
        have ha : 0 < a := by dsimp only [a]; omega
        have hne : ord F (1 : F) ≠ ord F (C.n : F) := by
          rw [ord_one, htarget]
          exact ne_of_lt (by exact_mod_cast ha)
        have hden : ord F C.denominator = (0 : WithTop ℤ) := by
          rw [WildQuadraticCommonCorrectionData.denominator,
            ord_add_eq_min F hne, ord_one, htarget,
            min_eq_left]
          exact_mod_cast ha.le
        apply (div_mem_lattice_iff F C.denominator ((2 : F) * C.s)
          0 (T : ℤ) hden).2
        apply lattice_antitone F (show (0 : ℤ) + T ≤
          (T : ℤ) / 2 + (a + (T : ℤ)) / 2 by omega)
        exact hnum
    | boundaryEven heq heven =>
        have ha : a = 0 := by dsimp only [a]; omega
        have hden := hboundaryUnit heq heven
        apply (div_mem_lattice_iff F C.denominator ((2 : F) * C.s)
          0 (T : ℤ) hden).2
        apply lattice_antitone F (show (0 : ℤ) + T ≤
          (T : ℤ) / 2 + (a + (T : ℤ)) / 2 by
            obtain ⟨j, hj⟩ := heven
            omega)
        exact hnum
    | above habove =>
        have ha : a < 0 := by dsimp only [a]; omega
        have hne : ord F (1 : F) ≠ ord F (C.n : F) := by
          rw [ord_one, htarget]
          exact Ne.symm (ne_of_lt (by exact_mod_cast ha))
        have hden : ord F C.denominator = (a : WithTop ℤ) := by
          rw [WildQuadraticCommonCorrectionData.denominator,
            ord_add_eq_min F hne, ord_one, htarget,
            min_eq_right]
          exact_mod_cast ha.le
        apply (div_mem_lattice_iff F C.denominator ((2 : F) * C.s)
          a (T : ℤ) hden).2
        apply lattice_antitone F (show a + T ≤
          (T : ℤ) / 2 + (a + (T : ℤ)) / 2 by omega)
        exact hnum

/-! ## Compatibility with the exact ErrorFormula -/

section RealAssembly

variable [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
  {V : WildQuadraticCoefficientView F K q t m}
  {data : FirstMainComputationalData F K V.chiFData.character
    V.psiF.character}
  {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
  {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
    V.psiF.character data D (t := t) (m := m)}

section CommonAssemblyCore

variable {W : WildQuadraticCommonCoefficientView F K t m}
  {commonData : FirstMainComputationalData F K W.chiFData.character
    W.psiF.character}
  {commonPhase : FirstMainPhaseData F K W.chiFData.character
    W.psiF.character commonData}
  {commonAssembly : ExactQuadraticPhaseAssembly F K W.chiFData.character
    W.psiF.character commonData commonPhase (t := t) (m := m)}

private theorem quadraticIndex_tau_ne_one_common :
    commonAssembly.indexing.tau ≠ 1 := by
  intro htau
  have hindex : commonAssembly.indexing.index false =
      commonAssembly.indexing.index true := by
    rw [commonAssembly.indexing.index_false, htau,
      commonAssembly.indexing.index_true]
  exact Bool.false_ne_true (commonAssembly.indexing.index.injective hindex)

private theorem wildQuadratic_tau_conductor_eq_common
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (commonData.normCharacterData commonAssembly.indexing.tau).conductor =
      t + 1 := by
  have hcond : IsMultiplicativeConductor F
      (commonData.normCharacterData
        commonAssembly.indexing.tau).character (t + 1) := by
    rw [commonData.normCharacterData_character]
    exact ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      commonAssembly.indexing.tau quadraticIndex_tau_ne_one_common
  exact ((commonData.normCharacterData
    commonAssembly.indexing.tau).conductor_eq_of_isConductor hcond).symm

private theorem wildQuadratic_base_conductor_eq_common
    (coordinates : WildQuadraticCommonCoordinateCompatibility W commonData
      commonPhase commonAssembly) :
    W.chiFData.conductor = m := by
  calc
    W.chiFData.conductor = (commonData.twistData 1).conductor := by
      rw [coordinates.baseData_eq]
    _ = commonAssembly.baseData.conductor := by
      rw [commonAssembly.baseData_eq]
    _ = m := commonAssembly.baseConductor

private theorem wildQuadratic_twist_conductor_eq_common
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W commonData
      commonPhase commonAssembly)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W.chiFData) :
    (commonData.twistData commonAssembly.indexing.tau).conductor =
      max m (t + 1) := by
  have hcond := minimalOrbit_nontrivialTwist_isConductor
    F K ht hres pi hpi hgen W.chiFData hminimal
      commonAssembly.indexing.tau quadraticIndex_tau_ne_one_common
  have hcond' : IsMultiplicativeConductor F
      (commonData.twistData commonAssembly.indexing.tau).character
        (max m (t + 1)) := by
    rw [commonData.twistData_character]
    simpa only [wildQuadratic_base_conductor_eq_common coordinates] using hcond
  exact ((commonData.twistData
    commonAssembly.indexing.tau).conductor_eq_of_isConductor hcond').symm

private theorem wildQuadratic_boundary_denominator_order_common
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticActualPhaseRows W commonData commonPhase
      commonAssembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W commonData
      commonPhase commonAssembly)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W.chiFData)
    (hboundary : m = t + 1) :
    ord F W.correction.denominator = (0 : WithTop ℤ) := by
  have htauConductor := wildQuadratic_tau_conductor_eq_common
    (commonAssembly := commonAssembly) ht hres pi hpi hgen
  have htwistConductor := wildQuadratic_twist_conductor_eq_common
    (commonAssembly := commonAssembly) ht hres pi hpi hgen coordinates hminimal
  have htauRatio := rows.tau.selectedStationaryPair_ratio_order
  have htwistRatio := rows.twist.selectedStationaryPair_ratio_order
  rw [rows.tau_pair, htauConductor, coordinates.baseAddData_eq] at htauRatio
  have hmax : max m (t + 1) = t + 1 := by rw [hboundary, max_self]
  rw [rows.twist_pair, htwistConductor, coordinates.baseAddData_eq,
    hmax] at htwistRatio
  have htauRatio_ne : W.stationaryPairs.tau.ratio ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [htauRatio]
    exact WithTop.coe_ne_top
  have hden : W.correction.denominator =
      W.stationaryPairs.tauChiF.ratio /
        W.stationaryPairs.tau.ratio := by
    rw [W.tauChiF_ratio]
    apply (eq_div_iff htauRatio_ne).2
    dsimp only [WildQuadraticCommonCorrectionData.denominator]
    ring
  rw [hden, ord_div, htwistRatio, htauRatio]
  simp

private theorem wildQuadratic_A_order_common
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticActualPhaseRows W commonData commonPhase
      commonAssembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W commonData
      commonPhase commonAssembly) :
    ord F commonAssembly.A =
      ((-(((t + 1 : ℕ) : ℤ) + W.psiF.conductor) : ℤ) : WithTop ℤ) := by
  have htauRatio := rows.tau.selectedStationaryPair_ratio_order
  rw [rows.tau_pair,
    wildQuadratic_tau_conductor_eq_common (commonAssembly := commonAssembly)
      ht hres pi hpi hgen,
    coordinates.baseAddData_eq] at htauRatio
  rw [coordinates.A_eq]
  exact htauRatio

omit [Finite (NormCharacter F K)] in
private theorem wildQuadratic_additiveConductor_compTrace_common
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    commonData.extensionAddChar.conductor =
      2 * W.psiF.conductor + (t + 1 : ℕ) := by
  have hpsi : commonData.extensionAddChar.character =
      W.psiF.character.compTrace := by
    calc
      commonData.extensionAddChar.character =
          tracePullbackAddChar F K W.psiF.character :=
        commonData.extensionAddChar_character
      _ = W.psiF.character.compTrace := by
        apply ContinuousAddChar.ext
        intro x
        rw [tracePullbackAddChar_apply,
          ContinuousAddChar.compTrace_apply]
  have h := W.psiF.conductor_compTrace_eq_cyclicPrime
    F K ht hres pi hpi hgen commonData.extensionAddChar hpsi
  rw [W.correction.degree_eq_two] at h
  simpa using h

end CommonAssemblyCore

private theorem quadraticIndex_tau_ne_one : A.indexing.tau ≠ 1 :=
  quadraticIndex_tau_ne_one_common (W := V.toCommon) (commonData := data)
    (commonPhase := D) (commonAssembly := A)

/-- The real nonidentity norm row has exact conductor `T=t+1`. -/
theorem wildQuadratic_tau_conductor_eq
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (data.normCharacterData A.indexing.tau).conductor = t + 1 :=
  wildQuadratic_tau_conductor_eq_common (W := V.toCommon)
    (commonData := data) (commonPhase := D) (commonAssembly := A)
      ht hres pi hpi hgen

/-- The base row really has the conductor `m` indexing the coefficient view. -/
theorem wildQuadratic_base_conductor_eq
    (coordinates : WildQuadraticCoordinateCompatibility V data D A) :
    V.chiFData.conductor = m :=
  wildQuadratic_base_conductor_eq_common coordinates.toCommon

/-- Whole-orbit minimality gives the exact nontrivial-twist conductor
`max m T`, retaining the weak equality case at the boundary. -/
theorem wildQuadratic_twist_conductor_eq
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K V.chiFData) :
    (data.twistData A.indexing.tau).conductor = max m (t + 1) :=
  wildQuadratic_twist_conductor_eq_common (W := V.toCommon)
    (commonData := data) (commonPhase := D) (commonAssembly := A)
      ht hres pi hpi hgen coordinates.toCommon hminimal

/-- At `m=T`, the literal correction denominator `1+n` is a unit.  This is
derived from the actual tau and twisted rows and minimality; the correction
unit is not discarded or assumed. -/
theorem wildQuadratic_boundary_denominator_order
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticPhaseRowCompatibility V data D A)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K V.chiFData)
    (hboundary : m = t + 1) :
    ord F V.correction.denominator = (0 : WithTop ℤ) :=
  wildQuadratic_boundary_denominator_order_common (W := V.toCommon)
    (commonData := data) (commonPhase := D) (commonAssembly := A)
      ht hres pi hpi hgen rows.toActualPhaseRows coordinates.toCommon hminimal
        hboundary

/-- The actual norm-row stationary ratio used in ErrorFormula has exact
order `-(T+n(psi_F))`. -/
theorem wildQuadratic_A_order
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticPhaseRowCompatibility V data D A)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A) :
    ord F A.A =
      ((-(((t + 1 : ℕ) : ℤ) + V.psiF.conductor) : ℤ) : WithTop ℤ) :=
  wildQuadratic_A_order_common (W := V.toCommon) (commonData := data)
    (commonPhase := D) (commonAssembly := A)
      ht hres pi hpi hgen rows.toActualPhaseRows coordinates.toCommon

omit [Finite (NormCharacter F K)] in
/-- PullbackConductors supplies the exact upstairs additive conductor
`2*n(psi_F)+T`; this is recorded at the same depth used to kill the retained
elementary phase. -/
theorem wildQuadratic_additiveConductor_compTrace
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    data.extensionAddChar.conductor =
      2 * V.psiF.conductor + (t + 1 : ℕ) :=
  wildQuadratic_additiveConductor_compTrace_common (W := V.toCommon)
    ht hres pi hpi hgen

/-- Exact elementary conclusion: the trace-pullback conductor is the one
from PullbackConductors, `X` lies in `p_F^T`, and the retained phase with its
minus orientation is one. -/
theorem wildQuadratic_nonboundary_elementary
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticPhaseRowCompatibility V data D A)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K V.chiFData)
    (hrow : (V.coefficients.1).row ≠ .boundaryOdd) :
    data.extensionAddChar.conductor =
        2 * V.psiF.conductor + (t + 1 : ℕ) ∧
      V.correction.X ∈ lattice F ((t + 1 : ℕ) : ℤ) ∧
      (V.psiF.character (-A.A * V.correction.X) : ℂ) = 1 := by
  have hcase := wildQuadratic_nonboundary_depthCase V.conductor_gt_one
    V.coefficients hrow
  have hboundaryUnit : m = t + 1 → Even (t + 1) →
      ord F V.correction.denominator = (0 : WithTop ℤ) := by
    intro hboundary _
    exact wildQuadratic_boundary_denominator_order (A := A)
      ht hres pi hpi hgen rows coordinates hminimal hboundary
  have hX := wildQuadratic_correction_mem pi hpi hgen V.correction
    hcase hboundaryUnit
  refine ⟨wildQuadratic_additiveConductor_compTrace (V := V)
      ht hres pi hpi hgen, hX, ?_⟩
  have hAord := wildQuadratic_A_order (A := A)
    ht hres pi hpi hgen rows coordinates
  have hAmem : A.A ∈ lattice F
      (-(((t + 1 : ℕ) : ℤ) + V.psiF.conductor)) := by
    rw [mem_lattice, hAord]
  have hnegX : -V.correction.X ∈ lattice F ((t + 1 : ℕ) : ℤ) :=
    neg_mem_lattice F hX
  have harg : A.A * (-V.correction.X) ∈
      lattice F (-V.psiF.conductor) := by
    have hmul := mul_mem_lattice F hAmem hnegX
    simpa only [show
      -(((t + 1 : ℕ) : ℤ) + V.psiF.conductor) + (t + 1 : ℕ) =
        -V.psiF.conductor by omega] using hmul
  have htrivial := V.psiF.isConductor.trivial
    (A.A * (-V.correction.X)) harg
  have hval := congrArg (Units.val : ℂˣ → ℂ) htrivial
  simpa only [Units.val_one,
    show A.A * (-V.correction.X) = -A.A * V.correction.X by ring] using hval

/-! ## Q-free cancellation in the exact three all-even rows -/

section AllEvenAssembly

variable {W : WildQuadraticAllEvenCoefficientView F K t m}
  {commonData : FirstMainComputationalData F K W.chiFData.character
    W.psiF.character}
  {commonPhase : FirstMainPhaseData F K W.chiFData.character
    W.psiF.character commonData}
  {commonAssembly : ExactQuadraticPhaseAssembly F K W.chiFData.character
    W.psiF.character commonData commonPhase (t := t) (m := m)}

/-- Exact q-free elementary cancellation for the three actual all-even rows.
The proof retains the boundary denominator and derives its order from the
actual tau/twist stationary pairs. -/
theorem wildQuadratic_allEven_elementary
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticAllEvenPhaseRowCompatibility W commonData
      commonPhase commonAssembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W.toCommon
      commonData commonPhase commonAssembly)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W.chiFData) :
    commonData.extensionAddChar.conductor =
        2 * W.psiF.conductor + (t + 1 : ℕ) ∧
      W.correction.X ∈ lattice F ((t + 1 : ℕ) : ℤ) ∧
      (W.psiF.character
        (-commonAssembly.A * W.correction.X) : ℂ) = 1 := by
  have hrowEven : W.coefficients.1.row.IsAllEven := by
    change (W.criticalInputs.toAllEvenCoefficientData W.isAllEven).row.IsAllEven
    simpa using W.isAllEven
  have hrow : W.coefficients.1.row ≠ .boundaryOdd := by
    intro h
    rw [h] at hrowEven
    cases hrowEven
  have hcase := wildQuadratic_nonboundary_depthCase W.conductor_gt_one
    W.coefficients hrow
  have hboundaryUnit : m = t + 1 → Even (t + 1) →
      ord F W.correction.denominator = (0 : WithTop ℤ) := by
    intro hboundary _
    exact wildQuadratic_boundary_denominator_order_common
      (commonAssembly := commonAssembly) ht hres pi hpi hgen
        rows.actualRows coordinates hminimal hboundary
  have hX := wildQuadratic_correction_mem pi hpi hgen W.correction
    hcase hboundaryUnit
  refine ⟨wildQuadratic_additiveConductor_compTrace_common (W := W.toCommon)
      ht hres pi hpi hgen, hX, ?_⟩
  have hAord := wildQuadratic_A_order_common
    (commonAssembly := commonAssembly) ht hres pi hpi hgen
      rows.actualRows coordinates
  have hAmem : commonAssembly.A ∈ lattice F
      (-(((t + 1 : ℕ) : ℤ) + W.psiF.conductor)) := by
    rw [mem_lattice, hAord]
  have hnegX : -W.correction.X ∈ lattice F ((t + 1 : ℕ) : ℤ) :=
    neg_mem_lattice F hX
  have harg : commonAssembly.A * (-W.correction.X) ∈
      lattice F (-W.psiF.conductor) := by
    have hmul := mul_mem_lattice F hAmem hnegX
    simpa only [show
      -(((t + 1 : ℕ) : ℤ) + W.psiF.conductor) + (t + 1 : ℕ) =
        -W.psiF.conductor by omega] using hmul
  have htrivial := W.psiF.isConductor.trivial
    (commonAssembly.A * (-W.correction.X)) harg
  have hval := congrArg (Units.val : ℂˣ → ℂ) htrivial
  simpa only [Units.val_one,
    show commonAssembly.A * (-W.correction.X) =
      -commonAssembly.A * W.correction.X by ring] using hval

variable {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}

/-- Q-free wild-quadratic cancellation in exactly the three all-even rows. -/
theorem wildQuadratic_nonboundary_allEven
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (rows : WildQuadraticAllEvenPhaseRowCompatibility W commonData
      commonPhase commonAssembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W.toCommon
      commonData commonPhase commonAssembly)
    (completeCorrection : commonAssembly.CompleteCorrectionData)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W.chiFData) :
    errorTerm F K DeltaF DeltaK W.chiFData.character W.psiF.character = 1 := by
  let formula := wildQuadratic_allEvenErrorFormula hDeltaF hDeltaK rows
    coordinates completeCorrection
  have helementary := wildQuadratic_allEven_elementary
    (commonAssembly := commonAssembly) ht hres pi hpi hgen rows coordinates
      hminimal
  exact formula.exact_formula.trans helementary.2.2

end AllEvenAssembly

variable {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}

/-- Wild-quadratic cancellation in all and only the nine nonboundary rows.
The exact ErrorFormula first cancels the positively oriented refinement/Hasse
corrections, leaving `psi_F(-A*X)`; the depth theorem then makes that phase
one. -/
theorem wildQuadratic_nonboundary
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (rows : WildQuadraticPhaseRowCompatibility V data D A)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A)
    (refinements : WildQuadraticRefinementAssembly V data D A coordinates)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K V.chiFData)
    (hrow : (V.coefficients.1).row ≠ .boundaryOdd) :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character = 1 := by
  let formula := wildQuadratic_errorFormula hDeltaF hDeltaK rows coordinates
    refinements
  have hfinite := wildQuadratic_errorFormula_nonboundary formula hrow
  have helementary := wildQuadratic_nonboundary_elementary (A := A)
    ht hres pi hpi hgen rows coordinates hminimal hrow
  calc
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
        (V.psiF.character (-A.A * V.correction.X) : ℂ) :=
      hfinite.exact_formula
    _ = 1 := helementary.2.2

end RealAssembly

end

end LanglandsFirstMainLemma
