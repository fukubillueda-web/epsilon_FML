import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.Lamprecht.StationaryClass

/-!
# The truncated norm polynomial at stationary depth

For conductor decompositions

  m_K = 2 d_K + epsilon_K,    m_F = 2 d_F + epsilon_F,

this file constructs the representative-free additive map

  p_K^(d_K + epsilon_K) / p_K^m_K  ->  p_F^(d_F + epsilon_F) / p_F^m_F

induced by x |-> N(1+x)-1.  Its precision certificate keeps separate the
three norm-filtration inclusions at the variable, conductor, and stationary
ambiguity depths.  The last one also induces norm on the unit stationary
classes U_K^0/U_K^d_K -> U_F^0/U_F^d_F.

The exact elementary-symmetric expansion is retained.  A trace-only
specialization is available only after every nonlinear coefficient,
including the terminal norm term, has been proved to vanish at the target
precision.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-! ## Certified depths and norm-filtration precision -/

/-- A stationary conductor decomposition m = 2d + epsilon with epsilon in {0,1}. -/
structure IsStationaryConductorDecomposition (m d epsilon : ℕ) : Prop where
  conductor_gt_one : 1 < m
  epsilon_le_one : epsilon ≤ 1
  conductor_eq : m = 2 * d + epsilon

namespace IsStationaryConductorDecomposition

variable {m d epsilon : ℕ}

/-- The minimal stationary variable depth d+epsilon is positive. -/
theorem variableDepth_pos
    (h : IsStationaryConductorDecomposition m d epsilon) :
    0 < d + epsilon := by
  rcases h with ⟨hm, hepsilon, rfl⟩
  omega

/-- The floor half-depth d is positive for a conductor greater than one. -/
theorem floorDepth_pos
    (h : IsStationaryConductorDecomposition m d epsilon) :
    0 < d := by
  rcases h with ⟨hm, hepsilon, rfl⟩
  omega

/-- The stationary variable depth lies below the conductor. -/
theorem variableDepth_le_conductor
    (h : IsStationaryConductorDecomposition m d epsilon) :
    d + epsilon ≤ m := by
  rcases h with ⟨hm, hepsilon, rfl⟩
  omega

/-- The conductor lies in the additive range of the stationary variable depth. -/
theorem conductor_le_two_variableDepth
    (h : IsStationaryConductorDecomposition m d epsilon) :
    m ≤ 2 * (d + epsilon) := by
  rcases h with ⟨hm, hepsilon, rfl⟩
  omega

/-- The coefficient ambiguity depth is exactly m-(d+epsilon)=d. -/
theorem conductor_sub_variableDepth
    (h : IsStationaryConductorDecomposition m d epsilon) :
    m - (d + epsilon) = d := by
  rcases h with ⟨hm, hepsilon, rfl⟩
  omega

end IsStationaryConductorDecomposition

/-- The norm sends the indicated upstairs unit-filtration layer into the
downstairs layer. -/
def NormUnitFiltrationInclusion (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ u : Kˣ, u ∈ unitFiltration K sourceDepth →
    normUnits F K u ∈ unitFiltration F targetDepth

/-- The three distinct norm-filtration inclusions at stationary depth. -/
structure NormPolynomialPrecision
    (mK dK epsilonK mF dF epsilonF : ℕ) : Prop where
  sourceDecomposition :
    IsStationaryConductorDecomposition mK dK epsilonK
  targetDecomposition :
    IsStationaryConductorDecomposition mF dF epsilonF
  variable_inclusion :
    NormUnitFiltrationInclusion F K (dK + epsilonK) (dF + epsilonF)
  conductor_inclusion :
    NormUnitFiltrationInclusion F K mK mF
  ambiguity_inclusion :
    NormUnitFiltrationInclusion F K dK dF

/-! ## Norm on unit filtrations and their quotients -/

/-- Restriction of norm to two certified unit-filtration layers. -/
noncomputable def normUnitFiltrationHom
    {sourceDepth targetDepth : ℕ}
    (h : NormUnitFiltrationInclusion F K sourceDepth targetDepth) :
    unitFiltration K sourceDepth →* unitFiltration F targetDepth where
  toFun u := ⟨normUnits F K (u : Kˣ), h (u : Kˣ) u.property⟩
  map_one' := by ext; simp
  map_mul' u v := by ext; simp

@[simp]
theorem coe_normUnitFiltrationHom
    {sourceDepth targetDepth : ℕ}
    (h : NormUnitFiltrationInclusion F K sourceDepth targetDepth)
    (u : unitFiltration K sourceDepth) :
    ((normUnitFiltrationHom F K h u : unitFiltration F targetDepth) : Fˣ) =
      normUnits F K (u : Kˣ) := rfl

/-- Norm induced on certified unit-filtration quotients. -/
noncomputable def normUnitFiltrationQuotientHom
    {sourceNum sourceDen targetNum targetDen : ℕ}
    (hsource : sourceNum ≤ sourceDen) (htarget : targetNum ≤ targetDen)
    (hnum : NormUnitFiltrationInclusion F K sourceNum targetNum)
    (hden : NormUnitFiltrationInclusion F K sourceDen targetDen) :
    UnitFiltrationQuotient K sourceNum sourceDen hsource →*
      UnitFiltrationQuotient F targetNum targetDen htarget :=
  QuotientGroup.lift (unitFiltrationInside K hsource)
    ((unitFiltrationQuotientMk F htarget).comp
      (normUnitFiltrationHom F K hnum))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        unitFiltrationQuotientMk_eq_one_iff]
      exact hden (u : Kˣ) ((mem_unitFiltrationInside K hsource u).1 hu))

@[simp]
theorem normUnitFiltrationQuotientHom_mk
    {sourceNum sourceDen targetNum targetDen : ℕ}
    (hsource : sourceNum ≤ sourceDen) (htarget : targetNum ≤ targetDen)
    (hnum : NormUnitFiltrationInclusion F K sourceNum targetNum)
    (hden : NormUnitFiltrationInclusion F K sourceDen targetDen)
    (u : unitFiltration K sourceNum) :
    normUnitFiltrationQuotientHom F K hsource htarget hnum hden
        (unitFiltrationQuotientMk K hsource u) =
      unitFiltrationQuotientMk F htarget
        ⟨normUnits F K (u : Kˣ), hnum (u : Kˣ) u.property⟩ := rfl

/-! ## The additive truncated norm -/

/-- The additive truncated norm on arbitrary positive linear-range depths.
The stationary map below is its conductor-decomposition specialization. -/
noncomputable def truncatedNormPolynomial
    {sourceNum sourceDen targetNum targetDen : ℕ}
    (hsourcePos : 0 < sourceNum) (htargetPos : 0 < targetNum)
    (hsource : sourceNum ≤ sourceDen) (htarget : targetNum ≤ targetDen)
    (hsourceLinear : sourceDen ≤ 2 * sourceNum)
    (htargetLinear : targetDen ≤ 2 * targetNum)
    (hnum : NormUnitFiltrationInclusion F K sourceNum targetNum)
    (hden : NormUnitFiltrationInclusion F K sourceDen targetDen) :
    LatticeQuotient K (sourceNum : ℤ) (sourceDen : ℤ)
        (Int.ofNat_le.mpr hsource) →+
      LatticeQuotient F (targetNum : ℤ) (targetDen : ℤ)
        (Int.ofNat_le.mpr htarget) where
  toFun x := Multiplicative.toAdd
    (positiveUnitFiltrationQuotientMulEquivLattice F htargetPos htarget htargetLinear
      (normUnitFiltrationQuotientHom F K hsource htarget hnum hden
        ((positiveUnitFiltrationQuotientMulEquivLattice K hsourcePos hsource
          hsourceLinear).symm (Multiplicative.ofAdd x))))
  map_zero' := by simp
  map_add' x y := by simp

/-- Evaluation of the generic truncated norm on a numerator representative. -/
@[simp]
theorem truncatedNormPolynomial_mk
    {sourceNum sourceDen targetNum targetDen : ℕ}
    (hsourcePos : 0 < sourceNum) (htargetPos : 0 < targetNum)
    (hsource : sourceNum ≤ sourceDen) (htarget : targetNum ≤ targetDen)
    (hsourceLinear : sourceDen ≤ 2 * sourceNum)
    (htargetLinear : targetDen ≤ 2 * targetNum)
    (hnum : NormUnitFiltrationInclusion F K sourceNum targetNum)
    (hden : NormUnitFiltrationInclusion F K sourceDen targetDen)
    (x : lattice K (sourceNum : ℤ)) :
    truncatedNormPolynomial F K hsourcePos htargetPos hsource htarget
        hsourceLinear htargetLinear hnum hden
        (latticeQuotientMk K (Int.ofNat_le.mpr hsource) x) =
      latticeQuotientMk F (Int.ofNat_le.mpr htarget)
        (positiveUnitDisplacement F htargetPos
          ⟨normUnits F K (positiveUnitOfLattice K hsourcePos x : Kˣ),
            hnum _ (positiveUnitOfLattice K hsourcePos x).property⟩) := by
  change Multiplicative.toAdd
      (positiveUnitFiltrationQuotientMulEquivLattice F htargetPos htarget htargetLinear
        (normUnitFiltrationQuotientHom F K hsource htarget hnum hden
          ((positiveUnitFiltrationQuotientMulEquivLattice K hsourcePos hsource
            hsourceLinear).symm
            (Multiplicative.ofAdd (latticeQuotientMk K _ x))))) = _
  have hsourceInv :
      (positiveUnitFiltrationQuotientMulEquivLattice K hsourcePos hsource
          hsourceLinear).symm
          (Multiplicative.ofAdd
            (latticeQuotientMk K (Int.ofNat_le.mpr hsource) x)) =
        unitFiltrationQuotientMk K hsource
          (positiveUnitOfLattice K hsourcePos x) := by
    apply (positiveUnitFiltrationQuotientMulEquivLattice K hsourcePos hsource
      hsourceLinear).injective
    rw [(positiveUnitFiltrationQuotientMulEquivLattice K hsourcePos hsource
      hsourceLinear).apply_symm_apply]
    change Multiplicative.ofAdd
        (latticeQuotientMk K (Int.ofNat_le.mpr hsource) x) =
      Multiplicative.ofAdd
        (positiveUnitFiltrationQuotientEquivLattice K hsourcePos hsource
          (unitFiltrationQuotientMk K hsource
            (positiveUnitOfLattice K hsourcePos x)))
    rw [positiveUnitFiltrationQuotientEquivLattice_mk]
    apply congrArg Multiplicative.ofAdd
    apply (latticeQuotientMk_eq_mk_iff K (Int.ofNat_le.mpr hsource)).2
    simp
  rw [hsourceInv, normUnitFiltrationQuotientHom_mk]
  rfl

/-- The truncated norm map at the manuscript's stationary depth. -/
noncomputable def normPolynomial
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF) :
    LamprechtVariableQuotient K (mK : ℤ) ((dK + epsilonK : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.sourceDecomposition.variableDepth_le_conductor) →+
      LamprechtVariableQuotient F (mF : ℤ) ((dF + epsilonF : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.targetDecomposition.variableDepth_le_conductor) :=
  truncatedNormPolynomial F K
    h.sourceDecomposition.variableDepth_pos
    h.targetDecomposition.variableDepth_pos
    h.sourceDecomposition.variableDepth_le_conductor
    h.targetDecomposition.variableDepth_le_conductor
    h.sourceDecomposition.conductor_le_two_variableDepth
    h.targetDecomposition.conductor_le_two_variableDepth
    h.variable_inclusion h.conductor_inclusion

/-- The field-valued norm polynomial N(1+x)-1. -/
noncomputable def normPolynomialValue (x : K) : F :=
  norm F K (1 + x) - 1

/-- Exact norm expansion, with every elementary symmetric term retained. -/
theorem normPolynomialValue_eq_sum_elementarySymmetric (x : K) :
    normPolynomialValue F K x =
      ∑ j ∈ Finset.range (Module.finrank F K),
        elementarySymmetric F K (j + 1) x := by
  rw [normPolynomialValue, norm_one_add_eq_one_add_sum_elementarySymmetric]
  abel

/-- The representative naturally produced by the quotient construction. -/
noncomputable def normPolynomialRepresentative
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (x : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    lattice F ((dF + epsilonF : ℕ) : ℤ) :=
  positiveUnitDisplacement F h.targetDecomposition.variableDepth_pos
    ⟨normUnits F K
        (positiveUnitOfLattice K h.sourceDecomposition.variableDepth_pos x : Kˣ),
      h.variable_inclusion _
        (positiveUnitOfLattice K h.sourceDecomposition.variableDepth_pos x).property⟩

@[simp]
theorem coe_normPolynomialRepresentative
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (x : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    (normPolynomialRepresentative F K h x : F) =
      normPolynomialValue F K (x : K) := by
  simp [normPolynomialRepresentative, normPolynomialValue]

/-- Evaluation of the stationary truncated norm on every supplied numerator. -/
@[simp]
theorem normPolynomial_mk
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (x : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    normPolynomial F K h
        (latticeQuotientMk K
          (Int.ofNat_le.mpr h.sourceDecomposition.variableDepth_le_conductor) x) =
      latticeQuotientMk F
        (Int.ofNat_le.mpr h.targetDecomposition.variableDepth_le_conductor)
        (normPolynomialRepresentative F K h x) :=
  truncatedNormPolynomial_mk F K
    h.sourceDecomposition.variableDepth_pos
    h.targetDecomposition.variableDepth_pos
    h.sourceDecomposition.variableDepth_le_conductor
    h.targetDecomposition.variableDepth_le_conductor
    h.sourceDecomposition.conductor_le_two_variableDepth
    h.targetDecomposition.conductor_le_two_variableDepth
    h.variable_inclusion h.conductor_inclusion x

@[simp]
theorem normPolynomial_zero
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF) :
    normPolynomial F K h 0 = 0 :=
  map_zero (normPolynomial F K h)

/-- Exact additivity at the two certified half-depth precisions. -/
@[simp]
theorem normPolynomial_add
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (x y : LamprechtVariableQuotient K (mK : ℤ)
      ((dK + epsilonK : ℕ) : ℤ)
      (Int.ofNat_le.mpr h.sourceDecomposition.variableDepth_le_conductor)) :
    normPolynomial F K h (x + y) =
      normPolynomial F K h x + normPolynomial F K h y :=
  map_add (normPolynomial F K h) x y

/-- The conductor-depth inclusion makes the polynomial output independent
of the source lattice representative. -/
theorem normPolynomial_representative_independent
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (x y : lattice K ((dK + epsilonK : ℕ) : ℤ))
    (hxy : CongruentAtDepth (mK : ℤ) (x : K) (y : K)) :
    CongruentAtDepth (mF : ℤ)
      (normPolynomialRepresentative F K h x : F)
      (normPolynomialRepresentative F K h y : F) := by
  have hmk :
      latticeQuotientMk K
          (Int.ofNat_le.mpr
            h.sourceDecomposition.variableDepth_le_conductor) x =
        latticeQuotientMk K
          (Int.ofNat_le.mpr
            h.sourceDecomposition.variableDepth_le_conductor) y :=
    (latticeQuotientMk_eq_mk_iff_congruentAtDepth K
      (Int.ofNat_le.mpr
        h.sourceDecomposition.variableDepth_le_conductor)).2 hxy
  have himage := congrArg (normPolynomial F K h) hmk
  rw [normPolynomial_mk, normPolynomial_mk] at himage
  exact (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
    (Int.ofNat_le.mpr
      h.targetDecomposition.variableDepth_le_conductor)).1 himage

/-- Quotient evaluation by the exact elementary-symmetric expansion. -/
theorem normPolynomial_mk_eq_sum_elementarySymmetric
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (x : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    ∃ hsum :
        (∑ j ∈ Finset.range (Module.finrank F K),
          elementarySymmetric F K (j + 1) (x : K)) ∈
            lattice F ((dF + epsilonF : ℕ) : ℤ),
      normPolynomial F K h
          (latticeQuotientMk K
            (Int.ofNat_le.mpr h.sourceDecomposition.variableDepth_le_conductor) x) =
        latticeQuotientMk F
          (Int.ofNat_le.mpr h.targetDecomposition.variableDepth_le_conductor)
          ⟨∑ j ∈ Finset.range (Module.finrank F K),
            elementarySymmetric F K (j + 1) (x : K), hsum⟩ := by
  have hvalue :
      normPolynomialValue F K (x : K) ∈
        lattice F ((dF + epsilonF : ℕ) : ℤ) := by
    rw [← coe_normPolynomialRepresentative F K h x]
    exact (normPolynomialRepresentative F K h x).property
  have hsum :
      (∑ j ∈ Finset.range (Module.finrank F K),
        elementarySymmetric F K (j + 1) (x : K)) ∈
          lattice F ((dF + epsilonF : ℕ) : ℤ) := by
    rw [← normPolynomialValue_eq_sum_elementarySymmetric F K]
    exact hvalue
  refine ⟨hsum, ?_⟩
  rw [normPolynomial_mk]
  congr 1
  apply Subtype.ext
  exact (coe_normPolynomialRepresentative F K h x).trans
    (normPolynomialValue_eq_sum_elementarySymmetric F K (x : K))

/-! ## Trace and the exact nonlinear correction -/

/-- The exact trace-lattice inclusion required at one quotient depth. -/
def TraceLatticeInclusion (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ x : K, x ∈ lattice K (sourceDepth : ℤ) →
    trace F K x ∈ lattice F (targetDepth : ℤ)

/-- Trace restricted to certified numerator lattices. -/
noncomputable def traceLatticeHom
    {sourceDepth targetDepth : ℕ}
    (h : TraceLatticeInclusion F K sourceDepth targetDepth) :
    lattice K (sourceDepth : ℤ) →+ lattice F (targetDepth : ℤ) where
  toFun x := ⟨trace F K (x : K), h (x : K) x.property⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_traceLatticeHom
    {sourceDepth targetDepth : ℕ}
    (h : TraceLatticeInclusion F K sourceDepth targetDepth)
    (x : lattice K (sourceDepth : ℤ)) :
    ((traceLatticeHom F K h x : lattice F (targetDepth : ℤ)) : F) =
      trace F K (x : K) :=
  rfl

/-- Trace on actual lattice quotients, with separate numerator and
denominator precision. -/
noncomputable def traceLatticeQuotientHom
    {sourceNum sourceDen targetNum targetDen : ℕ}
    (hsource : sourceNum ≤ sourceDen) (htarget : targetNum ≤ targetDen)
    (hnum : TraceLatticeInclusion F K sourceNum targetNum)
    (hden : TraceLatticeInclusion F K sourceDen targetDen) :
    LatticeQuotient K (sourceNum : ℤ) (sourceDen : ℤ)
        (Int.ofNat_le.mpr hsource) →+
      LatticeQuotient F (targetNum : ℤ) (targetDen : ℤ)
        (Int.ofNat_le.mpr htarget) :=
  QuotientAddGroup.lift
    (latticeInside K (Int.ofNat_le.mpr hsource)).toAddSubgroup
    ((latticeQuotientMk F (Int.ofNat_le.mpr htarget)).toAddMonoidHom.comp
      (traceLatticeHom F K hnum))
    (by
      intro x hx
      rw [AddMonoidHom.mem_ker]
      apply (latticeQuotientMk_eq_zero_iff F
        (Int.ofNat_le.mpr htarget)).2
      exact hden (x : K)
        ((mem_latticeInside K (Int.ofNat_le.mpr hsource)).1 hx))

@[simp]
theorem traceLatticeQuotientHom_mk
    {sourceNum sourceDen targetNum targetDen : ℕ}
    (hsource : sourceNum ≤ sourceDen) (htarget : targetNum ≤ targetDen)
    (hnum : TraceLatticeInclusion F K sourceNum targetNum)
    (hden : TraceLatticeInclusion F K sourceDen targetDen)
    (x : lattice K (sourceNum : ℤ)) :
    traceLatticeQuotientHom F K hsource htarget hnum hden
        (latticeQuotientMk K (Int.ofNat_le.mpr hsource) x) =
      latticeQuotientMk F (Int.ofNat_le.mpr htarget)
        ⟨trace F K (x : K), hnum (x : K) x.property⟩ :=
  rfl

/-- Reindexing of the nonlinear tail from shifted ranges to degrees
2 through the terminal extension degree. -/
theorem sum_range_pred_shift_eq_sum_Icc
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range (n - 1), f (k + 2)) =
      ∑ j ∈ Finset.Icc 2 n, f j := by
  apply Finset.sum_bij (fun k _ => k + 2)
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro a₁ ha₁ a₂ ha₂ heq
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 2, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rfl

/-- Every nonlinear elementary-symmetric correction, including the
terminal norm term. -/
noncomputable def normPolynomialHigherCorrectionValue (x : K) : F :=
  ∑ j ∈ Finset.Icc 2 (Module.finrank F K),
    elementarySymmetric F K j x

/-- Exact trace-plus-correction expansion; no precision truncation occurs. -/
theorem normPolynomialValue_eq_trace_add_higherCorrection (x : K) :
    normPolynomialValue F K x =
      trace F K x + normPolynomialHigherCorrectionValue F K x := by
  have hdegree : 0 < Module.finrank F K := Module.finrank_pos
  calc
    normPolynomialValue F K x =
        ∑ j ∈ Finset.range (Module.finrank F K),
          elementarySymmetric F K (j + 1) x :=
      normPolynomialValue_eq_sum_elementarySymmetric F K x
    _ = (∑ j ∈ Finset.range (Module.finrank F K - 1),
          elementarySymmetric F K (j + 2) x) +
          elementarySymmetric F K 1 x := by
      conv_lhs =>
        rw [← Nat.succ_pred_eq_of_pos hdegree, Finset.sum_range_succ']
      congr 1
    _ = normPolynomialHigherCorrectionValue F K x + trace F K x := by
      rw [normPolynomialHigherCorrectionValue, elementarySymmetric_one]
      congr 1
      exact sum_range_pred_shift_eq_sum_Icc
        (fun j => elementarySymmetric F K j x) hdegree
    _ = trace F K x + normPolynomialHigherCorrectionValue F K x :=
      add_comm _ _

/-- Vanishing precision for exactly the intermediate degrees 2 <= j < [K:F]. -/
def NormPolynomialIntermediateTermsVanishAt
    (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ (x : K), x ∈ lattice K (sourceDepth : ℤ) →
    ∀ {j : ℕ}, 2 ≤ j → j < Module.finrank F K →
      elementarySymmetric F K j x ∈ lattice F (targetDepth : ℤ)

/-- Separate vanishing precision for the terminal norm coefficient. -/
def NormPolynomialTerminalTermVanishAt
    (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ (x : K), x ∈ lattice K (sourceDepth : ℤ) →
    elementarySymmetric F K (Module.finrank F K) x ∈
      lattice F (targetDepth : ℤ)

/-- The strong wild symmetric bound supplies exactly the intermediate
vanishing range; it makes no claim about the terminal norm coefficient. -/
theorem wild_normPolynomialIntermediateTermsVanishAt
    [IsGalois F K]
    (p T sourceDepth targetDepth : ℕ)
    (hp : p.Prime) (hT : 2 ≤ T)
    (hres : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace :
      TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (hdepth : p * targetDepth ≤
      2 * sourceDepth + (p - 1) * T) :
    NormPolynomialIntermediateTermsVanishAt
      F K sourceDepth targetDepth := by
  intro x hx j hjtwo hjlt
  exact wild_intermediateSymmetric_bound F K p T sourceDepth targetDepth
    hp hT hres hdegree htrace hdepth hx hjtwo (by simpa [hdegree] using hjlt)

/-- In a totally ramified extension, a source-depth bound kills the
terminal norm term at every shallower requested target depth. -/
theorem totallyRamified_normPolynomialTerminalTermVanishAt
    (p sourceDepth targetDepth : ℕ)
    (hdegree : Module.finrank F K = p)
    (hram : ramificationIndex F K = p)
    (hdepth : targetDepth ≤ sourceDepth) :
    NormPolynomialTerminalTermVanishAt
      F K sourceDepth targetDepth := by
  intro x hx
  rw [mem_lattice, hdegree]
  calc
    (((targetDepth : ℕ) : ℤ) : WithTop ℤ) ≤
        (((sourceDepth : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast hdepth
    _ ≤ ord F (elementarySymmetric F K p x) :=
      elementarySymmetric_degree_bound F K p (sourceDepth : ℤ)
        hdegree hram hx

/-- The trace difference has the requested precision only after both the
intermediate coefficients and the terminal norm coefficient vanish. -/
theorem normPolynomialValue_sub_trace_mem
    {sourceDepth targetDepth : ℕ}
    (hintermediate :
      NormPolynomialIntermediateTermsVanishAt F K sourceDepth targetDepth)
    (hterminal :
      NormPolynomialTerminalTermVanishAt F K sourceDepth targetDepth)
    (x : K) (hx : x ∈ lattice K (sourceDepth : ℤ)) :
    normPolynomialValue F K x - trace F K x ∈
      lattice F (targetDepth : ℤ) := by
  have hhigher :
      normPolynomialHigherCorrectionValue F K x ∈
        lattice F (targetDepth : ℤ) := by
    apply sum_mem_lattice F
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj2, hjle⟩
    rcases lt_or_eq_of_le hjle with hjlt | rfl
    · exact hintermediate x hx hj2 hjlt
    · exact hterminal x hx
  rw [normPolynomialValue_eq_trace_add_higherCorrection]
  convert hhigher using 1
  abel

/-- With only the intermediate terms killed, the terminal norm remains
in the exact critical-range polynomial. -/
theorem normPolynomialValue_sub_trace_add_norm_mem
    {sourceDepth targetDepth : ℕ}
    (hdegree : 2 ≤ Module.finrank F K)
    (hintermediate :
      NormPolynomialIntermediateTermsVanishAt F K sourceDepth targetDepth)
    (x : K) (hx : x ∈ lattice K (sourceDepth : ℤ)) :
    normPolynomialValue F K x - (trace F K x + norm F K x) ∈
      lattice F (targetDepth : ℤ) := by
  have hmiddle :
      (∑ j ∈ Finset.Icc 2 (Module.finrank F K - 1),
        elementarySymmetric F K j x) ∈
          lattice F (targetDepth : ℤ) := by
    apply sum_mem_lattice F
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj2, hjle⟩
    exact hintermediate x hx hj2 (by omega)
  have hsplit :
      normPolynomialHigherCorrectionValue F K x =
        (∑ j ∈ Finset.Icc 2 (Module.finrank F K - 1),
          elementarySymmetric F K j x) + norm F K x := by
    rw [normPolynomialHigherCorrectionValue]
    conv_lhs =>
      rw [show Module.finrank F K =
        Module.finrank F K - 1 + 1 by omega]
    rw [Finset.sum_Icc_succ_top (by omega)]
    congr 1
    rw [Nat.sub_add_cancel (by omega), elementarySymmetric_finrank]
  rw [normPolynomialValue_eq_trace_add_higherCorrection, hsplit]
  convert hmiddle using 1
  abel

/-- Critical-range quotient formula: the intermediate coefficients vanish,
while the terminal norm coefficient is retained. -/
theorem normPolynomial_mk_eq_trace_add_norm
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (hdegree : 2 ≤ Module.finrank F K)
    (hintermediate :
      NormPolynomialIntermediateTermsVanishAt F K (dK + epsilonK) mF)
    (x : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    ∃ hvalue : trace F K (x : K) + norm F K (x : K) ∈
        lattice F ((dF + epsilonF : ℕ) : ℤ),
      normPolynomial F K h
          (latticeQuotientMk K
            (Int.ofNat_le.mpr
              h.sourceDecomposition.variableDepth_le_conductor) x) =
        latticeQuotientMk F
          (Int.ofNat_le.mpr
            h.targetDecomposition.variableDepth_le_conductor)
          ⟨trace F K (x : K) + norm F K (x : K), hvalue⟩ := by
  have hdiff :
      normPolynomialValue F K (x : K) -
          (trace F K (x : K) + norm F K (x : K)) ∈
        lattice F (mF : ℤ) :=
    normPolynomialValue_sub_trace_add_norm_mem F K hdegree
      hintermediate (x : K) x.property
  have hdiffNum :
      normPolynomialValue F K (x : K) -
          (trace F K (x : K) + norm F K (x : K)) ∈
        lattice F ((dF + epsilonF : ℕ) : ℤ) :=
    lattice_antitone F
      (Int.ofNat_le.mpr
        h.targetDecomposition.variableDepth_le_conductor) hdiff
  have hnorm :
      normPolynomialValue F K (x : K) ∈
        lattice F ((dF + epsilonF : ℕ) : ℤ) := by
    rw [← coe_normPolynomialRepresentative F K h x]
    exact (normPolynomialRepresentative F K h x).property
  have hvalue :
      trace F K (x : K) + norm F K (x : K) ∈
        lattice F ((dF + epsilonF : ℕ) : ℤ) := by
    have hmem :=
      (lattice F ((dF + epsilonF : ℕ) : ℤ)).sub_mem hnorm hdiffNum
    convert hmem using 1
    abel
  refine ⟨hvalue, ?_⟩
  rw [normPolynomial_mk]
  apply (latticeQuotientMk_eq_mk_iff F
    (Int.ofNat_le.mpr
      h.targetDecomposition.variableDepth_le_conductor)).2
  rw [coe_normPolynomialRepresentative]
  exact hdiff

/-- The stationary trace map with the two independently certified trace
depths needed by the later adjoint. -/
noncomputable def normPolynomialTrace
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K mK mF) :
    LamprechtVariableQuotient K (mK : ℤ) ((dK + epsilonK : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.sourceDecomposition.variableDepth_le_conductor) →+
      LamprechtVariableQuotient F (mF : ℤ) ((dF + epsilonF : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.targetDecomposition.variableDepth_le_conductor) :=
  traceLatticeQuotientHom F K
    h.sourceDecomposition.variableDepth_le_conductor
    h.targetDecomposition.variableDepth_le_conductor
    hvariable hconductor

@[simp]
theorem normPolynomialTrace_mk
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K mK mF)
    (x : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    normPolynomialTrace F K h hvariable hconductor
        (latticeQuotientMk K
          (Int.ofNat_le.mpr
            h.sourceDecomposition.variableDepth_le_conductor) x) =
      latticeQuotientMk F
        (Int.ofNat_le.mpr
          h.targetDecomposition.variableDepth_le_conductor)
        ⟨trace F K (x : K), hvariable (x : K) x.property⟩ :=
  rfl

/-- Trace compatibility at stationary precision.  The terminal norm term
is a separate hypothesis and cannot be inferred from the intermediate
symmetric bounds. -/
theorem normPolynomial_eq_trace
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K mK mF)
    (hintermediate :
      NormPolynomialIntermediateTermsVanishAt F K (dK + epsilonK) mF)
    (hterminal :
      NormPolynomialTerminalTermVanishAt F K (dK + epsilonK) mF) :
    normPolynomial F K h =
      normPolynomialTrace F K h hvariable hconductor := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ :=
    latticeQuotientMk_surjective K
      (Int.ofNat_le.mpr
        h.sourceDecomposition.variableDepth_le_conductor) z
  rw [normPolynomial_mk, normPolynomialTrace_mk]
  apply (latticeQuotientMk_eq_mk_iff F
    (Int.ofNat_le.mpr
      h.targetDecomposition.variableDepth_le_conductor)).2
  change (normPolynomialRepresentative F K h x : F) -
      trace F K (x : K) ∈ lattice F (mF : ℤ)
  rw [coe_normPolynomialRepresentative]
  exact normPolynomialValue_sub_trace_mem F K
    hintermediate hterminal (x : K) x.property

/-! ## Elementary-symmetric certificates for the three inclusions -/

/-- Every term in the exact norm expansion at sourceDepth has targetDepth
valuation. -/
def NormPolynomialElementaryBoundsAt
    (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ (x : K), (((sourceDepth : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x →
    ∀ j ∈ Finset.range (Module.finrank F K),
      (((targetDepth : ℕ) : ℤ) : WithTop ℤ) ≤
        ord F (elementarySymmetric F K (j + 1) x)

/-- The degree-one member of the elementary-symmetric bounds is exactly
the required trace-lattice inclusion. -/
theorem traceLatticeInclusion_of_elementarySymmetricBounds
    {sourceDepth targetDepth : ℕ}
    (hterms :
      NormPolynomialElementaryBoundsAt F K sourceDepth targetDepth) :
    TraceLatticeInclusion F K sourceDepth targetDepth := by
  intro x hx
  have htrace := hterms x hx 0
    (Finset.mem_range.mpr Module.finrank_pos)
  simpa using htrace

/-- Elementary-symmetric bounds prove the corresponding norm-filtration
inclusion; no norm-filtration statement is assumed in this lemma. -/
theorem normUnitFiltrationInclusion_of_elementarySymmetricBounds
    {sourceDepth targetDepth : ℕ}
    (hsourcePos : 0 < sourceDepth) (htargetPos : 0 < targetDepth)
    (hterms : NormPolynomialElementaryBoundsAt F K sourceDepth targetDepth) :
    NormUnitFiltrationInclusion F K sourceDepth targetDepth := by
  intro u hu
  let uK : unitFiltration K sourceDepth := ⟨u, hu⟩
  let x : lattice K (sourceDepth : ℤ) :=
    positiveUnitDisplacement K hsourcePos uK
  have hxTerms :
      ∀ j ∈ Finset.range (Module.finrank F K),
        elementarySymmetric F K (j + 1) (x : K) ∈
          lattice F (targetDepth : ℤ) := by
    intro j hj
    exact hterms (x : K) x.property j hj
  have hvalue :
      normPolynomialValue F K (x : K) ∈ lattice F (targetDepth : ℤ) := by
    rw [normPolynomialValue_eq_sum_elementarySymmetric]
    exact sum_mem_lattice F hxTerms
  let y : lattice F (targetDepth : ℤ) :=
    ⟨normPolynomialValue F K (x : K), hvalue⟩
  have heq :
      normUnits F K u = (positiveUnitOfLattice F htargetPos y : Fˣ) := by
    apply Units.ext
    simp [uK, x, y, normPolynomialValue]
  rw [heq]
  exact (positiveUnitOfLattice F htargetPos y).property

/-- Construct all three stationary norm-filtration inclusions from exact
elementary-symmetric bounds at their respective depths. -/
theorem NormPolynomialPrecision.ofElementarySymmetricBounds
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (hK : IsStationaryConductorDecomposition mK dK epsilonK)
    (hF : IsStationaryConductorDecomposition mF dF epsilonF)
    (hvariable :
      NormPolynomialElementaryBoundsAt F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : NormPolynomialElementaryBoundsAt F K mK mF)
    (hambiguity : NormPolynomialElementaryBoundsAt F K dK dF) :
    NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF where
  sourceDecomposition := hK
  targetDecomposition := hF
  variable_inclusion :=
    normUnitFiltrationInclusion_of_elementarySymmetricBounds F K
      hK.variableDepth_pos hF.variableDepth_pos hvariable
  conductor_inclusion :=
    normUnitFiltrationInclusion_of_elementarySymmetricBounds F K
      (Nat.lt_trans Nat.zero_lt_one hK.conductor_gt_one)
      (Nat.lt_trans Nat.zero_lt_one hF.conductor_gt_one) hconductor
  ambiguity_inclusion :=
    normUnitFiltrationInclusion_of_elementarySymmetricBounds F K
      hK.floorDepth_pos hF.floorDepth_pos hambiguity

/-! ## The extra stationary ambiguity inclusion -/

/-- Norm on local units preserves depth zero. -/
theorem normUnitFiltrationInclusion_zero :
    NormUnitFiltrationInclusion F K 0 0 := by
  intro u hu
  rw [mem_unitFiltration_zero] at hu ⊢
  rw [coe_normUnits, ord_norm, hu]
  simp

/-- The extra depth inclusion induces norm on honest unit stationary
classes. -/
noncomputable def stationaryNormClass
    (sourceDepth targetDepth : ℕ)
    (hambiguity :
      NormUnitFiltrationInclusion F K sourceDepth targetDepth) :
    UnitFiltrationQuotient K 0 sourceDepth (Nat.zero_le _) →*
      UnitFiltrationQuotient F 0 targetDepth (Nat.zero_le _) :=
  normUnitFiltrationQuotientHom F K (Nat.zero_le _) (Nat.zero_le _)
    (normUnitFiltrationInclusion_zero F K) hambiguity

@[simp]
theorem stationaryNormClass_mk
    (sourceDepth targetDepth : ℕ)
    (hambiguity :
      NormUnitFiltrationInclusion F K sourceDepth targetDepth)
    (u : unitFiltration K 0) :
    stationaryNormClass F K sourceDepth targetDepth hambiguity
        (unitFiltrationQuotientMk K (Nat.zero_le _) u) =
      unitFiltrationQuotientMk F (Nat.zero_le _)
        ⟨normUnits F K (u : Kˣ),
          normUnitFiltrationInclusion_zero F K (u : Kˣ) u.property⟩ := rfl

/-- Norm of a stationary unit class is independent of its unit
representative at exactly the extra ambiguity precision. -/
theorem stationaryNormClass_representative_independent
    (sourceDepth targetDepth : ℕ)
    (hambiguity :
      NormUnitFiltrationInclusion F K sourceDepth targetDepth)
    (u v : unitFiltration K 0)
    (huv : CongruentAtDepth (sourceDepth : ℤ)
      (((u : Kˣ) : K)) (((v : Kˣ) : K))) :
    CongruentAtDepth (targetDepth : ℤ)
      ((normUnits F K (u : Kˣ) : Fˣ) : F)
      ((normUnits F K (v : Kˣ) : Fˣ) : F) := by
  have hmk :
      unitFiltrationQuotientMk K (Nat.zero_le sourceDepth) u =
        unitFiltrationQuotientMk K (Nat.zero_le sourceDepth) v :=
    (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth K
      (Nat.zero_le sourceDepth) u v).2 huv
  have himage :=
    congrArg (stationaryNormClass F K sourceDepth targetDepth hambiguity) hmk
  rw [stationaryNormClass_mk, stationaryNormClass_mk] at himage
  exact (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
    (Nat.zero_le targetDepth) _ _).1 himage

/-- The stationary ambiguity norm map attached to a full precision
certificate. -/
noncomputable def normPolynomialStationaryNormClass
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF) :
    UnitFiltrationQuotient K 0 dK (Nat.zero_le _) →*
      UnitFiltrationQuotient F 0 dF (Nat.zero_le _) :=
  stationaryNormClass F K dK dF h.ambiguity_inclusion

/-! ## Denominator-depth projection -/

/-- Norm on unit quotients commutes with replacing both denominators by
shallower depths. -/
theorem normUnitFiltrationQuotientHom_projection
    {sourceNum sourceDen₁ sourceDen₂ targetNum targetDen₁ targetDen₂ : ℕ}
    (hsource₁ : sourceNum ≤ sourceDen₁)
    (hsource₁₂ : sourceDen₁ ≤ sourceDen₂)
    (htarget₁ : targetNum ≤ targetDen₁)
    (htarget₁₂ : targetDen₁ ≤ targetDen₂)
    (hnum : NormUnitFiltrationInclusion F K sourceNum targetNum)
    (hden₁ :
      NormUnitFiltrationInclusion F K sourceDen₁ targetDen₁)
    (hden₂ :
      NormUnitFiltrationInclusion F K sourceDen₂ targetDen₂)
    (z : UnitFiltrationQuotient K sourceNum sourceDen₂
      (hsource₁.trans hsource₁₂)) :
    unitFiltrationQuotientProjection F htarget₁ htarget₁₂
        (normUnitFiltrationQuotientHom F K
          (hsource₁.trans hsource₁₂) (htarget₁.trans htarget₁₂)
          hnum hden₂ z) =
      normUnitFiltrationQuotientHom F K hsource₁ htarget₁ hnum hden₁
        (unitFiltrationQuotientProjection K hsource₁ hsource₁₂ z) := by
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective K
      (hsource₁.trans hsource₁₂) z
  rfl

/-- The additive truncated norm commutes with denominator-depth
projection. -/
theorem truncatedNormPolynomial_projection
    {sourceNum sourceDen₁ sourceDen₂ targetNum targetDen₁ targetDen₂ : ℕ}
    (hsourcePos : 0 < sourceNum) (htargetPos : 0 < targetNum)
    (hsource₁ : sourceNum ≤ sourceDen₁)
    (hsource₁₂ : sourceDen₁ ≤ sourceDen₂)
    (htarget₁ : targetNum ≤ targetDen₁)
    (htarget₁₂ : targetDen₁ ≤ targetDen₂)
    (hsourceLinear₁ : sourceDen₁ ≤ 2 * sourceNum)
    (hsourceLinear₂ : sourceDen₂ ≤ 2 * sourceNum)
    (htargetLinear₁ : targetDen₁ ≤ 2 * targetNum)
    (htargetLinear₂ : targetDen₂ ≤ 2 * targetNum)
    (hnum : NormUnitFiltrationInclusion F K sourceNum targetNum)
    (hden₁ :
      NormUnitFiltrationInclusion F K sourceDen₁ targetDen₁)
    (hden₂ :
      NormUnitFiltrationInclusion F K sourceDen₂ targetDen₂)
    (z : LatticeQuotient K (sourceNum : ℤ) (sourceDen₂ : ℤ)
      (Int.ofNat_le.mpr (hsource₁.trans hsource₁₂))) :
    latticeQuotientProjection F (Int.ofNat_le.mpr htarget₁)
        (Int.ofNat_le.mpr htarget₁₂)
        (truncatedNormPolynomial F K hsourcePos htargetPos
          (hsource₁.trans hsource₁₂) (htarget₁.trans htarget₁₂)
          hsourceLinear₂ htargetLinear₂ hnum hden₂ z) =
      truncatedNormPolynomial F K hsourcePos htargetPos
        hsource₁ htarget₁ hsourceLinear₁ htargetLinear₁ hnum hden₁
        (latticeQuotientProjection K (Int.ofNat_le.mpr hsource₁)
          (Int.ofNat_le.mpr hsource₁₂) z) := by
  obtain ⟨x, rfl⟩ :=
    latticeQuotientMk_surjective K
      (Int.ofNat_le.mpr (hsource₁.trans hsource₁₂)) z
  rw [truncatedNormPolynomial_mk, latticeQuotientProjection_mk]
  rw [latticeQuotientProjection_mk, truncatedNormPolynomial_mk]

/-! ## Denominator-ratio scaling for the later adjoint -/

/-- The field-valued ratio by which the trace adjoint changes for a
specified denominator pair. -/
def normPolynomialDenominatorRatio (gammaF : Fˣ) (gammaK : Kˣ) : K :=
  (gammaK : K) / algebraMap F K (gammaF : F)

theorem normPolynomialDenominatorRatio_ne_zero
    (gammaF : Fˣ) (gammaK : Kˣ) :
    normPolynomialDenominatorRatio F K gammaF gammaK ≠ 0 := by
  exact div_ne_zero (Units.ne_zero gammaK)
    ((map_ne_zero (algebraMap F K)).2 (Units.ne_zero gammaF))

/-- Scaling a base-field coefficient by the explicit denominator ratio. -/
noncomputable def denominatorScaledRepresentative
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hratio :
      ord K (normPolynomialDenominatorRatio F K gammaF gammaK) = 0)
    (x : lattice F 0) : lattice K 0 := by
  refine ⟨normPolynomialDenominatorRatio F K gammaF gammaK *
      algebraMap F K (x : F), ?_⟩
  rw [mem_lattice, ord_mul, hratio, ord_algebraMap, zero_add]
  have hx := x.property
  rw [mem_lattice] at hx
  simpa using nsmul_le_nsmul_right hx (ramificationIndex F K)

private theorem denominatorScaledRepresentative_congruent
    (dF dK : ℕ) (hdepth : dK ≤ ramificationIndex F K * dF)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hratio :
      ord K (normPolynomialDenominatorRatio F K gammaF gammaK) = 0)
    (x y : lattice F 0)
    (hxy : CongruentAtDepth (dF : ℤ) (x : F) (y : F)) :
    CongruentAtDepth (dK : ℤ)
      (denominatorScaledRepresentative F K gammaF gammaK hratio x : K)
      (denominatorScaledRepresentative F K gammaF gammaK hratio y : K) := by
  rw [CongruentAtDepth]
  change (((dK : ℕ) : ℤ) : WithTop ℤ) ≤
    ord K (normPolynomialDenominatorRatio F K gammaF gammaK *
        algebraMap F K (x : F) -
      normPolynomialDenominatorRatio F K gammaF gammaK *
        algebraMap F K (y : F))
  rw [← mul_sub, ← map_sub, ord_mul, hratio, zero_add, ord_algebraMap]
  have hscaled := nsmul_le_nsmul_right hxy (ramificationIndex F K)
  have hdepth' : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤
      ramificationIndex F K • ((((dF : ℕ) : ℤ) : WithTop ℤ)) := by
    calc
      (((dK : ℕ) : ℤ) : WithTop ℤ) ≤
          ((((ramificationIndex F K * dF : ℕ) : ℤ)) : WithTop ℤ) := by
            exact_mod_cast hdepth
      _ = ramificationIndex F K •
          ((((dF : ℕ) : ℤ) : WithTop ℤ)) := by
        rw [← WithTop.coe_nsmul]
        norm_num [nsmul_eq_mul]
  exact hdepth'.trans hscaled

/-- Multiplication by the exact denominator ratio, followed by base-field
inclusion, on the honest coefficient lattice quotients.  Exact local-unit
order and ramification-scaled depth are explicit hypotheses. -/
noncomputable def denominatorScaledAlgebraMap
    (dF dK : ℕ) (hdepth : dK ≤ ramificationIndex F K * dF)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hratio :
      ord K (normPolynomialDenominatorRatio F K gammaF gammaK) = 0) :
    LatticeQuotient F 0 (dF : ℤ) (by omega) →+
      LatticeQuotient K 0 (dK : ℤ) (by omega) where
  toFun := latticeQuotientLift F (by omega)
    (fun x ↦ latticeQuotientMk K (by omega)
      (denominatorScaledRepresentative F K gammaF gammaK hratio x))
    (fun x y hxy ↦ by
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth K
        (by omega)).2
      exact denominatorScaledRepresentative_congruent F K dF dK hdepth
        gammaF gammaK hratio x y hxy)
  map_zero' := by
    change latticeQuotientLift F (by omega) _ _
      (latticeQuotientMk F (by omega) 0) = 0
    rw [latticeQuotientLift_mk]
    apply (latticeQuotientMk_eq_zero_iff K (by omega)).2
    simp [denominatorScaledRepresentative]
  map_add' := by
    intro a b
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F (by omega) a
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F (by omega) b
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk,
      ← latticeQuotientMk_add]
    congr 1
    apply Subtype.ext
    simp [denominatorScaledRepresentative, mul_add]

@[simp]
theorem denominatorScaledAlgebraMap_mk
    (dF dK : ℕ) (hdepth : dK ≤ ramificationIndex F K * dF)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hratio :
      ord K (normPolynomialDenominatorRatio F K gammaF gammaK) = 0)
    (x : lattice F 0) :
    denominatorScaledAlgebraMap F K dF dK hdepth gammaF gammaK hratio
        (latticeQuotientMk F (by omega) x) =
      latticeQuotientMk K (by omega)
        (denominatorScaledRepresentative F K gammaF gammaK hratio x) :=
  rfl

/-- With a common denominator, denominator scaling is ordinary base-field
inclusion at the certified ramification-scaled precision. -/
@[simp]
theorem denominatorScaledAlgebraMap_common_mk
    (dF dK : ℕ) (hdepth : dK ≤ ramificationIndex F K * dF)
    (gammaF : Fˣ) (x : lattice F 0) :
    denominatorScaledAlgebraMap F K dF dK hdepth gammaF
        (Units.map (algebraMap F K) gammaF)
        (by simp [normPolynomialDenominatorRatio])
        (latticeQuotientMk F (by omega) x) =
      latticeQuotientMk K (by omega)
        ⟨algebraMap F K (x : F), by
          rw [mem_lattice, ord_algebraMap]
          have hx := x.property
          rw [mem_lattice] at hx
          simpa using nsmul_le_nsmul_right hx (ramificationIndex F K)⟩ := by
  rw [denominatorScaledAlgebraMap_mk]
  congr 1
  apply Subtype.ext
  simp [denominatorScaledRepresentative, normPolynomialDenominatorRatio]

/-- Exact trace identity behind the denominator-sensitive trace adjoint. -/
theorem trace_denominatorScaled_div
    (gammaF : Fˣ) (gammaK : Kˣ) (x : F) (y : K) :
    trace F K
        (normPolynomialDenominatorRatio F K gammaF gammaK *
            algebraMap F K x * y / (gammaK : K)) =
      x * trace F K y / (gammaF : F) := by
  have harg :
      normPolynomialDenominatorRatio F K gammaF gammaK *
            algebraMap F K x * y / (gammaK : K) =
        algebraMap F K (x / (gammaF : F)) * y := by
    rw [map_div₀]
    simp only [normPolynomialDenominatorRatio]
    field_simp [Units.ne_zero gammaF, Units.ne_zero gammaK]
  rw [harg, ← Algebra.smul_def, map_smul]
  ring

end

end LanglandsFirstMainLemma
