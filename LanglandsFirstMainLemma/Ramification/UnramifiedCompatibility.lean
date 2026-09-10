import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.ResidueField
import LanglandsFirstMainLemma.Basic.CharacterConductors
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.NormTrace
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Unramified trace, norm, conductor, and norm-quotient compatibility

For a finite unramified extension of nonarchimedean local fields this file derives, from the
local-field extension APIs, the full compatibility package used in Langlands's unramified case:
common uniformizers and residue degree, reduction of integral trace and norm, exact trace images
of every fractional lattice, exact norm images of every unit-filtration layer, preservation of
both conductor conventions, and the explicit cyclic norm quotient.  The positive-depth norm
surjectivity proof contains its completeness argument locally so that the node has exactly the
three dependencies recorded in the blueprint.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open IsLocalRing Filter Topology

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]

private theorem ord_unit_ne_top (u : Fˣ) : ord F (u : F) ≠ ⊤ :=
  (ord_ne_top_iff F).2 (Units.ne_zero u)

/-- The normalized integer order of a nonzero local-field element. -/
noncomputable def localUnitOrder (u : Fˣ) : ℤ :=
  (ord F (u : F)).untop (ord_unit_ne_top F u)

@[simp]
theorem coe_localUnitOrder (u : Fˣ) :
    (localUnitOrder F u : WithTop ℤ) = ord F (u : F) :=
  WithTop.coe_untop _ _

private noncomputable def localUnitOrderHom : Fˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (localUnitOrder F u)
  map_one' := by
    change localUnitOrder F 1 = 0
    apply WithTop.coe_injective
    rw [coe_localUnitOrder]
    simp
  map_mul' u v := by
    change localUnitOrder F (u * v) = localUnitOrder F u + localUnitOrder F v
    apply WithTop.coe_injective
    rw [WithTop.coe_add, coe_localUnitOrder, coe_localUnitOrder,
      coe_localUnitOrder]
    exact ord_mul F (u : F) (v : F)

/-- Normalized order modulo `f`, written multiplicatively. -/
noncomputable def localUnitOrderMod (f : ℕ) : Fˣ →* Multiplicative (ZMod f) :=
  (Int.castAddHom (ZMod f)).toMultiplicative.comp (localUnitOrderHom F)

@[simp]
theorem localUnitOrderMod_apply (f : ℕ) (u : Fˣ) :
    Multiplicative.toAdd (localUnitOrderMod F f u) =
      (localUnitOrder F u : ZMod f) := rfl

theorem localUnitOrderMod_surjective (f : ℕ) :
    Function.Surjective (localUnitOrderMod F f) := by
  obtain ⟨π₀, hπ₀irr⟩ :=
    IsDiscreteValuationRing.exists_irreducible (ringOfIntegers F)
  have hπspan : maximalIdeal (ringOfIntegers F) = Ideal.span {π₀} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π₀).mp hπ₀irr
  have hπunif : (ValuativeRel.valuation F).IsUniformizer (π₀ : F) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact hπspan
  have hπ0 : (π₀ : F) ≠ 0 := by
    intro h
    exact hπ₀irr.ne_zero (Subtype.ext h)
  let π : Fˣ := Units.mk0 (π₀ : F) hπ0
  intro z
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  refine ⟨π ^ a, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [localUnitOrderMod_apply]
  rw [← ha]
  congr 1
  apply WithTop.coe_injective
  rw [coe_localUnitOrder]
  change ord F ((Units.coeHom F) (π ^ a)) = (a : WithTop ℤ)
  rw [(Units.coeHom F).map_zpow, ord_zpow]
  change a • ord F (π₀ : F) = (a : WithTop ℤ)
  rw [ord_uniformizer F hπunif]
  cases a with
  | ofNat n => simp
  | negSucc n =>
      rw [negSucc_zsmul]
      have h : (n + 1) • (1 : WithTop ℤ) =
          (((n + 1) • (1 : ℤ) : ℤ) : WithTop ℤ) :=
        (WithTop.coe_nsmul (1 : ℤ) (n + 1)).symm
      rw [h, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr
      rw [Int.negSucc_eq]
      simp

private theorem unramified_map_maximalIdeal
    (hunr : ramificationIndex F K = 1) :
    Ideal.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))
        (maximalIdeal (ringOfIntegers F)) = maximalIdeal (ringOfIntegers K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (ringOfIntegers F)
  have hp : maximalIdeal (ringOfIntegers F) = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  let πK : ringOfIntegers K := algebraMap (ringOfIntegers F) (ringOfIntegers K) π
  have hcoe : (πK : K) = algebraMap F K (π : F) :=
    Valuation.HasExtension.val_algebraMap π
  have hπunifF : (ValuativeRel.valuation F).IsUniformizer (π : F) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact hp
  have hordK : ord K (πK : K) = 1 := by
    rw [hcoe, ord_algebraMap, hunr, one_nsmul, ord_uniformizer F hπunifF]
  have hπunifK : (ValuativeRel.valuation K).IsUniformizer (πK : K) :=
    (ord_eq_one_iff_isUniformizer K (πK : K)).mp hordK
  have hq : maximalIdeal (ringOfIntegers K) = Ideal.span {πK} :=
    Valuation.IsUniformizer.is_generator hπunifK
  rw [hp, Ideal.map_span, Set.image_singleton, ← hq]

private lemma Algebra.norm_quotient_mk_local
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] [IsLocalRing R] (x : S) :
    Algebra.norm (R ⧸ maximalIdeal R)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R S) (maximalIdeal R)) x) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b,
    Algebra.norm_eq_matrix_det (IsLocalRing.basisQuotient b), RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.toMatrix_apply, IsLocalRing.basisQuotient_apply,
    LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul,
    IsLocalRing.basisQuotient_repr]

/- The completeness step is kept private here: this node has only the three blueprint
dependencies listed in the manuscript graph, so it specializes the standard successive-lifting
argument instead of importing a later blueprint node. -/
private theorem unramified_isOpen_lattice
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (n : ℤ) :
    IsOpen (lattice E n : Set E) := by
  obtain ⟨a, ha⟩ := exists_ord_eq E n
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hopen := (ValuativeRel.valuation E).isOpen_closedBall
    (r := (ValuativeRel.valuation E).restrict a) (by simp [ha0])
  convert hopen using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff E a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation E),
    (ValuativeRel.valuation E).restrict_le_iff]

private theorem unramified_isClosed_lattice
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (n : ℤ) :
    IsClosed (lattice E n : Set E) := by
  exact AddSubgroup.isClosed_of_isOpen (lattice E n).toAddSubgroup
    (by simpa using unramified_isOpen_lattice E n)

private theorem unramified_localField_t2Space
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : T2Space E := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 hx)
  refine ⟨(lattice E (k + 1) : Set E),
    (unramified_isOpen_lattice E (k + 1)).mem_nhds (by simp), ?_⟩
  intro hmem
  rw [SetLike.mem_coe, mem_lattice, ← hk, WithTop.coe_le_coe] at hmem
  omega

private theorem unramified_lattice_hasBasis_nhds_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    (nhds (0 : E)).HasBasis (fun _ : ℤ ↦ True) fun n ↦ (lattice E n : Set E) := by
  rw [Filter.hasBasis_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨a, ha⟩ :=
      ValuativeRel.valuation_surjective (γ : ValuativeRel.ValueGroupWithZero E)
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact Units.ne_zero γ ha.symm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff E).2 ha0)
    refine ⟨k + 1, trivial, fun x hx ↦ hγ ?_⟩
    change ValuativeRel.valuation E x < (γ : ValuativeRel.ValueGroupWithZero E)
    rw [← ha]
    have hax : ord E a < ord E x := by
      rw [← hk]
      exact (WithTop.coe_lt_coe.mpr (show k < k + 1 by omega)).trans_le hx
    have hv : x <ᵥ a := (ord_lt_ord_iff E a x).1 hax
    rw [lt_iff_not_ge, ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation E)]
    exact hv
  · rintro ⟨n, -, hns⟩
    exact Filter.mem_of_superset
      ((unramified_isOpen_lattice E n).mem_nhds (by simp)) hns

private theorem unramified_tendsto_zero_of_mem_lattice
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ → ℕ} (hd : Tendsto d atTop atTop) {x : ℕ → E}
    (hx : ∀ n, x n ∈ lattice E (d n : ℤ)) :
    Tendsto x atTop (nhds 0) := by
  rw [(unramified_lattice_hasBasis_nhds_zero E).tendsto_right_iff]
  intro r _
  cases r with
  | ofNat r =>
      filter_upwards [(tendsto_atTop.1 hd r)] with n hn
      exact lattice_antitone E (Int.ofNat_le.2 hn) (hx n)
  | negSucc r =>
      filter_upwards [(tendsto_atTop.1 hd 0)] with n _
      exact lattice_antitone E (by omega) (hx n)

private theorem unramified_tendsto_one_of_mem_unitFiltration
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ → ℕ} (hd : Tendsto d atTop atTop) {u : ℕ → Eˣ}
    (hu : ∀ n, u n ∈ unitFiltration E (d n + 1)) :
    Tendsto (fun n ↦ (u n : E)) atTop (nhds 1) := by
  have hsub : Tendsto (fun n ↦ (u n : E) - 1) atTop (nhds 0) := by
    apply unramified_tendsto_zero_of_mem_lattice E hd
    intro n
    have hdeep :=
      (mem_unitFiltration_succ_iff_sub_mem_lattice E (d n) (u n)).1 (hu n)
    exact lattice_antitone E (by omega) hdeep
  convert hsub.const_add 1 using 1 <;> simp

private theorem unramified_successiveLifting_surjective
    {E L : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (φ : E →* L) (hφ : Continuous φ)
    (sourceDepth : ℕ → ℕ) (targetDepth : ℕ)
    (hsource_mono : Monotone sourceDepth)
    (hsource_tendsto : Tendsto sourceDepth atTop atTop)
    (hlift : ∀ (n : ℕ) (u : Lˣ),
      u ∈ unitFiltration L (targetDepth + n) →
        ∃ x : Eˣ, x ∈ unitFiltration E (sourceDepth n + 1) ∧
          u / Units.map φ x ∈ unitFiltration L (targetDepth + n + 1)) :
    ∀ u : Lˣ, u ∈ unitFiltration L targetDepth →
      ∃ x : Eˣ, x ∈ unitFiltration E (sourceDepth 0 + 1) ∧
        Units.map φ x = u := by
  classical
  intro u hu
  let lift : ∀ (n : ℕ) (v : unitFiltration L (targetDepth + n)),
      Σ x : unitFiltration E (sourceDepth n + 1),
        { w : unitFiltration L (targetDepth + (n + 1)) //
          (w : Lˣ) = (v : Lˣ) / Units.map φ (x : Eˣ) } := fun n v ↦ by
    let hex := hlift n (v : Lˣ) v.property
    let x : Eˣ := Classical.choose hex
    have hx : x ∈ unitFiltration E (sourceDepth n + 1) :=
      (Classical.choose_spec hex).1
    have herror :
        (v : Lˣ) / Units.map φ x ∈ unitFiltration L (targetDepth + n + 1) :=
      (Classical.choose_spec hex).2
    let x' : unitFiltration E (sourceDepth n + 1) := ⟨x, hx⟩
    let w : Lˣ := (v : Lˣ) / Units.map φ x
    have hw : w ∈ unitFiltration L (targetDepth + (n + 1)) := by
      simpa only [Nat.add_assoc] using herror
    exact ⟨x', ⟨⟨w, hw⟩, rfl⟩⟩
  let residual : (n : ℕ) → unitFiltration L (targetDepth + n) := fun n ↦
    Nat.rec (motive := fun k ↦ unitFiltration L (targetDepth + k))
      ⟨u, by simpa using hu⟩ (fun k v ↦ (lift k v).2.1) n
  let correction : (n : ℕ) → unitFiltration E (sourceDepth n + 1) := fun n ↦
    (lift n (residual n)).1
  have residual_succ : ∀ n : ℕ,
      (residual (n + 1)).1 =
        (residual n).1 / Units.map φ (correction n).1 := by
    intro n
    simpa [residual, correction] using (lift n (residual n)).2.2
  let partialProduct : ℕ → Eˣ := fun n ↦
    ∏ i ∈ Finset.range n, (correction i).1
  have partialProduct_succ : ∀ n : ℕ,
      partialProduct (n + 1) = partialProduct n * (correction n).1 := by
    intro n
    simp [partialProduct, Finset.prod_range_succ]
  have partialProduct_mem : ∀ n : ℕ,
      partialProduct n ∈ unitFiltration E (sourceDepth 0 + 1) := by
    intro n
    apply Subgroup.prod_mem
    intro i hi
    exact unitFiltration_antitone E
      (Nat.add_le_add_right (hsource_mono (Nat.zero_le i)) 1)
      (correction i).property
  have residual_eq : ∀ n : ℕ,
      (residual n).1 = u / Units.map φ (partialProduct n) := by
    intro n
    induction n with
    | zero => simp [residual, partialProduct]
    | succ n ih =>
        rw [residual_succ, ih, partialProduct_succ, map_mul]
        rw [div_div]
  have increment_mem : ∀ n : ℕ,
      (partialProduct (n + 1) : E) - (partialProduct n : E) ∈
        lattice E (sourceDepth n : ℤ) := by
    intro n
    have hp0 : (partialProduct n : E) ∈ lattice E 0 := by
      rw [mem_lattice]
      exact (mem_unitGroup_iff_ord_eq_zero E (partialProduct n)).1
        (unitFiltration_le_unitGroup E _ (partialProduct_mem n)) |>.ge
    have hc : ((correction n).1 : E) - 1 ∈ lattice E (sourceDepth n : ℤ) := by
      have hdeep :=
        (mem_unitFiltration_succ_iff_sub_mem_lattice E (sourceDepth n)
          (correction n).1).1 (correction n).property
      exact lattice_antitone E (by omega) hdeep
    rw [partialProduct_succ]
    change (partialProduct n : E) * ((correction n).1 : E) -
      (partialProduct n : E) ∈ _
    rw [show (partialProduct n : E) * ((correction n).1 : E) -
      (partialProduct n : E) =
        (partialProduct n : E) * (((correction n).1 : E) - 1) by ring]
    simpa only [zero_add] using mul_mem_lattice E hp0 hc
  letI : NonarchimedeanAddGroup E :=
    { toIsTopologicalAddGroup := inferInstance
      is_nonarchimedean := by
        intro V hV
        obtain ⟨n, -, hn⟩ :=
          (unramified_lattice_hasBasis_nhds_zero E).mem_iff.mp hV
        let W : OpenAddSubgroup E :=
          { toAddSubgroup := (lattice E n).toAddSubgroup
            isOpen' := by simpa using unramified_isOpen_lattice E n }
        exact ⟨W, hn⟩ }
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have partialProduct_cauchy : CauchySeq (fun n ↦ (partialProduct n : E)) := by
    apply NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero
    exact unramified_tendsto_zero_of_mem_lattice E hsource_tendsto increment_mem
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete partialProduct_cauchy
  have hx_mem : x - 1 ∈ lattice E ((sourceDepth 0 + 1 : ℕ) : ℤ) := by
    apply (unramified_isClosed_lattice E _).mem_of_tendsto
      (hx.sub tendsto_const_nhds)
    exact Filter.Eventually.of_forall fun n ↦
      (mem_unitFiltration_succ_iff_sub_mem_lattice E (sourceDepth 0)
        (partialProduct n)).1 (partialProduct_mem n)
  let xUnit : Eˣ := principalUnitOf E (sourceDepth 0) (x - 1) hx_mem
  have hxUnit : (xUnit : E) = x := by
    simp [xUnit]
  have hxUnit_mem : xUnit ∈ unitFiltration E (sourceDepth 0 + 1) :=
    principalUnitOf_mem E (sourceDepth 0) (x - 1) hx_mem
  have hresidual : Tendsto (fun n ↦ ((residual n).1 : L)) atTop (nhds 1) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    apply unramified_tendsto_one_of_mem_unitFiltration L tendsto_id
    intro n
    apply unitFiltration_antitone L
      (show n + 1 ≤ targetDepth + (n + 1) by omega)
    exact (residual (n + 1)).property
  have hφx0 : φ x ≠ 0 := by
    rw [← hxUnit]
    exact Units.ne_zero (Units.map φ xUnit)
  have hquotient :
      Tendsto (fun n ↦ (u : L) / φ (partialProduct n : E)) atTop
        (nhds ((u : L) / φ x)) :=
    tendsto_const_nhds.div ((hφ.tendsto x).comp hx) hφx0
  have hresidual_eq :
      (fun n ↦ ((residual n).1 : L)) =
        fun n ↦ (u : L) / φ (partialProduct n : E) := by
    funext n
    simpa only [Units.val_div_eq_div_val, Units.coe_map] using
      congrArg ((↑) : Lˣ → L) (residual_eq n)
  rw [hresidual_eq] at hresidual
  letI : T2Space L := unramified_localField_t2Space L
  have hdiv : (u : L) / φ x = 1 :=
    tendsto_nhds_unique hquotient hresidual
  have hφx : φ x = (u : L) := ((div_eq_one_iff_eq hφx0).1 hdiv).symm
  refine ⟨xUnit, hxUnit_mem, ?_⟩
  apply Units.ext
  change φ (xUnit : E) = (u : L)
  rw [hxUnit]
  exact hφx

section Finite

variable [Module.Finite F K]

noncomputable def integralTrace (x : ringOfIntegers K) : ringOfIntegers F := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  exact Algebra.intTrace (ringOfIntegers F) (ringOfIntegers K) x

noncomputable def integralNorm (x : ringOfIntegers K) : ringOfIntegers F := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  exact Algebra.intNorm (ringOfIntegers F) (ringOfIntegers K) x

@[simp]
theorem coe_integralTrace (x : ringOfIntegers K) :
    (integralTrace F K x : F) = trace F K (x : K) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  change algebraMap (ringOfIntegers F) F
      (Algebra.intTrace (ringOfIntegers F) (ringOfIntegers K) x) =
    Algebra.trace F K (algebraMap (ringOfIntegers K) K x)
  exact Algebra.algebraMap_intTrace
    (A := ringOfIntegers F) (B := ringOfIntegers K) (K := F) (L := K) x

@[simp]
theorem coe_integralNorm (x : ringOfIntegers K) :
    (integralNorm F K x : F) = norm F K (x : K) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  change algebraMap (ringOfIntegers F) F
      (Algebra.intNorm (ringOfIntegers F) (ringOfIntegers K) x) =
    Algebra.norm F (algebraMap (ringOfIntegers K) K x)
  exact Algebra.algebraMap_intNorm
    (A := ringOfIntegers F) (B := ringOfIntegers K) (K := F) (L := K) x

omit [Module.Finite F K] in
theorem unramified_uniformizer
    (hunr : ramificationIndex F K = 1) {π : F}
    (hπ : (ValuativeRel.valuation F).IsUniformizer π) :
    (ValuativeRel.valuation K).IsUniformizer (algebraMap F K π) := by
  rw [← ord_eq_one_iff_isUniformizer K, ord_algebraMap, hunr, one_nsmul,
    ord_uniformizer F hπ]

theorem unramified_residue_degree
    (hunr : ramificationIndex F K = 1) :
    Module.finrank (ResidueField F) (ResidueField K) = Module.finrank F K := by
  rw [← residueDegree_eq_finrank_residueField F K,
    finrank_eq_ramificationIndex_mul_residueDegree F K, hunr, one_mul]

theorem unramified_uniformizer_norm
    (hunr : ramificationIndex F K = 1) {π : F}
    (hπ : (ValuativeRel.valuation F).IsUniformizer π) :
    (ValuativeRel.valuation K).IsUniformizer (algebraMap F K π) ∧
      norm F K (algebraMap F K π) = π ^ Module.finrank F K :=
  ⟨unramified_uniformizer F K hunr hπ, norm_algebraMap F K π⟩

theorem residue_trace (hunr : ramificationIndex F K = 1)
    (x : ringOfIntegers K) :
    residueTrace (ResidueField F) (ResidueField K) (residueMap K x) =
      residueMap F (integralTrace F K x) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : Module.Free (ringOfIntegers F) (ringOfIntegers K) :=
    Module.free_of_finite_type_torsion_free'
  let p := maximalIdeal (ringOfIntegers F)
  let q := maximalIdeal (ringOfIntegers K)
  let pK := Ideal.map (algebraMap (ringOfIntegers F) (ringOfIntegers K)) p
  have hpq : pK = q := unramified_map_maximalIdeal F K hunr
  change Algebra.trace ((ringOfIntegers F) ⧸ p) ((ringOfIntegers K) ⧸ q)
      (Ideal.Quotient.mk q x) = Ideal.Quotient.mk p (integralTrace F K x)
  let e : ((ringOfIntegers K) ⧸ pK) ≃+* ((ringOfIntegers K) ⧸ q) :=
    Ideal.quotEquivOfEq hpq
  have he :
      (algebraMap ((ringOfIntegers F) ⧸ p) ((ringOfIntegers K) ⧸ q)).comp
          (RingEquiv.refl ((ringOfIntegers F) ⧸ p)) =
        e.toRingHom.comp
          (algebraMap ((ringOfIntegers F) ⧸ p) ((ringOfIntegers K) ⧸ pK)) := by
    apply RingHom.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro z
    change Ideal.Quotient.mk q
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) z) =
      e (Ideal.Quotient.mk pK
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) z))
    rw [Ideal.quotEquivOfEq_mk]
  have htransport := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.refl ((ringOfIntegers F) ⧸ p)) e he (Ideal.Quotient.mk pK x)
  rw [Ideal.quotEquivOfEq_mk] at htransport
  calc
    _ = Algebra.trace ((ringOfIntegers F) ⧸ p) ((ringOfIntegers K) ⧸ pK)
        (Ideal.Quotient.mk pK x) := by simpa using htransport.symm
    _ = Ideal.Quotient.mk p
        (Algebra.trace (ringOfIntegers F) (ringOfIntegers K) x) :=
      Algebra.trace_quotient_mk x
    _ = Ideal.Quotient.mk p (integralTrace F K x) := by
      change Ideal.Quotient.mk p
          (Algebra.trace (ringOfIntegers F) (ringOfIntegers K) x) =
        Ideal.Quotient.mk p
          (Algebra.intTrace (ringOfIntegers F) (ringOfIntegers K) x)
      rw [Algebra.intTrace_eq_trace]

theorem residue_norm (hunr : ramificationIndex F K = 1)
    (x : ringOfIntegers K) :
    residueNorm (ResidueField F) (ResidueField K) (residueMap K x) =
      residueMap F (integralNorm F K x) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : Module.Free (ringOfIntegers F) (ringOfIntegers K) :=
    Module.free_of_finite_type_torsion_free'
  let p := maximalIdeal (ringOfIntegers F)
  let q := maximalIdeal (ringOfIntegers K)
  let pK := Ideal.map (algebraMap (ringOfIntegers F) (ringOfIntegers K)) p
  have hpq : pK = q := unramified_map_maximalIdeal F K hunr
  change Algebra.norm ((ringOfIntegers F) ⧸ p)
      (Ideal.Quotient.mk q x) = Ideal.Quotient.mk p (integralNorm F K x)
  let e : ((ringOfIntegers K) ⧸ pK) ≃+* ((ringOfIntegers K) ⧸ q) :=
    Ideal.quotEquivOfEq hpq
  have he :
      (algebraMap ((ringOfIntegers F) ⧸ p) ((ringOfIntegers K) ⧸ q)).comp
          (RingEquiv.refl ((ringOfIntegers F) ⧸ p)) =
        e.toRingHom.comp
          (algebraMap ((ringOfIntegers F) ⧸ p) ((ringOfIntegers K) ⧸ pK)) := by
    apply RingHom.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro z
    change Ideal.Quotient.mk q
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) z) =
      e (Ideal.Quotient.mk pK
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) z))
    rw [Ideal.quotEquivOfEq_mk]
  have htransport := Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl ((ringOfIntegers F) ⧸ p)) e he (Ideal.Quotient.mk pK x)
  rw [Ideal.quotEquivOfEq_mk] at htransport
  calc
    _ = Algebra.norm ((ringOfIntegers F) ⧸ p)
        (Ideal.Quotient.mk pK x) := by simpa using htransport.symm
    _ = Ideal.Quotient.mk p (Algebra.norm (ringOfIntegers F) x) :=
      Algebra.norm_quotient_mk_local x
    _ = Ideal.Quotient.mk p (integralNorm F K x) := by
      change Ideal.Quotient.mk p (Algebra.norm (ringOfIntegers F) x) =
        Ideal.Quotient.mk p
          (Algebra.intNorm (ringOfIntegers F) (ringOfIntegers K) x)
      rw [Algebra.intNorm_eq_norm]

/-- Reduction commutes with both trace and norm in an unramified local-field
extension.  The norm statement is proved for every integral element, hence in
particular for every integral unit as in the manuscript. -/
theorem unramified_residue_trace_norm
    (hunr : ramificationIndex F K = 1) :
    (∀ x : ringOfIntegers K,
      residueTrace (ResidueField F) (ResidueField K) (residueMap K x) =
        residueMap F (integralTrace F K x)) ∧
    (∀ x : ringOfIntegers K,
      residueNorm (ResidueField F) (ResidueField K) (residueMap K x) =
        residueMap F (integralNorm F K x)) :=
  ⟨residue_trace F K hunr, residue_norm F K hunr⟩

private theorem exists_integralTrace_eq_one
    (hunr : ramificationIndex F K = 1) :
    ∃ x : ringOfIntegers K, integralTrace F K x = 1 := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : Module.Free (ringOfIntegers F) (ringOfIntegers K) :=
    Module.free_of_finite_type_torsion_free'
  have hsurj := Algebra.trace_surjective (ResidueField F) (ResidueField K)
  obtain ⟨xbar, hxbar⟩ := hsurj 1
  obtain ⟨x, hx⟩ := residueMap_surjective K xbar
  have hres : residueMap F (integralTrace F K x) = 1 := by
    rw [← residue_trace F K hunr x, hx, hxbar]
  have hunit : IsUnit (integralTrace F K x) :=
    (residue_ne_zero_iff_isUnit (integralTrace F K x)).1 (by simp [hres])
  let t : (ringOfIntegers F)ˣ := hunit.unit
  let y : ringOfIntegers K := (↑(t⁻¹) : ringOfIntegers F) • x
  refine ⟨y, ?_⟩
  change Algebra.intTrace (ringOfIntegers F) (ringOfIntegers K) y = 1
  rw [show y = (↑(t⁻¹) : ringOfIntegers F) • x by rfl, map_smul]
  change (↑(t⁻¹) : ringOfIntegers F) * integralTrace F K x = 1
  rw [← hunit.unit_spec]
  exact Units.inv_mul t

theorem integralTrace_surjective
    (hunr : ramificationIndex F K = 1) :
    Function.Surjective (integralTrace F K) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : Module.Free (ringOfIntegers F) (ringOfIntegers K) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨x, hx⟩ := exists_integralTrace_eq_one F K hunr
  intro y
  refine ⟨y • x, ?_⟩
  change Algebra.intTrace (ringOfIntegers F) (ringOfIntegers K) (y • x) = y
  rw [map_smul]
  change y * integralTrace F K x = y
  rw [hx, mul_one]

theorem trace_mem_lattice
    (hunr : ramificationIndex F K = 1) (a : ℤ) {x : K}
    (hx : x ∈ lattice K a) : trace F K x ∈ lattice F a := by
  obtain ⟨c, hc⟩ := exists_ord_eq F a
  have hc0 : c ≠ 0 := (ord_ne_top_iff F).1 (by rw [hc]; simp)
  have hcK : ord K (algebraMap F K c) = (a : WithTop ℤ) := by
    rw [ord_algebraMap, hunr, one_nsmul, hc]
  let z : K := (algebraMap F K c)⁻¹ * x
  have hz : z ∈ lattice K 0 := by
    rw [mem_lattice]
    dsimp only [z]
    rw [ord_mul, ord_inv, hcK]
    rw [mem_lattice] at hx
    norm_num at hx ⊢
    have h := add_le_add_left hx (-(a : WithTop ℤ))
    simpa [add_assoc, add_comm] using h
  let zO : ringOfIntegers K := ⟨z, (mem_lattice_zero_iff K).1 hz⟩
  have htrz : trace F K z ∈ lattice F 0 := by
    have hzint := (integralTrace F K zO).property
    have hzlat : (integralTrace F K zO : F) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 hzint
    simpa [zO] using hzlat
  have hcLat : c ∈ lattice F a := by rw [mem_lattice, hc]
  have hprod := mul_mem_lattice F hcLat htrz
  have hcx : algebraMap F K c * z = x := by
    simp [z, hc0]
  rw [← hcx, ← Algebra.smul_def, map_smul]
  change c * trace F K z ∈ lattice F a
  simpa only [add_zero] using hprod

theorem trace_lattice_surjective
    (hunr : ramificationIndex F K = 1) (a : ℤ) :
    ∀ y : F, y ∈ lattice F a →
      ∃ x : K, x ∈ lattice K a ∧ trace F K x = y := by
  intro y hy
  obtain ⟨c, hc⟩ := exists_ord_eq F a
  have hc0 : c ≠ 0 := (ord_ne_top_iff F).1 (by rw [hc]; simp)
  have hcK : ord K (algebraMap F K c) = (a : WithTop ℤ) := by
    rw [ord_algebraMap, hunr, one_nsmul, hc]
  let y0 : F := c⁻¹ * y
  have hy0 : y0 ∈ lattice F 0 := by
    rw [mem_lattice]
    dsimp only [y0]
    rw [ord_mul, ord_inv, hc]
    rw [mem_lattice] at hy
    norm_num at hy ⊢
    have h := add_le_add_left hy (-(a : WithTop ℤ))
    simpa [add_assoc, add_comm] using h
  let yO : ringOfIntegers F := ⟨y0, (mem_lattice_zero_iff F).1 hy0⟩
  obtain ⟨zO, hzO⟩ := integralTrace_surjective F K hunr yO
  let x : K := algebraMap F K c * (zO : K)
  refine ⟨x, ?_, ?_⟩
  · change algebraMap F K c * (zO : K) ∈ lattice K a
    have hprod := mul_mem_lattice K
      (show algebraMap F K c ∈ lattice K a by rw [mem_lattice, hcK])
      ((mem_lattice_zero_iff K).2 zO.property)
    simpa only [add_zero] using hprod
  · rw [show x = c • (zO : K) by simp [x, Algebra.smul_def], map_smul]
    change c * trace F K (zO : K) = y
    rw [← coe_integralTrace F K zO, hzO]
    simp [yO, y0, hc0]

theorem unramified_trace_lattice
    (hunr : ramificationIndex F K = 1) (a : ℤ) :
    (∀ x : K, x ∈ lattice K a → trace F K x ∈ lattice F a) ∧
      (∀ y : F, y ∈ lattice F a →
        ∃ x : K, x ∈ lattice K a ∧ trace F K x = y) :=
  ⟨fun _ hx ↦ trace_mem_lattice F K hunr a hx,
    trace_lattice_surjective F K hunr a⟩

theorem unramified_trace_lattice_image
    (hunr : ramificationIndex F K = 1) (a : ℤ) (y : F) :
    y ∈ lattice F a ↔
      ∃ x : K, x ∈ lattice K a ∧ trace F K x = y := by
  constructor
  · exact trace_lattice_surjective F K hunr a y
  · rintro ⟨x, hx, rfl⟩
    exact trace_mem_lattice F K hunr a hx

private theorem norm_one_add_integral_expansion
    (a : ringOfIntegers F) (x : ringOfIntegers K) :
    ∃ r : ringOfIntegers F,
      norm F K (1 + algebraMap F K (a : F) * (x : K)) =
        1 + trace F K (x : K) * (a : F) + (r : F) * (a : F) ^ 2 := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : Module.Free (ringOfIntegers F) (ringOfIntegers K) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a x
  refine ⟨r, ?_⟩
  have hrF := congrArg (fun z : ringOfIntegers F ↦ (z : F)) hr
  rw [← Algebra.intNorm_eq_norm, ← Algebra.intTrace_eq_trace] at hrF
  change (integralNorm F K (1 + a • x) : F) =
    1 + (integralTrace F K x : F) * (a : F) + (r : F) * (a : F) ^ 2 at hrF
  rw [coe_integralNorm, coe_integralTrace] at hrF
  have hcoe : ((1 + a • x : ringOfIntegers K) : K) =
      1 + algebraMap F K (a : F) * (x : K) := by
    have ha : algebraMap (ringOfIntegers K) K
          (algebraMap (ringOfIntegers F) (ringOfIntegers K) a) =
        algebraMap F K (a : F) :=
      Valuation.HasExtension.val_algebraMap
        (vR := ValuativeRel.valuation F) (vA := ValuativeRel.valuation K) a
    change algebraMap (ringOfIntegers K) K (1 + a • x) = _
    rw [map_add, map_one, Algebra.smul_def, map_mul]
    rw [ha]
    rfl
  rw [hcoe] at hrF
  exact hrF

private theorem exists_scaled_integral_of_mem_lattice
    (d : ℕ) {y : F} (hy : y ∈ lattice F (d : ℤ)) :
    ∃ c : F, ord F c = (d : WithTop ℤ) ∧
      ∃ z : ringOfIntegers F, y = c * (z : F) := by
  obtain ⟨c, hc⟩ := exists_ord_eq F (d : ℤ)
  have hc0 : c ≠ 0 := (ord_ne_top_iff F).1 (by rw [hc]; simp)
  let z0 : F := c⁻¹ * y
  have hz0 : z0 ∈ lattice F 0 := by
    rw [mem_lattice]
    dsimp only [z0]
    rw [ord_mul, ord_inv, hc]
    rw [mem_lattice] at hy
    norm_num at hy ⊢
    have h := add_le_add_left hy (-(d : WithTop ℤ))
    simpa [add_assoc, add_comm] using h
  let z : ringOfIntegers F := ⟨z0, (mem_lattice_zero_iff F).1 hz0⟩
  refine ⟨c, hc, z, ?_⟩
  simp [z, z0, hc0]

private theorem unramified_norm_one_step
    (hunr : ramificationIndex F K = 1) (n : ℕ) (u : Fˣ)
    (hu : u ∈ unitFiltration F (n + 1)) :
    ∃ v : Kˣ, v ∈ unitFiltration K (n + 1) ∧
      u / normUnits F K v ∈ unitFiltration F (n + 2) := by
  have hdisp : (u : F) - 1 ∈ lattice F ((n + 1 : ℕ) : ℤ) :=
    (mem_unitFiltration_succ_iff_sub_mem_lattice F n u).1 hu
  obtain ⟨c, hc, y, hy⟩ :=
    exists_scaled_integral_of_mem_lattice F (n + 1) hdisp
  obtain ⟨x, hx⟩ := integralTrace_surjective F K hunr y
  let z : K := algebraMap F K c * (x : K)
  have hcK : ord K (algebraMap F K c) = ((n + 1 : ℕ) : WithTop ℤ) := by
    rw [ord_algebraMap, hunr, one_nsmul, hc]
  have hz : z ∈ lattice K ((n + 1 : ℕ) : ℤ) := by
    change algebraMap F K c * (x : K) ∈ _
    have hprod := mul_mem_lattice K
      (show algebraMap F K c ∈ lattice K ((n + 1 : ℕ) : ℤ) by
        rw [mem_lattice, hcK]
        norm_num)
      ((mem_lattice_zero_iff K).2 x.property)
    simpa only [add_zero] using hprod
  let v : Kˣ := principalUnitOf K n z hz
  have hv : v ∈ unitFiltration K (n + 1) :=
    principalUnitOf_mem K n z hz
  refine ⟨v, hv, ?_⟩
  have hc0 : c ∈ lattice F 0 := by
    rw [mem_lattice, hc]
    exact_mod_cast (show (0 : ℤ) ≤ (n + 1 : ℕ) by omega)
  let cO : ringOfIntegers F := ⟨c, (mem_lattice_zero_iff F).1 hc0⟩
  obtain ⟨r, hr0⟩ := norm_one_add_integral_expansion F K cO x
  have hr : norm F K (1 + algebraMap F K c * (x : K)) =
      1 + trace F K (x : K) * c + (r : F) * c ^ 2 := by
    simpa [cO] using hr0
  have hvcoe : (v : K) = 1 + algebraMap F K c * (x : K) := rfl
  have htr : trace F K (x : K) = (y : F) := by
    rw [← coe_integralTrace F K x, hx]
  have hnorm : norm F K (v : K) =
      1 + (y : F) * c + (r : F) * c ^ 2 := by
    rw [hvcoe, hr, htr]
  have hdiff : (u : F) - norm F K (v : K) = -((r : F) * c ^ 2) := by
    have huval : (u : F) = 1 + c * (y : F) := by
      calc
        (u : F) = ((u : F) - 1) + 1 := by ring
        _ = c * (y : F) + 1 := by rw [hy]
        _ = 1 + c * (y : F) := by ring
    rw [huval, hnorm]
    ring
  have hr0 : (r : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 r.property
  have hcLat : c ∈ lattice F ((n + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, hc]
    exact le_rfl
  have hsq : c ^ 2 ∈ lattice F
      (((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ)) := by
    rw [pow_two]
    exact mul_mem_lattice F hcLat hcLat
  have herr : -((r : F) * c ^ 2) ∈ lattice F ((n + 2 : ℕ) : ℤ) := by
    apply (lattice F ((n + 2 : ℕ) : ℤ)).neg_mem
    apply lattice_antitone F
      (n := ((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ)) (by omega)
    simpa only [zero_add] using mul_mem_lattice F hr0 hsq
  have hun : u ∈ unitGroup F := unitFiltration_le_unitGroup F _ hu
  have hv0 : v ∈ unitGroup K := unitFiltration_le_unitGroup K _ hv
  have hnorm0 : normUnits F K v ∈ unitGroup F := by
    rw [mem_unitGroup_iff_ord_eq_zero]
    change ord F (norm F K (v : K)) = 0
    rw [ord_norm, (mem_unitGroup_iff_ord_eq_zero K v).1 hv0]
    simp
  rw [div_mem_unitFiltration_iff_congruentAtDepth F (n + 2) u
    (normUnits F K v) hun hnorm0]
  rw [CongruentAtDepth]
  change (((n + 2 : ℕ) : ℤ) : WithTop ℤ) ≤
    ord F ((u : F) - norm F K (v : K))
  rw [hdiff]
  exact herr

theorem unramified_norm_unitFiltration_surjective_pos
    (hunr : ramificationIndex F K = 1) {d : ℕ} (hd : 0 < d) :
    ∀ u : Fˣ, u ∈ unitFiltration F d →
      ∃ v : Kˣ, v ∈ unitFiltration K d ∧ normUnits F K v = u := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  apply unramified_successiveLifting_surjective
    (norm F K) (continuous_norm F K) (fun k ↦ n + k) (n + 1)
  · intro a b hab
    exact Nat.add_le_add_left hab n
  · simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  · intro k u hu
    have hu' : u ∈ unitFiltration F ((n + k) + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu
    obtain ⟨v, hv, herr⟩ := unramified_norm_one_step F K hunr (n + k) u hu'
    refine ⟨v, ?_, ?_⟩
    · simpa only [Nat.add_assoc] using hv
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using herr

theorem unramified_norm_mem_unitFiltration
    (hunr : ramificationIndex F K = 1) (m : ℕ) {u : Kˣ}
    (hu : u ∈ unitFiltration K m) :
    normUnits F K u ∈ unitFiltration F m := by
  cases m with
  | zero =>
      rw [mem_unitFiltration_zero, coe_normUnits, ord_norm,
        (mem_unitFiltration_zero K u).1 hu]
      simp
  | succ n =>
      rw [mem_unitFiltration_succ_iff_sub_mem_lattice]
      have hd : (u : K) - 1 ∈ lattice K ((n + 1 : ℕ) : ℤ) :=
        (mem_unitFiltration_succ_iff_sub_mem_lattice K n u).1 hu
      obtain ⟨c, hc⟩ := exists_ord_eq F ((n + 1 : ℕ) : ℤ)
      have hc0 : c ≠ 0 := (ord_ne_top_iff F).1 (by rw [hc]; simp)
      have hcInt : c ∈ lattice F 0 := by
        rw [mem_lattice, hc]
        exact WithTop.coe_nonneg.mpr (Int.natCast_nonneg (n + 1))
      let cO : ringOfIntegers F := ⟨c, (mem_lattice_zero_iff F).1 hcInt⟩
      have hcK : ord K (algebraMap F K c) =
          ((((n + 1 : ℕ) : ℤ) : WithTop ℤ)) := by
        rw [ord_algebraMap, hunr, one_nsmul, hc]
      let z : K := (algebraMap F K c)⁻¹ * ((u : K) - 1)
      have hz : z ∈ lattice K 0 := by
        have hcInv : (algebraMap F K c)⁻¹ ∈
            lattice K (-((n + 1 : ℕ) : ℤ)) := by
          rw [mem_lattice, ord_inv, hcK]
          norm_num
        have hprod := mul_mem_lattice K hcInv hd
        simpa [z] using hprod
      let zO : ringOfIntegers K := ⟨z, (mem_lattice_zero_iff K).1 hz⟩
      obtain ⟨q, hq⟩ := norm_one_add_integral_expansion F K cO zO
      have hcz : algebraMap F K c * (zO : K) = (u : K) - 1 := by
        simp [zO, z, hc0]
      have harg : 1 + algebraMap F K (cO : F) * (zO : K) = (u : K) := by
        rw [show (cO : F) = c by rfl, hcz]
        ring
      have hnormu : norm F K (u : K) =
          1 + trace F K (zO : K) * c + (q : F) * c ^ 2 := by
        rw [← harg]
        simpa only [show (cO : F) = c by rfl] using hq
      have htrace0 : trace F K (zO : K) ∈ lattice F 0 := by
        have hz0 : (integralTrace F K zO : F) ∈ lattice F 0 :=
          (mem_lattice_zero_iff F).2 (integralTrace F K zO).property
        simpa using hz0
      have hcLat : c ∈ lattice F ((n + 1 : ℕ) : ℤ) := by
        rw [mem_lattice, hc]
      have hlinear : trace F K (zO : K) * c ∈
          lattice F ((n + 1 : ℕ) : ℤ) := by
        simpa [add_comm] using mul_mem_lattice F htrace0 hcLat
      have hq0 : (q : F) ∈ lattice F 0 :=
        (mem_lattice_zero_iff F).2 q.property
      have hcSq : c ^ 2 ∈
          lattice F (((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ)) := by
        simpa [pow_two] using mul_mem_lattice F hcLat hcLat
      have hquadraticDeep : (q : F) * c ^ 2 ∈
          lattice F (0 + (((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ))) :=
        mul_mem_lattice F hq0 hcSq
      have hquadratic : (q : F) * c ^ 2 ∈
          lattice F ((n + 1 : ℕ) : ℤ) :=
        lattice_antitone F (by omega) hquadraticDeep
      have hsum :=
        (lattice F ((n + 1 : ℕ) : ℤ)).add_mem hlinear hquadratic
      rw [coe_normUnits, hnormu]
      convert hsum using 1
      ring

noncomputable def unramifiedNormUnitGroup : unitGroup K →* unitGroup F :=
  (normUnits F K).comp (unitGroup K).subtype |>.codRestrict (unitGroup F) (by
    intro u
    rw [mem_unitGroup_iff_ord_eq_zero]
    change ord F (norm F K ((u : Kˣ) : K)) = 0
    rw [ord_norm, (mem_unitGroup_iff_ord_eq_zero K u).1 u.property]
    simp)

@[simp]
theorem coe_unramifiedNormUnitGroup (u : unitGroup K) :
    ((unramifiedNormUnitGroup F K u : unitGroup F) : Fˣ) =
      normUnits F K (u : Kˣ) := rfl

theorem unramified_residue_norm_units
    (hunr : ramificationIndex F K = 1) (u : unitGroup K) :
    residueUnits F (unramifiedNormUnitGroup F K u) =
      Units.map (residueNorm (ResidueField F) (ResidueField K))
        (residueUnits K u) := by
  apply Units.ext
  rw [residueUnits_coe]
  change residueMap F
      (unitGroupMulEquivRingOfIntegers F (unramifiedNormUnitGroup F K u)) =
    residueNorm (ResidueField F) (ResidueField K)
      (residueMap K (unitGroupMulEquivRingOfIntegers K u))
  rw [residue_norm F K hunr]
  congr 1
  apply Subtype.ext
  rw [coe_integralNorm]
  rfl

theorem unramified_norm_unitFiltration_zero_surjective
    (hunr : ramificationIndex F K = 1) :
    ∀ u : Fˣ, u ∈ unitFiltration F 0 →
      ∃ x : Kˣ, x ∈ unitFiltration K 0 ∧ normUnits F K x = u := by
  intro u hu
  let u₀ : unitGroup F := ⟨u, by simpa using hu⟩
  obtain ⟨bbar, hbbar⟩ := FiniteField.unitsMap_norm_surjective
    (ResidueField F) (ResidueField K) (residueUnits F u₀)
  obtain ⟨b₀, hb₀⟩ := residueUnits_surjective K bbar
  let e₀ : unitGroup F := u₀ / unramifiedNormUnitGroup F K b₀
  have heker : e₀ ∈ (residueUnits F).ker := by
    rw [MonoidHom.mem_ker]
    rw [map_div, unramified_residue_norm_units F K hunr, hb₀, hbbar]
    simp
  rw [residueUnits_ker] at heker
  have he : (e₀ : Fˣ) ∈ unitFiltration F 1 :=
    (mem_unitFiltrationInside F (show 0 ≤ 1 by omega) e₀).1 heker
  obtain ⟨c, hc, hnc⟩ :=
    unramified_norm_unitFiltration_surjective_pos F K hunr (by omega) (e₀ : Fˣ) he
  refine ⟨(b₀ : Kˣ) * c, ?_, ?_⟩
  · apply (unitFiltration K 0).mul_mem
    · exact b₀.property
    · exact unitFiltration_antitone K (show 0 ≤ 1 by omega) hc
  · rw [map_mul, hnc]
    change normUnits F K (b₀ : Kˣ) * (e₀ : Fˣ) = u
    rw [show (e₀ : Fˣ) =
      (u₀ : Fˣ) / normUnits F K (b₀ : Kˣ) by rfl]
    simp
    rfl

theorem unramified_norm_unitFiltration
    (hunr : ramificationIndex F K = 1) (m : ℕ) :
    (∀ x : Kˣ, x ∈ unitFiltration K m →
      normUnits F K x ∈ unitFiltration F m) ∧
    (∀ u : Fˣ, u ∈ unitFiltration F m →
      ∃ x : Kˣ, x ∈ unitFiltration K m ∧ normUnits F K x = u) := by
  refine ⟨fun _ hx ↦ unramified_norm_mem_unitFiltration F K hunr m hx, ?_⟩
  cases m with
  | zero => exact unramified_norm_unitFiltration_zero_surjective F K hunr
  | succ n =>
      exact unramified_norm_unitFiltration_surjective_pos F K hunr (by omega)

theorem unramified_norm_unitFiltration_image
    (hunr : ramificationIndex F K = 1) (m : ℕ) (u : Fˣ) :
    u ∈ unitFiltration F m ↔
      ∃ x : Kˣ, x ∈ unitFiltration K m ∧ normUnits F K x = u := by
  constructor
  · exact (unramified_norm_unitFiltration F K hunr m).2 u
  · rintro ⟨x, hx, rfl⟩
    exact (unramified_norm_unitFiltration F K hunr m).1 x hx

theorem unramified_addCharTrivialOnLattice_iff
    (hunr : ramificationIndex F K = 1) (ψ : ContinuousAddChar F) (a : ℤ) :
    AddCharTrivialOnLattice K ψ.compTrace a ↔
      AddCharTrivialOnLattice F ψ a := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ :=
      trace_lattice_surjective F K hunr a y hy
    simpa [hxy] using h x hx
  · intro h x hx
    rw [ContinuousAddChar.compTrace_apply]
    exact h _ (trace_mem_lattice F K hunr a hx)

theorem unramified_quasiCharTrivialOnUnitFiltration_iff
    (hunr : ramificationIndex F K = 1)
    (χ : ContinuousQuasiChar F) (m : ℕ) :
    QuasiCharTrivialOnUnitFiltration K χ.compNorm m ↔
      QuasiCharTrivialOnUnitFiltration F χ m := by
  constructor
  · intro h u hu
    obtain ⟨x, hx, hxu⟩ :=
      (unramified_norm_unitFiltration F K hunr m).2 u hu
    simpa [hxu] using h x hx
  · intro h x hx
    rw [ContinuousQuasiChar.compNorm_apply]
    exact h _ ((unramified_norm_unitFiltration F K hunr m).1 x hx)

theorem unramified_additiveConductor_compTrace
    (hunr : ramificationIndex F K = 1)
    (ψ : ContinuousAddChar F) (n : ℤ) :
    IsAdditiveConductor K ψ.compTrace n ↔ IsAdditiveConductor F ψ n := by
  constructor
  · intro h
    refine ⟨(unramified_addCharTrivialOnLattice_iff F K hunr ψ (-n)).1
      h.trivial, ?_⟩
    intro r hr
    exact h.minimal r
      ((unramified_addCharTrivialOnLattice_iff F K hunr ψ r).2 hr)
  · intro h
    refine ⟨(unramified_addCharTrivialOnLattice_iff F K hunr ψ (-n)).2
      h.trivial, ?_⟩
    intro r hr
    exact h.minimal r
      ((unramified_addCharTrivialOnLattice_iff F K hunr ψ r).1 hr)

theorem unramified_multiplicativeConductor_compNorm
    (hunr : ramificationIndex F K = 1)
    (χ : ContinuousQuasiChar F) (m : ℕ) :
    IsMultiplicativeConductor K χ.compNorm m ↔
      IsMultiplicativeConductor F χ m := by
  constructor
  · intro h
    refine ⟨(unramified_quasiCharTrivialOnUnitFiltration_iff F K hunr χ m).1
      h.trivial, ?_⟩
    intro r hr
    exact h.minimal r
      ((unramified_quasiCharTrivialOnUnitFiltration_iff F K hunr χ r).2 hr)
  · intro h
    refine ⟨(unramified_quasiCharTrivialOnUnitFiltration_iff F K hunr χ m).2
      h.trivial, ?_⟩
    intro r hr
    exact h.minimal r
      ((unramified_quasiCharTrivialOnUnitFiltration_iff F K hunr χ r).1 hr)

private theorem unramified_residueDegree_eq_finrank
    (hunr : ramificationIndex F K = 1) :
    residueDegree F K = Module.finrank F K := by
  rw [finrank_eq_ramificationIndex_mul_residueDegree F K, hunr, one_mul]

private theorem norm_range_le_orderMod_kernel
    :
    (normUnits F K).range ≤
      (localUnitOrderMod F (residueDegree F K)).ker := by
  rintro y ⟨x, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Multiplicative.toAdd.injective
  rw [localUnitOrderMod_apply]
  change (localUnitOrder F (normUnits F K x) : ZMod (residueDegree F K)) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨localUnitOrder K x, ?_⟩
  apply WithTop.coe_injective
  rw [coe_localUnitOrder]
  change ord F (norm F K (x : K)) =
    (((residueDegree F K : ℤ) * localUnitOrder K x : ℤ) : WithTop ℤ)
  rw [ord_norm, ← coe_localUnitOrder, ← WithTop.coe_nsmul]
  congr 1

private theorem orderMod_kernel_le_norm_range
    (hunr : ramificationIndex F K = 1) :
    (localUnitOrderMod F (residueDegree F K)).ker ≤
      (normUnits F K).range := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hycast : (localUnitOrder F y : ZMod (residueDegree F K)) = 0 := by
    have h := congrArg Multiplicative.toAdd hy
    simpa using h
  have hydiv : (residueDegree F K : ℤ) ∣ localUnitOrder F y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hycast
  obtain ⟨a, ha⟩ := hydiv
  obtain ⟨π₀, hπ₀irr⟩ :=
    IsDiscreteValuationRing.exists_irreducible (ringOfIntegers F)
  have hπspan : maximalIdeal (ringOfIntegers F) = Ideal.span {π₀} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π₀).mp hπ₀irr
  have hπunif : (ValuativeRel.valuation F).IsUniformizer (π₀ : F) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact hπspan
  have hπ0 : (π₀ : F) ≠ 0 := by
    intro h
    exact hπ₀irr.ne_zero (Subtype.ext h)
  let π : Fˣ := Units.mk0 (π₀ : F) hπ0
  have hπord : localUnitOrder F π = 1 := by
    apply WithTop.coe_injective
    rw [coe_localUnitOrder]
    exact ord_uniformizer F hπunif
  let u : Fˣ := y / π ^ ((residueDegree F K : ℤ) * a)
  have huord : localUnitOrder F u = 0 := by
    change localUnitOrder F (y / π ^ ((residueDegree F K : ℤ) * a)) = 0
    have hmap := congrArg Multiplicative.toAdd
      (map_div (localUnitOrderHom F) y
        (π ^ ((residueDegree F K : ℤ) * a)))
    change localUnitOrder F (y / π ^ ((residueDegree F K : ℤ) * a)) =
      localUnitOrder F y -
        localUnitOrder F (π ^ ((residueDegree F K : ℤ) * a)) at hmap
    have hz := congrArg Multiplicative.toAdd
      ((localUnitOrderHom F).map_zpow π ((residueDegree F K : ℤ) * a))
    change localUnitOrder F (π ^ ((residueDegree F K : ℤ) * a)) =
      ((residueDegree F K : ℤ) * a) * localUnitOrder F π at hz
    rw [hmap, hz, hπord]
    simp only [mul_one]
    omega
  have hu : u ∈ unitFiltration F 0 := by
    rw [mem_unitFiltration_zero, ← coe_localUnitOrder]
    simp [huord]
  obtain ⟨v, -, hv⟩ :=
    unramified_norm_unitFiltration_zero_surjective F K hunr u hu
  have hdegree : Module.finrank F K = residueDegree F K := by
    rw [finrank_eq_ramificationIndex_mul_residueDegree, hunr, one_mul]
  have hnormbase (w : Fˣ) :
      normUnits F K (Units.map (algebraMap F K) w) =
        w ^ Module.finrank F K := by
    apply Units.ext
    change norm F K (algebraMap F K (w : F)) =
      ((w ^ Module.finrank F K : Fˣ) : F)
    rw [norm_algebraMap]
    rfl
  refine ⟨Units.map (algebraMap F K) (π ^ a) * v, ?_⟩
  rw [map_mul, hnormbase, hdegree, hv]
  change (π ^ a) ^ residueDegree F K * u = y
  rw [← zpow_natCast, ← zpow_mul]
  change π ^ (a * (residueDegree F K : ℤ)) *
      (y / π ^ ((residueDegree F K : ℤ) * a)) = y
  rw [mul_comm a (residueDegree F K : ℤ)]
  simp

theorem unramified_orderMod_kernel_eq_norm_range
    (hunr : ramificationIndex F K = 1) :
    (localUnitOrderMod F (residueDegree F K)).ker =
      (normUnits F K).range :=
  le_antisymm (orderMod_kernel_le_norm_range F K hunr)
    (norm_range_le_orderMod_kernel F K)

theorem mem_unramified_norm_range_iff_order_dvd
    (hunr : ramificationIndex F K = 1) (u : Fˣ) :
    u ∈ (normUnits F K).range ↔
      (residueDegree F K : ℤ) ∣ localUnitOrder F u := by
  rw [← unramified_orderMod_kernel_eq_norm_range F K hunr,
    MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    rw [localUnitOrderMod_apply] at h'
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
  · intro h
    apply Multiplicative.toAdd.injective
    rw [localUnitOrderMod_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h

theorem mem_unramified_norm_range_iff_uniformizer
    (hunr : ramificationIndex F K = 1) (π : Fˣ)
    (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F)) (u : Fˣ) :
    u ∈ (normUnits F K).range ↔
      ∃ a : ℤ, ∃ ε : Fˣ, ε ∈ unitFiltration F 0 ∧
        u = π ^ ((residueDegree F K : ℤ) * a) * ε := by
  have hπord : localUnitOrder F π = 1 := by
    apply WithTop.coe_injective
    rw [coe_localUnitOrder, ord_uniformizer F hπ]
    norm_num
  constructor
  · intro hu
    obtain ⟨a, ha⟩ :=
      (mem_unramified_norm_range_iff_order_dvd F K hunr u).1 hu
    let ε : Fˣ := u / π ^ ((residueDegree F K : ℤ) * a)
    have hεord : localUnitOrder F ε = 0 := by
      change localUnitOrder F
        (u / π ^ ((residueDegree F K : ℤ) * a)) = 0
      have hmap := congrArg Multiplicative.toAdd
        (map_div (localUnitOrderHom F) u
          (π ^ ((residueDegree F K : ℤ) * a)))
      change localUnitOrder F
          (u / π ^ ((residueDegree F K : ℤ) * a)) =
        localUnitOrder F u -
          localUnitOrder F (π ^ ((residueDegree F K : ℤ) * a)) at hmap
      have hz := congrArg Multiplicative.toAdd
        ((localUnitOrderHom F).map_zpow π ((residueDegree F K : ℤ) * a))
      change localUnitOrder F (π ^ ((residueDegree F K : ℤ) * a)) =
        ((residueDegree F K : ℤ) * a) * localUnitOrder F π at hz
      rw [hmap, hz, hπord]
      simp only [mul_one]
      omega
    have hε : ε ∈ unitFiltration F 0 := by
      rw [mem_unitFiltration_zero, ← coe_localUnitOrder]
      simp [hεord]
    refine ⟨a, ε, hε, ?_⟩
    simp [ε]
  · rintro ⟨a, ε, hε, rfl⟩
    apply (mem_unramified_norm_range_iff_order_dvd F K hunr _).2
    refine ⟨a, ?_⟩
    have hεord : localUnitOrder F ε = 0 := by
      apply WithTop.coe_injective
      rw [coe_localUnitOrder]
      exact (mem_unitFiltration_zero F ε).1 hε
    have hmul := congrArg Multiplicative.toAdd
      ((localUnitOrderHom F).map_mul
        (π ^ ((residueDegree F K : ℤ) * a)) ε)
    change localUnitOrder F
        (π ^ ((residueDegree F K : ℤ) * a) * ε) =
      localUnitOrder F (π ^ ((residueDegree F K : ℤ) * a)) +
        localUnitOrder F ε at hmul
    have hz := congrArg Multiplicative.toAdd
      ((localUnitOrderHom F).map_zpow π ((residueDegree F K : ℤ) * a))
    change localUnitOrder F (π ^ ((residueDegree F K : ℤ) * a)) =
      ((residueDegree F K : ℤ) * a) * localUnitOrder F π at hz
    rw [hmul, hz, hπord, hεord]
    ring

/-- The norm quotient in an unramified extension, explicitly identified with the
cyclic group of normalized orders modulo the residue degree. -/
noncomputable def unramifiedNormQuotientEquiv
    (hunr : ramificationIndex F K = 1) :
    Fˣ ⧸ (normUnits F K).range ≃* Multiplicative (ZMod (residueDegree F K)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (unramified_orderMod_kernel_eq_norm_range F K hunr).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (localUnitOrderMod F (residueDegree F K))
      (localUnitOrderMod_surjective F (residueDegree F K)))

@[simp]
theorem unramifiedNormQuotientEquiv_mk
    (hunr : ramificationIndex F K = 1) (x : Fˣ) :
    unramifiedNormQuotientEquiv F K hunr (QuotientGroup.mk x) =
      localUnitOrderMod F (residueDegree F K) x := by
  simp [unramifiedNormQuotientEquiv,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse]

theorem unramifiedNormQuotient_natCard
    (hunr : ramificationIndex F K = 1) :
    Nat.card (Fˣ ⧸ (normUnits F K).range) = Module.finrank F K := by
  rw [← unramified_residueDegree_eq_finrank F K hunr,
    ← Nat.card_zmod (residueDegree F K)]
  exact Nat.card_congr (unramifiedNormQuotientEquiv F K hunr).toEquiv

theorem unramifiedNormQuotient_isCyclic
    (hunr : ramificationIndex F K = 1) :
    IsCyclic (Fˣ ⧸ (normUnits F K).range) := by
  exact (unramifiedNormQuotientEquiv F K hunr).isCyclic.mpr inferInstance

theorem unramifiedNormQuotientEquiv_uniformizer
    (hunr : ramificationIndex F K = 1) (π : Fˣ)
    (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F)) :
    unramifiedNormQuotientEquiv F K hunr (QuotientGroup.mk π) =
      Multiplicative.ofAdd (1 : ZMod (residueDegree F K)) := by
  rw [unramifiedNormQuotientEquiv_mk]
  apply Multiplicative.toAdd.injective
  rw [localUnitOrderMod_apply]
  change (localUnitOrder F π : ZMod (residueDegree F K)) = 1
  have hord : localUnitOrder F π = 1 := by
    apply WithTop.coe_injective
    rw [coe_localUnitOrder, ord_uniformizer F hπ]
    norm_num
  rw [hord]
  norm_num

theorem unramifiedNormQuotient_uniformizer_generates
    (hunr : ramificationIndex F K = 1) (π : Fˣ)
    (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F)) :
    Subgroup.zpowers (QuotientGroup.mk π :
      Fˣ ⧸ (normUnits F K).range) = ⊤ := by
  apply top_unique
  intro q _
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective
    (Multiplicative.toAdd (unramifiedNormQuotientEquiv F K hunr q))
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨a, (unramifiedNormQuotientEquiv F K hunr).injective ?_⟩
  rw [map_zpow, unramifiedNormQuotientEquiv_uniformizer F K hunr π hπ]
  apply Multiplicative.toAdd.injective
  simpa using ha

end Finite

end

end LanglandsFirstMainLemma
