import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.UnitFiltration

/-!
# Successive lifting in complete unit filtrations

This file isolates the completeness argument used when surjectivity on successive unit-graded
pieces is upgraded to exact surjectivity on a positive-depth unit group.  Corrections are chosen
one layer at a time.  Their partial products are Cauchy because their source depths tend to
infinity; completeness of the source local field supplies a limit, and continuity identifies its
image with the prescribed target unit.
-/

namespace LanglandsFirstMainLemma

open Filter Topology

private theorem isOpen_lattice
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) :
    IsOpen (lattice F n : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hopen := (ValuativeRel.valuation F).isOpen_closedBall
    (r := (ValuativeRel.valuation F).restrict a) (by simp [ha0])
  convert hopen using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    (ValuativeRel.valuation F).restrict_le_iff]

private theorem isClosed_lattice
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) :
    IsClosed (lattice F n : Set F) := by
  exact AddSubgroup.isClosed_of_isOpen (lattice F n).toAddSubgroup
    (by simpa using isOpen_lattice F n)

private theorem localField_t2Space
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : T2Space F := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hx)
  refine ⟨(lattice F (k + 1) : Set F),
    (isOpen_lattice F (k + 1)).mem_nhds (by simp), ?_⟩
  intro hmem
  rw [SetLike.mem_coe, mem_lattice, ← hk, WithTop.coe_le_coe] at hmem
  omega

/-- The integer-indexed valuation lattices form a neighborhood basis of zero. -/
private theorem lattice_hasBasis_nhds_zero
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    (nhds (0 : F)).HasBasis (fun _ : ℤ ↦ True) fun n ↦ (lattice F n : Set F) := by
  rw [Filter.hasBasis_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValuativeRel.ValueGroupWithZero F)
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact Units.ne_zero γ ha.symm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 ha0)
    refine ⟨k + 1, trivial, fun x hx ↦ hγ ?_⟩
    change ValuativeRel.valuation F x < (γ : ValuativeRel.ValueGroupWithZero F)
    rw [← ha]
    have hax : ord F a < ord F x := by
      rw [← hk]
      exact (WithTop.coe_lt_coe.mpr (show k < k + 1 by omega)).trans_le hx
    have hv : x <ᵥ a := (ord_lt_ord_iff F a x).1 hax
    rw [lt_iff_not_ge, ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation F)]
    exact hv
  · rintro ⟨n, -, hns⟩
    exact Filter.mem_of_superset ((isOpen_lattice F n).mem_nhds (by simp)) hns

/-- Elements whose lattice depths tend to infinity converge to zero. -/
private theorem tendsto_zero_of_mem_lattice
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {d : ℕ → ℕ} (hd : Tendsto d atTop atTop) {x : ℕ → F}
    (hx : ∀ n, x n ∈ lattice F (d n : ℤ)) :
    Tendsto x atTop (nhds 0) := by
  rw [(lattice_hasBasis_nhds_zero F).tendsto_right_iff]
  intro r _
  cases r with
  | ofNat r =>
      filter_upwards [(tendsto_atTop.1 hd r)] with n hn
      exact lattice_antitone F (Int.ofNat_le.2 hn) (hx n)
  | negSucc r =>
      filter_upwards [(tendsto_atTop.1 hd 0)] with n _
      exact lattice_antitone F (by omega) (hx n)

/-- A sequence of units lying in layers whose depths tend to infinity converges to one. -/
private theorem tendsto_one_of_mem_unitFiltration
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {d : ℕ → ℕ} (hd : Tendsto d atTop atTop) {u : ℕ → Fˣ}
    (hu : ∀ n, u n ∈ unitFiltration F (d n + 1)) :
    Tendsto (fun n ↦ (u n : F)) atTop (nhds 1) := by
  have hsub : Tendsto (fun n ↦ (u n : F) - 1) atTop (nhds 0) := by
    apply tendsto_zero_of_mem_lattice F hd
    intro n
    have hdeep :=
      (mem_unitFiltration_succ_iff_sub_mem_lattice F (d n) (u n)).1 (hu n)
    exact lattice_antitone F (by omega) hdeep
  convert hsub.const_add 1 using 1 <;> simp

/--
Successive filtered lifting for local-field units.

Let `φ : E →* F` be continuous, let `sourceDepth` be monotone and tend to infinity, and fix
`targetDepth`.  Suppose that for every `n`, each element of `U_F^(targetDepth + n)` can be
corrected by the image of an element of `U_E^(sourceDepth n + 1)`, leaving an error in
`U_F^(targetDepth + n + 1)`.  Then every element of `U_F^targetDepth` is exactly the image of an
element of `U_E^(sourceDepth 0 + 1)`.
-/
theorem successiveLifting_surjective
    {E F : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (φ : E →* F) (hφ : Continuous φ)
    (sourceDepth : ℕ → ℕ) (targetDepth : ℕ)
    (hsource_mono : Monotone sourceDepth)
    (hsource_tendsto : Tendsto sourceDepth atTop atTop)
    (hlift : ∀ (n : ℕ) (u : Fˣ),
      u ∈ unitFiltration F (targetDepth + n) →
        ∃ x : Eˣ, x ∈ unitFiltration E (sourceDepth n + 1) ∧
          u / Units.map φ x ∈ unitFiltration F (targetDepth + n + 1)) :
    ∀ u : Fˣ, u ∈ unitFiltration F targetDepth →
      ∃ x : Eˣ, x ∈ unitFiltration E (sourceDepth 0 + 1) ∧ Units.map φ x = u := by
  classical
  intro u hu
  let lift : ∀ (n : ℕ) (v : unitFiltration F (targetDepth + n)),
      Σ x : unitFiltration E (sourceDepth n + 1),
        { w : unitFiltration F (targetDepth + (n + 1)) //
          (w : Fˣ) = (v : Fˣ) / Units.map φ (x : Eˣ) } := fun n v ↦ by
    let hex := hlift n (v : Fˣ) v.property
    let x : Eˣ := Classical.choose hex
    have hx : x ∈ unitFiltration E (sourceDepth n + 1) := (Classical.choose_spec hex).1
    have herror :
        (v : Fˣ) / Units.map φ x ∈ unitFiltration F (targetDepth + n + 1) :=
      (Classical.choose_spec hex).2
    let x' : unitFiltration E (sourceDepth n + 1) := ⟨x, hx⟩
    let w : Fˣ := (v : Fˣ) / Units.map φ x
    have hw : w ∈ unitFiltration F (targetDepth + (n + 1)) := by
      simpa only [Nat.add_assoc] using herror
    exact ⟨x', ⟨⟨w, hw⟩, rfl⟩⟩
  let residual : (n : ℕ) → unitFiltration F (targetDepth + n) := fun n ↦
    Nat.rec (motive := fun k ↦ unitFiltration F (targetDepth + k))
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
      (Nat.add_le_add_right (hsource_mono (Nat.zero_le i)) 1) (correction i).property
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
      have hdeep := (mem_unitFiltration_succ_iff_sub_mem_lattice E (sourceDepth n)
        (correction n).1).1 (correction n).property
      exact lattice_antitone E (by omega) hdeep
    rw [partialProduct_succ]
    change (partialProduct n : E) * ((correction n).1 : E) - (partialProduct n : E) ∈ _
    rw [show (partialProduct n : E) * ((correction n).1 : E) - (partialProduct n : E) =
      (partialProduct n : E) * (((correction n).1 : E) - 1) by ring]
    simpa only [zero_add] using mul_mem_lattice E hp0 hc
  letI : NonarchimedeanAddGroup E :=
    { toIsTopologicalAddGroup := inferInstance
      is_nonarchimedean := by
        intro V hV
        obtain ⟨n, -, hn⟩ := (lattice_hasBasis_nhds_zero E).mem_iff.mp hV
        let W : OpenAddSubgroup E :=
          { toAddSubgroup := (lattice E n).toAddSubgroup
            isOpen' := by simpa using isOpen_lattice E n }
        exact ⟨W, hn⟩ }
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have partialProduct_cauchy : CauchySeq (fun n ↦ (partialProduct n : E)) := by
    apply NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero
    exact tendsto_zero_of_mem_lattice E hsource_tendsto increment_mem
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete partialProduct_cauchy
  have hx_mem : x - 1 ∈ lattice E ((sourceDepth 0 + 1 : ℕ) : ℤ) := by
    apply (isClosed_lattice E _).mem_of_tendsto (hx.sub tendsto_const_nhds)
    exact Filter.Eventually.of_forall fun n ↦
      (mem_unitFiltration_succ_iff_sub_mem_lattice E (sourceDepth 0) (partialProduct n)).1
        (partialProduct_mem n)
  let xUnit : Eˣ := principalUnitOf E (sourceDepth 0) (x - 1) hx_mem
  have hxUnit : (xUnit : E) = x := by
    simp [xUnit]
  have hxUnit_mem : xUnit ∈ unitFiltration E (sourceDepth 0 + 1) :=
    principalUnitOf_mem E (sourceDepth 0) (x - 1) hx_mem
  have hresidual : Tendsto (fun n ↦ ((residual n).1 : F)) atTop (nhds 1) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    apply tendsto_one_of_mem_unitFiltration F tendsto_id
    intro n
    apply unitFiltration_antitone F (show n + 1 ≤ targetDepth + (n + 1) by omega)
    exact (residual (n + 1)).property
  have hφx0 : φ x ≠ 0 := by
    rw [← hxUnit]
    exact Units.ne_zero (Units.map φ xUnit)
  have hquotient :
      Tendsto (fun n ↦ (u : F) / φ (partialProduct n : E)) atTop
        (nhds ((u : F) / φ x)) :=
    tendsto_const_nhds.div ((hφ.tendsto x).comp hx) hφx0
  have hresidual_eq :
      (fun n ↦ ((residual n).1 : F)) = fun n ↦ (u : F) / φ (partialProduct n : E) := by
    funext n
    simpa only [Units.val_div_eq_div_val, Units.coe_map] using
      congrArg ((↑) : Fˣ → F) (residual_eq n)
  rw [hresidual_eq] at hresidual
  letI : T2Space F := localField_t2Space F
  have hdiv : (u : F) / φ x = 1 := tendsto_nhds_unique hquotient hresidual
  have hφx : φ x = (u : F) := ((div_eq_one_iff_eq hφx0).1 hdiv).symm
  refine ⟨xUnit, hxUnit_mem, ?_⟩
  apply Units.ext
  change φ (xUnit : E) = (u : F)
  rw [hxUnit]
  exact hφx

end LanglandsFirstMainLemma
