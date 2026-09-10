import LanglandsFirstMainLemma.LocalField.UnitFiltration
import LanglandsFirstMainLemma.LocalField.ResidueField
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Finite quotients of local-field lattices and unit filtrations

This file supplies the finite quotient interfaces used by the finite definition of `Delta` and
by Lamprecht stationary phase.  Public definitions work directly with quotient classes: no
representative is selected.  Existence choices occur only inside proofs of finiteness and
cardinality.
-/

namespace LanglandsFirstMainLemma

section Finiteness

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem isOpen_lattice (n : ℤ) :
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

private theorem isCompact_lattice (n : ℤ) :
    IsCompact (lattice F n : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have hcompact := IsNonarchimedeanLocalField.isCompact_closedBall F
    (ValuativeRel.valuation F a)
  convert hcompact using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)]

private theorem mem_maximalIdeal_pow_iff_mem_lattice (k : ℕ)
    (x : ringOfIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) ^ k ↔
      (x : F) ∈ lattice F (k : ℤ) := by
  obtain ⟨π, hπ⟩ := exists_ord_eq F 1
  have hπ0 : π ≠ 0 := (ord_ne_top_iff F).1 (by simp [hπ])
  have hπint : π ∈ ringOfIntegers F :=
    (mem_lattice_zero_iff F).1 (by rw [mem_lattice, hπ]; simp)
  let π₀ : ringOfIntegers F := ⟨π, hπint⟩
  have hπu : (ValuativeRel.valuation F).IsUniformizer (π₀ : F) :=
    (ord_eq_one_iff_isUniformizer F π).1 hπ
  have hmax : IsLocalRing.maximalIdeal (ringOfIntegers F) = Ideal.span {π₀} :=
    hπu.is_generator
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : (y : F) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 y.property
    have hpow : (π₀ : F) ^ k ∈ lattice F (k : ℤ) := by
      rw [mem_lattice, ord_pow, hπ]
      simp
    rw [hy]
    simpa [add_comm, mul_comm] using mul_mem_lattice F hy0 hpow
  · intro hx
    have hπuz : (ValuativeRel.valuation F).IsUniformizer π := hπu
    rw [lattice_eq_uniformizer_zpow_smul F hπuz (k : ℤ)] at hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    let y₀ : ringOfIntegers F := ⟨y, (mem_lattice_zero_iff F).1 hy⟩
    refine ⟨y₀, ?_⟩
    apply Subtype.ext
    simpa [π₀, y₀, smul_eq_mul, mul_comm] using hxy.symm

private noncomputable def latticeScalingEquiv {m : ℤ} (a : F)
    (ha : ord F a = (m : WithTop ℤ)) :
    ringOfIntegers F ≃ₗ[ringOfIntegers F] lattice F m where
  toFun x := ⟨a * (x : F), by
    have haMem : a ∈ lattice F m := by rw [mem_lattice, ha]
    simpa using mul_mem_lattice F haMem ((mem_lattice_zero_iff F).2 x.property)⟩
  invFun x := ⟨a⁻¹ * (x : F), (mem_lattice_zero_iff F).1 (by
    have haInv : a⁻¹ ∈ lattice F (-m) := by
      rw [mem_lattice, ord_inv, ha]
      norm_num
    simpa using mul_mem_lattice F haInv x.property)⟩
  left_inv x := by
    apply Subtype.ext
    change a⁻¹ * (a * (x : F)) = (x : F)
    have ha0 : a ≠ 0 := (ord_ne_top_iff F).1 (by rw [ha]; simp)
    simp [ha0]
  right_inv x := by
    apply Subtype.ext
    change a * (a⁻¹ * (x : F)) = (x : F)
    have ha0 : a ≠ 0 := (ord_ne_top_iff F).1 (by rw [ha]; simp)
    simp [ha0]
  map_add' x y := by
    apply Subtype.ext
    change a * ((x : F) + (y : F)) = a * (x : F) + a * (y : F)
    ring
  map_smul' c x := by
    apply Subtype.ext
    change a * ((c : F) * (x : F)) = (c : F) * (a * (x : F))
    ring

private theorem map_maximalIdeal_pow_latticeScalingEquiv {m n : ℤ} (h : m ≤ n)
    (a : F) (ha : ord F a = (m : WithTop ℤ)) :
    Submodule.map
        (latticeScalingEquiv F a ha :
          ringOfIntegers F →ₗ[ringOfIntegers F] lattice F m)
        (IsLocalRing.maximalIdeal (ringOfIntegers F) ^ (n - m).toNat) =
      latticeInside F h := by
  ext x
  rw [Submodule.mem_map_equiv, mem_maximalIdeal_pow_iff_mem_lattice F,
    mem_latticeInside]
  have hcast : ((n - m).toNat : ℤ) = n - m := by omega
  rw [mem_lattice, mem_lattice, hcast]
  change ((n - m : ℤ) : WithTop ℤ) ≤ ord F (a⁻¹ * (x : F)) ↔
    (n : WithTop ℤ) ≤ ord F (x : F)
  rw [ord_mul, ord_inv, ha]
  norm_num
  constructor <;> intro hx
  · have := add_le_add_left hx (m : WithTop ℤ)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  · have := add_le_add_left hx (-(m : WithTop ℤ))
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this

private noncomputable def latticeQuotientEquivMaximalIdealPow {m n : ℤ}
    (h : m ≤ n) :
    (ringOfIntegers F ⧸
        IsLocalRing.maximalIdeal (ringOfIntegers F) ^ (n - m).toNat)
      ≃ₗ[ringOfIntegers F] LatticeQuotient F m n h := by
  let a := Classical.choose (exists_ord_eq F m)
  have ha := Classical.choose_spec (exists_ord_eq F m)
  exact Submodule.Quotient.equiv _ _ (latticeScalingEquiv F a ha)
    (map_maximalIdeal_pow_latticeScalingEquiv F h a ha)

/-- Every certified lattice quotient `𝖭_F^m / 𝖭_F^n` is finite. -/
theorem finiteLatticeQuotient {m n : ℤ} (h : m ≤ n) :
    Finite (LatticeQuotient F m n h) := by
  letI : CompactSpace (lattice F m) :=
    isCompact_iff_compactSpace.mp (isCompact_lattice F m)
  have hopen : IsOpen (latticeInside F h : Set (lattice F m)) := by
    rw [show (latticeInside F h : Set (lattice F m)) =
        ((lattice F m).subtype : lattice F m → F) ⁻¹' (lattice F n : Set F) by
      ext x
      simp]
    exact (isOpen_lattice F n).preimage continuous_subtype_val
  exact AddSubgroup.quotient_finite_of_isOpen
    (latticeInside F h).toAddSubgroup (by simpa using hopen)

instance instFiniteLatticeQuotient {m n : ℤ} (h : m ≤ n) :
    Finite (LatticeQuotient F m n h) :=
  finiteLatticeQuotient F h

/-- A coherent finite enumeration of a certified lattice quotient. -/
@[reducible] noncomputable def latticeQuotientFintype {m n : ℤ} (h : m ≤ n) :
    Fintype (LatticeQuotient F m n h) :=
  Fintype.ofFinite _

private theorem natCard_residueField :
    Nat.card (ResidueField F) = residueCard F := by
  letI := residueFieldFintype F
  rw [Nat.card_eq_fintype_card]
  rfl

/-- The exact cardinality of `𝖭_F^m / 𝖭_F^n` is `q_F ^ (n - m)`. -/
theorem latticeQuotient_card {m n : ℤ} (h : m ≤ n) :
    Nat.card (LatticeQuotient F m n h) =
      residueCard F ^ (n - m).toNat := by
  let O := ringOfIntegers F
  let P : Ideal O := IsLocalRing.maximalIdeal O
  calc
    Nat.card (LatticeQuotient F m n h) =
        Nat.card (O ⧸ P ^ (n - m).toNat) :=
      Nat.card_congr (latticeQuotientEquivMaximalIdealPow F h).symm.toEquiv
    _ = Submodule.cardQuot (P ^ (n - m).toNat) :=
      (Submodule.cardQuot_apply _).symm
    _ = Submodule.cardQuot P ^ (n - m).toNat := by
      rw [cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O)]
    _ = residueCard F ^ (n - m).toNat := by
      rw [Submodule.cardQuot_apply]
      change Nat.card (ResidueField F) ^ (n - m).toNat = _
      rw [natCard_residueField F]

/-- `Fintype.card` form of `latticeQuotient_card`. -/
theorem latticeQuotient_fintype_card {m n : ℤ} (h : m ≤ n) :
    @Fintype.card (LatticeQuotient F m n h) (latticeQuotientFintype F h) =
      residueCard F ^ (n - m).toNat := by
  letI := latticeQuotientFintype F h
  rw [← Nat.card_eq_fintype_card]
  exact latticeQuotient_card F h

/-- A finite lattice quotient always has nonzero cardinality, so its cardinality can be used
as a denominator. -/
theorem latticeQuotient_card_ne_zero {m n : ℤ} (h : m ≤ n) :
    Nat.card (LatticeQuotient F m n h) ≠ 0 :=
  (Nat.card_pos (α := LatticeQuotient F m n h)).ne'

end Finiteness

section PositiveUnitQuotients

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- At positive depth, `u - 1` lies in the lattice with the same index. -/
noncomputable def positiveUnitDisplacement {m : ℕ} (hm : 0 < m)
    (u : unitFiltration F m) : lattice F (m : ℤ) :=
  ⟨((u : Fˣ) : F) - 1, by
    have hm' : m = (m - 1) + 1 := by omega
    have hu : (u : Fˣ) ∈ unitFiltration F ((m - 1) + 1) := by
      simpa only [← hm'] using u.property
    have hdisp :=
      (mem_unitFiltration_succ_iff_sub_mem_lattice F (m - 1) (u : Fˣ)).1 hu
    simpa only [← hm'] using hdisp⟩

@[simp]
theorem coe_positiveUnitDisplacement {m : ℕ} (hm : 0 < m)
    (u : unitFiltration F m) :
    (positiveUnitDisplacement F hm u : F) = ((u : Fˣ) : F) - 1 :=
  rfl

/-- A positive-depth lattice element canonically gives the principal unit `1 + x`. -/
noncomputable def positiveUnitOfLattice {m : ℕ} (hm : 0 < m)
    (x : lattice F (m : ℤ)) : unitFiltration F m := by
  have hm' : m = (m - 1) + 1 := by omega
  have hx : (x : F) ∈ lattice F (((m - 1) + 1 : ℕ) : ℤ) := by
    rw [← hm']
    exact x.property
  let u₀ : Fˣ := principalUnitOf F (m - 1) (x : F) hx
  refine ⟨u₀, ?_⟩
  rw [hm']
  exact principalUnitOf_mem F (m - 1) (x : F) hx

@[simp]
theorem coe_positiveUnitOfLattice {m : ℕ} (hm : 0 < m)
    (x : lattice F (m : ℤ)) :
    ((positiveUnitOfLattice F hm x : Fˣ) : F) = 1 + (x : F) := by
  change (principalUnitOf F (m - 1) (x : F) (by
    have hm' : m = (m - 1) + 1 := by omega
    rw [← hm']
    exact x.property) : F) = 1 + (x : F)
  rfl

/-- The representative-free map `U^m/U^n → 𝖭^m/𝖭^n`, `[u] ↦ [u-1]`, for
positive `m`. -/
noncomputable def positiveUnitFiltrationQuotientToLattice {m n : ℕ}
    (hm : 0 < m) (h : m ≤ n) :
    UnitFiltrationQuotient F m n h →
      LatticeQuotient F (m : ℤ) (n : ℤ) (by exact_mod_cast h) := by
  let hZ : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
  exact Quotient.lift
    (fun u ↦ latticeQuotientMk F hZ
      (positiveUnitDisplacement F hm u))
    (by
      intro u v huv
      have huvQ : unitFiltrationQuotientMk F h u =
          unitFiltrationQuotientMk F h v :=
        Quotient.sound huv
      have hcong := (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F h u v).1 huvQ
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        hZ).2
      rw [CongruentAtDepth] at hcong ⊢
      simpa only [coe_positiveUnitDisplacement, sub_sub_sub_cancel_right] using hcong)

@[simp]
theorem positiveUnitFiltrationQuotientToLattice_mk {m n : ℕ}
    (hm : 0 < m) (h : m ≤ n) (u : unitFiltration F m) :
    positiveUnitFiltrationQuotientToLattice F hm h
        (unitFiltrationQuotientMk F h u) =
      latticeQuotientMk F (by exact_mod_cast h)
        (positiveUnitDisplacement F hm u) :=
  rfl

/-- The representative-free inverse `[x] ↦ [1+x]` at positive depth. -/
noncomputable def latticeQuotientToPositiveUnitFiltration {m n : ℕ}
    (hm : 0 < m) (h : m ≤ n) :
    LatticeQuotient F (m : ℤ) (n : ℤ) (by exact_mod_cast h) →
      UnitFiltrationQuotient F m n h := by
  let hZ : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
  exact Quotient.lift
    (fun x ↦ unitFiltrationQuotientMk F h (positiveUnitOfLattice F hm x))
    (by
      intro x y hxy
      have hmemInside : x - y ∈ latticeInside F hZ :=
        (Submodule.quotientRel_def (latticeInside F hZ)).1 hxy
      have hmem : (x : F) - (y : F) ∈ lattice F (n : ℤ) :=
        (mem_latticeInside F hZ).1 hmemInside
      apply (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F h _ _).2
      rw [CongruentAtDepth]
      simpa using hmem)

@[simp]
theorem latticeQuotientToPositiveUnitFiltration_mk {m n : ℕ}
    (hm : 0 < m) (h : m ≤ n) (x : lattice F (m : ℤ)) :
    latticeQuotientToPositiveUnitFiltration F hm h
        (latticeQuotientMk F (by exact_mod_cast h) x) =
      unitFiltrationQuotientMk F h (positiveUnitOfLattice F hm x) :=
  rfl

/-- For `0 < m ≤ n`, principal-unit classes modulo `U^n` are canonically the
additive lattice classes modulo `𝖭^n`.  This is a type equivalence for every such pair;
the stronger additive/multiplicative compatibility requires `n ≤ 2m` and is supplied below. -/
noncomputable def positiveUnitFiltrationQuotientEquivLattice {m n : ℕ}
    (hm : 0 < m) (h : m ≤ n) :
    UnitFiltrationQuotient F m n h ≃
      LatticeQuotient F (m : ℤ) (n : ℤ) (by exact_mod_cast h) where
  toFun := positiveUnitFiltrationQuotientToLattice F hm h
  invFun := latticeQuotientToPositiveUnitFiltration F hm h
  left_inv z := by
    induction z using Quotient.inductionOn with
    | _ u =>
        change unitFiltrationQuotientMk F h
            (positiveUnitOfLattice F hm (positiveUnitDisplacement F hm u)) =
          unitFiltrationQuotientMk F h u
        apply (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F h _ _).2
        rw [CongruentAtDepth]
        simp
  right_inv z := by
    induction z using Quotient.inductionOn with
    | _ x =>
        change latticeQuotientMk F (by exact_mod_cast h)
            (positiveUnitDisplacement F hm (positiveUnitOfLattice F hm x)) =
          latticeQuotientMk F (by exact_mod_cast h) x
        apply (latticeQuotientMk_eq_mk_iff F (by exact_mod_cast h)).2
        simp

@[simp]
theorem positiveUnitFiltrationQuotientEquivLattice_mk {m n : ℕ}
    (hm : 0 < m) (h : m ≤ n) (u : unitFiltration F m) :
    positiveUnitFiltrationQuotientEquivLattice F hm h
        (unitFiltrationQuotientMk F h u) =
      latticeQuotientMk F (by exact_mod_cast h)
        (positiveUnitDisplacement F hm u) :=
  rfl

/-- In the linear range `n ≤ 2m`, the positive-unit/lattice equivalence identifies
multiplication of unit classes with addition of displacement classes. -/
noncomputable def positiveUnitFiltrationQuotientMulEquivLattice
    {m n : ℕ} (hm : 0 < m) (h : m ≤ n) (hlin : n ≤ 2 * m) :
    UnitFiltrationQuotient F m n h ≃*
      Multiplicative
        (LatticeQuotient F (m : ℤ) (n : ℤ) (Int.ofNat_le.mpr h)) where
  toEquiv := (positiveUnitFiltrationQuotientEquivLattice F hm h).trans
    Multiplicative.ofAdd
  map_mul' z w := by
    induction z using Quotient.inductionOn with
    | _ u =>
      induction w using Quotient.inductionOn with
      | _ v =>
        change latticeQuotientMk F (Int.ofNat_le.mpr h)
              (positiveUnitDisplacement F hm (u * v)) =
            latticeQuotientMk F (Int.ofNat_le.mpr h)
                (positiveUnitDisplacement F hm u) +
              latticeQuotientMk F (Int.ofNat_le.mpr h)
                (positiveUnitDisplacement F hm v)
        rw [← map_add]
        apply (latticeQuotientMk_eq_mk_iff F (Int.ofNat_le.mpr h)).2
        change (((((u * v : unitFiltration F m) : Fˣ) : F) - 1) -
            ((((u : Fˣ) : F) - 1) + (((v : Fˣ) : F) - 1))) ∈
          lattice F (n : ℤ)
        have hu := (positiveUnitDisplacement F hm u).property
        have hv := (positiveUnitDisplacement F hm v).property
        have hprod :
            ((((u : Fˣ) : F) - 1) * (((v : Fˣ) : F) - 1)) ∈
              lattice F ((m : ℤ) + m) :=
          mul_mem_lattice F hu hv
        have hprod' := lattice_antitone F
          (show (n : ℤ) ≤ (m : ℤ) + m by omega) hprod
        rw [show (((((u * v : unitFiltration F m) : Fˣ) : F) - 1) -
            ((((u : Fˣ) : F) - 1) + (((v : Fˣ) : F) - 1))) =
              (((u : Fˣ) : F) - 1) * (((v : Fˣ) : F) - 1) by
          change ((((u : Fˣ) : F) * ((v : Fˣ) : F) - 1) -
            ((((u : Fˣ) : F) - 1) + (((v : Fˣ) : F) - 1))) = _
          ring]
        exact hprod'

/-- Positive-unit displacement commutes with replacing a deeper denominator by a shallower
one. -/
theorem positiveUnitFiltrationQuotientEquivLattice_projection
    {m n₁ n₂ : ℕ} (hm : 0 < m) (h₁ : m ≤ n₁) (h₁₂ : n₁ ≤ n₂)
    (z : UnitFiltrationQuotient F m n₂ (h₁.trans h₁₂)) :
    positiveUnitFiltrationQuotientEquivLattice F hm h₁
        (unitFiltrationQuotientProjection F h₁ h₁₂ z) =
      latticeQuotientProjection F (Int.ofNat_le.mpr h₁)
        (Int.ofNat_le.mpr h₁₂)
        (positiveUnitFiltrationQuotientEquivLattice F hm (h₁.trans h₁₂) z) := by
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F (h₁.trans h₁₂) z
  rfl

end PositiveUnitQuotients

section UnitFiniteness

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private noncomputable def unitFiltrationInsideEquiv {a b : ℕ} (h : a ≤ b) :
    unitFiltrationInside F h ≃* unitFiltration F b where
  toFun u := ⟨(u : unitFiltration F a),
    (mem_unitFiltrationInside F h (u : unitFiltration F a)).1 u.property⟩
  invFun u := ⟨⟨(u : Fˣ), unitFiltration_antitone F h u.property⟩,
    (mem_unitFiltrationInside F h _).2 u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem map_subgroupOf_unitFiltrationInsideEquiv {a b n : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) :
    ((unitFiltrationInside F (hab.trans hbn)).subgroupOf
        (unitFiltrationInside F hab)).map (unitFiltrationInsideEquiv F hab) =
      unitFiltrationInside F hbn := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (mem_unitFiltrationInside F hbn _).2
    exact (mem_unitFiltrationInside F (hab.trans hbn) _).1 hv
  · intro hu
    refine ⟨(unitFiltrationInsideEquiv F hab).symm u, ?_,
      (unitFiltrationInsideEquiv F hab).apply_symm_apply u⟩
    exact (mem_unitFiltrationInside F (hab.trans hbn) _).2
      ((mem_unitFiltrationInside F hbn _).1 hu)

private noncomputable def unitFiltrationQuotientEquivProd {a b n : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) :
    UnitFiltrationQuotient F a n (hab.trans hbn) ≃
      UnitFiltrationQuotient F a b hab × UnitFiltrationQuotient F b n hbn := by
  let N := unitFiltrationInside F (hab.trans hbn)
  let T := unitFiltrationInside F hab
  let e₁ : (unitFiltration F a ⧸ N) ≃
      (unitFiltration F a ⧸ T) × T ⧸ N.subgroupOf T :=
    Subgroup.quotientEquivProdOfLE (unitFiltrationInside_le F hab hbn)
  let e₂ : T ⧸ N.subgroupOf T ≃* UnitFiltrationQuotient F b n hbn :=
    QuotientGroup.congr _ _ (unitFiltrationInsideEquiv F hab)
      (map_subgroupOf_unitFiltrationInsideEquiv F hab hbn)
  exact e₁.trans (Equiv.prodCongr (Equiv.refl _) e₂.toEquiv)

/-- Every certified unit-filtration quotient `U_F^m/U_F^n` is finite. -/
theorem finiteUnitFiltrationQuotient {m n : ℕ} (h : m ≤ n) :
    Finite (UnitFiltrationQuotient F m n h) := by
  by_cases hm : m = 0
  · subst m
    cases n with
    | zero =>
        letI : Subsingleton (UnitFiltrationQuotient F 0 0 h) :=
          ⟨by
            intro x y
            induction x using Quotient.inductionOn with
            | _ u =>
                induction y using Quotient.inductionOn with
                | _ v =>
                    apply (unitFiltrationQuotientMk_eq_mk_iff F h u v).2
                    exact (unitFiltration F 0).div_mem u.property v.property⟩
        exact Finite.of_subsingleton
    | succ k =>
        have h₀₁ : 0 ≤ 1 := by omega
        have h₁n : 1 ≤ k + 1 := by omega
        letI : Fintype
            (IsLocalRing.ResidueField
              ((ValuativeRel.valuation F).valuationSubring)) :=
          residueFieldFintype F
        letI : Finite
            (IsLocalRing.ResidueField
              ((ValuativeRel.valuation F).valuationSubring))ˣ :=
          Finite.of_injective
            (fun u : (IsLocalRing.ResidueField
                ((ValuativeRel.valuation F).valuationSubring))ˣ ↦
              (u : IsLocalRing.ResidueField
                ((ValuativeRel.valuation F).valuationSubring)))
            Units.val_injective
        letI : Finite (UnitFiltrationQuotient F 0 1 h₀₁) :=
          Finite.of_injective (unitGradedZeroEquivResidueFieldUnits F)
            (unitGradedZeroEquivResidueFieldUnits F).injective
        letI : Finite (UnitFiltrationQuotient F 1 (k + 1) h₁n) :=
          Finite.of_injective
            (positiveUnitFiltrationQuotientEquivLattice F (by omega) h₁n)
            (positiveUnitFiltrationQuotientEquivLattice F (by omega) h₁n).injective
        exact Finite.of_injective (unitFiltrationQuotientEquivProd F h₀₁ h₁n)
          (unitFiltrationQuotientEquivProd F h₀₁ h₁n).injective
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    exact Finite.of_injective (positiveUnitFiltrationQuotientEquivLattice F hmpos h)
      (positiveUnitFiltrationQuotientEquivLattice F hmpos h).injective

instance instFiniteUnitFiltrationQuotient {m n : ℕ} (h : m ≤ n) :
    Finite (UnitFiltrationQuotient F m n h) :=
  finiteUnitFiltrationQuotient F h

/-- A coherent finite enumeration of a certified unit-filtration quotient. -/
@[reducible] noncomputable def unitFiltrationQuotientFintype {m n : ℕ}
    (h : m ≤ n) : Fintype (UnitFiltrationQuotient F m n h) :=
  Fintype.ofFinite _

/-- At positive depth, `|U_F^m/U_F^n| = q_F^(n-m)`. -/
theorem positiveUnitFiltrationQuotient_card {m n : ℕ} (hm : 0 < m)
    (h : m ≤ n) :
    Nat.card (UnitFiltrationQuotient F m n h) = residueCard F ^ (n - m) := by
  rw [Nat.card_congr (positiveUnitFiltrationQuotientEquivLattice F hm h)]
  convert latticeQuotient_card F (show (m : ℤ) ≤ (n : ℤ) by exact_mod_cast h) using 1
  congr
  omega

/-- At depth zero, the trivial quotient has one element. -/
theorem unitFiltrationQuotient_card_zero_zero :
    Nat.card (UnitFiltrationQuotient F 0 0 (by omega)) = 1 := by
  change (unitFiltrationInside F (show 0 ≤ 0 by omega)).index = 1
  rw [show unitFiltrationInside F (show 0 ≤ 0 by omega) = ⊤ by
    ext u
    simp only [Subgroup.mem_top, iff_true]
    exact (mem_unitFiltrationInside F (show 0 ≤ 0 by omega) u).2 u.property]
  exact Subgroup.index_top

/-- For `n > 0`, `|U_F^0/U_F^n| = (q_F-1) q_F^(n-1)`. -/
theorem unitFiltrationQuotient_card_zero {n : ℕ} (hn : 0 < n) :
    Nat.card (UnitFiltrationQuotient F 0 n (by omega)) =
      (residueCard F - 1) * residueCard F ^ (n - 1) := by
  have h₀₁ : 0 ≤ 1 := by omega
  have h₁n : 1 ≤ n := hn
  rw [Nat.card_congr (unitFiltrationQuotientEquivProd F h₀₁ h₁n), Nat.card_prod,
    Nat.card_congr (unitGradedZeroEquivResidueFieldUnits F).toEquiv, Nat.card_units,
    positiveUnitFiltrationQuotient_card F (by omega) h₁n]
  change (Nat.card (ResidueField F) - 1) * residueCard F ^ (n - 1) = _
  rw [natCard_residueField F]

/-- Complete cardinality formula, including the boundary between `U^0` and positive layers. -/
theorem unitFiltrationQuotient_card {m n : ℕ} (h : m ≤ n) :
    Nat.card (UnitFiltrationQuotient F m n h) =
      if m = 0 then
        if n = 0 then 1 else (residueCard F - 1) * residueCard F ^ (n - 1)
      else residueCard F ^ (n - m) := by
  by_cases hm : m = 0
  · subst m
    by_cases hn : n = 0
    · subst n
      simpa using unitFiltrationQuotient_card_zero_zero F
    · simpa [hn] using unitFiltrationQuotient_card_zero F (Nat.pos_of_ne_zero hn)
  · simpa [hm] using positiveUnitFiltrationQuotient_card F (Nat.pos_of_ne_zero hm) h

/-- `Fintype.card` form of `unitFiltrationQuotient_card`. -/
theorem unitFiltrationQuotient_fintype_card {m n : ℕ} (h : m ≤ n) :
    @Fintype.card (UnitFiltrationQuotient F m n h)
        (unitFiltrationQuotientFintype F h) =
      if m = 0 then
        if n = 0 then 1 else (residueCard F - 1) * residueCard F ^ (n - 1)
      else residueCard F ^ (n - m) := by
  letI := unitFiltrationQuotientFintype F h
  rw [← Nat.card_eq_fintype_card]
  exact unitFiltrationQuotient_card F h

/-- A finite unit-filtration quotient always has nonzero cardinality, so its cardinality can
be used as a denominator. -/
theorem unitFiltrationQuotient_card_ne_zero {m n : ℕ} (h : m ≤ n) :
    Nat.card (UnitFiltrationQuotient F m n h) ≠ 0 :=
  (Nat.card_pos (α := UnitFiltrationQuotient F m n h)).ne'

end UnitFiniteness

section QuotientArithmetic

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Addition of lattice classes is computed on any numerator representatives. -/
@[simp]
theorem latticeQuotientMk_add {m n : ℤ} (h : m ≤ n)
    (x y : lattice F m) :
    latticeQuotientMk F h (x + y) =
      latticeQuotientMk F h x + latticeQuotientMk F h y :=
  map_add (latticeQuotientMk F h) x y

/-- Negation of a lattice class is computed on any numerator representative. -/
@[simp]
theorem latticeQuotientMk_neg {m n : ℤ} (h : m ≤ n)
    (x : lattice F m) :
    latticeQuotientMk F h (-x) = -latticeQuotientMk F h x :=
  map_neg (latticeQuotientMk F h) x

/-- Subtraction of lattice classes is computed on any numerator representatives. -/
@[simp]
theorem latticeQuotientMk_sub {m n : ℤ} (h : m ≤ n)
    (x y : lattice F m) :
    latticeQuotientMk F h (x - y) =
      latticeQuotientMk F h x - latticeQuotientMk F h y :=
  map_sub (latticeQuotientMk F h) x y

/-- Multiplication of unit classes is computed on any numerator representatives. -/
@[simp]
theorem unitFiltrationQuotientMk_mul {m n : ℕ} (h : m ≤ n)
    (u v : unitFiltration F m) :
    unitFiltrationQuotientMk F h (u * v) =
      unitFiltrationQuotientMk F h u * unitFiltrationQuotientMk F h v :=
  map_mul (unitFiltrationQuotientMk F h) u v

/-- Inversion of a unit class is computed on any numerator representative. -/
@[simp]
theorem unitFiltrationQuotientMk_inv {m n : ℕ} (h : m ≤ n)
    (u : unitFiltration F m) :
    unitFiltrationQuotientMk F h u⁻¹ =
      (unitFiltrationQuotientMk F h u)⁻¹ :=
  map_inv (unitFiltrationQuotientMk F h) u

/-- Division of unit classes is computed on any numerator representatives. -/
@[simp]
theorem unitFiltrationQuotientMk_div {m n : ℕ} (h : m ≤ n)
    (u v : unitFiltration F m) :
    unitFiltrationQuotientMk F h (u / v) =
      unitFiltrationQuotientMk F h u / unitFiltrationQuotientMk F h v :=
  map_div (unitFiltrationQuotientMk F h) u v

/-- Projecting a lattice quotient to the same denominator is the identity. -/
@[simp]
theorem latticeQuotientProjection_self {m n : ℤ} (h : m ≤ n)
    (z : LatticeQuotient F m n (h.trans le_rfl)) :
    latticeQuotientProjection F h le_rfl z = z := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F (h.trans le_rfl) z
  rfl

/-- Lattice denominator projections compose transitively. -/
theorem latticeQuotientProjection_trans {m n₁ n₂ n₃ : ℤ}
    (hm : m ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (z : LatticeQuotient F m n₃ ((hm.trans h₁₂).trans h₂₃)) :
    latticeQuotientProjection F hm h₁₂
        (latticeQuotientProjection F (hm.trans h₁₂) h₂₃ z) =
      latticeQuotientProjection F hm (h₁₂.trans h₂₃) z := by
  obtain ⟨x, rfl⟩ :=
    latticeQuotientMk_surjective F ((hm.trans h₁₂).trans h₂₃) z
  rfl

/-- Projecting a unit-filtration quotient to the same denominator is the identity. -/
@[simp]
theorem unitFiltrationQuotientProjection_self {m n : ℕ} (h : m ≤ n)
    (z : UnitFiltrationQuotient F m n (h.trans le_rfl)) :
    unitFiltrationQuotientProjection F h le_rfl z = z := by
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F (h.trans le_rfl) z
  rfl

/-- Unit-filtration denominator projections compose transitively. -/
theorem unitFiltrationQuotientProjection_trans {m n₁ n₂ n₃ : ℕ}
    (hm : m ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (z : UnitFiltrationQuotient F m n₃ ((hm.trans h₁₂).trans h₂₃)) :
    unitFiltrationQuotientProjection F hm h₁₂
        (unitFiltrationQuotientProjection F (hm.trans h₁₂) h₂₃ z) =
      unitFiltrationQuotientProjection F hm (h₁₂.trans h₂₃) z := by
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective F ((hm.trans h₁₂).trans h₂₃) z
  rfl

end QuotientArithmetic

section RepresentativeFreeDescent

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Descend a function on a numerator lattice that is invariant modulo the denominator.
The resulting public function consumes a quotient class, not a selected representative. -/
noncomputable def latticeQuotientLift {m n : ℤ} (h : m ≤ n) {A : Sort*}
    (f : lattice F m → A)
    (hf : ∀ (x y : lattice F m),
      CongruentAtDepth n (x : F) (y : F) → f x = f y) :
    LatticeQuotient F m n h → A :=
  Quotient.lift f (fun x y hxy ↦ hf x y <|
    (latticeQuotientMk_eq_mk_iff_congruentAtDepth F h).1
      (Quotient.sound hxy))

@[simp]
theorem latticeQuotientLift_mk {m n : ℤ} (h : m ≤ n) {A : Sort*}
    (f : lattice F m → A)
    (hf : ∀ (x y : lattice F m),
      CongruentAtDepth n (x : F) (y : F) → f x = f y)
    (x : lattice F m) :
    latticeQuotientLift F h f hf (latticeQuotientMk F h x) = f x :=
  rfl

/-- Descend a two-variable function that is separately invariant modulo two lattice
denominators. -/
noncomputable def latticeQuotientLift2 {m₁ n₁ m₂ n₂ : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂) {A : Sort*}
    (f : lattice F m₁ → lattice F m₂ → A)
    (hf₁ : ∀ (x x' : lattice F m₁) (y : lattice F m₂),
      CongruentAtDepth n₁ (x : F) (x' : F) → f x y = f x' y)
    (hf₂ : ∀ (x : lattice F m₁) (y y' : lattice F m₂),
      CongruentAtDepth n₂ (y : F) (y' : F) → f x y = f x y') :
    LatticeQuotient F m₁ n₁ h₁ →
      LatticeQuotient F m₂ n₂ h₂ → A :=
  Quotient.lift₂ f (fun x y x' y' hxx hyy ↦
    (hf₁ x x' y <|
      (latticeQuotientMk_eq_mk_iff_congruentAtDepth F h₁).1
        (Quotient.sound hxx)).trans <|
    hf₂ x' y y' <|
      (latticeQuotientMk_eq_mk_iff_congruentAtDepth F h₂).1
        (Quotient.sound hyy))

@[simp]
theorem latticeQuotientLift2_mk_mk {m₁ n₁ m₂ n₂ : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂) {A : Sort*}
    (f : lattice F m₁ → lattice F m₂ → A)
    (hf₁ : ∀ (x x' : lattice F m₁) (y : lattice F m₂),
      CongruentAtDepth n₁ (x : F) (x' : F) → f x y = f x' y)
    (hf₂ : ∀ (x : lattice F m₁) (y y' : lattice F m₂),
      CongruentAtDepth n₂ (y : F) (y' : F) → f x y = f x y')
    (x : lattice F m₁) (y : lattice F m₂) :
    latticeQuotientLift2 F h₁ h₂ f hf₁ hf₂
        (latticeQuotientMk F h₁ x) (latticeQuotientMk F h₂ y) = f x y :=
  rfl

/-- Descend a function on a unit-filtration numerator that is invariant modulo the
denominator congruence. -/
noncomputable def unitFiltrationQuotientLift {m n : ℕ} (h : m ≤ n) {A : Sort*}
    (f : unitFiltration F m → A)
    (hf : ∀ (u v : unitFiltration F m),
      CongruentAtDepth (n : ℤ) ((u : Fˣ) : F) ((v : Fˣ) : F) → f u = f v) :
    UnitFiltrationQuotient F m n h → A :=
  Quotient.lift f (fun u v huv ↦ hf u v <|
    (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F h u v).1
      (Quotient.sound huv))

@[simp]
theorem unitFiltrationQuotientLift_mk {m n : ℕ} (h : m ≤ n) {A : Sort*}
    (f : unitFiltration F m → A)
    (hf : ∀ (u v : unitFiltration F m),
      CongruentAtDepth (n : ℤ) ((u : Fˣ) : F) ((v : Fˣ) : F) → f u = f v)
    (u : unitFiltration F m) :
    unitFiltrationQuotientLift F h f hf
        (unitFiltrationQuotientMk F h u) = f u :=
  rfl

/-- The finite sum of a representative-invariant function over a lattice quotient. -/
noncomputable def latticeQuotientSum {m n : ℤ} (h : m ≤ n)
    {A : Type*} [AddCommMonoid A] (f : lattice F m → A)
    (hf : ∀ (x y : lattice F m),
      CongruentAtDepth n (x : F) (y : F) → f x = f y) : A := by
  letI := latticeQuotientFintype F h
  exact ∑ z, latticeQuotientLift F h f hf z

/-- The iterated finite sum of a separately representative-invariant function over two
lattice quotients. -/
noncomputable def latticeQuotientSum2 {m₁ n₁ m₂ n₂ : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    {A : Type*} [AddCommMonoid A]
    (f : lattice F m₁ → lattice F m₂ → A)
    (hf₁ : ∀ (x x' : lattice F m₁) (y : lattice F m₂),
      CongruentAtDepth n₁ (x : F) (x' : F) → f x y = f x' y)
    (hf₂ : ∀ (x : lattice F m₁) (y y' : lattice F m₂),
      CongruentAtDepth n₂ (y : F) (y' : F) → f x y = f x y') : A := by
  letI := latticeQuotientFintype F h₁
  letI := latticeQuotientFintype F h₂
  exact ∑ x, ∑ y, latticeQuotientLift2 F h₁ h₂ f hf₁ hf₂ x y

/-- The finite sum of a representative-invariant function over a unit-filtration quotient. -/
noncomputable def unitFiltrationQuotientSum {m n : ℕ} (h : m ≤ n)
    {A : Type*} [AddCommMonoid A] (f : unitFiltration F m → A)
    (hf : ∀ (u v : unitFiltration F m),
      CongruentAtDepth (n : ℤ) ((u : Fˣ) : F) ((v : Fˣ) : F) → f u = f v) : A := by
  letI := unitFiltrationQuotientFintype F h
  exact ∑ z, unitFiltrationQuotientLift F h f hf z

/-- Translation permutes every finite lattice quotient, so it does not change a sum. -/
theorem sum_latticeQuotient_add_left {m n : ℤ} (h : m ≤ n)
    {A : Type*} [AddCommMonoid A] (a : LatticeQuotient F m n h)
    (f : LatticeQuotient F m n h → A) :
    letI := latticeQuotientFintype F h
    ∑ x, f (a + x) = ∑ x, f x := by
  letI := latticeQuotientFintype F h
  exact @Equiv.sum_comp _ _ _ _ _ _ (Equiv.addLeft a) f

/-- Multiplication by a unit class permutes every finite unit-filtration quotient, so it
does not change a sum. -/
theorem sum_unitFiltrationQuotient_mul_left {m n : ℕ} (h : m ≤ n)
    {A : Type*} [AddCommMonoid A] (a : UnitFiltrationQuotient F m n h)
    (f : UnitFiltrationQuotient F m n h → A) :
    letI := unitFiltrationQuotientFintype F h
    ∑ x, f (a * x) = ∑ x, f x := by
  letI := unitFiltrationQuotientFintype F h
  exact @Equiv.sum_comp _ _ _ _ _ _ (Equiv.mulLeft a) f

end RepresentativeFreeDescent

section ProjectionFibers

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private noncomputable def latticeQuotientKernelMap {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    LatticeQuotient F n₁ n₂ h →
      {z : LatticeQuotient F m n₂ (hm.trans h) //
        latticeQuotientProjection F hm h z = 0} :=
  Quotient.lift
    (fun x ↦ ⟨latticeQuotientMk F (hm.trans h)
        ⟨(x : F), lattice_antitone F hm x.property⟩, by
      rw [latticeQuotientProjection_mk, latticeQuotientMk_eq_zero_iff]
      exact x.property⟩)
    (fun x y hxy ↦ by
      apply Subtype.ext
      apply (latticeQuotientMk_eq_mk_iff F (hm.trans h)).2
      have heq : latticeQuotientMk F h x = latticeQuotientMk F h y :=
        Quotient.sound hxy
      exact (latticeQuotientMk_eq_mk_iff F h).1 heq)

@[simp]
private theorem latticeQuotientKernelMap_mk {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) (x : lattice F n₁) :
    (latticeQuotientKernelMap F hm h (latticeQuotientMk F h x) :
      LatticeQuotient F m n₂ (hm.trans h)) =
      latticeQuotientMk F (hm.trans h)
        ⟨(x : F), lattice_antitone F hm x.property⟩ :=
  rfl

private theorem latticeQuotientKernelMap_injective {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    Function.Injective (latticeQuotientKernelMap F hm h) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h x
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h y
  apply (latticeQuotientMk_eq_mk_iff F h).2
  have heq : latticeQuotientMk F (hm.trans h)
        ⟨(x : F), lattice_antitone F hm x.property⟩ =
      latticeQuotientMk F (hm.trans h)
        ⟨(y : F), lattice_antitone F hm y.property⟩ :=
    congrArg Subtype.val hxy
  exact (latticeQuotientMk_eq_mk_iff F (hm.trans h)).1 heq

private theorem latticeQuotientKernelMap_surjective {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    Function.Surjective (latticeQuotientKernelMap F hm h) := by
  intro z
  obtain ⟨x, hx⟩ := latticeQuotientMk_surjective F (hm.trans h) (z : _)
  have hxden : (x : F) ∈ lattice F n₁ := by
    have hz := z.property
    rw [← hx, latticeQuotientProjection_mk,
      latticeQuotientMk_eq_zero_iff] at hz
    exact hz
  let x₁ : lattice F n₁ := ⟨x, hxden⟩
  refine ⟨latticeQuotientMk F h x₁, ?_⟩
  apply Subtype.ext
  rw [latticeQuotientKernelMap_mk]
  exact hx

/-- The kernel of a lattice denominator projection is canonically the quotient of the two
denominator lattices. -/
noncomputable def latticeQuotientKernelEquiv {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    LatticeQuotient F n₁ n₂ h ≃
      {z : LatticeQuotient F m n₂ (hm.trans h) //
        latticeQuotientProjection F hm h z = 0} :=
  Equiv.ofBijective (latticeQuotientKernelMap F hm h)
    ⟨latticeQuotientKernelMap_injective F hm h,
      latticeQuotientKernelMap_surjective F hm h⟩

/-- A proof-only equivalence between a projection fiber and its kernel quotient.  It is kept
private because constructing it requires choosing a point of the fiber. -/
private noncomputable def latticeQuotientProjectionFiberEquiv {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂)
    (y : LatticeQuotient F m n₁ hm) :
    {z : LatticeQuotient F m n₂ (hm.trans h) //
        latticeQuotientProjection F hm h z = y} ≃
      LatticeQuotient F n₁ n₂ h := by
  let p := (latticeQuotientProjection F hm h).toAddMonoidHom
  let e₁ : {z : LatticeQuotient F m n₂ (hm.trans h) //
        latticeQuotientProjection F hm h z = y} ≃ p ⁻¹' {y} :=
    Equiv.setCongr (by ext z; rfl)
  let e₂ : p ⁻¹' {y} ≃ p.ker :=
    p.fiberEquivKerOfSurjective (latticeQuotientProjection_surjective F hm h) y
  let e₃ : p.ker ≃
      {z : LatticeQuotient F m n₂ (hm.trans h) //
        latticeQuotientProjection F hm h z = 0} :=
    Equiv.setCongr (by ext z; rfl)
  exact e₁.trans (e₂.trans (e₃.trans (latticeQuotientKernelEquiv F hm h).symm))

/-- Every fiber of a lattice denominator projection has `q_F^(n₂-n₁)` elements. -/
theorem latticeQuotientProjection_fiber_card {m n₁ n₂ : ℤ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂)
    (y : LatticeQuotient F m n₁ hm) :
    Nat.card {z : LatticeQuotient F m n₂ (hm.trans h) //
        latticeQuotientProjection F hm h z = y} =
      residueCard F ^ (n₂ - n₁).toNat := by
  rw [Nat.card_congr (latticeQuotientProjectionFiberEquiv F hm h y)]
  exact latticeQuotient_card F h

private noncomputable def unitFiltrationQuotientKernelMap {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    UnitFiltrationQuotient F n₁ n₂ h →
      {z : UnitFiltrationQuotient F m n₂ (hm.trans h) //
        unitFiltrationQuotientProjection F hm h z = 1} :=
  Quotient.lift
    (fun u ↦ ⟨unitFiltrationQuotientMk F (hm.trans h)
        ⟨(u : Fˣ), unitFiltration_antitone F hm u.property⟩, by
      rw [unitFiltrationQuotientProjection_mk,
        unitFiltrationQuotientMk_eq_one_iff]
      exact u.property⟩)
    (fun u v huv ↦ by
      apply Subtype.ext
      apply (unitFiltrationQuotientMk_eq_mk_iff F (hm.trans h) _ _).2
      have heq : unitFiltrationQuotientMk F h u =
          unitFiltrationQuotientMk F h v := Quotient.sound huv
      exact (unitFiltrationQuotientMk_eq_mk_iff F h u v).1 heq)

@[simp]
private theorem unitFiltrationQuotientKernelMap_mk {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) (u : unitFiltration F n₁) :
    (unitFiltrationQuotientKernelMap F hm h
        (unitFiltrationQuotientMk F h u) :
      UnitFiltrationQuotient F m n₂ (hm.trans h)) =
      unitFiltrationQuotientMk F (hm.trans h)
        ⟨(u : Fˣ), unitFiltration_antitone F hm u.property⟩ :=
  rfl

private theorem unitFiltrationQuotientKernelMap_injective {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    Function.Injective (unitFiltrationQuotientKernelMap F hm h) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F h x
  obtain ⟨v, rfl⟩ := unitFiltrationQuotientMk_surjective F h y
  apply (unitFiltrationQuotientMk_eq_mk_iff F h u v).2
  have heq : unitFiltrationQuotientMk F (hm.trans h)
        ⟨(u : Fˣ), unitFiltration_antitone F hm u.property⟩ =
      unitFiltrationQuotientMk F (hm.trans h)
        ⟨(v : Fˣ), unitFiltration_antitone F hm v.property⟩ :=
    congrArg Subtype.val hxy
  exact (unitFiltrationQuotientMk_eq_mk_iff F (hm.trans h) _ _).1 heq

private theorem unitFiltrationQuotientKernelMap_surjective {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    Function.Surjective (unitFiltrationQuotientKernelMap F hm h) := by
  intro z
  obtain ⟨u, hu⟩ := unitFiltrationQuotientMk_surjective F (hm.trans h) (z : _)
  have huden : (u : Fˣ) ∈ unitFiltration F n₁ := by
    have hz := z.property
    rw [← hu, unitFiltrationQuotientProjection_mk,
      unitFiltrationQuotientMk_eq_one_iff] at hz
    exact hz
  let u₁ : unitFiltration F n₁ := ⟨u, huden⟩
  refine ⟨unitFiltrationQuotientMk F h u₁, ?_⟩
  apply Subtype.ext
  rw [unitFiltrationQuotientKernelMap_mk]
  exact hu

/-- The kernel of a unit-filtration denominator projection is canonically the quotient of the
two denominator filtration groups. -/
noncomputable def unitFiltrationQuotientKernelEquiv {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂) :
    UnitFiltrationQuotient F n₁ n₂ h ≃
      {z : UnitFiltrationQuotient F m n₂ (hm.trans h) //
        unitFiltrationQuotientProjection F hm h z = 1} :=
  Equiv.ofBijective (unitFiltrationQuotientKernelMap F hm h)
    ⟨unitFiltrationQuotientKernelMap_injective F hm h,
      unitFiltrationQuotientKernelMap_surjective F hm h⟩

/-- A proof-only equivalence between a unit projection fiber and its kernel quotient.  It is
kept private because constructing it requires choosing a point of the fiber. -/
private noncomputable def unitFiltrationQuotientProjectionFiberEquiv {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂)
    (y : UnitFiltrationQuotient F m n₁ hm) :
    {z : UnitFiltrationQuotient F m n₂ (hm.trans h) //
        unitFiltrationQuotientProjection F hm h z = y} ≃
      UnitFiltrationQuotient F n₁ n₂ h := by
  let p := unitFiltrationQuotientProjection F hm h
  let e₁ : {z : UnitFiltrationQuotient F m n₂ (hm.trans h) //
        unitFiltrationQuotientProjection F hm h z = y} ≃ p ⁻¹' {y} :=
    Equiv.setCongr (by ext z; rfl)
  let e₂ : p ⁻¹' {y} ≃ p.ker :=
    p.fiberEquivKerOfSurjective
      (unitFiltrationQuotientProjection_surjective F hm h) y
  let e₃ : p.ker ≃
      {z : UnitFiltrationQuotient F m n₂ (hm.trans h) //
        unitFiltrationQuotientProjection F hm h z = 1} :=
    Equiv.setCongr (by ext z; rfl)
  exact e₁.trans (e₂.trans
    (e₃.trans (unitFiltrationQuotientKernelEquiv F hm h).symm))

/-- Every fiber of a unit-filtration denominator projection has the cardinality of
`U_F^n₁/U_F^n₂`, including the separate depth-zero case. -/
theorem unitFiltrationQuotientProjection_fiber_card {m n₁ n₂ : ℕ}
    (hm : m ≤ n₁) (h : n₁ ≤ n₂)
    (y : UnitFiltrationQuotient F m n₁ hm) :
    Nat.card {z : UnitFiltrationQuotient F m n₂ (hm.trans h) //
        unitFiltrationQuotientProjection F hm h z = y} =
      if n₁ = 0 then
        if n₂ = 0 then 1 else
          (residueCard F - 1) * residueCard F ^ (n₂ - 1)
      else residueCard F ^ (n₂ - n₁) := by
  rw [Nat.card_congr (unitFiltrationQuotientProjectionFiberEquiv F hm h y)]
  exact unitFiltrationQuotient_card F h

end ProjectionFibers

section QuotientProducts

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Canonical multiplication of two lattice quotient classes.  The two upper bounds on `k`
ensure that the result is independent of changing either representative. -/
noncomputable def latticeQuotientMul
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂) :
    LatticeQuotient F m₁ n₁ h₁ → LatticeQuotient F m₂ n₂ h₂ →
      LatticeQuotient F (m₁ + m₂) k hdepth :=
  latticeQuotientLift2 F h₁ h₂
    (fun x y ↦ latticeQuotientMk F hdepth
      ⟨(x : F) * (y : F), mul_mem_lattice F x.property y.property⟩)
    (fun x x' y hxx ↦ by
      apply (latticeQuotientMk_eq_mk_iff F hdepth).2
      apply lattice_antitone F hk₁
      rw [← sub_mul]
      exact mul_mem_lattice F
        ((congruentAtDepth_iff_sub_mem_lattice F n₁ (x : F) (x' : F)).1 hxx)
        y.property)
    (fun x y y' hyy ↦ by
      apply (latticeQuotientMk_eq_mk_iff F hdepth).2
      apply lattice_antitone F hk₂
      rw [← mul_sub]
      exact mul_mem_lattice F x.property
        ((congruentAtDepth_iff_sub_mem_lattice F n₂ (y : F) (y' : F)).1 hyy))

@[simp]
theorem latticeQuotientMul_mk_mk
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x : lattice F m₁) (y : lattice F m₂) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂
        (latticeQuotientMk F h₁ x) (latticeQuotientMk F h₂ y) =
      latticeQuotientMk F hdepth
        ⟨(x : F) * (y : F), mul_mem_lattice F x.property y.property⟩ :=
  rfl

private theorem latticeQuotientMul_zero_right
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x : LatticeQuotient F m₁ n₁ h₁) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x 0 = 0 := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h₁ x
  change latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂
      (latticeQuotientMk F h₁ x) (latticeQuotientMk F h₂ 0) = 0
  rw [latticeQuotientMul_mk_mk]
  simp

private theorem latticeQuotientMul_add_right
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x : LatticeQuotient F m₁ n₁ h₁)
    (y z : LatticeQuotient F m₂ n₂ h₂) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x (y + z) =
      latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x y +
        latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x z := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h₁ x
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h₂ y
  obtain ⟨z, rfl⟩ := latticeQuotientMk_surjective F h₂ z
  change latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂
      (latticeQuotientMk F h₁ x) (latticeQuotientMk F h₂ (y + z)) = _
  rw [latticeQuotientMul_mk_mk, latticeQuotientMul_mk_mk,
    latticeQuotientMul_mk_mk, ← latticeQuotientMk_add]
  congr 1
  apply Subtype.ext
  simp [mul_add]

private theorem latticeQuotientMul_zero_left
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (y : LatticeQuotient F m₂ n₂ h₂) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ 0 y = 0 := by
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h₂ y
  change latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂
      (latticeQuotientMk F h₁ 0) (latticeQuotientMk F h₂ y) = 0
  rw [latticeQuotientMul_mk_mk]
  simp

private theorem latticeQuotientMul_add_left
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x z : LatticeQuotient F m₁ n₁ h₁)
    (y : LatticeQuotient F m₂ n₂ h₂) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ (x + z) y =
      latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x y +
        latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ z y := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h₁ x
  obtain ⟨z, rfl⟩ := latticeQuotientMk_surjective F h₁ z
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h₂ y
  change latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂
      (latticeQuotientMk F h₁ (x + z)) (latticeQuotientMk F h₂ y) = _
  rw [latticeQuotientMul_mk_mk, latticeQuotientMul_mk_mk,
    latticeQuotientMul_mk_mk, ← latticeQuotientMk_add]
  congr 1
  apply Subtype.ext
  simp [add_mul]

/-- The quotient product, bundled as an additive homomorphism in each variable. -/
noncomputable def latticeQuotientMulAddHom
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂) :
    LatticeQuotient F m₁ n₁ h₁ →+
      LatticeQuotient F m₂ n₂ h₂ →+
        LatticeQuotient F (m₁ + m₂) k hdepth where
  toFun x :=
    { toFun := latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x
      map_zero' := latticeQuotientMul_zero_right F h₁ h₂ hdepth hk₁ hk₂ x
      map_add' := latticeQuotientMul_add_right F h₁ h₂ hdepth hk₁ hk₂ x }
  map_zero' := by
    apply AddMonoidHom.ext
    exact latticeQuotientMul_zero_left F h₁ h₂ hdepth hk₁ hk₂
  map_add' x z := by
    apply AddMonoidHom.ext
    exact latticeQuotientMul_add_left F h₁ h₂ hdepth hk₁ hk₂ x z

@[simp]
theorem latticeQuotientMulAddHom_apply
    {m₁ n₁ m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x : LatticeQuotient F m₁ n₁ h₁)
    (y : LatticeQuotient F m₂ n₂ h₂) :
    latticeQuotientMulAddHom F h₁ h₂ hdepth hk₁ hk₂ x y =
      latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x y :=
  rfl

/-- Division by an explicitly supplied element of valuation `r` shifts both quotient depths
by `-r`.  No element of a quotient is represented or selected by this operation. -/
noncomputable def latticeQuotientDiv
    (a : F) (r : ℤ) (ha : ord F a = (r : WithTop ℤ))
    {m n : ℤ} (h : m ≤ n) :
    LatticeQuotient F m n h →
      LatticeQuotient F (m - r) (n - r) (sub_le_sub_right h r) :=
  latticeQuotientLift F h
    (fun x ↦ latticeQuotientMk F (sub_le_sub_right h r)
      ⟨(x : F) / a, (div_mem_lattice_iff F a (x : F) r (m - r) ha).2
        (by simpa only [show r + (m - r) = m by omega] using x.property)⟩)
    (fun x y hxy ↦ by
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        (sub_le_sub_right h r)).2
      apply (congruentAtDepth_iff_sub_mem_lattice F (n - r)
        ((x : F) / a) ((y : F) / a)).2
      rw [← sub_div]
      exact (div_mem_lattice_iff F a ((x : F) - (y : F)) r (n - r) ha).2
        (by
          simpa only [show r + (n - r) = n by omega] using
            (congruentAtDepth_iff_sub_mem_lattice F n (x : F) (y : F)).1 hxy))

@[simp]
theorem latticeQuotientDiv_mk
    (a : F) (r : ℤ) (ha : ord F a = (r : WithTop ℤ))
    {m n : ℤ} (h : m ≤ n) (x : lattice F m) :
    latticeQuotientDiv F a r ha h (latticeQuotientMk F h x) =
      latticeQuotientMk F (sub_le_sub_right h r)
        ⟨(x : F) / a, (div_mem_lattice_iff F a (x : F) r (m - r) ha).2
          (by simpa only [show r + (m - r) = m by omega] using x.property)⟩ :=
  rfl

/-- Division by a fixed scalar, bundled as an additive homomorphism. -/
noncomputable def latticeQuotientDivAddHom
    (a : F) (r : ℤ) (ha : ord F a = (r : WithTop ℤ))
    {m n : ℤ} (h : m ≤ n) :
    LatticeQuotient F m n h →+
      LatticeQuotient F (m - r) (n - r) (sub_le_sub_right h r) where
  toFun := latticeQuotientDiv F a r ha h
  map_zero' := by
    change latticeQuotientDiv F a r ha h (latticeQuotientMk F h 0) = 0
    rw [latticeQuotientDiv_mk]
    simp
  map_add' := by
    intro x y
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h x
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h y
    change latticeQuotientDiv F a r ha h (latticeQuotientMk F h (x + y)) =
      latticeQuotientDiv F a r ha h (latticeQuotientMk F h x) +
        latticeQuotientDiv F a r ha h (latticeQuotientMk F h y)
    rw [latticeQuotientDiv_mk, latticeQuotientDiv_mk,
      latticeQuotientDiv_mk, ← latticeQuotientMk_add]
    congr 1
    apply Subtype.ext
    exact add_div (x : F) (y : F) a

@[simp]
theorem latticeQuotientDivAddHom_apply
    (a : F) (r : ℤ) (ha : ord F a = (r : WithTop ℤ))
    {m n : ℤ} (h : m ≤ n) (x : LatticeQuotient F m n h) :
    latticeQuotientDivAddHom F a r ha h x = latticeQuotientDiv F a r ha h x :=
  rfl

/-- Multiplication of lattice classes commutes with replacing its target denominator by a
shallower one. -/
theorem latticeQuotientProjection_mul
    {m₁ n₁ m₂ n₂ k₁ k₂ : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (hdepth₁ : m₁ + m₂ ≤ k₁) (hk₁₂ : k₁ ≤ k₂)
    (hk₂₁ : k₂ ≤ n₁ + m₂) (hk₂₂ : k₂ ≤ m₁ + n₂)
    (x : LatticeQuotient F m₁ n₁ h₁)
    (y : LatticeQuotient F m₂ n₂ h₂) :
    latticeQuotientProjection F hdepth₁ hk₁₂
        (latticeQuotientMul F h₁ h₂ (hdepth₁.trans hk₁₂)
          hk₂₁ hk₂₂ x y) =
      latticeQuotientMul F h₁ h₂ hdepth₁
        (hk₁₂.trans hk₂₁) (hk₁₂.trans hk₂₂) x y := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h₁ x
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h₂ y
  rfl

/-- Multiplication is unchanged when the first input class is projected to a shallower
denominator for which the product is already well-defined. -/
theorem latticeQuotientMul_projection_left
    {m₁ n₁ n₁' m₂ n₂ k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₁' : n₁ ≤ n₁') (h₂ : m₂ ≤ n₂)
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x : LatticeQuotient F m₁ n₁' (h₁.trans h₁'))
    (y : LatticeQuotient F m₂ n₂ h₂) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂
        (latticeQuotientProjection F h₁ h₁' x) y =
      latticeQuotientMul F (h₁.trans h₁') h₂ hdepth
        (hk₁.trans (add_le_add_left h₁' m₂)) hk₂ x y := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F (h₁.trans h₁') x
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F h₂ y
  rfl

/-- Multiplication is unchanged when the second input class is projected to a shallower
denominator for which the product is already well-defined. -/
theorem latticeQuotientMul_projection_right
    {m₁ n₁ m₂ n₂ n₂' k : ℤ}
    (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂) (h₂' : n₂ ≤ n₂')
    (hdepth : m₁ + m₂ ≤ k)
    (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ m₁ + n₂)
    (x : LatticeQuotient F m₁ n₁ h₁)
    (y : LatticeQuotient F m₂ n₂' (h₂.trans h₂')) :
    latticeQuotientMul F h₁ h₂ hdepth hk₁ hk₂ x
        (latticeQuotientProjection F h₂ h₂' y) =
      latticeQuotientMul F h₁ (h₂.trans h₂') hdepth hk₁
        (hk₂.trans (add_le_add_right h₂' m₁)) x y := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F h₁ x
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F (h₂.trans h₂') y
  rfl

/-- Division by a fixed scalar commutes with denominator projection. -/
theorem latticeQuotientDiv_projection
    (a : F) (r : ℤ) (ha : ord F a = (r : WithTop ℤ))
    {m n₁ n₂ : ℤ} (hm : m ≤ n₁) (h₁₂ : n₁ ≤ n₂)
    (z : LatticeQuotient F m n₂ (hm.trans h₁₂)) :
    latticeQuotientDiv F a r ha hm
        (latticeQuotientProjection F hm h₁₂ z) =
      latticeQuotientProjection F (sub_le_sub_right hm r)
        (sub_le_sub_right h₁₂ r)
        (latticeQuotientDiv F a r ha (hm.trans h₁₂) z) := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F (hm.trans h₁₂) z
  rfl

end QuotientProducts

end LanglandsFirstMainLemma
