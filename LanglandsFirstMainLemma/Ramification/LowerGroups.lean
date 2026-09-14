import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Valuation

/-!
# Lower ramification groups

For a finite Galois extension of nonarchimedean local fields, this file defines the lower
ramification group `G_i` directly from the congruences

`σ x ≡ x (mod 𝔭_K ^ (i + 1))` for every `x ∈ 𝒪_K`.

The construction uses only the normalized order and the elementary Galois API developed for
finite local-field extensions.  In particular, no higher-ramification typeclass or imported
ramification-group theory is assumed.
-/

noncomputable section

namespace LanglandsFirstMainLemma

/-- An integer-valued order lies at depth `n` but not at depth `n + 1` exactly when it equals
`n`.  The `⊤` case is included, so this lemma can be applied directly to `ord` without first
proving that the element is nonzero. -/
theorem withTopInt_le_and_not_succ_le_iff_eq (n : ℤ) (a : WithTop ℤ) :
    ((n : WithTop ℤ) ≤ a ∧ ¬ ((n + 1 : ℤ) : WithTop ℤ) ≤ a) ↔
      a = (n : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
      simp only [WithTop.coe_le_coe, WithTop.coe_eq_coe]
      omega

section LowerRamificationGroups

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  [hGalois : IsGalois F K]

omit [IsGalois F K] in
/-- Applying an `F`-automorphism of `K` to both entries preserves congruence at every integer
depth. -/
theorem galois_congruentAtDepth_iff (σ : Gal(K/F)) (n : ℤ) (x y : K) :
    CongruentAtDepth n (σ x) (σ y) ↔ CongruentAtDepth n x y := by
  simp only [CongruentAtDepth, ← map_sub, ord_galoisConjugate]

/-- The automorphisms carrying one fixed element to itself modulo the depth-`n` lattice form a
subgroup of the Galois group. -/
noncomputable def galoisCongruenceSubgroup (n : ℤ) (x : K) : Subgroup Gal(K/F) where
  carrier := {σ | CongruentAtDepth n (σ x) x}
  one_mem' := by simp [CongruentAtDepth]
  mul_mem' := by
    intro σ τ hσ hτ
    change CongruentAtDepth n (σ x) x at hσ
    change CongruentAtDepth n (τ x) x at hτ
    change CongruentAtDepth n ((σ * τ) x) x
    rw [AlgEquiv.mul_apply]
    exact ((galois_congruentAtDepth_iff F K σ n (τ x) x).2 hτ).trans hσ
  inv_mem' := by
    intro σ hσ
    change CongruentAtDepth n (σ x) x at hσ
    change CongruentAtDepth n (σ⁻¹ x) x
    have h := (galois_congruentAtDepth_iff F K σ.symm n (σ x) x).2 hσ
    simpa using h.symm

omit [IsGalois F K] in
@[simp]
theorem mem_galoisCongruenceSubgroup (σ : Gal(K/F)) (n : ℤ) (x : K) :
    σ ∈ galoisCongruenceSubgroup F K n x ↔ CongruentAtDepth n (σ x) x :=
  Iff.rfl

/-- The restriction of Galois automorphisms to the upper valuation ring, bundled as a group
homomorphism. -/
noncomputable def galoisIntegerAut :
    Gal(K/F) →* RingAut (ringOfIntegers K) where
  toFun := galoisIntegerEquiv F K
  map_one' := by
    apply RingEquiv.ext
    intro x
    ext
    rfl
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    ext
    rfl

/-- The induced action of the Galois group on the upper residue field. -/
noncomputable def galoisResidueAction :
    Gal(K/F) →* RingAut (ResidueField K) :=
  IsLocalRing.ResidueField.mapAut.comp (galoisIntegerAut F K)

omit [IsGalois F K] in
@[simp]
theorem galoisResidueAction_residue (σ : Gal(K/F)) (x : ringOfIntegers K) :
    galoisResidueAction F K σ (residueMap K x) =
      residueMap K (galoisIntegerEquiv F K σ x) :=
  rfl

include hGalois

/-- The lower ramification group in integer numbering.  The manuscript uses this definition for
`i ≥ -1`; defining the same formula for every integer makes the antitone filtration easier to
use and agrees with the full Galois group at every `i ≤ -1`. -/
noncomputable def lowerRamificationGroup (i : ℤ) : Subgroup Gal(K/F) :=
  ⨅ x : ringOfIntegers K, galoisCongruenceSubgroup F K (i + 1) (x : K)

omit hGalois

omit hGalois in
/-- Exact membership in `G_i`, in the manuscript's congruence notation. -/
@[simp]
theorem mem_lowerRamificationGroup (σ : Gal(K/F)) (i : ℤ) :
    σ ∈ lowerRamificationGroup F K i ↔
      ∀ x : ringOfIntegers K, CongruentAtDepth (i + 1) (σ (x : K)) (x : K) := by
  simp [lowerRamificationGroup]

/-- Exact membership in `G_i`, expanded as the normalized valuation inequality. -/
theorem mem_lowerRamificationGroup_iff_ord (σ : Gal(K/F)) (i : ℤ) :
    σ ∈ lowerRamificationGroup F K i ↔
      ∀ x : ringOfIntegers K,
        ((i + 1 : ℤ) : WithTop ℤ) ≤ ord K (σ (x : K) - (x : K)) := by
  simp only [mem_lowerRamificationGroup, CongruentAtDepth]

/-- Exact membership in `G_i`, expressed using the project's integer-indexed valuation lattice. -/
theorem mem_lowerRamificationGroup_iff_lattice (σ : Gal(K/F)) (i : ℤ) :
    σ ∈ lowerRamificationGroup F K i ↔
      ∀ x : ringOfIntegers K, σ (x : K) - (x : K) ∈ lattice K (i + 1) := by
  simp only [mem_lowerRamificationGroup, congruentAtDepth_iff_sub_mem_lattice]

/-- The zeroth lower group is exactly inertia: the kernel of the induced action on the upper
residue field. -/
theorem lowerRamificationGroup_zero_eq_ker_galoisResidueAction :
    lowerRamificationGroup F K 0 = MonoidHom.ker (galoisResidueAction F K) := by
  ext σ
  rw [mem_lowerRamificationGroup, MonoidHom.mem_ker]
  constructor
  · intro hσ
    apply RingEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := residueMap_surjective K z
    change residueMap K (galoisIntegerEquiv F K σ x) = residueMap K x
    rw [residueMap_eq_residueMap_iff]
    exact (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1 (hσ x)
  · intro hσ x
    have heq := (RingEquiv.ext_iff.mp hσ) (residueMap K x)
    change residueMap K (galoisIntegerEquiv F K σ x) = residueMap K x at heq
    rw [residueMap_eq_residueMap_iff] at heq
    exact (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).2 heq

/-- Lower ramification groups decrease as the lower index increases. -/
theorem lowerRamificationGroup_antitone :
    Antitone (lowerRamificationGroup F K) := by
  intro i j hij σ hσ
  rw [mem_lowerRamificationGroup] at hσ ⊢
  intro x
  exact (hσ x).mono (by omega)

/-- Elementwise form of the decreasing-filtration law. -/
theorem lowerRamificationGroup_mono {i j : ℤ} (hij : i ≤ j) :
    lowerRamificationGroup F K j ≤ lowerRamificationGroup F K i :=
  lowerRamificationGroup_antitone F K hij

/-- Each successor lower group is contained in the preceding group. -/
theorem lowerRamificationGroup_succ_le (i : ℤ) :
    lowerRamificationGroup F K (i + 1) ≤ lowerRamificationGroup F K i :=
  lowerRamificationGroup_mono F K (by omega)

omit [IsGalois F K] in
private theorem integral_galois_congruentAtDepth_zero
    (σ : Gal(K/F)) (x : ringOfIntegers K) :
    CongruentAtDepth 0 (σ (x : K)) (x : K) := by
  rw [CongruentAtDepth]
  have hx : (0 : WithTop ℤ) ≤ ord K (x : K) :=
    (ord_nonneg_iff_mem_integer K (x : K)).2 x.prop
  have hσx : (0 : WithTop ℤ) ≤ ord K (σ (x : K)) := by
    simpa only [ord_galoisConjugate] using hx
  exact (le_min hσx hx).trans (ord_sub K (σ (x : K)) (x : K))

/-- At every index at most `-1`, the lower ramification group is the full Galois group. -/
theorem lowerRamificationGroup_eq_top_of_le_neg_one {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup F K i = ⊤ := by
  apply eq_top_iff.mpr
  intro σ _
  rw [mem_lowerRamificationGroup]
  intro x
  exact (integral_galois_congruentAtDepth_zero F K σ x).mono (by omega)

/-- The manuscript's boundary identity `G_{-1} = G`. -/
@[simp]
theorem lowerRamificationGroup_neg_one :
    lowerRamificationGroup F K (-1) = ⊤ :=
  lowerRamificationGroup_eq_top_of_le_neg_one F K (le_rfl)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K] in
private theorem exists_integral_moved
    (σ : Gal(K/F)) (hσ : σ ≠ 1) :
    ∃ x : K, x ∈ ringOfIntegers K ∧ σ x ≠ x := by
  have hmoved : ∃ y : K, σ y ≠ y := by
    by_contra h
    apply hσ
    apply AlgEquiv.ext
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hmoved
  rcases (ValuativeRel.valuation K).valuationSubring.mem_or_inv_mem y with hyint | hyinv
  · exact ⟨y, hyint, hy⟩
  · refine ⟨y⁻¹, hyinv, ?_⟩
    intro hinv
    apply hy
    exact inv_injective (by
      calc
        (σ y)⁻¹ = σ (y⁻¹) := (map_inv₀ σ y).symm
        _ = y⁻¹ := hinv)

private theorem exists_depth_not_mem_lowerRamificationGroup
    (σ : Gal(K/F)) (hσ : σ ≠ 1) :
    ∃ i : ℤ, σ ∉ lowerRamificationGroup F K i := by
  obtain ⟨x, hxint, hxmove⟩ := exists_integral_moved F K σ hσ
  have hsub : σ x - x ≠ 0 := sub_ne_zero.mpr hxmove
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff K).2 hsub)
  refine ⟨k, ?_⟩
  rw [mem_lowerRamificationGroup]
  intro hmem
  have hx := hmem ⟨x, hxint⟩
  rw [CongruentAtDepth, ← hk] at hx
  simp only [WithTop.coe_le_coe] at hx
  omega

/-- The lower filtration is eventually trivial.  This is proved from finiteness of the Galois
group and the defining congruences: every nonidentity automorphism moves an integral element,
and therefore exits the filtration at a finite depth.  No higher-ramification theorem is used. -/
theorem exists_nonnegative_lowerRamificationGroup_eq_bot :
    ∃ i : ℤ, 0 ≤ i ∧ lowerRamificationGroup F K i = ⊥ := by
  classical
  have hexit : ∀ σ : Gal(K/F), σ ≠ 1 →
      ∃ i : ℤ, σ ∉ lowerRamificationGroup F K i :=
    fun σ hσ => exists_depth_not_mem_lowerRamificationGroup F K σ hσ
  let d : Gal(K/F) → ℤ := fun σ => if h : σ = 1 then 0 else (hexit σ h).choose
  have hd {σ : Gal(K/F)} (hσ : σ ≠ 1) :
      σ ∉ lowerRamificationGroup F K (d σ) := by
    simp only [d, dif_neg hσ]
    exact (hexit σ hσ).choose_spec
  let N : ℤ := ∑ σ : Gal(K/F), max 0 (d σ)
  refine ⟨N, ?_, le_antisymm ?_ bot_le⟩
  · dsimp only [N]
    exact Finset.sum_nonneg fun σ _ => le_max_left 0 (d σ)
  · intro σ hσN
    have heq : σ = 1 := by
      by_contra hne
      apply hd hne
      apply (lowerRamificationGroup_antitone F K ?_) hσN
      have hpart : max 0 (d σ) ≤ N := by
        dsimp only [N]
        apply Finset.single_le_sum (fun τ _ => le_max_left 0 (d τ))
        exact Finset.mem_univ σ
      exact (le_max_right 0 (d σ)).trans hpart
    simp [heq]

/-- Once one lower ramification group is trivial, every deeper group is trivial. -/
theorem lowerRamificationGroup_eq_bot_of_ge
    {i j : ℤ} (hi : lowerRamificationGroup F K i = ⊥) (hij : i ≤ j) :
    lowerRamificationGroup F K j = ⊥ := by
  apply le_antisymm
  · rw [← hi]
    exact lowerRamificationGroup_antitone F K hij
  · exact bot_le

/-- Eventual triviality in threshold form, ready for construction of a last ramification break. -/
theorem lowerRamificationGroup_eventually_bot :
    ∃ i : ℤ, 0 ≤ i ∧ ∀ j : ℤ, i ≤ j → lowerRamificationGroup F K j = ⊥ := by
  obtain ⟨i, hi0, hi⟩ := exists_nonnegative_lowerRamificationGroup_eq_bot F K
  exact ⟨i, hi0, fun j hij => lowerRamificationGroup_eq_bot_of_ge F K hi hij⟩

/-- Every lower ramification group is normal in the full Galois group. -/
theorem lowerRamificationGroup_normal (i : ℤ) :
    (lowerRamificationGroup F K i).Normal := by
  constructor
  intro σ hσ τ
  rw [mem_lowerRamificationGroup] at hσ ⊢
  intro x
  let y : ringOfIntegers K := galoisIntegerEquiv F K τ.symm x
  have hy := hσ y
  have hτ := (galois_congruentAtDepth_iff F K τ (i + 1)
    (σ (y : K)) (y : K)).2 hy
  simpa [y, mul_assoc] using hτ

noncomputable instance lowerRamificationGroup.instNormal (i : ℤ) :
    (lowerRamificationGroup F K i).Normal :=
  lowerRamificationGroup_normal F K i

omit [IsGalois F K] in
/-- The integer lower group is contained in the congruence stabilizer of every integral test
element.  Taking the test element to be a uniformizer gives the safe, hypothesis-free direction
of the usual uniformizer criterion. -/
theorem lowerRamificationGroup_le_galoisCongruenceSubgroup
    (i : ℤ) (x : ringOfIntegers K) :
    lowerRamificationGroup F K i ≤
      galoisCongruenceSubgroup F K (i + 1) (x : K) :=
  iInf_le _ x

/-- Membership in `G_i` forces the expected congruence on every chosen uniformizer. -/
theorem lowerRamificationGroup_uniformizer
    {i : ℤ} {σ : Gal(K/F)} {π : K}
    (hσ : σ ∈ lowerRamificationGroup F K i)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    CongruentAtDepth (i + 1) (σ π) π := by
  have hπint : π ∈ ringOfIntegers K := by
    apply (ord_nonneg_iff_mem_integer K π).1
    rw [ord_uniformizer K hπ]
    simp
  exact (mem_lowerRamificationGroup F K σ i).1 hσ ⟨π, hπint⟩

/-- Valuation form of the necessary uniformizer condition for membership in `G_i`. -/
theorem lowerRamificationGroup_uniformizer_ord
    {i : ℤ} {σ : Gal(K/F)} {π : K}
    (hσ : σ ∈ lowerRamificationGroup F K i)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    ((i + 1 : ℤ) : WithTop ℤ) ≤ ord K (σ π - π) :=
  lowerRamificationGroup_uniformizer F K hσ hπ

/-- The uniformizer displacement of an element of `G_i`, retained as an element of the exact
numerator lattice `𝔭_K^{i+1}` rather than coerced immediately to the field.  The chosen
uniformizer is part of this coordinate. -/
noncomputable def lowerRamificationDisplacement
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : lattice K (i + 1) :=
  ⟨(σ : Gal(K/F)) π - π, (congruentAtDepth_iff_sub_mem_lattice K (i + 1) _ _).1
    (lowerRamificationGroup_uniformizer F K σ.prop hπ)⟩

@[simp]
theorem coe_lowerRamificationDisplacement
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    (lowerRamificationDisplacement F K σ π hπ : K) =
      (σ : Gal(K/F)) π - π :=
  rfl

/-- Divide the displacement by the indicated uniformizer power and retain the result as an
integral element.  This is the representative used by the positive-depth ramification map; its
integrality follows directly from membership in `G_i`. -/
noncomputable def lowerRamificationNormalizedDisplacement
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : lattice K 0 := by
  refine ⟨((σ : Gal(K/F)) π - π) / π ^ (i + 1), ?_⟩
  apply (div_mem_lattice_iff K (π ^ (i + 1))
    ((σ : Gal(K/F)) π - π) (i + 1) 0 ?_).2
  · simpa using (lowerRamificationDisplacement F K σ π hπ).prop
  · rw [ord_zpow, ord_uniformizer K hπ]
    cases i + 1 with
    | ofNat n => simp
    | negSucc n =>
        rw [negSucc_zsmul]
        norm_num [Int.negSucc_eq]

@[simp]
theorem coe_lowerRamificationNormalizedDisplacement
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    (lowerRamificationNormalizedDisplacement F K σ π hπ : K) =
      ((σ : Gal(K/F)) π - π) / π ^ (i + 1) :=
  rfl

/-- At depth zero, the tame ramification coordinate starts from the integral ratio
`σ(π) / π`.  It is deliberately separate from the additive displacement used at positive
depth. -/
noncomputable def lowerRamificationTameRatio
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : lattice K 0 := by
  refine ⟨(σ : Gal(K/F)) π / π, ?_⟩
  apply (div_mem_lattice_iff K π ((σ : Gal(K/F)) π) 1 0
    (ord_uniformizer K hπ)).2
  rw [mem_lattice, ord_galoisConjugate, ord_uniformizer K hπ]
  simp

@[simp]
theorem coe_lowerRamificationTameRatio
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    (lowerRamificationTameRatio F K σ π hπ : K) =
      (σ : Gal(K/F)) π / π :=
  rfl

/-- The tame ratio has order zero, so its residue class is nonzero. -/
theorem ord_lowerRamificationTameRatio_eq_zero
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    ord K (lowerRamificationTameRatio F K σ π hπ : K) = 0 := by
  rw [coe_lowerRamificationTameRatio, ord_div, ord_galoisConjugate,
    ord_uniformizer K hπ]
  simp

/-- The multiplicative ramification coordinate at depth zero, first retained as its residue
class. -/
noncomputable def lowerRamificationTameResidue
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : ResidueField K :=
  reduce K (lowerRamificationTameRatio F K σ π hπ : K)
    (lowerRamificationTameRatio F K σ π hπ).prop

/-- The tame residue coordinate is nonzero. -/
theorem lowerRamificationTameResidue_ne_zero
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    lowerRamificationTameResidue F K σ π hπ ≠ 0 := by
  intro hzero
  let z := lowerRamificationTameRatio F K σ π hπ
  have hzero' : reduce K (z : K) z.prop = 0 := hzero
  have hcong : CongruentAtDepth 1 (z : K) 0 := by
    rw [← reduce_eq_reduce_iff K z.prop (lattice K 0).zero_mem]
    have hreduce0 : reduce K 0 (lattice K 0).zero_mem = 0 := rfl
    exact hzero'.trans hreduce0.symm
  rw [CongruentAtDepth, sub_zero,
    ord_lowerRamificationTameRatio_eq_zero F K σ π hπ] at hcong
  exact (not_le_of_gt (show (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ) by norm_num)) hcong

/-- The tame residue coordinate as an element of `k_Kˣ`, matching the multiplicative target
of the manuscript's depth-zero ramification map. -/
noncomputable def lowerRamificationTameResidueUnit
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : (ResidueField K)ˣ :=
  Units.mk0 (lowerRamificationTameResidue F K σ π hπ)
    (lowerRamificationTameResidue_ne_zero F K σ π hπ)

@[simp]
theorem coe_lowerRamificationTameResidueUnit
    (σ : lowerRamificationGroup F K 0) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    (lowerRamificationTameResidueUnit F K σ π hπ : ResidueField K) =
      lowerRamificationTameResidue F K σ π hπ :=
  rfl

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K] hGalois in
/-- Integer powers of a uniformizer have the corresponding exact normalized order. -/
theorem ord_uniformizer_zpow {π : K}
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) (n : ℤ) :
    ord K (π ^ n) = (n : WithTop ℤ) := by
  rw [ord_zpow, ord_uniformizer K hπ]
  cases n with
  | ofNat m => simp
  | negSucc m =>
      rw [negSucc_zsmul]
      norm_num [Int.negSucc_eq]

/-- If the upper valuation ring is generated over the lower valuation ring by one integral
element `π`, then testing the defining congruence on `π` alone is sufficient.  For a totally
ramified extension this is the algebraic interface through which a uniformizer gives the usual
uniformizer criterion; the generation hypothesis is kept explicit because the criterion is
false for a general (for example unramified) extension. -/
theorem mem_lowerRamificationGroup_iff_of_adjoin_eq_top
    {i : ℤ} {σ : Gal(K/F)} (π : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    σ ∈ lowerRamificationGroup F K i ↔
      CongruentAtDepth (i + 1) (σ (π : K)) (π : K) := by
  constructor
  · intro hσ
    exact (mem_lowerRamificationGroup F K σ i).1 hσ π
  · intro hπ
    rw [mem_lowerRamificationGroup]
    intro x
    have hx : x ∈ Algebra.adjoin (ringOfIntegers F)
        ({π} : Set (ringOfIntegers K)) := by
      rw [hgen]
      trivial
    exact Algebra.adjoin_induction (p := fun (z : ringOfIntegers K) _ =>
        CongruentAtDepth (i + 1) (σ (z : K)) (z : K))
      (fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact hπ)
      (fun r => by
        have heq : σ ((algebraMap (ringOfIntegers F) (ringOfIntegers K) r :
            ringOfIntegers K) : K) =
            ((algebraMap (ringOfIntegers F) (ringOfIntegers K) r :
              ringOfIntegers K) : K) := by
          change σ (algebraMap F K (r : F)) = algebraMap F K (r : F)
          exact σ.commutes (r : F)
        rw [heq]
        exact CongruentAtDepth.refl _)
      (fun a b _ _ ha hb => by
        simpa only [map_add, Subring.coe_add] using ha.add hb)
      (fun a b _ _ ha hb => by
        have hσa : (0 : WithTop ℤ) ≤ ord K (σ (a : K)) :=
          (ord_nonneg_iff_mem_integer K _).2
            ((galoisConjugate_mem_ringOfIntegers_iff F K σ (a : K)).2 a.prop)
        have hb0 : (0 : WithTop ℤ) ≤ ord K (b : K) :=
          (ord_nonneg_iff_mem_integer K _).2 b.prop
        simpa only [map_mul, Subring.coe_mul] using ha.mul hσa hb0 hb)
      hx

/-- Valuation form of the one-generator membership criterion. -/
theorem mem_lowerRamificationGroup_iff_ord_of_adjoin_eq_top
    {i : ℤ} {σ : Gal(K/F)} (π : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    σ ∈ lowerRamificationGroup F K i ↔
      ((i + 1 : ℤ) : WithTop ℤ) ≤ ord K (σ (π : K) - (π : K)) :=
  mem_lowerRamificationGroup_iff_of_adjoin_eq_top F K π hgen

/-- Under the same explicit one-generator hypothesis, the exact shell `G_i \ G_{i+1}` is
detected by equality of the displacement order with `i + 1`.  When the generator is a
uniformizer of a totally ramified extension, this is the uniformizer-difference formula used by
the different and ramification-map constructions. -/
theorem lowerRamificationGroup_mem_and_not_mem_succ_iff_ord_sub_eq
    {i : ℤ} {σ : Gal(K/F)} (π : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    σ ∈ lowerRamificationGroup F K i ∧
        σ ∉ lowerRamificationGroup F K (i + 1) ↔
      ord K (σ (π : K) - (π : K)) = ((i + 1 : ℤ) : WithTop ℤ) := by
  rw [mem_lowerRamificationGroup_iff_of_adjoin_eq_top F K π hgen,
    mem_lowerRamificationGroup_iff_of_adjoin_eq_top F K π hgen]
  rw [CongruentAtDepth, CongruentAtDepth]
  exact withTopInt_le_and_not_succ_le_iff_eq (i + 1)
    (ord K (σ (π : K) - (π : K)))

/-- On the exact shell `G_i \ G_{i+1}`, the normalized displacement has order zero. -/
theorem ord_lowerRamificationNormalizedDisplacement_eq_zero
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (hσ : (σ : Gal(K/F)) ∉ lowerRamificationGroup F K (i + 1)) :
    ord K (lowerRamificationNormalizedDisplacement F K σ (π : K) hπ : K) = 0 := by
  have hshell : ord K ((σ : Gal(K/F)) (π : K) - (π : K)) =
      ((i + 1 : ℤ) : WithTop ℤ) :=
    (lowerRamificationGroup_mem_and_not_mem_succ_iff_ord_sub_eq F K π hgen).1
      ⟨σ.prop, hσ⟩
  rw [coe_lowerRamificationNormalizedDisplacement, ord_div, hshell,
    ord_uniformizer_zpow K hπ]
  simp

/-- The residue class of the normalized positive-depth displacement.  It is a quotient class in
`k_K`; the definition makes no choice of a field representative beyond the displayed chosen
uniformizer coordinate. -/
noncomputable def lowerRamificationResidueDisplacement
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : ResidueField K :=
  reduce K (lowerRamificationNormalizedDisplacement F K σ π hπ : K)
    (lowerRamificationNormalizedDisplacement F K σ π hπ).prop

/-- The residual displacement of an exact-shell element is nonzero. -/
theorem lowerRamificationResidueDisplacement_ne_zero
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (hσ : (σ : Gal(K/F)) ∉ lowerRamificationGroup F K (i + 1)) :
    lowerRamificationResidueDisplacement F K σ (π : K) hπ ≠ 0 := by
  intro hzero
  let z := lowerRamificationNormalizedDisplacement F K σ (π : K) hπ
  have hzord : ord K (z : K) = 0 :=
    ord_lowerRamificationNormalizedDisplacement_eq_zero F K σ π hπ hgen hσ
  have hzero' : reduce K (z : K) z.prop = 0 := by
    exact hzero
  have hcong : CongruentAtDepth 1 (z : K) 0 := by
    rw [← reduce_eq_reduce_iff K z.prop (lattice K 0).zero_mem]
    have hreduce0 : reduce K 0 (lattice K 0).zero_mem = 0 := rfl
    exact hzero'.trans hreduce0.symm
  rw [CongruentAtDepth, sub_zero, hzord] at hcong
  exact (not_le_of_gt (show (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ) by norm_num)) hcong

/-- Under the one-generator hypothesis, vanishing of the normalized residual displacement has
exactly the next lower group as its kernel set.  This is the representative-free kernel
interface used when the positive-depth ramification map is bundled downstream. -/
@[simp]
theorem lowerRamificationResidueDisplacement_eq_zero_iff
    {i : ℤ} (σ : lowerRamificationGroup F K i) (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    lowerRamificationResidueDisplacement F K σ (π : K) hπ = 0 ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K (i + 1) := by
  let z := lowerRamificationNormalizedDisplacement F K σ (π : K) hπ
  change reduce K (z : K) z.prop = 0 ↔ _
  change residueMap K
      ⟨(z : K), (mem_lattice_zero_iff K).1 z.prop⟩ = 0 ↔ _
  rw [residueMap_eq_zero_iff]
  change (((σ : Gal(K/F)) (π : K) - (π : K)) /
      (π : K) ^ (i + 1)) ∈ lattice K 1 ↔ _
  rw [div_mem_lattice_iff K ((π : K) ^ (i + 1))
    ((σ : Gal(K/F)) (π : K) - (π : K)) (i + 1) 1
    (ord_uniformizer_zpow K hπ (i + 1))]
  rw [mem_lowerRamificationGroup_iff_of_adjoin_eq_top F K π hgen]
  exact (congruentAtDepth_iff_sub_mem_lattice K ((i + 1) + 1)
    ((σ : Gal(K/F)) (π : K)) (π : K)).symm

/-- Under the one-generator hypothesis, the tame residue coordinate equals one exactly on
`G₁`.  This is the kernel-set interface for the eventual multiplicative ramification map. -/
theorem lowerRamificationTameResidue_eq_one_iff
    (σ : lowerRamificationGroup F K 0) (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    lowerRamificationTameResidue F K σ (π : K) hπ = 1 ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K 1 := by
  let z := lowerRamificationTameRatio F K σ (π : K) hπ
  change residueMap K
      ⟨(z : K), (mem_lattice_zero_iff K).1 z.prop⟩ = residueMap K 1 ↔ _
  rw [residueMap_eq_residueMap_iff]
  change ((σ : Gal(K/F)) (π : K) / (π : K) - 1) ∈ lattice K 1 ↔ _
  rw [div_sub_one hπ.ne_zero]
  rw [div_mem_lattice_iff K (π : K)
    ((σ : Gal(K/F)) (π : K) - (π : K)) 1 1 (ord_uniformizer K hπ)]
  rw [mem_lowerRamificationGroup_iff_of_adjoin_eq_top F K π hgen]
  exact (congruentAtDepth_iff_sub_mem_lattice K (1 + 1)
    ((σ : Gal(K/F)) (π : K)) (π : K)).symm

/-- The unit-valued tame coordinate has exactly `G₁` as its kernel set. -/
@[simp]
theorem lowerRamificationTameResidueUnit_eq_one_iff
    (σ : lowerRamificationGroup F K 0) (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    lowerRamificationTameResidueUnit F K σ (π : K) hπ = 1 ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K 1 := by
  rw [← lowerRamificationTameResidue_eq_one_iff F K σ π hπ hgen]
  exact Units.ext_iff

/-- For `i ≤ j`, this is `G_j` regarded as a subgroup of `G_i`.  Keeping the certified
inclusion in the definition makes later quotients `G_i / G_j` honest quotient groups. -/
noncomputable def lowerRamificationGroupInside {i j : ℤ} (hij : i ≤ j) :
    Subgroup (lowerRamificationGroup F K i) :=
  (Subgroup.inclusion (lowerRamificationGroup_antitone F K hij)).range

@[simp]
theorem mem_lowerRamificationGroupInside {i j : ℤ} (hij : i ≤ j)
    (σ : lowerRamificationGroup F K i) :
    σ ∈ lowerRamificationGroupInside F K hij ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K j := by
  constructor
  · rintro ⟨τ, hτ⟩
    rw [← congrArg Subtype.val hτ]
    exact τ.prop
  · intro hσ
    exact ⟨⟨σ, hσ⟩, rfl⟩

/-- Mapping the certified denominator back to the full Galois group recovers exactly `G_j`. -/
@[simp]
theorem map_lowerRamificationGroupInside_subtype {i j : ℤ} (hij : i ≤ j) :
    (lowerRamificationGroupInside F K hij).map
      (lowerRamificationGroup F K i).subtype = lowerRamificationGroup F K j := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (mem_lowerRamificationGroupInside F K hij τ).1 hτ
  · intro hσ
    let τ : lowerRamificationGroup F K i :=
      ⟨σ, lowerRamificationGroup_antitone F K hij hσ⟩
    exact ⟨τ, (mem_lowerRamificationGroupInside F K hij τ).2 hσ, rfl⟩

noncomputable instance lowerRamificationGroupInside.instNormal
    {i j : ℤ} (hij : i ≤ j) :
    (lowerRamificationGroupInside F K hij).Normal := by
  constructor
  intro σ hσ τ
  apply (mem_lowerRamificationGroupInside F K hij _).2
  have hconj := (lowerRamificationGroup_normal F K j).conj_mem
    (σ : Gal(K/F)) ((mem_lowerRamificationGroupInside F K hij σ).1 hσ)
    (τ : Gal(K/F))
  simpa using hconj

/-- The finite lower-ramification quotient `G_i / G_j`, with its denominator inclusion
certified by `i ≤ j`. -/
abbrev LowerRamificationQuotient {i j : ℤ} (hij : i ≤ j) :=
  lowerRamificationGroup F K i ⧸ lowerRamificationGroupInside F K hij

/-- A specified finite enumeration of the honest quotient `G_i / G_j`. -/
@[reducible]
noncomputable def lowerRamificationQuotientFintype {i j : ℤ} (hij : i ≤ j) :
    Fintype (LowerRamificationQuotient F K hij) :=
  Fintype.ofFinite _

/-- The cardinality of `G_i/G_j` is the index of its certified denominator in `G_i`. -/
theorem lowerRamificationQuotient_natCard {i j : ℤ} (hij : i ≤ j) :
    Nat.card (LowerRamificationQuotient F K hij) =
      (lowerRamificationGroupInside F K hij).index :=
  (lowerRamificationGroupInside F K hij).index_eq_card.symm

/-- The canonical homomorphism from `G_i` to the honest quotient `G_i / G_j`. -/
noncomputable def lowerRamificationQuotientMk {i j : ℤ} (hij : i ≤ j) :
    lowerRamificationGroup F K i →* LowerRamificationQuotient F K hij :=
  QuotientGroup.mk' (lowerRamificationGroupInside F K hij)

@[simp]
theorem lowerRamificationQuotientMk_apply {i j : ℤ} (hij : i ≤ j)
    (σ : lowerRamificationGroup F K i) :
    lowerRamificationQuotientMk F K hij σ = (σ : LowerRamificationQuotient F K hij) :=
  rfl

/-- The quotient map has exactly `G_j` (inside `G_i`) as its kernel. -/
theorem lowerRamificationQuotientMk_ker {i j : ℤ} (hij : i ≤ j) :
    (lowerRamificationQuotientMk F K hij).ker =
      lowerRamificationGroupInside F K hij :=
  QuotientGroup.ker_mk' _

@[simp]
theorem lowerRamificationQuotientMk_eq_one_iff {i j : ℤ} (hij : i ≤ j)
    (σ : lowerRamificationGroup F K i) :
    lowerRamificationQuotientMk F K hij σ = 1 ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K j := by
  rw [← MonoidHom.mem_ker, lowerRamificationQuotientMk_ker]
  exact mem_lowerRamificationGroupInside F K hij σ

/-- The canonical quotient map is surjective. -/
theorem lowerRamificationQuotientMk_surjective {i j : ℤ} (hij : i ≤ j) :
    Function.Surjective (lowerRamificationQuotientMk F K hij) :=
  QuotientGroup.mk'_surjective (lowerRamificationGroupInside F K hij)

/-- Equality of two quotient classes is exactly membership of their quotient in the certified
denominator `G_j`. -/
theorem lowerRamificationQuotientMk_eq_iff {i j : ℤ} (hij : i ≤ j)
    (σ τ : lowerRamificationGroup F K i) :
    lowerRamificationQuotientMk F K hij σ =
        lowerRamificationQuotientMk F K hij τ ↔
      ((σ / τ : lowerRamificationGroup F K i) : Gal(K/F)) ∈
        lowerRamificationGroup F K j := by
  rw [lowerRamificationQuotientMk_apply, lowerRamificationQuotientMk_apply,
    QuotientGroup.eq_iff_div_mem]
  exact mem_lowerRamificationGroupInside F K hij (σ / τ)

/-- The successive lower ramification quotient `G_i / G_{i+1}`. -/
abbrev LowerRamificationGraded (i : ℤ) :=
  LowerRamificationQuotient F K (show i ≤ i + 1 by omega)

/-- Canonical projection to the successive quotient `G_i / G_{i+1}`. -/
noncomputable def lowerRamificationGradedMk (i : ℤ) :
    lowerRamificationGroup F K i →* LowerRamificationGraded F K i :=
  lowerRamificationQuotientMk F K (show i ≤ i + 1 by omega)

@[simp]
theorem lowerRamificationGradedMk_eq_one_iff (i : ℤ)
    (σ : lowerRamificationGroup F K i) :
    lowerRamificationGradedMk F K i σ = 1 ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K (i + 1) :=
  lowerRamificationQuotientMk_eq_one_iff F K (show i ≤ i + 1 by omega) σ

/-- Lower numbering at a real index uses the ceiling, exactly as in the manuscript. -/
noncomputable def lowerRamificationGroupReal (u : ℝ) : Subgroup Gal(K/F) :=
  lowerRamificationGroup F K ⌈u⌉

@[simp]
theorem mem_lowerRamificationGroupReal (σ : Gal(K/F)) (u : ℝ) :
    σ ∈ lowerRamificationGroupReal F K u ↔
      ∀ x : ringOfIntegers K,
        CongruentAtDepth (⌈u⌉ + 1) (σ (x : K)) (x : K) := by
  simp [lowerRamificationGroupReal]

/-- The real-indexed lower filtration is decreasing. -/
theorem lowerRamificationGroupReal_antitone :
    Antitone (lowerRamificationGroupReal F K) := by
  intro u v huv
  exact lowerRamificationGroup_antitone F K (Int.ceil_mono huv)

omit [IsGalois F K] in
/-- Real lower numbering agrees with integer lower numbering at integer arguments. -/
@[simp]
theorem lowerRamificationGroupReal_intCast (i : ℤ) :
    lowerRamificationGroupReal F K (i : ℝ) = lowerRamificationGroup F K i := by
  simp [lowerRamificationGroupReal]

/-- The real-indexed filtration has the same `-1` boundary as the integer filtration. -/
@[simp]
theorem lowerRamificationGroupReal_neg_one :
    lowerRamificationGroupReal F K (-1) = ⊤ := by
  rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num,
    lowerRamificationGroupReal_intCast]
  exact lowerRamificationGroup_neg_one F K

end LowerRamificationGroups

end LanglandsFirstMainLemma
