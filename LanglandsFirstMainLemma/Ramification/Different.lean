import LanglandsFirstMainLemma.Ramification.PrimeCyclicExtension
import LanglandsFirstMainLemma.Ramification.LowerGroups

/-!
# The different exponent

For a nonidentity Galois automorphism `σ`, its contribution to Hilbert's different formula is
the least nonnegative `n` for which `σ ∉ Gₙ`.  With the project's convention

`Gᵢ = {σ | ord (σ x - x) ≥ i + 1 for every integral x}`,

this contribution is exactly `ord (σ π - π)` whenever the chosen integral uniformizer `π`
generates the upper valuation ring over the lower one.  The different exponent is the sum of
these contributions over the finite set of nonidentity automorphisms.  Thus it has the
manuscript's normalized upper valuation `v_K(𝔇_{K/F})`; the identity is deliberately excluded,
since its displacement is zero and has order `⊤`.

For a cyclic extension of prime degree with lower break `t`, every nonidentity automorphism lies
in the exact shell `Gₜ \ Gₜ₊₁`.  Each contribution is therefore `t + 1`, and the number of
contributions is `[K : F] - 1`.
-/

noncomputable section

open scoped BigOperators

namespace LanglandsFirstMainLemma

section NonidentityAutomorphisms

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [Module.Finite F K] [IsGalois F K]

/-- The finite indexing set in Hilbert's different formula.  The identity is excluded. -/
noncomputable def nonidentityGaloisAutomorphisms : Finset Gal(K/F) := by
  classical
  exact (Finset.univ : Finset Gal(K/F)).erase 1

omit [IsGalois F K] in
@[simp]
theorem mem_nonidentityGaloisAutomorphisms {σ : Gal(K/F)} :
    σ ∈ nonidentityGaloisAutomorphisms F K ↔ σ ≠ 1 := by
  classical
  simp [nonidentityGaloisAutomorphisms]

end NonidentityAutomorphisms

section GeneralGalois

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
  [IsGalois F K]

omit [IsGalois F K] in
private theorem exists_not_mem_lowerRamificationGroup_nat
    (σ : Gal(K/F)) (hσ : σ ≠ 1) :
    ∃ n : ℕ, σ ∉ lowerRamificationGroup F K (n : ℤ) := by
  obtain ⟨i, hi0, hi⟩ := exists_nonnegative_lowerRamificationGroup_eq_bot F K
  refine ⟨i.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hi0, hi, Subgroup.mem_bot]
  exact hσ

/-- The contribution of `σ` to the normalized different exponent: for `σ ≠ 1`, this is the
least `n ≥ 0` such that `σ ∉ Gₙ`.  The identity is assigned zero but never enters the sum. -/
noncomputable def lowerDifferentSummand (σ : Gal(K/F)) : ℕ := by
  classical
  exact if hσ : σ = 1 then 0
    else Nat.find (exists_not_mem_lowerRamificationGroup_nat F K σ hσ)

omit [IsGalois F K] in
@[simp]
theorem lowerDifferentSummand_one : lowerDifferentSummand F K 1 = 0 := by
  simp [lowerDifferentSummand]

omit [IsGalois F K] in
/-- A nonidentity automorphism exits the lower filtration at its different summand. -/
theorem lowerDifferentSummand_not_mem
    {σ : Gal(K/F)} (hσ : σ ≠ 1) :
    σ ∉ lowerRamificationGroup F K (lowerDifferentSummand F K σ : ℤ) := by
  classical
  rw [lowerDifferentSummand, dif_neg hσ]
  exact Nat.find_spec (exists_not_mem_lowerRamificationGroup_nat F K σ hσ)

omit [IsGalois F K] in
/-- Before its different summand, a nonidentity automorphism still belongs to the lower
filtration. -/
theorem lowerDifferentSummand_mem_of_lt
    {σ : Gal(K/F)} (hσ : σ ≠ 1) {n : ℕ}
    (hn : n < lowerDifferentSummand F K σ) :
    σ ∈ lowerRamificationGroup F K (n : ℤ) := by
  classical
  rw [lowerDifferentSummand, dif_neg hσ] at hn
  exact not_not.mp
    (Nat.find_min (exists_not_mem_lowerRamificationGroup_nat F K σ hσ) hn)

/-- The manuscript-normalized different exponent `v_K(𝔇_{K/F})`, in its numerical Hilbert-sum
form.  It is data derived from the lower filtration, not a typeclass field. -/
noncomputable def differentExponent : ℕ :=
  ∑ σ ∈ nonidentityGaloisAutomorphisms F K, lowerDifferentSummand F K σ

omit [IsGalois F K] in
/-- If an integral uniformizer generates the upper valuation ring, the filtration contribution
of every nonidentity automorphism is exactly its normalized uniformizer-displacement order.
The explicit generator hypothesis is the converse-uniformizer criterion used in the proof. -/
theorem ord_galois_uniformizer_sub_eq_lowerDifferentSummand
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {σ : Gal(K/F)} (hσ : σ ≠ 1) :
    ord K (σ (π : K) - (π : K)) =
      (((lowerDifferentSummand F K σ : ℕ) : ℤ) : WithTop ℤ) := by
  have hnotmem := lowerDifferentSummand_not_mem F K hσ
  have hmem : σ ∈ lowerRamificationGroup F K
      ((lowerDifferentSummand F K σ : ℤ) - 1) := by
    cases hsum : lowerDifferentSummand F K σ with
    | zero =>
      norm_num
    | succ n =>
      have hm := lowerDifferentSummand_mem_of_lt F K hσ
        (n := n) (by omega)
      simpa [hsum] using hm
  apply (withTopInt_le_and_not_succ_le_iff_eq
    (lowerDifferentSummand F K σ : ℤ)
    (ord K (σ (π : K) - (π : K)))).1
  constructor
  · have hlower := lowerRamificationGroup_uniformizer_ord F K hmem hπ
    simpa only [sub_add_cancel] using hlower
  · intro hnext
    apply hnotmem
    apply (mem_lowerRamificationGroup_iff_ord_of_adjoin_eq_top F K π hgen).2
    simpa only [Int.reduceNeg, sub_add_cancel] using hnext

omit [IsGalois F K] in
/-- Hilbert's uniformizer-difference formula for the normalized different exponent.  The sum is
over `σ ≠ 1`, never over the identity. -/
theorem differentExponent_eq_uniformizerDifferenceSum
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    (differentExponent F K : ℤ) =
      ∑ σ ∈ nonidentityGaloisAutomorphisms F K,
        (ord K (σ (π : K) - (π : K))).untop₀ := by
  classical
  unfold differentExponent
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hσne : σ ≠ 1 := (mem_nonidentityGaloisAutomorphisms F K).1 hσ
  have hord := ord_galois_uniformizer_sub_eq_lowerDifferentSummand
    F K π hπ hgen hσne
  simp [hord]

omit [IsGalois F K] in
/-- Under an exact one-break profile, every nonidentity contribution is `t + 1`. -/
theorem lowerDifferentSummand_eq_succ_of_isLowerBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    {σ : Gal(K/F)} (hσ : σ ≠ 1) :
    lowerDifferentSummand F K σ = t + 1 := by
  apply le_antisymm
  · by_contra hle
    have hlt : t + 1 < lowerDifferentSummand F K σ := Nat.lt_of_not_ge hle
    have hmem := lowerDifferentSummand_mem_of_lt F K hσ hlt
    have hmem' : σ ∈ lowerRamificationGroup F K ((t : ℤ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hmem
    rw [ht.2, Subgroup.mem_bot] at hmem'
    exact hσ hmem'
  · by_contra hle
    have hdt : lowerDifferentSummand F K σ ≤ t := by omega
    have htop := PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break
      F K ht (show (lowerDifferentSummand F K σ : ℤ) ≤ (t : ℤ) by exact_mod_cast hdt)
    apply lowerDifferentSummand_not_mem F K hσ
    rw [htop]
    trivial

omit [IsGalois F K] in
/-- For every nonidentity automorphism in a one-break extension, the chosen generating
uniformizer has displacement order exactly `t + 1`. -/
theorem ord_galois_uniformizer_sub_eq_of_isLowerBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {σ : Gal(K/F)} (hσ : σ ≠ 1) :
    ord K (σ (π : K) - (π : K)) = (((t + 1 : ℕ) : ℤ) : WithTop ℤ) := by
  rw [ord_galois_uniformizer_sub_eq_lowerDifferentSummand F K π hπ hgen hσ,
    lowerDifferentSummand_eq_succ_of_isLowerBreak F K ht hσ]

omit [IsGalois F K] in
/-- Trivial inertia (`G₀ = 1`) makes every nonidentity different summand zero. -/
theorem lowerDifferentSummand_eq_zero_of_lowerRamificationGroup_zero_eq_bot
    (hzero : lowerRamificationGroup F K 0 = ⊥)
    {σ : Gal(K/F)} (hσ : σ ≠ 1) :
    lowerDifferentSummand F K σ = 0 := by
  classical
  rw [lowerDifferentSummand, dif_neg hσ, Nat.find_eq_zero]
  change σ ∉ lowerRamificationGroup F K 0
  rw [hzero, Subgroup.mem_bot]
  exact hσ

omit [IsGalois F K] in
/-- The unramified lower-filtration branch has different exponent zero. -/
theorem differentExponent_eq_zero_of_lowerRamificationGroup_zero_eq_bot
    (hzero : lowerRamificationGroup F K 0 = ⊥) :
    differentExponent F K = 0 := by
  classical
  unfold differentExponent
  apply Finset.sum_eq_zero
  intro σ hσ
  exact lowerDifferentSummand_eq_zero_of_lowerRamificationGroup_zero_eq_bot
    F K hzero ((mem_nonidentityGaloisAutomorphisms F K).1 hσ)

end GeneralGalois

section PrimeCyclicCardinality

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

/-- A prime-cyclic Galois group has exactly `[K : F] - 1` nonidentity elements. -/
theorem card_nonidentityGaloisAutomorphisms :
    (nonidentityGaloisAutomorphisms F K).card = Module.finrank F K - 1 := by
  classical
  rw [nonidentityGaloisAutomorphisms, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    PrimeCyclicExtension.galoisCard_eq_degree F K]

end PrimeCyclicCardinality

section PrimeCyclicDifferent

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Evaluation of the uniformizer-difference sum: there are `[K : F] - 1` nonidentity
automorphisms, each with displacement order `t + 1`. -/
theorem uniformizerDifferenceSum_eq
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    ∑ σ ∈ nonidentityGaloisAutomorphisms F K,
        (ord K (σ (π : K) - (π : K))).untop₀ =
      (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  classical
  calc
    _ = ∑ _σ ∈ nonidentityGaloisAutomorphisms F K, ((t + 1 : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have hσne := (mem_nonidentityGaloisAutomorphisms F K).1 hσ
      rw [ord_galois_uniformizer_sub_eq_of_isLowerBreak F K ht π hπ hgen hσne]
      simp
    _ = ((nonidentityGaloisAutomorphisms F K).card : ℤ) * ((t + 1 : ℕ) : ℤ) := by
      simp
    _ = (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
      rw [card_nonidentityGaloisAutomorphisms F K]
      norm_num

/-- The different exponent of a ramified cyclic extension of prime degree with lower break `t`:

`d(K/F) = ([K : F] - 1) * (t + 1)`.

The chosen `π` is explicitly a uniformizer and an integral generator; no unjustified converse
uniformizer criterion is used. -/
theorem differentExponent_eq
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    differentExponent F K = (Module.finrank F K - 1) * (t + 1) := by
  apply Nat.cast_injective (R := ℤ)
  rw [differentExponent_eq_uniformizerDifferenceSum F K π hπ hgen,
    uniformizerDifferenceSum_eq F K ht π hπ hgen]

/-- Tame specialization (`t = 0`): `d(K/F) = [K : F] - 1`. -/
theorem differentExponent_tame_eq
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    differentExponent F K = Module.finrank F K - 1 := by
  simpa using differentExponent_eq F K ht π hπ hgen

/-- Wild prime-degree specialization.  The equality `[K : F] = char(k_F)` is explicit because
the prime-degree tame/wild dichotomy is a separate downstream node. -/
theorem differentExponent_wild_eq
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hdegree : Module.finrank F K = residueCharacteristic F)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    differentExponent F K =
      (residueCharacteristic F - 1) * (t + 1) := by
  rw [differentExponent_eq F K ht π hπ hgen, hdegree]

/-- Wild quadratic specialization: when `[K : F] = 2`, the exponent is `t + 1`. -/
theorem differentExponent_wildQuadratic_eq
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hdegree : Module.finrank F K = 2)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    differentExponent F K = t + 1 := by
  rw [differentExponent_eq F K ht π hπ hgen, hdegree]
  norm_num

end PrimeCyclicDifferent

end LanglandsFirstMainLemma
