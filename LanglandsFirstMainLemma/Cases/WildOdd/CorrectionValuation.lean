import LanglandsFirstMainLemma.Cases.WildOdd.CorrectionFormula
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.Ramification.PullbackConductors

/-!
# Valuation of the wild odd correction

This file proves Proposition `prop:X-depth` from the exact identity supplied by
`CorrectionFormula`.  The three cases `m < T`, `m = T`, and `T < m` are kept
separate through the denominator calculation.  In negative offset the proof
uses the reciprocal elementary-symmetric identity and the exact reciprocal
floor estimates from `SymmetricBounds`.
-/

open scoped BigOperators

namespace LanglandsFirstMainLemma

noncomputable section

private theorem finiteElementarySymmetric_reciprocal
    {ι R : Type*} [Fintype ι] [Field R]
    (z : ι → R) (hz : ∀ i, z i ≠ 0) (j : ℕ)
    (hj : j ≤ Fintype.card ι) :
    ((Finset.univ : Finset ι).val.map z).esymm j =
      (∏ i, z i) *
        ((Finset.univ : Finset ι).val.map fun i ↦ (z i)⁻¹).esymm
          (Fintype.card ι - j) := by
  classical
  rw [Finset.esymm_map_val, Finset.esymm_map_val]
  rw [Finset.mul_sum]
  refine Finset.sum_bij'
      (fun A _ ↦ Aᶜ) (fun A _ ↦ Aᶜ) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    rw [Finset.mem_powersetCard] at hA ⊢
    refine ⟨by simp, ?_⟩
    rw [Finset.card_compl, hA.2]
  · intro A hA
    rw [Finset.mem_powersetCard] at hA ⊢
    refine ⟨by simp, ?_⟩
    rw [Finset.card_compl, hA.2]
    omega
  · intro A _
    simp
  · intro A _
    simp
  · intro A _
    rw [Finset.prod_inv_distrib]
    have hprod : ∏ i ∈ Aᶜ, z i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ hz i
    rw [← div_eq_mul_inv]
    apply (eq_div_iff hprod).2
    have hsplit := Finset.prod_sdiff
      (show Aᶜ ⊆ (Finset.univ : Finset ι) by simp) (f := z)
    simpa [div_eq_mul_inv] using hsplit

private theorem correctionValuation_localField_infinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n ↦ (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord F (f m) = (m : WithTop ℤ) := (exists_ord_eq F m).choose_spec
    have hn : ord F (f n) = (n : WithTop ℤ) := (exists_ord_eq F n).choose_spec
    have hcoe : (m : WithTop ℤ) = (n : WithTop ℤ) := hm.symm.trans <|
      (congrArg (ord F) hmn).trans hn
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

/-- Reciprocal identity used in the `T < m` branch:
`s_j(u) = N(u) s_{p-j}(u⁻¹)`. -/
private theorem elementarySymmetric_reciprocal
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (x : K) (hx : x ≠ 0) (j : ℕ) (hj : j ≤ Module.finrank F K) :
    elementarySymmetric F K j x =
      norm F K x *
        elementarySymmetric F K (Module.finrank F K - j) x⁻¹ := by
  letI : Infinite F := correctionValuation_localField_infinite F
  apply (algebraMap F K).injective
  rw [map_mul, algebraMap_elementarySymmetric_eq_esymm_galois,
    algebraMap_elementarySymmetric_eq_esymm_galois,
    ← galoisConjugates_prod]
  simpa only [galoisConjugates, galoisConjugate, Multiset.map_map,
    Function.comp_apply, map_inv₀, ← Finset.prod_eq_multiset_prod,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank F K] using
    (finiteElementarySymmetric_reciprocal
      (z := fun σ : Gal(K/F) ↦ σ x)
      (fun σ ↦ (map_ne_zero σ).2 hx) j
      (by
        rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank F K]
        exact hj))

namespace WildOddCorrectionData

variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  {T : ℕ} (d : WildOddCorrectionData F K T)

/-- In the strict below-break case `m < T` (`0 < a`), the displayed
denominator in the closed formula is a unit. -/
theorem ord_one_sub_n_pow_of_pos (ha : 0 < d.a) :
    ord F (1 - d.n ^ (residueCharacteristic F - 1)) = 0 := by
  have hpow : ord F (d.n ^ (residueCharacteristic F - 1)) =
      ((((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
        WithTop ℤ) := by
    rw [ord_pow, d.ord_n, ← WithTop.coe_nsmul]
    congr 1
  have hcoeff : (0 : ℤ) < ((residueCharacteristic F - 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_pos_of_lt (residueCharacteristic_prime F).one_lt
  have hne : ord F (1 : F) ≠
      ord F (d.n ^ (residueCharacteristic F - 1)) := by
    rw [ord_one, hpow]
    exact ne_of_lt (WithTop.coe_pos.mpr (mul_pos hcoeff ha))
  rw [sub_eq_add_neg, ord_add_eq_min F (by simpa only [ord_neg] using hne),
    ord_one, ord_neg, hpow]
  exact min_eq_left (WithTop.coe_nonneg.mpr (le_of_lt (mul_pos hcoeff ha)))

/-- At the break `m = T` (`a = 0`), boundary noncancellation still makes the
displayed denominator a unit. -/
theorem ord_one_sub_n_pow_of_eq_zero (ha : d.a = 0) :
    ord F (1 - d.n ^ (residueCharacteristic F - 1)) = 0 := by
  rw [← d.zeroDenominator_eq]
  exact d.ord_zeroDenominator_of_boundary ha

/-- In the strict above-break case `T < m` (`a < 0`), the denominator has
exactly the valuation of `n^(p-1)`. -/
theorem ord_one_sub_n_pow_of_neg (ha : d.a < 0) :
    ord F (1 - d.n ^ (residueCharacteristic F - 1)) =
      ((((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
        WithTop ℤ) := by
  have hpow : ord F (d.n ^ (residueCharacteristic F - 1)) =
      ((((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
        WithTop ℤ) := by
    rw [ord_pow, d.ord_n, ← WithTop.coe_nsmul]
    congr 1
  have hcoeff : (0 : ℤ) < ((residueCharacteristic F - 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_pos_of_lt (residueCharacteristic_prime F).one_lt
  have hne : ord F (1 : F) ≠
      ord F (d.n ^ (residueCharacteristic F - 1)) := by
    rw [ord_one, hpow]
    exact ne_of_gt (WithTop.coe_lt_coe.mpr (mul_neg_of_pos_of_neg hcoeff ha))
  rw [sub_eq_add_neg, ord_add_eq_min F (by simpa only [ord_neg] using hne),
    ord_one, ord_neg, hpow]
  exact min_eq_right (WithTop.coe_le_coe.mpr
    (le_of_lt (mul_neg_of_pos_of_neg hcoeff ha)))

end WildOddCorrectionData

/-- The trace of `1` gives the mixed-characteristic lower bound
`floor((p-1)T/p) ≤ ord_F(p)`.  In equal characteristic the right side is
`top`, so the same statement remains literally true. -/
theorem wildOdd_prime_ord_lower_bound
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    (wildBaseDepth (residueCharacteristic F) T : WithTop ℤ) ≤
      ord F (residueCharacteristic F : F) := by
  simpa only [wildBaseDepth] using
    (degree_natCast_ord_bound F K (residueCharacteristic F)
      ((((residueCharacteristic F - 1) * T : ℕ) : ℤ))
      (residueCharacteristic_prime F).pos d.degree_eq d.traceLowerBound)

/-- In equal characteristic the residue prime itself is zero, so its
valuation is exactly `top`. -/
theorem wildOdd_prime_ord_eq_top_of_eq_zero
    {F : Type*} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hpzero : (residueCharacteristic F : F) = 0) :
    ord F (residueCharacteristic F : F) = ⊤ := by
  rw [hpzero, ord_zero]

/-- In the nonvanishing (mixed-characteristic) branch, the valuation of `p`
is an exact finite integer `e`, and the ramification estimate proves
`floor((p-1)T/p) ≤ e`. -/
theorem wildOdd_prime_ord_exists_of_ne_zero
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T)
    (hpne : (residueCharacteristic F : F) ≠ 0) :
    ∃ e : ℤ,
      ord F (residueCharacteristic F : F) = (e : WithTop ℤ) ∧
        wildBaseDepth (residueCharacteristic F) T ≤ e := by
  have hfinite : ord F (residueCharacteristic F : F) ≠ ⊤ :=
    (ord_ne_top_iff F).2 hpne
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hfinite
  refine ⟨e, he.symm, ?_⟩
  have h := wildOdd_prime_ord_lower_bound d
  rw [← he] at h
  exact WithTop.coe_le_coe.mp h

private theorem wildOdd_total_depth
    (p T : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hT : 2 ≤ T)
    {e : ℤ} (he : wildBaseDepth p T ≤ e) :
    (T : ℤ) ≤ e + wildBaseDepth p T := by
  have htwo := two_mul_wildBaseDepth_ge p T hp hp2 hT
  linarith

private theorem correctionFormulaB_ord_ge_of_nonneg
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) (ha : 0 ≤ d.a) :
    (wildBaseDepth (residueCharacteristic F) T : WithTop ℤ) ≤
      ord F (correctionFormulaB d) := by
  let p := residueCharacteristic F
  have hp : p.Prime := residueCharacteristic_prime F
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hsymm {j : ℕ} (hjpos : 1 ≤ j) (hjlt : j < p) :
      (wildBaseDepth p T : WithTop ℤ) ≤
        ord F (elementarySymmetric F K j d.u) := by
    have hmain := wild_elementarySymmetric_bound F K p T d.a hp d.two_le_T
      rfl d.degree_eq d.traceLowerBound (by rw [d.ord_u]) hjpos hjlt
    apply (WithTop.coe_le_coe.mpr ?_).trans hmain
    rw [wildBaseDepth]
    apply Int.ediv_le_ediv hpZ
    nlinarith [show (0 : ℤ) ≤ (j : ℤ) by positivity]
  have htrace : (wildBaseDepth p T : WithTop ℤ) ≤ ord F (trace F K d.u) := by
    simpa only [elementarySymmetric_one] using hsymm (j := 1) (by omega) (by
      have hp2 := hp.two_le
      have hpne := d.odd_residueCharacteristic
      omega)
  have hsum : (wildBaseDepth p T : WithTop ℤ) ≤
      ord F (∑ q ∈ Finset.Ico 1 (p - 1),
        (-d.n) ^ q * elementarySymmetric F K (p - q) d.u) := by
    apply ord_sum F
    intro q hq
    have hqmem := Finset.mem_Ico.mp hq
    have hjpos : 1 ≤ p - q := by omega
    have hjlt : p - q < p := by omega
    have hs := hsymm hjpos hjlt
    have hn : (0 : WithTop ℤ) ≤ ord F ((-d.n) ^ q) := by
      rw [ord_pow, ord_neg, d.ord_n, ← WithTop.coe_nsmul]
      exact WithTop.coe_nonneg.mpr (mul_nonneg (by positivity) ha)
    rw [ord_mul]
    simpa only [zero_add] using add_le_add hn hs
  rw [correctionFormulaB]
  exact (ord F).map_le_add htrace hsum

private theorem correctionFormulaB_ord_ge_adjusted_of_neg
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) (ha : d.a < 0) :
    ((wildBaseDepth (residueCharacteristic F) T +
        ((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
      WithTop ℤ) ≤ ord F (correctionFormulaB d) := by
  let p := residueCharacteristic F
  let c := d.a.natAbs
  have hp : p.Prime := residueCharacteristic_prime F
  have hp2 : 2 ≤ p := hp.two_le
  have hcpos : 0 < c := Int.natAbs_pos.mpr (ne_of_lt ha)
  have hca : (c : ℤ) = -d.a := by
    dsimp only [c]
    rw [Int.natCast_natAbs, abs_of_neg ha]
  have hac : d.a = -(c : ℤ) := by linarith
  have hy : ((c : ℤ) : WithTop ℤ) ≤ ord K d.u⁻¹ := by
    rw [ord_inv, d.ord_u]
    norm_cast
    exact hca.le
  have hsymm {j : ℕ} (hjpos : 1 ≤ j) (hjlt : j < p) :
      (((j : ℤ) * (c : ℤ) + (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) ≤
        ord F (elementarySymmetric F K j d.u⁻¹) :=
    wild_elementarySymmetric_bound F K p T (c : ℤ) hp d.two_le_T
      rfl d.degree_eq d.traceLowerBound hy hjpos hjlt
  have htrace :
      ((wildBaseDepth p T + ((p - 1 : ℕ) : ℤ) * d.a : ℤ) : WithTop ℤ) ≤
        ord F (trace F K d.u) := by
    have hrecip := elementarySymmetric_reciprocal d.u d.u_ne_zero 1
      (by rw [d.degree_eq]; exact hp.one_le)
    rw [← elementarySymmetric_one F K d.u, hrecip, d.degree_eq, d.norm_u,
      ord_mul, d.ord_n]
    have hs := hsymm (j := p - 1) (by omega) (by omega)
    have hnum := wild_reciprocal_first_depth p T c hp
    have hp1Z : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.one_le]
      norm_num
    have hp2Z : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by
      rw [Nat.cast_sub hp2]
      norm_num
    have harith :
        wildBaseDepth p T + ((p - 1 : ℕ) : ℤ) * d.a ≤
          d.a +
            (((p - 1 : ℕ) : ℤ) * (c : ℤ) +
              (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) := by
      rw [hac]
      push_cast at hnum ⊢
      rw [hp1Z, hp2Z] at hnum
      rw [hp1Z]
      nlinarith
    refine (WithTop.coe_le_coe.mpr harith).trans ?_
    rw [WithTop.coe_add]
    exact add_le_add_right hs (d.a : WithTop ℤ)
  have hsum :
      ((wildBaseDepth p T + ((p - 1 : ℕ) : ℤ) * d.a : ℤ) : WithTop ℤ) ≤
        ord F (∑ q ∈ Finset.Ico 1 (p - 1),
          (-d.n) ^ q * elementarySymmetric F K (p - q) d.u) := by
    apply ord_sum F
    intro q hq
    have hqmem := Finset.mem_Ico.mp hq
    let j := p - q
    have hjtwo : 2 ≤ j := by omega
    have hjlt : j < p := by omega
    have hpq : p - j = q := by dsimp only [j]; omega
    have hrecip := elementarySymmetric_reciprocal d.u d.u_ne_zero j
      (by rw [d.degree_eq]; exact hjlt.le)
    rw [hrecip, d.degree_eq, hpq, d.norm_u, ord_mul, ord_pow, ord_neg,
      d.ord_n, ord_mul]
    have hs := hsymm (j := q) (by omega) (by omega)
    have hnum := wild_reciprocal_intermediate_depth p T c j hp hjtwo hjlt
    have hp1Z : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.one_le]
      norm_num
    have hj2Z : ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 := by
      rw [Nat.cast_sub hjtwo]
      norm_num
    have harith :
        wildBaseDepth p T + ((p - 1 : ℕ) : ℤ) * d.a ≤
          (q : ℤ) * d.a +
            (d.a +
              (((q : ℤ) * (c : ℤ) + (((p - 1) * T : ℕ) : ℤ)) /
                (p : ℤ))) := by
      rw [hac]
      push_cast at hnum ⊢
      have hpjZ : ((p - j : ℕ) : ℤ) = (q : ℤ) := by
        exact_mod_cast hpq
      have hjZ : (j : ℤ) = (p : ℤ) - (q : ℤ) := by
        dsimp only [j]
        rw [Nat.cast_sub (by omega : q ≤ p)]
      rw [hj2Z, hpjZ] at hnum
      rw [hp1Z] at hnum ⊢
      rw [hjZ] at hnum
      nlinarith [hnum]
    rw [d.ord_n, ← WithTop.coe_nsmul]
    refine (WithTop.coe_le_coe.mpr harith).trans ?_
    simpa only [WithTop.coe_add, WithTop.coe_mul, ← WithTop.coe_nsmul,
      nsmul_eq_mul, add_comm, add_left_comm, add_assoc] using
      (add_le_add_left (add_le_add_left hs (d.a : WithTop ℤ))
        (q • (d.a : WithTop ℤ)))
  rw [correctionFormulaB]
  exact (ord F).map_le_add htrace hsum

/-- **Valuation of the wild odd correction.**  The correction in the exact
closed formula belongs to the unweakened manuscript lattice `p_F^T`.
Equal characteristic gives literal vanishing.  Otherwise the proof uses the
exact finite valuation of `p`, and treats the three strict break-position
cases separately. -/
theorem wildOdd_correction_mem
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    wildOddCorrectionX d ∈ lattice F (T : ℤ) := by
  rw [mem_lattice]
  let p := residueCharacteristic F
  by_cases hpzero : (p : F) = 0
  · rw [wildOdd_correctionFormula, show (residueCharacteristic F : F) = 0 by
      simpa only [p] using hpzero]
    simp
  · obtain ⟨e, heord, hebase⟩ := wildOdd_prime_ord_exists_of_ne_zero d
      (by simpa only [p] using hpzero)
    have htotal : (T : ℤ) ≤ e + wildBaseDepth p T :=
      wildOdd_total_depth p T (residueCharacteristic_prime F)
        d.odd_residueCharacteristic d.two_le_T hebase
    rcases lt_trichotomy 0 d.a with ha | ha | ha
    · have hden := d.ord_one_sub_n_pow_of_pos ha
      have hB := correctionFormulaB_ord_ge_of_nonneg d ha.le
      rw [wildOdd_correctionFormula, ord_div, ord_mul, heord, hden, sub_zero]
      exact (WithTop.coe_le_coe.mpr htotal).trans (by
        simpa only [WithTop.coe_add, add_comm] using
          add_le_add_left hB (e : WithTop ℤ))
    · have ha0 : d.a = 0 := ha.symm
      have hden := d.ord_one_sub_n_pow_of_eq_zero ha0
      have hB := correctionFormulaB_ord_ge_of_nonneg d ha0.ge
      rw [wildOdd_correctionFormula, ord_div, ord_mul, heord, hden, sub_zero]
      exact (WithTop.coe_le_coe.mpr htotal).trans (by
        simpa only [WithTop.coe_add, add_comm] using
          add_le_add_left hB (e : WithTop ℤ))
    · have hden := d.ord_one_sub_n_pow_of_neg ha
      have hB := correctionFormulaB_ord_ge_adjusted_of_neg d ha
      rw [wildOdd_correctionFormula, ord_div, ord_mul, heord, hden]
      let r : ℤ := ((p - 1 : ℕ) : ℤ) * d.a
      change ((T : ℤ) : WithTop ℤ) ≤
        (e : WithTop ℤ) + ord F (correctionFormulaB d) - (r : WithTop ℤ)
      by_cases htop : ord F (correctionFormulaB d) = ⊤
      · simp [htop]
      · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
        rw [← hk] at hB ⊢
        have hBk : wildBaseDepth p T + r ≤ k :=
          WithTop.coe_le_coe.mp (by simpa only [r, p] using hB)
        rw [← WithTop.coe_add,
          ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe]
        omega

/-- Triviality of a multiplicative character of exact conductor `T`, together
with a stationary linearization valid at a depth `r ≤ T`, proves the full
additive triviality statement `psi(A p_F^T) = 1`. -/
theorem wildOdd_additive_triviality
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {T r : ℕ} (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T)
    (tau : LocalQuasiCharData F) (htau : tau.conductor = T)
    (psi : ContinuousAddChar F) (A : F)
    (hlinear : ∀ x : lattice F (r : ℤ),
      tau.character (positiveUnitOfLattice F hr x) = psi (A * (x : F))) :
    ∀ x : F, x ∈ lattice F (T : ℤ) → psi (A * x) = 1 := by
  intro x hx
  let xT : lattice F (T : ℤ) := ⟨x, hx⟩
  let xR : lattice F (r : ℤ) :=
    ⟨x, lattice_antitone F (by exact_mod_cast hrT) hx⟩
  let uT := positiveUnitOfLattice F hT xT
  let uR := positiveUnitOfLattice F hr xR
  have hu : (uR : Fˣ) = (uT : Fˣ) := by
    apply Units.ext
    simp only [uR, uT, coe_positiveUnitOfLattice, xR, xT]
  have htriv : QuasiCharTrivialOnUnitFiltration F tau.character T := by
    simpa only [htau] using tau.isConductor.trivial
  calc
    psi (A * x) = tau.character (uR : Fˣ) := by
      simpa only [xR] using (hlinear xR).symm
    _ = tau.character (uT : Fˣ) := congrArg tau.character hu
    _ = 1 := htriv (uT : Fˣ) uT.property

/-- The additive phase of the closed correction is exactly one.  This is
deduced from exact conductor triviality and stationary linearization, after
the correction depth itself has been proved. -/
theorem wildOdd_correction_phase
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T r : ℕ} (d : WildOddCorrectionData F K T)
    (hr : 0 < r) (hrT : r ≤ T)
    (tau : LocalQuasiCharData F) (htau : tau.conductor = T)
    (psi : ContinuousAddChar F) (A : F)
    (hlinear : ∀ x : lattice F (r : ℤ),
      tau.character (positiveUnitOfLattice F hr x) = psi (A * (x : F))) :
    psi (-A * wildOddCorrectionX d) = 1 := by
  have hT : 0 < T := by omega
  have htriv := wildOdd_additive_triviality hT hr hrT tau htau psi A hlinear
  have hmem : -wildOddCorrectionX d ∈ lattice F (T : ℤ) :=
    (lattice F (T : ℤ)).neg_mem (wildOdd_correction_mem d)
  have harg : A * (-wildOddCorrectionX d) =
      -A * wildOddCorrectionX d := by ring
  rw [← harg]
  exact htriv (-wildOddCorrectionX d) hmem

end

end LanglandsFirstMainLemma
