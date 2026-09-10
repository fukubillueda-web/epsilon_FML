import LanglandsFirstMainLemma.Ramification.PrimeCyclicExtension
import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.LocalField.Valuation
import LanglandsFirstMainLemma.Basic.FiniteProducts
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Symmetric-function valuation bounds

This file separates the algebraic Newton identities from the exact tame and wild valuation
estimates used in the prime-degree norm calculations.
-/

open scoped BigOperators
open Finset Nat

namespace LanglandsFirstMainLemma

namespace FiniteFamily

/-- The `i`-th power sum of a finite family. -/
noncomputable def finitePowerSum {ι R : Type*} [Fintype ι] [CommRing R]
    (z : ι → R) (i : ℕ) : R := ∑ k, z k ^ i

/-- The `j`-th elementary symmetric coefficient of a finite family. -/
noncomputable def finiteElementarySymmetric {ι R : Type*} [Fintype ι] [CommRing R]
    (z : ι → R) (j : ℕ) : R := (Finset.univ.val.map z).esymm j

/-- Newton's identity for a finite family, before any valuation is introduced. -/
theorem newton {ι R : Type*} [Fintype ι] [CommRing R]
    (z : ι → R) (j : ℕ) :
    (j : R) * finiteElementarySymmetric z j =
      (-1 : R) ^ (j + 1) *
        ∑ a ∈ antidiagonal j with a.1 < j,
          (-1 : R) ^ a.1 * finiteElementarySymmetric z a.1 * finitePowerSum z a.2 := by
  have h := congrArg (MvPolynomial.aeval z)
    (MvPolynomial.mul_esymm_eq_sum ι R j)
  simp only [MvPolynomial.aeval_def] at h
  have heval (n : ℕ) :
      MvPolynomial.eval₂ (algebraMap R R) z (MvPolynomial.esymm ι R n) =
        (Finset.univ.val.map z).esymm n := by
    simpa only [MvPolynomial.aeval_def] using
      MvPolynomial.aeval_esymm_eq_multiset_esymm ι R n z
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_neg, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_natCast, MvPolynomial.eval₂_sum] at h
  simp_rw [heval] at h
  simpa [finitePowerSum, finiteElementarySymmetric, MvPolynomial.psum] using h

end FiniteFamily

private theorem nonarchimedeanLocalFieldInfinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n => (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord F (f m) = (m : WithTop ℤ) := (exists_ord_eq F m).choose_spec
    have hn : ord F (f n) = (n : WithTop ℤ) := (exists_ord_eq F n).choose_spec
    have hcoe : (m : WithTop ℤ) = (n : WithTop ℤ) := hm.symm.trans <|
      (congrArg (ord F) hmn).trans hn
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

/-- The `i`-th power sum of the Galois conjugates, written in the base field as a trace. -/
noncomputable def galoisPowerSum (F K : Type*) [Field F] [Field K]
    [Algebra F K] [Module.Free F K] [Module.Finite F K]
    (i : ℕ) (x : K) : F := trace F K (x ^ i)

/-- Upstairs, `galoisPowerSum` is the literal sum of the powers of the conjugates. -/
theorem algebraMap_galoisPowerSum_eq_sum_conjugates
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (i : ℕ) (x : K) :
    algebraMap F K (galoisPowerSum F K i x) =
      ∑ σ : Gal(K/F), (σ x) ^ i := by
  rw [galoisPowerSum, trace_eq_sum_automorphisms]
  simp

/-- Newton's identity for `Extension.elementarySymmetric` and the Galois power sums. -/
theorem elementarySymmetric_newton_identity
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (x : K) (j : ℕ) :
    (j : F) * elementarySymmetric F K j x =
      (-1 : F) ^ (j + 1) *
        ∑ a ∈ antidiagonal j with a.1 < j,
          (-1 : F) ^ a.1 * elementarySymmetric F K a.1 x *
            galoisPowerSum F K a.2 x := by
  letI : Infinite F := nonarchimedeanLocalFieldInfinite F
  apply (algebraMap F K).injective
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum]
  simp_rw [algebraMap_elementarySymmetric_eq_esymm_galois]
  simp_rw [algebraMap_galoisPowerSum_eq_sum_conjugates]
  simpa [FiniteFamily.finiteElementarySymmetric, FiniteFamily.finitePowerSum,
    galoisConjugates, galoisConjugate] using
    (FiniteFamily.newton (z := fun σ : Gal(K/F) => σ x) j)

/-- The exact lower-bound half of
`Tr(𝔭_K^q) = 𝔭_F^⌊(q+D)/p⌋`, with the denominator and different exponent explicit.

The different and full trace-lattice equality are proved in their own nodes, so this node takes
precisely the part of that equality needed by the symmetric-function argument as an input. -/
def TraceIdealLowerBound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] (p : ℕ) (D : ℤ) : Prop :=
  ∀ (q : ℤ) (z : K),
    (q : WithTop ℤ) ≤ ord K z →
      (((q + D) / (p : ℤ) : ℤ) : WithTop ℤ) ≤ ord F (trace F K z)

/-- Integer ceiling of `n / p`, written without passing through the rationals. -/
def integerCeilingDiv (n : ℤ) (p : ℕ) : ℤ :=
  (n + (p : ℤ) - 1) / (p : ℤ)

/-- The wild different contribution `D = (p - 1)(t + 1)`. -/
def wildDifferentContribution (p t : ℕ) : ℤ :=
  (((p - 1) * (t + 1) : ℕ) : ℤ)

/-- The floor `⌊(p-1)T/p⌋` that controls the norm--trace correction. -/
def wildBaseDepth (p T : ℕ) : ℤ :=
  (((p - 1) * T : ℕ) : ℤ) / (p : ℤ)

private theorem integerCeilingDiv_le_iff (n z : ℤ) (p : ℕ) (hp : 0 < p) :
    integerCeilingDiv n p ≤ z ↔ n ≤ (p : ℤ) * z := by
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  rw [integerCeilingDiv, Int.ediv_le_iff_le_mul hpZ, mul_comm z (p : ℤ)]
  omega

/-- The integer-ceiling formula as the negative of the floor of the negative quotient. -/
theorem integerCeilingDiv_eq_neg_ediv (n : ℤ) (p : ℕ) (hp : 0 < p) :
    integerCeilingDiv n p = -((-n) / (p : ℤ)) := by
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  unfold integerCeilingDiv
  apply le_antisymm
  · rw [Int.ediv_le_iff_le_mul hpZ]
    have hq : ((-n) / (p : ℤ)) * (p : ℤ) ≤ -n :=
      (Int.le_ediv_iff_mul_le hpZ).mp le_rfl
    calc
      n + (p : ℤ) - 1 < n + (p : ℤ) := by omega
      _ ≤ (-((-n) / (p : ℤ))) * (p : ℤ) + (p : ℤ) := by
        nlinarith
  · rw [neg_le]
    rw [Int.le_ediv_iff_mul_le hpZ]
    have hceil := (Int.ediv_le_iff_le_mul hpZ).mp
      (show (n + (p : ℤ) - 1) / (p : ℤ) ≤
        (n + (p : ℤ) - 1) / (p : ℤ) by rfl)
    nlinarith

/-- The manuscript identity
`⌊(p-1)T/p⌋ = T - ⌈T/p⌉`, with the positive denominator explicit. -/
theorem wildBaseDepth_eq_sub_integerCeilingDiv (p T : ℕ) (hp : 0 < p) :
    wildBaseDepth p T = (T : ℤ) - integerCeilingDiv (T : ℤ) p := by
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  have hcast : (((p - 1) * T : ℕ) : ℤ) =
      (p : ℤ) * (T : ℤ) - (T : ℤ) := by
    simp [Nat.cast_sub hp]
    ring
  rw [wildBaseDepth, hcast]
  rw [show (p : ℤ) * (T : ℤ) - (T : ℤ) =
      (-(T : ℤ)) + (T : ℤ) * (p : ℤ) by ring]
  rw [Int.add_mul_ediv_right _ _ hpZ.ne', integerCeilingDiv_eq_neg_ediv _ _ hp]
  ring

/-- For odd residue characteristic and `T ≥ 2`, twice the exact base depth reaches `T`. -/
theorem two_mul_wildBaseDepth_ge (p T : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hT : 2 ≤ T) :
    (T : ℤ) ≤ 2 * wildBaseDepth p T := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hp3Z : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hDcast : (((p - 1) * T : ℕ) : ℤ) = ((p : ℤ) - 1) * (T : ℤ) := by
    simp [Nat.cast_sub hp.one_le]
  rcases Nat.even_or_odd T with hEven | hOdd
  · rcases hEven with ⟨k, hk⟩
    have hkT : T = k + k := by omega
    have hkTZ : (T : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hkT
    have hkZ : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hmulZ : (k : ℤ) * (p : ℤ) ≤ (((p - 1) * T : ℕ) : ℤ) := by
      rw [hDcast, hkTZ]
      nlinarith
    have hkdiv : (k : ℤ) ≤ wildBaseDepth p T := by
      rw [wildBaseDepth, Int.le_ediv_iff_mul_le hpZ]
      exact hmulZ
    rw [hkTZ]
    linarith
  · rcases hOdd with ⟨k, hk⟩
    have hkT : T = 2 * k + 1 := by omega
    have hkpos : 1 ≤ k := by omega
    have hkTZ : (T : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hkT
    have hkposZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hkpos
    have hmulZ : ((k + 1 : ℕ) : ℤ) * (p : ℤ) ≤
        (((p - 1) * T : ℕ) : ℤ) := by
      rw [hDcast, hkTZ]
      push_cast
      nlinarith
    have hkdiv : ((k + 1 : ℕ) : ℤ) ≤ wildBaseDepth p T := by
      rw [wildBaseDepth, Int.le_ediv_iff_mul_le hpZ]
      exact hmulZ
    push_cast at hkdiv
    rw [hkTZ]
    linarith

/-- First reciprocal term in the negative-valuation part of the correction estimate. -/
theorem wild_reciprocal_first_depth (p T c : ℕ) (hp : p.Prime) :
    wildBaseDepth p T ≤
      (((p - 2) * c : ℕ) : ℤ) +
        ((((p - 1) * c + (p - 1) * T : ℕ) : ℤ) / (p : ℤ)) := by
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hdiv : wildBaseDepth p T ≤
      ((((p - 1) * c + (p - 1) * T : ℕ) : ℤ) / (p : ℤ)) := by
    apply Int.ediv_le_ediv hpZ
    exact_mod_cast Nat.le_add_left ((p - 1) * T) ((p - 1) * c)
  exact hdiv.trans (by omega)

/-- Intermediate reciprocal terms, with the exact manuscript range `2 ≤ j < p`. -/
theorem wild_reciprocal_intermediate_depth (p T c j : ℕ) (hp : p.Prime)
    (_hjtwo : 2 ≤ j) (_hjlt : j < p) :
    wildBaseDepth p T ≤
      (((j - 2) * c : ℕ) : ℤ) +
        ((((p - j) * c + (p - 1) * T : ℕ) : ℤ) / (p : ℤ)) := by
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hdiv : wildBaseDepth p T ≤
      ((((p - j) * c + (p - 1) * T : ℕ) : ℤ) / (p : ℤ)) := by
    apply Int.ediv_le_ediv hpZ
    exact_mod_cast Nat.le_add_left ((p - 1) * T) ((p - j) * c)
  exact hdiv.trans (by omega)

private theorem ediv_add_shift_le_add_ediv (p D u v : ℤ)
    (hp : 0 < p) (hD : p ≤ D) :
    (u + v + D) / p ≤ (u + D) / p + (v + D) / p := by
  have hfloor (A B : ℤ) :
      (A + B - p) / p ≤ A / p + B / p := by
    rw [Int.ediv_le_iff_le_mul hp]
    have hA : A < (A / p) * p + p :=
      (Int.ediv_le_iff_le_mul hp).mp le_rfl
    have hB : B < (B / p) * p + p :=
      (Int.ediv_le_iff_le_mul hp).mp le_rfl
    nlinarith
  calc
    (u + v + D) / p ≤ (u + v + 2 * D - p) / p := by
      apply Int.ediv_le_ediv hp
      linarith
    _ = ((u + D) + (v + D) - p) / p := by
      congr 1
      ring
    _ ≤ (u + D) / p + (v + D) / p := hfloor (u + D) (v + D)

/-- Exact power-sum bound from the trace-ideal estimate.

The positivity of the denominator, its identification with the extension degree, and the range
`i ≥ 1` are explicit so that later users cannot silently divide by zero or change degrees. -/
theorem powerSum_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p : ℕ) (D a : ℤ) (hp : 0 < p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p D)
    {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    (i : ℕ) (hi : 1 ≤ i) :
    (((i : ℤ) * a + D) / (p : ℤ) : ℤ) ≤ ord F (galoisPowerSum F K i x) := by
  have _audit : 0 < p ∧ Module.finrank F K = p ∧ 1 ≤ i := ⟨hp, hdegree, hi⟩
  have hxi : (((i : ℤ) * a : ℤ) : WithTop ℤ) ≤ ord K (x ^ i) := by
    rw [ord_pow]
    have hsmul := nsmul_le_nsmul_right hx i
    calc
      (((i : ℤ) * a : ℤ) : WithTop ℤ) = i • (a : WithTop ℤ) := by
        rw [← WithTop.coe_nsmul]
        congr
      _ ≤ i • ord K x := hsmul
  exact htrace ((i : ℤ) * a) (x ^ i) hxi

/-- The trace of `1` gives the exact lower bound on the valuation of the prime degree. -/
theorem degree_natCast_ord_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p : ℕ) (D : ℤ) (hp : 0 < p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p D) :
    ((D / (p : ℤ) : ℤ) : WithTop ℤ) ≤ ord F (p : F) := by
  have h := powerSum_bound F K p D 0 hp hdegree htrace
    (x := (1 : K)) (by simp) 1 (by omega)
  have htraceOne : trace F K (1 : K) = (p : F) := by
    rw [show (1 : K) = algebraMap F K 1 by simp, trace_algebraMap, hdegree]
    simp
  simpa [galoisPowerSum, htraceOne] using h

/-- A positive natural number below the residue characteristic has valuation zero. -/
theorem ord_natCast_eq_zero_of_lt_residueCharacteristic
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < residueCharacteristic F) :
    ord F (j : F) = 0 := by
  have hnonneg : 0 ≤ ord F (j : F) :=
    (ord_nonneg_iff_mem_integer F _).2 (show (j : F) ∈ ringOfIntegers F by simp)
  have hnotpos : ¬0 < ord F (j : F) := by
    intro hpos
    have hmem : (j : F) ∈ lattice F 1 := by
      change ((1 : ℤ) : WithTop ℤ) ≤ ord F (j : F)
      by_cases htop : ord F (j : F) = ⊤
      · simp [htop]
      · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
        rw [← hz] at hpos ⊢
        simp only [WithTop.coe_pos, WithTop.coe_le_coe] at hpos ⊢
        omega
    have hr : residueMap F (j : ringOfIntegers F) = 0 :=
      (residueMap_eq_zero_iff F (j : ringOfIntegers F)).2 hmem
    have hc : (j : ResidueField F) = 0 := by simpa using hr
    have hdvd : residueCharacteristic F ∣ j :=
      (CharP.cast_eq_zero_iff (ResidueField F) (residueCharacteristic F) j).mp hc
    exact (Nat.not_dvd_of_pos_of_lt hjpos hjlt) hdvd
  exact le_antisymm (le_of_not_gt hnotpos) hnonneg

/-- The terminal elementary symmetric coefficient is the norm, whose valuation is exact in a
totally ramified extension. -/
theorem elementarySymmetric_degree_ord
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (hdegree : Module.finrank F K = p)
    (hram : ramificationIndex F K = p) (x : K) :
    ord F (elementarySymmetric F K p x) = ord K x := by
  have hfactor := finrank_eq_ramificationIndex_mul_residueDegree F K
  have hp : 0 < p := by
    rw [← hram]
    exact ramificationIndex_pos F K
  have htot : residueDegree F K = 1 := by
    rw [hdegree, hram] at hfactor
    exact mul_left_cancel₀ hp.ne' (by simpa using hfactor.symm)
  rw [← hdegree, elementarySymmetric_finrank, ord_norm, htot, one_nsmul]

/-- Lower-bound form of `elementarySymmetric_degree_ord`. -/
theorem elementarySymmetric_degree_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (a : ℤ) (hdegree : Module.finrank F K = p)
    (hram : ramificationIndex F K = p)
    {x : K} (hx : (a : WithTop ℤ) ≤ ord K x) :
    (a : WithTop ℤ) ≤ ord F (elementarySymmetric F K p x) := by
  rw [elementarySymmetric_degree_ord F K p hdegree hram x]
  exact hx

/-- Exact ceiling bound obtained from conjugate monomials.  The proof explicitly uses
`ord_K(y) = e(K/F) ord_F(y)` for base-field coefficients. -/
theorem totallyRamified_elementarySymmetric_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (ell : ℕ) (a : ℤ) (hell : 0 < ell)
    (hdegree : Module.finrank F K = ell)
    (hram : ramificationIndex F K = ell)
    {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    (j : ℕ) (hj : j ≤ ell) :
    (integerCeilingDiv ((j : ℤ) * a) ell : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  classical
  letI : Infinite F := nonarchimedeanLocalFieldInfinite F
  have hjdegree : j ≤ Module.finrank F K := by simpa [hdegree] using hj
  have hprod (t : Finset Gal(K/F)) :
      t.card • (a : WithTop ℤ) ≤ ord K (∏ σ ∈ t, σ x) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert σ t hσ ih =>
        have hσx : (a : WithTop ℤ) ≤ ord K (σ x) := by simpa using hx
        simpa [Finset.card_insert_of_notMem, hσ, succ_nsmul, add_comm] using
          add_le_add hσx ih
  have hup : (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord K (algebraMap F K (elementarySymmetric F K j x)) := by
    rw [algebraMap_elementarySymmetric_eq_esymm_galois, galoisConjugates,
      Finset.esymm_map_val]
    apply ord_sum K
    intro t ht
    have htcard : t.card = j := (Finset.mem_powersetCard.mp ht).2
    have htbound := hprod t
    rw [htcard] at htbound
    calc
      (((j : ℤ) * a : ℤ) : WithTop ℤ) = j • (a : WithTop ℤ) := by
        rw [← WithTop.coe_nsmul]
        congr
      _ ≤ ord K (∏ σ ∈ t, σ x) := htbound
  rw [ord_algebraMap, hram] at hup
  by_cases hs : ord F (elementarySymmetric F K j x) = ⊤
  · simp [hs]
  · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hs
    rw [← hz] at hup ⊢
    rw [← WithTop.coe_nsmul] at hup
    simp only [WithTop.coe_le_coe] at hup ⊢
    apply (integerCeilingDiv_le_iff ((j : ℤ) * a) z ell hell).2
    simpa [nsmul_eq_mul, mul_comm] using hup

/-- The exact intermediate-coefficient bound used in the tame odd prime-degree range. -/
theorem tame_elementarySymmetric_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (ell : ℕ) (a : ℤ) (hell : ell.Prime) (_hell2 : ell ≠ 2)
    (_htame : residueCharacteristic F ≠ ell)
    (hdegree : Module.finrank F K = ell)
    (hram : ramificationIndex F K = ell)
    {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    {j : ℕ} (_hjtwo : 2 ≤ j) (hjlt : j < ell) :
    (integerCeilingDiv ((j : ℤ) * a) ell : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  exact totallyRamified_elementarySymmetric_bound F K ell a hell.pos hdegree hram hx j hjlt.le

/-- Strong wild bound with `D = (p - 1)T`, for exactly `1 ≤ j < p`. -/
theorem wild_elementarySymmetric_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T : ℕ) (a : ℤ) (hp : p.Prime) (hT : 2 ≤ T)
    (hres : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    {j : ℕ} (hjpos : 1 ≤ j) (hjlt : j < p) :
    (((j : ℤ) * a + (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  let D : ℤ := (((p - 1) * T : ℕ) : ℤ)
  have hp0 : 0 < p := hp.pos
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp0
  have hDnat : p ≤ (p - 1) * T := by
    have htwo : p ≤ (p - 1) * 2 := by omega
    exact htwo.trans (Nat.mul_le_mul_left (p - 1) hT)
  have hDZ : (p : ℤ) ≤ D := by
    dsimp only [D]
    exact_mod_cast hDnat
  change (((j : ℤ) * a + D) / (p : ℤ) : ℤ) ≤
    ord F (elementarySymmetric F K j x)
  revert hjpos hjlt
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjpos hjlt
      let target : ℤ := ((j : ℤ) * a + D) / (p : ℤ)
      have hjord : ord F (j : F) = 0 := by
        apply ord_natCast_eq_zero_of_lt_residueCharacteristic F hjpos
        simpa [hres] using hjlt
      have hsum : (target : WithTop ℤ) ≤
          ord F (∑ b ∈ antidiagonal j with b.1 < j,
            (-1 : F) ^ b.1 * elementarySymmetric F K b.1 x *
              galoisPowerSum F K b.2 x) := by
        apply ord_sum F
        intro b hb
        simp only [Finset.mem_filter] at hb
        have hbadd : b.1 + b.2 = j := by simpa using hb.1
        have hb1lt : b.1 < j := hb.2
        have hb2pos : 1 ≤ b.2 := by omega
        by_cases hb10 : b.1 = 0
        · have hb2j : b.2 = j := by omega
          have hpower := powerSum_bound F K p D a hp0 hdegree htrace hx b.2 hb2pos
          rw [hb2j] at hpower
          simpa [target, hb10, hb2j, elementarySymmetric_zero] using hpower
        · have hb1pos : 1 ≤ b.1 := Nat.one_le_iff_ne_zero.mpr hb10
          have hb1p : b.1 < p := hb1lt.trans hjlt
          have hcoeff := ih b.1 hb1lt hb1pos hb1p
          have hpower := powerSum_bound F K p D a hp0 hdegree htrace hx b.2 hb2pos
          have hbcast : (b.1 : ℤ) + (b.2 : ℤ) = (j : ℤ) := by
            exact_mod_cast hbadd
          have hsplit : (j : ℤ) * a = (b.1 : ℤ) * a + (b.2 : ℤ) * a := by
            rw [← hbcast]
            ring
          have harith : target ≤
              (((b.1 : ℤ) * a + D) / (p : ℤ)) +
                (((b.2 : ℤ) * a + D) / (p : ℤ)) := by
            dsimp only [target]
            rw [hsplit]
            exact ediv_add_shift_le_add_ediv (p : ℤ) D
              ((b.1 : ℤ) * a) ((b.2 : ℤ) * a) hpZ hDZ
          have hsumBounds :
              (((((b.1 : ℤ) * a + D) / (p : ℤ)) +
                (((b.2 : ℤ) * a + D) / (p : ℤ)) : ℤ) : WithTop ℤ) ≤
                ord F (elementarySymmetric F K b.1 x) +
                  ord F (galoisPowerSum F K b.2 x) := by
            rw [WithTop.coe_add]
            exact add_le_add hcoeff hpower
          calc
            (target : WithTop ℤ) ≤
                (((((b.1 : ℤ) * a + D) / (p : ℤ)) +
                  (((b.2 : ℤ) * a + D) / (p : ℤ)) : ℤ) : WithTop ℤ) :=
              WithTop.coe_le_coe.mpr harith
            _ ≤ ord F (elementarySymmetric F K b.1 x) +
                ord F (galoisPowerSum F K b.2 x) := hsumBounds
            _ = ord F ((-1 : F) ^ b.1 * elementarySymmetric F K b.1 x *
                galoisPowerSum F K b.2 x) := by simp
      have hnewton := elementarySymmetric_newton_identity F K x j
      calc
        (target : WithTop ℤ) ≤
            ord F ((-1 : F) ^ (j + 1) *
              ∑ b ∈ antidiagonal j with b.1 < j,
                (-1 : F) ^ b.1 * elementarySymmetric F K b.1 x *
                  galoisPowerSum F K b.2 x) := by simpa using hsum
        _ = ord F ((j : F) * elementarySymmetric F K j x) :=
          congrArg (ord F) hnewton.symm
        _ = ord F (elementarySymmetric F K j x) := by simp [hjord]

/-- The manuscript's wild prime-degree package.  Here `t` is an actual lower break,
`T = t + 1`, `D = (p - 1)T`, and the terminal coefficient is treated separately as the norm. -/
theorem wild_symmetric_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    (t : ℕ) (_hbreak : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueCharacteristic F = Module.finrank F K)
    (hram : ramificationIndex F K = Module.finrank F K)
    (htrace : TraceIdealLowerBound F K (Module.finrank F K)
      (wildDifferentContribution (Module.finrank F K) t))
    (a : ℤ) {x : K} (hx : (a : WithTop ℤ) ≤ ord K x) :
    (∀ {j : ℕ}, 1 ≤ j → j < Module.finrank F K →
      (((j : ℤ) * a + wildDifferentContribution (Module.finrank F K) t) /
          (Module.finrank F K : ℤ) : ℤ) ≤
        ord F (elementarySymmetric F K j x)) ∧
      (ord F (elementarySymmetric F K (Module.finrank F K) x) = ord K x ∧
        (a : WithTop ℤ) ≤
          ord F (elementarySymmetric F K (Module.finrank F K) x)) := by
  have hp := PrimeCyclicExtension.degree_prime F K
  have hT : 2 ≤ t + 1 := by omega
  constructor
  · intro j hjpos hjlt
    simpa [wildDifferentContribution] using
      (wild_elementarySymmetric_bound F K (Module.finrank F K) (t + 1) a
        hp hT hres rfl (by simpa [wildDifferentContribution] using htrace) hx hjpos hjlt)
  · have hend := elementarySymmetric_degree_ord F K (Module.finrank F K) rfl hram x
    exact ⟨hend, hend.symm ▸ hx⟩

/-- For nonnegative inputs, every nonterminal wild coefficient has the uniform `D / p`
lower bound used in the norm--trace correction calculation. -/
theorem wild_elementarySymmetric_uniform_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T : ℕ) (a : ℤ) (hp : p.Prime) (hT : 2 ≤ T)
    (hres : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    {x : K} (hx : (a : WithTop ℤ) ≤ ord K x) (ha : 0 ≤ a)
    {j : ℕ} (hjpos : 1 ≤ j) (hjlt : j < p) :
    (((((p - 1) * T : ℕ) : ℤ) / (p : ℤ) : ℤ) : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  have hmain := wild_elementarySymmetric_bound F K p T a hp hT hres hdegree htrace hx hjpos hjlt
  apply (WithTop.coe_le_coe.mpr ?_).trans hmain
  apply Int.ediv_le_ediv (by exact_mod_cast hp.pos)
  nlinarith [show (0 : ℤ) ≤ (j : ℤ) by positivity]

/-- Numerical specialization that kills exactly the intermediate range `2 ≤ j < p` at a
requested norm-truncation depth.  For `p = 2` the range is empty. -/
theorem wild_intermediateSymmetric_bound
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T q r : ℕ) (hp : p.Prime) (hT : 2 ≤ T)
    (hres : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (hdepth : p * r ≤ 2 * q + (p - 1) * T)
    {x : K} (hx : ((q : ℕ) : WithTop ℤ) ≤ ord K x)
    {j : ℕ} (hjtwo : 2 ≤ j) (hjlt : j < p) :
    ((r : ℕ) : WithTop ℤ) ≤ ord F (elementarySymmetric F K j x) := by
  have hmain := wild_elementarySymmetric_bound F K p T (q : ℤ) hp hT hres hdegree htrace
    hx (by omega) hjlt
  apply (WithTop.coe_le_coe.mpr ?_).trans hmain
  have hjq : 2 * q ≤ j * q := Nat.mul_le_mul_right q hjtwo
  have hnum : p * r ≤ j * q + (p - 1) * T := hdepth.trans (Nat.add_le_add_right hjq _)
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  rw [Int.le_ediv_iff_mul_le hpZ]
  have hnumZ : ((p * r : ℕ) : ℤ) ≤ ((j * q + (p - 1) * T : ℕ) : ℤ) := by
    exact_mod_cast hnum
  simpa [mul_comm] using hnumZ

end LanglandsFirstMainLemma
