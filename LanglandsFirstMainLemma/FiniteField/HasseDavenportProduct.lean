import LanglandsFirstMainLemma.FiniteField.CharacterAPI
import LanglandsFirstMainLemma.FiniteField.HDProductParametrization
import LanglandsFirstMainLemma.FiniteField.HasseDavenportLift
import LanglandsFirstMainLemma.Basic.FiniteProducts
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Hasse--Davenport multiplication

The proof follows Appendix A of Otsubo, *Hypergeometric functions over finite fields*.
The only Davenport--Hasse input in the rational-point count is the extension-field
**lifting** identity already proved in `HasseDavenportLift`; the multiplication identity
proved here is not used in its own proof.

All multiplicative characters below are Mathlib `MulChar`s.  In particular every one of
them, including the trivial character, has value zero at the field element zero.  This is
the convention used in Otsubo's Jacobi sums and is important in every point count.
-/

open scoped BigOperators
open Finset
open Polynomial

namespace LanglandsFirstMainLemma

noncomputable section

universe u v

variable {k : Type u} {K : Type v}
  [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]

/-- The zero-extended weight of a tuple of finite-field elements. -/
private def generalizedJacobiWeight {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (x : Fin r → k) : ℂ :=
  ∏ i, alpha i (x i)

/-- The fiber at `a` of the generalized Jacobi convolution. -/
private def generalizedJacobiFiber {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (a : k) : ℂ := by
  classical
  exact ∑ x : Fin r → k,
    if (∑ i, x i) = a then generalizedJacobiWeight alpha x else 0

/-- The generalized Jacobi sum, with every character (also `1`) extended by zero at zero. -/
private def generalizedJacobiSum {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) : ℂ :=
  generalizedJacobiFiber alpha 1

private def generalizedJacobiProduct {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) : FiniteMulChar k :=
  ∏ i, alpha i

private def scaleTupleEquiv {r : ℕ} (a : k) (ha : a ≠ 0) :
    (Fin r → k) ≃ (Fin r → k) where
  toFun x i := a * x i
  invFun x i := a⁻¹ * x i
  left_inv x := by
    funext i
    simp [ha]
  right_inv x := by
    funext i
    simp [ha]

@[simp] private lemma scaleTupleEquiv_apply {r : ℕ} (a : k) (ha : a ≠ 0)
    (x : Fin r → k) (i : Fin r) :
    scaleTupleEquiv a ha x i = a * x i := rfl

private lemma generalizedJacobiProduct_apply_of_ne_zero {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) {a : k} (ha : a ≠ 0) :
    generalizedJacobiProduct alpha a = ∏ i, alpha i a := by
  classical
  have hs : ∀ s : Finset (Fin r),
      (∏ i ∈ s, alpha i) a = ∏ i ∈ s, alpha i a := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)]
    | @insert i s hi ih => simp [hi, MulChar.mul_apply, ih]
  simpa [generalizedJacobiProduct] using hs Finset.univ

private lemma generalizedJacobiFiber_ne_zero {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) {a : k} (ha : a ≠ 0) :
    generalizedJacobiFiber alpha a =
      generalizedJacobiProduct alpha a * generalizedJacobiSum alpha := by
  classical
  rw [generalizedJacobiFiber, generalizedJacobiSum, generalizedJacobiFiber,
    ← (scaleTupleEquiv a ha).sum_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [scaleTupleEquiv_apply, generalizedJacobiWeight]
  have hsum : (∑ i, a * x i) = a * ∑ i, x i := by
    rw [Finset.mul_sum]
  rw [hsum]
  by_cases hx : (∑ i, x i) = 1
  · rw [if_pos hx, if_pos (by simp [hx])]
    rw [generalizedJacobiProduct_apply_of_ne_zero alpha ha]
    simp_rw [map_mul]
    rw [Finset.prod_mul_distrib]
  · have hscaled : a * ∑ i, x i ≠ a := by
      intro h
      apply hx
      exact mul_left_cancel₀ ha (by simpa using h)
    simp [hx, hscaled]

private lemma sum_generalizedJacobiFiber {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) :
    (∑ a : k, generalizedJacobiFiber alpha a) =
      ∏ i, ∑ x : k, alpha i x := by
  classical
  rw [Fintype.prod_sum]
  simp only [generalizedJacobiFiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [generalizedJacobiWeight]

private lemma prod_gaussSum_eq_sum_generalizedJacobiFiber {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (psi : FiniteAddChar k) :
    (∏ i, gaussSum (alpha i) psi) =
      ∑ a : k, generalizedJacobiFiber alpha a * psi a := by
  classical
  simp only [gaussSum]
  rw [Fintype.prod_sum]
  simp only [generalizedJacobiFiber]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]
  have hpsi : psi (∑ i, x i) = ∏ i, psi (x i) := by
    have hs : ∀ s : Finset (Fin r),
        psi (∑ i ∈ s, x i) = ∏ i ∈ s, psi (x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, psi.map_add_eq_mul, ih]
    simpa using hs Finset.univ
  rw [← hpsi]
  simp [generalizedJacobiWeight]

private lemma sum_generalizedJacobiFiber_eq_zero_add {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) :
    (∑ a : k, generalizedJacobiFiber alpha a) =
      generalizedJacobiFiber alpha 0 +
        generalizedJacobiSum alpha *
          (∑ a : k, generalizedJacobiProduct alpha a) := by
  classical
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (0 : k))]
  have hprod :
      (∑ a : k, generalizedJacobiProduct alpha a) =
        ∑ a ∈ (Finset.univ \ {0}), generalizedJacobiProduct alpha a := by
    rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (0 : k))]
    rw [(generalizedJacobiProduct alpha).map_zero]
    simp
  rw [hprod, Finset.mul_sum]
  rw [add_comm (∑ a ∈ (Finset.univ \ {0}), generalizedJacobiFiber alpha a)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := by simpa using ha
  rw [generalizedJacobiFiber_ne_zero alpha ha0]
  ring

private lemma sum_generalizedJacobiFiber_mul_addChar_eq_zero_add {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (psi : FiniteAddChar k) :
    (∑ a : k, generalizedJacobiFiber alpha a * psi a) =
      generalizedJacobiFiber alpha 0 +
        generalizedJacobiSum alpha *
          gaussSum (generalizedJacobiProduct alpha) psi := by
  classical
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (0 : k))]
  simp only [AddChar.map_zero_eq_one, mul_one]
  have hgauss :
      gaussSum (generalizedJacobiProduct alpha) psi =
        ∑ a ∈ (Finset.univ \ {0}),
          generalizedJacobiProduct alpha a * psi a := by
    rw [gaussSum, Finset.sum_eq_sum_sdiff_singleton_add
      (Finset.mem_univ (0 : k))]
    rw [(generalizedJacobiProduct alpha).map_zero]
    simp
  rw [hgauss, Finset.mul_sum]
  rw [add_comm
    (∑ a ∈ (Finset.univ \ {0}), generalizedJacobiFiber alpha a * psi a)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := by simpa using ha
  rw [generalizedJacobiFiber_ne_zero alpha ha0]
  ring

private lemma sum_trivialFiniteMulChar :
    (∑ a : k, (1 : FiniteMulChar k) a) = (Fintype.card k : ℂ) - 1 := by
  classical
  rw [MulChar.sum_one_eq_card_units, Fintype.card_units,
    Nat.cast_sub Fintype.card_pos]
  norm_num

private lemma prod_character_sums_eq_zero_of_exists_nontrivial {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (h : ∃ i, alpha i ≠ 1) :
    (∏ i, ∑ a : k, alpha i a) = 0 := by
  classical
  obtain ⟨i, hi⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact MulChar.sum_eq_zero_of_ne_one hi

private lemma exists_nontrivial_of_generalizedJacobiProduct_ne_one {r : ℕ}
    (alpha : Fin r → FiniteMulChar k)
    (h : generalizedJacobiProduct alpha ≠ 1) :
    ∃ i, alpha i ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  apply h
  simp [generalizedJacobiProduct, hall]

/-- Generalized Gauss--Jacobi when the product character is nontrivial. -/
private theorem generalizedGaussJacobi_of_product_ne_one {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (psi : FiniteAddChar k)
    (hprod : generalizedJacobiProduct alpha ≠ 1) :
    (∏ i, gaussSum (alpha i) psi) =
      generalizedJacobiSum alpha *
        gaussSum (generalizedJacobiProduct alpha) psi := by
  classical
  have hsome : ∃ i, alpha i ≠ 1 :=
    exists_nontrivial_of_generalizedJacobiProduct_ne_one alpha hprod
  have hchars : (∏ i, ∑ a : k, alpha i a) = 0 :=
    prod_character_sums_eq_zero_of_exists_nontrivial alpha hsome
  have hprodsum : (∑ a : k, generalizedJacobiProduct alpha a) = 0 :=
    MulChar.sum_eq_zero_of_ne_one hprod
  have hzero : generalizedJacobiFiber alpha 0 = 0 := by
    have h := (sum_generalizedJacobiFiber_eq_zero_add alpha).symm.trans
      (sum_generalizedJacobiFiber alpha)
    rw [hprodsum, mul_zero, add_zero, hchars] at h
    exact h
  rw [prod_gaussSum_eq_sum_generalizedJacobiFiber,
    sum_generalizedJacobiFiber_mul_addChar_eq_zero_add, hzero, zero_add]

/-- Exact generalized Gauss--Jacobi formula when the product character is trivial but the
family is not the all-trivial family.  It is cross-multiplied, so no possibly zero Gauss sum
is divided out. -/
private theorem generalizedGaussJacobi_of_product_eq_one {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (psi : FiniteAddChar k)
    (hpsi : psi ≠ 1) (hprod : generalizedJacobiProduct alpha = 1)
    (hsome : ∃ i, alpha i ≠ 1) :
    (∏ i, gaussSum (alpha i) psi) =
      -(Fintype.card k : ℂ) * generalizedJacobiSum alpha := by
  classical
  have hchars : (∏ i, ∑ a : k, alpha i a) = 0 :=
    prod_character_sums_eq_zero_of_exists_nontrivial alpha hsome
  have hprodsum :
      (∑ a : k, generalizedJacobiProduct alpha a) =
        (Fintype.card k : ℂ) - 1 := by
    rw [hprod]
    exact sum_trivialFiniteMulChar
  have hzero :
      generalizedJacobiFiber alpha 0 +
        generalizedJacobiSum alpha * ((Fintype.card k : ℂ) - 1) = 0 := by
    calc
      _ = ∑ a : k, generalizedJacobiFiber alpha a := by
        rw [sum_generalizedJacobiFiber_eq_zero_add, hprodsum]
      _ = ∏ i, ∑ a : k, alpha i a := sum_generalizedJacobiFiber alpha
      _ = 0 := hchars
  calc
    (∏ i, gaussSum (alpha i) psi) =
        generalizedJacobiFiber alpha 0 +
          generalizedJacobiSum alpha *
            gaussSum (generalizedJacobiProduct alpha) psi := by
      rw [prod_gaussSum_eq_sum_generalizedJacobiFiber,
        sum_generalizedJacobiFiber_mul_addChar_eq_zero_add]
    _ = generalizedJacobiFiber alpha 0 - generalizedJacobiSum alpha := by
      rw [hprod, gaussSum_one_left hpsi]
      ring
    _ = -(Fintype.card k : ℂ) * generalizedJacobiSum alpha := by
      linear_combination hzero

/-- Exact zero-extension count for the all-trivial family. -/
private theorem generalizedJacobiSum_all_trivial {r : ℕ}
    (alpha : Fin r → FiniteMulChar k) (psi : FiniteAddChar k)
    (hpsi : psi ≠ 1) (hall : ∀ i, alpha i = 1) :
    (Fintype.card k : ℂ) * generalizedJacobiSum alpha =
      ((Fintype.card k : ℂ) - 1) ^ r - (-1 : ℂ) ^ r := by
  classical
  have hprod : generalizedJacobiProduct alpha = 1 := by
    simp [generalizedJacobiProduct, hall]
  have hchars :
      (∏ i, ∑ a : k, alpha i a) = ((Fintype.card k : ℂ) - 1) ^ r := by
    simp_rw [hall]
    rw [sum_trivialFiniteMulChar]
    simp
  have hgauss :
      (∏ i, gaussSum (alpha i) psi) = (-1 : ℂ) ^ r := by
    simp_rw [hall]
    rw [gaussSum_one_left hpsi]
    simp
  have hprodsum :
      (∑ a : k, generalizedJacobiProduct alpha a) =
        (Fintype.card k : ℂ) - 1 := by
    rw [hprod]
    exact sum_trivialFiniteMulChar
  have htotal :
      generalizedJacobiFiber alpha 0 +
          generalizedJacobiSum alpha * ((Fintype.card k : ℂ) - 1) =
        ((Fintype.card k : ℂ) - 1) ^ r := by
    calc
      _ = ∑ a : k, generalizedJacobiFiber alpha a := by
        rw [sum_generalizedJacobiFiber_eq_zero_add, hprodsum]
      _ = ∏ i, ∑ a : k, alpha i a := sum_generalizedJacobiFiber alpha
      _ = _ := hchars
  have hgaussFiber :
      generalizedJacobiFiber alpha 0 - generalizedJacobiSum alpha =
        (-1 : ℂ) ^ r := by
    calc
      _ = generalizedJacobiFiber alpha 0 +
          generalizedJacobiSum alpha *
            gaussSum (generalizedJacobiProduct alpha) psi := by
        rw [hprod, gaussSum_one_left hpsi]
        ring
      _ = ∑ a : k, generalizedJacobiFiber alpha a * psi a := by
        rw [sum_generalizedJacobiFiber_mul_addChar_eq_zero_add]
      _ = ∏ i, gaussSum (alpha i) psi :=
        (prod_gaussSum_eq_sum_generalizedJacobiFiber alpha psi).symm
      _ = _ := hgauss
  linear_combination htotal - hgaussFiber

private lemma normMulChar_mul (χ φ : FiniteMulChar k) :
    normMulChar k K (χ * φ) = normMulChar k K χ * normMulChar k K φ := by
  ext x
  simp [normMulChar_apply, MulChar.mul_apply]

/-- The ordinary-Gauss-sum form of the already proved extension-field lifting theorem.
This is the sole Davenport--Hasse input in Otsubo's cycle calculation. -/
private lemma gaussSum_norm_trace_lift
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    gaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
      -((-gaussSum χ ψ) ^ Module.finrank k K) := by
  have h := hasseDavenportLift (K := K) χ⁻¹ ψ hψ
  have h' :
      -gaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
        (-gaussSum χ ψ) ^ Module.finrank k K := by
    simpa [langlandsGaussSum, normMulChar_inv] using h
  calc
    gaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
        -(-gaussSum (normMulChar k K χ) (traceAddChar k K ψ)) := by ring
    _ = -((-gaussSum χ ψ) ^ Module.finrank k K) := congrArg Neg.neg h'

/-- Jacobi lifting when the product character is nontrivial.  The cancellation is by a
Gauss sum whose nonvanishing is proved before it is cancelled. -/
private lemma jacobiSum_norm_trace_lift_of_mul_ne_one
    {χ φ : FiniteMulChar k} (hχφ : χ * φ ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    jacobiSum (normMulChar k K χ) (normMulChar k K φ) =
      -((-jacobiSum χ φ) ^ Module.finrank k K) := by
  let χK := normMulChar k K χ
  let φK := normMulChar k K φ
  have hmul : normMulChar k K (χ * φ) = χK * φK := normMulChar_mul χ φ
  have hχKφK : χK * φK ≠ 1 := by
    rw [← hmul]
    exact (normMulChar_ne_one_iff k K (χ * φ)).mpr hχφ
  have hK := jacobiSum_mul_nontrivial hχKφK (traceAddChar k K ψ)
  have hk := jacobiSum_mul_nontrivial hχφ ψ
  have hGprodK := gaussSum_norm_trace_lift (K := K) (χ * φ) ψ hψ
  have hGχK := gaussSum_norm_trace_lift (K := K) χ ψ hψ
  have hGφK := gaussSum_norm_trace_lift (K := K) φ ψ hψ
  have hGprodK0 : gaussSum (χK * φK) (traceAddChar k K ψ) ≠ 0 :=
    gaussSum_ne_zero ((traceAddChar_ne_one_iff k K ψ).mpr hψ)
  apply mul_left_injective₀ hGprodK0
  change
    jacobiSum χK φK * gaussSum (χK * φK) (traceAddChar k K ψ) =
      -((-jacobiSum χ φ) ^ Module.finrank k K) *
        gaussSum (χK * φK) (traceAddChar k K ψ)
  rw [mul_comm (jacobiSum χK φK), hK]
  change
    gaussSum (normMulChar k K χ) (traceAddChar k K ψ) *
        gaussSum (normMulChar k K φ) (traceAddChar k K ψ) =
      -((-jacobiSum χ φ) ^ Module.finrank k K) *
        gaussSum (χK * φK) (traceAddChar k K ψ)
  rw [mul_comm (-((-jacobiSum χ φ) ^ Module.finrank k K))]
  rw [← hmul, hGχK, hGφK, hGprodK]
  calc
    -((-gaussSum χ ψ) ^ Module.finrank k K) *
          -((-gaussSum φ ψ) ^ Module.finrank k K) =
        ((-gaussSum χ ψ) * (-gaussSum φ ψ)) ^ Module.finrank k K := by
          rw [mul_pow]
          ring
    _ = (gaussSum χ ψ * gaussSum φ ψ) ^ Module.finrank k K := by
          congr 1
          ring
    _ = (gaussSum (χ * φ) ψ * jacobiSum χ φ) ^ Module.finrank k K :=
          congrArg (fun z : ℂ => z ^ Module.finrank k K) hk.symm
    _ = ((-gaussSum (χ * φ) ψ) * (-jacobiSum χ φ)) ^
          Module.finrank k K := by
          congr 1
          ring
    _ = -((-gaussSum (χ * φ) ψ) ^ Module.finrank k K) *
          -((-jacobiSum χ φ) ^ Module.finrank k K) := by
          rw [mul_pow]
          ring

/-- Otsubo's signed binary Jacobi sum. -/
private def signedBinaryJacobiSum (χ φ : FiniteMulChar k) : ℂ :=
  -jacobiSum χ φ

private lemma signedBinaryJacobiSum_norm_lift_of_mul_ne_one
    {χ φ : FiniteMulChar k} (hχφ : χ * φ ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    signedBinaryJacobiSum (normMulChar k K χ) (normMulChar k K φ) =
      signedBinaryJacobiSum χ φ ^ Module.finrank k K := by
  rw [signedBinaryJacobiSum, signedBinaryJacobiSum,
    jacobiSum_norm_trace_lift_of_mul_ne_one hχφ ψ hψ]
  ring

/-- The product-character-trivial branch of Jacobi lifting.  Otsubo uses it only with
the first character nontrivial, so the exceptional pair `(1,1)` never occurs. -/
private lemma signedBinaryJacobiSum_norm_lift_of_mul_eq_one
    {χ φ : FiniteMulChar k} (hχ : χ ≠ 1) (hχφ : χ * φ = 1) :
    signedBinaryJacobiSum (normMulChar k K χ) (normMulChar k K φ) =
      signedBinaryJacobiSum χ φ ^ Module.finrank k K := by
  have hφ : φ = χ⁻¹ := eq_inv_of_mul_eq_one_right hχφ
  subst φ
  have hχK : normMulChar k K χ ≠ 1 :=
    (normMulChar_ne_one_iff k K χ).mpr hχ
  rw [normMulChar_inv, signedBinaryJacobiSum, signedBinaryJacobiSum,
    jacobiSum_nontrivial_inv hχK, jacobiSum_nontrivial_inv hχ]
  simp only [neg_neg]
  rw [normMulChar_apply, show (-1 : K) = algebraMap k K (-1 : k) by simp,
    residueNorm_algebraMap, map_pow]

private lemma signedBinaryJacobiSum_norm_lift
    {χ φ : FiniteMulChar k} (hχ : χ ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    signedBinaryJacobiSum (normMulChar k K χ) (normMulChar k K φ) =
      signedBinaryJacobiSum χ φ ^ Module.finrank k K := by
  by_cases hχφ : χ * φ = 1
  · exact signedBinaryJacobiSum_norm_lift_of_mul_eq_one hχ hχφ
  · exact signedBinaryJacobiSum_norm_lift_of_mul_ne_one hχφ ψ hψ

private lemma ell_ne_zero_in_field (ell : ℕ)
    (hdiv : ell ∣ Fintype.card k - 1) : (ell : k) ≠ 0 := by
  classical
  intro hell
  have hchar : ringChar k ∣ ell :=
    (CharP.cast_eq_zero_iff k (ringChar k) ell).mp hell
  letI : Fact (Nat.Prime (ringChar k)) := ⟨CharP.prime_ringChar k⟩
  have hcq : ringChar k ∣ Fintype.card k := by
    exact (prime_dvd_char_iff_dvd_card (ringChar k)).mp (dvd_refl _)
  have hqpos : 1 ≤ Fintype.card k := Fintype.card_pos
  have hcop : Nat.Coprime (Fintype.card k - 1) (Fintype.card k) :=
    (Nat.coprime_self_sub_left hqpos).mpr (Nat.coprime_one_left _)
  have hellcop : Nat.Coprime ell (Fintype.card k) :=
    Nat.Coprime.of_dvd_left hdiv hcop
  have hone : ringChar k = 1 := Nat.eq_one_of_dvd_coprimes hellcop hchar hcq
  exact (CharP.prime_ringChar k).ne_one hone

/-- Exact root-of-unity parametrization in the cyclic character group. -/
private lemma mulChar_root_param (ell : ℕ) (eta alpha : FiniteMulChar k)
    (heta : orderOf eta = ell) (halpha : alpha ^ ell = 1) :
    ∃ i < ell, eta ^ i = alpha := by
  classical
  have hell : ell ≠ 0 := by simpa [← heta] using (orderOf_pos eta).ne'
  letI : NeZero ell := ⟨hell⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hprim : IsPrimitiveRoot (eta (g : k)) ell := by
    constructor
    · rw [← MulChar.pow_apply_coe, ← heta, pow_orderOf_eq_one]
      exact MulChar.one_apply_coe g
    · intro n hn
      rw [← heta, orderOf_dvd_iff_pow_eq_one]
      rw [MulChar.eq_iff hg]
      simpa [MulChar.pow_apply_coe] using hn
  have haeval : alpha (g : k) ^ ell = 1 := by
    rw [← MulChar.pow_apply_coe, halpha]
    exact MulChar.one_apply_coe g
  obtain ⟨i, hi, hei⟩ := hprim.eq_pow_of_pow_eq_one haeval
  refine ⟨i, hi, ?_⟩
  rw [MulChar.eq_iff hg]
  simpa [MulChar.pow_apply_coe] using hei

private lemma exists_primitiveRoot_field (ell : ℕ)
    (hdiv : ell ∣ Fintype.card k - 1) :
    ∃ z : k, IsPrimitiveRoot z ell := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hdiv' : ell ∣ orderOf g := by
    rw [hg, Nat.card_eq_fintype_card, Fintype.card_units]
    exact hdiv
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  let z : kˣ := g ^ (orderOf g / ell)
  have hzorder : orderOf z = ell := orderOf_pow_orderOf_div hg0 hdiv'
  refine ⟨(z : k), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
  exact hzorder

private lemma inv_mulChar_inv_cast_pow (χ : FiniteMulChar k) (ell : ℕ) :
    χ⁻¹ (((ell : k)⁻¹) ^ ell) = χ ((ell : k) ^ ell) := by
  rw [MulChar.inv_apply']
  congr 1
  rw [inv_pow, inv_inv]

private lemma gaussSum_eq_neg_langlandsGaussSum_inv
    (α : FiniteMulChar k) (ψ : FiniteAddChar k) :
    gaussSum α ψ = -langlandsGaussSum α⁻¹ ψ := by
  simp [langlandsGaussSum]

private lemma range_eq_insert_Icc {ell : ℕ} (hell : 0 < ell) :
    Finset.range ell = insert 0 (Finset.Icc 1 (ell - 1)) := by
  ext j
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

private lemma prod_range_eq_head_mul_Icc {M : Type*} [CommMonoid M]
    (f : ℕ → M) {ell : ℕ} (hell : 0 < ell) :
    (∏ j ∈ Finset.range ell, f j) =
      f 0 * ∏ j ∈ Finset.Icc 1 (ell - 1), f j := by
  rw [range_eq_insert_Icc hell, Finset.prod_insert]
  simp

private lemma card_pow_fiber_of_exists {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G]
    (d : ℕ) (hd : d ∣ Fintype.card G) (a : G)
    (ha : ∃ x : G, x ^ d = a) :
    Fintype.card {x : G // x ^ d = a} = d := by
  classical
  obtain ⟨x, rfl⟩ := ha
  let f : G →* G := powMonoidHom d
  calc
    Fintype.card {y : G // y ^ d = x ^ d} =
        Fintype.card ((f ⁻¹' {f x} : Set G)) := by
          apply Fintype.card_congr
          apply Equiv.setCongr
          ext y
          change (y ^ d = x ^ d) ↔ (powMonoidHom d) y = (powMonoidHom d) x
          rfl
    _ = Fintype.card f.ker := Fintype.card_congr (f.fiberEquivKer x)
    _ = d := by
      rw [Fintype.card_eq_nat_card, IsCyclic.card_powMonoidHom_ker,
        Nat.card_eq_fintype_card, Nat.gcd_eq_right hd]

private lemma normMulChar_one' :
    normMulChar k K (1 : FiniteMulChar k) = 1 := by
  ext x
  simp [normMulChar_apply, MulChar.one_apply]

private lemma normMulChar_pow (χ : FiniteMulChar k) (n : ℕ) :
    normMulChar k K (χ ^ n) = normMulChar k K χ ^ n := by
  induction n with
  | zero => simpa using (normMulChar_one' (k := k) (K := K))
  | succ n ih => rw [pow_succ, normMulChar_mul, ih, pow_succ]

private lemma orderOf_normMulChar (χ : FiniteMulChar k) :
    orderOf (normMulChar k K χ) = orderOf χ := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← normMulChar_pow, pow_orderOf_eq_one, normMulChar_one']
  · apply orderOf_dvd_of_pow_eq_one
    have hnorm :
        normMulChar k K (χ ^ orderOf (normMulChar k K χ)) = 1 := by
      rw [normMulChar_pow, pow_orderOf_eq_one]
    have hreflect : ∀ θ : FiniteMulChar k,
        normMulChar k K θ = 1 ↔ θ = 1 := by
      intro θ
      simpa only [not_ne_iff] using
        not_congr (normMulChar_ne_one_iff k K θ)
    exact (hreflect _).mp hnorm

private lemma neg_neg_pow_eq (z : ℂ) {d : ℕ} (hd : 0 < d) :
    -((-z) ^ d) = (-1 : ℂ) ^ (d - 1) * z ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [Nat.succ_sub_one, neg_pow, pow_succ]
  ring

private lemma pow_exists_iff_mulChar_eq_one (ell : ℕ)
    (η : FiniteMulChar k) (hη : orderOf η = ell) (u : kˣ) :
    (∃ x : kˣ, x ^ ell = u) ↔ η (u : k) = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hprim : IsPrimitiveRoot (η (g : k)) ell := by
    constructor
    · rw [← MulChar.pow_apply_coe, ← hη, pow_orderOf_eq_one]
      exact MulChar.one_apply_coe g
    · intro n hn
      rw [← hη, orderOf_dvd_iff_pow_eq_one]
      rw [MulChar.eq_iff hg]
      simpa [MulChar.pow_apply_coe] using hn
  constructor
  · rintro ⟨x, rfl⟩
    calc
      η ((x ^ ell : kˣ) : k) = η (x : k) ^ ell := by
        change ↑(η.toUnitHom (x ^ ell)) = (↑(η.toUnitHom x) : ℂ) ^ ell
        rw [map_pow]
        rfl
      _ = (η ^ ell) (x : k) := (MulChar.pow_apply_coe η ell x).symm
      _ = (η ^ orderOf η) (x : k) := by rw [hη]
      _ = 1 := by rw [pow_orderOf_eq_one]; exact MulChar.one_apply_coe x
  · intro hu
    have hug : u ∈ Submonoid.powers g :=
      mem_powers_iff_mem_zpowers.mpr (hg u)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff u g).mp hug
    have hpow : η (g : k) ^ n = 1 := by
      calc
        η (g : k) ^ n = η ((g ^ n : kˣ) : k) := by
          change (↑(η.toUnitHom g) : ℂ) ^ n = ↑(η.toUnitHom (g ^ n))
          rw [map_pow]
          rfl
        _ = η (u : k) := congrArg (fun z : kˣ ↦ η (z : k)) hn
        _ = 1 := hu
    obtain ⟨t, ht⟩ := (hprim.pow_eq_one_iff_dvd n).mp hpow
    refine ⟨g ^ t, ?_⟩
    rw [← hn]
    subst n
    rw [Nat.mul_comm]
    exact (pow_mul g t ell).symm

private lemma sum_character_powers_on_unit [DecidableEq k]
    (ell : ℕ) (η : FiniteMulChar k) (hη : orderOf η = ell) (u : kˣ) :
    (∑ j : Fin ell, (η ^ (j : ℕ)) (u : k)) =
      if ∃ x : kˣ, x ^ ell = u then (ell : ℂ) else 0 := by
  classical
  have hpow : η (u : k) ^ ell = 1 := by
    calc
      η (u : k) ^ ell = (η ^ ell) (u : k) :=
        (MulChar.pow_apply_coe η ell u).symm
      _ = (η ^ orderOf η) (u : k) := by rw [hη]
      _ = 1 := by rw [pow_orderOf_eq_one]; exact MulChar.one_apply_coe u
  by_cases hex : ∃ x : kˣ, x ^ ell = u
  · rw [if_pos hex]
    have hu : η (u : k) = 1 :=
      (pow_exists_iff_mulChar_eq_one ell η hη u).mp hex
    calc
      (∑ j : Fin ell, (η ^ (j : ℕ)) (u : k)) =
          ∑ j : Fin ell, η (u : k) ^ (j : ℕ) := by
            apply Fintype.sum_congr
            intro j
            exact MulChar.pow_apply_coe η (j : ℕ) u
      _ = ∑ j ∈ Finset.range ell, η (u : k) ^ j :=
        Fin.sum_univ_eq_sum_range (fun j ↦ η (u : k) ^ j) ell
      _ = (ell : ℂ) := by simp [hu]
  · rw [if_neg hex]
    have hu : η (u : k) ≠ 1 := by
      exact fun h ↦ hex ((pow_exists_iff_mulChar_eq_one ell η hη u).mpr h)
    calc
      (∑ j : Fin ell, (η ^ (j : ℕ)) (u : k)) =
          ∑ j : Fin ell, η (u : k) ^ (j : ℕ) := by
            apply Fintype.sum_congr
            intro j
            exact MulChar.pow_apply_coe η (j : ℕ) u
      _ = ∑ j ∈ Finset.range ell, η (u : k) ^ j :=
        Fin.sum_univ_eq_sum_range (fun j ↦ η (u : k) ^ j) ell
      _ = 0 := by rw [geom_sum_eq hu, hpow]; simp

private lemma cast_card_pow_fiber_eq_character_sum [DecidableEq k]
    (ell : ℕ) (η : FiniteMulChar k) (hη : orderOf η = ell)
    (hdiv : ell ∣ Fintype.card kˣ) (u : kˣ) :
    (Fintype.card {x : kˣ // x ^ ell = u} : ℂ) =
      ∑ j : Fin ell, (η ^ (j : ℕ)) (u : k) := by
  classical
  rw [sum_character_powers_on_unit ell η hη u]
  by_cases hex : ∃ x : kˣ, x ^ ell = u
  · rw [if_pos hex, card_pow_fiber_of_exists ell hdiv u hex]
  · rw [if_neg hex]
    haveI : IsEmpty {x : kˣ // x ^ ell = u} :=
      ⟨fun x ↦ hex ⟨x.1, x.2⟩⟩
    rw [Fintype.card_eq_zero]
    simp

private lemma sum_field_eq_zero_add_units [DecidableEq k] (f : k → ℂ) :
    (∑ x : k, f x) = f 0 + ∑ u : kˣ, f (u : k) := by
  classical
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (0 : k))]
  rw [add_comm]
  congr 1
  calc
    (∑ x ∈ (Finset.univ \ {0}), f x) =
        ∑ x : {x : k // x ≠ 0}, f x.1 := by
          apply Finset.sum_subtype
          intro x
          simp
    _ = ∑ u : kˣ, f (u : k) := by
      simpa using (Equiv.sum_comp unitsEquivNeZero
        (fun x : {x : k // x ≠ 0} ↦ f x.1)).symm

private lemma sum_units_comp_pow [DecidableEq k] (ell : ℕ) (f : kˣ → ℂ) :
    (∑ x : kˣ, f (x ^ ell)) =
      ∑ u : kˣ, (Fintype.card {x : kˣ // x ^ ell = u} : ℂ) * f u := by
  classical
  calc
    (∑ x : kˣ, f (x ^ ell)) =
        ∑ u : kˣ, ∑ _x : {x : kˣ // x ^ ell = u}, f u :=
      (Fintype.sum_fiberwise' (fun x : kˣ ↦ x ^ ell) f).symm
    _ = ∑ u : kˣ,
        (Fintype.card {x : kˣ // x ^ ell = u} : ℂ) * f u := by
      apply Fintype.sum_congr
      intro u
      simp [nsmul_eq_mul]

private lemma sum_fin_eq_zero_add_nonzero {ell : ℕ} [NeZero ell]
    (f : Fin ell → ℂ) :
    (∑ j : Fin ell, f j) =
      f 0 + ∑ j : {j : Fin ell // j.val ≠ 0}, f j.1 := by
  classical
  rw [Finset.sum_eq_sum_sdiff_singleton_add
    (Finset.mem_univ (0 : Fin ell)), add_comm]
  congr 1
  apply Finset.sum_subtype
  intro j
  simp

private lemma power_curve_sum_eq_one_add_jacobi [DecidableEq k]
    (ell : ℕ) (η α : FiniteMulChar k)
    (hη : orderOf η = ell) (hdiv : ell ∣ Fintype.card kˣ) :
    (∑ y : k, α (1 - y ^ ell)) =
      1 + ∑ j : Fin ell, jacobiSum α (η ^ (j : ℕ)) := by
  classical
  have hell : ell ≠ 0 := by
    simpa [← hη] using (orderOf_pos η).ne'
  let f : kˣ → ℂ := fun u ↦ α (1 - (u : k))
  calc
    (∑ y : k, α (1 - y ^ ell)) =
        α 1 + ∑ x : kˣ, α (1 - (x : k) ^ ell) := by
      rw [sum_field_eq_zero_add_units]
      simp [hell]
    _ = 1 + ∑ x : kˣ, f (x ^ ell) := by
      simp [f, Units.val_pow_eq_pow_val]
    _ = 1 + ∑ u : kˣ,
        (Fintype.card {x : kˣ // x ^ ell = u} : ℂ) * f u := by
      rw [sum_units_comp_pow]
    _ = 1 + ∑ u : kˣ,
        (∑ j : Fin ell, (η ^ (j : ℕ)) (u : k)) * f u := by
      congr 1
      apply Fintype.sum_congr
      intro u
      rw [cast_card_pow_fiber_eq_character_sum ell η hη hdiv u]
    _ = 1 + ∑ j : Fin ell, ∑ u : kˣ,
        (η ^ (j : ℕ)) (u : k) * f u := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = 1 + ∑ j : Fin ell, jacobiSum α (η ^ (j : ℕ)) := by
      congr 1
      apply Fintype.sum_congr
      intro j
      rw [jacobiSum_comm]
      change (∑ u : kˣ,
          (η ^ (j : ℕ)) (u : k) * α (1 - (u : k))) =
        ∑ x : k, (η ^ (j : ℕ)) x * α (1 - x)
      have hsplit := sum_field_eq_zero_add_units
        (fun x : k ↦ (η ^ (j : ℕ)) x * α (1 - x))
      rw [MulChar.map_zero, zero_mul, zero_add] at hsplit
      exact hsplit.symm

private lemma power_curve_norm_sum_eq_signed_jacobi_powers
    (ell : ℕ) (η α : FiniteMulChar k)
    (hη : orderOf η = ell) (hα : α ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    (∑ y : K, normMulChar k K α (1 - y ^ ell)) =
      (-1 : ℂ) ^ (Module.finrank k K - 1) *
        ∑ j : {j : Fin ell // j.val ≠ 0},
          jacobiSum α (η ^ (j.1 : ℕ)) ^ Module.finrank k K := by
  classical
  have hell : ell ≠ 0 := by
    simpa [← hη] using (orderOf_pos η).ne'
  letI : NeZero ell := ⟨hell⟩
  let ηK := normMulChar k K η
  let αK := normMulChar k K α
  have hηK : orderOf ηK = ell := by
    dsimp [ηK]
    rw [orderOf_normMulChar, hη]
  have hdivK : ell ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, ← hηK]
    exact MulChar.orderOf_dvd_card_sub_one K ηK
  have hcurve := power_curve_sum_eq_one_add_jacobi ell ηK αK hηK hdivK
  rw [hcurve, sum_fin_eq_zero_add_nonzero]
  have hαK : αK ≠ 1 := (normMulChar_ne_one_iff k K α).mpr hα
  have hzero : jacobiSum αK (ηK ^ ((0 : Fin ell) : ℕ)) = -1 := by
    rw [show ηK ^ ((0 : Fin ell) : ℕ) = 1 by simp]
    rw [jacobiSum_comm, jacobiSum_one_nontrivial hαK]
  rw [hzero]
  simp only [add_neg_cancel_left]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro j
  have hlift := signedBinaryJacobiSum_norm_lift (K := K)
    (χ := α) (φ := η ^ (j.1 : ℕ)) hα ψ hψ
  change -jacobiSum (normMulChar k K α)
      (normMulChar k K (η ^ (j.1 : ℕ))) =
    (-jacobiSum α (η ^ (j.1 : ℕ))) ^ Module.finrank k K at hlift
  have hnormPow :
      normMulChar k K (η ^ (j.1 : ℕ)) = ηK ^ (j.1 : ℕ) :=
    normMulChar_pow η (j.1 : ℕ)
  rw [hnormPow] at hlift
  have hd : 0 < Module.finrank k K := Module.finrank_pos
  have hordinary :
      jacobiSum αK (ηK ^ (j.1 : ℕ)) =
        (-1 : ℂ) ^ (Module.finrank k K - 1) *
          jacobiSum α (η ^ (j.1 : ℕ)) ^ Module.finrank k K := by
    rw [← neg_neg (jacobiSum αK (ηK ^ (j.1 : ℕ))), hlift]
    exact neg_neg_pow_eq _ hd
  exact hordinary

private def hdEmbeddingMultiplicity (x : K) : ℕ :=
  Module.finrank (↥(IntermediateField.adjoin k {x})) K

private theorem Matrix.hd_charpoly_blockDiagonal_eq_prod
    {R : Type*} [CommRing R]
    {m o : Type*} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]
    (M : o → Matrix m m R) :
    (Matrix.blockDiagonal M).charpoly = ∏ i, (M i).charpoly := by
  rw [Matrix.charpoly]
  have hcharmatrix :
      Matrix.charmatrix (Matrix.blockDiagonal M) =
        Matrix.blockDiagonal (fun i ↦ Matrix.charmatrix (M i)) := by
    apply Matrix.ext
    rintro ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b <;> by_cases hij : i = j <;>
      simp [Matrix.blockDiagonal_apply, hab, hij]
  rw [hcharmatrix, Matrix.det_blockDiagonal]
  rfl

private theorem hd_lmul_charpoly_eq_minpoly_pow (x : K) :
    (Algebra.lmul k K x).charpoly =
      (minpoly k x) ^ hdEmbeddingMultiplicity (k := k) x := by
  let E := ↥(IntermediateField.adjoin k {x})
  let xE : E :=
    ⟨x, IntermediateField.subset_adjoin k {x} (Set.mem_singleton x)⟩
  let pb : PowerBasis k E :=
    IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral x)
  let bK := Module.Free.chooseBasis E K
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex E K)
  letI := Classical.decEq (Module.Free.ChooseBasisIndex E K)
  have hx : algebraMap E K xE = x := rfl
  have hgen : pb.gen = xE := by
    simp only [pb, xE, E, IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hmin : minpoly k xE = minpoly k x := by
    rw [show xE = IntermediateField.AdjoinSimple.gen k x by
      apply Subtype.ext
      rfl]
    exact IntermediateField.minpoly_gen k x
  have hblock :
      Algebra.leftMulMatrix (pb.basis.smulTower bK) x =
        Matrix.blockDiagonal (fun _ ↦ Algebra.leftMulMatrix pb.basis xE) := by
    calc
      Algebra.leftMulMatrix (pb.basis.smulTower bK) x =
          Algebra.leftMulMatrix (pb.basis.smulTower bK) (algebraMap E K xE) := by
        exact congrArg (Algebra.leftMulMatrix (pb.basis.smulTower bK)) hx.symm
      _ = Matrix.blockDiagonal (fun _ ↦ Algebra.leftMulMatrix pb.basis xE) :=
        Algebra.smulTower_leftMulMatrix_algebraMap pb.basis bK xE
  calc
    (Algebra.lmul k K x).charpoly =
        (Algebra.leftMulMatrix (pb.basis.smulTower bK) x).charpoly := by
      exact (LinearMap.charpoly_toMatrix (Algebra.lmul k K x)
        (pb.basis.smulTower bK)).symm
    _ = (Matrix.blockDiagonal (fun _ ↦
          Algebra.leftMulMatrix pb.basis xE)).charpoly := by rw [hblock]
    _ = ∏ _ : Module.Free.ChooseBasisIndex E K,
          (Algebra.leftMulMatrix pb.basis xE).charpoly := by
      exact Matrix.hd_charpoly_blockDiagonal_eq_prod _
    _ = ∏ _ : Module.Free.ChooseBasisIndex E K, minpoly k x := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← hgen, charpoly_leftMulMatrix, hgen, hmin]
    _ = (minpoly k x) ^ Module.finrank E K := by
      rw [Finset.prod_const, Finset.card_univ, Module.finrank_eq_card_basis bK]
    _ = (minpoly k x) ^ hdEmbeddingMultiplicity (k := k) x := rfl

private theorem reverse_charpoly_lmul_eval_eq_norm (x : K) (z : k) :
    (Algebra.lmul k K x).charpoly.reverse.eval z =
      Algebra.norm k (1 - algebraMap k K z * x) := by
  classical
  let b := Module.Free.chooseBasis k K
  let M := Algebra.leftMulMatrix b x
  have hchar : (Algebra.lmul k K x).charpoly = M.charpoly := by
    exact (LinearMap.charpoly_toMatrix (Algebra.lmul k K x) b).symm
  rw [hchar, Matrix.reverse_charpoly]
  rw [Matrix.charpolyRev]
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  rw [Algebra.norm_eq_matrix_det b]
  apply congrArg Matrix.det
  calc
    (1 - X • M.map C).map (evalRingHom z) = 1 - z • M := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [M]
        exact mul_comm _ _
      · simp [M, hij]
        exact mul_comm _ _
    _ = Algebra.leftMulMatrix b (1 - algebraMap k K z * x) := by
      rw [map_sub, map_one, map_mul]
      simp [M, Algebra.smul_def]

private theorem reverse_minpoly_eval_pow_eq_norm (x : K) (z : k) :
    (minpoly k x).reverse.eval z ^ hdEmbeddingMultiplicity (k := k) x =
      Algebra.norm k (1 - algebraMap k K z * x) := by
  have hreverse_pow (p : k[X]) (n : ℕ) :
      (p ^ n).reverse = p.reverse ^ n := by
    induction n with
    | zero => rw [pow_zero, pow_zero, ← C_1, reverse_C]
    | succ n ih => simp [pow_succ, ih]
  rw [← reverse_charpoly_lmul_eval_eq_norm (k := k) x z,
    hd_lmul_charpoly_eq_minpoly_pow (k := k), hreverse_pow, eval_pow]

private noncomputable def hdRootProductWeight {ell : ℕ} (ζ : k)
    (α : FiniteMulChar k) : MonicWeight k ℂ :=
  MonicWeight.ofFun
    (fun p ↦ α (∏ j : Fin ell, p.reverse.eval (ζ ^ (j : ℕ))))
    (by
      rw [← C_1, reverse_C]
      simp)
    (by
      intro p q hp hq
      rw [reverse_mul]
      · simp only [eval_mul, Finset.prod_mul_distrib, map_mul]
      · simp [hp.leadingCoeff, hq.leadingCoeff])

private lemma prod_one_sub_primitive_powers_extension {ell : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ ell) (hell : 0 < ell) (x : K) :
    (∏ j : Fin ell,
        (1 - algebraMap k K (ζ ^ (j : ℕ)) * x)) = 1 - x ^ ell := by
  have hζK : IsPrimitiveRoot (algebraMap k K ζ) ell :=
    hζ.map_of_injective (algebraMap k K).injective
  have hpoly := X_pow_sub_C_eq_prod hζK hell
    (show x ^ ell = x ^ ell from rfl)
  apply_fun Polynomial.eval 1 at hpoly
  calc
    (∏ j : Fin ell, (1 - algebraMap k K (ζ ^ (j : ℕ)) * x)) =
        ∏ j ∈ Finset.range ell,
          (1 - algebraMap k K (ζ ^ j) * x) :=
      Fin.prod_univ_eq_prod_range
        (fun j ↦ 1 - algebraMap k K (ζ ^ j) * x) ell
    _ =
        ∏ j ∈ Finset.range ell,
          (1 - (algebraMap k K ζ) ^ j * x) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [map_pow]
    _ = 1 - x ^ ell := by
      simpa only [eval_sub, eval_pow, eval_X, one_pow, eval_C, eval_prod,
        eval_mul, mul_one] using hpoly.symm

private theorem hdRootProductWeight_minpoly_power {ell : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ ell) (hell : 0 < ell)
    (α : FiniteMulChar k) (x : K) :
    hdRootProductWeight (ell := ell) ζ α
        ⟨minpoly k x, minpoly.monic (Algebra.IsIntegral.isIntegral x)⟩ ^
          hdEmbeddingMultiplicity (k := k) x =
      α (Algebra.norm k (1 - x ^ ell)) := by
  change (α (∏ j : Fin ell,
      (minpoly k x).reverse.eval (ζ ^ (j : ℕ)))) ^
        hdEmbeddingMultiplicity (k := k) x =
      α (Algebra.norm k (1 - x ^ ell))
  rw [← map_pow]
  congr 1
  rw [← Finset.prod_pow]
  simp_rw [reverse_minpoly_eval_pow_eq_norm (k := k)]
  rw [← map_prod]
  rw [prod_one_sub_primitive_powers_extension (k := k) hζ hell]

noncomputable local instance hdConjugacyClassFintype :
    Fintype (ConjRootClass k K) := by
  classical
  exact Fintype.ofSurjective (ConjRootClass.mk k) fun c ↦ by
    induction c with
    | h x => exact ⟨x, rfl⟩

noncomputable local instance hdConjugacyClassCarrierFintype
    (c : ConjRootClass k K) : Fintype c.carrier := by
  classical
  change Fintype {x : K // ConjRootClass.mk k x = c}
  infer_instance

private noncomputable def hdRootProductConjugacyTerm {ell : ℕ} (ζ : k)
    (α : FiniteMulChar k) (c : ConjRootClass k K) : ℂ :=
  (c.minpoly.natDegree : ℂ) *
    hdRootProductWeight (ell := ell) ζ α
      ⟨c.minpoly, c.monic_minpoly⟩ ^
        (Module.finrank k K / c.minpoly.natDegree)

private lemma hdRootProductConjugacyTerm_eq_sum_carrier
    {ell : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ ell) (hell : 0 < ell)
    (α : FiniteMulChar k) (c : ConjRootClass k K) :
    hdRootProductConjugacyTerm (K := K) (ell := ell) ζ α c =
      ∑ x : c.carrier, α (Algebra.norm k (1 - x.1 ^ ell)) := by
  classical
  let A := hdRootProductWeight (ell := ell) ζ α
    ⟨c.minpoly, c.monic_minpoly⟩ ^
      (Module.finrank k K / c.minpoly.natDegree)
  have hcard : Fintype.card c.carrier = c.minpoly.natDegree :=
    conjugacyClass_carrier_card k K c
  calc
    hdRootProductConjugacyTerm (K := K) (ell := ell) ζ α c =
        c.minpoly.natDegree • A := by
      simp [hdRootProductConjugacyTerm, A, nsmul_eq_mul]
    _ = ∑ _x : c.carrier, A := by simp [hcard]
    _ = ∑ x : c.carrier, α (Algebra.norm k (1 - x.1 ^ ell)) := by
      apply Fintype.sum_congr
      intro x
      have hx : IsIntegral k x.1 := Algebra.IsIntegral.isIntegral x.1
      have hmk : ConjRootClass.mk k x.1 = c :=
        ConjRootClass.mem_carrier.mp x.2
      have hminpoly : minpoly k x.1 = c.minpoly := by
        simpa using congrArg ConjRootClass.minpoly hmk
      have hexp :
          Module.finrank k K / c.minpoly.natDegree =
            hdEmbeddingMultiplicity (k := k) x.1 := by
        rw [← hminpoly, ← IntermediateField.adjoin.finrank hx,
          ← Module.finrank_mul_finrank k
            (↥(IntermediateField.adjoin k ({x.1} : Set K))) K,
          Nat.mul_div_right _ Module.finrank_pos]
        rfl
      simpa [A, hminpoly, hexp] using
        hdRootProductWeight_minpoly_power (K := K) hζ hell α x.1

private theorem hdRootProductWeight_closedPointPowerSum
    {ell : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ ell) (hell : 0 < ell)
    (α : FiniteMulChar k) :
    MonicWeight.closedPointPowerSum
        (hdRootProductWeight (ell := ell) ζ α) (Module.finrank k K) =
      ∑ x : K, α (Algebra.norm k (1 - x ^ ell)) := by
  classical
  let w := hdRootProductWeight (ell := ell) ζ α
  let term : MonicWeight.DivisorPrimeIndex k (Module.finrank k K) → ℂ :=
    fun x ↦ (x.1.1 : ℂ) * MonicWeight.exactPrimeWeight k w x.2 ^
      (Module.finrank k K / x.1.1)
  let lifted : K → ℂ := fun x ↦ α (Algebra.norm k (1 - x ^ ell))
  calc
    MonicWeight.closedPointPowerSum w (Module.finrank k K) =
        ∑ x : MonicWeight.DivisorPrimeIndex k (Module.finrank k K), term x := by
      exact (sum_divisorPrimeIndex_eq_closedPointPowerSum k w
        (Module.finrank k K)).symm
    _ = ∑ c : ConjRootClass k K,
        hdRootProductConjugacyTerm (K := K) (ell := ell) ζ α c := by
      symm
      apply Fintype.sum_equiv (conjugacyClassDivisorPrimeEquiv k K)
      intro c
      rfl
    _ = ∑ c : ConjRootClass k K, ∑ x : c.carrier, lifted x.1 := by
      apply Fintype.sum_congr
      intro c
      exact hdRootProductConjugacyTerm_eq_sum_carrier (K := K) hζ hell α c
    _ = ∑ c : ConjRootClass k K,
        ∑ x : {x : K // ConjRootClass.mk k x = c}, lifted x.1 := by
      apply Fintype.sum_congr
      intro c
      apply Fintype.sum_equiv (conjugacyClassCarrierEquivFiber k K c)
      intro x
      rfl
    _ = ∑ x : K, lifted x :=
      Fintype.sum_fiberwise (ConjRootClass.mk k) lifted

private def elementarySum {T : Type*} [Fintype T]
    (a : T → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ s ∈ (Finset.univ : Finset T).powersetCard n, ∏ t ∈ s, a t

private def finitePowerSum {T : Type*} [Fintype T]
    (a : T → ℂ) (n : ℕ) : ℂ :=
  ∑ t : T, a t ^ n

@[simp] private lemma elementarySum_zero {T : Type*} [Fintype T]
    (a : T → ℂ) : elementarySum a 0 = 1 := by
  simp [elementarySum]

private lemma elementarySum_card {T : Type*} [Fintype T]
    (a : T → ℂ) :
    elementarySum a (Fintype.card T) = ∏ t : T, a t := by
  classical
  rw [elementarySum, ← Finset.card_univ, Finset.powersetCard_self]
  simp

private lemma elementarySum_newton {T : Type*} [Fintype T]
    (a : T → ℂ) (n : ℕ) :
    (n : ℂ) * elementarySum a n = (-1 : ℂ) ^ (n + 1) *
      ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)) with z.1 < n,
        (-1 : ℂ) ^ z.1 * elementarySum a z.1 * finitePowerSum a z.2 := by
  classical
  have h := MvPolynomial.mul_esymm_eq_sum T ℂ n
  have heval := congrArg (MvPolynomial.eval a) h
  simpa [elementarySum, finitePowerSum, MvPolynomial.esymm,
    MvPolynomial.psum] using heval

private lemma sum_antidiagonal_succ_filter_fst
    (f : ℕ × ℕ → ℂ) (n : ℕ) :
    (∑ z ∈ (Finset.HasAntidiagonal.antidiagonal (n + 1) : Finset (ℕ × ℕ)) with
        z.1 < n + 1, f z) =
      ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
        f (z.1, z.2 + 1) := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [lt_self_iff_false, ↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro z hz
  have hzsum : z.1 + z.2 = n :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hz
  rw [if_pos (by omega)]

private lemma elementarySum_signed_recurrence {T : Type*} [Fintype T]
    (a : T → ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * elementarySum a (n + 1) =
      ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
        elementarySum a z.1 *
          ((-1 : ℂ) ^ z.2 * finitePowerSum a (z.2 + 1)) := by
  classical
  rw [elementarySum_newton]
  rw [sum_antidiagonal_succ_filter_fst]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hzsum : z.1 + z.2 = n :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hz
  have hexp : n + 2 + z.1 = 2 * (z.1 + 1) + z.2 := by omega
  calc
    (-1 : ℂ) ^ (n + 1 + 1) *
        ((-1 : ℂ) ^ z.1 * elementarySum a z.1 * finitePowerSum a (z.2 + 1)) =
      ((-1 : ℂ) ^ (n + 2) * (-1 : ℂ) ^ z.1) *
        (elementarySum a z.1 * finitePowerSum a (z.2 + 1)) := by ring
    _ = ((-1 : ℂ) ^ z.2) *
        (elementarySum a z.1 * finitePowerSum a (z.2 + 1)) := by
      rw [← pow_add, hexp, pow_add, pow_mul]
      norm_num
    _ = elementarySum a z.1 *
        ((-1 : ℂ) ^ z.2 * finitePowerSum a (z.2 + 1)) := by ring

private lemma derivative_recurrence (A B : ℕ → ℂ)
    (hderiv :
      PowerSeries.derivative ℂ (PowerSeries.mk A) =
        PowerSeries.mk A * PowerSeries.mk (fun n ↦ B (n + 1)))
    (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * A (n + 1) =
      ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
        A z.1 * B (z.2 + 1) := by
  have h := congrArg (PowerSeries.coeff n) hderiv
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul] at h
  simpa only [PowerSeries.coeff_mk, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_comm] using h

private theorem coefficients_eq_elementarySum_of_signed_powerSums
    {T : Type*} [Fintype T] (A B : ℕ → ℂ) (a : T → ℂ)
    (hA0 : A 0 = 1)
    (hderiv :
      PowerSeries.derivative ℂ (PowerSeries.mk A) =
        PowerSeries.mk A * PowerSeries.mk (fun n ↦ B (n + 1)))
    (hB : ∀ r, 0 < r →
      B r = (-1 : ℂ) ^ (r - 1) * finitePowerSum a r) :
    ∀ n, A n = elementarySum a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using hA0
      | succ m =>
          have hA := derivative_recurrence A B hderiv m
          have hE := elementarySum_signed_recurrence a m
          have hrhs :
              (∑ z ∈ (Finset.HasAntidiagonal.antidiagonal m : Finset (ℕ × ℕ)),
                  A z.1 * B (z.2 + 1)) =
                ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal m : Finset (ℕ × ℕ)),
                  elementarySum a z.1 *
                    ((-1 : ℂ) ^ z.2 * finitePowerSum a (z.2 + 1)) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hzsum : z.1 + z.2 = m :=
              Finset.HasAntidiagonal.mem_antidiagonal.mp hz
            rw [ih z.1 (by omega), hB (z.2 + 1) (by omega)]
            simp
          have hmul :
              (((m + 1 : ℕ) : ℂ) * A (m + 1)) =
                ((m + 1 : ℕ) : ℂ) * elementarySum a (m + 1) := by
            rw [hA, hrhs, ← hE]
          have hcast : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero m
          exact (mul_right_injective₀ hcast) hmul

private theorem degreeSum_card_eq_prod_of_closedPointPowerSums
    {T : Type*} [Fintype T] (w : MonicWeight k ℂ) (a : T → ℂ)
    (hB : ∀ r, 0 < r →
      MonicWeight.closedPointPowerSum w r =
        (-1 : ℂ) ^ (r - 1) * ∑ t : T, a t ^ r) :
    MonicWeight.degreeSum w (Fintype.card T) = ∏ t : T, a t := by
  let A : ℕ → ℂ := MonicWeight.degreeSum w
  let B : ℕ → ℂ := MonicWeight.closedPointPowerSum w
  have hall : ∀ n, A n = elementarySum a n :=
    coefficients_eq_elementarySum_of_signed_powerSums A B a
      (MonicWeight.degreeSum_zero w)
      (by simpa [A, B, MonicWeight.series, MonicWeight.closedPointSeries] using
        MonicWeight.closedPointSeries_derivative k w)
      (by
        intro r hr
        simpa [B, finitePowerSum] using hB r hr)
  rw [← elementarySum_card a]
  exact hall (Fintype.card T)

private lemma sum_primitive_powers {n r : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (hr0 : r ≠ 0) (hrn : r < n) :
    ∑ j : Fin n, (ζ ^ r) ^ (j : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hne : ζ ^ r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hr0 hrn
  have hpow : (ζ ^ r) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hmul := mul_geom_sum (ζ ^ r) n
  rw [hpow, sub_self] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

private lemma sum_eval_primitive_powers {n : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (P : k[X]) (hdeg : P.natDegree < n) :
    ∑ j : Fin n, P.eval (ζ ^ (j : ℕ)) = (n : k) * P.coeff 0 := by
  classical
  simp_rw [P.eval_eq_sum_range]
  rw [sum_comm]
  calc
    ∑ i ∈ range (P.natDegree + 1),
        ∑ j : Fin n, P.coeff i * (ζ ^ (j : ℕ)) ^ i =
        ∑ i ∈ range (P.natDegree + 1),
          P.coeff i * ∑ j : Fin n, (ζ ^ i) ^ (j : ℕ) := by
            apply sum_congr rfl
            intro i hi
            rw [← mul_sum]
            congr 1
            apply Fintype.sum_congr
            intro j
            rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (n : k) * P.coeff 0 := by
      rw [sum_eq_single 0]
      · simp [mul_comm]
      · intro i hi hi0
        have hi_le : i ≤ P.natDegree := Nat.le_of_lt_succ (mem_range.mp hi)
        have hin : i < n := lt_of_le_of_lt hi_le hdeg
        rw [sum_primitive_powers hζ hi0 hin, mul_zero]
      · simp

private def FourierHyperplane (m : ℕ) :=
  {s : Fin (m + 1) → k // ∑ j, s j = ((m + 1 : ℕ) : k)}

private noncomputable def monicFourierMap (m : ℕ) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (m + 1)) :
    MonicPolynomialOfDegree k m → FourierHyperplane (k := k) m := fun Q ↦
  ⟨fun j ↦ Q.1.reverse.eval (ζ ^ (j : ℕ)), by
    have hdeg : Q.1.reverse.natDegree < m + 1 := by
      calc
        Q.1.reverse.natDegree ≤ Q.1.natDegree := Polynomial.reverse_natDegree_le Q.1
        _ = m := Q.2.2
        _ < m + 1 := Nat.lt_succ_self m
    rw [sum_eval_primitive_powers hζ Q.1.reverse hdeg]
    rw [Polynomial.coeff_zero_reverse, Q.2.1.leadingCoeff, mul_one]⟩

private lemma powers_injective {n : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (fun j : Fin n ↦ ζ ^ (j : ℕ)) := by
  intro i j hij
  apply Fin.ext
  exact hζ.pow_inj i.isLt j.isLt hij

private lemma monicFourierMap_injective (m : ℕ) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (m + 1)) :
    Function.Injective (monicFourierMap m ζ hζ) := by
  intro Q R hQR
  apply Subtype.ext
  have heval : ∀ j : Fin (m + 1),
      Q.1.reverse.eval (ζ ^ (j : ℕ)) =
        R.1.reverse.eval (ζ ^ (j : ℕ)) := by
    intro j
    exact congrArg (fun s ↦ s.1 j) hQR
  have hrev : Q.1.reverse = R.1.reverse := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q.1.reverse R.1.reverse
      (f := fun j : Fin (m + 1) ↦ ζ ^ (j : ℕ))
    · exact powers_injective hζ
    · exact heval
    · rw [Fintype.card_fin]
      exact max_lt
        (by calc
          Q.1.reverse.natDegree ≤ Q.1.natDegree := Polynomial.reverse_natDegree_le Q.1
          _ = m := Q.2.2
          _ < m + 1 := Nat.lt_succ_self m)
        (by calc
          R.1.reverse.natDegree ≤ R.1.natDegree := Polynomial.reverse_natDegree_le R.1
          _ = m := R.2.2
          _ < m + 1 := Nat.lt_succ_self m)
  have := congrArg (fun P : k[X] ↦ P.reflect m) hrev
  simpa only [Polynomial.reverse, Q.2.2, R.2.2,
    Polynomial.reflect_reflect] using this

private lemma monicFourierMap_surjective (m : ℕ) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (m + 1))
    (hcast : ((m + 1 : ℕ) : k) ≠ 0) :
    Function.Surjective (monicFourierMap m ζ hζ) := by
  classical
  rintro ⟨s, hsum⟩
  let v : Fin (m + 1) → k := fun j ↦ ζ ^ (j : ℕ)
  have hv : Function.Injective v := powers_injective hζ
  have hv' : Set.InjOn v ↑(univ : Finset (Fin (m + 1))) := by
    intro i hi j hj hij
    exact hv hij
  let P : k[X] := Lagrange.interpolate univ v s
  have hPeval (j : Fin (m + 1)) : P.eval (v j) = s j :=
    Lagrange.eval_interpolate_at_node (s := univ) s hv' (mem_univ j)
  have hPdegree : P.degree < (m + 1 : ℕ) := by
    simpa [P] using Lagrange.degree_interpolate_lt (s := univ) s hv'
  have hsne : ∃ j : Fin (m + 1), s j ≠ 0 := by
    by_contra hs
    push Not at hs
    have hz : ∑ j : Fin (m + 1), s j = 0 := by simp [hs]
    exact hcast (hsum.symm.trans hz)
  have hPne : P ≠ 0 := by
    obtain ⟨j, hj⟩ := hsne
    intro hP
    have he := hPeval j
    rw [hP, eval_zero] at he
    exact hj he.symm
  have hPnat : P.natDegree < m + 1 :=
    (natDegree_lt_iff_degree_lt hPne).mpr hPdegree
  have hPcoeff : P.coeff 0 = 1 := by
    have hfourier := sum_eval_primitive_powers hζ P hPnat
    have hevals : ∑ j : Fin (m + 1), P.eval (ζ ^ (j : ℕ)) =
        ∑ j : Fin (m + 1), s j := by
      apply Fintype.sum_congr
      exact hPeval
    rw [hevals, hsum] at hfourier
    apply mul_left_cancel₀ hcast
    simpa only [mul_one] using hfourier.symm
  let Q : k[X] := P.reflect m
  have hQdeg_le : Q.natDegree ≤ m := by
    apply (natDegree_reflect_le (N := m) (p := P)).trans
    exact max_le le_rfl (Nat.le_of_lt_succ hPnat)
  have hQcoeff : Q.coeff m = 1 := by
    change (P.reflect m).coeff m = 1
    rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, hPcoeff]
  have hQdeg : Q.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hQdeg_le (hQcoeff.trans_ne one_ne_zero)
  have hQmonic : Q.Monic := by
    rw [Monic.def, leadingCoeff, hQdeg, hQcoeff]
  let q : MonicPolynomialOfDegree k m := ⟨Q, hQmonic, hQdeg⟩
  refine ⟨q, Subtype.ext ?_⟩
  funext j
  change Q.reverse.eval (ζ ^ (j : ℕ)) = s j
  have hQr : Q.reverse = P := by
    dsimp [Q]
    rw [Polynomial.reverse, hQdeg, Polynomial.reflect_reflect]
  rw [hQr]
  exact hPeval j

private noncomputable def monicFourierEquiv (m : ℕ) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (m + 1))
    (hcast : ((m + 1 : ℕ) : k) ≠ 0) :
    MonicPolynomialOfDegree k m ≃ FourierHyperplane (k := k) m :=
  Equiv.ofBijective (monicFourierMap m ζ hζ)
    ⟨monicFourierMap_injective m ζ hζ,
      monicFourierMap_surjective m ζ hζ hcast⟩

private noncomputable instance FourierHyperplaneFintype (m : ℕ) :
    Fintype (FourierHyperplane (k := k) m) :=
  Fintype.ofInjective (fun s : FourierHyperplane (k := k) m ↦ s.1)
    Subtype.val_injective

private lemma hdRootProductWeight_degreeSum (m : ℕ) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (m + 1))
    (hcast : ((m + 1 : ℕ) : k) ≠ 0)
    (α : FiniteMulChar k) :
    MonicWeight.degreeSum (hdRootProductWeight (ell := m + 1) ζ α) m =
      ∑ s : FourierHyperplane (k := k) m, α (∏ j, s.1 j) := by
  classical
  rw [MonicWeight.degreeSum]
  exact Fintype.sum_equiv (monicFourierEquiv m ζ hζ hcast)
    (fun Q : MonicPolynomialOfDegree k m ↦
      hdRootProductWeight (ell := m + 1) ζ α
        ⟨Q.1, by change Q.1.Monic; exact Q.2.1⟩)
    (fun s : FourierHyperplane (k := k) m ↦ α (∏ j, s.1 j))
    (fun Q ↦ rfl)

private def AddHyperplane (n : ℕ) (a : k) :=
  {x : Fin n → k // ∑ i, x i = a}

private noncomputable instance AddHyperplaneFintype (n : ℕ) (a : k) :
    Fintype (AddHyperplane (k := k) n a) :=
  Fintype.ofInjective (fun x : AddHyperplane (k := k) n a ↦ x.1)
    Subtype.val_injective

private noncomputable def scaleAddHyperplaneEquiv (m : ℕ)
    (hcast : ((m + 1 : ℕ) : k) ≠ 0) :
    AddHyperplane (k := k) (m + 1) 1 ≃ FourierHyperplane (k := k) m where
  toFun x := ⟨fun i ↦ (m + 1 : k) * x.1 i, by
    rw [← Finset.mul_sum, x.2, mul_one]
    norm_num⟩
  invFun s := ⟨fun i ↦ ((m + 1 : k))⁻¹ * s.1 i, by
    rw [← Finset.mul_sum, s.2]
    norm_num at hcast ⊢
    exact inv_mul_cancel₀ hcast⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    norm_num at hcast ⊢
    field_simp
  right_inv s := by
    apply Subtype.ext
    funext i
    norm_num at hcast ⊢
    field_simp

@[simp] private lemma scaleAddHyperplaneEquiv_apply (m : ℕ)
    (hcast : ((m + 1 : ℕ) : k) ≠ 0)
    (x : AddHyperplane (k := k) (m + 1) 1) (i : Fin (m + 1)) :
    (scaleAddHyperplaneEquiv (k := k) m hcast x).1 i =
      (m + 1 : k) * x.1 i := rfl

private lemma generalizedJacobiSum_const_eq_subtype (n : ℕ)
    (α : FiniteMulChar k) :
    generalizedJacobiSum (fun _ : Fin n ↦ α) =
      ∑ x : AddHyperplane (k := k) n 1, ∏ i, α (x.1 i) := by
  classical
  unfold generalizedJacobiSum generalizedJacobiFiber generalizedJacobiWeight
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro x
  simp

private lemma hdRootProductWeight_degreeSum_eq_constJacobi
    (m : ℕ) (ζ : k)
    (hζ : IsPrimitiveRoot ζ (m + 1))
    (hcast : ((m + 1 : ℕ) : k) ≠ 0)
    (α : FiniteMulChar k) :
    MonicWeight.degreeSum
        (hdRootProductWeight (ell := m + 1) ζ α) m =
      α (m + 1 : k) ^ (m + 1) *
        generalizedJacobiSum (fun _ : Fin (m + 1) ↦ α) := by
  classical
  rw [hdRootProductWeight_degreeSum m ζ hζ hcast,
    generalizedJacobiSum_const_eq_subtype]
  rw [← (scaleAddHyperplaneEquiv (k := k) m hcast).sum_comp]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro x
  simp only [scaleAddHyperplaneEquiv_apply]
  rw [map_prod]
  simp_rw [map_mul]
  rw [Finset.prod_mul_distrib]
  simp

private abbrev HDNonzeroIndex (ell : ℕ) := {j : Fin ell // j.val ≠ 0}

private lemma card_hdNonzeroIndex {ell : ℕ} (hell : 0 < ell) :
    Fintype.card (HDNonzeroIndex ell) = ell - 1 := by
  classical
  letI : NeZero ell := ⟨hell.ne'⟩
  let Z := {j : Fin ell // j.val = 0}
  have hZ : Fintype.card Z = 1 := by
    letI : Unique Z :=
      ⟨⟨0, rfl⟩, fun z ↦ by
        apply Subtype.ext
        apply Fin.ext
        exact z.2⟩
    exact Fintype.card_unique
  calc
    Fintype.card (HDNonzeroIndex ell) =
        Fintype.card (Fin ell) - Fintype.card Z := by
      exact Fintype.card_subtype_compl (fun j : Fin ell ↦ j.val = 0)
    _ = ell - 1 := by rw [Fintype.card_fin, hZ]

private def hdNonzeroIndexEquivIcc {ell : ℕ} (hell : 0 < ell) :
    HDNonzeroIndex ell ≃ {j : ℕ // j ∈ Icc 1 (ell - 1)} where
  toFun j := ⟨j.1.val, by
    rw [mem_Icc]
    constructor
    · omega
    · exact Nat.le_sub_one_of_lt j.1.isLt⟩
  invFun j := ⟨⟨j.1, by
    have hj := (mem_Icc.mp j.2).2
    omega⟩, by
      have hj := (mem_Icc.mp j.2).1
      exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hj)⟩
  left_inv j := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Subtype.ext; rfl

private lemma prod_hdNonzeroIndex_eq_prod_Icc
    {M : Type*} [CommMonoid M] {ell : ℕ} (hell : 0 < ell)
    (f : ℕ → M) :
    (∏ j : HDNonzeroIndex ell, f j.1.val) =
      ∏ j ∈ Icc 1 (ell - 1), f j := by
  classical
  calc
    (∏ j : HDNonzeroIndex ell, f j.1.val) =
        ∏ j : {j : ℕ // j ∈ Icc 1 (ell - 1)}, f j.1 := by
      exact Fintype.prod_equiv (hdNonzeroIndexEquivIcc hell)
        (fun j : HDNonzeroIndex ell ↦ f j.1.val)
        (fun j : {j : ℕ // j ∈ Icc 1 (ell - 1)} ↦ f j.1)
        (fun _ ↦ rfl)
    _ = ∏ j ∈ Icc 1 (ell - 1), f j := by
      simpa using (Finset.prod_attach (Icc 1 (ell - 1)) f)

private lemma hdRootProductWeight_closedPointPowerSums
    {ell : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ ell)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (hα : α ^ ell ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    ∀ r, 0 < r →
      MonicWeight.closedPointPowerSum
          (hdRootProductWeight (ell := ell) ζ α) r =
        (-1 : ℂ) ^ (r - 1) *
          ∑ j : HDNonzeroIndex ell,
            jacobiSum α (η ^ (j.1 : ℕ)) ^ r := by
  intro r hr
  letI : Fact (Nat.Prime (ringChar k)) := ⟨CharP.prime_ringChar k⟩
  letI : NeZero r := ⟨hr.ne'⟩
  let K := FiniteField.Extension k (ringChar k) r
  letI : Fintype K := Fintype.ofFinite K
  have hell : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  have hα1 : α ≠ 1 := by
    intro h
    apply hα
    rw [h, one_pow]
  have hclosed :=
    hdRootProductWeight_closedPointPowerSum (K := K) hζ hell α
  have hcurve :=
    power_curve_norm_sum_eq_signed_jacobi_powers
      (K := K) ell η α hη hα1 ψ hψ
  rw [FiniteField.finrank_extension] at hclosed hcurve
  calc
    MonicWeight.closedPointPowerSum
        (hdRootProductWeight (ell := ell) ζ α) r =
        ∑ x : K, α (Algebra.norm k (1 - x ^ ell)) := hclosed
    _ = ∑ x : K, normMulChar k K α (1 - x ^ ell) := by
      apply Fintype.sum_congr
      intro x
      rfl
    _ = (-1 : ℂ) ^ (r - 1) *
        ∑ j : HDNonzeroIndex ell,
          jacobiSum α (η ^ (j.1 : ℕ)) ^ r := hcurve

private lemma hdRootProductWeight_degreeSum_eq_jacobi_product
    {ell : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ ell)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (hα : α ^ ell ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    MonicWeight.degreeSum
        (hdRootProductWeight (ell := ell) ζ α) (ell - 1) =
      ∏ j : HDNonzeroIndex ell,
        jacobiSum α (η ^ (j.1 : ℕ)) := by
  classical
  let a : HDNonzeroIndex ell → ℂ := fun j ↦
    jacobiSum α (η ^ (j.1 : ℕ))
  have hell : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  have hNewton :=
    degreeSum_card_eq_prod_of_closedPointPowerSums
      (hdRootProductWeight (ell := ell) ζ α) a
      (hdRootProductWeight_closedPointPowerSums
        hζ η α hη hα ψ hψ)
  rw [card_hdNonzeroIndex hell] at hNewton
  exact hNewton

private lemma hard_jacobi_identity_subtype
    {ell : ℕ} (hdiv : ell ∣ Fintype.card k - 1)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (hα : α ^ ell ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    α (ell : k) ^ ell * generalizedJacobiSum (fun _ : Fin ell ↦ α) =
      ∏ j : HDNonzeroIndex ell,
        jacobiSum α (η ^ (j.1 : ℕ)) := by
  classical
  have hell : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_field ell hdiv
  have hcast : (ell : k) ≠ 0 := ell_ne_zero_in_field ell hdiv
  have hdegree :=
    hdRootProductWeight_degreeSum_eq_jacobi_product
      hζ η α hη hα ψ hψ
  have hFourier :=
    hdRootProductWeight_degreeSum_eq_constJacobi
      (k := k) (ell - 1) ζ
      (by simpa [Nat.sub_add_cancel hell] using hζ)
      (by simpa [Nat.sub_add_cancel hell] using hcast) α
  rw [Nat.sub_add_cancel hell] at hFourier
  have hcastAdd : ((ell - 1 : ℕ) : k) + 1 = (ell : k) := by
    simpa using congrArg (fun n : ℕ ↦ (n : k)) (Nat.sub_add_cancel hell)
  rw [hcastAdd] at hFourier
  exact hFourier.symm.trans hdegree

private theorem hard_jacobi_identity_Icc
    {ell : ℕ} (hdiv : ell ∣ Fintype.card k - 1)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (hα : α ^ ell ≠ 1)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    α (ell : k) ^ ell * generalizedJacobiSum (fun _ : Fin ell ↦ α) =
      ∏ j ∈ Icc 1 (ell - 1), jacobiSum α (η ^ j) := by
  have hell : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  rw [← prod_hdNonzeroIndex_eq_prod_Icc hell
    (fun j ↦ jacobiSum α (η ^ j))]
  exact hard_jacobi_identity_subtype hdiv η α hη hα ψ hψ

private lemma order_pow_eq_one {ell : ℕ} (η : FiniteMulChar k)
    (hη : orderOf η = ell) : η ^ ell = 1 := by
  rw [← hη]
  exact pow_orderOf_eq_one η

private lemma alpha_mul_eta_pow_ne_one_of_alpha_pow_ne_one
    {ell : ℕ} (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (hα : α ^ ell ≠ 1) (j : ℕ) :
    α * η ^ j ≠ 1 := by
  intro h
  apply hα
  have haeq : α = (η ^ j)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa [mul_comm] using h)
  rw [haeq, inv_pow]
  have hηell : η ^ ell = 1 := order_pow_eq_one η hη
  have hpow : (η ^ j) ^ ell = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hηell, one_pow]
  rw [hpow, inv_one]

private lemma prod_binary_gauss_jacobi
    {ell : ℕ} (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (hα : α ^ ell ≠ 1) (ψ : FiniteAddChar k) :
    (∏ j ∈ Icc 1 (ell - 1), gaussSum (α * η ^ j) ψ) *
        (∏ j ∈ Icc 1 (ell - 1), jacobiSum α (η ^ j)) =
      gaussSum α ψ ^ (ell - 1) *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
  classical
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ j ∈ Icc 1 (ell - 1),
        gaussSum (α * η ^ j) ψ * jacobiSum α (η ^ j)) =
        ∏ j ∈ Icc 1 (ell - 1),
          gaussSum α ψ * gaussSum (η ^ j) ψ := by
      apply Finset.prod_congr rfl
      intro j hj
      exact jacobiSum_mul_nontrivial
        (alpha_mul_eta_pow_ne_one_of_alpha_pow_ne_one η α hη hα j) ψ
    _ = (∏ j ∈ Icc 1 (ell - 1), gaussSum α ψ) *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
      rw [Finset.prod_mul_distrib]
    _ = gaussSum α ψ ^ (ell - 1) *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
      congr 1
      simp

private lemma generalizedGaussJacobi_const
    {ell : ℕ} (α : FiniteMulChar k) (ψ : FiniteAddChar k)
    (hα : α ^ ell ≠ 1) :
    gaussSum α ψ ^ ell =
      generalizedJacobiSum (fun _ : Fin ell ↦ α) *
        gaussSum (α ^ ell) ψ := by
  simpa [generalizedJacobiProduct] using
    generalizedGaussJacobi_of_product_ne_one (fun _ : Fin ell ↦ α) ψ (by
      simpa [generalizedJacobiProduct] using hα)

private lemma prod_gauss_pow_cyclic_shift
    {ell : ℕ} (η : FiniteMulChar k) (hη : orderOf η = ell)
    (ψ : FiniteAddChar k) (i : ℕ) :
    (∏ j ∈ range ell, gaussSum (η ^ (i + j)) ψ) =
      ∏ j ∈ range ell, gaussSum (η ^ j) ψ := by
  classical
  have hellpos : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  letI : NeZero ell := ⟨hellpos.ne'⟩
  let a : Fin ell := ⟨i % ell, Nat.mod_lt i hellpos⟩
  calc
    (∏ j ∈ range ell, gaussSum (η ^ (i + j)) ψ) =
        ∏ j : Fin ell, gaussSum (η ^ (i + (j : ℕ))) ψ :=
      (Fin.prod_univ_eq_prod_range
        (fun j ↦ gaussSum (η ^ (i + j)) ψ) ell).symm
    _ = ∏ j : Fin ell, gaussSum (η ^ ((a + j : Fin ell) : ℕ)) ψ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hpow : η ^ (i + (j : ℕ)) = η ^ ((a + j : Fin ell) : ℕ) := by
        rw [← pow_mod_orderOf η (i + (j : ℕ)), hη]
        congr 1
        change (i + (j : ℕ)) % ell = (i % ell + (j : ℕ)) % ell
        rw [Nat.add_mod]
        simp [Nat.mod_eq_of_lt j.isLt]
      rw [hpow]
    _ = ∏ j : Fin ell, gaussSum (η ^ (j : ℕ)) ψ := by
      refine Fintype.prod_equiv (Equiv.addRight a)
        (fun j : Fin ell ↦ gaussSum (η ^ ((a + j : Fin ell) : ℕ)) ψ)
        (fun j : Fin ell ↦ gaussSum (η ^ (j : ℕ)) ψ) ?_
      intro j
      simp [add_comm]
    _ = ∏ j ∈ range ell, gaussSum (η ^ j) ψ :=
      Fin.prod_univ_eq_prod_range (fun j ↦ gaussSum (η ^ j) ψ) ell

private lemma coefficient_eq_one_of_mulChar_pow_eq_one
    {ell : ℕ} (hdiv : ell ∣ Fintype.card k - 1)
    (α : FiniteMulChar k) (hα : α ^ ell = 1) :
    α (((ell : k)⁻¹) ^ ell) = 1 := by
  have hellpos : 0 < ell := by
    by_contra hell
    have hell0 : ell = 0 := Nat.eq_zero_of_not_pos hell
    subst ell
    have hcard : Fintype.card k - 1 = 0 := Nat.zero_dvd.mp hdiv
    exact (by have := Fintype.one_lt_card (α := k); omega)
  have hell : ell ≠ 0 := hellpos.ne'
  have hellk : (ell : k) ≠ 0 := ell_ne_zero_in_field ell hdiv
  rw [map_pow, ← MulChar.pow_apply' α hell, hα]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (inv_ne_zero hellk))

private theorem hasseDavenportOrdinary_easy
    {ell : ℕ} (hdiv : ell ∣ Fintype.card k - 1)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1)
    (hα : α ^ ell = 1) :
    (∏ j ∈ range ell, gaussSum (α * η ^ j) ψ) =
      α (((ell : k)⁻¹) ^ ell) * gaussSum (α ^ ell) ψ *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
  classical
  have hellpos : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  obtain ⟨i, hi, hialpha⟩ := mulChar_root_param ell η α hη hα
  have hcoeff : α (((ell : k)⁻¹) ^ ell) = 1 :=
    coefficient_eq_one_of_mulChar_pow_eq_one hdiv α hα
  rw [hcoeff, hα, gaussSum_one_left hψ, one_mul]
  calc
    (∏ j ∈ range ell, gaussSum (α * η ^ j) ψ) =
        ∏ j ∈ range ell, gaussSum (η ^ (i + j)) ψ := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [← hialpha, pow_add]
    _ = ∏ j ∈ range ell, gaussSum (η ^ j) ψ :=
      prod_gauss_pow_cyclic_shift η hη ψ i
    _ = gaussSum (η ^ 0) ψ *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ :=
      prod_range_eq_head_mul_Icc (fun j ↦ gaussSum (η ^ j) ψ) hellpos
    _ = -1 * ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
      rw [pow_zero, gaussSum_one_left hψ]

private theorem hasseDavenportOrdinary_hard
    {ell : ℕ} (hdiv : ell ∣ Fintype.card k - 1)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1)
    (hα : α ^ ell ≠ 1) :
    (∏ j ∈ range ell, gaussSum (α * η ^ j) ψ) =
      α (((ell : k)⁻¹) ^ ell) * gaussSum (α ^ ell) ψ *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
  classical
  have hellpos : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  have hell0 : (ell : k) ≠ 0 := ell_ne_zero_in_field ell hdiv
  let A : ℂ := gaussSum α ψ
  let P : ℂ := ∏ j ∈ Icc 1 (ell - 1), gaussSum (α * η ^ j) ψ
  let B : ℂ := ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ
  let J : ℂ := generalizedJacobiSum (fun _ : Fin ell ↦ α)
  let H : ℂ := gaussSum (α ^ ell) ψ
  let C : ℂ := α (ell : k) ^ ell
  let D : ℂ := α (((ell : k)⁻¹) ^ ell)
  have hcount := hard_jacobi_identity_Icc hdiv η α hη hα ψ hψ
  have hbinary : P * (C * J) = A ^ (ell - 1) * B := by
    rw [hcount]
    exact prod_binary_gauss_jacobi η α hη hα ψ
  have hgeneral : A ^ ell = J * H :=
    generalizedGaussJacobi_const α ψ hα
  have hJ : J ≠ 0 := by
    intro hJ
    have hA : A ≠ 0 := gaussSum_ne_zero hψ
    have hApow : A ^ ell ≠ 0 := pow_ne_zero ell hA
    apply hApow
    rw [hgeneral, hJ, zero_mul]
  have hpowA : A * A ^ (ell - 1) = A ^ ell := by
    rw [← pow_succ']
    congr 1
    omega
  have hcancelJ : A * P * C = H * B := by
    apply mul_right_cancel₀ hJ
    calc
      (A * P * C) * J = A * (P * (C * J)) := by ring
      _ = A * (A ^ (ell - 1) * B) := by rw [hbinary]
      _ = A ^ ell * B := by rw [← hpowA]; ring
      _ = (J * H) * B := by rw [hgeneral]
      _ = (H * B) * J := by ring
  have hDC : D * C = 1 := by
    dsimp [D, C]
    have hinv : α ((ell : k)⁻¹) = (α (ell : k))⁻¹ := by
      let u : kˣ := Units.mk0 (ell : k) hell0
      change ↑(α.toUnitHom u⁻¹) = (↑(α.toUnitHom u) : ℂ)⁻¹
      rw [map_inv]
      exact Units.val_inv_eq_inv_val _
    rw [map_pow, hinv, inv_pow]
    have hval : α (ell : k) ≠ 0 := by
      exact ((isUnit_iff_ne_zero.mpr hell0).map α).ne_zero
    exact inv_mul_cancel₀ (pow_ne_zero ell hval)
  rw [prod_range_eq_head_mul_Icc
    (fun j ↦ gaussSum (α * η ^ j) ψ) hellpos]
  simp only [pow_zero, mul_one]
  change A * P = D * H * B
  calc
    A * P = (D * C) * (A * P) := by rw [hDC, one_mul]
    _ = D * (A * P * C) := by ring
    _ = D * (H * B) := by rw [hcancelJ]
    _ = D * H * B := by ring

private theorem hasseDavenportOrdinary
    {ell : ℕ} (hdiv : ell ∣ Fintype.card k - 1)
    (η α : FiniteMulChar k) (hη : orderOf η = ell)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    (∏ j ∈ range ell, gaussSum (α * η ^ j) ψ) =
      α (((ell : k)⁻¹) ^ ell) * gaussSum (α ^ ell) ψ *
        ∏ j ∈ Icc 1 (ell - 1), gaussSum (η ^ j) ψ := by
  by_cases hα : α ^ ell = 1
  · exact hasseDavenportOrdinary_easy hdiv η α hη ψ hψ hα
  · exact hasseDavenportOrdinary_hard hdiv η α hη ψ hψ hα

private lemma inv_inv_mul_inv_pow (χ η : FiniteMulChar k) (j : ℕ) :
    (χ⁻¹ * (η⁻¹) ^ j)⁻¹ = χ * η ^ j := by
  simp [mul_comm]

private lemma inv_inv_pow (χ : FiniteMulChar k) (ell : ℕ) :
    ((χ⁻¹) ^ ell)⁻¹ = χ ^ ell := by
  simp

/-- Hasse--Davenport multiplication in the project's Langlands normalization. -/
theorem hasseDavenportProduct
    (ell : ℕ) (hdiv : ell ∣ Fintype.card k - 1)
    (η χ : FiniteMulChar k) (hη : orderOf η = ell)
    (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    χ ((ell : k) ^ ell) * langlandsGaussSum (χ ^ ell) ψ *
        (∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (η ^ j) ψ) =
      langlandsGaussSum χ ψ *
        ∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (χ * η ^ j) ψ := by
  classical
  have hηInv : orderOf η⁻¹ = ell := by
    rw [orderOf_inv, hη]
  have hellpos : 0 < ell := by
    simpa [← hη] using orderOf_pos η
  have hord := hasseDavenportOrdinary hdiv η⁻¹ χ⁻¹ hηInv ψ hψ
  rw [prod_range_eq_head_mul_Icc
    (fun j ↦ gaussSum (χ⁻¹ * (η⁻¹) ^ j) ψ) hellpos] at hord
  simp only [pow_zero, mul_one] at hord
  rw [inv_mulChar_inv_cast_pow χ ell] at hord
  simp_rw [gaussSum_eq_neg_langlandsGaussSum_inv] at hord
  simp only [inv_inv, inv_inv_mul_inv_pow, inv_inv_pow] at hord
  rw [Finset.prod_neg, Finset.prod_neg] at hord
  let S : ℂ := (-1 : ℂ) ^ (Icc 1 (ell - 1)).card
  let Tχ : ℂ := langlandsGaussSum χ ψ
  let Tχell : ℂ := langlandsGaussSum (χ ^ ell) ψ
  let Pχ : ℂ :=
    ∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (χ * η ^ j) ψ
  let Pη : ℂ :=
    ∏ j ∈ Icc 1 (ell - 1), langlandsGaussSum (η ^ j) ψ
  let Cχ : ℂ := χ ((ell : k) ^ ell)
  have hord' : (-Tχ) * (S * Pχ) = Cχ * (-Tχell) * (S * Pη) := by
    simpa [S, Tχ, Tχell, Pχ, Pη, Cχ] using hord
  have hS : S ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hcancel : Tχ * Pχ = Cχ * Tχell * Pη := by
    apply mul_left_cancel₀ hS
    calc
      S * (Tχ * Pχ) = -((-Tχ) * (S * Pχ)) := by ring
      _ = -(Cχ * (-Tχell) * (S * Pη)) := by rw [hord']
      _ = S * (Cχ * Tχell * Pη) := by ring
  exact hcancel.symm

end

end LanglandsFirstMainLemma
