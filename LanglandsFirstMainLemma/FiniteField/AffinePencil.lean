import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Basic.FiniteProducts

open scoped BigOperators
open Polynomial

namespace LanglandsFirstMainLemma

section

variable {p : ℕ} [Fact p.Prime]

lemma zmod_factorization :
    (∏ j : ZMod p, (X - C j : (ZMod p)[X])) = X ^ p - X := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hp
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa only [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hcard : (X ^ p - X : (ZMod p)[X]).roots.card =
      (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp]
    exact ZMod.card p
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots] at h
  exact h

end

section

variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [CharP k p]

lemma primeField_factorization :
    (∏ j : ZMod p,
      (X - C ((ZMod.castHom (dvd_refl p) k) j) : k[X])) = X ^ p - X := by
  let iota := ZMod.castHom (dvd_refl p) k
  calc
    (∏ j : ZMod p, (X - C (iota j) : k[X])) =
        Polynomial.map iota (∏ j : ZMod p, (X - C j : (ZMod p)[X])) := by
          change (∏ j : ZMod p, (X - C (iota j) : k[X])) =
            (Polynomial.mapRingHom iota) (∏ j : ZMod p, (X - C j : (ZMod p)[X]))
          rw [map_prod]
          simp
    _ = Polynomial.map iota (X ^ p - X : (ZMod p)[X]) := by
      rw [zmod_factorization]
    _ = X ^ p - X := by simp

end


section


variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [CharP k p]

lemma primeField_sum_inv_sub (x : k)
    (hx : ∀ j : ZMod p, x - (ZMod.castHom (dvd_refl p) k) j ≠ 0) :
    ∑ j : ZMod p, (x - (ZMod.castHom (dvd_refl p) k) j)⁻¹ =
      -1 / (x ^ p - x) := by
  classical
  let iota := ZMod.castHom (dvd_refl p) k
  let a : ZMod p → k := fun j => x - iota j
  have hprod : (∏ j : ZMod p, a j) = x ^ p - x := by
    have h := congrArg (Polynomial.eval x) (primeField_factorization (p := p) (k := k))
    simp only [eval_sub, eval_pow, eval_X] at h
    change Polynomial.eval x
      (∏ j : ZMod p, (X - C (iota j) : k[X])) = x ^ p - x at h
    change (Polynomial.evalRingHom x)
      (∏ j : ZMod p, (X - C (iota j) : k[X])) = x ^ p - x at h
    rw [map_prod] at h
    simpa [a, iota] using h
  have hprod0 : x ^ p - x ≠ 0 := by
    rw [← hprod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)
  have hderiv :
      (∑ j : ZMod p, ∏ l ∈ (Finset.univ : Finset (ZMod p)).erase j, a l) = -1 := by
    have h := congrArg (Polynomial.eval x)
      (congrArg Polynomial.derivative (primeField_factorization (p := p) (k := k)))
    rw [show (∏ j : ZMod p, (X - C (iota j) : k[X])) =
        ∏ j ∈ (Finset.univ : Finset (ZMod p)), (X - C (iota j) : k[X]) by simp,
      derivative_prod_finset] at h
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero,
      derivative_X_pow, mul_one] at h
    rw [CharP.cast_eq_zero k p] at h
    simp only [C_0, zero_mul, zero_sub, eval_neg, eval_one] at h
    change Polynomial.eval x
      (∑ j : ZMod p,
        ∏ l ∈ (Finset.univ : Finset (ZMod p)).erase j,
          (X - C (iota l) : k[X])) = -1 at h
    change (Polynomial.evalRingHom x)
      (∑ j : ZMod p,
        ∏ l ∈ (Finset.univ : Finset (ZMod p)).erase j,
          (X - C (iota l) : k[X])) = -1 at h
    rw [map_sum] at h
    simp_rw [map_prod] at h
    simpa [a, iota] using h
  have hlog :
      (x ^ p - x) * (∑ j : ZMod p, (a j)⁻¹) = -1 := by
    rw [← hprod, Finset.mul_sum]
    calc
      (∑ j : ZMod p, (∏ l : ZMod p, a l) * (a j)⁻¹) =
          ∑ j : ZMod p, ∏ l ∈ (Finset.univ : Finset (ZMod p)).erase j, a l := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.prod_erase_mul (Finset.univ : Finset (ZMod p)) a
              (Finset.mem_univ j)]
            have haj : a j ≠ 0 := by simpa [a, iota] using hx j
            rw [mul_assoc, mul_inv_cancel₀ haj, mul_one]
      _ = -1 := hderiv
  apply (eq_div_iff hprod0).2
  simpa [a, iota, mul_comm] using hlog

private def negEquiv (R : Type*) [AddGroup R] : R ≃ R where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x

lemma affineCoefficientProduct {rho : k} (hrho : rho ≠ 0) :
    (∏ j : ZMod p, (1 + (ZMod.castHom (dvd_refl p) k) j * rho)) =
      1 - rho ^ (p - 1) := by
  let iota := ZMod.castHom (dvd_refl p) k
  have hminus : (∏ j : ZMod p, (1 - iota j * rho)) = 1 - rho ^ (p - 1) := by
    have h := congrArg (Polynomial.eval rho⁻¹)
      (primeField_factorization (p := p) (k := k))
    simp only [eval_sub, eval_pow, eval_X] at h
    change Polynomial.eval rho⁻¹
      (∏ j : ZMod p, (X - C (iota j) : k[X])) = rho⁻¹ ^ p - rho⁻¹ at h
    change (Polynomial.evalRingHom rho⁻¹)
      (∏ j : ZMod p, (X - C (iota j) : k[X])) = rho⁻¹ ^ p - rho⁻¹ at h
    rw [map_prod] at h
    have heval : (∏ j : ZMod p, (rho⁻¹ - iota j)) = rho⁻¹ ^ p - rho⁻¹ := by
      change (∏ j : ZMod p, Polynomial.eval rho⁻¹
        (X - C (iota j) : k[X])) = rho⁻¹ ^ p - rho⁻¹ at h
      simpa only [eval_sub, eval_X, eval_C] using h
    calc
      (∏ j : ZMod p, (1 - iota j * rho)) =
          rho ^ p * ∏ j : ZMod p, (rho⁻¹ - iota j) := by
            rw [← show (∏ _j : ZMod p, rho) = rho ^ p by
              simp only [Finset.prod_const, Finset.card_univ, ZMod.card],
              ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro j _
            field_simp
      _ = rho ^ p * (rho⁻¹ ^ p - rho⁻¹) := by rw [heval]
      _ = 1 - rho ^ (p - 1) := by
        have hp0 : 0 < p := (Fact.out : p.Prime).pos
        have hpEq : (p - 1) + 1 = p := Nat.sub_add_cancel (by omega)
        have hrpow : rho ^ p * rho⁻¹ = rho ^ (p - 1) := by
          calc
            rho ^ p * rho⁻¹ = (rho ^ (p - 1) * rho) * rho⁻¹ := by
              rw [← pow_succ, hpEq]
            _ = rho ^ (p - 1) := by field_simp
        rw [mul_sub, ← mul_pow, mul_inv_cancel₀ hrho, one_pow, hrpow]
  calc
    (∏ j : ZMod p, (1 + iota j * rho)) =
        ∏ j : ZMod p, (1 - iota j * rho) := by
          apply Fintype.prod_equiv (negEquiv (ZMod p))
          intro j
          change 1 + iota j * rho = 1 - iota (-j) * rho
          rw [map_neg]
          ring
    _ = 1 - rho ^ (p - 1) := hminus

lemma affineReciprocalSum {rho : k} (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p, 1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0) :
    (∑ j : ZMod p, (1 + (ZMod.castHom (dvd_refl p) k) j * rho)⁻¹) =
      rho ^ (p - 1) / (rho ^ (p - 1) - 1) := by
  let iota := ZMod.castHom (dvd_refl p) k
  have hminus : ∀ j : ZMod p, 1 - iota j * rho ≠ 0 := by
    intro j
    have h := hnonzero (-j)
    change 1 + iota (-j) * rho ≠ 0 at h
    rw [map_neg] at h
    simpa [sub_eq_add_neg] using h
  have hx : ∀ j : ZMod p, rho⁻¹ - iota j ≠ 0 := by
    intro j
    rw [show rho⁻¹ - iota j = rho⁻¹ * (1 - iota j * rho) by field_simp]
    exact mul_ne_zero (inv_ne_zero hrho) (hminus j)
  have hinv := primeField_sum_inv_sub (p := p) (k := k) rho⁻¹ hx
  have hreindex :
      (∑ j : ZMod p, (1 + iota j * rho)⁻¹) =
        ∑ j : ZMod p, (1 - iota j * rho)⁻¹ := by
    apply Fintype.sum_equiv (negEquiv (ZMod p))
    intro j
    change (1 + iota j * rho)⁻¹ = (1 - iota (-j) * rho)⁻¹
    rw [map_neg]
    ring
  rw [hreindex]
  have hscale :
      (∑ j : ZMod p, (rho⁻¹ - iota j)⁻¹) =
        rho * ∑ j : ZMod p, (1 - iota j * rho)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show rho⁻¹ - iota j = rho⁻¹ * (1 - iota j * rho) by field_simp]
    rw [mul_inv_rev, inv_inv]
    ring
  rw [hscale] at hinv
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpEq : (p - 1) + 1 = p := Nat.sub_add_cancel (by omega)
  have hpow : rho⁻¹ ^ p = rho⁻¹ ^ (p - 1) * rho⁻¹ := by
    rw [← pow_succ, hpEq]
  rw [hpow] at hinv
  have hR : rho ^ (p - 1) ≠ 0 := pow_ne_zero _ hrho
  rw [inv_pow] at hinv
  field_simp [hrho, hR] at hinv
  have hformula :
      (∑ j : ZMod p, (1 - iota j * rho)⁻¹) =
        rho ^ (p - 1) / (rho ^ (p - 1) - 1) := by
    calc
      (∑ j : ZMod p, (1 - iota j * rho)⁻¹) =
          -(rho ^ (p - 1) / (1 - rho ^ (p - 1))) := by
            simpa [mul_comm] using hinv
      _ = rho ^ (p - 1) / (rho ^ (p - 1) - 1) := by
        rw [show 1 - rho ^ (p - 1) = -(rho ^ (p - 1) - 1) by ring, div_neg]
        ring
  exact hformula

lemma affineRationalSum (hp : p ≠ 2) {rho sigma tau : k} (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p, 1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0) :
    (∑ j : ZMod p,
      (sigma + (ZMod.castHom (dvd_refl p) k) j * tau) ^ 2 /
        (1 + (ZMod.castHom (dvd_refl p) k) j * rho)) =
      rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
        (rho ^ (p - 1) - 1) := by
  classical
  let iota := ZMod.castHom (dvd_refl p) k
  have hp3 : 3 ≤ p := by
    have hp1 := (Fact.out : p.Prime).one_lt
    omega
  have hsumOne : (∑ _j : ZMod p, (1 : k)) = 0 := by
    simp [ZMod.card]
  have hsumZMod : (∑ j : ZMod p, j) = 0 := by
    have h := FiniteField.sum_pow_lt_card_sub_one (ZMod p) 1 (by
      rw [ZMod.card]
      omega)
    simpa using h
  have hsumJ : (∑ j : ZMod p, iota j) = 0 := by
    calc
      (∑ j : ZMod p, iota j) = iota (∑ j : ZMod p, j) := by
        rw [map_sum]
      _ = 0 := by rw [hsumZMod, map_zero]
  have hS0 := affineReciprocalSum (p := p) (k := k) hrho hnonzero
  change (∑ j : ZMod p, (1 + iota j * rho)⁻¹) = _ at hS0
  have hS1 :
      (∑ j : ZMod p, iota j / (1 + iota j * rho)) =
        -rho⁻¹ * (rho ^ (p - 1) / (rho ^ (p - 1) - 1)) := by
    calc
      (∑ j : ZMod p, iota j / (1 + iota j * rho)) =
          ∑ j : ZMod p, rho⁻¹ * (1 - (1 + iota j * rho)⁻¹) := by
            apply Finset.sum_congr rfl
            intro j _
            have hd : 1 + iota j * rho ≠ 0 := by simpa [iota] using hnonzero j
            rw [inv_eq_one_div]
            field_simp [hrho, hd]
            ring
      _ = rho⁻¹ * ((∑ _j : ZMod p, (1 : k)) -
          ∑ j : ZMod p, (1 + iota j * rho)⁻¹) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = -rho⁻¹ * (rho ^ (p - 1) / (rho ^ (p - 1) - 1)) := by
            rw [hsumOne, hS0]
            ring
  have hS2 :
      (∑ j : ZMod p, iota j ^ 2 / (1 + iota j * rho)) =
        rho⁻¹ ^ 2 * (rho ^ (p - 1) / (rho ^ (p - 1) - 1)) := by
    calc
      (∑ j : ZMod p, iota j ^ 2 / (1 + iota j * rho)) =
          ∑ j : ZMod p, rho⁻¹ *
            (iota j - iota j / (1 + iota j * rho)) := by
              apply Finset.sum_congr rfl
              intro j _
              have hd : 1 + iota j * rho ≠ 0 := by simpa [iota] using hnonzero j
              rw [inv_eq_one_div]
              field_simp [hrho, hd]
              ring
      _ = rho⁻¹ * ((∑ j : ZMod p, iota j) -
          ∑ j : ZMod p, iota j / (1 + iota j * rho)) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = rho⁻¹ ^ 2 * (rho ^ (p - 1) / (rho ^ (p - 1) - 1)) := by
            rw [hsumJ, hS1]
            ring
  calc
    (∑ j : ZMod p, (sigma + iota j * tau) ^ 2 / (1 + iota j * rho)) =
        sigma ^ 2 * (∑ j : ZMod p, (1 + iota j * rho)⁻¹) +
          (2 * sigma * tau) *
            (∑ j : ZMod p, iota j / (1 + iota j * rho)) +
          tau ^ 2 *
            (∑ j : ZMod p, iota j ^ 2 / (1 + iota j * rho)) := by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
                ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              field_simp [hnonzero j]
              ring
    _ = rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
        (rho ^ (p - 1) - 1) := by
          rw [hS0, hS1, hS2]
          ring

lemma affineRationalSum_exact (hp : p ≠ 2) {rho sigma tau : k} (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p, 1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0) :
    (∑ j : ZMod p,
      (sigma + (ZMod.castHom (dvd_refl p) k) j * tau) ^ 2 /
        (1 + (ZMod.castHom (dvd_refl p) k) j * rho)) =
      rho ^ (p - 3) * (sigma * rho - tau) ^ 2 /
        (rho ^ (p - 1) - 1) := by
  rw [affineRationalSum hp hrho hnonzero]
  have hp3 : 3 ≤ p := by
    have hp1 := (Fact.out : p.Prime).one_lt
    omega
  have hpow : rho ^ (p - 1) = rho ^ (p - 3) * rho ^ 2 := by
    rw [← pow_add]
    congr
    omega
  rw [hpow]
  congr 1
  field_simp [hrho]

lemma primeFieldUnitProduct :
    (∏ u : (ZMod p)ˣ, (ZMod.castHom (dvd_refl p) k) (u : ZMod p)) = -1 := by
  let iota := ZMod.castHom (dvd_refl p) k
  have hZ : (∏ u : (ZMod p)ˣ, (u : ZMod p)) = -1 := by
    calc
      (∏ u : (ZMod p)ˣ, (u : ZMod p)) =
          ((∏ u : (ZMod p)ˣ, u : (ZMod p)ˣ) : ZMod p) := by
            change (∏ u : (ZMod p)ˣ, (Units.coeHom (ZMod p)) u) = _
            symm
            simp
      _ = -1 := by rw [FiniteField.prod_univ_units_id_eq_neg_one]; rfl
  calc
    (∏ u : (ZMod p)ˣ, iota (u : ZMod p)) =
        iota (∏ u : (ZMod p)ˣ, (u : ZMod p)) := by rw [map_prod]
    _ = -1 := by rw [hZ, map_neg, map_one]

lemma primeFieldUnitSum (hp : p ≠ 2) :
    (∑ u : (ZMod p)ˣ, (ZMod.castHom (dvd_refl p) k) (u : ZMod p)) = 0 := by
  let iota := ZMod.castHom (dvd_refl p) k
  have hp3 : 3 ≤ p := by
    have hp1 := (Fact.out : p.Prime).one_lt
    omega
  have hZ : (∑ u : (ZMod p)ˣ, (u : ZMod p)) = 0 := by
    have h := FiniteField.sum_pow_units (ZMod p) 1
    rw [ZMod.card, if_neg] at h
    · simpa using h
    · intro hdvd
      have hle := Nat.le_of_dvd (by omega : 0 < 1) hdvd
      omega
  calc
    (∑ u : (ZMod p)ˣ, iota (u : ZMod p)) =
        iota (∑ u : (ZMod p)ˣ, (u : ZMod p)) := by rw [map_sum]
    _ = 0 := by rw [hZ, map_zero]

omit [Fact p.Prime] in
lemma quadraticPhase_prod [Fintype k] {I : Type*} [Fintype I] (hp : p ≠ 2)
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (a b : I → k)
    (ha : ∀ i, a i ≠ 0) :
    (∏ i, quadraticPhase psi (a i) (b i)) =
      finiteQuadraticChar k (∏ i, a i) *
        psi (∑ i, -(b i) ^ 2 / (2 * a i)) *
          quadraticPhase psi 1 0 ^ Fintype.card I := by
  classical
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have hnu :
      (∏ i, finiteQuadraticChar k (a i)) =
        finiteQuadraticChar k (∏ i, a i) := by
    change (∏ i, (finiteQuadraticChar k).toMonoidHom (a i)) =
      (finiteQuadraticChar k).toMonoidHom (∏ i, a i)
    rw [map_prod]
  have hpsiSum :
      (∏ i, psi (-(b i) ^ 2 / (2 * a i))) =
        psi (∑ i, -(b i) ^ 2 / (2 * a i)) := by
    have h := map_sum psi.toAddMonoidHom
      (fun i : I => -(b i) ^ 2 / (2 * a i)) Finset.univ
    exact congrArg Additive.toMul h.symm
  calc
    (∏ i, quadraticPhase psi (a i) (b i)) =
        ∏ i, (finiteQuadraticChar k (a i) *
          psi (-(b i) ^ 2 / (2 * a i)) * quadraticPhase psi 1 0) := by
            apply Finset.prod_congr rfl
            intro i _
            exact quadraticPhase_eq_basic hchar hpsi (ha i) (b i)
    _ = (∏ i, finiteQuadraticChar k (a i)) *
        (∏ i, psi (-(b i) ^ 2 / (2 * a i))) *
          ∏ _i : I, quadraticPhase psi 1 0 := by
            simp_rw [Finset.prod_mul_distrib]
    _ = finiteQuadraticChar k (∏ i, a i) *
        psi (∑ i, -(b i) ^ 2 / (2 * a i)) *
          quadraticPhase psi 1 0 ^ Fintype.card I := by
            rw [hnu, hpsiSum]
            rw [Finset.prod_const, Finset.card_univ]

omit [CharP k p] in
lemma affineQuadraticCharCoefficients [Fintype k] (hp : p ≠ 2)
    {rho a0 : k} (hrho : rho ≠ 0) (ha0 : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹)
    (ha0ne : a0 ≠ 0) :
    finiteQuadraticChar k (-a0 * rho ^ (p - 1)) =
      finiteQuadraticChar k (1 - rho ^ (p - 1)) := by
  let nu := finiteQuadraticChar k
  have hR : rho ^ (p - 1) ≠ 0 := pow_ne_zero _ hrho
  rcases (Fact.out : p.Prime).odd_of_ne_two hp with ⟨m, hm⟩
  have hpSub : p - 1 = 2 * m := by omega
  have hnuR : nu (rho ^ (p - 1)) = 1 := by
    rw [map_pow, hpSub, pow_mul, finiteQuadraticChar_sq k hrho, one_pow]
  have hnuA : nu a0 = nu (1 - (rho ^ (p - 1))⁻¹) := by
    calc
      nu a0 = nu a0 ^ p := by
        rw [hm, pow_add, pow_mul, finiteQuadraticChar_sq k ha0ne, one_pow, one_mul,
          pow_one]
      _ = nu (a0 ^ p) := by rw [map_pow]
      _ = nu (1 - (rho ^ (p - 1))⁻¹) := by rw [ha0]
  have hnuRinv : nu (rho ^ (p - 1))⁻¹ = 1 := by
    simp only [nu]
    change (finiteQuadraticChar k).toMonoidWithZeroHom
      (rho ^ (p - 1))⁻¹ = 1
    rw [map_inv₀]
    change ((finiteQuadraticChar k) (rho ^ (p - 1)))⁻¹ = 1
    rw [hnuR, inv_one]
  have hrewrite :
      1 - (rho ^ (p - 1))⁻¹ =
        -(1 - rho ^ (p - 1)) * (rho ^ (p - 1))⁻¹ := by
    field_simp [hR]
    ring
  rw [show -a0 * rho ^ (p - 1) = (-1) * a0 * rho ^ (p - 1) by ring,
    map_mul, map_mul, hnuA, hrewrite, map_mul,
    show -(1 - rho ^ (p - 1)) = (-1) * (1 - rho ^ (p - 1)) by ring,
    map_mul, hnuRinv, hnuR]
  simp only [nu] at *
  have hsq := finiteQuadraticChar_sq k (a := (-1 : k)) (neg_ne_zero.mpr one_ne_zero)
  simp only [mul_one]
  rw [← mul_assoc, ← pow_two, hsq, one_mul]

lemma affineAdditiveExponentPow (hp : p ≠ 2) {rho sigma tau a0 b0 : k}
    (hrho : rho ≠ 0) (hden : rho ^ (p - 1) - 1 ≠ 0)
    (ha0 : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹)
    (hb0 : b0 ^ p = sigma - rho⁻¹ * tau) :
    (-b0 ^ 2 / (2 * a0)) ^ p =
      -(rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
        (rho ^ (p - 1) - 1)) / 2 := by
  have hR : rho ^ (p - 1) ≠ 0 := pow_ne_zero _ hrho
  rcases (Fact.out : p.Prime).odd_of_ne_two hp with ⟨m, hm⟩
  have hnegOne : (-1 : k) ^ p = -1 := by
    rw [hm, pow_add, pow_mul]
    simp
  have htwoPow : (2 : k) ^ p = 2 := by
    calc
      (2 : k) ^ p = (1 + 1) ^ p := by norm_num
      _ = 1 ^ p + 1 ^ p := add_pow_char 1 1 p
      _ = 2 := by norm_num
  have hbSquare : (b0 ^ 2) ^ p = (b0 ^ p) ^ 2 := by
    simp only [← pow_mul]
    rw [mul_comm]
  rw [div_pow, mul_pow, neg_pow, hnegOne, hbSquare, hb0, htwoPow, ha0]
  field_simp [hR, hden]

/-- The affine-pencil product identity from `lem:affine-pencil`, with the prime field
indexed by `ZMod p` and its nonzero elements by `(ZMod p)ˣ`. -/
theorem affinePencil [Fintype k] (hp : p ≠ 2) (psi : FiniteAddChar k)
    (hpsi : psi ≠ 1) (hfrob : ∀ z : k, psi (z ^ p) = psi z)
    {rho sigma tau a0 b0 : k} (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p,
      1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0)
    (ha0 : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹)
    (hb0 : b0 ^ p = sigma - rho⁻¹ * tau) :
    quadraticPhase psi a0 b0 *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase psi
            ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * rho)
            ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * tau)) =
      ∏ j : ZMod p,
        quadraticPhase psi
          (1 + (ZMod.castHom (dvd_refl p) k) j * rho)
          (sigma + (ZMod.castHom (dvd_refl p) k) j * tau) := by
  classical
  let iota := ZMod.castHom (dvd_refl p) k
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  have hR : rho ^ (p - 1) ≠ 0 := pow_ne_zero _ hrho
  have hcoeff := affineCoefficientProduct (p := p) (k := k) hrho
  change (∏ j : ZMod p, (1 + iota j * rho)) = 1 - rho ^ (p - 1) at hcoeff
  have hcoeff0 : (∏ j : ZMod p, (1 + iota j * rho)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by simpa [iota] using hnonzero j)
  have honeSub : 1 - rho ^ (p - 1) ≠ 0 := by simpa [hcoeff] using hcoeff0
  have hden : rho ^ (p - 1) - 1 ≠ 0 := by
    rw [show rho ^ (p - 1) - 1 = -(1 - rho ^ (p - 1)) by ring]
    exact neg_ne_zero.mpr honeSub
  have hbase : 1 - (rho ^ (p - 1))⁻¹ ≠ 0 := by
    intro hz
    apply hden
    field_simp [hR] at hz
    simpa using hz
  have ha0ne : a0 ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp0.ne'] at ha0
    exact hbase ha0.symm
  let A : Option (ZMod p)ˣ → k
    | none => a0
    | some u => iota (u : ZMod p) * rho
  let B : Option (ZMod p)ˣ → k
    | none => b0
    | some u => iota (u : ZMod p) * tau
  let C : ZMod p → k := fun j => 1 + iota j * rho
  let D : ZMod p → k := fun j => sigma + iota j * tau
  have hAne : ∀ x, A x ≠ 0 := by
    intro x
    cases x with
    | none => exact ha0ne
    | some u =>
        apply mul_ne_zero
        · intro hu
          apply u.ne_zero
          apply iota.injective
          simpa only [map_zero] using hu
        · exact hrho
  have hCne : ∀ j, C j ≠ 0 := by
    intro j
    simpa [C, iota] using hnonzero j
  have hunitCoeff :
      (∏ u : (ZMod p)ˣ, iota (u : ZMod p) * rho) =
        -rho ^ (p - 1) := by
    calc
      (∏ u : (ZMod p)ˣ, iota (u : ZMod p) * rho) =
          (∏ u : (ZMod p)ˣ, iota (u : ZMod p)) *
            ∏ _u : (ZMod p)ˣ, rho := by rw [Finset.prod_mul_distrib]
      _ = (-1) * rho ^ (p - 1) := by
        rw [primeFieldUnitProduct (p := p) (k := k), Finset.prod_const,
          Finset.card_univ, Fintype.card_units, ZMod.card]
      _ = -rho ^ (p - 1) := by ring
  have hAprod : (∏ x, A x) = -a0 * rho ^ (p - 1) := by
    rw [Fintype.prod_option]
    change a0 * (∏ u : (ZMod p)ˣ, iota (u : ZMod p) * rho) = _
    rw [hunitCoeff]
    ring
  have hCprod : (∏ j, C j) = 1 - rho ^ (p - 1) := by
    simpa [C] using hcoeff
  have hcharCoeff : finiteQuadraticChar k (∏ x, A x) =
      finiteQuadraticChar k (∏ j, C j) := by
    rw [hAprod, hCprod]
    exact affineQuadraticCharCoefficients hp hrho ha0 ha0ne
  have hunitExponent :
      (∑ u : (ZMod p)ˣ,
        -(B (some u)) ^ 2 / (2 * A (some u))) = 0 := by
    calc
      (∑ u : (ZMod p)ˣ, -(B (some u)) ^ 2 / (2 * A (some u))) =
          (-(tau ^ 2) / (2 * rho)) *
            ∑ u : (ZMod p)ˣ, iota (u : ZMod p) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              change -(iota (u : ZMod p) * tau) ^ 2 /
                  (2 * (iota (u : ZMod p) * rho)) = _
              have hu : iota (u : ZMod p) ≠ 0 := by
                intro hz
                apply u.ne_zero
                apply iota.injective
                simpa only [map_zero] using hz
              field_simp [hu, hrho, h2]
      _ = 0 := by
        rw [primeFieldUnitSum (p := p) (k := k) hp, mul_zero]
  have hAsum :
      (∑ x, -(B x) ^ 2 / (2 * A x)) = -b0 ^ 2 / (2 * a0) := by
    rw [Fintype.sum_option]
    change -b0 ^ 2 / (2 * a0) +
      (∑ u : (ZMod p)ˣ, -(B (some u)) ^ 2 / (2 * A (some u))) = _
    rw [hunitExponent, add_zero]
  have hrat := affineRationalSum (p := p) (k := k) hp
    (rho := rho) (sigma := sigma) (tau := tau) hrho hnonzero
  change (∑ j : ZMod p, (D j) ^ 2 / C j) =
    rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
      (rho ^ (p - 1) - 1) at hrat
  have hCsum :
      (∑ j, -(D j) ^ 2 / (2 * C j)) = (-b0 ^ 2 / (2 * a0)) ^ p := by
    calc
      (∑ j : ZMod p, -(D j) ^ 2 / (2 * C j)) =
          (-1 / 2) * ∑ j : ZMod p, (D j) ^ 2 / C j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            field_simp [h2, hCne j]
      _ = (-1 / 2) *
          (rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
            (rho ^ (p - 1) - 1)) := by rw [hrat]
      _ = (-b0 ^ 2 / (2 * a0)) ^ p := by
        rw [affineAdditiveExponentPow hp hrho hden ha0 hb0]
        ring
  have hpsiExponent :
      psi (∑ x, -(B x) ^ 2 / (2 * A x)) =
        psi (∑ j, -(D j) ^ 2 / (2 * C j)) := by
    rw [hAsum, hCsum, hfrob]
  have hcard : Fintype.card (Option (ZMod p)ˣ) = Fintype.card (ZMod p) := by
    rw [Fintype.card_option, Fintype.card_units, ZMod.card]
    omega
  change quadraticPhase psi (A none) (B none) *
      (∏ u : (ZMod p)ˣ, quadraticPhase psi (A (some u)) (B (some u))) =
    ∏ j : ZMod p, quadraticPhase psi (C j) (D j)
  rw [← Fintype.prod_option
    (fun x : Option (ZMod p)ˣ => quadraticPhase psi (A x) (B x))]
  rw [quadraticPhase_prod (p := p) hp psi hpsi A B hAne,
    quadraticPhase_prod (p := p) hp psi hpsi C D hCne,
    hcharCoeff, hpsiExponent, hcard]

private lemma finiteQuadraticChar_map_mul_apply [Fintype k] (x y : k) :
    finiteQuadraticChar k (x * y) =
      finiteQuadraticChar k x * finiteQuadraticChar k y :=
  (finiteQuadraticChar k).map_mul' x y

omit [Fact p.Prime] in
private lemma quadraticPhase_scale [Fintype k] (hp : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {a c : k} (ha : a ≠ 0) (hc : c ≠ 0) (b : k) :
    quadraticPhase psi (c * a) (c * b) =
      finiteQuadraticChar k c *
        psi (-(c - 1) * b ^ 2 / (2 * a)) * quadraticPhase psi a b := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have hca : c * a ≠ 0 := mul_ne_zero hc ha
  rw [quadraticPhase_eq_basic hchar hpsi hca,
    quadraticPhase_eq_basic hchar hpsi ha,
    finiteQuadraticChar_map_mul_apply]
  have harg : -(c * b) ^ 2 / (2 * (c * a)) =
      -(c - 1) * b ^ 2 / (2 * a) + -b ^ 2 / (2 * a) := by
    field_simp
    ring
  rw [harg, psi.map_add_eq_mul]
  ring

private lemma quadraticPhase_frobenius [Fintype k]
    (psi : FiniteAddChar k) (hfrob : ∀ z : k, psi (z ^ p) = psi z)
    (a b : k) :
    quadraticPhase psi (a ^ p) (b ^ p) = quadraticPhase psi a b := by
  rw [quadraticPhase, quadraticPhase]
  congr 1
  rw [quadraticSum, quadraticSum]
  symm
  apply Fintype.sum_equiv (frobeniusEquiv k p)
  intro x
  change psi (a / 2 * x ^ 2 + b * x) =
    psi (a ^ p / 2 * (x ^ p) ^ 2 + b ^ p * x ^ p)
  rw [← hfrob (a / 2 * x ^ 2 + b * x)]
  congr 1
  have htwoPow : (2 : k) ^ p = 2 := by
    calc
      (2 : k) ^ p = (1 + 1) ^ p := by norm_num
      _ = 1 ^ p + 1 ^ p := add_pow_char 1 1 p
      _ = 2 := by norm_num
  rw [add_pow_char, mul_pow, div_pow, htwoPow, mul_pow]
  ring

/-- Common scaling of every row in the affine-pencil quotient leaves the
normalized quotient unchanged.  The upper row is written at Frobenius depth,
so the chosen root `c0` with `c0 ^ p = c` is part of the data. -/
theorem affinePencil_homogeneous_quotient [Fintype k]
    (hp : p ≠ 2) (psi : FiniteAddChar k) (hpsi : psi ≠ 1)
    (hfrob : ∀ z : k, psi (z ^ p) = psi z)
    {rho sigma tau a0 b0 c0 c : k}
    (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p,
      1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0)
    (ha0 : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹)
    (hb0 : b0 ^ p = sigma - rho⁻¹ * tau)
    (hc0pow : c0 ^ p = c) (hc : c ≠ 0) :
    (quadraticPhase psi (c * a0 ^ p) (c * b0 ^ p) *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase psi
            (c * ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * rho))
            (c * ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * tau)))) /
      (∏ j : ZMod p,
        quadraticPhase psi
          (c * (1 + (ZMod.castHom (dvd_refl p) k) j * rho))
          (c * (sigma + (ZMod.castHom (dvd_refl p) k) j * tau))) =
    (quadraticPhase psi a0 b0 *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase psi
            ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * rho)
            ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * tau))) /
      (∏ j : ZMod p,
        quadraticPhase psi
          (1 + (ZMod.castHom (dvd_refl p) k) j * rho)
          (sigma + (ZMod.castHom (dvd_refl p) k) j * tau)) := by
  classical
  let iota := ZMod.castHom (dvd_refl p) k
  let nu := finiteQuadraticChar k
  let z0 := -b0 ^ 2 / (2 * a0)
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  have hR : rho ^ (p - 1) ≠ 0 := pow_ne_zero _ hrho
  have hcoeff := affineCoefficientProduct (p := p) (k := k) hrho
  change (∏ j : ZMod p, (1 + iota j * rho)) = 1 - rho ^ (p - 1) at hcoeff
  have hcoeff0 : (∏ j : ZMod p, (1 + iota j * rho)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by simpa [iota] using hnonzero j)
  have honeSub : 1 - rho ^ (p - 1) ≠ 0 := by
    simpa [hcoeff] using hcoeff0
  have hden : rho ^ (p - 1) - 1 ≠ 0 := by
    rw [show rho ^ (p - 1) - 1 = -(1 - rho ^ (p - 1)) by ring]
    exact neg_ne_zero.mpr honeSub
  have hbase : 1 - (rho ^ (p - 1))⁻¹ ≠ 0 := by
    intro hz
    apply hden
    field_simp [hR] at hz
    simpa using hz
  have ha0ne : a0 ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp0.ne'] at ha0
    exact hbase ha0.symm
  have hc0 : c0 ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp0.ne'] at hc0pow
    exact hc hc0pow.symm
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hpOdd : p = 2 * m + 1 := by omega
  have hpEven : p - 1 = 2 * m := by omega
  have hnuOdd (x : k) (hx : x ≠ 0) : nu x ^ p = nu x := by
    rw [hpOdd, pow_add, pow_mul, finiteQuadraticChar_sq k hx,
      one_pow, pow_one, one_mul]
  have hnuEven : nu c ^ (p - 1) = 1 := by
    rw [hpEven, pow_mul, finiteQuadraticChar_sq k hc, one_pow]
  have hnuRelation : nu c = nu c0 := by
    calc
      nu c = nu (c0 ^ p) := by rw [hc0pow]
      _ = nu c0 ^ p := by rw [map_pow]
      _ = nu c0 := hnuOdd c0 hc0
  have hnuCPow : nu c ^ p = nu c0 := by
    rw [hnuOdd c hc, hnuRelation]
  have hupperFrob :
      quadraticPhase psi (c * a0 ^ p) (c * b0 ^ p) =
        quadraticPhase psi (c0 * a0) (c0 * b0) := by
    rw [← hc0pow, ← mul_pow, ← mul_pow]
    exact quadraticPhase_frobenius psi hfrob (c0 * a0) (c0 * b0)
  have hupperScale :
      quadraticPhase psi (c0 * a0) (c0 * b0) =
        nu c0 * psi ((c0 - 1) * z0) * quadraticPhase psi a0 b0 := by
    rw [quadraticPhase_scale hp hpsi ha0ne hc0 b0]
    congr 2
    simp only [z0]
    ring_nf
  have hunitArg :
      (∑ u : (ZMod p)ˣ,
        -(c - 1) * (iota (u : ZMod p) * tau) ^ 2 /
          (2 * (iota (u : ZMod p) * rho))) = 0 := by
    calc
      _ = (-(c - 1) * tau ^ 2 / (2 * rho)) *
          ∑ u : (ZMod p)ˣ, iota (u : ZMod p) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _hu
            have hiota : iota (u : ZMod p) ≠ 0 := by
              intro hu
              apply u.ne_zero
              apply iota.injective
              simpa only [map_zero] using hu
            field_simp [hiota, hrho, h2]
      _ = 0 := by
        rw [primeFieldUnitSum (p := p) (k := k) hp, mul_zero]
  have hunitPsi :
      (∏ u : (ZMod p)ˣ,
        psi (-(c - 1) * (iota (u : ZMod p) * tau) ^ 2 /
          (2 * (iota (u : ZMod p) * rho)))) = 1 := by
    have hmap := map_sum psi.toAddMonoidHom
      (fun u : (ZMod p)ˣ =>
        -(c - 1) * (iota (u : ZMod p) * tau) ^ 2 /
          (2 * (iota (u : ZMod p) * rho))) Finset.univ
    have hprod :
        (∏ u : (ZMod p)ˣ,
          psi (-(c - 1) * (iota (u : ZMod p) * tau) ^ 2 /
            (2 * (iota (u : ZMod p) * rho)))) =
          psi (∑ u : (ZMod p)ˣ,
            -(c - 1) * (iota (u : ZMod p) * tau) ^ 2 /
              (2 * (iota (u : ZMod p) * rho))) :=
      congrArg Additive.toMul hmap.symm
    rw [hprod, hunitArg, AddChar.map_zero_eq_one]
  have hunitScale :
      (∏ u : (ZMod p)ˣ,
        quadraticPhase psi (c * (iota (u : ZMod p) * rho))
          (c * (iota (u : ZMod p) * tau))) =
      ∏ u : (ZMod p)ˣ,
        quadraticPhase psi (iota (u : ZMod p) * rho)
          (iota (u : ZMod p) * tau) := by
    have hpoint (u : (ZMod p)ˣ) :
        quadraticPhase psi (c * (iota (u : ZMod p) * rho))
            (c * (iota (u : ZMod p) * tau)) =
          nu c *
            psi (-(c - 1) * (iota (u : ZMod p) * tau) ^ 2 /
              (2 * (iota (u : ZMod p) * rho))) *
            quadraticPhase psi (iota (u : ZMod p) * rho)
              (iota (u : ZMod p) * tau) := by
      apply quadraticPhase_scale hp hpsi
      · exact mul_ne_zero (by
          intro hu
          apply u.ne_zero
          apply iota.injective
          simpa only [map_zero] using hu) hrho
      · exact hc
    simp_rw [hpoint, Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_units, ZMod.card,
      hnuEven, hunitPsi, one_mul, one_mul]
  let C : ZMod p → k := fun j => 1 + iota j * rho
  let D : ZMod p → k := fun j => sigma + iota j * tau
  have hCne : ∀ j, C j ≠ 0 := by
    intro j
    simpa [C, iota] using hnonzero j
  have hrat := affineRationalSum (p := p) (k := k) hp
    (rho := rho) (sigma := sigma) (tau := tau) hrho hnonzero
  change (∑ j : ZMod p, (D j) ^ 2 / C j) =
    rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
      (rho ^ (p - 1) - 1) at hrat
  have hCsum :
      (∑ j, -(D j) ^ 2 / (2 * C j)) = z0 ^ p := by
    calc
      (∑ j : ZMod p, -(D j) ^ 2 / (2 * C j)) =
          (-1 / 2) * ∑ j : ZMod p, (D j) ^ 2 / C j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            field_simp [h2, hCne j]
      _ = (-1 / 2) *
          (rho ^ (p - 1) * (sigma - rho⁻¹ * tau) ^ 2 /
            (rho ^ (p - 1) - 1)) := by rw [hrat]
      _ = z0 ^ p := by
        simp only [z0]
        rw [affineAdditiveExponentPow hp hrho hden ha0 hb0]
        ring
  have hdenArg :
      (∑ j : ZMod p,
        -(c - 1) * (D j) ^ 2 / (2 * C j)) = (c - 1) * z0 ^ p := by
    calc
      _ = (c - 1) * ∑ j : ZMod p, -(D j) ^ 2 / (2 * C j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (c - 1) * z0 ^ p := by rw [hCsum]
  have hscaleFrob :
      psi ((c0 - 1) * z0) = psi ((c - 1) * z0 ^ p) := by
    calc
      psi ((c0 - 1) * z0) = psi (((c0 - 1) * z0) ^ p) := (hfrob _).symm
      _ = psi ((c - 1) * z0 ^ p) := by
        congr 1
        rw [mul_pow, sub_pow_char, one_pow, hc0pow]
  have hdenPsi :
      (∏ j : ZMod p,
        psi (-(c - 1) * (D j) ^ 2 / (2 * C j))) =
        psi ((c0 - 1) * z0) := by
    have hmap := map_sum psi.toAddMonoidHom
      (fun j : ZMod p => -(c - 1) * (D j) ^ 2 / (2 * C j)) Finset.univ
    have hprod :
        (∏ j : ZMod p,
          psi (-(c - 1) * (D j) ^ 2 / (2 * C j))) =
          psi (∑ j : ZMod p,
            -(c - 1) * (D j) ^ 2 / (2 * C j)) :=
      congrArg Additive.toMul hmap.symm
    rw [hprod, hdenArg, ← hscaleFrob]
  have hdenScale :
      (∏ j : ZMod p,
        quadraticPhase psi (c * C j) (c * D j)) =
      (nu c0 * psi ((c0 - 1) * z0)) *
        ∏ j : ZMod p, quadraticPhase psi (C j) (D j) := by
    have hpoint (j : ZMod p) :
        quadraticPhase psi (c * C j) (c * D j) =
          nu c * psi (-(c - 1) * (D j) ^ 2 / (2 * C j)) *
            quadraticPhase psi (C j) (D j) := by
      exact quadraticPhase_scale hp hpsi (hCne j) hc (D j)
    simp_rw [hpoint, Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_univ, ZMod.card, hnuCPow, hdenPsi]
  let scale : ℂ := nu c0 * psi ((c0 - 1) * z0)
  have hscale_ne : scale ≠ 0 := by
    apply mul_ne_zero
    · intro hzero
      have hn := finiteQuadraticChar_norm k hc0
      change ‖nu c0‖ = 1 at hn
      rw [hzero, norm_zero] at hn
      norm_num at hn
    · intro hzero
      have hn := finiteAddChar_norm psi ((c0 - 1) * z0)
      rw [hzero, norm_zero] at hn
      norm_num at hn
  have hnumScale :
      quadraticPhase psi (c * a0 ^ p) (c * b0 ^ p) *
          (∏ u : (ZMod p)ˣ,
            quadraticPhase psi (c * (iota (u : ZMod p) * rho))
              (c * (iota (u : ZMod p) * tau))) =
        scale * (quadraticPhase psi a0 b0 *
          ∏ u : (ZMod p)ˣ,
            quadraticPhase psi (iota (u : ZMod p) * rho)
              (iota (u : ZMod p) * tau)) := by
    rw [hupperFrob, hupperScale, hunitScale]
    dsimp only [scale]
    ring
  change
    (quadraticPhase psi (c * a0 ^ p) (c * b0 ^ p) *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase psi (c * (iota (u : ZMod p) * rho))
            (c * (iota (u : ZMod p) * tau)))) /
      (∏ j : ZMod p, quadraticPhase psi (c * C j) (c * D j)) = _
  rw [hnumScale, hdenScale]
  exact mul_div_mul_left _ _ hscale_ne

end

end LanglandsFirstMainLemma
