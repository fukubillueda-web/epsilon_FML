import LanglandsFirstMainLemma.FiniteField.CharacterAPI
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase

/-!
# Hasse functions over finite fields

A Hasse function for an additive character `psi` is a nowhere-zero complex-valued
function whose polar form is `(x, y) ↦ psi (x * y)`. Thus its defining law is

`phi (x + y) = phi x * phi y * psi (x * y)`.

The sign in this law is the one used in the odd-conductor part of Lamprecht's formula.
This file packages the law and proves the translation and scaling identities used in the
stationary-representative and Hasse-lift arguments.
-/

open scoped BigOperators ComplexConjugate

namespace LanglandsFirstMainLemma

universe u

/-- A nowhere-zero quadratic refinement of the polar character
`(x, y) ↦ psi (x * y)` on a field. -/
structure HasseFunction (k : Type u) [Field k] (psi : FiniteAddChar k) where
  /-- The underlying complex-valued function. -/
  toFun : k → ℂ
  /-- Hasse functions take no zero value. -/
  ne_zero' : ∀ x, toFun x ≠ 0
  /-- The quadratic-refinement law, with the manuscript's positive polar phase. -/
  map_add' : ∀ x y, toFun (x + y) = toFun x * toFun y * psi (x * y)

namespace HasseFunction

variable {k : Type u} [Field k] {psi : FiniteAddChar k}

instance : FunLike (HasseFunction k psi) k ℂ where
  coe := HasseFunction.toFun
  coe_injective phi phi' h := by
    cases phi
    cases phi'
    simp_all

@[ext]
theorem ext (phi phi' : HasseFunction k psi) (h : ∀ x, phi x = phi' x) : phi = phi' :=
  DFunLike.ext phi phi' h

/-- Every value of a Hasse function is nonzero. -/
theorem ne_zero (phi : HasseFunction k psi) (x : k) : phi x ≠ 0 :=
  phi.ne_zero' x

/-- The defining quadratic-refinement law. -/
theorem map_add (phi : HasseFunction k psi) (x y : k) :
    phi (x + y) = phi x * phi y * psi (x * y) :=
  phi.map_add' x y

/-- A nowhere-zero Hasse function takes the value one at zero. -/
@[simp]
theorem map_zero (phi : HasseFunction k psi) : phi 0 = 1 := by
  have h := phi.map_add 0 0
  simp only [zero_add, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  apply mul_left_cancel₀ (phi.ne_zero 0)
  simpa only [mul_one] using h.symm

/-- Twisting by the linear character `x ↦ psi (a * x)` preserves the polar character. -/
noncomputable def translate (phi : HasseFunction k psi) (a : k) : HasseFunction k psi where
  toFun x := phi x * psi (a * x)
  ne_zero' x := mul_ne_zero (phi.ne_zero x) (AddChar.val_isUnit psi _).ne_zero
  map_add' x y := by
    rw [phi.map_add, mul_add, psi.map_add_eq_mul]
    ring

@[simp]
theorem translate_apply (phi : HasseFunction k psi) (a x : k) :
    phi.translate a x = phi x * psi (a * x) :=
  rfl

/-- The representative-change translation identity in the exact orientation used by
Lamprecht's odd-conductor formula. -/
theorem translate_apply_eq_inv_mul (phi : HasseFunction k psi) (a x : k) :
    phi.translate a x = (phi a)⁻¹ * phi (x + a) := by
  rw [translate_apply]
  rw [phi.map_add]
  field_simp [phi.ne_zero a]

/-- Iterating the refinement law gives the binomial correction used in the closed-point
calculation of the Hasse-function lift. -/
theorem map_nsmul (phi : HasseFunction k psi) (n : ℕ) (x : k) :
    phi (n • x) = phi x ^ n * psi ((n.choose 2 : k) * x ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, phi.map_add, ih]
      calc
        (phi x ^ n * psi ((n.choose 2 : k) * x ^ 2)) * phi x * psi (n • x * x) =
            phi x ^ (n + 1) *
              (psi ((n.choose 2 : k) * x ^ 2) * psi (n • x * x)) := by
                rw [pow_succ]
                ring
        _ = phi x ^ (n + 1) *
            psi ((n.choose 2 : k) * x ^ 2 + n • x * x) := by
              rw [psi.map_add_eq_mul]
        _ = phi x ^ (n + 1) * psi ((((n + 1).choose 2 : ℕ) : k) * x ^ 2) := by
              congr 2
              simp only [nsmul_eq_mul]
              rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
              push_cast
              ring

/-- Rescaling the argument by `c` rescales the polar character by `c²`. -/
noncomputable def scale (phi : HasseFunction k psi) (c : k) :
    HasseFunction k (psi.mulShift (c ^ 2)) where
  toFun x := phi (c * x)
  ne_zero' x := phi.ne_zero _
  map_add' x y := by
    rw [mul_add, phi.map_add]
    simp only [AddChar.mulShift_apply]
    rw [show c * x * (c * y) = c ^ 2 * (x * y) by ring]

@[simp]
theorem scale_apply (phi : HasseFunction k psi) (c x : k) :
    phi.scale c x = phi (c * x) :=
  rfl

section FiniteSums

variable [Fintype k]

/-- The refinement law and finiteness force every Hasse-function value to have norm one. -/
@[simp]
theorem norm_apply (phi : HasseFunction k psi) (x : k) : ‖phi x‖ = 1 := by
  have hp : ringChar k ≠ 0 := CharP.ringChar_ne_zero_of_finite k
  have hsmul : ringChar k • x = 0 := by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have h := congrArg norm (phi.map_nsmul (ringChar k) x)
  rw [hsmul, phi.map_zero, norm_one, norm_mul, norm_pow, finiteAddChar_norm, mul_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp).1 h.symm

/-- The finite Hasse sum attached to `phi`. -/
noncomputable def sum (phi : HasseFunction k psi) : ℂ :=
  ∑ x : k, phi x

/-- The total complex phase of the Hasse sum. -/
noncomputable def sumPhase (phi : HasseFunction k psi) : ℂ :=
  phase phi.sum

/-- Translating a Hasse function multiplies its sum by the inverse value at the
translation parameter. -/
theorem sum_translate (phi : HasseFunction k psi) (a : k) :
    (phi.translate a).sum = (phi a)⁻¹ * phi.sum := by
  rw [sum, sum]
  calc
    (∑ x : k, phi.translate a x) = ∑ x : k, (phi a)⁻¹ * phi (x + a) := by
      apply Finset.sum_congr rfl
      intro x _
      exact phi.translate_apply_eq_inv_mul a x
    _ = (phi a)⁻¹ * ∑ x : k, phi (x + a) := by
      rw [Finset.mul_sum]
    _ = (phi a)⁻¹ * ∑ x : k, phi x := by
      congr 1
      apply Fintype.sum_bijective (fun x : k ↦ x + a) (AddGroup.addRight_bijective a)
      intro x
      rfl

/-- A nonzero argument rescaling does not change the Hasse sum. -/
theorem sum_scale (phi : HasseFunction k psi) (c : k) (hc : c ≠ 0) :
    (phi.scale c).sum = phi.sum := by
  rw [sum, sum]
  apply Fintype.sum_bijective (fun x : k ↦ c * x) (mulLeft_bijective₀ c hc)
  intro x
  rfl

/-- The exact conjugate-product form of the magnitude identity for a Hasse sum. -/
theorem sum_star_mul_self (phi : HasseFunction k psi) (hpsi : psi ≠ 1) :
    star phi.sum * phi.sum = (Fintype.card k : ℂ) := by
  classical
  have hunit : ∀ y : k, star (phi y) * phi y = 1 := by
    intro y
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, phi.norm_apply y]
    norm_num
  calc
    star phi.sum * phi.sum =
        (∑ y : k, star (phi y)) * (∑ x : k, phi x) := by
          rw [sum, Complex.star_def, map_sum]
    _ = ∑ y : k, star (phi y) * (∑ x : k, phi x) := by
      rw [Finset.sum_mul]
    _ = ∑ y : k, ∑ h : k, star (phi y) * phi (y + h) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      simpa using
        ((AddGroup.addLeft_bijective y).sum_comp
          (fun x : k ↦ star (phi y) * phi x)).symm
    _ = ∑ h : k, ∑ y : k, star (phi y) * phi (y + h) := by
      rw [Finset.sum_comm]
    _ = ∑ h : k, phi h * ∑ y : k, psi (h * y) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [phi.map_add]
      calc
        star (phi y) * (phi y * phi h * psi (y * h)) =
            (star (phi y) * phi y) * phi h * psi (y * h) := by ring
        _ = phi h * psi (h * y) := by
          rw [hunit]
          simp only [one_mul, mul_comm y h]
    _ = ∑ h : k, if h = 0 then (Fintype.card k : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h = 0
      · subst h
        simp
      · have hsum : (∑ y : k, psi (h * y)) = 0 := by
          change (∑ y : k, (psi.mulShift h) y) = 0
          exact finiteAddChar_sum_eq_zero ((AddChar.IsPrimitive.of_ne_one hpsi) hh)
        rw [hsum]
        simp [hh]
    _ = (Fintype.card k : ℂ) := by simp

/-- The manuscript's exact squared-magnitude identity for a Hasse sum. -/
theorem sum_norm_sq (phi : HasseFunction k psi) (hpsi : psi ≠ 1) :
    ‖phi.sum‖ ^ 2 = (Fintype.card k : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_inj]
  rw [Complex.normSq_eq_conj_mul_self]
  simpa [Complex.star_def] using sum_star_mul_self phi hpsi

/-- A Hasse sum with nontrivial polar additive character is nonzero. -/
theorem sum_ne_zero (phi : HasseFunction k psi) (hpsi : psi ≠ 1) :
    phi.sum ≠ 0 := by
  intro hzero
  have hs := sum_norm_sq phi hpsi
  rw [hzero, norm_zero] at hs
  norm_num at hs
  have hcard : (Fintype.card k : ℝ) ≠ 0 := by positivity
  exact hcard hs.symm

/-- The exact magnitude of a Hasse sum. -/
theorem sum_norm (phi : HasseFunction k psi) (hpsi : psi ≠ 1) :
    ‖phi.sum‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have hs := sum_norm_sq phi hpsi
  have hcard : (0 : ℝ) ≤ Fintype.card k := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg phi.sum, Real.sqrt_nonneg (Fintype.card k : ℝ)]

/-- Translation transports the Hasse-sum phase by the inverse Hasse value. -/
theorem sumPhase_translate (phi : HasseFunction k psi) (hpsi : psi ≠ 1) (a : k) :
    (phi.translate a).sumPhase = (phi a)⁻¹ * phi.sumPhase := by
  rw [sumPhase, sumPhase, sum_translate]
  apply phase_mul_of_norm_eq_one
  · rw [norm_inv, norm_apply]
    norm_num
  · exact sum_ne_zero phi hpsi

end FiniteSums

section QuadraticExamples

/-- In odd characteristic, the standard quadratic exponential is a Hasse function with
polar character `psi (a * x * y)`. -/
noncomputable def quadratic (hchar : ringChar k ≠ 2) (psi : FiniteAddChar k) (a b : k) :
    HasseFunction k (psi.mulShift a) where
  toFun x := psi (a / 2 * x ^ 2 + b * x)
  ne_zero' x := (AddChar.val_isUnit psi _).ne_zero
  map_add' x y := by
    simp only [AddChar.mulShift_apply]
    rw [← psi.map_add_eq_mul, ← psi.map_add_eq_mul]
    congr 1
    field_simp [Ring.two_ne_zero hchar]
    ring

@[simp]
theorem quadratic_apply (hchar : ringChar k ≠ 2) (psi : FiniteAddChar k) (a b x : k) :
    quadratic hchar psi a b x = psi (a / 2 * x ^ 2 + b * x) :=
  rfl

variable [Fintype k]

/-- The sum of the standard Hasse function is exactly the manuscript's quadratic sum. -/
theorem sum_quadratic (hchar : ringChar k ≠ 2) (psi : FiniteAddChar k) (a b : k) :
    (quadratic hchar psi a b).sum = quadraticSum psi a b :=
  rfl

/-- The Hasse-sum phase of the standard quadratic refinement is exactly `quadraticPhase`. -/
theorem sumPhase_quadratic (hchar : ringChar k ≠ 2) (psi : FiniteAddChar k) (a b : k) :
    (quadratic hchar psi a b).sumPhase = quadraticPhase psi a b :=
  rfl

end QuadraticExamples

end HasseFunction

end LanglandsFirstMainLemma
