import LanglandsFirstMainLemma.FiniteField.CharacterAPI
import LanglandsFirstMainLemma.Basic.Phase

/-!
# Normalized quadratic phases over finite fields

This file formalizes `lem:quadratic-phase-new` from the manuscript.  The raw sum is

`Sψ(a, b) = ∑ x, ψ((a / 2) * x ^ 2 + b * x)`,

and `quadraticPhase ψ a b` is its total complex phase.  All substantive results assume
that the finite field has odd characteristic, that `ψ` is nontrivial, and that the
quadratic coefficient `a` is nonzero.
-/

open scoped BigOperators

namespace LanglandsFirstMainLemma

section QuadraticCharacter

variable (k : Type*) [Field k] [Fintype k]

/-- The quadratic character of `k`, embedded in `ℂ` and extended by zero at zero. -/
noncomputable def finiteQuadraticChar : FiniteMulChar k := by
  classical
  exact (quadraticChar k).ringHomComp (Int.castRingHom ℂ)

/-- The complex quadratic character is nontrivial in odd characteristic. -/
theorem finiteQuadraticChar_ne_one (hchar : ringChar k ≠ 2) :
    finiteQuadraticChar k ≠ 1 := by
  classical
  exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2
    (quadraticChar_ne_one hchar)

/-- The complex quadratic character still has order two. -/
theorem finiteQuadraticChar_isQuadratic :
    (finiteQuadraticChar k).IsQuadratic := by
  classical
  exact (quadraticChar_isQuadratic k).comp (Int.castRingHom ℂ)

/-- The exact square of the quadratic character at a nonzero element. -/
@[simp]
theorem finiteQuadraticChar_sq {a : k} (ha : a ≠ 0) :
    finiteQuadraticChar k a ^ 2 = 1 := by
  classical
  change ((quadraticChar k a : ℤ) : ℂ) ^ 2 = 1
  rw [← Int.cast_pow, quadraticChar_sq_one ha]
  norm_num

/-- Quadratic-character values at nonzero elements have complex norm one. -/
@[simp]
theorem finiteQuadraticChar_norm {a : k} (ha : a ≠ 0) :
    ‖finiteQuadraticChar k a‖ = 1 := by
  classical
  rcases quadraticChar_dichotomy ha with h | h
  · change ‖((quadraticChar k a : ℤ) : ℂ)‖ = 1
    rw [h]
    norm_num
  · change ‖((quadraticChar k a : ℤ) : ℂ)‖ = 1
    rw [h]
    norm_num

end QuadraticCharacter

section QuadraticSums

variable {k : Type*} [Field k] [Fintype k]

/-- Every value of a complex additive character of a finite field has norm one. -/
@[simp]
theorem finiteAddChar_norm (psi : FiniteAddChar k) (x : k) : ‖psi x‖ = 1 := by
  have hpos : 0 < ringChar k :=
    Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite k)
  simpa using
    (Complex.norm_eq_one_of_mem_rootsOfUnity (psi.val_mem_rootsOfUnity x hpos))

/-- The unnormalized quadratic sum in the manuscript's `a / 2` convention. -/
noncomputable def quadraticSum (psi : FiniteAddChar k) (a b : k) : ℂ :=
  ∑ x : k, psi (a / 2 * x ^ 2 + b * x)

/-- The normalized quadratic phase `Qψ(a,b)`.  The nonzero hypotheses belong to its
theorems rather than to this total definition. -/
noncomputable def quadraticPhase (psi : FiniteAddChar k) (a b : k) : ℂ :=
  phase (quadraticSum psi a b)

/-- Completing the square at the level of the raw finite sum. -/
theorem quadraticSum_completeSquare (hchar : ringChar k ≠ 2)
    (psi : FiniteAddChar k) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticSum psi a b =
      psi (-b ^ 2 / (2 * a)) * quadraticSum psi a 0 := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  rw [quadraticSum, quadraticSum]
  calc
    (∑ x : k, psi (a / 2 * x ^ 2 + b * x)) =
        ∑ y : k, psi (-b ^ 2 / (2 * a)) * psi (a / 2 * y ^ 2) := by
          apply Fintype.sum_bijective (fun x : k ↦ x + b / a)
            (AddGroup.addRight_bijective (b / a))
          intro x
          rw [← psi.map_add_eq_mul]
          congr 1
          field_simp
          ring
    _ = psi (-b ^ 2 / (2 * a)) * ∑ y : k, psi (a / 2 * y ^ 2) := by
          rw [Finset.mul_sum]
    _ = psi (-b ^ 2 / (2 * a)) *
        ∑ y : k, psi (a / 2 * y ^ 2 + 0 * y) := by simp

/-- Translating the variable by `c` changes the raw sum by the exact elementary phase
prescribed by completing the square. -/
theorem quadraticSum_translate (hchar : ringChar k ≠ 2)
    (psi : FiniteAddChar k) (a b c : k) :
    quadraticSum psi a (b + a * c) =
      psi (-(a / 2 * c ^ 2 + b * c)) * quadraticSum psi a b := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  rw [quadraticSum, quadraticSum]
  calc
    (∑ x : k, psi (a / 2 * x ^ 2 + (b + a * c) * x)) =
        ∑ y : k, psi (-(a / 2 * c ^ 2 + b * c)) *
          psi (a / 2 * y ^ 2 + b * y) := by
          apply Fintype.sum_bijective (fun x : k ↦ x + c)
            (AddGroup.addRight_bijective c)
          intro x
          rw [← psi.map_add_eq_mul]
          congr 1
          field_simp
          ring
    _ = psi (-(a / 2 * c ^ 2 + b * c)) *
        ∑ y : k, psi (a / 2 * y ^ 2 + b * y) := by
          rw [Finset.mul_sum]

/-- Counting the fibers of the squaring map gives the quadratic-character expansion. -/
private theorem sum_square_eq_character_sum (hchar : ringChar k ≠ 2)
    (psi : FiniteAddChar k) (c : k) :
    (∑ x : k, psi (c * x ^ 2)) =
      ∑ y : k, (finiteQuadraticChar k y + 1) * psi (c * y) := by
  classical
  rw [← Fintype.sum_fiberwise (fun x : k ↦ x ^ 2)
    (fun x ↦ psi (c * x ^ 2))]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ x : {x : k // x ^ 2 = y}, psi (c * (x : k) ^ 2)) =
        ∑ _x : {x : k // x ^ 2 = y}, psi (c * y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [x.property]
    _ = (finiteQuadraticChar k y + 1) * psi (c * y) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          congr 1
          change (Fintype.card {x : k // x ^ 2 = y} : ℂ) =
            (((quadraticChar k y : ℤ) : ℂ) + 1)
          norm_cast
          rw [show Fintype.card {x : k // x ^ 2 = y} =
            {x : k | x ^ 2 = y}.toFinset.card from (Set.toFinset_card _).symm]
          exact quadraticChar_card_sqrts hchar y

/-- The pure quadratic sum is a quadratic-character Gauss sum, with the exact positive
normalization and no extra sign. -/
theorem sum_quadratic_eq_gaussSum (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {c : k} (hc : c ≠ 0) :
    (∑ x : k, psi (c * x ^ 2)) =
      finiteQuadraticChar k c * gaussSum (finiteQuadraticChar k) psi := by
  classical
  let cu : kˣ := Units.mk0 c hc
  have hprimitive : psi.IsPrimitive := AddChar.IsPrimitive.of_ne_one hpsi
  have hshift : psi.mulShift c ≠ 1 := hprimitive hc
  rw [sum_square_eq_character_sum hchar]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [one_mul, ← AddChar.mulShift_apply]
  change gaussSum (finiteQuadraticChar k) (psi.mulShift c) +
      ∑ y : k, (psi.mulShift c) y = _
  rw [finiteAddChar_sum_eq_zero hshift, add_zero]
  calc
    gaussSum (finiteQuadraticChar k) (psi.mulShift c) =
        (finiteQuadraticChar k)⁻¹ cu * gaussSum (finiteQuadraticChar k) psi := by
          simpa [cu] using gaussSum_mulShift_eq (finiteQuadraticChar k) psi cu
    _ = finiteQuadraticChar k c * gaussSum (finiteQuadraticChar k) psi := by
          rw [(finiteQuadraticChar_isQuadratic k).inv]
          rfl

/-- Exact Gauss-sum expression for the manuscript's two-variable quadratic sum. -/
theorem quadraticSum_eq_gaussSum (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticSum psi a b =
      psi (-b ^ 2 / (2 * a)) * finiteQuadraticChar k (a / 2) *
        gaussSum (finiteQuadraticChar k) psi := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  rw [quadraticSum_completeSquare hchar psi ha b, quadraticSum]
  simp only [zero_mul, add_zero]
  rw [sum_quadratic_eq_gaussSum hchar hpsi (div_ne_zero ha h2)]
  ring

/-- Exact reduction to the basic normalized quadratic sum `Sψ(1,0)`. -/
theorem quadraticSum_eq_basic (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticSum psi a b =
      finiteQuadraticChar k a * psi (-b ^ 2 / (2 * a)) *
        quadraticSum psi 1 0 := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  rw [quadraticSum_eq_gaussSum hchar hpsi ha b,
    quadraticSum_eq_gaussSum hchar hpsi one_ne_zero 0]
  simp
  have hcoeff : finiteQuadraticChar k (a / 2) =
      finiteQuadraticChar k a * finiteQuadraticChar k (1 / 2) := by
    calc
      finiteQuadraticChar k (a / 2) = finiteQuadraticChar k (a * (1 / 2)) := by
        congr 1
        ring
      _ = finiteQuadraticChar k a * finiteQuadraticChar k (1 / 2) :=
        (finiteQuadraticChar k).map_mul a (1 / 2)
  rw [hcoeff]
  ring_nf

/-- The squared norm of every nondegenerate quadratic sum is exactly the field cardinality. -/
theorem quadraticSum_norm_sq (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    ‖quadraticSum psi a b‖ ^ 2 = (Fintype.card k : ℝ) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  rw [quadraticSum_eq_gaussSum hchar hpsi ha b, norm_mul, norm_mul,
    finiteAddChar_norm, finiteQuadraticChar_norm k (div_ne_zero ha h2), one_mul, one_mul]
  exact gaussSum_norm_sq (finiteQuadraticChar_ne_one k hchar) hpsi

/-- The defining quadratic sum has magnitude `|k|^(1/2)`. -/
theorem quadraticSum_norm (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    ‖quadraticSum psi a b‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have hs := quadraticSum_norm_sq hchar hpsi ha b
  have hcard : (0 : ℝ) ≤ Fintype.card k := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg (quadraticSum psi a b), Real.sqrt_nonneg (Fintype.card k : ℝ)]

/-- Every nondegenerate quadratic sum is nonzero. -/
theorem quadraticSum_ne_zero (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticSum psi a b ≠ 0 := by
  intro hzero
  have hs := quadraticSum_norm_sq hchar hpsi ha b
  rw [hzero, norm_zero] at hs
  norm_num at hs
  have hcard : (Fintype.card k : ℝ) ≠ 0 := by positivity
  exact hcard hs.symm

/-- Exact square of the raw quadratic sum, including the additive translation and
quadratic sign. -/
theorem quadraticSum_sq (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticSum psi a b ^ 2 =
      finiteQuadraticChar k (-1) * psi (-b ^ 2 / a) * (Fintype.card k : ℂ) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  rw [quadraticSum_eq_gaussSum hchar hpsi ha b]
  calc
    (psi (-b ^ 2 / (2 * a)) * finiteQuadraticChar k (a / 2) *
        gaussSum (finiteQuadraticChar k) psi) ^ 2 =
        psi (-b ^ 2 / (2 * a)) ^ 2 *
          finiteQuadraticChar k (a / 2) ^ 2 *
            gaussSum (finiteQuadraticChar k) psi ^ 2 := by ring
    _ = psi (-b ^ 2 / (2 * a)) ^ 2 * 1 *
        (finiteQuadraticChar k (-1) * (Fintype.card k : ℂ)) := by
          rw [finiteQuadraticChar_sq k (div_ne_zero ha h2),
            gaussSum_sq (finiteQuadraticChar_ne_one k hchar)
              (finiteQuadraticChar_isQuadratic k) (AddChar.IsPrimitive.of_ne_one hpsi)]
    _ = finiteQuadraticChar k (-1) * psi (-b ^ 2 / a) *
        (Fintype.card k : ℂ) := by
          rw [pow_two, ← psi.map_add_eq_mul]
          have harg : -b ^ 2 / (2 * a) + -b ^ 2 / (2 * a) = -b ^ 2 / a := by
            field_simp
            ring
          rw [harg]
          ring

/-- Completing the square after phase normalization. -/
theorem quadraticPhase_completeSquare (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticPhase psi a b =
      psi (-b ^ 2 / (2 * a)) * quadraticPhase psi a 0 := by
  rw [quadraticPhase, quadraticPhase, quadraticSum_completeSquare hchar psi ha b]
  exact phase_mul_of_norm_eq_one (finiteAddChar_norm psi _)
    (quadraticSum_ne_zero hchar hpsi ha 0)

/-- Translation identity for normalized quadratic phases. -/
theorem quadraticPhase_translate (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b c : k) :
    quadraticPhase psi a (b + a * c) =
      psi (-(a / 2 * c ^ 2 + b * c)) * quadraticPhase psi a b := by
  rw [quadraticPhase, quadraticPhase, quadraticSum_translate hchar]
  exact phase_mul_of_norm_eq_one (finiteAddChar_norm psi _)
    (quadraticSum_ne_zero hchar hpsi ha b)

/-- The normalized completing-square identity in precisely the manuscript's order of factors. -/
theorem quadraticPhase_eq_basic (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticPhase psi a b =
      finiteQuadraticChar k a * psi (-b ^ 2 / (2 * a)) *
        quadraticPhase psi 1 0 := by
  rw [quadraticPhase, quadraticPhase, quadraticSum_eq_basic hchar hpsi ha b]
  apply phase_mul_of_norm_eq_one
  · rw [norm_mul, finiteQuadraticChar_norm k ha, finiteAddChar_norm, one_mul]
  · exact quadraticSum_ne_zero hchar hpsi one_ne_zero 0

/-- The basic normalized quadratic phase has the exact square `ν(-1)`. -/
theorem quadraticPhase_basic_sq (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) :
    quadraticPhase psi 1 0 ^ 2 = finiteQuadraticChar k (-1) := by
  rw [quadraticPhase, ← phase_pow, quadraticSum_sq hchar hpsi one_ne_zero 0]
  simp
  have hnu : finiteQuadraticChar k (-1) ≠ 0 := by
    intro hzero
    have hn := finiteQuadraticChar_norm k (neg_ne_zero.mpr one_ne_zero)
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hcard : (Fintype.card k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hphaseCard : phase (Fintype.card k : ℂ) = 1 := by
    rw [phase_of_ne_zero hcard, Complex.norm_natCast]
    exact div_self hcard
  rw [phase_mul]
  · rw [phase_of_norm_eq_one (finiteQuadraticChar_norm k (neg_ne_zero.mpr one_ne_zero)),
      hphaseCard, mul_one]
  · exact hnu
  · exact hcard

/-- Exact square of every normalized quadratic phase. -/
theorem quadraticPhase_sq (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) {a : k} (ha : a ≠ 0) (b : k) :
    quadraticPhase psi a b ^ 2 =
      finiteQuadraticChar k (-1) * psi (-b ^ 2 / a) := by
  rw [quadraticPhase, ← phase_pow, quadraticSum_sq hchar hpsi ha b]
  have hu : ‖finiteQuadraticChar k (-1) * psi (-b ^ 2 / a)‖ = 1 := by
    rw [norm_mul, finiteQuadraticChar_norm k (neg_ne_zero.mpr one_ne_zero),
      finiteAddChar_norm, one_mul]
  have hnu : finiteQuadraticChar k (-1) ≠ 0 := by
    intro hzero
    have hn := finiteQuadraticChar_norm k (neg_ne_zero.mpr one_ne_zero)
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hpsiValue : psi (-b ^ 2 / a) ≠ 0 := by
    intro hzero
    have hn := finiteAddChar_norm psi (-b ^ 2 / a)
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hcard : (Fintype.card k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hphaseCard : phase (Fintype.card k : ℂ) = 1 := by
    rw [phase_of_ne_zero hcard, Complex.norm_natCast]
    exact div_self hcard
  rw [phase_mul]
  · rw [phase_of_norm_eq_one hu, hphaseCard, mul_one]
  · exact mul_ne_zero hnu hpsiValue
  · exact hcard

end QuadraticSums

end LanglandsFirstMainLemma
