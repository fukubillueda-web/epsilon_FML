import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.FiniteField.QuadraticPhasePowers
import LanglandsFirstMainLemma.Basic.FiniteProducts

open scoped BigOperators

namespace LanglandsFirstMainLemma

section ScalarPhaseProducts

variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k] [CharP k p]

private theorem finiteQuadraticChar_map_mul_apply (x y : k) :
    finiteQuadraticChar k (x * y) =
      finiteQuadraticChar k x * finiteQuadraticChar k y :=
  (finiteQuadraticChar k).map_mul' x y

private theorem finiteQuadraticChar_map_pow_apply (x : k) (n : ℕ) :
    finiteQuadraticChar k (x ^ n) = finiteQuadraticChar k x ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact (finiteQuadraticChar k).map_one'
  | succ n ih =>
      rw [pow_succ, finiteQuadraticChar_map_mul_apply, ih, pow_succ]

omit [Fact p.Prime] in
/-- The three powers of the basic phase, with the residue characteristic written
as the explicit prime `p` used to index the wild orbit. -/
theorem wildOdd_basicPhasePowers (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) :
    quadraticPhase psi 1 0 ^ 2 = finiteQuadraticChar k (-1) ∧
      quadraticPhase psi 1 0 ^ (p - 1) = finiteQuadraticChar k (-1) ∧
      quadraticPhase psi 1 0 ^ p =
        quadraticPhase psi 1 0 * finiteQuadraticChar k (-1) := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  simpa only [ringChar.eq k p] using quadraticPhase_powers hchar hpsi

omit [Fact p.Prime] in
/-- Scaling both coefficients by a nonzero scalar retains the exact additive
translation.  In particular, the quadratic-character factor `ν(c)` must not be
dropped. -/
theorem wildOdd_quadraticPhase_scale (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {a c : k} (ha : a ≠ 0) (hc : c ≠ 0) (b : k) :
    quadraticPhase psi (c * a) (c * b) =
      finiteQuadraticChar k c * psi (-(c - 1) * b ^ 2 / (2 * a)) *
        quadraticPhase psi a b := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hca : c * a ≠ 0 := mul_ne_zero hc ha
  rw [quadraticPhase_eq_basic hchar hpsi hca,
    quadraticPhase_eq_basic hchar hpsi ha]
  rw [finiteQuadraticChar_map_mul_apply]
  have harg : -(c * b) ^ 2 / (2 * (c * a)) =
      -(c - 1) * b ^ 2 / (2 * a) + -b ^ 2 / (2 * a) := by
    field_simp
    ring
  rw [harg, psi.map_add_eq_mul]
  ring

omit [Fact p.Prime] in
/-- Product form of the quadratic-phase formula.  Every denominator condition
is recorded by `ha`; no degenerate quadratic coefficient is admitted. -/
theorem wildOdd_quadraticPhase_product (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {I : Type*} [Fintype I] (a b : I → k) (ha : ∀ i, a i ≠ 0) :
    (∏ i, quadraticPhase psi (a i) (b i)) =
      finiteQuadraticChar k (∏ i, a i) *
        psi (∑ i, -(b i) ^ 2 / (2 * a i)) *
          quadraticPhase psi 1 0 ^ Fintype.card I := by
  classical
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
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
            rw [hnu, hpsiSum, Finset.prod_const, Finset.card_univ]

/-- Repeating the same nondegenerate phase `p` times leaves the exact factor
`q₀ ν(-a)`.  The additive phase disappears because an additive-character value
has `p`-th power one, while the sign comes from `q₀ ^ p`. -/
theorem wildOdd_repeatedPhase (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {a : k} (ha : a ≠ 0) (gamma : k) :
    quadraticPhase psi a (a * gamma) ^ p =
      quadraticPhase psi 1 0 * finiteQuadraticChar k (-a) := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  let z : k := -(a * gamma) ^ 2 / (2 * a)
  have hpsiPow : psi z ^ p = 1 := by
    calc
      psi z ^ p = psi (p • z) := (AddChar.map_nsmul_eq_pow psi p z).symm
      _ = psi 0 := by rw [show p • z = 0 by simp [nsmul_eq_mul]]
      _ = 1 := AddChar.map_zero_eq_one psi
  have hnuSq : finiteQuadraticChar k a ^ 2 = 1 :=
    finiteQuadraticChar_sq k ha
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpOdd : p = 2 * m + 1 := by omega
  have hnuPow : finiteQuadraticChar k a ^ p = finiteQuadraticChar k a := by
    rw [hpOdd, pow_add, pow_mul, hnuSq, one_pow, pow_one, one_mul]
  have hqPow : quadraticPhase psi 1 0 ^ p =
      quadraticPhase psi 1 0 * finiteQuadraticChar k (-1) := by
    simpa only [ringChar.eq k p] using (quadraticPhase_powers hchar hpsi).2.2
  rw [quadraticPhase_eq_basic hchar hpsi ha, mul_pow, mul_pow,
    hnuPow, hpsiPow, mul_one, hqPow]
  rw [show -a = (-1) * a by ring, finiteQuadraticChar_map_mul_apply]
  ring

/-- The upper homogeneous coefficient has the same exact phase as
`q₀ ν(-a)`.  Nonvanishing of both `a` and `d` is explicit, and the even
exponent `p - 1` removes only the `ν(d)` factor, not `ν(-1)`. -/
theorem wildOdd_upperScalarPhase (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {a d : k} (ha : a ≠ 0) (hd : d ≠ 0) :
    quadraticPhase psi (-a * d ^ (p - 1)) 0 =
      quadraticPhase psi 1 0 * finiteQuadraticChar k (-a) := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hcoeff : -a * d ^ (p - 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr ha) (pow_ne_zero _ hd)
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpEven : p - 1 = 2 * m := by omega
  have hnuDPow : finiteQuadraticChar k (d ^ (p - 1)) = 1 := by
    rw [finiteQuadraticChar_map_pow_apply, hpEven, pow_mul,
      finiteQuadraticChar_sq k hd, one_pow]
  rw [quadraticPhase_eq_basic hchar hpsi hcoeff]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_div,
    AddChar.map_zero_eq_one, mul_one]
  rw [finiteQuadraticChar_map_mul_apply, hnuDPow, mul_one]
  ring

/-- Exact nonboundary identity `T^p = U` above the break. -/
theorem wildOdd_repeatedPhase_eq_upperScalar (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {a d : k} (ha : a ≠ 0) (hd : d ≠ 0) (gamma : k) :
    quadraticPhase psi a (a * gamma) ^ p =
      quadraticPhase psi (-a * d ^ (p - 1)) 0 := by
  rw [wildOdd_repeatedPhase hp2 hpsi ha gamma,
    wildOdd_upperScalarPhase hp2 hpsi ha hd]

/-- Exact repeated-phase product over all of the prime field.  In contrast to
`wildOdd_scalarPencil`, this index is `ZMod p`, so its zero element is included
and the constant phase occurs exactly `p` times. -/
theorem wildOdd_repeatedPhase_primeFieldProduct (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {a d : k} (ha : a ≠ 0) (hd : d ≠ 0) (gamma : k) :
    (∏ _j : ZMod p, quadraticPhase psi a (a * gamma)) =
      quadraticPhase psi (-a * d ^ (p - 1)) 0 := by
  classical
  rw [Finset.prod_const, Finset.card_univ, ZMod.card,
    wildOdd_repeatedPhase_eq_upperScalar hp2 hpsi ha hd gamma]

/-- The product of the nonzero prime-field scalar phases is exactly one.
The index type is `(ZMod p)ˣ`, so the zero scalar is genuinely omitted.
The two surviving factors `q₀^(p-1)` and `ν(-1)` are both retained before
their final cancellation. -/
theorem wildOdd_scalarPencil (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    (omega : (ZMod p)ˣ →* kˣ) (homega : Function.Injective omega)
    {a : k} (ha : a ≠ 0) (gamma : k) :
    (∏ j : (ZMod p)ˣ,
      quadraticPhase psi (a * (omega j : k))
        (a * (omega j : k) * gamma)) = 1 := by
  classical
  let q0 := quadraticPhase psi 1 0
  let nu := finiteQuadraticChar k
  have hpPrime : p.Prime := Fact.out
  have hpGt : 2 < p := lt_of_le_of_ne hpPrime.two_le hp2.symm
  have hsum : (∑ j : (ZMod p)ˣ, (omega j : k)) = 0 := by
    have hnot : ¬p - 1 ∣ 1 := by
      intro hdiv
      have hle : p - 1 ≤ 1 := Nat.le_of_dvd (by omega) hdiv
      omega
    simpa only [pow_one, if_neg hnot] using sum_primeField p 1 omega homega
  have hprod : (∏ j : (ZMod p)ˣ, (omega j : k)) = -1 :=
    prod_primeField p hp2 omega homega
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    simp [Fintype.card_units, ZMod.card]
  have hcoeff (j : (ZMod p)ˣ) : a * (omega j : k) ≠ 0 :=
    mul_ne_zero ha (Units.ne_zero (omega j))
  have harg :
      (∑ j : (ZMod p)ˣ,
        -(a * (omega j : k) * gamma) ^ 2 /
          (2 * (a * (omega j : k)))) = 0 := by
    calc
      (∑ j : (ZMod p)ˣ,
        -(a * (omega j : k) * gamma) ^ 2 /
          (2 * (a * (omega j : k)))) =
          ∑ j : (ZMod p)ˣ, (-(a * gamma ^ 2) / 2) * (omega j : k) := by
            apply Finset.sum_congr rfl
            intro j _
            field_simp [ha, Units.ne_zero (omega j)]
      _ = (-(a * gamma ^ 2) / 2) * ∑ j : (ZMod p)ˣ, (omega j : k) := by
        rw [Finset.mul_sum]
      _ = 0 := by rw [hsum, mul_zero]
  have hcoeffProd :
      (∏ j : (ZMod p)ˣ, a * (omega j : k)) = a ^ (p - 1) * (-1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      hcard, hprod]
  obtain ⟨m, hm⟩ := hpPrime.odd_of_ne_two hp2
  have hpEven : p - 1 = 2 * m := by omega
  have hnuAPow : nu a ^ (p - 1) = 1 := by
    rw [hpEven, pow_mul, finiteQuadraticChar_sq k ha, one_pow]
  have hnuCoeff :
      nu (∏ j : (ZMod p)ˣ, a * (omega j : k)) = nu (-1) := by
    rw [hcoeffProd]
    change finiteQuadraticChar k (a ^ (p - 1) * (-1)) =
      finiteQuadraticChar k (-1)
    rw [finiteQuadraticChar_map_mul_apply, finiteQuadraticChar_map_pow_apply]
    change nu a ^ (p - 1) * nu (-1) = nu (-1)
    rw [hnuAPow, one_mul]
  have hqPred : q0 ^ (p - 1) = nu (-1) := by
    simpa only [q0, nu] using (wildOdd_basicPhasePowers hp2 hpsi).2.1
  have hnuNegSq : nu (-1) ^ 2 = 1 :=
    finiteQuadraticChar_sq k (neg_ne_zero.mpr one_ne_zero)
  rw [wildOdd_quadraticPhase_product hp2 hpsi
    (fun j : (ZMod p)ˣ => a * (omega j : k))
    (fun j : (ZMod p)ˣ => a * (omega j : k) * gamma) hcoeff]
  rw [harg, hnuCoeff]
  simp only [AddChar.map_zero_eq_one, mul_one, hcard, nu]
  rw [hqPred]
  simpa [pow_two] using hnuNegSq

end ScalarPhaseProducts

end LanglandsFirstMainLemma
