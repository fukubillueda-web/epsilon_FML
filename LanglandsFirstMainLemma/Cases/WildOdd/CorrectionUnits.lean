import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.Basic.FiniteProducts

/-!
# Correction units in the wild odd-prime calculation

The prime-field indices in this file are lifted to the local field by the canonical
Teichmüller section.  In particular, they are not ordinary natural-number casts in mixed
characteristic.  The exceptional index zero is kept separate throughout: its correction is
built from the corrected dual element `uᵛ`, whereas the nonzero corrections are indexed by
`(ZMod p)ˣ`.

The hypotheses bundled by `WildOddCorrectionData` are exactly the input used in Lemmas
`lem:parameter-ratios` and `lem:correction-depth`: the odd residue characteristic, the
nonstable conductor interval, the norm/valuation normalization of `u`, the wild trace bound,
and the boundary noncancellation supplied by minimality of the conductor orbit.
-/

open scoped BigOperators
open Finset
open Polynomial

namespace LanglandsFirstMainLemma

noncomputable section

section PrimeFieldLifts

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩

/-- The canonical Teichmüller representative in `F` of an element of its prime residue
field.  The source is `ZMod (residueCharacteristic F)`, not a natural-number cast into `F`. -/
noncomputable def wildOddPrimeFieldLift
    (j : ZMod (residueCharacteristic F)) : F :=
  ((teichmuller F
      (ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F) j) :
        ringOfIntegers F) : F)

@[simp]
theorem wildOddPrimeFieldLift_zero :
    wildOddPrimeFieldLift F 0 = 0 := by
  simp [wildOddPrimeFieldLift]

@[simp]
theorem wildOddPrimeFieldLift_one :
    wildOddPrimeFieldLift F 1 = 1 := by
  simp [wildOddPrimeFieldLift]

@[simp]
theorem wildOddPrimeFieldLift_mul (i j : ZMod (residueCharacteristic F)) :
    wildOddPrimeFieldLift F (i * j) =
      wildOddPrimeFieldLift F i * wildOddPrimeFieldLift F j := by
  simp [wildOddPrimeFieldLift]

/-- Prime-field Teichmüller representatives satisfy the literal `p`-power identity. -/
@[simp]
theorem wildOddPrimeFieldLift_pow (j : ZMod (residueCharacteristic F)) :
    wildOddPrimeFieldLift F j ^ residueCharacteristic F =
      wildOddPrimeFieldLift F j := by
  let p := residueCharacteristic F
  let ι := ZMod.castHom (dvd_refl p) (ResidueField F)
  have hj : (ι j) ^ p = ι j := by
    rw [← map_pow]
    congr 1
    exact ZMod.pow_card j
  change (((teichmuller F (ι j)) ^ p : ringOfIntegers F) : F) =
    ((teichmuller F (ι j) : ringOfIntegers F) : F)
  exact congrArg (fun x : ringOfIntegers F ↦ (x : F)) <|
    (map_pow (teichmuller F) (ι j) p).symm.trans (congrArg (teichmuller F) hj)

/-- The canonical prime-field Teichmüller realization is injective. -/
theorem wildOddPrimeFieldLift_injective :
    Function.Injective (wildOddPrimeFieldLift F) := by
  intro i j hij
  have ht : teichmuller F
      (ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F) i) =
      teichmuller F
        (ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F) j) :=
    Subtype.ext hij
  have hc := teichmuller_injective F ht
  exact (ZMod.castHom (dvd_refl (residueCharacteristic F))
    (ResidueField F)).injective hc

theorem wildOddPrimeFieldLift_ne_zero
    (j : (ZMod (residueCharacteristic F))ˣ) :
    wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) ≠ 0 := by
  intro hj
  have : (j : ZMod (residueCharacteristic F)) = 0 :=
    wildOddPrimeFieldLift_injective F (hj.trans (wildOddPrimeFieldLift_zero F).symm)
  exact Units.ne_zero j this

/-- Nonzero prime-field Teichmüller representatives as canonical local units. -/
noncomputable def wildOddPrimeFieldLocalUnits :
    (ZMod (residueCharacteristic F))ˣ →* unitGroup F :=
  (unitGroupMulEquivRingOfIntegers F).symm.toMonoidHom.comp <|
    (teichmullerUnits F).comp <|
      Units.map
        (ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F))

/-- The same representatives in the ambient unit group `Fˣ`. -/
noncomputable def wildOddPrimeFieldUnits :
    (ZMod (residueCharacteristic F))ˣ →* Fˣ :=
  (unitGroup F).subtype.comp (wildOddPrimeFieldLocalUnits F)

@[simp]
theorem coe_wildOddPrimeFieldUnits
    (j : (ZMod (residueCharacteristic F))ˣ) :
    (wildOddPrimeFieldUnits F j : F) =
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) := rfl

theorem wildOddPrimeFieldUnits_injective :
    Function.Injective (wildOddPrimeFieldUnits F) := by
  intro i j hij
  apply Units.ext
  apply wildOddPrimeFieldLift_injective F
  exact congrArg ((↑) : Fˣ → F) hij

/-- Every nonzero prime-field Teichmüller representative has valuation zero. -/
theorem ord_wildOddPrimeFieldLift
    (j : (ZMod (residueCharacteristic F))ˣ) :
    ord F (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F))) = 0 := by
  let u : unitGroup F := wildOddPrimeFieldLocalUnits F j
  exact (mem_unitGroup_iff_ord_eq_zero F (u : Fˣ)).1 u.property

/-- Compatibility between the unit-indexed realization and the full prime-field indexing. -/
@[simp]
theorem wildOddPrimeFieldLift_units_coe
    (j : (ZMod (residueCharacteristic F))ˣ) :
    wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) =
      (wildOddPrimeFieldUnits F j : F) := rfl

/-- The integer representative used in the exponent `τ^j`.  It is kept
separate from the Teichmüller representative used in field-valued formulas. -/
def wildOddPrimeFieldNatRepresentative
    (j : ZMod (residueCharacteristic F)) : ℕ := j.val

/-- Exact reduction compatibility between the integer representative and the
Teichmüller representative.  This is a congruence at depth one, not a literal
identity in a mixed-characteristic field. -/
theorem wildOddPrimeFieldLift_sub_natCast_mem_lattice_one
    (j : ZMod (residueCharacteristic F)) :
    wildOddPrimeFieldLift F j -
        (wildOddPrimeFieldNatRepresentative F j : F) ∈ lattice F 1 := by
  let ι := ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F)
  change ((teichmuller F (ι j) : ringOfIntegers F) : F) -
      (((j.val : ringOfIntegers F) : F)) ∈ lattice F 1
  apply (residueMap_eq_residueMap_iff F
    (teichmuller F (ι j)) (j.val : ringOfIntegers F)).1
  rw [residueMap_teichmuller]
  have hj : ι j = (j.val : ResidueField F) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hj, map_natCast]

/-- The exact mixed-characteristic factorization for the canonical prime-field
Teichmüller representatives.  Oddness is what changes the roots from `[j]` to `-[j]`
without changing `X ^ p - X`. -/
theorem wildOddPrimeFieldPolynomial
    (hodd : residueCharacteristic F ≠ 2) :
    (∏ j : ZMod (residueCharacteristic F),
      (X + C (wildOddPrimeFieldLift F j) : F[X])) =
        X ^ residueCharacteristic F - X := by
  classical
  let p := residueCharacteristic F
  let f : ZMod p → F := fun j ↦ -wildOddPrimeFieldLift F j
  let P : F[X] := X ^ p - X
  let Q : F[X] := ∏ j : ZMod p, (X - C (f j))
  have hp : p.Prime := residueCharacteristic_prime F
  have hpodd : Odd p := hp.odd_of_ne_two hodd
  have hf : Function.Injective f := by
    intro i j hij
    apply wildOddPrimeFieldLift_injective F
    exact neg_injective hij
  have hroot (j : ZMod p) : IsRoot P (f j) := by
    simp only [IsRoot, P, eval_sub, eval_pow, eval_X]
    change (-wildOddPrimeFieldLift F j) ^ p - (-wildOddPrimeFieldLift F j) = 0
    rw [hpodd.neg_pow, wildOddPrimeFieldLift_pow]
    ring
  have hQdvdP : Q ∣ P := by
    apply Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hf)
    intro j
    exact dvd_iff_isRoot.mpr (hroot j)
  have hQmonic : Q.Monic := by
    simpa only [Q] using
      (monic_prod_of_monic (Finset.univ : Finset (ZMod p))
        (fun j ↦ X - C (f j)) (fun j _ ↦ monic_X_sub_C (f j)))
  have hPmonic : P.Monic := by
    change (X ^ p - X : F[X]).Monic
    exact monic_X_pow_sub (by simpa using hp.one_lt)
  have hPdegree : P.natDegree = p := by
    simpa only [P] using FiniteField.X_pow_card_sub_X_natDegree_eq F hp.one_lt
  have hQdegree : Q.natDegree = p := by
    change (∏ j : ZMod p, (X - C (f j) : F[X])).natDegree = p
    rw [show (∏ j : ZMod p, (X - C (f j) : F[X])) =
      ∏ j ∈ (Finset.univ : Finset (ZMod p)), (X - C (f j)) by simp]
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, ZMod.card]
  have hPQ : P = Q :=
    eq_of_monic_of_dvd_of_natDegree_le hQmonic hPmonic hQdvdP
      (by rw [hPdegree, hQdegree])
  calc
    (∏ j : ZMod p, (X + C (wildOddPrimeFieldLift F j) : F[X])) = Q := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [f, C_neg, sub_neg_eq_add]
    _ = P := hPQ.symm

/-- Evaluation of `wildOddPrimeFieldPolynomial`: the exact identity
`∏_j (x + [j]) = x^p - x` used by the exceptional correction. -/
theorem prod_add_wildOddPrimeFieldLift
    (hodd : residueCharacteristic F ≠ 2) (x : F) :
    (∏ j : ZMod (residueCharacteristic F),
      (x + wildOddPrimeFieldLift F j)) =
        x ^ residueCharacteristic F - x := by
  have h := congrArg (Polynomial.eval x) (wildOddPrimeFieldPolynomial F hodd)
  simpa [Polynomial.eval_prod] using h

end PrimeFieldLifts

/-- The signed conductor offset `a = T - m`. -/
def wildOddCorrectionOffset (T m : ℕ) : ℤ := (T : ℤ) - (m : ℤ)

/-- The manuscript depth `R(c) = ⌊(c + (p-1)T)/p⌋`. -/
def wildOddCorrectionDepth (p T c : ℕ) : ℕ :=
  (c + (p - 1) * T) / p

/-- The normalized norm quotient `Z(w) = N(1+w)/(1+N(w))` used for both
families of correction units. -/
noncomputable def wildOddNormalizedNorm
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] (w : K) : F :=
  norm F K (1 + w) / (1 + norm F K w)

/-- The natural-number depth is the manuscript's integer floor. -/
theorem wildOddCorrectionDepth_cast (p T c : ℕ) :
    (wildOddCorrectionDepth p T c : ℤ) =
      ((c : ℤ) + (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) := by
  simp [wildOddCorrectionDepth]

section Data

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

/-- Input data for the wild odd-prime correction calculation.

The boundary field is the residue-level noncancellation consequence of minimality, expressed
at field level: when `a = 0`, every `n + [j]` has valuation zero.  Away from the boundary the
same denominator facts are derived from unequal valuations. -/
structure WildOddCorrectionData (T : ℕ) where
  /-- Conductor `m = m_F(χ_F)` in the nonstable interval. -/
  m : ℕ
  /-- The initial correction element `u`. -/
  u : K
  odd_residueCharacteristic : residueCharacteristic F ≠ 2
  two_le_T : 2 ≤ T
  two_le_m : 2 ≤ m
  m_le : m ≤ 2 * T - 1
  degree_eq : Module.finrank F K = residueCharacteristic F
  residueDegree_eq_one : residueDegree F K = 1
  traceLowerBound : TraceIdealLowerBound F K (residueCharacteristic F)
    ((((residueCharacteristic F - 1) * T : ℕ) : ℤ))
  ord_u : ord K u = ((wildOddCorrectionOffset T m : ℤ) : WithTop ℤ)
  boundary_noncancellation : wildOddCorrectionOffset T m = 0 →
    ∀ j : ZMod (residueCharacteristic F),
      ord F (norm F K u + wildOddPrimeFieldLift F j) = 0

namespace WildOddCorrectionData

variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  {T : ℕ} (d : WildOddCorrectionData F K T)

local instance : Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩

/-- The offset `a = T-m` attached to the data. -/
abbrev a : ℤ := wildOddCorrectionOffset T d.m

/-- The initial norm parameter `n = N(u)`. -/
noncomputable def n : F := norm F K d.u

/-- The corrected dual element `uᵛ = -n/u`. -/
noncomputable def dual : K := -(algebraMap F K d.n) / d.u

/-- The exceptional denominator `1 + N(uᵛ)`. -/
noncomputable def zeroDenominator : F := 1 + norm F K d.dual

/-- The nonzero-index denominator `n + [j]`. -/
noncomputable def denominator
    (j : (ZMod (residueCharacteristic F))ˣ) : F :=
  d.n + wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F))

/-- The exceptional correction value before bundling it as a unit. -/
noncomputable def zZeroValue : F :=
  norm F K (1 + d.dual) / d.zeroDenominator

/-- The correction value at a nonzero prime-field index. -/
noncomputable def zValue
    (j : (ZMod (residueCharacteristic F))ˣ) : F :=
  norm F K (d.u + algebraMap F K
    (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) /
      d.denominator j

theorem u_ne_zero : d.u ≠ 0 := by
  exact (ord_ne_top_iff K).mp (d.ord_u.trans_ne (WithTop.coe_ne_top :
    ((d.a : ℤ) : WithTop ℤ) ≠ ⊤))

theorem n_ne_zero : d.n ≠ 0 := by
  rw [n, norm_apply]
  exact Algebra.norm_ne_zero_iff.mpr d.u_ne_zero

/-- Exact valuation of the norm parameter. -/
theorem ord_n : ord F d.n = ((d.a : ℤ) : WithTop ℤ) := by
  rw [n, ord_norm, d.residueDegree_eq_one, one_nsmul, d.ord_u]

theorem dual_ne_zero : d.dual ≠ 0 := by
  rw [dual]
  have hnK : algebraMap F K d.n ≠ 0 := by
    intro h
    apply d.n_ne_zero
    exact (algebraMap F K).injective (by simpa using h)
  exact div_ne_zero (neg_ne_zero.mpr hnK) d.u_ne_zero

/-- Exact valuation of the corrected dual element. -/
theorem ord_dual :
    ord K d.dual = ((((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
      WithTop ℤ) := by
  have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
  rw [d.degree_eq, d.residueDegree_eq_one, mul_one] at hdeg
  have hram : ramificationIndex F K = residueCharacteristic F := hdeg.symm
  rw [dual, ord_div, ord_neg, ord_algebraMap, hram, d.ord_n, d.ord_u]
  rw [← WithTop.coe_nsmul]
  simp only [nsmul_eq_mul]
  norm_cast
  rw [Nat.cast_sub (residueCharacteristic_prime F).one_le]
  ring

/-- Norm of a negative element in the odd-degree extension. -/
theorem norm_neg (d' : WildOddCorrectionData F K T) (x : K) :
    norm F K (-x) = -norm F K x := by
  let p := residueCharacteristic F
  have hpodd : Odd p := (residueCharacteristic_prime F).odd_of_ne_two
    d'.odd_residueCharacteristic
  rw [show -x = algebraMap F K (-1) * x by simp, map_mul, norm_algebraMap,
    d'.degree_eq, hpodd.neg_one_pow, neg_one_mul]

/-- Exact compatibility of the field norm with division. -/
theorem norm_div (x y : K) :
    norm F K (x / y) = norm F K x / norm F K y := by
  rw [div_eq_mul_inv, map_mul, norm_apply, Algebra.norm_inv, div_eq_mul_inv]

/-- The corrected dual has the manuscript's exact norm, including its sign. -/
theorem norm_dual :
    norm F K d.dual = -d.n ^ (residueCharacteristic F - 1) := by
  let p := residueCharacteristic F
  have hp : p.Prime := residueCharacteristic_prime F
  have hpodd : Odd p := hp.odd_of_ne_two d.odd_residueCharacteristic
  rw [dual, norm_div (F := F) (K := K), show -(algebraMap F K d.n) =
    algebraMap F K (-d.n) by simp, norm_algebraMap, d.degree_eq,
    hpodd.neg_pow]
  change -(d.n ^ p) / d.n = -d.n ^ (p - 1)
  field_simp [d.n_ne_zero]
  rw [mul_comm d.n, pow_sub_one_mul hp.pos.ne']

@[simp]
theorem zeroDenominator_eq :
    d.zeroDenominator = 1 - d.n ^ (residueCharacteristic F - 1) := by
  rw [zeroDenominator, d.norm_dual]
  ring

/-- Every nonzero-index denominator is nonzero; cancellation is not used in this proof. -/
theorem denominator_ne_zero
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.denominator j ≠ 0 := by
  by_cases ha : d.a = 0
  · have h := d.boundary_noncancellation ha
      (j : ZMod (residueCharacteristic F))
    apply (ord_ne_top_iff F).mp
    have hne : ord F (norm F K d.u +
        wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F))) ≠ ⊤ := by
      rw [h]
      exact WithTop.zero_ne_top
    simpa only [denominator, n] using hne
  · have hordNe : ord F d.n ≠
        ord F (wildOddPrimeFieldLift F
          (j : ZMod (residueCharacteristic F))) := by
      rw [d.ord_n, ord_wildOddPrimeFieldLift]
      simpa using ha
    have hord : ord F (d.denominator j) =
        min (ord F d.n)
          (ord F (wildOddPrimeFieldLift F
            (j : ZMod (residueCharacteristic F)))) := by
      exact ord_add_eq_min F hordNe
    apply (ord_ne_top_iff F).mp
    rw [hord, d.ord_n, ord_wildOddPrimeFieldLift]
    simp

/-- The exceptional denominator is nonzero, with the boundary case deduced from the exact
Teichmüller product rather than assumed. -/
theorem zeroDenominator_ne_zero : d.zeroDenominator ≠ 0 := by
  rw [d.zeroDenominator_eq]
  by_cases ha : d.a = 0
  · have hfac : ∀ j : ZMod (residueCharacteristic F),
        d.n + wildOddPrimeFieldLift F j ≠ 0 := by
      intro j
      apply (ord_ne_top_iff F).mp
      have h := d.boundary_noncancellation ha j
      have hne : ord F (norm F K d.u + wildOddPrimeFieldLift F j) ≠ ⊤ := by
        rw [h]
        exact WithTop.zero_ne_top
      simpa only [n] using hne
    have hprod : (∏ j : ZMod (residueCharacteristic F),
        (d.n + wildOddPrimeFieldLift F j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hfac j)
    rw [prod_add_wildOddPrimeFieldLift F d.odd_residueCharacteristic d.n] at hprod
    intro hzero
    apply hprod
    have hpow : d.n ^ (residueCharacteristic F - 1) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    rw [← pow_sub_one_mul (residueCharacteristic_prime F).pos.ne' d.n, hpow]
    ring
  · have hp1 : 1 ≤ residueCharacteristic F :=
      (residueCharacteristic_prime F).one_le
    have hpowOrd : ord F (d.n ^ (residueCharacteristic F - 1)) =
        ((((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
          WithTop ℤ) := by
      rw [ord_pow, d.ord_n, ← WithTop.coe_nsmul]
      congr 1
    have hcoeff : ((residueCharacteristic F - 1 : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt (residueCharacteristic_prime F).one_lt).ne'
    have hordNe : ord F (1 : F) ≠
        ord F (d.n ^ (residueCharacteristic F - 1)) := by
      rw [ord_one, hpowOrd]
      exact fun h ↦ mul_ne_zero hcoeff ha (WithTop.coe_eq_coe.mp h.symm)
    have hord : ord F ((1 : F) + -(d.n ^ (residueCharacteristic F - 1))) =
        min (ord F (1 : F))
          (ord F (-(d.n ^ (residueCharacteristic F - 1)))) :=
      ord_add_eq_min F (by simpa only [ord_neg] using hordNe)
    apply (ord_ne_top_iff F).mp
    simpa only [sub_eq_add_neg, hord, ord_one, ord_neg, hpowOrd]
      using ne_of_lt ((min_le_left
        (0 : WithTop ℤ)
        ((((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a : ℤ) :
          WithTop ℤ)).trans_lt (WithTop.coe_lt_top (0 : ℤ)))

/-- Literal nonvanishing of the exceptional displayed denominator. -/
theorem one_sub_n_pow_ne_zero :
    1 - d.n ^ (residueCharacteristic F - 1) ≠ 0 := by
  rw [← d.zeroDenominator_eq]
  exact d.zeroDenominator_ne_zero

/-- The numerator at a nonzero index is nonzero. -/
theorem nonzeroNumerator_ne_zero
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.u + algebraMap F K
      (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F))) ≠ 0 := by
  intro hzero
  have hu : d.u = -algebraMap F K
      (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F))) :=
    eq_neg_of_add_eq_zero_left hzero
  apply d.denominator_ne_zero j
  rw [denominator, n, hu, norm_neg d, norm_algebraMap, d.degree_eq,
    wildOddPrimeFieldLift_pow]
  ring

/-- The exceptional numerator is nonzero. -/
theorem zeroNumerator_ne_zero : 1 + d.dual ≠ 0 := by
  intro hzero
  have hdual : d.dual = -1 := eq_neg_of_add_eq_zero_right hzero
  apply d.zeroDenominator_ne_zero
  rw [zeroDenominator, hdual, norm_neg d, map_one]
  ring

theorem zValue_ne_zero
    (j : (ZMod (residueCharacteristic F))ˣ) : d.zValue j ≠ 0 := by
  rw [zValue]
  exact div_ne_zero
    (Algebra.norm_ne_zero_iff.mpr (d.nonzeroNumerator_ne_zero j))
    (d.denominator_ne_zero j)

theorem zZeroValue_ne_zero : d.zZeroValue ≠ 0 := by
  rw [zZeroValue]
  exact div_ne_zero (Algebra.norm_ne_zero_iff.mpr d.zeroNumerator_ne_zero)
    d.zeroDenominator_ne_zero

/-- The exceptional correction as a genuine field unit. -/
noncomputable def zZero : Fˣ := Units.mk0 d.zZeroValue d.zZeroValue_ne_zero

/-- The nonzero prime-field-indexed corrections as genuine field units. -/
noncomputable def z
    (j : (ZMod (residueCharacteristic F))ˣ) : Fˣ :=
  Units.mk0 (d.zValue j) (d.zValue_ne_zero j)

@[simp]
theorem coe_zZero : (d.zZero : F) = d.zZeroValue := rfl

@[simp]
theorem coe_z (j : (ZMod (residueCharacteristic F))ˣ) :
    (d.z j : F) = d.zValue j := rfl

/-- Displacement of the exceptional correction unit. -/
noncomputable def xZero : F := (d.zZero : F) - 1

/-- Displacement of a nonzero-index correction unit. -/
noncomputable def x (j : (ZMod (residueCharacteristic F))ˣ) : F :=
  (d.z j : F) - 1

@[simp]
theorem xZero_eq : d.xZero = d.zZeroValue - 1 := rfl

@[simp]
theorem x_eq (j : (ZMod (residueCharacteristic F))ˣ) :
    d.x j = d.zValue j - 1 := rfl

/-- The full prime-field product occurring in the exceptional ratio. -/
noncomputable def primeFieldProduct : F :=
  ∏ j : ZMod (residueCharacteristic F),
    (d.n + wildOddPrimeFieldLift F j)

/-- The same product after separating the exceptional zero index. -/
noncomputable def nonzeroPrimeFieldProduct : F :=
  ∏ j : (ZMod (residueCharacteristic F))ˣ,
    (d.n + wildOddPrimeFieldLift F
      (j : ZMod (residueCharacteristic F)))

/-- Exact compatibility of the full indexing with the unit-indexed nonzero prime field. -/
theorem primeFieldProduct_reindex :
    d.primeFieldProduct = d.n * d.nonzeroPrimeFieldProduct := by
  classical
  rw [primeFieldProduct, nonzeroPrimeFieldProduct,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun j : ZMod (residueCharacteristic F) ↦
        d.n + wildOddPrimeFieldLift F j) 0]
  rw [wildOddPrimeFieldLift_zero, add_zero]
  congr 1
  exact (Equiv.prod_comp unitsEquivNeZero
    (fun j : {j : ZMod (residueCharacteristic F) // j ≠ 0} ↦
      d.n + wildOddPrimeFieldLift F
        (j : ZMod (residueCharacteristic F)))).symm

/-- Exact evaluation of the full Teichmüller product. -/
theorem primeFieldProduct_eq :
    d.primeFieldProduct =
      d.n ^ residueCharacteristic F - d.n := by
  exact prod_add_wildOddPrimeFieldLift F d.odd_residueCharacteristic d.n

/-- The initial norm parameter is definitionally the norm of `u`. -/
@[simp]
theorem norm_u : norm F K d.u = d.n := rfl

/-- Exact exceptional numerator identity, before any cancellation. -/
theorem norm_one_add_dual :
    norm F K (1 + d.dual) =
      -norm F K (algebraMap F K d.n - d.u) / d.n := by
  have hone : 1 + d.dual =
      -(algebraMap F K d.n - d.u) / d.u := by
    rw [dual]
    field_simp [d.u_ne_zero]
    ring
  rw [hone, norm_div (F := F) (K := K), norm_neg d, d.norm_u]

/-- First parameter-ratio identity, in the manuscript's norm-equals-denominator-times-unit
direction. -/
theorem norm_add_eq_denominator_mul
    (j : (ZMod (residueCharacteristic F))ˣ) :
    norm F K (d.u + algebraMap F K
      (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) =
        d.denominator j * (d.z j : F) := by
  rw [coe_z, zValue]
  exact (mul_div_cancel₀ _ (d.denominator_ne_zero j)).symm

/-- The full Teichmüller product is nonzero. -/
theorem primeFieldProduct_ne_zero : d.primeFieldProduct ≠ 0 := by
  rw [d.primeFieldProduct_eq]
  let p := residueCharacteristic F
  have hp : p.Prime := residueCharacteristic_prime F
  have hpow : d.n ^ (residueCharacteristic F - 1) - 1 ≠ 0 := by
    intro h
    apply d.zeroDenominator_ne_zero
    rw [d.zeroDenominator_eq]
    simpa only [neg_sub, neg_zero] using congrArg Neg.neg h
  rw [show d.n ^ p - d.n = (d.n ^ (p - 1) - 1) * d.n by
    rw [← pow_sub_one_mul hp.pos.ne' d.n]
    ring]
  simpa only [sub_mul, one_mul] using mul_ne_zero hpow d.n_ne_zero

/-- Second parameter-ratio identity, with the exact manuscript orientation. -/
theorem norm_sub_eq_primeFieldProduct_mul :
    norm F K (algebraMap F K d.n - d.u) =
      d.primeFieldProduct * (d.zZero : F) := by
  rw [coe_zZero, zZeroValue, d.norm_one_add_dual,
    d.zeroDenominator_eq, d.primeFieldProduct_eq]
  have hden : 1 - d.n ^ (residueCharacteristic F - 1) ≠ 0 := by
    simpa only [d.zeroDenominator_eq] using d.zeroDenominator_ne_zero
  rw [show d.n ^ residueCharacteristic F - d.n =
      -d.n * (1 - d.n ^ (residueCharacteristic F - 1)) by
    rw [← pow_sub_one_mul (residueCharacteristic_prime F).pos.ne' d.n]
    ring]
  field_simp [d.n_ne_zero, hden]

theorem norm_sub_ne_zero :
    norm F K (algebraMap F K d.n - d.u) ≠ 0 := by
  rw [d.norm_sub_eq_primeFieldProduct_mul]
  exact mul_ne_zero d.primeFieldProduct_ne_zero (Units.ne_zero d.zZero)

/-- Formula-facing exceptional ratio, proved only after both denominators are known nonzero. -/
theorem primeFieldProduct_div_norm_sub :
    d.primeFieldProduct / norm F K (algebraMap F K d.n - d.u) =
      ((d.zZero : F))⁻¹ := by
  rw [d.norm_sub_eq_primeFieldProduct_mul]
  rw [div_eq_mul_inv, mul_inv_rev]
  calc
    d.primeFieldProduct *
        (((d.zZero : F))⁻¹ * d.primeFieldProduct⁻¹) =
      ((d.zZero : F))⁻¹ *
        (d.primeFieldProduct * d.primeFieldProduct⁻¹) := by ring
    _ = ((d.zZero : F))⁻¹ := by
      rw [mul_inv_cancel₀ d.primeFieldProduct_ne_zero, mul_one]

/-- Norm after dividing the `j`-th numerator by its Teichmüller index. -/
theorem norm_scaled_add
    (j : (ZMod (residueCharacteristic F))ˣ) :
    norm F K ((d.u + algebraMap F K
      (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) /
        algebraMap F K
          (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) =
      norm F K (d.u + algebraMap F K
        (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) /
          wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) := by
  rw [norm_div (F := F) (K := K), norm_algebraMap, d.degree_eq,
    wildOddPrimeFieldLift_pow]

/-- Formula-facing nonzero-index ratio, with the norm and inverse correction in their exact
directions. -/
theorem denominator_div_index
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.denominator j /
        wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) =
      norm F K ((d.u + algebraMap F K
        (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) /
          algebraMap F K
            (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) *
        ((d.z j : F))⁻¹ := by
  rw [d.norm_scaled_add j, d.norm_add_eq_denominator_mul j]
  symm
  calc
    (d.denominator j * (d.z j : F)) /
          wildOddPrimeFieldLift F
            (j : ZMod (residueCharacteristic F)) * ((d.z j : F))⁻¹ =
        (d.denominator j /
          wildOddPrimeFieldLift F
            (j : ZMod (residueCharacteristic F))) *
            ((d.z j : F) * ((d.z j : F))⁻¹) := by ring
    _ = d.denominator j /
        (wildOddPrimeFieldLift F
          (j : ZMod (residueCharacteristic F))) := by
      rw [mul_inv_cancel₀ (Units.ne_zero (d.z j)), mul_one]

/-- The norm of a prime-field Teichmüller lift is literally that lift. -/
theorem norm_primeFieldLift
    (d' : WildOddCorrectionData F K T)
    (j : ZMod (residueCharacteristic F)) :
    norm F K (algebraMap F K (wildOddPrimeFieldLift F j)) =
      wildOddPrimeFieldLift F j := by
  rw [norm_algebraMap, d'.degree_eq, wildOddPrimeFieldLift_pow]

/-- Normalized norm is unchanged by inversion. -/
theorem normalizedNorm_inv (w : K) (hw : w ≠ 0) :
    wildOddNormalizedNorm F K w⁻¹ = wildOddNormalizedNorm F K w := by
  have hn : norm F K w ≠ 0 := Algebra.norm_ne_zero_iff.mpr hw
  have hone : 1 + w⁻¹ = (1 + w) / w := by
    field_simp [hw]
    ring
  rw [wildOddNormalizedNorm, wildOddNormalizedNorm, hone,
    norm_div (F := F) (K := K), Algebra.norm_inv]
  field_simp [hn]
  ring

/-- The exceptional correction is exactly `Z(uᵛ)`. -/
theorem zZeroValue_eq_normalizedNorm :
    d.zZeroValue = wildOddNormalizedNorm F K d.dual := rfl

/-- A nonzero-index correction is exactly `Z(u/[j])`. -/
theorem zValue_eq_normalizedNorm
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.zValue j = wildOddNormalizedNorm F K
      (d.u / algebraMap F K
        (wildOddPrimeFieldLift F
          (j : ZMod (residueCharacteristic F)))) := by
  let q : F := wildOddPrimeFieldLift F
    (j : ZMod (residueCharacteristic F))
  have hq : q ≠ 0 := wildOddPrimeFieldLift_ne_zero F j
  have hqK : algebraMap F K q ≠ 0 := by
    intro h
    apply hq
    exact (algebraMap F K).injective (by simpa using h)
  have hone : 1 + d.u / algebraMap F K q =
      (d.u + algebraMap F K q) / algebraMap F K q := by
    field_simp [hqK]
    ring
  change norm F K (d.u + algebraMap F K q) / (d.n + q) =
    wildOddNormalizedNorm F K (d.u / algebraMap F K q)
  rw [wildOddNormalizedNorm, hone,
    norm_div (F := F) (K := K), d.norm_primeFieldLift,
    norm_div (F := F) (K := K), d.norm_u, d.norm_primeFieldLift]
  have hden : 1 + d.n / q = (d.n + q) / q := by
    field_simp [hq]
    ring
  rw [hden, div_div_div_cancel_right₀ hq]

/-- Exact elementary-symmetric expansion of `Z(w)-1`; the terminal norm term
has been canceled only after the displayed denominator was proved nonzero. -/
theorem normalizedNorm_sub_one_eq
    (d' : WildOddCorrectionData F K T)
    (w : K) (hden : 1 + norm F K w ≠ 0) :
    wildOddNormalizedNorm F K w - 1 =
      (∑ r ∈ Finset.range (residueCharacteristic F - 1),
        elementarySymmetric F K (r + 1) w) /
          (1 + norm F K w) := by
  have hp1 : 1 ≤ residueCharacteristic F :=
    (residueCharacteristic_prime F).one_le
  have hdegree : Module.finrank F K = residueCharacteristic F := d'.degree_eq
  have hnorm : norm F K (1 + w) =
      1 + (∑ r ∈ Finset.range (residueCharacteristic F - 1),
        elementarySymmetric F K (r + 1) w) + norm F K w := by
    rw [norm_one_add_eq_one_add_sum_elementarySymmetric, hdegree,
      show residueCharacteristic F = residueCharacteristic F - 1 + 1 by omega,
      Finset.sum_range_succ, Nat.sub_add_cancel hp1,
      ← hdegree, elementarySymmetric_finrank]
    ring
  rw [wildOddNormalizedNorm, hnorm]
  field_simp [hden]
  ring

/-- The exact wild symmetric-function estimate for a normalized norm of
nonnegative input valuation. -/
theorem normalizedNorm_depth
    (d' : WildOddCorrectionData F K T)
    {w : K} {c : ℕ}
    (hw : ord K w = (((c : ℕ) : ℤ) : WithTop ℤ))
    (hdenOrd : ord F (1 + norm F K w) = 0) :
    (((wildOddCorrectionDepth (residueCharacteristic F) T c : ℕ) : ℤ) :
        WithTop ℤ) ≤
      ord F (wildOddNormalizedNorm F K w - 1) := by
  let p := residueCharacteristic F
  have hp : p.Prime := residueCharacteristic_prime F
  have hden : 1 + norm F K w ≠ 0 := by
    apply (ord_ne_top_iff F).mp
    rw [hdenOrd]
    exact WithTop.zero_ne_top
  rw [d'.normalizedNorm_sub_one_eq w hden, ord_div, hdenOrd, sub_zero]
  apply ord_sum F
  intro r hr
  simp only [Finset.mem_range] at hr
  have hb := wild_elementarySymmetric_bound F K p T (c : ℤ)
    hp d'.two_le_T rfl d'.degree_eq d'.traceLowerBound
    (show (((c : ℕ) : ℤ) : WithTop ℤ) ≤ ord K w by rw [hw])
    (show 1 ≤ r + 1 by omega) (show r + 1 < p by omega)
  apply (WithTop.coe_le_coe.mpr ?_).trans hb
  rw [wildOddCorrectionDepth_cast]
  apply Int.ediv_le_ediv (by exact_mod_cast hp.pos)
  push_cast
  nlinarith

/-- A nonzero Teichmüller index remains valuation zero after scalar extension. -/
theorem ord_algebraMap_primeFieldLift
    (j : (ZMod (residueCharacteristic F))ˣ) :
    ord K (algebraMap F K
      (wildOddPrimeFieldLift F
        (j : ZMod (residueCharacteristic F)))) = 0 := by
  rw [ord_algebraMap, ord_wildOddPrimeFieldLift, nsmul_zero]

/-- Exact valuation of the nonzero-index normalized-norm input. -/
theorem ord_scaled_u
    (j : (ZMod (residueCharacteristic F))ˣ) :
    ord K (d.u / algebraMap F K
      (wildOddPrimeFieldLift F
        (j : ZMod (residueCharacteristic F)))) =
      ((d.a : ℤ) : WithTop ℤ) := by
  rw [ord_div, d.ord_u, ord_algebraMap_primeFieldLift, sub_zero]

/-- A normalized norm with strictly positive input valuation has unit denominator. -/
theorem normalizedNorm_denominator_ord_of_pos
    (d' : WildOddCorrectionData F K T)
    {w : K} {c : ℕ} (hc : 0 < c)
    (hw : ord K w = (((c : ℕ) : ℤ) : WithTop ℤ)) :
    ord F (1 + norm F K w) = 0 := by
  have hn : ord F (norm F K w) = (((c : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, d'.residueDegree_eq_one, one_nsmul, hw]
  have hne : ord F (1 : F) ≠ ord F (norm F K w) := by
    rw [ord_one, hn]
    exact_mod_cast hc.ne
  rw [ord_add_eq_min F hne, ord_one, hn]
  simp

/-- Positive-valuation specialization of `normalizedNorm_depth`. -/
theorem normalizedNorm_depth_of_pos
    (d' : WildOddCorrectionData F K T)
    {w : K} {c : ℕ} (hc : 0 < c)
    (hw : ord K w = (((c : ℕ) : ℤ) : WithTop ℤ)) :
    (((wildOddCorrectionDepth (residueCharacteristic F) T c : ℕ) : ℤ) :
        WithTop ℤ) ≤
      ord F (wildOddNormalizedNorm F K w - 1) := by
  exact normalizedNorm_depth d' hw
    (normalizedNorm_denominator_ord_of_pos d' hc hw)

/-- Negative input valuations are reduced exactly by `Z(w⁻¹)=Z(w)`. -/
theorem normalizedNorm_depth_of_neg
    (d' : WildOddCorrectionData F K T)
    {w : K} {c : ℕ} (hc : 0 < c)
    (hw : ord K w = ((-(c : ℤ)) : WithTop ℤ)) :
    (((wildOddCorrectionDepth (residueCharacteristic F) T c : ℕ) : ℤ) :
        WithTop ℤ) ≤
      ord F (wildOddNormalizedNorm F K w - 1) := by
  have hw0 : w ≠ 0 := by
    apply (ord_ne_top_iff K).mp
    rw [hw]
    exact WithTop.coe_ne_top
  have hi : ord K w⁻¹ = (((c : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_inv, hw]
    norm_num
  have hb := normalizedNorm_depth_of_pos d' hc hi
  rw [WildOddCorrectionData.normalizedNorm_inv
    (F := F) (K := K) w hw0] at hb
  exact hb

/-- Uniform absolute-value form of the normalized-norm depth estimate. -/
theorem normalizedNorm_depth_natAbs
    (d' : WildOddCorrectionData F K T)
    {w : K} {a : ℤ}
    (hw : ord K w = (a : WithTop ℤ))
    (hzero : a = 0 → ord F (1 + norm F K w) = 0) :
    (((wildOddCorrectionDepth (residueCharacteristic F) T a.natAbs : ℕ) : ℤ) :
        WithTop ℤ) ≤
      ord F (wildOddNormalizedNorm F K w - 1) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hc : 0 < a.natAbs := Int.natAbs_pos.mpr (by omega)
    have hacast : (a.natAbs : ℤ) = -a := by
      rw [Int.natCast_natAbs, abs_of_neg ha]
    apply normalizedNorm_depth_of_neg d' hc
    rw [hw]
    congr 1
    rw [hacast]
    ring
  · subst a
    simpa using normalizedNorm_depth d' hw (hzero rfl)
  · have hc : 0 < a.natAbs := Int.natAbs_pos.mpr (by omega)
    apply normalizedNorm_depth_of_pos d' hc
    rw [hw]
    congr 1
    exact (Int.natAbs_of_nonneg ha.le).symm

/-- At `a=0`, minimal-orbit noncancellation makes the nonzero-index
normalized-norm denominator a unit. -/
theorem ord_scaled_u_denominator_of_boundary
    (j : (ZMod (residueCharacteristic F))ˣ) (ha : d.a = 0) :
    ord F (1 + norm F K
      (d.u / algebraMap F K
        (wildOddPrimeFieldLift F
          (j : ZMod (residueCharacteristic F))))) = 0 := by
  let q : F := wildOddPrimeFieldLift F
    (j : ZMod (residueCharacteristic F))
  have hq : q ≠ 0 := wildOddPrimeFieldLift_ne_zero F j
  have hfrac : 1 + d.n / q = (d.n + q) / q := by
    field_simp [hq]
    ring
  rw [norm_div (F := F) (K := K), d.norm_u, d.norm_primeFieldLift]
  change ord F (1 + d.n / q) = 0
  rw [hfrac, ord_div]
  have hnum : ord F (d.n + q) = 0 := by
    simpa only [n] using d.boundary_noncancellation ha
      (j : ZMod (residueCharacteristic F))
  rw [hnum, ord_wildOddPrimeFieldLift, sub_zero]

/-- At `a=0`, the exceptional denominator is a unit; this is deduced from
all prime-field factors, not postulated separately. -/
theorem ord_zeroDenominator_of_boundary (ha : d.a = 0) :
    ord F d.zeroDenominator = 0 := by
  classical
  have hfac : ∀ j : ZMod (residueCharacteristic F),
      ord F (d.n + wildOddPrimeFieldLift F j) = 0 := by
    intro j
    simpa only [n] using d.boundary_noncancellation ha j
  have hprod : ord F d.primeFieldProduct = 0 := by
    rw [primeFieldProduct]
    let s := (Finset.univ : Finset (ZMod (residueCharacteristic F)))
    change ord F (s.prod (fun j ↦ d.n + wildOddPrimeFieldLift F j)) = 0
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, ord_mul, hfac j, ih, zero_add]
  have hrel : d.primeFieldProduct = -d.n * d.zeroDenominator := by
    rw [d.primeFieldProduct_eq, d.zeroDenominator_eq,
      ← pow_sub_one_mul (residueCharacteristic_prime F).pos.ne' d.n]
    ring
  calc
    ord F d.zeroDenominator = ord F (-d.n * d.zeroDenominator) := by
      rw [ord_mul, ord_neg, d.ord_n, ha]
      simp
    _ = ord F d.primeFieldProduct := congrArg (ord F) hrel.symm
    _ = 0 := hprod

/-- Exact manuscript depth estimate for every nonzero prime-field correction. -/
theorem ord_x_ge_correctionDepth
    (j : (ZMod (residueCharacteristic F))ˣ) :
    (((wildOddCorrectionDepth (residueCharacteristic F) T
        (Int.natAbs d.a) : ℕ) : ℤ) : WithTop ℤ) ≤
      ord F (d.x j) := by
  let w : K := d.u / algebraMap F K
    (wildOddPrimeFieldLift F
      (j : ZMod (residueCharacteristic F)))
  have hword : ord K w = ((d.a : ℤ) : WithTop ℤ) := by
    simpa only [w] using d.ord_scaled_u j
  have hx : d.x j = wildOddNormalizedNorm F K w - 1 := by
    rw [x, coe_z, d.zValue_eq_normalizedNorm]
  rw [hx]
  apply normalizedNorm_depth_natAbs d hword
  intro ha
  simpa only [w] using d.ord_scaled_u_denominator_of_boundary j ha

/-- Exact manuscript depth estimate for the exceptional correction. -/
theorem ord_xZero_ge_correctionDepth :
    (((wildOddCorrectionDepth (residueCharacteristic F) T
        ((residueCharacteristic F - 1) * Int.natAbs d.a) : ℕ) : ℤ) :
        WithTop ℤ) ≤
      ord F d.xZero := by
  have hk : (((residueCharacteristic F - 1 : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt
      (residueCharacteristic_prime F).one_lt).ne'
  have hzero :
      ((residueCharacteristic F - 1 : ℕ) : ℤ) * d.a = 0 →
        ord F (1 + norm F K d.dual) = 0 := by
    intro h
    have ha : d.a = 0 := (mul_eq_zero.mp h).resolve_left hk
    simpa only [zeroDenominator] using d.ord_zeroDenominator_of_boundary ha
  have hdepth := normalizedNorm_depth_natAbs d d.ord_dual hzero
  have hx : d.xZero = wildOddNormalizedNorm F K d.dual - 1 := by
    rw [xZero, coe_zZero, d.zZeroValue_eq_normalizedNorm]
  rw [hx]
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hdepth

private theorem ceilDiv_two_mono {x y : ℕ} (hxy : x ≤ y) :
    x ⌈/⌉ 2 ≤ y ⌈/⌉ 2 := by
  rw [ceilDiv_le_iff_le_mul (by omega : 0 < (2 : ℕ))]
  exact hxy.trans (by
    simpa only [two_nsmul, two_mul] using
      (le_smul_ceilDiv (b := y) (by omega : 0 < (2 : ℕ))))

/-- The ordinary correction depth contains the stationary half-depth. -/
theorem wildOddCorrectionDepth_ge_half
    (p T c : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hT : 2 ≤ T) :
    T ⌈/⌉ 2 ≤ wildOddCorrectionDepth p T c := by
  have hb := two_mul_wildBaseDepth_ge p T hp hp2 hT
  have heq : wildBaseDepth p T = ((((p - 1) * T) / p : ℕ) : ℤ) := by
    rw [wildBaseDepth, ← Int.natCast_div]
  rw [heq] at hb
  have hb' : T ≤ 2 * (((p - 1) * T) / p) := by
    exact_mod_cast hb
  have hbase : T ⌈/⌉ 2 ≤ wildOddCorrectionDepth p T 0 := by
    rw [ceilDiv_le_iff_le_mul (by omega : 0 < (2 : ℕ))]
    simpa [wildOddCorrectionDepth] using hb'
  exact hbase.trans (Nat.div_le_div_right
    (by omega : 0 + (p - 1) * T ≤ c + (p - 1) * T))

/-- The exceptional correction depth contains `⌈m/2⌉`, with the two signs of
`a=T-m` treated exactly as in the manuscript. -/
theorem wildOddCorrectionDepth_exceptional_ge_half
    (p T m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (_hT : 2 ≤ T) (hm : 2 ≤ m) :
    m ⌈/⌉ 2 ≤ wildOddCorrectionDepth p T
      ((p - 1) * Int.natAbs (wildOddCorrectionOffset T m)) := by
  by_cases h : m ≤ T
  · rw [wildOddCorrectionOffset, Int.natAbs_natCast_sub_natCast_of_ge h]
    have hmM : m ≤ T + (T - m) := by omega
    have hM : 2 ≤ T + (T - m) := by omega
    calc
      m ⌈/⌉ 2 ≤ (T + (T - m)) ⌈/⌉ 2 := ceilDiv_two_mono hmM
      _ ≤ wildOddCorrectionDepth p (T + (T - m)) 0 :=
        wildOddCorrectionDepth_ge_half p _ 0 hp hp2 hM
      _ = wildOddCorrectionDepth p T ((p - 1) * (T - m)) := by
        simp only [wildOddCorrectionDepth, zero_add]
        congr 1
        rw [Nat.mul_add]
        omega
  · have hTm : T ≤ m := by omega
    rw [wildOddCorrectionOffset, Int.natAbs_natCast_sub_natCast_of_le hTm]
    calc
      m ⌈/⌉ 2 ≤ wildOddCorrectionDepth p m 0 :=
        wildOddCorrectionDepth_ge_half p m 0 hp hp2 hm
      _ = wildOddCorrectionDepth p T ((p - 1) * (m - T)) := by
        simp only [wildOddCorrectionDepth, zero_add]
        congr 1
        rw [← Nat.mul_add, Nat.sub_add_cancel hTm]

/-- Every correction depth occurring here is positive. -/
theorem correctionDepth_pos
    (d' : WildOddCorrectionData F K T) (c : ℕ) :
    0 < wildOddCorrectionDepth (residueCharacteristic F) T c := by
  have hhalf := wildOddCorrectionDepth_ge_half
    (residueCharacteristic F) T c (residueCharacteristic_prime F)
      d'.odd_residueCharacteristic d'.two_le_T
  have hceil : 1 ≤ T ⌈/⌉ 2 := by
    simpa using ceilDiv_two_mono d'.two_le_T
  exact Nat.zero_lt_one.trans_le (hceil.trans hhalf)

/-- Each nonzero-index correction belongs to the exact `R(|a|)` unit layer. -/
theorem z_mem_correctionFiltration
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.z j ∈ unitFiltration F
      (wildOddCorrectionDepth (residueCharacteristic F) T
        (Int.natAbs d.a)) := by
  have hr := correctionDepth_pos d (Int.natAbs d.a)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [hk]
  apply (mem_unitFiltration_succ_iff_ord F k (d.z j)).2
  simpa only [x, hk] using d.ord_x_ge_correctionDepth j

/-- The exceptional correction belongs to its exact `R((p-1)|a|)` unit layer. -/
theorem zZero_mem_correctionFiltration :
    d.zZero ∈ unitFiltration F
      (wildOddCorrectionDepth (residueCharacteristic F) T
        ((residueCharacteristic F - 1) * Int.natAbs d.a)) := by
  have hr := correctionDepth_pos d
    ((residueCharacteristic F - 1) * Int.natAbs d.a)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [hk]
  apply (mem_unitFiltration_succ_iff_ord F k d.zZero).2
  simpa only [xZero, hk] using d.ord_xZero_ge_correctionDepth

/-- Downstream stationary-character interface for every nonzero index. -/
theorem z_mem_halfFiltration
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.z j ∈ unitFiltration F (T ⌈/⌉ 2) := by
  exact unitFiltration_antitone F
    (wildOddCorrectionDepth_ge_half
      (residueCharacteristic F) T (Int.natAbs d.a)
      (residueCharacteristic_prime F) d.odd_residueCharacteristic d.two_le_T)
    (d.z_mem_correctionFiltration j)

/-- Downstream linearization interface for the exceptional correction. -/
theorem zZero_mem_conductorHalfFiltration :
    d.zZero ∈ unitFiltration F (d.m ⌈/⌉ 2) := by
  exact unitFiltration_antitone F
    (wildOddCorrectionDepth_exceptional_ge_half
      (residueCharacteristic F) T d.m
      (residueCharacteristic_prime F) d.odd_residueCharacteristic
      d.two_le_T d.two_le_m)
    d.zZero_mem_correctionFiltration

end WildOddCorrectionData

end Data

end

end LanglandsFirstMainLemma
