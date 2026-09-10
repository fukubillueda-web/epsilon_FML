import LanglandsFirstMainLemma.Cases.WildOdd.CorrectionUnits
import LanglandsFirstMainLemma.Basic.FiniteProducts

open scoped BigOperators

namespace LanglandsFirstMainLemma

noncomputable section

private theorem correctionFormula_localField_infinite
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

private theorem correctionFormula_elementarySymmetric_algebraMap_mul
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (c : F) (x : K) (j : ℕ) :
    elementarySymmetric F K j (algebraMap F K c * x) =
      c ^ j * elementarySymmetric F K j x := by
  letI : Infinite F := correctionFormula_localField_infinite F
  apply (algebraMap F K).injective
  rw [algebraMap_elementarySymmetric_eq_esymm_galois,
    map_mul, map_pow, algebraMap_elementarySymmetric_eq_esymm_galois]
  rw [galoisConjugates, galoisConjugates]
  simp only [galoisConjugate, map_mul, AlgEquiv.commutes]
  simpa [smul_eq_mul] using
    (Multiset.pow_smul_esymm (algebraMap F K c) j
      ((Finset.univ : Finset Gal(K/F)).val.map fun σ => σ x)).symm

private theorem correctionFormula_norm_add_algebraMap
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p : ℕ) (hdegree : Module.finrank F K = p)
    (x : K) (c : F) (hc : c ≠ 0) :
    norm F K (x + algebraMap F K c) =
      ∑ r ∈ Finset.range (p + 1),
        c ^ (p - r) * elementarySymmetric F K r x := by
  have hfactor : x + algebraMap F K c =
      algebraMap F K c * (1 + algebraMap F K c⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc,
      map_one, one_mul]
    ring
  rw [hfactor, map_mul, norm_algebraMap, hdegree,
    norm_one_add_eq_sum_elementarySymmetric, hdegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : r ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  rw [correctionFormula_elementarySymmetric_algebraMap_mul]
  calc
    c ^ p * (c⁻¹ ^ r * elementarySymmetric F K r x) =
        (c ^ (p - r) * c ^ r) *
          (c⁻¹ ^ r * elementarySymmetric F K r x) := by
            rw [pow_sub_mul_pow c hrle]
    _ = c ^ (p - r) * ((c * c⁻¹) ^ r *
          elementarySymmetric F K r x) := by ring
    _ = c ^ (p - r) * elementarySymmetric F K r x := by
      rw [mul_inv_cancel₀ hc, one_pow, one_mul]

end

end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma

noncomputable section

private theorem correctionFormula_norm_add_expansion
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T)
    (j : (ZMod (residueCharacteristic F))ˣ) :
    norm F K (d.u + algebraMap F K
      (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) =
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) +
        (∑ r ∈ Finset.range (residueCharacteristic F - 1),
          wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) ^
              (residueCharacteristic F - (r + 1)) *
            elementarySymmetric F K (r + 1) d.u) + d.n := by
  let p := residueCharacteristic F
  let q := wildOddPrimeFieldLift F (j : ZMod p)
  have hp3 : 3 ≤ p := by
    have hp2 := (residueCharacteristic_prime F).two_le
    have hpne := d.odd_residueCharacteristic
    omega
  have hq : q ≠ 0 := wildOddPrimeFieldLift_ne_zero F j
  rw [correctionFormula_norm_add_algebraMap F K p d.degree_eq d.u q hq]
  let f : ℕ → F := fun r ↦
    q ^ (p - r) * elementarySymmetric F K r d.u
  have hzero : f 0 = q := by
    unfold f
    rw [Nat.sub_zero, elementarySymmetric_zero, mul_one]
    simpa only [p, q] using
      (wildOddPrimeFieldLift_pow F
        (j : ZMod (residueCharacteristic F)))
  have hterminal : f p = d.n := by
    simp only [f, Nat.sub_self, pow_zero, one_mul]
    have h := elementarySymmetric_finrank F K d.u
    rw [d.degree_eq] at h
    simpa only [p, WildOddCorrectionData.norm_u] using h
  have hshift : (∑ r ∈ Finset.range p, f r) =
      (∑ r ∈ Finset.range (p - 1), f (r + 1)) + f 0 := by
    have h := Finset.sum_range_succ' f (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    exact h
  calc
    (∑ r ∈ Finset.range (p + 1),
      q ^ (p - r) * elementarySymmetric F K r d.u) =
        ∑ r ∈ Finset.range (p + 1), f r := rfl
    _ = (∑ r ∈ Finset.range p, f r) + f p :=
      Finset.sum_range_succ f p
    _ = ((∑ r ∈ Finset.range (p - 1), f (r + 1)) + f 0) + f p := by
      rw [hshift]
    _ = q + (∑ r ∈ Finset.range (p - 1),
        q ^ (p - (r + 1)) * elementarySymmetric F K (r + 1) d.u) + d.n := by
      rw [hzero, hterminal]
      simp only [f]
      ring

private theorem correctionFormula_nonzero_numerator
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T)
    (j : (ZMod (residueCharacteristic F))ˣ) :
    norm F K (d.u + algebraMap F K
        (wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)))) -
      d.denominator j =
        ∑ r ∈ Finset.range (residueCharacteristic F - 1),
          wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) ^
              (residueCharacteristic F - (r + 1)) *
            elementarySymmetric F K (r + 1) d.u := by
  rw [correctionFormula_norm_add_expansion d j]
  simp only [WildOddCorrectionData.denominator]
  ring

private theorem correctionFormula_x_nonzero
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T)
    (j : (ZMod (residueCharacteristic F))ˣ) :
    d.x j =
      (∑ r ∈ Finset.range (residueCharacteristic F - 1),
        wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) ^
            (residueCharacteristic F - (r + 1)) *
          elementarySymmetric F K (r + 1) d.u) / d.denominator j := by
  apply (eq_div_iff (d.denominator_ne_zero j)).2
  rw [WildOddCorrectionData.x_eq,
    ← d.coe_z j,
    ← correctionFormula_nonzero_numerator d j,
    d.norm_add_eq_denominator_mul j]
  ring

private theorem correctionFormula_norm_sub_expansion
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    norm F K (algebraMap F K d.n - d.u) =
      d.n ^ residueCharacteristic F - d.n +
        (∑ r ∈ Finset.range (residueCharacteristic F - 1),
          (-1 : F) ^ (r + 1) * elementarySymmetric F K (r + 1) d.u *
            d.n ^ (residueCharacteristic F - (r + 1))) := by
  let p := residueCharacteristic F
  have hp3 : 3 ≤ p := by
    have hp2 := (residueCharacteristic_prime F).two_le
    have hpne := d.odd_residueCharacteristic
    omega
  have hneg (r : ℕ) :
      elementarySymmetric F K r (-d.u) =
        (-1 : F) ^ r * elementarySymmetric F K r d.u := by
    have h := correctionFormula_elementarySymmetric_algebraMap_mul
      F K (-1 : F) d.u r
    simpa using h
  rw [show algebraMap F K d.n - d.u = -d.u + algebraMap F K d.n by ring,
    correctionFormula_norm_add_algebraMap F K p d.degree_eq (-d.u) d.n d.n_ne_zero]
  simp_rw [hneg]
  let f : ℕ → F := fun r ↦
    d.n ^ (p - r) *
      ((-1 : F) ^ r * elementarySymmetric F K r d.u)
  have hpodd : Odd p := (residueCharacteristic_prime F).odd_of_ne_two
    d.odd_residueCharacteristic
  have hzero : f 0 = d.n ^ p := by
    simp [f]
  have hterminal : f p = -d.n := by
    simp only [f, Nat.sub_self, pow_zero, one_mul]
    have h := elementarySymmetric_finrank F K d.u
    rw [d.degree_eq] at h
    rw [h, WildOddCorrectionData.norm_u, hpodd.neg_one_pow, neg_one_mul]
  have hshift : (∑ r ∈ Finset.range p, f r) =
      (∑ r ∈ Finset.range (p - 1), f (r + 1)) + f 0 := by
    have h := Finset.sum_range_succ' f (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    exact h
  calc
    (∑ r ∈ Finset.range (p + 1),
      d.n ^ (p - r) *
        ((-1 : F) ^ r * elementarySymmetric F K r d.u)) =
        ∑ r ∈ Finset.range (p + 1), f r := rfl
    _ = (∑ r ∈ Finset.range p, f r) + f p :=
      Finset.sum_range_succ f p
    _ = ((∑ r ∈ Finset.range (p - 1), f (r + 1)) + f 0) + f p := by
      rw [hshift]
    _ = d.n ^ p - d.n +
        (∑ r ∈ Finset.range (p - 1),
          (-1 : F) ^ (r + 1) * elementarySymmetric F K (r + 1) d.u *
            d.n ^ (p - (r + 1))) := by
      rw [hzero, hterminal]
      simp only [f]
      ring

private theorem correctionFormula_exceptional_numerator
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    norm F K (algebraMap F K d.n - d.u) -
        (d.n ^ residueCharacteristic F - d.n) =
      ∑ r ∈ Finset.range (residueCharacteristic F - 1),
        (-1 : F) ^ (r + 1) * elementarySymmetric F K (r + 1) d.u *
          d.n ^ (residueCharacteristic F - (r + 1)) := by
  rw [correctionFormula_norm_sub_expansion d]
  ring

private theorem correctionFormula_n_mul_xZero
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    d.n * d.xZero =
      -(∑ r ∈ Finset.range (residueCharacteristic F - 1),
        (-1 : F) ^ (r + 1) * elementarySymmetric F K (r + 1) d.u *
          d.n ^ (residueCharacteristic F - (r + 1))) /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
  let S : F :=
    ∑ r ∈ Finset.range (residueCharacteristic F - 1),
      (-1 : F) ^ (r + 1) * elementarySymmetric F K (r + 1) d.u *
        d.n ^ (residueCharacteristic F - (r + 1))
  have hprodX : (d.n ^ residueCharacteristic F - d.n) * d.xZero = S := by
    rw [← d.primeFieldProduct_eq]
    calc
      d.primeFieldProduct * d.xZero =
          d.primeFieldProduct * ((d.zZero : F) - 1) := rfl
      _ = d.primeFieldProduct * (d.zZero : F) - d.primeFieldProduct := by ring
      _ = norm F K (algebraMap F K d.n - d.u) - d.primeFieldProduct := by
        rw [d.norm_sub_eq_primeFieldProduct_mul]
      _ = norm F K (algebraMap F K d.n - d.u) -
          (d.n ^ residueCharacteristic F - d.n) := by
        rw [d.primeFieldProduct_eq]
      _ = S := correctionFormula_exceptional_numerator d
  have hfactor : d.n ^ residueCharacteristic F - d.n =
      -d.n * (1 - d.n ^ (residueCharacteristic F - 1)) := by
    rw [← pow_sub_one_mul (residueCharacteristic_prime F).pos.ne' d.n]
    ring
  have hden := d.one_sub_n_pow_ne_zero
  change d.n * d.xZero = -S / (1 - d.n ^ (residueCharacteristic F - 1))
  field_simp [hden]
  rw [hfactor] at hprodX
  linear_combination -hprodX

/-- The exact numerator called `B` in Proposition `prop:X-closed`. -/
noncomputable def correctionFormulaB
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) : F :=
  trace F K d.u +
    ∑ q ∈ Finset.Ico 1 (residueCharacteristic F - 1),
      (-d.n) ^ q *
        elementarySymmetric F K (residueCharacteristic F - q) d.u

private theorem correctionFormula_exceptional_sum_reindex
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    -(∑ r ∈ Finset.range (residueCharacteristic F - 1),
      (-1 : F) ^ (r + 1) * elementarySymmetric F K (r + 1) d.u *
        d.n ^ (residueCharacteristic F - (r + 1))) =
      trace F K d.u * d.n ^ (residueCharacteristic F - 1) +
        ∑ q ∈ Finset.Ico 1 (residueCharacteristic F - 1),
          (-d.n) ^ q *
            elementarySymmetric F K (residueCharacteristic F - q) d.u := by
  let p := residueCharacteristic F
  have hp3 : 3 ≤ p := by
    have hp2 := (residueCharacteristic_prime F).two_le
    have hpne := d.odd_residueCharacteristic
    omega
  have hpodd : Odd p := (residueCharacteristic_prime F).odd_of_ne_two
    d.odd_residueCharacteristic
  have hpeven : Even (p - 1) := by
    rcases hpodd with ⟨k, hk⟩
    use k
    omega
  let A : ℕ → F := fun r ↦
    (-1 : F) ^ r * elementarySymmetric F K r d.u * d.n ^ (p - r)
  let C : ℕ → F := fun q ↦
    (-d.n) ^ q * elementarySymmetric F K (p - q) d.u
  have hshift :
      (∑ r ∈ Finset.range (p - 1), A (r + 1)) =
        ∑ r ∈ Finset.Ico 1 p, A r := by
    have h := Finset.sum_Ico_add A 0 (p - 1) 1
    simp only [zero_add, Nat.Ico_zero_eq_range,
      Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    simpa only [add_comm] using h
  have hreflect :
      (∑ q ∈ Finset.Ico 1 p, A (p - q)) =
        ∑ r ∈ Finset.Ico 1 p, A r := by
    have h := Finset.sum_Ico_reflect A 1 (m := p) (n := p) (by omega)
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using h
  have hterm (q : ℕ) (hq : q ∈ Finset.Ico 1 p) :
      -A (p - q) = C q := by
    have hqle : q ≤ p := (Finset.mem_Ico.mp hq).2.le
    have hpow : (-1 : F) ^ (p - q) * (-1 : F) ^ q = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hqle, hpodd.neg_one_pow]
    have hsq : (-1 : F) ^ q * (-1 : F) ^ q = 1 := by
      rw [← mul_pow]
      norm_num
    have hsign : -((-1 : F) ^ (p - q)) = (-1 : F) ^ q := by
      calc
        -((-1 : F) ^ (p - q)) =
            -((-1 : F) ^ (p - q)) *
              (((-1 : F) ^ q) * ((-1 : F) ^ q)) := by rw [hsq, mul_one]
        _ = -(((-1 : F) ^ (p - q)) * (-1 : F) ^ q) *
              (-1 : F) ^ q := by ring
        _ = (-1 : F) ^ q := by rw [hpow]; ring
    change -(((-1 : F) ^ (p - q) *
      elementarySymmetric F K (p - q) d.u * d.n ^ (p - (p - q)))) =
        (-d.n) ^ q * elementarySymmetric F K (p - q) d.u
    rw [Nat.sub_sub_self hqle, neg_pow d.n q]
    rw [← hsign]
    ring
  have hminus :
      -(∑ r ∈ Finset.Ico 1 p, A r) =
        ∑ q ∈ Finset.Ico 1 p, C q := by
    rw [← hreflect, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    exact hterm q hq
  have hsplit :
      (∑ q ∈ Finset.Ico 1 p, C q) =
        (∑ q ∈ Finset.Ico 1 (p - 1), C q) + C (p - 1) := by
    have h := Finset.sum_Ico_succ_top (a := 1) (b := p - 1)
      (by omega) C
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    exact h
  have htop : C (p - 1) = trace F K d.u * d.n ^ (p - 1) := by
    change (-d.n) ^ (p - 1) *
      elementarySymmetric F K (p - (p - 1)) d.u =
        trace F K d.u * d.n ^ (p - 1)
    rw [Nat.sub_sub_self (by omega : 1 ≤ p),
      elementarySymmetric_one, neg_pow d.n (p - 1), hpeven.neg_one_pow, one_mul]
    ring
  change -(∑ r ∈ Finset.range (p - 1), A (r + 1)) =
    trace F K d.u * d.n ^ (p - 1) +
      ∑ q ∈ Finset.Ico 1 (p - 1), C q
  rw [hshift, hminus, hsplit, htop]
  ring

/-- The manuscript's simplified exceptional-index identity. -/
theorem correctionFormula_n_mul_xZero_eq_B_sub_trace
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    d.n * d.xZero =
      correctionFormulaB d /
          (1 - d.n ^ (residueCharacteristic F - 1)) - trace F K d.u := by
  rw [correctionFormula_n_mul_xZero d,
    correctionFormula_exceptional_sum_reindex d]
  rw [correctionFormulaB]
  field_simp [d.one_sub_n_pow_ne_zero]
  ring

end


end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma

noncomputable section

open Finset

local instance correctionFormula_residuePrimeFact
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩


private theorem sum_surviving_primeField_indices
    {R : Type*} [CommRing R] (p : ℕ) (hp : 3 ≤ p)
    (n : R) (s : ℕ → R) (C : R) :
    (∑ q ∈ Finset.range (p - 1), ∑ r ∈ Finset.range (p - 1),
      ((-n) ^ q * s (r + 1)) *
        if r + 1 + q = 1 ∨ r + 1 + q = p then C else 0) =
      C * (s 1 + ∑ q ∈ Finset.range (p - 2),
        (-n) ^ (q + 1) * s (p - (q + 1))) := by
  have hzero : (∑ r ∈ Finset.range (p - 1),
      ((-n) ^ 0 * s (r + 1)) *
        if r + 1 + 0 = 1 ∨ r + 1 + 0 = p then C else 0) = s 1 * C := by
    calc
      _ = ((-n) ^ 0 * s (0 + 1)) *
          if 0 + 1 + 0 = 1 ∨ 0 + 1 + 0 = p then C else 0 := by
        apply Finset.sum_eq_single 0
        · intro r hr hr0
          have hrlt : r < p - 1 := Finset.mem_range.mp hr
          simp only [pow_zero, one_mul]
          split_ifs with h
          · rcases h with h | h <;> omega
          · simp
        · intro h
          exfalso
          simp at h
          omega
      _ = s 1 * C := by simp
  have hpos (q : ℕ) (hq : q < p - 2) :
      (∑ r ∈ Finset.range (p - 1),
        ((-n) ^ (q + 1) * s (r + 1)) *
          if r + 1 + (q + 1) = 1 ∨ r + 1 + (q + 1) = p then C else 0) =
        ((-n) ^ (q + 1) * s (p - (q + 1))) * C := by
    calc
      _ = ((-n) ^ (q + 1) * s ((p - (q + 1) - 1) + 1)) *
          if (p - (q + 1) - 1) + 1 + (q + 1) = 1 ∨
            (p - (q + 1) - 1) + 1 + (q + 1) = p then C else 0 := by
        apply Finset.sum_eq_single (p - (q + 1) - 1)
        · intro r hr hneq
          have hrlt : r < p - 1 := Finset.mem_range.mp hr
          split_ifs with h
          · rcases h with h | h
            · omega
            · exfalso
              apply hneq
              omega
          · simp
        · intro hmem
          exfalso
          apply hmem
          apply Finset.mem_range.mpr
          omega
      _ = ((-n) ^ (q + 1) * s (p - (q + 1))) * C := by
        have hqp : q + 1 < p := by omega
        have hdiff : 1 ≤ p - (q + 1) := Nat.sub_pos_of_lt hqp
        rw [Nat.sub_add_cancel hdiff]
        rw [if_pos]
        exact Or.inr (Nat.sub_add_cancel hqp.le)
  calc
    _ = (∑ q ∈ Finset.range (p - 2 + 1), ∑ r ∈ Finset.range (p - 1),
          ((-n) ^ q * s (r + 1)) *
            if r + 1 + q = 1 ∨ r + 1 + q = p then C else 0) := by
      congr 3
      omega
    _ = (∑ q ∈ Finset.range (p - 2), ∑ r ∈ Finset.range (p - 1),
          ((-n) ^ (q + 1) * s (r + 1)) *
            if r + 1 + (q + 1) = 1 ∨ r + 1 + (q + 1) = p then C else 0) +
        (∑ r ∈ Finset.range (p - 1),
          ((-n) ^ 0 * s (r + 1)) *
            if r + 1 + 0 = 1 ∨ r + 1 + 0 = p then C else 0) := by
      rw [Finset.sum_range_succ']
    _ = (∑ q ∈ Finset.range (p - 2),
          ((-n) ^ (q + 1) * s (p - (q + 1))) * C) + s 1 * C := by
      rw [hzero]
      apply congrArg (fun z ↦ z + s 1 * C)
      apply Finset.sum_congr rfl
      intro q hq
      exact hpos q (Finset.mem_range.mp hq)
    _ = C * (s 1 + ∑ q ∈ Finset.range (p - 2),
        (-n) ^ (q + 1) * s (p - (q + 1))) := by
      rw [← Finset.sum_mul]
      ring

private theorem dvd_primeField_exponent_iff
    (p r q : ℕ) (hp : 3 ≤ p) (hr : 1 ≤ r) (hr' : r < p)
    (hq : q < p - 1) :
    p - 1 ∣ 2 * p - 1 - r - q ↔ r + q = 1 ∨ r + q = p := by
  have heq : (2 * p - 1 - r - q) + (r + q - 1) = 2 * (p - 1) := by
    omega
  have hklt : r + q - 1 < 2 * (p - 1) := by omega
  have hdvd : p - 1 ∣ 2 * p - 1 - r - q ↔ p - 1 ∣ r + q - 1 := by
    constructor
    · intro he
      apply (Nat.dvd_add_iff_left he).mpr
      rw [add_comm, heq]
      simpa [mul_comm] using dvd_mul_right (p - 1) 2
    · intro hk
      apply (Nat.dvd_add_iff_right hk).mpr
      rw [add_comm, heq]
      simpa [mul_comm] using dvd_mul_right (p - 1) 2
  rw [hdvd]
  constructor
  · intro hk
    by_cases hlt : r + q - 1 < p - 1
    · left
      have hz := Nat.eq_zero_of_dvd_of_lt hk hlt
      omega
    · right
      have hsub : p - 1 ∣ (r + q - 1) - (p - 1) :=
        Nat.dvd_sub hk (dvd_refl (p - 1))
      have hsub_lt : (r + q - 1) - (p - 1) < p - 1 := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hsub hsub_lt
      omega
  · rintro (h | h)
    · simp [h]
    · simpa [h]

private theorem sum_primeField_double_reduction
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {R : Type*} [CommRing R] [IsDomain R]
    (ω : (ZMod p)ˣ →* Rˣ) (hω : Function.Injective ω)
    (n : R) (s : ℕ → R) :
    (∑ q ∈ Finset.range (p - 1), ∑ r ∈ Finset.range (p - 1),
      ((-n) ^ q * s (r + 1)) *
        (∑ j : (ZMod p)ˣ, ((ω j : R) ^ (2 * p - 1 - (r + 1) - q)))) =
      (((p - 1 : ℕ) : R)) *
        (s 1 + ∑ q ∈ Finset.range (p - 2),
          (-n) ^ (q + 1) * s (p - (q + 1))) := by
  classical
  have hp : 3 ≤ p := by
    have hpprime : p.Prime := Fact.out
    have hp2le : 2 ≤ p := hpprime.two_le
    omega
  calc
    _ = ∑ q ∈ Finset.range (p - 1), ∑ r ∈ Finset.range (p - 1),
        ((-n) ^ q * s (r + 1)) *
          if r + 1 + q = 1 ∨ r + 1 + q = p then
            (((p - 1 : ℕ) : R)) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' : q < p - 1 := Finset.mem_range.mp hq
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r < p - 1 := Finset.mem_range.mp hr
      rw [sum_primeField p (2 * p - 1 - (r + 1) - q) ω hω]
      simp only [dvd_primeField_exponent_iff p (r + 1) q hp (by omega)
        (by omega) hq']
    _ = (((p - 1 : ℕ) : R)) *
        (s 1 + ∑ q ∈ Finset.range (p - 2),
          (-n) ^ (q + 1) * s (p - (q + 1))) :=
      sum_surviving_primeField_indices p hp n s (((p - 1 : ℕ) : R))

private theorem sum_wildOddPrimeField_double_reduction
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fact (residueCharacteristic F).Prime]
    (hodd : residueCharacteristic F ≠ 2) (n : F) (s : ℕ → F) :
    (∑ q ∈ Finset.range (residueCharacteristic F - 1),
      ∑ r ∈ Finset.range (residueCharacteristic F - 1),
      ((-n) ^ q * s (r + 1)) *
        (∑ j : (ZMod (residueCharacteristic F))ˣ,
          ((wildOddPrimeFieldUnits F j : F) ^
            (2 * residueCharacteristic F - 1 - (r + 1) - q)))) =
      (((residueCharacteristic F - 1 : ℕ) : F)) *
        (s 1 + ∑ q ∈ Finset.range (residueCharacteristic F - 2),
          (-n) ^ (q + 1) * s (residueCharacteristic F - (q + 1))) := by
  exact sum_primeField_double_reduction (residueCharacteristic F) hodd
    (wildOddPrimeFieldUnits F) (wildOddPrimeFieldUnits_injective F) n s

private theorem sum_wildOddPrimeField_double_reduction_r_outer
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fact (residueCharacteristic F).Prime]
    (hodd : residueCharacteristic F ≠ 2) (n : F) (s : ℕ → F) :
    (∑ r ∈ Finset.range (residueCharacteristic F - 1),
      ∑ q ∈ Finset.range (residueCharacteristic F - 1),
      ((-n) ^ q * s (r + 1)) *
        (∑ j : (ZMod (residueCharacteristic F))ˣ,
          ((wildOddPrimeFieldUnits F j : F) ^
            (2 * residueCharacteristic F - 1 - (r + 1) - q)))) =
      (((residueCharacteristic F - 1 : ℕ) : F)) *
        (s 1 + ∑ q ∈ Finset.range (residueCharacteristic F - 2),
          (-n) ^ (q + 1) * s (residueCharacteristic F - (q + 1))) := by
  rw [Finset.sum_comm]
  exact sum_wildOddPrimeField_double_reduction F hodd n s

private theorem inverse_add_primeFieldUnit
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {R : Type*} [Field R]
    (ω : (ZMod p)ˣ →* Rˣ) (n : R)
    (hD : 1 - n ^ (p - 1) ≠ 0)
    (j : (ZMod p)ˣ) (hadd : n + (ω j : R) ≠ 0) :
    (n + (ω j : R))⁻¹ =
      (∑ q ∈ Finset.range (p - 1),
        (-n) ^ q * (ω j : R) ^ (p - 2 - q)) /
          (1 - n ^ (p - 1)) := by
  classical
  have hpprime : p.Prime := Fact.out
  have hp1 : 1 ≤ p - 1 := Nat.sub_pos_of_lt hpprime.one_lt
  have hjpow : (ω j : R) ^ (p - 1) = 1 := by
    have hjz : (j : ZMod p) ^ (p - 1) = 1 := by
      simpa [ZMod.card] using
        (FiniteField.pow_card_sub_one_eq_one (j : ZMod p) (Units.ne_zero j))
    have hju : j ^ (p - 1) = 1 := Units.ext hjz
    have hmap : ω j ^ (p - 1) = 1 := by rw [← map_pow, hju, map_one]
    simpa using congrArg ((↑) : Rˣ → R) hmap
  have hnegpow : (-n) ^ (p - 1) = n ^ (p - 1) := by
    rw [neg_pow, (hpprime.even_sub_one hp2).neg_one_pow, one_mul]
  have htel :
      (∑ q ∈ Finset.range (p - 1),
        (-n) ^ q * (ω j : R) ^ (p - 2 - q)) *
          (n + (ω j : R)) = 1 - n ^ (p - 1) := by
    have hgeom := geom_sum₂_mul (-n) (ω j : R) (p - 1)
    rw [show p - 1 - 1 = p - 2 by omega, hnegpow, hjpow] at hgeom
    linear_combination -hgeom
  field_simp [hadd, hD]
  simpa [mul_comm] using htel.symm

private theorem correctionFormula_inv_denominator
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fact (residueCharacteristic F).Prime]
    {T : ℕ} (d : WildOddCorrectionData F K T)
    (j : (ZMod (residueCharacteristic F))ˣ) :
    (d.denominator j)⁻¹ =
      (∑ q ∈ Finset.range (residueCharacteristic F - 1),
        (-d.n) ^ q *
          wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) ^
            (residueCharacteristic F - 2 - q)) /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
  simpa only [WildOddCorrectionData.denominator,
    coe_wildOddPrimeFieldUnits] using
      (inverse_add_primeFieldUnit (residueCharacteristic F)
        d.odd_residueCharacteristic (wildOddPrimeFieldUnits F) d.n
        d.one_sub_n_pow_ne_zero j (d.denominator_ne_zero j))

private theorem correctionFormula_nonzero_sum_of_x_formula
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fact (residueCharacteristic F).Prime]
    {T : ℕ} (d : WildOddCorrectionData F K T)
    (hx : ∀ j : (ZMod (residueCharacteristic F))ˣ,
      d.x j =
        (∑ r ∈ Finset.range (residueCharacteristic F - 1),
          wildOddPrimeFieldLift F
                (j : ZMod (residueCharacteristic F)) ^
              (residueCharacteristic F - (r + 1)) *
            elementarySymmetric F K (r + 1) d.u) / d.denominator j) :
    (∑ j : (ZMod (residueCharacteristic F))ˣ,
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) * d.x j) =
      ((((residueCharacteristic F - 1 : ℕ) : F)) *
        (trace F K d.u +
          ∑ q ∈ Finset.range (residueCharacteristic F - 2),
            (-d.n) ^ (q + 1) *
              elementarySymmetric F K
                (residueCharacteristic F - (q + 1)) d.u)) /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
  classical
  let p := residueCharacteristic F
  let s : ℕ → F := fun r ↦ elementarySymmetric F K r d.u
  let D : F := 1 - d.n ^ (p - 1)
  have hp3 : 3 ≤ p := by
    have hp2le := (residueCharacteristic_prime F).two_le
    have hpne := d.odd_residueCharacteristic
    omega
  have hinv (j : (ZMod p)ˣ) :
      (d.denominator j)⁻¹ =
        (∑ q ∈ Finset.range (p - 1),
          (-d.n) ^ q * wildOddPrimeFieldLift F (j : ZMod p) ^ (p - 2 - q)) /
            D := by
    simpa only [p, D] using correctionFormula_inv_denominator d j
  have hpoint (j : (ZMod p)ˣ) :
      wildOddPrimeFieldLift F (j : ZMod p) * d.x j =
        (∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ((-d.n) ^ q * s (r + 1)) *
              wildOddPrimeFieldLift F (j : ZMod p) ^
                (2 * p - 1 - (r + 1) - q)) / D := by
    let t : F := wildOddPrimeFieldLift F (j : ZMod p)
    let A : F := ∑ r ∈ Finset.range (p - 1),
      t ^ (p - (r + 1)) * s (r + 1)
    let G : F := ∑ q ∈ Finset.range (p - 1),
      (-d.n) ^ q * t ^ (p - 2 - q)
    have hterm (q r : ℕ) (hq : q < p - 1) (hr : r < p - 1) :
        ((-d.n) ^ q * t ^ (p - 2 - q)) *
            (t * (t ^ (p - (r + 1)) * s (r + 1))) =
          ((-d.n) ^ q * s (r + 1)) *
            t ^ (2 * p - 1 - (r + 1) - q) := by
      have hexp : (p - 2 - q) + 1 + (p - (r + 1)) =
          2 * p - 1 - (r + 1) - q := by omega
      have hpows : t ^ (p - 2 - q) * t * t ^ (p - (r + 1)) =
          t ^ (2 * p - 1 - (r + 1) - q) := by
        calc
          t ^ (p - 2 - q) * t * t ^ (p - (r + 1)) =
              t ^ ((p - 2 - q) + 1) * t ^ (p - (r + 1)) := by
                rw [pow_succ]
          _ = t ^ ((p - 2 - q) + 1 + (p - (r + 1))) := by
            simp [pow_add]
          _ = t ^ (2 * p - 1 - (r + 1) - q) := by rw [hexp]
      calc
        ((-d.n) ^ q * t ^ (p - 2 - q)) *
              (t * (t ^ (p - (r + 1)) * s (r + 1))) =
            ((-d.n) ^ q * s (r + 1)) *
              (t ^ (p - 2 - q) * t * t ^ (p - (r + 1))) := by ring
        _ = ((-d.n) ^ q * s (r + 1)) *
              t ^ (2 * p - 1 - (r + 1) - q) := by rw [hpows]
    have hprod : G * (t * A) =
        ∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ((-d.n) ^ q * s (r + 1)) *
              t ^ (2 * p - 1 - (r + 1) - q) := by
      calc
        G * (t * A) =
            ∑ q ∈ Finset.range (p - 1),
              ((-d.n) ^ q * t ^ (p - 2 - q)) * (t * A) := by
                simp only [G]
                rw [Finset.sum_mul]
        _ = ∑ q ∈ Finset.range (p - 1),
              ∑ r ∈ Finset.range (p - 1),
                ((-d.n) ^ q * t ^ (p - 2 - q)) *
                  (t * (t ^ (p - (r + 1)) * s (r + 1))) := by
            apply Finset.sum_congr rfl
            intro q _
            simp only [A]
            rw [Finset.mul_sum, Finset.mul_sum]
        _ = ∑ q ∈ Finset.range (p - 1),
              ∑ r ∈ Finset.range (p - 1),
                ((-d.n) ^ q * s (r + 1)) *
                  t ^ (2 * p - 1 - (r + 1) - q) := by
            apply Finset.sum_congr rfl
            intro q hq
            apply Finset.sum_congr rfl
            intro r hr
            exact hterm q r (Finset.mem_range.mp hq) (Finset.mem_range.mp hr)
    calc
      t * d.x j = t * (A / d.denominator j) := by
        rw [hx j]
      _ = t * A * (d.denominator j)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      _ = t * A * (G / D) := by rw [hinv j]
      _ = (G * (t * A)) / D := by rw [div_eq_mul_inv]; ring
      _ = (∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ((-d.n) ^ q * s (r + 1)) *
              t ^ (2 * p - 1 - (r + 1) - q)) / D := by rw [hprod]
  have hreorder :
      (∑ j : (ZMod p)ˣ,
        ∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ((-d.n) ^ q * s (r + 1)) *
              wildOddPrimeFieldLift F (j : ZMod p) ^
                (2 * p - 1 - (r + 1) - q)) =
        ∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ((-d.n) ^ q * s (r + 1)) *
              (∑ j : (ZMod p)ˣ,
                wildOddPrimeFieldLift F (j : ZMod p) ^
                  (2 * p - 1 - (r + 1) - q)) := by
    calc
      _ = ∑ q ∈ Finset.range (p - 1),
          ∑ j : (ZMod p)ˣ,
            ∑ r ∈ Finset.range (p - 1),
              ((-d.n) ^ q * s (r + 1)) *
                wildOddPrimeFieldLift F (j : ZMod p) ^
                  (2 * p - 1 - (r + 1) - q) := by
        rw [Finset.sum_comm]
      _ = ∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ∑ j : (ZMod p)ˣ,
              ((-d.n) ^ q * s (r + 1)) *
                wildOddPrimeFieldLift F (j : ZMod p) ^
                  (2 * p - 1 - (r + 1) - q) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_comm]
      _ = ∑ q ∈ Finset.range (p - 1),
          ∑ r ∈ Finset.range (p - 1),
            ((-d.n) ^ q * s (r + 1)) *
              (∑ j : (ZMod p)ˣ,
                wildOddPrimeFieldLift F (j : ZMod p) ^
                  (2 * p - 1 - (r + 1) - q)) := by
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
  have hdouble :
      (∑ q ∈ Finset.range (p - 1),
        ∑ r ∈ Finset.range (p - 1),
          ((-d.n) ^ q * s (r + 1)) *
            (∑ j : (ZMod p)ˣ,
              wildOddPrimeFieldLift F (j : ZMod p) ^
                (2 * p - 1 - (r + 1) - q))) =
        (((p - 1 : ℕ) : F)) *
          (s 1 + ∑ q ∈ Finset.range (p - 2),
            (-d.n) ^ (q + 1) * s (p - (q + 1))) := by
    simpa only [coe_wildOddPrimeFieldUnits] using
      (sum_wildOddPrimeField_double_reduction F
        d.odd_residueCharacteristic d.n s)
  calc
    (∑ j : (ZMod p)ˣ,
      wildOddPrimeFieldLift F (j : ZMod p) * d.x j) =
        ∑ j : (ZMod p)ˣ,
          (∑ q ∈ Finset.range (p - 1),
            ∑ r ∈ Finset.range (p - 1),
              ((-d.n) ^ q * s (r + 1)) *
                wildOddPrimeFieldLift F (j : ZMod p) ^
                  (2 * p - 1 - (r + 1) - q)) / D := by
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint j
    _ = (∑ j : (ZMod p)ˣ,
          ∑ q ∈ Finset.range (p - 1),
            ∑ r ∈ Finset.range (p - 1),
              ((-d.n) ^ q * s (r + 1)) *
                wildOddPrimeFieldLift F (j : ZMod p) ^
                  (2 * p - 1 - (r + 1) - q)) / D := by
      rw [Finset.sum_div]
    _ = ((((p - 1 : ℕ) : F)) *
        (s 1 + ∑ q ∈ Finset.range (p - 2),
          (-d.n) ^ (q + 1) * s (p - (q + 1)))) / D := by
      rw [hreorder, hdouble]
    _ = ((((residueCharacteristic F - 1 : ℕ) : F)) *
        (trace F K d.u +
          ∑ q ∈ Finset.range (residueCharacteristic F - 2),
            (-d.n) ^ (q + 1) * elementarySymmetric F K
              (residueCharacteristic F - (q + 1)) d.u)) /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
      simp only [p, s, D, elementarySymmetric_one]

private theorem correctionFormula_nonzero_sum_with_fact
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fact (residueCharacteristic F).Prime]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    (∑ j : (ZMod (residueCharacteristic F))ˣ,
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) * d.x j) =
      ((((residueCharacteristic F - 1 : ℕ) : F)) *
        (trace F K d.u +
          ∑ q ∈ Finset.range (residueCharacteristic F - 2),
            (-d.n) ^ (q + 1) *
              elementarySymmetric F K
                (residueCharacteristic F - (q + 1)) d.u)) /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
  apply correctionFormula_nonzero_sum_of_x_formula d
  exact correctionFormula_x_nonzero d

/-- Reindexing the shifted range from the prime-field double sum to the manuscript's
indexing of the numerator (B). -/
theorem correctionFormula_B_reindex
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    trace F K d.u +
        ∑ q ∈ Finset.range (residueCharacteristic F - 2),
          (-d.n) ^ (q + 1) *
            elementarySymmetric F K
              (residueCharacteristic F - (q + 1)) d.u =
      correctionFormulaB d := by
  let p := residueCharacteristic F
  let C : ℕ → F := fun q ↦
    (-d.n) ^ q * elementarySymmetric F K (p - q) d.u
  have hp3 : 3 ≤ p := by
    have hp2 := (residueCharacteristic_prime F).two_le
    have hpne := d.odd_residueCharacteristic
    omega
  have hshift :
      (∑ q ∈ Finset.range (p - 2), C (q + 1)) =
        ∑ q ∈ Finset.Ico 1 (p - 1), C q := by
    have h := Finset.sum_Ico_add C 0 (p - 2) 1
    simp only [zero_add, Nat.Ico_zero_eq_range] at h
    simpa only [show p - 2 + 1 = p - 1 by omega, add_comm] using h
  rw [correctionFormulaB]
  change trace F K d.u + (∑ q ∈ Finset.range (p - 2), C (q + 1)) =
    trace F K d.u + ∑ q ∈ Finset.Ico 1 (p - 1), C q
  rw [hshift]

/-- The exact contribution of all nonzero prime-field indices, in the
manuscript's (B)-notation. -/
theorem correctionFormula_nonzero_sum
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    (∑ j : (ZMod (residueCharacteristic F))ˣ,
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) * d.x j) =
      (((residueCharacteristic F - 1 : ℕ) : F) * correctionFormulaB d) /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
  rw [correctionFormula_nonzero_sum_with_fact d, correctionFormula_B_reindex d]

/-- The exact correction quantity (X) from Proposition `prop:exact-odd-assembly`,
with the exceptional index kept separate from the nonzero prime-field indices. -/
noncomputable def wildOddCorrectionX
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) : F :=
  trace F K d.u + d.n * d.xZero +
    ∑ j : (ZMod (residueCharacteristic F))ˣ,
      wildOddPrimeFieldLift F (j : ZMod (residueCharacteristic F)) * d.x j

/-- The closed norm--trace correction formula of Proposition `prop:X-closed`.
This is an exact equality in (F), not a congruence or valuation estimate. -/
theorem wildOdd_correctionFormula
    {F K : Type*} [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {T : ℕ} (d : WildOddCorrectionData F K T) :
    wildOddCorrectionX d =
      (residueCharacteristic F : F) * correctionFormulaB d /
        (1 - d.n ^ (residueCharacteristic F - 1)) := by
  have hpcast :
      (residueCharacteristic F : F) =
        ((residueCharacteristic F - 1 : ℕ) : F) + 1 := by
    have hp1 : 1 ≤ residueCharacteristic F :=
      (residueCharacteristic_prime F).one_le
    have hnat : residueCharacteristic F - 1 + 1 = residueCharacteristic F :=
      Nat.sub_add_cancel hp1
    calc
      (residueCharacteristic F : F) =
          ((residueCharacteristic F - 1 + 1 : ℕ) : F) :=
        congrArg (fun n : ℕ ↦ (n : F)) hnat.symm
      _ = ((residueCharacteristic F - 1 : ℕ) : F) + 1 := by simp
  rw [wildOddCorrectionX, correctionFormula_n_mul_xZero_eq_B_sub_trace d,
    correctionFormula_nonzero_sum d, hpcast]
  ring

end

end LanglandsFirstMainLemma
