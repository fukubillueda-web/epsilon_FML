import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.LocalField.Extension

/-!
# Higher symmetric terms on the wild odd upper critical line

This file proves Lemma `lem:odd-upper-higher-vanishing` of the manuscript. The lower,
critical, and upper conductor rows are obtained from the exact norm-pullback formulas. The
wild symmetric-function estimate is then used with its exact floor and exact different
contribution. Degrees zero, one, two, the intermediate range, and the terminal norm term are
kept separate.
-/

open scoped BigOperators

namespace LanglandsFirstMainLemma

noncomputable section

/-- The manuscript's three-row formula for the last nontrivial upper conductor depth. -/
def wildOddUpperDepth (p t d : ℕ) : ℕ :=
  if 2 * d < t then 2 * d
  else if 2 * d = t then t
  else t + p * (2 * d - t)

/-- The valuation `a = t - b = t - 2d` of the upper correction multiplier. -/
def wildOddUpperShift (t d : ℕ) : ℤ := (t : ℤ) - 2 * (d : ℤ)

/-- The degree-`j` term in the exact upper critical correction
`s_j(ux) - N(u)s_j(x)`. -/
noncomputable def wildOddUpperCorrectionTerm
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (u x : K) (j : ℕ) : F :=
  elementarySymmetric F K j (u * x) -
    norm F K u * elementarySymmetric F K j x

/-- The exact combination `sum_{j=2}^p (s_j(ux) - N(u)s_j(x))`. -/
noncomputable def wildOddUpperCorrection
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (u x : K) : F :=
  ∑ j ∈ Finset.Icc 2 p, wildOddUpperCorrectionTerm F K u x j

/-- The degree-two correction which survives on the last ramification quotient. -/
noncomputable def wildOddUpperQuadraticCorrection
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (u x : K) : F :=
  wildOddUpperCorrectionTerm F K u x 2

/-- Coefficients of the exact upper correction, extended by zero outside degrees `2,...,p`.
This makes absence of constant and affine terms a literal coefficient statement. -/
noncomputable def wildOddUpperCorrectionCoefficient
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (u x : K) (j : ℕ) : F :=
  if 2 ≤ j ∧ j ≤ p then wildOddUpperCorrectionTerm F K u x j else 0

/-- There is no constant term in the upper correction. -/
@[simp] theorem wildOddUpperCorrectionCoefficient_zero
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (u x : K) :
    wildOddUpperCorrectionCoefficient F K p u x 0 = 0 := by
  simp [wildOddUpperCorrectionCoefficient]

/-- There is no affine term in the upper correction. -/
@[simp] theorem wildOddUpperCorrectionCoefficient_one
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (u x : K) :
    wildOddUpperCorrectionCoefficient F K p u x 1 = 0 := by
  simp [wildOddUpperCorrectionCoefficient]

/-- Degree two is exactly the displayed quadratic correction. -/
theorem wildOddUpperCorrectionCoefficient_two
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (hp : 2 ≤ p) (u x : K) :
    wildOddUpperCorrectionCoefficient F K p u x 2 =
      wildOddUpperQuadraticCorrection F K u x := by
  simp [wildOddUpperCorrectionCoefficient, wildOddUpperQuadraticCorrection, hp]

/-- The terminal degree is an exact cancellation, not a valuation estimate. -/
theorem wildOddUpperCorrectionTerm_degree
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (hdegree : Module.finrank F K = p) (u x : K) :
    wildOddUpperCorrectionTerm F K u x p = 0 := by
  rw [wildOddUpperCorrectionTerm, ← hdegree, elementarySymmetric_finrank,
    elementarySymmetric_finrank, map_mul]
  ring

/-- When the odd prime degree is three, the range `3 ≤ j < p` is empty. -/
theorem wildOdd_intermediate_range_empty_degree_three
    {j : ℕ} (hj : 3 ≤ j) (hjlt : j < 3) : False := by
  omega

private theorem wildOddLocalField_infinite
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

/-- Elementary symmetric coefficients are homogeneous of their stated degree under a
base-field scalar. -/
theorem elementarySymmetric_algebraMap_mul
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (c : F) (x : K) (j : ℕ) :
    elementarySymmetric F K j (algebraMap F K c * x) =
      c ^ j * elementarySymmetric F K j x := by
  letI : Infinite F := wildOddLocalField_infinite F
  apply (algebraMap F K).injective
  rw [algebraMap_elementarySymmetric_eq_esymm_galois,
    map_mul, map_pow, algebraMap_elementarySymmetric_eq_esymm_galois]
  rw [galoisConjugates, galoisConjugates]
  simp only [galoisConjugate, map_mul, AlgEquiv.commutes]
  simpa [smul_eq_mul] using
    (Multiset.pow_smul_esymm (algebraMap F K c) j
      ((Finset.univ : Finset Gal(K/F)).val.map fun σ => σ x)).symm

/-- The surviving degree-two correction is genuinely homogeneous quadratic. -/
theorem wildOddUpperQuadraticCorrection_homogeneous
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (c : F) (u x : K) :
    wildOddUpperQuadraticCorrection F K u (algebraMap F K c * x) =
      c ^ 2 * wildOddUpperQuadraticCorrection F K u x := by
  unfold wildOddUpperQuadraticCorrection wildOddUpperCorrectionTerm
  rw [show u * (algebraMap F K c * x) = algebraMap F K c * (u * x) by ring]
  rw [elementarySymmetric_algebraMap_mul,
    elementarySymmetric_algebraMap_mul]
  ring

/-- Separate the exact degree-two term, the range `3 ≤ j < p`, and the terminal degree. -/
theorem wildOddUpperCorrection_decompose
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (hp : 3 ≤ p) (u x : K) :
    wildOddUpperCorrection F K p u x =
      wildOddUpperQuadraticCorrection F K u x +
        (∑ j ∈ Finset.Ico 3 p, wildOddUpperCorrectionTerm F K u x j) +
          wildOddUpperCorrectionTerm F K u x p := by
  have hIcc : Finset.Icc 2 p = insert 2 (insert p (Finset.Ico 3 p)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have h2 : 2 ∉ insert p (Finset.Ico 3 p) := by
    simp
    omega
  have hpnot : p ∉ Finset.Ico 3 p := by simp
  rw [wildOddUpperCorrection, hIcc, Finset.sum_insert h2, Finset.sum_insert hpnot]
  rw [wildOddUpperQuadraticCorrection]
  ring

/-- View the correction at a chosen stationary representative. The representative is absent
from the formula: its later translation changes the critical affine character and elementary
factor together, but it cannot change this norm correction. -/
noncomputable def wildOddUpperCorrectionAtRepresentative
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (_representative : K) (p : ℕ) (u x : K) : F :=
  wildOddUpperCorrection F K p u x

/-- Every representative translation used later leaves the upper norm correction unchanged. -/
@[simp] theorem wildOddUpperCorrectionAtRepresentative_translate
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    (representative translation : K) (p : ℕ) (u x : K) :
    wildOddUpperCorrectionAtRepresentative F K (representative + translation) p u x =
      wildOddUpperCorrectionAtRepresentative F K representative p u x := rfl

/-- The exact three conductor rows, with the high row kept in integers so no truncated natural
subtraction can weaken the break factor. -/
def WildOddUpperDepthFormula (p t d dK : ℕ) : Prop :=
  (2 * d < t → dK = d) ∧
  (2 * d = t → dK = d) ∧
  (t < 2 * d →
    (2 * (dK : ℤ) : ℤ) =
      (t : ℤ) + (p : ℤ) * (2 * (d : ℤ) - (t : ℤ)))

/-- The implication form of the three conductor rows is equivalent to the displayed piecewise
natural-number formula. -/
theorem WildOddUpperDepthFormula.eq_piecewise
    {p t d dK : ℕ} (h : WildOddUpperDepthFormula p t d dK) :
    2 * dK = wildOddUpperDepth p t d := by
  by_cases hbelow : 2 * d < t
  · simp [wildOddUpperDepth, hbelow, h.1 hbelow]
  · by_cases hcritical : 2 * d = t
    · simp [wildOddUpperDepth, hcritical, h.2.1 hcritical]
    · have habove : t < 2 * d := by omega
      have hZ := h.2.2 habove
      simp [wildOddUpperDepth, hbelow, hcritical]
      apply Int.ofNat_injective
      change (2 : ℤ) * (dK : ℤ) =
        (t : ℤ) + (p : ℤ) * ((2 * d - t : ℕ) : ℤ)
      rw [Nat.cast_sub habove.le]
      push_cast
      exact hZ

/-- The exact depth rows obtained from the norm-pullback conductor formulas. The critical row
uses minimality in the norm-character orbit, and the high row retains the full different factor
`(p-1)(t+1)`. -/
theorem wildOdd_upperDepth_eq_of_conductors
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (d dK : ℕ) (hchiF : chiF.conductor = 2 * d + 1)
    (hchiK : chiK.conductor = 2 * dK + 1)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q) :
    WildOddUpperDepthFormula (Module.finrank F K) t d dK := by
  constructor
  · intro hbelow
    have heq := chiF.conductor_compNorm_eq_belowBreak
      F K ht hres pi hpi hgen chiK hcomp (by omega)
    omega
  constructor
  · intro hcritical
    have heq := chiF.conductor_compNorm_eq_of_minimalOrbit
      F K ht hres pi hpi hgen chiK hcomp (by omega) hminimal
    omega
  · intro habove
    have heq := chiF.conductor_compNorm_eq_high_explicit
      F K ht hres pi hpi hgen chiK hcomp (by omega)
    rw [hchiF, hchiK] at heq
    push_cast [Nat.cast_sub (show 1 ≤ Module.finrank F K from Module.finrank_pos)] at heq
    linarith

/-- The two exact numerical inequalities used under the wild symmetric-function floors. The
`p=3` branch is disposed of separately as an empty intermediate range; for `p≥5`, the proof
keeps the rows `2d<t`, `2d=t`, and `t<2d` separate. -/
theorem wildOdd_upper_numerical_inequalities
    (p t d dK j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (htpos : 0 < t) (hdpos : 0 < d)
    (hdepth : 2 * dK = wildOddUpperDepth p t d)
    (hj : 3 ≤ j) (hjlt : j < p) :
    (((t + 1 : ℕ) : ℤ) ≤
        (j : ℤ) * ((dK : ℤ) + wildOddUpperShift t d)) ∧
      (((t + 1 : ℕ) : ℤ) ≤
        (j : ℤ) * (dK : ℤ) + (p : ℤ) * wildOddUpperShift t d) := by
  have hp3 : 3 ≤ p := by
    have hpge2 := hp.two_le
    omega
  by_cases hp_eq_three : p = 3
  · exact (wildOdd_intermediate_range_empty_degree_three hj (by omega)).elim
  have hp_ne_four : p ≠ 4 := by
    intro hp_eq_four
    subst p
    norm_num at hp
  have hp5 : 5 ≤ p := by omega
  have hp4 : 4 ≤ p := hp5.trans' (by omega)
  rcases lt_trichotomy (2 * d) t with hlt | heq | hgt
  · have hdK : dK = d := by
      simp [wildOddUpperDepth, hlt] at hdepth
      omega
    subst dK
    have hdle : d ≤ t := by omega
    have h2dle : 2 * d ≤ t := by omega
    have hfirstBase : t + 1 ≤ 3 * (t - d) := by omega
    have hfirstMono : 3 * (t - d) ≤ j * (t - d) :=
      Nat.mul_le_mul_right (t - d) hj
    have hfirstNat : t + 1 ≤ j * (t - d) := hfirstBase.trans hfirstMono
    have hsecondBase : t + 1 ≤ 3 * d + 4 * (t - 2 * d) := by omega
    have hjd : 3 * d ≤ j * d := Nat.mul_le_mul_right d hj
    have hpa : 4 * (t - 2 * d) ≤ p * (t - 2 * d) :=
      Nat.mul_le_mul_right (t - 2 * d) hp4
    have hsecondNat : t + 1 ≤ j * d + p * (t - 2 * d) := by omega
    constructor
    · have hcast : (t : ℤ) - (d : ℤ) = ((t - d : ℕ) : ℤ) := by omega
      push_cast
      rw [wildOddUpperShift,
        show (d : ℤ) + ((t : ℤ) - 2 * (d : ℤ)) = (t : ℤ) - (d : ℤ) by ring,
        hcast]
      exact_mod_cast hfirstNat
    · have hcast : (t : ℤ) - 2 * (d : ℤ) = ((t - 2 * d : ℕ) : ℤ) := by
        omega
      push_cast
      rw [wildOddUpperShift, hcast]
      exact_mod_cast hsecondNat
  · have hdK : dK = d := by
      simp [wildOddUpperDepth, heq] at hdepth
      omega
    subst t
    subst dK
    have hbase : 2 * d + 1 ≤ 3 * d := by omega
    have hmono : 3 * d ≤ j * d := Nat.mul_le_mul_right d hj
    have hnat : 2 * d + 1 ≤ j * d := hbase.trans hmono
    constructor <;> push_cast <;> norm_num [wildOddUpperShift] <;> exact_mod_cast hnat
  · let q : ℕ := 2 * d - t
    have hqpos : 0 < q := by omega
    have hnotlt : ¬ 2 * d < t := by omega
    have hne : 2 * d ≠ t := by omega
    have hdepthq : 2 * dK = t + p * q := by
      simpa [wildOddUpperDepth, q, hnotlt, hne] using hdepth
    have h4q : 4 * q ≤ p * q := Nat.mul_le_mul_right q hp4
    have hqle : q ≤ dK := by omega
    have hdKpos : 0 < dK := by omega
    have hfirstBase : t + 1 ≤ 3 * (dK - q) := by omega
    have hfirstMono : 3 * (dK - q) ≤ j * (dK - q) :=
      Nat.mul_le_mul_right (dK - q) hj
    have hfirstNat : t + 1 ≤ j * (dK - q) := hfirstBase.trans hfirstMono
    have hsecondBase : t + 1 + p * q ≤ 3 * dK := by omega
    have hsecondMono : 3 * dK ≤ j * dK := Nat.mul_le_mul_right dK hj
    have hsecondNat : t + 1 + p * q ≤ j * dK := hsecondBase.trans hsecondMono
    have hqcast : wildOddUpperShift t d = -(q : ℤ) := by
      dsimp [wildOddUpperShift, q]
      omega
    have hdiffcast : (dK : ℤ) - (q : ℤ) = ((dK - q : ℕ) : ℤ) := by omega
    constructor
    · push_cast
      rw [show (dK : ℤ) + wildOddUpperShift t d =
          (dK : ℤ) - (q : ℤ) by rw [hqcast]; ring, hdiffcast]
      exact_mod_cast hfirstNat
    · push_cast
      rw [hqcast]
      have hsecondZ : (t : ℤ) + 1 + (p : ℤ) * (q : ℤ) ≤
          (j : ℤ) * (dK : ℤ) := by exact_mod_cast hsecondNat
      linarith

/-- Exact-depth application of the wild symmetric-function bound to both intermediate term
families. No floor is replaced by a weaker estimate. -/
theorem wildOdd_intermediate_terms_mem
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    {p t d dK j : ℕ}
    (hp : p.Prime) (htpos : 0 < t) (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p) (hres : residueDegree F K = 1)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * (t + 1) : ℕ) : ℤ))
    (hj : 3 ≤ j) (hjlt : j < p)
    (hnum1 : ((t + 1 : ℕ) : ℤ) ≤
      (j : ℤ) * ((dK : ℤ) + (t : ℤ) - 2 * (d : ℤ)))
    (hnum2 : ((t + 1 : ℕ) : ℤ) ≤
      (j : ℤ) * (dK : ℤ) + (p : ℤ) * ((t : ℤ) - 2 * (d : ℤ)))
    (u x : K)
    (hu : ord K u = (((t : ℤ) - 2 * (d : ℤ) : ℤ) : WithTop ℤ))
    (hx : ((dK : ℤ) : WithTop ℤ) ≤ ord K x) :
    elementarySymmetric F K j (u * x) ∈ lattice F ((t + 1 : ℕ) : ℤ) ∧
      norm F K u * elementarySymmetric F K j x ∈
        lattice F ((t + 1 : ℕ) : ℤ) := by
  let a : ℤ := (t : ℤ) - 2 * (d : ℤ)
  let q : ℤ := dK + a
  let D : ℤ := (((p - 1) * (t + 1) : ℕ) : ℤ)
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hD : D = ((p : ℤ) - 1) * ((t : ℤ) + 1) := by
    dsimp only [D]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hux : (q : WithTop ℤ) ≤ ord K (u * x) := by
    rw [ord_mul, hu]
    change ((dK : ℤ) + a : WithTop ℤ) ≤ (a : WithTop ℤ) + ord K x
    simpa [add_comm] using add_le_add_left hx (a : WithTop ℤ)
  have hsux := wild_elementarySymmetric_bound F K p (t + 1) q hp (by omega)
    hchar hdegree (by simpa [D] using htrace) hux (by omega : 1 ≤ j) hjlt
  have hsx := wild_elementarySymmetric_bound F K p (t + 1) (dK : ℤ) hp (by omega)
    hchar hdegree (by simpa [D] using htrace) hx (by omega : 1 ≤ j) hjlt
  have hsuxD : ((((j : ℤ) * q + D) / (p : ℤ) : ℤ) : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j (u * x)) := by
    simpa only [D] using hsux
  have hsxD : ((((j : ℤ) * (dK : ℤ) + D) / (p : ℤ) : ℤ) : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
    simpa only [D] using hsx
  constructor
  · rw [mem_lattice]
    apply (show (((t + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        ((((j : ℤ) * q + D) / (p : ℤ) : ℤ) : WithTop ℤ) by
      rw [WithTop.coe_le_coe, Int.le_ediv_iff_mul_le hpZ, hD]
      dsimp only [q, a]
      push_cast
      calc
        ((t : ℤ) + 1) * (p : ℤ) =
            ((t : ℤ) + 1) + ((p : ℤ) - 1) * ((t : ℤ) + 1) := by ring
        _ ≤ (j : ℤ) * ((dK : ℤ) + (t : ℤ) - 2 * (d : ℤ)) +
            ((p : ℤ) - 1) * ((t : ℤ) + 1) := by
              simpa only [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
                add_le_add_right hnum1 (((p : ℤ) - 1) * ((t : ℤ) + 1))
        _ = (j : ℤ) * ((dK : ℤ) + ((t : ℤ) - 2 * (d : ℤ))) +
            ((p : ℤ) - 1) * ((t : ℤ) + 1) := by ring).trans
    exact hsuxD
  · rw [mem_lattice, ord_mul, ord_norm, hres, one_nsmul, hu]
    apply (show (((t + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (a : WithTop ℤ) +
          ((((j : ℤ) * (dK : ℤ) + D) / (p : ℤ) : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      have haux : ((t : ℤ) + 1) - (p : ℤ) * a ≤ (j : ℤ) * (dK : ℤ) := by
        dsimp only [a]
        push_cast at hnum2
        linarith
      have hdiv : ((t + 1 : ℕ) : ℤ) - a ≤
          ((j : ℤ) * (dK : ℤ) + D) / (p : ℤ) := by
        rw [Int.le_ediv_iff_mul_le hpZ, hD]
        push_cast
        calc
          ((t : ℤ) + 1 - a) * (p : ℤ) =
              ((p : ℤ) - 1) * ((t : ℤ) + 1) +
                (((t : ℤ) + 1) - (p : ℤ) * a) := by ring
          _ ≤ ((p : ℤ) - 1) * ((t : ℤ) + 1) +
                (j : ℤ) * (dK : ℤ) := by
                  simpa only [add_comm, add_left_comm, add_assoc] using
                    add_le_add_left haux (((p : ℤ) - 1) * ((t : ℤ) + 1))
          _ = (j : ℤ) * (dK : ℤ) +
                ((p : ℤ) - 1) * ((t : ℤ) + 1) := by ring
      linarith).trans
    have hadd := add_le_add_left hsxD (a : WithTop ℤ)
    simpa only [add_comm] using hadd

/-- Complete conclusion of the upper higher-symmetric calculation. -/
structure WildOddHigherSymmetricVanishingResult
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K]
    (t : ℕ) (u x : K) : Prop where
  intermediate : ∀ {j : ℕ}, 3 ≤ j → j < Module.finrank F K →
    elementarySymmetric F K j (u * x) ∈ lattice F ((t + 1 : ℕ) : ℤ) ∧
      norm F K u * elementarySymmetric F K j x ∈
        lattice F ((t + 1 : ℕ) : ℤ)
  terminalCancellation :
    wildOddUpperCorrectionTerm F K u x (Module.finrank F K) = 0
  quadraticReduction :
    wildOddUpperCorrection F K (Module.finrank F K) u x -
      wildOddUpperQuadraticCorrection F K u x ∈ lattice F ((t + 1 : ℕ) : ℤ)
  constantCoefficient :
    wildOddUpperCorrectionCoefficient F K (Module.finrank F K) u x 0 = 0
  affineCoefficient :
    wildOddUpperCorrectionCoefficient F K (Module.finrank F K) u x 1 = 0
  quadraticHomogeneous : ∀ c : F,
    wildOddUpperQuadraticCorrection F K u (algebraMap F K c * x) =
      c ^ 2 * wildOddUpperQuadraticCorrection F K u x
  representativeTranslation : ∀ representative translation : K,
    wildOddUpperCorrectionAtRepresentative F K (representative + translation)
        (Module.finrank F K) u x =
      wildOddUpperCorrectionAtRepresentative F K representative
        (Module.finrank F K) u x

/-- **Higher symmetric terms on the upper critical line**
(`lem:odd-upper-higher-vanishing`).

For a wildly ramified cyclic extension of odd prime degree, the exact pullback-conductor rows
give the upper critical depth. Every degree `3 ≤ j < p` term lies in `p_F^(t+1)`, the degree-`p`
terms cancel exactly, and modulo that exact lattice the full correction is its homogeneous
degree-two term. Degrees zero and one are absent, and stationary-representative translations
cannot change the correction.
-/
theorem wildOdd_higherSymmetric_vanish
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hodd : Module.finrank F K ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (d dK : ℕ) (hdpos : 0 < d)
    (hchiF : chiF.conductor = 2 * d + 1)
    (hchiK : chiK.conductor = 2 * dK + 1)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q)
    (u : Kˣ) (x : K)
    (hu : ord K (u : K) = (wildOddUpperShift t d : WithTop ℤ))
    (hx : ((dK : ℤ) : WithTop ℤ) ≤ ord K x) :
    WildOddHigherSymmetricVanishingResult F K t (u : K) x := by
  let p := Module.finrank F K
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen
  have htrace : TraceIdealLowerBound F K p (((p - 1) * (t + 1) : ℕ) : ℤ) := by
    simpa [p] using traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hdepthFormula := wildOdd_upperDepth_eq_of_conductors
    F K ht hres pi hpi hgen chiF chiK hcomp d dK hchiF hchiK hminimal
  have hdepth : 2 * dK = wildOddUpperDepth p t d :=
    hdepthFormula.eq_piecewise
  have hintermediate : ∀ {j : ℕ}, 3 ≤ j → j < p →
      elementarySymmetric F K j ((u : K) * x) ∈ lattice F ((t + 1 : ℕ) : ℤ) ∧
        norm F K (u : K) * elementarySymmetric F K j x ∈
          lattice F ((t + 1 : ℕ) : ℤ) := by
    intro j hj hjlt
    have hnum := wildOdd_upper_numerical_inequalities
      p t d dK j hp hodd htpos hdpos hdepth hj hjlt
    refine wildOdd_intermediate_terms_mem (p := p) (t := t) (d := d) (dK := dK)
      (j := j) F K hp htpos hchar rfl hres htrace hj hjlt ?_ ?_
      (u : K) x ?_ hx
    · simpa [wildOddUpperShift, sub_eq_add_neg, add_assoc] using hnum.1
    · simpa [wildOddUpperShift, sub_eq_add_neg, add_assoc] using hnum.2
    · simpa [wildOddUpperShift] using hu
  have hterminal :
      wildOddUpperCorrectionTerm F K (u : K) x p = 0 :=
    wildOddUpperCorrectionTerm_degree F K p rfl (u : K) x
  have htail :
      (∑ j ∈ Finset.Ico 3 p, wildOddUpperCorrectionTerm F K (u : K) x j) ∈
        lattice F ((t + 1 : ℕ) : ℤ) := by
    apply sum_mem_lattice F
    intro j hj
    have hjrange := Finset.mem_Ico.mp hj
    have hterms := hintermediate hjrange.1 hjrange.2
    exact sub_mem_lattice F hterms.1 hterms.2
  refine
    { intermediate := ?_
      terminalCancellation := hterminal
      quadraticReduction := ?_
      constantCoefficient := by simp
      affineCoefficient := by simp
      quadraticHomogeneous := ?_
      representativeTranslation := ?_ }
  · intro j hj hjlt
    exact hintermediate hj hjlt
  · rw [wildOddUpperCorrection_decompose F K p hp3 (u : K) x, hterminal]
    convert htail using 1
    ring
  · intro c
    exact wildOddUpperQuadraticCorrection_homogeneous F K c (u : K) x
  · intro representative translation
    exact wildOddUpperCorrectionAtRepresentative_translate
      F K representative translation p (u : K) x

end

end LanglandsFirstMainLemma
