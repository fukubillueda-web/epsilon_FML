import LanglandsFirstMainLemma.Parameters.PhaseReduction.ResidualCoordinates
import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsFirstMainLemma.Ramification.NormAboveBreak

/-!
# Quotient-correct residual transport and common displayed coordinates

This module contains the residual class tables, exact complete-function
transport, and the actual upper rows displayed in the fixed lower residue
coordinate. All quotient representatives and Frobenius directions are
preserved literally.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ### Quotient-correct residual class table -/

/-- Normalize an actual depth-`d` field element by the supplied source
uniformizer, then reduce.  The element remains an explicit lattice element;
this definition never selects a representative of a quotient class. -/
noncomputable def phaseReductionResidualClass
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) (y : lattice E (d : ℤ)) : ResidueField E :=
  reduce E ((y : E) / (varpi : E) ^ d) <| by
    apply (div_mem_lattice_iff E ((varpi : E) ^ d) (y : E)
      (d : ℤ) 0 (by rw [ord_pow, hvarpi]; norm_num)).2
    simpa using y.property

@[simp]
theorem phaseReductionResidualClass_source
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) (z : ResidueField E) :
    phaseReductionResidualClass E varpi hvarpi d
      ⟨(varpi : E) ^ d * (teichmuller E z : E), by
        have hp : (varpi : E) ^ d ∈ lattice E (d : ℤ) := by
          rw [mem_lattice, ord_pow, hvarpi]
          norm_num
        have hz : (teichmuller E z : E) ∈ lattice E 0 :=
          (mem_lattice_zero_iff E).2 (teichmuller E z).property
        simpa using mul_mem_lattice E hp hz⟩ = z := by
  unfold phaseReductionResidualClass
  have hp : (varpi : E) ^ d ≠ 0 := pow_ne_zero _ (Units.ne_zero varpi)
  change residueMap E ⟨((varpi : E) ^ d * (teichmuller E z : E)) /
    (varpi : E) ^ d, _⟩ = z
  rw [show (⟨((varpi : E) ^ d * (teichmuller E z : E)) /
      (varpi : E) ^ d, _⟩ : ringOfIntegers E) = teichmuller E z by
    apply Subtype.ext
    exact mul_div_cancel_left₀ _ hp]
  exact residueMap_teichmuller E z

theorem phaseReductionResidualClass_eq_of_sub_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) (y y' : lattice E (d : ℤ))
    (hyy' : (y : E) - (y' : E) ∈ lattice E ((d + 1 : ℕ) : ℤ)) :
    phaseReductionResidualClass E varpi hvarpi d y =
      phaseReductionResidualClass E varpi hvarpi d y' := by
  unfold phaseReductionResidualClass
  apply (reduce_eq_reduce_iff (F := E) _ _).2
  rw [congruentAtDepth_iff_sub_mem_lattice, ← sub_div]
  apply (div_mem_lattice_iff E ((varpi : E) ^ d)
    ((y : E) - (y' : E)) (d : ℤ) 1 (by
      rw [ord_pow, hvarpi]
      norm_num)).2
  simpa only [Nat.cast_add, Nat.cast_one] using hyy'

theorem phaseReductionResidualClass_eq_source_of_sub_mem
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) (z : ResidueField E) (y : lattice E (d : ℤ))
    (hy : (y : E) - (varpi : E) ^ d * (teichmuller E z : E) ∈
      lattice E ((d + 1 : ℕ) : ℤ)) :
    phaseReductionResidualClass E varpi hvarpi d y = z := by
  let yz : lattice E (d : ℤ) :=
    ⟨(varpi : E) ^ d * (teichmuller E z : E), by
      have hp : (varpi : E) ^ d ∈ lattice E (d : ℤ) := by
        rw [mem_lattice, ord_pow, hvarpi]
        norm_num
      have hz : (teichmuller E z : E) ∈ lattice E 0 :=
        (mem_lattice_zero_iff E).2 (teichmuller E z).property
      simpa using mul_mem_lattice E hp hz⟩
  rw [← phaseReductionResidualClass_source E varpi hvarpi d z]
  exact phaseReductionResidualClass_eq_of_sub_mem E varpi hvarpi d y yz hy

theorem phaseReductionResidualClass_eq_zero_of_mem_succ
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) (y : lattice E (d : ℤ))
    (hy : (y : E) ∈ lattice E ((d + 1 : ℕ) : ℤ)) :
    phaseReductionResidualClass E varpi hvarpi d y = 0 := by
  have hzero : (y : E) - (0 : E) ∈ lattice E ((d + 1 : ℕ) : ℤ) := by
    simpa using hy
  let yz : lattice E (d : ℤ) :=
    ⟨(varpi : E) ^ d * (teichmuller E (0 : ResidueField E) : E), by
      have hp : (varpi : E) ^ d ∈ lattice E (d : ℤ) := by
        rw [mem_lattice, ord_pow, hvarpi]
        norm_num
      have hz : (teichmuller E (0 : ResidueField E) : E) ∈ lattice E 0 :=
        (mem_lattice_zero_iff E).2 (teichmuller E 0).property
      simpa using mul_mem_lattice E hp hz⟩
  have hyz : (yz : E) = 0 := by simp [yz]
  have h := phaseReductionResidualClass_eq_of_sub_mem E varpi hvarpi d y yz (by
    simpa only [hyz] using hzero)
  exact h.trans (phaseReductionResidualClass_source E varpi hvarpi d 0)

/-- The actual upper source displacement in the lower residue coordinate.
Its residue input is the natural upper coordinate; the displayed coordinate
is its `p`th power below. -/
noncomputable def phaseReductionUpperSourceDisplacement
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K]
    (pi : ringOfIntegers K) (d : ℕ) (z : ResidueField F) : K :=
  algebraMap F K (teichmuller F z : F) * (pi : K) ^ d

theorem phaseReductionUpperSourceDisplacement_mem
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (d : ℕ) (z : ResidueField F) :
    phaseReductionUpperSourceDisplacement F K pi d z ∈ lattice K (d : ℤ) := by
  rw [mem_lattice, phaseReductionUpperSourceDisplacement, ord_mul,
    ord_algebraMap, ord_pow, ord_uniformizer K hpi]
  have hz : (0 : WithTop ℤ) ≤ ord F (teichmuller F z : F) :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  have hzK : (0 : WithTop ℤ) ≤
      (ramificationIndex F K) • ord F (teichmuller F z : F) :=
    nsmul_nonneg hz _
  simpa [add_comm] using add_le_add_right hzK ((d : ℤ) : WithTop ℤ)

/-- In both low odd rows, the base norm polynomial has displayed residual
class `X`: in the natural upper coordinate `z`, that class is `z^p`. -/
theorem phaseReductionLowBasePolynomial_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t d : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    normPolynomialValue F K
          (phaseReductionUpperSourceDisplacement F K pi d z) -
        (norm F K (pi : K)) ^ d *
          (teichmuller F (z ^ Module.finrank F K) : F) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  let aO : ringOfIntegers F := teichmuller F z
  let a : F := (aO : F)
  let piF : F := norm F K (pi : K)
  let x : K := phaseReductionUpperSourceDisplacement F K pi d z
  have hchar : residueCharacteristic F = p := by
    simpa [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  have hx : ((d : ℕ) : WithTop ℤ) ≤ ord K x := by
    change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x
    simpa only [x, mem_lattice] using
      (phaseReductionUpperSourceDisplacement_mem F K pi hpi d z)
  have hrem := wild_norm_one_add_sub_one_sub_norm_mem_lattice
    F K ht htpos hd hres hchar pi hpi hgen x hx
  have hpiFOrd : ord F piF = ((1 : ℤ) : WithTop ℤ) := by
    dsimp only [piF]
    simpa using (by
      rw [ord_norm, hres, one_nsmul, ord_uniformizer K hpi] :
        ord F (norm F K (pi : K)) = (1 : WithTop ℤ))
  have haPowInt : a ^ p ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (aO ^ p).property
  have hteichInt : (teichmuller F (z ^ p) : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F (z ^ p)).property
  have hcoeff : a ^ p - (teichmuller F (z ^ p) : F) ∈ lattice F 1 := by
    change ((aO ^ p : ringOfIntegers F) : F) -
      ((teichmuller F (z ^ p) : ringOfIntegers F) : F) ∈ lattice F 1
    rw [← residueMap_eq_residueMap_iff]
    dsimp only [aO]
    rw [map_pow, residueMap_teichmuller, residueMap_teichmuller]
  have hpiPow : piF ^ d ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, ord_pow, hpiFOrd]
    norm_num
  have hendpoint :
      norm F K x - piF ^ d * (teichmuller F (z ^ p) : F) ∈
        lattice F ((d + 1 : ℕ) : ℤ) := by
    have hmul0 := mul_mem_lattice F hpiPow hcoeff
    have hmul : piF ^ d *
        (a ^ p - (teichmuller F (z ^ p) : F)) ∈
        lattice F ((d + 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hmul0
    have hnorm : norm F K x = a ^ p * piF ^ d := by
      dsimp only [x, phaseReductionUpperSourceDisplacement, a, aO, piF, p]
      rw [map_mul, norm_algebraMap, map_pow]
    rw [hnorm]
    convert hmul using 1
    ring
  have hsum := add_mem_lattice F hrem hendpoint
  change norm F K (1 + x) - 1 -
      norm F K (pi : K) ^ d *
        (teichmuller F (z ^ Module.finrank F K) : F) ∈ _
  simpa only [p, piF] using (by
    convert hsum using 1
    ring)

theorem phaseReductionLowBaseResidualClass
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t d : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    let piF := phaseReductionLowerUniformizer F K pi hpi
    let y : lattice F (d : ℤ) :=
      ⟨normPolynomialValue F K
          (phaseReductionUpperSourceDisplacement F K pi d z), by
        exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos (by omega)
          hres (residueCharacteristic_eq_degree_of_positive_break
            F K ht htpos pi hpi hgen) pi hpi hgen _
            (by
              change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ _
              simpa only [mem_lattice] using
                phaseReductionUpperSourceDisplacement_mem F K pi hpi d z)⟩
    phaseReductionResidualClass F piF
      (phaseReductionLowerUniformizer_order F K hres pi hpi) d y =
        z ^ Module.finrank F K := by
  dsimp only
  apply phaseReductionResidualClass_eq_source_of_sub_mem F
    (phaseReductionLowerUniformizer F K pi hpi)
    (phaseReductionLowerUniformizer_order F K hres pi hpi) d
    (z ^ Module.finrank F K)
  simpa only [phaseReductionLowerUniformizer_coe] using
    phaseReductionLowBasePolynomial_congruent F K ht htpos hd hres pi hpi
      hgen z

/-- At the boundary, the actual `tau` class is the displayed class
multiplied by the reduction of `N(u)`.  This is the manuscript's `d₀ X`
after `d₀` is derived from the same source `u`; no independent scalar is
introduced. -/
theorem phaseReductionLowBoundaryTauPolynomial_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t d : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hd : d < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Kˣ) (hu : ord K (u : K) = (0 : WithTop ℤ))
    (z : ResidueField F) :
    let nO : ringOfIntegers F :=
      ⟨norm F K (u : K), by
        rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres,
          one_nsmul, hu]
        exact le_rfl⟩
    normPolynomialValue F K
          ((u : K) * phaseReductionUpperSourceDisplacement F K pi d z) -
        (norm F K (pi : K)) ^ d *
          (teichmuller F
            (residueMap F nO * z ^ Module.finrank F K) : F) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
  dsimp only
  let p := Module.finrank F K
  let aO : ringOfIntegers F := teichmuller F z
  let a : F := (aO : F)
  let n : F := norm F K (u : K)
  let nO : ringOfIntegers F := ⟨n, by
    rw [← mem_lattice_zero_iff, mem_lattice]
    dsimp only [n]
    rw [ord_norm, hres, one_nsmul, hu]
    exact le_rfl⟩
  let piF : F := norm F K (pi : K)
  let x : K := (u : K) * phaseReductionUpperSourceDisplacement F K pi d z
  have hchar : residueCharacteristic F = p := by
    simpa [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  have hx : ((d : ℕ) : WithTop ℤ) ≤ ord K x := by
    change (((d : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x
    dsimp only [x]
    rw [ord_mul, hu, zero_add]
    simpa only [mem_lattice] using
      phaseReductionUpperSourceDisplacement_mem F K pi hpi d z
  have hrem := wild_norm_one_add_sub_one_sub_norm_mem_lattice
    F K ht htpos hd hres hchar pi hpi hgen x hx
  have hpiFOrd : ord F piF = ((1 : ℤ) : WithTop ℤ) := by
    dsimp only [piF]
    simpa using (by
      rw [ord_norm, hres, one_nsmul, ord_uniformizer K hpi] :
        ord F (norm F K (pi : K)) = (1 : WithTop ℤ))
  have hnaInt : n * a ^ p ∈ lattice F 0 := by
    rw [mem_lattice, ord_mul]
    dsimp only [n]
    rw [ord_norm, hres, one_nsmul, hu, zero_add]
    exact (mem_lattice_zero_iff F).2 (aO ^ p).property
  have htInt :
      (teichmuller F (residueMap F nO * z ^ p) : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2
      (teichmuller F (residueMap F nO * z ^ p)).property
  have hcoeff :
      n * a ^ p - (teichmuller F (residueMap F nO * z ^ p) : F) ∈
        lattice F 1 := by
    change ((nO * aO ^ p : ringOfIntegers F) : F) -
      ((teichmuller F (residueMap F nO * z ^ p) :
        ringOfIntegers F) : F) ∈ lattice F 1
    rw [← residueMap_eq_residueMap_iff]
    change residueMap F nO *
      (residueMap F (teichmuller F z)) ^ p = _
    rw [residueMap_teichmuller, residueMap_teichmuller]
  have hpiPow : piF ^ d ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, ord_pow, hpiFOrd]
    norm_num
  have hendpoint :
      norm F K x - piF ^ d *
          (teichmuller F (residueMap F nO * z ^ p) : F) ∈
        lattice F ((d + 1 : ℕ) : ℤ) := by
    have hmul0 := mul_mem_lattice F hpiPow hcoeff
    have hmul : piF ^ d *
        (n * a ^ p -
          (teichmuller F (residueMap F nO * z ^ p) : F)) ∈
        lattice F ((d + 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hmul0
    have hnorm : norm F K x = n * a ^ p * piF ^ d := by
      dsimp only [x, phaseReductionUpperSourceDisplacement, n, a, aO, piF, p]
      rw [map_mul, map_mul, norm_algebraMap, map_pow]
      ring
    rw [hnorm]
    convert hmul using 1
    ring
  have hsum := add_mem_lattice F hrem hendpoint
  change norm F K (1 + x) - 1 -
      norm F K (pi : K) ^ d *
        (teichmuller F
          (residueMap F nO * z ^ Module.finrank F K) : F) ∈ _
  simpa only [p, piF] using (by
    convert hsum using 1
    ring)

/-- In the strict-low row, the norm-character argument is already one
step beyond its actual critical depth, hence its residual class is zero. -/
theorem phaseReductionLowStrictTauPolynomial_deep
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t d dTau a : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hstrict : 2 * d < t)
    (htau : t = 2 * dTau) (ha : a + 2 * d = t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : K) (hu : ord K u = ((a : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    normPolynomialValue F K
        (u * phaseReductionUpperSourceDisplacement F K pi d z) ∈
      lattice F ((dTau + 1 : ℕ) : ℤ) := by
  let q := a + d
  have hq : q ≤ t + 1 := by dsimp only [q]; omega
  have hqDeep : dTau + 1 ≤ q := by dsimp only [q]; omega
  have hx : ((q : ℕ) : WithTop ℤ) ≤
      ord K (u * phaseReductionUpperSourceDisplacement F K pi d z) := by
    rw [ord_mul, hu]
    have hz := phaseReductionUpperSourceDisplacement_mem F K pi hpi d z
    rw [mem_lattice] at hz
    change (((a + d : ℕ) : ℤ) : WithTop ℤ) ≤ _
    simpa only [Nat.cast_add, WithTop.coe_add, add_comm] using
      add_le_add_left hz ((a : ℤ) : WithTop ℤ)
  have hchar := residueCharacteristic_eq_degree_of_positive_break
    F K ht htpos pi hpi hgen
  have hP := wild_norm_one_add_sub_one_mem_lattice F K ht htpos hq hres
    hchar pi hpi hgen _ hx
  apply lattice_antitone F (m := ((dTau + 1 : ℕ) : ℤ))
    (n := (q : ℤ))
  · exact_mod_cast hqDeep
  · exact hP

/-- The integer-depth comparison needed for the strict-high residual row.
It is stated independently because both the base and norm-character rows use
the same conductor arithmetic. -/
theorem phaseReductionHighClassDepthArithmetic
    (p t T d dK v : ℕ)
    (hp3 : 3 ≤ p) (htpos : 0 < t) (hT : T = t + 1)
    (hm : 2 * d + 1 = T + v) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + p * v) :
    d + 1 ≤ dK ∧
      p * (d + 1) ≤ dK + (p - 1) * T := by
  have hp1 : 1 ≤ p := by omega
  have hprod : 2 ≤ (p - 1) * t := by
    calc
      2 = 2 * 1 := by omega
      _ ≤ (p - 1) * t := Nat.mul_le_mul (by omega) htpos
  constructor
  · nlinarith
  · have hmZ : 2 * (d : ℤ) + 1 = (T : ℤ) + (v : ℤ) := by
      exact_mod_cast hm
    have hmKZ : 2 * (dK : ℤ) + 1 =
        (T : ℤ) + (p : ℤ) * (v : ℤ) := by
      exact_mod_cast hmK
    have hTZ : (T : ℤ) = (t : ℤ) + 1 := by exact_mod_cast hT
    have hprodZ : (2 : ℤ) ≤ ((p - 1) * t : ℕ) := by
      exact_mod_cast hprod
    have hgoalZ :
        (p : ℤ) * ((d : ℤ) + 1) ≤
          (dK : ℤ) + ((p : ℤ) - 1) * (T : ℤ) := by
      push_cast at hprodZ
      nlinarith
    exact_mod_cast hgoalZ

/-- Any upper field element at the actual high stationary depth has
norm-polynomial value one step beyond the lower base critical depth.  This
order-form statement applies directly to the source-tied Teichmuller lift;
it does not identify that lift with a separately chosen representative. -/
theorem phaseReductionHighBasePolynomial_deep_of_order
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T d dK v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hT : T = t + 1)
    (hm : 2 * d + 1 = T + v) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K) (hx : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x) :
    normPolynomialValue F K x ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  have hpPrime : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp3 : 3 ≤ p := by
    have hp2 := hpPrime.two_le
    by_contra h
    have hpEq : p = 2 := by omega
    have hoddp : Odd p := by simpa only [p] using hodd
    rw [hpEq] at hoddp
    norm_num at hoddp
  have harith := phaseReductionHighClassDepthArithmetic p t T d dK v hp3 htpos
    hT hm hv (by simpa only [p] using hmK)
  have hchar : residueCharacteristic F = p := by
    simpa only [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  have htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ) := by
    have h0 := traceIdealLowerBound_of_integralGenerator
      F K ht hres pi hpi hgen
    simpa only [p, hT] using h0
  rw [normPolynomialValue_eq_sum_elementarySymmetric]
  apply sum_mem_lattice F
  intro j hj
  simp only [Finset.mem_range] at hj
  by_cases htop : j + 1 = p
  · rw [htop, show p = Module.finrank F K by rfl,
      elementarySymmetric_finrank, mem_lattice, ord_norm, hres, one_nsmul]
    exact (show (((d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (((dK : ℕ) : ℤ) : WithTop ℤ) by
          exact_mod_cast harith.1).trans hx
  · have hjpos : 1 ≤ j + 1 := by omega
    have hjlt : j + 1 < p := by omega
    have hbound := wild_elementarySymmetric_bound F K p T (dK : ℤ)
      hpPrime (by omega) hchar rfl htrace hx hjpos hjlt
    rw [mem_lattice]
    apply (show (((d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (((((j + 1 : ℕ) : ℤ) * (dK : ℤ) +
          (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) :
            WithTop ℤ) by
      rw [WithTop.coe_le_coe, Int.le_ediv_iff_mul_le
        (by exact_mod_cast hpPrime.pos)]
      have hjmono : dK ≤ (j + 1) * dK :=
        Nat.le_mul_of_pos_left dK hjpos
      have hnat : p * (d + 1) ≤
          (j + 1) * dK + (p - 1) * T :=
        harith.2.trans (Nat.add_le_add_right hjmono ((p - 1) * T))
      exact_mod_cast (by simpa [mul_comm] using hnat)).trans
    exact hbound

/-- In the strict-high row, the norm-polynomial value of an upper source
displacement lies one step beyond the base critical depth. -/
theorem phaseReductionHighBasePolynomial_deep
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T d dK v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hT : T = t + 1)
    (hm : 2 * d + 1 = T + v) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    normPolynomialValue F K
        (phaseReductionUpperSourceDisplacement F K pi dK z) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  have hpPrime : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp3 : 3 ≤ p := by
    have hp2 := hpPrime.two_le
    by_contra h
    have hpEq : p = 2 := by omega
    have hoddp : Odd p := by simpa only [p] using hodd
    rw [hpEq] at hoddp
    norm_num at hoddp
  have harith := phaseReductionHighClassDepthArithmetic p t T d dK v hp3 htpos
    hT hm hv (by simpa only [p] using hmK)
  have hchar : residueCharacteristic F = p := by
    simpa only [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  have hram : ramificationIndex F K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  have htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ) := by
    have h0 := traceIdealLowerBound_of_integralGenerator
      F K ht hres pi hpi hgen
    simpa only [p, hT] using h0
  let x : K := phaseReductionUpperSourceDisplacement F K pi dK z
  have hx : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x := by
    simpa only [x, mem_lattice] using
      phaseReductionUpperSourceDisplacement_mem F K pi hpi dK z
  rw [normPolynomialValue_eq_sum_elementarySymmetric]
  apply sum_mem_lattice F
  intro j hj
  simp only [Finset.mem_range] at hj
  by_cases htop : j + 1 = p
  · rw [htop, show p = Module.finrank F K by rfl,
      elementarySymmetric_finrank, mem_lattice, ord_norm, hres, one_nsmul]
    exact (show (((d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (((dK : ℕ) : ℤ) : WithTop ℤ) by
          exact_mod_cast harith.1).trans hx
  · have hjpos : 1 ≤ j + 1 := by omega
    have hjlt : j + 1 < p := by omega
    have hbound := wild_elementarySymmetric_bound F K p T (dK : ℤ)
      hpPrime (by omega) hchar rfl htrace hx hjpos hjlt
    rw [mem_lattice]
    apply (show (((d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (((((j + 1 : ℕ) : ℤ) * (dK : ℤ) +
          (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) :
            WithTop ℤ) by
      rw [WithTop.coe_le_coe, Int.le_ediv_iff_mul_le
        (by exact_mod_cast hpPrime.pos)]
      have hjmono : dK ≤ (j + 1) * dK :=
        Nat.le_mul_of_pos_left dK hjpos
      have hnat : p * (d + 1) ≤
          (j + 1) * dK + (p - 1) * T :=
        harith.2.trans (Nat.add_le_add_right hjmono ((p - 1) * T))
      exact_mod_cast (by simpa [mul_comm] using hnat)).trans
    exact hbound

/-- The quotient residual class of the strict-high base row is zero. -/
theorem phaseReductionHighBaseResidualClass_zero
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T d dK v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hT : T = t + 1)
    (hm : 2 * d + 1 = T + v) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    let piF := phaseReductionLowerUniformizer F K pi hpi
    let y : lattice F (d : ℤ) :=
      ⟨normPolynomialValue F K
          (phaseReductionUpperSourceDisplacement F K pi dK z),
        lattice_antitone F (by omega)
          (phaseReductionHighBasePolynomial_deep F K ht htpos hT hm hv hmK
            hodd hres pi hpi hgen z)⟩
    phaseReductionResidualClass F piF
      (phaseReductionLowerUniformizer_order F K hres pi hpi) d y = 0 := by
  dsimp only
  apply phaseReductionResidualClass_eq_zero_of_mem_succ F
    (phaseReductionLowerUniformizer F K pi hpi)
    (phaseReductionLowerUniformizer_order F K hres pi hpi) d
  exact phaseReductionHighBasePolynomial_deep F K ht htpos hT hm hv hmK hodd
    hres pi hpi hgen z

/-- For every parity of the lower break, multiplying an actual upper-depth
source lift by an element of order `-v` puts the norm polynomial at the
post-drop norm-character depth `(t+2)/2`. -/
theorem phaseReductionHighTauPolynomial_deep_of_order
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T dK v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hT : T = t + 1) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u x : K) (hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (hx0 : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x) :
    normPolynomialValue F K (u * x) ∈
      lattice F ((((t + 2) / 2 : ℕ) : ℤ)) := by
  let p := Module.finrank F K
  have hpPrime : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp3 : 3 ≤ p := by
    have hp2 := hpPrime.two_le
    by_contra h
    have hpEq : p = 2 := by omega
    have hoddp : Odd p := by simpa only [p] using hodd
    rw [hpEq] at hoddp
    norm_num at hoddp
  have hpmod : p % 2 = 1 := by
    exact Nat.odd_iff.mp (by simpa only [p] using hodd)
  have hsumMod : (t + p * v) % 2 = 0 := by
    rw [← show 2 * dK = t + p * v by
      change 2 * dK + 1 = T + p * v at hmK
      omega]
    omega
  have hpar : t % 2 = v % 2 := by
    rw [Nat.add_mod, Nat.mul_mod, hpmod] at hsumMod
    have htmod := Nat.mod_lt t (by omega : 0 < 2)
    have hvmod := Nat.mod_lt v (by omega : 0 < 2)
    omega
  have hceil : 2 * ((t + 2) / 2) ≤ t + v := by
    have htmod := Nat.mod_lt t (by omega : 0 < 2)
    have hvmod := Nat.mod_lt v (by omega : 0 < 2)
    omega
  have hpv : 3 * v ≤ p * v := Nat.mul_le_mul_right v hp3
  have hmK' : 2 * dK = t + p * v := by
    change 2 * dK + 1 = T + p * v at hmK
    omega
  have hdepth : (t + 2) / 2 + v ≤ dK := by omega
  have hx : (((((t + 2) / 2 : ℕ) : ℤ)) : WithTop ℤ) ≤
      ord K (u * x) := by
    rw [ord_mul, hu]
    have hdepthZ : (((t + 2) / 2 : ℕ) : ℤ) ≤
        -(v : ℤ) + (dK : ℤ) := by
      have hz : (((t + 2) / 2 : ℕ) : ℤ) + (v : ℤ) ≤ (dK : ℤ) := by
        exact_mod_cast hdepth
      linarith
    calc
      (((((t + 2) / 2 : ℕ) : ℤ)) : WithTop ℤ) ≤
          (((-(v : ℤ) + (dK : ℤ)) : ℤ) : WithTop ℤ) :=
        WithTop.coe_le_coe.mpr hdepthZ
      _ = ((-(v : ℤ) : ℤ) : WithTop ℤ) +
          (((dK : ℕ) : ℤ) : WithTop ℤ) := by norm_num
      _ ≤ ((-(v : ℤ) : ℤ) : WithTop ℤ) + ord K x :=
        by simpa only [add_comm] using
          add_le_add_left hx0 (((-(v : ℤ) : ℤ) : WithTop ℤ))
  have hi : (t + 2) / 2 ≤ t + 1 := by omega
  exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos hi hres
    (residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen) pi hpi hgen _ hx

/-- In the strict-high row, the norm-character source displacement is also
one step beyond its critical depth. -/
theorem phaseReductionHighTauPolynomial_deep
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T d dK dTau v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hT : T = t + 1) (htau : t = 2 * dTau)
    (hm : 2 * d + 1 = T + v) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : K) (hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    normPolynomialValue F K
        (u * phaseReductionUpperSourceDisplacement F K pi dK z) ∈
      lattice F ((dTau + 1 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  have hpPrime : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp3 : 3 ≤ p := by
    have hp2 := hpPrime.two_le
    by_contra h
    have hpEq : p = 2 := by omega
    have hoddp : Odd p := by simpa only [p] using hodd
    rw [hpEq] at hoddp
    norm_num at hoddp
  have hdepth : dTau + 1 + v ≤ dK := by
    have hmK' : 2 * dK = t + p * v := by
      change 2 * dK + 1 = T + p * v at hmK
      omega
    have htwo : 2 * (dTau + v) + 1 ≤ 2 * dK := by
      rw [hmK', htau]
      nlinarith
    omega
  have hx0 := phaseReductionUpperSourceDisplacement_mem F K pi hpi dK z
  rw [mem_lattice] at hx0
  have hx : ((((dTau + 1 : ℕ) : ℤ)) : WithTop ℤ) ≤
      ord K (u * phaseReductionUpperSourceDisplacement F K pi dK z) := by
    rw [ord_mul, hu]
    have hdepthZ : (dTau + 1 : ℤ) ≤ -(v : ℤ) + (dK : ℤ) := by
      have hz : ((dTau + 1 + v : ℕ) : ℤ) ≤ (dK : ℤ) := by
        exact_mod_cast hdepth
      push_cast at hz
      linarith
    calc
      ((((dTau + 1 : ℕ) : ℤ)) : WithTop ℤ) ≤
          (((-(v : ℤ) + (dK : ℤ)) : ℤ) : WithTop ℤ) :=
        WithTop.coe_le_coe.mpr hdepthZ
      _ = ((-(v : ℤ) : ℤ) : WithTop ℤ) +
          (((dK : ℕ) : ℤ) : WithTop ℤ) := by norm_num
      _ ≤ ((-(v : ℤ) : ℤ) : WithTop ℤ) +
          ord K (phaseReductionUpperSourceDisplacement F K pi dK z) :=
        by simpa only [add_comm] using
          add_le_add_left hx0 (((-(v : ℤ) : ℤ) : WithTop ℤ))
  have hi : dTau + 1 ≤ t + 1 := by omega
  exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos hi hres
    (residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen) pi hpi hgen _ hx

/-- The quotient residual class of the strict-high norm-character row is
zero. -/
theorem phaseReductionHighTauResidualClass_zero
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T d dK dTau v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hT : T = t + 1) (htau : t = 2 * dTau)
    (hm : 2 * d + 1 = T + v) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : K) (hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (z : ResidueField F) :
    let piF := phaseReductionLowerUniformizer F K pi hpi
    let y : lattice F (dTau : ℤ) :=
      ⟨normPolynomialValue F K
          (u * phaseReductionUpperSourceDisplacement F K pi dK z),
        lattice_antitone F (by omega)
          (phaseReductionHighTauPolynomial_deep F K ht htpos hT htau hm hv
            hmK hodd hres pi hpi hgen u hu z)⟩
    phaseReductionResidualClass F piF
      (phaseReductionLowerUniformizer_order F K hres pi hpi) dTau y = 0 := by
  dsimp only
  apply phaseReductionResidualClass_eq_zero_of_mem_succ F
    (phaseReductionLowerUniformizer F K pi hpi)
    (phaseReductionLowerUniformizer_order F K hres pi hpi) dTau
  exact phaseReductionHighTauPolynomial_deep F K ht htpos hT htau hm hv hmK
    hodd hres pi hpi hgen u hu z

/-- Exact multiplicative/additive-character identity behind the odd
source-coordinate transport.  The norm character disappears only on the
displayed value in the actual norm range. -/
theorem phaseReductionExactCriticalTransport_characterIdentity
    (F K : Type*)
    [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsModuleTopology F K]
    (psiF : ContinuousAddChar F) (psiK : ContinuousAddChar K)
    (chiF : ContinuousQuasiChar F) (chiK : ContinuousQuasiChar K)
    (tau : NormCharacter F K)
    (hpsi : psiK = psiF.compTrace)
    (hchi : chiK = chiF.compNorm)
    (A n : F) (u x : K)
    (onePlusX onePlusUx : Kˣ) :
    (psiF (A * n * phaseReductionNormPolynomial F K x) *
          (chiF (normUnits F K onePlusX))⁻¹) *
        (psiF (A * phaseReductionNormPolynomial F K (u * x)) *
          (tau.1 (normUnits F K onePlusUx))⁻¹)⁻¹ *
        psiF (A *
          (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x)) =
      psiK
          (algebraMap F K A * (algebraMap F K n - u) * x) *
        (chiK onePlusX)⁻¹ := by
  have htraceScalar (a : F) (z : K) :
      trace F K (algebraMap F K a * z) = a * trace F K z := by
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul a z
  have harg :
      A * n * phaseReductionNormPolynomial F K x -
          A * phaseReductionNormPolynomial F K (u * x) +
          A * (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x) =
        trace F K
          (algebraMap F K A * (algebraMap F K n - u) * x) := by
    calc
      _ = A * n * trace F K x - A * trace F K (u * x) := by
        simp only [phaseReductionNormHigherPart]
        ring
      _ = trace F K
          (algebraMap F K (A * n) * x -
            algebraMap F K A * (u * x)) := by
        rw [map_sub, htraceScalar, htraceScalar]
      _ = trace F K
          (algebraMap F K A * (algebraMap F K n - u) * x) := by
        congr 1
        push_cast
        ring
  have hadd :
      psiF (A * n * phaseReductionNormPolynomial F K x) *
          (psiF (A * phaseReductionNormPolynomial F K (u * x)))⁻¹ *
          psiF (A *
            (phaseReductionNormHigherPart F K (u * x) -
              n * phaseReductionNormHigherPart F K x)) =
        psiF
          (trace F K
            (algebraMap F K A * (algebraMap F K n - u) * x)) := by
    have hsub :
        psiF
            (A * n * phaseReductionNormPolynomial F K x -
              A * phaseReductionNormPolynomial F K (u * x)) =
          psiF (A * n * phaseReductionNormPolynomial F K x) *
            (psiF (A * phaseReductionNormPolynomial F K (u * x)))⁻¹ := by
      rw [sub_eq_add_neg, ContinuousAddChar.map_add_eq_mul]
      congr 1
      exact AddChar.map_neg_eq_inv psiF.toAddChar _
    calc
      _ = psiF
          (A * n * phaseReductionNormPolynomial F K x -
            A * phaseReductionNormPolynomial F K (u * x)) *
          psiF (A *
            (phaseReductionNormHigherPart F K (u * x) -
              n * phaseReductionNormHigherPart F K x)) := by
        rw [hsub]
      _ = psiF
          ((A * n * phaseReductionNormPolynomial F K x -
              A * phaseReductionNormPolynomial F K (u * x)) +
            A * (phaseReductionNormHigherPart F K (u * x) -
              n * phaseReductionNormHigherPart F K x)) := by
        exact (ContinuousAddChar.map_add_eq_mul psiF _ _).symm
      _ = _ := congrArg psiF harg
  have htau : tau.1 (normUnits F K onePlusUx) = 1 :=
    NormCharacter.eq_one_on_normRange F K tau _ ⟨onePlusUx, rfl⟩
  rw [hpsi, hchi, ContinuousAddChar.compTrace_apply,
    ContinuousQuasiChar.compNorm_apply, htau]
  simp only [inv_one, mul_one]
  change
    (psiF (A * n * phaseReductionNormPolynomial F K x) *
          (chiF (normUnits F K onePlusX))⁻¹) *
        (psiF (A * phaseReductionNormPolynomial F K (u * x)))⁻¹ *
        psiF (A *
          (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x)) =
      psiF
          (trace F K
            (algebraMap F K A * (algebraMap F K n - u) * x)) *
        (chiF (normUnits F K onePlusX))⁻¹
  rw [← hadd]
  ac_rfl

/-- Relational form of the exact critical transport.  The three ratios are
literal stationary numerator/denominator ratios, and every unit argument is
tied to `x`, `P(x)`, or `P(u*x)`. -/
theorem phaseReductionExactCriticalTransport_of_stationaryRatios
    (F K : Type*)
    [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsModuleTopology F K]
    (psiF : ContinuousAddChar F) (psiK : ContinuousAddChar K)
    (chiF : ContinuousQuasiChar F) (chiK : ContinuousQuasiChar K)
    (tau : NormCharacter F K)
    (hpsi : psiK = psiF.compTrace)
    (hchi : chiK = chiF.compNorm)
    (A n : F) (u x : K)
    (hn : norm F K u = n)
    (tauRatio baseRatio : F) (upperRatio : K)
    (hTauRatio : tauRatio = A)
    (hBaseRatio : baseRatio = A * n)
    (hUpperRatio : upperRatio =
      algebraMap F K A * (algebraMap F K n - u))
    (upperUnit upperUxUnit : Kˣ) (baseUnit tauUnit : Fˣ)
    (hUpperUnit : (upperUnit : K) = 1 + x)
    (hUpperUxUnit : (upperUxUnit : K) = 1 + u * x)
    (hBaseUnit : (baseUnit : F) =
      1 + phaseReductionNormPolynomial F K x)
    (hTauUnit : (tauUnit : F) =
      1 + phaseReductionNormPolynomial F K (u * x)) :
    (psiF (baseRatio * phaseReductionNormPolynomial F K x) *
          (chiF baseUnit)⁻¹) *
        (psiF (tauRatio * phaseReductionNormPolynomial F K (u * x)) *
          (tau.1 tauUnit)⁻¹)⁻¹ *
        psiF (A *
          (phaseReductionNormHigherPart F K (u * x) -
            n * phaseReductionNormHigherPart F K x)) =
      psiK (upperRatio * x) * (chiK upperUnit)⁻¹ := by
  subst n
  have hBaseNorm : baseUnit = normUnits F K upperUnit := by
    apply Units.ext
    rw [coe_normUnits, hBaseUnit, hUpperUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  have hTauNorm : tauUnit = normUnits F K upperUxUnit := by
    apply Units.ext
    rw [coe_normUnits, hTauUnit, hUpperUxUnit]
    simp only [phaseReductionNormPolynomial]
    ring
  rw [hTauRatio, hBaseRatio, hUpperRatio, hBaseNorm, hTauNorm]
  exact phaseReductionExactCriticalTransport_characterIdentity F K psiF psiK
    chiF chiK tau hpsi hchi A (norm F K u) u x upperUnit upperUxUnit

/-- Exact complete-function multiplication at one common critical
coordinate.  The product character and the literal sum representative are
both used before any coefficient extraction. -/
theorem criticalPolarFunction_mul_of_literal_sum
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi chi₁ chi₂ : LocalQuasiCharData E)
    (psi : LocalAddCharData E)
    (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hm₁ : chi₁.conductor = 2 * d + 1)
    (hm₂ : chi₂.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (hlarge₁ : 1 < chi₁.conductor)
    (hlarge₂ : 1 < chi₂.conductor)
    (hchar : chi.character = chi₁.character * chi₂.character)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma₁ : ord E (gamma : E) =
      (((chi₁.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma₂ : ord E (gamma : E) =
      (((chi₂.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta₁ : lattice E ((chi₁.conductor : ℤ) - (chi₁.conductor : ℤ)))
    (beta₂ : lattice E ((chi₂.conductor : ℤ) - (chi₂.conductor : ℤ)))
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : (beta : E) = (beta₁ : E) + (beta₂ : E))
    (x : ResidueField E) :
    criticalPolarFunction E chi psi d hm hlarge ⟨gamma, hgamma⟩
        delta hdelta beta x =
      criticalPolarFunction E chi₁ psi d hm₁ hlarge₁ ⟨gamma, hgamma₁⟩
          delta hdelta beta₁ x *
        criticalPolarFunction E chi₂ psi d hm₂ hlarge₂ ⟨gamma, hgamma₂⟩
          delta hdelta beta₂ x := by
  unfold criticalPolarFunction criticalPolarValue
  rw [hchar, ContinuousQuasiChar.mul_apply]
  have hu₁ :
      criticalPolarUnit E chi d hm hlarge delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
        criticalPolarUnit E chi₁ d hm₁ hlarge₁ delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hu₂ :
      criticalPolarUnit E chi d hm hlarge delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
        criticalPolarUnit E chi₂ d hm₂ hlarge₂ delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hchi₁ := congrArg
    (fun u : unitFiltration E d ↦ chi₁.character (u : Eˣ)) hu₁
  have hchi₂ := congrArg
    (fun u : unitFiltration E d ↦ chi₂.character (u : Eˣ)) hu₂
  have hpsi :
      psi.character
          ((beta : E) * (delta : E) * (teichmuller E x : E) /
            (gamma : E)) =
        psi.character
            ((beta₁ : E) * (delta : E) * (teichmuller E x : E) /
              (gamma : E)) *
          psi.character
            ((beta₂ : E) * (delta : E) * (teichmuller E x : E) /
              (gamma : E)) := by
    rw [← psi.character.map_add_eq_mul]
    congr 1
    rw [hbeta]
    ring
  rw [hpsi, hchi₁, hchi₂]
  push_cast
  rw [mul_inv]
  ring

/-- If a secondary character is stationary-linearized on the common
critical coordinate, multiplying it into the dominant row and adding its
literal stationary numerator does not change the complete function.  The
secondary character retains its own, possibly smaller, conductor. -/
theorem criticalPolarFunction_eq_of_linearized_factor
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi chi₁ : LocalQuasiCharData E)
    (theta₂ : ContinuousQuasiChar E) (psi : LocalAddCharData E)
    (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hm₁ : chi₁.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) (hlarge₁ : 1 < chi₁.conductor)
    (hchar : chi.character = chi₁.character * theta₂)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma₁ : ord E (gamma : E) =
      (((chi₁.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta₁ : lattice E
      ((chi₁.conductor : ℤ) - (chi₁.conductor : ℤ)))
    (beta : lattice E
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (beta₂ : E) (hbeta : (beta : E) = (beta₁ : E) + beta₂)
    (hlinear : ∀ x : ResidueField E,
      (theta₂
          (criticalPolarUnit E chi₁ d hm₁ hlarge₁ delta hdelta
            (teichmuller E x : E)
            ((mem_lattice_zero_iff E).2
              (teichmuller E x).property) : Eˣ) : ℂ) =
        (psi.character
          (beta₂ * (delta : E) * (teichmuller E x : E) /
            (gamma : E)) : ℂ))
    (x : ResidueField E) :
    criticalPolarFunction E chi psi d hm hlarge ⟨gamma, hgamma⟩
        delta hdelta beta x =
      criticalPolarFunction E chi₁ psi d hm₁ hlarge₁ ⟨gamma, hgamma₁⟩
        delta hdelta beta₁ x := by
  unfold criticalPolarFunction criticalPolarValue
  rw [hchar, ContinuousQuasiChar.mul_apply]
  have hu :
      criticalPolarUnit E chi d hm hlarge delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
        criticalPolarUnit E chi₁ d hm₁ hlarge₁ delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hchi₁ := congrArg
    (fun u : unitFiltration E d ↦ (chi₁.character (u : Eˣ) : ℂ)) hu
  have htheta₂ := congrArg
    (fun u : unitFiltration E d ↦ (theta₂ (u : Eˣ) : ℂ)) hu
  have hpsi :
      (psi.character
          ((beta : E) * (delta : E) * (teichmuller E x : E) /
            (gamma : E)) : ℂ) =
        (psi.character
            ((beta₁ : E) * (delta : E) * (teichmuller E x : E) /
              (gamma : E)) : ℂ) *
          (psi.character
            (beta₂ * (delta : E) * (teichmuller E x : E) /
              (gamma : E)) : ℂ) := by
    have hpsiUnits :
        psi.character
            ((beta : E) * (delta : E) * (teichmuller E x : E) /
              (gamma : E)) =
          psi.character
              ((beta₁ : E) * (delta : E) * (teichmuller E x : E) /
                (gamma : E)) *
            psi.character
              (beta₂ * (delta : E) * (teichmuller E x : E) /
                (gamma : E)) := by
      rw [← psi.character.map_add_eq_mul]
      congr 1
      rw [hbeta]
      ring
    simpa only [Units.val_mul] using
      congrArg (fun u : ℂˣ ↦ (u : ℂ)) hpsiUnits
  rw [hpsi]
  push_cast
  rw [hchi₁, htheta₂, hlinear x]
  rw [mul_inv]
  field_simp [ContinuousAddChar.apply_ne_zero,
    ContinuousQuasiChar.apply_ne_zero]

/-- Literal scaling of a stationary numerator by `j`, together with the
actual character power, raises the complete critical function pointwise to
the `j`th power in the unchanged common coordinate. -/
theorem criticalPolarFunction_pow_of_literal_nsmul
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi chiPow : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d j : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hmPow : chiPow.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) (hlargePow : 1 < chiPow.conductor)
    (hchar : chiPow.character = chi.character ^ j)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgammaPow : ord E (gamma : E) =
      (((chiPow.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice E
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (betaPow : lattice E
      ((chiPow.conductor : ℤ) - (chiPow.conductor : ℤ)))
    (hbeta : (betaPow : E) = (j : E) * (beta : E))
    (x : ResidueField E) :
    criticalPolarFunction E chiPow psi d hmPow hlargePow
        ⟨gamma, hgammaPow⟩ delta hdelta betaPow x =
      (criticalPolarFunction E chi psi d hm hlarge ⟨gamma, hgamma⟩
        delta hdelta beta x) ^ j := by
  unfold criticalPolarFunction criticalPolarValue
  rw [hchar, ContinuousQuasiChar.pow_apply]
  have hu :
      criticalPolarUnit E chiPow d hmPow hlargePow delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
        criticalPolarUnit E chi d hm hlarge delta hdelta
          (teichmuller E x : E)
          ((mem_lattice_zero_iff E).2 (teichmuller E x).property) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hchi := congrArg
    (fun u : unitFiltration E d ↦ (chi.character (u : Eˣ) : ℂ)) hu
  have hpsi :
      (psi.character
          ((betaPow : E) * (delta : E) * (teichmuller E x : E) /
            (gamma : E)) : ℂ) =
        (psi.character
          ((beta : E) * (delta : E) * (teichmuller E x : E) /
            (gamma : E)) : ℂ) ^ j := by
    rw [hbeta]
    have harg :
        (j : E) * (beta : E) * (delta : E) *
              (teichmuller E x : E) / (gamma : E) =
          j • ((beta : E) * (delta : E) *
              (teichmuller E x : E) / (gamma : E)) := by
      simp only [nsmul_eq_mul]
      ring
    rw [harg]
    exact congrArg (fun u : ℂˣ ↦ (u : ℂ))
      (AddChar.map_nsmul_eq_pow psi.character.toAddChar j _)
  rw [hpsi]
  push_cast
  rw [hchi]
  rw [← inv_pow, ← mul_pow]

namespace CriticalPolarFunction

universe u v

/-- Transport a complete positive-polar function across an exact residue
field equivalence.  The orientation is `reindex phi e y = phi (e⁻¹ y)`, so
both coefficients move forward through `e`. -/
noncomputable def reindex
    {k : Type u} {l : Type v} [Field k] [Field l]
    {psiK : FiniteAddChar k} {psiL : FiniteAddChar l} {A : k}
    (phi : CriticalPolarFunction k psiK A)
    (e : k ≃+* l) (hpsi : ∀ x, psiL (e x) = psiK x) :
    CriticalPolarFunction l psiL (e A) where
  toFun y := phi (e.symm y)
  ne_zero' y := phi.ne_zero _
  map_add' x y := by
    rw [e.symm.map_add, phi.map_add]
    congr 1
    rw [← hpsi (A * (e.symm x * e.symm y))]
    congr 1
    simp

@[simp]
theorem reindex_apply
    {k : Type u} {l : Type v} [Field k] [Field l]
    {psiK : FiniteAddChar k} {psiL : FiniteAddChar l} {A : k}
    (phi : CriticalPolarFunction k psiK A)
    (e : k ≃+* l) (hpsi : ∀ x, psiL (e x) = psiK x) (y : l) :
    reindex phi e hpsi y = phi (e.symm y) :=
  rfl

/-- Cross-field reindexing carries the complete affine/polar pair as
`(A,B) ↦ (e A,e B)`. -/
theorem affineCoefficient_reindex
    {k : Type u} {l : Type v} [Field k] [Field l]
    [Fintype k] [Fintype l]
    {psiK : FiniteAddChar k} {psiL : FiniteAddChar l} {A : k}
    (hcharK : ringChar k ≠ 2) (hcharL : ringChar l ≠ 2)
    (hpsiK : psiK ≠ 1) (hpsiL : psiL ≠ 1)
    (phi : CriticalPolarFunction k psiK A)
    (e : k ≃+* l) (hpsi : ∀ x, psiL (e x) = psiK x) :
    (reindex phi e hpsi).affineCoefficient hcharL hpsiL =
      e (phi.affineCoefficient hcharK hpsiK) := by
  apply CriticalPolarFunction.affineCoefficient_unique hcharL hpsiL
  intro y
  rw [reindex_apply, phi.eq_quadratic hcharK hpsiK]
  rw [← hpsi]
  congr 1
  rw [e.map_add, e.map_mul, map_div₀, e.map_pow, e.map_mul]
  rw [show e (2 : k) = (2 : l) by exact map_ofNat e 2]
  simp

/-- Reindexing preserves the complete finite sum. -/
theorem sum_reindex
    {k : Type u} {l : Type v} [Field k] [Field l]
    [Fintype k] [Fintype l]
    {psiK : FiniteAddChar k} {psiL : FiniteAddChar l} {A : k}
    (phi : CriticalPolarFunction k psiK A)
    (e : k ≃+* l) (hpsi : ∀ x, psiL (e x) = psiK x) :
    (∑ y : l, reindex phi e hpsi y) = ∑ x : k, phi x :=
  e.symm.toEquiv.sum_comp phi

/-- Hence cross-field coordinate transport preserves the phase of the
complete critical sum. -/
theorem phase_sum_reindex
    {k : Type u} {l : Type v} [Field k] [Field l]
    [Fintype k] [Fintype l]
    {psiK : FiniteAddChar k} {psiL : FiniteAddChar l} {A : k}
    (phi : CriticalPolarFunction k psiK A)
    (e : k ≃+* l) (hpsi : ∀ x, psiL (e x) = psiK x) :
    phase (∑ y : l, reindex phi e hpsi y) =
      phase (∑ x : k, phi x) := by
  rw [sum_reindex]

end CriticalPolarFunction

namespace PhaseReductionResidualTransport

universe u v

/-- Put an actual upper critical function into the common lower residue
coordinate using only the canonical residue equivalence and compatibility of
the already normalized additive characters. -/
noncomputable def upperInLowerCoordinate
    {kF : Type u} {kK : Type v} [Field kF] [Field kK]
    {psiF : FiniteAddChar kF} {psiK : FiniteAddChar kK} {A : kK}
    (e : kF ≃+* kK) (hpsi : ∀ x, psiK (e x) = psiF x)
    (phi : CriticalPolarFunction kK psiK A) :
    CriticalPolarFunction kF psiF (e.symm A) :=
  CriticalPolarFunction.reindex phi e.symm
    (fun y ↦ by simpa using (hpsi (e.symm y)).symm)

@[simp]
theorem upperInLowerCoordinate_apply
    {kF : Type u} {kK : Type v} [Field kF] [Field kK]
    {psiF : FiniteAddChar kF} {psiK : FiniteAddChar kK} {A : kK}
    (e : kF ≃+* kK) (hpsi : ∀ x, psiK (e x) = psiF x)
    (phi : CriticalPolarFunction kK psiK A) (x : kF) :
    upperInLowerCoordinate e hpsi phi x = phi (e x) := by
  rfl

/-- Cross-field transport takes the upper affine coefficient through the
canonical inverse residue equivalence, with the same direction as the polar
coefficient. -/
theorem upperInLowerCoordinate_affineCoefficient
    {kF : Type u} {kK : Type v} [Field kF] [Field kK]
    [Fintype kF] [Fintype kK]
    {psiF : FiniteAddChar kF} {psiK : FiniteAddChar kK} {A : kK}
    (hcharF : ringChar kF ≠ 2) (hcharK : ringChar kK ≠ 2)
    (hpsiF : psiF ≠ 1) (hpsiK : psiK ≠ 1)
    (e : kF ≃+* kK) (hpsi : ∀ x, psiK (e x) = psiF x)
    (phi : CriticalPolarFunction kK psiK A) :
    (upperInLowerCoordinate e hpsi phi).affineCoefficient hcharF hpsiF =
      e.symm (phi.affineCoefficient hcharK hpsiK) :=
  CriticalPolarFunction.affineCoefficient_reindex hcharK hcharF hpsiK
    hpsiF phi e.symm (fun y ↦ by simpa using (hpsi (e.symm y)).symm)

/-- Canonical `p`-power Frobenius on a finite field. -/
noncomputable def primeFrobeniusEquiv
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p] : k ≃+* k := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k).toRingEquiv

@[simp]
theorem primeFrobeniusEquiv_apply
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p] (x : k) :
    primeFrobeniusEquiv p k x = x ^ p := by
  change x ^ Fintype.card (ZMod p) = x ^ p
  rw [ZMod.card]

/-- The manuscript's displayed upper coordinate: first regard the natural
upper function in the common lower residue field, then reindex its argument
by inverse Frobenius.  The resulting polar coefficient is the forward
`p`th power, and no freely chosen residue scalar occurs. -/
noncomputable def displayedUpperReindex
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p]
    {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A)
    (hpsi : ∀ x, psi0 (x ^ p) = psi0 x) :
    CriticalPolarFunction k psi0 (primeFrobeniusEquiv p k A) :=
  CriticalPolarFunction.reindex phi (primeFrobeniusEquiv p k)
    (fun x ↦ by rw [primeFrobeniusEquiv_apply]; exact hpsi x)

@[simp]
theorem displayedUpperReindex_apply
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p]
    {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A)
    (hpsi : ∀ x, psi0 (x ^ p) = psi0 x) (z : k) :
    displayedUpperReindex p k phi hpsi z =
      phi ((primeFrobeniusEquiv p k).symm z) :=
  rfl

@[simp]
theorem displayedUpperReindex_polarCoefficient
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p] (A : k) :
    primeFrobeniusEquiv p k A = A ^ p :=
  primeFrobeniusEquiv_apply p k A

/-- In odd characteristic, inverse-Frobenius display moves the affine
coefficient forward by the same `p`th power. -/
theorem displayedUpperReindex_affineCoefficient
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p]
    {psi0 : FiniteAddChar k} {A : k}
    (hodd : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A)
    (hpsi : ∀ x, psi0 (x ^ p) = psi0 x) :
    (displayedUpperReindex p k phi hpsi).affineCoefficient hodd hpsi0 =
      (phi.affineCoefficient hodd hpsi0) ^ p := by
  change (CriticalPolarFunction.reindex phi (primeFrobeniusEquiv p k)
    _).affineCoefficient hodd hpsi0 = _
  rw [CriticalPolarFunction.affineCoefficient_reindex hodd hodd hpsi0 hpsi0]
  exact primeFrobeniusEquiv_apply p k _

theorem displayedUpperReindex_sum
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p]
    {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A)
    (hpsi : ∀ x, psi0 (x ^ p) = psi0 x) :
    (∑ z : k, displayedUpperReindex p k phi hpsi z) =
      ∑ z : k, phi z :=
  CriticalPolarFunction.sum_reindex phi (primeFrobeniusEquiv p k)
    (fun x ↦ by rw [primeFrobeniusEquiv_apply]; exact hpsi x)

theorem displayedUpperReindex_phase
    (p : ℕ) (k : Type u) [Field k] [Fintype k]
    [Fact p.Prime] [CharP k p]
    {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A)
    (hpsi : ∀ x, psi0 (x ^ p) = psi0 x) :
    phase (∑ z : k, displayedUpperReindex p k phi hpsi z) =
      phase (∑ z : k, phi z) := by
  rw [displayedUpperReindex_sum]

/-- Complete source-tied displayed upper function: canonical upper-to-lower
residue transport followed by the manuscript's inverse-Frobenius display.
The result type records the exact forward-`p` polar coefficient. -/
noncomputable def sourceTiedDisplayedUpper
    (p : ℕ) (kF : Type u) (kK : Type v)
    [Field kF] [Fintype kF] [Field kK]
    [Fact p.Prime] [CharP kF p]
    {psiF : FiniteAddChar kF} {psiK : FiniteAddChar kK} {A : kK}
    (e : kF ≃+* kK) (hpsi : ∀ x, psiK (e x) = psiF x)
    (hFrob : ∀ x, psiF (x ^ p) = psiF x)
    (phi : CriticalPolarFunction kK psiK A) :
    CriticalPolarFunction kF psiF
      (primeFrobeniusEquiv p kF (e.symm A)) :=
  displayedUpperReindex p kF (upperInLowerCoordinate e hpsi phi) hFrob

@[simp]
theorem sourceTiedDisplayedUpper_apply
    (p : ℕ) (kF : Type u) (kK : Type v)
    [Field kF] [Fintype kF] [Field kK]
    [Fact p.Prime] [CharP kF p]
    {psiF : FiniteAddChar kF} {psiK : FiniteAddChar kK} {A : kK}
    (e : kF ≃+* kK) (hpsi : ∀ x, psiK (e x) = psiF x)
    (hFrob : ∀ x, psiF (x ^ p) = psiF x)
    (phi : CriticalPolarFunction kK psiK A) (x : kF) :
    sourceTiedDisplayedUpper p kF kK e hpsi hFrob phi x =
      phi (e ((primeFrobeniusEquiv p kF).symm x)) :=
  rfl

@[simp]
theorem sourceTiedDisplayedUpper_polarCoefficient
    (p : ℕ) (kF : Type u) (kK : Type v)
    [Field kF] [Fintype kF] [Field kK]
    [Fact p.Prime] [CharP kF p] (e : kF ≃+* kK) (A : kK) :
    primeFrobeniusEquiv p kF (e.symm A) = (e.symm A) ^ p :=
  primeFrobeniusEquiv_apply p kF _

/-- The source-tied displayed upper affine coefficient is likewise the
forward `p`th power of the canonically transported natural coefficient. -/
theorem sourceTiedDisplayedUpper_affineCoefficient
    (p : ℕ) (kF : Type u) (kK : Type v)
    [Field kF] [Fintype kF] [Field kK] [Fintype kK]
    [Fact p.Prime] [CharP kF p]
    {psiF : FiniteAddChar kF} {psiK : FiniteAddChar kK} {A : kK}
    (hcharF : ringChar kF ≠ 2) (hcharK : ringChar kK ≠ 2)
    (hpsiF : psiF ≠ 1) (hpsiK : psiK ≠ 1)
    (e : kF ≃+* kK) (hpsi : ∀ x, psiK (e x) = psiF x)
    (hFrob : ∀ x, psiF (x ^ p) = psiF x)
    (phi : CriticalPolarFunction kK psiK A) :
    (sourceTiedDisplayedUpper p kF kK e hpsi hFrob phi).affineCoefficient
        hcharF hpsiF =
      (e.symm (phi.affineCoefficient hcharK hpsiK)) ^ p := by
  unfold sourceTiedDisplayedUpper
  rw [displayedUpperReindex_affineCoefficient p kF hcharF hpsiF]
  rw [upperInLowerCoordinate_affineCoefficient hcharF hcharK hpsiF hpsiK]

end PhaseReductionResidualTransport

/-! ### Actual upper rows in the common displayed coordinate -/

/-- The minimal residual additive-character normalization used to put the
actual upper and lower Lamprecht functions in one coordinate.  The upper
character is derived below; it is not an independently selectable field. -/
structure FrobeniusResidualAddCharData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) where
  lower : FiniteAddChar (ResidueField F)
  lower_ne_one : lower ≠ 1
  frobenius : ∀ x, lower (x ^ p) = lower x

namespace FrobeniusResidualAddCharData

variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  {p : ℕ}

/-- Pull the one fixed lower residual character through the canonical
residue equivalence. -/
noncomputable def upper
    (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1) :
    FiniteAddChar (ResidueField K) :=
  C.lower.compAddMonoidHom
    (PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) hres).symm.toAddMonoidHom

@[simp]
theorem upper_apply_equiv
    (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1) (x : ResidueField F) :
    C.upper hres
        (PhaseReductionResidualCoordinateSource.residueEquiv
          (F := F) (K := K) hres x) = C.lower x := by
  change C.lower
      ((PhaseReductionResidualCoordinateSource.residueEquiv
        (F := F) (K := K) hres).symm
        (PhaseReductionResidualCoordinateSource.residueEquiv
          (F := F) (K := K) hres x)) = C.lower x
  rw [RingEquiv.symm_apply_apply]

theorem upper_ne_one
    (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1) : C.upper hres ≠ 1 := by
  intro h
  apply C.lower_ne_one
  ext x
  rw [← C.upper_apply_equiv hres x, h]
  rfl

/-- The canonical `p`-power Frobenius, with primality and characteristic
derived from the local field and the supplied characteristic identity. -/
noncomputable def frobeniusEquiv
    (C : FrobeniusResidualAddCharData F p)
    (hchar : residueCharacteristic F = p) :
    ResidueField F ≃+* ResidueField F := by
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime F⟩
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  letI : Fintype (ResidueField F) := residueFieldFintype F
  exact PhaseReductionResidualTransport.primeFrobeniusEquiv p
    (ResidueField F)

@[simp]
theorem frobeniusEquiv_apply
    (C : FrobeniusResidualAddCharData F p)
    (hchar : residueCharacteristic F = p) (x : ResidueField F) :
    C.frobeniusEquiv hchar x = x ^ p := by
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime F⟩
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  letI : Fintype (ResidueField F) := residueFieldFintype F
  exact PhaseReductionResidualTransport.primeFrobeniusEquiv_apply p
    (ResidueField F) x

theorem lower_frobeniusEquiv
    (C : FrobeniusResidualAddCharData F p)
    (hchar : residueCharacteristic F = p) (x : ResidueField F) :
    C.lower (C.frobeniusEquiv hchar x) = C.lower x := by
  rw [C.frobeniusEquiv_apply hchar]
  exact C.frobenius x

end FrobeniusResidualAddCharData

namespace LocalLamprechtPhaseData

universe u v

section DisplayedInLowerCoordinate

variable {F : Type u} {K : Type v}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}

local instance : Fintype (ResidueField F) := residueFieldFintype F
local instance : Fintype (ResidueField K) := residueFieldFintype K

/-- An actual upper Lamprecht row in the common lower residue coordinate,
followed by the manuscript's inverse-Frobenius display. -/
noncomputable def displayedInLowerCoordinate
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (D : LocalLamprechtPhaseData K chiK psiK) :
    CriticalPolarFunction (ResidueField F) C.lower
      (C.frobeniusEquiv hchar
        ((PhaseReductionResidualCoordinateSource.residueEquiv
            (F := F) (K := K) hres).symm
          (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres)))) :=
  CriticalPolarFunction.reindex
    (PhaseReductionResidualTransport.upperInLowerCoordinate
      (PhaseReductionResidualCoordinateSource.residueEquiv hres)
      (C.upper_apply_equiv hres)
      (D.toCriticalPolarFunction (C.upper hres) (C.upper_ne_one hres)))
    (C.frobeniusEquiv hchar) (C.lower_frobeniusEquiv hchar)

@[simp]
theorem displayedInLowerCoordinate_apply
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (D : LocalLamprechtPhaseData K chiK psiK) (x : ResidueField F) :
    D.displayedInLowerCoordinate p hchar hres C x =
      D.criticalFunction
        (PhaseReductionResidualCoordinateSource.residueEquiv hres
          ((C.frobeniusEquiv hchar).symm x)) := by
  rw [displayedInLowerCoordinate,
    CriticalPolarFunction.reindex_apply,
    PhaseReductionResidualTransport.upperInLowerCoordinate_apply,
    toCriticalPolarFunction_apply]

/-- This common-coordinate display is a reindexing of the same complete
actual function, so its finite sum is unchanged. -/
theorem displayedInLowerCoordinate_sum
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (D : LocalLamprechtPhaseData K chiK psiK) :
    (∑ x : ResidueField F,
        D.displayedInLowerCoordinate p hchar hres C x) =
      ∑ y : ResidueField K, D.criticalFunction y := by
  unfold displayedInLowerCoordinate
  rw [CriticalPolarFunction.sum_reindex]
  unfold PhaseReductionResidualTransport.upperInLowerCoordinate
  rw [CriticalPolarFunction.sum_reindex]
  apply Finset.sum_congr rfl
  intro y _hy
  exact D.toCriticalPolarFunction_apply (C.upper hres)
    (C.upper_ne_one hres) y

theorem displayedInLowerCoordinate_phase
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (D : LocalLamprechtPhaseData K chiK psiK) :
    phase (∑ x : ResidueField F,
        D.displayedInLowerCoordinate p hchar hres C x) =
      phase (∑ y : ResidueField K, D.criticalFunction y) := by
  rw [D.displayedInLowerCoordinate_sum p hchar hres C]

/-- The displayed polar coefficient is the forward Frobenius of the
canonically transported natural coefficient, hence its exact `p`th power. -/
theorem displayedInLowerCoordinate_polarCoefficient
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (D : LocalLamprechtPhaseData K chiK psiK) :
    C.frobeniusEquiv hchar
        ((PhaseReductionResidualCoordinateSource.residueEquiv
            (F := F) (K := K) hres).symm
          (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres))) =
      ((PhaseReductionResidualCoordinateSource.residueEquiv
          (F := F) (K := K) hres).symm
        (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres))) ^ p := by
  exact C.frobeniusEquiv_apply hchar _

/-- The affine coefficient has the same exact transport direction: inverse
residue equivalence followed by forward Frobenius. -/
theorem displayedInLowerCoordinate_affineCoefficient
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (D : LocalLamprechtPhaseData K chiK psiK)
    (hoddF : ringChar (ResidueField F) ≠ 2)
    (hoddK : ringChar (ResidueField K) ≠ 2) :
    (D.displayedInLowerCoordinate p hchar hres C).affineCoefficient
        hoddF C.lower_ne_one =
      ((PhaseReductionResidualCoordinateSource.residueEquiv
          (F := F) (K := K) hres).symm
        (D.affineCoefficient (C.upper hres) (C.upper_ne_one hres) hoddK)) ^
          p := by
  unfold displayedInLowerCoordinate
  rw [CriticalPolarFunction.affineCoefficient_reindex hoddF hoddF
    C.lower_ne_one C.lower_ne_one]
  rw [PhaseReductionResidualTransport.upperInLowerCoordinate_affineCoefficient
    hoddF hoddK C.lower_ne_one (C.upper_ne_one hres)]
  rw [C.frobeniusEquiv_apply hchar]
  rfl

end DisplayedInLowerCoordinate

end LocalLamprechtPhaseData

end

end LanglandsFirstMainLemma
