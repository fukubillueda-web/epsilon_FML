import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.Herbrand
import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.Ramification.PrimeDegreeDichotomy
import LanglandsFirstMainLemma.LocalField.SuccessiveLifting
import LanglandsFirstMainLemma.LocalField.FiniteQuotients
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.DedekindDomain.Different

open scoped BigOperators
open Polynomial

namespace LanglandsFirstMainLemma

noncomputable section

section TraceEstimate

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- A generator of the integral closure gives a power basis after localization.  This is the
bridge from the chosen uniformizer coordinate to the trace-dual description of the different. -/
private noncomputable def fieldPowerBasisOfIntegralGenerator
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    PowerBasis F K := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  let pbO : PowerBasis (ringOfIntegers F) (ringOfIntegers K) :=
    PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral pi) hgen
  let bF : Module.Basis (Fin pbO.dim) F K :=
    pbO.basis.localizationLocalization F (nonZeroDivisors (ringOfIntegers F)) K
  exact
    { gen := (pi : K)
      dim := pbO.dim
      basis := bF
      basis_eq_pow := by
        intro i
        rw [show bF i = algebraMap (ringOfIntegers K) K (pbO.basis i) by
          exact Module.Basis.localizationLocalization_apply F
            (nonZeroDivisors (ringOfIntegers F)) K pbO.basis i]
        rw [pbO.basis_eq_pow]
        simp only [map_pow]
        rw [show pbO.gen = pi by simp [pbO]]
        rw [show algebraMap (ringOfIntegers K) K pi = (pi : K) by
          exact congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) pi] }

@[simp]
private theorem fieldPowerBasisOfIntegralGenerator_gen
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (fieldPowerBasisOfIntegralGenerator F K pi hgen).gen = (pi : K) :=
  rfl

private theorem field_adjoin_eq_top_of_integral_adjoin_eq_top
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Algebra.adjoin F ({(pi : K)} : Set K) = ⊤ :=
  (fieldPowerBasisOfIntegralGenerator F K pi hgen).adjoin_gen_eq_top

private theorem localFieldInfinite (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Infinite L := by
  let f : ℤ → L := fun n ↦ (exists_ord_eq L n).choose
  have hf : Function.Injective f := fun m n h ↦ by
    have hm := (exists_ord_eq L m).choose_spec
    have hn := (exists_ord_eq L n).choose_spec
    exact WithTop.coe_injective (hm.symm.trans ((congrArg (ord L) h).trans hn))
  exact Infinite.of_injective f hf

private theorem minpoly_integralGenerator_map_eq_prod_galois
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (minpoly F (pi : K)).map (algebraMap F K) =
      ∏ σ : Gal(K/F), (X - C (σ (pi : K))) := by
  letI : Infinite F := localFieldInfinite F
  let pb := fieldPowerBasisOfIntegralGenerator F K pi hgen
  calc
    (minpoly F (pi : K)).map (algebraMap F K) =
        ((Algebra.leftMulMatrix pb.basis pb.gen).charpoly).map (algebraMap F K) := by
          rw [charpoly_leftMulMatrix, fieldPowerBasisOfIntegralGenerator_gen]
    _ = (Algebra.lmul F K (pi : K)).charpoly.map (algebraMap F K) := by
      rw [← Algebra.toMatrix_lmul_eq, LinearMap.charpoly_toMatrix]
      congr 2
    _ = ∏ σ : Gal(K/F), (X - C (σ (pi : K))) :=
      map_lmul_charpoly_eq_prod_galois F K (pi : K)

private theorem aeval_derivative_minpoly_integralGenerator_eq_prod
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    aeval (pi : K) (derivative (minpoly F (pi : K))) =
      ∏ σ ∈ nonidentityGaloisAutomorphisms F K,
        ((pi : K) - σ (pi : K)) := by
  classical
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map]
  rw [minpoly_integralGenerator_map_eq_prod_galois F K pi hgen]
  rw [derivative_prod_finset]
  change (evalRingHom (pi : K))
      (∑ a : Gal(K/F),
        (∏ b ∈ (Finset.univ : Finset Gal(K/F)).erase a,
          (X - C (b (pi : K)))) * derivative (X - C (a (pi : K)))) = _
  rw [map_sum]
  simp only [map_prod, derivative_X_sub_C, mul_one]
  simp only [map_sub]
  unfold nonidentityGaloisAutomorphisms
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ hσ hσne
    have hmem : (1 : Gal(K/F)) ∈ (Finset.univ : Finset Gal(K/F)).erase σ := by
      simp [Ne.symm hσne]
    rw [Finset.prod_eq_zero hmem]
    simp
  · simp

private theorem ord_aeval_derivative_minpoly_integralGenerator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    ord K (aeval (pi : K) (derivative (minpoly F (pi : K)))) =
      ((((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) : WithTop ℤ) := by
  classical
  rw [aeval_derivative_minpoly_integralGenerator_eq_prod F K pi hgen]
  have hordprod (s : Finset Gal(K/F)) :
      ord K (∏ σ ∈ s, ((pi : K) - σ (pi : K))) =
        ∑ σ ∈ s, ord K ((pi : K) - σ (pi : K)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert σ s hσ ih =>
        simp only [Finset.prod_insert hσ, Finset.sum_insert hσ]
        rw [ord_mul, ih]
  rw [hordprod]
  calc
    ∑ σ ∈ nonidentityGaloisAutomorphisms F K,
        ord K ((pi : K) - σ (pi : K)) =
        ∑ _σ ∈ nonidentityGaloisAutomorphisms F K,
          (((t + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [show (pi : K) - σ (pi : K) = -(σ (pi : K) - (pi : K)) by ring,
        ord_neg]
      exact ord_galois_uniformizer_sub_eq_of_isLowerBreak F K ht pi hpi hgen
        ((mem_nonidentityGaloisAutomorphisms F K).1 hσ)
    _ = _ := by
      rw [Finset.sum_const, card_nonidentityGaloisAutomorphisms F K]
      rw [← WithTop.coe_nsmul]
      congr 1

private theorem coe_mem_adjoin_of_integral_adjoin_eq_top
    (pi x : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (x : K) ∈ Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K) := by
  have hx : x ∈ Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) := by
    rw [hgen]
    trivial
  exact Algebra.adjoin_induction (p := fun (z : ringOfIntegers K) _ ↦
      (z : K) ∈ Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K))
    (fun z hz ↦ by
      rw [Set.mem_singleton_iff.mp hz]
      exact Algebra.subset_adjoin (Set.mem_singleton (pi : K)))
    (fun r ↦ by
      change algebraMap (ringOfIntegers F) K r ∈ _
      exact (Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K)).algebraMap_mem r)
    (fun a b _ _ ha hb ↦ by simpa only [Subring.coe_add] using add_mem ha hb)
    (fun a b _ _ ha hb ↦ by simpa only [Subring.coe_mul] using mul_mem ha hb)
    hx

/-- The lower half of the exact trace-ideal formula, proved here from the trace dual and the
different rather than imported from the later norm-filtration theorem. -/
theorem traceIdealLowerBound_of_integralGenerator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    TraceIdealLowerBound F K (Module.finrank F K)
      (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  have hp : 0 < Module.finrank F K := Module.finrank_pos
  have hfield := field_adjoin_eq_top_of_integral_adjoin_eq_top F K pi hgen
  have hpint0 : IsIntegral (ringOfIntegers F) pi := Algebra.IsIntegral.isIntegral pi
  have hpint : IsIntegral (ringOfIntegers F) (pi : K) :=
    hpint0.map (IsScalarTower.toAlgHom
      (ringOfIntegers F) (ringOfIntegers K) K)
  let D : ℤ := (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)
  let d : K := aeval (pi : K) (derivative (minpoly F (pi : K)))
  have hdord : ord K d = (D : WithTop ℤ) := by
    simpa only [D] using
      ord_aeval_derivative_minpoly_integralGenerator F K ht pi hpi hgen
  have hd0 : d ≠ 0 :=
    (ord_ne_top_iff K).1 (by rw [hdord]; exact WithTop.coe_ne_top)
  have hdual := traceForm_dualSubmodule_adjoin
    (ringOfIntegers F) F hfield hpint
  intro q z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff K).2 hz0)
  have hqk : q ≤ k := by
    rw [← hk] at hz
    exact_mod_cast hz
  let n : ℤ := (q + D) / (Module.finrank F K : ℤ)
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have ha0 : a ≠ 0 := (ord_ne_top_iff F).1 (by rw [ha]; exact WithTop.coe_ne_top)
  let w : K := z / algebraMap F K a
  have hnle : (Module.finrank F K : ℤ) * n ≤ q + D := by
    dsimp only [n]
    have hpZ : (0 : ℤ) < Module.finrank F K := by exact_mod_cast hp
    simpa only [mul_comm] using Int.ediv_mul_le (q + D) hpZ.ne'
  have hword : (0 : WithTop ℤ) ≤ ord K (d * w) := by
    rw [ord_mul, hdord, ord_div, ← hk, ord_algebraMap, hram, ha]
    rw [← WithTop.coe_nsmul]
    norm_cast
    simp only [nsmul_eq_mul]
    omega
  let c : ringOfIntegers K := ⟨d * w, (ord_nonneg_iff_mem_integer K _).1 hword⟩
  have hc : (d * w) ∈
      Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K) := by
    simpa only [c] using coe_mem_adjoin_of_integral_adjoin_eq_top F K pi c hgen
  have hwdual : w ∈ (Algebra.traceForm F K).dualSubmodule
      (Subalgebra.toSubmodule
        (Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K))) := by
    rw [hdual, Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hd0)]
    simpa only [inv_inv, smul_eq_mul, Subalgebra.mem_toSubmodule] using hc
  have htraceInt := (LinearMap.BilinForm.mem_dualSubmodule
    (Algebra.traceForm F K)).1 hwdual (1 : K)
      ((Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K)).one_mem)
  rw [Algebra.traceForm_apply, mul_one] at htraceInt
  have htraceNonneg : (0 : WithTop ℤ) ≤ ord F (trace F K w) := by
    rw [ord_nonneg_iff_mem_integer]
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp htraceInt
    rw [← hr]
    exact r.prop
  have hzfac : z = algebraMap F K a * w := by
    dsimp only [w]
    have hmapa0 : algebraMap F K a ≠ 0 := by
      simpa only [map_zero] using (algebraMap F K).injective.ne ha0
    exact (mul_div_cancel₀ z hmapa0).symm
  have htracefac : trace F K z = a * trace F K w := by
    rw [hzfac]
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul a w
  rw [htracefac, ord_mul, ha]
  exact le_add_of_nonneg_right htraceNonneg

private theorem ord_nonneg_of_mem_integral_adjoin
    (pi : ringOfIntegers K) (x : K)
    (hx : x ∈ Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K)) :
    (0 : WithTop ℤ) ≤ ord K x := by
  exact Algebra.adjoin_induction (p := fun z _ ↦ (0 : WithTop ℤ) ≤ ord K z)
    (fun z hz ↦ by
      rw [Set.mem_singleton_iff.mp hz]
      exact (ord_nonneg_iff_mem_integer K _).2 pi.prop)
    (fun r ↦ by
      change (0 : WithTop ℤ) ≤ ord K (algebraMap F K (r : F))
      rw [ord_algebraMap]
      exact nsmul_nonneg ((ord_nonneg_iff_mem_integer F _).2 r.prop)
        (ramificationIndex F K))
    (fun a b _ _ ha hb ↦ (min_le_min ha hb).trans (ord_add K a b))
    (fun a b _ _ ha hb ↦ by rw [ord_mul]; exact add_nonneg ha hb)
    hx

/-- Exact surjectivity of the trace on a valuation lattice.  It is proved directly from the
trace-dual lattice generated by the minpoly derivative.  The floor relation is an explicit
hypothesis, so every denominator and rounding direction remains visible. -/
theorem trace_lattice_surjective_of_integralGenerator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (q r : ℤ)
    (hr : r = (q + (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) /
      (Module.finrank F K : ℤ))
    (y : F) (hy : y ∈ lattice F r) :
    ∃ x : K, x ∈ lattice K q ∧ trace F K x = y := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  have hp : 0 < Module.finrank F K := Module.finrank_pos
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  let D : ℤ := (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)
  have hrD : r = (q + D) / (Module.finrank F K : ℤ) := by
    simpa only [D] using hr
  let d : K := aeval (pi : K) (derivative (minpoly F (pi : K)))
  have hdord : ord K d = (D : WithTop ℤ) := by
    simpa only [D] using
      ord_aeval_derivative_minpoly_integralGenerator F K ht pi hpi hgen
  have hd0 : d ≠ 0 :=
    (ord_ne_top_iff K).1 (by rw [hdord]; exact WithTop.coe_ne_top)
  have hfield := field_adjoin_eq_top_of_integral_adjoin_eq_top F K pi hgen
  have hpint0 : IsIntegral (ringOfIntegers F) pi := Algebra.IsIntegral.isIntegral pi
  have hpint : IsIntegral (ringOfIntegers F) (pi : K) :=
    hpint0.map (IsScalarTower.toAlgHom
      (ringOfIntegers F) (ringOfIntegers K) K)
  have hdual := traceForm_dualSubmodule_adjoin
    (ringOfIntegers F) F hfield hpint
  have htrace := traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hexact : ∃ x₀ : K, x₀ ∈ lattice K q ∧
      trace F K x₀ ∉ lattice F (r + 1) := by
    by_contra hnone
    push_neg at hnone
    obtain ⟨c, hc⟩ := exists_ord_eq K q
    obtain ⟨a, ha⟩ := exists_ord_eq F (-(r + 1))
    let w : K := algebraMap F K a * c
    have hwdual : w ∈ (Algebra.traceForm F K).dualSubmodule
        (Subalgebra.toSubmodule
          (Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K))) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro z hz
      have hz0 := ord_nonneg_of_mem_integral_adjoin F K pi (z : K) hz
      have hcz : c * (z : K) ∈ lattice K q := by
        rw [mem_lattice, ord_mul, hc]
        exact le_add_of_nonneg_right hz0
      have hdeep := hnone (c * (z : K)) hcz
      have hdeepOrd : ((r + 1 : ℤ) : WithTop ℤ) ≤
          ord F (trace F K (c * (z : K))) := hdeep
      rw [Algebra.traceForm_apply]
      change trace F K (w * (z : K)) ∈ (1 : Submodule (ringOfIntegers F) F)
      have hlin : trace F K (w * (z : K)) =
          a * trace F K (c * (z : K)) := by
        dsimp only [w]
        rw [mul_assoc]
        simpa [Algebra.smul_def] using
          (Algebra.trace F K).map_smul a (c * (z : K))
      rw [hlin]
      apply Submodule.mem_one.mpr
      refine ⟨⟨a * trace F K (c * (z : K)), ?_⟩, rfl⟩
      rw [← ord_nonneg_iff_mem_integer]
      have haMem : a ∈ lattice F (-(r + 1)) := by
        rw [mem_lattice, ha]
      have hprod := mul_mem_lattice F haMem hdeep
      have hzero : a * trace F K (c * (z : K)) ∈ lattice F 0 := by
        convert hprod using 1 <;> ring
      exact hzero
    have hdw : d * w ∈
        Algebra.adjoin (ringOfIntegers F) ({(pi : K)} : Set K) := by
      rw [hdual] at hwdual
      rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hd0)] at hwdual
      simpa only [inv_inv, smul_eq_mul, Subalgebra.mem_toSubmodule] using hwdual
    have hdword := ord_nonneg_of_mem_integral_adjoin F K pi (d * w) hdw
    have hstrict : q + D < (Module.finrank F K : ℤ) * (r + 1) := by
      rw [hrD]
      have hpZ : (0 : ℤ) < Module.finrank F K := by exact_mod_cast hp
      simpa only [mul_comm] using Int.lt_ediv_add_one_mul_self (q + D) hpZ
    have hcalc : ord K (d * w) =
        ((D + (Module.finrank F K : ℤ) * (-(r + 1)) + q : ℤ) :
          WithTop ℤ) := by
      rw [ord_mul, hdord]
      dsimp only [w]
      rw [ord_mul, ord_algebraMap, hram, ha, hc, ← WithTop.coe_nsmul]
      norm_num
      simp only [nsmul_eq_mul, add_assoc, add_comm, add_left_comm]
    have hdword' : 0 ≤
        D + (Module.finrank F K : ℤ) * (-(r + 1)) + q := by
      rw [hcalc] at hdword
      exact_mod_cast hdword
    rw [show (Module.finrank F K : ℤ) * (-(r + 1)) =
        -((Module.finrank F K : ℤ) * (r + 1)) by ring] at hdword'
    omega
  obtain ⟨x₀, hx₀, htraceNot⟩ := hexact
  have htraceLow : ((r : ℤ) : WithTop ℤ) ≤ ord F (trace F K x₀) := by
    rw [hrD]
    exact htrace q x₀ hx₀
  have htraceOrd : ord F (trace F K x₀) = (r : WithTop ℤ) :=
    (withTopInt_le_and_not_succ_le_iff_eq r (ord F (trace F K x₀))).1
      ⟨htraceLow, htraceNot⟩
  have htrace0 : trace F K x₀ ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [htraceOrd]; exact WithTop.coe_ne_top)
  let b : F := y / trace F K x₀
  have hb0 : (0 : WithTop ℤ) ≤ ord F b := by
    rw [ord_div, htraceOrd]
    have hyord : ((r : ℤ) : WithTop ℤ) ≤ ord F y := hy
    have hy' := add_le_add_left hyord (-((r : ℤ) : WithTop ℤ))
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hy'
  let b₀ : ringOfIntegers F := ⟨b, (ord_nonneg_iff_mem_integer F _).1 hb0⟩
  refine ⟨algebraMap F K b * x₀, ?_, ?_⟩
  · rw [mem_lattice, ord_mul, ord_algebraMap]
    exact hx₀.trans (le_add_of_nonneg_left
      (nsmul_nonneg hb0 (ramificationIndex F K)))
  · simpa [b, Algebra.smul_def, htrace0] using
      (Algebra.trace F K).map_smul b x₀

end TraceEstimate

section RamificationGradedMap

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- The unit `σ(π)/π` underlying both the tame and positive-depth ramification
coordinates. -/
noncomputable def ramificationRatioUnit (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : Kˣ :=
  Units.mk0 ((σ : Gal(K/F)) π / π)
    (div_ne_zero ((map_ne_zero (σ : Gal(K/F))).2 hπ.ne_zero) hπ.ne_zero)

@[simp]
theorem coe_ramificationRatioUnit (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    (ramificationRatioUnit F K i σ π hπ : K) = (σ : Gal(K/F)) π / π :=
  rfl

theorem ord_ramificationRatioUnit (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    ord K (ramificationRatioUnit F K i σ π hπ : K) = 0 := by
  rw [coe_ramificationRatioUnit, ord_div, ord_galoisConjugate,
    ord_uniformizer K hπ]
  simp

theorem ramificationRatioUnit_mem (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    ramificationRatioUnit F K i σ π hπ ∈ unitFiltration K i := by
  cases i with
  | zero =>
      rw [mem_unitFiltration_zero]
      exact ord_ramificationRatioUnit F K 0 σ π hπ
  | succ n =>
      rw [mem_unitFiltration_succ, congruentAtDepth_iff_sub_mem_lattice K]
      change ((σ : Gal(K/F)) π / π - 1) ∈ lattice K (((n + 1 : ℕ) : ℤ))
      rw [div_sub_one hπ.ne_zero]
      rw [div_mem_lattice_iff K π ((σ : Gal(K/F)) π - π) 1
        (((n + 1 : ℕ) : ℤ)) (ord_uniformizer K hπ)]
      have hs := (lowerRamificationDisplacement F K σ π hπ).property
      change ((σ : Gal(K/F)) π - π) ∈ lattice K (((n + 1 : ℕ) : ℤ) + 1) at hs
      simpa only [add_comm] using hs

/-- The pre-quotient ramification homomorphism `G_i → gr^i U_K`. -/
noncomputable def ramificationUnitGradedPreHom (i : ℕ) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    lowerRamificationGroup F K (i : ℤ) →* UnitGradedPiece K i where
  toFun σ := unitGradedMk K i
    ⟨ramificationRatioUnit F K i σ π hπ,
      ramificationRatioUnit_mem F K i σ π hπ⟩
  map_one' := by
    apply (unitGradedMk_eq_one_iff K i _).2
    simpa [ramificationRatioUnit, hπ.ne_zero] using (unitFiltration K (i + 1)).one_mem
  map_mul' σ τ := by
    rw [← map_mul]
    apply (unitGradedMk_eq_mk_iff K i _ _).2
    let x : ringOfIntegers K := ⟨(τ : Gal(K/F)) π / π,
      (ord_nonneg_iff_mem_integer K _).1 (by
        rw [ord_div, ord_galoisConjugate, ord_uniformizer K hπ]
        simp)⟩
    have hact := (mem_lowerRamificationGroup F K
      (σ : Gal(K/F)) (i : ℤ)).1 σ.property x
    change CongruentAtDepth ((i : ℤ) + 1)
      ((σ : Gal(K/F)) ((τ : Gal(K/F)) π / π))
      ((τ : Gal(K/F)) π / π) at hact
    have hmul := hact.mul_left
      (a := (σ : Gal(K/F)) π / π)
      (by rw [ord_div, ord_galoisConjugate, ord_uniformizer K hπ]; simp)
    change CongruentAtDepth (((i + 1 : ℕ) : ℤ))
      (((σ * τ : lowerRamificationGroup F K (i : ℤ)) : Gal(K/F)) π / π)
      (((σ : Gal(K/F)) π / π) * ((τ : Gal(K/F)) π / π))
    change CongruentAtDepth ((i : ℤ) + 1)
      (((σ * τ : lowerRamificationGroup F K (i : ℤ)) : Gal(K/F)) π / π)
      (((σ : Gal(K/F)) π / π) * ((τ : Gal(K/F)) π / π))
    convert hmul using 1
    · simp only [Subgroup.coe_mul, AlgEquiv.mul_apply]
      calc
        (σ : Gal(K/F)) ((τ : Gal(K/F)) π) / π =
            ((σ : Gal(K/F)) π / π) *
              ((σ : Gal(K/F)) ((τ : Gal(K/F)) π) /
                (σ : Gal(K/F)) π) := by
                  field_simp [hπ.ne_zero,
                    ((map_ne_zero (σ : Gal(K/F))).2 hπ.ne_zero)]
        _ = ((σ : Gal(K/F)) π / π) *
              (σ : Gal(K/F)) ((τ : Gal(K/F)) π / π) := by
                rw [map_div₀ (σ : Gal(K/F))]

theorem ramificationRatioUnit_mem_succ_iff (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ))
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    ramificationRatioUnit F K i σ (π : K) hπ ∈ unitFiltration K (i + 1) ↔
      (σ : Gal(K/F)) ∈ lowerRamificationGroup F K ((i : ℤ) + 1) := by
  rw [mem_unitFiltration_succ, congruentAtDepth_iff_sub_mem_lattice K]
  change ((σ : Gal(K/F)) (π : K) / (π : K) - 1) ∈
      lattice K (((i + 1 : ℕ) : ℤ)) ↔ _
  rw [div_sub_one hπ.ne_zero]
  rw [div_mem_lattice_iff K (π : K)
    ((σ : Gal(K/F)) (π : K) - (π : K)) 1
    (((i + 1 : ℕ) : ℤ)) (ord_uniformizer K hπ)]
  rw [mem_lowerRamificationGroup_iff_of_adjoin_eq_top F K π hgen,
    congruentAtDepth_iff_sub_mem_lattice K]
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]

private theorem ramificationUnitGradedPreHom_ker (i : ℕ)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    lowerRamificationGroupInside F K
        (show (i : ℤ) ≤ (i : ℤ) + 1 by omega) =
      (ramificationUnitGradedPreHom F K i (π : K) hπ).ker := by
  ext σ
  rw [mem_lowerRamificationGroupInside, MonoidHom.mem_ker]
  change _ ↔ unitGradedMk K i
      ⟨ramificationRatioUnit F K i σ (π : K) hπ,
        ramificationRatioUnit_mem F K i σ (π : K) hπ⟩ = 1
  rw [unitGradedMk_eq_one_iff]
  exact (ramificationRatioUnit_mem_succ_iff F K i σ π hπ hgen).symm

/-- The exact ramification map `G_i/G_(i+1) → gr^i U_K`, simultaneously covering the
degree-zero multiplicative coordinate and the positive-depth displacement coordinate. -/
noncomputable def ramificationUnitGradedHom (i : ℕ)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    LowerRamificationGraded F K (i : ℤ) →* UnitGradedPiece K i :=
  QuotientGroup.lift
    (lowerRamificationGroupInside F K (show (i : ℤ) ≤ (i : ℤ) + 1 by omega))
    (ramificationUnitGradedPreHom F K i (π : K) hπ)
    (ramificationUnitGradedPreHom_ker F K i π hπ hgen).le

@[simp]
theorem ramificationUnitGradedHom_mk (i : ℕ)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (σ : lowerRamificationGroup F K (i : ℤ)) :
    ramificationUnitGradedHom F K i π hπ hgen
        (lowerRamificationGradedMk F K (i : ℤ) σ) =
      unitGradedMk K i
        ⟨ramificationRatioUnit F K i σ (π : K) hπ,
          ramificationRatioUnit_mem F K i σ (π : K) hπ⟩ :=
  rfl

theorem ramificationUnitGradedHom_injective (i : ℕ)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    Function.Injective (ramificationUnitGradedHom F K i π hπ hgen) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).2
  exact ramificationUnitGradedPreHom_ker F K i π hπ hgen

theorem norm_ramificationRatioUnit_eq_one (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ))
    (π : K) (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    normUnits F K (ramificationRatioUnit F K i σ π hπ) = 1 := by
  apply Units.ext
  change norm F K ((σ : Gal(K/F)) π / π) = 1
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, norm_galoisConjugate]
  exact mul_inv_cancel₀ ((Algebra.norm_ne_zero_iff).2 hπ.ne_zero)

private theorem residueCharacteristic_mem_lattice_one :
    (((residueCharacteristic K : ℕ) : ringOfIntegers K) : K) ∈ lattice K 1 := by
  apply (residueMap_eq_zero_iff K (residueCharacteristic K : ringOfIntegers K)).1
  change (residueCharacteristic K : ResidueField K) = 0
  exact CharP.cast_eq_zero (ResidueField K) (residueCharacteristic K)

private theorem residueCharacteristic_nsmul_latticeGraded_eq_zero
    (r : ℤ) (z : LatticeGradedPiece K r) :
    residueCharacteristic K • z = 0 := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective K
    (show r ≤ r + 1 by omega) z
  rw [← Nat.cast_smul_eq_nsmul (ringOfIntegers K), ← map_smul]
  apply (latticeQuotientMk_eq_zero_iff K (show r ≤ r + 1 by omega)).2
  change (((residueCharacteristic K : ℕ) : ringOfIntegers K) : K) *
      (x : K) ∈ lattice K (r + 1)
  simpa only [add_comm] using mul_mem_lattice K
    (residueCharacteristic_mem_lattice_one K) x.property

private theorem residueCharacteristic_pow_unitGraded_eq_one
    (n : ℕ) (u : UnitGradedPiece K (n + 1)) :
    u ^ residueCharacteristic K = 1 := by
  let e := positiveUnitGradedAddEquivLattice K n
  have hz := residueCharacteristic_nsmul_latticeGraded_eq_zero K
    (((n + 1 : ℕ) : ℤ)) (e (Additive.ofMul u))
  have hu : residueCharacteristic K • Additive.ofMul u = 0 := by
    apply e.injective
    rw [map_nsmul, map_zero]
    exact hz
  have := congrArg Additive.toMul hu
  simpa only [toMul_nsmul, toMul_ofMul, toMul_zero] using this

variable [PrimeCyclicExtension F K]

private noncomputable def generatorInLowerBreak {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    lowerRamificationGroup F K (t : ℤ) :=
  ⟨PrimeCyclicExtension.generator F K, by rw [ht.1]; trivial⟩

private theorem lowerRamificationGradedMk_injective_of_isLowerBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    Function.Injective (lowerRamificationGradedMk F K (t : ℤ)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (lowerRamificationQuotientMk F K
    (show (t : ℤ) ≤ (t : ℤ) + 1 by omega)).ker = ⊥
  rw [lowerRamificationQuotientMk_ker]
  ext σ
  rw [mem_lowerRamificationGroupInside, Subgroup.mem_bot, ht.2, Subgroup.mem_bot]
  constructor
  · intro hσ
    exact Subtype.ext hσ
  · intro hσ
    exact congrArg Subtype.val hσ

private theorem orderOf_lowerRamificationGraded_generator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    orderOf (lowerRamificationGradedMk F K (t : ℤ)
      (generatorInLowerBreak F K ht)) = Module.finrank F K := by
  calc
    _ = orderOf (generatorInLowerBreak F K ht) :=
      orderOf_injective (lowerRamificationGradedMk F K (t : ℤ))
        (lowerRamificationGradedMk_injective_of_isLowerBreak F K ht) _
    _ = orderOf (PrimeCyclicExtension.generator F K) := by
      rw [← orderOf_submonoid (generatorInLowerBreak F K ht)]
      rfl
    _ = Module.finrank F K := PrimeCyclicExtension.orderOf_generator F K

private theorem orderOf_ramificationUnitGraded_generator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    orderOf (ramificationUnitGradedHom F K t π hπ hgen
      (lowerRamificationGradedMk F K (t : ℤ)
        (generatorInLowerBreak F K ht))) = Module.finrank F K := by
  rw [orderOf_injective (ramificationUnitGradedHom F K t π hπ hgen)
    (ramificationUnitGradedHom_injective F K t π hπ hgen)]
  exact orderOf_lowerRamificationGraded_generator F K ht

/-- A positive lower break forces the prime extension degree to equal the residue
characteristic.  This is derived from the faithful positive ramification coordinate, not
assumed as extra wild-ramification data. -/
theorem residueCharacteristic_eq_degree_of_positive_isLowerBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    residueCharacteristic F = Module.finrank F K := by
  let u : UnitGradedPiece K t :=
    ramificationUnitGradedHom F K t π hπ hgen
      (lowerRamificationGradedMk F K (t : ℤ)
        (generatorInLowerBreak F K ht))
  have huorder : orderOf u = Module.finrank F K :=
    orderOf_ramificationUnitGraded_generator F K ht π hπ hgen
  have hupow : u ^ residueCharacteristic K = 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    exact residueCharacteristic_pow_unitGraded_eq_one K n u
  have hdvd : Module.finrank F K ∣ residueCharacteristic K := by
    rw [← huorder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hupow
  have hdegree : Module.finrank F K = residueCharacteristic K :=
    (Nat.prime_dvd_prime_iff_eq
      (PrimeCyclicExtension.degree_prime F K)
      (residueCharacteristic_prime K)).mp hdvd
  rw [← residueCharacteristic_extension_eq F K]
  exact hdegree.symm

end RamificationGradedMap

section WildNormCongruences

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Up to and including one level past the break, the norm of `1+x` stays at the
same numbered depth.  The proof is the exact elementary-symmetric expansion together with the
trace bound proved above; no norm-filtration theorem is imported. -/
theorem wild_norm_one_add_sub_one_mem_lattice
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hit : i ≤ t + 1)
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K) (hx : ((i : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 ∈ lattice F (i : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  have htrace := traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hs := wild_symmetric_bound F K t ht htpos hchar hram
    (by simpa [wildDifferentContribution] using htrace) (i : ℤ) hx
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  by_cases hjtop : j + 1 = Module.finrank F K
  · rw [hjtop, hs.2.1]
    exact hx
  · have hjpos : 1 ≤ j + 1 := by omega
    have hjlt : j + 1 < Module.finrank F K := by omega
    apply (show ((i : ℤ) : WithTop ℤ) ≤
        ((((j + 1 : ℕ) : ℤ) * (i : ℤ) +
          wildDifferentContribution (Module.finrank F K) t) /
            (Module.finrank F K : ℤ) : ℤ) by
      rw [WithTop.coe_le_coe]
      rw [Int.le_ediv_iff_mul_le (by
        exact_mod_cast (PrimeCyclicExtension.degree_prime F K).pos)]
      rw [wildDifferentContribution]
      have hpdecomp : Module.finrank F K =
          1 + (Module.finrank F K - 1) := by
        have := (PrimeCyclicExtension.degree_prime F K).two_le
        omega
      have hnat : Module.finrank F K * i ≤
          (j + 1) * i + (Module.finrank F K - 1) * (t + 1) := by
        calc
          Module.finrank F K * i =
              (1 + (Module.finrank F K - 1)) * i :=
            congrArg (fun n : ℕ ↦ n * i) hpdecomp
          _ = i + (Module.finrank F K - 1) * i := by
            rw [add_mul, one_mul]
          _ ≤ i + (Module.finrank F K - 1) * (t + 1) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hit) i
          _ ≤ (j + 1) * i + (Module.finrank F K - 1) * (t + 1) := by
            gcongr
            exact Nat.le_mul_of_pos_left i hjpos
      have hnatZ : (Module.finrank F K : ℤ) * (i : ℤ) ≤
          ((j + 1 : ℕ) : ℤ) * (i : ℤ) +
            (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
        exact_mod_cast hnat
      simpa only [mul_comm (Module.finrank F K : ℤ) (i : ℤ)] using hnatZ).trans
        (hs.1 hjpos hjlt)

/-- Strictly below the break, all nonterminal terms in the norm expansion gain one full
target depth.  Thus the exact graded map is represented by the terminal norm `x ↦ N(x)`. -/
theorem wild_norm_one_add_sub_one_sub_norm_mem_lattice
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hit : i < t)
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K) (hx : ((i : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 - norm F K x ∈
      lattice F ((i + 1 : ℕ) : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  have htrace := traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hs := wild_symmetric_bound F K t ht htpos hchar hram
    (by simpa [wildDifferentContribution] using htrace) (i : ℤ) hx
  have hp2 : 2 ≤ Module.finrank F K :=
    (PrimeCyclicExtension.degree_prime F K).two_le
  have hp0 : 0 < Module.finrank F K := by omega
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [show Module.finrank F K = (Module.finrank F K - 1) + 1 by omega]
  rw [Finset.sum_range_succ]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ Module.finrank F K)]
  rw [elementarySymmetric_finrank, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjpos : 1 ≤ j + 1 := by omega
  have hjlt : j + 1 < Module.finrank F K := by omega
  apply (show (((i + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      ((((j + 1 : ℕ) : ℤ) * (i : ℤ) +
        wildDifferentContribution (Module.finrank F K) t) /
          (Module.finrank F K : ℤ) : ℤ) by
    rw [WithTop.coe_le_coe]
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp0)]
    rw [wildDifferentContribution]
    have htstep : i + 2 ≤ t + 1 := by omega
    have hpdecomp : Module.finrank F K =
        1 + (Module.finrank F K - 1) := by omega
    have hnat : Module.finrank F K * (i + 1) ≤
        (j + 1) * i + (Module.finrank F K - 1) * (t + 1) := by
      calc
        Module.finrank F K * (i + 1) =
            (1 + (Module.finrank F K - 1)) * (i + 1) :=
          congrArg (fun n : ℕ ↦ n * (i + 1)) hpdecomp
        _ = (i + 1) + (Module.finrank F K - 1) * (i + 1) := by
          rw [add_mul, one_mul]
        _ ≤ i + (Module.finrank F K - 1) * (i + 2) := by
          rw [show (Module.finrank F K - 1) * (i + 2) =
              (Module.finrank F K - 1) * (i + 1) +
                (Module.finrank F K - 1) by ring]
          omega
        _ ≤ i + (Module.finrank F K - 1) * (t + 1) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ htstep) i
        _ ≤ (j + 1) * i + (Module.finrank F K - 1) * (t + 1) := by
          gcongr
          exact Nat.le_mul_of_pos_left i hjpos
    have hnatZ : (Module.finrank F K : ℤ) * ((i + 1 : ℕ) : ℤ) ≤
        (((j + 1 : ℕ) : ℤ) * (i : ℤ) +
          (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) := by
      exact_mod_cast hnat
    simpa only [mul_comm (Module.finrank F K : ℤ) (((i + 1 : ℕ) : ℤ))]
      using hnatZ).trans (hs.1 hjpos hjlt)

/-- At the positive critical depth the only surviving terms of the exact norm expansion are
the trace and the terminal norm.  This is the representative-level formula for the critical
graded norm; every intermediate coefficient lies one step deeper. -/
theorem wild_norm_critical_sub_trace_sub_norm_mem_lattice
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K) (hx : ((t : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 - trace F K x - norm F K x ∈
      lattice F ((t + 1 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  have hp2 : 2 ≤ p := (PrimeCyclicExtension.degree_prime F K).two_le
  have hp0 : 0 < p := by omega
  have hram : ramificationIndex F K = p := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  have htrace := traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hs := wild_symmetric_bound F K t ht htpos hchar hram
    (by simpa [p, wildDifferentContribution] using htrace) (t : ℤ) hx
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [show Module.finrank F K =
      (Module.finrank F K - 1) + 1 by omega, Finset.sum_range_succ']
  rw [elementarySymmetric_one, add_sub_cancel_right]
  rw [show Module.finrank F K - 1 =
      (Module.finrank F K - 2) + 1 by omega, Finset.sum_range_succ]
  rw [show p - 2 + 1 + 1 = Module.finrank F K by omega]
  rw [elementarySymmetric_finrank, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjpos : 1 ≤ j + 1 + 1 := by omega
  have hjtwo : 2 ≤ j + 1 + 1 := by omega
  have hjlt : j + 1 + 1 < Module.finrank F K := by
    omega
  apply (show ((((t + 1 : ℕ) : ℤ)) : WithTop ℤ) ≤
      (((((j + 1 + 1 : ℕ) : ℤ) * (t : ℤ) +
        wildDifferentContribution (Module.finrank F K) t) /
          (Module.finrank F K : ℤ) : ℤ) : WithTop ℤ) by
    rw [WithTop.coe_le_coe]
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp0)]
    rw [wildDifferentContribution]
    have hpdecomp : p = 1 + (p - 1) := by omega
    have hbase : p * (t + 1) ≤ 2 * t + (p - 1) * (t + 1) := by
      calc
        p * (t + 1) = p * t + p := by ring
        _ ≤ p * t + (t + (p - 1)) := by
          rw [hpdecomp]
          omega
        _ = 2 * t + (p - 1) * (t + 1) := by
          rw [hpdecomp]
          simp only [Nat.add_sub_cancel_left]
          ring
    have hjbound : 2 * t ≤ (j + 1 + 1) * t :=
      Nat.mul_le_mul_right t hjtwo
    have hnat : p * (t + 1) ≤
        (j + 1 + 1) * t + (p - 1) * (t + 1) :=
      hbase.trans (Nat.add_le_add_right hjbound ((p - 1) * (t + 1)))
    have hnatZ : (p : ℤ) * ((t + 1 : ℕ) : ℤ) ≤
        ((j + 1 + 1 : ℕ) : ℤ) * (t : ℤ) +
          (((p - 1) * (t + 1) : ℕ) : ℤ) := by
      exact_mod_cast hnat
    simpa only [p, mul_comm (Module.finrank F K : ℤ) (((t + 1 : ℕ) : ℤ))]
      using hnatZ).trans (hs.1 hjpos hjlt)

/-- On sufficiently deep layers the exact norm expansion is congruent to its trace term.  The
two displayed numerical hypotheses separately control the terminal norm coefficient and all
intermediate symmetric coefficients. -/
theorem wild_norm_one_add_sub_one_sub_trace_mem_lattice
    {t q s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hsq : s ≤ q)
    (hbound : Module.finrank F K * s ≤
      2 * q + (Module.finrank F K - 1) * (t + 1))
    (x : K) (hx : ((q : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 - trace F K x ∈ lattice F (s : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  have htrace := traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hsymmetric := wild_symmetric_bound F K t ht htpos hchar hram
    (by simpa [wildDifferentContribution] using htrace) (q : ℤ) hx
  have hp2 : 2 ≤ Module.finrank F K :=
    (PrimeCyclicExtension.degree_prime F K).two_le
  have hp0 : 0 < Module.finrank F K := by omega
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [show Module.finrank F K = (Module.finrank F K - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  rw [elementarySymmetric_one, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  by_cases hjtop : j + 1 + 1 = Module.finrank F K
  · rw [hjtop, hsymmetric.2.1]
    exact (show ((s : ℕ) : WithTop ℤ) ≤ ((q : ℕ) : WithTop ℤ) by
      exact_mod_cast hsq).trans hx
  · have hjpos : 1 ≤ j + 1 + 1 := by omega
    have hjlt : j + 1 + 1 < Module.finrank F K := by omega
    apply (show ((s : ℤ) : WithTop ℤ) ≤
        (((((j + 1 + 1 : ℕ) : ℤ) * (q : ℤ) +
          wildDifferentContribution (Module.finrank F K) t) /
            (Module.finrank F K : ℤ) : ℤ) : WithTop ℤ) by
      rw [WithTop.coe_le_coe]
      rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp0)]
      rw [wildDifferentContribution]
      have htwo : 2 * q ≤ (j + 1 + 1) * q := by
        exact Nat.mul_le_mul_right q (by omega)
      have hnat := hbound.trans
        (Nat.add_le_add_right htwo ((Module.finrank F K - 1) * (t + 1)))
      have hnatZ : (Module.finrank F K : ℤ) * (s : ℤ) ≤
          ((j + 1 + 1 : ℕ) : ℤ) * (q : ℤ) +
            (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
        exact_mod_cast hnat
      simpa only [mul_comm (Module.finrank F K : ℤ) (s : ℤ)] using hnatZ).trans
        (hsymmetric.1 hjpos hjlt)

end WildNormCongruences

section FilteredNorm

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The norm carries the indicated source unit layer into the indicated target layer.

The two depths are kept separate so that the same quotient construction can be used both below
the break (where they agree) and after Herbrand's change of numbering. -/
def NormMapsUnitFiltration (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ u : Kˣ, u ∈ unitFiltration K sourceDepth →
    normUnits F K u ∈ unitFiltration F targetDepth

/-- Norm preserves the unit group (depth zero) in every finite local-field extension. -/
theorem normMapsUnitFiltration_zero : NormMapsUnitFiltration F K 0 0 := by
  intro u hu
  rw [mem_unitFiltration_zero, coe_normUnits, ord_norm,
    (mem_unitFiltration_zero K u).1 hu]
  simp

/-- Restriction of the field norm to a pair of unit-filtration layers. -/
noncomputable def normBelowBreakUnitFiltrationHom (sourceDepth targetDepth : ℕ)
    (hmap : NormMapsUnitFiltration F K sourceDepth targetDepth) :
    unitFiltration K sourceDepth →* unitFiltration F targetDepth :=
  ((normUnits F K).comp (unitFiltration K sourceDepth).subtype).codRestrict
    (unitFiltration F targetDepth) (fun u ↦ hmap u u.property)

@[simp]
theorem coe_normBelowBreakUnitFiltrationHom (sourceDepth targetDepth : ℕ)
    (hmap : NormMapsUnitFiltration F K sourceDepth targetDepth)
    (u : unitFiltration K sourceDepth) :
    ((normBelowBreakUnitFiltrationHom F K sourceDepth targetDepth hmap u :
        unitFiltration F targetDepth) : Fˣ) = normUnits F K (u : Kˣ) :=
  rfl

/-- The representative-independent norm map on two certified filtration quotients.

`hnum` puts norms of numerator representatives in the target numerator.  `hden` is the
separate condition that makes changing a representative by the source denominator invisible
modulo the target denominator. -/
noncomputable def normUnitFiltrationQuotient
    {sourceNumerator sourceDenominator targetNumerator targetDenominator : ℕ}
    (hsource : sourceNumerator ≤ sourceDenominator)
    (htarget : targetNumerator ≤ targetDenominator)
    (hnum : NormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden : NormMapsUnitFiltration F K sourceDenominator targetDenominator) :
    UnitFiltrationQuotient K sourceNumerator sourceDenominator hsource →*
      UnitFiltrationQuotient F targetNumerator targetDenominator htarget :=
  QuotientGroup.lift (unitFiltrationInside K hsource)
    ((unitFiltrationQuotientMk F htarget).comp
      (normBelowBreakUnitFiltrationHom F K sourceNumerator targetNumerator hnum)) (by
        intro u hu
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
          unitFiltrationQuotientMk_eq_one_iff]
        exact hden (u : Kˣ) ((mem_unitFiltrationInside K hsource u).1 hu))

@[simp]
theorem normUnitFiltrationQuotient_mk
    {sourceNumerator sourceDenominator targetNumerator targetDenominator : ℕ}
    (hsource : sourceNumerator ≤ sourceDenominator)
    (htarget : targetNumerator ≤ targetDenominator)
    (hnum : NormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden : NormMapsUnitFiltration F K sourceDenominator targetDenominator)
    (u : unitFiltration K sourceNumerator) :
    normUnitFiltrationQuotient F K hsource htarget hnum hden
        (unitFiltrationQuotientMk K hsource u) =
      unitFiltrationQuotientMk F htarget
        (normBelowBreakUnitFiltrationHom F K sourceNumerator targetNumerator hnum u) :=
  rfl

/-- The norm induced on the `i`-th unit-graded piece.  The successor hypothesis is exactly
the quotient well-definedness condition and is intentionally separate from the numerator
hypothesis. -/
noncomputable def normUnitGraded (i : ℕ)
    (hi : NormMapsUnitFiltration F K i i)
    (hsucc : NormMapsUnitFiltration F K (i + 1) (i + 1)) :
    UnitGradedPiece K i →* UnitGradedPiece F i :=
  normUnitFiltrationQuotient F K (Nat.le_succ i) (Nat.le_succ i) hi hsucc

@[simp]
theorem normUnitGraded_mk (i : ℕ)
    (hi : NormMapsUnitFiltration F K i i)
    (hsucc : NormMapsUnitFiltration F K (i + 1) (i + 1))
    (u : unitFiltration K i) :
    normUnitGraded F K i hi hsucc (unitGradedMk K i u) =
      unitGradedMk F i (normBelowBreakUnitFiltrationHom F K i i hi u) :=
  rfl

/-- Surjectivity of one graded norm map gives a one-step correction at that depth. -/
theorem exists_normUnitFiltration_oneStepCorrection
    (i : ℕ)
    (hi : NormMapsUnitFiltration F K i i)
    (hsucc : NormMapsUnitFiltration F K (i + 1) (i + 1))
    (hsurj : Function.Surjective (normUnitGraded F K i hi hsucc))
    (u : Fˣ) (hu : u ∈ unitFiltration F i) :
    ∃ x : Kˣ, x ∈ unitFiltration K i ∧
      u / normUnits F K x ∈ unitFiltration F (i + 1) := by
  let u₀ : unitFiltration F i := ⟨u, hu⟩
  obtain ⟨z, hz⟩ := hsurj (unitGradedMk F i u₀)
  obtain ⟨x₀, rfl⟩ := unitGradedMk_surjective K i z
  refine ⟨(x₀ : Kˣ), x₀.property, ?_⟩
  have heq :
      unitGradedMk F i (normBelowBreakUnitFiltrationHom F K i i hi x₀) =
        unitGradedMk F i u₀ := by
    simpa only [normUnitGraded_mk] using hz
  have hcong := (unitGradedMk_eq_mk_iff F i _ _).1 heq
  exact (div_mem_unitFiltration_iff_congruentAtDepth F (i + 1) u
    (normUnits F K (x₀ : Kˣ))
    (unitFiltration_le_unitGroup F i hu)
    (unitFiltration_le_unitGroup F i
      (show normUnits F K (x₀ : Kˣ) ∈ unitFiltration F i from
        hi (x₀ : Kˣ) x₀.property))).2 hcong.symm

/-- Injectivity of one graded norm map detects one extra source-filtration step from one extra
target-filtration step. -/
theorem mem_unitFiltration_succ_of_norm_of_graded_injective
    (i : ℕ)
    (hi : NormMapsUnitFiltration F K i i)
    (hsucc : NormMapsUnitFiltration F K (i + 1) (i + 1))
    (hinj : Function.Injective (normUnitGraded F K i hi hsucc))
    (u : Kˣ) (hu : u ∈ unitFiltration K i)
    (hnu : normUnits F K u ∈ unitFiltration F (i + 1)) :
    u ∈ unitFiltration K (i + 1) := by
  let u₀ : unitFiltration K i := ⟨u, hu⟩
  have hmapOne : normUnitGraded F K i hi hsucc (unitGradedMk K i u₀) = 1 := by
    rw [normUnitGraded_mk, unitGradedMk_eq_one_iff]
    exact hnu
  have hsourceOne : unitGradedMk K i u₀ = 1 := by
    apply hinj
    simpa using hmapOne
  exact (unitGradedMk_eq_one_iff K i u₀).1 hsourceOne

/-- Successive use of surjective graded norm maps corrects a target unit through any finite
interval of depths.  This is the finite (no completeness needed) lifting used to splice the
below-break graded isomorphisms. -/
theorem exists_normUnitFiltration_finiteCorrection
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (hsurj : ∀ i (hri : r ≤ i) (hit : i < t),
      Function.Surjective
        (normUnitGraded F K i (hmap i hri hit.le)
          (hmap (i + 1) (by omega) (by omega))))
    (u : Fˣ) (hu : u ∈ unitFiltration F r) :
    ∃ x : Kˣ, x ∈ unitFiltration K r ∧
      u / normUnits F K x ∈ unitFiltration F t := by
  induction t, hrt using Nat.le_induction with
  | base =>
      exact ⟨1, (unitFiltration K r).one_mem, by simpa using hu⟩
  | succ t hrt ih =>
      obtain ⟨x, hx, herr⟩ := ih
        (fun i hri hit ↦ hmap i hri (hit.trans (Nat.le_succ t)))
        (fun i hri hit ↦ by
          simpa only using hsurj i hri (hit.trans_le (Nat.le_succ t)))
      obtain ⟨y, hy, hnext⟩ :=
        exists_normUnitFiltration_oneStepCorrection F K t
          (hmap t hrt (Nat.le_succ t))
          (hmap (t + 1) (by omega) le_rfl)
          (hsurj t hrt (Nat.lt_succ_self t))
          (u / normUnits F K x) herr
      refine ⟨x * y, unitFiltration_mul_mem K hx
        (unitFiltration_antitone K hrt hy), ?_⟩
      simpa only [map_mul, div_div] using hnext

/-- If every graded norm map in a finite interval is injective, membership of the norm in the
final target layer forces membership of the source representative in the final source layer. -/
theorem mem_unitFiltration_of_norm_mem_of_graded_injective
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (hinj : ∀ i (hri : r ≤ i) (hit : i < t),
      Function.Injective
        (normUnitGraded F K i (hmap i hri hit.le)
          (hmap (i + 1) (by omega) (by omega))))
    (u : Kˣ) (hu : u ∈ unitFiltration K r)
    (hnu : normUnits F K u ∈ unitFiltration F t) :
    u ∈ unitFiltration K t := by
  induction t, hrt using Nat.le_induction with
  | base => exact hu
  | succ t hrt ih =>
      have hut : u ∈ unitFiltration K t :=
        ih (fun i hri hit ↦ hmap i hri (hit.trans (Nat.le_succ t)))
          (fun i hri hit ↦ by
            simpa only using hinj i hri (hit.trans_le (Nat.le_succ t)))
          (unitFiltration_antitone F (Nat.le_succ t) hnu)
      exact mem_unitFiltration_succ_of_norm_of_graded_injective F K t
        (hmap t hrt (Nat.le_succ t))
        (hmap (t + 1) (by omega) le_rfl)
        (hinj t hrt (Nat.lt_succ_self t)) u hut hnu

/-- Norm on the finite interval quotient `U_K^r/U_K^t → U_F^r/U_F^t`, with
well-definedness at both endpoints kept explicit in `hmap`. -/
noncomputable def normUnitFiltrationInterval
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i) :
    UnitFiltrationQuotient K r t hrt →* UnitFiltrationQuotient F r t hrt :=
  normUnitFiltrationQuotient F K hrt hrt
    (hmap r le_rfl hrt) (hmap t hrt le_rfl)

@[simp]
theorem normUnitFiltrationInterval_mk
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (u : unitFiltration K r) :
    normUnitFiltrationInterval F K hrt hmap
        (unitFiltrationQuotientMk K hrt u) =
      unitFiltrationQuotientMk F hrt
        (normBelowBreakUnitFiltrationHom F K r r (hmap r le_rfl hrt) u) :=
  rfl

/-- Surjective graded norm maps throughout `[r,t)` splice to a surjection on
`U^r/U^t`. -/
theorem normUnitFiltrationInterval_surjective
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (hsurj : ∀ i (hri : r ≤ i) (hit : i < t),
      Function.Surjective
        (normUnitGraded F K i (hmap i hri hit.le)
          (hmap (i + 1) (by omega) (by omega)))) :
    Function.Surjective (normUnitFiltrationInterval F K hrt hmap) := by
  intro z
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F hrt z
  obtain ⟨x, hx, herr⟩ :=
    exists_normUnitFiltration_finiteCorrection F K hrt hmap hsurj
      (u : Fˣ) u.property
  let x₀ : unitFiltration K r := ⟨x, hx⟩
  refine ⟨unitFiltrationQuotientMk K hrt x₀, ?_⟩
  rw [normUnitFiltrationInterval_mk]
  apply (unitFiltrationQuotientMk_eq_mk_iff F hrt _ _).2
  have hinv := (unitFiltration F t).inv_mem herr
  simpa only [Subgroup.coe_inv, inv_div,
    coe_normBelowBreakUnitFiltrationHom] using hinv

/-- Injective graded norm maps throughout `[r,t)` splice to an injection on
`U^r/U^t`. -/
theorem normUnitFiltrationInterval_injective
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (hinj : ∀ i (hri : r ≤ i) (hit : i < t),
      Function.Injective
        (normUnitGraded F K i (hmap i hri hit.le)
          (hmap (i + 1) (by omega) (by omega)))) :
    Function.Injective (normUnitFiltrationInterval F K hrt hmap) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hz
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective K hrt z
    rw [normUnitFiltrationInterval_mk,
      unitFiltrationQuotientMk_eq_one_iff] at hz
    have hnorm : normUnits F K (u : Kˣ) ∈ unitFiltration F t := by
      exact hz
    apply (unitFiltrationQuotientMk_eq_one_iff K hrt u).2
    exact mem_unitFiltration_of_norm_mem_of_graded_injective F K hrt hmap hinj
      (u : Kˣ) u.property hnorm
  · intro hz
    rw [Subgroup.mem_bot] at hz
    subst z
    exact (normUnitFiltrationInterval F K hrt hmap).ker.one_mem

/-- The multiplicative equivalence on a finite unit-filtration interval obtained by splicing
bijective graded norm maps. -/
noncomputable def normUnitFiltrationIntervalEquiv
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (hbij : ∀ i (hri : r ≤ i) (hit : i < t),
      Function.Bijective
        (normUnitGraded F K i (hmap i hri hit.le)
          (hmap (i + 1) (by omega) (by omega)))) :
    UnitFiltrationQuotient K r t hrt ≃*
      UnitFiltrationQuotient F r t hrt :=
  MulEquiv.ofBijective (normUnitFiltrationInterval F K hrt hmap)
    ⟨normUnitFiltrationInterval_injective F K hrt hmap
        (fun i hri hit ↦ (hbij i hri hit).1),
      normUnitFiltrationInterval_surjective F K hrt hmap
        (fun i hri hit ↦ (hbij i hri hit).2)⟩

@[simp]
theorem normUnitFiltrationIntervalEquiv_apply
    {r t : ℕ} (hrt : r ≤ t)
    (hmap : ∀ i, r ≤ i → i ≤ t → NormMapsUnitFiltration F K i i)
    (hbij : ∀ i (hri : r ≤ i) (hit : i < t),
      Function.Bijective
        (normUnitGraded F K i (hmap i hri hit.le)
          (hmap (i + 1) (by omega) (by omega))))
    (z : UnitFiltrationQuotient K r t hrt) :
    normUnitFiltrationIntervalEquiv F K hrt hmap hbij z =
      normUnitFiltrationInterval F K hrt hmap z :=
  rfl

end FilteredNorm

section GradedCardinality

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]

/-- Residue degree one identifies the two canonical finite residue cardinalities. -/
theorem residueCard_eq_of_residueDegree_eq_one
    (hres : residueDegree F K = 1) :
    residueCard K = residueCard F := by
  letI := residueFieldFintype F
  letI := residueFieldFintype K
  exact (Fintype.card_congr (Equiv.ofBijective
    (algebraMap (ResidueField F) (ResidueField K))
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
      ((residueDegree_eq_finrank_residueField F K).symm.trans hres)))).symm

/-- Corresponding unit-graded pieces have the same finite cardinality in a totally ramified
extension, including the distinct degree-zero formula `q-1`. -/
theorem unitGradedPiece_card_eq_of_residueDegree_eq_one
    (i : ℕ) (hres : residueDegree F K = 1) :
    Nat.card (UnitGradedPiece K i) = Nat.card (UnitGradedPiece F i) := by
  rw [unitFiltrationQuotient_card K (Nat.le_succ i),
    unitFiltrationQuotient_card F (Nat.le_succ i),
    residueCard_eq_of_residueDegree_eq_one F K hres]

theorem unitGradedMap_bijective_of_injective_of_residueDegree_eq_one
    (i : ℕ) (hres : residueDegree F K = 1)
    (f : UnitGradedPiece K i →* UnitGradedPiece F i)
    (hinj : Function.Injective f) :
    Function.Bijective f :=
  (Nat.bijective_iff_injective_and_card f).2
    ⟨hinj, unitGradedPiece_card_eq_of_residueDegree_eq_one F K i hres⟩

end GradedCardinality

section WildBelowBreak

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- In the positive-break case the norm preserves every equally numbered layer through
`t+1`. -/
theorem wild_normMapsUnitFiltration
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hit : i ≤ t + 1)
    (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    NormMapsUnitFiltration F K i i := by
  intro u hu
  cases i with
  | zero =>
      rw [mem_unitFiltration_zero, coe_normUnits, ord_norm,
        (mem_unitFiltration_zero K u).1 hu, hres, one_nsmul]
  | succ n =>
      rw [mem_unitFiltration_succ] at hu ⊢
      rw [congruentAtDepth_iff_sub_mem_lattice K] at hu
      rw [congruentAtDepth_iff_sub_mem_lattice F]
      change norm F K (u : K) - 1 ∈ lattice F (((n + 1 : ℕ) : ℤ))
      rw [show (u : K) = 1 + ((u : K) - 1) by ring]
      exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos hit hres
        (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht htpos π hπ hgen)
        π hπ hgen ((u : K) - 1) hu

/-- The exact below-break graded norm has trivial kernel.  In positive depth its coordinate is
the terminal term `x ↦ N(x)` of the norm expansion; at degree zero the same argument is the
residue Frobenius. -/
theorem normUnitGraded_injective_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hit : i < t)
    (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    Function.Injective (normUnitGraded F K i
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_bot]
    obtain ⟨u, rfl⟩ := unitGradedMk_surjective K i z
    rw [MonoidHom.mem_ker, normUnitGraded_mk, unitGradedMk_eq_one_iff] at hz
    rw [unitGradedMk_eq_one_iff]
    have hu0 : ((i : ℕ) : WithTop ℤ) ≤ ord K (((u : Kˣ) : K) - 1) := by
      cases i with
      | zero =>
          have huord := (mem_unitFiltration_zero K (u : Kˣ)).1 u.property
          calc
            (0 : WithTop ℤ) = min (ord K ((u : Kˣ) : K)) (ord K 1) := by
              simp [huord]
            _ ≤ ord K (((u : Kˣ) : K) - 1) := ord_sub K _ 1
      | succ n =>
          exact (mem_unitFiltration_succ_iff_sub_mem_lattice K n (u : Kˣ)).1 u.property
    have hrem := wild_norm_one_add_sub_one_sub_norm_mem_lattice F K ht htpos hit hres
      (residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht htpos π hπ hgen)
      π hπ hgen (((u : Kˣ) : K) - 1) hu0
    have hnormu : norm F K ((u : Kˣ) : K) - 1 ∈
        lattice F (((i + 1 : ℕ) : ℤ)) := by
      have hh := (mem_unitFiltration_succ_iff_sub_mem_lattice F i
        (normBelowBreakUnitFiltrationHom F K i i _ u)).1 hz
      rw [coe_normBelowBreakUnitFiltrationHom, coe_normUnits] at hh
      exact hh
    have hnormx : norm F K (((u : Kˣ) : K) - 1) ∈
        lattice F (((i + 1 : ℕ) : ℤ)) := by
      have hsub := sub_mem_lattice F hnormu hrem
      convert hsub using 1 <;> ring
    have hordnorm : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        ord F (norm F K (((u : Kˣ) : K) - 1)) := hnormx
    rw [ord_norm, hres, one_nsmul] at hordnorm
    exact (mem_unitFiltration_succ_iff_sub_mem_lattice K i (u : Kˣ)).2 hordnorm
  · intro hz
    rw [Subgroup.mem_bot] at hz
    subst z
    exact (normUnitGraded F K i _ _).ker.one_mem

/-- Below the break the graded norm is bijective: injectivity comes from the exact norm
expansion and surjectivity from equality of the two finite graded cardinalities. -/
theorem normUnitGraded_bijective_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hit : i < t)
    (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    Function.Bijective (normUnitGraded F K i
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)) :=
  unitGradedMap_bijective_of_injective_of_residueDegree_eq_one F K i hres _
    (normUnitGraded_injective_belowBreak F K ht htpos hit hres π hπ hgen)

/-- The multiplicative equivalence induced by norm on every graded level `i<t`. -/
noncomputable def normUnitGradedEquiv_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hit : i < t)
    (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    UnitGradedPiece K i ≃* UnitGradedPiece F i :=
  MulEquiv.ofBijective (normUnitGraded F K i
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen))
    (normUnitGraded_bijective_belowBreak F K ht htpos hit hres π hπ hgen)

end WildBelowBreak

section WildDeepCorrection

open Filter Topology

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- One trace-controlled correction strictly above the critical layer.  The source depth is
`t + p n + (p-1) + 1 = Ψ(t+1+n)`, while the target depth is `t+1+n`; this is the audited
lower/upper numbering shift used by successive lifting. -/
theorem exists_wild_norm_aboveBreak_oneStep
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (n : ℕ) (u : Fˣ) (hu : u ∈ unitFiltration F (t + 1 + n)) :
    ∃ x : Kˣ,
      x ∈ unitFiltration K (t + Module.finrank F K * n +
        (Module.finrank F K - 1) + 1) ∧
      u / normUnits F K x ∈ unitFiltration F (t + 1 + n + 1) := by
  let p := Module.finrank F K
  have hp2 : 2 ≤ p := (PrimeCyclicExtension.degree_prime F K).two_le
  have hp0 : 0 < p := by omega
  have hp1 : 1 ≤ p := by omega
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht htpos π hπ hgen
  let a : ℕ := t + p * n + (p - 1)
  let q : ℕ := a + 1
  let r : ℕ := t + 1 + n
  let s : ℕ := r + 1
  have hy : (u : F) - 1 ∈ lattice F (r : ℤ) := by
    have hu' := (mem_unitFiltration_succ_iff_sub_mem_lattice F (t + n) u).1
      (show u ∈ unitFiltration F ((t + n) + 1) by
        simpa only [r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu)
    simpa only [r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu'
  have hfloor : (r : ℤ) =
      ((q : ℤ) + (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
    obtain ⟨k, hpk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp0)
    have hnumNat : q + (p - 1) * (t + 1) = p * r + (p - 1) := by
      dsimp only [q, a, r]
      rw [hpk]
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    have hnum : (q : ℤ) + (((p - 1) * (t + 1) : ℕ) : ℤ) =
        (p : ℤ) * (r : ℤ) + ((p - 1 : ℕ) : ℤ) := by
      exact_mod_cast hnumNat
    rw [hnum, Int.mul_add_ediv_left _ _ (by exact_mod_cast hp0.ne')]
    have hsmall : (((p - 1 : ℕ) : ℤ) / (p : ℤ)) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast Nat.sub_lt hp0 Nat.zero_lt_one
    rw [hsmall, add_zero]
  obtain ⟨z, hz, htracez⟩ :=
    trace_lattice_surjective_of_integralGenerator F K ht hres π hπ hgen
      (q : ℤ) (r : ℤ) (by simpa only [p] using hfloor) ((u : F) - 1) hy
  have hsq : s ≤ q := by
    obtain ⟨k, hpk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp0)
    have hk : 1 ≤ k := by omega
    have hkn : n ≤ k * n := by
      simpa only [one_mul] using Nat.mul_le_mul_right n hk
    dsimp only [s, r, q, a]
    rw [hpk]
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, add_mul, one_mul]
    omega
  have hbound : p * s ≤ 2 * q + (p - 1) * (t + 1) := by
    obtain ⟨k, hpk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp0)
    have heq : 2 * q + (p - 1) * (t + 1) = p * s + (q - 1) := by
      dsimp only [s, r, q, a]
      rw [hpk]
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    rw [heq]
    exact Nat.le_add_right _ _
  have hrem := wild_norm_one_add_sub_one_sub_trace_mem_lattice F K ht htpos hres
    hchar π hπ hgen hsq hbound z hz
  let x : Kˣ := principalUnitOf K a z (by simpa only [q, a] using hz)
  have hx : x ∈ unitFiltration K (a + 1) :=
    principalUnitOf_mem K a z (by simpa only [q, a] using hz)
  refine ⟨x, by simpa only [a, p, Nat.add_assoc] using hx, ?_⟩
  have hun : u ∈ unitGroup F := unitFiltration_le_unitGroup F _ hu
  have hx0 : x ∈ unitGroup K := unitFiltration_le_unitGroup K _ hx
  have hnorm0 : normUnits F K x ∈ unitGroup F := by
    rw [mem_unitGroup_iff_ord_eq_zero]
    change ord F (norm F K (x : K)) = 0
    rw [ord_norm, (mem_unitGroup_iff_ord_eq_zero K x).1 hx0]
    simp
  change u / normUnits F K x ∈ unitFiltration F s
  rw [div_mem_unitFiltration_iff_congruentAtDepth F s u
    (normUnits F K x) hun hnorm0]
  rw [CongruentAtDepth]
  change ((s : ℤ) : WithTop ℤ) ≤ ord F ((u : F) - norm F K (x : K))
  have hdiff : (u : F) - norm F K (x : K) ∈ lattice F (s : ℤ) := by
    have hpos : norm F K (x : K) - (u : F) ∈ lattice F (s : ℤ) := by
      change norm F K (1 + z) - (u : F) ∈ lattice F (s : ℤ)
      convert hrem using 1
      rw [htracez]
      ring
    have hneg := (lattice F (s : ℤ)).neg_mem hpos
    convert hneg using 1 <;> ring
  exact hdiff

/-- The essential endpoint correction: every unit in `U_F^(t+1)` is the exact norm of a unit
already lying in `U_K^(t+1)`.  Corrections are actually chosen at the deeper Herbrand levels
`t+p, t+2p, ...`, and completeness supplies the exact limit. -/
theorem wild_norm_unitFiltration_surjective_break_succ
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    ∀ u : Fˣ, u ∈ unitFiltration F (t + 1) →
      ∃ x : Kˣ, x ∈ unitFiltration K (t + 1) ∧ normUnits F K x = u := by
  let p := Module.finrank F K
  have hp2 : 2 ≤ p := (PrimeCyclicExtension.degree_prime F K).two_le
  have hp0 : 0 < p := by omega
  have hlift := successiveLifting_surjective
    (norm F K) (continuous_norm F K)
    (fun n ↦ t + p * n + (p - 1)) (t + 1)
    (by
      intro a b hab
      exact Nat.add_le_add_right (Nat.add_le_add_left
        (Nat.mul_le_mul_left p hab) t) (p - 1))
    (by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      have hpn : n ≤ p * n := by
        simpa only [one_mul] using Nat.mul_le_mul_right n (show 1 ≤ p by omega)
      omega)
    (by
      intro n u hu
      simpa only [p, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        exists_wild_norm_aboveBreak_oneStep F K ht htpos hres π hπ hgen n u
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu))
  intro u hu
  obtain ⟨x, hx, hnorm⟩ := hlift u hu
  refine ⟨x, unitFiltration_antitone K ?_ hx, hnorm⟩
  dsimp only [p]
  have hp1 : 1 ≤ Module.finrank F K := by omega
  omega

end WildDeepCorrection

section CriticalWildKernel

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Every ramification class has trivial graded norm because `N(σ(π)/π)=1` exactly. -/
theorem ramificationUnitGradedHom_le_normUnitGraded_ker
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    (ramificationUnitGradedHom F K t π hπ hgen).range ≤
      (normUnitGraded F K t
        (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
        (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)).ker := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨σ, rfl⟩ := lowerRamificationQuotientMk_surjective F K
    (show (t : ℤ) ≤ (t : ℤ) + 1 by omega) z
  change normUnitGraded F K t _ _
    (ramificationUnitGradedHom F K t π hπ hgen
      (lowerRamificationGradedMk F K (t : ℤ) σ)) = 1
  rw [ramificationUnitGradedHom_mk, normUnitGraded_mk,
    unitGradedMk_eq_one_iff]
  simpa only [coe_normBelowBreakUnitFiltrationHom, norm_ramificationRatioUnit_eq_one F K t σ
    (π : K) hπ] using (unitFiltration F (t + 1)).one_mem

/-- A critical graded-kernel class first acquires an exact norm-one representative.  The
correction factor lies in `U_K^(t+1)` and comes from the independently proved endpoint norm
surjectivity; Hilbert 90 is not applied before this correction. -/
theorem exists_exactNormOneRepresentative_of_criticalKernel
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (z : UnitGradedPiece K t)
    (hz : z ∈ (normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)).ker) :
    ∃ w : unitFiltration K t, normUnits F K (w : Kˣ) = 1 ∧
      unitGradedMk K t w = z := by
  obtain ⟨u, rfl⟩ := unitGradedMk_surjective K t z
  rw [MonoidHom.mem_ker, normUnitGraded_mk, unitGradedMk_eq_one_iff] at hz
  obtain ⟨v, hv, hnv⟩ := wild_norm_unitFiltration_surjective_break_succ F K
    ht htpos hres π hπ hgen (normUnits F K (u : Kˣ)) hz
  let w : Kˣ := (u : Kˣ) / v
  have hw : w ∈ unitFiltration K t :=
    (unitFiltration K t).div_mem u.property
      (unitFiltration_antitone K (Nat.le_succ t) hv)
  refine ⟨⟨w, hw⟩, ?_, ?_⟩
  · dsimp only [w]
    rw [_root_.map_div (normUnits F K), hnv]
    exact div_self' (normUnits F K (u : Kˣ))
  · apply (unitGradedMk_eq_mk_iff K t _ _).2
    rw [← div_mem_unitFiltration_iff_congruentAtDepth K (t + 1) w (u : Kˣ)
      (unitFiltration_le_unitGroup K t hw)
      (unitFiltration_le_unitGroup K t u.property)]
    dsimp only [w]
    have hvInv := (unitFiltration K (t + 1)).inv_mem hv
    have heq : ((u : Kˣ) / v) / (u : Kˣ) = v⁻¹ := by
      simp only [div_eq_mul_inv]
      rw [mul_comm (u : Kˣ) v⁻¹, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact hvInv

end CriticalWildKernel

section Hilbert90Correction

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Hilbert 90 is applied only after the critical kernel class has been corrected to exact norm
one.  Its orientation is recorded verbatim as `y / g(y) = w`. -/
theorem exists_hilbert90_coboundary_of_criticalKernel
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (z : UnitGradedPiece K t)
    (hz : z ∈ (normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)).ker) :
    ∃ w : unitFiltration K t,
      normUnits F K (w : Kˣ) = 1 ∧ unitGradedMk K t w = z ∧
      ∃ y : Kˣ, (y : K) / PrimeCyclicExtension.generator F K (y : K) = (w : Kˣ) := by
  obtain ⟨w, hwNorm, hwClass⟩ :=
    exists_exactNormOneRepresentative_of_criticalKernel F K ht htpos hres π hπ hgen z hz
  have hwNormField : norm F K ((w : Kˣ) : K) = 1 := by
    exact congrArg Units.val hwNorm
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one
    (g := PrimeCyclicExtension.generator F K)
    (PrimeCyclicExtension.generator_mem_zpowers F K) hwNormField
  exact ⟨w, hwNorm, hwClass, y, hy⟩

private theorem exactNormOne_class_mem_ramification_range
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (w : unitFiltration K t) (y : Kˣ)
    (hy : (y : K) / PrimeCyclicExtension.generator F K (y : K) = (w : Kˣ)) :
    unitGradedMk K t w ∈ (ramificationUnitGradedHom F K t π hπ hgen).range := by
  let g := PrimeCyclicExtension.generator F K
  let gT : lowerRamificationGroup F K (t : ℤ) :=
    ⟨g, by rw [ht.1]; trivial⟩
  let πU : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  let gy : Kˣ := Units.map (g : K →* K) y
  have hyU : y / gy = (w : Kˣ) := by
    apply Units.ext
    dsimp only [gy]
    rw [Units.val_div_eq_div_val, Units.coe_map]
    change (y : K) / g (y : K) = ((w : Kˣ) : K)
    exact hy
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff K).2 (Units.ne_zero y))
  let v : Kˣ := y / πU ^ m
  have hvord : ord K (v : K) = 0 := by
    dsimp only [v]
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val]
    dsimp only [πU]
    change ord K ((y : K) / (π : K) ^ m) = 0
    rw [ord_div, ord_zpow, ord_uniformizer K hπ]
    have hmone : m • (1 : WithTop ℤ) = (m : WithTop ℤ) := by
      cases m with
      | ofNat n => simp
      | negSucc n =>
          rw [negSucc_zsmul]
          norm_num [Int.negSucc_eq]
    rw [hmone, hm]
    simp
  let gv : Kˣ := Units.map (g : K →* K) v
  have hgvord : ord K (gv : K) = 0 := by
    change ord K (g (v : K)) = 0
    rw [ord_galoisConjugate, hvord]
  let vO : ringOfIntegers K :=
    ⟨(v : K), (ord_nonneg_iff_mem_integer K _).1 hvord.ge⟩
  have hact := (mem_lowerRamificationGroup F K g (t : ℤ)).1 gT.property vO
  change CongruentAtDepth ((t : ℤ) + 1) (gv : K) (v : K) at hact
  let f : Kˣ := v / gv
  have hfdeep : f ∈ unitFiltration K (t + 1) := by
    rw [mem_unitFiltration_succ, congruentAtDepth_iff_sub_mem_lattice K]
    dsimp only [f]
    rw [Units.val_div_eq_div_val]
    change (v : K) / (gv : K) - 1 ∈ lattice K (((t + 1 : ℕ) : ℤ))
    rw [div_sub_one (Units.ne_zero gv)]
    rw [div_mem_lattice_iff K (gv : K) ((v : K) - (gv : K)) 0
      (((t + 1 : ℕ) : ℤ)) hgvord]
    have hneg : (v : K) - (gv : K) ∈ lattice K ((t : ℤ) + 1) := by
      simpa only [neg_sub] using (lattice K ((t : ℤ) + 1)).neg_mem hact
    simpa only [Nat.cast_add, Nat.cast_one, zero_add] using hneg
  let ρ : Kˣ := ramificationRatioUnit F K t gT (π : K) hπ
  have hρmem : ρ ∈ unitFiltration K t :=
    ramificationRatioUnit_mem F K t gT (π : K) hπ
  have hgv : gv = gy / (Units.map (g : K →* K) πU) ^ m := by
    dsimp only [gv, v, gy]
    rw [_root_.map_div, map_zpow]
  have hρ : ρ = Units.map (g : K →* K) πU / πU := by
    apply Units.ext
    dsimp only [ρ]
    rw [coe_ramificationRatioUnit, Units.val_div_eq_div_val, Units.coe_map]
    dsimp only [gT, πU]
    change g (π : K) / (π : K) = g (π : K) / (π : K)
    rfl
  have hwfactor : (w : Kˣ) = f * ρ ^ (-m) := by
    rw [← hyU]
    dsimp only [f, v]
    rw [hgv, hρ]
    simp only [div_eq_mul_inv, mul_zpow, mul_inv_rev, inv_zpow,
      ← zpow_neg, neg_neg]
    calc
      y * gy⁻¹ = y * gy⁻¹ *
          ((πU ^ (-m) * πU ^ m) *
            ((Units.map (g : K →* K) πU) ^ m *
              (Units.map (g : K →* K) πU) ^ (-m))) := by
        rw [← zpow_add, ← zpow_add]
        simp
      _ = _ := by ac_rfl
  let f₀ : unitFiltration K t :=
    ⟨f, unitFiltration_antitone K (Nat.le_succ t) hfdeep⟩
  let ρ₀ : unitFiltration K t := ⟨ρ, hρmem⟩
  have hwSubtype : w = f₀ * ρ₀ ^ (-m) := by
    apply Subtype.ext
    exact hwfactor
  refine ⟨(lowerRamificationGradedMk F K (t : ℤ) gT) ^ (-m), ?_⟩
  have hfOne : unitGradedMk K t f₀ = 1 :=
    (unitGradedMk_eq_one_iff K t f₀).2 hfdeep
  have hρClass :
      (ramificationUnitGradedHom F K t π hπ hgen)
          (lowerRamificationGradedMk F K (t : ℤ) gT) =
        unitGradedMk K t ρ₀ := by
    rw [ramificationUnitGradedHom_mk]
  calc
    (ramificationUnitGradedHom F K t π hπ hgen)
        ((lowerRamificationGradedMk F K (t : ℤ) gT) ^ (-m)) =
        ((ramificationUnitGradedHom F K t π hπ hgen)
          (lowerRamificationGradedMk F K (t : ℤ) gT)) ^ (-m) :=
      map_zpow (ramificationUnitGradedHom F K t π hπ hgen)
        (lowerRamificationGradedMk F K (t : ℤ) gT) (-m)
    _ = (unitGradedMk K t ρ₀) ^ (-m) := congrArg (fun q => q ^ (-m)) hρClass
    _ = unitGradedMk K t (ρ₀ ^ (-m)) :=
      (map_zpow (unitGradedMk K t) ρ₀ (-m)).symm
    _ = unitGradedMk K t (f₀ * ρ₀ ^ (-m)) := by
      have hmul := map_mul (unitGradedMk K t) f₀ (ρ₀ ^ (-m))
      rw [hfOne] at hmul
      exact (one_mul _).symm.trans hmul.symm
    _ = unitGradedMk K t w := by rw [← hwSubtype]

/-- At a positive break the critical graded kernel is exactly the image of the injective
ramification map. -/
theorem gradedNorm_kernel_positiveBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    (normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres π hπ hgen)).ker =
      (ramificationUnitGradedHom F K t π hπ hgen).range := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, _hwNorm, hwClass, y, hy⟩ :=
      exists_hilbert90_coboundary_of_criticalKernel F K ht htpos hres π hπ hgen z hz
    rw [← hwClass]
    exact exactNormOne_class_mem_ramification_range F K ht π hπ hgen w y hy
  · exact ramificationUnitGradedHom_le_normUnitGraded_ker F K
      ht htpos hres π hπ hgen

end Hilbert90Correction

section TameNormCongruences

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- In a totally ramified extension, the norm of a principal unit is again principal. -/
theorem norm_one_add_sub_one_mem_lattice_one_of_residueDegree_eq_one
    (hres : residueDegree F K = 1)
    (x : K) (hx : ((1 : ℕ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 ∈ lattice F 1 := by
  let p := Module.finrank F K
  have hp : 0 < p := Module.finrank_pos
  have hram : ramificationIndex F K = p := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjpos : 1 ≤ j + 1 := by omega
  have hjle : j + 1 ≤ p := by
    dsimp only [p]
    omega
  have hs := totallyRamified_elementarySymmetric_bound F K p 1 hp rfl hram hx
    (j + 1) hjle
  apply (show ((1 : ℤ) : WithTop ℤ) ≤
      (integerCeilingDiv (((j + 1 : ℕ) : ℤ) * 1) p : ℤ) by
    rw [WithTop.coe_le_coe]
    unfold integerCeilingDiv
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp)]
    push_cast
    omega).trans
  simpa only [mul_one] using hs

/-- At depths `p(n+1)`, every non-trace coefficient gains the next target level. -/
theorem tame_norm_one_add_sub_one_sub_trace_mem_lattice
    (hres : residueDegree F K = 1) (n : ℕ)
    (x : K)
    (hx : (((Module.finrank F K * (n + 1) : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x) :
    norm F K (1 + x) - 1 - trace F K x ∈ lattice F ((n + 2 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  let q := p * (n + 1)
  let s := n + 2
  have hp2 : 2 ≤ p := (PrimeCyclicExtension.degree_prime F K).two_le
  have hp : 0 < p := by omega
  have hram : ramificationIndex F K = p := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [show Module.finrank F K = (Module.finrank F K - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  rw [elementarySymmetric_one, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjtwo : 2 ≤ j + 1 + 1 := by omega
  have hjle : j + 1 + 1 ≤ p := by
    dsimp only [p]
    omega
  have hsymmetric := totallyRamified_elementarySymmetric_bound F K p (q : ℤ) hp
    rfl hram (by simpa only [q, p] using hx) (j + 1 + 1) hjle
  have hnat : p * s ≤ (j + 1 + 1) * q + (p - 1) := by
    calc
      p * s = p * (n + 2) := by rfl
      _ ≤ p * (2 * (n + 1)) := Nat.mul_le_mul_left p (by omega)
      _ = 2 * (p * (n + 1)) := by ring
      _ ≤ (j + 1 + 1) * (p * (n + 1)) := by
        gcongr
      _ ≤ (j + 1 + 1) * q + (p - 1) := by
        dsimp only [q]
        exact Nat.le_add_right _ _
  apply (show ((s : ℕ) : WithTop ℤ) ≤
      (integerCeilingDiv (((j + 1 + 1 : ℕ) : ℤ) * (q : ℤ)) p : ℤ) by
    exact_mod_cast (show (s : ℤ) ≤
      integerCeilingDiv (((j + 1 + 1 : ℕ) : ℤ) * (q : ℤ)) p by
      unfold integerCeilingDiv
      rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp)]
      have hp1 : 1 ≤ p := hp
      have hnatZ : ((p * s : ℕ) : ℤ) ≤
          (((j + 1 + 1) * q + (p - 1) : ℕ) : ℤ) := by
        exact_mod_cast hnat
      calc
        (s : ℤ) * (p : ℤ) = ((p * s : ℕ) : ℤ) := by push_cast; ring
        _ ≤ (((j + 1 + 1) * q + (p - 1) : ℕ) : ℤ) := hnatZ
        _ = ((j + 1 + 1 : ℕ) : ℤ) * (q : ℤ) + (p : ℤ) - 1 := by
          push_cast [Nat.cast_sub hp1]
          ring)
    ).trans hsymmetric

/-- In a totally ramified extension the norm preserves the first principal-unit layer. -/
theorem normMapsUnitFiltration_one_of_residueDegree_eq_one
    (hres : residueDegree F K = 1) :
    NormMapsUnitFiltration F K 1 1 := by
  intro u hu
  rw [mem_unitFiltration_succ] at hu ⊢
  rw [congruentAtDepth_iff_sub_mem_lattice K] at hu
  rw [congruentAtDepth_iff_sub_mem_lattice F]
  change norm F K (u : K) - 1 ∈ lattice F 1
  rw [show (u : K) = 1 + ((u : K) - 1) by ring]
  exact norm_one_add_sub_one_mem_lattice_one_of_residueDegree_eq_one F K hres
    ((u : K) - 1) hu

end TameNormCongruences

section TameDeepCorrection

open Filter Topology

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

private theorem exists_tame_norm_oneStep
    (hres : residueDegree F K = 1)
    (htraceSurj : ∀ (q r : ℤ),
      r = (q + (((Module.finrank F K - 1) * (0 + 1) : ℕ) : ℤ)) /
        (Module.finrank F K : ℤ) →
      ∀ (y : F), y ∈ lattice F r →
        ∃ x : K, x ∈ lattice K q ∧ trace F K x = y)
    (n : ℕ) (u : Fˣ) (hu : u ∈ unitFiltration F (1 + n)) :
    ∃ x : Kˣ,
      x ∈ unitFiltration K
        (Module.finrank F K * n + (Module.finrank F K - 1) + 1) ∧
      u / normUnits F K x ∈ unitFiltration F (1 + n + 1) := by
  let p := Module.finrank F K
  have hp2 : 2 ≤ p := (PrimeCyclicExtension.degree_prime F K).two_le
  have hp : 0 < p := by omega
  let a : ℕ := p * n + (p - 1)
  let q : ℕ := a + 1
  let r : ℕ := 1 + n
  let s : ℕ := r + 1
  have hy : (u : F) - 1 ∈ lattice F (r : ℤ) := by
    have hu' := (mem_unitFiltration_succ_iff_sub_mem_lattice F n u).1
      (by simpa only [r, Nat.add_comm] using hu)
    simpa only [r, Nat.add_comm] using hu'
  have hq : q = p * (n + 1) := by
    dsimp only [q, a]
    rw [show p * n + (p - 1) + 1 = p * n + ((p - 1) + 1) by omega,
      Nat.sub_add_cancel (show 1 ≤ p by omega)]
    ring
  have hfloor : (r : ℤ) =
      ((q : ℤ) + (((p - 1) * (0 + 1) : ℕ) : ℤ)) / (p : ℤ) := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
    rw [show ((q : ℕ) : ℤ) = (p : ℤ) * (r : ℤ) by
      rw [hq]
      exact_mod_cast (show p * (n + 1) = p * r by
        dsimp only [r]
        congr 1
        omega)]
    simp only [zero_add, mul_one]
    rw [show (p : ℤ) * (r : ℤ) + ((p - 1 : ℕ) : ℤ) =
        ((p - 1 : ℕ) : ℤ) + (r : ℤ) * (p : ℤ) by ring]
    rw [Int.add_mul_ediv_right _ _ hpZ.ne']
    have hsmall : (((p - 1 : ℕ) : ℤ) / (p : ℤ)) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast Nat.sub_lt hp Nat.zero_lt_one
    rw [hsmall, zero_add]
  obtain ⟨z, hz, htracez⟩ := htraceSurj (q : ℤ) (r : ℤ)
    (by simpa only [p] using hfloor) ((u : F) - 1) hy
  have hzord : (((Module.finrank F K * (n + 1) : ℕ) : ℤ) : WithTop ℤ) ≤
      ord K z := by
    rw [mem_lattice] at hz
    simpa only [hq, p] using hz
  have hrem := tame_norm_one_add_sub_one_sub_trace_mem_lattice F K hres n z hzord
  have hrem' : norm F K (1 + z) - 1 - trace F K z ∈ lattice F (s : ℤ) := by
    simpa only [s, r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrem
  let x : Kˣ := principalUnitOf K a z (by simpa only [q, a] using hz)
  have hx : x ∈ unitFiltration K (a + 1) :=
    principalUnitOf_mem K a z (by simpa only [q, a] using hz)
  refine ⟨x, by simpa only [a, p, Nat.add_assoc] using hx, ?_⟩
  have hun : u ∈ unitGroup F := unitFiltration_le_unitGroup F _ hu
  have hx0 : x ∈ unitGroup K := unitFiltration_le_unitGroup K _ hx
  have hnorm0 : normUnits F K x ∈ unitGroup F := by
    rw [mem_unitGroup_iff_ord_eq_zero]
    change ord F (norm F K (x : K)) = 0
    rw [ord_norm, (mem_unitGroup_iff_ord_eq_zero K x).1 hx0]
    simp
  change u / normUnits F K x ∈ unitFiltration F s
  rw [div_mem_unitFiltration_iff_congruentAtDepth F s u
    (normUnits F K x) hun hnorm0]
  rw [CongruentAtDepth]
  change ((s : ℤ) : WithTop ℤ) ≤ ord F ((u : F) - norm F K (x : K))
  have hdiff : (u : F) - norm F K (x : K) ∈ lattice F (s : ℤ) := by
    have hpos : norm F K (x : K) - (u : F) ∈ lattice F (s : ℤ) := by
      change norm F K (1 + z) - (u : F) ∈ lattice F (s : ℤ)
      convert hrem' using 1
      rw [htracez]
      ring
    have hneg := (lattice F (s : ℤ)).neg_mem hpos
    convert hneg using 1 <;> ring
  exact hdiff

private theorem tame_norm_unitFiltration_surjective_one
    (hres : residueDegree F K = 1)
    (htraceSurj : ∀ (q r : ℤ),
      r = (q + (((Module.finrank F K - 1) * (0 + 1) : ℕ) : ℤ)) /
        (Module.finrank F K : ℤ) →
      ∀ (y : F), y ∈ lattice F r →
        ∃ x : K, x ∈ lattice K q ∧ trace F K x = y) :
    ∀ u : Fˣ, u ∈ unitFiltration F 1 →
      ∃ x : Kˣ, x ∈ unitFiltration K 1 ∧ normUnits F K x = u := by
  let p := Module.finrank F K
  have hp : 0 < p := Module.finrank_pos
  have hlift := successiveLifting_surjective
    (norm F K) (continuous_norm F K)
    (fun n ↦ p * n + (p - 1)) 1
    (by
      intro a b hab
      exact Nat.add_le_add_right (Nat.mul_le_mul_left p hab) (p - 1))
    (by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      have hpn : n ≤ p * n := by
        simpa only [one_mul] using Nat.mul_le_mul_right n (show 1 ≤ p by omega)
      omega)
    (by
      intro n u hu
      exact exists_tame_norm_oneStep F K hres htraceSurj n u hu)
  intro u hu
  obtain ⟨x, hx, hnorm⟩ := hlift u hu
  refine ⟨x, unitFiltration_antitone K ?_ hx, hnorm⟩
  dsimp only [p]
  omega

/-- A trace-controlled correction above the tame critical layer. -/
theorem exists_tame_norm_aboveBreak_oneStep
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (n : ℕ) (u : Fˣ) (hu : u ∈ unitFiltration F (1 + n)) :
    ∃ x : Kˣ,
      x ∈ unitFiltration K
        (Module.finrank F K * n + (Module.finrank F K - 1) + 1) ∧
      u / normUnits F K x ∈ unitFiltration F (1 + n + 1) := by
  exact exists_tame_norm_oneStep F K hres
    (fun q r hr y hy ↦
      trace_lattice_surjective_of_integralGenerator F K ht hres pi hpi hgen
        q r hr y hy) n u hu

/-- Every first principal unit of the base is exactly a norm in the tame case. -/
theorem tame_norm_unitFiltration_surjective_break_succ
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    ∀ u : Fˣ, u ∈ unitFiltration F 1 →
      ∃ x : Kˣ, x ∈ unitFiltration K 1 ∧ normUnits F K x = u := by
  apply tame_norm_unitFiltration_surjective_one F K hres
  intro q r hr y hy
  exact trace_lattice_surjective_of_integralGenerator F K ht hres pi hpi hgen
    q r hr y hy

end TameDeepCorrection

section TameCriticalKernel

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- At the tame break the ramification coordinate has trivial graded norm. -/
theorem tame_ramificationUnitGradedHom_le_normUnitGraded_ker
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (ramificationUnitGradedHom F K 0 pi hpi hgen).range ≤
      (normUnitGraded F K 0
        (normMapsUnitFiltration_zero F K)
        (normMapsUnitFiltration_one_of_residueDegree_eq_one F K hres)).ker := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨sigma, rfl⟩ := lowerRamificationQuotientMk_surjective F K
    (show (0 : ℤ) ≤ (0 : ℤ) + 1 by omega) z
  change normUnitGraded F K 0 _ _
    (ramificationUnitGradedHom F K 0 pi hpi hgen
      (lowerRamificationGradedMk F K (0 : ℤ) sigma)) = 1
  change normUnitGraded F K 0 _ _
    (unitGradedMk K 0
      ⟨ramificationRatioUnit F K 0 sigma (pi : K) hpi,
        ramificationRatioUnit_mem F K 0 sigma (pi : K) hpi⟩) = 1
  rw [normUnitGraded_mk, unitGradedMk_eq_one_iff]
  simpa only [coe_normBelowBreakUnitFiltrationHom,
    norm_ramificationRatioUnit_eq_one F K 0 sigma (pi : K) hpi] using
      (unitFiltration F 1).one_mem

/-- A tame critical kernel class can be corrected inside `U_K^1` to exact norm one. -/
theorem exists_tame_exactNormOneRepresentative_of_criticalKernel
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : UnitGradedPiece K 0)
    (hz : z ∈ (normUnitGraded F K 0
      (normMapsUnitFiltration_zero F K)
      (normMapsUnitFiltration_one_of_residueDegree_eq_one F K hres)).ker) :
    ∃ w : unitFiltration K 0, normUnits F K (w : Kˣ) = 1 ∧
      unitGradedMk K 0 w = z := by
  obtain ⟨u, rfl⟩ := unitGradedMk_surjective K 0 z
  rw [MonoidHom.mem_ker, normUnitGraded_mk, unitGradedMk_eq_one_iff] at hz
  obtain ⟨v, hv, hnv⟩ := tame_norm_unitFiltration_surjective_break_succ F K
    ht hres pi hpi hgen (normUnits F K (u : Kˣ)) hz
  let w : Kˣ := (u : Kˣ) / v
  have hw : w ∈ unitFiltration K 0 :=
    (unitFiltration K 0).div_mem u.property
      (unitFiltration_antitone K (Nat.zero_le 1) hv)
  refine ⟨⟨w, hw⟩, ?_, ?_⟩
  · dsimp only [w]
    rw [_root_.map_div (normUnits F K), hnv]
    exact div_self' (normUnits F K (u : Kˣ))
  · apply (unitGradedMk_eq_mk_iff K 0 _ _).2
    rw [← div_mem_unitFiltration_iff_congruentAtDepth K 1 w (u : Kˣ)
      (unitFiltration_le_unitGroup K 0 hw)
      (unitFiltration_le_unitGroup K 0 u.property)]
    dsimp only [w]
    have hvInv := (unitFiltration K 1).inv_mem hv
    have heq : ((u : Kˣ) / v) / (u : Kˣ) = v⁻¹ := by
      simp only [div_eq_mul_inv]
      rw [mul_comm (u : Kˣ) v⁻¹, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact hvInv

end TameCriticalKernel

section TameHilbert90

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Hilbert 90 after the tame endpoint correction, with orientation `y/g(y)=w`. -/
theorem exists_tame_hilbert90_coboundary_of_criticalKernel
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : UnitGradedPiece K 0)
    (hz : z ∈ (normUnitGraded F K 0
      (normMapsUnitFiltration_zero F K)
      (normMapsUnitFiltration_one_of_residueDegree_eq_one F K hres)).ker) :
    ∃ w : unitFiltration K 0,
      normUnits F K (w : Kˣ) = 1 ∧ unitGradedMk K 0 w = z ∧
      ∃ y : Kˣ, (y : K) / PrimeCyclicExtension.generator F K (y : K) = (w : Kˣ) := by
  obtain ⟨w, hwNorm, hwClass⟩ :=
    exists_tame_exactNormOneRepresentative_of_criticalKernel F K
      ht hres pi hpi hgen z hz
  have hwNormField : norm F K ((w : Kˣ) : K) = 1 := congrArg Units.val hwNorm
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one
    (g := PrimeCyclicExtension.generator F K)
    (PrimeCyclicExtension.generator_mem_zpowers F K) hwNormField
  exact ⟨w, hwNorm, hwClass, y, hy⟩

/-- At the tame break the critical graded norm kernel is exactly the ramification image. -/
theorem gradedNorm_kernel_tameBreak
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (normUnitGraded F K 0
      (normMapsUnitFiltration_zero F K)
      (normMapsUnitFiltration_one_of_residueDegree_eq_one F K hres)).ker =
      (ramificationUnitGradedHom F K 0 pi hpi hgen).range := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, _hwNorm, hwClass, y, hy⟩ :=
      exists_tame_hilbert90_coboundary_of_criticalKernel F K
        ht hres pi hpi hgen z hz
    rw [← hwClass]
    exact exactNormOne_class_mem_ramification_range F K
      ht pi hpi hgen w y hy
  · exact tame_ramificationUnitGradedHom_le_normUnitGraded_ker F K
      ht hres pi hpi hgen

end TameHilbert90

section CriticalGradedNorm

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Norm preserves the critical numerator layer in both the tame (`t=0`) and positive-break
branches. -/
theorem normMapsUnitFiltration_atBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    NormMapsUnitFiltration F K t t := by
  by_cases ht0 : t = 0
  · subst t
    exact normMapsUnitFiltration_zero F K
  · exact wild_normMapsUnitFiltration F K ht (Nat.pos_of_ne_zero ht0)
      (by omega) hres pi hpi hgen

/-- Norm preserves the denominator one step beyond the critical layer.  At `t=0` this is
principal-unit containment; at `t>0` it is the last same-numbered wild containment. -/
theorem normMapsUnitFiltration_break_succ
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    NormMapsUnitFiltration F K (t + 1) (t + 1) := by
  by_cases ht0 : t = 0
  · subst t
    simpa only [zero_add] using
      normMapsUnitFiltration_one_of_residueDegree_eq_one F K hres
  · exact wild_normMapsUnitFiltration F K ht (Nat.pos_of_ne_zero ht0)
      (by omega) hres pi hpi hgen

/-- The exact norm homomorphism on the critical quotient
`U_K^t/U_K^(t+1) → U_F^t/U_F^(t+1)`.  The numerator and denominator
well-definedness proofs are supplied separately. -/
noncomputable def criticalGradedNorm
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    UnitGradedPiece K t →* UnitGradedPiece F t :=
  normUnitGraded F K t
    (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)
    (normMapsUnitFiltration_break_succ F K ht hres pi hpi hgen)

@[simp]
theorem criticalGradedNorm_mk
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : unitFiltration K t) :
    criticalGradedNorm F K ht hres pi hpi hgen (unitGradedMk K t u) =
      unitGradedMk F t
        (normBelowBreakUnitFiltrationHom F K t t
          (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen) u) :=
  rfl

end CriticalGradedNorm

section CriticalCardinality

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

private theorem lowerRamificationGraded_card_at_break
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    Nat.card (LowerRamificationGraded F K (t : ℤ)) = Module.finrank F K := by
  let hij : (t : ℤ) ≤ (t : ℤ) + 1 := by omega
  have hinside : lowerRamificationGroupInside F K hij = ⊥ := by
    ext sigma
    rw [mem_lowerRamificationGroupInside, ht.2, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [lowerRamificationQuotient_natCard F K hij, hinside, Subgroup.index_bot,
    ht.1, Subgroup.card_top, PrimeCyclicExtension.galoisCard_eq_degree F K]

private theorem card_cokernel_eq_card_kernel_of_card_eq
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hcard : Nat.card G = Nat.card H) :
    Nat.card (H ⧸ f.range) = Nat.card f.ker := by
  have hker := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hrange := Subgroup.card_eq_card_quotient_mul_card_subgroup f.range
  have hfirstIso : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hmul : Nat.card f.range * Nat.card (H ⧸ f.range) =
      Nat.card f.range * Nat.card f.ker := by
    calc
      Nat.card f.range * Nat.card (H ⧸ f.range) = Nat.card H := by
        rw [mul_comm]
        exact hrange.symm
      _ = Nat.card G := hcard.symm
      _ = Nat.card (G ⧸ f.ker) * Nat.card f.ker := hker
      _ = Nat.card f.range * Nat.card f.ker := by rw [hfirstIso]
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.range)) hmul

/-- The critical graded kernel has exactly the prime extension degree many elements. -/
theorem criticalGradedNorm_kernel_card_positiveBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Nat.card ((normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)).ker) =
      Module.finrank F K := by
  rw [gradedNorm_kernel_positiveBreak F K ht htpos hres pi hpi hgen]
  calc
    Nat.card (ramificationUnitGradedHom F K t pi hpi hgen).range =
        Nat.card (LowerRamificationGraded F K (t : ℤ)) :=
      (Nat.card_congr (Equiv.ofInjective
        (ramificationUnitGradedHom F K t pi hpi hgen)
        (ramificationUnitGradedHom_injective F K t pi hpi hgen))).symm
    _ = Module.finrank F K := lowerRamificationGraded_card_at_break F K ht

/-- At the positive break, the ramification coordinate followed by the graded norm is an
exact pair of multiplicative homomorphisms. -/
theorem ramification_gradedNorm_mulExact_positiveBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.MulExact
      (ramificationUnitGradedHom F K t pi hpi hgen)
      (normUnitGraded F K t
        (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
        (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)) := by
  rw [MonoidHom.mulExact_iff]
  exact gradedNorm_kernel_positiveBreak F K ht htpos hres pi hpi hgen

/-- The quotient of the critical target graded line by the norm image has exactly the prime
extension degree many elements. -/
theorem criticalGradedNorm_cokernel_card_positiveBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Nat.card (UnitGradedPiece F t ⧸
      (normUnitGraded F K t
        (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
        (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)).range) =
      Module.finrank F K := by
  let f : UnitGradedPiece K t →* UnitGradedPiece F t :=
    normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
  change Nat.card (UnitGradedPiece F t ⧸ f.range) = Module.finrank F K
  calc
    Nat.card (UnitGradedPiece F t ⧸ f.range) = Nat.card f.ker :=
      card_cokernel_eq_card_kernel_of_card_eq f
        (unitGradedPiece_card_eq_of_residueDegree_eq_one F K t hres)
    _ = Module.finrank F K := by
      dsimp only [f]
      exact criticalGradedNorm_kernel_card_positiveBreak F K ht htpos hres pi hpi hgen

/-- Equivalently, the critical norm image has cardinality `residueCard F / [K:F]`;
the multiplication form avoids introducing truncated natural-number division. -/
theorem criticalGradedNorm_range_card_mul_degree
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Nat.card ((normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)).range) *
        Module.finrank F K = residueCard F := by
  let f : UnitGradedPiece K t →* UnitGradedPiece F t :=
    normUnitGraded F K t
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
      (wild_normMapsUnitFiltration F K ht htpos (by omega) hres pi hpi hgen)
  change Nat.card f.range * Module.finrank F K = residueCard F
  have hcoker : Nat.card (UnitGradedPiece F t ⧸ f.range) = Module.finrank F K := by
    dsimp only [f]
    exact criticalGradedNorm_cokernel_card_positiveBreak F K ht htpos hres pi hpi hgen
  calc
    Nat.card f.range * Module.finrank F K =
        Nat.card (UnitGradedPiece F t ⧸ f.range) * Nat.card f.range := by
      rw [hcoker, mul_comm]
    _ = Nat.card (UnitGradedPiece F t) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup f.range).symm
    _ = residueCard F := by
      rw [unitFiltrationQuotient_card F (Nat.le_succ t)]
      simp [htpos.ne']

end CriticalCardinality

/-- Principal critical-kernel theorem, including both the tame break `t=0` and every positive
break.  In each branch an approximate graded-kernel representative is first corrected to exact
norm one; only then is Hilbert 90 used to identify its class with the ramification image. -/
theorem gradedNorm_kernel
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (criticalGradedNorm F K ht hres pi hpi hgen).ker =
      (ramificationUnitGradedHom F K t pi hpi hgen).range := by
  by_cases ht0 : t = 0
  · subst t
    change (normUnitGraded F K 0 _ _).ker =
      (ramificationUnitGradedHom F K 0 pi hpi hgen).range
    exact gradedNorm_kernel_tameBreak F K ht hres pi hpi hgen
  · change (normUnitGraded F K t _ _).ker =
      (ramificationUnitGradedHom F K t pi hpi hgen).range
    exact gradedNorm_kernel_positiveBreak F K ht (Nat.pos_of_ne_zero ht0)
      hres pi hpi hgen

/-- The ramification map followed by the exact critical graded norm is exact, for both the
tame and positive-break branches. -/
theorem ramification_criticalGradedNorm_mulExact
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.MulExact
      (ramificationUnitGradedHom F K t pi hpi hgen)
      (criticalGradedNorm F K ht hres pi hpi hgen) := by
  rw [MonoidHom.mulExact_iff]
  exact gradedNorm_kernel F K ht hres pi hpi hgen

/-- At every unique break, including `t=0`, the critical graded norm kernel has order equal to
the prime extension degree. -/
theorem criticalGradedNorm_kernel_card
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Nat.card (criticalGradedNorm F K ht hres pi hpi hgen).ker =
      Module.finrank F K := by
  rw [gradedNorm_kernel F K ht hres pi hpi hgen]
  calc
    Nat.card (ramificationUnitGradedHom F K t pi hpi hgen).range =
        Nat.card (LowerRamificationGraded F K (t : ℤ)) :=
      (Nat.card_congr (Equiv.ofInjective
        (ramificationUnitGradedHom F K t pi hpi hgen)
        (ramificationUnitGradedHom_injective F K t pi hpi hgen))).symm
    _ = Module.finrank F K := lowerRamificationGraded_card_at_break F K ht

/-- The exact critical cokernel has order equal to the prime extension degree, including at
the tame break.  The source and target graded pieces have the same finite cardinality because
the residue degree is one. -/
theorem criticalGradedNorm_cokernel_card
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Nat.card (UnitGradedPiece F t ⧸
      (criticalGradedNorm F K ht hres pi hpi hgen).range) =
      Module.finrank F K := by
  let f : UnitGradedPiece K t →* UnitGradedPiece F t :=
    criticalGradedNorm F K ht hres pi hpi hgen
  change Nat.card (UnitGradedPiece F t ⧸ f.range) = Module.finrank F K
  calc
    Nat.card (UnitGradedPiece F t ⧸ f.range) = Nat.card f.ker :=
      card_cokernel_eq_card_kernel_of_card_eq f
        (unitGradedPiece_card_eq_of_residueDegree_eq_one F K t hres)
    _ = Module.finrank F K := by
      dsimp only [f]
      exact criticalGradedNorm_kernel_card F K ht hres pi hpi hgen

section CriticalNormPolynomial

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Divide a lattice element of integral depth by the matching uniformizer power and reduce. -/
private def criticalNormLatticeResiduePreAddHom (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi) (r : ℕ) :
    lattice E (r : ℤ) →+ ResidueField E where
  toFun x := residueMap E ⟨(x : E) / pi ^ r, (mem_lattice_zero_iff E).1 (by
    apply (div_mem_lattice_iff E (pi ^ r) (x : E) (r : ℤ) 0 (by
      rw [ord_pow, ord_uniformizer E hpi]
      norm_num)).2
    simpa using x.property)⟩
  map_zero' := by
    change residueMap E ⟨(0 : E) / pi ^ r, _⟩ = 0
    rw [show (⟨(0 : E) / pi ^ r, _⟩ : ringOfIntegers E) = 0 by ext; simp]
    exact map_zero _
  map_add' x y := by
    change residueMap E ⟨((x : E) + (y : E)) / pi ^ r, _⟩ =
      residueMap E ⟨(x : E) / pi ^ r, _⟩ + residueMap E ⟨(y : E) / pi ^ r, _⟩
    rw [← map_add]
    congr 1
    ext
    exact add_div _ _ _

private theorem criticalNormLatticeResiduePreAddHom_surjective (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi) (r : ℕ) :
    Function.Surjective (criticalNormLatticeResiduePreAddHom E pi hpi r) := by
  intro z
  let x : lattice E (r : ℤ) :=
    ⟨((teichmuller E z : ringOfIntegers E) : E) * pi ^ r, by
      have hz0 : ((teichmuller E z : ringOfIntegers E) : E) ∈ lattice E 0 :=
        (mem_lattice_zero_iff E).2 (teichmuller E z).property
      have hpir : pi ^ r ∈ lattice E (r : ℤ) := by
        rw [mem_lattice, ord_pow, ord_uniformizer E hpi]
        norm_num
      simpa using mul_mem_lattice E hz0 hpir⟩
  refine ⟨x, ?_⟩
  change residueMap E ⟨(x : E) / pi ^ r, _⟩ = z
  have hp : pi ^ r ≠ 0 := pow_ne_zero _ hpi.ne_zero
  rw [show (⟨(x : E) / pi ^ r, _⟩ : ringOfIntegers E) = teichmuller E z by
    ext
    dsimp only [x]
    exact mul_div_cancel_right₀ _ hp]
  exact residueMap_teichmuller E z

private theorem criticalNormLatticeResiduePreAddHom_ker (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi) (r : ℕ) :
    (criticalNormLatticeResiduePreAddHom E pi hpi r).ker =
      (latticeInside E (show (r : ℤ) ≤ (r : ℤ) + 1 by omega)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker]
  change residueMap E ⟨(x : E) / pi ^ r, _⟩ = 0 ↔ _
  rw [residueMap_eq_zero_iff]
  change (x : E) / pi ^ r ∈ lattice E 1 ↔
    x ∈ latticeInside E (show (r : ℤ) ≤ (r : ℤ) + 1 by omega)
  rw [mem_latticeInside]
  exact div_mem_lattice_iff E (pi ^ r) (x : E) (r : ℤ) 1 (by
    rw [ord_pow, ord_uniformizer E hpi]
    norm_num)

/-- The normalized residue coordinate on an integral lattice graded line. -/
noncomputable def criticalNormLatticeGradedResidueAddEquiv (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi) (r : ℕ) :
    LatticeGradedPiece E (r : ℤ) ≃+ ResidueField E :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (criticalNormLatticeResiduePreAddHom_ker E pi hpi r).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (criticalNormLatticeResiduePreAddHom E pi hpi r)
      (criticalNormLatticeResiduePreAddHom_surjective E pi hpi r))

@[simp]
theorem criticalNormLatticeGradedResidueAddEquiv_mk (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi) (r : ℕ)
    (x : lattice E (r : ℤ)) :
    criticalNormLatticeGradedResidueAddEquiv E pi hpi r
        (latticeQuotientMk E (show (r : ℤ) ≤ (r : ℤ) + 1 by omega) x) =
      reduce E ((x : E) / pi ^ r) (by
        apply (div_mem_lattice_iff E (pi ^ r) (x : E) (r : ℤ) 0 (by
          rw [ord_pow, ord_uniformizer E hpi]
          norm_num)).2
        simpa using x.property) := by
  rfl

/-- At any positive integral depth, normalized displacement identifies the unit graded line
with the residue field.  Positivity is explicit; no endpoint presentation `t=s+1` is retained
in the API. -/
noncomputable def criticalNormPositiveUnitGradedResidueAddEquiv
    {t : ℕ} (htpos : 0 < t) (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi) :
    Additive (UnitGradedPiece E t) ≃+ ResidueField E :=
  match t with
  | 0 => (Nat.not_lt_zero 0 htpos).elim
  | n + 1 => (positiveUnitGradedAddEquivLattice E n).trans
      (criticalNormLatticeGradedResidueAddEquiv E pi hpi (n + 1))

@[simp]
theorem criticalNormPositiveUnitGradedResidueAddEquiv_mk
    {t : ℕ} (htpos : 0 < t) (pi : E)
    (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (u : unitFiltration E t) :
    criticalNormPositiveUnitGradedResidueAddEquiv E htpos pi hpi
        (Additive.ofMul (unitGradedMk E t u)) =
      reduce E ((((u : Eˣ) : E) - 1) / pi ^ t) (by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
        apply (div_mem_lattice_iff E (pi ^ (n + 1)) (((u : Eˣ) : E) - 1)
          (n + 1 : ℤ) 0 (by
            rw [ord_pow, ord_uniformizer E hpi]
            norm_num)).2
        simpa using (unitFiltrationDisplacement E n u).property) := by
  cases t with
  | zero => omega
  | succ n => rfl

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- The canonical residue-field equivalence supplied by residue degree one. -/
noncomputable def criticalNormResidueEquiv
    (hres : residueDegree F K = 1) : ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K, hres]
    have hdim : Module.finrank (ResidueField F) (ResidueField F) =
        Module.finrank (ResidueField F) (ResidueField K) := by
      simp [hfin]
    have hinj : Function.Injective
        (Algebra.linearMap (ResidueField F) (ResidueField K)) :=
      (algebraMap (ResidueField F) (ResidueField K)).injective
    have hsurj :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by simpa only [Algebra.linearMap_apply] using hx⟩

@[simp]
theorem criticalNormResidueEquiv_apply
    (hres : residueDegree F K = 1) (z : ResidueField F) :
    criticalNormResidueEquiv F K hres z = extensionResidueMap F K z :=
  rfl

/-- The lower uniformizer used to normalize the critical norm polynomial. -/
def criticalNormLowerUniformizer (pi : ringOfIntegers K) : F :=
  norm F K (pi : K)

theorem criticalNormLowerUniformizer_isUniformizer
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    (ValuativeRel.valuation F).IsUniformizer
      (criticalNormLowerUniformizer F K pi) := by
  rw [← ord_eq_one_iff_isUniformizer, criticalNormLowerUniformizer, ord_norm,
    hres, one_nsmul, ord_uniformizer K hpi]

/-- The canonical source displacement with residue coordinate `z` at depth `t`. -/
def criticalNormSourceDisplacement (t : ℕ) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (z : ResidueField F) : lattice K (t : ℤ) :=
  ⟨algebraMap F K (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t, by
    have hzF : (((teichmuller F z : ringOfIntegers F) : F)) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 (teichmuller F z).property
    have hzK : algebraMap F K
        (((teichmuller F z : ringOfIntegers F) : F)) ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap]
      exact nsmul_nonneg hzF (ramificationIndex F K)
    have hpit : (pi : K) ^ t ∈ lattice K (t : ℤ) := by
      rw [mem_lattice, ord_pow, ord_uniformizer K hpi]
      norm_num
    simpa using mul_mem_lattice K hzK hpit⟩

/-- The principal source unit at a positive critical depth. -/
noncomputable def criticalNormSourceUnit
    {t : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (z : ResidueField F) : unitFiltration K t :=
  match t with
  | 0 => (Nat.not_lt_zero 0 htpos).elim
  | n + 1 =>
      ⟨principalUnitOf K n
          (criticalNormSourceDisplacement F K (n + 1) pi hpi z)
          (criticalNormSourceDisplacement F K (n + 1) pi hpi z).property,
        principalUnitOf_mem K n
          (criticalNormSourceDisplacement F K (n + 1) pi hpi z)
          (criticalNormSourceDisplacement F K (n + 1) pi hpi z).property⟩

@[simp]
theorem coe_criticalNormSourceUnit
    {t : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (z : ResidueField F) :
    (((criticalNormSourceUnit F K htpos pi hpi z : unitFiltration K t) : Kˣ) : K) =
      1 + algebraMap F K (((teichmuller F z : ringOfIntegers F) : F)) *
        (pi : K) ^ t := by
  cases t with
  | zero => omega
  | succ n => rfl

/-- The fixed generator viewed in the lower ramification group at the break. -/
noncomputable def criticalNormBreakGenerator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    lowerRamificationGroup F K (t : ℤ) :=
  ⟨PrimeCyclicExtension.generator F K, by rw [ht.1]; trivial⟩

/-- The fixed generator's class on the critical ramification graded line. -/
noncomputable def criticalNormGradedGenerator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    LowerRamificationGraded F K (t : ℤ) :=
  lowerRamificationGradedMk F K (t : ℤ) (criticalNormBreakGenerator F K ht)

/-- The upper-residue ramification displacement of the fixed cyclic generator. -/
noncomputable def criticalNormUpperRamificationLambda
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) : ResidueField K :=
  lowerRamificationResidueDisplacement F K (criticalNormBreakGenerator F K ht)
    (pi : K) hpi

/-- The base-residue ramification coefficient in the canonical residue-degree-one coordinate. -/
noncomputable def criticalNormRamificationLambda
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) : ResidueField F :=
  (criticalNormResidueEquiv F K hres).symm
    (criticalNormUpperRamificationLambda F K ht pi hpi)

@[simp]
theorem criticalNormResidueEquiv_ramificationLambda
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    criticalNormResidueEquiv F K hres
        (criticalNormRamificationLambda F K ht hres pi hpi) =
      criticalNormUpperRamificationLambda F K ht pi hpi :=
  (criticalNormResidueEquiv F K hres).apply_symm_apply _

theorem criticalNormRamificationLambda_ne_zero
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    criticalNormRamificationLambda F K ht hres pi hpi ≠ 0 := by
  intro hz
  have hzK := congrArg (criticalNormResidueEquiv F K hres) hz
  have hupper : criticalNormUpperRamificationLambda F K ht pi hpi ≠ 0 := by
    apply lowerRamificationResidueDisplacement_ne_zero F K _ pi hpi hgen
    exact (PrimeCyclicExtension.generator_mem_break_and_not_mem_succ F K ht).2
  apply hupper
  rw [criticalNormRamificationLambda,
    (criticalNormResidueEquiv F K hres).apply_symm_apply, map_zero] at hzK
  exact hzK

/-- The trace of a critical-depth element remains in the equally numbered lower lattice. -/
theorem criticalNormTrace_mem
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K) (hx : x ∈ lattice K (t : ℤ)) :
    trace F K x ∈ lattice F (t : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  have hmap := traceIdealLowerBound_of_integralGenerator F K
    ht hres pi hpi hgen (t : ℤ) x hx
  have hp : 0 < Module.finrank F K := Module.finrank_pos
  have heq :
      ((t : ℤ) +
          (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) /
          (Module.finrank F K : ℤ) = (t : ℤ) := by
    have hnumNat :
        t + (Module.finrank F K - 1) * (t + 1) =
          Module.finrank F K * t + (Module.finrank F K - 1) := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      rw [hd]
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    have hnum :
        (t : ℤ) + (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) =
          (Module.finrank F K : ℤ) * (t : ℤ) +
            ((Module.finrank F K - 1 : ℕ) : ℤ) := by
      exact_mod_cast hnumNat
    rw [hnum, Int.mul_add_ediv_left _ _ (by exact_mod_cast hp.ne')]
    have hsmall :
        (((Module.finrank F K - 1 : ℕ) : ℤ) /
            (Module.finrank F K : ℤ)) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast Nat.sub_lt hp Nat.zero_lt_one
    rw [hsmall, add_zero]
  rw [heq] at hmap
  exact hmap

/-- The normalized critical trace coefficient. -/
noncomputable def criticalNormLinearCoefficient
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) : ResidueField F :=
  reduce F
    (trace F K ((pi : K) ^ t) / (criticalNormLowerUniformizer F K pi) ^ t) (by
      apply (div_mem_lattice_iff F
        ((criticalNormLowerUniformizer F K pi) ^ t)
        (trace F K ((pi : K) ^ t)) (t : ℤ) 0 (by
          rw [ord_pow, ord_uniformizer F
            (criticalNormLowerUniformizer_isUniformizer F K hres pi hpi)]
          norm_num)).2
      exact criticalNormTrace_mem F K ht hres pi hpi hgen _ (by
        rw [mem_lattice, ord_pow, ord_uniformizer K hpi]
        norm_num))

/-- The critical norm map in normalized residue coordinates. -/
noncomputable def criticalNormPolynomialValue
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) : ResidueField F :=
  criticalNormPositiveUnitGradedResidueAddEquiv F htpos
    (criticalNormLowerUniformizer F K pi)
    (criticalNormLowerUniformizer_isUniformizer F K hres pi hpi)
    (Additive.ofMul
      (criticalGradedNorm F K ht hres pi hpi hgen
        (unitGradedMk K t (criticalNormSourceUnit F K htpos pi hpi z))))

theorem criticalNormPolynomialValue_raw
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    criticalNormPolynomialValue F K ht htpos hres pi hpi hgen z =
      reduce F
        ((norm F K
            (1 + algebraMap F K
              (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t) - 1) /
          (criticalNormLowerUniformizer F K pi) ^ t) (by
            have hu := (normBelowBreakUnitFiltrationHom F K t t
              (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)
              (criticalNormSourceUnit F K htpos pi hpi z)).property
            have hdisp :
                norm F K
                    (1 + algebraMap F K
                      (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t) - 1 ∈
                  lattice F (t : ℤ) := by
              have hu' :
                  ((normBelowBreakUnitFiltrationHom F K t t
                    (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)
                    (criticalNormSourceUnit F K htpos pi hpi z) :
                      unitFiltration F t) : Fˣ) ∈
                    unitFiltration F (t - 1 + 1) := by
                simpa only [Nat.sub_add_cancel htpos] using hu
              have hd := (mem_unitFiltration_succ_iff_sub_mem_lattice F (t - 1) _).1 hu'
              simpa only [Nat.sub_add_cancel htpos,
                coe_normBelowBreakUnitFiltrationHom,
                coe_normUnits, coe_criticalNormSourceUnit] using hd
            apply (div_mem_lattice_iff F
              ((criticalNormLowerUniformizer F K pi) ^ t)
              (norm F K
                (1 + algebraMap F K
                  (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t) - 1)
              (t : ℤ) 0 (by
                rw [ord_pow, ord_uniformizer F
                  (criticalNormLowerUniformizer_isUniformizer F K hres pi hpi)]
                norm_num)).2
            simpa only [add_zero] using hdisp) := by
  rw [criticalNormPolynomialValue, criticalGradedNorm_mk,
    criticalNormPositiveUnitGradedResidueAddEquiv_mk]
  simp only [coe_normBelowBreakUnitFiltrationHom, coe_normUnits,
    coe_criticalNormSourceUnit]

theorem criticalNormPolynomialValue_eq
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    criticalNormPolynomialValue F K ht htpos hres pi hpi hgen z =
      z ^ Module.finrank F K +
        criticalNormLinearCoefficient F K ht hres pi hpi hgen * z := by
  rw [criticalNormPolynomialValue_raw]
  let p := Module.finrank F K
  let piF := criticalNormLowerUniformizer F K pi
  let aO : ringOfIntegers F := teichmuller F z
  let a : F := (aO : F)
  let x : K := algebraMap F K a * (pi : K) ^ t
  let c : F := trace F K ((pi : K) ^ t) / piF ^ t
  have hpiF : (ValuativeRel.valuation F).IsUniformizer piF :=
    criticalNormLowerUniformizer_isUniformizer F K hres pi hpi
  have hpiF0 : piF ^ t ≠ 0 := pow_ne_zero _ hpiF.ne_zero
  have hxord : ((t : ℕ) : WithTop ℤ) ≤ ord K x := by
    dsimp only [x]
    rw [ord_mul, ord_algebraMap, ord_pow, ord_uniformizer K hpi]
    have ha : (0 : WithTop ℤ) ≤ ord F a :=
      (mem_lattice_zero_iff F).2 aO.property
    simpa [add_comm] using
      add_le_add_right (nsmul_nonneg ha (ramificationIndex F K))
        ((t : ℕ) : WithTop ℤ)
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht htpos pi hpi hgen
  have hcrit := wild_norm_critical_sub_trace_sub_norm_mem_lattice
    F K ht htpos hres hchar pi hpi hgen x hxord
  have hcInt : c ∈ lattice F 0 := by
    dsimp only [c, piF]
    apply (div_mem_lattice_iff F ((criticalNormLowerUniformizer F K pi) ^ t)
      (trace F K ((pi : K) ^ t)) (t : ℤ) 0 (by
        rw [ord_pow, ord_uniformizer F hpiF]
        norm_num)).2
    exact criticalNormTrace_mem F K ht hres pi hpi hgen _ (by
      rw [mem_lattice, ord_pow, ord_uniformizer K hpi]
      norm_num)
  have hbInt : a ^ p + c * a ∈ lattice F 0 :=
    add_mem_lattice F ((mem_lattice_zero_iff F).2 (aO ^ p).property)
      (mul_mem_lattice F hcInt ((mem_lattice_zero_iff F).2 aO.property))
  have htrace : trace F K x = a * trace F K ((pi : K) ^ t) := by
    dsimp only [x]
    simpa [Algebra.smul_def] using
      (Algebra.trace F K).map_smul a ((pi : K) ^ t)
  have hnorm : norm F K x = a ^ p * piF ^ t := by
    dsimp only [x, p, piF, criticalNormLowerUniformizer]
    rw [map_mul, norm_algebraMap, map_pow]
  have hdiv :
      (norm F K (1 + x) - 1 - trace F K x - norm F K x) / piF ^ t ∈
        lattice F 1 := by
    apply (div_mem_lattice_iff F (piF ^ t)
      (norm F K (1 + x) - 1 - trace F K x - norm F K x)
      (t : ℤ) 1 (by
        rw [ord_pow, ord_uniformizer F hpiF]
        norm_num)).2
    simpa only [Nat.cast_add, Nat.cast_one] using hcrit
  have hcongr : CongruentAtDepth 1
      ((norm F K (1 + x) - 1) / piF ^ t) (a ^ p + c * a) := by
    rw [congruentAtDepth_iff_sub_mem_lattice]
    convert hdiv using 1
    rw [htrace, hnorm]
    dsimp only [c]
    field_simp
    ring
  calc
    reduce F
        ((norm F K
            (1 + algebraMap F K
              (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t) - 1) /
          (criticalNormLowerUniformizer F K pi) ^ t) _ =
        reduce F (a ^ p + c * a) hbInt := by
          apply (reduce_eq_reduce_iff (F := F) _ hbInt).2
          simpa only [x, a, aO, piF] using hcongr
    _ = z ^ Module.finrank F K +
        criticalNormLinearCoefficient F K ht hres pi hpi hgen * z := by
      change residueMap F ⟨a ^ p + c * a, (mem_lattice_zero_iff F).1 hbInt⟩ = _
      let cO : ringOfIntegers F := ⟨c, (mem_lattice_zero_iff F).1 hcInt⟩
      have haReduce : residueMap F aO = z := residueMap_teichmuller F z
      have hcReduce : residueMap F cO =
          criticalNormLinearCoefficient F K ht hres pi hpi hgen := by
        rfl
      rw [show (⟨a ^ p + c * a, _⟩ : ringOfIntegers F) = aO ^ p + cO * aO by
        apply Subtype.ext
        rfl]
      simp only [map_add, map_pow, map_mul, haReduce, hcReduce, p]

@[simp]
theorem criticalNormSourceCoordinate
    {t : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (z : ResidueField F) :
    criticalNormPositiveUnitGradedResidueAddEquiv K htpos (pi : K) hpi
        (Additive.ofMul
          (unitGradedMk K t (criticalNormSourceUnit F K htpos pi hpi z))) =
      extensionResidueMap F K z := by
  rw [criticalNormPositiveUnitGradedResidueAddEquiv_mk]
  simp only [coe_criticalNormSourceUnit]
  change residueMap K
      ⟨((1 + algebraMap F K
          (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t) - 1) /
        (pi : K) ^ t, _⟩ = _
  have hp : (pi : K) ^ t ≠ 0 := pow_ne_zero _ hpi.ne_zero
  rw [show (⟨_, _⟩ : ringOfIntegers K) =
      algebraMap (ringOfIntegers F) (ringOfIntegers K) (teichmuller F z) by
    apply Subtype.ext
    calc
      ((1 + algebraMap F K
            (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ t - 1) /
          (pi : K) ^ t) =
          algebraMap F K (((teichmuller F z : ringOfIntegers F) : F)) := by
            simpa only [add_sub_cancel_left] using mul_div_cancel_right₀
              (algebraMap F K (((teichmuller F z : ringOfIntegers F) : F))) hp
      _ = algebraMap (ringOfIntegers F) K (teichmuller F z) := by
        have hcoeF : algebraMap (ringOfIntegers F) F (teichmuller F z) =
            (((teichmuller F z : ringOfIntegers F) : F)) :=
          congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers F))
            (teichmuller F z)
        rw [IsScalarTower.algebraMap_apply (ringOfIntegers F) F K, hcoeF]
      _ = ((algebraMap (ringOfIntegers F) (ringOfIntegers K)
          (teichmuller F z) : ringOfIntegers K) : K) := by
        have hcoeK : algebraMap (ringOfIntegers K) K
              (algebraMap (ringOfIntegers F) (ringOfIntegers K) (teichmuller F z)) =
            ((algebraMap (ringOfIntegers F) (ringOfIntegers K)
              (teichmuller F z) : ringOfIntegers K) : K) :=
          congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K))
            (algebraMap (ringOfIntegers F) (ringOfIntegers K) (teichmuller F z))
        exact (IsScalarTower.algebraMap_apply
          (ringOfIntegers F) (ringOfIntegers K) K (teichmuller F z)).trans hcoeK]
  change extensionResidueMap F K (residueMap F (teichmuller F z)) = _
  rw [residueMap_teichmuller]

@[simp]
theorem criticalNormPositiveRamificationCoordinate
    {t : ℕ} (htpos : 0 < t) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (sigma : lowerRamificationGroup F K (t : ℤ)) :
    criticalNormPositiveUnitGradedResidueAddEquiv K htpos (pi : K) hpi
        (Additive.ofMul
          (ramificationUnitGradedHom F K t pi hpi hgen
            (lowerRamificationGradedMk F K (t : ℤ) sigma))) =
      lowerRamificationResidueDisplacement F K sigma (pi : K) hpi := by
  rw [ramificationUnitGradedHom_mk,
    criticalNormPositiveUnitGradedResidueAddEquiv_mk]
  simp only [lowerRamificationResidueDisplacement,
    lowerRamificationNormalizedDisplacement]
  apply (reduce_eq_reduce_iff K _ _).2
  apply (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).2
  have hpi0 : (pi : K) ≠ 0 := hpi.ne_zero
  have heq :
      (((sigma : Gal(K/F)) (pi : K) / (pi : K) - 1) / (pi : K) ^ t) =
        ((sigma : Gal(K/F)) (pi : K) - (pi : K)) /
          (pi : K) ^ ((t : ℤ) + 1) := by
    rw [div_sub_one hpi0, div_div, zpow_add₀ hpi0]
    congr 1
    simp only [zpow_natCast, zpow_one]
    ac_rfl
  rw [coe_ramificationRatioUnit]
  change (((sigma : Gal(K/F)) (pi : K) / (pi : K) - 1) / (pi : K) ^ t) -
      ((sigma : Gal(K/F)) (pi : K) - (pi : K)) /
        (pi : K) ^ ((t : ℤ) + 1) ∈ lattice K 1
  rw [heq, sub_self]
  exact (lattice K 1).zero_mem

/-- The fixed cyclic generator identifies the additive group of `ZMod [K:F]` with the
Galois group. -/
noncomputable def criticalNormGaloisZModEquiv :
    Multiplicative (ZMod (Module.finrank F K)) ≃* Gal(K/F) :=
  zmodMulEquivOfGenerator
    (PrimeCyclicExtension.generator_mem_zpowers F K)
    (PrimeCyclicExtension.galoisCard_eq_degree F K)

theorem criticalNormGaloisZModEquiv_apply_val
    (u : ZMod (Module.finrank F K)) :
    criticalNormGaloisZModEquiv F K (Multiplicative.ofAdd u) =
      PrimeCyclicExtension.generator F K ^ (u.val : ℤ) := by
  letI : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
  calc
    criticalNormGaloisZModEquiv F K (Multiplicative.ofAdd u) =
        criticalNormGaloisZModEquiv F K
          (Multiplicative.ofAdd
            ((u.val : ℤ) : ZMod (Module.finrank F K))) := by
      congr 2
      simpa using (ZMod.natCast_zmod_val u).symm
    _ = PrimeCyclicExtension.generator F K ^ (u.val : ℤ) :=
      zmodMulEquivOfGenerator_apply_ofAdd_intCast
        (PrimeCyclicExtension.generator_mem_zpowers F K)
        (PrimeCyclicExtension.galoisCard_eq_degree F K) (u.val : ℤ)

/-- An arbitrary Galois element viewed in the full lower group at its unique break. -/
noncomputable def criticalNormLowerBreakElement
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (sigma : Gal(K/F)) : lowerRamificationGroup F K (t : ℤ) :=
  ⟨sigma, by rw [ht.1]; trivial⟩

theorem criticalNormGradedClass_zmod
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (u : ZMod (Module.finrank F K)) :
    lowerRamificationGradedMk F K (t : ℤ)
        (criticalNormLowerBreakElement F K ht
          (criticalNormGaloisZModEquiv F K (Multiplicative.ofAdd u))) =
      criticalNormGradedGenerator F K ht ^ u.val := by
  rw [criticalNormGaloisZModEquiv_apply_val]
  change lowerRamificationGradedMk F K (t : ℤ)
      (criticalNormLowerBreakElement F K ht
        (PrimeCyclicExtension.generator F K ^ (u.val : ℤ))) = _
  have hlower : criticalNormLowerBreakElement F K ht
      (PrimeCyclicExtension.generator F K ^ (u.val : ℤ)) =
      (criticalNormBreakGenerator F K ht) ^ (u.val : ℤ) := by
    apply Subtype.ext
    rfl
  rw [hlower, map_zpow]
  rfl

/-- Along the cyclic `ZMod [K:F]` enumeration, the actual ramification-line residues are
exactly `j * lambda`. -/
theorem criticalNormResidueDisplacement_zmod
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : ZMod (Module.finrank F K)) :
    lowerRamificationResidueDisplacement F K
        (criticalNormLowerBreakElement F K ht
          (criticalNormGaloisZModEquiv F K (Multiplicative.ofAdd u)))
        (pi : K) hpi =
      (u.val : ResidueField K) *
        criticalNormUpperRamificationLambda F K ht pi hpi := by
  rw [← criticalNormPositiveRamificationCoordinate F K htpos pi hpi hgen]
  rw [criticalNormGradedClass_zmod F K ht u]
  rw [map_pow, ofMul_pow, map_nsmul]
  have hgenerator :
      criticalNormPositiveUnitGradedResidueAddEquiv K htpos (pi : K) hpi
          (Additive.ofMul
            (ramificationUnitGradedHom F K t pi hpi hgen
              (criticalNormGradedGenerator F K ht))) =
        criticalNormUpperRamificationLambda F K ht pi hpi := by
    rw [criticalNormGradedGenerator,
      criticalNormPositiveRamificationCoordinate F K htpos pi hpi hgen]
    rfl
  rw [hgenerator, nsmul_eq_mul]

theorem criticalNormSourceClass_eq_generator
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    unitGradedMk K t
        (criticalNormSourceUnit F K htpos pi hpi
          (criticalNormRamificationLambda F K ht hres pi hpi)) =
      ramificationUnitGradedHom F K t pi hpi hgen
        (criticalNormGradedGenerator F K ht) := by
  change Additive.ofMul
      (unitGradedMk K t
        (criticalNormSourceUnit F K htpos pi hpi
          (criticalNormRamificationLambda F K ht hres pi hpi))) =
    Additive.ofMul
      (ramificationUnitGradedHom F K t pi hpi hgen
        (criticalNormGradedGenerator F K ht))
  apply (criticalNormPositiveUnitGradedResidueAddEquiv K htpos (pi : K) hpi).injective
  rw [criticalNormSourceCoordinate F K htpos pi hpi]
  change _ = criticalNormPositiveUnitGradedResidueAddEquiv K htpos (pi : K) hpi
    (Additive.ofMul
      (ramificationUnitGradedHom F K t pi hpi hgen
        (lowerRamificationGradedMk F K (t : ℤ)
          (criticalNormBreakGenerator F K ht))))
  rw [criticalNormPositiveRamificationCoordinate F K htpos pi hpi hgen]
  exact criticalNormResidueEquiv_ramificationLambda F K ht hres pi hpi

theorem criticalNormPolynomialValue_lambda_eq_zero
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    criticalNormPolynomialValue F K ht htpos hres pi hpi hgen
        (criticalNormRamificationLambda F K ht hres pi hpi) = 0 := by
  rw [criticalNormPolynomialValue,
    criticalNormSourceClass_eq_generator F K ht htpos hres pi hpi hgen]
  have hk :
      criticalGradedNorm F K ht hres pi hpi hgen
          (ramificationUnitGradedHom F K t pi hpi hgen
            (criticalNormGradedGenerator F K ht)) = 1 := by
    change ramificationUnitGradedHom F K t pi hpi hgen
        (criticalNormGradedGenerator F K ht) ∈
      (criticalGradedNorm F K ht hres pi hpi hgen).ker
    exact (ramificationUnitGradedHom_le_normUnitGraded_ker
      F K ht htpos hres pi hpi hgen) ⟨_, rfl⟩
  rw [hk]
  simp

/-- Exact positive-break critical norm polynomial in the normalized residue coordinate. -/
theorem criticalNormPolynomialValue_exact_of_positiveBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    criticalNormPolynomialValue F K ht htpos hres pi hpi hgen z =
      z ^ Module.finrank F K -
        criticalNormRamificationLambda F K ht hres pi hpi ^
          (Module.finrank F K - 1) * z := by
  have hz := criticalNormPolynomialValue_lambda_eq_zero
    F K ht htpos hres pi hpi hgen
  rw [criticalNormPolynomialValue_eq] at hz ⊢
  let lambda := criticalNormRamificationLambda F K ht hres pi hpi
  have hlambda : lambda ≠ 0 :=
    criticalNormRamificationLambda_ne_zero F K ht hres pi hpi hgen
  have hp : 0 < Module.finrank F K := Module.finrank_pos
  have hpow :
      lambda ^ Module.finrank F K =
        lambda ^ (Module.finrank F K - 1) * lambda := by
    calc
      lambda ^ Module.finrank F K =
          lambda ^ (Module.finrank F K - 1 + 1) := by
            congr 1
            omega
      _ = lambda ^ (Module.finrank F K - 1) * lambda := pow_succ _ _
  have hc : criticalNormLinearCoefficient F K ht hres pi hpi hgen =
      -lambda ^ (Module.finrank F K - 1) := by
    rw [hpow] at hz
    have hfactor :
        (lambda ^ (Module.finrank F K - 1) +
          criticalNormLinearCoefficient F K ht hres pi hpi hgen) * lambda = 0 := by
      calc
        _ = lambda ^ (Module.finrank F K - 1) * lambda +
            criticalNormLinearCoefficient F K ht hres pi hpi hgen * lambda := by ring
        _ = 0 := hz
    have hsum := (mul_eq_zero.mp hfactor).resolve_right hlambda
    linear_combination hsum
  rw [hc]
  ring

/-- The normalized critical trace coefficient is the negative `(p-1)`-st power of the
ramification lambda. -/
theorem criticalNormLinearCoefficient_eq_neg_ramificationLambda_pow
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (htpos : 0 < t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    criticalNormLinearCoefficient F K ht hres pi hpi hgen =
      -criticalNormRamificationLambda F K ht hres pi hpi ^
        (Module.finrank F K - 1) := by
  have h := criticalNormPolynomialValue_exact_of_positiveBreak
    F K ht htpos hres pi hpi hgen (1 : ResidueField F)
  rw [criticalNormPolynomialValue_eq] at h
  simp only [one_pow, mul_one] at h
  linear_combination h

end CriticalNormPolynomial

section BelowBreakLifting

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- The norm preserves every equally numbered unit layer at or below the break.  The `t=0`
branch contains only depth zero; every nonzero break uses the wild containment theorem. -/
theorem normMapsUnitFiltration_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i ≤ t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    NormMapsUnitFiltration F K i i := by
  by_cases ht0 : t = 0
  · subst t
    have hi : i = 0 := Nat.eq_zero_of_le_zero hit
    subst i
    exact normMapsUnitFiltration_zero F K
  · exact wild_normMapsUnitFiltration F K ht (Nat.pos_of_ne_zero ht0)
      (hit.trans (Nat.le_succ t)) hres pi hpi hgen

/-- Every graded norm strictly below the break is bijective.  If `t=0` there is no such
index, so the statement has no exceptional tame branch. -/
theorem gradedNorm_bijective_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Bijective (normUnitGraded F K i
      (normMapsUnitFiltration_belowBreak F K ht hit.le hres pi hpi hgen)
      (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)) := by
  exact normUnitGraded_bijective_belowBreak F K ht (by omega) hit
    hres pi hpi hgen

/-- Strictly below the break, the graded norm kernel is trivial. -/
theorem gradedNorm_kernel_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (normUnitGraded F K i
      (normMapsUnitFiltration_belowBreak F K ht hit.le hres pi hpi hgen)
      (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen).1

/-- Strictly below the break, the graded norm image is the whole target. -/
theorem gradedNorm_range_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (normUnitGraded F K i
      (normMapsUnitFiltration_belowBreak F K ht hit.le hres pi hpi hgen)
      (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen).2

private theorem lowerRamificationGraded_eq_one_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i < t) (z : LowerRamificationGraded F K (i : ℤ)) : z = 1 := by
  obtain ⟨sigma, rfl⟩ := lowerRamificationQuotientMk_surjective F K
    (show (i : ℤ) ≤ (i : ℤ) + 1 by omega) z
  change lowerRamificationGradedMk F K (i : ℤ) sigma = 1
  rw [lowerRamificationGradedMk_eq_one_iff]
  rw [PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break F K ht
    (show (i : ℤ) + 1 ≤ (t : ℤ) by omega)]
  exact Subgroup.mem_top _

/-- Strictly below the break, the ramification map and the graded norm form an exact pair.
Here both `G_i` and `G_(i+1)` are the full Galois group, so the ramification quotient and
the graded norm kernel are both trivial. -/
theorem ramification_gradedNorm_mulExact_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.MulExact
      (ramificationUnitGradedHom F K i pi hpi hgen)
      (normUnitGraded F K i
        (normMapsUnitFiltration_belowBreak F K ht hit.le hres pi hpi hgen)
        (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)) := by
  rw [MonoidHom.mulExact_iff,
    gradedNorm_kernel_belowBreak F K ht hit hres pi hpi hgen]
  apply le_antisymm
  · exact bot_le
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_bot,
      lowerRamificationGraded_eq_one_belowBreak F K ht hit x, map_one]

/-- The norm-induced multiplicative equivalence on a single graded layer `i<t`. -/
noncomputable def gradedNormEquiv_belowBreak
    {t i : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hit : i < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    UnitGradedPiece K i ≃* UnitGradedPiece F i :=
  MulEquiv.ofBijective (normUnitGraded F K i
      (normMapsUnitFiltration_belowBreak F K ht hit.le hres pi hpi hgen)
      (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen))
    (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen)

/-- Splicing precisely the layers `i=r,…,t-1` gives the finite interval equivalence
`U_K^r/U_K^t ≃ U_F^r/U_F^t`.  The exceptional critical layer `i=t` is not used. -/
noncomputable def normUnitFiltrationEquiv_belowBreak
    {r t : ℕ} (hrt : r ≤ t)
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    UnitFiltrationQuotient K r t hrt ≃*
      UnitFiltrationQuotient F r t hrt :=
  normUnitFiltrationIntervalEquiv F K hrt
    (fun i _ hit ↦ normMapsUnitFiltration_belowBreak F K ht hit hres pi hpi hgen)
    (fun i _ hit ↦ gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen)

/-- Finite below-break lifting: a target unit of depth `r` has a norm representative modulo
`U_F^t`.  No surjectivity at the critical graded layer is asserted. -/
theorem exists_norm_belowBreak_finiteCorrection
    {r t : ℕ} (hrt : r ≤ t)
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Fˣ) (hu : u ∈ unitFiltration F r) :
    ∃ x : Kˣ, x ∈ unitFiltration K r ∧
      u / normUnits F K x ∈ unitFiltration F t :=
  exists_normUnitFiltration_finiteCorrection F K hrt
    (fun i _ hit ↦ normMapsUnitFiltration_belowBreak F K ht hit hres pi hpi hgen)
    (fun i _ hit ↦
      (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen).2)
    u hu

/-- Finite below-break detection: if a depth-`r` source unit has norm in `U_F^t`, then the
source unit already lies in `U_K^t`. -/
theorem mem_unitFiltration_of_norm_mem_belowBreak
    {r t : ℕ} (hrt : r ≤ t)
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Kˣ) (hu : u ∈ unitFiltration K r)
    (hnu : normUnits F K u ∈ unitFiltration F t) :
    u ∈ unitFiltration K t :=
  mem_unitFiltration_of_norm_mem_of_graded_injective F K hrt
    (fun i _ hit ↦ normMapsUnitFiltration_belowBreak F K ht hit hres pi hpi hgen)
    (fun i _ hit ↦
      (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen).1)
    u hu hnu

private theorem ord_unit_ne_top (L : Type*) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (u : Lˣ) : ord L (u : L) ≠ ⊤ :=
  (ord_ne_top_iff L).2 (Units.ne_zero u)

private noncomputable def unitOrder (L : Type*) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (u : Lˣ) : ℤ :=
  (ord L (u : L)).untop (ord_unit_ne_top L u)

@[simp]
private theorem coe_unitOrder (L : Type*) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (u : Lˣ) :
    (unitOrder L u : WithTop ℤ) = ord L (u : L) :=
  WithTop.coe_untop _ _

/-- Every nonzero target element has a norm representative modulo the critical target unit
layer.  The valuation is matched first (using residue degree one), then the unit error is
corrected only through the strict below-break layers. -/
theorem exists_norm_representative_mod_break
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (y : Fˣ) :
    ∃ x : Kˣ, y / normUnits F K x ∈ unitFiltration F t := by
  obtain ⟨a, ha⟩ := exists_ord_eq K (unitOrder F y)
  have ha0 : a ≠ 0 := by
    apply (ord_ne_top_iff K).1
    rw [ha]
    exact WithTop.coe_ne_top
  let aU : Kˣ := Units.mk0 a ha0
  have herr0 : y / normUnits F K aU ∈ unitFiltration F 0 := by
    rw [mem_unitFiltration_zero]
    rw [Units.val_div_eq_div_val]
    change ord F ((y : F) / (normUnits F K aU : F)) = 0
    rw [ord_div, coe_normUnits, ord_norm,
      hres, one_nsmul, show ((aU : Kˣ) : K) = a by rfl, ha,
      ← coe_unitOrder F y]
    simp
  obtain ⟨u, hu, herr⟩ :=
    exists_norm_belowBreak_finiteCorrection F K (Nat.zero_le t)
      ht hres pi hpi hgen (y / normUnits F K aU) herr0
  refine ⟨aU * u, ?_⟩
  simpa only [map_mul, div_div] using herr

/-- If the norm of a nonzero source element lies in the critical target unit layer, then the
source element lies in the matching source layer. -/
theorem mem_unitFiltration_break_of_norm_mem
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : Kˣ) (hnx : normUnits F K x ∈ unitFiltration F t) :
    x ∈ unitFiltration K t := by
  have hnorm0 : normUnits F K x ∈ unitFiltration F 0 :=
    unitFiltration_antitone F (Nat.zero_le t) hnx
  have hxord : ord K (x : K) = 0 := by
    have h := (mem_unitFiltration_zero F (normUnits F K x)).1 hnorm0
    rw [coe_normUnits, ord_norm, hres, one_nsmul] at h
    exact h
  exact mem_unitFiltration_of_norm_mem_belowBreak F K
    (Nat.zero_le t) ht hres pi hpi hgen x
    ((mem_unitFiltration_zero K x).2 hxord) hnx

/-- Norm on nonzero field elements modulo a pair of equally numbered unit layers. -/
noncomputable def normFieldFiltrationQuotient (t : ℕ)
    (hmap : NormMapsUnitFiltration F K t t) :
    (Kˣ ⧸ unitFiltration K t) →* (Fˣ ⧸ unitFiltration F t) :=
  QuotientGroup.map (unitFiltration K t) (unitFiltration F t)
    (normUnits F K) (by
      intro u hu
      exact hmap u hu)

@[simp]
theorem normFieldFiltrationQuotient_mk (t : ℕ)
    (hmap : NormMapsUnitFiltration F K t t) (x : Kˣ) :
    normFieldFiltrationQuotient F K t hmap
        ((QuotientGroup.mk' (unitFiltration K t)) x) =
      (QuotientGroup.mk' (unitFiltration F t)) (normUnits F K x) :=
  QuotientGroup.map_mk' (unitFiltration K t) (unitFiltration F t)
    (normUnits F K) _ x

private theorem normFieldFiltrationQuotient_surjective_belowBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Surjective
      (normFieldFiltrationQuotient F K t
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)) := by
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (unitFiltration F t) z
  obtain ⟨x, herr⟩ :=
    exists_norm_representative_mod_break F K ht hres pi hpi hgen y
  refine ⟨(QuotientGroup.mk' (unitFiltration K t)) x, ?_⟩
  rw [normFieldFiltrationQuotient_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  have hinv := (unitFiltration F t).inv_mem herr
  simpa only [inv_div] using hinv

private theorem normFieldFiltrationQuotient_injective_belowBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Injective
      (normFieldFiltrationQuotient F K t
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (unitFiltration K t) z
    rw [normFieldFiltrationQuotient_mk] at hz
    change ((normUnits F K x : Fˣ) : Fˣ ⧸ unitFiltration F t) = 1 at hz
    rw [QuotientGroup.eq_one_iff] at hz
    change ((x : Kˣ) : Kˣ ⧸ unitFiltration K t) = 1
    exact (QuotientGroup.eq_one_iff x).2
      (mem_unitFiltration_break_of_norm_mem F K
        ht hres pi hpi hgen x hz)
  · intro hz
    rw [Subgroup.mem_bot] at hz
    subst z
    exact (normFieldFiltrationQuotient F K t _).ker.one_mem

/-- Norm is an equivalence on the full multiplicative quotients modulo the critical unit
layer.  For `t=0` this is the valuation quotient; for `t>0` its unit part is obtained by
splicing exactly the strictly subcritical graded layers. -/
noncomputable def normFieldFiltrationEquiv_belowBreak
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (Kˣ ⧸ unitFiltration K t) ≃* (Fˣ ⧸ unitFiltration F t) :=
  MulEquiv.ofBijective
    (normFieldFiltrationQuotient F K t
      (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen))
    ⟨normFieldFiltrationQuotient_injective_belowBreak F K ht hres pi hpi hgen,
      normFieldFiltrationQuotient_surjective_belowBreak F K ht hres pi hpi hgen⟩

end BelowBreakLifting

end

end LanglandsFirstMainLemma
