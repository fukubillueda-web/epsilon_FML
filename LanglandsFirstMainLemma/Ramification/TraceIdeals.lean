import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.Basic.CharacterConductors
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Trace ideals and the inverse different

For a finite Galois extension of nonarchimedean local fields, this file identifies the trace
dual of every integer-indexed fractional lattice and computes its exact trace image.  The
different exponent is the upstairs normalized exponent `differentExponent F K` constructed
from Hilbert's lower-ramification sum.  A chosen integral uniformizer generating the upper
valuation ring connects that numerical exponent to the genuine trace dual; no trace
surjectivity or trace-lattice formula is assumed.

The final section gives the exact quadratic graded-trace interface, including the nonzero-shell
criterion used in the wild quadratic calculation.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped Pointwise

private theorem traceIdeals_nonarchimedeanLocalFieldInfinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n ↦ (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord F (f m) = (m : WithTop ℤ) := (exists_ord_eq F m).choose_spec
    have hn : ord F (f n) = (n : WithTop ℤ) := (exists_ord_eq F n).choose_spec
    have hcoe : (m : WithTop ℤ) = (n : WithTop ℤ) :=
      hm.symm.trans ((congrArg (ord F) hmn).trans hn)
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

private theorem field_adjoin_eq_top_of_integer_adjoin_eq_top
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K]
    (π : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    Algebra.adjoin F ({(π : K)} : Set K) = ⊤ := by
  rw [eq_top_iff]
  intro x _hx
  obtain ⟨a, b, _hb, hab⟩ :=
    IsFractionRing.div_surjective (ringOfIntegers K) x
  have hintegral (z : ringOfIntegers K) :
      (z : K) ∈ Algebra.adjoin F ({(π : K)} : Set K) := by
    have hz : z ∈ Algebra.adjoin (ringOfIntegers F)
        ({π} : Set (ringOfIntegers K)) := by
      rw [hgen]
      trivial
    exact Algebra.adjoin_induction (p := fun (z : ringOfIntegers K) _ ↦
        (z : K) ∈ Algebra.adjoin F ({(π : K)} : Set K))
      (fun z hz ↦ by
        rw [Set.mem_singleton_iff.mp hz]
        exact Algebra.subset_adjoin (Set.mem_singleton (π : K)))
      (fun r ↦ by
        change algebraMap F K (r : F) ∈ Algebra.adjoin F ({(π : K)} : Set K)
        exact (Algebra.adjoin F ({(π : K)} : Set K)).algebraMap_mem (r : F))
      (fun u v _ _ hu hv ↦ by
        simpa only [Subring.coe_add] using
          (Algebra.adjoin F ({(π : K)} : Set K)).add_mem hu hv)
      (fun u v _ _ hu hv ↦ by
        simpa only [Subring.coe_mul] using
          (Algebra.adjoin F ({(π : K)} : Set K)).mul_mem hu hv)
      hz
  have ha : algebraMap (ringOfIntegers K) K a ∈
      Algebra.adjoin F ({(π : K)} : Set K) := by
    rw [congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) a]
    exact hintegral a
  have hb : algebraMap (ringOfIntegers K) K b ∈
      Algebra.adjoin F ({(π : K)} : Set K) := by
    rw [congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) b]
    exact hintegral b
  have hbInv : (algebraMap (ringOfIntegers K) K b)⁻¹ ∈
      Algebra.adjoin F ({(π : K)} : Set K) :=
    (Algebra.IsIntegral.isIntegral (algebraMap (ringOfIntegers K) K b)).inv_mem hb
  rw [← hab]
  simpa only [div_eq_mul_inv] using
    (Algebra.adjoin F ({(π : K)} : Set K)).mul_mem ha hbInv

private theorem integer_adjoin_toSubmodule_eq_lattice_zero
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (π : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    (Algebra.adjoin (ringOfIntegers F) ({(π : K)} : Set K)).toSubmodule =
      (lattice K 0).restrictScalars (ringOfIntegers F) := by
  ext x
  constructor
  · intro hx
    exact Algebra.adjoin_induction (p := fun (z : K) _ ↦ z ∈ lattice K 0)
      (fun z hz ↦ by
        rw [Set.mem_singleton_iff.mp hz]
        exact (mem_lattice_zero_iff K).2 π.property)
      (fun r ↦ by
        have hr : (algebraMap (ringOfIntegers F) (ringOfIntegers K) r :
            ringOfIntegers K).1 ∈ ringOfIntegers K :=
          (algebraMap (ringOfIntegers F) (ringOfIntegers K) r).property
        apply (mem_lattice_zero_iff K).2
        rw [IsScalarTower.algebraMap_apply (ringOfIntegers F) F K]
        rw [congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers F)) r]
        simpa only [Valuation.HasExtension.val_algebraMap] using hr)
      (fun u v _ _ hu hv ↦ add_mem_lattice K hu hv)
      (fun u v _ _ hu hv ↦ by
        simpa only [zero_add] using mul_mem_lattice K hu hv)
      hx
  · intro hx
    let xO : ringOfIntegers K :=
      ⟨x, (mem_lattice_zero_iff K).1 hx⟩
    let inclusion : ringOfIntegers K →ₐ[ringOfIntegers F] K :=
      IsScalarTower.toAlgHom (ringOfIntegers F) (ringOfIntegers K) K
    have hxO : xO ∈ Algebra.adjoin (ringOfIntegers F)
        ({π} : Set (ringOfIntegers K)) := by
      rw [hgen]
      trivial
    have hxmap : inclusion xO ∈ Subalgebra.map inclusion
        (Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K))) :=
      ⟨xO, hxO, rfl⟩
    rw [AlgHom.map_adjoin_singleton] at hxmap
    have hinclusion (z : ringOfIntegers K) : inclusion z = (z : K) := by
      change algebraMap (ringOfIntegers K) K z = (z : K)
      exact congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) z
    rw [hinclusion xO, hinclusion π] at hxmap
    exact hxmap

/-- Membership in Mathlib's trace dual, written in the manuscript's integral-lattice
normalization. -/
theorem mem_traceDual_iff_trace_mul_mem_lattice_zero
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    {a : ℤ} {z : K} :
    z ∈ Submodule.traceDual (ringOfIntegers F) F (lattice K a) ↔
      ∀ x : K, x ∈ lattice K a → trace F K (z * x) ∈ lattice F 0 := by
  rw [Submodule.mem_traceDual]
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _hx
  simp only [Algebra.traceForm_apply, lattice_zero, Submodule.mem_one,
    RingHom.mem_range]

private theorem aeval_derivative_minpoly_eq_prod_nonidentity
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    Polynomial.aeval (π : K) (Polynomial.derivative (minpoly F (π : K))) =
      ∏ σ ∈ nonidentityGaloisAutomorphisms F K, ((π : K) - σ (π : K)) := by
  classical
  letI : Infinite F := traceIdeals_nonarchimedeanLocalFieldInfinite F
  let x : K := (π : K)
  have hfield : Algebra.adjoin F ({x} : Set K) = ⊤ := by
    exact field_adjoin_eq_top_of_integer_adjoin_eq_top F K π hgen
  let pb : PowerBasis F K :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral x) hfield
  have hpbgen : pb.gen = x :=
    PowerBasis.ofAdjoinEqTop_gen (Algebra.IsIntegral.isIntegral x) hfield
  have hchar : (Algebra.lmul F K x).charpoly = minpoly F x := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul F K x) pb.basis]
    change (Algebra.leftMulMatrix pb.basis x).charpoly = minpoly F x
    rw [← hpbgen]
    exact charpoly_leftMulMatrix pb
  have hpoly :
      (minpoly F x).map (algebraMap F K) =
        Multiset.prod ((galoisConjugates F K x).map
          (fun z ↦ Polynomial.X - Polynomial.C z)) := by
    rw [← hchar]
    simpa [galoisConjugates, galoisConjugate] using
      (map_lmul_charpoly_eq_prod_galois F K x)
  have hinjective :
      Function.Injective (fun σ : Gal(K/F) ↦ galoisConjugate σ x) := by
    intro σ τ hστ
    have hhom : σ.toAlgHom = τ.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hfield
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hστ
    apply AlgEquiv.ext
    intro z
    exact DFunLike.congr_fun hhom z
  have hxmem : x ∈ galoisConjugates F K x := by
    rw [galoisConjugates, Multiset.mem_map]
    exact ⟨1, by simp, by simp [galoisConjugate]⟩
  change Polynomial.aeval x (Polynomial.derivative (minpoly F x)) = _
  calc
    Polynomial.aeval x (Polynomial.derivative (minpoly F x)) =
        Polynomial.eval x
          (Polynomial.derivative ((minpoly F x).map (algebraMap F K))) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.derivative_map]
    _ = Polynomial.eval x
          (Polynomial.derivative
            (Multiset.prod ((galoisConjugates F K x).map
              (fun z ↦ Polynomial.X - Polynomial.C z)))) := by
      rw [hpoly]
    _ = Multiset.prod
          (((galoisConjugates F K x).erase x).map (fun z ↦ x - z)) :=
      Polynomial.eval_multiset_prod_X_sub_C_derivative hxmem
    _ = ∏ σ ∈ nonidentityGaloisAutomorphisms F K, (x - σ x) := by
      have herase :
          Multiset.map (fun σ : Gal(K/F) ↦ galoisConjugate σ x)
              (Finset.univ.erase 1).val =
            (Multiset.map (fun σ : Gal(K/F) ↦ galoisConjugate σ x)
              (Finset.univ : Finset Gal(K/F)).val).erase x := by
        simpa [galoisConjugate] using
          (Multiset.map_erase (fun σ : Gal(K/F) ↦ galoisConjugate σ x)
            hinjective 1 (Finset.univ : Finset Gal(K/F)).val)
      rw [galoisConjugates, ← herase, Multiset.map_map,
        ← Finset.prod_eq_multiset_prod]
      rfl

private theorem ord_aeval_derivative_minpoly_eq_differentExponent
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    ord K (Polynomial.aeval (π : K)
        (Polynomial.derivative (minpoly F (π : K)))) =
      (((differentExponent F K : ℕ) : ℤ) : WithTop ℤ) := by
  classical
  rw [aeval_derivative_minpoly_eq_prod_nonidentity F K π hgen]
  have hordprod (s : Finset Gal(K/F)) :
      ord K (∏ σ ∈ s, ((π : K) - σ (π : K))) =
        ∑ σ ∈ s, ord K ((π : K) - σ (π : K)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert σ s hσ ih =>
        rw [Finset.prod_insert hσ, Finset.sum_insert hσ, ord_mul, ih]
  rw [hordprod]
  unfold differentExponent
  rw [Nat.cast_sum, WithTop.coe_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hσne : σ ≠ 1 := (mem_nonidentityGaloisAutomorphisms F K).1 hσ
  rw [show (π : K) - σ (π : K) = -(σ (π : K) - (π : K)) by ring,
    ord_neg,
    ord_galois_uniformizer_sub_eq_lowerDifferentSummand F K π hπ hgen hσne]

/-- The integral trace dual is the inverse different, with the different exponent measured by
the normalized order upstairs. -/
theorem traceDual_lattice_zero
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    Submodule.traceDual (ringOfIntegers F) F (lattice K 0) =
      lattice K (-(differentExponent F K : ℤ)) := by
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  let δ : K := Polynomial.aeval (π : K)
    (Polynomial.derivative (minpoly F (π : K)))
  have hδord : ord K δ =
      (((differentExponent F K : ℕ) : ℤ) : WithTop ℤ) := by
    exact ord_aeval_derivative_minpoly_eq_differentExponent F K π hπ hgen
  have hδ0 : δ ≠ 0 := by
    exact (ord_ne_top_iff K).1 (by rw [hδord]; simp)
  have hfield : Algebra.adjoin F ({(π : K)} : Set K) = ⊤ :=
    field_adjoin_eq_top_of_integer_adjoin_eq_top F K π hgen
  have hπIntegral : IsIntegral (ringOfIntegers F) (π : K) := by
    have hπO : IsIntegral (ringOfIntegers F) π :=
      IsIntegralClosure.isIntegral (ringOfIntegers F) K π
    rw [← congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) π]
    exact hπO.algebraMap
  have hdual := traceForm_dualSubmodule_adjoin
    (ringOfIntegers F) F hfield hπIntegral
  have hadjoin := integer_adjoin_toSubmodule_eq_lattice_zero F K π hgen
  ext z
  change z ∈ (Submodule.traceDual (ringOfIntegers F) F (lattice K 0)).restrictScalars
      (ringOfIntegers F) ↔ z ∈ lattice K (-(differentExponent F K : ℤ))
  rw [Submodule.restrictScalars_traceDual, ← hadjoin, hdual, hadjoin]
  change z ∈ δ⁻¹ • (lattice K 0).restrictScalars (ringOfIntegers F) ↔
    z ∈ lattice K (-(differentExponent F K : ℤ))
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hδ0), inv_inv]
  change δ * z ∈ lattice K 0 ↔ z ∈ lattice K (-(differentExponent F K : ℤ))
  rw [mem_lattice, mem_lattice, ord_mul, hδord]
  by_cases hz : ord K z = ⊤
  · simp [hz]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hz
    rw [← hk]
    exact (show ((0 : ℤ) : WithTop ℤ) ≤
          ((differentExponent F K : ℤ) : WithTop ℤ) + (k : WithTop ℤ) ↔
        ((-(differentExponent F K : ℤ) : ℤ) : WithTop ℤ) ≤ (k : WithTop ℤ) by
      rw [← WithTop.coe_add]
      simp only [WithTop.coe_le_coe]
      omega)

/-- The trace dual of `𝔭_K^a` is `𝔭_K^(-a-d(K/F))` for every integer `a`.
The different shift is measured upstairs and the formula includes all negative depths. -/
theorem traceDual_lattice
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (a : ℤ) :
    Submodule.traceDual (ringOfIntegers F) F (lattice K a) =
      lattice K (-a - (differentExponent F K : ℤ)) := by
  let D : ℤ := differentExponent F K
  have hbase (z : K) :
      (∀ x : K, x ∈ lattice K 0 → trace F K (z * x) ∈ lattice F 0) ↔
        z ∈ lattice K (-D) := by
    rw [← mem_traceDual_iff_trace_mul_mem_lattice_zero F K,
      traceDual_lattice_zero F K π hπ hgen]
  ext z
  rw [mem_traceDual_iff_trace_mul_mem_lattice_zero F K]
  change (∀ x : K, x ∈ lattice K a → trace F K (z * x) ∈ lattice F 0) ↔
    z ∈ lattice K (-a - D)
  calc
    (∀ x : K, x ∈ lattice K a → trace F K (z * x) ∈ lattice F 0) ↔
        ∀ x : K, x ∈ lattice K a → z * x ∈ lattice K (-D) := by
      constructor
      · intro h x hx
        apply (hbase (z * x)).1
        intro y hy
        have hxy : x * y ∈ lattice K a := by
          simpa using mul_mem_lattice K hx hy
        simpa [mul_assoc] using h (x * y) hxy
      · intro h x hx
        have h' := (hbase (z * x)).2 (h x hx) 1 (by simp)
        simpa using h'
    _ ↔ z ∈ lattice K ((-D) - a) := mul_lattice_subset_iff K
    _ ↔ z ∈ lattice K (-a - D) := by ring_nf

private theorem traceIdeals_ediv_lower_upper (n : ℤ) (e : ℕ) (he : 0 < e) :
    (n / (e : ℤ)) * (e : ℤ) ≤ n ∧
      n < (n / (e : ℤ) + 1) * (e : ℤ) := by
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  constructor
  · exact Int.ediv_mul_le n heZ.ne'
  · exact (Int.ediv_lt_iff_lt_mul heZ).mp (by omega)

private theorem trace_lattice_image_of_traceDual
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (D a : ℤ)
    (hdual : Submodule.traceDual (ringOfIntegers F) F (lattice K a) =
      lattice K (-a - D)) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) =
      lattice F ((a + D) / (ramificationIndex F K : ℤ)) := by
  let e : ℕ := ramificationIndex F K
  let c : ℤ := (a + D) / (e : ℤ)
  have he : 0 < e := ramificationIndex_pos F K
  have hbounds : c * (e : ℤ) ≤ a + D ∧
      a + D < (c + 1) * (e : ℤ) := by
    simpa only [c] using traceIdeals_ediv_lower_upper (a + D) e he

  have htrace_mem : ∀ x : K, x ∈ lattice K a →
      trace F K x ∈ lattice F c := by
    intro x hx
    have hmul : ∀ y : F, y ∈ lattice F (-c) →
        trace F K x * y ∈ lattice F 0 := by
      intro y hy
      have hyK : algebraMap F K y ∈ lattice K (-a - D) := by
        rw [mem_lattice, ord_algebraMap]
        rw [mem_lattice] at hy
        have hsmul := nsmul_le_nsmul_right hy e
        have harith : -a - D ≤ (e : ℤ) * (-c) := by
          nlinarith [hbounds.1]
        apply (WithTop.coe_le_coe.mpr harith).trans
        have hcoe : (((e : ℤ) * (-c) : ℤ) : WithTop ℤ) =
            e • ((-c : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_nsmul]
          congr 1
        rw [hcoe]
        exact hsmul
      have hyDual : algebraMap F K y ∈
          Submodule.traceDual (ringOfIntegers F) F (lattice K a) := by
        rw [hdual]
        exact hyK
      have htr :=
        (mem_traceDual_iff_trace_mul_mem_lattice_zero F K).1 hyDual x hx
      rw [← Algebra.smul_def, map_smul] at htr
      change y * trace F K x ∈ lattice F 0 at htr
      simpa only [mul_comm] using htr
    have hz := (mul_lattice_subset_iff F (c := trace F K x)
      (m := 0) (n := -c)).1 hmul
    simpa using hz

  have hexact : ∃ x : K, x ∈ lattice K a ∧
      ord F (trace F K x) = (c : WithTop ℤ) := by
    by_contra hnone
    have hnone' : ∀ x : K, x ∈ lattice K a →
        ord F (trace F K x) ≠ (c : WithTop ℤ) := by
      intro x hx heq
      exact hnone ⟨x, hx, heq⟩
    have htrace_deep : ∀ x : K, x ∈ lattice K a →
        trace F K x ∈ lattice F (c + 1) := by
      intro x hx
      rw [mem_lattice]
      have hc := htrace_mem x hx
      rw [mem_lattice] at hc
      have hne := hnone' x hx
      by_cases htop : ord F (trace F K x) = ⊤
      · simp [htop]
      have hlt : (c : WithTop ℤ) < ord F (trace F K x) :=
        lt_of_le_of_ne hc (Ne.symm hne)
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hz] at hlt ⊢
      exact WithTop.coe_le_coe.mpr (by
        have hltZ : c < z := WithTop.coe_lt_coe.mp hlt
        omega)
    obtain ⟨y, hy⟩ := exists_ord_eq F (-(c + 1))
    have hyDual : algebraMap F K y ∈
        Submodule.traceDual (ringOfIntegers F) F (lattice K a) := by
      apply (mem_traceDual_iff_trace_mul_mem_lattice_zero F K).2
      intro x hx
      have hprod := mul_mem_lattice F
        (show y ∈ lattice F (-(c + 1)) by rw [mem_lattice, hy])
        (htrace_deep x hx)
      have htrace : trace F K (algebraMap F K y * x) =
          y * trace F K x := by
        rw [← Algebra.smul_def, map_smul]
        rfl
      rw [htrace]
      simpa using hprod
    have hyLat : algebraMap F K y ∈ lattice K (-a - D) := by
      rw [← hdual]
      exact hyDual
    have hordMap : ord K (algebraMap F K y) =
        (((e : ℤ) * (-(c + 1)) : ℤ) : WithTop ℤ) := by
      rw [ord_algebraMap, hy]
      simpa [e, mul_comm] using
        (WithTop.coe_nsmul (-(c + 1)) e).symm
    rw [mem_lattice, hordMap, WithTop.coe_le_coe] at hyLat
    have hstrict : (e : ℤ) * (-(c + 1)) < -a - D := by
      nlinarith [hbounds.2]
    exact (not_lt_of_ge hyLat) hstrict

  obtain ⟨x0, hx0, htrace0⟩ := hexact
  have htrace0ne : trace F K x0 ≠ 0 := by
    intro hz
    simp [hz] at htrace0
  change Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
      ((lattice K a).restrictScalars (ringOfIntegers F)) = lattice F c
  ext y
  constructor
  · intro hy
    rcases Submodule.mem_map.mp hy with ⟨x, hx, hxy⟩
    rw [← hxy]
    exact htrace_mem x hx
  · intro hy
    let z : F := (trace F K x0)⁻¹ * y
    have hz : z ∈ lattice F 0 := by
      rw [mem_lattice]
      dsimp only [z]
      rw [ord_mul, ord_inv, htrace0]
      rw [mem_lattice] at hy
      norm_num at hy ⊢
      have h := add_le_add_left hy (-(c : WithTop ℤ))
      simpa [add_assoc, add_comm, add_left_comm] using h
    let x : K := algebraMap F K z * x0
    have hx : x ∈ lattice K a := by
      have hzK : algebraMap F K z ∈ lattice K 0 := by
        rw [mem_lattice, ord_algebraMap]
        rw [mem_lattice] at hz
        have hsmul := nsmul_le_nsmul_right hz e
        simpa [e] using hsmul
      simpa [x] using mul_mem_lattice K hzK hx0
    apply Submodule.mem_map.mpr
    refine ⟨x, hx, ?_⟩
    change trace F K x = y
    rw [show x = z • x0 by simp [x, Algebra.smul_def], map_smul]
    change z * trace F K x0 = y
    dsimp only [z]
    field_simp

/-- Exact trace-image formula at every integer depth.  Lean's integer division by the positive
ramification index is the manuscript's floor. -/
theorem trace_lattice_image_eq
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (a : ℤ) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) =
      lattice F ((a + (differentExponent F K : ℤ)) /
        (ramificationIndex F K : ℤ)) :=
  trace_lattice_image_of_traceDual F K (differentExponent F K : ℤ) a
    (traceDual_lattice F K π hπ hgen a)

/-- Elementwise exact trace-image formula.  In particular, the zero target has the zero
preimage, while every nonzero target is obtained by scaling an exact-depth trace. -/
theorem mem_trace_lattice_image_iff
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (a : ℤ) (y : F) :
    y ∈ lattice F ((a + (differentExponent F K : ℤ)) /
        (ramificationIndex F K : ℤ)) ↔
      ∃ x : K, x ∈ lattice K a ∧ trace F K x = y := by
  rw [← trace_lattice_image_eq F K π hπ hgen a]
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- Containment half of the exact trace-image formula, exposed for valuation estimates. -/
theorem trace_mem_lattice_floor
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (a : ℤ) {x : K} (hx : x ∈ lattice K a) :
    trace F K x ∈ lattice F ((a + (differentExponent F K : ℤ)) /
      (ramificationIndex F K : ℤ)) :=
  (mem_trace_lattice_image_iff F K π hπ hgen a (trace F K x)).2
    ⟨x, hx, rfl⟩

/-- The ceiling exponent of the base-field annihilator is the negative of the trace-image
floor.  This is the manuscript's floor/ceiling conversion, valid also when `a + d` is
negative. -/
theorem trace_annihilator_ceiling_eq
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (a : ℤ) :
    (- (a + (differentExponent F K : ℤ)) +
          (ramificationIndex F K : ℤ) - 1) /
        (ramificationIndex F K : ℤ) =
      -((a + (differentExponent F K : ℤ)) /
        (ramificationIndex F K : ℤ)) := by
  let n : ℤ := a + (differentExponent F K : ℤ)
  let e : ℕ := ramificationIndex F K
  have he : 0 < e := ramificationIndex_pos F K
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  change (-n + (e : ℤ) - 1) / (e : ℤ) = -(n / (e : ℤ))
  apply le_antisymm
  · rw [Int.ediv_le_iff_le_mul heZ]
    have hlower := Int.ediv_mul_le n heZ.ne'
    nlinarith
  · rw [Int.le_ediv_iff_mul_le heZ]
    have hupper : n < (n / (e : ℤ) + 1) * (e : ℤ) :=
      (Int.ediv_lt_iff_lt_mul heZ).mp (by omega)
    nlinarith

/-- Triviality of an additive character pulled back by trace is equivalent to triviality on
the exact trace-image lattice. -/
theorem addCharTrivialOnLattice_compTrace_iff
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (ψ : ContinuousAddChar F) (a : ℤ) :
    AddCharTrivialOnLattice K ψ.compTrace a ↔
      AddCharTrivialOnLattice F ψ
        ((a + (differentExponent F K : ℤ)) /
          (ramificationIndex F K : ℤ)) := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ :=
      (mem_trace_lattice_image_iff F K π hπ hgen a y).1 hy
    have hxone := h x hx
    rw [ContinuousAddChar.compTrace_apply, hxy] at hxone
    exact hxone
  · intro h x hx
    rw [ContinuousAddChar.compTrace_apply]
    exact h (trace F K x) (trace_mem_lattice_floor F K π hπ hgen a hx)

/-- Pullback by trace shifts the manuscript's additive conductor by `e n + d`, with `d`
measured upstairs.  The sign is fixed by the convention that conductor `n` means triviality
on `𝔭_F^{-n}`. -/
theorem isAdditiveConductor_compTrace
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {ψ : ContinuousAddChar F} {n : ℤ}
    (hψ : IsAdditiveConductor F ψ n) :
    IsAdditiveConductor K ψ.compTrace
      ((ramificationIndex F K : ℤ) * n +
        (differentExponent F K : ℤ)) := by
  let e : ℕ := ramificationIndex F K
  let D : ℤ := differentExponent F K
  have he : 0 < e := ramificationIndex_pos F K
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  refine ⟨?_, ?_⟩
  · rw [addCharTrivialOnLattice_compTrace_iff F K π hπ hgen]
    have hdepth : (-((e : ℤ) * n + D) + D) / (e : ℤ) = -n := by
      have he0 : (e : ℤ) ≠ 0 := ne_of_gt heZ
      rw [show -((e : ℤ) * n + D) + D = (e : ℤ) * (-n) by ring]
      exact Int.mul_ediv_cancel_left (-n) he0
    rw [hdepth]
    exact hψ.trivial
  · intro a ha
    have hdown :=
      (addCharTrivialOnLattice_compTrace_iff F K π hπ hgen ψ a).1 ha
    have hmin : -n ≤ (a + D) / (e : ℤ) := hψ.minimal _ hdown
    have hmul : (-n) * (e : ℤ) ≤ a + D :=
      (Int.le_ediv_iff_mul_le heZ).mp hmin
    change -((e : ℤ) * n + D) ≤ a
    nlinarith

private theorem extensionResidueMap_surjective_of_residueDegree_eq_one
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    (hf : residueDegree F K = 1) :
    Function.Surjective (extensionResidueMap F K) := by
  have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
    rw [← residueDegree_eq_finrank_residueField F K, hf]
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

private theorem exists_base_approximation_at_ramification_multiple
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (hres : Function.Surjective (extensionResidueMap F K))
    (s : ℤ) {y : K}
    (hy : y ∈ lattice K ((ramificationIndex F K : ℤ) * s)) :
    ∃ b : F, b ∈ lattice F s ∧
      y - algebraMap F K b ∈
        lattice K ((ramificationIndex F K : ℤ) * s + 1) := by
  let e : ℕ := ramificationIndex F K
  obtain ⟨u, hu⟩ := exists_ord_eq F s
  have hu0 : u ≠ 0 := (ord_ne_top_iff F).1 (by rw [hu]; simp)
  have huK0 : algebraMap F K u ≠ 0 := by
    simpa using (algebraMap F K).injective.ne hu0
  have huKord : ord K (algebraMap F K u) =
      (((e : ℤ) * s : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hu]
    rw [← WithTop.coe_nsmul]
    congr 1
  let z : K := y / algebraMap F K u
  have hz : z ∈ lattice K 0 := by
    dsimp only [z]
    apply (div_mem_lattice_iff K (algebraMap F K u) y
      ((e : ℤ) * s) 0 huKord).2
    simpa [e] using hy
  let zO : ringOfIntegers K := ⟨z, (mem_lattice_zero_iff K).1 hz⟩
  obtain ⟨xi, hxi⟩ := hres (residueMap K zO)
  obtain ⟨vO, hvO⟩ := residueMap_surjective F xi
  let vK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) vO
  have hresEq : residueMap K zO = residueMap K vK := by
    change residueMap K zO = extensionResidueMap F K (residueMap F vO)
    rw [hvO, hxi]
  have hdiff0 : (zO : K) - (vK : K) ∈ lattice K 1 :=
    (residueMap_eq_residueMap_iff K zO vK).1 hresEq
  have hvKcoe : (vK : K) = algebraMap F K (vO : F) :=
    Valuation.HasExtension.val_algebraMap vO
  have hdiff : z - algebraMap F K (vO : F) ∈ lattice K 1 := by
    simpa only [zO, hvKcoe] using hdiff0
  let b : F := u * (vO : F)
  have hb : b ∈ lattice F s := by
    have huLat : u ∈ lattice F s := by rw [mem_lattice, hu]
    have hvLat : (vO : F) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 vO.property
    simpa [b] using mul_mem_lattice F huLat hvLat
  refine ⟨b, hb, ?_⟩
  have huKLat : algebraMap F K u ∈ lattice K ((e : ℤ) * s) := by
    rw [mem_lattice, huKord]
  have hprod := mul_mem_lattice K huKLat hdiff
  have heq : y - algebraMap F K b =
      algebraMap F K u * (z - algebraMap F K (vO : F)) := by
    dsimp only [b, z]
    rw [map_mul]
    field_simp
  rw [heq]
  simpa [e] using hprod

private theorem quadratic_trace_kernel_step_of_traceDual
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (D r q : ℤ)
    (hram : ramificationIndex F K = 2)
    (hodd : r + D = 2 * q + 1)
    (hres : Function.Surjective (extensionResidueMap F K))
    (hdual0 : Submodule.traceDual (ringOfIntegers F) F (lattice K 0) =
      lattice K (-D))
    (hdualTest :
      Submodule.traceDual (ringOfIntegers F) F (lattice K (-r - 1 - D)) =
        lattice K (r + 1))
    {x : K} (hx : x ∈ lattice K r)
    (htrace : trace F K x ∈ lattice F (q + 1)) :
    x ∈ lattice K (r + 1) := by
  rw [← hdualTest]
  apply (mem_traceDual_iff_trace_mul_mem_lattice_zero F K).2
  intro y hy
  have hmultiple : (ramificationIndex F K : ℤ) * (-(q + 1)) =
      -r - 1 - D := by
    rw [hram]
    norm_num
    omega
  have hyMultiple : y ∈
      lattice K ((ramificationIndex F K : ℤ) * (-(q + 1))) := by
    rw [hmultiple]
    exact hy
  obtain ⟨b, hb, hyb⟩ :=
    exists_base_approximation_at_ramification_multiple F K hres (-(q + 1)) hyMultiple
  have hbaseProd : b * trace F K x ∈ lattice F 0 := by
    have h := mul_mem_lattice F hb htrace
    simpa using h
  have hbaseTrace : trace F K (x * algebraMap F K b) ∈ lattice F 0 := by
    have heq : trace F K (x * algebraMap F K b) = b * trace F K x := by
      rw [mul_comm, ← Algebra.smul_def, map_smul]
      rfl
    rw [heq]
    exact hbaseProd
  have hybDepth : y - algebraMap F K b ∈ lattice K (-r - D) := by
    have htarget : (ramificationIndex F K : ℤ) * (-(q + 1)) + 1 =
        -r - D := by
      rw [hmultiple]
      omega
    rw [← htarget]
    exact hyb
  have herrProd : x * (y - algebraMap F K b) ∈ lattice K (-D) := by
    rw [← show r + (-r - D) = -D by omega]
    exact mul_mem_lattice K hx hybDepth
  have herrDual : x * (y - algebraMap F K b) ∈
      Submodule.traceDual (ringOfIntegers F) F (lattice K 0) := by
    rw [hdual0]
    exact herrProd
  have herrTrace : trace F K (x * (y - algebraMap F K b)) ∈ lattice F 0 := by
    have hone : (1 : K) ∈ lattice K 0 := by simp [lattice_zero]
    have h := (mem_traceDual_iff_trace_mul_mem_lattice_zero F K).1
      herrDual 1 hone
    simpa using h
  have hsum := add_mem_lattice F hbaseTrace herrTrace
  convert hsum using 1
  rw [← map_add]
  congr 1
  ring

private def latticeTraceLinearMap
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    {r q : ℤ}
    (hmem : ∀ x : K, x ∈ lattice K r → trace F K x ∈ lattice F q) :
    lattice K r →ₗ[ringOfIntegers F] lattice F q where
  toFun x := ⟨trace F K x, hmem x x.property⟩
  map_add' x y := by ext; simp
  map_smul' c x := by
    ext
    change trace F K ((c : F) • (x : K)) = (c : F) • trace F K (x : K)
    exact map_smul (trace F K) (c : F) (x : K)

/-- Trace on successive lattice quotients.  The hypotheses are precisely representative
independence at the two adjacent depths. -/
noncomputable def traceLatticeGraded
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (r q : ℤ)
    (hmem : ∀ x : K, x ∈ lattice K r → trace F K x ∈ lattice F q)
    (hdeep : ∀ x : K, x ∈ lattice K (r + 1) →
      trace F K x ∈ lattice F (q + 1)) :
    LatticeGradedPiece K r →ₗ[ringOfIntegers F] LatticeGradedPiece F q :=
  Submodule.mapQ
    ((latticeInside K (show r ≤ r + 1 by omega)).restrictScalars (ringOfIntegers F))
    (latticeInside F (show q ≤ q + 1 by omega))
    (latticeTraceLinearMap F K hmem) (by
      intro x hx
      apply (mem_latticeInside F (show q ≤ q + 1 by omega)).2
      exact hdeep x ((mem_latticeInside K (show r ≤ r + 1 by omega)).1 hx))

/-- Representative formula for trace on successive lattice quotients. -/
@[simp]
theorem traceLatticeGraded_mk
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (r q : ℤ)
    (hmem : ∀ x : K, x ∈ lattice K r → trace F K x ∈ lattice F q)
    (hdeep : ∀ x : K, x ∈ lattice K (r + 1) →
      trace F K x ∈ lattice F (q + 1))
    (x : lattice K r) :
    traceLatticeGraded F K r q hmem hdeep
        (latticeQuotientMk K (show r ≤ r + 1 by omega) x) =
      latticeQuotientMk F (show q ≤ q + 1 by omega)
        ⟨trace F K x, hmem x x.property⟩ :=
  rfl

private theorem traceLatticeGraded_bijective
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (r q : ℤ)
    (hmem : ∀ x : K, x ∈ lattice K r → trace F K x ∈ lattice F q)
    (hdeep : ∀ x : K, x ∈ lattice K (r + 1) →
      trace F K x ∈ lattice F (q + 1))
    (hsurj : ∀ y : F, y ∈ lattice F q →
      ∃ x : K, x ∈ lattice K r ∧ trace F K x = y)
    (hker : ∀ x : K, x ∈ lattice K r →
      trace F K x ∈ lattice F (q + 1) → x ∈ lattice K (r + 1)) :
    Function.Bijective (traceLatticeGraded F K r q hmem hdeep) := by
  constructor
  · intro z₁ z₂ heq
    have hzero : traceLatticeGraded F K r q hmem hdeep (z₁ - z₂) = 0 := by
      rw [map_sub, heq, sub_self]
    obtain ⟨x, hx⟩ := latticeQuotientMk_surjective K
      (show r ≤ r + 1 by omega) (z₁ - z₂)
    have hmapx : traceLatticeGraded F K r q hmem hdeep
        (latticeQuotientMk K (show r ≤ r + 1 by omega) x) = 0 := by
      rw [hx]
      exact hzero
    rw [traceLatticeGraded_mk, latticeQuotientMk_eq_zero_iff] at hmapx
    have hxdeep : (x : K) ∈ lattice K (r + 1) :=
      hker x x.property hmapx
    have hxzero : latticeQuotientMk K (show r ≤ r + 1 by omega) x = 0 :=
      (latticeQuotientMk_eq_zero_iff K (show r ≤ r + 1 by omega)).2 hxdeep
    apply sub_eq_zero.mp
    calc
      z₁ - z₂ = latticeQuotientMk K (show r ≤ r + 1 by omega) x := hx.symm
      _ = 0 := hxzero
  · intro z
    obtain ⟨y, hy⟩ := latticeQuotientMk_surjective F
      (show q ≤ q + 1 by omega) z
    obtain ⟨x, hx, hxy⟩ := hsurj y y.property
    let xL : lattice K r := ⟨x, hx⟩
    refine ⟨latticeQuotientMk K (show r ≤ r + 1 by omega) xL, ?_⟩
    rw [traceLatticeGraded_mk, ← hy]
    congr 1
    apply Subtype.ext
    exact hxy

private noncomputable def traceLatticeGradedEquiv
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (r q : ℤ)
    (hmem : ∀ x : K, x ∈ lattice K r → trace F K x ∈ lattice F q)
    (hdeep : ∀ x : K, x ∈ lattice K (r + 1) →
      trace F K x ∈ lattice F (q + 1))
    (hsurj : ∀ y : F, y ∈ lattice F q →
      ∃ x : K, x ∈ lattice K r ∧ trace F K x = y)
    (hker : ∀ x : K, x ∈ lattice K r →
      trace F K x ∈ lattice F (q + 1) → x ∈ lattice K (r + 1)) :
    LatticeGradedPiece K r ≃ₗ[ringOfIntegers F] LatticeGradedPiece F q :=
  LinearEquiv.ofBijective (traceLatticeGraded F K r q hmem hdeep)
    (traceLatticeGraded_bijective F K r q hmem hdeep hsurj hker)

private theorem quadratic_trace_depths
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Finite F K]
    {r q : ℤ}
    (hram : ramificationIndex F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1) :
    (r + (differentExponent F K : ℤ)) /
          (ramificationIndex F K : ℤ) = q ∧
      (r + 1 + (differentExponent F K : ℤ)) /
          (ramificationIndex F K : ℤ) = q + 1 := by
  constructor
  · rw [hram, hodd]
    norm_num
    omega
  · rw [hram]
    have hdepth : r + 1 + (differentExponent F K : ℤ) = 2 * (q + 1) := by
      omega
    rw [hdepth]
    norm_num

/-- In ramification index two and at an odd shifted depth, trace induces the quadratic
graded map `𝔭_K^r/𝔭_K^{r+1} → 𝔭_F^q/𝔭_F^{q+1}`. -/
noncomputable def quadraticGradedTrace
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {r q : ℤ}
    (hram : ramificationIndex F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1) :
    LatticeGradedPiece K r →ₗ[ringOfIntegers F] LatticeGradedPiece F q := by
  apply traceLatticeGraded F K r q
  · intro x hx
    have ht := trace_mem_lattice_floor F K π hπ hgen r hx
    rw [(quadratic_trace_depths F K hram hodd).1] at ht
    exact ht
  · intro x hx
    have ht := trace_mem_lattice_floor F K π hπ hgen (r + 1) hx
    rw [(quadratic_trace_depths F K hram hodd).2] at ht
    exact ht

/-- The quadratic graded trace sends the class of `x` to the class of `Tr(x)`. -/
@[simp]
theorem quadraticGradedTrace_mk
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {r q : ℤ}
    (hram : ramificationIndex F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1)
    (x : lattice K r) :
    quadraticGradedTrace F K π hπ hgen hram hodd
        (latticeQuotientMk K (show r ≤ r + 1 by omega) x) =
      latticeQuotientMk F (show q ≤ q + 1 by omega)
        ⟨trace F K x, by
          have ht := trace_mem_lattice_floor F K π hπ hgen r x.property
          rw [(quadratic_trace_depths F K hram hodd).1] at ht
          exact ht⟩ :=
  rfl

/-- Exact kernel statement for the quadratic graded trace.  This is the manuscript's shell
criterion and includes the endpoint `r = 0`. -/
theorem quadratic_trace_mem_succ_iff
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {r q : ℤ} (_hr : 0 ≤ r)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1)
    {x : K} (hx : x ∈ lattice K r) :
    trace F K x ∈ lattice F (q + 1) ↔ x ∈ lattice K (r + 1) := by
  have hresDegree : residueDegree F K = 1 := by
    have hprod := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hdegree, hram] at hprod
    omega
  have hres : Function.Surjective (extensionResidueMap F K) :=
    extensionResidueMap_surjective_of_residueDegree_eq_one F K hresDegree
  have hdualTest :
      Submodule.traceDual (ringOfIntegers F) F
          (lattice K (-r - 1 - (differentExponent F K : ℤ))) =
        lattice K (r + 1) := by
    have h := traceDual_lattice F K π hπ hgen
      (-r - 1 - (differentExponent F K : ℤ))
    convert h using 1
    ring_nf
  constructor
  · intro htrace
    exact quadratic_trace_kernel_step_of_traceDual F K
      (differentExponent F K : ℤ) r q hram hodd hres
      (traceDual_lattice_zero F K π hπ hgen) hdualTest hx htrace
  · intro hxdeep
    have ht := trace_mem_lattice_floor F K π hπ hgen (r + 1) hxdeep
    rw [(quadratic_trace_depths F K hram hodd).2] at ht
    exact ht

/-- The quadratic graded trace is bijective.  Surjectivity comes from the exact trace-image
formula, while injectivity is the representative-level shell criterion. -/
theorem quadraticGradedTrace_bijective
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {r q : ℤ} (hr : 0 ≤ r)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1) :
    Function.Bijective (quadraticGradedTrace F K π hπ hgen hram hodd) := by
  let hmem : ∀ x : K, x ∈ lattice K r → trace F K x ∈ lattice F q := by
    intro x hx
    have ht := trace_mem_lattice_floor F K π hπ hgen r hx
    rw [(quadratic_trace_depths F K hram hodd).1] at ht
    exact ht
  let hdeep : ∀ x : K, x ∈ lattice K (r + 1) →
      trace F K x ∈ lattice F (q + 1) := by
    intro x hx
    have ht := trace_mem_lattice_floor F K π hπ hgen (r + 1) hx
    rw [(quadratic_trace_depths F K hram hodd).2] at ht
    exact ht
  apply traceLatticeGraded_bijective F K r q hmem hdeep
  · intro y hy
    exact (mem_trace_lattice_image_iff F K π hπ hgen r y).1
      (by simpa only [(quadratic_trace_depths F K hram hodd).1] using hy)
  · intro x hx htrace
    exact (quadratic_trace_mem_succ_iff F K π hπ hgen hr hram hdegree hodd hx).1
      htrace

/-- The exact quadratic graded-trace isomorphism required downstream. -/
noncomputable def quadraticGradedTraceEquiv
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {r q : ℤ} (hr : 0 ≤ r)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1) :
    LatticeGradedPiece K r ≃ₗ[ringOfIntegers F] LatticeGradedPiece F q :=
  LinearEquiv.ofBijective (quadraticGradedTrace F K π hπ hgen hram hodd)
    (quadraticGradedTrace_bijective F K π hπ hgen hr hram hdegree hodd)

/-- Wild-quadratic specialization with the manuscript's lower-break convention
`T = t + 1` made explicit. -/
noncomputable def wildQuadraticGradedTraceEquiv
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (_htpos : 0 < t)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    {r q : ℤ} (hr : 0 ≤ r)
    (hodd : r + ((t + 1 : ℕ) : ℤ) = 2 * q + 1) :
    LatticeGradedPiece K r ≃ₗ[ringOfIntegers F] LatticeGradedPiece F q := by
  have hDnat := differentExponent_wildQuadratic_eq F K ht hdegree π hπ hgen
  have hD : (differentExponent F K : ℤ) = ((t + 1 : ℕ) : ℤ) := by
    exact_mod_cast hDnat
  exact quadraticGradedTraceEquiv F K π hπ hgen hr hram hdegree (by omega)

/-- At an odd shifted depth, trace has exact target order exactly when its argument has exact
source order.  In particular the zero element lies in neither exact shell. -/
theorem quadratic_trace_shell_iff
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    {r q : ℤ} (hr : 0 ≤ r)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    (hodd : r + (differentExponent F K : ℤ) = 2 * q + 1)
    (x : K) (hx : x ∈ lattice K r) :
    ord F (trace F K x) = (q : WithTop ℤ) ↔
      ord K x = (r : WithTop ℤ) := by
  have htraceLower : trace F K x ∈ lattice F q := by
    have ht := trace_mem_lattice_floor F K π hπ hgen r hx
    rw [(quadratic_trace_depths F K hram hodd).1] at ht
    exact ht
  have hkernel :=
    quadratic_trace_mem_succ_iff F K π hπ hgen hr hram hdegree hodd hx
  rw [← mem_lattice_and_not_mem_succ_iff F,
    ← mem_lattice_and_not_mem_succ_iff K]
  constructor
  · rintro ⟨_hlower, hnotDeep⟩
    exact ⟨hx, fun hxDeep ↦ hnotDeep (hkernel.2 hxDeep)⟩
  · rintro ⟨_hlower, hnotDeep⟩
    exact ⟨htraceLower, fun htraceDeep ↦ hnotDeep (hkernel.1 htraceDeep)⟩

private theorem trace_one_eq_two
    (F K : Type*) [Field F] [Field K]
    [Algebra F K] [Module.Free F K]
    (hdegree : Module.finrank F K = 2) :
    trace F K (1 : K) = (2 : F) := by
  rw [← map_one (algebraMap F K), trace_algebraMap, hdegree]
  norm_num

/-- If the quadratic different exponent `T` is odd, then the lower-field order of `2` is
`(T - 1) / 2`. -/
theorem quadratic_ord_two
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    {d : ℤ}
    (hodd : (differentExponent F K : ℤ) = 2 * d + 1) :
    ord F (2 : F) = (d : WithTop ℤ) := by
  have hshell := quadratic_trace_shell_iff F K π hπ hgen
    (r := 0) (q := d) (by omega) hram hdegree
    (by simpa only [zero_add] using hodd) 1 (by simp)
  have hshell' : ord F (trace F K (1 : K)) = (d : WithTop ℤ) :=
    hshell.mpr (by simp)
  rwa [trace_one_eq_two F K hdegree] at hshell'

/-- For a quadratic odd different exponent, trace of an integral unit agrees with twice any
lower-field lift of its residue modulo the next lattice. -/
theorem quadratic_unit_trace_congr
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    {d : ℤ}
    (hodd : (differentExponent F K : ℤ) = 2 * d + 1)
    (w : ringOfIntegers K) (_hwUnit : IsUnit w)
    (wtilde : ringOfIntegers F)
    (hw : residueMap K w =
      extensionResidueMap F K (residueMap F wtilde)) :
    trace F K (w : K) - (2 : F) * (wtilde : F) ∈ lattice F (d + 1) := by
  let wtildeK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) wtilde
  have hres : residueMap K w = residueMap K wtildeK := by
    change residueMap K w = extensionResidueMap F K (residueMap F wtilde)
    exact hw
  have hdiffK : (w : K) - (wtildeK : K) ∈ lattice K 1 :=
    (residueMap_eq_residueMap_iff K w wtildeK).1 hres
  have ht := trace_mem_lattice_floor F K π hπ hgen 1 hdiffK
  have hfloor : ((1 : ℤ) + (differentExponent F K : ℤ)) /
      (ramificationIndex F K : ℤ) = d + 1 := by
    rw [hram, hodd]
    omega
  rw [hfloor] at ht
  have hwcoe : (wtildeK : K) = algebraMap F K (wtilde : F) := rfl
  rw [hwcoe, map_sub, trace_algebraMap, hdegree] at ht
  norm_num at ht
  have hneg := neg_mem_lattice F ht
  simpa only [neg_sub] using hneg

/-- The manuscript's strict odd-conductor specialization: if `m = 2d + 1 > T` and
`r = m - T`, then the quadratic graded trace identifies depth `r` with depth `d`. -/
noncomputable def quadraticOddConductorGradedTraceEquiv
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    {T m d r : ℤ}
    (hT : (differentExponent F K : ℤ) = T)
    (hm : m = 2 * d + 1) (hr : r = m - T) (hstrict : T < m) :
    LatticeGradedPiece K r ≃ₗ[ringOfIntegers F] LatticeGradedPiece F d :=
  quadraticGradedTraceEquiv F K π hπ hgen (by omega) hram hdegree (by omega)

/-- Exact nonzero-shell form of the strict odd-conductor specialization.  The minus sign used
downstream does not change normalized order. -/
theorem quadratic_odd_conductor_neg_trace_shell_iff
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤)
    (hram : ramificationIndex F K = 2)
    (hdegree : Module.finrank F K = 2)
    {T m d r : ℤ}
    (hT : (differentExponent F K : ℤ) = T)
    (hm : m = 2 * d + 1) (hr : r = m - T) (hstrict : T < m)
    (x : K) (hx : x ∈ lattice K r) :
    ord F (-trace F K x) = (d : WithTop ℤ) ↔
      ord K x = (r : WithTop ℤ) := by
  rw [ord_neg]
  exact quadratic_trace_shell_iff F K π hπ hgen (by omega) hram hdegree
    (by omega) x hx

end

end LanglandsFirstMainLemma
