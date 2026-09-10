import LanglandsFirstMainLemma.Ramification.Herbrand
import LanglandsFirstMainLemma.Ramification.TraceIdeals
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.LocalField.SuccessiveLifting
import LanglandsFirstMainLemma.LocalField.FiniteQuotients

namespace LanglandsFirstMainLemma

noncomputable section

open Filter Topology

def aboveBreakSourceDepth (t ell r : ℕ) : ℕ :=
  herbrandPsiNat t ell r

theorem aboveBreakSourceDepth_eq (t ell : ℕ) {r : ℕ} (hr : t ≤ r) :
    aboveBreakSourceDepth t ell r = t + ell * (r - t) := by
  exact herbrandPsiNat_of_break_le t ell hr

theorem aboveBreak_trace_floor
    (t ell : ℕ) (hell : 0 < ell) {r : ℕ} (hr : t < r) :
    (((aboveBreakSourceDepth t ell r : ℕ) : ℤ) +
        (((ell - 1) * (t + 1) : ℕ) : ℤ)) / (ell : ℤ) = (r : ℤ) := by
  have htr : t ≤ r := hr.le
  have hnumNat : aboveBreakSourceDepth t ell r + (ell - 1) * (t + 1) =
      ell * r + (ell - 1) := by
    rw [aboveBreakSourceDepth_eq t ell htr]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
    simp only [Nat.add_sub_cancel_left, Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  have hnum : ((aboveBreakSourceDepth t ell r : ℕ) : ℤ) +
        (((ell - 1) * (t + 1) : ℕ) : ℤ) =
      (ell : ℤ) * (r : ℤ) + ((ell - 1 : ℕ) : ℤ) := by
    exact_mod_cast hnumNat
  rw [hnum, Int.mul_add_ediv_left _ _ (by exact_mod_cast hell.ne')]
  have hsmall : (((ell - 1 : ℕ) : ℤ) / (ell : ℤ)) = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · positivity
    · exact_mod_cast Nat.sub_lt hell Nat.zero_lt_one
  rw [hsmall, add_zero]

theorem aboveBreak_trace_floor_succ
    (t ell : ℕ) (hell : 0 < ell) {r : ℕ} (hr : t < r) :
    ((((aboveBreakSourceDepth t ell r + 1 : ℕ) : ℤ) +
        (((ell - 1) * (t + 1) : ℕ) : ℤ)) / (ell : ℤ)) = ((r + 1 : ℕ) : ℤ) := by
  have htr : t ≤ r := hr.le
  have hnumNat : aboveBreakSourceDepth t ell r + 1 + (ell - 1) * (t + 1) =
      ell * (r + 1) := by
    rw [aboveBreakSourceDepth_eq t ell htr]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
    simp only [Nat.add_sub_cancel_left, Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  have hnum : (((aboveBreakSourceDepth t ell r + 1 : ℕ) : ℤ) +
        (((ell - 1) * (t + 1) : ℕ) : ℤ)) =
      (ell : ℤ) * ((r + 1 : ℕ) : ℤ) := by
    exact_mod_cast hnumNat
  rw [hnum]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hell.ne')

section PositiveBreakCharacteristic

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

private noncomputable def aboveBreakRamificationRatioUnit (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) : Kˣ :=
  Units.mk0 ((σ : Gal(K/F)) π / π)
    (div_ne_zero ((map_ne_zero (σ : Gal(K/F))).2 hπ.ne_zero) hπ.ne_zero)

@[simp]
private theorem coe_aboveBreakRamificationRatioUnit (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    (aboveBreakRamificationRatioUnit F K i σ π hπ : K) =
      (σ : Gal(K/F)) π / π :=
  rfl

private theorem aboveBreakRamificationRatioUnit_mem (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ)) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    aboveBreakRamificationRatioUnit F K i σ π hπ ∈ unitFiltration K i := by
  cases i with
  | zero =>
      rw [mem_unitFiltration_zero, coe_aboveBreakRamificationRatioUnit,
        ord_div, ord_galoisConjugate, ord_uniformizer K hπ]
      simp
  | succ n =>
      rw [mem_unitFiltration_succ, congruentAtDepth_iff_sub_mem_lattice K]
      change ((σ : Gal(K/F)) π / π - 1) ∈ lattice K (((n + 1 : ℕ) : ℤ))
      rw [div_sub_one hπ.ne_zero]
      rw [div_mem_lattice_iff K π ((σ : Gal(K/F)) π - π) 1
        (((n + 1 : ℕ) : ℤ)) (ord_uniformizer K hπ)]
      have hs := (lowerRamificationDisplacement F K σ π hπ).property
      change ((σ : Gal(K/F)) π - π) ∈ lattice K (((n + 1 : ℕ) : ℤ) + 1) at hs
      simpa only [add_comm] using hs

private noncomputable def aboveBreakRamificationUnitGradedPreHom (i : ℕ) (π : K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer π) :
    lowerRamificationGroup F K (i : ℤ) →* UnitGradedPiece K i where
  toFun σ := unitGradedMk K i
    ⟨aboveBreakRamificationRatioUnit F K i σ π hπ,
      aboveBreakRamificationRatioUnit_mem F K i σ π hπ⟩
  map_one' := by
    apply (unitGradedMk_eq_one_iff K i _).2
    simpa [aboveBreakRamificationRatioUnit, hπ.ne_zero] using
      (unitFiltration K (i + 1)).one_mem
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

private theorem aboveBreakRamificationRatioUnit_mem_succ_iff (i : ℕ)
    (σ : lowerRamificationGroup F K (i : ℤ))
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    aboveBreakRamificationRatioUnit F K i σ (π : K) hπ ∈
        unitFiltration K (i + 1) ↔
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

private theorem aboveBreak_residueCharacteristic_mem_lattice_one :
    (((residueCharacteristic K : ℕ) : ringOfIntegers K) : K) ∈ lattice K 1 := by
  apply (residueMap_eq_zero_iff K (residueCharacteristic K : ringOfIntegers K)).1
  change (residueCharacteristic K : ResidueField K) = 0
  exact CharP.cast_eq_zero (ResidueField K) (residueCharacteristic K)

private theorem aboveBreak_residueCharacteristic_nsmul_latticeGraded_eq_zero
    (s : ℤ) (z : LatticeGradedPiece K s) :
    residueCharacteristic K • z = 0 := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective K
    (show s ≤ s + 1 by omega) z
  rw [← Nat.cast_smul_eq_nsmul (ringOfIntegers K), ← map_smul]
  apply (latticeQuotientMk_eq_zero_iff K (show s ≤ s + 1 by omega)).2
  change (((residueCharacteristic K : ℕ) : ringOfIntegers K) : K) *
      (x : K) ∈ lattice K (s + 1)
  simpa only [add_comm] using mul_mem_lattice K
    (aboveBreak_residueCharacteristic_mem_lattice_one K) x.property

private theorem aboveBreak_residueCharacteristic_pow_unitGraded_eq_one
    (n : ℕ) (u : UnitGradedPiece K (n + 1)) :
    u ^ residueCharacteristic K = 1 := by
  let e := positiveUnitGradedAddEquivLattice K n
  have hz := aboveBreak_residueCharacteristic_nsmul_latticeGraded_eq_zero K
    (((n + 1 : ℕ) : ℤ)) (e (Additive.ofMul u))
  have hu : residueCharacteristic K • Additive.ofMul u = 0 := by
    apply e.injective
    rw [map_nsmul, map_zero]
    exact hz
  have := congrArg Additive.toMul hu
  simpa only [toMul_nsmul, toMul_ofMul, toMul_zero] using this

variable [PrimeCyclicExtension F K]

private noncomputable def aboveBreakGeneratorInLowerBreak {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    lowerRamificationGroup F K (t : ℤ) :=
  ⟨PrimeCyclicExtension.generator F K, by rw [ht.1]; trivial⟩

/-- A positive break derives the wild characteristic equality from the faithful positive
ramification coordinate; it is not assumed by the norm theorem. -/
theorem residueCharacteristic_eq_degree_of_positive_break
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (π : ringOfIntegers K)
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({π} : Set (ringOfIntegers K)) = ⊤) :
    residueCharacteristic F = Module.finrank F K := by
  let σ := aboveBreakGeneratorInLowerBreak F K ht
  let u : UnitGradedPiece K t :=
    aboveBreakRamificationUnitGradedPreHom F K t (π : K) hπ σ
  have hσorder : orderOf σ = Module.finrank F K := by
    calc
      orderOf σ = orderOf (PrimeCyclicExtension.generator F K) := by
        rw [← orderOf_submonoid σ]
        rfl
      _ = Module.finrank F K := PrimeCyclicExtension.orderOf_generator F K
  have hupowDegree : u ^ Module.finrank F K = 1 := by
    change (aboveBreakRamificationUnitGradedPreHom F K t (π : K) hπ σ) ^
      Module.finrank F K = 1
    rw [← map_pow, ← hσorder, pow_orderOf_eq_one, map_one]
  have hune : u ≠ 1 := by
    intro hu
    change unitGradedMk K t
        ⟨aboveBreakRamificationRatioUnit F K t σ (π : K) hπ,
          aboveBreakRamificationRatioUnit_mem F K t σ (π : K) hπ⟩ = 1 at hu
    rw [unitGradedMk_eq_one_iff,
      aboveBreakRamificationRatioUnit_mem_succ_iff F K t σ π hπ hgen,
      ht.2, Subgroup.mem_bot] at hu
    exact PrimeCyclicExtension.generator_ne_one F K hu
  have huorderDvd : orderOf u ∣ Module.finrank F K :=
    orderOf_dvd_iff_pow_eq_one.mpr hupowDegree
  have huorder : orderOf u = Module.finrank F K := by
    rcases (Nat.dvd_prime (PrimeCyclicExtension.degree_prime F K)).1 huorderDvd with
      horder | horder
    · exact (hune (orderOf_eq_one_iff.mp horder)).elim
    · exact horder
  have hupowChar : u ^ residueCharacteristic K = 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
    exact aboveBreak_residueCharacteristic_pow_unitGraded_eq_one K n u
  have hdvd : Module.finrank F K ∣ residueCharacteristic K := by
    rw [← huorder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hupowChar
  have hdegree : Module.finrank F K = residueCharacteristic K :=
    (Nat.prime_dvd_prime_iff_eq
      (PrimeCyclicExtension.degree_prime F K)
      (residueCharacteristic_prime K)).mp hdvd
  rw [← residueCharacteristic_extension_eq F K]
  exact hdegree.symm

end PositiveBreakCharacteristic

section Congruence

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

private theorem aboveBreak_traceIdealLowerBound
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    TraceIdealLowerBound F K (Module.finrank F K)
      (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  intro q z hz
  have hzlat : z ∈ lattice K q := hz
  have htrace := trace_mem_lattice_floor F K pi hpi hgen q hzlat
  rw [differentExponent_eq F K ht pi hpi hgen, hram] at htrace
  exact htrace

/-- Exact elementary-symmetric expansion of `N(1+x)-1`. -/
theorem norm_one_add_sub_one_eq_sum_elementarySymmetric (x : K) :
    norm F K (1 + x) - 1 =
      ∑ j ∈ Finset.range (Module.finrank F K),
        elementarySymmetric F K (j + 1) x := by
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric]
  ring

/-- Every elementary-symmetric coefficient of degree at least two vanishes at the next target
depth above the break.  The terminal coefficient is treated by the exact norm valuation; the
intermediate coefficients use the wild bound for `t>0` and the totally ramified ceiling bound
for `t=0`. -/
theorem higher_elementarySymmetric_mem_lattice_aboveBreak
    {t r j : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K)
    (hx : ((aboveBreakSourceDepth t (Module.finrank F K) r : ℕ) : WithTop ℤ) ≤
      ord K x)
    (hjtwo : 2 ≤ j) (hjle : j ≤ Module.finrank F K) :
    elementarySymmetric F K j x ∈ lattice F ((r + 1 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  let a := aboveBreakSourceDepth t p r
  have hp := PrimeCyclicExtension.degree_prime F K
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hram : ramificationIndex F K = p := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  have ha : a = t + p * (r - t) := aboveBreakSourceDepth_eq t p hr.le
  have hra : r + 1 ≤ a := by
    have hdiff : 1 ≤ r - t := by omega
    have hmul := Nat.mul_le_mul_right (r - t) hp2
    rw [ha]
    nlinarith [Nat.sub_add_cancel hr.le]
  by_cases hjtop : j = p
  · subst j
    rw [mem_lattice, elementarySymmetric_degree_ord F K p rfl hram]
    exact (show ((r + 1 : ℕ) : WithTop ℤ) ≤ (a : WithTop ℤ) by
      exact_mod_cast hra).trans (by simpa only [a, p] using hx)
  · have hjlt : j < p := by omega
    rw [mem_lattice]
    by_cases ht0 : t = 0
    · subst t
      have ha0 : a = p * r := by simp [a, aboveBreakSourceDepth, herbrandPsiNat]
      have hxInt : (((a : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x := by
        rw [← show (a : WithTop ℤ) = (((a : ℕ) : ℤ) : WithTop ℤ) by norm_num]
        simpa only [a, p] using hx
      have hs := totallyRamified_elementarySymmetric_bound F K p (a : ℤ)
        hp0 rfl hram hxInt j hjlt.le
      apply (show (((r + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
          (integerCeilingDiv ((j : ℤ) * (a : ℤ)) p : WithTop ℤ) by
        rw [WithTop.coe_le_coe, integerCeilingDiv]
        rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp0)]
        have hr1 : 1 ≤ r := by omega
        have hnat : p * (r + 1) ≤ j * p * r := by
          calc
            p * (r + 1) ≤ p * (2 * r) := Nat.mul_le_mul_left p (by omega)
            _ = 2 * p * r := by ring
            _ ≤ j * p * r := by gcongr
        have hnatZ : (p : ℤ) * ((r + 1 : ℕ) : ℤ) ≤
            (j : ℤ) * (p : ℤ) * (r : ℤ) := by exact_mod_cast hnat
        rw [ha0]
        have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp0
        have hpminus : (0 : ℤ) ≤ (p : ℤ) - 1 := by omega
        have hmain : (p : ℤ) * ((r + 1 : ℕ) : ℤ) ≤
            (j : ℤ) * (p : ℤ) * (r : ℤ) + (p : ℤ) - 1 := by nlinarith
        convert hmain using 1 <;> push_cast <;> ring).trans hs
    · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
      have htrace := aboveBreak_traceIdealLowerBound F K ht hres pi hpi hgen
      have hdepth : p * (r + 1) ≤ 2 * a + (p - 1) * (t + 1) := by
        rw [ha]
        have hdiff : 1 ≤ r - t := by omega
        have hsub := Nat.sub_add_cancel hr.le
        have hpsub := Nat.sub_add_cancel (show 1 ≤ p by omega)
        nlinarith
      exact wild_intermediateSymmetric_bound F K p (t + 1) a (r + 1)
        hp (by omega) (hchar htpos) rfl
        (by simpa [p, wildDifferentContribution] using htrace)
        hdepth (by simpa only [a, p] using hx) hjtwo hjlt

theorem norm_one_add_sub_one_sub_trace_mem_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r)
    (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K)
    (hx : ((aboveBreakSourceDepth t (Module.finrank F K) r : ℕ) : WithTop ℤ) ≤
      ord K x) :
    norm F K (1 + x) - 1 - trace F K x ∈ lattice F ((r + 1 : ℕ) : ℤ) := by
  have hp2 : 2 ≤ Module.finrank F K :=
    (PrimeCyclicExtension.degree_prime F K).two_le
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric, add_sub_cancel_left]
  rw [show Module.finrank F K = (Module.finrank F K - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  rw [elementarySymmetric_one, add_sub_cancel_right, mem_lattice]
  apply ord_sum F
  intro j hj
  simp only [Finset.mem_range] at hj
  exact higher_elementarySymmetric_mem_lattice_aboveBreak F K ht hr hres hchar
    pi hpi hgen x hx (by omega) (by omega)

theorem trace_lattice_image_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K (aboveBreakSourceDepth t (Module.finrank F K) r : ℤ)).restrictScalars
          (ringOfIntegers F)) =
      lattice F (r : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  rw [trace_lattice_image_eq F K pi hpi hgen]
  rw [differentExponent_eq F K ht pi hpi hgen, hram]
  rw [aboveBreak_trace_floor t (Module.finrank F K)
    (PrimeCyclicExtension.degree_prime F K).pos hr]

theorem trace_lattice_image_aboveBreak_succ
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K ((aboveBreakSourceDepth t (Module.finrank F K) r + 1 : ℕ) : ℤ)).restrictScalars
          (ringOfIntegers F)) =
      lattice F ((r + 1 : ℕ) : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdeg := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdeg
    exact hdeg.symm
  rw [trace_lattice_image_eq F K pi hpi hgen]
  rw [differentExponent_eq F K ht pi hpi hgen, hram]
  rw [aboveBreak_trace_floor_succ t (Module.finrank F K)
    (PrimeCyclicExtension.degree_prime F K).pos hr]

theorem trace_mem_lattice_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    {x : K} (hx : x ∈ lattice K (aboveBreakSourceDepth t (Module.finrank F K) r : ℤ)) :
    trace F K x ∈ lattice F (r : ℤ) := by
  have hmap := trace_lattice_image_aboveBreak F K ht hr hres pi hpi hgen
  rw [← hmap]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

theorem trace_mem_lattice_aboveBreak_succ
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    {x : K}
    (hx : x ∈ lattice K ((aboveBreakSourceDepth t (Module.finrank F K) r + 1 : ℕ) : ℤ)) :
    trace F K x ∈ lattice F ((r + 1 : ℕ) : ℤ) := by
  have hmap := trace_lattice_image_aboveBreak_succ F K ht hr hres pi hpi hgen
  rw [← hmap]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

end Congruence

section FilteredNorm

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The norm carries one certified source layer into a possibly differently numbered target
layer. -/
def AboveBreakNormMapsUnitFiltration (sourceDepth targetDepth : ℕ) : Prop :=
  ∀ u : Kˣ, u ∈ unitFiltration K sourceDepth →
    normUnits F K u ∈ unitFiltration F targetDepth

/-- Restriction of norm between a certified pair of filtration layers. -/
noncomputable def aboveBreakNormUnitFiltrationHom (sourceDepth targetDepth : ℕ)
    (hmap : AboveBreakNormMapsUnitFiltration F K sourceDepth targetDepth) :
    unitFiltration K sourceDepth →* unitFiltration F targetDepth :=
  ((normUnits F K).comp (unitFiltration K sourceDepth).subtype).codRestrict
    (unitFiltration F targetDepth) (fun u ↦ hmap u u.property)

@[simp]
theorem coe_aboveBreakNormUnitFiltrationHom (sourceDepth targetDepth : ℕ)
    (hmap : AboveBreakNormMapsUnitFiltration F K sourceDepth targetDepth)
    (u : unitFiltration K sourceDepth) :
    ((aboveBreakNormUnitFiltrationHom F K sourceDepth targetDepth hmap u :
        unitFiltration F targetDepth) : Fˣ) = normUnits F K (u : Kˣ) :=
  rfl

/-- The heterogeneous norm map on unit-filtration quotients.  Numerator and denominator
containment are separate inputs, so representative independence is explicit. -/
noncomputable def aboveBreakNormUnitFiltrationQuotient
    {sourceNumerator sourceDenominator targetNumerator targetDenominator : ℕ}
    (hsource : sourceNumerator ≤ sourceDenominator)
    (htarget : targetNumerator ≤ targetDenominator)
    (hnum : AboveBreakNormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden : AboveBreakNormMapsUnitFiltration F K sourceDenominator targetDenominator) :
    UnitFiltrationQuotient K sourceNumerator sourceDenominator hsource →*
      UnitFiltrationQuotient F targetNumerator targetDenominator htarget :=
  QuotientGroup.lift (unitFiltrationInside K hsource)
    ((unitFiltrationQuotientMk F htarget).comp
      (aboveBreakNormUnitFiltrationHom F K sourceNumerator targetNumerator hnum)) (by
        intro u hu
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
          unitFiltrationQuotientMk_eq_one_iff]
        exact hden (u : Kˣ) ((mem_unitFiltrationInside K hsource u).1 hu))

@[simp]
theorem aboveBreakNormUnitFiltrationQuotient_mk
    {sourceNumerator sourceDenominator targetNumerator targetDenominator : ℕ}
    (hsource : sourceNumerator ≤ sourceDenominator)
    (htarget : targetNumerator ≤ targetDenominator)
    (hnum : AboveBreakNormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden : AboveBreakNormMapsUnitFiltration F K sourceDenominator targetDenominator)
    (u : unitFiltration K sourceNumerator) :
    aboveBreakNormUnitFiltrationQuotient F K hsource htarget hnum hden
        (unitFiltrationQuotientMk K hsource u) =
      unitFiltrationQuotientMk F htarget
        (aboveBreakNormUnitFiltrationHom F K sourceNumerator targetNumerator hnum u) :=
  rfl

theorem aboveBreakNormUnitFiltrationQuotient_deeper_eq_one
    {sourceNumerator sourceDenominator targetNumerator targetDenominator : ℕ}
    (hsource : sourceNumerator ≤ sourceDenominator)
    (htarget : targetNumerator ≤ targetDenominator)
    (hnum : AboveBreakNormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden : AboveBreakNormMapsUnitFiltration F K sourceDenominator targetDenominator)
    (u : unitFiltration K sourceNumerator)
    (hu : (u : Kˣ) ∈ unitFiltration K sourceDenominator) :
    aboveBreakNormUnitFiltrationQuotient F K hsource htarget hnum hden
        (unitFiltrationQuotientMk K hsource u) = 1 := by
  rw [aboveBreakNormUnitFiltrationQuotient_mk,
    unitFiltrationQuotientMk_eq_one_iff]
  exact hden (u : Kˣ) hu

/-- Quotient norm commutes with replacing both denominator depths by shallower certified
denominators. -/
theorem aboveBreakNormUnitFiltrationQuotient_projection
    {sourceNumerator sourceDenominator₁ sourceDenominator₂
      targetNumerator targetDenominator₁ targetDenominator₂ : ℕ}
    (hsource₁ : sourceNumerator ≤ sourceDenominator₁)
    (hsource₁₂ : sourceDenominator₁ ≤ sourceDenominator₂)
    (htarget₁ : targetNumerator ≤ targetDenominator₁)
    (htarget₁₂ : targetDenominator₁ ≤ targetDenominator₂)
    (hnum : AboveBreakNormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden₁ : AboveBreakNormMapsUnitFiltration F K sourceDenominator₁ targetDenominator₁)
    (hden₂ : AboveBreakNormMapsUnitFiltration F K sourceDenominator₂ targetDenominator₂) :
    (unitFiltrationQuotientProjection F htarget₁ htarget₁₂).comp
        (aboveBreakNormUnitFiltrationQuotient F K
          (hsource₁.trans hsource₁₂) (htarget₁.trans htarget₁₂) hnum hden₂) =
      (aboveBreakNormUnitFiltrationQuotient F K hsource₁ htarget₁ hnum hden₁).comp
        (unitFiltrationQuotientProjection K hsource₁ hsource₁₂) := by
  ext z
  rfl

end FilteredNorm

section AboveBreakContainment

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

theorem normMapsUnitFiltration_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    AboveBreakNormMapsUnitFiltration F K
      (aboveBreakSourceDepth t (Module.finrank F K) r) r := by
  let a := aboveBreakSourceDepth t (Module.finrank F K) r
  intro u hu
  have ha0 : 0 < a := by
    have hra : r ≤ a := self_le_herbrandPsiNat t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos r
    exact lt_of_lt_of_le (Nat.zero_lt_of_lt hr) hra
  have haeq : a = (a - 1) + 1 := by omega
  have hx : (u : K) - 1 ∈ lattice K (a : ℤ) := by
    have hu' := (mem_unitFiltration_succ_iff_sub_mem_lattice K (a - 1) u).1
      (by simpa only [← haeq] using hu)
    simpa only [← haeq] using hu'
  have htrace := trace_mem_lattice_aboveBreak F K ht hr hres pi hpi hgen hx
  have hxord : (a : WithTop ℤ) ≤ ord K ((u : K) - 1) := by
    rw [show (a : WithTop ℤ) = (((a : ℕ) : ℤ) : WithTop ℤ) by norm_num]
    exact hx
  have hrem := norm_one_add_sub_one_sub_trace_mem_aboveBreak F K ht hr hres hchar
    pi hpi hgen ((u : K) - 1) (by simpa only [a] using hxord)
  have hnorm : norm F K (u : K) - 1 ∈ lattice F (r : ℤ) := by
    have hrem' : norm F K (u : K) - 1 - trace F K ((u : K) - 1) ∈
        lattice F (r : ℤ) := by
      have hunit : 1 + ((u : K) - 1) = (u : K) := by ring
      rw [hunit] at hrem
      exact lattice_antitone F
        (show (r : ℤ) ≤ ((r + 1 : ℕ) : ℤ) by omega) hrem
    have hsum := add_mem_lattice F htrace hrem'
    convert hsum using 1 <;> ring
  have hr0 : 0 < r := Nat.zero_lt_of_lt hr
  have hreq : r = (r - 1) + 1 := by omega
  rw [hreq]
  apply (mem_unitFiltration_succ_iff_sub_mem_lattice F (r - 1)
    (normUnits F K u)).2
  change norm F K (u : K) - 1 ∈ lattice F (((r - 1 + 1 : ℕ) : ℤ))
  simpa only [← hreq] using hnorm

theorem normMapsUnitFiltration_aboveBreak_succ
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    AboveBreakNormMapsUnitFiltration F K
      (aboveBreakSourceDepth t (Module.finrank F K) r + 1) (r + 1) := by
  let a := aboveBreakSourceDepth t (Module.finrank F K) r
  intro u hu
  have ha0 : 0 < a := by
    have hra : r ≤ a := self_le_herbrandPsiNat t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos r
    exact lt_of_lt_of_le (Nat.zero_lt_of_lt hr) hra
  have hxdeep : (u : K) - 1 ∈ lattice K ((a + 1 : ℕ) : ℤ) := by
    exact (mem_unitFiltration_succ_iff_sub_mem_lattice K a u).1
      (by simpa only [a] using hu)
  have hx : (u : K) - 1 ∈ lattice K (a : ℤ) :=
    lattice_antitone K (by omega) hxdeep
  have htrace := trace_mem_lattice_aboveBreak_succ F K ht hr hres pi hpi hgen
    (by simpa only [a] using hxdeep)
  have hxord : (a : WithTop ℤ) ≤ ord K ((u : K) - 1) := by
    rw [show (a : WithTop ℤ) = (((a : ℕ) : ℤ) : WithTop ℤ) by norm_num]
    exact hx
  have hrem := norm_one_add_sub_one_sub_trace_mem_aboveBreak F K ht hr hres hchar
    pi hpi hgen ((u : K) - 1) (by simpa only [a] using hxord)
  have hnorm : norm F K (u : K) - 1 ∈ lattice F ((r + 1 : ℕ) : ℤ) := by
    have hunit : 1 + ((u : K) - 1) = (u : K) := by ring
    rw [hunit] at hrem
    have hsum := add_mem_lattice F htrace hrem
    convert hsum using 1 <;> ring
  exact (mem_unitFiltration_succ_iff_sub_mem_lattice F r
    (normUnits F K u)).2 (by simpa only [coe_normUnits] using hnorm)

/-- The norm on the above-break graded layer at upper depth `r`.  The source is the
Herbrand depth `Ψ(r)`, while the target remains `r`. -/
noncomputable def normGradedAboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    UnitGradedPiece K (aboveBreakSourceDepth t (Module.finrank F K) r) →*
      UnitGradedPiece F r :=
  aboveBreakNormUnitFiltrationQuotient F K
    (Nat.le_succ (aboveBreakSourceDepth t (Module.finrank F K) r))
    (Nat.le_succ r)
    (normMapsUnitFiltration_aboveBreak F K ht hr hres hchar pi hpi hgen)
    (normMapsUnitFiltration_aboveBreak_succ F K ht hr hres hchar pi hpi hgen)

@[simp]
theorem normGradedAboveBreak_mk
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r)) :
    normGradedAboveBreak F K ht hr hres hchar pi hpi hgen
        (unitGradedMk K (aboveBreakSourceDepth t (Module.finrank F K) r) u) =
      unitGradedMk F r
        (aboveBreakNormUnitFiltrationHom F K
          (aboveBreakSourceDepth t (Module.finrank F K) r) r
          (normMapsUnitFiltration_aboveBreak F K ht hr hres hchar pi hpi hgen) u) :=
  rfl

theorem normGradedAboveBreak_deeper_eq_one
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r))
    (hu : (u : Kˣ) ∈
      unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r + 1)) :
    normGradedAboveBreak F K ht hr hres hchar pi hpi hgen
        (unitGradedMk K (aboveBreakSourceDepth t (Module.finrank F K) r) u) = 1 := by
  exact aboveBreakNormUnitFiltrationQuotient_deeper_eq_one F K
    (Nat.le_succ (aboveBreakSourceDepth t (Module.finrank F K) r))
    (Nat.le_succ r)
    (normMapsUnitFiltration_aboveBreak F K ht hr hres hchar pi hpi hgen)
    (normMapsUnitFiltration_aboveBreak_succ F K ht hr hres hchar pi hpi hgen)
    u hu

/-- On representatives `u = 1+x`, the above-break graded norm is the trace class
`[1+Tr(x)]`.  The source and target representatives remain explicit certified units. -/
theorem normGradedAboveBreak_mk_eq_trace
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K)
    (hx : ((aboveBreakSourceDepth t (Module.finrank F K) r : ℕ) : WithTop ℤ) ≤
      ord K x)
    (u : unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r))
    (hu : ((u : Kˣ) : K) = 1 + x)
    (v : unitFiltration F r)
    (hv : ((v : Fˣ) : F) = 1 + trace F K x) :
    normGradedAboveBreak F K ht hr hres hchar pi hpi hgen
        (unitGradedMk K (aboveBreakSourceDepth t (Module.finrank F K) r) u) =
      unitGradedMk F r v := by
  rw [normGradedAboveBreak_mk]
  apply (unitGradedMk_eq_mk_iff F r _ _).2
  rw [congruentAtDepth_iff_sub_mem_lattice F]
  change norm F K ((u : Kˣ) : K) - ((v : Fˣ) : F) ∈
    lattice F ((r + 1 : ℕ) : ℤ)
  rw [hu, hv]
  have hrem := norm_one_add_sub_one_sub_trace_mem_aboveBreak F K ht hr hres hchar
    pi hpi hgen x hx
  convert hrem using 1 <;> ring

/-- At every strict above-break depth, the induced graded norm is surjective. -/
theorem norm_graded_surjective_above_break_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Surjective (normGradedAboveBreak F K ht hr hres hchar pi hpi hgen) := by
  let a := aboveBreakSourceDepth t (Module.finrank F K) r
  intro z
  obtain ⟨u, rfl⟩ := unitGradedMk_surjective F r z
  have hr0 : 0 < r := Nat.zero_lt_of_lt hr
  have hreq : r = (r - 1) + 1 := by omega
  have hy : ((u : Fˣ) : F) - 1 ∈ lattice F (r : ℤ) := by
    have hu' := (mem_unitFiltration_succ_iff_sub_mem_lattice F (r - 1) u).1
      (by simpa only [← hreq] using u.property)
    simpa only [← hreq] using hu'
  have htraceImage := trace_lattice_image_aboveBreak F K ht hr hres pi hpi hgen
  have hyMap : ((u : Fˣ) : F) - 1 ∈ Submodule.map
      ((trace F K).restrictScalars (ringOfIntegers F))
      ((lattice K (a : ℤ)).restrictScalars (ringOfIntegers F)) := by
    rw [htraceImage]
    exact hy
  obtain ⟨x, hx, htrace⟩ := Submodule.mem_map.mp hyMap
  have ha0 : 0 < a := by
    have hra : r ≤ a := self_le_herbrandPsiNat t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos r
    exact lt_of_lt_of_le hr0 hra
  have haeq : a = (a - 1) + 1 := by omega
  have hxAt : (x : K) ∈ lattice K (((a - 1) + 1 : ℕ) : ℤ) := by
    rw [← haeq]
    exact hx
  let xUnit : Kˣ := principalUnitOf K (a - 1) x hxAt
  have hxUnit : xUnit ∈ unitFiltration K a := by
    rw [haeq]
    exact principalUnitOf_mem K (a - 1) x hxAt
  let xs : unitFiltration K a := ⟨xUnit, hxUnit⟩
  refine ⟨unitGradedMk K a xs, ?_⟩
  rw [normGradedAboveBreak_mk]
  apply (unitGradedMk_eq_mk_iff F r _ _).2
  rw [congruentAtDepth_iff_sub_mem_lattice F]
  change norm F K (1 + (x : K)) - ((u : Fˣ) : F) ∈
    lattice F ((r + 1 : ℕ) : ℤ)
  have hxord : (a : WithTop ℤ) ≤ ord K (x : K) := by
    rw [show (a : WithTop ℤ) = (((a : ℕ) : ℤ) : WithTop ℤ) by norm_num]
    exact hx
  have hrem := norm_one_add_sub_one_sub_trace_mem_aboveBreak F K ht hr hres hchar
    pi hpi hgen (x : K) (by simpa only [a] using hxord)
  have htrace' : trace F K (x : K) = ((u : Fˣ) : F) - 1 := htrace
  rw [htrace'] at hrem
  convert hrem using 1 <;> ring

/-- One correction at an arbitrary strict above-break upper depth. -/
theorem exists_norm_aboveBreak_oneStep_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Fˣ) (hu : u ∈ unitFiltration F r) :
    ∃ x : Kˣ,
      x ∈ unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r) ∧
      u / normUnits F K x ∈ unitFiltration F (r + 1) := by
  let a := aboveBreakSourceDepth t (Module.finrank F K) r
  let u0 : unitFiltration F r := ⟨u, hu⟩
  obtain ⟨z, hz⟩ := norm_graded_surjective_above_break_of_characteristic F K
    ht hr hres hchar pi hpi hgen (unitGradedMk F r u0)
  obtain ⟨x0, rfl⟩ := unitGradedMk_surjective K a z
  refine ⟨(x0 : Kˣ), x0.property, ?_⟩
  have heq :
      unitGradedMk F r
          (aboveBreakNormUnitFiltrationHom F K a r
            (normMapsUnitFiltration_aboveBreak F K ht hr hres hchar pi hpi hgen) x0) =
        unitGradedMk F r u0 := by
    simpa only [normGradedAboveBreak_mk, a] using hz
  have hcong := (unitGradedMk_eq_mk_iff F r _ _).1 heq
  exact (div_mem_unitFiltration_iff_congruentAtDepth F (r + 1) u
    (normUnits F K (x0 : Kˣ))
    (unitFiltration_le_unitGroup F r hu)
    (unitFiltration_le_unitGroup F r
      (normMapsUnitFiltration_aboveBreak F K ht hr hres hchar pi hpi hgen
        (x0 : Kˣ) x0.property))).2 hcong.symm

/-- Successive lifting upgrades the graded corrections to exact norm surjectivity on the
complete unit layer at every strict above-break depth. -/
theorem norm_unitFiltration_surjective_aboveBreak_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    ∀ u : Fˣ, u ∈ unitFiltration F r →
      ∃ x : Kˣ,
        x ∈ unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r) ∧
        normUnits F K x = u := by
  let p := Module.finrank F K
  let a := aboveBreakSourceDepth t p r
  let sourceDepth : ℕ → ℕ := fun n ↦ (a - 1) + p * n
  have hp0 : 0 < p := (PrimeCyclicExtension.degree_prime F K).pos
  have ha0 : 0 < a := by
    have hra : r ≤ a := self_le_herbrandPsiNat t p hp0 r
    exact lt_of_lt_of_le (Nat.zero_lt_of_lt hr) hra
  have hsource_eq (n : ℕ) : sourceDepth n + 1 =
      aboveBreakSourceDepth t p (r + n) := by
    have hpsi := herbrandPsiNat_add t p hr.le n
    change (a - 1) + p * n + 1 = aboveBreakSourceDepth t p (r + n)
    rw [show (a - 1) + p * n + 1 = a + p * n by omega]
    exact hpsi.symm
  have hlift := successiveLifting_surjective
    (norm F K) (continuous_norm F K) sourceDepth r
    (by
      intro m n hmn
      exact Nat.add_le_add_left (Nat.mul_le_mul_left p hmn) (a - 1))
    (by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      have hpn : n ≤ p * n := by
        simpa only [one_mul] using Nat.mul_le_mul_right n (show 1 ≤ p by omega)
      exact hn.trans (hpn.trans (Nat.le_add_left _ _)))
    (by
      intro n u hu
      have hrn : t < r + n := hr.trans_le (Nat.le_add_right r n)
      obtain ⟨x, hx, herr⟩ := exists_norm_aboveBreak_oneStep_of_characteristic F K
        ht hrn hres hchar pi hpi hgen u hu
      refine ⟨x, ?_, ?_⟩
      · simpa only [hsource_eq n, p] using hx
      · simpa only [Nat.add_assoc] using herr)
  intro u hu
  obtain ⟨x, hx, hnorm⟩ := hlift u hu
  refine ⟨x, ?_, by simpa only [Units.coe_map] using hnorm⟩
  rw [hsource_eq 0] at hx
  simpa only [Nat.add_zero, p] using hx

/-- Exact elementwise norm image at the first above-break source depth. -/
theorem mem_unitFiltration_iff_exists_norm_aboveBreak_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Fˣ) :
    u ∈ unitFiltration F r ↔
      ∃ x : Kˣ,
        x ∈ unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r) ∧
        normUnits F K x = u := by
  constructor
  · exact norm_unitFiltration_surjective_aboveBreak_of_characteristic F K
      ht hr hres hchar pi hpi hgen u
  · rintro ⟨x, hx, rfl⟩
    exact normMapsUnitFiltration_aboveBreak F K ht hr hres hchar pi hpi hgen x hx

/-- The exact first image formula `N(U_K^Ψ(r)) = U_F^r`. -/
theorem norm_unitFiltration_map_eq_aboveBreak_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Subgroup.map (normUnits F K)
        (unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r)) =
      unitFiltration F r := by
  ext u
  rw [Subgroup.mem_map]
  exact (mem_unitFiltration_iff_exists_norm_aboveBreak_of_characteristic F K
    ht hr hres hchar pi hpi hgen u).symm

/-- Exact elementwise norm image for the distinct successor source depth `Ψ(r)+1`. -/
theorem mem_unitFiltration_succ_iff_exists_norm_aboveBreak_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Fˣ) :
    u ∈ unitFiltration F (r + 1) ↔
      ∃ x : Kˣ,
        x ∈ unitFiltration K
          (aboveBreakSourceDepth t (Module.finrank F K) r + 1) ∧
        normUnits F K x = u := by
  constructor
  · intro hu
    have hrsucc : t < r + 1 := hr.trans (Nat.lt_succ_self r)
    obtain ⟨x, hx, hnorm⟩ :=
      norm_unitFiltration_surjective_aboveBreak_of_characteristic F K ht hrsucc hres
        hchar pi hpi hgen u hu
    refine ⟨x, unitFiltration_antitone K ?_ hx, hnorm⟩
    exact (herbrandPsiNat_add_one_lt_succ t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K) hr.le).le
  · rintro ⟨x, hx, rfl⟩
    exact normMapsUnitFiltration_aboveBreak_succ F K ht hr hres hchar pi hpi hgen x hx

/-- The exact second image formula `N(U_K^(Ψ(r)+1)) = U_F^(r+1)`. -/
theorem norm_unitFiltration_map_eq_aboveBreak_succ_of_characteristic
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (hchar : 0 < t → residueCharacteristic F = Module.finrank F K)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Subgroup.map (normUnits F K)
        (unitFiltration K
          (aboveBreakSourceDepth t (Module.finrank F K) r + 1)) =
      unitFiltration F (r + 1) := by
  ext u
  rw [Subgroup.mem_map]
  exact (mem_unitFiltration_succ_iff_exists_norm_aboveBreak_of_characteristic F K
    ht hr hres hchar pi hpi hgen u).symm

private theorem aboveBreakCharacteristic
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    0 < t → residueCharacteristic F = Module.finrank F K :=
  fun htpos ↦ residueCharacteristic_eq_degree_of_positive_break F K
    ht htpos pi hpi hgen

/-- Canonical higher-coefficient vanishing, with wildness derived when the break is positive. -/
theorem higher_elementarySymmetric_mem_lattice_aboveBreakCanonical
    {t r j : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K)
    (hx : ((aboveBreakSourceDepth t (Module.finrank F K) r : ℕ) : WithTop ℤ) ≤
      ord K x)
    (hjtwo : 2 ≤ j) (hjle : j ≤ Module.finrank F K) :
    elementarySymmetric F K j x ∈ lattice F ((r + 1 : ℕ) : ℤ) :=
  higher_elementarySymmetric_mem_lattice_aboveBreak F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen x hx hjtwo hjle

/-- Canonical norm--trace congruence at the exact next target depth. -/
theorem norm_one_add_sub_one_sub_trace_mem_aboveBreakCanonical
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K)
    (hx : ((aboveBreakSourceDepth t (Module.finrank F K) r : ℕ) : WithTop ℤ) ≤
      ord K x) :
    norm F K (1 + x) - 1 - trace F K x ∈
      lattice F ((r + 1 : ℕ) : ℤ) :=
  norm_one_add_sub_one_sub_trace_mem_aboveBreak F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen x hx

/-- Canonical numerator containment, with the positive-break characteristic equality derived
from the ramification coordinate. -/
theorem normMapsUnitFiltration_aboveBreakCanonical
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    AboveBreakNormMapsUnitFiltration F K
      (aboveBreakSourceDepth t (Module.finrank F K) r) r :=
  normMapsUnitFiltration_aboveBreak F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

/-- Canonical denominator containment at the distinct source depth `Ψ(r)+1`. -/
theorem normMapsUnitFiltration_aboveBreakCanonical_succ
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    AboveBreakNormMapsUnitFiltration F K
      (aboveBreakSourceDepth t (Module.finrank F K) r + 1) (r + 1) :=
  normMapsUnitFiltration_aboveBreak_succ F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

/-- The canonical above-break graded norm, with no extra tame/wild hypothesis. -/
noncomputable def normGradedAboveBreakCanonical
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    UnitGradedPiece K (aboveBreakSourceDepth t (Module.finrank F K) r) →*
      UnitGradedPiece F r :=
  normGradedAboveBreak F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

@[simp]
theorem normGradedAboveBreakCanonical_mk
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r)) :
    normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen
        (unitGradedMk K (aboveBreakSourceDepth t (Module.finrank F K) r) u) =
      unitGradedMk F r
        (aboveBreakNormUnitFiltrationHom F K
          (aboveBreakSourceDepth t (Module.finrank F K) r) r
          (normMapsUnitFiltration_aboveBreakCanonical F K ht hr hres pi hpi hgen) u) :=
  rfl

/-- Canonical representative formula `[1+x] ↦ [1+Tr(x)]`. -/
theorem normGradedAboveBreakCanonical_mk_eq_trace
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (x : K)
    (hx : ((aboveBreakSourceDepth t (Module.finrank F K) r : ℕ) : WithTop ℤ) ≤
      ord K x)
    (u : unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r))
    (hu : ((u : Kˣ) : K) = 1 + x)
    (v : unitFiltration F r)
    (hv : ((v : Fˣ) : F) = 1 + trace F K x) :
    normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen
        (unitGradedMk K (aboveBreakSourceDepth t (Module.finrank F K) r) u) =
      unitGradedMk F r v := by
  exact normGradedAboveBreak_mk_eq_trace F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen x hx u hu v hv

/-- Principal exported theorem: the canonical graded norm is surjective at every natural
upper depth strictly above the lower break. -/
theorem norm_graded_surjective_above_break
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Surjective
      (normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen) :=
  norm_graded_surjective_above_break_of_characteristic F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

set_option synthInstance.maxHeartbeats 100000 in
private theorem aboveBreakResidueCard_eq
    (hres : residueDegree F K = 1) :
    residueCard K = residueCard F := by
  letI := residueFieldFintype F
  letI := residueFieldFintype K
  exact (Fintype.card_congr (Equiv.ofBijective
    (algebraMap (ResidueField F) (ResidueField K))
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
      ((residueDegree_eq_finrank_residueField F K).symm.trans hres)))).symm

/-- The canonical graded norm is bijective, hence is the manuscript's above-break graded
isomorphism. -/
theorem norm_graded_bijective_above_break
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Function.Bijective
      (normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen) := by
  let a := aboveBreakSourceDepth t (Module.finrank F K) r
  have hr0 : 0 < r := Nat.zero_lt_of_lt hr
  have ha0 : 0 < a := by
    have hra : r ≤ a := self_le_herbrandPsiNat t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos r
    exact hr0.trans_le hra
  apply (Nat.bijective_iff_surjective_and_card
    (normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen)).2
  refine ⟨norm_graded_surjective_above_break F K ht hr hres pi hpi hgen, ?_⟩
  rw [positiveUnitFiltrationQuotient_card K ha0 (Nat.le_succ a),
    positiveUnitFiltrationQuotient_card F hr0 (Nat.le_succ r),
    aboveBreakResidueCard_eq F K hres]
  simp

/-- Multiplicative equivalence induced by norm on the strict above-break graded layer. -/
noncomputable def normGradedAboveBreakEquiv
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    UnitGradedPiece K (aboveBreakSourceDepth t (Module.finrank F K) r) ≃*
      UnitGradedPiece F r :=
  MulEquiv.ofBijective (normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen)
    (norm_graded_bijective_above_break F K ht hr hres pi hpi hgen)

@[simp]
theorem normGradedAboveBreakEquiv_apply
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (z : UnitGradedPiece K (aboveBreakSourceDepth t (Module.finrank F K) r)) :
    normGradedAboveBreakEquiv F K ht hr hres pi hpi hgen z =
      normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen z :=
  rfl

/-- The range of the canonical graded norm is the entire target graded piece. -/
theorem normGradedAboveBreakCanonical_range_eq_top
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (normGradedAboveBreakCanonical F K ht hr hres pi hpi hgen).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (norm_graded_surjective_above_break F K ht hr hres pi hpi hgen)

/-- Exact full-layer surjectivity obtained by complete successive lifting. -/
theorem norm_unitFiltration_surjective_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    ∀ u : Fˣ, u ∈ unitFiltration F r →
      ∃ x : Kˣ,
        x ∈ unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r) ∧
        normUnits F K x = u :=
  norm_unitFiltration_surjective_aboveBreak_of_characteristic F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

/-- Elementwise form of the first exact image formula. -/
theorem mem_unitFiltration_iff_exists_norm_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Fˣ) :
    u ∈ unitFiltration F r ↔
      ∃ x : Kˣ,
        x ∈ unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r) ∧
        normUnits F K x = u :=
  mem_unitFiltration_iff_exists_norm_aboveBreak_of_characteristic F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen u

/-- Exact first image formula `N(U_K^Ψ(r)) = U_F^r`. -/
theorem norm_unitFiltration_map_eq_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Subgroup.map (normUnits F K)
        (unitFiltration K (aboveBreakSourceDepth t (Module.finrank F K) r)) =
      unitFiltration F r :=
  norm_unitFiltration_map_eq_aboveBreak_of_characteristic F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

/-- Exact second image formula `N(U_K^(Ψ(r)+1)) = U_F^(r+1)`. -/
theorem norm_unitFiltration_map_eq_aboveBreak_succ
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Subgroup.map (normUnits F K)
        (unitFiltration K
          (aboveBreakSourceDepth t (Module.finrank F K) r + 1)) =
      unitFiltration F (r + 1) :=
  norm_unitFiltration_map_eq_aboveBreak_succ_of_characteristic F K ht hr hres
    (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen

/-- Elementwise form of the successor exact image formula. -/
theorem mem_unitFiltration_succ_iff_exists_norm_aboveBreak
    {t r : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hr : t < r) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (u : Fˣ) :
    u ∈ unitFiltration F (r + 1) ↔
      ∃ x : Kˣ,
        x ∈ unitFiltration K
          (aboveBreakSourceDepth t (Module.finrank F K) r + 1) ∧
        normUnits F K x = u :=
  mem_unitFiltration_succ_iff_exists_norm_aboveBreak_of_characteristic F K
    ht hr hres (aboveBreakCharacteristic F K ht pi hpi hgen) pi hpi hgen u

end AboveBreakContainment

end

end LanglandsFirstMainLemma
