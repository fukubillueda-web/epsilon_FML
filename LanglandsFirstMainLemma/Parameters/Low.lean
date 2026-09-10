import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsFirstMainLemma.Ramification.NormCharacters

/-!
# The low-conductor stationary-parameter table

This file formalizes Proposition `prop:low-parameter-table`.  Throughout the
principal table `2 ≤ m = 2*d + epsilon ≤ T = t+1`.  The downstairs character
is minimal in its complete norm-character orbit.  Stationary parameters are
literal lattice-quotient classes; field representatives occur only as
explicit existential witnesses and are never canonical.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

open Polynomial

set_option maxHeartbeats 2000000

/-! ## Integer powers and Teichmuller representatives -/

/-- The prime-field part of the canonical Teichmuller section. -/
noncomputable def primeTeichmuller
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p) :
    ZMod p →*₀ ringOfIntegers F :=
  (teichmuller F).comp
    (ZMod.castHom (by simpa [residueCharacteristic, hchar])
      (ResidueField F)).toMonoidWithZeroHom

@[simp]
theorem residueMap_primeTeichmuller
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p)
    (j : ZMod p) :
    residueMap F (primeTeichmuller F p hchar j) =
      ZMod.castHom (by simpa [residueCharacteristic, hchar]) (ResidueField F) j := by
  simp [primeTeichmuller]

@[simp]
theorem primeTeichmuller_pow_residueCharacteristic
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p)
    (j : ZMod p) :
    primeTeichmuller F p hchar j ^ p = primeTeichmuller F p hchar j := by
  rw [← map_pow]
  congr 1
  simpa [ZMod.card] using (FiniteField.pow_card j)

set_option backward.isDefEq.respectTransparency false in
private theorem primeTeichmuller_smodEq_natCastPow
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p)
    (j : ZMod p) (n : ℕ) :
    primeTeichmuller F p hchar j ≡
      (j.val : ringOfIntegers F) ^ p ^ n
        [SMOD IsLocalRing.maximalIdeal (ringOfIntegers F) ^ (n + 1)] := by
  subst p
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let x : ResidueField F :=
    ZMod.castHom (dvd_refl (residueCharacteristic F)) (ResidueField F) j
  let e : ResidueField F →* Perfection (ResidueField F) (residueCharacteristic F) :=
    Perfection.liftMonoidHom (residueCharacteristic F)
      (ResidueField F) (ResidueField F) (MonoidHom.id (ResidueField F))
  let tt := Perfection.teichmuller₀ (residueCharacteristic F)
    (IsLocalRing.maximalIdeal (ringOfIntegers F))
  change teichmuller F x ≡ (j.val : ringOfIntegers F) ^
      residueCharacteristic F ^ n
        [SMOD IsLocalRing.maximalIdeal (ringOfIntegers F) ^ (n + 1)]
  unfold teichmuller
  change tt (e x) ≡ (j.val : ringOfIntegers F) ^
      residueCharacteristic F ^ n
        [SMOD IsLocalRing.maximalIdeal (ringOfIntegers F) ^ (n + 1)]
  apply Perfection.teichmuller₀_sModEq
  change residueMap F (j.val : ringOfIntegers F) =
    Perfection.coeff (ResidueField F) (residueCharacteristic F) n (e x)
  have hxpow : x ^ residueCharacteristic F ^ n = x := by
    change (ZMod.castHom (dvd_refl (residueCharacteristic F))
      (ResidueField F) j) ^ residueCharacteristic F ^ n = _
    rw [← map_pow]
    congr 1
    exact ZMod.pow_card_pow j
  have hcoeff : Perfection.coeff (ResidueField F)
      (residueCharacteristic F) n (e x) = x := by
    change (powMulEquiv (ResidueField F)
      (residueCharacteristic F ^ n)).symm x = x
    apply (powMulEquiv (ResidueField F)
      (residueCharacteristic F ^ n)).injective
    rw [MulEquiv.apply_symm_apply, powMulEquiv_apply, hxpow]
  rw [hcoeff]
  dsimp only [x]
  rw [map_natCast, ZMod.natCast_val, ZMod.castHom_apply]

private theorem mem_maximalIdeal_pow_iff_mem_lattice'
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : ℕ) (x : ringOfIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) ^ k ↔
      (x : F) ∈ lattice F (k : ℤ) := by
  obtain ⟨pi, hpi⟩ := exists_ord_eq F 1
  have hpi0 : pi ≠ 0 := (ord_ne_top_iff F).1 (by simp [hpi])
  have hpiint : pi ∈ ringOfIntegers F :=
    (mem_lattice_zero_iff F).1 (by rw [mem_lattice, hpi]; simp)
  let pi0 : ringOfIntegers F := ⟨pi, hpiint⟩
  have hpiu : (ValuativeRel.valuation F).IsUniformizer (pi0 : F) :=
    (ord_eq_one_iff_isUniformizer F pi).1 hpi
  have hmax : IsLocalRing.maximalIdeal (ringOfIntegers F) = Ideal.span {pi0} :=
    hpiu.is_generator
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : (y : F) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 y.property
    have hpimem : (pi0 : F) ^ k ∈ lattice F (k : ℤ) := by
      rw [mem_lattice, ord_pow, hpi]
      simp
    rw [hy]
    simpa [add_comm, mul_comm] using mul_mem_lattice F hy0 hpimem
  · intro hx
    have hpiuz : (ValuativeRel.valuation F).IsUniformizer pi := hpiu
    rw [lattice_eq_uniformizer_zpow_smul F hpiuz (k : ℤ)] at hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    let y0 : ringOfIntegers F := ⟨y, (mem_lattice_zero_iff F).1 hy⟩
    refine ⟨y0, ?_⟩
    apply Subtype.ext
    simpa [pi0, y0, smul_eq_mul, mul_comm] using hxy.symm

private theorem degree_natCast_mem_lattice_halfBreak
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    ((Module.finrank F K : ℕ) : F) ∈
      lattice F ((((t + 1) / 2 : ℕ) : ℤ)) := by
  let p := Module.finrank F K
  let T := t + 1
  have hpprime : p.Prime := PrimeCyclicExtension.degree_prime F K
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have hpord := degree_natCast_ord_bound F K p
    ((((p - 1) * T : ℕ) : ℤ)) hpprime.pos rfl (by
      simpa [p, T] using htrace)
  have hpord' :
      ((((((p - 1) * T) / p : ℕ) : ℤ)) : WithTop ℤ) ≤
        ord F (p : F) := by
    simpa using hpord
  have htwo : 2 * (T / 2) ≤ T := Nat.mul_div_le T 2
  have hrle : T / 2 ≤ T := Nat.div_le_self T 2
  have hp2 : 2 ≤ p := hpprime.two_le
  have hp2eq : p = (p - 2) + 2 := by omega
  have hp1eq : p - 1 = (p - 2) + 1 := by omega
  have hmul : p * (T / 2) ≤ (p - 1) * T := by
    calc
      p * (T / 2) = ((p - 2) + 2) * (T / 2) :=
        congrArg (fun z : ℕ ↦ z * (T / 2)) hp2eq
      _ = 2 * (T / 2) + (p - 2) * (T / 2) := by ring
      _ ≤ T + (p - 2) * T :=
        Nat.add_le_add htwo (Nat.mul_le_mul_left (p - 2) hrle)
      _ = ((p - 2) + 1) * T := by ring
      _ = (p - 1) * T :=
        congrArg (fun z : ℕ ↦ z * T) hp1eq.symm
  have hquot : T / 2 ≤ ((p - 1) * T) / p :=
    (Nat.le_div_iff_mul_le hpprime.pos).2 (by simpa [mul_comm] using hmul)
  change ((((T / 2 : ℕ) : ℤ) : WithTop ℤ)) ≤ ord F (p : F)
  exact (WithTop.coe_le_coe.mpr (by exact_mod_cast hquot)).trans hpord'

theorem primeTeichmuller_sub_natCast_mem_lattice_halfBreak
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (p : ℕ) [Fact p.Prime]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = p)
    (hchar : residueCharacteristic F = p)
    (j : ZMod p) :
    ((primeTeichmuller F p hchar j : ringOfIntegers F) : F) -
        (j.val : F) ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
  let r := (t + 1) / 2
  have hpdeep : (p : F) ∈ lattice F (r : ℤ) := by
    have h := degree_natCast_mem_lattice_halfBreak
      F K ht hres pi hpi hgen
    simpa [r, hdegree] using h
  have happ := primeTeichmuller_smodEq_natCastPow F p hchar j r
  have herrIdeal :
      primeTeichmuller F p hchar j -
          (j.val : ringOfIntegers F) ^ p ^ r ∈
        IsLocalRing.maximalIdeal (ringOfIntegers F) ^ (r + 1) :=
    (SModEq.sub_mem).1 happ
  have herrPlus :
      (((primeTeichmuller F p hchar j -
          (j.val : ringOfIntegers F) ^ p ^ r : ringOfIntegers F) : F)) ∈
        lattice F ((r + 1 : ℕ) : ℤ) :=
    (mem_maximalIdeal_pow_iff_mem_lattice' F (r + 1)
      (primeTeichmuller F p hchar j -
        (j.val : ringOfIntegers F) ^ p ^ r)).1 herrIdeal
  have herr :
      ((primeTeichmuller F p hchar j : ringOfIntegers F) : F) -
          ((j.val : F) ^ p ^ r) ∈ lattice F (r : ℤ) := by
    apply lattice_antitone F (by omega) herrPlus
  have hmod : j.val ^ p ^ r ≡ j.val [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa using (ZMod.pow_card_pow (n := r) j)
  obtain ⟨z, hz⟩ := hmod.dvd
  have hzF := congrArg (fun a : ℤ ↦ (a : F)) hz
  push_cast at hzF
  have hpowEq : (j.val : F) ^ p ^ r - (j.val : F) =
      (p : F) * (-(z : F)) := by
    linear_combination -hzF
  have hzint : (-(z : F)) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (by simp)
  have hpow : (j.val : F) ^ p ^ r - (j.val : F) ∈
      lattice F (r : ℤ) := by
    rw [hpowEq]
    simpa using mul_mem_lattice F hpdeep hzint
  rw [show ((primeTeichmuller F p hchar j : ringOfIntegers F) : F) -
      (j.val : F) =
        (((primeTeichmuller F p hchar j : ringOfIntegers F) : F) -
          (j.val : F) ^ p ^ r) +
        ((j.val : F) ^ p ^ r - (j.val : F)) by ring]
  exact add_mem herr hpow

theorem integerPower_eq_primeTeichmuller_stationary
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (p : ℕ) [Fact p.Prime]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = p)
    (hchar : residueCharacteristic F = p)
    (theta : ContinuousQuasiChar F)
    (htheta : IsMultiplicativeConductor F theta (t + 1))
    (psi : LocalAddCharData F) (A : F)
    (hlin : ∀ y : lattice F ((((t + 2) / 2 : ℕ) : ℤ)),
      theta (positiveUnitOfLattice F (by omega) y) =
        psi.character (A * (y : F)))
    (j : ZMod p)
    (x : lattice F ((((t + 2) / 2 : ℕ) : ℤ))) :
    psi.character ((j.val : F) * A * (x : F)) =
      psi.character
        (((primeTeichmuller F p hchar j : ringOfIntegers F) : F) *
          A * (x : F)) := by
  let T := t + 1
  let r := T / 2
  let s := (T + 1) / 2
  have hdiff :
      ((primeTeichmuller F p hchar j : ringOfIntegers F) : F) -
          (j.val : F) ∈ lattice F (r : ℤ) := by
    simpa [T, r] using
      (primeTeichmuller_sub_natCast_mem_lattice_halfBreak
        F K p ht hres pi hpi hgen hdegree hchar j)
  let z : F :=
    (((primeTeichmuller F p hchar j : ringOfIntegers F) : F) -
      (j.val : F)) * (x : F)
  have hzraw : z ∈ lattice F ((r : ℤ) + (s : ℤ)) := by
    apply mul_mem_lattice F hdiff
    simpa [T, s] using x.property
  have hrs : r + s = T := by
    dsimp only [r, s]
    omega
  have hzT : z ∈ lattice F (T : ℤ) := by
    have hrsZ : (r : ℤ) + (s : ℤ) = (T : ℤ) := by exact_mod_cast hrs
    rw [← hrsZ]
    exact hzraw
  have hspos : 0 < s := by dsimp only [s, T]; omega
  have hTpos : 0 < T := by dsimp only [T]; omega
  have hsleT : s ≤ T := by omega
  let zT : lattice F (T : ℤ) := ⟨z, hzT⟩
  let zS : lattice F (s : ℤ) :=
    ⟨z, lattice_antitone F (by exact_mod_cast hsleT) hzT⟩
  have hunit :
      (positiveUnitOfLattice F hspos zS : Fˣ) =
        positiveUnitOfLattice F hTpos zT := by
    apply Units.ext
    simp [zS, zT]
  have htau : theta (positiveUnitOfLattice F hspos zS) = 1 := by
    rw [hunit]
    exact htheta.trivial _ (positiveUnitOfLattice F hTpos zT).property
  have hphase : psi.character (A * z) = 1 := by
    have hzlin := hlin
      (⟨z, lattice_antitone F (by
        change ((((t + 2) / 2 : ℕ) : ℤ)) ≤ (T : ℤ)
        exact_mod_cast (by dsimp only [T]; omega)) hzT⟩)
    have hzs :
        (⟨z, lattice_antitone F (by
          change ((((t + 2) / 2 : ℕ) : ℤ)) ≤ (T : ℤ)
          exact_mod_cast (by dsimp only [T]; omega)) hzT⟩ :
            lattice F ((((t + 2) / 2 : ℕ) : ℤ))) = zS := by
      apply Subtype.ext
      rfl
    rw [hzs] at hzlin
    exact hzlin.symm.trans htau
  symm
  calc
    psi.character
        (((primeTeichmuller F p hchar j : ringOfIntegers F) : F) *
          A * (x : F)) =
      psi.character ((j.val : F) * A * (x : F) + A * z) := by
        congr 1
        dsimp only [z]
        ring
    _ = psi.character ((j.val : F) * A * (x : F)) *
        psi.character (A * z) := psi.character.map_add_eq_mul _ _
    _ = psi.character ((j.val : F) * A * (x : F)) := by rw [hphase, mul_one]

private theorem teichRootsPolynomial
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R]
    (w : ZMod p → R) (hw : Function.Injective w)
    (hroot : ∀ j, w j ^ p = w j) :
    (∏ j : ZMod p, (X - C (w j))) = (X ^ p - X : R[X]) := by
  classical
  have hpprime : p.Prime := Fact.out
  let s : Multiset R := (Finset.univ.val.map w)
  have hs_nodup : s.Nodup := Finset.univ.nodup.map hw
  have hq0 : (X ^ p - X : R[X]) ≠ 0 := by
    have hp : 1 < p := hpprime.one_lt
    exact (monic_X_pow_sub (by simpa using hp)).ne_zero
  have hs_le : s ≤ (X ^ p - X : R[X]).roots := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ s
    · have hcount : s.count x = 1 :=
        Multiset.count_eq_one_of_mem hs_nodup hx
      rw [hcount]
      apply (Multiset.one_le_count_iff_mem).2
      rw [mem_roots hq0]
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
      simp [hroot]
    · simp [Multiset.count_eq_zero.mpr hx]
  have hdvd : (s.map fun a ↦ X - C a).prod ∣ (X ^ p - X : R[X]) :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hq0 s).2 hs_le
  have hprodMonic : (s.map fun a ↦ X - C a).prod.Monic :=
    monic_multisetProd_X_sub_C s
  have hqMonic : (X ^ p - X : R[X]).Monic := by
    exact monic_X_pow_sub (by simpa using hpprime.one_lt)
  have hdegree : (X ^ p - X : R[X]).natDegree ≤
      (s.map fun a ↦ X - C a).prod.natDegree := by
    have hqdegree : (X ^ p - X : R[X]).natDegree = p := by
      rw [natDegree_sub_eq_left_of_natDegree_lt]
      rw [monic_X.natDegree_pow, natDegree_X, mul_one]
      simpa [monic_X.natDegree_pow] using hpprime.one_lt
    rw [hqdegree, natDegree_multiset_prod_X_sub_C_eq_card]
    simp [s, ZMod.card]
  have heq := eq_of_monic_of_dvd_of_natDegree_le hprodMonic hqMonic hdvd hdegree
  simpa [s] using heq.symm

theorem primeTeichmullerPolynomial_sub
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p) :
    (∏ j : ZMod p, (X - C (primeTeichmuller F p hchar j))) =
      (X ^ p - X : (ringOfIntegers F)[X]) := by
  apply teichRootsPolynomial (primeTeichmuller F p hchar)
  · exact (teichmuller_injective F).comp
      (ZMod.castHom (by simpa [residueCharacteristic, hchar]) (ResidueField F)).injective
  · exact primeTeichmuller_pow_residueCharacteristic F p hchar

theorem primeTeichmullerPolynomial_add
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p) :
    (∏ j : ZMod p, (X + C (primeTeichmuller F p hchar j))) =
      (X ^ p + C ((-1 : ringOfIntegers F) ^ p) * X :
        (ringOfIntegers F)[X]) := by
  classical
  have hsub := primeTeichmullerPolynomial_sub F p hchar
  have hcomp := congrArg
    (fun q : (ringOfIntegers F)[X] ↦ q.comp (-X)) hsub
  rw [prod_comp] at hcomp
  simp only [sub_comp, pow_comp, X_comp, C_comp] at hcomp
  have hpcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hnegprod :
      (∏ j : ZMod p, (-X - C (primeTeichmuller F p hchar j))) =
        C ((-1 : ringOfIntegers F) ^ p) *
          ∏ j : ZMod p, (X + C (primeTeichmuller F p hchar j)) := by
    calc
      (∏ j : ZMod p, (-X - C (primeTeichmuller F p hchar j))) =
          ∏ j : ZMod p,
            (C (-1) * (X + C (primeTeichmuller F p hchar j))) := by
              apply Finset.prod_congr rfl
              intro j _
              rw [show C (-1 : ringOfIntegers F) =
                (-1 : (ringOfIntegers F)[X]) by simp]
              ring
      _ = (∏ _j : ZMod p, C (-1)) *
          ∏ j : ZMod p, (X + C (primeTeichmuller F p hchar j)) := by
            rw [Finset.prod_mul_distrib]
      _ = C ((-1 : ringOfIntegers F) ^ p) *
          ∏ j : ZMod p, (X + C (primeTeichmuller F p hchar j)) := by
            rw [Finset.prod_const,
              show Finset.univ.card = p by simpa using hpcard, ← C_pow]
  have hsign : ((-1 : ringOfIntegers F) ^ p) * ((-1 : ringOfIntegers F) ^ p) = 1 := by
    rw [← pow_add, show p + p = 2 * p by omega, pow_mul]
    simp
  calc
    (∏ j : ZMod p, (X + C (primeTeichmuller F p hchar j))) =
        C ((-1 : ringOfIntegers F) ^ p) *
          ∏ j : ZMod p, (-X - C (primeTeichmuller F p hchar j)) := by
            rw [hnegprod]
            rw [← mul_assoc, ← C_mul, hsign]
            simp
    _ = C ((-1 : ringOfIntegers F) ^ p) * ((-X) ^ p - -X) := by
      rw [hcomp]
    _ = X ^ p + C ((-1 : ringOfIntegers F) ^ p) * X := by
      have hnegpow : (-X : (ringOfIntegers F)[X]) ^ p =
          C ((-1 : ringOfIntegers F) ^ p) * X ^ p := by
        calc
          (-X : (ringOfIntegers F)[X]) ^ p =
              (-1 : (ringOfIntegers F)[X]) ^ p * X ^ p := neg_pow X p
          _ = C (-1 : ringOfIntegers F) ^ p * X ^ p := by simp
          _ = C ((-1 : ringOfIntegers F) ^ p) * X ^ p := by rw [C_pow]
      rw [hnegpow]
      calc
        C ((-1 : ringOfIntegers F) ^ p) *
            (C ((-1 : ringOfIntegers F) ^ p) * X ^ p - -X) =
          (C ((-1 : ringOfIntegers F) ^ p) *
              C ((-1 : ringOfIntegers F) ^ p)) * X ^ p +
            C ((-1 : ringOfIntegers F) ^ p) * X := by ring
        _ = X ^ p + C ((-1 : ringOfIntegers F) ^ p) * X := by
          rw [← C_mul, hsign]
          simp

theorem primeTeichmullerPolynomial_add_field
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p) :
    (∏ j : ZMod p,
      (X + C (((primeTeichmuller F p hchar j : ringOfIntegers F) : F)))) =
      (X ^ p + C ((-1 : F) ^ p) * X : F[X]) := by
  have h := congrArg (Polynomial.map (algebraMap (ringOfIntegers F) F))
    (primeTeichmullerPolynomial_add F p hchar)
  rw [Polynomial.map_prod] at h
  have halg (a : ringOfIntegers F) :
      algebraMap (ringOfIntegers F) F a = (a : F) := rfl
  simpa [halg] using h

theorem prod_primeTeichmuller_add
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p)
    (x : F) :
    (∏ j : ZMod p,
      (x + ((primeTeichmuller F p hchar j : ringOfIntegers F) : F))) =
      x ^ p + (-1 : F) ^ p * x := by
  have h := congrArg (Polynomial.eval x)
    (primeTeichmullerPolynomial_add_field F p hchar)
  simpa [Polynomial.eval_prod] using h

theorem sum_primeTeichmuller
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p) :
    (∑ j : ZMod p, primeTeichmuller F p hchar j) =
      if p = 2 then 1 else 0 := by
  classical
  have hpprime : p.Prime := Fact.out
  have hcoeff :
      ((∏ j : ZMod p, (X - C (primeTeichmuller F p hchar j))) :
          (ringOfIntegers F)[X]).coeff (p - 1) =
        -∑ j : ZMod p, primeTeichmuller F p hchar j := by
    simpa [ZMod.card] using
      (prod_X_sub_C_coeff_card_pred (R := ringOfIntegers F)
        (s := Finset.univ) (primeTeichmuller F p hchar)
        (by simp [ZMod.card, hpprime.pos]))
  rw [primeTeichmullerPolynomial_sub F p hchar] at hcoeff
  by_cases hp2 : p = 2
  · have hneg := congrArg Neg.neg hcoeff
    simp [hp2, coeff_sub, coeff_X_pow, coeff_X] at hneg ⊢
    exact hneg.symm
  · have hpgt : 2 < p := lt_of_le_of_ne hpprime.two_le (Ne.symm hp2)
    have hpred_ne : p - 1 ≠ p := by omega
    have hpred_ne_one : p - 1 ≠ 1 := by omega
    have hrhs : ((X ^ p - X : (ringOfIntegers F)[X]).coeff (p - 1)) = 0 := by
      simp [coeff_sub, coeff_X_pow, coeff_X, hpred_ne, Ne.symm hpred_ne_one]
    rw [hrhs] at hcoeff
    simp [hp2]
    exact neg_eq_zero.mp hcoeff.symm


variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

/-! ## Audited low depths -/

/-- The floor half-depth `r₀ = ⌊(t+1)/2⌋`. -/
def lowCriticalFloorDepth (t : ℕ) : ℕ := (t + 1) / 2

/-- The parity term of the critical conductor. -/
def lowCriticalParity (t : ℕ) : ℕ := (t + 1) % 2

/-- The stationary variable depth `s₀ = ⌈(t+1)/2⌉`. -/
def lowCriticalVariableDepth (t : ℕ) : ℕ :=
  lowCriticalFloorDepth t + lowCriticalParity t

@[simp]
theorem lowCriticalParity_le_one : lowCriticalParity t ≤ 1 := by
  exact Nat.le_of_lt_succ (Nat.mod_lt (t + 1) (by omega : 0 < 2))

theorem lowCriticalConductor_eq :
    t + 1 = 2 * lowCriticalFloorDepth t + lowCriticalParity t := by
  rw [lowCriticalFloorDepth, lowCriticalParity]
  omega

theorem lowCriticalVariableDepth_eq_ceilDiv :
    lowCriticalVariableDepth t = (t + 1) ⌈/⌉ 2 := by
  rw [lowCriticalVariableDepth, lowCriticalFloorDepth, lowCriticalParity,
    Nat.ceilDiv_eq_add_pred_div]
  omega

/-- Exact stationary decomposition of `T=t+1`. -/
theorem lowCriticalConductorDecomposition
    (hT : 2 ≤ t + 1) :
    IsStationaryConductorDecomposition (t + 1)
      (lowCriticalFloorDepth t) (lowCriticalParity t) where
  conductor_gt_one := hT
  epsilon_le_one := lowCriticalParity_le_one (t := t)
  conductor_eq := lowCriticalConductor_eq (t := t)

/-- Both exact-norm precisions in the low table are subcritical. -/
theorem lowConductor_subcriticalDepths
    {m d epsilon : ℕ}
    (hm : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1) :
    lowCriticalFloorDepth t ≤ t ∧ d ≤ t := by
  have hmgt := hm.conductor_gt_one
  have htpos : 0 < t := by omega
  constructor
  · rw [lowCriticalFloorDepth]
    omega
  · rw [hm.conductor_eq] at hLow
    omega

/-- The minimal stationary depth of `chi` is no deeper than `s₀`. -/
theorem lowConductor_variableDepth_le_critical
    {m d epsilon : ℕ}
    (hm : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1) :
    d + epsilon ≤ lowCriticalVariableDepth t := by
  have hT := lowCriticalConductor_eq (t := t)
  have hepsilon := hm.epsilon_le_one
  have hparity := lowCriticalParity_le_one (t := t)
  rw [lowCriticalVariableDepth]
  rw [hm.conductor_eq] at hLow
  omega

/-! ## Actual conductors in the complete low orbit -/

include ht hres pi hpi hgen

/-- Piecewise conductor index for a low norm-character twist. -/
noncomputable def lowTwistConductor
    (chi : LocalQuasiCharData F) (mu : NormCharacter F K) : ℕ := by
  classical
  exact if mu = 1 then chi.conductor else t + 1

/-- The identity twist retains `m`; every nonidentity twist has actual
conductor `T=t+1`. -/
theorem lowTwist_conductor_eq
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hLow : chi.conductor ≤ t + 1)
    (mu : NormCharacter F K) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chi mu).conductor =
      lowTwistConductor (t := t) F K chi mu := by
  classical
  rw [ramifiedNormCharacterOrbitTwistData_conductor_eq_ite
    F K ht hres pi hpi hgen chi hminimal mu,
    minimalOrbitTwistConductor, lowTwistConductor]
  split_ifs
  · rfl
  · rw [Nat.max_eq_right hLow]

/-- Piecewise conductor index for the cyclic enumeration. -/
noncomputable def lowZModTwistConductor
    (chi : LocalQuasiCharData F)
    (j : Multiplicative (ZMod (Module.finrank F K))) : ℕ := by
  classical
  exact if j = 1 then chi.conductor else t + 1

/-- Cyclic-indexed form of the complete lower twist-conductor table. -/
theorem lowZModTwist_conductor_eq
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hLow : chi.conductor ≤ t + 1)
    (j : Multiplicative (ZMod (Module.finrank F K))) :
    (ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chi
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen j)).conductor =
      lowZModTwistConductor (t := t) F K chi j := by
  classical
  rw [lowTwist_conductor_eq F K ht hres pi hpi hgen chi hminimal hLow]
  simp only [lowZModTwistConductor, lowTwistConductor]
  by_cases hj : j = 1
  · subst j
    simp
  · rw [if_neg hj, if_neg]
    exact (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen j).2 hj

/-- In the low range, norm pullback preserves the actual conductor. -/
theorem lowCompNorm_conductor_eq
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hLow : chiF.conductor ≤ t + 1) :
    chiK.conductor = chiF.conductor :=
  minimalOrbit_compNorm_conductor_eq_of_leCritical
    F K ht hres pi hpi hgen chiF hminimal chiK hchi hLow

/-! ## Exact low stationary norm precision and denominators -/

/-- The three same-numbered norm containments at the actual low conductor,
stationary-variable depth, and coefficient-ambiguity depth. -/
theorem lowNormPolynomialPrecision
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1) :
    NormPolynomialPrecision F K chiK.conductor d epsilon
      chiF.conductor d epsilon := by
  have htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    omega
  have hmK := lowCompNorm_conductor_eq F K ht hres pi hpi hgen
    chiF hminimal chiK hchi hLow
  have hvar : d + epsilon ≤ t + 1 :=
    hF.variableDepth_le_conductor.trans hLow
  have hd : d ≤ t + 1 := by omega
  refine
    { sourceDecomposition := ?_
      targetDecomposition := hF
      variable_inclusion := ?_
      conductor_inclusion := ?_
      ambiguity_inclusion := ?_ }
  · rw [hmK]
    exact hF
  · exact wild_normMapsUnitFiltration F K ht htpos hvar
      hres pi hpi hgen
  · rw [hmK]
    exact wild_normMapsUnitFiltration F K ht htpos hLow
      hres pi hpi hgen
  · exact wild_normMapsUnitFiltration F K ht htpos hd
      hres pi hpi hgen

omit ht hres pi hpi hgen in
/-- In the low range the stationary floor depth is positive and the
conductor-`m` coefficient depth fits in the critical coefficient depth. -/
theorem lowConductor_floorDepth_bounds
    {m d epsilon : ℕ}
    (hm : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1) :
    1 ≤ d ∧ d ≤ lowCriticalFloorDepth t := by
  have hmgt := hm.conductor_gt_one
  have he := hm.epsilon_le_one
  have hT := lowCriticalConductor_eq (t := t)
  have hparity := lowCriticalParity_le_one (t := t)
  rw [hm.conductor_eq] at hmgt hLow
  rw [hT] at hLow
  omega

omit ht hres pi hpi hgen in
/-- With `v=T-m`, multiplying the conductor-`m` coefficient by an element
of order `v` makes its class well defined on the common critical quotient. -/
theorem lowConductor_commonLayer_bound
    {m d epsilon : ℕ}
    (hm : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1) :
    lowCriticalFloorDepth t ≤ (t + 1 - m) + d := by
  have he := hm.epsilon_le_one
  have hT := lowCriticalConductor_eq (t := t)
  have hparity := lowCriticalParity_le_one (t := t)
  rw [hm.conductor_eq] at hLow ⊢
  omega

omit ht hres pi hpi hgen

/-! ## Critical cancellation, genuine drops, and endpoints -/

include ht hres pi hpi hgen

/-- At the critical endpoint, whole-orbit minimality rules out cancellation
in the final quotient layer. -/
theorem lowCriticalMinimalTwist_noncancellation
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryLeadingClassProjection F M hr
      (stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psi M hr Gamma hGamma +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chi.character (t + 1) (by
            simpa only [hcritical] using chi.isConductor))
          psi M hr Gamma hGamma) ≠ 0 :=
  minimalOrbit_stationary F K ht hres pi hpi hgen
    chi hminimal hcritical mu hmu psi M hr Gamma hGamma

/-- The exhaustive critical cancellation interface.  At the retained
critical conductor the leading quotient class is nonzero.  A genuine
non-endpoint drop constructs the new stationary class at its actual
conductor and minimal half-depth before restricting it to the old critical
layer.  At conductor zero or one there is no stationary object. -/
theorem lowCriticalCancellation_classification
    (chi : LocalQuasiCharData F) (hcritical : chi.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (prod : LocalQuasiCharData F)
    (hprod : prod.character = mu.1 * chi.character)
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    (prod.conductor = t + 1 ∧
      stationaryLeadingClassProjection F M hr
        (stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F mu.1 (t + 1)
              (ramifiedNormCharacter_conductor
                F K ht hres pi hpi hgen mu hmu))
            psi M hr Gamma hGamma +
          stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F chi.character (t + 1) (by
              simpa only [hcritical] using chi.isConductor))
            psi M hr Gamma hGamma) ≠ 0) ∨
    (∃ (hdrop : prod.conductor < t + 1)
        (hgt : 1 < prod.conductor),
      droppedStationaryClassRestriction F
          (quasiCharDataOfIsConductor F (mu.1 * chi.character)
            prod.conductor (by
              rw [← hprod]
              exact prod.isConductor))
          psi M hr hdrop hgt Gamma hGamma =
        stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F mu.1 (t + 1)
              (ramifiedNormCharacter_conductor
                F K ht hres pi hpi hgen mu hmu))
            psi M hr Gamma hGamma +
          stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F chi.character (t + 1) (by
              simpa only [hcritical] using chi.isConductor))
            psi M hr Gamma hGamma) ∨
    (prod.conductor ≤ 1 ∧
      ¬ ∃ r' : ℕ, IsLamprechtStationaryDepth prod.conductor r') := by
  have hmuConductor : IsMultiplicativeConductor F mu.1 (t + 1) :=
    ramifiedNormCharacter_conductor
      F K ht hres pi hpi hgen mu hmu
  have hchiConductor :
      IsMultiplicativeConductor F chi.character (t + 1) := by
    simpa only [hcritical] using chi.isConductor
  have hprodConductor : IsMultiplicativeConductor F
      (mu.1 * chi.character) prod.conductor := by
    rw [← hprod]
    exact prod.isConductor
  rcases criticalNormCharacterTwist_conductor_eq_or_drop
      F K ht hres pi hpi hgen chi hcritical mu hmu prod hprod with
    hsame | hdrop
  · left
    refine ⟨hsame, ?_⟩
    intro hzero
    have hstrict :=
      (stationaryLeadingClassCancellation_iff F (t + 1) prod.conductor
        hmuConductor hchiConductor hprodConductor psi M hr Gamma hGamma).2
        hzero
    omega
  · by_cases hgt : 1 < prod.conductor
    · right
      left
      refine ⟨hdrop, hgt, ?_⟩
      exact criticalNormCharacterTwist_stationaryClass_afterDrop
        F K ht hres pi hpi hgen chi hcritical mu hmu prod.conductor
          hprodConductor hdrop hgt psi M hr Gamma hGamma
    · right
      right
      have hend : prod.conductor ≤ 1 := by omega
      exact ⟨hend,
        normCharacterTwist_noStationaryClass_of_endpoint
          F K ht hres pi hpi hgen prod hend⟩

/-- The original conductor-zero and conductor-one endpoint rows carry no
native stationary numerator class. -/
theorem lowEndpoint_noStationaryClass
    (chi : LocalQuasiCharData F) (hend : chi.conductor ≤ 1) :
    ¬ ∃ r : ℕ, IsLamprechtStationaryDepth chi.conductor r :=
  noStationaryClass_of_conductor_le_one hend

omit ht hres pi hpi hgen

/-- The exact norm `epsilon=N(epsilon₁)`. -/
def lowEpsilon (epsilon₁ : Kˣ) : Fˣ := normUnits F K epsilon₁

/-- The downstairs denominator `gamma_F=delta/epsilon`. -/
def lowGammaF (delta : Fˣ) (epsilon₁ : Kˣ) : Fˣ :=
  delta / lowEpsilon F K epsilon₁

/-- The upstairs denominator `gamma_K=delta/epsilon₁`. -/
def lowGammaK (delta : Fˣ) (epsilon₁ : Kˣ) : Kˣ :=
  Units.map (algebraMap F K) delta / epsilon₁

@[simp]
theorem lowEpsilon_coe (epsilon₁ : Kˣ) :
    (lowEpsilon F K epsilon₁ : F) = norm F K (epsilon₁ : K) := rfl

include hres
/-- Total ramification makes `epsilon` have the same order as `epsilon₁`. -/
theorem lowEpsilon_order {v : ℤ} (epsilon₁ : Kˣ)
    (hepsilon₁ : ord K (epsilon₁ : K) = (v : WithTop ℤ)) :
    ord F (lowEpsilon F K epsilon₁ : F) = (v : WithTop ℤ) := by
  rw [lowEpsilon_coe, ord_norm, hres, one_nsmul]
  exact hepsilon₁
omit hres

include hres
/-- `gamma_F` has the exact denominator order for `chi_F`. -/
theorem lowGammaF_order
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (delta : Fˣ) (epsilon₁ : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hLow : chiF.conductor ≤ t + 1) :
    ord F (lowGammaF F K delta epsilon₁ : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) := by
  rw [lowGammaF, Units.val_div_eq_div_val, ord_div, hdelta,
    lowEpsilon_order F K hres epsilon₁ hepsilon₁]
  norm_cast
  omega
omit hres

include ht hres pi hpi hgen
/-- `gamma_K` is admissible at the actual preserved upstairs conductor. -/
theorem lowGammaK_order
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (delta : Fˣ) (epsilon₁ : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hLow : chiF.conductor ≤ t + 1) :
    ord K (lowGammaK F K delta epsilon₁ : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  have hmK := lowCompNorm_conductor_eq F K ht hres pi hpi hgen
    chiF hminimal chiK hchi hLow
  have hnK := psiF.conductor_compTrace_eq_cyclicPrime
    F K ht hres pi hpi hgen psiK hpsi
  have hpone : 1 ≤ Module.finrank F K := Module.finrank_pos
  simp only [lowGammaK, Units.val_div_eq_div_val, Units.coe_map,
    MonoidHom.coe_coe]
  rw [ord_div, ord_algebraMap, hram, hdelta, hepsilon₁, hmK, hnK]
  norm_cast
  push_cast [Nat.cast_sub hLow, Nat.cast_sub hpone]
  ring
omit ht hres pi hpi hgen

/-! ## Simultaneous exact norm representatives -/

/-- A pair of independently selected exact norms representing two supplied
stationary coefficient classes.  The structure records only quotient-level
validity at the requested precisions; it does not make either source element
canonical. -/
structure LowStationaryNormRepresentativePair
    (r d : ℕ)
    (alphaClass : StationaryCoefficientQuotient F r)
    (betaClass : StationaryCoefficientQuotient F d) where
  alphaTarget : Fˣ
  betaTarget : Fˣ
  alpha₁ : Kˣ
  beta₁ : Kˣ
  alphaRepresentative :
    IsSubcriticalNormRepresentative F K 0 r
      alphaTarget alpha₁
  betaRepresentative :
    IsSubcriticalNormRepresentative F K 0 d
      betaTarget beta₁
  alpha_class :
    latticeQuotientMk F (by omega)
        (⟨(alphaTarget : F),
          alphaRepresentative.coefficient_exactDepth.1⟩ : lattice F 0) =
      alphaClass
  beta_class :
    latticeQuotientMk F (by omega)
        (⟨(betaTarget : F),
          betaRepresentative.coefficient_exactDepth.1⟩ : lattice F 0) =
      betaClass

namespace LowStationaryNormRepresentativePair

variable {F K}

/-- The exact norm attached to the independently chosen `alpha₁`. -/
def alpha {r d : ℕ} {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (P : LowStationaryNormRepresentativePair F K r d alphaClass betaClass) : Fˣ :=
  normUnits F K P.alpha₁

/-- The exact norm attached to the independently chosen `beta₁`. -/
def beta {r d : ℕ} {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (P : LowStationaryNormRepresentativePair F K r d alphaClass betaClass) : Fˣ :=
  normUnits F K P.beta₁

/-- The exact norm `alpha=N(alpha₁)` represents precisely the requested
quotient class, and only at the requested precision. -/
theorem alpha_norm_class {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (P : LowStationaryNormRepresentativePair F K r d alphaClass betaClass) :
    latticeQuotientMk F (by omega)
        (⟨((P.alpha : Fˣ) : F),
          P.alphaRepresentative.norm_exactDepth.1⟩ : lattice F 0) =
      alphaClass := by
  have hnorm :
      latticeQuotientMk F (show (0 : ℤ) ≤ (r : ℤ) by omega)
          (⟨((P.alpha : Fˣ) : F),
            P.alphaRepresentative.norm_exactDepth.1⟩ : lattice F 0) =
        latticeQuotientMk F (show (0 : ℤ) ≤ (r : ℤ) by omega)
          (⟨(P.alphaTarget : F),
            P.alphaRepresentative.coefficient_exactDepth.1⟩ : lattice F 0) := by
    apply (latticeQuotientMk_eq_mk_iff F (by omega)).2
    simpa [alpha] using
      neg_mem_lattice F P.alphaRepresentative.norm_congruent
  exact hnorm.trans P.alpha_class

/-- The exact norm `beta=N(beta₁)` represents precisely the requested
quotient class, and only at the requested precision. -/
theorem beta_norm_class {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (P : LowStationaryNormRepresentativePair F K r d alphaClass betaClass) :
    latticeQuotientMk F (by omega)
        (⟨((P.beta : Fˣ) : F),
          P.betaRepresentative.norm_exactDepth.1⟩ : lattice F 0) =
      betaClass := by
  have hnorm :
      latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
          (⟨((P.beta : Fˣ) : F),
            P.betaRepresentative.norm_exactDepth.1⟩ : lattice F 0) =
        latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
          (⟨(P.betaTarget : F),
            P.betaRepresentative.coefficient_exactDepth.1⟩ : lattice F 0) := by
    apply (latticeQuotientMk_eq_mk_iff F (by omega)).2
    simpa [beta] using
      neg_mem_lattice F P.betaRepresentative.norm_congruent
  exact hnorm.trans P.beta_class

end LowStationaryNormRepresentativePair

/-- Every representative of a literal stationary coefficient class has
exact order zero. -/
theorem stationaryCoefficientClass_representative_ord_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice E 0)
    (hc : latticeQuotientMk E (by omega) c =
      stationaryCoefficientClass E chi psi h gamma hgamma) :
    ord E (c : E) = (0 : WithTop ℤ) := by
  have hcLamp :=
    congrArg (stationaryCoefficientLamprechtEquivAtConductor E h) hc
  rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
    stationaryCoefficientClass_toLamprecht] at hcLamp
  have hord := stationaryNumeratorClass_representative_ord E chi psi
    (chi.conductor : ℤ) (stationaryDepthOfConductorDecomposition E chi h)
    gamma hgamma
    (⟨(c : E), by simpa using c.property⟩ :
      lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ))) hcLamp
  simpa using hord

include ht hres pi hpi hgen
/-- The norm-character class at precision `r₀` and the `chi_F` class at
precision `d` permit independent, simultaneous exact norm representatives. -/
theorem lowSimultaneousStationaryNormRepresentatives
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1)
    (delta gammaF : Fˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
      (ramifiedNormCharacter_conductor
        F K ht hres pi hpi hgen tau htau)
    let hT : 2 ≤ t + 1 := by
      have hm := hF.conductor_gt_one
      omega
    Nonempty (LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d
      (stationaryCoefficientClass F tauData psiF
        (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
      (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)) := by
  dsimp only
  let tauData : LocalQuasiCharData F :=
    quasiCharDataOfIsConductor F tau.1 (t + 1)
      (ramifiedNormCharacter_conductor
        F K ht hres pi hpi hgen tau htau)
  have hT : 2 ≤ t + 1 := by
    have hm := hF.conductor_gt_one
    omega
  let hTdec := lowCriticalConductorDecomposition (t := t) hT
  obtain ⟨a, ha⟩ := latticeQuotientMk_surjective F (by omega)
    (stationaryCoefficientClass F tauData psiF hTdec delta hdelta)
  obtain ⟨b, hb⟩ := latticeQuotientMk_surjective F (by omega)
    (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
  have haord : ord F (a : F) = (0 : WithTop ℤ) :=
    stationaryCoefficientClass_representative_ord_zero F K F tauData psiF
      hTdec delta hdelta a ha
  have hbord : ord F (b : F) = (0 : WithTop ℤ) :=
    stationaryCoefficientClass_representative_ord_zero F K F chiF psiF
      hF gammaF hgammaF b hb
  have ha0 : (a : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [haord]; exact WithTop.coe_ne_top)
  have hb0 : (b : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hbord]; exact WithTop.coe_ne_top)
  let aUnit : Fˣ := Units.mk0 (a : F) ha0
  let bUnit : Fˣ := Units.mk0 (b : F) hb0
  have haUnit : ord F (aUnit : F) = (0 : WithTop ℤ) := by
    simpa [aUnit] using haord
  have hbUnit : ord F (bUnit : F) = (0 : WithTop ℤ) := by
    simpa [bUnit] using hbord
  let depth : Bool → ℕ := fun i ↦
    if i then d else lowCriticalFloorDepth t
  let coeff : Bool → Fˣ := fun i ↦ if i then bUnit else aUnit
  have hdepth : ∀ i, depth i ≤ t := by
    intro i
    rcases lowConductor_subcriticalDepths (t := t) hF hLow with ⟨hr, hd⟩
    cases i <;> simp [depth, hr, hd]
  have hcoeff : ∀ i, ord F (coeff i : F) = (0 : WithTop ℤ) := by
    intro i
    cases i <;> simp [coeff, haUnit, hbUnit]
  obtain ⟨c₁, hc₁⟩ := normRepresentatives_subcritical_finite
    F K ht hres pi hpi hgen (fun _ : Bool ↦ (0 : ℤ)) depth hdepth
      coeff hcoeff
  let alpha₁ := c₁ false
  let beta₁ := c₁ true
  have halphaRaw : IsSubcriticalNormRepresentative F K 0
      (lowCriticalFloorDepth t) aUnit alpha₁ := by
    simpa [alpha₁, depth, coeff] using hc₁ false
  have hbetaRaw : IsSubcriticalNormRepresentative F K 0 d bUnit beta₁ := by
    simpa [beta₁, depth, coeff] using hc₁ true
  refine ⟨{
    alphaTarget := aUnit
    betaTarget := bUnit
    alpha₁ := alpha₁
    beta₁ := beta₁
    alphaRepresentative := halphaRaw
    betaRepresentative := hbetaRaw
    alpha_class := ?_
    beta_class := ?_ }⟩
  · simpa [aUnit] using ha
  · simpa [bUnit] using hb
omit ht hres pi hpi hgen

/-- The complete and deliberately limited independence statement for two
simultaneous choices.  It records equality only in the two permitted target
quotients and membership of the two source ratios in their permitted unit
filtrations. -/
structure LowStationaryNormRepresentativePairIndependence
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (P Q : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : Prop where
  alphaTarget_congruent :
    CongruentAtDepth (r : ℤ) (P.alphaTarget : F) (Q.alphaTarget : F)
  betaTarget_congruent :
    CongruentAtDepth (d : ℤ) (P.betaTarget : F) (Q.betaTarget : F)
  alphaNorm_congruent :
    CongruentAtDepth (r : ℤ) (P.alpha : F) (Q.alpha : F)
  betaNorm_congruent :
    CongruentAtDepth (d : ℤ) (P.beta : F) (Q.beta : F)
  alphaSource_ratio : P.alpha₁ / Q.alpha₁ ∈ unitFiltration K r
  betaSource_ratio : P.beta₁ / Q.beta₁ ∈ unitFiltration K d

include ht hres pi hpi hgen
/-- Independent simultaneous existential choices are unique only in the two
quotients supplied by the manuscript.  In particular this theorem contains
no equality between source representatives. -/
theorem lowStationaryNormRepresentativePairs_independent
    {r d : ℕ} (hr : r ≤ t) (hd : d ≤ t)
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (P Q : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    LowStationaryNormRepresentativePairIndependence F K P Q := by
  have halphaTarget : CongruentAtDepth (r : ℤ)
      (P.alphaTarget : F) (Q.alphaTarget : F) := by
    have hclass := P.alpha_class.trans Q.alpha_class.symm
    have hmem := (latticeQuotientMk_eq_mk_iff F
      (show (0 : ℤ) ≤ (r : ℤ) by omega)).1 hclass
    exact hmem
  have hbetaTarget : CongruentAtDepth (d : ℤ)
      (P.betaTarget : F) (Q.betaTarget : F) := by
    have hclass := P.beta_class.trans Q.beta_class.symm
    have hmem := (latticeQuotientMk_eq_mk_iff F
      (show (0 : ℤ) ≤ (d : ℤ) by omega)).1 hclass
    exact hmem
  have halphaTarget' : (P.alphaTarget : F) - (Q.alphaTarget : F) ∈
      lattice F ((0 : ℤ) + (r : ℤ)) := by
    rw [mem_lattice]
    have halphaIneq := halphaTarget
    rw [CongruentAtDepth] at halphaIneq
    simpa only [zero_add] using halphaIneq
  have hbetaTarget' : (P.betaTarget : F) - (Q.betaTarget : F) ∈
      lattice F ((0 : ℤ) + (d : ℤ)) := by
    rw [mem_lattice]
    have hbetaIneq := hbetaTarget
    rw [CongruentAtDepth] at hbetaIneq
    simpa only [zero_add] using hbetaIneq
  have halphaNorm : CongruentAtDepth (r : ℤ)
      (P.alpha : F) (Q.alpha : F) := by
    change (((r : ℕ) : ℤ) : WithTop ℤ) ≤
      ord F ((P.alpha : F) - (Q.alpha : F))
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_congruent_of_coefficient_congruent
        Q.alphaRepresentative halphaTarget'
  have hbetaNorm : CongruentAtDepth (d : ℤ)
      (P.beta : F) (Q.beta : F) := by
    change (((d : ℕ) : ℤ) : WithTop ℤ) ≤
      ord F ((P.beta : F) - (Q.beta : F))
    simpa [LowStationaryNormRepresentativePair.beta, coe_normUnits] using
      P.betaRepresentative.norm_congruent_of_coefficient_congruent
        Q.betaRepresentative hbetaTarget'
  exact
    { alphaTarget_congruent := halphaTarget
      betaTarget_congruent := hbetaTarget
      alphaNorm_congruent := halphaNorm
      betaNorm_congruent := hbetaNorm
      alphaSource_ratio := subcriticalNormRepresentatives_source_ratio_mem
        F K ht hres pi hpi hgen hr (by simpa using halphaTarget)
          P.alphaRepresentative Q.alphaRepresentative
      betaSource_ratio := subcriticalNormRepresentatives_source_ratio_mem
        F K ht hres pi hpi hgen hd (by simpa using hbetaTarget)
          P.betaRepresentative Q.betaRepresentative }
omit ht hres pi hpi hgen

/-! ## The cyclic generator and the heterogeneous common twist layer -/

include ht hres pi hpi hgen

/-- The generator corresponding to `1 ∈ Z/[K:F]Z` in the fixed complete
ramified norm-character enumeration. -/
noncomputable def lowNormCharacterGenerator : NormCharacter F K :=
  ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))

/-- The complete cyclic enumeration really is the power enumeration of the
fixed generator. -/
theorem lowNormCharacterGenerator_pow
    (j : ZMod (Module.finrank F K)) :
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd j) =
      lowNormCharacterGenerator F K ht hres pi hpi hgen ^ j.val := by
  letI : NeZero (Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩
  rw [lowNormCharacterGenerator, ← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  change j = j.val • (1 : ZMod (Module.finrank F K))
  simpa using (ZMod.natCast_zmod_val j).symm

/-- The fixed generator is nonidentity. -/
theorem lowNormCharacterGenerator_ne_one :
    lowNormCharacterGenerator F K ht hres pi hpi hgen ≠ 1 := by
  letI : NeZero (Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩
  letI : Fact (1 < Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).one_lt⟩
  rw [lowNormCharacterGenerator,
    ramifiedNormCharacterZModEquiv_ne_one_iff]
  intro h
  have h' := congrArg Multiplicative.toAdd h
  have h10 : (1 : ZMod (Module.finrank F K)) = 0 := by simpa using h'
  have hv := congrArg ZMod.val h10
  rw [ZMod.val_one, ZMod.val_zero] at hv
  exact Nat.one_ne_zero hv

omit ht hres pi hpi hgen

/-- Multiplication by the exact norm `eta` transports a supplied native
coefficient representative to the common-denominator numerator shell. -/
def lowIdentityCommonRepresentative
    {m d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1)
    (eta : Fˣ)
    (heta : ord F (eta : F) =
      (((t + 1 - m : ℕ) : ℤ) : WithTop ℤ))
    (c : lattice F 0) : lattice F 0 :=
  ⟨(eta : F) * (c : F), by
    rw [mem_lattice, ord_mul, heta]
    have hc := c.property
    rw [mem_lattice] at hc
    exact add_nonneg (by simp) hc⟩

/-- The identity twist has native conductor `m`, so its class relative to
`gamma_F` is transported to the critical common layer by the quotient map
`[beta] ↦ [eta*beta]`.  This does not manufacture a conductor-`T`
stationary class for the identity twist. -/
noncomputable def lowIdentityCommonClass
    {m d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1)
    (eta : Fˣ)
    (heta : ord F (eta : F) =
      (((t + 1 - m : ℕ) : ℤ) : WithTop ℤ)) :
    StationaryCoefficientQuotient F d →
      StationaryCoefficientQuotient F (lowCriticalFloorDepth t) :=
  latticeQuotientLift F (show (0 : ℤ) ≤ (d : ℤ) by omega)
    (fun c ↦ latticeQuotientMk F
      (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
      (lowIdentityCommonRepresentative (t := t) F hF hLow eta heta c))
    (by
      intro c c' hcc'
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F (by omega)).2
      rw [CongruentAtDepth]
      change (((lowCriticalFloorDepth t : ℕ) : ℤ) : WithTop ℤ) ≤
        ord F ((eta : F) * (c : F) - (eta : F) * (c' : F))
      rw [← mul_sub, ord_mul, heta]
      rw [CongruentAtDepth] at hcc'
      have hbound := lowConductor_commonLayer_bound (t := t) hF hLow
      calc
        (((lowCriticalFloorDepth t : ℕ) : ℤ) : WithTop ℤ) ≤
            ((((t + 1 - m) + d : ℕ) : ℤ) : WithTop ℤ) := by
          exact_mod_cast hbound
        _ = ((((t + 1 - m : ℕ) : ℤ) : WithTop ℤ) +
            (((d : ℕ) : ℤ) : WithTop ℤ)) := by norm_num
        _ ≤ ((((t + 1 - m : ℕ) : ℤ) : WithTop ℤ) +
            ord F ((c : F) - (c' : F))) := by
          simpa [add_comm] using
            add_le_add_right hcc'
              ((((t + 1 - m : ℕ) : ℤ) : WithTop ℤ)))

@[simp]
theorem lowIdentityCommonClass_mk
    {m d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hLow : m ≤ t + 1)
    (eta : Fˣ)
    (heta : ord F (eta : F) =
      (((t + 1 - m : ℕ) : ℤ) : WithTop ℤ))
    (c : lattice F 0) :
    lowIdentityCommonClass (F := F) (K := K) (t := t) hF hLow eta heta
        (latticeQuotientMk F
          (show (0 : ℤ) ≤ (d : ℤ) by exact_mod_cast Nat.zero_le d) c) =
      latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by
          exact_mod_cast Nat.zero_le (lowCriticalFloorDepth t))
        (lowIdentityCommonRepresentative (t := t) F
          hF hLow eta heta c) := rfl

/-! ## Upstairs low stationary class -/

private theorem lowAddChar_eq_of_sub_mem_conductor
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (psi : LocalAddCharData E) {a b : E}
    (hab : a - b ∈ lattice E (-psi.conductor)) :
    psi.character a = psi.character b := by
  apply Units.ext
  apply (div_eq_one_iff_eq (Units.ne_zero (psi.character b))).1
  have hdiv : psi.character a / psi.character b = 1 := by
    calc
      psi.character a / psi.character b =
          psi.character.toAddChar (a - b) :=
        (psi.character.toAddChar.map_sub_eq_div a b).symm
      _ = 1 := psi.isConductor.trivial (a - b) hab
  simpa using congrArg Units.val hdiv

private theorem lowScaledError_mem_conductor
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (psi : LocalAddCharData E) {T : ℕ}
    (delta a z : E)
    (hdelta : ord E delta =
      ((((T : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (ha : ord E a = 0)
    (hz : z ∈ lattice E (T : ℤ)) :
    a * z / delta ∈ lattice E (-psi.conductor) := by
  apply (div_mem_lattice_iff E delta (a * z)
    ((T : ℤ) + psi.conductor) (-psi.conductor) hdelta).2
  rw [show (T : ℤ) + psi.conductor + -psi.conductor = (T : ℤ) by ring]
  rw [mem_lattice, ord_mul, ha, zero_add]
  exact hz

set_option maxHeartbeats 2000000 in
theorem lowUpstairsStationaryClass
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1)
    (hprecision : NormPolynomialPrecision F K chiK.conductor d epsilon
      chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (epsilon₁ alpha₁ beta₁ : Kˣ)
    (deltaF : Fˣ)
    (hdelta : ord F (deltaF : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ))
    (halpha₁ : ord K (alpha₁ : K) = (0 : WithTop ℤ))
    (hbeta₁ : ord K (beta₁ : K) = (0 : WithTop ℤ))
    (hgammaF : ord F (lowGammaF F K deltaF epsilon₁ : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (lowGammaK F K deltaF epsilon₁ : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (halphaClass :
      latticeQuotientMk F (by omega)
          (⟨(normUnits F K alpha₁ : F), by
            rw [mem_lattice, coe_normUnits, ord_norm, hres, one_nsmul, halpha₁]
            simp⟩ : lattice F 0) =
        stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen tau htau))
          psiF (lowCriticalConductorDecomposition (t := t) (by
            have hm := hF.conductor_gt_one
            omega)) deltaF hdelta)
    (hbetaClass :
      latticeQuotientMk F (by omega)
          (⟨(normUnits F K beta₁ : F), by
            rw [mem_lattice, coe_normUnits, ord_norm, hres, one_nsmul, hbeta₁]
            simp⟩ : lattice F 0) =
        stationaryCoefficientClass F chiF psiF hF
          (lowGammaF F K deltaF epsilon₁) hgammaF) :
    let eta := lowEpsilon F K epsilon₁
    let alpha := normUnits F K alpha₁
    let beta := normUnits F K beta₁
    let candidate : K :=
      algebraMap F K (beta : F) * algebraMap F K (eta : F) / (epsilon₁ : K) -
        (beta₁ : K) * algebraMap F K (alpha : F) / (alpha₁ : K)
    ∃ hcand : candidate ∈ lattice K 0,
      latticeQuotientMk K (by omega) ⟨candidate, hcand⟩ =
        stationaryCoefficientClass K chiK psiK
          hprecision.sourceDecomposition (lowGammaK F K deltaF epsilon₁) hgammaK := by
  dsimp only
  let eta : Fˣ := lowEpsilon F K epsilon₁
  let alpha : Fˣ := normUnits F K alpha₁
  let beta : Fˣ := normUnits F K beta₁
  let candidate : K :=
    algebraMap F K (beta : F) * algebraMap F K (eta : F) / (epsilon₁ : K) -
      (beta₁ : K) * algebraMap F K (alpha : F) / (alpha₁ : K)
  change ∃ hcand : candidate ∈ lattice K 0,
    latticeQuotientMk K (by omega) ⟨candidate, hcand⟩ =
      stationaryCoefficientClass K chiK psiK hprecision.sourceDecomposition
        (lowGammaK F K deltaF epsilon₁) hgammaK
  have htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    omega
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos pi hpi hgen
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have halpha : ord F (alpha : F) = (0 : WithTop ℤ) := by
    simp only [alpha, coe_normUnits, ord_norm, hres, one_nsmul, halpha₁]
  have hbeta : ord F (beta : F) = (0 : WithTop ℤ) := by
    simp only [beta, coe_normUnits, ord_norm, hres, one_nsmul, hbeta₁]
  have heta : ord F (eta : F) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ) := by
    exact lowEpsilon_order F K hres epsilon₁ hepsilon₁
  have hcandidate : candidate ∈ lattice K 0 := by
    rw [mem_lattice]
    change (0 : WithTop ℤ) ≤ ord K
      (algebraMap F K (beta : F) * algebraMap F K (eta : F) / (epsilon₁ : K) -
        (beta₁ : K) * algebraMap F K (alpha : F) / (alpha₁ : K))
    have hleft : (0 : WithTop ℤ) ≤ ord K
        (algebraMap F K (beta : F) * algebraMap F K (eta : F) /
          (epsilon₁ : K)) := by
      simp only [ord_div, ord_mul, ord_algebraMap, hbeta, hram, heta,
        hepsilon₁, nsmul_zero, zero_add]
      rw [← WithTop.coe_nsmul]
      norm_cast
      rw [nsmul_eq_mul]
      have hpZ : (1 : ℤ) ≤ (Module.finrank F K : ℤ) := by
        exact_mod_cast Module.finrank_pos (R := F) (M := K)
      have hvZ : (0 : ℤ) ≤ (t + 1 - chiF.conductor : ℕ) := by omega
      exact sub_nonneg.mpr (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpZ hvZ)
    have hright : (0 : WithTop ℤ) ≤ ord K
        ((beta₁ : K) * algebraMap F K (alpha : F) / (alpha₁ : K)) := by
      simp only [ord_div, ord_mul, ord_algebraMap, hbeta₁, halpha,
        halpha₁, hram, nsmul_zero, zero_add, sub_zero]
      simp
    exact (min_le_min hleft hright).trans
      (ord_sub K
        (algebraMap F K (beta : F) * algebraMap F K (eta : F) / (epsilon₁ : K))
        ((beta₁ : K) * algebraMap F K (alpha : F) / (alpha₁ : K)))
  refine ⟨hcandidate, ?_⟩
  let tauData : LocalQuasiCharData F :=
    quasiCharDataOfIsConductor F tau.1 (t + 1)
      (ramifiedNormCharacter_conductor
        F K ht hres pi hpi hgen tau htau)
  let hT : 2 ≤ t + 1 := by
    have hm := hF.conductor_gt_one
    omega
  let hTdec := lowCriticalConductorDecomposition (t := t) hT
  have halphaLinear :=
    (latticeQuotientMk_eq_stationaryCoefficientClass_iff
      F tauData psiF hTdec deltaF hdelta
      (⟨(alpha : F), by rw [mem_lattice, halpha]; simp⟩ : lattice F 0)).1 (by
        simpa only [tauData, hTdec, hT, alpha] using halphaClass)
  have hstationary := stationaryClass_compNorm F K chiF chiK psiF psiK
    hprecision hchi hpsi (lowGammaF F K deltaF epsilon₁)
      (lowGammaK F K deltaF epsilon₁) hgammaF hgammaK
  rw [hstationary]
  rw [← hbetaClass]
  apply (stationaryPairingLeftEquiv K hprecision.sourceDecomposition
    psiK (lowGammaK F K deltaF epsilon₁) hgammaK).injective
  apply AddChar.ext
  intro z
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective K
    (Int.ofNat_le.mpr
      hprecision.sourceDecomposition.variableDepth_le_conductor) z
  change stationaryPairingLeft K hprecision.sourceDecomposition psiK
      (lowGammaK F K deltaF epsilon₁) hgammaK
      (latticeQuotientMk K (by omega) ⟨candidate, hcandidate⟩)
      (latticeQuotientMk K
        (Int.ofNat_le.mpr
          hprecision.sourceDecomposition.variableDepth_le_conductor) x) =
    stationaryPairingLeft K hprecision.sourceDecomposition psiK
      (lowGammaK F K deltaF epsilon₁) hgammaK
      (normPolynomialAdjoint F K hprecision psiF psiK
        (lowGammaF F K deltaF epsilon₁) (lowGammaK F K deltaF epsilon₁)
        hgammaF hgammaK
        (latticeQuotientMk F (by omega)
          (⟨(beta : F), by rw [mem_lattice, hbeta]; simp⟩ : lattice F 0)))
      (latticeQuotientMk K
        (Int.ofNat_le.mpr
          hprecision.sourceDecomposition.variableDepth_le_conductor) x)
  rw [stationaryPairingLeft_mk_mk]
  have hadjoint := normPolynomialAdjoint_pairing F K hprecision psiF psiK
    (lowGammaF F K deltaF epsilon₁) (lowGammaK F K deltaF epsilon₁)
    hgammaF hgammaK
    (latticeQuotientMk F (by omega)
      (⟨(beta : F), by rw [mem_lattice, hbeta]; simp⟩ : lattice F 0))
    (latticeQuotientMk K
      (Int.ofNat_le.mpr
        hprecision.sourceDecomposition.variableDepth_le_conductor) x)
  rw [normPolynomial_mk, stationaryPairingLeft_mk_mk] at hadjoint
  rw [← hadjoint]
  rw [coe_normPolynomialRepresentative]
  -- It remains to compare the explicit low candidate with the exact norm
  -- polynomial.  The following proof mirrors the manuscript conversion.
  let v : ℕ := t + 1 - chiF.conductor
  let q : ℕ := d + epsilon
  have hp : (Module.finrank F K).Prime :=
    PrimeCyclicExtension.degree_prime F K
  have hp2 : 2 ≤ Module.finrank F K := hp.two_le
  have hintermediateX : NormPolynomialIntermediateTermsVanishAt F K
      q chiF.conductor := by
    apply wild_normPolynomialIntermediateTermsVanishAt F K
      (Module.finrank F K) (t + 1) q chiF.conductor hp hT hchar rfl
      (by simpa [wildDifferentContribution] using htrace)
    have hfirst : Module.finrank F K * chiF.conductor ≤
        2 * q + (Module.finrank F K - 1) * chiF.conductor := by
      have hpdecomp : Module.finrank F K =
          1 + (Module.finrank F K - 1) := by omega
      rw [hpdecomp, add_mul, one_mul]
      simpa only [q, Nat.add_sub_cancel_left] using
        Nat.add_le_add_right hF.conductor_le_two_variableDepth
          ((Module.finrank F K - 1) * chiF.conductor)
    exact hfirst.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left (Module.finrank F K - 1) hLow) (2 * q))
  have hdiffX : normPolynomialValue F K (x : K) -
        (trace F K (x : K) + norm F K (x : K)) ∈
      lattice F (chiF.conductor : ℤ) :=
    normPolynomialValue_sub_trace_add_norm_mem F K hp2 hintermediateX
      (x : K) (by simpa only [q] using x.property)
  let y : K :=
    (epsilon₁ : K) * (beta₁ : K) * (x : K) / (alpha₁ : K)
  have hy : (((q + v : ℕ) : ℤ) : WithTop ℤ) ≤ ord K y := by
    dsimp only [y]
    rw [ord_div, ord_mul, ord_mul, hepsilon₁, hbeta₁, halpha₁,
      add_zero, sub_zero]
    have hxord := x.property
    rw [mem_lattice] at hxord
    have hxordq : ((((q : ℕ) : ℤ) : WithTop ℤ)) ≤ ord K (x : K) := by
      simpa only [q] using hxord
    calc
      (((q + v : ℕ) : ℤ) : WithTop ℤ) =
          ((((v : ℕ) : ℤ) : WithTop ℤ) +
            (((q : ℕ) : ℤ) : WithTop ℤ)) := by
        norm_cast
        omega
      _ ≤ ((((v : ℕ) : ℤ) : WithTop ℤ) + ord K (x : K)) :=
        by simpa only [add_comm] using
          add_le_add_left hxordq
            ((((v : ℕ) : ℤ) : WithTop ℤ))
      _ = ((((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ) +
          ord K (x : K)) := by rfl
  have hqvEq : q + v = t + 1 - d := by
    apply Nat.eq_sub_of_add_eq
    have hqAdd : q + d = chiF.conductor := by
      dsimp only [q]
      rw [hF.conductor_eq]
      omega
    have hmAdd : chiF.conductor + v = t + 1 := by
      dsimp only [v]
      exact Nat.add_sub_of_le hLow
    calc
      q + v + d = (q + d) + v := by omega
      _ = chiF.conductor + v := by rw [hqAdd]
      _ = t + 1 := hmAdd
  have hqvCritical : lowCriticalVariableDepth t ≤ q + v := by
    have hdcrit := (lowConductor_floorDepth_bounds (t := t) hF hLow).2
    have hsEq : lowCriticalVariableDepth t =
        t + 1 - lowCriticalFloorDepth t := by
      apply Nat.eq_sub_of_add_eq
      rw [lowCriticalVariableDepth]
      have hTformula := lowCriticalConductor_eq (t := t)
      omega
    rw [hsEq, hqvEq]
    exact Nat.sub_le_sub_left hdcrit (t + 1)
  have hqvT : q + v ≤ t + 1 := by
    rw [hqvEq]
    exact Nat.sub_le (t + 1) d
  have hnormPolyY : normPolynomialValue F K y ∈ lattice F (q + v : ℤ) := by
    exact wild_norm_one_add_sub_one_mem_lattice F K ht htpos hqvT hres
      hchar pi hpi hgen y hy
  let zF : lattice F (lowCriticalVariableDepth t : ℤ) :=
    ⟨normPolynomialValue F K y,
      lattice_antitone F (by exact_mod_cast hqvCritical) hnormPolyY⟩
  have hzTau : psiF.character
      ((alpha : F) * (zF : F) / (deltaF : F)) = 1 := by
    rw [← halphaLinear zF]
    change tau.1 (positiveUnitOfLattice F hTdec.variableDepth_pos zF) = 1
    let yLat : lattice K (q + v : ℤ) := ⟨y, by simpa [mem_lattice] using hy⟩
    have hqvpos : 0 < q + v :=
      lt_of_lt_of_le hTdec.variableDepth_pos hqvCritical
    let yUnit : Kˣ := positiveUnitOfLattice K hqvpos yLat
    have hunit : positiveUnitOfLattice F hTdec.variableDepth_pos zF =
        normUnits F K yUnit := by
      apply Units.ext
      change 1 + normPolynomialValue F K y = norm F K (1 + y)
      rw [normPolynomialValue]
      ring
    rw [hunit]
    exact tau.eq_one_on_normRange F K (normUnits F K yUnit) ⟨yUnit, rfl⟩
  have hintermediateY : NormPolynomialIntermediateTermsVanishAt F K
      (q + v) (t + 1) := by
    apply wild_normPolynomialIntermediateTermsVanishAt F K
      (Module.finrank F K) (t + 1) (q + v) (t + 1)
      hp hT hchar rfl
      (by simpa [wildDifferentContribution] using htrace)
    have hnum : t + 1 ≤ 2 * (q + v) := by
      dsimp only [q, v]
      rw [hF.conductor_eq]
      omega
    have hpdecomp : Module.finrank F K =
        1 + (Module.finrank F K - 1) := by omega
    rw [hpdecomp, add_mul, one_mul]
    simp only [Nat.add_sub_cancel_left]
    exact Nat.add_le_add_right hnum ((Module.finrank F K - 1) * (t + 1))
  have hdiffY : normPolynomialValue F K y -
        (trace F K y + norm F K y) ∈ lattice F ((t + 1 : ℕ) : ℤ) :=
    normPolynomialValue_sub_trace_add_norm_mem F K hp2 hintermediateY y
      (by simpa only [mem_lattice] using hy)
  have htruncY : psiF.character
      ((alpha : F) * normPolynomialValue F K y / (deltaF : F)) =
      psiF.character
        ((alpha : F) * (trace F K y + norm F K y) / (deltaF : F)) := by
    apply lowAddChar_eq_of_sub_mem_conductor F psiF
    have herr := lowScaledError_mem_conductor F psiF deltaF (alpha : F)
      (normPolynomialValue F K y - (trace F K y + norm F K y))
      hdelta halpha hdiffY
    convert herr using 1 <;> ring
  have hsumY : psiF.character
      ((alpha : F) * (trace F K y + norm F K y) / (deltaF : F)) = 1 := by
    rw [← htruncY]
    simpa only [zF] using hzTau
  have hnormY : (alpha : F) * norm F K y =
      (eta : F) * (beta : F) * norm F K (x : K) := by
    change norm F K (alpha₁ : K) *
        norm F K ((epsilon₁ : K) * (beta₁ : K) * (x : K) / (alpha₁ : K)) =
      norm F K (epsilon₁ : K) * norm F K (beta₁ : K) * norm F K (x : K)
    rw [div_eq_mul_inv, map_mul, map_mul, map_mul, Algebra.norm_inv]
    field_simp [Units.ne_zero alpha₁,
      (Algebra.norm_ne_zero_iff.mpr (Units.ne_zero alpha₁))]
  have hconversion : psiF.character
      (-((alpha : F) * trace F K y / (deltaF : F))) =
      psiF.character
        ((eta : F) * (beta : F) * norm F K (x : K) / (deltaF : F)) := by
    have hsum' : psiF.character
          ((alpha : F) * trace F K y / (deltaF : F)) *
        psiF.character
          ((alpha : F) * norm F K y / (deltaF : F)) = 1 := by
      rw [← ContinuousAddChar.map_add_eq_mul]
      convert hsumY using 1 <;> ring
    have hneg := AddChar.map_neg_eq_inv psiF.character.toAddChar
      ((alpha : F) * trace F K y / (deltaF : F))
    change psiF.character
      (-((alpha : F) * trace F K y / (deltaF : F))) =
        (psiF.character
          ((alpha : F) * trace F K y / (deltaF : F)))⁻¹ at hneg
    rw [hneg, eq_inv_of_mul_eq_one_left hsum']
    simp only [inv_inv]
    congr 1
    rw [hnormY]
  have hmv : chiF.conductor + v = t + 1 := by
    dsimp only [v]
    exact Nat.add_sub_of_le hLow
  have hbetaEtaLat : (beta : F) * (eta : F) ∈ lattice F (v : ℤ) := by
    rw [mem_lattice, ord_mul, hbeta, heta, zero_add]
  have herrXfull : (beta : F) * (eta : F) *
        (normPolynomialValue F K (x : K) -
          (trace F K (x : K) + norm F K (x : K))) ∈
      lattice F ((t + 1 : ℕ) : ℤ) := by
    have hmul := mul_mem_lattice F hbetaEtaLat hdiffX
    have hdepth : (v : ℤ) + (chiF.conductor : ℤ) = (t + 1 : ℕ) := by
      exact_mod_cast (by simpa only [add_comm] using hmv)
    simpa only [hdepth] using hmul
  have htruncX : psiF.character
      ((beta : F) * (eta : F) * normPolynomialValue F K (x : K) /
        (deltaF : F)) =
      psiF.character
        ((beta : F) * (eta : F) *
          (trace F K (x : K) + norm F K (x : K)) / (deltaF : F)) := by
    apply lowAddChar_eq_of_sub_mem_conductor F psiF
    have herr := lowScaledError_mem_conductor F psiF deltaF (1 : F)
      ((beta : F) * (eta : F) *
        (normPolynomialValue F K (x : K) -
          (trace F K (x : K) + norm F K (x : K))))
      hdelta (by simp) herrXfull
    convert herr using 1 <;> ring
  have hargCandidate : candidate * (x : K) /
        (lowGammaK F K deltaF epsilon₁ : K) =
      algebraMap F K
          ((beta : F) * (eta : F) / (deltaF : F)) * (x : K) -
        algebraMap F K ((alpha : F) / (deltaF : F)) * y := by
    dsimp only [candidate, y, lowGammaK]
    simp only [Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe]
    simp only [map_div₀, map_mul]
    field_simp [Units.ne_zero epsilon₁, Units.ne_zero alpha₁,
      Units.ne_zero deltaF]
  have htraceCandidate : trace F K
        (candidate * (x : K) / (lowGammaK F K deltaF epsilon₁ : K)) =
      (beta : F) * (eta : F) * trace F K (x : K) / (deltaF : F) -
        (alpha : F) * trace F K y / (deltaF : F) := by
    rw [hargCandidate, map_sub]
    rw [← Algebra.smul_def, map_smul, ← Algebra.smul_def, map_smul]
    ring
  have hphaseCandidate : psiK.character
        (candidate * (x : K) / (lowGammaK F K deltaF epsilon₁ : K)) =
      psiF.character
        ((beta : F) * (eta : F) *
          (trace F K (x : K) + norm F K (x : K)) / (deltaF : F)) := by
    calc
      _ = psiF.character (trace F K
          (candidate * (x : K) /
            (lowGammaK F K deltaF epsilon₁ : K))) := by
        rw [hpsi, ContinuousAddChar.compTrace_apply]
      _ = psiF.character
          ((beta : F) * (eta : F) * trace F K (x : K) / (deltaF : F) -
            (alpha : F) * trace F K y / (deltaF : F)) := by
        rw [htraceCandidate]
      _ = psiF.character
            ((beta : F) * (eta : F) * trace F K (x : K) / (deltaF : F)) *
          psiF.character
            (-((alpha : F) * trace F K y / (deltaF : F))) := by
        rw [sub_eq_add_neg, ContinuousAddChar.map_add_eq_mul]
      _ = psiF.character
            ((beta : F) * (eta : F) * trace F K (x : K) / (deltaF : F)) *
          psiF.character
            ((eta : F) * (beta : F) * norm F K (x : K) / (deltaF : F)) := by
        rw [hconversion]
      _ = psiF.character
          ((beta : F) * (eta : F) * trace F K (x : K) / (deltaF : F) +
            (eta : F) * (beta : F) * norm F K (x : K) / (deltaF : F)) := by
        rw [ContinuousAddChar.map_add_eq_mul]
      _ = psiF.character
          ((beta : F) * (eta : F) *
            (trace F K (x : K) + norm F K (x : K)) / (deltaF : F)) := by
        congr 1
        ring
  have hphaseDownstairs : psiF.character
        ((beta : F) * normPolynomialValue F K (x : K) /
          (lowGammaF F K deltaF epsilon₁ : F)) =
      psiF.character
        ((beta : F) * (eta : F) * normPolynomialValue F K (x : K) /
          (deltaF : F)) := by
    congr 1
    dsimp only [lowGammaF, eta, lowEpsilon]
    simp only [Units.val_div_eq_div_val]
    field_simp [Units.ne_zero deltaF, Units.ne_zero (normUnits F K epsilon₁)]
  apply congrArg Units.val
  exact hphaseCandidate.trans (htruncX.symm.trans hphaseDownstairs.symm)

set_option maxHeartbeats 2000000 in
/-- Pair-packaged form of `lowUpstairsStationaryClass`.  The two source
representatives remain independent existential choices; only their recorded
stationary quotient classes are used. -/
theorem lowUpstairsStationaryClass_ofPair
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1)
    (hprecision : NormPolynomialPrecision F K chiK.conductor d epsilon
      chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (hT : 2 ≤ t + 1)
    (epsilon₁ : Kˣ) (deltaF : Fˣ)
    (hdelta : ord F (deltaF : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hgammaF : ord F (lowGammaF F K deltaF epsilon₁ : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (lowGammaK F K deltaF epsilon₁ : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (P : LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d
      (stationaryCoefficientClass F
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor
            F K ht hres pi hpi hgen tau htau))
        psiF (lowCriticalConductorDecomposition (t := t) hT) deltaF hdelta)
      (stationaryCoefficientClass F chiF psiF hF
        (lowGammaF F K deltaF epsilon₁) hgammaF)) :
    let eta := lowEpsilon F K epsilon₁
    let alpha := P.alpha
    let beta := P.beta
    let candidate : K :=
      algebraMap F K (beta : F) * algebraMap F K (eta : F) / (epsilon₁ : K) -
        (P.beta₁ : K) * algebraMap F K (alpha : F) / (P.alpha₁ : K)
    ∃ hcand : candidate ∈ lattice K 0,
      latticeQuotientMk K (by omega) ⟨candidate, hcand⟩ =
        stationaryCoefficientClass K chiK psiK
          hprecision.sourceDecomposition (lowGammaK F K deltaF epsilon₁) hgammaK := by
  simpa only [LowStationaryNormRepresentativePair.alpha,
    LowStationaryNormRepresentativePair.beta] using
    lowUpstairsStationaryClass (F := F) (K := K) ht hres pi hpi hgen
      chiF chiK psiF psiK hF hLow hprecision hchi hpsi tau htau
      epsilon₁ P.alpha₁ P.beta₁ deltaF hdelta hepsilon₁
      P.alphaRepresentative.source_order P.betaRepresentative.source_order
      hgammaF hgammaK P.alpha_norm_class P.beta_norm_class

/-! ## Exact twist norms and the normalized LOW product -/

/-- Local proof that a discretely valued field is infinite. -/
private theorem lowNormProductLocalFieldInfinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n ↦ (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord F (f m) = (m : WithTop ℤ) :=
      (exists_ord_eq F m).choose_spec
    have hn : ord F (f n) = (n : WithTop ℤ) :=
      (exists_ord_eq F n).choose_spec
    exact WithTop.coe_injective (hm.symm.trans ((congrArg (ord F) hmn).trans hn))
  exact Infinite.of_injective f hf


/-- Homogeneity of the local-field elementary symmetric coefficients under
base-field scaling. -/
theorem low_elementarySymmetric_algebraMap_mul
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsGalois F K]
    (i : ℕ) (c : F) (u : K) :
    elementarySymmetric F K i (algebraMap F K c * u) =
      c ^ i * elementarySymmetric F K i u := by
  letI : Infinite F := lowNormProductLocalFieldInfinite F
  apply (algebraMap F K).injective
  rw [map_mul, map_pow,
    algebraMap_elementarySymmetric_eq_esymm_galois,
    algebraMap_elementarySymmetric_eq_esymm_galois]
  have hconj :
      galoisConjugates F K (algebraMap F K c * u) =
        (galoisConjugates F K u).map
          (fun x ↦ algebraMap F K c * x) := by
    simp [galoisConjugates, galoisConjugate, Multiset.map_map]
  rw [hconj]
  simpa [smul_eq_mul] using
    (Multiset.pow_smul_esymm (R := K) (S := K)
      (algebraMap F K c) i (galoisConjugates F K u)).symm

/-- Exact affine norm expansion with both endpoints visible. -/
theorem low_norm_algebraMap_sub_eq_sum_elementarySymmetric
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsGalois F K]
    (n : F) (hn : n ≠ 0) (u : K) :
    norm F K (algebraMap F K n - u) =
      ∑ i ∈ Finset.range (Module.finrank F K + 1),
        (-1 : F) ^ i * n ^ (Module.finrank F K - i) *
          elementarySymmetric F K i u := by
  let p := Module.finrank F K
  have hfactor : algebraMap F K n - u =
      algebraMap F K n *
        (1 + algebraMap F K (-n⁻¹) * u) := by
    rw [map_neg, map_inv₀]
    field_simp [((map_ne_zero (algebraMap F K)).2 hn)]
    rw [sub_eq_add_neg]
  rw [hfactor, map_mul, norm_algebraMap,
    norm_one_add_eq_sum_elementarySymmetric, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [low_elementarySymmetric_algebraMap_mul]
  have hpow : n ^ p * (-n⁻¹) ^ i =
      (-1 : F) ^ i * n ^ (p - i) := by
    rw [neg_pow, inv_pow, pow_sub₀ n hn hip]
    ring
  dsimp only [p] at hpow
  rw [← mul_assoc, hpow]

/-- Exact denominator/depth interface for the normalized product: only the
two endpoint terms remain after the supplied intermediate lattice bounds. -/
theorem low_norm_algebraMap_sub_endpoints_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [Algebra F K] [Module.Free F K] [Module.Finite F K]
    [IsGalois F K]
    (d : ℕ) (n : F) (hn : n ≠ 0) (u : K)
    (hdegree : 2 ≤ Module.finrank F K)
    (hterms : ∀ {i : ℕ}, 1 ≤ i → i < Module.finrank F K →
      (-1 : F) ^ i * n ^ (Module.finrank F K - i) *
        elementarySymmetric F K i u ∈ lattice F (d : ℤ)) :
    CongruentAtDepth (d : ℤ)
      (norm F K (algebraMap F K n - u))
      (n ^ Module.finrank F K +
        (-1 : F) ^ Module.finrank F K * norm F K u) := by
  let p := Module.finrank F K
  let f : ℕ → F := fun i ↦
    (-1 : F) ^ i * n ^ (p - i) * elementarySymmetric F K i u
  have hmiddle : (∑ j ∈ Finset.range (p - 1), f (j + 1)) ∈
      lattice F (d : ℤ) := by
    apply sum_mem_lattice F
    intro j hj
    simp only [Finset.mem_range] at hj
    exact hterms (by omega) (by simpa [p] using (show j + 1 < p by omega))
  rw [congruentAtDepth_iff_sub_mem_lattice]
  rw [low_norm_algebraMap_sub_eq_sum_elementarySymmetric F K n hn u]
  rw [show p + 1 = (p - 1 + 1) + 1 by omega,
    Finset.sum_range_succ', Finset.sum_range_succ]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  simp [f, p]
  rw [mem_lattice] at hmiddle
  convert hmiddle using 1
  · norm_cast
  · have heq :
        n ^ Module.finrank F K +
              (-1 : F) ^ Module.finrank F K * norm F K u -
            ((∑ x ∈ Finset.range (Module.finrank F K - 1),
                (-1 : F) ^ (x + 1) *
                  n ^ (Module.finrank F K - (x + 1)) *
                  elementarySymmetric F K (x + 1) u) +
              (-1 : F) ^ Module.finrank F K * norm F K u +
              n ^ Module.finrank F K) =
          -(∑ j ∈ Finset.range (p - 1), f (j + 1)) := by
          dsimp only [p, f]
          ring
    rw [heq, ord_neg]


/-- The exact numerical lower bound on every intermediate term in the
normalized LOW product.  This is deliberately stated with the manuscript's
natural-number floor, so no ceiling/floor conversion is hidden. -/
theorem lowProductIntermediateDepth
    (p T m d epsilon v i : ℕ)
    (hp : p.Prime)
    (hm : m = 2 * d + epsilon)
    (hepsilon : epsilon ≤ 1)
    (hv : v = T - m)
    (hmT : m ≤ T)
    (hi : 1 ≤ i)
    (hip : i < p) :
    d ≤ (p - i - 1) * v +
      (i * v + (p - 1) * T) / p := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hTv : T = m + v := by omega
  have hdeT : d + epsilon ≤ T := by omega
  have hkey : p * (T - (d + epsilon)) ≤
      i * v + (p - 1) * T := by
    have hkeyZ : (p : ℤ) * ((T - (d + epsilon) : ℕ) : ℤ) ≤
        (i : ℤ) * (v : ℤ) + ((p - 1 : ℕ) : ℤ) * (T : ℤ) := by
      rw [Nat.cast_sub hdeT, Nat.cast_sub (by omega : 1 ≤ p)]
      push_cast
      nlinarith
    exact_mod_cast hkeyZ
  have hfloor : T - (d + epsilon) ≤
      (i * v + (p - 1) * T) / p :=
    (Nat.le_div_iff_mul_le hp0).2 (by simpa [mul_comm] using hkey)
  omega

/-- Uniform LOW twist bound for every nonterminal symmetric coefficient. -/
theorem lowTwistIntermediateDepth
    (p T v i : ℕ) (hp : p.Prime) (hi : 1 ≤ i) (hip : i < p) :
    T / 2 ≤ (i * v + (p - 1) * T) / p := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  apply (Nat.le_div_iff_mul_le hp0).2
  rw [mul_comm (T / 2) p]
  have htwo : 2 * (T / 2) ≤ T := Nat.mul_div_le T 2
  have hrle : T / 2 ≤ T := Nat.div_le_self T 2
  have hp2eq : p = (p - 2) + 2 := by omega
  have hp1eq : p - 1 = (p - 2) + 1 := by omega
  calc
    p * (T / 2) = ((p - 2) + 2) * (T / 2) :=
      congrArg (fun z : ℕ ↦ z * (T / 2)) hp2eq
    _ = 2 * (T / 2) + (p - 2) * (T / 2) := by ring
    _ ≤ T + (p - 2) * T :=
      Nat.add_le_add htwo (Nat.mul_le_mul_left (p - 2) hrle)
    _ = (p - 1) * T := by rw [hp1eq]; ring
    _ ≤ i * v + (p - 1) * T := Nat.le_add_left _ _

/-- If every nonterminal coefficient of the exact norm expansion is in one
target lattice, the error after retaining exactly the constant and terminal
norm terms lies in that lattice. -/
theorem low_norm_one_add_sub_one_sub_norm_mem_of_nonterminal
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [Algebra F K] [Module.Free F K] [Module.Finite F K]
    (r : ℕ) (hdegree : 2 ≤ Module.finrank F K)
    (w : K)
    (hterms : ∀ {i : ℕ}, 1 ≤ i → i < Module.finrank F K →
      elementarySymmetric F K i w ∈ lattice F (r : ℤ)) :
    norm F K (1 + w) - 1 - norm F K w ∈ lattice F (r : ℤ) := by
  have hmiddle :
      (∑ j ∈ Finset.range (Module.finrank F K - 1),
        elementarySymmetric F K (j + 1) w) ∈ lattice F (r : ℤ) := by
    apply sum_mem_lattice F
    intro j hj
    simp only [Finset.mem_range] at hj
    exact hterms (by omega) (by omega)
  rw [norm_one_add_eq_one_add_sum_elementarySymmetric]
  rw [show Module.finrank F K = Module.finrank F K - 1 + 1 by omega,
    Finset.sum_range_succ]
  rw [show Module.finrank F K - 1 + 1 = Module.finrank F K by omega,
    elementarySymmetric_finrank]
  convert hmiddle using 1
  abel

/-- The strong wild estimate kills every nonterminal term in the LOW twist
norm at precisely the common coefficient depth `floor((t+1)/2)`. -/
theorem lowTwistNormRemainder_mem
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t v : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (w : K)
    (hw : ((v : ℕ) : WithTop ℤ) ≤ ord K w) :
    norm F K (1 + w) - 1 - norm F K w ∈
      lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
  let p := Module.finrank F K
  let T := t + 1
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp2 : 2 ≤ p := hp.two_le
  have hT : 2 ≤ T := by omega
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos pi hpi hgen
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  apply low_norm_one_add_sub_one_sub_norm_mem_of_nonterminal
    F K (T / 2) hp2 w
  intro i hi hip
  rw [mem_lattice]
  have hsym := wild_elementarySymmetric_bound F K p T (v : ℤ)
    hp hT hchar rfl (by
      simpa [p, T, wildDifferentContribution] using htrace) hw hi hip
  have hn := lowTwistIntermediateDepth p T v i hp hi hip
  have hnZ : (T / 2 : ℕ) ≤
      ((i : ℤ) * (v : ℤ) + (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) := by
    exact_mod_cast hn
  exact (WithTop.coe_le_coe.mpr hnZ).trans hsym

/-- Scaling the two-endpoint expansion by its nonzero leading summand gives
the affine norm congruence. -/
theorem low_norm_add_sub_endpoint_norms_mem_of_ratio
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [Algebra F K] [Module.Free F K] [Module.Finite F K]
    (r : ℕ) (a b : K) (ha : a ≠ 0)
    (hnorma : norm F K a ∈ lattice F 0)
    (hrem : norm F K (1 + b / a) - 1 - norm F K (b / a) ∈
      lattice F (r : ℤ)) :
    norm F K (a + b) - (norm F K a + norm F K b) ∈
      lattice F (r : ℤ) := by
  have hscaled := mul_mem_lattice F hnorma hrem
  have hab : a + b = a * (1 + b / a) := by field_simp
  have hnormb : norm F K b = norm F K a * norm F K (b / a) := by
    calc
      norm F K b = norm F K (a * (b / a)) := by
        congr 1
        field_simp
      _ = norm F K a * norm F K (b / a) := map_mul _ _ _
  rw [hab, map_mul, hnormb]
  simpa only [zero_add, mul_sub, mul_one, sub_add_eq_sub_sub] using hscaled

/-- Representative-level LOW twist congruence.  The prime-field scalar is
required to satisfy the Teichmuller equation `j^p=j`; no false equality with
its integer lift is used. -/
theorem lowTwistNorm_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t v : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (alpha₁ epsilon₁ beta₁ : Kˣ) (j : F)
    (hj : j ≠ 0)
    (hjpow : j ^ Module.finrank F K = j)
    (hnorma : norm F K
      (algebraMap F K j * (alpha₁ : K)) ∈ lattice F 0)
    (hw : ((v : ℕ) : WithTop ℤ) ≤
      ord K ((epsilon₁ : K) * (beta₁ : K) /
        (algebraMap F K j * (alpha₁ : K)))) :
    CongruentAtDepth (((t + 1) / 2 : ℕ) : ℤ)
      (norm F K
        (algebraMap F K j * (alpha₁ : K) +
          (epsilon₁ : K) * (beta₁ : K)))
      (j * norm F K (alpha₁ : K) +
        norm F K (epsilon₁ : K) * norm F K (beta₁ : K)) := by
  let a : K := algebraMap F K j * (alpha₁ : K)
  let b : K := (epsilon₁ : K) * (beta₁ : K)
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact mul_ne_zero ((map_ne_zero (algebraMap F K)).2 hj) (Units.ne_zero alpha₁)
  have hrem := lowTwistNormRemainder_mem F K ht hres pi hpi hgen
    htpos (b / a) (by simpa [a, b] using hw)
  have hmain := low_norm_add_sub_endpoint_norms_mem_of_ratio
    F K ((t + 1) / 2) a b ha (by simpa [a] using hnorma) hrem
  rw [congruentAtDepth_iff_sub_mem_lattice]
  simpa [a, b, map_mul, norm_algebraMap, hjpow] using hmain

/-- The normalized upstairs norm has exactly the manuscript's product
denominator `alpha^p/epsilon` and final depth `d`.  The unscaled norm is first
controlled at depth `d+v`; division by `epsilon` then shifts by exactly
`-v`, preventing a spurious stronger congruence. -/
theorem lowNormalizedNorm_endpoints_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t m d epsilon v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (hm : m = 2 * d + epsilon) (hepsilon : epsilon ≤ 1)
    (hmT : m ≤ t + 1) (hv : v = t + 1 - m)
    (alpha epsilonF : Fˣ) (u : K)
    (halpha : ord F (alpha : F) = (0 : WithTop ℤ))
    (hepsilonF : ord F (epsilonF : F) = ((v : ℕ) : WithTop ℤ))
    (hu : ord K u = ((v : ℕ) : WithTop ℤ)) :
    let p := Module.finrank F K
    let n := norm F K u
    let A := (alpha : F) ^ p / (epsilonF : F)
    CongruentAtDepth (d : ℤ)
      (A * norm F K (algebraMap F K n - u))
      (A * (n ^ p + (-1 : F) ^ p * n)) := by
  dsimp only
  let p := Module.finrank F K
  let T := t + 1
  let n := norm F K u
  let A := (alpha : F) ^ p / (epsilonF : F)
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp2 : 2 ≤ p := hp.two_le
  have hT : 2 ≤ T := by omega
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos pi hpi hgen
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have hnord : ord F n = ((v : ℤ) : WithTop ℤ) := by
    dsimp only [n]
    rw [ord_norm, hres, one_nsmul, hu]
    norm_cast
  have hn : n ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hnord]; exact WithTop.coe_ne_top)
  have hbase : CongruentAtDepth ((d + v : ℕ) : ℤ)
      (norm F K (algebraMap F K n - u))
      (n ^ p + (-1 : F) ^ p * norm F K u) := by
    apply low_norm_algebraMap_sub_endpoints_congruent
      F K (d + v) n hn u hp2
    intro i hi hip
    rw [mem_lattice, ord_mul, ord_mul]
    simp only [ord_pow, ord_neg, ord_one, nsmul_zero, zero_add]
    rw [hnord]
    have hsym := wild_elementarySymmetric_bound F K p T (v : ℤ)
      hp hT hchar rfl (by
        simpa [p, T, wildDifferentContribution] using htrace)
      (by simpa using hu.ge) hi hip
    have hnum := lowProductIntermediateDepth
      p T m d epsilon v i hp hm hepsilon (by simpa [T] using hv)
        (by simpa [T] using hmT) hi hip
    have hpi : p - i = (p - i - 1) + 1 := by omega
    have hpiV : (p - i) * v = v + (p - i - 1) * v := by
      calc
        (p - i) * v = ((p - i - 1) + 1) * v :=
          congrArg (fun z : ℕ ↦ z * v) hpi
        _ = v + (p - i - 1) * v := by ring
    have hnum' : d + v ≤ (p - i) * v +
        (i * v + (p - 1) * T) / p := by
      calc
        d + v = v + d := by omega
        _ ≤ v + ((p - i - 1) * v +
            (i * v + (p - 1) * T) / p) := Nat.add_le_add_left hnum v
        _ = (p - i) * v + (i * v + (p - 1) * T) / p := by
          rw [hpiV]
          ac_rfl
    have hnumZ : ((d + v : ℕ) : ℤ) ≤
        ((p - i : ℕ) : ℤ) * (v : ℤ) +
          ((i : ℤ) * (v : ℤ) +
            (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) := by
      exact_mod_cast hnum'
    have hmul :
        (((((p - i : ℕ) : ℤ) * (v : ℤ) : ℤ)) : WithTop ℤ) =
          (p - i) • (((v : ℕ) : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul]
      congr 1
    calc
      ((((d + v : ℕ) : ℤ) : WithTop ℤ)) ≤
          (((((p - i : ℕ) : ℤ) * (v : ℤ) +
            ((i : ℤ) * (v : ℤ) +
              (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) :
                WithTop ℤ)) := WithTop.coe_le_coe.mpr hnumZ
      _ = (p - i) • ((v : ℤ) : WithTop ℤ) +
          ((((i : ℤ) * (v : ℤ) +
            (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) :
              WithTop ℤ) := by
            rw [WithTop.coe_add, hmul]
      _ ≤ (p - i) • ((v : ℤ) : WithTop ℤ) +
          ord F (elementarySymmetric F K i u) :=
            by simpa [add_comm] using
              (add_le_add_left hsym ((p - i) •
                (((v : ℕ) : ℤ) : WithTop ℤ)))
  have hA : ((-(v : ℤ) : ℤ) : WithTop ℤ) ≤ ord F A := by
    dsimp only [A]
    rw [ord_div, ord_pow, halpha, hepsilonF]
    simp
  have hscaled := CongruentAtDepth.mul_left_shift
    (r := -(v : ℤ)) (s := ((d + v : ℕ) : ℤ)) A hA hbase
  simpa [A, n, p] using hscaled

/-- The two surviving endpoint terms are exactly the nonzero prime-field
product.  The lift is abstracted only by its proved polynomial identity, so
this applies to the canonical Teichmuller lift in mixed characteristic. -/
theorem lowNormEndpoints_eq_primeProduct
    (F : Type*) [Field F]
    (p : ℕ) [Fact p.Prime]
    (omega : ZMod p → F)
    (hpoly :
      (∏ j : ZMod p, (Polynomial.X + Polynomial.C (omega j))) =
        (Polynomial.X ^ p +
          Polynomial.C ((-1 : F) ^ p) * Polynomial.X : F[X]))
    (hzero : omega 0 = 0)
    (alpha epsilonF beta : Fˣ) :
    let n : F := (epsilonF : F) * (beta : F) / (alpha : F)
    ((alpha : F) ^ p / (epsilonF : F)) *
        (n ^ p + (-1 : F) ^ p * n) =
      (beta : F) *
        ∏ j : (ZMod p)ˣ,
          ((epsilonF : F) * (beta : F) +
            omega (j : ZMod p) * (alpha : F)) := by
  classical
  dsimp only
  let n : F := (epsilonF : F) * (beta : F) / (alpha : F)
  let f : ZMod p → F := fun j ↦ n + omega j
  have hfull : (∏ j : ZMod p, f j) =
      n ^ p + (-1 : F) ^ p * n := by
    have h := congrArg (Polynomial.eval n) hpoly
    simpa [Polynomial.eval_prod, f] using h
  have hcompl :
      (∏ j ∈ ({0} : Finset (ZMod p))ᶜ, f j) =
        ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
    rw [Finset.prod_subtype (p := fun x : ZMod p ↦ x ≠ 0)
      (({0} : Finset (ZMod p))ᶜ)
      (fun x ↦ by simp) f]
    exact (Equiv.prod_comp unitsEquivNeZero
      (fun j : {x : ZMod p // x ≠ 0} ↦ f (j : ZMod p))).symm
  have hsplit : (∏ j : ZMod p, f j) =
      n * ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
    rw [Fintype.prod_eq_mul_prod_compl (0 : ZMod p) f, hcompl]
    simp [f, hzero]
  have hscale (j : (ZMod p)ˣ) :
      (epsilonF : F) * (beta : F) +
          omega (j : ZMod p) * (alpha : F) =
        (alpha : F) * f (j : ZMod p) := by
    dsimp only [f, n]
    field_simp [Units.ne_zero alpha]
  have hprodScale :
      (∏ j : (ZMod p)ˣ,
          ((epsilonF : F) * (beta : F) +
            omega (j : ZMod p) * (alpha : F))) =
        (alpha : F) ^ (p - 1) *
          ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
    calc
      _ = ∏ j : (ZMod p)ˣ,
          ((alpha : F) * f (j : ZMod p)) := by
            apply Finset.prod_congr rfl
            intro j _
            exact hscale j
      _ = (∏ _j : (ZMod p)ˣ, (alpha : F)) *
          ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
            rw [Finset.prod_mul_distrib]
      _ = (alpha : F) ^ (p - 1) *
          ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
            rw [Finset.prod_const, Finset.card_univ,
              Fintype.card_units, ZMod.card]
  rw [← hfull, hsplit, hprodScale]
  dsimp only [n]
  field_simp [Units.ne_zero alpha, Units.ne_zero epsilonF]
  have hpow : (alpha : F) * (alpha : F) ^ (p - 1) =
      (alpha : F) ^ p := by
    rw [mul_comm, pow_sub_one_mul ((Fact.out : p.Prime).pos.ne' : p ≠ 0)]
  calc
    (alpha : F) ^ p * ∏ j : (ZMod p)ˣ, f (j : ZMod p) =
        ((alpha : F) * (alpha : F) ^ (p - 1)) *
          ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by rw [hpow]
    _ = ((alpha : F) * ∏ j : (ZMod p)ˣ, f (j : ZMod p)) *
        (alpha : F) ^ (p - 1) := by ring

/-- Combined exact LOW product congruence for the normalized upstairs
representative. -/
theorem lowNormalizedNorm_product_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fact (Module.finrank F K).Prime]
    {t m d epsilon v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (hm : m = 2 * d + epsilon) (hepsilon : epsilon ≤ 1)
    (hmT : m ≤ t + 1) (hv : v = t + 1 - m)
    (alpha epsilonF beta : Fˣ) (u : K)
    (halpha : ord F (alpha : F) = (0 : WithTop ℤ))
    (hepsilonF : ord F (epsilonF : F) = ((v : ℕ) : WithTop ℤ))
    (hu : ord K u = ((v : ℕ) : WithTop ℤ))
    (hn : norm F K u =
      (epsilonF : F) * (beta : F) / (alpha : F))
    (omega : ZMod (Module.finrank F K) → F)
    (hpoly :
      (∏ j : ZMod (Module.finrank F K),
          (Polynomial.X + Polynomial.C (omega j))) =
        (Polynomial.X ^ Module.finrank F K +
          Polynomial.C ((-1 : F) ^ Module.finrank F K) *
            Polynomial.X : F[X]))
    (hzero : omega 0 = 0) :
    let p := Module.finrank F K
    let n : F := norm F K u
    let A := (alpha : F) ^ p / (epsilonF : F)
    CongruentAtDepth (d : ℤ)
      (A * norm F K (algebraMap F K n - u))
      ((beta : F) * ∏ j : (ZMod p)ˣ,
        ((epsilonF : F) * (beta : F) +
          omega (j : ZMod p) * (alpha : F))) := by
  dsimp only
  have hnorm := lowNormalizedNorm_endpoints_congruent
    F K ht hres pi hpi hgen htpos hm hepsilon hmT hv
      alpha epsilonF u halpha hepsilonF hu
  rw [hn] at hnorm
  change CongruentAtDepth (d : ℤ)
    (((alpha : F) ^ Module.finrank F K / (epsilonF : F)) *
      norm F K (algebraMap F K
        ((epsilonF : F) * (beta : F) / (alpha : F)) - u))
    (((alpha : F) ^ Module.finrank F K / (epsilonF : F)) *
      (((epsilonF : F) * (beta : F) / (alpha : F)) ^
          Module.finrank F K +
        (-1 : F) ^ Module.finrank F K *
          ((epsilonF : F) * (beta : F) / (alpha : F)))) at hnorm
  have hend := lowNormEndpoints_eq_primeProduct F
    (Module.finrank F K) omega hpoly hzero alpha epsilonF beta
  rw [hend] at hnorm
  simpa [hn] using hnorm

/-- Prime-Teichmuller specialization of the normalized LOW product
congruence.  The target depth remains exactly `d`. -/
theorem lowPrimeTeichmullerNormalizedNorm_product_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fact (Module.finrank F K).Prime]
    {t m d epsilon v : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (hm : m = 2 * d + epsilon) (hepsilon : epsilon ≤ 1)
    (hmT : m ≤ t + 1) (hv : v = t + 1 - m)
    (hchar : residueCharacteristic F = Module.finrank F K)
    (alpha epsilonF beta : Fˣ) (u : K)
    (halpha : ord F (alpha : F) = (0 : WithTop ℤ))
    (hepsilonF : ord F (epsilonF : F) = ((v : ℕ) : WithTop ℤ))
    (hu : ord K u = ((v : ℕ) : WithTop ℤ))
    (hn : norm F K u =
      (epsilonF : F) * (beta : F) / (alpha : F)) :
    let p := Module.finrank F K
    let n : F := norm F K u
    let A := (alpha : F) ^ p / (epsilonF : F)
    CongruentAtDepth (d : ℤ)
      (A * norm F K (algebraMap F K n - u))
      ((beta : F) * ∏ j : (ZMod p)ˣ,
        ((epsilonF : F) * (beta : F) +
          (((primeTeichmuller F p hchar (j : ZMod p) :
              ringOfIntegers F) : F)) * (alpha : F))) := by
  apply lowNormalizedNorm_product_congruent F K ht hres pi hpi hgen
    htpos hm hepsilon hmT hv alpha epsilonF beta u halpha hepsilonF hu hn
    (fun j ↦ ((primeTeichmuller F (Module.finrank F K) hchar j :
      ringOfIntegers F) : F))
  · exact primeTeichmullerPolynomial_add_field
      F (Module.finrank F K) hchar
  · simp [primeTeichmuller]

/-! ## Complete twist stationary classes on the LOW common denominator -/

theorem lowIdentityCommonClass_isRestriction
    {t : ℕ} (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hLow : chi.conductor ≤ t + 1)
    (delta gammaF eta beta : Fˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgammaF : ord F (gammaF : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (heta : ord F (eta : F) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hfactor : delta = eta * gammaF)
    (hbeta : ord F (beta : F) = (0 : WithTop ℤ))
    (hbetaClass : latticeQuotientMk F (by omega)
        (⟨(beta : F), (mem_lattice_and_not_mem_succ_iff F).2 hbeta |>.1⟩ : lattice F 0) =
      stationaryCoefficientClass F chi psi hF gammaF hgammaF) :
    let hT : 2 ≤ t + 1 := by
      have hm := hF.conductor_gt_one
      omega
    let hTdec := lowCriticalConductorDecomposition (t := t) hT
    IsStationaryRestrictionClass F chi.character psi (t + 1 : ℤ)
      (by
        have hp := lowCriticalParity_le_one (t := t)
        have heq := lowCriticalConductor_eq (t := t)
        omega)
      (by
        have hp := lowCriticalParity_le_one (t := t)
        have heq := lowCriticalConductor_eq (t := t)
        omega)
      delta
      (stationaryCoefficientLamprechtEquivAtConductor F hTdec
        (lowIdentityCommonClass (F := F) (K := K) (t := t)
          hF hLow eta heta
          (stationaryCoefficientClass F chi psi hF gammaF hgammaF))) := by
  dsimp only
  intro c hc x
  let b : lattice F 0 :=
    ⟨(beta : F), (mem_lattice_and_not_mem_succ_iff F).2 hbeta |>.1⟩
  have hbClass : latticeQuotientMk F (by omega) b =
      stationaryCoefficientClass F chi psi hF gammaF hgammaF := by
    simpa [b] using hbetaClass
  have hvar := lowConductor_variableDepth_le_critical (t := t) hF hLow
  let xNative : lattice F ((d + epsilon : ℕ) : ℤ) :=
    ⟨(x : F), lattice_antitone F (by exact_mod_cast hvar) x.property⟩
  have hlinear :=
    (latticeQuotientMk_eq_stationaryCoefficientClass_iff
      F chi psi hF gammaF hgammaF b).1 hbClass xNative
  let c₀ : lattice F 0 :=
    lowIdentityCommonRepresentative (t := t) F hF hLow eta heta b
  have hcommon :
      lowIdentityCommonClass (F := F) (K := K) (t := t)
          hF hLow eta heta
          (stationaryCoefficientClass F chi psi hF gammaF hgammaF) =
        latticeQuotientMk F (by omega) c₀ := by
    rw [← hbClass, lowIdentityCommonClass_mk]
  have hc₀ :
      latticeQuotientMk F
          (sub_le_sub_left
            (Int.ofNat_le.mpr
              (lowCriticalConductorDecomposition (t := t)
                (by have hm := hF.conductor_gt_one; omega)).variableDepth_le_conductor)
            (t + 1 : ℕ))
          (⟨(c₀ : F), by simpa using c₀.property⟩ :
            lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ))) =
        stationaryCoefficientLamprechtEquivAtConductor F
          (lowCriticalConductorDecomposition (t := t)
            (by have hm := hF.conductor_gt_one; omega))
          (lowIdentityCommonClass (F := F) (K := K) (t := t)
            hF hLow eta heta
            (stationaryCoefficientClass F chi psi hF gammaF hgammaF)) := by
    rw [hcommon, stationaryCoefficientLamprechtEquivAtConductor_mk]
  have hclasses := hc.trans hc₀.symm
  have hdiff := (latticeQuotientMk_eq_mk_iff F _).1 hclasses
  have hphaseMem :
      ((c : F) - (c₀ : F)) * (x : F) / (delta : F) ∈
        lattice F (-psi.conductor) :=
    (forall_mul_div_mem_lattice_iff_left F hdelta).2 hdiff (x : F) x.property
  have hphase :
      psi.character (((c : F) - (c₀ : F)) * (x : F) / (delta : F)) = 1 :=
    psi.isConductor.trivial _ hphaseMem
  have hunit :
      (positiveUnitOfLattice F (by
          have hp := lowCriticalParity_le_one (t := t)
          have heq := lowCriticalConductor_eq (t := t)
          omega) x : Fˣ) =
        positiveUnitOfLattice F hF.variableDepth_pos xNative := by
    apply Units.ext
    simp [xNative]
  rw [hunit, hlinear]
  calc
    psi.character ((beta : F) * (xNative : F) / (gammaF : F)) =
        psi.character ((c₀ : F) * (x : F) / (delta : F)) := by
      congr 1
      simp only [c₀, lowIdentityCommonRepresentative, xNative,
        b, Submodule.coe_mk]
      rw [hfactor]
      field_simp [Units.ne_zero eta, Units.ne_zero gammaF]
      <;> push_cast
      <;> ring
    _ = psi.character ((c : F) * (x : F) / (delta : F)) := by
      rw [show (c : F) * (x : F) / (delta : F) =
          (c₀ : F) * (x : F) / (delta : F) +
            ((c : F) - (c₀ : F)) * (x : F) / (delta : F) by ring,
        psi.character.map_add_eq_mul, hphase, mul_one]

theorem lowNonzeroTwistCommonClass
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hLow : chi.conductor ≤ t + 1)
    (delta gammaF eta : Fˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgammaF : ord F (gammaF : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (heta : ord F (eta : F) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hfactor : delta = eta * gammaF)
    (j : ℕ) (hj : tau ^ j ≠ 1)
    (hprod : IsMultiplicativeConductor F
      ((tau ^ j).1 * chi.character) (t + 1)) :
    let hT : 2 ≤ t + 1 := by
      have hm := hF.conductor_gt_one
      omega
    let hTdec := lowCriticalConductorDecomposition (t := t) hT
    let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
      (ramifiedNormCharacter_conductor F K
        ht hres pi hpi hgen tau htau)
    let prodData := quasiCharDataOfIsConductor F
      ((tau ^ j).1 * chi.character) (t + 1) hprod
    stationaryCoefficientClass F prodData psi hTdec delta hdelta =
      j • stationaryCoefficientClass F tauData psi hTdec delta hdelta +
        lowIdentityCommonClass (F := F) (K := K) (t := t)
          hF hLow eta heta
          (stationaryCoefficientClass F chi psi hF gammaF hgammaF) := by
  dsimp only
  let hT : 2 ≤ t + 1 := by
    have hm := hF.conductor_gt_one
    omega
  let hTdec := lowCriticalConductorDecomposition (t := t) hT
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K
      ht hres pi hpi hgen tau htau)
  let powerData := quasiCharDataOfIsConductor F (tau ^ j).1 (t + 1)
    (ramifiedNormCharacter_conductor F K
      ht hres pi hpi hgen (tau ^ j) hj)
  let prodData := quasiCharDataOfIsConductor F
    ((tau ^ j).1 * chi.character) (t + 1) hprod
  let sTau := stationaryNumeratorClass F tauData psi ((t + 1 : ℕ) : ℤ)
    (stationaryDepthOfConductorDecomposition F tauData hTdec) delta hdelta
  let sPower := stationaryNumeratorClass F powerData psi ((t + 1 : ℕ) : ℤ)
    (stationaryDepthOfConductorDecomposition F powerData hTdec) delta hdelta
  let sChi := stationaryCoefficientLamprechtEquivAtConductor F hTdec
    (lowIdentityCommonClass (F := F) (K := K) (t := t)
      hF hLow eta heta
      (stationaryCoefficientClass F chi psi hF gammaF hgammaF))
  have hsPower : IsStationaryRestrictionClass F (tau ^ j).1 psi
      ((t + 1 : ℕ) : ℤ)
      (stationaryDepthOfConductorDecomposition F powerData hTdec).pos
      (stationaryDepthOfConductorDecomposition F powerData hTdec).le_conductor
      delta sPower :=
    stationaryNumeratorClass_isRestriction F powerData psi ((t + 1 : ℕ) : ℤ)
      (stationaryDepthOfConductorDecomposition F powerData hTdec) delta hdelta
  have hsChi : IsStationaryRestrictionClass F chi.character psi
      ((t + 1 : ℕ) : ℤ)
      (stationaryDepthOfConductorDecomposition F powerData hTdec).pos
      (stationaryDepthOfConductorDecomposition F powerData hTdec).le_conductor
      delta sChi := by
    obtain ⟨b, hb⟩ := latticeQuotientMk_surjective F (by omega)
      (stationaryCoefficientClass F chi psi hF gammaF hgammaF)
    have hbord : ord F (b : F) = (0 : WithTop ℤ) :=
      stationaryCoefficientClass_representative_ord_zero F K F chi psi
        hF gammaF hgammaF b hb
    have hb0 : (b : F) ≠ 0 :=
      (ord_ne_top_iff F).1 (by rw [hbord]; exact WithTop.coe_ne_top)
    let beta : Fˣ := Units.mk0 (b : F) hb0
    have hbetaClass : latticeQuotientMk F (by omega)
          (⟨(beta : F), (mem_lattice_and_not_mem_succ_iff F).2
            (by simpa [beta] using hbord) |>.1⟩ : lattice F 0) =
        stationaryCoefficientClass F chi psi hF gammaF hgammaF := by
      simpa [beta] using hb
    simpa [powerData, hTdec, sChi] using
      lowIdentityCommonClass_isRestriction (F := F) (K := K) chi psi hF hLow
        delta gammaF eta beta hdelta hgammaF heta hfactor
        (by simpa [beta] using hbord) hbetaClass
  have hsMul := IsStationaryRestrictionClass.mul F psi ((t + 1 : ℕ) : ℤ)
    (stationaryDepthOfConductorDecomposition F powerData hTdec).pos
    (stationaryDepthOfConductorDecomposition F powerData hTdec).le_conductor
    delta hdelta sPower sChi hsPower hsChi
  have hsProd : IsStationaryNumeratorClass F prodData psi ((t + 1 : ℕ) : ℤ)
      (stationaryDepthOfConductorDecomposition F prodData hTdec)
      delta (sPower + sChi) := by
    intro c hc x
    exact hsMul c hc x
  have huniq : sPower + sChi =
      stationaryNumeratorClass F prodData psi ((t + 1 : ℕ) : ℤ)
        (stationaryDepthOfConductorDecomposition F prodData hTdec)
        delta hdelta :=
    stationaryNumeratorClass_unique F prodData psi ((t + 1 : ℕ) : ℤ)
      (stationaryDepthOfConductorDecomposition F prodData hTdec)
      delta hdelta (sPower + sChi) hsProd
  have hpower := normCharacterPower_stationaryClass_eq_nsmul
    F K ht hres pi hpi hgen tau htau j hj psi ((t + 1 : ℕ) : ℤ)
      (stationaryDepthOfConductorDecomposition F tauData hTdec) delta hdelta
  have hpower' : sPower = j • sTau := by
    simpa [sPower, sTau, powerData, tauData, hTdec] using hpower
  have htauClass :
      stationaryCoefficientLamprechtEquivAtConductor F hTdec
          (stationaryCoefficientClass F tauData psi hTdec delta hdelta) =
        sTau := by
    simpa [sTau, tauData, hTdec, Nat.cast_add, Nat.cast_one] using
      (stationaryCoefficientClass_toLamprecht F tauData psi hTdec delta hdelta)
  apply (stationaryCoefficientLamprechtEquivAtConductor F hTdec).injective
  calc
    stationaryCoefficientLamprechtEquivAtConductor F hTdec
        (stationaryCoefficientClass F prodData psi hTdec delta hdelta) =
      stationaryNumeratorClass F prodData psi ((t + 1 : ℕ) : ℤ)
        (stationaryDepthOfConductorDecomposition F prodData hTdec)
        delta hdelta :=
      stationaryCoefficientClass_toLamprecht F prodData psi hTdec delta hdelta
    _ = sPower + sChi := huniq.symm
    _ = j • sTau + sChi := by rw [hpower']
    _ = stationaryCoefficientLamprechtEquivAtConductor F hTdec
        (j • stationaryCoefficientClass F tauData psi hTdec delta hdelta +
          lowIdentityCommonClass (F := F) (K := K) (t := t)
            hF hLow eta heta
            (stationaryCoefficientClass F chi psi hF gammaF hgammaF)) := by
      rw [map_add, map_nsmul,
        htauClass]

theorem lowTeichmuller_nsmul_class
    (p : ℕ) [Fact p.Prime]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = p)
    (hchar : residueCharacteristic F = p)
    (j : ZMod p) (alpha : Fˣ)
    (halpha : ord F (alpha : F) = (0 : WithTop ℤ)) :
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (⟨((primeTeichmuller F p hchar j : ringOfIntegers F) : F) *
            (alpha : F), by
          simpa only [zero_add] using mul_mem_lattice F
            ((mem_lattice_zero_iff F).2
              (primeTeichmuller F p hchar j).property)
            ((mem_lattice_and_not_mem_succ_iff F).2 halpha |>.1)⟩ :
          lattice F 0) =
      j.val • latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (⟨(alpha : F),
          (mem_lattice_and_not_mem_succ_iff F).2 halpha |>.1⟩ : lattice F 0) := by
  rw [← map_nsmul]
  apply (latticeQuotientMk_eq_mk_iff F
    (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)).2
  have hdiff := primeTeichmuller_sub_natCast_mem_lattice_halfBreak
    F K p ht hres pi hpi hgen hdegree hchar j
  have hmul := mul_mem_lattice F hdiff
    ((mem_lattice_and_not_mem_succ_iff F).2 halpha |>.1)
  have hnsmul :
      ((j.val •
        (⟨(alpha : F),
          (mem_lattice_and_not_mem_succ_iff F).2 halpha |>.1⟩ : lattice F 0) :
          lattice F 0) : F) = (j.val : F) * (alpha : F) := by
    change j.val • (alpha : F) = (j.val : F) * (alpha : F)
    simp [nsmul_eq_mul]
  rw [hnsmul]
  simpa only [Submodule.coe_mk, ← sub_mul, add_zero,
    lowCriticalFloorDepth] using hmul



theorem lowGeneratorPower_ne_one
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0) :
    lowNormCharacterGenerator F K ht hres pi hpi hgen ^ j.val ≠ 1 := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  have hindex : (Multiplicative.ofAdd j) ≠ 1 := by
    intro h
    apply hj
    have h' := congrArg Multiplicative.toAdd h
    simpa using h'
  have hmu : mu ≠ 1 :=
    (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2 hindex
  have hpow := lowNormCharacterGenerator_pow
    F K ht hres pi hpi hgen j
  intro hone
  apply hmu
  exact hpow.trans hone

theorem lowGeneratorPowerTwist_isConductor
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hLow : chi.conductor ≤ t + 1)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0) :
    IsMultiplicativeConductor F
      ((lowNormCharacterGenerator F K ht hres pi hpi hgen ^ j.val).1 *
        chi.character) (t + 1) := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  have hindex : (Multiplicative.ofAdd j) ≠ 1 := by
    intro h
    apply hj
    have h' := congrArg Multiplicative.toAdd h
    simpa using h'
  have hmu : mu ≠ 1 :=
    (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2 hindex
  have hcond := minimalOrbit_nontrivialTwist_isConductor
    F K ht hres pi hpi hgen chi hminimal mu hmu
  have hpow := lowNormCharacterGenerator_pow
    F K ht hres pi hpi hgen j
  dsimp only [mu] at hcond
  rw [hpow] at hcond
  simpa [Nat.max_eq_right hLow] using hcond

noncomputable def lowNonzeroTwistDatum
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hLow : chi.conductor ≤ t + 1)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0) :
    LocalQuasiCharData F :=
  quasiCharDataOfIsConductor F
    ((lowNormCharacterGenerator F K ht hres pi hpi hgen ^ j.val).1 *
      chi.character) (t + 1)
    (lowGeneratorPowerTwist_isConductor F K ht hres pi hpi hgen
      chi hminimal hLow j hj)

@[simp]
theorem lowNonzeroTwistDatum_conductor
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hLow : chi.conductor ≤ t + 1)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0) :
    (lowNonzeroTwistDatum F K ht hres pi hpi hgen
      chi hminimal hLow j hj).conductor = t + 1 := rfl

theorem lowNonzeroTwistDatum_eq_actual
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hLow : chi.conductor ≤ t + 1)
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0) :
    lowNonzeroTwistDatum F K ht hres pi hpi hgen
        chi hminimal hLow j hj =
      ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chi
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j)) := by
  apply LocalQuasiCharData.ext_character
  rw [ramifiedNormCharacterOrbitTwistData_character]
  exact congrArg (fun mu : NormCharacter F K ↦ mu.1 * chi.character)
    (lowNormCharacterGenerator_pow F K ht hres pi hpi hgen j).symm

private theorem lowPrimeTeichmuller_order_zero
    (p : ℕ) [Fact p.Prime]
    (hchar : residueCharacteristic F = p)
    (j : ZMod p) (hj : j ≠ 0) :
    ord F (((primeTeichmuller F p hchar j : ringOfIntegers F) : F)) =
      (0 : WithTop ℤ) := by
  have hinj : Function.Injective (primeTeichmuller F p hchar) :=
    (teichmuller_injective F).comp
      (ZMod.castHom (by simpa [residueCharacteristic, hchar])
        (ResidueField F)).injective
  have hjR : primeTeichmuller F p hchar j ≠ 0 := by
    intro hzero
    apply hj
    apply hinj
    simpa using hzero
  have hjF : (((primeTeichmuller F p hchar j : ringOfIntegers F) : F)) ≠ 0 := by
    exact fun hzero ↦ hjR (Subtype.ext hzero)
  have hpow := congrArg (ord F)
    (congrArg (fun z : ringOfIntegers F ↦ (z : F))
      (primeTeichmuller_pow_residueCharacteristic F p hchar j))
  change ord F
      ((((primeTeichmuller F p hchar j : ringOfIntegers F) : F)) ^ p) =
    ord F (((primeTeichmuller F p hchar j : ringOfIntegers F) : F)) at hpow
  rw [ord_pow] at hpow
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff F).2 hjF)
  rw [← hz, ← WithTop.coe_nsmul] at hpow
  have hzEq : p • z = z := WithTop.coe_injective hpow
  rw [nsmul_eq_mul] at hzEq
  have hp := (Fact.out : p.Prime).two_le
  have : z = 0 := by
    nlinarith
  rw [← hz, this]
  rfl

theorem lowTwistNorm_congruent_primeTeichmuller
    {t v : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (hchar : residueCharacteristic F = Module.finrank F K)
    [Fact (Module.finrank F K).Prime]
    (epsilon₁ alpha₁ beta₁ : Kˣ)
    (hepsilon₁ : ord K (epsilon₁ : K) = ((v : ℕ) : WithTop ℤ))
    (halpha₁ : ord K (alpha₁ : K) = (0 : WithTop ℤ))
    (hbeta₁ : ord K (beta₁ : K) = (0 : WithTop ℤ))
    (j : ZMod (Module.finrank F K)) :
    let omega : F :=
      ((primeTeichmuller F (Module.finrank F K) hchar j :
        ringOfIntegers F) : F)
    CongruentAtDepth (lowCriticalFloorDepth t : ℤ)
      (norm F K
        (algebraMap F K omega * (alpha₁ : K) +
          (epsilon₁ : K) * (beta₁ : K)))
      (omega * (normUnits F K alpha₁ : F) +
        (lowEpsilon F K epsilon₁ : F) * (normUnits F K beta₁ : F)) := by
  dsimp only
  let p := Module.finrank F K
  let omega : F :=
    ((primeTeichmuller F p hchar j : ringOfIntegers F) : F)
  by_cases hj : j = 0
  · subst j
    have heq :
        norm F K
            (algebraMap F K omega * (alpha₁ : K) +
              (epsilon₁ : K) * (beta₁ : K)) =
          omega * (normUnits F K alpha₁ : F) +
            (lowEpsilon F K epsilon₁ : F) *
              (normUnits F K beta₁ : F) := by
      simp [omega, primeTeichmuller, map_mul, lowEpsilon, coe_normUnits]
    rw [heq]
    exact CongruentAtDepth.refl _
  · letI : Fact p.Prime := inferInstance
    have hjord : ord F omega = (0 : WithTop ℤ) := by
      exact lowPrimeTeichmuller_order_zero F p hchar j hj
    have hj0 : omega ≠ 0 := (ord_ne_top_iff F).1 (by
      rw [hjord]
      exact WithTop.coe_ne_top)
    have hjpow : omega ^ Module.finrank F K = omega := by
      have h := congrArg (fun z : ringOfIntegers F ↦ (z : F))
        (primeTeichmuller_pow_residueCharacteristic F p hchar j)
      change omega ^ p = omega at h
      simpa only [p] using h
    have hram : ramificationIndex F K = Module.finrank F K := by
      have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
      rw [hres, mul_one] at hdegree
      exact hdegree.symm
    have hnorma : norm F K
        (algebraMap F K omega * (alpha₁ : K)) ∈ lattice F 0 := by
      rw [mem_lattice, map_mul, ord_mul, ord_norm, hres, one_nsmul,
        ord_norm, hres, one_nsmul, ord_algebraMap, hram, hjord, halpha₁]
      simp
    have hw : ((v : ℕ) : WithTop ℤ) ≤
        ord K ((epsilon₁ : K) * (beta₁ : K) /
          (algebraMap F K omega * (alpha₁ : K))) := by
      rw [ord_div, ord_mul, ord_mul, ord_algebraMap, hram, hjord,
        hepsilon₁, hbeta₁, halpha₁]
      simp
    have h := lowTwistNorm_congruent F K ht hres pi hpi hgen htpos
      alpha₁ epsilon₁ beta₁ omega hj0 hjpow hnorma hw
    simpa [p, omega, lowCriticalFloorDepth, coe_normUnits,
      lowEpsilon_coe] using h

def lowUpstairsCandidate
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : K :=
  algebraMap F K (P.beta : F) *
      algebraMap F K (lowEpsilon F K epsilon₁ : F) / (epsilon₁ : K) -
    (P.beta₁ : K) * algebraMap F K (P.alpha : F) / (P.alpha₁ : K)

def lowNormalizedRatio
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : K :=
  (epsilon₁ : K) * (P.beta₁ : K) / (P.alpha₁ : K)

def lowNormalizedUpstairsCandidate
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : K :=
  algebraMap F K (P.alpha : F) / (epsilon₁ : K) *
    (algebraMap F K (norm F K (lowNormalizedRatio F K epsilon₁ P)) -
      lowNormalizedRatio F K epsilon₁ P)

theorem lowNormalizedRatio_order
    {r d v : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (hepsilon₁ : ord K (epsilon₁ : K) = ((v : ℕ) : WithTop ℤ))
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    ord K (lowNormalizedRatio F K epsilon₁ P) =
      ((v : ℕ) : WithTop ℤ) := by
  rw [lowNormalizedRatio, ord_div, ord_mul, hepsilon₁,
    P.betaRepresentative.source_order, P.alphaRepresentative.source_order]
  simp

theorem lowNormalizedRatio_norm
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    norm F K (lowNormalizedRatio F K epsilon₁ P) =
      (lowEpsilon F K epsilon₁ : F) * (P.beta : F) / (P.alpha : F) := by
  simp only [lowNormalizedRatio, div_eq_mul_inv, map_mul, Algebra.norm_inv,
    lowEpsilon_coe, LowStationaryNormRepresentativePair.alpha,
    LowStationaryNormRepresentativePair.beta, coe_normUnits]

theorem lowUpstairsCandidate_eq_normalized
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    lowUpstairsCandidate F K epsilon₁ P =
      lowNormalizedUpstairsCandidate F K epsilon₁ P := by
  rw [lowUpstairsCandidate, lowNormalizedUpstairsCandidate,
    lowNormalizedRatio_norm]
  dsimp only [lowNormalizedRatio]
  simp only [map_div₀, map_mul]
  field_simp [Units.ne_zero epsilon₁, Units.ne_zero P.alpha₁,
    Units.ne_zero P.alpha, Units.ne_zero P.beta,
    Units.ne_zero (lowEpsilon F K epsilon₁)]

theorem norm_lowNormalizedUpstairsCandidate
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon₁ : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    norm F K (lowNormalizedUpstairsCandidate F K epsilon₁ P) =
      ((P.alpha : F) ^ Module.finrank F K /
          (lowEpsilon F K epsilon₁ : F)) *
        norm F K
          (algebraMap F K (norm F K (lowNormalizedRatio F K epsilon₁ P)) -
            lowNormalizedRatio F K epsilon₁ P) := by
  rw [lowNormalizedUpstairsCandidate, map_mul, div_eq_mul_inv, map_mul,
    norm_algebraMap, Algebra.norm_inv, lowEpsilon_coe]
  field_simp [Algebra.norm_ne_zero_iff.mpr (Units.ne_zero epsilon₁)]

theorem lowIdentityCommonClass_ofPair
    {t d epsilon : ℕ}
    (chi : LocalQuasiCharData F)
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hLow : chi.conductor ≤ t + 1)
    (epsilon₁ : Kˣ)
    (hres : residueDegree F K = 1)
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (betaClass : StationaryCoefficientQuotient F d)
    {alphaClass : StationaryCoefficientQuotient F (lowCriticalFloorDepth t)}
    (P : LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d alphaClass betaClass) :
    lowIdentityCommonClass (F := F) (K := K) (t := t)
        hF hLow (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁)
        betaClass =
      latticeQuotientMk F (by omega)
        (lowIdentityCommonRepresentative (t := t) F hF hLow
          (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁)
          (⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩ :
            lattice F 0)) := by
  let b : lattice F 0 :=
    ⟨(P.beta : F), by
      simpa [LowStationaryNormRepresentativePair.beta, coe_normUnits] using
        P.betaRepresentative.norm_exactDepth.1⟩
  have hb : latticeQuotientMk F (by omega) b = betaClass := by
    simpa [b] using P.beta_norm_class
  calc
    lowIdentityCommonClass (F := F) (K := K) (t := t)
        hF hLow (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁) betaClass =
      lowIdentityCommonClass (F := F) (K := K) (t := t)
        hF hLow (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁)
          (latticeQuotientMk F (by omega) b) := congrArg _ hb.symm
    _ = latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (lowIdentityCommonRepresentative (t := t) F hF hLow
          (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁) b) :=
      lowIdentityCommonClass_mk (F := F) (K := K) hF hLow
        (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁) b

theorem lowNonzeroTwistClass_ofPair
    {t d epsilon : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hLow : chi.conductor ≤ t + 1)
    (delta : Fˣ) (epsilon₁ : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (j : ZMod (Module.finrank F K)) (hj : j ≠ 0)
    (hchar : residueCharacteristic F = Module.finrank F K)
    [Fact (Module.finrank F K).Prime]
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon₁ : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (P : LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d
      (stationaryCoefficientClass F
        (quasiCharDataOfIsConductor F
          (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
            (lowNormCharacterGenerator F K ht hres pi hpi hgen)
            (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
        psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
      (stationaryCoefficientClass F chi psi hF
        (lowGammaF F K delta epsilon₁) hgammaF)) :
    let omega : F :=
      ((primeTeichmuller F (Module.finrank F K) hchar j :
        ringOfIntegers F) : F)
    ∃ haff : omega * (P.alpha : F) +
        (lowEpsilon F K epsilon₁ : F) * (P.beta : F) ∈ lattice F 0,
      latticeQuotientMk F (by omega)
          ⟨omega * (P.alpha : F) +
            (lowEpsilon F K epsilon₁ : F) * (P.beta : F), haff⟩ =
        stationaryCoefficientClass F
          (lowNonzeroTwistDatum F K ht hres pi hpi hgen
            chi hminimal hLow j hj)
          psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta := by
  dsimp only
  let p := Module.finrank F K
  letI : Fact p.Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 := lowNormCharacterGenerator_ne_one
    F K ht hres pi hpi hgen
  let eta := lowEpsilon F K epsilon₁
  have heta : ord F (eta : F) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) :=
    lowEpsilon_order F K hres epsilon₁ hepsilon₁
  have halpha : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  have hbeta : ord F (P.beta : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.beta, coe_normUnits] using
      P.betaRepresentative.norm_order
  let omega : F :=
    ((primeTeichmuller F p hchar j : ringOfIntegers F) : F)
  have homega : omega ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (primeTeichmuller F p hchar j).property
  have halphaMem := (mem_lattice_and_not_mem_succ_iff F).2 halpha |>.1
  have hbetaMem := (mem_lattice_and_not_mem_succ_iff F).2 hbeta |>.1
  have hetaMem : (eta : F) ∈ lattice F 0 := by
    rw [mem_lattice, heta]
    simp
  have haff : omega * (P.alpha : F) + (eta : F) * (P.beta : F) ∈
      lattice F 0 := by
    apply add_mem
    · simpa only [zero_add] using mul_mem_lattice F homega halphaMem
    · simpa only [zero_add] using mul_mem_lattice F hetaMem hbetaMem
  refine ⟨haff, ?_⟩
  have hjpow := lowGeneratorPower_ne_one F K ht hres pi hpi hgen j hj
  have hprod := lowGeneratorPowerTwist_isConductor
    F K ht hres pi hpi hgen chi hminimal hLow j hj
  have hcommon := lowNonzeroTwistCommonClass F K ht hres pi hpi hgen
    chi psi tau htau hF hLow delta (lowGammaF F K delta epsilon₁) eta
      hdelta hgammaF heta (by
        simpa [eta, lowGammaF, mul_comm])
      j.val hjpow hprod
  have hcommon' :
      stationaryCoefficientClass F
          (lowNonzeroTwistDatum F K ht hres pi hpi hgen
            chi hminimal hLow j hj)
          psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta =
        j.val • stationaryCoefficientClass F
            (quasiCharDataOfIsConductor F tau.1 (t + 1)
              (ramifiedNormCharacter_conductor
                F K ht hres pi hpi hgen tau htau))
            psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta +
          lowIdentityCommonClass (F := F) (K := K) (t := t)
            hF hLow eta heta
            (stationaryCoefficientClass F chi psi hF
              (lowGammaF F K delta epsilon₁) hgammaF) := by
    simpa [lowNonzeroTwistDatum, tau] using hcommon
  have hteich := lowTeichmuller_nsmul_class F K p ht hres pi hpi hgen
    rfl hchar j P.alpha halpha
  have hteich' :
      latticeQuotientMk F (by omega)
          (⟨omega * (P.alpha : F), by
            simpa only [zero_add] using
              mul_mem_lattice F homega halphaMem⟩ : lattice F 0) =
        j.val • stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen tau htau))
          psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta := by
    calc
      _ = j.val • latticeQuotientMk F (by omega)
          (⟨(P.alpha : F), halphaMem⟩ : lattice F 0) := by
        simpa [omega, p] using hteich
      _ = _ := congrArg (fun z ↦ j.val • z) P.alpha_norm_class
  have hidentity := lowIdentityCommonClass_ofPair F K chi hF hLow
    epsilon₁ hres hepsilon₁
    (stationaryCoefficientClass F chi psi hF
      (lowGammaF F K delta epsilon₁) hgammaF) P
  have hidentity' :
      lowIdentityCommonClass (F := F) (K := K) (t := t)
          hF hLow eta heta
          (stationaryCoefficientClass F chi psi hF
            (lowGammaF F K delta epsilon₁) hgammaF) =
        latticeQuotientMk F (by omega)
          (⟨(eta : F) * (P.beta : F), by
            simpa only [zero_add] using
              mul_mem_lattice F hetaMem hbetaMem⟩ : lattice F 0) := by
    simpa [eta, lowIdentityCommonRepresentative] using hidentity
  let ca : lattice F 0 :=
    ⟨omega * (P.alpha : F), by
      simpa only [zero_add] using mul_mem_lattice F homega halphaMem⟩
  let cb : lattice F 0 :=
    ⟨(eta : F) * (P.beta : F), by
      simpa only [zero_add] using mul_mem_lattice F hetaMem hbetaMem⟩
  calc
    latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        ⟨omega * (P.alpha : F) + (eta : F) * (P.beta : F), haff⟩ =
      latticeQuotientMk F
        (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega)
        (ca + cb) := by
        congr 1
    _ = latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) ca +
        latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) cb :=
      latticeQuotientMk_add F _ ca cb
    _ = j.val • stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen tau htau))
          psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta +
        lowIdentityCommonClass (F := F) (K := K) (t := t)
          hF hLow eta heta
          (stationaryCoefficientClass F chi psi hF
            (lowGammaF F K delta epsilon₁) hgammaF) := by
      rw [show latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) ca =
          j.val • stationaryCoefficientClass F
            (quasiCharDataOfIsConductor F tau.1 (t + 1)
              (ramifiedNormCharacter_conductor
                F K ht hres pi hpi hgen tau htau))
            psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta by
            simpa [ca] using hteich',
        show latticeQuotientMk F
          (show (0 : ℤ) ≤ (lowCriticalFloorDepth t : ℤ) by omega) cb =
          lowIdentityCommonClass (F := F) (K := K) (t := t)
            hF hLow eta heta
            (stationaryCoefficientClass F chi psi hF
              (lowGammaF F K delta epsilon₁) hgammaF) by
            simpa [cb] using hidentity'.symm]
    _ = stationaryCoefficientClass F
          (lowNonzeroTwistDatum F K ht hres pi hpi hgen
            chi hminimal hLow j hj)
          psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta :=
      hcommon'.symm

/-- The norm of the upstairs stationary numerator class is independent of
its supplied representative at exactly the manuscript's depth `d`.  The
result is a congruence, not a field equality. -/
theorem lowUpstairsStationaryNorm_representatives_independent
    {t d epsilon : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1)
    (gammaK : Kˣ)
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (b b' : lattice K 0)
    (hb : latticeQuotientMk K (by omega) b =
      stationaryCoefficientClass K chiK psiK
        (lowNormPolynomialPrecision F K ht hres pi hpi hgen
          chiF hminimal chiK hchi hF hLow).sourceDecomposition
        gammaK hgammaK)
    (hb' : latticeQuotientMk K (by omega) b' =
      stationaryCoefficientClass K chiK psiK
        (lowNormPolynomialPrecision F K ht hres pi hpi hgen
          chiF hminimal chiK hchi hF hLow).sourceDecomposition
        gammaK hgammaK) :
    CongruentAtDepth (d : ℤ)
      (norm F K (b : K)) (norm F K (b' : K)) := by
  let hprecision := lowNormPolynomialPrecision F K ht hres pi hpi hgen
    chiF hminimal chiK hchi hF hLow
  have hbord : ord K (b : K) = (0 : WithTop ℤ) :=
    stationaryCoefficientClass_representative_ord_zero F K K chiK psiK
      hprecision.sourceDecomposition gammaK hgammaK b hb
  have hb'ord : ord K (b' : K) = (0 : WithTop ℤ) :=
    stationaryCoefficientClass_representative_ord_zero F K K chiK psiK
      hprecision.sourceDecomposition gammaK hgammaK b' hb'
  have hb0 : (b : K) ≠ 0 :=
    (ord_ne_top_iff K).1 (by rw [hbord]; exact WithTop.coe_ne_top)
  have hb'0 : (b' : K) ≠ 0 :=
    (ord_ne_top_iff K).1 (by rw [hb'ord]; exact WithTop.coe_ne_top)
  let bu : Kˣ := Units.mk0 (b : K) hb0
  let bu' : Kˣ := Units.mk0 (b' : K) hb'0
  have hbu : bu ∈ unitFiltration K 0 := by
    rw [mem_unitFiltration_zero]
    simpa [bu] using hbord
  have hbu' : bu' ∈ unitFiltration K 0 := by
    rw [mem_unitFiltration_zero]
    simpa [bu'] using hb'ord
  have hbb : CongruentAtDepth (d : ℤ) (bu : K) (bu' : K) := by
    rw [CongruentAtDepth]
    simpa [bu, bu'] using
      (latticeQuotientMk_eq_mk_iff K
        (show (0 : ℤ) ≤ (d : ℤ) by omega)).1 (hb.trans hb'.symm)
  have hnorm := stationaryNormClass_representative_independent F K d d
    hprecision.ambiguity_inclusion
    (⟨bu, hbu⟩ : unitFiltration K 0)
    (⟨bu', hbu'⟩ : unitFiltration K 0) hbb
  simpa [bu, bu', coe_normUnits] using hnorm

local instance lowFinrankPrimeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

structure LowConductorParameterTableData
    {t d epsilon : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1)
    (delta : Fˣ) (epsilon₁ : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon₁ : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (lowGammaK F K delta epsilon₁ : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (P : LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d
      (stationaryCoefficientClass F
        (quasiCharDataOfIsConductor F
          (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
            (lowNormCharacterGenerator F K ht hres pi hpi hgen)
            (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
        psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
      (stationaryCoefficientClass F chiF psiF hF
        (lowGammaF F K delta epsilon₁) hgammaF)) : Prop where
  exact_twist_conductors : ∀ mu : NormCharacter F K,
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu).conductor =
      lowTwistConductor (t := t) F K chiF mu
  pullback_conductor : chiK.conductor = chiF.conductor
  simultaneous_precisions : lowCriticalFloorDepth t ≤ t ∧ d ≤ t
  alpha_native_class :
    latticeQuotientMk F (by omega)
        (⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩ :
          lattice F 0) =
      stationaryCoefficientClass F
        (quasiCharDataOfIsConductor F
          (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
            (lowNormCharacterGenerator F K ht hres pi hpi hgen)
            (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
        psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta
  beta_native_class :
    latticeQuotientMk F (by omega)
        (⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩ :
          lattice F 0) =
      stationaryCoefficientClass F chiF psiF hF
        (lowGammaF F K delta epsilon₁) hgammaF
  upstairs_class : ∃ hcand : lowUpstairsCandidate F K epsilon₁ P ∈ lattice K 0,
    latticeQuotientMk K (by omega)
        ⟨lowUpstairsCandidate F K epsilon₁ P, hcand⟩ =
      stationaryCoefficientClass K chiK psiK
        (lowNormPolynomialPrecision F K ht hres pi hpi hgen
          chiF hminimal chiK hchi hF hLow).sourceDecomposition
        (lowGammaK F K delta epsilon₁) hgammaK
  upstairs_norm_independent : ∀ (b b' : lattice K 0),
    latticeQuotientMk K (by omega) b =
        stationaryCoefficientClass K chiK psiK
          (lowNormPolynomialPrecision F K ht hres pi hpi hgen
            chiF hminimal chiK hchi hF hLow).sourceDecomposition
          (lowGammaK F K delta epsilon₁) hgammaK →
      latticeQuotientMk K (by omega) b' =
        stationaryCoefficientClass K chiK psiK
          (lowNormPolynomialPrecision F K ht hres pi hpi hgen
            chiF hminimal chiK hchi hF hLow).sourceDecomposition
          (lowGammaK F K delta epsilon₁) hgammaK →
      CongruentAtDepth (d : ℤ)
        (norm F K (b : K)) (norm F K (b' : K))
  identity_common_class :
    lowIdentityCommonClass (F := F) (K := K) (t := t)
        hF hLow (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁)
        (stationaryCoefficientClass F chiF psiF hF
          (lowGammaF F K delta epsilon₁) hgammaF) =
      latticeQuotientMk F (by omega)
        (lowIdentityCommonRepresentative (t := t) F hF hLow
          (lowEpsilon F K epsilon₁)
          (lowEpsilon_order F K hres epsilon₁ hepsilon₁)
          (⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩ :
            lattice F 0))
  nonzero_twist_class : ∀
      (j : ZMod (Module.finrank F K)) (hj : j ≠ 0),
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    let omega : F :=
      ((primeTeichmuller F (Module.finrank F K) hchar j :
        ringOfIntegers F) : F)
    ∃ haff : omega * (P.alpha : F) +
        (lowEpsilon F K epsilon₁ : F) * (P.beta : F) ∈ lattice F 0,
      latticeQuotientMk F (by omega)
          ⟨omega * (P.alpha : F) +
            (lowEpsilon F K epsilon₁ : F) * (P.beta : F), haff⟩ =
        stationaryCoefficientClass F
          (lowNonzeroTwistDatum F K ht hres pi hpi hgen
            chiF hminimal hLow j hj)
          psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta
  twist_norm : ∀ j : ZMod (Module.finrank F K),
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    let omega : F :=
      ((primeTeichmuller F (Module.finrank F K) hchar j :
        ringOfIntegers F) : F)
    CongruentAtDepth (lowCriticalFloorDepth t : ℤ)
      (norm F K
        (algebraMap F K omega * (P.alpha₁ : K) +
          (epsilon₁ : K) * (P.beta₁ : K)))
      (omega * (P.alpha : F) +
        (lowEpsilon F K epsilon₁ : F) * (P.beta : F))
  normalized_ratio_order :
    ord K (lowNormalizedRatio F K epsilon₁ P) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ)
  normalized_ratio_norm :
    norm F K (lowNormalizedRatio F K epsilon₁ P) =
      (lowEpsilon F K epsilon₁ : F) * (P.beta : F) / (P.alpha : F)
  product_congruence :
    let hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
    CongruentAtDepth (d : ℤ)
      (norm F K (lowUpstairsCandidate F K epsilon₁ P))
      ((P.beta : F) * ∏ j : (ZMod (Module.finrank F K))ˣ,
        ((lowEpsilon F K epsilon₁ : F) * (P.beta : F) +
          (((primeTeichmuller F (Module.finrank F K) hchar
            (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)) *
              (P.alpha : F)))

set_option maxHeartbeats 4000000 in
/-- The low-conductor parameter table selects coherent stationary
representatives and packages the exact norm, ratio, and product congruences
required by the Low branch from the minimal norm-orbit data. -/
theorem lowConductorParameterTable
    {t d epsilon : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hLow : chiF.conductor ≤ t + 1)
    (delta : Fˣ) (epsilon₁ : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hepsilon₁ : ord K (epsilon₁ : K) =
      (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ)) :
    let hT : 2 ≤ t + 1 := by
      have hm := hF.conductor_gt_one
      omega
    let gammaF := lowGammaF F K delta epsilon₁
    let gammaK := lowGammaK F K delta epsilon₁
    let hgammaF := lowGammaF_order (t := t) F K hres
      chiF psiF delta epsilon₁ hdelta hepsilon₁ hLow
    let hgammaK := lowGammaK_order F K ht hres pi hpi hgen
      chiF chiK psiF psiK hminimal hchi hpsi delta epsilon₁
        hdelta hepsilon₁ hLow
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    ∃ P : LowStationaryNormRepresentativePair F K
        (lowCriticalFloorDepth t) d
        (stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
              (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
          psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF),
      LowConductorParameterTableData F K ht hres pi hpi hgen
        chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon₁
          hdelta hepsilon₁ hT hgammaF hgammaK P := by
  dsimp only
  let hT : 2 ≤ t + 1 := by
    have hm := hF.conductor_gt_one
    omega
  let gammaF := lowGammaF F K delta epsilon₁
  let gammaK := lowGammaK F K delta epsilon₁
  let hgammaF := lowGammaF_order (t := t) F K hres
    chiF psiF delta epsilon₁ hdelta hepsilon₁ hLow
  let hgammaK := lowGammaK_order F K ht hres pi hpi hgen
    chiF chiK psiF psiK hminimal hchi hpsi delta epsilon₁
      hdelta hepsilon₁ hLow
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 := lowNormCharacterGenerator_ne_one
    F K ht hres pi hpi hgen
  obtain ⟨P⟩ := lowSimultaneousStationaryNormRepresentatives
    F K ht hres pi hpi hgen chiF psiF tau htau hF hLow delta gammaF
      hdelta hgammaF
  refine ⟨P, ?_⟩
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩
  have htpos : 0 < t := by
    have hm := hF.conductor_gt_one
    omega
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos pi hpi hgen
  have halpha : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  have heta := lowEpsilon_order F K hres epsilon₁ hepsilon₁
  have hu := lowNormalizedRatio_order F K epsilon₁ hepsilon₁ P
  have hn := lowNormalizedRatio_norm F K epsilon₁ P
  have hprecision := lowNormPolynomialPrecision F K ht hres pi hpi hgen
    chiF hminimal chiK hchi hF hLow
  have hup := lowUpstairsStationaryClass_ofPair F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hLow hprecision hchi hpsi tau htau hT
      epsilon₁ delta hdelta hepsilon₁ hgammaF hgammaK P
  have hprod := lowPrimeTeichmullerNormalizedNorm_product_congruent
    F K ht hres pi hpi hgen htpos hF.conductor_eq hF.epsilon_le_one
      hLow rfl hchar P.alpha (lowEpsilon F K epsilon₁) P.beta
      (lowNormalizedRatio F K epsilon₁ P) halpha heta hu hn
  have hnorm := norm_lowNormalizedUpstairsCandidate F K epsilon₁ P
  have hcand := lowUpstairsCandidate_eq_normalized F K epsilon₁ P
  have hprod' : CongruentAtDepth (d : ℤ)
      (norm F K (lowUpstairsCandidate F K epsilon₁ P))
      ((P.beta : F) * ∏ j : (ZMod (Module.finrank F K))ˣ,
        ((lowEpsilon F K epsilon₁ : F) * (P.beta : F) +
          (((primeTeichmuller F (Module.finrank F K) hchar
            (j : ZMod (Module.finrank F K)) : ringOfIntegers F) : F)) *
              (P.alpha : F))) := by
    rw [hcand, hnorm]
    exact hprod
  exact
    { exact_twist_conductors := fun mu ↦
        lowTwist_conductor_eq F K ht hres pi hpi hgen
          chiF hminimal hLow mu
      pullback_conductor :=
        lowCompNorm_conductor_eq F K ht hres pi hpi hgen
          chiF hminimal chiK hchi hLow
      simultaneous_precisions := lowConductor_subcriticalDepths
        (t := t) hF hLow
      alpha_native_class := P.alpha_norm_class
      beta_native_class := P.beta_norm_class
      upstairs_class := by
        simpa [lowUpstairsCandidate, gammaK] using hup
      upstairs_norm_independent := fun b b' hb hb' ↦
        lowUpstairsStationaryNorm_representatives_independent F K
          ht hres pi hpi hgen chiF chiK psiK hminimal hchi hF hLow
            gammaK hgammaK b b' hb hb'
      identity_common_class := lowIdentityCommonClass_ofPair
        F K chiF hF hLow epsilon₁ hres hepsilon₁
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) P
      nonzero_twist_class := by
        intro j hj
        exact lowNonzeroTwistClass_ofPair F K ht hres pi hpi hgen
          chiF psiF hminimal hF hLow delta epsilon₁ hdelta hepsilon₁
            j hj hchar hT hgammaF P
      twist_norm := by
        intro j
        exact lowTwistNorm_congruent_primeTeichmuller F K
          ht hres pi hpi hgen htpos hchar epsilon₁ P.alpha₁ P.beta₁
            hepsilon₁ P.alphaRepresentative.source_order
              P.betaRepresentative.source_order j
      normalized_ratio_order := hu
      normalized_ratio_norm := hn
      product_congruence := hprod' }

end

end LanglandsFirstMainLemma
