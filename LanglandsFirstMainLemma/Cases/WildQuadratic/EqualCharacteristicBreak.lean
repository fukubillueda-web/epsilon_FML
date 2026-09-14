import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier

/-!
# Equal-characteristic quadratic break parity

For a totally ramified quadratic extension in characteristic two, this file follows the
manuscript's reduced Artin--Schreier argument.  A minimal negative-order parameter cannot have
even pole order: on the corresponding graded piece the leading term of the Artin--Schreier
operator is Frobenius, and a residue-field square root supplies a translation which cancels that
term.  The resulting odd pole is then compared directly with the integer-indexed lower
ramification filtration.
-/

noncomputable section

namespace LanglandsFirstMainLemma

open scoped Matrix

/-- A quadratic Galois extension in characteristic two admits an Artin--Schreier generator with
the manuscript's orientation `y ^ 2 - y = a` and nontrivial automorphism `y ↦ y + 1`. -/
private theorem exists_artinSchreier_generator
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [CharP F 2]
    (hdegree : Module.finrank F K = 2) :
    ∃ (sigma : Gal(K/F)) (y : K) (a : F), sigma ≠ 1 ∧
      sigma y = y + 1 ∧ y ^ 2 - y = algebraMap F K a := by
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  have hcard : Nat.card Gal(K/F) = 2 :=
    (IsGalois.card_aut_eq_finrank F K).trans hdegree
  obtain ⟨sigma, hsigma, hsigma_unique⟩ :=
    (Nat.card_eq_two_iff' (1 : Gal(K/F))).mp hcard
  have hsigma_sq : sigma * sigma = 1 := by
    by_contra hne
    have heq : sigma * sigma = sigma := hsigma_unique (sigma * sigma) hne
    apply hsigma
    have heq' := congrArg (fun tau : Gal(K/F) => sigma.symm * tau) heq
    simpa using heq'
  obtain ⟨z, hz⟩ : ∃ z : K, sigma z ≠ z := by
    by_contra h
    push Not at h
    apply hsigma
    ext x
    simpa using h x
  let delta : K := sigma z - z
  have hdelta0 : delta ≠ 0 := sub_ne_zero.mpr hz
  have hsigma_delta : sigma delta = delta := by
    dsimp only [delta]
    rw [map_sub, ← AlgEquiv.mul_apply, hsigma_sq]
    change z - sigma z = sigma z - z
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  have hdelta_fixed : ∀ tau : Gal(K/F), tau delta = delta := by
    intro tau
    by_cases htau : tau = 1
    · subst tau
      rfl
    · rw [hsigma_unique tau htau]
      exact hsigma_delta
  obtain ⟨d, hd⟩ : ∃ d : F, algebraMap F K d = delta :=
    (IsGalois.mem_range_algebraMap_iff_fixed delta).mpr hdelta_fixed
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hdelta0
    rw [← hd, hd0, map_zero]
  let y : K := z / algebraMap F K d
  have hy : sigma y = y + 1 := by
    dsimp only [y]
    rw [map_div₀, sigma.commutes, hd]
    field_simp [hdelta0]
    dsimp only [delta]
    ring
  have hparameter_fixed : ∀ tau : Gal(K/F), tau (y ^ 2 - y) = y ^ 2 - y := by
    intro tau
    by_cases htau : tau = 1
    · simp [htau]
    · rw [hsigma_unique tau htau, map_sub, map_pow, hy]
      simp only [CharTwo.sub_eq_add]
      ring_nf
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have hthree : (3 : K) = 1 := by
        calc
          (3 : K) = 2 + 1 := by norm_num
          _ = 1 := by rw [htwo, zero_add]
      rw [htwo, hthree, zero_add, mul_one]
  obtain ⟨a, ha⟩ : ∃ a : F, algebraMap F K a = y ^ 2 - y :=
    (IsGalois.mem_range_algebraMap_iff_fixed (y ^ 2 - y)).mpr hparameter_fixed
  exact ⟨sigma, y, a, hsigma, hy, ha.symm⟩

/-- If `sigma` is in inertia and sends an Artin--Schreier generator to `y + 1`, then both the
generator and its parameter have the same strictly negative normalized order. -/
private theorem artinSchreier_parameter_negative
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K]
    (sigma : Gal(K/F)) (hram : ramificationIndex F K = 2)
    (hsigma0 : sigma ∈ lowerRamificationGroup F K 0)
    (y : K) (a : F) (hy : sigma y = y + 1)
    (ha : y ^ 2 - y = algebraMap F K a) :
    ∃ n : ℤ, n < 0 ∧ ord K y = (n : WithTop ℤ) ∧
      ord F a = (n : WithTop ℤ) := by
  have hy0 : y ≠ 0 := by
    intro hy0
    have h := hy
    simp [hy0] at h
  have hynotint : ¬ 0 ≤ ord K y := by
    intro hyint
    let yO : ringOfIntegers K :=
      ⟨y, (ord_nonneg_iff_mem_integer K y).mp hyint⟩
    have hcong := (mem_lowerRamificationGroup_iff_ord F K sigma 0).mp hsigma0 yO
    have hdiff : sigma (yO : K) - (yO : K) = 1 := by
      change sigma y - y = 1
      rw [hy]
      ring
    rw [hdiff, ord_one] at hcong
    have hfalse : ¬ (((1 : ℤ) : WithTop ℤ) ≤ 0) := by norm_num
    exact hfalse hcong
  have hyord_ne_top : ord K y ≠ ⊤ := (ord_ne_top_iff K).mpr hy0
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hyord_ne_top
  have hnneg : n < 0 := by
    rw [← hn] at hynotint
    simpa using hynotint
  have hyord : ord K y = (n : WithTop ℤ) := hn.symm
  have hy2ord : ord K (y ^ 2) = ((2 * n : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hyord, ← WithTop.coe_nsmul]
    congr 1
  have hnegord : ord K (-y) = (n : WithTop ℤ) := by simp [hyord]
  have hdistinct : ord K (y ^ 2) ≠ ord K (-y) := by
    intro h
    rw [hy2ord, hnegord] at h
    simp only [WithTop.coe_eq_coe] at h
    omega
  have hparameterK :
      ord K (algebraMap F K a) = ((2 * n : ℤ) : WithTop ℤ) := by
    rw [← ha, show y ^ 2 - y = y ^ 2 + -y by ring,
      ord_add_eq_min K hdistinct, hy2ord, hnegord]
    rw [min_eq_left]
    simp only [WithTop.coe_le_coe]
    omega
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, map_zero, ord_zero] at hparameterK
    exact WithTop.top_ne_coe hparameterK
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff F).mpr ha0)
  have hm' : ord F a = (m : WithTop ℤ) := hm.symm
  rw [ord_algebraMap, hram, hm', ← WithTop.coe_nsmul] at hparameterK
  have hmn : m = n := by
    simp only [WithTop.coe_eq_coe] at hparameterK
    norm_num [nsmul_eq_mul] at hparameterK
    omega
  exact ⟨n, hnneg, hyord, by simpa [hmn] using hm'⟩

/-- At an even pole, the leading graded Artin--Schreier term is a square.  The unique residue
square root supplied by the finite-field Artin--Schreier file lifts to a translation which
strictly improves the parameter order. -/
private theorem improve_even_artinSchreier_pole
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharP F 2]
    (pi : F) (hpi : (ValuativeRel.valuation F).IsUniformizer pi)
    (a : F) (r q : ℕ) (hrpos : 0 < r) (hr : r = q + q)
    (ha : ord F a = ((-(r : ℤ) : ℤ) : WithTop ℤ)) :
    ∃ c : F, ord F c = ((-(q : ℤ) : ℤ) : WithTop ℤ) ∧
      ((-(r : ℤ) : ℤ) : WithTop ℤ) < ord F (a - (c ^ 2 - c)) := by
  letI : CharP (ringOfIntegers F) 2 :=
    (SubringClass.subtype (ringOfIntegers F)).charP
      (fun x y hxy ↦ Subtype.ext hxy) 2
  letI : CharP (ResidueField F) 2 :=
    CharP.of_ringHom_of_ne_zero (residueMap F) 2 (by norm_num)
  letI : Fintype (ResidueField F) := residueFieldFintype F
  have hqpos : 0 < q := by omega
  have hpi0 : pi ≠ 0 :=
    (ord_ne_top_iff F).mp (by rw [ord_uniformizer F hpi]; simp)
  have hpiord : ord F pi = (1 : WithTop ℤ) := ord_uniformizer F hpi
  let u : F := a * pi ^ r
  have huord : ord F u = 0 := by
    dsimp only [u]
    rw [ord_mul, ha, ord_pow, hpiord]
    norm_num [← WithTop.coe_nsmul, nsmul_eq_mul]
  have huint : u ∈ lattice F 0 := by
    rw [mem_lattice, huord]
    norm_num
  let uO : ringOfIntegers F :=
    ⟨u, (mem_lattice_zero_iff F).mp huint⟩
  let ubar : ResidueField F := residueMap F uO
  have hubar0 : ubar ≠ 0 := by
    intro hubar0
    have huDeep : (uO : F) ∈ lattice F 1 :=
      (residueMap_eq_zero_iff F uO).mp hubar0
    rw [mem_lattice, show (uO : F) = u from rfl, huord] at huDeep
    have hfalse : ¬ (((1 : ℤ) : WithTop ℤ) ≤ 0) := by norm_num
    exact hfalse huDeep
  obtain ⟨dbar, hdbar, -⟩ := existsUnique_squareRoot (ResidueField F) ubar
  have hdbar0 : dbar ≠ 0 := by
    intro hdbar0
    apply hubar0
    rw [← hdbar, hdbar0, zero_pow]
    norm_num
  obtain ⟨dO, hdO⟩ := residueMap_surjective F dbar
  let d : F := dO
  have hdMem : d ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).mpr dO.property
  have hdNotDeep : d ∉ lattice F 1 := by
    intro hdDeep
    have hzero : residueMap F dO = 0 :=
      (residueMap_eq_zero_iff F dO).mpr hdDeep
    exact hdbar0 (hdO.symm.trans hzero)
  have hdord : ord F d = 0 :=
    (mem_lattice_and_not_mem_succ_iff F).mp ⟨hdMem, hdNotDeep⟩
  let c : F := d / pi ^ q
  have hcord : ord F c = ((-(q : ℤ) : ℤ) : WithTop ℤ) := by
    dsimp only [c]
    rw [ord_div, hdord, ord_pow, hpiord]
    norm_num [← WithTop.coe_nsmul, nsmul_eq_mul]
  have hres : residueMap F uO = residueMap F (dO ^ 2) := by
    rw [map_pow, hdO, hdbar]
  have hnormalized : u - d ^ 2 ∈ lattice F 1 :=
    (residueMap_eq_residueMap_iff F uO (dO ^ 2)).mp hres
  have hpirord : ord F (pi ^ r) = ((r : ℤ) : WithTop ℤ) := by
    rw [ord_pow, hpiord]
    norm_num [← WithTop.coe_nsmul, nsmul_eq_mul]
  have hcancelIdentity : (u - d ^ 2) / pi ^ r = a - c ^ 2 := by
    dsimp only [u, c]
    rw [hr, pow_add]
    field_simp [pow_ne_zero q hpi0]
  have hcancel : a - c ^ 2 ∈ lattice F (1 - (r : ℤ)) := by
    rw [← hcancelIdentity]
    apply (div_mem_lattice_iff F (pi ^ r) (u - d ^ 2)
      (r : ℤ) (1 - (r : ℤ)) hpirord).mpr
    have hdepth : (r : ℤ) + (1 - (r : ℤ)) = 1 := by omega
    simpa only [hdepth] using hnormalized
  have hcDeep : c ∈ lattice F (1 - (r : ℤ)) := by
    rw [mem_lattice, hcord]
    simp only [WithTop.coe_le_coe]
    have hrZ : (r : ℤ) = (q : ℤ) + (q : ℤ) := by exact_mod_cast hr
    omega
  have hnewMem : a - (c ^ 2 - c) ∈ lattice F (1 - (r : ℤ)) := by
    have hadd := add_mem_lattice F hcancel hcDeep
    convert hadd using 1
    ring
  refine ⟨c, hcord, ?_⟩
  have hdepth : (((1 : ℤ) - r : ℤ) : WithTop ℤ) ≤
      ord F (a - (c ^ 2 - c)) := hnewMem
  exact (show (((-(r : ℤ)) : ℤ) : WithTop ℤ) <
      (((1 : ℤ) - r : ℤ) : WithTop ℤ) by
        simp only [WithTop.coe_lt_coe]
        omega).trans_le hdepth

/-- A reduced Artin--Schreier parameter has a positive odd pole order.  Reducedness is expressed
as minimality among all translated Artin--Schreier generators, so parity is not an input. -/
private theorem exists_reduced_artinSchreier_generator
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K]
    [CharP F 2]
    (sigma : Gal(K/F)) (hram : ramificationIndex F K = 2)
    (hsigma0 : sigma ∈ lowerRamificationGroup F K 0)
    (y0 : K) (a0 : F) (hy0 : sigma y0 = y0 + 1)
    (ha0 : y0 ^ 2 - y0 = algebraMap F K a0) :
    ∃ (r : ℕ) (y : K) (a : F), 0 < r ∧ Odd r ∧
      sigma y = y + 1 ∧ y ^ 2 - y = algebraMap F K a ∧
      ord K y = ((-(r : ℤ) : ℤ) : WithTop ℤ) ∧
      ord F a = ((-(r : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  let P : ℕ → Prop := fun r ↦ 0 < r ∧ ∃ (y : K) (a : F),
    sigma y = y + 1 ∧ y ^ 2 - y = algebraMap F K a ∧
      ord K y = ((-(r : ℤ) : ℤ) : WithTop ℤ) ∧
      ord F a = ((-(r : ℤ) : ℤ) : WithTop ℤ)
  have hP : ∃ r, P r := by
    obtain ⟨n, hn, hyn, han⟩ :=
      artinSchreier_parameter_negative F K sigma hram hsigma0 y0 a0 hy0 ha0
    let r : ℕ := (-n).toNat
    have hnonneg : 0 ≤ -n := by omega
    have hr_cast : (r : ℤ) = -n := Int.toNat_of_nonneg hnonneg
    have hrpos : 0 < r := by
      have h : (0 : ℤ) < (r : ℤ) := by omega
      exact_mod_cast h
    refine ⟨r, hrpos, y0, a0, hy0, ha0, ?_, ?_⟩
    · simpa [hr_cast] using hyn
    · simpa [hr_cast] using han
  let r : ℕ := Nat.find hP
  have hr_data : P r := Nat.find_spec hP
  rcases hr_data with ⟨hrpos, y, a, hy, ha, hyord, haord⟩
  have hrodd : Odd r := by
    rw [← Nat.not_even_iff_odd]
    intro hreven
    obtain ⟨q, hq⟩ := hreven
    obtain ⟨pi, hpiord⟩ := exists_ord_eq F 1
    have hpi : (ValuativeRel.valuation F).IsUniformizer pi :=
      (ord_eq_one_iff_isUniformizer F pi).mp hpiord
    obtain ⟨c, hcord, himprove⟩ :=
      improve_even_artinSchreier_pole F pi hpi a r q hrpos (by omega) haord
    let y' : K := y - algebraMap F K c
    let a' : F := a - (c ^ 2 - c)
    have hy' : sigma y' = y' + 1 := by
      dsimp only [y']
      rw [map_sub, sigma.commutes, hy]
      ring
    have ha' : y' ^ 2 - y' = algebraMap F K a' := by
      dsimp only [y', a']
      simp only [map_sub, map_pow]
      simp only [CharTwo.sub_eq_add] at ha ⊢
      rw [add_sq]
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      simp only [htwo, zero_mul]
      linear_combination ha
    obtain ⟨n', hn', hyn', han'⟩ :=
      artinSchreier_parameter_negative F K sigma hram hsigma0 y' a' hy' ha'
    let r' : ℕ := (-n').toNat
    have hr'nonneg : 0 ≤ -n' := by omega
    have hr'cast : (r' : ℤ) = -n' := Int.toNat_of_nonneg hr'nonneg
    have hr'pos : 0 < r' := by
      have h : (0 : ℤ) < (r' : ℤ) := by omega
      exact_mod_cast h
    have hPr' : P r' := by
      refine ⟨hr'pos, y', a', hy', ha', ?_, ?_⟩
      · simpa [hr'cast] using hyn'
      · simpa [hr'cast] using han'
    have hr'lt : r' < r := by
      have hneg : ((-(r : ℤ) : ℤ) : WithTop ℤ) <
          ((-(r' : ℤ) : ℤ) : WithTop ℤ) := by
        rw [han'] at himprove
        simpa [hr'cast] using himprove
      simp only [WithTop.coe_lt_coe] at hneg
      omega
    exact (Nat.find_min hP hr'lt) hPr'
  exact ⟨r, y, a, hrpos, hrodd, hy, ha, hyord, haord⟩

/-- The nontrivial automorphism lies in the lower group indexed by the reduced pole.  The proof
uses the basis `1,y`; oddness prevents cancellation between its two coordinate valuations. -/
private theorem automorphism_mem_lowerGroup_at_reducedPole
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (hdegree : Module.finrank F K = 2)
    (hram : ramificationIndex F K = 2)
    (sigma : Gal(K/F)) (y : K) (r : ℕ)
    (hodd : Odd r) (hy : sigma y = y + 1)
    (hyord : ord K y = ((-(r : ℤ) : ℤ) : WithTop ℤ)) :
    sigma ∈ lowerRamificationGroup F K (r : ℤ) := by
  have hy_not_base : ∀ a : F, algebraMap F K a ≠ y := by
    intro a ha
    have hfixed := sigma.commutes a
    rw [ha, hy] at hfixed
    have hone : (1 : K) = 0 := by
      calc
        (1 : K) = (y + 1) - y := by ring
        _ = y - y := by rw [hfixed]
        _ = 0 := sub_self y
    exact one_ne_zero hone
  have hLI : LinearIndependent F ![(1 : K), y] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a
    simpa only [Algebra.smul_def, mul_one] using hy_not_base a
  have hcard : Fintype.card (Fin 2) = Module.finrank F K := by simp [hdegree]
  let b : Module.Basis (Fin 2) F K :=
    basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hb : (b : Fin 2 → K) = ![(1 : K), y] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard
  rw [mem_lowerRamificationGroup_iff_ord]
  intro x
  let A : F := b.equivFun (x : K) 0
  let B : F := b.equivFun (x : K) 1
  have hx : algebraMap F K A + algebraMap F K B * y = (x : K) := by
    have hrepr := b.sum_equivFun (x : K)
    simpa only [Fin.sum_univ_two, hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Algebra.smul_def, mul_one, A, B] using hrepr
  have hdiff : sigma (x : K) - (x : K) = algebraMap F K B := by
    rw [← hx, map_add, map_mul, sigma.commutes, sigma.commutes, hy]
    ring
  rw [hdiff]
  by_cases hB : B = 0
  · rw [hB, map_zero, ord_zero]
    exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hB)
  have hBord : ord F B = (n : WithTop ℤ) := hn.symm
  have hmapBord : ord K (algebraMap F K B) = ((2 * n : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, hBord, ← WithTop.coe_nsmul]
    congr 1
  have hByord : ord K (algebraMap F K B * y) =
      ((2 * n - r : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hmapBord, hyord]
    rw [← WithTop.coe_add]
    congr 1
  have hBy_nonneg : (0 : WithTop ℤ) ≤ ord K (algebraMap F K B * y) := by
    by_cases hA : A = 0
    · rw [hA, map_zero, zero_add] at hx
      rw [hx]
      exact (ord_nonneg_iff_mem_integer K (x : K)).mpr x.property
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).mpr hA)
    have hAord : ord F A = (m : WithTop ℤ) := hm.symm
    have hmapAord : ord K (algebraMap F K A) = ((2 * m : ℤ) : WithTop ℤ) := by
      rw [ord_algebraMap, hram, hAord, ← WithTop.coe_nsmul]
      congr 1
    have hdistinct : ord K (algebraMap F K A) ≠
        ord K (algebraMap F K B * y) := by
      rw [hmapAord, hByord]
      intro heq
      have heqZ : 2 * m = 2 * n - (r : ℤ) := WithTop.coe_eq_coe.mp heq
      obtain ⟨q, hq⟩ := hodd
      have hqz : (r : ℤ) = 2 * (q : ℤ) + 1 := by exact_mod_cast hq
      omega
    have hxord : ord K (x : K) =
        min (ord K (algebraMap F K A))
          (ord K (algebraMap F K B * y)) := by
      rw [← hx, ord_add_eq_min K hdistinct]
    have hxnonneg : (0 : WithTop ℤ) ≤ ord K (x : K) :=
      (ord_nonneg_iff_mem_integer K (x : K)).mpr x.property
    rw [hxord] at hxnonneg
    exact hxnonneg.trans (min_le_right _ _)
  rw [hByord] at hBy_nonneg
  rw [hmapBord]
  have hBy_nonnegZ : (0 : ℤ) ≤ 2 * n - (r : ℤ) := by
    exact_mod_cast hBy_nonneg
  simp only [WithTop.coe_le_coe]
  obtain ⟨q, hq⟩ := hodd
  have hqz : (r : ℤ) = 2 * (q : ℤ) + 1 := by exact_mod_cast hq
  omega

/-- The same automorphism leaves the next lower group.  For `r = 2q + 1`, the manuscript's
explicit uniformizer `pi_F^(q+1) y` has displacement of exact order `r + 1`. -/
private theorem automorphism_not_mem_lowerGroup_after_reducedPole
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K] [IsGalois F K]
    (hram : ramificationIndex F K = 2)
    (sigma : Gal(K/F)) (y : K) (r : ℕ)
    (hodd : Odd r) (hy : sigma y = y + 1)
    (hyord : ord K y = ((-(r : ℤ) : ℤ) : WithTop ℤ)) :
    sigma ∉ lowerRamificationGroup F K ((r : ℤ) + 1) := by
  obtain ⟨q, hq⟩ := hodd
  have hqz : (r : ℤ) = 2 * (q : ℤ) + 1 := by exact_mod_cast hq
  obtain ⟨pi, hpiord⟩ := exists_ord_eq F 1
  let piK : K := algebraMap F K (pi ^ (q + 1)) * y
  have hcoefficientOrd : ord K (algebraMap F K (pi ^ (q + 1))) =
      ((2 * ((q : ℤ) + 1) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, ord_pow, hpiord]
    norm_cast
    simp
  have hpiKord : ord K piK = (1 : WithTop ℤ) := by
    dsimp only [piK]
    rw [ord_mul, hcoefficientOrd, hyord]
    rw [← WithTop.coe_add]
    congr 1
    omega
  have hpiK : (ValuativeRel.valuation K).IsUniformizer piK :=
    (ord_eq_one_iff_isUniformizer K piK).mp hpiKord
  have hdiff : sigma piK - piK = algebraMap F K (pi ^ (q + 1)) := by
    dsimp only [piK]
    rw [map_mul, sigma.commutes, hy]
    ring
  intro hsigma
  have hbound := lowerRamificationGroup_uniformizer_ord F K hsigma hpiK
  rw [hdiff, hcoefficientOrd] at hbound
  simp only [WithTop.coe_le_coe] at hbound
  omega

/-- Let `K/F` be a totally ramified quadratic Galois extension of nonarchimedean local fields
of equal characteristic two.  If `t` is its unique lower break in the project's convention
`G_t = Gal(K/F)` and `G_(t+1) = 1`, then `t` is odd. -/
theorem quadraticBreak_odd_equalCharacteristic
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    [CharP F 2]
    (hdegree : Module.finrank F K = 2)
    (hresidue : residueDegree F K = 1)
    (t : ℕ)
    (hbreak : lowerRamificationGroup F K (t : ℤ) = ⊤)
    (hbreak_succ : lowerRamificationGroup F K ((t : ℤ) + 1) = ⊥) :
    Odd t := by
  have hram : ramificationIndex F K = 2 := by
    have hfund := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hdegree, hresidue, mul_one] at hfund
    exact hfund.symm
  obtain ⟨sigma, y0, a0, hsigma, hy0, ha0⟩ :=
    exists_artinSchreier_generator F K hdegree
  have hsigma_t : sigma ∈ lowerRamificationGroup F K (t : ℤ) := by
    rw [hbreak]
    exact Subgroup.mem_top sigma
  have hsigma0 : sigma ∈ lowerRamificationGroup F K 0 :=
    (lowerRamificationGroup_antitone F K (by positivity)) hsigma_t
  obtain ⟨r, y, a, hrpos, hrodd, hy, ha, hyord, haord⟩ :=
    exists_reduced_artinSchreier_generator F K sigma hram hsigma0 y0 a0 hy0 ha0
  have hsigma_r : sigma ∈ lowerRamificationGroup F K (r : ℤ) :=
    automorphism_mem_lowerGroup_at_reducedPole F K hdegree hram sigma y r hrodd hy hyord
  have hsigma_not_rsucc :
      sigma ∉ lowerRamificationGroup F K ((r : ℤ) + 1) :=
    automorphism_not_mem_lowerGroup_after_reducedPole F K hram sigma y r hrodd hy hyord
  have hsigma_not_tsucc :
      sigma ∉ lowerRamificationGroup F K ((t : ℤ) + 1) := by
    rw [hbreak_succ]
    simpa using hsigma
  have hrt : r ≤ t := by
    by_contra hnot
    have htr : t < r := Nat.lt_of_not_ge hnot
    apply hsigma_not_tsucc
    apply (lowerRamificationGroup_antitone F K ?_) hsigma_r
    exact_mod_cast Nat.succ_le_of_lt htr
  have htr : t ≤ r := by
    by_contra hnot
    have hrt' : r < t := Nat.lt_of_not_ge hnot
    apply hsigma_not_rsucc
    apply (lowerRamificationGroup_antitone F K ?_) hsigma_t
    exact_mod_cast Nat.succ_le_of_lt hrt'
  have htreq : t = r := Nat.le_antisymm htr hrt
  simpa [htreq] using hrodd

end LanglandsFirstMainLemma
