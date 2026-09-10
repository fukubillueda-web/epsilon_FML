import LanglandsFirstMainLemma.Cases.WildOdd.UpperResidualNormalization
import LanglandsFirstMainLemma.Cases.WildOdd.HigherSymmetricVanishing

/-!
# Upper residual coefficients in the wild odd-prime case

The opening support block identifies the higher-norm correction, proves the
needed symmetric, trace, and valuation bounds, and reduces the retained
correction to a pure quadratic residual character.  The coefficient block then
computes the natural upper polar coefficient and transports it first to the
lower coordinate and then to the displayed inverse-Frobenius coordinate.
Here High is the strict-above branch, while Low contains both the strict-below
and boundary subcases.

Readers should begin with `WildOddUpperCoefficientPair` and
`wildOddUpperPairBelow`, `wildOddUpperPairBoundary`,
`wildOddUpperPairAbove`, and `wildOddUpperPairEven`, then read the
natural-coordinate results
`highActual_naturalPolar`, `lowActual_naturalPolar_strict`, and
`lowActual_naturalPolar_boundary`.  The pure-quadratic correction theorems and
`wildOdd_actualHighCoefficients_above`,
`wildOdd_actualHighCoefficients_even`,
`wildOdd_actualLowCoefficients_strict`,
`wildOdd_actualLowCoefficients_boundary`, and
`wildOdd_actualLowCoefficients_even` supply the terminal rows.
Finally, `WildOddUpperRepresentativeTranslationCertificate` records the exact
representative translation, and `WildOddUpperResidualCoefficientsAPI` with
`wildOdd_upperResidualCoefficients` is the client-facing façade linking these
constituent declarations.
-/

namespace LanglandsFirstMainLemma
noncomputable section
theorem phaseReductionNormHigherPart_sub_eq_wildOddUpperCorrection
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (hdegree : Module.finrank F K = p) (u x : K) :
    phaseReductionNormHigherPart F K (u * x) -
        norm F K u * phaseReductionNormHigherPart F K x =
      wildOddUpperCorrection F K p u x := by
  rw [phaseReductionNormHigherPart_eq_higherCorrection,
    phaseReductionNormHigherPart_eq_higherCorrection,
    normPolynomialHigherCorrectionValue,
    normPolynomialHigherCorrectionValue, hdegree]
  rw [wildOddUpperCorrection, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rfl
private theorem wildOdd_localField_infinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : ℤ → F := fun n ↦ (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm := (exists_ord_eq F m).choose_spec
    have hn := (exists_ord_eq F n).choose_spec
    apply WithTop.coe_injective
    exact hm.symm.trans ((congrArg (ord F) hmn).trans hn)
  exact Infinite.of_injective f hf
private theorem Multiset.esymm_two_cons
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_add,
    Multiset.powersetCard_one]
  simpa using
    (Multiset.sum_map_mul_left (s := s) (f := fun x : R ↦ x) (a := a))
private theorem wildOdd_esymm_two_map_add
    {ι R : Type*} [CommRing R] (s : Finset ι) (f g : ι → R) :
    (s.val.map (fun i ↦ f i + g i)).esymm 2 =
      (s.val.map f).esymm 2 + (s.val.map g).esymm 2 +
        (∑ i ∈ s, f i) * (∑ i ∈ s, g i) - ∑ i ∈ s, f i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Multiset.esymm]
  | @insert a s ha ih =>
      rw [← Finset.cons_eq_insert a s ha]
      simp only [Finset.cons_val, Multiset.map_cons, Multiset.esymm_two_cons,
        Finset.sum_cons, ih, ← Finset.sum_eq_multiset_sum,
        Finset.sum_add_distrib]
      ring
theorem wildOdd_elementarySymmetric_two_add
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F K] [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (x y : K) :
    elementarySymmetric F K 2 (x + y) =
      elementarySymmetric F K 2 x + elementarySymmetric F K 2 y +
        trace F K x * trace F K y - trace F K (x * y) := by
  letI : Infinite F := wildOdd_localField_infinite F
  apply (algebraMap F K).injective
  simp only [map_add, map_mul, map_sub]
  simp_rw [algebraMap_elementarySymmetric_eq_esymm_galois]
  have h := wildOdd_esymm_two_map_add
    (Finset.univ : Finset Gal(K/F)) (fun σ ↦ σ x) (fun σ ↦ σ y)
  have hx : (∑ σ : Gal(K/F), σ x) = algebraMap F K (trace F K x) := by
    simpa [galoisConjugates, galoisConjugate] using
      galoisConjugates_sum F K x
  have hy : (∑ σ : Gal(K/F), σ y) = algebraMap F K (trace F K y) := by
    simpa [galoisConjugates, galoisConjugate] using
      galoisConjugates_sum F K y
  have hxy : (∑ σ : Gal(K/F), σ (x * y)) =
      algebraMap F K (trace F K (x * y)) := by
    simpa [galoisConjugates, galoisConjugate] using
      galoisConjugates_sum F K (x * y)
  have hdiag : (∑ σ : Gal(K/F), σ x * σ y) =
      algebraMap F K (trace F K (x * y)) := by
    rw [← hxy]
    apply Finset.sum_congr rfl
    intro σ _
    exact (σ.map_mul x y).symm
  simpa [galoisConjugates, galoisConjugate, hx, hy, hxy, hdiag] using h
theorem wildOdd_integralLift_sub_algebraMap_teichmuller_mem_lattice_one
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    (e : ResidueField F ≃+* ResidueField K)
    (he : ∀ z, e z = extensionResidueMap F K z)
    (z : ResidueField F) (lift : lattice K 0)
    (hlift : reduce K (lift : K) lift.property = e z) :
    (lift : K) - algebraMap F K ((teichmuller F z : ringOfIntegers F) : F) ∈
      lattice K 1 := by
  let tzF : ringOfIntegers F := teichmuller F z
  let tzK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) tzF
  have htzKcoe : (tzK : K) = algebraMap F K (tzF : F) :=
    Valuation.HasExtension.val_algebraMap tzF
  have htzK : algebraMap F K (tzF : F) ∈ lattice K 0 := by
    rw [← htzKcoe]
    exact (mem_lattice_zero_iff K).2 tzK.property
  have hreduce :
      reduce K (algebraMap F K (tzF : F)) htzK = e z := by
    rw [he]
    change residueMap K tzK = extensionResidueMap F K z
    have hz : residueMap F tzF = z := by simp [tzF]
    rw [← hz]
    change residueMap K tzK = extensionResidueMap F K (residueMap F tzF)
    rfl
  exact (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1
    ((reduce_eq_reduce_iff K lift.property htzK).1 (hlift.trans hreduce.symm))
theorem wildOdd_elementarySymmetric_two_mem
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hT : 2 ≤ T)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (q s : ℤ) {x : K} (hx : (q : WithTop ℤ) ≤ ord K x)
    (hnum : (p : ℤ) * s ≤
      2 * q + (((p - 1) * T : ℕ) : ℤ)) :
    elementarySymmetric F K 2 x ∈ lattice F s := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hb := wild_elementarySymmetric_bound F K p T q hp hT hchar
    hdegree htrace hx (j := 2) (by omega) (by omega)
  rw [mem_lattice]
  apply (show (s : WithTop ℤ) ≤
      ((((2 : ℕ) : ℤ) * q + (((p - 1) * T : ℕ) : ℤ)) /
        (p : ℤ) : ℤ) by
    rw [WithTop.coe_le_coe, Int.le_ediv_iff_mul_le hpZ]
    simpa only [Nat.cast_ofNat, mul_comm] using hnum).trans
  exact hb
theorem wildOdd_trace_mem_of_numerical
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p T : ℕ) (hp : p.Prime)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (q s : ℤ) {x : K} (hx : (q : WithTop ℤ) ≤ ord K x)
    (hnum : (p : ℤ) * s ≤
      q + (((p - 1) * T : ℕ) : ℤ)) :
    trace F K x ∈ lattice F s := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  rw [mem_lattice]
  apply (show (s : WithTop ℤ) ≤
      (((q + (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ) : ℤ) :
        WithTop ℤ) by
    rw [WithTop.coe_le_coe, Int.le_ediv_iff_mul_le hpZ]
    simpa only [mul_comm] using hnum).trans
  exact htrace q x hx
private theorem wildOdd_ediv_add_shift_le_add_ediv
    (p D u v : ℤ) (hp : 0 < p) (hD : p ≤ D) :
    (u + v + D) / p ≤ (u + D) / p + (v + D) / p := by
  have hfloor (A B : ℤ) :
      (A + B - p) / p ≤ A / p + B / p := by
    rw [Int.ediv_le_iff_le_mul hp]
    have hA : A < (A / p) * p + p :=
      (Int.ediv_le_iff_le_mul hp).mp le_rfl
    have hB : B < (B / p) * p + p :=
      (Int.ediv_le_iff_le_mul hp).mp le_rfl
    nlinarith
  calc
    (u + v + D) / p ≤ (u + v + 2 * D - p) / p := by
      apply Int.ediv_le_ediv hp
      linarith
    _ = ((u + D) + (v + D) - p) / p := by
      congr 1
      ring
    _ ≤ (u + D) / p + (v + D) / p := hfloor _ _
theorem wildOdd_trace_mul_trace_mem
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p T : ℕ) (hp : p.Prime) (hT : 2 ≤ T)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (q₁ q₂ s : ℤ) {x y : K}
    (hx : (q₁ : WithTop ℤ) ≤ ord K x)
    (hy : (q₂ : WithTop ℤ) ≤ ord K y)
    (hnum : (p : ℤ) * s ≤
      q₁ + q₂ + (((p - 1) * T : ℕ) : ℤ)) :
    trace F K x * trace F K y ∈ lattice F s := by
  let D : ℤ := (((p - 1) * T : ℕ) : ℤ)
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hDZ : (p : ℤ) ≤ D := by
    dsimp only [D]
    have : p ≤ (p - 1) * T := by
      have htwo : p ≤ (p - 1) * 2 := by
        have := hp.two_le
        omega
      exact htwo.trans (Nat.mul_le_mul_left (p - 1) hT)
    exact_mod_cast this
  have hbase : s ≤ (q₁ + q₂ + D) / (p : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hpZ]
    simpa only [D, mul_comm] using hnum
  have hsplit := wildOdd_ediv_add_shift_le_add_ediv (p : ℤ) D q₁ q₂ hpZ hDZ
  have htx := htrace q₁ x hx
  have hty := htrace q₂ y hy
  rw [mem_lattice, ord_mul]
  exact (show (s : WithTop ℤ) ≤
      (((q₁ + D) / (p : ℤ) : ℤ) : WithTop ℤ) +
        (((q₂ + D) / (p : ℤ) : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    exact hbase.trans hsplit).trans (add_le_add htx hty)
theorem wildOddUpperQuadraticCorrection_add_deep
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T dK : ℕ) (a : ℤ) (hp : p.Prime) (hp2 : p ≠ 2) (hT : 2 ≤ T)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (hres : residueDegree F K = 1)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (u y z : K)
    (hu : ord K u = (a : WithTop ℤ))
    (hy : ((dK : ℤ) : WithTop ℤ) ≤ ord K y)
    (hz : (((dK : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ord K z)
    (hcrossU : (T : ℤ) ≤ 2 * ((dK : ℤ) + a) + 1)
    (hcrossN : (T : ℤ) ≤ 2 * (dK : ℤ) + 1 + (p : ℤ) * a) :
    wildOddUpperQuadraticCorrection F K u (y + z) -
        wildOddUpperQuadraticCorrection F K u y ∈ lattice F (T : ℤ) := by
  have hp1 : 1 ≤ p := hp.one_le
  have hD : (((p - 1) * T : ℕ) : ℤ) =
      ((p : ℤ) - 1) * (T : ℤ) := by
    push_cast [Nat.cast_sub hp1]
    ring_nf
  have huy : (((dK : ℤ) + a : ℤ) : WithTop ℤ) ≤ ord K (u * y) := by
    rw [ord_mul, hu]
    simpa only [WithTop.coe_add, add_comm] using
      add_le_add_left hy (a : WithTop ℤ)
  have huzord : (((dK : ℤ) + a + 1 : ℤ) : WithTop ℤ) ≤
      ord K (u * z) := by
    rw [ord_mul, hu]
    simpa only [WithTop.coe_add, add_comm, add_left_comm, add_assoc] using
      add_le_add_left hz (a : WithTop ℤ)
  have hyz : (((dK : ℤ) + ((dK : ℤ) + 1) : ℤ) : WithTop ℤ) ≤
      ord K (y * z) := by
    rw [ord_mul]
    exact add_le_add hy hz
  have huyuz : (((dK : ℤ) + a + ((dK : ℤ) + a + 1) : ℤ) :
      WithTop ℤ) ≤
      ord K ((u * y) * (u * z)) := by
    rw [ord_mul]
    exact add_le_add huy huzord
  have hnormu : norm F K u ∈ lattice F a := by
    rw [mem_lattice, ord_norm, hres, one_nsmul, hu]
  have heuz : elementarySymmetric F K 2 (u * z) ∈ lattice F (T : ℤ) := by
    apply wildOdd_elementarySymmetric_two_mem F K p T hp hp2 hT hchar
      hdegree htrace ((dK : ℤ) + a + 1) (T : ℤ) huzord
    rw [hD]
    nlinarith
  have hez : elementarySymmetric F K 2 z ∈ lattice F ((T : ℤ) - a) := by
    apply wildOdd_elementarySymmetric_two_mem F K p T hp hp2 hT hchar
      hdegree htrace ((dK : ℤ) + 1) ((T : ℤ) - a) hz
    rw [hD]
    nlinarith
  have htrU : trace F K (u * y) * trace F K (u * z) ∈
      lattice F (T : ℤ) := by
    apply wildOdd_trace_mul_trace_mem F K p T hp hT htrace
      ((dK : ℤ) + a) ((dK : ℤ) + a + 1) (T : ℤ) huy huzord
    rw [hD]
    nlinarith
  have htrUprod : trace F K ((u * y) * (u * z)) ∈ lattice F (T : ℤ) := by
    apply wildOdd_trace_mem_of_numerical F K p T hp htrace
      ((dK : ℤ) + a + ((dK : ℤ) + a + 1)) (T : ℤ) huyuz
    rw [hD]
    nlinarith
  have htrN : trace F K y * trace F K z ∈ lattice F ((T : ℤ) - a) := by
    apply wildOdd_trace_mul_trace_mem F K p T hp hT htrace
      (dK : ℤ) ((dK : ℤ) + 1) ((T : ℤ) - a) hy hz
    rw [hD]
    nlinarith
  have htrNprod : trace F K (y * z) ∈ lattice F ((T : ℤ) - a) := by
    apply wildOdd_trace_mem_of_numerical F K p T hp htrace
      ((dK : ℤ) + ((dK : ℤ) + 1)) ((T : ℤ) - a) hyz
    rw [hD]
    nlinarith
  have hn_ez : norm F K u * elementarySymmetric F K 2 z ∈
      lattice F (T : ℤ) := by
    simpa only [add_sub_cancel] using mul_mem_lattice F hnormu hez
  have hn_tr : norm F K u * (trace F K y * trace F K z) ∈
      lattice F (T : ℤ) := by
    simpa only [add_sub_cancel] using mul_mem_lattice F hnormu htrN
  have hn_trprod : norm F K u * trace F K (y * z) ∈
      lattice F (T : ℤ) := by
    simpa only [add_sub_cancel] using mul_mem_lattice F hnormu htrNprod
  have huPart :
      elementarySymmetric F K 2 (u * z) +
          trace F K (u * y) * trace F K (u * z) -
        trace F K ((u * y) * (u * z)) ∈ lattice F (T : ℤ) :=
    sub_mem_lattice F (add_mem_lattice F heuz htrU) htrUprod
  have hnPart :
      norm F K u * elementarySymmetric F K 2 z +
          norm F K u * (trace F K y * trace F K z) -
        norm F K u * trace F K (y * z) ∈ lattice F (T : ℤ) :=
    sub_mem_lattice F (add_mem_lattice F hn_ez hn_tr) hn_trprod
  have hmain := sub_mem_lattice F huPart hnPart
  have huProduct : (u * y) * (u * z) = u ^ 2 * y * z := by ring
  rw [huProduct] at hmain
  simp only [wildOddUpperQuadraticCorrection, wildOddUpperCorrectionTerm]
  rw [show u * (y + z) = u * y + u * z by ring,
    wildOdd_elementarySymmetric_two_add F K (u * y) (u * z),
    wildOdd_elementarySymmetric_two_add F K y z]
  convert hmain using 1
  all_goals ring_nf
theorem wildOdd_upperLift_numerics
    (p b t dK : ℕ) (r : ℤ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hbreak : r + 2 * (dK : ℤ) = (t : ℤ))
    (hbelow : b < t → r = (t : ℤ) - (b : ℤ))
    (hboundary : b = t → r = 0)
    (habove : t < b → r = (p : ℤ) * ((t : ℤ) - (b : ℤ))) :
    ((t + 1 : ℕ) : ℤ) ≤
        2 * ((dK : ℤ) + ((t : ℤ) - (b : ℤ))) + 1 ∧
      ((t + 1 : ℕ) : ℤ) ≤
        2 * (dK : ℤ) + 1 +
          (p : ℤ) * ((t : ℤ) - (b : ℤ)) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases lt_trichotomy b t with hbt | hbt | htb
  · have hr := hbelow hbt
    constructor <;> push_cast at * <;> nlinarith
  · have hr := hboundary hbt
    constructor <;> push_cast at * <;> nlinarith
  · have hr := habove htb
    constructor <;> push_cast at * <;> nlinarith
theorem wildOdd_upperCoordinate_numerics
    (p b t dK : ℕ) (r : ℤ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hbreak : r + 2 * (dK : ℤ) = (t : ℤ))
    (hbelow : b < t → r = (t : ℤ) - (b : ℤ))
    (hboundary : b = t → r = 0)
    (habove : t < b → r = (p : ℤ) * ((t : ℤ) - (b : ℤ))) :
    (t : ℤ) ≤ 2 * ((dK : ℤ) + ((t : ℤ) - (b : ℤ))) ∧
      (t : ℤ) ≤ 2 * (dK : ℤ) +
        (p : ℤ) * ((t : ℤ) - (b : ℤ)) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases lt_trichotomy b t with hbt | hbt | htb
  · have hr := hbelow hbt
    constructor <;> nlinarith
  · have hr := hboundary hbt
    constructor <;> nlinarith
  · have hr := habove htb
    constructor <;> nlinarith
theorem wildOddUpperQuadraticCorrection_mem
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T t dK : ℕ) (a : ℤ) (hp : p.Prime) (hp2 : p ≠ 2) (hT : 2 ≤ T)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (hres : residueDegree F K = 1)
    (htT : t ≤ T)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (u x : K)
    (hu : ord K u = (a : WithTop ℤ))
    (hx : ((dK : ℤ) : WithTop ℤ) ≤ ord K x)
    (hU : (t : ℤ) ≤ 2 * ((dK : ℤ) + a))
    (hN : (t : ℤ) ≤ 2 * (dK : ℤ) + (p : ℤ) * a) :
    wildOddUpperQuadraticCorrection F K u x ∈ lattice F (t : ℤ) := by
  have hp1 : 1 ≤ p := hp.one_le
  have hD : (((p - 1) * T : ℕ) : ℤ) =
      ((p : ℤ) - 1) * (T : ℤ) := by
    push_cast [Nat.cast_sub hp1]
    ring_nf
  have hux : (((dK : ℤ) + a : ℤ) : WithTop ℤ) ≤ ord K (u * x) := by
    rw [ord_mul, hu]
    simpa only [WithTop.coe_add, add_comm] using
      add_le_add_left hx (a : WithTop ℤ)
  have hnormu : norm F K u ∈ lattice F a := by
    rw [mem_lattice, ord_norm, hres, one_nsmul, hu]
  have heux : elementarySymmetric F K 2 (u * x) ∈ lattice F (t : ℤ) := by
    apply wildOdd_elementarySymmetric_two_mem F K p T hp hp2 hT hchar
      hdegree htrace ((dK : ℤ) + a) (t : ℤ) hux
    rw [hD]
    have hTge : (t : ℤ) ≤ (T : ℤ) := by exact_mod_cast htT
    nlinarith
  have hex : elementarySymmetric F K 2 x ∈ lattice F ((t : ℤ) - a) := by
    apply wildOdd_elementarySymmetric_two_mem F K p T hp hp2 hT hchar
      hdegree htrace (dK : ℤ) ((t : ℤ) - a) hx
    rw [hD]
    have hTge : (t : ℤ) ≤ (T : ℤ) := by exact_mod_cast htT
    nlinarith
  have hnex : norm F K u * elementarySymmetric F K 2 x ∈
      lattice F (t : ℤ) := by
    simpa only [add_sub_cancel] using mul_mem_lattice F hnormu hex
  exact sub_mem_lattice F heux hnex
theorem wildOddUpperQuadraticCorrection_integralLift_teichmuller
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T dK : ℕ) (a : ℤ) (hp : p.Prime) (hp2 : p ≠ 2) (hT : 2 ≤ T)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (hres : residueDegree F K = 1)
    (htrace : TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ))
    (e : ResidueField F ≃+* ResidueField K)
    (he : ∀ z, e z = extensionResidueMap F K z)
    (u coordinate : K)
    (hu : ord K u = (a : WithTop ℤ))
    (hcoordinate : ord K coordinate = ((dK : ℤ) : WithTop ℤ))
    (Z : ResidueField F) (lift : lattice K 0)
    (hlift : reduce K (lift : K) lift.property = e Z)
    (hcrossU : (T : ℤ) ≤ 2 * ((dK : ℤ) + a) + 1)
    (hcrossN : (T : ℤ) ≤ 2 * (dK : ℤ) + 1 + (p : ℤ) * a) :
    wildOddUpperQuadraticCorrection F K u (coordinate * (lift : K)) -
        ((teichmuller F Z : ringOfIntegers F) : F) ^ 2 *
          wildOddUpperQuadraticCorrection F K u coordinate ∈
      lattice F (T : ℤ) := by
  let c : F := ((teichmuller F Z : ringOfIntegers F) : F)
  have hcF : c ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F Z).property
  let cKint : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) (teichmuller F Z)
  have hcKcoe : (cKint : K) = algebraMap F K c :=
    Valuation.HasExtension.val_algebraMap (teichmuller F Z)
  have hcK : algebraMap F K c ∈ lattice K 0 := by
    rw [← hcKcoe]
    exact (mem_lattice_zero_iff K).2 cKint.property
  have hliftDiff : (lift : K) - algebraMap F K c ∈ lattice K 1 := by
    exact wildOdd_integralLift_sub_algebraMap_teichmuller_mem_lattice_one
      F K e he Z lift hlift
  have hcoordLat : coordinate ∈ lattice K (dK : ℤ) := by
    rw [mem_lattice, hcoordinate]
  let y : K := algebraMap F K c * coordinate
  let w : K := coordinate * ((lift : K) - algebraMap F K c)
  have hy : ((dK : ℤ) : WithTop ℤ) ≤ ord K y := by
    have hmul := mul_mem_lattice K hcK hcoordLat
    simpa only [zero_add, mem_lattice, y] using hmul
  have hw : (((dK : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ord K w := by
    have hmul := mul_mem_lattice K hcoordLat hliftDiff
    simpa only [mem_lattice, w] using hmul
  have hdeep := wildOddUpperQuadraticCorrection_add_deep
    F K p T dK a hp hp2 hT hchar hdegree hres htrace u y w hu hy hw
    hcrossU hcrossN
  have hsplit : coordinate * (lift : K) = y + w := by
    dsimp only [y, w]
    ring
  have hhom := wildOddUpperQuadraticCorrection_homogeneous F K c u coordinate
  rw [← hsplit] at hdeep
  change wildOddUpperQuadraticCorrection F K u (coordinate * (lift : K)) -
      c ^ 2 * wildOddUpperQuadraticCorrection F K u coordinate ∈ _
  rw [← hhom]
  simpa only [y, mul_comm (algebraMap F K c) coordinate] using hdeep
theorem wildOdd_normHigherPart_sub_eq_correction
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (p : ℕ) (hdegree : Module.finrank F K = p)
    (u x : K) :
    phaseReductionNormHigherPart F K (u * x) -
        norm F K u * phaseReductionNormHigherPart F K x =
      wildOddUpperCorrection F K p u x := by
  rw [phaseReductionNormHigherPart_eq_higherCorrection,
    phaseReductionNormHigherPart_eq_higherCorrection,
    normPolynomialHigherCorrectionValue,
    normPolynomialHigherCorrectionValue, hdegree]
  rw [wildOddUpperCorrection, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rfl
noncomputable def CriticalPolarFunction_mulPureQuadratic
    {k : Type*} [Field k] {psi0 : FiniteAddChar k} {A₀ : k}
    (g : CriticalPolarFunction k psi0 A₀) (q : k) :
    CriticalPolarFunction k psi0 (A₀ + 2 * q) where
  toFun x := g x * psi0 (q * x ^ 2)
  ne_zero' x := mul_ne_zero (g.ne_zero x) (AddChar.val_isUnit psi0 _).ne_zero
  map_add' x y := by
    rw [g.map_add]
    rw [show q * (x + y) ^ 2 = q * x ^ 2 + q * y ^ 2 + 2 * q * (x * y) by ring]
    rw [psi0.map_add_eq_mul, psi0.map_add_eq_mul]
    rw [show (A₀ + 2 * q) * (x * y) = A₀ * (x * y) + 2 * q * (x * y) by ring]
    rw [psi0.map_add_eq_mul]
    ring
@[simp] theorem CriticalPolarFunction_mulPureQuadratic_apply
    {k : Type*} [Field k] {psi0 : FiniteAddChar k} {A₀ : k}
    (g : CriticalPolarFunction k psi0 A₀) (q x : k) :
    CriticalPolarFunction_mulPureQuadratic g q x =
      g x * psi0 (q * x ^ 2) := rfl
theorem CriticalPolarFunction_affineCoefficient_mulPureQuadratic
    {k : Type*} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} {A₀ : k}
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (g : CriticalPolarFunction k psi0 A₀) (q : k) :
    (CriticalPolarFunction_mulPureQuadratic g q).affineCoefficient
        hchar hpsi0 =
      g.affineCoefficient hchar hpsi0 := by
  apply CriticalPolarFunction.affineCoefficient_unique hchar hpsi0
  intro x
  rw [CriticalPolarFunction_mulPureQuadratic_apply,
    g.eq_quadratic hchar hpsi0]
  rw [← psi0.map_add_eq_mul]
  congr 1
  field_simp [Ring.two_ne_zero hchar]
  ring
theorem wildOdd_scaledQuadraticCorrection_eq_residueQuadratic
    (F : Type*) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime]
    (psiF : LocalAddCharData F) (A breakCoordinate : Fˣ)
    (t T : ℕ) (hT : T = t + 1)
    (hbreak : ord F (breakCoordinate : F) = ((t : ℤ) : WithTop ℤ))
    (hA : ord F (A : F) =
      (-((T : ℤ) + psiF.conductor) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (etaZero : ResidueField F)
    (hnormal : ∀ z : ResidueField F,
      (psiF.character
        ((A : F) * (breakCoordinate : F) * (teichmuller F z : F)) : ℂ) =
        psi0 (etaZero * z))
    (sigma : ResidueField F ≃+* ResidueField F)
    (hsigma : ∀ z, sigma z = z ^ p)
    (hpsi0 : ∀ z, psi0 (z ^ p) = psi0 z)
    (Q₀ : F) (hQ₀ : Q₀ ∈ lattice F (t : ℤ))
    (C : ResidueField F → F)
    (hC : ∀ X,
      C X - (teichmuller F (sigma.symm X) : F) ^ 2 * Q₀ ∈
        lattice F (T : ℤ)) :
    ∃ q : ResidueField F, ∀ X,
      (psiF.character ((A : F) * C X) : ℂ) = psi0 (q * X ^ 2) := by
  let qField : F := Q₀ / (breakCoordinate : F)
  have hqField : qField ∈ lattice F 0 := by
    apply (div_mem_lattice_iff F (breakCoordinate : F) Q₀ (t : ℤ) 0 hbreak).2
    simpa only [add_zero] using hQ₀
  let qInt : ringOfIntegers F :=
    ⟨qField, (mem_lattice_zero_iff F).1 hqField⟩
  let qBar : ResidueField F := reduce F qField hqField
  refine ⟨(etaZero * qBar) ^ p, ?_⟩
  intro X
  let Z : ResidueField F := sigma.symm X
  let c : F := (teichmuller F Z : F)
  let zRes : ResidueField F := Z ^ 2 * qBar
  have hcq : c ^ 2 * qField ∈ lattice F 0 := by
    have hc : c ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 (teichmuller F Z).property
    have hc2 : c ^ 2 ∈ lattice F 0 := by
      simpa only [pow_two, zero_add] using mul_mem_lattice F hc hc
    simpa only [zero_add] using mul_mem_lattice F hc2 hqField
  have hreduce : reduce F (c ^ 2 * qField) hcq = zRes := by
    let wInt : ringOfIntegers F := (teichmuller F Z) ^ 2 * qInt
    have hwcoe : (wInt : F) = c ^ 2 * qField := rfl
    change residueMap F wInt = zRes
    simp [wInt, zRes, qInt, qBar, reduce]
  have hunitDiff : c ^ 2 * qField - (teichmuller F zRes : F) ∈ lattice F 1 := by
    let wInt : ringOfIntegers F :=
      ⟨c ^ 2 * qField, (mem_lattice_zero_iff F).1 hcq⟩
    apply (residueMap_eq_residueMap_iff F wInt (teichmuller F zRes)).1
    change reduce F (c ^ 2 * qField) hcq = residueMap F (teichmuller F zRes)
    simpa only [residueMap_teichmuller] using hreduce
  have hbreakMem : (breakCoordinate : F) ∈ lattice F (t : ℤ) := by
    rw [mem_lattice, hbreak]
  have hQeq : (breakCoordinate : F) * qField = Q₀ := by
    dsimp [qField]
    field_simp [Units.ne_zero breakCoordinate]
  have hcanonicalDiff :
      c ^ 2 * Q₀ -
          (breakCoordinate : F) * (teichmuller F zRes : F) ∈
        lattice F (T : ℤ) := by
    have hmul := mul_mem_lattice F hbreakMem hunitDiff
    rw [hT]
    convert hmul using 1
    · exact rfl
    · rw [← hQeq]
      ring
  calc
    (psiF.character ((A : F) * C X) : ℂ) =
        (psiF.character ((A : F) * (c ^ 2 * Q₀)) : ℂ) :=
      scaledAddChar_eq_of_sub_mem_lattice F psiF A T hA (hC X)
    _ = (psiF.character
          ((A : F) * ((breakCoordinate : F) * (teichmuller F zRes : F))) : ℂ) :=
      scaledAddChar_eq_of_sub_mem_lattice F psiF A T hA hcanonicalDiff
    _ = psi0 (etaZero * zRes) := by
      simpa only [mul_assoc] using hnormal zRes
    _ = psi0 ((etaZero * qBar) ^ p * X ^ 2) := by
      have hZX : Z ^ p = X := by
        rw [← hsigma Z]
        exact sigma.apply_symm_apply X
      rw [← hpsi0 (etaZero * zRes)]
      congr 1
      dsimp only [zRes]
      rw [mul_pow, mul_pow]
      rw [show (Z ^ 2) ^ p = (Z ^ p) ^ 2 by
        calc
          (Z ^ 2) ^ p = Z ^ (2 * p) := (pow_mul Z 2 p).symm
          _ = Z ^ (p * 2) := by rw [mul_comm]
          _ = (Z ^ p) ^ 2 := pow_mul Z p 2]
      rw [hZX]
      ring
/-- The correction calculation in the actual common source coordinate.
The only nonquadratic input is the already-proved
`wildOdd_higherSymmetric_vanish`: degrees `3,\ldots,p-1` disappear and the
terminal norm terms cancel, while the genuine degree-two term is retained. -/
theorem wildOdd_actualSourceDisplayedCorrection_eq_pureQuadratic
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hodd : Module.finrank F K ≠ 2)
    (psiF : LocalAddCharData F)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (d dK : ℕ) (hdpos : 0 < d)
    (hchiF : chiF.conductor = 2 * d + 1)
    (hchiK : chiK.conductor = 2 * dK + 1)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q)
    (S : PhaseReductionResidualCoordinateSource F K)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (A : Fˣ)
    (hA : ord F (A : F) =
      (-((((t + 1 : ℕ) : ℤ) + psiF.conductor) : ℤ) : WithTop ℤ))
    (etaZero : ResidueField F)
    (hetaZero : ∀ z : ResidueField F,
      (psiF.character
        ((A : F) * (S.lowerUniformizer : F) ^ t *
          (teichmuller F z : F)) : ℂ) = C.lower (etaZero * z))
    (u : Kˣ) (n : F) (hnorm : norm F K (u : K) = n)
    (a : ℤ)
    (hu : ord K (u : K) = (wildOddUpperShift t d : WithTop ℤ))
    (hua : ord K (u : K) = (a : WithTop ℤ))
    (coordinate : K)
    (hcoordinate : ord K coordinate = ((dK : ℤ) : WithTop ℤ))
    (lift : ResidueField F → lattice K 0)
    (hlift : ∀ Z,
      reduce K (lift Z : K) (lift Z).property =
        PhaseReductionResidualCoordinateSource.residueEquiv hres Z) :
    ∃ q : ResidueField F, ∀ X : ResidueField F,
      (psiF.character
        ((A : F) *
          (phaseReductionNormHigherPart F K
              ((u : K) *
                (coordinate *
                  (lift ((C.frobeniusEquiv
                    (residueCharacteristic_eq_degree_of_positive_break
                      F K ht htpos pi hpi hgen)).symm X) : K))) -
            n * phaseReductionNormHigherPart F K
              (coordinate *
                (lift ((C.frobeniusEquiv
                  (residueCharacteristic_eq_degree_of_positive_break
                    F K ht htpos pi hpi hgen)).symm X) : K)))) : ℂ) =
        C.lower (q * X ^ 2) := by
  let p := Module.finrank F K
  let T := t + 1
  let hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  let sigma := C.frobeniusEquiv hchar
  let coordinateAt : ResidueField F → K := fun Z ↦
    coordinate * (lift Z : K)
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro hpEq
    exact hodd (by simpa only [p] using hpEq)
  have hT : T = t + 1 := rfl
  have hTtwo : 2 ≤ T := by simp only [T]; omega
  have htt : t ≤ T := by simp only [T]; omega
  have htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ) := by
    rw [hT]
    simpa only [p] using
      traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hdepthFormula := wildOdd_upperDepth_eq_of_conductors
    F K ht hres pi hpi hgen chiF chiK hcomp d dK hchiF hchiK hminimal
  let r : ℤ := (t : ℤ) - 2 * (dK : ℤ)
  have hrbreak : r + 2 * (dK : ℤ) = (t : ℤ) := by
    dsimp only [r]
    ring
  have hrbelow : 2 * d < t → r = (t : ℤ) - (2 * d : ℕ) := by
    intro hbelow
    have hdK := hdepthFormula.1 hbelow
    dsimp only [r]
    rw [hdK]
    push_cast
    ring
  have hrboundary : 2 * d = t → r = 0 := by
    intro hboundary
    have hdK := hdepthFormula.2.1 hboundary
    dsimp only [r]
    rw [hdK]
    push_cast
    omega
  have hrabove : t < 2 * d →
      r = (p : ℤ) * ((t : ℤ) - (2 * d : ℕ)) := by
    intro habove
    have hdK := hdepthFormula.2.2 habove
    dsimp only [r]
    push_cast at hdK ⊢
    linarith
  have hbase := wildOdd_upperCoordinate_numerics p (2 * d) t dK r hp hp2
    hrbreak hrbelow hrboundary hrabove
  have hcross := wildOdd_upperLift_numerics p (2 * d) t dK r hp hp2
    hrbreak hrbelow hrboundary hrabove
  have ha : a = (t : ℤ) - (2 * d : ℕ) := by
    apply WithTop.coe_injective
    rw [← hua, hu]
    simp only [wildOddUpperShift]
    push_cast
    ring
  let Q₀ : F := wildOddUpperQuadraticCorrection F K (u : K) coordinate
  have hQ₀ : Q₀ ∈ lattice F (t : ℤ) := by
    apply wildOddUpperQuadraticCorrection_mem F K p T t dK a hp hp2 hTtwo
      hchar rfl hres htt htrace (u : K) coordinate hua
      (le_of_eq hcoordinate.symm) (by simpa only [p, ha] using hbase.1)
      (by simpa only [p, ha] using hbase.2)
  let correction : ResidueField F → F := fun X ↦
    phaseReductionNormHigherPart F K
        ((u : K) * coordinateAt (sigma.symm X)) -
      n * phaseReductionNormHigherPart F K (coordinateAt (sigma.symm X))
  have hcorrection : ∀ X,
      correction X -
          (teichmuller F (sigma.symm X) : F) ^ 2 * Q₀ ∈
        lattice F (T : ℤ) := by
    intro X
    let Z := sigma.symm X
    let x := coordinateAt Z
    have hx : ((dK : ℤ) : WithTop ℤ) ≤ ord K x := by
      have hliftMem := (lift Z).property
      rw [mem_lattice] at hliftMem
      have hliftMem' : (0 : WithTop ℤ) ≤ ord K (lift Z : K) := by
        simpa using hliftMem
      rw [ord_mul, hcoordinate]
      simpa only [zero_add, add_comm] using
        add_le_add_left hliftMem' ((dK : ℤ) : WithTop ℤ)
    have HV := wildOdd_higherSymmetric_vanish F K ht htpos hres pi hpi hgen
      hodd chiF chiK hcomp d dK hdpos hchiF hchiK hminimal u x hu hx
    have hHigher := phaseReductionNormHigherPart_sub_eq_wildOddUpperCorrection
      F K p rfl (u : K) x
    rw [hnorm] at hHigher
    have hfull : correction X -
        wildOddUpperQuadraticCorrection F K (u : K) x ∈
          lattice F (T : ℤ) := by
      rw [hT]
      have hred := HV.quadraticReduction
      change
        (phaseReductionNormHigherPart F K ((u : K) * x) -
            n * phaseReductionNormHigherPart F K x) -
          wildOddUpperQuadraticCorrection F K (u : K) x ∈ _
      rw [hHigher]
      exact hred
    have hquad := wildOddUpperQuadraticCorrection_integralLift_teichmuller
      F K p T dK a hp hp2 hTtwo hchar rfl hres htrace
      (PhaseReductionResidualCoordinateSource.residueEquiv hres)
      (fun z ↦ rfl) (u : K) coordinate hua hcoordinate Z (lift Z)
      (hlift Z) (by simpa only [p, T, ha] using hcross.1)
      (by simpa only [p, T, ha] using hcross.2)
    have hsum := add_mem_lattice F hfull hquad
    convert hsum using 1
    all_goals
      dsimp only [x, Z, correction, coordinateAt, Q₀]
      ring_nf
  have hbreak : ord F ((S.lowerUniformizer ^ t : Fˣ) : F) =
      ((t : ℤ) : WithTop ℤ) := by
    simp only [Units.val_pow_eq_pow_val, ord_pow, S.lower_order]
    norm_num
  exact wildOdd_scaledQuadraticCorrection_eq_residueQuadratic F p psiF A
    (S.lowerUniformizer ^ t) t T hT hbreak hA C.lower
    etaZero hetaZero sigma
    (C.frobeniusEquiv_apply hchar) C.frobenius Q₀ hQ₀ correction
    hcorrection
end
end LanglandsFirstMainLemma
namespace LanglandsFirstMainLemma
noncomputable section
section High
variable (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra F K]
  [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition (data.twistData 1).conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hodd : Odd (Module.finrank F K)) (htpos : 0 < t)
  (hstrict : t + 1 < (data.twistData 1).conductor)
  (hupper : (data.twistData 1).conductor < 2 * (t + 1)) (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) = ((((data.twistData 1).conductor : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)
local instance upperResidualHighCorrection_neZero :
    NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance upperResidualHighCorrection_degreePrime :
    Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩
/-- In the actual strict High branch, the displayed higher-norm correction is
a pure quadratic residual character and therefore has no hidden affine term. -/
theorem wildOdd_actualHighCorrection_eq_pureQuadratic (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    ∃ q : ResidueField F, ∀ X : ResidueField F,
      let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let y := PhaseReductionResidualCoordinateSource.residueEquiv hres ((C.frobeniusEquiv hchar).symm X)
      let x : K := (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) * (teichmuller K y : K)
      let A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source.productRows
      let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source.productRows
      let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source.productRows
      (data.baseAddChar.character (A * (phaseReductionNormHigherPart F K (u*x) - n*phaseReductionNormHigherPart F K x)) : ℂ) = C.lower (q*X^2) := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A : Fˣ := normUnits F K source.productRows.alpha1 / gammaF
  let u : Kˣ := source.productRows.beta1 / source.productRows.alpha1
  let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source.productRows
  let a : ℤ := t - 2*d
  let coordinate : K := phaseReductionSourceCoordinate K S.upperUniformizer dK
  let lift : ResidueField F → lattice K 0 := fun Z ↦ ⟨teichmuller K (PhaseReductionResidualCoordinateSource.residueEquiv hres Z), (mem_lattice_zero_iff K).2 (teichmuller K _).property⟩
  have hne : Module.finrank F K ≠ 2 := by intro h; rw [h] at hodd; norm_num at hodd
  have hd : 0 < d := by have h := hF.conductor_eq; rw [hepsilon] at h; omega
  have hcF : (data.twistData 1).conductor = 2*d+1 := by simpa [hepsilon] using hF.conductor_eq
  have heK : epsilonK = 1 := (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source).trans hepsilon
  have hcK : chiK.conductor = 2*dK+1 := by simpa [heK] using hK.conductor_eq
  have hA : ord F (A:F) = (-((((t+1:ℕ):ℤ)+data.baseAddChar.conductor:ℤ):WithTop ℤ)) := by
    dsimp [A]; rw [Units.val_div_eq_div_val, ord_div, coe_normUnits, source.productRows.alpha_choice.norm_order, hgammaF]; rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]; congr 1; push_cast; ring
  have hn : norm F K (u:K) = n := by simp [u,n,highOddNormalizedNorm,highOddNormalizedRatio]
  have hua : ord K (u:K) = (a:WithTop ℤ) := by
    have ha : -(((data.twistData 1).conductor-(t+1):ℕ):ℤ)=a := by dsimp [a]; rw [Int.ofNat_sub hstrict.le, hcF]; push_cast; ring
    calc ord K (u:K) = ((-(((data.twistData 1).conductor-(t+1):ℕ):ℤ):ℤ):WithTop ℤ) := by simpa [u,highOddNormalizedRatio,Units.val_div_eq_div_val] using (highOddNormalizedRatio_order F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source.productRows)
         _ = (a:WithTop ℤ) := congrArg (fun z:ℤ ↦ (z:WithTop ℤ)) ha
  have hu : ord K (u:K) = (wildOddUpperShift t d:WithTop ℤ) := by simpa [a,wildOddUpperShift] using hua
  have hcoord : ord K coordinate = ((dK:ℤ):WithTop ℤ) := phaseReductionSourceCoordinate_order K S.upperUniformizer S.upper_order dK
  have hlift : ∀ Z, reduce K (lift Z:K) (lift Z).property = PhaseReductionResidualCoordinateSource.residueEquiv hres Z := fun Z ↦ residueMap_teichmuller K _
  let eta := wildOddUpperEtaZero S data.baseAddChar A t hA C
  have heta := wildOddUpperEtaZero_spec S data.baseAddChar A t hA C
  simpa [A,u,n,coordinate,lift,S,highOddExactCoefficient,highOddNormalizedRatio] using
    (wildOdd_actualSourceDisplayedCorrection_eq_pureQuadratic ht htpos hres pi hpi hgen hne data.baseAddChar (data.twistData 1) chiK hchi d dK hd hcF hcK hminimal S C A hA eta heta u n hn a hu hua coordinate hcoord lift hlift)
theorem wildOdd_actualHighDisplayed_above (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (units : ResidueField F → Kˣ)
    (hunits : ∀ X, let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen; let S := phaseReductionResidualCoordinateSource F K hres pi hpi; let y := PhaseReductionResidualCoordinateSource.residueEquiv hres ((C.frobeniusEquiv hchar).symm X); let x : K := (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) * teichmuller K y; let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source.productRows; (units X:K)=1+u*x) :
    ∃ q : ResidueField F, ∀ X, highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF (Module.finrank F K) (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen) C source X = C.lower (q*X^2) := by
  obtain ⟨q,hq⟩ := wildOdd_actualHighCorrection_eq_pureQuadratic F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source hepsilon C
  refine ⟨q, fun X ↦ ?_⟩
  have hd := highSourceDisplayed_polynomialDepths F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF (Module.finrank F K) (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen) C source hepsilon X
  have hh := highSourceDisplayed_exactCriticalTransport_above F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF (Module.finrank F K) (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen) C source hepsilon X (units X) (hunits X) hd.1 hd.2
  dsimp only at hh
  let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
  have htw : highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0 0 = 1 := LocalLamprechtPhaseData.criticalFunction_zero _
  have hno : highSourceNormFunction F K ht hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source jOne 0 = 1 := LocalLamprechtPhaseData.criticalFunction_zero _
  rw [htw, hno] at hh
  simp only [inv_one, one_mul] at hh
  exact hh.trans (hq X)
end High
section Low
variable (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t) (hres : residueDegree F K = 1) (pi : ringOfIntegers K) (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F} (data : FirstMainComputationalData F K globalChi globalPsi) (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K) {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition (data.twistData 1).conductor d epsilon) (hminimal : IsMinimalNormCharacterOrbitRepresentative F K (data.twistData 1)) (hchi : chiK.character = (data.twistData 1).character.compNorm) (hpsi : psiK.character = data.baseAddChar.character.compTrace) (hLow : (data.twistData 1).conductor ≤ t+1)
  (delta : Fˣ) (epsilon1 : Kˣ) (hdelta : ord F (delta:F) = ((((t+1:ℕ):ℤ)+data.baseAddChar.conductor:ℤ):WithTop ℤ)) (hepsilon1 : ord K (epsilon1:K) = (((t+1-(data.twistData 1).conductor:ℕ):ℤ):WithTop ℤ)) (hT : 2 ≤ t+1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1:F) = ((((data.twistData 1).conductor:ℤ)+data.baseAddChar.conductor:ℤ):WithTop ℤ)) (hgammaK : ord K (lowGammaK F K delta epsilon1:K) = (((chiK.conductor:ℤ)+psiK.conductor:ℤ):WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K (lowCriticalFloorDepth t) d (stationaryCoefficientClass F (quasiCharDataOfIsConductor F (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t+1) (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen (lowNormCharacterGenerator F K ht hres pi hpi hgen) (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))) data.baseAddChar (lowCriticalConductorDecomposition (t:=t) hT) delta hdelta) (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF (lowGammaF F K delta epsilon1) hgammaF))
  (table : LowConductorParameterTableData F K ht hres pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)
local instance upperResidualLowCorrection_neZero :
    NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
local instance upperResidualLowCorrection_degreePrime :
    Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩
include hminimal chiK hchi hLow hepsilon1 in
/-- In the actual Low branch, the displayed higher-norm correction is a pure
quadratic residual character for both the strict and boundary preparations. -/
theorem wildOdd_actualLowCorrection_eq_pureQuadratic (hodd : Odd (Module.finrank F K)) (hepsilon : epsilon=1) (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    ∃ q : ResidueField F, ∀ X : ResidueField F, let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht (by omega) pi hpi hgen; let z := (C.frobeniusEquiv hchar).symm X; let x := phaseReductionUpperSourceDisplacement F K pi d z; let A := lowOddExactCoefficient (F:=F) (K:=K) (P:=P) (hT:=hT); let u := lowNormalizedRatio F K epsilon1 P; let n := lowOddNormalizedNorm (F:=F) (K:=K) (P:=P) (hT:=hT); (data.baseAddChar.character (A*(phaseReductionNormHigherPart F K (u*x)-n*phaseReductionNormHigherPart F K x)):ℂ)=C.lower (q*X^2) := by
  have htpos : 0<t := by omega
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let coordinate : K := phaseReductionSourceCoordinate K S.upperUniformizer d
  let lift : ResidueField F → lattice K 0 := fun Z ↦ ⟨phaseReductionUpperSourceDisplacement F K pi d Z / coordinate, by dsimp [coordinate,S]; exact phaseReductionUpperSourceDisplacement_div_mem F K hres pi hpi Z⟩
  let A : Fˣ := P.alpha/delta
  let u : Kˣ := epsilon1*P.beta₁/P.alpha₁
  let n : F := lowOddNormalizedNorm (F:=F) (K:=K) (P:=P) (hT:=hT)
  let a : ℤ := t-2*d
  have hne : Module.finrank F K ≠2 := by intro e; rw [e] at hodd; norm_num at hodd
  have hcF : (data.twistData 1).conductor=2*d+1 := by simpa [hepsilon] using hF.conductor_eq
  have hd : 0<d := by have hm:=hF.conductor_gt_one; rw [hcF] at hm; omega
  let precision := lowNormPolynomialPrecision F K ht hres pi hpi hgen (data.twistData 1) hminimal chiK hchi hF hLow
  have hcK : chiK.conductor=2*d+1 := by simpa [precision,hepsilon] using precision.sourceDecomposition.conductor_eq
  have hmin : ∀ (mu : NormCharacter F K) q, IsMultiplicativeConductor F (mu.1*(data.twistData 1).character) q → (data.twistData 1).conductor ≤ q := hminimal
  have hA : ord F (A:F)=(-((((t+1:ℕ):ℤ)+data.baseAddChar.conductor:ℤ):WithTop ℤ)) := by dsimp [A]; rw [Units.val_div_eq_div_val,ord_div]; change ord F (norm F K (P.alpha₁:K))-ord F (delta:F)=_; rw [P.alphaRepresentative.norm_order,hdelta]; simp
  have hn : norm F K (u:K)=n := by dsimp [u,n]; simpa [lowOddNormalizedNorm,lowNormalizedRatio,Units.val_div_eq_div_val,Units.val_mul] using lowNormalizedRatio_norm F K epsilon1 P
  have ha : ((t+1-(data.twistData 1).conductor:ℕ):ℤ)=a := by dsimp [a]; rw [Int.ofNat_sub hLow,hcF]; push_cast; ring
  have hua : ord K (u:K)=(a:WithTop ℤ) := by rw [show ord K (u:K)=((t+1-(data.twistData 1).conductor:ℕ):WithTop ℤ) by simpa [u,lowNormalizedRatio,Units.val_div_eq_div_val,Units.val_mul] using lowNormalizedRatio_order F K epsilon1 hepsilon1 P]; exact congrArg (fun z:ℤ ↦ (z:WithTop ℤ)) ha
  have hu : ord K (u:K)=(wildOddUpperShift t d:WithTop ℤ) := by simpa [a,wildOddUpperShift] using hua
  have hcoord : ord K coordinate=((d:ℤ):WithTop ℤ) := phaseReductionSourceCoordinate_order K S.upperUniformizer S.upper_order d
  have hlift : ∀ Z, reduce K (lift Z:K) (lift Z).property=PhaseReductionResidualCoordinateSource.residueEquiv hres Z := fun Z ↦ phaseReductionUpperSourceDisplacement_reduces F K hres pi hpi Z
  let eta := wildOddUpperEtaZero S data.baseAddChar A t hA C
  have heta := wildOddUpperEtaZero_spec S data.baseAddChar A t hA C
  obtain ⟨q,hq⟩ := wildOdd_actualSourceDisplayedCorrection_eq_pureQuadratic ht htpos hres pi hpi hgen hne data.baseAddChar (data.twistData 1) chiK hchi d d hd hcF hcK hmin S C A hA eta heta u n hn a hu hua coordinate hcoord lift hlift
  refine ⟨q, fun X ↦ ?_⟩
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen
  let Z := (C.frobeniusEquiv hchar).symm X
  have hx : coordinate*(lift Z:K)=phaseReductionUpperSourceDisplacement F K pi d Z := by dsimp [lift]; field_simp [coordinate,Units.ne_zero (phaseReductionSourceCoordinate K S.upperUniformizer d)]
  have hh:=hq X
  rw [show (C.frobeniusEquiv (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi hgen)).symm X=Z by rfl,hx] at hh
  simpa [A,u,n,S,Z,hchar,lowOddExactCoefficient,lowNormalizedRatio,Units.val_div_eq_div_val,Units.val_mul] using hh
theorem wildOdd_actualLowDisplayed_below (hodd : Odd (Module.finrank F K)) (hepsilon : epsilon=1) (hstrict : (data.twistData 1).conductor<t+1) (C : FrobeniusResidualAddCharData F (Module.finrank F K)) (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table) (units : ResidueField F→Kˣ)
    (hunits : ∀ X, let hchar:=residueCharacteristic_eq_degree_of_positive_break F K ht (by have hm:=hF.conductor_gt_one; omega) pi hpi hgen; let z:=(C.frobeniusEquiv hchar).symm X; let x:=phaseReductionUpperSourceDisplacement F K pi d z; let u:=lowNormalizedRatio F K epsilon1 P; (units X:K)=1+u*x) :
    ∃ q, ∀ X, lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K) (residueCharacteristic_eq_degree_of_positive_break F K ht (by omega) pi hpi hgen) C W X = lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table X * C.lower (q*X^2) := by
  obtain ⟨q,hq⟩ := wildOdd_actualLowCorrection_eq_pureQuadratic F K ht hres pi hpi hgen data chiK hF hminimal hchi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hodd hepsilon C
  refine ⟨q, fun X ↦ ?_⟩
  have hh:=lowSourceDisplayed_exactCriticalTransport_strict F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table W hepsilon hstrict C X (units X) (hunits X)
  dsimp only at hh
  let j : OddNormIndex F K := ⟨1,one_ne_zero⟩
  have hz : lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j 0=1 := LocalLamprechtPhaseData.criticalFunction_zero _
  rw [hz] at hh
  calc
    _ = _ := hh
    _ = _ := by rw [inv_one,mul_one,hq X]
theorem wildOdd_actualLowDisplayed_boundary (hodd : Odd (Module.finrank F K)) (hepsilon : epsilon=1) (hboundary : (data.twistData 1).conductor=t+1) (C : FrobeniusResidualAddCharData F (Module.finrank F K)) (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table) (units : ResidueField F→Kˣ)
    (hunits : ∀ X, let hchar:=residueCharacteristic_eq_degree_of_positive_break F K ht (by have hm:=hF.conductor_gt_one; omega) pi hpi hgen; let z:=(C.frobeniusEquiv hchar).symm X; let x:=phaseReductionUpperSourceDisplacement F K pi d z; let u:=lowNormalizedRatio F K epsilon1 P; (units X:K)=1+u*x) :
    ∃ q, ∀ X, let hchar:=residueCharacteristic_eq_degree_of_positive_break F K ht (by omega) pi hpi hgen; let u:=lowNormalizedRatio F K epsilon1 P
      let hu : ord K u=(0:WithTop ℤ) := by simpa [hboundary] using lowNormalizedRatio_order F K epsilon1 hepsilon1 P
      let nO : ringOfIntegers F := ⟨norm F K u, by rw [← mem_lattice_zero_iff,mem_lattice,ord_norm,hres,one_nsmul,hu]; exact le_rfl⟩
      let tauX:=residueMap F nO*X; let j : OddNormIndex F K:=⟨1,one_ne_zero⟩; lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K) hchar C W X = lowSourceBaseFunction F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table X * (lowSourceNormFunction F K ht hres pi hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j tauX)⁻¹ * C.lower (q*X^2) := by
  obtain ⟨q,hq⟩ := wildOdd_actualLowCorrection_eq_pureQuadratic F K ht hres pi hpi hgen data chiK hF hminimal hchi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF P hodd hepsilon C
  refine ⟨q, fun X ↦ ?_⟩
  have hh:=lowSourceDisplayed_exactCriticalTransport_boundary F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table W hepsilon hboundary C X (units X) (hunits X)
  dsimp only at hh ⊢
  exact hh.trans (congrArg (fun z:ℂ ↦ _*_*z) (hq X))
end Low
end
end LanglandsFirstMainLemma
namespace LanglandsFirstMainLemma
noncomputable section
universe u v
/-! ## Natural upper polar coefficient from the actual Lamprecht row -/
/-- Rewriting the actual stationary ratio before applying trace preserves
the lower scalar and its order. -/
theorem wildOdd_stationaryRatio_trace_value
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {psiF : LocalAddCharData F} {psiK : LocalAddCharData K}
    (hpsi : psiK.character = psiF.character.compTrace)
    (beta gamma : K) (A : F) (y delta z : K)
    (hratio : beta / gamma = algebraMap F K A * y) :
    (psiK.character (beta * delta ^ 2 * z / gamma) : ℂ) =
      psiF.character (A * trace F K (y * delta ^ 2 * z)) := by
  have harg : beta * delta ^ 2 * z / gamma =
      algebraMap F K A * (y * delta ^ 2 * z) := by
    rw [div_eq_mul_inv] at hratio ⊢
    calc
      beta * delta ^ 2 * z * gamma⁻¹ =
          (beta * gamma⁻¹) * (delta ^ 2 * z) := by ring
      _ = (algebraMap F K A * y) * (delta ^ 2 * z) := by rw [hratio]
      _ = algebraMap F K A * (y * delta ^ 2 * z) := by ring
  rw [hpsi, ContinuousAddChar.compTrace_apply, harg]
  exact congrArg (fun x : F => (psiF.character x : ℂ)) (by
    convert (Algebra.trace F K).map_smul A (y * delta ^ 2 * z) using 1 <;>
      simp [Algebra.smul_def])
/-- The polar coefficient of the real odd Lamprecht constructor, after only
the canonical residue-field equivalence, is the normalized trace coefficient
times the initial stationary residue. -/
theorem LocalLamprechtPhaseData.odd_upperPolarInLowerCoordinate_eq
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiK : LocalQuasiCharData K}
    {psiF : LocalAddCharData F} {psiK : LocalAddCharData K}
    (p : ℕ) (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (hpsi : psiK.character = psiF.character.compTrace)
    (d : ℕ) (hm : chiK.conductor = 2 * d + 1)
    (hlarge : 1 < chiK.conductor)
    (Gamma : AdmissibleGamma K chiK psiK)
    (delta : Kˣ) (hdelta : ord K (delta : K) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice K
      ((chiK.conductor : ℤ) - (chiK.conductor : ℤ)))
    (hbeta : latticeQuotientMk K
        (sub_le_sub_left
          (criticalPolar_stationaryDepth K chiK d hm hlarge).int_le_conductor
          (chiK.conductor : ℤ)) beta =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (criticalPolar_stationaryDepth K chiK d hm hlarge)
        Gamma Gamma.property)
    (A : F) (y : K) (betaInv initial : ResidueField F)
    (hratio : (beta : K) / ((Gamma : Kˣ) : K) =
      algebraMap F K A * y)
    (hnormalizedTrace : ∀ z : ResidueField F,
      (psiF.character
        (A * trace F K
          (y * (delta : K) ^ 2 *
            (teichmuller K
              (PhaseReductionResidualCoordinateSource.residueEquiv
                (F := F) (K := K) hres z) : K))) : ℂ) =
        C.lower ((betaInv * initial) * z)) :
    (PhaseReductionResidualCoordinateSource.residueEquiv
        (F := F) (K := K) hres).symm
      (LocalLamprechtPhaseData.polarCoefficient
        (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta hbeta)
          (C.upper hres) (C.upper_ne_one hres)) =
      betaInv * initial := by
  letI := residueFieldFintype K
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  apply e.injective
  rw [e.apply_symm_apply]
  unfold LocalLamprechtPhaseData.polarCoefficient
  dsimp only
  apply finiteAddCharCoefficient_unique
  apply AddChar.ext
  intro zK
  let zF : ResidueField F := e.symm zK
  have hzK : e zF = zK := e.apply_symm_apply zK
  have hzmem : (teichmuller K zK : K) ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2 (teichmuller K zK).property
  have hraw := lamprechtResidualAddChar_integral_lift K chiK psiK d hm
    hlarge Gamma delta hdelta beta hbeta (teichmuller K zK : K) hzmem
  have hreduce : reduce K (teichmuller K zK : K) hzmem = zK := by
    simp [reduce]
  rw [AddChar.mulShift_apply]
  calc
    C.upper hres (e (betaInv * initial) * zK) =
        C.lower ((betaInv * initial) * zF) := by
      rw [← hzK, ← e.map_mul, C.upper_apply_equiv]
    _ = psiF.character
        (A * trace F K
          (y * (delta : K) ^ 2 * (teichmuller K (e zF) : K))) :=
      (hnormalizedTrace zF).symm
    _ = psiK.character
        ((beta : K) * (delta : K) ^ 2 *
          (teichmuller K (e zF) : K) / ((Gamma : Kˣ) : K)) := by
      exact (wildOdd_stationaryRatio_trace_value hpsi
        (beta : K) ((Gamma : Kˣ) : K) A y (delta : K)
          (teichmuller K (e zF) : K) hratio).symm
    _ = lamprechtResidualAddChar K chiK psiK d hm hlarge Gamma delta hdelta
        zK := by
      rw [hzK]
      simpa only [hreduce] using hraw.symm
/-! ## Coefficient pairs and exact function comparison -/
/-- The polar/affine pair of one odd upstairs residual function.  This type
is deliberately upper-specific: the lower coefficient table is assembled in
its own node. -/
structure WildOddUpperCoefficientPair (k : Type*) where
  polar : k
  affine : k
  deriving DecidableEq
@[ext]
theorem WildOddUpperCoefficientPair.ext {k : Type*}
    {P Q : WildOddUpperCoefficientPair k}
    (hpolar : P.polar = Q.polar) (haffine : P.affine = Q.affine) : P = Q := by
  cases P
  cases Q
  simp_all
/-- Equality of complete positive-polar functions determines both
coefficients. -/
theorem criticalPolarFunction_coefficients_eq_of_function_eq
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2)
    {A₁ A₂ : k}
    (phi₁ : CriticalPolarFunction k psi0 A₁)
    (phi₂ : CriticalPolarFunction k psi0 A₂)
    (hfun : ∀ x, phi₁ x = phi₂ x) :
    A₁ = A₂ ∧
      phi₁.affineCoefficient hchar hpsi0 =
        phi₂.affineCoefficient hchar hpsi0 := by
  have hpolar : A₁ = A₂ := by
    apply AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hpsi0)
    apply AddChar.ext
    intro z
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply]
    have h₁ := phi₁.map_add 1 z
    have h₂ := phi₂.map_add 1 z
    rw [hfun, hfun, hfun] at h₁
    have hcommon : phi₂ 1 * phi₂ z ≠ 0 :=
      mul_ne_zero (phi₂.ne_zero 1) (phi₂.ne_zero z)
    apply mul_left_cancel₀ hcommon
    simpa using h₁.symm.trans h₂
  subst A₂
  refine ⟨rfl, ?_⟩
  have heq : phi₁ = phi₂ := CriticalPolarFunction.ext _ _ hfun
  subst phi₂
  rfl
/-- Product of two complete positive-polar functions. -/
noncomputable def CriticalPolarFunction.mul
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A₁ A₂ : k}
    (phi₁ : CriticalPolarFunction k psi0 A₁)
    (phi₂ : CriticalPolarFunction k psi0 A₂) :
    CriticalPolarFunction k psi0 (A₁ + A₂) where
  toFun x := phi₁ x * phi₂ x
  ne_zero' x := mul_ne_zero (phi₁.ne_zero x) (phi₂.ne_zero x)
  map_add' x y := by
    rw [phi₁.map_add, phi₂.map_add]
    calc
      phi₁ x * phi₁ y * psi0 (A₁ * (x * y)) *
          (phi₂ x * phi₂ y * psi0 (A₂ * (x * y))) =
        (phi₁ x * phi₂ x) * (phi₁ y * phi₂ y) *
          (psi0 (A₁ * (x * y)) * psi0 (A₂ * (x * y))) := by ring
      _ = (phi₁ x * phi₂ x) * (phi₁ y * phi₂ y) *
          psi0 ((A₁ + A₂) * (x * y)) := by
        rw [← psi0.map_add_eq_mul]
        congr 1
        ring
@[simp]
theorem CriticalPolarFunction.mul_apply
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A₁ A₂ : k}
    (phi₁ : CriticalPolarFunction k psi0 A₁)
    (phi₂ : CriticalPolarFunction k psi0 A₂) (x : k) :
    phi₁.mul phi₂ x = phi₁ x * phi₂ x := rfl
/-- Inverse after the literal argument scaling `x ↦ c*x`.  The sign and
the square on the polar coefficient encode the manuscript's inverse norm-row
orientation. -/
noncomputable def CriticalPolarFunction.invScale
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A) (c : k) :
    CriticalPolarFunction k psi0 (-(c ^ 2 * A)) where
  toFun x := (phi (c * x))⁻¹
  ne_zero' x := inv_ne_zero (phi.ne_zero _)
  map_add' x y := by
    calc
      (phi (c * (x + y)))⁻¹ =
          (phi (c * x) * phi (c * y) *
            psi0 (A * ((c * x) * (c * y))))⁻¹ := by
        rw [mul_add, phi.map_add]
      _ = (phi (c * x))⁻¹ * (phi (c * y))⁻¹ *
          psi0 (-(c ^ 2 * A) * (x * y)) := by
        rw [mul_inv_rev, mul_inv_rev, ← AddChar.map_neg_eq_inv]
        have harg : -(A * ((c * x) * (c * y))) =
            -(c ^ 2 * A) * (x * y) := by ring
        rw [harg]
        ring
@[simp]
theorem CriticalPolarFunction.invScale_apply
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A) (c x : k) :
    phi.invScale c x = (phi (c * x))⁻¹ := rfl
theorem CriticalPolarFunction.affineCoefficient_mul
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} {A₁ A₂ : k}
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi₁ : CriticalPolarFunction k psi0 A₁)
    (phi₂ : CriticalPolarFunction k psi0 A₂) :
    (phi₁.mul phi₂).affineCoefficient hchar hpsi0 =
      phi₁.affineCoefficient hchar hpsi0 +
        phi₂.affineCoefficient hchar hpsi0 := by
  apply CriticalPolarFunction.affineCoefficient_unique hchar hpsi0
  intro x
  rw [CriticalPolarFunction.mul_apply, phi₁.eq_quadratic hchar hpsi0,
    phi₂.eq_quadratic hchar hpsi0, ← psi0.map_add_eq_mul]
  congr 1
  ring
theorem CriticalPolarFunction.affineCoefficient_invScale
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} {A : k}
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) (c : k) :
    (phi.invScale c).affineCoefficient hchar hpsi0 =
      -(c * phi.affineCoefficient hchar hpsi0) := by
  apply CriticalPolarFunction.affineCoefficient_unique hchar hpsi0
  intro x
  rw [CriticalPolarFunction.invScale_apply,
    phi.eq_quadratic hchar hpsi0, ← AddChar.map_neg_eq_inv]
  congr 1
  field_simp [Ring.two_ne_zero hchar]
  ring
/-- The neutral complete critical function, used only to certify that a
genuine homogeneous quadratic correction has no affine part. -/
noncomputable def CriticalPolarFunction.one
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} :
    CriticalPolarFunction k psi0 0 where
  toFun _ := 1
  ne_zero' _ := one_ne_zero
  map_add' x y := by simp
@[simp]
theorem CriticalPolarFunction.one_apply
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} (x : k) :
    (CriticalPolarFunction.one : CriticalPolarFunction k psi0 0) x = 1 :=
  rfl
theorem CriticalPolarFunction.affineCoefficient_one
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2) :
    ((CriticalPolarFunction.one : CriticalPolarFunction k psi0 0).affineCoefficient
      hchar hpsi0) = 0 := by
  apply CriticalPolarFunction.affineCoefficient_unique hchar hpsi0
  intro x
  simp
/-- Function equality with a base row times a homogeneous quadratic gives
the base affine coefficient, without first guessing the correction's polar
coefficient. -/
theorem CriticalPolarFunction.affineCoefficient_of_base_mul_quadratic
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2)
    {A ABase : k}
    (upper : CriticalPolarFunction k psi0 A)
    (base : CriticalPolarFunction k psi0 ABase) (q : k)
    (hfun : ∀ x, upper x = base x * psi0 (q * x ^ 2)) :
    upper.affineCoefficient hchar hpsi0 =
      base.affineCoefficient hchar hpsi0 := by
  let comparison := CriticalPolarFunction_mulPureQuadratic base q
  have hcoeff := criticalPolarFunction_coefficients_eq_of_function_eq
    hpsi0 hchar upper comparison (by
      intro x
      simpa only [comparison, CriticalPolarFunction_mulPureQuadratic_apply]
        using hfun x)
  rw [hcoeff.2, CriticalPolarFunction_affineCoefficient_mulPureQuadratic]
/-- The same coefficient extraction for a base row divided by a scaled norm
row.  This is the exact boundary orientation. -/
theorem CriticalPolarFunction.affineCoefficient_of_base_mul_invScale_quadratic
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2)
    {A ABase ANorm : k}
    (upper : CriticalPolarFunction k psi0 A)
    (base : CriticalPolarFunction k psi0 ABase)
    (normRow : CriticalPolarFunction k psi0 ANorm)
    (c q : k)
    (hfun : ∀ x, upper x =
      base x * (normRow (c * x))⁻¹ * psi0 (q * x ^ 2)) :
    upper.affineCoefficient hchar hpsi0 =
      base.affineCoefficient hchar hpsi0 -
        c * normRow.affineCoefficient hchar hpsi0 := by
  let lower := base.mul (normRow.invScale c)
  let comparison := CriticalPolarFunction_mulPureQuadratic lower q
  have hcoeff := criticalPolarFunction_coefficients_eq_of_function_eq
    hpsi0 hchar upper comparison (by
      intro x
      simpa only [comparison, lower,
        CriticalPolarFunction_mulPureQuadratic_apply,
        CriticalPolarFunction.mul_apply, CriticalPolarFunction.invScale_apply,
        mul_assoc] using hfun x)
  rw [hcoeff.2, CriticalPolarFunction_affineCoefficient_mulPureQuadratic,
    CriticalPolarFunction.affineCoefficient_mul,
    CriticalPolarFunction.affineCoefficient_invScale]
  ring
/-- A genuine pure quadratic factor has zero hidden affine coefficient. -/
theorem CriticalPolarFunction.affineCoefficient_eq_zero_of_pureQuadratic
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2)
    {A : k} (upper : CriticalPolarFunction k psi0 A) (q : k)
    (hfun : ∀ x, upper x = psi0 (q * x ^ 2)) :
    upper.affineCoefficient hchar hpsi0 = 0 := by
  have h := CriticalPolarFunction.affineCoefficient_of_base_mul_quadratic
    hpsi0 hchar upper
      (CriticalPolarFunction.one : CriticalPolarFunction k psi0 0) q (by
        intro x
        simpa using hfun x)
  rw [h, CriticalPolarFunction.affineCoefficient_one]
/-! ## Canonical source, upper-to-lower, and inverse-Frobenius directions -/
/-- The complete common-coordinate statement used by the upper row.  Both
selected coordinates are derived from one supplied PhaseReduction source;
the lower source coordinate is the exact norm of the upper one. -/
structure WildOddUpperCoordinateTransport
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (S : PhaseReductionResidualCoordinateSource F K)
    {dF dK : ℕ} (deltaF : Fˣ) (deltaK : Kˣ)
    (hdeltaF : ord F (deltaF : F) = ((dF : ℤ) : WithTop ℤ))
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ)) : Prop where
  common_source :
    phaseReductionSourceCoordinate F S.lowerUniformizer dF =
      normUnits F K
        (phaseReductionSourceCoordinate K S.upperUniformizer dF)
  upper_selected :
    criticalPolarScaledCoordinate K
        (PhaseReductionResidualCoordinateSource.transportUnit
          (LamprechtCriticalCoordinate.odd deltaK hdeltaK)
          S.upperUniformizer S.upper_order)
        (phaseReductionSourceCoordinate K S.upperUniformizer dK) = deltaK
  lower_selected :
    criticalPolarScaledCoordinate F
        (PhaseReductionResidualCoordinateSource.transportUnit
          (LamprechtCriticalCoordinate.odd deltaF hdeltaF)
          S.lowerUniformizer S.lower_order)
        (phaseReductionSourceCoordinate F S.lowerUniformizer dF) = deltaF
/-- Exact upper/source and upper/lower transport, with no reconstructed or
independently rescaled coordinate. -/
theorem wildOdd_upperCoordinateTransport
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (S : PhaseReductionResidualCoordinateSource F K)
    {dF dK : ℕ} (deltaF : Fˣ) (deltaK : Kˣ)
    (hdeltaF : ord F (deltaF : F) = ((dF : ℤ) : WithTop ℤ))
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ)) :
    WildOddUpperCoordinateTransport S deltaF deltaK hdeltaF hdeltaK where
  common_source :=
    PhaseReductionResidualCoordinateSource.lowerSourceCoordinate_eq_norm
      S dF
  upper_selected :=
    PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq
      deltaK hdeltaK S.upperUniformizer S.upper_order
  lower_selected :=
    PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq
      deltaF hdeltaF S.lowerUniformizer S.lower_order
/-- The natural upper coefficient transported only through the canonical
residue equivalence, before the displayed inverse-Frobenius reindexing. -/
noncomputable def LocalLamprechtPhaseData.upperPolarInLowerCoordinate
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    (D : LocalLamprechtPhaseData K chiK psiK)
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1) : ResidueField F :=
  (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres))
theorem LocalLamprechtPhaseData.upperInLowerCoordinate_polarCoefficient
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    (D : LocalLamprechtPhaseData K chiK psiK)
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1) :
    ∀ x : ResidueField F,
      PhaseReductionResidualTransport.upperInLowerCoordinate
        (PhaseReductionResidualCoordinateSource.residueEquiv hres)
        (C.upper_apply_equiv hres)
        (D.toCriticalPolarFunction (C.upper hres) (C.upper_ne_one hres)) x =
          D.criticalFunction
            (PhaseReductionResidualCoordinateSource.residueEquiv hres x) := by
  intro x
  rw [PhaseReductionResidualTransport.upperInLowerCoordinate_apply,
    D.toCriticalPolarFunction_apply]
/-- The exact inverse-Frobenius display: the argument moves through
`Fr⁻¹`, while the transported polar coefficient moves through forward
Frobenius, hence to its `p`th power. -/
theorem LocalLamprechtPhaseData.displayedUpper_exactDirection
    {F : Type u} {K : Type v}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    (D : LocalLamprechtPhaseData K chiK psiK)
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1) :
    (∀ x : ResidueField F,
      D.displayedInLowerCoordinate p hchar hres C x =
        D.criticalFunction
          (PhaseReductionResidualCoordinateSource.residueEquiv hres
            ((C.frobeniusEquiv hchar).symm x))) ∧
      C.frobeniusEquiv hchar (D.upperPolarInLowerCoordinate p C hres) =
        D.upperPolarInLowerCoordinate p C hres ^ p := by
  constructor
  · exact D.displayedInLowerCoordinate_apply p hchar hres C
  · exact C.frobeniusEquiv_apply hchar _
private theorem compact_zsmul_one (a : ℤ) :
    a • ((1 : ℤ) : WithTop ℤ) = (a : WithTop ℤ) := by
  cases a with
  | ofNat n => simp
  | negSucc n => rw [negSucc_zsmul]; norm_num [Int.negSucc_eq]
/-- Initial residue at a signed depth in the actual source uniformizer. -/
noncomputable def sourceInitialResidue
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ) (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (a : ℤ) (x : E) (hx : ord E x = (a : WithTop ℤ)) : ResidueField E :=
  reduce E (x / (varpi : E) ^ a) (by
    rw [mem_lattice, ord_div, hx, ord_zpow, hvarpi, compact_zsmul_one]
    simp)
/-- Exact order at a signed source depth makes the initial residue nonzero.
This uses only the defining valuation equality, including when the depth is
negative. -/
theorem sourceInitialResidue_ne_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ) (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (a : ℤ) (x : E) (hx : ord E x = (a : WithTop ℤ)) :
    sourceInitialResidue E varpi hvarpi a x hx ≠ 0 := by
  intro hz
  unfold sourceInitialResidue reduce at hz
  rw [residueMap_eq_zero_iff, mem_lattice, ord_div, hx, ord_zpow, hvarpi,
    compact_zsmul_one] at hz
  have hnot : ¬ (((1 : ℤ) : WithTop ℤ) ≤ (a : WithTop ℤ) - a) := by
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, sub_self]
    norm_num
  exact hnot hz
/-- Negation is transported without changing the signed source depth. -/
theorem sourceInitialResidue_neg
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ) (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (r : ℤ) (x : E) (hx : ord E x = (r : WithTop ℤ)) :
    sourceInitialResidue E varpi hvarpi r (-x) (by simpa using hx) =
      -sourceInitialResidue E varpi hvarpi r x hx := by
  unfold sourceInitialResidue reduce
  have hmem : x / (varpi : E) ^ r ∈ lattice E 0 := by
    rw [mem_lattice, ord_div, hx, ord_zpow, hvarpi, compact_zsmul_one]
    simp
  let xO : ringOfIntegers E :=
    ⟨x / (varpi : E) ^ r, (mem_lattice_zero_iff E).1 hmem⟩
  have heq :
      (⟨(-x) / (varpi : E) ^ r, by
        simpa only [neg_div] using (ringOfIntegers E).neg_mem xO.property⟩ :
          ringOfIntegers E) = -xO := by
    apply Subtype.ext
    change (-x) / (varpi : E) ^ r = -(x / (varpi : E) ^ r)
    rw [neg_div]
  rw [heq, map_neg]
/-- The normalized critical trace quotient is exactly the initial residue in
the real PhaseReduction source coordinate. -/
private theorem normalizedTrace_initial_eq_sourceInitialResidue
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ) (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (r : ℤ) (d t : ℕ) (y : E) (hy : ord E y = (r : WithTop ℤ))
    (hdepth : r + 2 * (d : ℤ) = (t : ℤ))
    (hx : y * ((varpi : E) ^ d) ^ 2 / (varpi : E) ^ t ∈ lattice E 0) :
    reduce E (y * ((varpi : E) ^ d) ^ 2 / (varpi : E) ^ t) hx =
      sourceInitialResidue E varpi hvarpi r y hy := by
  unfold sourceInitialResidue
  congr 1
  rw [show (varpi : E) ^ t =
      (varpi : E) ^ r * (varpi : E) ^ (2 * d) by
    calc
      (varpi : E) ^ t = (varpi : E) ^ (t : ℤ) := by rw [zpow_natCast]
      _ = (varpi : E) ^ (r + 2 * (d : ℤ)) := by rw [hdepth]
      _ = (varpi : E) ^ r * (varpi : E) ^ (2 * (d : ℤ)) :=
        zpow_add₀ (Units.ne_zero varpi) _ _
      _ = (varpi : E) ^ r * (varpi : E) ^ (2 * d) := by
        rw [← zpow_natCast]
        congr 2]
  rw [show ((varpi : E) ^ d) ^ 2 = (varpi : E) ^ (2 * d) by
    rw [← pow_mul]
    congr 1
    omega]
  field_simp [Units.ne_zero varpi]
private theorem compact_reduce_norm_unit_pow
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (v : K) (hvord : ord K v = (0 : WithTop ℤ)) :
    let hv : v ∈ lattice K 0 := by rw [mem_lattice, hvord]; exact le_rfl
    let hn : algebraMap F K (norm F K v) ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap, ord_norm, hres, one_nsmul, hvord,
        nsmul_zero]
      exact le_rfl
    reduce K (algebraMap F K (norm F K v)) hn =
      (reduce K v hv) ^ Module.finrank F K := by
  dsimp only
  classical
  have hv : v ∈ lattice K 0 := by rw [mem_lattice, hvord]; exact le_rfl
  let vO : ringOfIntegers K :=
    ⟨v, (mem_lattice_zero_iff K).1 hv⟩
  let cO : Gal(K/F) → ringOfIntegers K := fun σ ↦
    ⟨σ v, by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_galoisConjugate, hvord]
      exact le_rfl⟩
  let nO : ringOfIntegers K :=
    ⟨algebraMap F K (norm F K v), by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_algebraMap, ord_norm,
        hres, one_nsmul, hvord, nsmul_zero]
      exact le_rfl⟩
  have hnO : nO = ∏ σ : Gal(K/F), cO σ := by
    apply Subtype.ext
    dsimp only [nO, cO]
    change algebraMap F K (norm F K v) =
      algebraMap (ringOfIntegers K) K
        (∏ σ : Gal(K/F), (⟨σ v, _⟩ : ringOfIntegers K))
    rw [map_prod]
    change algebraMap F K (norm F K v) = ∏ σ : Gal(K/F), σ v
    exact Algebra.norm_eq_prod_automorphisms F v
  have hconj (σ : Gal(K/F)) : residueMap K (cO σ) = residueMap K vO := by
    apply (residueMap_eq_residueMap_iff K _ _).2
    have htop : lowerRamificationGroup F K (0 : ℤ) = ⊤ :=
      PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break
        F K ht (by omega)
    have hσ : σ ∈ lowerRamificationGroup F K (0 : ℤ) := by
      rw [htop]
      trivial
    rw [← congruentAtDepth_iff_sub_mem_lattice]
    simpa only [cO, vO, zero_add] using
      (mem_lowerRamificationGroup F K σ (0 : ℤ)).1 hσ
        (⟨v, (mem_lattice_zero_iff K).1 hv⟩ : ringOfIntegers K)
  change residueMap K nO = (residueMap K vO) ^ Module.finrank F K
  rw [hnO, map_prod]
  calc
    ∏ σ : Gal(K/F), residueMap K (cO σ) =
        ∏ _σ : Gal(K/F), residueMap K vO := by
      apply Finset.prod_congr rfl
      intro σ _
      exact hconj σ
    _ = (residueMap K vO) ^ Fintype.card Gal(K/F) := by simp
    _ = (residueMap K vO) ^ Module.finrank F K := by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
/-- Exact signed-depth norm residue in the real PhaseReduction source:
`d₀ = ζ^p`, including negative signed depths. -/
theorem sourceInitialResidue_norm_eq_pow
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (S : PhaseReductionResidualCoordinateSource F K)
    (a : ℤ) (u : K) (hu : ord K u = (a : WithTop ℤ)) :
    let p := Module.finrank F K
    let hn : ord K (algebraMap F K (norm F K u)) =
        (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
      have hram : ramificationIndex F K = p := by
        have h := finrank_eq_ramificationIndex_mul_residueDegree F K
        rw [hres, mul_one] at h
        exact h.symm
      rw [ord_algebraMap, hram, ord_norm, hres, one_nsmul, hu,
        ← WithTop.coe_nsmul]
      congr 1
    sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
        (algebraMap F K (norm F K u)) hn =
      (sourceInitialResidue K S.upperUniformizer S.upper_order a u hu) ^ p := by
  dsimp only
  classical
  let p := Module.finrank F K
  have hu0 : u ≠ 0 := (ord_ne_top_iff K).1 (by rw [hu]; exact WithTop.coe_ne_top)
  let uU : Kˣ := Units.mk0 u hu0
  let vU : Kˣ := uU / S.upperUniformizer ^ a
  have hvcoe : (vU : K) = u / (S.upperUniformizer : K) ^ a := by
    simp only [vU, uU, Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0]
  have hvord : ord K (vU : K) = (0 : WithTop ℤ) := by
    rw [hvcoe, ord_div, hu, ord_zpow, S.upper_order, compact_zsmul_one]
    simp
  have hram : ramificationIndex F K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at h
    exact h.symm
  have hn : ord K (algebraMap F K (norm F K u)) =
      (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, ord_norm, hres, one_nsmul, hu,
      ← WithTop.coe_nsmul]
    congr 1
  let hpi : (ValuativeRel.valuation K).IsUniformizer
      (S.upperUniformizer : K) :=
    (ord_eq_one_iff_isUniformizer K _).1 S.upper_order
  let toG₁ : Gal(K/F) → lowerRamificationGroup F K (1 : ℤ) := fun σ ↦
    ⟨σ, by
      rw [PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break
        F K ht (by omega)]
      trivial⟩
  let q : Kˣ := ∏ σ : Gal(K/F),
    ramificationRatioUnit F K 1 (toG₁ σ) (S.upperUniformizer : K) hpi
  have hqmem : q ∈ unitFiltration K 1 := by
    apply Subgroup.prod_mem
    intro σ _
    exact ramificationRatioUnit_mem F K 1 (toG₁ σ)
      (S.upperUniformizer : K) hpi
  have hqcoe : (q : K) =
      algebraMap F K (norm F K (S.upperUniformizer : K)) /
        (S.upperUniformizer : K) ^ p := by
    dsimp only [q]
    change (Units.coeHom K) (∏ σ : Gal(K/F),
      ramificationRatioUnit F K 1 (toG₁ σ)
        (S.upperUniformizer : K) hpi) = _
    rw [map_prod]
    simp_rw [show ∀ σ : Gal(K/F),
      (Units.coeHom K)
          (ramificationRatioUnit F K 1 (toG₁ σ)
            (S.upperUniformizer : K) hpi) =
        σ (S.upperUniformizer : K) / (S.upperUniformizer : K) from
      fun σ ↦ coe_ramificationRatioUnit F K 1 (toG₁ σ)
        (S.upperUniformizer : K) hpi]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
    rw [Algebra.norm_eq_prod_automorphisms]
  have hqpow : CongruentAtDepth 1 (((q : Kˣ) ^ a : K)) 1 := by
    have hm := (unitFiltration K 1).zpow_mem hqmem a
    have hh := (mem_unitFiltration_succ K 0 _).1 hm
    simp only [Units.val_zpow_eq_zpow_val] at hh
    convert hh using 1 <;> norm_num
  have hfactor :
      algebraMap F K (norm F K u) /
          (S.upperUniformizer : K) ^ ((p : ℤ) * a) =
        ((q : Kˣ) ^ a : K) * algebraMap F K (norm F K (vU : K)) := by
    have huU : uU = S.upperUniformizer ^ a * vU := by simp [vU]
    have hqU : q =
        Units.map (algebraMap F K) (normUnits F K S.upperUniformizer) /
          S.upperUniformizer ^ p := by
      apply Units.ext
      simpa only [hqcoe, Units.val_div_eq_div_val, Units.coe_map,
        MonoidHom.coe_coe, coe_normUnits, Units.val_pow_eq_pow_val]
    have hunit :
        Units.map (algebraMap F K) (normUnits F K uU) /
            S.upperUniformizer ^ ((p : ℤ) * a) =
          q ^ a * Units.map (algebraMap F K) (normUnits F K vU) := by
      rw [hqU, huU, map_mul, map_mul, map_zpow]
      rw [show S.upperUniformizer ^ p =
          S.upperUniformizer ^ (p : ℤ) by norm_num]
      rw [div_zpow, zpow_mul, map_zpow]
      simp only [div_eq_mul_inv]
      ac_rfl
    simpa only [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val,
      Units.val_mul, Units.coe_map, MonoidHom.coe_coe, coe_normUnits,
      uU, Units.val_mk0] using congrArg (Units.val : Kˣ → K) hunit
  have hnvord : ord K (algebraMap F K (norm F K (vU : K))) =
      (0 : WithTop ℤ) := by
    rw [ord_algebraMap, ord_norm, hres, one_nsmul, hvord, nsmul_zero]
  have hprod : CongruentAtDepth 1
      (((q : Kˣ) ^ a : K) * algebraMap F K (norm F K (vU : K)))
      (algebraMap F K (norm F K (vU : K))) := by
    simpa only [one_mul] using CongruentAtDepth.mul_right
      (a := algebraMap F K (norm F K (vU : K))) (by simp [hnvord]) hqpow
  calc
    sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
        (algebraMap F K (norm F K u)) hn =
        reduce K
          (algebraMap F K (norm F K u) /
            (S.upperUniformizer : K) ^ ((p : ℤ) * a)) (by
              rw [mem_lattice, ord_div, hn, ord_zpow, S.upper_order,
                compact_zsmul_one]
              simp) := rfl
    _ = reduce K (algebraMap F K (norm F K (vU : K))) (by
          rw [mem_lattice, hnvord]
          exact le_rfl) := by
      apply (reduce_eq_reduce_iff (F := K) _ _).2
      rw [hfactor]
      exact hprod
    _ = (reduce K (vU : K) (by rw [mem_lattice, hvord]; exact le_rfl)) ^ p := by
      simpa only [p] using compact_reduce_norm_unit_pow F K ht hres (vU : K) hvord
    _ = (sourceInitialResidue K S.upperUniformizer S.upper_order a u hu) ^ p := by
      unfold sourceInitialResidue
      congr 2

/-- The same signed norm identity downstairs.  The normalization first
compares the exact lower norm coordinate with an order-zero norm, transports
that residue through the residue-degree-one equivalence, and then identifies
it with the actual signed upper norm coordinate.  In particular this proof
does not introduce a residue scalar when `a < 0`. -/
theorem sourceInitialResidue_norm_downstairs_eq_pow
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (S : PhaseReductionResidualCoordinateSource F K)
    (a : ℤ) (u : K) (hu : ord K u = (a : WithTop ℤ)) :
    let p := Module.finrank F K
    let e := PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) hres
    let hn : ord F (norm F K u) = (a : WithTop ℤ) := by
      rw [ord_norm, hres, one_nsmul, hu]
    sourceInitialResidue F S.lowerUniformizer S.lower_order a
        (norm F K u) hn =
      (e.symm
        (sourceInitialResidue K S.upperUniformizer S.upper_order a u hu)) ^ p := by
  dsimp only
  classical
  let p := Module.finrank F K
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  have hu0 : u ≠ 0 :=
    (ord_ne_top_iff K).1 (by rw [hu]; exact WithTop.coe_ne_top)
  let uU : Kˣ := Units.mk0 u hu0
  let vU : Kˣ := uU / S.upperUniformizer ^ a
  have hvcoe : (vU : K) = u / (S.upperUniformizer : K) ^ a := by
    simp only [vU, uU, Units.val_div_eq_div_val,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hvord : ord K (vU : K) = (0 : WithTop ℤ) := by
    rw [hvcoe, ord_div, hu, ord_zpow, S.upper_order, compact_zsmul_one]
    simp
  have huU : uU = S.upperUniformizer ^ a * vU := by
    simp [vU]
  have hnormU : normUnits F K uU =
      S.lowerUniformizer ^ a * normUnits F K vU := by
    rw [huU, map_mul, map_zpow, S.lower_eq_norm]
  have hnormNormalized :
      norm F K u / (S.lowerUniformizer : F) ^ a =
        norm F K (vU : K) := by
    have h := congrArg (Units.val : Fˣ → F) hnormU
    simp only [uU, Units.val_mk0, Units.val_mul,
      Units.val_zpow_eq_zpow_val, coe_normUnits] at h
    rw [h]
    have hpow : (S.lowerUniformizer : F) ^ a ≠ 0 := by
      simpa only [Units.val_zpow_eq_zpow_val] using
        Units.ne_zero (S.lowerUniformizer ^ a)
    exact mul_div_cancel_left₀ _ hpow
  have hnormV : ord F (norm F K (vU : K)) = (0 : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, hvord]
  have hnormVK : ord K (algebraMap F K (norm F K (vU : K))) =
      (0 : WithTop ℤ) := by
    rw [ord_algebraMap, ord_norm, hres, one_nsmul, hvord, nsmul_zero]
  have hn : ord F (norm F K u) = (a : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, hu]
  have hFInitial :
      sourceInitialResidue F S.lowerUniformizer S.lower_order a
          (norm F K u) hn =
        sourceInitialResidue F S.lowerUniformizer S.lower_order 0
          (norm F K (vU : K)) hnormV := by
    unfold sourceInitialResidue
    congr 1
    simpa only [zpow_zero, div_one] using hnormNormalized
  have hvInitial :
      sourceInitialResidue K S.upperUniformizer S.upper_order 0
          (vU : K) hvord =
        sourceInitialResidue K S.upperUniformizer S.upper_order a u hu := by
    unfold sourceInitialResidue
    congr 1
    simpa only [zpow_zero, div_one] using hvcoe
  have hleft :
      e (sourceInitialResidue F S.lowerUniformizer S.lower_order 0
          (norm F K (vU : K)) hnormV) =
        sourceInitialResidue K S.upperUniformizer S.upper_order 0
          (algebraMap F K (norm F K (vU : K))) hnormVK := by
    have hnormVmem : norm F K (vU : K) ∈ lattice F 0 := by
      rw [mem_lattice, hnormV]
      exact le_rfl
    let nO : ringOfIntegers F :=
      ⟨norm F K (vU : K), (mem_lattice_zero_iff F).1 hnormVmem⟩
    unfold sourceInitialResidue
    simp only [zpow_zero, div_one]
    rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
    unfold reduce
    change extensionResidueMap F K (residueMap F nO) =
      residueMap K
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) nO)
    exact
      Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation F) (ValuativeRel.valuation K) nO
  have hsigned := sourceInitialResidue_norm_eq_pow F K ht htpos hres S a u hu
  have hzero := sourceInitialResidue_norm_eq_pow F K ht htpos hres S 0
    (vU : K) hvord
  dsimp only at hsigned hzero
  have htransport :
      sourceInitialResidue K S.upperUniformizer S.upper_order 0
          (algebraMap F K (norm F K (vU : K))) hnormVK =
        sourceInitialResidue K S.upperUniformizer S.upper_order
          ((p : ℤ) * a) (algebraMap F K (norm F K u)) (by
            have hram : ramificationIndex F K = p := by
              have h := finrank_eq_ramificationIndex_mul_residueDegree F K
              rw [hres, mul_one] at h
              exact h.symm
            rw [ord_algebraMap, hram, ord_norm, hres, one_nsmul, hu,
              ← WithTop.coe_nsmul]
            congr 1) := by
    calc
      _ = (sourceInitialResidue K S.upperUniformizer S.upper_order 0
          (vU : K) hvord) ^ p := hzero
      _ = (sourceInitialResidue K S.upperUniformizer S.upper_order a u hu) ^ p :=
        congrArg (fun z ↦ z ^ p) hvInitial
      _ = _ := hsigned.symm
  apply e.injective
  rw [hFInitial, hleft, map_pow, e.apply_symm_apply]
  exact htransport.trans hsigned
/-- The two strict manuscript initial coordinates of `u-n`.  The equal-order
boundary is supplied only by `UpperResidualNormalization`. -/
theorem sourceInitialResidue_u_sub_norm_extremeCases
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (S : PhaseReductionResidualCoordinateSource F K)
    (a : ℤ) (u : K) (hu : ord K u = (a : WithTop ℤ))
    (n : F) (hnorm : n = norm F K u) :
    let p := Module.finrank F K
    let ζ := sourceInitialResidue K S.upperUniformizer S.upper_order a u hu
    let d₀ := ζ ^ p
    (0 < a → ∃ hsub : ord K (u - algebraMap F K n) = (a : WithTop ℤ),
      sourceInitialResidue K S.upperUniformizer S.upper_order a
        (u - algebraMap F K n) hsub = ζ) ∧
    (a < 0 → ∃ hsub : ord K (u - algebraMap F K n) =
        (((p : ℤ) * a : ℤ) : WithTop ℤ),
      sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
        (u - algebraMap F K n) hsub = -d₀) := by
  subst n
  dsimp only
  let p := Module.finrank F K
  have hp1 : 1 < p := PrimeCyclicExtension.degree_prime F K |>.one_lt
  have hram : ramificationIndex F K = p := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at h
    exact h.symm
  have hn : ord K (algebraMap F K (norm F K u)) =
      (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, hram, ord_norm, hres, one_nsmul, hu,
      ← WithTop.coe_nsmul]
    congr 1
  let ζ := sourceInitialResidue K S.upperUniformizer S.upper_order a u hu
  have hnormResidue :
      sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
          (algebraMap F K (norm F K u)) hn = ζ ^ p := by
    simpa only [p, ζ] using
      sourceInitialResidue_norm_eq_pow F K ht htpos hres S a u hu
  constructor
  · intro ha
    have hlt : a < (p : ℤ) * a := by nlinarith
    have hs : ord K (u - algebraMap F K (norm F K u)) =
        (a : WithTop ℤ) := by
      rw [sub_eq_add_neg, ord_add_eq_min K]
      · rw [ord_neg, hu, hn, min_eq_left]
        exact WithTop.coe_le_coe.mpr hlt.le
      · rw [ord_neg, hu, hn]
        exact fun h ↦ (ne_of_lt hlt) (WithTop.coe_eq_coe.mp h)
    refine ⟨hs, ?_⟩
    unfold sourceInitialResidue
    apply (reduce_eq_reduce_iff (F := K) _ _).2
    rw [congruentAtDepth_iff_sub_mem_lattice]
    have hpow : ord K ((S.upperUniformizer : K) ^ a) =
        (a : WithTop ℤ) := by
      rw [ord_zpow, S.upper_order, compact_zsmul_one]
    rw [show (u - algebraMap F K (norm F K u)) /
        (S.upperUniformizer : K) ^ a - u / (S.upperUniformizer : K) ^ a =
          -(algebraMap F K (norm F K u) /
            (S.upperUniformizer : K) ^ a) by ring]
    rw [mem_lattice, ord_neg, ord_div, hn, hpow]
    norm_cast
    omega
  · intro ha
    have hlt : (p : ℤ) * a < a := by nlinarith
    have hs : ord K (u - algebraMap F K (norm F K u)) =
          (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
        rw [sub_eq_add_neg, ord_add_eq_min K]
        · rw [ord_neg, hu, hn, min_eq_right]
          exact WithTop.coe_le_coe.mpr hlt.le
        · rw [ord_neg, hu, hn]
          exact fun h ↦ (ne_of_gt hlt) (WithTop.coe_eq_coe.mp h)
    refine ⟨hs, ?_⟩
    have hnneg : ord K (-algebraMap F K (norm F K u)) =
          (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
        simpa only [ord_neg] using hn
    have hneg :
          sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
              (-algebraMap F K (norm F K u)) hnneg =
            -sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
              (algebraMap F K (norm F K u)) hn := by
        have hint : algebraMap F K (norm F K u) /
            (S.upperUniformizer : K) ^ ((p : ℤ) * a) ∈ lattice K 0 := by
          rw [mem_lattice, ord_div, hn, ord_zpow, S.upper_order,
            compact_zsmul_one]
          simp
        let xO : ringOfIntegers K :=
          ⟨algebraMap F K (norm F K u) /
            (S.upperUniformizer : K) ^ ((p : ℤ) * a),
              (mem_lattice_zero_iff K).1 hint⟩
        unfold sourceInitialResidue reduce
        simp only [neg_div]
        change residueMap K (-xO) = -residueMap K xO
        exact map_neg (residueMap K) xO
    have hdominant :
          sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
              (u - algebraMap F K (norm F K u)) hs =
            -sourceInitialResidue K S.upperUniformizer S.upper_order ((p : ℤ) * a)
              (algebraMap F K (norm F K u)) hn := by
        rw [← hneg]
        unfold sourceInitialResidue
        apply (reduce_eq_reduce_iff (F := K) _ _).2
        rw [congruentAtDepth_iff_sub_mem_lattice]
        have hpow : ord K ((S.upperUniformizer : K) ^ ((p : ℤ) * a)) =
            (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
          rw [ord_zpow, S.upper_order, compact_zsmul_one]
        change (u - algebraMap F K (norm F K u)) /
              (S.upperUniformizer : K) ^ ((p : ℤ) * a) -
            (-algebraMap F K (norm F K u)) /
              (S.upperUniformizer : K) ^ ((p : ℤ) * a) ∈ lattice K 1
        rw [show (u - algebraMap F K (norm F K u)) /
              (S.upperUniformizer : K) ^ ((p : ℤ) * a) -
            (-algebraMap F K (norm F K u)) /
              (S.upperUniformizer : K) ^ ((p : ℤ) * a) =
              u / (S.upperUniformizer : K) ^ ((p : ℤ) * a) by ring]
        rw [mem_lattice, ord_div, hu, hpow]
        norm_cast
        omega
    rw [hdominant, hnormResidue]
/-! ## The three manuscript upper rows -/
def wildOddUpperPairBelow {k : Type*} [Mul k] (eta gamma : k) :
    WildOddUpperCoefficientPair k :=
  ⟨eta, eta * gamma⟩
def wildOddUpperPairBoundary {k : Type*} [Ring k]
    (p : ℕ) (etaZero dZero gamma gammaZero : k) :
    WildOddUpperCoefficientPair k :=
  ⟨-etaZero * (dZero ^ p - dZero),
    etaZero * dZero * (gamma - gammaZero)⟩
def wildOddUpperPairAbove {k : Type*} [Ring k]
    (p : ℕ) (eta dZero : k) : WildOddUpperCoefficientPair k :=
  ⟨-(dZero ^ (p - 1) * eta), 0⟩
/-- Algebraic normalization shared by the three upper rows.  `betaInv` is
the manuscript's `β₀⁻¹`; its `p`th power is the last-layer coefficient
`η₀`. -/
structure WildOddUpperPolarNormalization (k : Type*) [Field k] (p : ℕ) where
  betaInv : k
  etaZero : k
  zeta : k
  dZero : k
  eta : k
  betaInv_pow : betaInv ^ p = etaZero
  dZero_eq : zeta ^ p = dZero
  eta_eq : eta = etaZero * dZero
/-- Natural-to-displayed polar transport, with the upper-to-lower residue
equivalence already applied. -/
theorem wildOdd_displayedPolar_from_natural
    {k : Type*} [Field k] (p : ℕ)
    (N : WildOddUpperPolarNormalization k p) (initial : k) :
    (N.betaInv * initial) ^ p = N.etaZero * initial ^ p := by
  rw [mul_pow, N.betaInv_pow]
theorem wildOdd_upperPolar_below
    {k : Type*} [Field k] (p : ℕ)
    (N : WildOddUpperPolarNormalization k p) :
    N.etaZero * N.zeta ^ p =
      (wildOddUpperPairBelow N.eta (1 : k)).polar := by
  change N.etaZero * N.zeta ^ p = N.eta
  rw [N.dZero_eq, N.eta_eq]
theorem wildOdd_upperPolar_boundary
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime]
    (hchar : CharP k p)
    (N : WildOddUpperPolarNormalization k p) :
    N.etaZero * (N.zeta - N.dZero) ^ p =
      (wildOddUpperPairBoundary p N.etaZero N.dZero 0 0).polar := by
  haveI : CharP k p := hchar
  rw [sub_pow_char, N.dZero_eq]
  simp only [WildOddUpperCoefficientPair.polar, wildOddUpperPairBoundary]
  ring
theorem wildOdd_upperPolar_above
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2)
    (N : WildOddUpperPolarNormalization k p) :
    N.etaZero * (-N.dZero) ^ p =
      (wildOddUpperPairAbove p N.eta N.dZero).polar := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hpodd
  rw [hpOdd.neg_pow, N.eta_eq]
  have hpow : N.dZero ^ p = N.dZero ^ (p - 1) * N.dZero := by
    have hpEq : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    calc
      N.dZero ^ p = N.dZero ^ (p - 1 + 1) :=
        congrArg (fun n : ℕ => N.dZero ^ n) hpEq.symm
      _ = N.dZero ^ (p - 1) * N.dZero := pow_succ _ _
  rw [hpow]
  simp only [WildOddUpperCoefficientPair.polar, wildOddUpperPairAbove]
  ring
/-! ## Complete upper coefficient rows -/
/-- The coefficient pair carried by one complete critical-polar function. -/
noncomputable def CriticalPolarFunction.upperCoefficientPair
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A)
    (hpsi0 : psi0 ≠ 1) (hchar : ringChar k ≠ 2) :
    WildOddUpperCoefficientPair k :=
  ⟨A, phi.affineCoefficient hchar hpsi0⟩

/-- At even conductor parity the complete residual function is constant one,
so both displayed upper coefficients vanish. -/
def wildOddUpperPairEven {k : Type*} [Zero k] :
    WildOddUpperCoefficientPair k :=
  ⟨0, 0⟩

theorem CriticalPolarFunction.upperCoefficientPair_eq_even
    {k : Type*} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2)
    {A : k} (upper : CriticalPolarFunction k psi0 A)
    (hfun : ∀ x, upper x = 1) :
    upper.upperCoefficientPair hpsi0 hchar = wildOddUpperPairEven := by
  let one : CriticalPolarFunction k psi0 0 := CriticalPolarFunction.one
  have hcoeff := criticalPolarFunction_coefficients_eq_of_function_eq
    hpsi0 hchar upper one (by
      intro x
      simpa only [one, CriticalPolarFunction.one_apply] using hfun x)
  apply WildOddUpperCoefficientPair.ext
  · exact hcoeff.1
  · exact hcoeff.2.trans
      (CriticalPolarFunction.affineCoefficient_one hpsi0 hchar)
/-! ## Representative translations -/
/-- A representative change is exposed together with all exact consequences
needed by the upstairs assembly: polar invariance, complete-function and affine
translation, and invariance of the elementary-times-Hasse factor. -/
structure WildOddUpperRepresentativeTranslationCertificate
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) : Prop where
  polar_transport :
    selected.polarCoefficient psi0 hpsi0 =
      source.polarCoefficient psi0 hpsi0
  function_transport : ∀ x,
    selected.criticalFunction x = source.criticalFunction x *
      psi0 (R.translationCoefficient psi0 hpsi0 * x)
  affine_transport :
    selected.affineCoefficient psi0 hpsi0 hchar =
      source.affineCoefficient psi0 hpsi0 hchar +
        R.translationCoefficient psi0 hpsi0
  complete_factor_transport : source.elementaryFactor * source.criticalFactor =
    selected.elementaryFactor * selected.criticalFactor
theorem wildOdd_upperRepresentativeTranslation
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    WildOddUpperRepresentativeTranslationCertificate R psi0 hpsi0 hchar := by
  refine
    { polar_transport := ?_
      function_transport := R.criticalFunction_eq_mul_translation psi0 hpsi0
      affine_transport := ?_
      complete_factor_transport := ?_ }
  · have hsource := congrArg
      (fun D : LocalLamprechtPhaseData E chi psi =>
        D.polarCoefficient psi0 hpsi0) R.source_eq
    have hselected := congrArg
      (fun D : LocalLamprechtPhaseData E chi psi =>
        D.polarCoefficient psi0 hpsi0) R.selected_eq
    exact hselected.trans (hsource.symm)
  · have hsource := congrArg
      (fun D : LocalLamprechtPhaseData E chi psi =>
        D.affineCoefficient psi0 hpsi0 hchar) R.source_eq
    have hselected := congrArg
      (fun D : LocalLamprechtPhaseData E chi psi =>
        D.affineCoefficient psi0 hpsi0 hchar) R.selected_eq
    calc
      selected.affineCoefficient psi0 hpsi0 hchar =
          (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
            R.hdelta R.beta' R.hbeta').affineCoefficient psi0 hpsi0 hchar :=
        hselected
      _ = (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
            R.hdelta R.beta R.hbeta).affineCoefficient psi0 hpsi0 hchar +
          R.translationCoefficient psi0 hpsi0 := by
        change criticalAffineCoefficient E chi psi R.d R.hm R.hlarge R.Gamma
            R.delta R.hdelta psi0 hpsi0 hchar R.beta' R.hbeta' =
          criticalAffineCoefficient E chi psi R.d R.hm R.hlarge R.Gamma
              R.delta R.hdelta psi0 hpsi0 hchar R.beta R.hbeta +
            R.translationCoefficient psi0 hpsi0
        simpa only [OddRepresentativeChangeData.translationCoefficient] using
          criticalAffineCoefficient_changeRepresentative E chi psi R.d R.hm
            R.hlarge R.Gamma R.delta R.hdelta psi0 hpsi0 hchar R.beta
              R.beta' R.hbeta R.hbeta'
      _ = source.affineCoefficient psi0 hpsi0 hchar +
          R.translationCoefficient psi0 hpsi0 := by
        exact congrArg
          (fun z => z + R.translationCoefficient psi0 hpsi0) hsource.symm
  · have hsource := congrArg
      (fun D : LocalLamprechtPhaseData E chi psi =>
        D.elementaryFactor * D.criticalFactor) R.source_eq
    have hselected := congrArg
      (fun D : LocalLamprechtPhaseData E chi psi =>
        D.elementaryFactor * D.criticalFactor) R.selected_eq
    calc
      source.elementaryFactor * source.criticalFactor =
          (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
            R.hdelta R.beta R.hbeta).elementaryFactor *
          (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
            R.hdelta R.beta R.hbeta).criticalFactor := hsource
      _ = (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
            R.hdelta R.beta' R.hbeta').elementaryFactor *
          (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
            R.hdelta R.beta' R.hbeta').criticalFactor :=
        by
          letI := residueFieldFintype E
          simpa only [LocalLamprechtPhaseData.elementaryFactor,
            LocalLamprechtPhaseData.criticalFactor] using
              lamprechtOdd_complete_representative_independent E chi psi R.d
                R.hm R.hlarge R.Gamma R.delta R.hdelta R.beta R.beta'
                  R.hbeta R.hbeta'
      _ = selected.elementaryFactor * selected.criticalFactor := hselected.symm
/-- Transporting a source-tied phase between definitionally equal local
character data does not alter its polar coefficient. -/
theorem transportLocalLamprechtPhaseData_polarCoefficient
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1) :
    (transportLocalLamprechtPhaseData hchi hpsi D).polarCoefficient
        psi0 hpsi0 = D.polarCoefficient psi0 hpsi0 := by
  have hc := LocalQuasiCharData.ext_character E hchi
  have hp := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  rfl
/-- Once the natural coefficient is known, forward Frobenius gives the
manuscript's displayed coefficient in exactly the stated direction. -/
theorem LocalLamprechtPhaseData.displayedPolar_eq_of_natural
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    (D : LocalLamprechtPhaseData K chiK psiK)
    (p : ℕ) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (hres : residueDegree F K = 1)
    (betaInv etaZero initial : ResidueField F)
    (hnatural : D.upperPolarInLowerCoordinate p C hres = betaInv * initial)
    (hbeta : betaInv ^ p = etaZero) :
    C.frobeniusEquiv hchar (D.upperPolarInLowerCoordinate p C hres) =
      etaZero * initial ^ p := by
  rw [hnatural, map_mul, C.frobeniusEquiv_apply,
    C.frobeniusEquiv_apply, hbeta]
noncomputable def wildOddUpperPolarNormalizationOfSource (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) (hchar : residueCharacteristic F = p) (C : FrobeniusResidualAddCharData F p) (etaZero zeta : ResidueField F) : WildOddUpperPolarNormalization (ResidueField F) p where
  betaInv := (C.frobeniusEquiv hchar).symm etaZero
  etaZero := etaZero
  zeta := zeta
  dZero := zeta ^ p
  eta := etaZero * zeta ^ p
  betaInv_pow := by rw [← C.frobeniusEquiv_apply hchar]; exact (C.frobeniusEquiv hchar).apply_symm_apply etaZero
  dZero_eq := rfl
  eta_eq := rfl

/-- The valuation calculation behind the actual High source unit.  An
element of order `-v` times the upper source lift lies at the genuine
post-drop depth `(t+2)/2`; parity is retained through the exact conductor
equation. -/
private theorem highTauDisplacement_mem_of_order
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t T dK v : ℕ}
    (hT : T = t + 1) (hv : 0 < v)
    (hmK : 2 * dK + 1 = T + Module.finrank F K * v)
    (hodd : Odd (Module.finrank F K))
    (u x : K) (hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ))
    (hx : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x) :
    u * x ∈ lattice K ((((t + 2) / 2 : ℕ) : ℤ)) := by
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
  rw [mem_lattice, ord_mul, hu]
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
    _ ≤ ((-(v : ℤ) : ℤ) : WithTop ℤ) + ord K x := by
      simpa only [add_comm] using
        add_le_add_left hx (((-(v : ℤ) : ℤ) : WithTop ℤ))
section HighActual

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (htpos : 0 < s + 1)
  (hstrict : s + 1 + 1 < (data.twistData 1).conductor)
  (hupper : (data.twistData 1).conductor < 2 * (s + 1 + 1))
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF)

local instance upperResidualHighActual_neZero : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance upperResidualHighActual_degreePrime :
    Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩
local instance upperResidualHighActual_residueFintype :
    Fintype (ResidueField F) := residueFieldFintype F

private theorem highActual_normalizedRatio_order (hepsilon : epsilon = 1) :
    ord K
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows : K) =
      (((s + 1 : ℤ) - 2 * (d : ℤ) : ℤ) : WithTop ℤ) := by
  have hconductor : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have hshift :
      -(((data.twistData 1).conductor - (s + 1 + 1) : ℕ) : ℤ) =
        (s + 1 : ℤ) - 2 * (d : ℤ) := by
    rw [Int.ofNat_sub hstrict.le, hconductor]
    push_cast
    ring
  calc
    ord K
        (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows : K) =
        ((-(((data.twistData 1).conductor - (s + 1 + 1) : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) := by
            simpa [Units.val_div_eq_div_val] using
              highOddNormalizedRatio_order F K ht hres pi hpi hgen data
                chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
                  hupper gammaF hgammaF source.productRows
    _ = (((s + 1 : ℤ) - 2 * (d : ℤ) : ℤ) : WithTop ℤ) :=
      congrArg (fun z : ℤ ↦ (z : WithTop ℤ)) hshift

noncomputable def highActualNormalization (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    WildOddUpperPolarNormalization (ResidueField F) (Module.finrank F K) := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  let u : K := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let a : ℤ := (s + 1 : ℤ) - 2 * (d : ℤ)
  let hu : ord K u = (a : WithTop ℤ) := by
    simpa only [u, a] using highActual_normalizedRatio_order F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source hepsilon
  let zeta := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    (sourceInitialResidue K S.upperUniformizer S.upper_order a u hu)
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  let hA := wildOddHighNormalizationCoefficient_order F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  exact wildOddUpperPolarNormalizationOfSource F (Module.finrank F K) hchar
    C etaZero zeta

/-- The actual High normalization parameter `dZero` is nonzero for the
source reason: its defining signed-depth initial residue has exact order.
No orbit-minimality or boundary noncancellation is used. -/
theorem highActualNormalization_dZero_ne_zero
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
    N.dZero ≠ 0 := by
  dsimp only
  let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source hepsilon C
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let u : K := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let a : ℤ := (s + 1 : ℤ) - 2 * (d : ℤ)
  have hu : ord K u = (a : WithTop ℤ) := by
    simpa only [u, a] using highActual_normalizedRatio_order F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source hepsilon
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order a u hu
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  have hzetaK : zetaK ≠ 0 :=
    sourceInitialResidue_ne_zero K S.upperUniformizer S.upper_order a u hu
  have hzeta : e.symm zetaK ≠ 0 := by
    intro hz
    apply hzetaK
    have hz' := congrArg e hz
    simpa only [map_zero, e.apply_symm_apply] using hz'
  have hNzeta : N.zeta = e.symm zetaK := rfl
  rw [← N.dZero_eq, hNzeta]
  exact pow_ne_zero _ hzeta

/-- The actual inverse-Frobenius displayed source displacement `u*x` lies
in the positive lattice at the dropped norm-character depth.  Both `u` and
`x` come literally from `source.productRows` and the common source
coordinate. -/
theorem highActualSourceUx_mem_lattice
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      htpos pi hpi hgen
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
      ((C.frobeniusEquiv hchar).symm X)
    let x : K :=
      (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
        (teichmuller K y : K)
    let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    u * x ∈ lattice K (((((s + 1) + 2) / 2 : ℕ) : ℤ)) := by
  dsimp only
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
    ((C.frobeniusEquiv hchar).symm X)
  let x : K := (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
    (teichmuller K y : K)
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let v := (data.twistData 1).conductor - ((s + 1) + 1)
  have hv : 0 < v := by dsimp only [v]; omega
  have hepsilonK : epsilonK = 1 :=
    (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source).trans hepsilon
  have hmKconductor := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen (data.twistData 1) chiK hminimal hchi hstrict.le
  have hmK : 2 * dK + 1 = (s + 1) + 1 + Module.finrank F K * v := by
    have hKc := hK.conductor_eq
    rw [hepsilonK] at hKc
    dsimp only [v]
    omega
  have hx : (((dK : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x := by
    simpa only [x] using
      phaseReductionSourceTeichmullerLift_order_ge K S.upperUniformizer
        S.upper_order dK y
  have hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [u, v] using
      highOddNormalizedRatio_order F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
  exact highTauDisplacement_mem_of_order F K rfl hv hmK hodd u x hu hx

/-- Canonical source-faithful unit for the actual displayed High variable.
Its displacement is literally `u*x`, not a compact surrogate with the same
residue. -/
noncomputable def highActualSourceUnit
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F) : Kˣ := by
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
    ((C.frobeniusEquiv hchar).symm X)
  let x : K := (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
    (teichmuller K y : K)
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let ux : lattice K (((((s + 1) + 2) / 2 : ℕ) : ℤ)) :=
    ⟨u * x, by
      simpa only [hchar, S, y, x, u] using
        highActualSourceUx_mem_lattice F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source hepsilon C X⟩
  exact (positiveUnitOfLattice K
    (by omega : 0 < ((s + 1) + 2) / 2) ux : Kˣ)

@[simp]
theorem highActualSourceUnit_coe
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (X : ResidueField F) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      htpos pi hpi hgen
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
      ((C.frobeniusEquiv hchar).symm X)
    let x : K :=
      (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
        (teichmuller K y : K)
    let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows
    (highActualSourceUnit F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        hepsilon C X : K) = 1 + u * x := by
  dsimp only
  simp only [highActualSourceUnit, coe_positiveUnitOfLattice]

/-- The fixed norm-character generator has exactly the elementary High
coefficient `etaZero`.  The proof evaluates its literal representative `1`
through the Lamprecht residual character; the chosen source coordinate
squares to the full lower break because the critical parity is odd. -/
theorem highActual_generatorPolar_eq_etaZero
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hparity : lowCriticalParity (s + 1) = 1) :
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
    (highNormGeneratorPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        hparity).polarCoefficient C.lower C.lower_ne_one = N.etaZero := by
  dsimp only
  unfold highNormGeneratorPhase
  dsimp only
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  dsimp only [LocalLamprechtPhaseData.polarCoefficient]
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  let hA := wildOddHighNormalizationCoefficient_order F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  change finiteAddCharCoefficient C.lower C.lower_ne_one _ = etaZero
  apply finiteAddCharCoefficient_unique
  apply AddChar.ext
  intro z
  rw [AddChar.mulShift_apply]
  symm
  rw [← wildOddUpperEtaZero_spec S data.baseAddChar A (s + 1) hA C z]
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  have htau : tau ≠ 1 :=
    highParameter_intermediate_indexOne_ne_one F K ht hres pi hpi hgen
  let tauData := quasiCharDataOfIsConductor F tau.1 (s + 1 + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  have hCrit := lowCriticalConductorDecomposition (t := s + 1) (by omega)
  rw [hparity] at hCrit
  let hTau : IsStationaryConductorDecomposition tauData.conductor
      (lowCriticalFloorDepth (s + 1)) 1 := by
    simpa only [tauData, quasiCharDataOfIsConductor_conductor] using hCrit
  let gammaTau := highNormGamma F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  have hgammaTau : ord F (gammaTau : F) =
      ((((s + 1 + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) := by
    simpa only [gammaTau] using
      highNormGamma_order F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let Gamma : AdmissibleGamma F tauData data.baseAddChar :=
    ⟨gammaTau, by
      simpa only [tauData, quasiCharDataOfIsConductor_conductor] using
        hgammaTau⟩
  let coordinate := phaseReductionSourceCoordinate F S.lowerUniformizer
    (lowCriticalFloorDepth (s + 1))
  have hcoordinate : ord F (coordinate : F) =
      ((lowCriticalFloorDepth (s + 1) : ℤ) : WithTop ℤ) := by
    exact phaseReductionSourceCoordinate_order F S.lowerUniformizer
      S.lower_order (lowCriticalFloorDepth (s + 1))
  let rep : lattice F 0 := ⟨1, by simp⟩
  have hclass : latticeQuotientMk F (by omega) rep =
      stationaryCoefficientClass F tauData data.baseAddChar hTau gammaTau
        Gamma.property := by
    simpa only [tau, tauData, hTau, gammaTau, Gamma, rep, hparity] using
      highNormGenerator_one_class F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let R : StationaryClassRepresentative F tauData data.baseAddChar hTau
      gammaTau Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative rep hclass
  let c : lattice F
      ((tauData.conductor : ℤ) - (tauData.conductor : ℤ)) :=
    R.toLamprecht
  have hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F tauData
            (lowCriticalFloorDepth (s + 1)) 1 (by omega)
              hTau.conductor_eq hTau.conductor_gt_one).int_le_conductor
          (tauData.conductor : ℤ)) c =
      stationaryNumeratorClass F tauData data.baseAddChar
        (tauData.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F tauData
          (lowCriticalFloorDepth (s + 1)) 1 (by omega)
            hTau.conductor_eq hTau.conductor_gt_one) Gamma Gamma.property := by
    simpa only [c, stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  have hzmem : (teichmuller F z : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F z).property
  change lamprechtResidualAddChar F tauData data.baseAddChar
      (lowCriticalFloorDepth (s + 1)) hTau.conductor_eq
      hTau.conductor_gt_one Gamma coordinate hcoordinate z = _
  calc
    _ = lamprechtResidualAddChar F tauData data.baseAddChar
        (lowCriticalFloorDepth (s + 1)) hTau.conductor_eq
        hTau.conductor_gt_one Gamma coordinate hcoordinate
          (reduce F (teichmuller F z : F) hzmem) := by
            congr 1
            simp [reduce]
    _ = (data.baseAddChar.character
          ((rep : F) * (coordinate : F) ^ 2 * (teichmuller F z : F) /
            ((Gamma : Fˣ) : F)) : ℂ) := by
      exact lamprechtResidualAddChar_integral_lift F tauData
        data.baseAddChar (lowCriticalFloorDepth (s + 1))
        hTau.conductor_eq hTau.conductor_gt_one Gamma coordinate hcoordinate
          c hc (teichmuller F z : F) hzmem
    _ = _ := by
      congr 2
      dsimp only [rep, coordinate, Gamma, gammaTau, A,
        wildOddHighNormalizationCoefficient, highNormGamma]
      simp only [one_mul, phaseReductionSourceCoordinate_coe,
        Units.val_div_eq_div_val, coe_normUnits]
      have hdepth : 2 * lowCriticalFloorDepth (s + 1) = s + 1 := by
        have hdec := lowCriticalConductor_eq (t := s + 1)
        rw [hparity] at hdec
        omega
      have hdepth' : lowCriticalFloorDepth (s + 1) * 2 = s + 1 := by
        omega
      rw [← pow_mul, hdepth', ← source.alpha1_eq]
      field_simp [Units.ne_zero gammaF,
        Units.ne_zero source.normRows.alpha1]

/-- Transporting only proof-bearing character data leaves the residual
polar coefficient unchanged. -/
private theorem transportLocalLamprechtPhaseData_polarCoefficient_eq
    {chi chi' : LocalQuasiCharData F} {psi psi' : LocalAddCharData F}
    (hchi' : chi.character = chi'.character)
    (hpsi' : psi.character = psi'.character)
    (D : LocalLamprechtPhaseData F chi psi)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    (transportLocalLamprechtPhaseData hchi' hpsi' D).polarCoefficient
        psi0 hpsi0 = D.polarCoefficient psi0 hpsi0 := by
  have hc : chi = chi' := LocalQuasiCharData.ext_character F hchi'
  have hp : psi = psi' := LocalAddCharData.ext_character hpsi'
  subst chi'
  subst psi'
  rfl

/-- The actual zero-index High source phase has polar coefficient
`eta = etaZero * dZero`.  The stationary numerator is first kept as its
literal quotient representative, then its exact ratio is rewritten as
`A*n`.  The signed depth `a = (s+1)-2d` is transported through the norm
initial residue, including when `a < 0`; no residual scalar is introduced. -/
theorem highActual_basePolar_eq_eta
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
    (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0
        ).polarCoefficient C.lower C.lower_ne_one = N.eta := by
  subst epsilon
  dsimp only
  unfold highSourceTwistPhase LocalLamprechtPhaseData.sourceTiedRow
  rw [show PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      (d := d) (epsilon := 1) hF.epsilon_le_one
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
        (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order =
      .odd (phaseReductionSourceCoordinate F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer d)
        (phaseReductionSourceCoordinate_order F
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lowerUniformizer
          (phaseReductionResidualCoordinateSource F K hres pi hpi).lower_order d) by
    unfold PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
    simp]
  unfold highOddLinearTwistPhaseForComputationalData
  dsimp only
  rw [transportLocalLamprechtPhaseData_polarCoefficient_eq]
  unfold localPhaseOfStationaryClass LocalLamprechtPhaseData.oddOfStationaryClass
  dsimp only [LocalLamprechtPhaseData.polarCoefficient]
  let p := Module.finrank F K
  let Q := source.productRows
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  let hA := wildOddHighNormalizationCoefficient_order F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source
  let u : K := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q
  let n : F := norm F K u
  let a : ℤ := (s + 1 : ℤ) - 2 * (d : ℤ)
  have hconductor : (data.twistData 1).conductor = 2 * d + 1 :=
    hF.conductor_eq
  have hu : ord K u = (a : WithTop ℤ) := by
    have hshift :
        -(((data.twistData 1).conductor - (s + 1 + 1) : ℕ) : ℤ) = a := by
      rw [Int.ofNat_sub hstrict.le, hconductor]
      dsimp only [a]
      push_cast
      ring
    rw [show ord K u =
        ((-(((data.twistData 1).conductor - (s + 1 + 1) : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) by
      simpa only [u, Q] using
        highOddNormalizedRatio_order F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF Q]
    exact congrArg (fun z : ℤ ↦ (z : WithTop ℤ)) hshift
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order a u hu
  let zeta := e.symm zetaK
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  change finiteAddCharCoefficient C.lower C.lower_ne_one _ =
    etaZero * zeta ^ p
  apply finiteAddCharCoefficient_unique
  apply AddChar.ext
  intro X
  rw [AddChar.mulShift_apply]
  symm
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K)))
  let twist := ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen
    (data.twistData 1) mu
  let hTwist := Q.factorDecomposition 0
  let Gamma : AdmissibleGamma F twist data.baseAddChar :=
    ⟨gammaF, Q.factorDenominator 0⟩
  let delta := phaseReductionSourceCoordinate F S.lowerUniformizer d
  have hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F S.lowerUniformizer S.lower_order d
  let R := highOddLinearTwistRepresentative F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF Q 0
  let c := R.toLamprecht
  have hc := R.toLamprecht_represents
  have hXmem : (teichmuller F X : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F X).property
  change lamprechtResidualAddChar F twist data.baseAddChar d
      hTwist.conductor_eq hTwist.conductor_gt_one Gamma delta hdelta X = _
  calc
    _ = lamprechtResidualAddChar F twist data.baseAddChar d
        hTwist.conductor_eq hTwist.conductor_gt_one Gamma delta hdelta
          (reduce F (teichmuller F X : F) hXmem) := by
            congr 1
            simp [reduce]
    _ = (data.baseAddChar.character
          ((c : F) * (delta : F) ^ 2 * (teichmuller F X : F) /
            ((Gamma : Fˣ) : F)) : ℂ) := by
      exact lamprechtResidualAddChar_integral_lift F twist data.baseAddChar d
        hTwist.conductor_eq hTwist.conductor_gt_one Gamma delta hdelta c hc
          (teichmuller F X : F) hXmem
    _ = _ := by
      have hn : ord F n = (a : WithTop ℤ) := by
        dsimp only [n]
        rw [ord_norm, hres, one_nsmul, hu]
      let n0 : F := n / (S.lowerUniformizer : F) ^ a
      have hn0ord : ord F n0 = (0 : WithTop ℤ) := by
        dsimp only [n0]
        rw [ord_div, hn, ord_zpow, S.lower_order, compact_zsmul_one]
        simp
      have hn0mem : n0 ∈ lattice F 0 := by
        rw [mem_lattice, hn0ord]
        exact le_rfl
      have hn0res : reduce F n0 hn0mem = zeta ^ p := by
        have hb := sourceInitialResidue_norm_downstairs_eq_pow F K ht htpos
          hres S a u hu
        dsimp only at hb
        simpa only [sourceInitialResidue, n0, n, zeta, zetaK, e, p] using hb
      let x0 : F := n0 * (teichmuller F X : F)
      have hx0mem : x0 ∈ lattice F 0 := by
        dsimp only [x0]
        simpa using mul_mem_lattice F hn0mem hXmem
      have hx0res : reduce F x0 hx0mem = zeta ^ p * X := by
        change residueMap F
            (⟨x0, (mem_lattice_zero_iff F).1 hx0mem⟩ :
              ringOfIntegers F) = _
        change residueMap F
            ((⟨n0, (mem_lattice_zero_iff F).1 hn0mem⟩ :
                ringOfIntegers F) *
              ⟨(teichmuller F X : F),
                (mem_lattice_zero_iff F).1 hXmem⟩) = _
        rw [map_mul]
        change reduce F n0 hn0mem * residueMap F (teichmuller F X) = _
        rw [hn0res, residueMap_teichmuller]
      have hzero :
          oddNormAllIndexScalar F K ht hres pi hpi hgen htpos 0 = 0 := by
        exact (highParameter_intermediate_teichmuller_eq_zero_iff F
          (Module.finrank F K)
          (residueCharacteristic_eq_degree_of_positive_break
            F K ht htpos pi hpi hgen) 0).2 rfl
      have hBaseRatio :
          ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF Q 0 : Fˣ) : F) / (gammaF : F) =
            (A : F) * n := by
        change
          ((highOddLinearTwistUnit F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF Q 0 : Fˣ) : F) / (gammaF : F) =
            (((normUnits F K Q.alpha1 / gammaF : Fˣ) : F)) * n
        rw [highOddLinearTwistUnit_coe]
        rw [highOddLinearTwistValue_eq_normalized, hzero]
        simp only [add_zero, Units.val_div_eq_div_val, coe_normUnits]
        field_simp [Units.ne_zero gammaF]
        rfl
      have hcRatio : (c : F) / (gammaF : F) = (A : F) * n := by
        simpa only [c, R, highOddLinearTwistUnit,
          StationaryClassRepresentative.toLamprecht,
          StationaryClassRepresentative.coe_unit] using hBaseRatio
      have hdepth : a + 2 * (d : ℤ) = ((s + 1 : ℕ) : ℤ) := by
        dsimp only [a]
        push_cast
        ring
      have hpow : (S.lowerUniformizer : F) ^ (s + 1) =
          (S.lowerUniformizer : F) ^ a *
            ((S.lowerUniformizer : F) ^ d) ^ 2 := by
        calc
          (S.lowerUniformizer : F) ^ (s + 1) =
              (S.lowerUniformizer : F) ^ ((s + 1 : ℕ) : ℤ) := by
                rw [zpow_natCast]
          _ = (S.lowerUniformizer : F) ^ (a + 2 * (d : ℤ)) := by
                rw [hdepth]
          _ = (S.lowerUniformizer : F) ^ a *
              (S.lowerUniformizer : F) ^ (2 * (d : ℤ)) :=
                zpow_add₀ (Units.ne_zero S.lowerUniformizer) _ _
          _ = (S.lowerUniformizer : F) ^ a *
              ((S.lowerUniformizer : F) ^ d) ^ 2 := by
                rw [show (S.lowerUniformizer : F) ^ (2 * (d : ℤ)) =
                    (S.lowerUniformizer : F) ^ (2 * d) by
                  rw [← zpow_natCast]
                  congr 2]
                rw [← pow_mul]
                congr 2
                omega
      have harg :
          (c : F) * (delta : F) ^ 2 * (teichmuller F X : F) /
              ((Gamma : Fˣ) : F) =
            (A : F) * (S.lowerUniformizer : F) ^ (s + 1) * x0 := by
        have hgamma : ((Gamma : Fˣ) : F) = (gammaF : F) := rfl
        rw [hgamma]
        rw [show (c : F) * (delta : F) ^ 2 *
              (teichmuller F X : F) / (gammaF : F) =
            ((c : F) / (gammaF : F)) * (delta : F) ^ 2 *
              (teichmuller F X : F) by ring]
        rw [hcRatio]
        dsimp only [delta, x0, n0]
        simp only [phaseReductionSourceCoordinate_coe]
        rw [hpow]
        field_simp [Units.ne_zero S.lowerUniformizer]
      rw [harg]
      have hcompact := wildOddCompactEta_integral F K S data.baseAddChar A
        (s + 1) hA C x0 hx0mem
      rw [hx0res] at hcompact
      calc
        _ = C.lower (etaZero * (zeta ^ p * X)) := by
          simpa only [etaZero] using hcompact.symm
        _ = _ := by
          congr 1
          ring

private theorem highActual_phaseSource_natural_of_trace
    (hepsilonK : epsilonK = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (betaInv initial : ResidueField F)
    (hnormalizedTrace :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
      ∀ z : ResidueField F,
        (data.baseAddChar.character
          ((wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen
              data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
                hupper gammaF hgammaF source : F) *
            trace F K
              ((algebraMap F K
                  (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
                    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                      gammaF hgammaF source.productRows) -
                highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
                  psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                    gammaF hgammaF source.productRows) *
                (delta : K) ^ 2 *
                (teichmuller K
                  (PhaseReductionResidualCoordinateSource.residueEquiv hres z) :
                    K))) : ℂ) = C.lower ((betaInv * initial) * z)) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
    let hdelta := phaseReductionSourceCoordinate_order K S.upperUniformizer
      S.upper_order dK
    (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
      ((highOddUpstairsPhaseSource F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows
          (hepsilonK.symm ▸ (.odd delta hdelta))).polarCoefficient
            (C.upper hres) (C.upper_ne_one hres)) = betaInv * initial := by
  subst epsilonK
  dsimp only at hnormalizedTrace ⊢
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
  have hdelta := phaseReductionSourceCoordinate_order K S.upperUniformizer
    S.upper_order dK
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) gammaF,
      highParameter_intermediate_commonDenominator F K ht hres pi hpi hgen
        (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi
          hstrict.le gammaF hgammaF⟩
  let R := OddIntermediateHighProductData.upstairsRepresentative F K ht hres
    pi hpi hgen (data.twistData 1) chiK data.baseAddChar psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict.le hupper gammaF hgammaF
        source.productRows
  have hratio :
      (R.toLamprecht : K) / ((Gamma : Kˣ) : K) =
        algebraMap F K
            (wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen
              data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
                hupper gammaF hgammaF source : F) *
          (algebraMap F K
              (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
                psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                  gammaF hgammaF source.productRows) -
            highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF source.productRows) := by
    simpa only [R, Gamma, StationaryClassRepresentative.toLamprecht,
      OddIntermediateHighProductData.upstairsRepresentative,
      StationaryClassRepresentative.ofCoefficientRepresentative,
      highOddUpstairsRepresentativeUnit,
      StationaryClassRepresentative.coe_unit, Units.coe_map,
      MonoidHom.coe_coe] using
        wildOddHighStationaryRatio_eq_normalized F K ht hres pi hpi hgen
          data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source
  change (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    ((LocalLamprechtPhaseData.oddOfStationaryClass dK hK Gamma delta hdelta
      R).polarCoefficient (C.upper hres) (C.upper_ne_one hres)) = _
  unfold LocalLamprechtPhaseData.oddOfStationaryClass
  exact LocalLamprechtPhaseData.odd_upperPolarInLowerCoordinate_eq
    (p := Module.finrank F K) hres C hpsi dK hK.conductor_eq
      hK.conductor_gt_one Gamma delta hdelta R.toLamprecht
        (by simpa only [stationaryDepthOfConductorDecomposition] using
          R.toLamprecht_represents)
        _ _ betaInv initial hratio hnormalizedTrace

private theorem highActual_natural_of_trace
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (betaInv initial : ResidueField F)
    (hnormalizedTrace :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
      ∀ z : ResidueField F,
        (data.baseAddChar.character
          ((wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen
              data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
                hupper gammaF hgammaF source : F) *
            trace F K
              ((algebraMap F K
                  (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
                    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                      gammaF hgammaF source.productRows) -
                highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
                  psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                    gammaF hgammaF source.productRows) *
                (delta : K) ^ 2 *
                (teichmuller K
                  (PhaseReductionResidualCoordinateSource.residueEquiv hres z) :
                    K))) : ℂ) = C.lower ((betaInv * initial) * z)) :
    (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source).upperPolarInLowerCoordinate (Module.finrank F K) C hres =
      betaInv * initial := by
  have hepsilonK : epsilonK = 1 :=
    (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source).trans
        hepsilon
  have hsource := highActual_phaseSource_natural_of_trace F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source hepsilonK C betaInv initial hnormalizedTrace
  subst epsilonK
  dsimp only at hsource
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
  have hdelta := phaseReductionSourceCoordinate_order K S.upperUniformizer
    S.upper_order dK
  have hchiData : chiK.character = data.extensionQuasiChar.character := by
    rw [data.extensionQuasiChar_character, hchi,
      data.twistData_character]
    exact normQuasiChar_normCharacter_mul F K
      (1 : NormCharacter F K) globalChi
  have hpsiData : psiK.character = data.extensionAddChar.character := by
    rw [data.extensionAddChar_character, hpsi,
      data.baseAddChar_character]
    rfl
  have htransport := transportLocalLamprechtPhaseData_polarCoefficient
    hchiData hpsiData
      (highOddUpstairsPhaseSource F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows (.odd delta hdelta))
      (C.upper hres) (C.upper_ne_one hres)
  unfold LocalLamprechtPhaseData.upperPolarInLowerCoordinate
  rw [show highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source =
      transportLocalLamprechtPhaseData hchiData hpsiData
        (highOddUpstairsPhaseSource F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source.productRows (.odd delta hdelta)) by
        simp [highSourceUpstairsPhase, LocalLamprechtPhaseData.sourceTiedRow,
          PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity,
          highOddUpstairsPhaseForComputationalData, hchiData, hpsiData,
          S, delta, hdelta]]
  rw [htransport]
  exact hsource

/-- Closed natural polar coefficient of the real source-tied High row.
The coefficient is in the canonical lower residue coordinate and precedes
the manuscript's forward-Frobenius display. -/
theorem highActual_naturalPolar (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
    (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source).upperPolarInLowerCoordinate (Module.finrank F K) C hres =
      N.betaInv * (-N.dZero) := by
  dsimp only
  let p := Module.finrank F K
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source
  let hA := wildOddHighNormalizationCoefficient_order F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source
  let u : K := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let n : F := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source.productRows
  let a : ℤ := (s + 1 : ℤ) - 2 * (d : ℤ)
  have hu : ord K u = (a : WithTop ℤ) := by
    simpa only [u, a] using highActual_normalizedRatio_order F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source hepsilon
  have hnorm : n = norm F K u := by
    rfl
  have hconductorF : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have hepsilonK : epsilonK = 1 :=
    (highActual_epsilon_eq F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source).trans
        hepsilon
  have hconductorK : chiK.conductor = 2 * dK + 1 := by
    simpa [hepsilonK] using hK.conductor_eq
  have haNeg : a < 0 := by
    dsimp only [a]
    rw [hconductorF] at hstrict
    push_cast
    omega
  have habove : s + 1 < 2 * d := by
    rw [hconductorF] at hstrict
    omega
  have hdepthFormula := wildOdd_upperDepth_eq_of_conductors F K ht hres pi
    hpi hgen (data.twistData 1) chiK hchi d dK hconductorF hconductorK
      hminimal
  have hrow := hdepthFormula.2.2 habove
  have hdepth : (p : ℤ) * a + 2 * (dK : ℤ) = (s + 1 : ℕ) := by
    dsimp only [p, a]
    push_cast at hrow ⊢
    linarith
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order a u hu
  let zeta := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    zetaK
  let dZero := zeta ^ p
  have hthree := sourceInitialResidue_u_sub_norm_extremeCases F K ht htpos
    hres S a u hu n hnorm
  obtain ⟨hsub, hsubInitial⟩ := hthree.2 haNeg
  let y : K := algebraMap F K n - u
  have hy : ord K y = (((p : ℤ) * a : ℤ) : WithTop ℤ) := by
    rw [show y = -(u - algebraMap F K n) by dsimp only [y]; ring, ord_neg,
      hsub]
  have hyInitial :
      sourceInitialResidue K S.upperUniformizer S.upper_order
          ((p : ℤ) * a) y hy = zetaK ^ p := by
    have hneg := sourceInitialResidue_neg K S.upperUniformizer S.upper_order
      ((p : ℤ) * a) (u - algebraMap F K n) hsub
    rw [hsubInitial] at hneg
    simpa only [p, y, zetaK, neg_sub, neg_neg] using hneg
  have hSpi : (S.upperUniformizer : K) = (pi : K) := by
    simp [S, phaseReductionResidualCoordinateSource,
      phaseReductionUpperUniformizer_coe]
  have hinitial : ∀ hx :
      y * ((pi : K) ^ dK) ^ 2 / (pi : K) ^ (s + 1) ∈ lattice K 0,
      (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          (reduce K
            (y * ((pi : K) ^ dK) ^ 2 / (pi : K) ^ (s + 1)) hx) =
        -(-dZero) := by
    intro hx
    have hreduce := normalizedTrace_initial_eq_sourceInitialResidue K
      S.upperUniformizer S.upper_order ((p : ℤ) * a) dK (s + 1) y hy
        hdepth hx
    have hreduce' :
        reduce K (y * ((pi : K) ^ dK) ^ 2 / (pi : K) ^ (s + 1)) hx =
          sourceInitialResidue K S.upperUniformizer S.upper_order
            ((p : ℤ) * a) y hy := by
      simpa only [hSpi] using hreduce
    rw [hreduce', hyInitial]
    simp only [map_pow, zeta, dZero, neg_neg]
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let betaInv := (C.frobeniusEquiv hchar).symm etaZero
  let lambda := wildOddCompactLambda F K ht hres pi hpi
  have hann : ∀ z : ResidueField F,
      C.lower (etaZero * (z ^ p - lambda ^ (p - 1) * z)) = 1 := by
    intro z
    simpa only [etaZero, A, hA, p, lambda, S] using
      wildOddHighNormalization_annihilator F K ht hres pi hpi hgen data
        chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source C z
  have hbeta : betaInv = etaZero * lambda ^ (p - 1) := by
    simpa only [betaInv] using
      wildOddUpperEtaZero_frobeniusPreimage_eq hchar C etaZero lambda hann
  have hnormalizedTrace :
      let delta := phaseReductionSourceCoordinate K S.upperUniformizer dK
      ∀ z : ResidueField F,
        (data.baseAddChar.character
          ((A : F) * trace F K
            ((algebraMap F K n - u) * (delta : K) ^ 2 *
              (teichmuller K
                (PhaseReductionResidualCoordinateSource.residueEquiv hres z) :
                  K))) : ℂ) = C.lower ((betaInv * (-dZero)) * z) := by
    dsimp only
    intro z
    simpa only [phaseReductionSourceCoordinate_coe, hSpi] using
        wildOddCompactNormalizedTraceCharacter F K ht hres pi hpi hgen
          data.baseAddChar A hA C betaInv (-dZero) hbeta ((p : ℤ) * a)
            dK y hy hdepth hinitial z
  have hnatural := highActual_natural_of_trace F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source hepsilon C betaInv (-dZero) (by
        simpa only [S, A, n, u] using hnormalizedTrace)
  simpa only [highActualNormalization, wildOddUpperPolarNormalizationOfSource,
    S, A, u, a, hu, zetaK, zeta, hchar, hA, etaZero, betaInv, dZero, p]
      using hnatural

/-- Complete odd-conductor High row above the break: after transport from the
natural source coordinate, the displayed upper pair is the manuscript's above
pair and its affine coefficient is zero. -/
theorem wildOdd_actualHighCoefficients_above
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2)
    (units : ResidueField F → Kˣ)
    (hunits : ∀ X,
      let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
        htpos pi hpi hgen
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let y := PhaseReductionResidualCoordinateSource.residueEquiv hres
        ((C.frobeniusEquiv hchar).symm X)
      let x : K :=
        (phaseReductionSourceCoordinate K S.upperUniformizer dK : K) *
          (teichmuller K y : K)
      let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source.productRows
      (units X : K) = 1 + u * x) :
    let p := Module.finrank F K
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      htpos pi hpi hgen
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
    let upper := highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
      pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF p hchar C source
    upper.upperCoefficientPair C.lower_ne_one hcharOdd =
      wildOddUpperPairAbove p N.eta N.dZero := by
  dsimp only
  let p := Module.finrank F K
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source hepsilon C
  let D := highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
  let upper := highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
    pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
      hupper gammaF hgammaF p hchar C source
  have hnat : D.upperPolarInLowerCoordinate p C hres =
      N.betaInv * (-N.dZero) := by
    simpa only [D, N, p] using highActual_naturalPolar F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source hepsilon C
  have hdisplay : C.frobeniusEquiv hchar
        (D.upperPolarInLowerCoordinate p C hres) =
      N.etaZero * (-N.dZero) ^ p :=
    LocalLamprechtPhaseData.displayedPolar_eq_of_natural D p hchar C hres
      N.betaInv N.etaZero (-N.dZero) hnat N.betaInv_pow
  have hpne : p ≠ 2 := by
    dsimp only [p]
    intro hp
    rw [hp] at hodd
    norm_num at hodd
  have hpolar : C.frobeniusEquiv hchar
        (D.upperPolarInLowerCoordinate p C hres) =
      (wildOddUpperPairAbove p N.eta N.dZero).polar :=
    hdisplay.trans (wildOdd_upperPolar_above p hpne N)
  obtain ⟨q, hq⟩ := wildOdd_actualHighDisplayed_above F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source hepsilon C units hunits
  have hfun : ∀ x, upper x = C.lower (q * x ^ 2) := by
    simpa only [upper] using hq
  change upper.upperCoefficientPair C.lower_ne_one hcharOdd = _
  apply WildOddUpperCoefficientPair.ext
  · change C.frobeniusEquiv hchar
        ((PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres))) =
      (wildOddUpperPairAbove p N.eta N.dZero).polar
    simpa only [LocalLamprechtPhaseData.upperPolarInLowerCoordinate] using
      hpolar
  · change upper.affineCoefficient hcharOdd C.lower_ne_one = 0
    exact CriticalPolarFunction.affineCoefficient_eq_zero_of_pureQuadratic
      C.lower_ne_one hcharOdd upper q hfun

/-- The actual High upstairs row at even conductor parity is the literal
constant-one row, hence has coefficient pair `(0,0)`. -/
theorem wildOdd_actualHighCoefficients_even
    (hepsilon : epsilon = 0)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let p := Module.finrank F K
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      htpos pi hpi hgen
    let upper := highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
      pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF p hchar C source
    upper.upperCoefficientPair C.lower_ne_one hcharOdd =
      wildOddUpperPairEven := by
  dsimp only
  apply CriticalPolarFunction.upperCoefficientPair_eq_even
    C.lower_ne_one hcharOdd
  intro X
  exact highSourceDisplayedUpstairsFunction_eq_one_of_even F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
          hpi hgen) C source hepsilon X

end HighActual
section LowActual

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hLow : (data.twistData 1).conductor ≤ s + 1 + 1)
  (delta : Fˣ) (epsilon1 : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((s + 1 + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) :
      WithTop ℤ))
  (hepsilon1 : ord K (epsilon1 : K) =
    (((s + 1 + 1 - (data.twistData 1).conductor : ℕ) : ℤ) :
      WithTop ℤ))
  (hT : 2 ≤ s + 1 + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth (s + 1)) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (s + 1 + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := s + 1) hT)
        delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF))
  (table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)

local instance upperResidualLowActual_neZero : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance upperResidualLowActual_degreePrime :
    Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩
local instance upperResidualLowActual_residueFintype :
    Fintype (ResidueField F) := residueFieldFintype F

/-- The generic normalized-trace bridge, but stated for the actual source-tied
Low phase rather than the untransported witness phase. -/
theorem lowActual_natural_of_trace
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (betaInv initial : ResidueField F)
    (hnormalizedTrace :
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let source := phaseReductionSourceCoordinate K S.upperUniformizer d
      ∀ z : ResidueField F,
        (data.baseAddChar.character
          (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
            trace F K
              ((algebraMap F K
                    (lowOddNormalizedNorm
                      (F := F) (K := K) (P := P) (hT := hT)) -
                  lowNormalizedRatio F K epsilon1 P) *
                (source : K) ^ 2 *
                (teichmuller K
                  (PhaseReductionResidualCoordinateSource.residueEquiv
                    hres z) : K))) : ℂ) =
          C.lower ((betaInv * initial) * z)) :
    (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W).upperPolarInLowerCoordinate
          (Module.finrank F K) C hres = betaInv * initial := by
  subst epsilon
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let source := phaseReductionSourceCoordinate K S.upperUniformizer d
  have hsource := phaseReductionSourceCoordinate_order K S.upperUniformizer
    S.upper_order d
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK :=
    ⟨lowGammaK F K delta epsilon1, hgammaK⟩
  let R : StationaryClassRepresentative K chiK psiK hSource
      (Gamma : Kˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative
      W.representative (by simpa only [hSource, Gamma] using W.represents)
  have hratio : (R.toLamprecht : K) / ((Gamma : Kˣ) : K) =
      algebraMap F K
          (lowOddExactCoefficient
            (F := F) (K := K) (P := P) (hT := hT)) *
        (algebraMap F K
            (lowOddNormalizedNorm
              (F := F) (K := K) (P := P) (hT := hT)) -
          lowNormalizedRatio F K epsilon1 P) := by
    simpa only [R, Gamma, StationaryClassRepresentative.toLamprecht,
      StationaryClassRepresentative.ofCoefficientRepresentative,
      lowOddUpstairsRepresentativeUnit,
      StationaryClassRepresentative.coe_unit, lowOddExactCoefficient,
      wildOddLowNormalizationCoefficient] using
        wildOddLowStationaryRatio_eq_normalized F K ht hres pi hpi hgen
          data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table W
  have hnat :
      (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          ((lowOddUpstairsPhaseFromWitness F K ht hres pi hpi hgen data
            chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table W
                (.odd source hsource)).polarCoefficient
                  (C.upper hres) (C.upper_ne_one hres)) =
        betaInv * initial := by
    change (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
        ((LocalLamprechtPhaseData.oddOfStationaryClass d hSource Gamma
          source hsource R).polarCoefficient
            (C.upper hres) (C.upper_ne_one hres)) = betaInv * initial
    unfold LocalLamprechtPhaseData.oddOfStationaryClass
    exact LocalLamprechtPhaseData.odd_upperPolarInLowerCoordinate_eq
      (p := Module.finrank F K) hres C hpsi d hSource.conductor_eq
        hSource.conductor_gt_one Gamma source hsource R.toLamprecht
          (by simpa only [stationaryDepthOfConductorDecomposition] using
            R.toLamprecht_represents)
          _ _ betaInv initial hratio hnormalizedTrace
  unfold LocalLamprechtPhaseData.upperPolarInLowerCoordinate
  unfold lowSourceUpstairsPhase LocalLamprechtPhaseData.sourceTiedRow
  unfold lowOddUpstairsPhaseForComputationalData
  rw [transportLocalLamprechtPhaseData_polarCoefficient]
  simpa [PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity]
    using hnat

/-- In the strict Low row, the natural polar coefficient of the actual
source-tied upstairs phase is `betaInv * zeta`, where `zeta` is the leading
coefficient of the literal normalized ratio in the accepted source
uniformizer. -/
private theorem lowActual_naturalPolar_strict_product
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hstrict : (data.twistData 1).conductor < s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let a : ℕ := s + 1 - 2 * d
    let u : K := lowNormalizedRatio F K epsilon1 P
    let hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
      have hc : (data.twistData 1).conductor = 2 * d + 1 := by
        simpa [hepsilon] using hF.conductor_eq
      have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
        dsimp only [a]
        omega
      change ord K (lowNormalizedRatio F K epsilon1 P) = _
      rw [lowNormalizedRatio_order F K epsilon1 hepsilon1 P, ha]
      norm_num
    let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
      (a : ℤ) u hu
    let zeta := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
      zetaK
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    let betaInv := etaZero *
      wildOddCompactLambda F K ht hres pi hpi ^ (Module.finrank F K - 1)
    (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W).upperPolarInLowerCoordinate
          (Module.finrank F K) C hres = betaInv * zeta := by
  dsimp only
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a : ℕ := s + 1 - 2 * d
  let u : K := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have haEq : a + 2 * d = s + 1 := by
    dsimp only [a]
    omega
  have haPos : 0 < a := by
    dsimp only [a]
    omega
  have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
    dsimp only [a]
    omega
  have hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    change ord K (lowNormalizedRatio F K epsilon1 P) = _
    rw [lowNormalizedRatio_order F K epsilon1 hepsilon1 P, ha]
    norm_num
  let n : F := lowOddNormalizedNorm
    (F := F) (K := K) (P := P) (hT := hT)
  have hnorm : n = norm F K u := by
    dsimp only [n, u]
    exact (lowNormalizedRatio_norm F K epsilon1 P).symm
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (a : ℤ) u hu
  let zeta := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    zetaK
  have hthree := sourceInitialResidue_u_sub_norm_extremeCases F K ht
    (by omega) hres S (a : ℤ) u hu n hnorm
  have hsub : ord K (u - algebraMap F K n) =
      (((a : ℕ) : ℤ) : WithTop ℤ) := by
    rcases hthree.1 (by exact_mod_cast haPos) with ⟨hsub, _⟩
    exact hsub
  have hsubInitial :
      sourceInitialResidue K S.upperUniformizer S.upper_order (a : ℤ)
          (u - algebraMap F K n) hsub = zetaK := by
    rcases hthree.1 (by exact_mod_cast haPos) with ⟨hsub', hsubInitial⟩
    simpa only [zetaK] using hsubInitial
  let y : K := algebraMap F K n - u
  have hy : ord K y = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    have hyEq : y = -(u - algebraMap F K n) := by
      dsimp only [y]
      ring
    rw [hyEq, ord_neg, hsub]
  have hdepth : (a : ℤ) + 2 * (d : ℤ) = (s + 1 : ℕ) := by
    exact_mod_cast haEq
  have hquot :
      y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1) =
        -((u - algebraMap F K n) /
          (S.upperUniformizer : K) ^ (a : ℤ)) := by
    have hpowD : ((pi : K) ^ d) ^ 2 = (pi : K) ^ (2 * d) := by
      rw [← pow_mul]
      congr 1
      omega
    have hpowT : (pi : K) ^ (s + 1) =
        (pi : K) ^ a * (pi : K) ^ (2 * d) := by
      rw [← pow_add, haEq]
    rw [hpowD, hpowT]
    change y * (pi : K) ^ (2 * d) /
        ((pi : K) ^ a * (pi : K) ^ (2 * d)) =
      -((u - algebraMap F K n) /
        (phaseReductionUpperUniformizer K pi hpi : K) ^ (a : ℤ))
    rw [phaseReductionUpperUniformizer_coe, zpow_natCast]
    dsimp only [y]
    field_simp [hpi.ne_zero]
    ring
  have hinitial : ∀ hx :
      y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1) ∈ lattice K 0,
      (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          (reduce K
            (y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1)) hx) =
        -zeta := by
    intro hx
    have hq : (u - algebraMap F K n) /
        (S.upperUniformizer : K) ^ (a : ℤ) ∈ lattice K 0 := by
      rw [mem_lattice, ord_div, hsub, ord_zpow, S.upper_order]
      simp
    let qO : ringOfIntegers K :=
      ⟨(u - algebraMap F K n) /
        (S.upperUniformizer : K) ^ (a : ℤ),
          (mem_lattice_zero_iff K).1 hq⟩
    have hreduce : reduce K
        (y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1)) hx =
        -reduce K
          ((u - algebraMap F K n) /
            (S.upperUniformizer : K) ^ (a : ℤ)) hq := by
      unfold reduce
      change residueMap K
          (⟨y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1), _⟩ :
            ringOfIntegers K) = -residueMap K qO
      rw [← map_neg]
      congr 1
      apply Subtype.ext
      exact hquot
    rw [hreduce, map_neg]
    change -((PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
      (reduce K
        ((u - algebraMap F K n) /
          (S.upperUniformizer : K) ^ (a : ℤ)) hq)) = -zeta
    congr 1
    simpa only [zeta, sourceInitialResidue] using congrArg
      (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
        hsubInitial
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let betaInv := etaZero *
    wildOddCompactLambda F K ht hres pi hpi ^ (Module.finrank F K - 1)
  have htrace : ∀ z : ResidueField F,
      (data.baseAddChar.character
        ((A : F) * trace F K
          (y * ((pi : K) ^ d) ^ 2 *
            (teichmuller K
              (PhaseReductionResidualCoordinateSource.residueEquiv
                hres z) : K))) : ℂ) =
        C.lower ((betaInv * zeta) * z) := by
    intro z
    exact wildOddCompactNormalizedTraceCharacter F K ht hres pi hpi hgen
      data.baseAddChar A hA C betaInv zeta rfl (a : ℤ) d y hy hdepth
        hinitial z
  apply lowActual_natural_of_trace
    F K ht hres pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P table W hepsilon C
        betaInv zeta
  dsimp only
  intro z
  have hz := htrace z
  simpa only [A, wildOddLowNormalizationCoefficient,
    lowOddExactCoefficient, y, n, u, S,
    phaseReductionResidualCoordinateSource,
    phaseReductionSourceCoordinate_coe,
    phaseReductionUpperUniformizer_coe] using hz

/-- Strict Low-row normalization with the manuscript's inverse-Frobenius
coefficient, not its polynomially equivalent display. -/
noncomputable def lowActualNormalization_strict
    (hepsilon : epsilon = 1)
    (hstrict : (data.twistData 1).conductor < s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    WildOddUpperPolarNormalization (ResidueField F) (Module.finrank F K) := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a : ℕ := s + 1 - 2 * d
  let u : K := lowNormalizedRatio F K epsilon1 P
  let hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    have hc : (data.twistData 1).conductor = 2 * d + 1 := by
      simpa [hepsilon] using hF.conductor_eq
    have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
      dsimp only [a]
      omega
    change ord K (lowNormalizedRatio F K epsilon1 P) = _
    rw [lowNormalizedRatio_order F K epsilon1 hepsilon1 P, ha]
    norm_num
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (a : ℤ) u hu
  let zeta := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    zetaK
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  exact wildOddUpperPolarNormalizationOfSource F (Module.finrank F K) hchar
    C etaZero zeta

/-- Closed strict Low-row natural polar coefficient in the accepted
inverse-Frobenius normalization. -/
theorem lowActual_naturalPolar_strict
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hstrict : (data.twistData 1).conductor < s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let N := lowActualNormalization_strict F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon hstrict C
    (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W).upperPolarInLowerCoordinate
          (Module.finrank F K) C hres = N.betaInv * N.zeta := by
  dsimp only
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let a : ℕ := s + 1 - 2 * d
  let u : K := lowNormalizedRatio F K epsilon1 P
  have hc : (data.twistData 1).conductor = 2 * d + 1 := by
    simpa [hepsilon] using hF.conductor_eq
  have ha : s + 1 + 1 - (data.twistData 1).conductor = a := by
    dsimp only [a]
    omega
  have hu : ord K u = (((a : ℕ) : ℤ) : WithTop ℤ) := by
    change ord K (lowNormalizedRatio F K epsilon1 P) = _
    rw [lowNormalizedRatio_order F K epsilon1 hepsilon1 P, ha]
    norm_num
  let zetaK := sourceInitialResidue K S.upperUniformizer S.upper_order
    (a : ℤ) u hu
  let zeta := (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
    zetaK
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let lambda := wildOddCompactLambda F K ht hres pi hpi
  let betaInv := etaZero * lambda ^ (Module.finrank F K - 1)
  have hann : ∀ z : ResidueField F,
      C.lower (etaZero *
        (z ^ Module.finrank F K -
          lambda ^ (Module.finrank F K - 1) * z)) = 1 := by
    intro z
    simpa only [etaZero, A, hA, lambda, S] using
      wildOddLowNormalization_annihilator F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table C z
  have hbeta : (C.frobeniusEquiv hchar).symm etaZero = betaInv := by
    simpa only [betaInv] using
      wildOddUpperEtaZero_frobeniusPreimage_eq hchar C etaZero lambda hann
  have hnatural := lowActual_naturalPolar_strict_product F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table W hepsilon hstrict C
  simpa only [lowActualNormalization_strict,
    wildOddUpperPolarNormalizationOfSource, S, a, u, hu, zetaK, zeta,
    hchar, A, hA, etaZero, lambda, betaInv, hbeta]
      using hnatural

private theorem lowBoundary_zeta_eq_sourceResidue
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let e := PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) hres
    N.zeta = e.symm (reduce K (lowNormalizedRatio F K epsilon1 P)
      N.u_integral) := by
  rfl

private theorem lowBoundary_dZero_eq_sourceNormResidue
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let e := PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) hres
    let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
    let hn : algebraMap F K n ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap]
      have hu : ord K (lowNormalizedRatio F K epsilon1 P) =
          (0 : WithTop ℤ) := by
        simpa [hboundary] using
          (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)
      have hnord : ord F n = (0 : WithTop ℤ) := by
        rw [show n = norm F K (lowNormalizedRatio F K epsilon1 P) by
          symm
          simpa only [n, lowOddNormalizedNorm] using
            (lowNormalizedRatio_norm F K epsilon1 P)]
        rw [ord_norm, hres, one_nsmul, hu]
      rw [hnord, nsmul_zero]
      exact le_rfl
    N.dZero = e.symm (reduce K (algebraMap F K n) hn) := by
  dsimp only
  let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  have hnEq : (N.nO : F) = n := by
    exact N.nO_coe.trans (by
      simpa only [n, lowOddNormalizedNorm] using
        (lowNormalizedRatio_norm F K epsilon1 P))
  have hdEq : residueMap F N.nO = N.dZero := N.residueMap_nO
  apply e.injective
  rw [e.apply_symm_apply, ← hdEq]
  rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
  unfold reduce
  let nOK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) N.nO
  change extensionResidueMap F K (residueMap F N.nO) =
    residueMap K ⟨algebraMap F K n, _⟩
  rw [show (⟨algebraMap F K n, _⟩ : ringOfIntegers K) = nOK by
    apply Subtype.ext
    change algebraMap F K n = algebraMap F K (N.nO : F)
    rw [hnEq]]
  exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
    (ValuativeRel.valuation F) (ValuativeRel.valuation K) N.nO

include hF in
private theorem lowBoundary_twice_depth
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    (0 : ℤ) + 2 * (d : ℤ) = (s + 1 : ℕ) := by
  have hm := hF.conductor_eq
  rw [hepsilon, hboundary] at hm
  simpa only [zero_add] using
    (show (2 : ℤ) * (d : ℤ) = (s + 1 : ℕ) by exact_mod_cast
      (show 2 * d = s + 1 by omega))

private theorem lowBoundary_normalizedDifference_order
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    ord K
      (algebraMap F K
          (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)) -
        lowNormalizedRatio F K epsilon1 P) = (0 : WithTop ℤ) := by
  let A : Fˣ := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let betaU : Kˣ := lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table W
  let GammaU : Kˣ := lowGammaK F K delta epsilon1
  have hratio : (betaU : K) / (GammaU : K) =
      algebraMap F K (A : F) * (algebraMap F K n - u) := by
    simpa only [A, u, n, betaU, GammaU] using
      (wildOddLowStationaryRatio_eq_normalized F K ht hres pi hpi hgen
        data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table W)
  let hSource := (lowNormPolynomialPrecision F K ht hres pi hpi hgen
    (data.twistData 1) hminimal chiK hchi hF hLow).sourceDecomposition
  let Gamma : AdmissibleGamma K chiK psiK := ⟨GammaU, hgammaK⟩
  let R : StationaryClassRepresentative K chiK psiK hSource
      (Gamma : Kˣ) Gamma.property :=
    StationaryClassRepresentative.ofCoefficientRepresentative W.representative
      (by simpa only [hSource, Gamma, GammaU] using W.represents)
  have hRord : ord K (R.toLamprecht : K) = (0 : WithTop ℤ) := by
    simpa only [sub_self, WithTop.coe_zero] using
      (stationaryNumeratorClass_representative_ord K chiK psiK
        (chiK.conductor : ℤ)
        (stationaryDepthOfConductorDecomposition K chiK hSource)
        (Gamma : Kˣ) Gamma.property R.toLamprecht R.toLamprecht_represents)
  have hbeta : ord K (betaU : K) = (0 : WithTop ℤ) := by
    change ord K ((R.unit : Kˣ) : K) = _
    rw [StationaryClassRepresentative.coe_unit]
    simpa only [StationaryClassRepresentative.toLamprecht] using hRord
  have hepsilonZero : ord K (epsilon1 : K) = (0 : WithTop ℤ) := by
    rw [hepsilon1, hboundary]
    simp
  let c : ℤ := ((s + 1 + 1 : ℕ) : ℤ) + data.baseAddChar.conductor
  have hdeltaC : ord F (delta : F) = ((c : ℤ) : WithTop ℤ) := by
    rw [hdelta]
  have hGamma : ord K (GammaU : K) =
      (((ramificationIndex F K : ℤ) * c : ℤ) : WithTop ℤ) := by
    dsimp only [GammaU, lowGammaK]
    rw [Units.val_div_eq_div_val, ord_div,
      Units.coe_map, MonoidHom.coe_coe, ord_algebraMap, hdeltaC,
      hepsilonZero, sub_zero]
    rw [← WithTop.coe_nsmul]
    congr 1
  have hA0 := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  have hA : ord K (algebraMap F K (A : F)) =
      ((-((ramificationIndex F K : ℤ) * c) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap]
    change ramificationIndex F K • ord F (A : F) = _
    rw [show ord F (A : F) = ((-c : ℤ) : WithTop ℤ) by
      rw [show ord F (A : F) =
          (-(((((s + 1) + 1 : ℕ) : ℤ) + data.baseAddChar.conductor) :
            WithTop ℤ)) by simpa only [A] using hA0]
      norm_cast]
    rw [← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hyne : algebraMap F K n - u ≠ 0 := by
    intro hy
    have hlhs : (betaU : K) / (GammaU : K) ≠ 0 :=
      div_ne_zero (Units.ne_zero betaU) (Units.ne_zero GammaU)
    apply hlhs
    rw [hratio, hy, mul_zero]
  have hyordNe : ord K (algebraMap F K n - u) ≠ ⊤ :=
    (ord_ne_top_iff K).2 hyne
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hyordNe
  have hord := congrArg (ord K) hratio
  rw [ord_div, hbeta, hGamma, ord_mul, hA, ← hb] at hord
  norm_cast at hord
  have hb0 : b = 0 := by linarith
  rw [← hb, hb0]
  rfl

private theorem lowBoundary_normalizedInitial
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let e := PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) hres
    let u := lowNormalizedRatio F K epsilon1 P
    let n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
    let y := algebraMap F K n - u
    ∀ hx : y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1) ∈ lattice K 0,
      e.symm (reduce K
        (y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1)) hx) =
          -(N.zeta - N.dZero) := by
  dsimp only
  let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let y : K := algebraMap F K n - u
  have htwice : 2 * d = s + 1 := by
    have hm := hF.conductor_eq
    rw [hepsilon, hboundary] at hm
    omega
  have hpower : ((pi : K) ^ d) ^ 2 = (pi : K) ^ (s + 1) := by
    rw [← pow_mul]
    congr 1
    omega
  have harg : y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1) = y := by
    rw [hpower]
    field_simp [pow_ne_zero _ hpi.ne_zero]
  intro hx
  have hu : u ∈ lattice K 0 := by
    exact N.u_integral
  have hn : algebraMap F K n ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    have huord : ord K u = (0 : WithTop ℤ) := by
      simpa only [u] using
        (show ord K (lowNormalizedRatio F K epsilon1 P) =
            (0 : WithTop ℤ) by
          simpa [hboundary] using
            (lowNormalizedRatio_order F K epsilon1 hepsilon1 P))
    have hnord : ord F n = (0 : WithTop ℤ) := by
      rw [show n = norm F K u by
        symm
        simpa only [n, u, lowOddNormalizedNorm] using
          (lowNormalizedRatio_norm F K epsilon1 P)]
      rw [ord_norm, hres, one_nsmul, huord]
    rw [hnord, nsmul_zero]
    exact le_rfl
  have hyMem : y ∈ lattice K 0 := by
    simpa only [y] using sub_mem_lattice K hn hu
  have hreduceArg :
      reduce K (y * ((pi : K) ^ d) ^ 2 / (pi : K) ^ (s + 1)) hx =
        reduce K y hyMem := by
    unfold reduce
    congr 1
    exact Subtype.ext harg
  rw [hreduceArg]
  have hz : N.zeta = e.symm (reduce K u hu) := by
    simpa only [N, e, u] using
      (lowBoundary_zeta_eq_sourceResidue F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary)
  have hd : N.dZero = e.symm (reduce K (algebraMap F K n) hn) := by
    simpa only [N, e, n] using
      (lowBoundary_dZero_eq_sourceNormResidue F K ht hres pi hpi hgen data
        hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary)
  have hreduce : e.symm (reduce K y hyMem) =
      e.symm (reduce K (algebraMap F K n) hn) -
        e.symm (reduce K u hu) := by
    unfold reduce
    rw [show (⟨y, (mem_lattice_zero_iff K).1 hyMem⟩ : ringOfIntegers K) =
        (⟨algebraMap F K n, (mem_lattice_zero_iff K).1 hn⟩ :
          ringOfIntegers K) -
            ⟨u, (mem_lattice_zero_iff K).1 hu⟩ by
      apply Subtype.ext
      rfl]
    simp only [map_sub]
  rw [hreduce, ← hd, ← hz]
  ring

private theorem lowOddBoundary_normalizedTrace
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    let betaInv := (C.frobeniusEquiv hchar).symm etaZero
    let source := phaseReductionSourceCoordinate K S.upperUniformizer d
    ∀ z : ResidueField F,
      (data.baseAddChar.character
        (lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT) *
          trace F K
            ((algebraMap F K
                (lowOddNormalizedNorm (F := F) (K := K) (P := P)
                  (hT := hT)) -
                lowNormalizedRatio F K epsilon1 P) *
              (source : K) ^ 2 *
                (teichmuller K
                  (PhaseReductionResidualCoordinateSource.residueEquiv hres z) :
                    K))) : ℂ) =
        C.lower ((betaInv * (N.zeta - N.dZero)) * z) := by
  dsimp only
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A : Fˣ := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let betaInv := (C.frobeniusEquiv hchar).symm etaZero
  let lambda := wildOddCompactLambda F K ht hres pi hpi
  let u : K := lowNormalizedRatio F K epsilon1 P
  let n : F := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  let y : K := algebraMap F K n - u
  have hann := wildOddLowNormalization_annihilator F K ht hres pi hpi hgen
    data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table C
  have hbeta : betaInv = etaZero * lambda ^ (Module.finrank F K - 1) := by
    exact wildOddUpperEtaZero_frobeniusPreimage_eq hchar C etaZero lambda hann
  have hy : ord K y = (0 : WithTop ℤ) := by
    simpa only [y, n, u] using
      (lowBoundary_normalizedDifference_order F K ht hres pi hpi hgen data
        chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table W hboundary)
  have hdepth : (0 : ℤ) + 2 * (d : ℤ) = (s + 1 : ℕ) :=
    lowBoundary_twice_depth F K data hF hepsilon hboundary
  have hinitial := lowBoundary_normalizedInitial F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
      hT hgammaF hgammaK P table W hepsilon hboundary
  intro z
  have htrace := wildOddCompactNormalizedTraceCharacter F K ht hres pi hpi
    hgen data.baseAddChar A hA C betaInv (N.zeta - N.dZero) hbeta
      (0 : ℤ) d y hy hdepth hinitial z
  simpa only [A, y, n, u, S, N, etaZero, betaInv, hchar,
    phaseReductionResidualCoordinateSource, phaseReductionSourceCoordinate_coe,
    phaseReductionUpperUniformizer_coe, wildOddLowNormalizationCoefficient,
    lowOddExactCoefficient] using htrace

/-- At the Low boundary, the natural upper polar coefficient retains the norm
row translation `betaInv * (zeta - dZero)` before displayed-coordinate
Frobenius transport. -/
theorem lowActual_naturalPolar_boundary
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K)) :
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    let N := wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
      hchar C etaZero B.zeta
    (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table W).upperPolarInLowerCoordinate
          (Module.finrank F K) C hres =
      N.betaInv * (N.zeta - N.dZero) := by
  dsimp only
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A : Fˣ := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let N := wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
    hchar C etaZero B.zeta
  have htrace := lowOddBoundary_normalizedTrace F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1
      hT hgammaF hgammaK P table W hepsilon hboundary C
  exact lowActual_natural_of_trace F K ht hres pi hpi hgen data chiK psiK
    hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table W hepsilon C N.betaInv (N.zeta - N.dZero) (by
        simpa only [S, A, hA, B, N, etaZero, hchar,
          wildOddUpperPolarNormalizationOfSource,
          WildOddBoundaryNormNormalization.dZero_eq] using htrace)

/-- Complete strict Low row below the break: the displayed upper pair is
`wildOddUpperPairBelow N.eta gamma`, with the affine term supplied by the
actual base row and no hidden affine contribution from the quadratic correction. -/
theorem wildOdd_actualLowCoefficients_strict
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hodd : Odd (Module.finrank F K))
    (hepsilon : epsilon = 1)
    (hstrict : (data.twistData 1).conductor < s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2)
    (gamma : ResidueField F)
    (hbase :
      (lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table (Module.finrank F K) C).affineCoefficient
            hcharOdd C.lower_ne_one =
        (lowActualNormalization_strict F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon hstrict C).eta *
            gamma)
    (units : ResidueField F → Kˣ)
    (hunits : ∀ X,
      let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
      let z := (C.frobeniusEquiv hchar).symm X
      let x := phaseReductionUpperSourceDisplacement F K pi d z
      let u := lowNormalizedRatio F K epsilon1 P
      (units X : K) = 1 + u * x) :
    let p := Module.finrank F K
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let N := lowActualNormalization_strict F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon hstrict C
    let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
      pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table p hchar C W
    upper.upperCoefficientPair C.lower_ne_one hcharOdd =
      wildOddUpperPairBelow N.eta gamma := by
  dsimp only
  let p := Module.finrank F K
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let N := lowActualNormalization_strict F K ht hres pi hpi hgen data hF
    delta epsilon1 hdelta hepsilon1 hT hgammaF P hepsilon hstrict C
  let D := lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table W
  let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
    pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table p hchar C W
  let base := lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table p C
  have hnat : D.upperPolarInLowerCoordinate p C hres =
      N.betaInv * N.zeta := by
    simpa only [D, N, p] using lowActual_naturalPolar_strict F K ht hres pi
      hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table W hepsilon hstrict C
  have hdisplay : C.frobeniusEquiv hchar
        (D.upperPolarInLowerCoordinate p C hres) =
      N.etaZero * N.zeta ^ p :=
    LocalLamprechtPhaseData.displayedPolar_eq_of_natural D p hchar C hres
      N.betaInv N.etaZero N.zeta hnat N.betaInv_pow
  have hpolar : C.frobeniusEquiv hchar
        (D.upperPolarInLowerCoordinate p C hres) =
      (wildOddUpperPairBelow N.eta gamma).polar := by
    refine hdisplay.trans ?_
    calc
      N.etaZero * N.zeta ^ p =
          (wildOddUpperPairBelow N.eta (1 : ResidueField F)).polar :=
        wildOdd_upperPolar_below p N
      _ = (wildOddUpperPairBelow N.eta gamma).polar := rfl
  obtain ⟨q, hq⟩ := wildOdd_actualLowDisplayed_below F K ht hres pi hpi
    hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table hodd hepsilon hstrict C W units
        hunits
  have hfun : ∀ x, upper x = base x * C.lower (q * x ^ 2) := by
    simpa only [upper, base, lowSourceBaseCriticalPolarFunction_apply] using hq
  change upper.upperCoefficientPair C.lower_ne_one hcharOdd = _
  apply WildOddUpperCoefficientPair.ext
  · change C.frobeniusEquiv hchar
        ((PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres))) =
      (wildOddUpperPairBelow N.eta gamma).polar
    simpa only [LocalLamprechtPhaseData.upperPolarInLowerCoordinate] using
      hpolar
  · change upper.affineCoefficient hcharOdd C.lower_ne_one = N.eta * gamma
    rw [CriticalPolarFunction.affineCoefficient_of_base_mul_quadratic
      C.lower_ne_one hcharOdd upper base q hfun]
    simpa only [base, N] using hbase

/-- The complete boundary row.  The scale in the norm row is identified with
the accepted boundary normalization before extracting the affine coefficient. -/
theorem wildOdd_actualLowCoefficients_boundary
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hodd : Odd (Module.finrank F K))
    (hepsilon : epsilon = 1)
    (hboundary : (data.twistData 1).conductor = s + 1 + 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2)
    (gamma gammaZero : ResidueField F)
    (hbase :
      let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
        (by omega) pi hpi hgen
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let A := wildOddLowNormalizationCoefficient
        (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
      let hA := wildOddLowNormalizationCoefficient_order
        (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
        (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
        (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
        (hT := hT) (hgammaF := hgammaF) (P := P)
      let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
      let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
      let N := wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
        hchar C etaZero B.zeta
      (lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table (Module.finrank F K) C).affineCoefficient
            hcharOdd C.lower_ne_one = N.eta * gamma)
    (hnorm :
      let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
        (by omega) pi hpi hgen
      let S := phaseReductionResidualCoordinateSource F K hres pi hpi
      let A := wildOddLowNormalizationCoefficient
        (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
      let hA := wildOddLowNormalizationCoefficient_order
        (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
        (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
        (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
        (hT := hT) (hgammaF := hgammaF) (P := P)
      let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
        data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
      let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
      let N := wildOddUpperPolarNormalizationOfSource F (Module.finrank F K)
        hchar C etaZero B.zeta
      let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
      CriticalPolarFunction.affineCoefficient hcharOdd C.lower_ne_one
        (lowSourceNormCriticalPolarFunction F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P (Module.finrank F K) C j) =
        N.etaZero * gammaZero)
    (units : ResidueField F → Kˣ)
    (hunits : ∀ X,
      let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
        (by have hm := hF.conductor_gt_one; omega) pi hpi hgen
      let z := (C.frobeniusEquiv hchar).symm X
      let x := phaseReductionUpperSourceDisplacement F K pi d z
      let u := lowNormalizedRatio F K epsilon1 P
      (units X : K) = 1 + u * x) :
    let p := Module.finrank F K
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let S := phaseReductionResidualCoordinateSource F K hres pi hpi
    let A := wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
    let hA := wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)
    let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
    let N := wildOddUpperPolarNormalizationOfSource F p hchar C etaZero B.zeta
    let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
      pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table p hchar C W
    upper.upperCoefficientPair C.lower_ne_one hcharOdd =
      wildOddUpperPairBoundary p N.etaZero N.dZero gamma gammaZero := by
  dsimp only
  let p := Module.finrank F K
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    (by omega) pi hpi hgen
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let A := wildOddLowNormalizationCoefficient
    (F := F) (K := K) (delta := delta) (hT := hT) (P := P)
  let hA := wildOddLowNormalizationCoefficient_order
    (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
    (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
    (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
    (hT := hT) (hgammaF := hgammaF) (P := P)
  let B := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen data
    hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  let etaZero := wildOddUpperEtaZero S data.baseAddChar A (s + 1) hA C
  let N := wildOddUpperPolarNormalizationOfSource F p hchar C etaZero B.zeta
  let D := lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table W
  let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
    pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK P table p hchar C W
  let base := lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table p C
  let j : OddNormIndex F K := ⟨1, one_ne_zero⟩
  let normRow := lowSourceNormCriticalPolarFunction F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hT hgammaF P p C j
  have hnat : D.upperPolarInLowerCoordinate p C hres =
      N.betaInv * (N.zeta - N.dZero) := by
    simpa only [D, N, p, hchar, S, A, hA, B, etaZero] using
      lowActual_naturalPolar_boundary F K ht hres pi hpi hgen data chiK
        psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table W hepsilon hboundary C
  have hdisplay : C.frobeniusEquiv hchar
        (D.upperPolarInLowerCoordinate p C hres) =
      N.etaZero * (N.zeta - N.dZero) ^ p :=
    LocalLamprechtPhaseData.displayedPolar_eq_of_natural D p hchar C hres
      N.betaInv N.etaZero (N.zeta - N.dZero) hnat N.betaInv_pow
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  have hpolar : C.frobeniusEquiv hchar
        (D.upperPolarInLowerCoordinate p C hres) =
      (wildOddUpperPairBoundary p N.etaZero N.dZero gamma gammaZero).polar := by
    refine hdisplay.trans ?_
    calc
      N.etaZero * (N.zeta - N.dZero) ^ p =
          (wildOddUpperPairBoundary p N.etaZero N.dZero 0 0).polar :=
        wildOdd_upperPolar_boundary p inferInstance N
      _ = (wildOddUpperPairBoundary p N.etaZero N.dZero gamma gammaZero).polar :=
        rfl
  let u : K := lowNormalizedRatio F K epsilon1 P
  have hu : ord K u = (0 : WithTop ℤ) := by
    simpa [u, hboundary] using
      lowNormalizedRatio_order F K epsilon1 hepsilon1 P
  let nO : ringOfIntegers F := ⟨norm F K u, by
    rw [← mem_lattice_zero_iff, mem_lattice, ord_norm, hres, one_nsmul, hu]
    exact le_rfl⟩
  have hnO : nO = B.nO := by
    apply Subtype.ext
    exact B.nO_coe.symm
  have hscale : residueMap F nO = N.dZero := by
    rw [hnO, B.residueMap_nO]
    simpa only [N, wildOddUpperPolarNormalizationOfSource] using B.dZero_eq
  obtain ⟨q, hq⟩ := wildOdd_actualLowDisplayed_boundary F K ht hres pi hpi
    hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table hodd hepsilon hboundary C W units
        hunits
  have hfun : ∀ x, upper x =
      base x * (normRow (N.dZero * x))⁻¹ * C.lower (q * x ^ 2) := by
    intro x
    have hx := hq x
    dsimp only at hx
    simpa only [upper, base, normRow, j,
      lowSourceBaseCriticalPolarFunction_apply,
      lowSourceNormCriticalPolarFunction_apply, u, nO, hscale] using hx
  change upper.upperCoefficientPair C.lower_ne_one hcharOdd = _
  apply WildOddUpperCoefficientPair.ext
  · change C.frobeniusEquiv hchar
        ((PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          (D.polarCoefficient (C.upper hres) (C.upper_ne_one hres))) =
      (wildOddUpperPairBoundary p N.etaZero N.dZero gamma gammaZero).polar
    simpa only [LocalLamprechtPhaseData.upperPolarInLowerCoordinate] using
      hpolar
  · change upper.affineCoefficient hcharOdd C.lower_ne_one =
      N.etaZero * N.dZero * (gamma - gammaZero)
    rw [CriticalPolarFunction.affineCoefficient_of_base_mul_invScale_quadratic
      C.lower_ne_one hcharOdd upper base normRow N.dZero q hfun]
    have hbase' : base.affineCoefficient hcharOdd C.lower_ne_one =
        N.eta * gamma := by
      simpa only [base, N, hchar, S, A, hA, B, etaZero] using hbase
    have hnorm' : normRow.affineCoefficient hcharOdd C.lower_ne_one =
        N.etaZero * gammaZero := by
      simpa only [normRow, j, N, hchar, S, A, hA, B, etaZero] using hnorm
    rw [hbase', hnorm', N.eta_eq]
    ring

/-- The actual Low upstairs row at even conductor parity is the literal
constant-one row, hence has coefficient pair `(0,0)`. -/
theorem wildOdd_actualLowCoefficients_even
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table)
    (hepsilon : epsilon = 0)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let p := Module.finrank F K
    let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
      (by omega) pi hpi hgen
    let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
      pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table p hchar C W
    upper.upperCoefficientPair C.lower_ne_one hcharOdd =
      wildOddUpperPairEven := by
  dsimp only
  apply CriticalPolarFunction.upperCoefficientPair_eq_even
    C.lower_ne_one hcharOdd
  intro X
  exact lowSourceDisplayedUpstairsFunction_eq_one_of_even F K ht hres pi hpi
    hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table (Module.finrank F K)
        (residueCharacteristic_eq_degree_of_positive_break F K ht (by omega)
          pi hpi hgen) C W hepsilon X

end LowActual

/-! ## Cohesive public upper-table package -/

/-- The complete upper residual-coefficient responsibility.  The façade
exports the canonical coordinate transports, natural coefficients, retained
quadratic correction, all three odd rows, both even-parity rows, and exact
representative translation without importing lower coefficient theory. -/
structure WildOddUpperResidualCoefficientsAPI : Prop where
  coordinateTransport : type_of% @wildOdd_upperCoordinateTransport.{u, v}
  upperInLowerCoordinate :
    type_of%
      @LocalLamprechtPhaseData.upperInLowerCoordinate_polarCoefficient.{u, v}
  inverseFrobeniusDisplay :
    type_of% @LocalLamprechtPhaseData.displayedUpper_exactDirection.{u, v}
  displayedPolar :
    type_of% @LocalLamprechtPhaseData.displayedPolar_eq_of_natural.{u, v}
  displayedAffine :
    type_of%
      @LocalLamprechtPhaseData.displayedInLowerCoordinate_affineCoefficient.{u, v}
  initialResidueNonzero : type_of% @sourceInitialResidue_ne_zero.{u}
  initialResidueNorm : type_of% @sourceInitialResidue_norm_eq_pow.{u, v}
  initialResidueNormDownstairs :
    type_of% @sourceInitialResidue_norm_downstairs_eq_pow.{u, v}
  extremeInitial :
    type_of% @sourceInitialResidue_u_sub_norm_extremeCases.{u, v}
  highActualDZeroNonzero : type_of% @highActualNormalization_dZero_ne_zero
  highActualSourceDisplacement : type_of% @highActualSourceUx_mem_lattice
  highActualSourceUnitCoe : type_of% @highActualSourceUnit_coe
  highGeneratorPolar : type_of% @highActual_generatorPolar_eq_etaZero
  highBasePolar : type_of% @highActual_basePolar_eq_eta
  naturalHigh : type_of% @highActual_naturalPolar
  naturalLowStrict : type_of% @lowActual_naturalPolar_strict
  naturalLowBoundary : type_of% @lowActual_naturalPolar_boundary
  quadraticHigh : type_of% @wildOdd_actualHighCorrection_eq_pureQuadratic
  quadraticLow : type_of% @wildOdd_actualLowCorrection_eq_pureQuadratic
  noHiddenAffine :
    type_of% @wildOdd_actualSourceDisplayedCorrection_eq_pureQuadratic.{u, v}
  highAbove : type_of% @wildOdd_actualHighCoefficients_above
  lowStrict : type_of% @wildOdd_actualLowCoefficients_strict
  lowBoundary : type_of% @wildOdd_actualLowCoefficients_boundary
  highEven : type_of% @wildOdd_actualHighCoefficients_even
  lowEven : type_of% @wildOdd_actualLowCoefficients_even
  representativeTranslation :
    type_of% @wildOdd_upperRepresentativeTranslation.{u}

/-- Principal exported theorem for the upper half of the wild odd residual
coefficient table. -/
theorem wildOdd_upperResidualCoefficients :
    WildOddUpperResidualCoefficientsAPI where
  coordinateTransport := wildOdd_upperCoordinateTransport
  upperInLowerCoordinate :=
    LocalLamprechtPhaseData.upperInLowerCoordinate_polarCoefficient
  inverseFrobeniusDisplay :=
    LocalLamprechtPhaseData.displayedUpper_exactDirection
  displayedPolar := LocalLamprechtPhaseData.displayedPolar_eq_of_natural
  displayedAffine :=
    LocalLamprechtPhaseData.displayedInLowerCoordinate_affineCoefficient
  initialResidueNonzero := sourceInitialResidue_ne_zero
  initialResidueNorm := sourceInitialResidue_norm_eq_pow
  initialResidueNormDownstairs := sourceInitialResidue_norm_downstairs_eq_pow
  extremeInitial := sourceInitialResidue_u_sub_norm_extremeCases
  highActualDZeroNonzero := highActualNormalization_dZero_ne_zero
  highActualSourceDisplacement := highActualSourceUx_mem_lattice
  highActualSourceUnitCoe := highActualSourceUnit_coe
  highGeneratorPolar := highActual_generatorPolar_eq_etaZero
  highBasePolar := highActual_basePolar_eq_eta
  naturalHigh := highActual_naturalPolar
  naturalLowStrict := lowActual_naturalPolar_strict
  naturalLowBoundary := lowActual_naturalPolar_boundary
  quadraticHigh := wildOdd_actualHighCorrection_eq_pureQuadratic
  quadraticLow := wildOdd_actualLowCorrection_eq_pureQuadratic
  noHiddenAffine := wildOdd_actualSourceDisplayedCorrection_eq_pureQuadratic
  highAbove := wildOdd_actualHighCoefficients_above
  lowStrict := wildOdd_actualLowCoefficients_strict
  lowBoundary := wildOdd_actualLowCoefficients_boundary
  highEven := wildOdd_actualHighCoefficients_even
  lowEven := wildOdd_actualLowCoefficients_even
  representativeTranslation := wildOdd_upperRepresentativeTranslation

end
end LanglandsFirstMainLemma
