import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Ramification.NormFiltration

/-!
# The common correction in the wild quadratic calculation

The high and low parameter theorems make different simultaneous existential
choices.  This file does not identify those choices in the fields.  Instead it
extracts from either package the same choice-relative pair

`u : Kˣ`, `n : Fˣ`, `N(u) = n`, `1 + n ≠ 0`,

together with its exact conductor and different shifts.  In the high adapter
the break-level unit `delta` remains present in
`n = beta / (N(alpha1) * delta)`.

All residue conclusions below are equalities in lattice quotients.  No field
representative of a stationary class or of a residue class is made canonical.
-/

namespace LanglandsFirstMainLemma

noncomputable section

set_option maxHeartbeats 4000000

private theorem residueCharacteristic_two_mem_lattice_one
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (hchar : residueCharacteristic F = 2) :
    (2 : F) ∈ lattice F 1 := by
  have hp :
      (((residueCharacteristic F : ℕ) : ringOfIntegers F) : F) ∈
        lattice F 1 := by
    apply (residueMap_eq_zero_iff F
      (residueCharacteristic F : ringOfIntegers F)).1
    change (residueCharacteristic F : ResidueField F) = 0
    exact CharP.cast_eq_zero (ResidueField F) (residueCharacteristic F)
  rw [hchar] at hp
  have hcast : (2 : F) = (((2 : ℕ) : ringOfIntegers F) : F) := by
    rw [← Nat.cast_ofNat]
    exact (Subring.coe_natCast (ringOfIntegers F) 2).symm
  rw [hcast]
  exact hp

/-- Choice-relative input for the common wild-quadratic correction.

`T` is the different exponent `t+1` and `m` is the downstairs conductor.
The source and target orders are both the signed shift `T-m`; this one record
therefore covers the low range, the boundary, and the strict high range. -/
structure WildQuadraticCommonCorrectionData
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (T m : ℕ) where
  /-- The selected upper-field ratio. -/
  u : Kˣ
  /-- Its selected lower-field norm ratio. -/
  n : Fˣ
  degree_eq_two : Module.finrank F K = 2
  residueDegree_eq_one : residueDegree F K = 1
  differentExponent_eq : differentExponent F K = T
  source_order : ord K (u : K) =
    ((((T : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : WithTop ℤ)
  target_order : ord F (n : F) =
    ((((T : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : WithTop ℤ)
  /-- Exact norm identity, not a congruence. -/
  norm_u : normUnits F K u = n
  /-- The displayed denominator is proved nonzero before any division. -/
  denominator_ne_zero : (1 : F) + (n : F) ≠ 0

namespace WildQuadraticCommonCorrectionData

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)

/-- The trace parameter `s=Tr(u)`. -/
def s : F := trace F K (C.u : K)

/-- The manuscript's signed quadratic dual `u^vee=-n/u`. -/
def dual : K := -(algebraMap F K (C.n : F)) / (C.u : K)

/-- The common denominator `1+n`. -/
def denominator : F := 1 + (C.n : F)

/-- The norm correction attached to the dual. -/
def z0 : F := norm F K (1 + C.dual) / C.denominator

/-- The norm correction attached to `u`. -/
def z1 : F := norm F K (1 + (C.u : K)) / C.denominator

def x : F := C.z0 - 1

def y : F := C.z1 - 1

/-- The signed additive combination used in the elementary phase. -/
def X : F := C.s + (C.n : F) * C.x + C.y

@[simp]
theorem denominator_ne_zero' : C.denominator ≠ 0 := by
  simpa only [denominator] using C.denominator_ne_zero

include C in
/-- Total ramification and degree two force ramification index two. -/
theorem ramificationIndex_eq_two : ramificationIndex F K = 2 := by
  have h := finrank_eq_ramificationIndex_mul_residueDegree F K
  rw [C.residueDegree_eq_one, mul_one, C.degree_eq_two] at h
  exact h.symm

/-- Field-valued form of the exact norm identity stored in the data. -/
theorem norm_u_field : norm F K (C.u : K) = (C.n : F) := by
  simpa only [coe_normUnits] using congrArg Units.val C.norm_u

private theorem norm_div (a b : K) :
    norm F K (a / b) = norm F K a / norm F K b := by
  rw [div_eq_mul_inv, map_mul, norm_apply, Algebra.norm_inv, div_eq_mul_inv]

private theorem norm_neg_two
    (hdegree : Module.finrank F K = 2) (a : K) :
    norm F K (-a) = norm F K a := by
  rw [show -a = algebraMap F K (-1 : F) * a by simp,
    map_mul, norm_algebraMap, hdegree]
  norm_num

/-- The signed dual has exactly the same norm `n`. -/
theorem norm_dual : norm F K C.dual = (C.n : F) := by
  rw [dual, norm_div (F := F) (K := K),
    norm_neg_two (F := F) (K := K) C.degree_eq_two,
    norm_algebraMap, C.degree_eq_two, C.norm_u_field]
  field_simp [Units.ne_zero C.n]

/-- The exact quadratic norm expansion for `1+u`. -/
theorem norm_one_add_u :
    norm F K (1 + (C.u : K)) = 1 + C.s + (C.n : F) := by
  have h := wildQuadratic_normPolynomialValue_eq_trace_add_norm
    F K C.degree_eq_two (C.u : K)
  rw [normPolynomialValue, C.norm_u_field] at h
  dsimp only [s]
  linear_combination h

/-- The exact quadratic norm expansion for `1+u^vee`, with the minus trace. -/
theorem norm_one_add_dual :
    norm F K (1 + C.dual) = 1 - C.s + (C.n : F) := by
  have hone : 1 + C.dual =
      -(algebraMap F K (C.n : F) - (C.u : K)) / (C.u : K) := by
    rw [dual]
    field_simp [Units.ne_zero C.u]
    ring
  have hsub := wildQuadratic_norm_sub
    F K C.degree_eq_two C.n (C.u : K)
  rw [hone, norm_div (F := F) (K := K),
    norm_neg_two (F := F) (K := K) C.degree_eq_two,
    hsub, C.norm_u_field]
  dsimp only [s]
  field_simp [Units.ne_zero C.n]
  ring

/-- The dual sign is also exact at trace level. -/
theorem trace_dual : trace F K C.dual = -C.s := by
  have h := wildQuadratic_normPolynomialValue_eq_trace_add_norm
    F K C.degree_eq_two C.dual
  rw [normPolynomialValue, C.norm_dual, C.norm_one_add_dual] at h
  linear_combination -h

theorem z0_eq :
    C.z0 = (1 - C.s + (C.n : F)) / C.denominator := by
  rw [z0, C.norm_one_add_dual]

theorem z1_eq :
    C.z1 = (1 + C.s + (C.n : F)) / C.denominator := by
  rw [z1, C.norm_one_add_u]

/-- First sign-sensitive identity in Lemma `lem:quad-X`. -/
theorem x_eq : C.x = -C.s / C.denominator := by
  rw [x, C.z0_eq]
  field_simp [C.denominator_ne_zero']
  dsimp only [denominator]
  ring

/-- Second sign-sensitive identity in Lemma `lem:quad-X`. -/
theorem y_eq : C.y = C.s / C.denominator := by
  rw [y, C.z1_eq]
  field_simp [C.denominator_ne_zero']
  dsimp only [denominator]
  ring

/-- Exact norm-minus-trace identity of Lemma `lem:quad-X`:
`s+n*x+y=2s/(1+n)`. -/
theorem X_eq : C.X = 2 * C.s / C.denominator := by
  rw [X, C.x_eq, C.y_eq]
  field_simp [C.denominator_ne_zero']
  dsimp only [denominator]
  ring

/-- The denominator clears `z0` in the manuscript direction. -/
theorem denominator_mul_z0 :
    C.denominator * C.z0 = norm F K (1 + C.dual) := by
  rw [z0]
  exact mul_div_cancel₀ _ C.denominator_ne_zero'

/-- The denominator clears `z1` in the manuscript direction. -/
theorem denominator_mul_z1 :
    C.denominator * C.z1 = norm F K (1 + (C.u : K)) := by
  rw [z1]
  exact mul_div_cancel₀ _ C.denominator_ne_zero'

/-- Exact selected-parameter factorization
`n-u=-u(1+u^vee)`. -/
theorem n_sub_u_eq :
    algebraMap F K (C.n : F) - (C.u : K) =
      -(C.u : K) * (1 + C.dual) := by
  rw [dual]
  field_simp [Units.ne_zero C.u]
  ring

/-- Exact norm ratio used in the four stationary representatives:
`N(n-u)=n(1+n)z0`. -/
theorem norm_n_sub_u_eq :
    norm F K (algebraMap F K (C.n : F) - (C.u : K)) =
      (C.n : F) * C.denominator * C.z0 := by
  rw [C.n_sub_u_eq, map_mul,
    norm_neg_two (F := F) (K := K) C.degree_eq_two,
    C.norm_u_field]
  calc
    (C.n : F) * norm F K (1 + C.dual) =
        (C.n : F) * (C.denominator * C.z0) := by
      rw [C.denominator_mul_z0]
    _ = (C.n : F) * C.denominator * C.z0 := by ring

/-- Exact second ratio `N(1+u)=(1+n)z1`. -/
theorem norm_one_add_u_eq_denominator_mul_z1 :
    norm F K (1 + (C.u : K)) = C.denominator * C.z1 := by
  exact C.denominator_mul_z1.symm

/-- The signed additive contribution of the same four selected parameters
is exactly `-s`. -/
theorem signed_trace_sum_eq :
    trace F K (algebraMap F K (C.n : F) - (C.u : K)) + 1 -
        (C.n : F) - ((C.n : F) + 1) = -C.s := by
  rw [map_sub, trace_algebraMap, C.degree_eq_two]
  dsimp only [s]
  ring

/-- Trace of the inverse in the exact direction used for the strict odd
critical element. -/
theorem trace_inv_eq :
    trace F K ((C.u : K)⁻¹) = C.s / (C.n : F) := by
  have hdual : C.dual =
      algebraMap F K (-(C.n : F)) * (C.u : K)⁻¹ := by
    rw [dual, div_eq_mul_inv, map_neg]
  have htrace : trace F K C.dual =
      -(C.n : F) * trace F K ((C.u : K)⁻¹) := by
    rw [hdual, ← Algebra.smul_def, map_smul]
    simp only [smul_eq_mul]
  rw [C.trace_dual] at htrace
  dsimp only [s] at htrace ⊢
  apply (eq_div_iff (Units.ne_zero C.n)).2
  linear_combination htrace

/-- The selected reciprocal, viewed in the field.  It is not replaced by a
canonical representative of its graded class. -/
def reciprocal : K := ((C.u)⁻¹ : Kˣ)

/-- The reciprocal has the exact opposite signed depth `m-T`. -/
theorem reciprocal_order :
    ord K C.reciprocal =
      ((((m : ℕ) : ℤ) - ((T : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [reciprocal, Units.val_inv_eq_inv_val, ord_inv, C.source_order,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  ring

/-- The exact source-lattice membership used in the strict high odd case. -/
theorem reciprocal_mem :
    C.reciprocal ∈ lattice K ((m : ℤ) - (T : ℤ)) := by
  rw [mem_lattice, C.reciprocal_order]

/-- The manuscript's strict-high critical scalar `c_chi=-Tr(u⁻¹)`. -/
def cChi : F := -trace F K C.reciprocal

/-- Exact field identity relating the common norm correction to `c_chi`.
The nonvanishing hypothesis is kept explicit; it will follow from the exact
odd target depth in the strict high specialization. -/
theorem x_div_cChi_eq
    (hcChi : C.cChi ≠ 0) :
    C.x / C.cChi = (C.n : F) / C.denominator := by
  have htrace : trace F K C.reciprocal = C.s / (C.n : F) := by
    simpa only [reciprocal, Units.val_inv_eq_inv_val] using C.trace_inv_eq
  have hs : C.s ≠ 0 := by
    intro hs
    apply hcChi
    rw [cChi, htrace, hs, zero_div, neg_zero]
  rw [x_eq, cChi, htrace]
  field_simp [C.denominator_ne_zero', Units.ne_zero C.n, hcChi, hs]

/-- The extra noncancellation needed to use both norm corrections as
arguments of multiplicative characters.  It is proved below for the actual
high and low stationary packages, rather than postulated for arbitrary
field representatives. -/
def OppositeNoncancellation : Prop :=
  (1 : F) - (C.n : F) ≠ 0

theorem n_ne_one (hopp : C.OppositeNoncancellation) :
    (C.n : F) ≠ 1 := by
  intro hn
  apply hopp
  rw [hn, sub_self]

/-- The actual opposite noncancellation excludes `u=-1`. -/
theorem one_add_u_ne_zero (hopp : C.OppositeNoncancellation) :
    (1 : K) + (C.u : K) ≠ 0 := by
  intro hzero
  have hu : (C.u : K) = -1 := eq_neg_of_add_eq_zero_right hzero
  apply C.n_ne_one hopp
  rw [← C.norm_u_field, hu,
    show (-1 : K) = algebraMap F K (-1 : F) by simp,
    norm_algebraMap, C.degree_eq_two]
  norm_num

/-- The same noncancellation excludes `u^vee=-1`. -/
theorem one_add_dual_ne_zero (hopp : C.OppositeNoncancellation) :
    (1 : K) + C.dual ≠ 0 := by
  intro hzero
  have hdual : C.dual = -1 := eq_neg_of_add_eq_zero_right hzero
  apply C.n_ne_one hopp
  rw [← C.norm_dual, hdual,
    show (-1 : K) = algebraMap F K (-1 : F) by simp,
    norm_algebraMap, C.degree_eq_two]
  norm_num

theorem z0_ne_zero (hopp : C.OppositeNoncancellation) : C.z0 ≠ 0 := by
  rw [z0]
  exact div_ne_zero
    (Algebra.norm_ne_zero_iff.mpr (C.one_add_dual_ne_zero hopp))
    C.denominator_ne_zero'

theorem z1_ne_zero (hopp : C.OppositeNoncancellation) : C.z1 ≠ 0 := by
  rw [z1]
  exact div_ne_zero
    (Algebra.norm_ne_zero_iff.mpr (C.one_add_u_ne_zero hopp))
    C.denominator_ne_zero'

/-- Formula-facing unit form of `z0`; the field value remains the selected,
choice-relative correction. -/
noncomputable def z0Unit (hopp : C.OppositeNoncancellation) : Fˣ :=
  Units.mk0 C.z0 (C.z0_ne_zero hopp)

/-- Formula-facing unit form of `z1`. -/
noncomputable def z1Unit (hopp : C.OppositeNoncancellation) : Fˣ :=
  Units.mk0 C.z1 (C.z1_ne_zero hopp)

@[simp]
theorem coe_z0Unit (hopp : C.OppositeNoncancellation) :
    (C.z0Unit hopp : F) = C.z0 := rfl

@[simp]
theorem coe_z1Unit (hopp : C.OppositeNoncancellation) :
    (C.z1Unit hopp : F) = C.z1 := rfl

end WildQuadraticCommonCorrectionData

/-! ## Extraction from the high and low simultaneous choices -/

section StationaryAdapters

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The low ratio uses exactly the three representatives supplied by `P`;
it does not choose a new element of `K`. -/
def lowWildQuadraticCommonU
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : Kˣ :=
  epsilon1 * P.beta₁ / P.alpha₁

/-- The corresponding exact low norm ratio
`n=epsilon*beta/alpha`. -/
def lowWildQuadraticCommonN
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : Fˣ :=
  lowEpsilon F K epsilon1 * P.beta / P.alpha

@[simp]
theorem lowWildQuadraticCommonU_coe
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    (lowWildQuadraticCommonU epsilon1 P : K) =
      lowNormalizedRatio F K epsilon1 P := by
  simp [lowWildQuadraticCommonU, lowNormalizedRatio,
    Units.val_div_eq_div_val]

/-- Exact low norm identity at unit level. -/
theorem lowWildQuadraticCommon_norm_u_eq_n
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    normUnits F K (lowWildQuadraticCommonU epsilon1 P) =
      lowWildQuadraticCommonN epsilon1 P := by
  apply Units.ext
  simpa [lowWildQuadraticCommonU, lowWildQuadraticCommonN,
    LowStationaryNormRepresentativePair.alpha,
    LowStationaryNormRepresentativePair.beta, lowEpsilon, coe_normUnits]

variable [PrimeCyclicExtension F K]

/-- The low denominator is nonzero.  Away from the boundary this follows
from its exact positive order.  At `m=T`, the proof uses the actual twist
stationary class at `j=1`; hence it uses minimal-orbit noncancellation without
turning either stationary quotient class into a canonical field element. -/
theorem lowWildQuadraticCommon_one_add_n_ne_zero
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
    (delta : Fˣ) (epsilon1 : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hepsilon1 : ord K (epsilon1 : K) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
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
        (lowGammaF F K delta epsilon1) hgammaF)) :
    (1 : F) + (lowWildQuadraticCommonN epsilon1 P : F) ≠ 0 := by
  have halpha : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  have hbeta : ord F (P.beta : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.beta, coe_normUnits] using
      P.betaRepresentative.norm_order
  have heta : ord F (lowEpsilon F K epsilon1 : F) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) :=
    lowEpsilon_order F K hres epsilon1 hepsilon1
  by_cases hcritical : chi.conductor = t + 1
  · have htpos : 0 < t := by omega
    have hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht htpos pi hpi hgen
    letI : Fact (Module.finrank F K).Prime :=
      ⟨PrimeCyclicExtension.degree_prime F K⟩
    have hj : (1 : ZMod (Module.finrank F K)) ≠ 0 := one_ne_zero
    obtain ⟨haff, hclass⟩ := lowNonzeroTwistClass_ofPair
      F K ht hres pi hpi hgen chi psi hminimal hF hLow delta epsilon1
        hdelta hepsilon1 (1 : ZMod (Module.finrank F K)) hj hchar hT
        hgammaF P
    have homegaROI :
        primeTeichmuller F (Module.finrank F K) hchar
          (1 : ZMod (Module.finrank F K)) = 1 := map_one _
    have homega :
        ((primeTeichmuller F (Module.finrank F K) hchar
          (1 : ZMod (Module.finrank F K)) : ringOfIntegers F) : F) = 1 :=
      congrArg (fun z : ringOfIntegers F ↦ (z : F)) homegaROI
    rw [homega, one_mul] at haff
    have hsumClass : latticeQuotientMk F (by omega)
          ⟨(P.alpha : F) +
              (lowEpsilon F K epsilon1 : F) * (P.beta : F),
            by simpa using haff⟩ =
        stationaryCoefficientClass F
          (lowNonzeroTwistDatum F K ht hres pi hpi hgen
            chi hminimal hLow (1 : ZMod (Module.finrank F K)) hj)
          psi (lowCriticalConductorDecomposition (t := t) hT)
            delta hdelta := by
      simpa only [homega, one_mul] using hclass
    have hsumOrd : ord F
        ((P.alpha : F) +
          (lowEpsilon F K epsilon1 : F) * (P.beta : F)) =
          (0 : WithTop ℤ) := by
      exact stationaryCoefficientClass_representative_ord_zero F K F
        (lowNonzeroTwistDatum F K ht hres pi hpi hgen
          chi hminimal hLow (1 : ZMod (Module.finrank F K)) hj)
        psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta
        ⟨(P.alpha : F) +
            (lowEpsilon F K epsilon1 : F) * (P.beta : F),
          by simpa using haff⟩ hsumClass
    have hsumNe :
        (P.alpha : F) +
          (lowEpsilon F K epsilon1 : F) * (P.beta : F) ≠ 0 :=
      (ord_ne_top_iff F).1 (hsumOrd.trans_ne WithTop.coe_ne_top)
    have hfactor :
        (P.alpha : F) *
            ((1 : F) + (lowWildQuadraticCommonN epsilon1 P : F)) =
          (P.alpha : F) +
            (lowEpsilon F K epsilon1 : F) * (P.beta : F) := by
      simp only [lowWildQuadraticCommonN, Units.val_div_eq_div_val,
        Units.val_mul]
      field_simp [Units.ne_zero P.alpha]
    intro hzero
    apply hsumNe
    rw [← hfactor, hzero, mul_zero]
  · have hstrict : chi.conductor < t + 1 :=
      lt_of_le_of_ne hLow hcritical
    have hnord : ord F (lowWildQuadraticCommonN epsilon1 P : F) =
        (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) := by
      rw [lowWildQuadraticCommonN, Units.val_div_eq_div_val, Units.val_mul,
        ord_div, ord_mul, heta, hbeta, halpha]
      simp
    intro hzero
    have hn : (lowWildQuadraticCommonN epsilon1 P : F) = -1 := by
      linear_combination hzero
    rw [hn, ord_neg, ord_one] at hnord
    have hpos : 0 < t + 1 - chi.conductor := Nat.sub_pos_of_lt hstrict
    have hne :
        (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact hne hnord.symm

/-- Extraction of the common correction from one explicit low simultaneous
representative pair.  The pair `P` and `epsilon1` remain visible arguments. -/
noncomputable def lowWildQuadraticCommonCorrection
    {t d epsilon : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hLow : chi.conductor ≤ t + 1)
    (delta : Fˣ) (epsilon1 : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hepsilon1 : ord K (epsilon1 : K) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
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
        (lowGammaF F K delta epsilon1) hgammaF)) :
    WildQuadraticCommonCorrectionData F K (t + 1) chi.conductor := by
  have hsource : ord K (lowWildQuadraticCommonU epsilon1 P : K) =
      (((((t + 1 : ℕ) : ℤ) - (chi.conductor : ℤ) : ℤ)) : WithTop ℤ) := by
    have hord := lowNormalizedRatio_order F K epsilon1 hepsilon1 P
    have hdepth : ((t + 1 - chi.conductor : ℕ) : ℤ) =
        ((t + 1 : ℕ) : ℤ) - (chi.conductor : ℤ) :=
      Int.ofNat_sub hLow
    have hordU : ord K (lowWildQuadraticCommonU epsilon1 P : K) =
        ((t + 1 - chi.conductor : ℕ) : WithTop ℤ) := by
      simpa only [lowWildQuadraticCommonU, lowNormalizedRatio,
        Units.val_mul, Units.val_div_eq_div_val] using hord
    have hnatCoe : ((t + 1 - chi.conductor : ℕ) : WithTop ℤ) =
        (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) := by
      norm_num
    exact hordU.trans (hnatCoe.trans
      (congrArg (fun z : ℤ ↦ (z : WithTop ℤ)) hdepth))
  have hnorm := lowWildQuadraticCommon_norm_u_eq_n epsilon1 P
  have htarget : ord F (lowWildQuadraticCommonN epsilon1 P : F) =
      (((((t + 1 : ℕ) : ℤ) - (chi.conductor : ℤ) : ℤ)) : WithTop ℤ) := by
    have hnormField := congrArg Units.val hnorm
    change norm F K (lowWildQuadraticCommonU epsilon1 P : K) =
      (lowWildQuadraticCommonN epsilon1 P : F) at hnormField
    rw [← hnormField, ord_norm, hres, one_nsmul]
    exact hsource
  exact
    { u := lowWildQuadraticCommonU epsilon1 P
      n := lowWildQuadraticCommonN epsilon1 P
      degree_eq_two := hdegree
      residueDegree_eq_one := hres
      differentExponent_eq :=
        differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen
      source_order := hsource
      target_order := htarget
      norm_u := hnorm
      denominator_ne_zero :=
        lowWildQuadraticCommon_one_add_n_ne_zero ht hres pi hpi hgen
          chi psi hminimal hF hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF P }

/-- The actual low stationary package excludes `n=1`.  At the boundary the
proof uses the selected `j=1` quotient representative and characteristic
two; away from the boundary it uses the exact positive order of `n`. -/
theorem lowWildQuadraticCommonCorrection_oppositeNoncancellation
    {t d epsilon : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hLow : chi.conductor ≤ t + 1)
    (delta : Fˣ) (epsilon1 : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hepsilon1 : ord K (epsilon1 : K) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
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
        (lowGammaF F K delta epsilon1) hgammaF)) :
    WildQuadraticCommonCorrectionData.OppositeNoncancellation
      (lowWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree
        chi psi hminimal hF hLow delta epsilon1 hdelta hepsilon1 hT
          hgammaF P) := by
  change (1 : F) - (lowWildQuadraticCommonN epsilon1 P : F) ≠ 0
  have halpha : ord F (P.alpha : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.alpha, coe_normUnits] using
      P.alphaRepresentative.norm_order
  have hbeta : ord F (P.beta : F) = (0 : WithTop ℤ) := by
    simpa [LowStationaryNormRepresentativePair.beta, coe_normUnits] using
      P.betaRepresentative.norm_order
  have heta : ord F (lowEpsilon F K epsilon1 : F) =
      (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) :=
    lowEpsilon_order F K hres epsilon1 hepsilon1
  by_cases hcritical : chi.conductor = t + 1
  · have htpos : 0 < t := by omega
    have hcharDegree : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht htpos pi hpi hgen
    have hchar : residueCharacteristic F = 2 := hcharDegree.trans hdegree
    letI : Fact (Module.finrank F K).Prime :=
      ⟨PrimeCyclicExtension.degree_prime F K⟩
    have hj : (1 : ZMod (Module.finrank F K)) ≠ 0 := one_ne_zero
    obtain ⟨haff, hclass⟩ := lowNonzeroTwistClass_ofPair
      F K ht hres pi hpi hgen chi psi hminimal hF hLow delta epsilon1
        hdelta hepsilon1 (1 : ZMod (Module.finrank F K)) hj hcharDegree hT
        hgammaF P
    have homegaROI :
        primeTeichmuller F (Module.finrank F K) hcharDegree
          (1 : ZMod (Module.finrank F K)) = 1 := map_one _
    have homega :
        ((primeTeichmuller F (Module.finrank F K) hcharDegree
          (1 : ZMod (Module.finrank F K)) : ringOfIntegers F) : F) = 1 :=
      congrArg (fun z : ringOfIntegers F ↦ (z : F)) homegaROI
    rw [homega, one_mul] at haff
    have hsumClass : latticeQuotientMk F (by omega)
          ⟨(P.alpha : F) +
              (lowEpsilon F K epsilon1 : F) * (P.beta : F),
            by simpa using haff⟩ =
        stationaryCoefficientClass F
          (lowNonzeroTwistDatum F K ht hres pi hpi hgen
            chi hminimal hLow (1 : ZMod (Module.finrank F K)) hj)
          psi (lowCriticalConductorDecomposition (t := t) hT)
            delta hdelta := by
      simpa only [homega, one_mul] using hclass
    have hsumOrd : ord F
        ((P.alpha : F) +
          (lowEpsilon F K epsilon1 : F) * (P.beta : F)) =
          (0 : WithTop ℤ) := by
      exact stationaryCoefficientClass_representative_ord_zero F K F
        (lowNonzeroTwistDatum F K ht hres pi hpi hgen
          chi hminimal hLow (1 : ZMod (Module.finrank F K)) hj)
        psi (lowCriticalConductorDecomposition (t := t) hT) delta hdelta
        ⟨(P.alpha : F) +
            (lowEpsilon F K epsilon1 : F) * (P.beta : F),
          by simpa using haff⟩ hsumClass
    have hsumNotMem :
        (P.alpha : F) +
            (lowEpsilon F K epsilon1 : F) * (P.beta : F) ∉
          lattice F 1 := by
      rw [mem_lattice, hsumOrd]
      simp
    have halphaMem : (P.alpha : F) ∈ lattice F 0 := by
      rw [mem_lattice, halpha]
      simp
    have htwo : (2 : F) ∈ lattice F 1 :=
      residueCharacteristic_two_mem_lattice_one F hchar
    have hfactor :
        (P.alpha : F) *
            ((1 : F) + (lowWildQuadraticCommonN epsilon1 P : F)) =
          (P.alpha : F) +
            (lowEpsilon F K epsilon1 : F) * (P.beta : F) := by
      simp only [lowWildQuadraticCommonN, Units.val_div_eq_div_val,
        Units.val_mul]
      field_simp [Units.ne_zero P.alpha]
    intro hzero
    have hn : (lowWildQuadraticCommonN epsilon1 P : F) = 1 :=
      (sub_eq_zero.mp hzero).symm
    apply hsumNotMem
    rw [← hfactor, hn]
    have hmul := mul_mem_lattice F halphaMem htwo
    simpa only [zero_add, one_add_one_eq_two] using hmul
  · have hstrict : chi.conductor < t + 1 :=
      lt_of_le_of_ne hLow hcritical
    have hnord : ord F (lowWildQuadraticCommonN epsilon1 P : F) =
        (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) := by
      rw [lowWildQuadraticCommonN, Units.val_div_eq_div_val, Units.val_mul,
        ord_div, ord_mul, heta, hbeta, halpha]
      simp
    intro hzero
    have hn : (lowWildQuadraticCommonN epsilon1 P : F) = 1 :=
      (sub_eq_zero.mp hzero).symm
    rw [hn, ord_one] at hnord
    have hpos : 0 < t + 1 - chi.conductor := Nat.sub_pos_of_lt hstrict
    have hne :
        (((t + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact hne hnord.symm

/-- Extraction of the same correction record from the complete high
parameter package.  The package `D`, and therefore its simultaneous
representatives `beta`, `beta1`, `delta`, and `alpha1`, remains an explicit
argument. -/
noncomputable def highWildQuadraticCommonCorrection
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (D : WildQuadraticHighParameterData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) :
    WildQuadraticCommonCorrectionData F K (t + 1) chiF.conductor where
  u := D.representatives.u
  n := D.representatives.n
  degree_eq_two := hdegree
  residueDegree_eq_one := hres
  differentExponent_eq :=
    differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen
  source_order := D.representatives.u_order
  target_order := D.representatives.n_order
  norm_u := D.representatives.norm_u_eq_n
  denominator_ne_zero := D.denominator_ne_zero

/-- The high normalization visibly retains the essential break-level unit
correction `delta`; it is not simplified to `1`. -/
theorem highWildQuadraticCommonCorrection_n_with_delta
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (D : WildQuadraticHighParameterData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) :
    (highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree htpos
      chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
        gammaF hgammaF D).n =
      D.representatives.beta /
        (D.representatives.alpha *
          (D.representatives.delta : Fˣ)) := by
  rfl

/-- Exact high scalar factorization with `delta` retained. -/
theorem highWildQuadraticCommonCorrection_delta_factorization
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (D : WildQuadraticHighParameterData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) :
    (D.representatives.alpha *
        (D.representatives.delta : Fˣ)) *
      (highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree htpos
        chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
          gammaF hgammaF D).n = D.representatives.beta := by
  exact D.representatives.cF_mul_n

/-- The norm of the high correction term contains the same indispensable
unit correction. -/
theorem highWildQuadraticCommonCorrection_exact_norm
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (D : WildQuadraticHighParameterData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) :
    norm F K D.representatives.correction =
      (D.representatives.beta : F) *
        ((D.representatives.alpha : F) *
          ((D.representatives.delta : Fˣ) : F)) := by
  simpa only [WildQuadraticHighRepresentatives.cF, Units.val_mul] using
    D.correction_norm

/-- The actual high stationary package also excludes `n=1`.  At the
boundary this is exactly the supplied noncancellation class, together with
residue characteristic two; away from it the exact negative order of `n`
suffices. -/
theorem highWildQuadraticCommonCorrection_oppositeNoncancellation
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (D : WildQuadraticHighParameterData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) :
    WildQuadraticCommonCorrectionData.OppositeNoncancellation
      (highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree htpos
        chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
          gammaF hgammaF D) := by
  let R := D.representatives
  change (1 : F) - (R.n : F) ≠ 0
  by_cases hcritical : chiF.conductor = t + 1
  · intro hzero
    have hn : (R.n : F) = 1 := (sub_eq_zero.mp hzero).symm
    apply D.boundary_noncancellation hcritical
    have hcF : (R.cF : F) ∈ lattice F 0 := by
      rw [mem_lattice, R.cF_order, hcritical]
      simp
    have htwo : (2 : F) ∈ lattice F 1 :=
      residueCharacteristic_two_mem_lattice_one
        F D.residueCharacteristic_downstairs
    have hmul := mul_mem_lattice F hcF htwo
    rw [R.betaTwist_eq_cF_mul_add_one, hn]
    simpa only [zero_add, one_add_one_eq_two] using hmul
  · intro hzero
    have hn : (R.n : F) = 1 := (sub_eq_zero.mp hzero).symm
    have hord := R.n_order
    rw [hn, ord_one] at hord
    have hstrict : t + 1 < chiF.conductor :=
      lt_of_le_of_ne hhigh (Ne.symm hcritical)
    have hneg :
        ((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) < 0 := by omega
    have hcoeNeg :
        ((((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) :
          WithTop ℤ) < 0 := by
      exact_mod_cast hneg
    rw [← hord] at hcoeNeg
    exact (lt_irrefl (0 : WithTop ℤ)) hcoeNeg

/-- Exactly the low representative ambiguity inherited by the common ratio.
The target representatives are compared only in their original quotient
classes, the two source representatives only in the justified filtrations,
and the displayed consequence for `u` is only at the minimum precision. -/
structure LowWildQuadraticCommonCorrectionAmbiguity
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon1 : Kˣ)
    (P Q : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) : Prop where
  permitted : LowStationaryNormRepresentativePairIndependence F K P Q
  u_ratio : lowWildQuadraticCommonU epsilon1 P /
      lowWildQuadraticCommonU epsilon1 Q ∈
    unitFiltration K (min r d)

/-- Independence of the low construction, and no more: this packages the
comparison supplied by `Parameters.Low` and derives the ratio precision for
`u`; it does not assert equality of any selected representative. -/
theorem lowWildQuadraticCommonCorrection_ambiguity
    {t r d : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hr : r ≤ t) (hd : d ≤ t)
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (epsilon1 : Kˣ)
    (P Q : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    LowWildQuadraticCommonCorrectionAmbiguity epsilon1 P Q := by
  let I := lowStationaryNormRepresentativePairs_independent
    F K ht hres pi hpi hgen hr hd P Q
  have ha : P.alpha₁ / Q.alpha₁ ∈ unitFiltration K (min r d) :=
    unitFiltration_antitone K (Nat.min_le_left r d) I.alphaSource_ratio
  have hb : P.beta₁ / Q.beta₁ ∈ unitFiltration K (min r d) :=
    unitFiltration_antitone K (Nat.min_le_right r d) I.betaSource_ratio
  have hu := mul_mem (s := unitFiltration K (min r d)) hb (inv_mem ha)
  refine ⟨I, ?_⟩
  have hratio :
      lowWildQuadraticCommonU epsilon1 P /
          lowWildQuadraticCommonU epsilon1 Q =
        (P.beta₁ / Q.beta₁) * (P.alpha₁ / Q.alpha₁)⁻¹ := by
    apply Units.ext
    simp only [lowWildQuadraticCommonU, Units.val_div_eq_div_val,
      Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero epsilon1, Units.ne_zero P.alpha₁,
      Units.ne_zero P.beta₁, Units.ne_zero Q.alpha₁,
      Units.ne_zero Q.beta₁]
  rw [hratio]
  exact hu

end StationaryAdapters

/-! ## Choice ambiguity in the high package -/

section HighChoiceAmbiguity

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

variable {t : ℕ}
  (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
  (hhigh : t + 1 ≤ chiF.conductor)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (tau : NormCharacter F K) (htau : tau ≠ 1)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

variable
  (D E : WildQuadraticHighParameterData
    F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
    hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF)

/-- Every comparison licensed by the high parameter package, at its native
quotient precision.  In particular this structure contains no literal
equality of `u`, `n`, corrections, or field representatives. -/
structure HighWildQuadraticCommonCorrectionAmbiguity : Prop where
  beta_class :
    latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(D.representatives.beta : F),
          D.representatives.beta_integral⟩ : lattice F 0) =
      latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(E.representatives.beta : F),
          E.representatives.beta_integral⟩ : lattice F 0)
  tau_class :
    let hr := wildQuadraticHigh_stationaryDepth htpos
    let cD : lattice F
        ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
      ⟨(D.representatives.cF : F), by
        simpa only [WildQuadraticHighRepresentatives.cF,
          WildQuadraticHighRepresentatives.alpha, Units.val_mul,
          coe_normUnits, mul_comm] using D.representatives.tau_integral⟩
    let cE : lattice F
        ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
      ⟨(E.representatives.cF : F), by
        simpa only [WildQuadraticHighRepresentatives.cF,
          WildQuadraticHighRepresentatives.alpha, Units.val_mul,
          coe_normUnits, mul_comm] using E.representatives.tau_integral⟩
    latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cD =
      latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cE
  twist_class :
    latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨D.representatives.betaTwist,
          D.representatives.betaTwist_integral⟩ : lattice F 0) =
      latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨E.representatives.betaTwist,
          E.representatives.betaTwist_integral⟩ : lattice F 0)
  upstairs_class :
    latticeQuotientMk K (show (0 : ℤ) ≤ (dK : ℤ) by omega)
        (⟨D.representatives.betaK,
          D.representatives.betaK_integral hdegree⟩ : lattice K 0) =
      latticeQuotientMk K (show (0 : ℤ) ≤ (dK : ℤ) by omega)
        (⟨E.representatives.betaK,
          E.representatives.betaK_integral hdegree⟩ : lattice K 0)
  norm_product_class :
    latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨norm F K D.representatives.betaK,
          D.representatives.norm_betaK_integral hdegree⟩ : lattice F 0) =
      latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨norm F K E.representatives.betaK,
          E.representatives.norm_betaK_integral hdegree⟩ : lattice F 0)

/-- High choice-independence is exactly the five quotient comparisons already
licensed by `Parameters.HighQuadratic`; nothing is promoted to field
equality. -/
theorem highWildQuadraticCommonCorrection_ambiguity :
    HighWildQuadraticCommonCorrectionAmbiguity ht hres pi hpi hgen hdegree
      htpos chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau
        gammaF hgammaF D E := by
  let R := D.representatives
  let Q := E.representatives
  have hbeta : latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(R.beta : F), R.beta_integral⟩ : lattice F 0) =
      latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(Q.beta : F), Q.beta_integral⟩ : lattice F 0) :=
    R.beta_class.trans Q.beta_class.symm
  let hr := wildQuadraticHigh_stationaryDepth htpos
  let cR : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
    ⟨(R.cF : F), by
      simpa only [WildQuadraticHighRepresentatives.cF,
        WildQuadraticHighRepresentatives.alpha, Units.val_mul,
        coe_normUnits, mul_comm] using R.tau_integral⟩
  let cQ : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
    ⟨(Q.cF : F), by
      simpa only [WildQuadraticHighRepresentatives.cF,
        WildQuadraticHighRepresentatives.alpha, Units.val_mul,
        coe_normUnits, mul_comm] using Q.tau_integral⟩
  have htauClass : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cR =
      latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cQ := by
    simpa only [cR, cQ, WildQuadraticHighRepresentatives.cF,
      WildQuadraticHighRepresentatives.alpha, Units.val_mul,
      coe_normUnits, mul_comm] using R.tau_class.trans Q.tau_class.symm
  have htwist := (R.twist_class hminimal).trans
    (Q.twist_class hminimal).symm
  have hupstairs :=
    (R.upstairs_class hdegree chiK psiK hK hminimal hchi hpsi).trans
      (Q.upstairs_class hdegree chiK psiK hK hminimal hchi hpsi).symm
  have hbetaDiff := (latticeQuotientMk_eq_mk_iff F
    (show (0 : ℤ) ≤ (d : ℤ) by omega)).1 hbeta
  have htwistDiff := (latticeQuotientMk_eq_mk_iff F
    (show (0 : ℤ) ≤ (d : ℤ) by omega)).1 htwist
  have hprodDiff :
      (R.beta : F) * R.betaTwist - (Q.beta : F) * Q.betaTwist ∈
        lattice F (d : ℤ) := by
    have h1 := mul_mem_lattice F R.beta_integral htwistDiff
    have h2 := mul_mem_lattice F hbetaDiff Q.betaTwist_integral
    have h1' : (R.beta : F) * (R.betaTwist - Q.betaTwist) ∈
        lattice F (d : ℤ) := by simpa using h1
    have h2' : ((R.beta : F) - (Q.beta : F)) * Q.betaTwist ∈
        lattice F (d : ℤ) := by simpa using h2
    have hsum := add_mem_lattice F h1' h2'
    convert hsum using 1 <;> ring
  have hprod : latticeQuotientMk F
        (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(R.beta : F) * R.betaTwist,
          R.beta_mul_betaTwist_integral⟩ : lattice F 0) =
      latticeQuotientMk F
        (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(Q.beta : F) * Q.betaTwist,
          Q.beta_mul_betaTwist_integral⟩ : lattice F 0) := by
    exact (latticeQuotientMk_eq_mk_iff F (by omega)).2 hprodDiff
  have hnorm := (R.norm_betaK_class hdegree).trans
    (hprod.trans (Q.norm_betaK_class hdegree).symm)
  refine ⟨hbeta, ?_, htwist, hupstairs, hnorm⟩
  simpa only [R, Q, hr, cR, cQ] using htauClass

end HighChoiceAmbiguity

/-! ## The exact odd-depth graded trace -/

section GradedTrace

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- The manuscript's strict odd equivalence at the literal source depth
`m-T` and target depth `d`, where `m=2d+1>T`. -/
noncomputable def wildQuadraticHighOddGradedTraceEquiv
    {T m d : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hm : m = 2 * d + 1) (hstrict : T < m) :
    LatticeGradedPiece K ((m : ℤ) - (T : ℤ)) ≃ₗ[ringOfIntegers F]
      LatticeGradedPiece F (d : ℤ) := by
  have hD : (differentExponent F K : ℤ) = (T : ℤ) := by
    exact_mod_cast C.differentExponent_eq
  have hmZ : (m : ℤ) = 2 * (d : ℤ) + 1 := by exact_mod_cast hm
  have hstrictZ : (T : ℤ) < (m : ℤ) := by exact_mod_cast hstrict
  exact quadraticOddConductorGradedTraceEquiv F K pi hpi hgen
    C.ramificationIndex_eq_two C.degree_eq_two
      (T := (T : ℤ)) (m := (m : ℤ)) (d := (d : ℤ))
      (r := (m : ℤ) - (T : ℤ)) hD hmZ rfl hstrictZ

/-- The negative trace of the selected reciprocal lies in the exact target
shell, not merely in the target lattice. -/
theorem wildQuadraticHighOdd_cChi_order
    {T m d : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hm : m = 2 * d + 1) (hstrict : T < m) :
    ord F C.cChi = ((d : ℤ) : WithTop ℤ) := by
  have hD : (differentExponent F K : ℤ) = (T : ℤ) := by
    exact_mod_cast C.differentExponent_eq
  have hmZ : (m : ℤ) = 2 * (d : ℤ) + 1 := by exact_mod_cast hm
  have hstrictZ : (T : ℤ) < (m : ℤ) := by exact_mod_cast hstrict
  have hshell := quadratic_odd_conductor_neg_trace_shell_iff
    F K pi hpi hgen C.ramificationIndex_eq_two C.degree_eq_two
      (T := (T : ℤ)) (m := (m : ℤ)) (d := (d : ℤ))
      (r := (m : ℤ) - (T : ℤ)) hD hmZ rfl hstrictZ
        C.reciprocal C.reciprocal_mem
  rw [WildQuadraticCommonCorrectionData.cChi]
  exact hshell.2 C.reciprocal_order

/-- At the precise strict odd depth, the quadratic graded-trace equivalence
sends the quotient class of the selected `-u⁻¹` to the quotient class of
`c_chi=-Tr(u⁻¹)`.  This is a quotient equality, not a field equality between
chosen representatives. -/
theorem wildQuadraticHighOdd_gradedTrace_class
    {T m d : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hm : m = 2 * d + 1) (hstrict : T < m) :
    wildQuadraticHighOddGradedTraceEquiv F K pi hpi hgen C hm hstrict
        (latticeQuotientMk K
          (show (m : ℤ) - (T : ℤ) ≤ (m : ℤ) - (T : ℤ) + 1 by omega)
          ⟨-C.reciprocal, neg_mem_lattice K C.reciprocal_mem⟩) =
      latticeQuotientMk F
        (show (d : ℤ) ≤ (d : ℤ) + 1 by omega)
        ⟨C.cChi, by
          rw [mem_lattice,
            wildQuadraticHighOdd_cChi_order F K pi hpi hgen C hm hstrict]⟩ := by
  have hD : (differentExponent F K : ℤ) = (T : ℤ) := by
    exact_mod_cast C.differentExponent_eq
  change quadraticGradedTraceEquiv F K pi hpi hgen (by omega)
      C.ramificationIndex_eq_two C.degree_eq_two (by omega)
      (latticeQuotientMk K
        (show (m : ℤ) - (T : ℤ) ≤ (m : ℤ) - (T : ℤ) + 1 by omega)
        ⟨-C.reciprocal, neg_mem_lattice K C.reciprocal_mem⟩) = _
  rw [quadraticGradedTraceEquiv]
  change quadraticGradedTrace F K pi hpi hgen C.ramificationIndex_eq_two
      (by omega)
      (latticeQuotientMk K
        (show (m : ℤ) - (T : ℤ) ≤ (m : ℤ) - (T : ℤ) + 1 by omega)
        ⟨-C.reciprocal, neg_mem_lattice K C.reciprocal_mem⟩) = _
  rw [quadraticGradedTrace_mk]
  apply congrArg (latticeQuotientMk F
    (show (d : ℤ) ≤ (d : ℤ) + 1 by omega))
  apply Subtype.ext
  exact map_neg (trace F K) C.reciprocal

/-- Formula-facing strict-high identity.  Nonvanishing of `c_chi` is derived
from its exact target depth, and the denominator direction is `n/(1+n)`. -/
theorem wildQuadraticHighOdd_x_div_cChi_eq
    {T m d : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hm : m = 2 * d + 1) (hstrict : T < m) :
    C.x / C.cChi = (C.n : F) / C.denominator := by
  apply C.x_div_cChi_eq
  apply (ord_ne_top_iff F).1
  rw [wildQuadraticHighOdd_cChi_order F K pi hpi hgen C hm hstrict]
  simp

end GradedTrace

/-! ## The odd boundary class -/

section BoundaryTrace

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- At `m=T`, bundle the already selected `u` as an integral unit.  This
does not select a new field representative. -/
noncomputable def wildQuadraticBoundaryRingUnit
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (hboundary : m = T) : (ringOfIntegers K)ˣ := by
  let u0 : unitGroup K :=
    ⟨C.u, (mem_unitGroup_iff_ord_eq_zero K C.u).2 (by
      rw [C.source_order, hboundary]
      simp)⟩
  exact unitGroupMulEquivRingOfIntegers K u0

@[simp]
theorem coe_wildQuadraticBoundaryRingUnit
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (hboundary : m = T) :
    (((wildQuadraticBoundaryRingUnit F K C hboundary :
      (ringOfIntegers K)ˣ) : ringOfIntegers K) : K) = (C.u : K) :=
  rfl

/-- Odd-boundary trace congruence with the lower residue lift retained as an
explicit argument.  Its modulus is exactly `p_F^(dTau+1)`. -/
theorem wildQuadraticBoundary_trace_congr
    {T m : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hboundary : m = T)
    {dTau : ℤ} (hodd : (T : ℤ) = 2 * dTau + 1)
    (wtilde : ringOfIntegers F)
    (hresidue :
      residueMap K
          (wildQuadraticBoundaryRingUnit F K C hboundary :
            ringOfIntegers K) =
        extensionResidueMap F K (residueMap F wtilde)) :
    C.s - (2 : F) * (wtilde : F) ∈ lattice F (dTau + 1) := by
  have hoddDifferent :
      (differentExponent F K : ℤ) = 2 * dTau + 1 := by
    rw [C.differentExponent_eq]
    exact hodd
  have h := quadratic_unit_trace_congr F K pi hpi hgen
    C.ramificationIndex_eq_two C.degree_eq_two hoddDifferent
    (wildQuadraticBoundaryRingUnit F K C hboundary : ringOfIntegers K)
    (wildQuadraticBoundaryRingUnit F K C hboundary).isUnit
    wtilde hresidue
  simpa only [WildQuadraticCommonCorrectionData.s,
    coe_wildQuadraticBoundaryRingUnit] using h

/-- At an odd boundary, graded trace carries the selected source class at
depth `0` to the class of `2*wtilde` at depth `dTau`.  This is precisely an
equality in the lattice quotient; `wtilde` remains choice-relative. -/
theorem wildQuadraticBoundary_gradedTrace_class
    {T m : ℕ}
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (C : WildQuadraticCommonCorrectionData F K T m)
    (hboundary : m = T)
    {dTau : ℤ} (hodd : (T : ℤ) = 2 * dTau + 1)
    (wtilde : ringOfIntegers F)
    (hresidue :
      residueMap K
          (wildQuadraticBoundaryRingUnit F K C hboundary :
            ringOfIntegers K) =
        extensionResidueMap F K (residueMap F wtilde)) :
    let hu : (C.u : K) ∈ lattice K 0 := by
      rw [mem_lattice, C.source_order, hboundary]
      simp
    let htwo : (2 : F) * (wtilde : F) ∈ lattice F dTau := by
      have hoddDifferent :
          (differentExponent F K : ℤ) = 2 * dTau + 1 := by
        rw [C.differentExponent_eq]
        exact hodd
      have htwoOrd := quadratic_ord_two F K pi hpi hgen
        C.ramificationIndex_eq_two C.degree_eq_two hoddDifferent
      have htwoMem : (2 : F) ∈ lattice F dTau := by
        rw [mem_lattice, htwoOrd]
      have hw : (wtilde : F) ∈ lattice F 0 :=
        (mem_lattice_zero_iff F).2 wtilde.property
      simpa only [add_zero] using mul_mem_lattice F htwoMem hw
    quadraticGradedTraceEquiv F K pi hpi hgen
        (show (0 : ℤ) ≤ 0 by omega)
        C.ramificationIndex_eq_two C.degree_eq_two (by
          rw [C.differentExponent_eq]
          omega)
        (latticeQuotientMk K (show (0 : ℤ) ≤ 0 + 1 by omega)
          (⟨(C.u : K), hu⟩ : lattice K 0)) =
      latticeQuotientMk F (show dTau ≤ dTau + 1 by omega)
        (⟨(2 : F) * (wtilde : F), htwo⟩ : lattice F dTau) := by
  dsimp only
  change quadraticGradedTrace F K pi hpi hgen C.ramificationIndex_eq_two
      (by
        rw [C.differentExponent_eq]
        omega)
      (latticeQuotientMk K (show (0 : ℤ) ≤ 0 + 1 by omega)
        (⟨(C.u : K), by
          rw [mem_lattice, C.source_order, hboundary]
          simp⟩ : lattice K 0)) = _
  rw [quadraticGradedTrace_mk]
  apply (latticeQuotientMk_eq_mk_iff F
    (show dTau ≤ dTau + 1 by omega)).2
  exact wildQuadraticBoundary_trace_congr F K pi hpi hgen C hboundary
    hodd wtilde hresidue

end BoundaryTrace

/-! ## Principal exact correction theorem -/

section PrincipalTheorem

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  {T m : ℕ}

/-- Principal API for the common correction.  It records the exact norm
identity, both signed quadratic norm expansions, and every equation of
Lemma `lem:quad-X`, all for the same selected pair `u,n`. -/
theorem wildQuadratic_commonCorrection
    (C : WildQuadraticCommonCorrectionData F K T m) :
    norm F K (C.u : K) = (C.n : F) ∧
    norm F K C.dual = (C.n : F) ∧
    norm F K (1 + (C.u : K)) = 1 + C.s + (C.n : F) ∧
    norm F K (1 + C.dual) = 1 - C.s + (C.n : F) ∧
    C.x = -C.s / C.denominator ∧
    C.y = C.s / C.denominator ∧
    C.X = 2 * C.s / C.denominator := by
  exact ⟨C.norm_u_field, C.norm_dual, C.norm_one_add_u,
    C.norm_one_add_dual, C.x_eq, C.y_eq, C.X_eq⟩

end PrincipalTheorem

end

end LanglandsFirstMainLemma
