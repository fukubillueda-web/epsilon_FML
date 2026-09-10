import LanglandsFirstMainLemma.Cases.WildEndpoints.One.CyclicWilson
import LanglandsFirstMainLemma.FiniteField.FrobeniusTrace

/-!
# Intrinsic graded critical polynomial at the wild endpoint
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

def wildEndpointIntrinsicLatticeZeroResidueAddHom : lattice E 0 →+ ResidueField E where
  toFun x := residueMap E ⟨(x : E), (mem_lattice_zero_iff E).1 x.property⟩
  map_zero' := by
    change residueMap E (0 : ringOfIntegers E) = 0
    exact map_zero (residueMap E)
  map_add' x y := by
    change residueMap E
        (⟨(x : E), (mem_lattice_zero_iff E).1 x.property⟩ +
          ⟨(y : E), (mem_lattice_zero_iff E).1 y.property⟩) =
      residueMap E ⟨(x : E), (mem_lattice_zero_iff E).1 x.property⟩ +
        residueMap E ⟨(y : E), (mem_lattice_zero_iff E).1 y.property⟩
    exact map_add (residueMap E) _ _

theorem wildEndpointIntrinsicLatticeZeroResidueAddHom_surjective :
    Function.Surjective (wildEndpointIntrinsicLatticeZeroResidueAddHom E) := by
  intro z
  obtain ⟨x, rfl⟩ := residueMap_surjective E z
  exact ⟨⟨(x : E), (mem_lattice_zero_iff E).2 x.property⟩, rfl⟩

theorem wildEndpointIntrinsicLatticeZeroResidueAddHom_ker :
    (wildEndpointIntrinsicLatticeZeroResidueAddHom E).ker =
      (latticeInside E (show (0 : ℤ) ≤ 1 by omega)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker]
  change residueMap E
      ⟨(x : E), (mem_lattice_zero_iff E).1 x.property⟩ = 0 ↔ _
  rw [residueMap_eq_zero_iff]
  change (x : E) ∈ lattice E 1 ↔ x ∈
    latticeInside E (show (0 : ℤ) ≤ 1 by omega)
  exact (mem_latticeInside E (show (0 : ℤ) ≤ 1 by omega)).symm

noncomputable def wildEndpointIntrinsicLatticeZeroResidueAddEquiv :
    LatticeGradedPiece E 0 ≃+ ResidueField E :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (wildEndpointIntrinsicLatticeZeroResidueAddHom_ker E).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (wildEndpointIntrinsicLatticeZeroResidueAddHom E)
      (wildEndpointIntrinsicLatticeZeroResidueAddHom_surjective E))

@[simp] theorem wildEndpointIntrinsicLatticeZeroResidueAddEquiv_mk (x : lattice E 0) :
    wildEndpointIntrinsicLatticeZeroResidueAddEquiv E
      (latticeQuotientMk E (show (0 : ℤ) ≤ 1 by omega) x) =
        residueMap E ⟨(x : E), (mem_lattice_zero_iff E).1 x.property⟩ := rfl

def wildEndpointIntrinsicLatticeGradedResiduePreAddHom
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (r : ℕ) : lattice E (r : ℤ) →+ ResidueField E where
  toFun x := residueMap E
    ⟨(x : E) / pi ^ r, (mem_lattice_zero_iff E).1 (by
      apply (div_mem_lattice_iff E (pi ^ r) (x : E) (r : ℤ) 0 (by
        rw [ord_pow, ord_uniformizer E hpi]
        norm_num)).2
      simpa using x.property)⟩
  map_zero' := by
    change residueMap E ⟨(0 : E) / pi ^ r, _⟩ = 0
    rw [show (⟨(0 : E) / pi ^ r, _⟩ : ringOfIntegers E) = 0 by
      apply Subtype.ext
      simp]
    exact map_zero (residueMap E)
  map_add' x y := by
    change residueMap E
        ⟨((x : E) + (y : E)) / pi ^ r, _⟩ =
      residueMap E ⟨(x : E) / pi ^ r, _⟩ +
        residueMap E ⟨(y : E) / pi ^ r, _⟩
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact add_div (x : E) (y : E) (pi ^ r)

theorem wildEndpointIntrinsicLatticeGradedResiduePreAddHom_surjective
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (r : ℕ) :
    Function.Surjective (wildEndpointIntrinsicLatticeGradedResiduePreAddHom E pi hpi r) := by
  intro z
  let x : lattice E (r : ℤ) :=
    ⟨((teichmuller E z : ringOfIntegers E) : E) * pi ^ r, by
      have hzero : ((teichmuller E z : ringOfIntegers E) : E) ∈ lattice E 0 :=
        (mem_lattice_zero_iff E).2 (teichmuller E z).property
      have hr : pi ^ r ∈ lattice E (r : ℤ) := by
        rw [mem_lattice, ord_pow, ord_uniformizer E hpi]
        norm_num
      simpa using mul_mem_lattice E hzero hr⟩
  refine ⟨x, ?_⟩
  change residueMap E ⟨(x : E) / pi ^ r, _⟩ = z
  have hp : pi ^ r ≠ 0 := pow_ne_zero _ hpi.ne_zero
  have hx : (x : E) / pi ^ r = (teichmuller E z : ringOfIntegers E) := by
    dsimp [x]
    field_simp
  rw [show (⟨(x : E) / pi ^ r, _⟩ : ringOfIntegers E) = teichmuller E z by
    apply Subtype.ext
    exact hx]
  exact residueMap_teichmuller E z

theorem wildEndpointIntrinsicLatticeGradedResiduePreAddHom_ker
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (r : ℕ) :
    (wildEndpointIntrinsicLatticeGradedResiduePreAddHom E pi hpi r).ker =
      (latticeInside E (show (r : ℤ) ≤ (r : ℤ) + 1 by omega)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker]
  change residueMap E ⟨(x : E) / pi ^ r, _⟩ = 0 ↔ _
  rw [residueMap_eq_zero_iff]
  change (x : E) / pi ^ r ∈ lattice E 1 ↔ x ∈
    latticeInside E (show (r : ℤ) ≤ (r : ℤ) + 1 by omega)
  rw [mem_latticeInside]
  exact div_mem_lattice_iff E (pi ^ r) (x : E) (r : ℤ) 1 (by
    rw [ord_pow, ord_uniformizer E hpi]
    norm_num)

noncomputable def wildEndpointIntrinsicLatticeGradedResidueAddEquiv
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (r : ℕ) : LatticeGradedPiece E (r : ℤ) ≃+ ResidueField E :=
  criticalNormLatticeGradedResidueAddEquiv E pi hpi r

noncomputable def wildEndpointIntrinsicLatticeGradedResidueAddHom
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (r : ℕ) : LatticeGradedPiece E (r : ℤ) →+ ResidueField E :=
  (wildEndpointIntrinsicLatticeGradedResidueAddEquiv E pi hpi r).toAddMonoidHom

@[simp] theorem wildEndpointIntrinsicLatticeGradedResidueAddHom_mk
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (r : ℕ) (x : lattice E (r : ℤ)) :
    wildEndpointIntrinsicLatticeGradedResidueAddHom E pi hpi r
        (latticeQuotientMk E (show (r : ℤ) ≤ (r : ℤ) + 1 by omega) x) =
      reduce E ((x : E) / pi ^ r) (by
        apply (div_mem_lattice_iff E (pi ^ r) (x : E) (r : ℤ) 0 (by
          rw [ord_pow, ord_uniformizer E hpi]
          norm_num)).2
        simpa using x.property) := by
  exact criticalNormLatticeGradedResidueAddEquiv_mk E pi hpi r x

noncomputable def wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (n : ℕ) : Additive (UnitGradedPiece E (n + 1)) ≃+ ResidueField E :=
  criticalNormPositiveUnitGradedResidueAddEquiv E (by omega) pi hpi

@[simp] theorem wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv_mk
    (pi : E) (hpi : (ValuativeRel.valuation E).IsUniformizer pi)
    (n : ℕ) (u : unitFiltration E (n + 1)) :
    wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv E pi hpi n
        (Additive.ofMul (unitGradedMk E (n + 1) u)) =
      reduce E ((((u : Eˣ) : E) - 1) / pi ^ (n + 1)) (by
        apply (div_mem_lattice_iff E (pi ^ (n + 1))
          (((u : Eˣ) : E) - 1) (n + 1 : ℤ) 0 (by
            rw [ord_pow, ord_uniformizer E hpi]
            norm_num)).2
        simpa using (unitFiltrationDisplacement E n u).property) := by
  exact criticalNormPositiveUnitGradedResidueAddEquiv_mk E (by omega) pi hpi u

end

noncomputable section

open scoped BigOperators

section RootCritical

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

def wildEndpointIntrinsicEndpointResidueEquiv : ResidueField F ≃+* ResidueField K := by
  exact criticalNormResidueEquiv F K hres

def wildEndpointIntrinsicCriticalLowerUniformizer : F :=
  criticalNormLowerUniformizer F K piK

include hres hpiK in
theorem wildEndpointIntrinsicCriticalLowerUniformizer_isUniformizer :
    (ValuativeRel.valuation F).IsUniformizer
      (wildEndpointIntrinsicCriticalLowerUniformizer F K piK) := by
  exact criticalNormLowerUniformizer_isUniformizer F K hres piK hpiK

def wildEndpointIntrinsicCriticalSourceDisplacement (z : ResidueField F) :
    lattice K ((s + 1 : ℕ) : ℤ) :=
  criticalNormSourceDisplacement F K (s + 1) piK hpiK z

def wildEndpointIntrinsicCriticalSourceUnit (z : ResidueField F) :
    unitFiltration K (s + 1) :=
  criticalNormSourceUnit F K (by omega) piK hpiK z

def wildEndpointIntrinsicCriticalPolynomialValue (z : ResidueField F) : ResidueField F :=
  criticalNormPolynomialValue F K ht (by omega) hres piK hpiK hgen z

theorem wildEndpointIntrinsicCriticalPolynomialValue_raw (z : ResidueField F) :
    wildEndpointIntrinsicCriticalPolynomialValue F K ht hres piK hpiK hgen z =
      reduce F
        ((norm F K
            (1 + algebraMap F K
              (((teichmuller F z : ringOfIntegers F) : F)) *
                (piK : K) ^ (s + 1)) - 1) /
          (wildEndpointIntrinsicCriticalLowerUniformizer F K piK) ^ (s + 1)) (by
            have hdisp := (unitFiltrationDisplacement F s
              (normBelowBreakUnitFiltrationHom F K (s + 1) (s + 1)
                (normMapsUnitFiltration_atBreak F K ht hres piK hpiK hgen)
                (wildEndpointIntrinsicCriticalSourceUnit F K piK hpiK z))).property
            apply (div_mem_lattice_iff F
              ((wildEndpointIntrinsicCriticalLowerUniformizer F K piK) ^ (s + 1))
              (norm F K
                (1 + algebraMap F K
                  (((teichmuller F z : ringOfIntegers F) : F)) *
                    (piK : K) ^ (s + 1)) - 1)
              (s + 1 : ℤ) 0 (by
                rw [ord_pow, ord_uniformizer F
                  (wildEndpointIntrinsicCriticalLowerUniformizer_isUniformizer
                    F K hres piK hpiK)]
                norm_num)).2
            simpa only [coe_unitFiltrationDisplacement,
              coe_normBelowBreakUnitFiltrationHom,
              coe_normUnits,
              wildEndpointIntrinsicCriticalSourceUnit,
              coe_criticalNormSourceUnit, Nat.cast_add, Nat.cast_one,
              add_zero] using hdisp) := by
  simpa only [wildEndpointIntrinsicCriticalPolynomialValue,
    wildEndpointIntrinsicCriticalLowerUniformizer] using
      criticalNormPolynomialValue_raw F K ht (by omega) hres piK hpiK hgen z

include ht hres hpiK hgen in
theorem wildEndpointIntrinsicTraceCritical_mem (x : K)
    (hx : x ∈ lattice K (s + 1 : ℤ)) :
    trace F K x ∈ lattice F (s + 1 : ℤ) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    criticalNormTrace_mem F K ht hres piK hpiK hgen x hx

def wildEndpointIntrinsicCriticalLinearCoefficient : ResidueField F :=
  criticalNormLinearCoefficient F K ht hres piK hpiK hgen

include ht hres hpiK hgen in
theorem wildEndpointIntrinsicCriticalPolynomialValue_eq (z : ResidueField F) :
    wildEndpointIntrinsicCriticalPolynomialValue F K ht hres piK hpiK hgen z =
      z ^ Module.finrank F K +
        wildEndpointIntrinsicCriticalLinearCoefficient F K ht hres piK hpiK hgen * z := by
  simpa only [wildEndpointIntrinsicCriticalPolynomialValue,
    wildEndpointIntrinsicCriticalLinearCoefficient] using
      criticalNormPolynomialValue_eq F K ht (by omega) hres piK hpiK hgen z

@[simp]
theorem wildEndpointIntrinsicCriticalSourceCoordinate (z : ResidueField F) :
    wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv K piK hpiK s
        (Additive.ofMul
          (unitGradedMk K (s + 1)
            (wildEndpointIntrinsicCriticalSourceUnit F K piK hpiK z))) =
      extensionResidueMap F K z := by
  simpa only [wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv,
    wildEndpointIntrinsicCriticalSourceUnit] using
      criticalNormSourceCoordinate F K (by omega) piK hpiK z

def wildEndpointIntrinsicCriticalLambda
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤) : ResidueField F :=
  criticalNormRamificationLambda F K ht hres piK hpiK

theorem wildEndpointIntrinsicCriticalLambda_ne_zero :
    wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen ≠ 0 := by
  simpa only [wildEndpointIntrinsicCriticalLambda] using
    criticalNormRamificationLambda_ne_zero F K ht hres piK hpiK hgen

@[simp]
theorem wildEndpointIntrinsicPositiveRamificationCoordinate_mk
    (sigma : lowerRamificationGroup F K (((s + 1 : ℕ) : ℤ))) :
    wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv K piK hpiK s
        (Additive.ofMul
          (ramificationUnitGradedHom F K (s + 1) piK hpiK hgen
            (lowerRamificationGradedMk F K (((s + 1 : ℕ) : ℤ)) sigma))) =
      lowerRamificationResidueDisplacement F K sigma (piK : K) hpiK := by
  simpa only [wildEndpointIntrinsicPositiveUnitGradedResidueAddEquiv] using
    criticalNormPositiveRamificationCoordinate F K (by omega) piK hpiK hgen sigma

theorem wildEndpointIntrinsicCriticalSourceClass_eq_generator :
    unitGradedMk K (s + 1)
        (wildEndpointIntrinsicCriticalSourceUnit F K piK hpiK
          (wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen)) =
      ramificationUnitGradedHom F K (s + 1) piK hpiK hgen
        (endpointGradedGenerator F K s ht) := by
  simpa only [wildEndpointIntrinsicCriticalSourceUnit,
    wildEndpointIntrinsicCriticalLambda, endpointGradedGenerator,
    endpointLowerBreakElement, criticalNormGradedGenerator,
    criticalNormBreakGenerator] using
      criticalNormSourceClass_eq_generator F K ht (by omega) hres piK hpiK hgen

/-- The critical quotient is recorded in the target-over-image direction;
this prevents silently reversing the cokernel used at the endpoint. -/
theorem wildEndpointIntrinsicCriticalExactAndCokernel :
    Function.MulExact
        (ramificationUnitGradedHom F K (s + 1) piK hpiK hgen)
        (criticalGradedNorm F K ht hres piK hpiK hgen) ∧
      Nat.card (UnitGradedPiece F (s + 1) ⧸
        (criticalGradedNorm F K ht hres piK hpiK hgen).range) =
          Module.finrank F K := by
  exact ⟨ramification_criticalGradedNorm_mulExact
      F K ht hres piK hpiK hgen,
    criticalGradedNorm_cokernel_card F K ht hres piK hpiK hgen⟩

theorem wildEndpointIntrinsicCriticalPolynomialValue_lambda_eq_zero :
    wildEndpointIntrinsicCriticalPolynomialValue F K ht hres piK hpiK hgen
        (wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen) = 0 := by
  simpa only [wildEndpointIntrinsicCriticalPolynomialValue,
    wildEndpointIntrinsicCriticalLambda] using
      criticalNormPolynomialValue_lambda_eq_zero
        F K ht (by omega) hres piK hpiK hgen

/-- The exact critical polynomial in the manuscript's normalized source
and target coordinates. -/
theorem wildEndpointIntrinsicCriticalPolynomialValue_exact (z : ResidueField F) :
    wildEndpointIntrinsicCriticalPolynomialValue F K ht hres piK hpiK hgen z =
      z ^ Module.finrank F K -
        wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen ^
          (Module.finrank F K - 1) * z := by
  simpa only [wildEndpointIntrinsicCriticalPolynomialValue,
    wildEndpointIntrinsicCriticalLambda] using
      criticalNormPolynomialValue_exact_of_positiveBreak
        F K ht (by omega) hres piK hpiK hgen z

end RootCritical
section EndpointCriticalLambdaAgreement

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
variable {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

/-- The base-field displacement used by the derivative calculation is the
same normalized ramification coefficient as the critical norm polynomial. -/
theorem endpointNormalizedDerivativeCriticalLambda_eq_intrinsic :
    endpointNormalizedDerivativeCriticalLambda F K s ht piK hpiK hgen hres =
      wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen := by
  have he : endpointResidueEquiv F K hres =
      wildEndpointIntrinsicEndpointResidueEquiv F K hres := by
    apply RingEquiv.ext
    intro x
    rfl
  have hupper : endpointRamificationLambda F K s ht piK hpiK hgen =
      criticalNormUpperRamificationLambda F K ht piK hpiK := by
    rw [endpointRamificationLambda, endpointGradedGenerator,
      ramificationResidueCoordinateAddHom_mk,
      criticalNormUpperRamificationLambda]
    rfl
  rw [endpointNormalizedDerivativeCriticalLambda,
    wildEndpointIntrinsicCriticalLambda, criticalNormRamificationLambda,
    he, wildEndpointIntrinsicEndpointResidueEquiv, hupper]

end EndpointCriticalLambdaAgreement
theorem wildEndpointIntrinsicCriticalPolynomialValue_range_eq_traceKernel
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤) :
    let p := Module.finrank F K
    letI : Fact p.Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
    letI : CharP (ResidueField F) p := ringChar.of_eq
      (residueCharacteristic_eq_degree_of_positive_isLowerBreak
        F K ht (by omega) piK hpiK hgen)
    letI : Algebra (ZMod p) (ResidueField F) := ZMod.algebra _ _
    let lambda := wildEndpointIntrinsicCriticalLambda
      F K ht hres piK hpiK hgen
    Set.range (wildEndpointIntrinsicCriticalPolynomialValue
      F K ht hres piK hpiK hgen) =
      Set.range (fun y : (Algebra.trace (ZMod p) (ResidueField F)).ker ↦
        lambda ^ p * (y : ResidueField F)) := by
  dsimp only
  let p := Module.finrank F K
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht (by omega) piK hpiK hgen
  letI : Fact p.Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  letI : Algebra (ZMod p) (ResidueField F) := ZMod.algebra _ _
  let lambda := wildEndpointIntrinsicCriticalLambda
    F K ht hres piK hpiK hgen
  have hlambda : lambda ≠ 0 :=
    wildEndpointIntrinsicCriticalLambda_ne_zero
      F K ht hres piK hpiK hgen
  have hfun :
      wildEndpointIntrinsicCriticalPolynomialValue
          F K ht hres piK hpiK hgen =
        fun z : ResidueField F ↦
          z ^ p - lambda ^ (p - 1) * z := by
    funext z
    exact wildEndpointIntrinsicCriticalPolynomialValue_exact
      F K ht hres piK hpiK hgen z
  rw [hfun]
  exact finiteField_scaledFrobeniusSub_range_eq_scaledTraceKer
    (ResidueField F) p hchar lambda hlambda

end

end LanglandsFirstMainLemma
