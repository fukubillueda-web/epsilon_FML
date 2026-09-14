import LanglandsFirstMainLemma.Cases.WildEndpoints.One.DerivativeDiscriminant
import LanglandsFirstMainLemma.Cases.WildEndpoints.One.IntrinsicCritical

/-!
# Stationary representatives and endpoint reciprocity
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section EndpointOneChoices

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
variable {s : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F K s)
  (hspos : 0 < s) (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)
  (piF : Fˣ)
  (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))

/-- The canonical half-depth for conductor `s+1`. -/
def endpointOneDepth (s : ℕ) : ℕ := (s + 1) / 2

/-- The canonical parity digit for conductor `s+1`. -/
def endpointOneParity (s : ℕ) : ℕ := (s + 1) % 2

theorem endpointOneParity_le_one : endpointOneParity s ≤ 1 := by
  simp only [endpointOneParity]
  omega

theorem endpointOne_conductor_decomposition :
    s + 1 = 2 * endpointOneDepth s + endpointOneParity s := by
  simp only [endpointOneDepth, endpointOneParity]
  omega

/-- A normalized conductor-one denominator before multiplication by the
single uniformizer: its exact order is the additive conductor. -/
abbrev EndpointOneNormalizedGamma (psi : LocalAddCharData F) :=
  {gamma : Fˣ //
    ord F (gamma : F) = ((psi.conductor : ℤ) : WithTop ℤ)}


/-- The actual admissible denominator for a conductor-one character,
obtained by restoring the one uniformizer suppressed by normalization. -/
def endpointOneGammaF
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    AdmissibleGamma F chi psi :=
  ⟨piF * (gammaF : Fˣ), by
    rw [Units.val_mul, ord_mul, ord_uniformizer F hpiF, gammaF.property,
      hchi]
    norm_num⟩


@[simp] theorem endpointOneGammaF_coe
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    (endpointOneGammaF F piF hpiF chi hchi psi gammaF : Fˣ) =
      piF * (gammaF : Fˣ) := rfl

/-- The common high-conductor denominator for the generator norm
character.  Its underlying element is exactly `piF^(s+1) * gammaF`. -/
def endpointOneGammaTau
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    AdmissibleGamma F (endpointTauData F K hs hres piK hpiK hgen) psi :=
  ⟨piF ^ (s + 1) * (gammaF : Fˣ), by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ord_mul, ord_pow,
      ord_uniformizer F hpiF, gammaF.property]
    norm_num⟩

@[simp] theorem endpointOneGammaTau_coe
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF : Fˣ) =
      piF ^ (s + 1) * (gammaF : Fˣ) := rfl

theorem endpointOneGammaTau_order
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    ord F
        (((endpointOneGammaTau F K hs hres piK hpiK hgen
          piF hpiF psi gammaF :
            AdmissibleGamma F
              (endpointTauData F K hs hres piK hpiK hgen) psi) : Fˣ) : F) =
      ((((s + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ) :=
  (endpointOneGammaTau F K hs hres piK hpiK hgen
    piF hpiF psi gammaF).property

include hspos

/-- The canonical stationary depth of the nontrivial norm-character
generator at conductor `s+1`. -/
theorem endpointOneTauStationaryDepth :
    IsLamprechtStationaryDepth
      (endpointTauData F K hs hres piK hpiK hgen).conductor
      (endpointOneDepth s + endpointOneParity s) :=
  stableTwist_stationaryDepth F
    (endpointTauData F K hs hres piK hpiK hgen)
      (endpointOneDepth s) (endpointOneParity s)
      (endpointOneParity_le_one (s := s))
      (by
        change s + 1 = 2 * endpointOneDepth s + endpointOneParity s
        exact endpointOne_conductor_decomposition (s := s))
      (by
        change 1 < s + 1
        exact Nat.add_lt_add_right hspos 1)

/-- A fixed representative of the generator stationary numerator class. -/
def endpointOneBTau
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    lattice F (((s + 1 : ℕ) : ℤ) - ((s + 1 : ℕ) : ℤ)) :=
  Classical.choose (latticeQuotientMk_surjective F
    (sub_le_sub_left
      (endpointOneTauStationaryDepth F K hs hspos hres piK hpiK hgen).int_le_conductor
      ((s + 1 : ℕ) : ℤ))
    (stationaryNumeratorClass F
      (endpointTauData F K hs hres piK hpiK hgen) psi
      ((s + 1 : ℕ) : ℤ)
      (endpointOneTauStationaryDepth F K hs hspos hres piK hpiK hgen)
      (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF)
      (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF).property))

theorem endpointOneBTau_spec
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    latticeQuotientMk F
        (sub_le_sub_left
          (endpointOneTauStationaryDepth
            F K hs hspos hres piK hpiK hgen).int_le_conductor
          ((s + 1 : ℕ) : ℤ))
        (endpointOneBTau F K hs hspos hres piK hpiK hgen
          piF hpiF psi gammaF) =
      stationaryNumeratorClass F
        (endpointTauData F K hs hres piK hpiK hgen) psi
        ((s + 1 : ℕ) : ℤ)
        (endpointOneTauStationaryDepth
          F K hs hspos hres piK hpiK hgen)
        (endpointOneGammaTau F K hs hres piK hpiK hgen
          piF hpiF psi gammaF)
        (endpointOneGammaTau F K hs hres piK hpiK hgen
          piF hpiF psi gammaF).property :=
  Classical.choose_spec (latticeQuotientMk_surjective F
    (sub_le_sub_left
      (endpointOneTauStationaryDepth F K hs hspos hres piK hpiK hgen).int_le_conductor
      ((s + 1 : ℕ) : ℤ))
    (stationaryNumeratorClass F
      (endpointTauData F K hs hres piK hpiK hgen) psi
      ((s + 1 : ℕ) : ℤ)
      (endpointOneTauStationaryDepth F K hs hspos hres piK hpiK hgen)
      (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF)
      (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF).property))

/-- The representative specification in exactly the let-bound shape
consumed by the explicit stable-twist/product bridge. -/
theorem endpointOneBTau_bridgeSpec
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    let d := endpointOneDepth s
    let epsilon := endpointOneParity s
    let gammaTau := endpointOneGammaTau F K hs hres piK hpiK hgen
      piF hpiF psi gammaF
    let thetaTau := endpointTauData F K hs hres piK hpiK hgen
    let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon
      (endpointOneParity_le_one (s := s))
      (by
        change s + 1 = 2 * endpointOneDepth s + endpointOneParity s
        exact endpointOne_conductor_decomposition (s := s))
      (by
        change 1 < s + 1
        exact Nat.add_lt_add_right hspos 1)
    latticeQuotientMk F
        (sub_le_sub_left hrTau.int_le_conductor ((s + 1 : ℕ) : ℤ))
        (endpointOneBTau F K hs hspos hres piK hpiK hgen
          piF hpiF psi gammaF) =
      stationaryNumeratorClass F thetaTau psi ((s + 1 : ℕ) : ℤ)
        hrTau (gammaTau : Fˣ) (by simpa using gammaTau.property) := by
  dsimp only
  exact endpointOneBTau_spec F K hs hspos hres piK hpiK hgen
    piF hpiF psi gammaF

theorem endpointOneBTau_order
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    ord F ((endpointOneBTau F K hs hspos hres piK hpiK hgen
      piF hpiF psi gammaF :
        lattice F (((s + 1 : ℕ) : ℤ) - ((s + 1 : ℕ) : ℤ))) : F) = 0 := by
  have hord := stationaryNumeratorClass_representative_ord F
    (endpointTauData F K hs hres piK hpiK hgen) psi
    ((s + 1 : ℕ) : ℤ)
    (endpointOneTauStationaryDepth F K hs hspos hres piK hpiK hgen)
    (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF)
    (endpointOneGammaTau F K hs hres piK hpiK hgen piF hpiF psi gammaF).property
    (endpointOneBTau F K hs hspos hres piK hpiK hgen piF hpiF psi gammaF)
    (endpointOneBTau_spec F K hs hspos hres piK hpiK hgen piF hpiF psi gammaF)
  simpa using hord

theorem endpointOneBTau_ne_zero
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    ((endpointOneBTau F K hs hspos hres piK hpiK hgen
      piF hpiF psi gammaF :
        lattice F (((s + 1 : ℕ) : ℤ) - ((s + 1 : ℕ) : ℤ))) : F) ≠ 0 := by
  apply (ord_ne_top_iff F).1
  rw [endpointOneBTau_order F K hs hspos hres piK hpiK hgen
    piF hpiF psi gammaF]
  simp

omit hspos

/-- Denominators for the complete norm-character family: the identity
uses the normalized order-`n` input, while every nonidentity character
uses the single common denominator `gammaTau`. -/
def endpointOneGammaNorm
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi)
    (mu : NormCharacter F K) :
    AdmissibleGamma F
      (wildNormCharacterData F K hs hres piK hpiK hgen mu) psi := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    exact ⟨(gammaF : Fˣ), by
      simpa [wildNormCharacterData_one] using gammaF.property⟩
  · exact ⟨(endpointOneGammaTau F K hs hres piK hpiK hgen
        piF hpiF psi gammaF : Fˣ), by
      rw [wildNormCharacterData_of_ne F K hs hres piK hpiK hgen mu hmu]
      exact (endpointOneGammaTau F K hs hres piK hpiK hgen
        piF hpiF psi gammaF).property⟩

@[simp] theorem endpointOneGammaNorm_one
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi) :
    (endpointOneGammaNorm F K hs hres piK hpiK hgen
      piF hpiF psi gammaF 1 : Fˣ) = (gammaF : Fˣ) := by
  simp [endpointOneGammaNorm]

theorem endpointOneGammaNorm_ne_one
    (psi : LocalAddCharData F)
    (gammaF : EndpointOneNormalizedGamma F psi)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (endpointOneGammaNorm F K hs hres piK hpiK hgen
      piF hpiF psi gammaF mu : Fˣ) =
      (endpointOneGammaTau F K hs hres piK hpiK hgen
        piF hpiF psi gammaF : Fˣ) := by
  simp [endpointOneGammaNorm, hmu]

end EndpointOneChoices
/-- Lift a complex-valued finite additive character to complex units.
Nonvanishing follows formally from the additive-character law. -/
def endpointFiniteAddCharToUnits {k : Type*} [AddCommGroup k]
    (psi : AddChar k ℂ) : AddChar k ℂˣ where
  toFun x := Units.mk0 (psi x) (by
    intro hx
    have hmul := AddChar.map_add_eq_mul psi x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at hmul
    exact one_ne_zero hmul)
  map_zero_eq_one' := by
    apply Units.ext
    simp
  map_add_eq_mul' x y := by
    apply Units.ext
    exact AddChar.map_add_eq_mul psi x y

@[simp] theorem endpointFiniteAddCharToUnits_coe
    {k : Type*} [AddCommGroup k] (psi : AddChar k ℂ) (x : k) :
    ((endpointFiniteAddCharToUnits psi x : ℂˣ) : ℂ) = psi x := rfl

/-- The exact norm lower uniformizer, bundled in the valuation ring. -/
def wildEndpointLowerUniformizerInteger
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K)) :
    ringOfIntegers F :=
  ⟨(wildLowerUniformizer F K piK hpiK : Fˣ),
    (mem_lattice_zero_iff F).1 (by
      rw [mem_lattice, ord_uniformizer F
        (wildLowerUniformizer_isUniformizer F K hres piK hpiK)]
      norm_num)⟩

@[simp] theorem wildEndpointLowerUniformizerInteger_coe
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K)) :
    (wildEndpointLowerUniformizerInteger F K hres piK hpiK : F) =
      (wildLowerUniformizer F K piK hpiK : Fˣ) := rfl

/-- An actual representative of the target of the intrinsic critical graded
norm on the source element `1 + z~ pi_K^t`. -/
def wildEndpointCriticalTargetUnit
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
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) : unitFiltration F (s + 1) :=
  normBelowBreakUnitFiltrationHom F K (s + 1) (s + 1)
      (normMapsUnitFiltration_atBreak F K ht hres piK hpiK hgen)
    (wildEndpointIntrinsicCriticalSourceUnit F K piK hpiK z)

/-- Divide the actual critical norm displacement by the exact norm
uniformizer to the break power. -/
def wildEndpointCriticalTargetNormalized
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
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) : lattice F 0 := by
  let uF := wildEndpointCriticalTargetUnit F K ht hres piK hpiK hgen z
  let xF : lattice F (((s + 1 : ℕ) : ℤ)) :=
    positiveUnitDisplacement F (by omega) uF
  let piF := wildEndpointLowerUniformizerInteger F K hres piK hpiK
  have hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) := by
    simpa only [piF, wildEndpointLowerUniformizerInteger_coe] using
      wildLowerUniformizer_isUniformizer F K hres piK hpiK
  refine ⟨(xF : F) / (piF : F) ^ (s + 1), ?_⟩
  apply (div_mem_lattice_iff F ((piF : F) ^ (s + 1)) (xF : F)
    (((s + 1 : ℕ) : ℤ)) 0 ?_).2
  · simpa only [add_zero] using xF.property
  · rw [ord_pow, ord_uniformizer F hpiF]
    norm_num

/-- The representative coordinate above is exactly the public intrinsic
critical polynomial value. -/
theorem wildEndpointCriticalTargetNormalized_eq_intrinsic
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
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (z : ResidueField F) :
    reduce F
        (wildEndpointCriticalTargetNormalized F K ht hres
          piK hpiK hgen z : F)
        (wildEndpointCriticalTargetNormalized F K ht hres
          piK hpiK hgen z).property =
      wildEndpointIntrinsicCriticalPolynomialValue
        F K ht hres piK hpiK hgen z := by
  rw [wildEndpointIntrinsicCriticalPolynomialValue_raw]
  rfl

/-- Triviality of the generator norm character on the actual critical norm
image forces the manuscript's reciprocal stationary power. -/
theorem wildEndpointTauStationaryAnnihilator
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
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi)
    (hnormalized :
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) = endpointCanonicalResidualAddChar (ResidueField F))
    (gammaTau : AdmissibleGamma F
      (endpointTauData F K ht hres piK hpiK hgen) psi)
    (hgammaTau :
      (gammaTau : Fˣ) =
        (wildLowerUniformizer F K piK hpiK) ^ (s + 1) * (gammaF : Fˣ))
    {r : ℕ}
    (hr : IsLamprechtStationaryDepth
      (endpointTauData F K ht hres piK hpiK hgen).conductor r)
    (bTau : lattice F
      ((((s + 1) + 1 : ℕ) : ℤ) -
        ((endpointTauData F K ht hres piK hpiK hgen).conductor : ℤ)))
    (hbTau :
      latticeQuotientMk F
          (sub_le_sub_left hr.int_le_conductor ((((s + 1) + 1 : ℕ) : ℤ))) bTau =
        stationaryNumeratorClass F
          (endpointTauData F K ht hres piK hpiK hgen) psi
          ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property) :
    let hb0 : (bTau : F) ∈ lattice F 0 := by
      simpa only [endpointTauData_conductor, sub_self] using bTau.property
    let aTau := reduce F (bTau : F) hb0
    aTau⁻¹ ^ (Module.finrank F K - 1) =
      (wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen) ^
        (Module.finrank F K * (Module.finrank F K - 1)) := by
  let theta := endpointTauData F K ht hres piK hpiK hgen
  let p := Module.finrank F K
  let hb0 : (bTau : F) ∈ lattice F 0 := by
    simpa only [endpointTauData_conductor, sub_self] using bTau.property
  let aTau := reduce F (bTau : F) hb0
  dsimp only
  letI hpFact : Fact p.Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht (by omega) piK hpiK hgen
  letI : CharP (ResidueField F) p := by
    rw [← hchar]
    infer_instance
  have hbOrd : ord F (bTau : F) = 0 := by
    have h := stationaryNumeratorClass_representative_ord
      F theta psi ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau
        gammaTau.property bTau hbTau
    simpa only [theta, endpointTauData_conductor, sub_self,
      WithTop.coe_zero] using h
  have haTau : aTau ≠ 0 := by
    intro ha0
    change residueMap F
      ⟨(bTau : F), (mem_lattice_zero_iff F).1 hb0⟩ = 0 at ha0
    rw [residueMap_eq_zero_iff] at ha0
    have hdeep : (((1 : ℤ) : WithTop ℤ)) ≤ ord F (bTau : F) := ha0
    rw [hbOrd] at hdeep
    exact (not_le_of_gt (by norm_num :
      (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ))) hdeep
  let psi0 : AddChar (ResidueField F) ℂˣ :=
    endpointFiniteAddCharToUnits
      (endpointCanonicalResidualAddChar (ResidueField F))
  have hpsi0 : psi0 ≠ 1 := by
    intro htriv
    apply endpointCanonicalResidualAddChar_ne_one (ResidueField F)
    ext z
    have hz := congrArg
      (fun xi : AddChar (ResidueField F) ℂˣ ↦ ((xi z : ℂˣ) : ℂ)) htriv
    simpa only [psi0, endpointFiniteAddCharToUnits_coe,
      AddChar.one_apply, Units.val_one] using hz
  have hfrob0 : ∀ z : ResidueField F, psi0 (z ^ p) = psi0 z := by
    intro z
    apply Units.ext
    simpa only [psi0, endpointFiniteAddCharToUnits_coe,
      residueCharacteristic, hchar] using
        endpointCanonicalResidualAddChar_frobenius (ResidueField F) z
  refine criticalPolynomial_annihilator
    (p := p) (a := aTau)
    (lambda := wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen)
    psi0 hpsi0 hfrob0 haTau ?_
  intro z
  let uK : unitFiltration K (s + 1) :=
    wildEndpointIntrinsicCriticalSourceUnit (s := s) F K piK hpiK z
  let uF := wildEndpointCriticalTargetUnit F K ht hres piK hpiK hgen z
  let xFt : lattice F (((s + 1 : ℕ) : ℤ)) :=
    positiveUnitDisplacement F (by omega) uF
  have hrt : r ≤ s + 1 := by
    have hpred := hr.le_predecessor
    simp only [endpointTauData_conductor] at hpred
    omega
  let xFr : lattice F (r : ℤ) :=
    ⟨(xFt : F), lattice_antitone F (by exact_mod_cast hrt) xFt.property⟩
  have hlinear := stationaryNumeratorClass_linearization
    F theta psi ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property
      bTau hbTau xFr
  have hunit : (positiveUnitOfLattice F hr.pos xFr : Fˣ) = (uF : Fˣ) := by
    apply Units.ext
    rw [coe_positiveUnitOfLattice, coe_positiveUnitDisplacement]
    ring
  rw [hunit] at hlinear
  have hnormRange : (uF : Fˣ) ∈ (normUnits F K).range := by
    refine ⟨(uK : Kˣ), ?_⟩
    rfl
  have htauOne :
      (endpointTau F K ht hres piK hpiK hgen).1 (uF : Fˣ) = 1 :=
    (endpointTau F K ht hres piK hpiK hgen).eq_one_on_normRange
      F K (uF : Fˣ) hnormRange
  have hpsiOne : psi.character
      ((bTau : F) * (xFr : F) / ((gammaTau : Fˣ) : F)) = 1 := by
    apply Units.ext
    simpa only [theta, endpointTauData_character, htauOne] using
      (congrArg Units.val hlinear).symm
  let y : lattice F 0 :=
    ⟨(bTau : F) *
        (wildEndpointCriticalTargetNormalized F K ht hres
          piK hpiK hgen z : F),
      by
        simpa only [zero_add] using mul_mem_lattice F hb0
          (wildEndpointCriticalTargetNormalized F K ht hres
            piK hpiK hgen z).property⟩
  have hyReduce : reduce F (y : F) y.property =
      aTau * (z ^ p -
        (wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen) ^
          (p - 1) * z) := by
    let bO : ringOfIntegers F :=
      ⟨(bTau : F), (mem_lattice_zero_iff F).1 hb0⟩
    let xO : ringOfIntegers F :=
      ⟨(wildEndpointCriticalTargetNormalized F K ht hres
          piK hpiK hgen z : F),
        (mem_lattice_zero_iff F).1
          (wildEndpointCriticalTargetNormalized F K ht hres
            piK hpiK hgen z).property⟩
    change residueMap F (bO * xO) = _
    rw [map_mul]
    change aTau * reduce F
        (wildEndpointCriticalTargetNormalized F K ht hres
          piK hpiK hgen z : F)
        (wildEndpointCriticalTargetNormalized F K ht hres
          piK hpiK hgen z).property = _
    rw [wildEndpointCriticalTargetNormalized_eq_intrinsic,
      wildEndpointIntrinsicCriticalPolynomialValue_exact]
  apply Units.ext
  change endpointCanonicalResidualAddChar (ResidueField F)
      (aTau * (z ^ p -
        (wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen) ^
          (p - 1) * z)) = 1
  rw [← hyReduce, ← hnormalized]
  rw [residualAddChar_integral_lift]
  apply congrArg Units.val at hpsiOne
  simp only [Units.val_one] at hpsiOne
  rw [← hpsiOne]
  congr 2
  dsimp only [y, xFr]
  let piF := wildEndpointLowerUniformizerInteger F K hres piK hpiK
  change (bTau : F) *
        ((((uF : Fˣ) : F) - 1) / (piF : F) ^ (s + 1)) /
      ((gammaF : Fˣ) : F) =
    (bTau : F) * (xFt : F) / ((gammaTau : Fˣ) : F)
  rw [hgammaTau]
  change (bTau : F) *
        ((((uF : Fˣ) : F) - 1) /
          ((wildLowerUniformizer F K piK hpiK : Fˣ) : F) ^ (s + 1)) /
      ((gammaF : Fˣ) : F) =
    (bTau : F) * (xFt : F) /
      (((wildLowerUniformizer F K piK hpiK : Fˣ) : F) ^ (s + 1) *
        ((gammaF : Fˣ) : F))
  rw [coe_positiveUnitDisplacement]
  field_simp [gammaF.coe_ne_zero]

/-- A depth-zero stationary numerator with its exact order, packaged as a
local unit. -/
def endpointStationaryLocalUnit
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (b : lattice F 0) (hbOrd : ord F (b : F) = 0) : unitGroup F :=
  ⟨Units.mk0 (b : F) ((ord_ne_top_iff F).1 (by rw [hbOrd]; simp)),
    (mem_unitGroup_iff_ord_eq_zero F _).2 hbOrd⟩

/-- The literal manuscript quotient `c_tau/(pi_F^t gamma_F)`, with
`c_tau = gamma_tau/b_tau`. -/
def endpointReciprocalStationaryRatio
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (t : ℕ) (piF : ringOfIntegers F)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (gammaF gammaTau : Fˣ)
    (b : lattice F 0) (hbOrd : ord F (b : F) = 0) : F :=
  (((gammaTau /
      ((endpointStationaryLocalUnit F b hbOrd : unitGroup F) : Fˣ)) /
    ((Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF) : Fˣ) : F)

theorem endpointReciprocalStationaryRatio_eq_inv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (t : ℕ) (piF : ringOfIntegers F)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (gammaF gammaTau : Fˣ)
    (hgammaTau : gammaTau =
      (Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF)
    (b : lattice F 0) (hbOrd : ord F (b : F) = 0) :
    endpointReciprocalStationaryRatio F t piF hpiF
        gammaF gammaTau b hbOrd =
      ((((endpointStationaryLocalUnit F b hbOrd : unitGroup F)⁻¹ :
        unitGroup F) : Fˣ) : F) := by
  change (((gammaTau /
      ((endpointStationaryLocalUnit F b hbOrd : unitGroup F) : Fˣ)) /
    ((Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF) : Fˣ) : F) = _
  rw [hgammaTau]
  let A : Fˣ := (Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF
  let B : Fˣ := (endpointStationaryLocalUnit F b hbOrd : unitGroup F)
  change ((A / B / A : Fˣ) : F) = (((B⁻¹ : Fˣ) : F))
  simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
  field_simp

theorem endpointReciprocalStationaryRatio_order
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (t : ℕ) (piF : ringOfIntegers F)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (gammaF gammaTau : Fˣ)
    (hgammaTau : gammaTau =
      (Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF)
    (b : lattice F 0) (hbOrd : ord F (b : F) = 0) :
    ord F (endpointReciprocalStationaryRatio F t piF hpiF
      gammaF gammaTau b hbOrd) = 0 := by
  rw [endpointReciprocalStationaryRatio_eq_inv
    F t piF hpiF gammaF gammaTau hgammaTau b hbOrd]
  exact (mem_unitGroup_iff_ord_eq_zero F _).1
    ((endpointStationaryLocalUnit F b hbOrd)⁻¹).property

/-- Reduction of the literal reciprocal ratio is the inverse stationary
coefficient. -/
theorem endpointReciprocalStationaryRatio_reduce
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (t : ℕ) (piF : ringOfIntegers F)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (gammaF gammaTau : Fˣ)
    (hgammaTau : gammaTau =
      (Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF)
    (b : lattice F 0) (hbOrd : ord F (b : F) = 0) :
    reduce F
        (endpointReciprocalStationaryRatio F t piF hpiF
          gammaF gammaTau b hbOrd)
        (by
          rw [mem_lattice,
            endpointReciprocalStationaryRatio_order F t piF hpiF
              gammaF gammaTau hgammaTau b hbOrd]
          exact le_rfl) =
      (reduce F (b : F) b.property)⁻¹ := by
  let bU := endpointStationaryLocalUnit F b hbOrd
  have hratio := endpointReciprocalStationaryRatio_eq_inv
    F t piF hpiF gammaF gammaTau hgammaTau b hbOrd
  change residueMap F _ = (residueMap F _)⁻¹
  calc
    residueMap F _ = ((residueUnits F (bU⁻¹) : (ResidueField F)ˣ) :
        ResidueField F) := by
      rw [residueUnits_coe]
      congr 1
      apply Subtype.ext
      exact hratio
    _ = (((residueUnits F bU)⁻¹ : (ResidueField F)ˣ) :
        ResidueField F) := by rw [map_inv]
    _ = (residueMap F _)⁻¹ := by
      have hbres : ((residueUnits F bU : (ResidueField F)ˣ) :
          ResidueField F) = residueMap F
            ⟨(b : F), (mem_lattice_zero_iff F).1 b.property⟩ := by
        rw [residueUnits_coe]
        congr 1
      simpa only [Units.val_inv_eq_inv_val] using
        congrArg (fun x : ResidueField F ↦ x⁻¹) hbres

/-- Literal form of the endpoint reciprocal relation: reduction of
`c_tau/(pi_F^t gamma_F)` has the prescribed `(p-1)`st power. -/
theorem wildEndpointReciprocalStationaryRelation
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p t : ℕ) (piF : ringOfIntegers F)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (gammaF gammaTau : Fˣ)
    (hgammaTau : gammaTau =
      (Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ t * gammaF)
    (b : lattice F 0) (hbOrd : ord F (b : F) = 0)
    (lambda : ResidueField F)
    (hpower : (reduce F (b : F) b.property)⁻¹ ^ (p - 1) =
      lambda ^ (p * (p - 1))) :
    reduce F
          (endpointReciprocalStationaryRatio F t piF hpiF
            gammaF gammaTau b hbOrd)
          (by
            rw [mem_lattice,
              endpointReciprocalStationaryRatio_order F t piF hpiF
                gammaF gammaTau hgammaTau b hbOrd]
            exact le_rfl) ^ (p - 1) =
      lambda ^ (p * (p - 1)) := by
  rw [endpointReciprocalStationaryRatio_reduce
    F t piF hpiF gammaF gammaTau hgammaTau b hbOrd]
  exact hpower

/-- One-shot intrinsic form of the manuscript relation
`res(c_tau/(pi_F^t gamma_F))^(p-1) = lambda^(p(p-1))`. -/
theorem wildEndpointTauReciprocalStationaryRelation
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
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi)
    (hnormalized :
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) = endpointCanonicalResidualAddChar (ResidueField F))
    (gammaTau : AdmissibleGamma F
      (endpointTauData F K ht hres piK hpiK hgen) psi)
    (hgammaTau :
      (gammaTau : Fˣ) =
        (wildLowerUniformizer F K piK hpiK) ^ (s + 1) * (gammaF : Fˣ))
    {r : ℕ}
    (hr : IsLamprechtStationaryDepth
      (endpointTauData F K ht hres piK hpiK hgen).conductor r)
    (bTau : lattice F
      ((((s + 1) + 1 : ℕ) : ℤ) -
        ((endpointTauData F K ht hres piK hpiK hgen).conductor : ℤ)))
    (hbTau :
      latticeQuotientMk F
          (sub_le_sub_left hr.int_le_conductor ((((s + 1) + 1 : ℕ) : ℤ))) bTau =
        stationaryNumeratorClass F
          (endpointTauData F K ht hres piK hpiK hgen) psi
          ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property) :
    let piF := wildEndpointLowerUniformizerInteger F K hres piK hpiK
    let hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) := by
      simpa only [piF, wildEndpointLowerUniformizerInteger_coe] using
        wildLowerUniformizer_isUniformizer F K hres piK hpiK
    let hb0 : (bTau : F) ∈ lattice F 0 := by
      simpa only [endpointTauData_conductor, sub_self] using bTau.property
    let b0 : lattice F 0 := ⟨(bTau : F), hb0⟩
    let hbOrd : ord F (b0 : F) = 0 := by
      have h := stationaryNumeratorClass_representative_ord
        F (endpointTauData F K ht hres piK hpiK hgen) psi
          ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property bTau hbTau
      simpa only [endpointTauData_conductor, sub_self,
        WithTop.coe_zero, b0] using h
    reduce F
          (endpointReciprocalStationaryRatio F (s + 1) piF hpiF
            (gammaF : Fˣ) (gammaTau : Fˣ) b0 hbOrd)
          (by
            rw [mem_lattice,
              endpointReciprocalStationaryRatio_order F (s + 1) piF hpiF
                (gammaF : Fˣ) (gammaTau : Fˣ) (by
                  rw [hgammaTau]
                  congr 2
                  apply Units.ext
                  rfl) b0 hbOrd]
            exact le_rfl) ^ (Module.finrank F K - 1) =
      (wildEndpointIntrinsicCriticalLambda F K ht hres piK hpiK hgen) ^
        (Module.finrank F K * (Module.finrank F K - 1)) := by
  dsimp only
  let piF := wildEndpointLowerUniformizerInteger F K hres piK hpiK
  have hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) := by
    simpa only [piF, wildEndpointLowerUniformizerInteger_coe] using
      wildLowerUniformizer_isUniformizer F K hres piK hpiK
  let hb0 : (bTau : F) ∈ lattice F 0 := by
    simpa only [endpointTauData_conductor, sub_self] using bTau.property
  let b0 : lattice F 0 := ⟨(bTau : F), hb0⟩
  have hbOrd : ord F (b0 : F) = 0 := by
    have h := stationaryNumeratorClass_representative_ord
      F (endpointTauData F K ht hres piK hpiK hgen) psi
        ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property bTau hbTau
    simpa only [endpointTauData_conductor, sub_self,
      WithTop.coe_zero, b0] using h
  apply wildEndpointReciprocalStationaryRelation F
    (Module.finrank F K) (s + 1) piF hpiF
      (gammaF : Fˣ) (gammaTau : Fˣ)
  · rw [hgammaTau]
    congr 2
    apply Units.ext
    rfl
  · have hpower := wildEndpointTauStationaryAnnihilator
      F K ht hres piK hpiK hgen chi hchi psi gammaF hnormalized
        gammaTau hgammaTau hr bTau hbTau
    simpa only [b0] using hpower

/-- The endpoint discriminant congruence at multiplicative conductor one,
with the reciprocal stationary element supplied by the endpoint stationary
class. -/
theorem endpoint_discriminant_congruence
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
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi)
    (hnormalized :
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) = endpointCanonicalResidualAddChar (ResidueField F))
    (gammaTau : AdmissibleGamma F
      (endpointTauData F K ht hres piK hpiK hgen) psi)
    (hgammaTau :
      (gammaTau : Fˣ) =
        (wildLowerUniformizer F K piK hpiK) ^ (s + 1) * (gammaF : Fˣ))
    {r : ℕ}
    (hr : IsLamprechtStationaryDepth
      (endpointTauData F K ht hres piK hpiK hgen).conductor r)
    (bTau : lattice F
      ((((s + 1) + 1 : ℕ) : ℤ) -
        ((endpointTauData F K ht hres piK hpiK hgen).conductor : ℤ)))
    (hbTau :
      latticeQuotientMk F
          (sub_le_sub_left hr.int_le_conductor ((((s + 1) + 1 : ℕ) : ℤ))) bTau =
        stationaryNumeratorClass F
          (endpointTauData F K ht hres piK hpiK hgen) psi
          ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property) :
    let piF := wildEndpointLowerUniformizerInteger F K hres piK hpiK
    let hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) := by
      simpa only [piF, wildEndpointLowerUniformizerInteger_coe] using
        wildLowerUniformizer_isUniformizer F K hres piK hpiK
    let hb0 : (bTau : F) ∈ lattice F 0 := by
      simpa only [endpointTauData_conductor, sub_self] using bTau.property
    let b0 : lattice F 0 := ⟨(bTau : F), hb0⟩
    let hbOrd : ord F (b0 : F) = 0 := by
      have h := stationaryNumeratorClass_representative_ord
        F (endpointTauData F K ht hres piK hpiK hgen) psi
          ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property bTau hbTau
      simpa only [endpointTauData_conductor, sub_self,
        WithTop.coe_zero, b0] using h
    let gammaK := endpointDerivativeGammaUnit
      F K ht piK hpiK hgen chi psi gammaF
    let cTau := (gammaTau : Fˣ) /
      ((endpointStationaryLocalUnit F b0 hbOrd : unitGroup F) : Fˣ)
    (normUnits F K gammaK / (gammaF : Fˣ)) /
        (((-1 : Fˣ) ^ Module.finrank F K) *
          cTau ^ (Module.finrank F K - 1)) ∈ unitFiltration F 1 := by
  dsimp only
  let piF := wildEndpointLowerUniformizerInteger F K hres piK hpiK
  have hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) := by
    simpa only [piF, wildEndpointLowerUniformizerInteger_coe] using
      wildLowerUniformizer_isUniformizer F K hres piK hpiK
  let hb0 : (bTau : F) ∈ lattice F 0 := by
    simpa only [endpointTauData_conductor, sub_self] using bTau.property
  let b0 : lattice F 0 := ⟨(bTau : F), hb0⟩
  have hbOrd : ord F (b0 : F) = 0 := by
    have h := stationaryNumeratorClass_representative_ord
      F (endpointTauData F K ht hres piK hpiK hgen) psi
        ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property bTau hbTau
    simpa only [endpointTauData_conductor, sub_self,
      WithTop.coe_zero, b0] using h
  let gammaK := endpointDerivativeGammaUnit
    F K ht piK hpiK hgen chi psi gammaF
  let bU : Fˣ :=
    ((endpointStationaryLocalUnit F b0 hbOrd : unitGroup F) : Fˣ)
  let cTau : Fˣ := (gammaTau : Fˣ) / bU
  let A : Fˣ :=
    (Units.mk0 (piF : F) hpiF.ne_zero : Fˣ) ^ (s + 1) * (gammaF : Fˣ)
  have hgammaTauA : (gammaTau : Fˣ) = A := by
    rw [hgammaTau]
    congr 2
    apply Units.ext
    rfl
  let ratio : F := endpointReciprocalStationaryRatio F (s + 1) piF hpiF
    (gammaF : Fˣ) (gammaTau : Fˣ) b0 hbOrd
  have hratioOrd : ord F ratio = 0 :=
    endpointReciprocalStationaryRatio_order F (s + 1) piF hpiF
      (gammaF : Fˣ) (gammaTau : Fˣ) hgammaTauA b0 hbOrd
  let ratioUnit : Fˣ := Units.mk0 ratio
    ((ord_ne_top_iff F).1 (by rw [hratioOrd]; simp))
  let a : unitGroup F :=
    ⟨ratioUnit, (mem_unitGroup_iff_ord_eq_zero F _).2 hratioOrd⟩
  have haCoe : ((a : unitGroup F) : Fˣ) = cTau / A := by
    apply Units.ext
    rfl
  have haReduce :
      ((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) =
        reduce F ratio (by
          rw [mem_lattice, hratioOrd]
          exact le_rfl) := by
    rw [residueUnits_coe]
    rfl
  have hstation := wildEndpointTauReciprocalStationaryRelation
    F K ht hres piK hpiK hgen chi hchi psi gammaF hnormalized
      gammaTau hgammaTau hr bTau hbTau
  dsimp only at hstation
  have haResidue :
      (((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) ^
          (Module.finrank F K - 1)) =
        endpointNormalizedDerivativeCriticalLambda F K s ht piK hpiK hgen hres ^
          (Module.finrank F K * (Module.finrank F K - 1)) := by
    rw [haReduce]
    rw [hstation]
    rw [endpointNormalizedDerivativeCriticalLambda_eq_intrinsic]
  let upper : Fˣ := normUnits F K gammaK / (gammaF : Fˣ)
  have hupper : upper =
      A ^ (Module.finrank F K - 1) *
        ((endpointNormalizedDerivativeNormLocalUnit
          F K s ht piK hpiK hgen : unitGroup F) : Fˣ) := by
    rw [show upper =
        normUnits F K
            (endpointDerivativeGammaUnit F K ht piK hpiK hgen chi psi gammaF) /
          (gammaF : Fˣ) by rfl]
    rw [endpointDerivativeGamma_norm_identity]
    congr 2
    exact hgammaTau.symm.trans hgammaTauA
  change upper /
      (((-1 : Fˣ) ^ Module.finrank F K) *
        cTau ^ (Module.finrank F K - 1)) ∈ unitFiltration F 1
  exact endpointDiscriminantCongruence_from_normalizedDerivative
    F K s ht piK hpiK hgen hres A cTau upper a haCoe haResidue hupper

end

end LanglandsFirstMainLemma
