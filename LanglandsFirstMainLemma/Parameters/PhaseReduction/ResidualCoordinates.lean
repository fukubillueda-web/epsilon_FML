import LanglandsFirstMainLemma.Parameters.PhaseReduction.StationaryData
import LanglandsFirstMainLemma.Lamprecht.CriticalPolarCoordinate
import LanglandsFirstMainLemma.Parameters.NormPolynomial

/-!
# Source-tied residual coordinates

This module contains the common lower/upper residual-coordinate source,
parity-exact critical coordinates, and exact coordinate-change formulas.
All selected representatives and normalizations are preserved literally.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Source-tied residual coordinates -/

/-- The manuscript's selected upper uniformizer, bundled as a field unit.
This is the uniformizer already supplied to the High/Low parameter tables. -/
def phaseReductionUpperUniformizer
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) : Kˣ :=
  Units.mk0 (pi : K) hpi.ne_zero

@[simp]
theorem phaseReductionUpperUniformizer_coe
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    ((phaseReductionUpperUniformizer K pi hpi : Kˣ) : K) = (pi : K) :=
  rfl

theorem phaseReductionUpperUniformizer_order
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    ord K ((phaseReductionUpperUniformizer K pi hpi : Kˣ) : K) =
      ((1 : ℤ) : WithTop ℤ) := by
  rw [phaseReductionUpperUniformizer_coe, ord_uniformizer K hpi]
  norm_num

/-- In residue degree one, the exact norm of the selected upper uniformizer
is the source-tied lower uniformizer. -/
def phaseReductionLowerUniformizer
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) : Fˣ :=
  normUnits F K (phaseReductionUpperUniformizer K pi hpi)

@[simp]
theorem phaseReductionLowerUniformizer_coe
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    ((phaseReductionLowerUniformizer F K pi hpi : Fˣ) : F) =
      norm F K (pi : K) :=
  rfl

theorem phaseReductionLowerUniformizer_order
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    ord F ((phaseReductionLowerUniformizer F K pi hpi : Fˣ) : F) =
      ((1 : ℤ) : WithTop ℤ) := by
  rw [phaseReductionLowerUniformizer_coe, ord_norm, hres, one_nsmul,
    ord_uniformizer K hpi]
  norm_num

/-- The common source coordinate at depth `d`: the `d`th power of the
selected source uniformizer. -/
def phaseReductionSourceCoordinate
    (E : Type*) [Field E] (varpi : Eˣ) (d : ℕ) : Eˣ :=
  varpi ^ d

@[simp]
theorem phaseReductionSourceCoordinate_coe
    (E : Type*) [Field E] (varpi : Eˣ) (d : ℕ) :
    ((phaseReductionSourceCoordinate E varpi d : Eˣ) : E) =
      (varpi : E) ^ d :=
  rfl

theorem phaseReductionSourceCoordinate_order
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) :
    ord E ((phaseReductionSourceCoordinate E varpi d : Eˣ) : E) =
      ((d : ℤ) : WithTop ℤ) := by
  rw [phaseReductionSourceCoordinate_coe, ord_pow, hvarpi]
  norm_num

/-- The literal Teichmuller lift in a source coordinate remains at least at
that coordinate's depth, including when the residue coordinate is zero. -/
theorem phaseReductionSourceTeichmullerLift_order_ge
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (d : ℕ) (z : ResidueField E) :
    (((d : ℕ) : ℤ) : WithTop ℤ) ≤
      ord E (((phaseReductionSourceCoordinate E varpi d : Eˣ) : E) *
        (teichmuller E z : E)) := by
  rw [ord_mul, phaseReductionSourceCoordinate_order E varpi hvarpi d]
  have hz : (0 : WithTop ℤ) ≤ ord E (teichmuller E z : E) :=
    (mem_lattice_zero_iff E).2 (teichmuller E z).property
  simpa only [zero_add, add_comm] using
    add_le_add_left hz (((d : ℕ) : ℤ) : WithTop ℤ)

/-- A single source choice ties the upper coordinate to the supplied
uniformizer and the lower coordinate to its exact norm.  Thus upper and
lower rows cannot be independently rescaled through this package. -/
structure PhaseReductionResidualCoordinateSource
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] where
  upperUniformizer : Kˣ
  lowerUniformizer : Fˣ
  upper_order : ord K (upperUniformizer : K) = ((1 : ℤ) : WithTop ℤ)
  lower_order : ord F (lowerUniformizer : F) = ((1 : ℤ) : WithTop ℤ)
  lower_eq_norm : lowerUniformizer = normUnits F K upperUniformizer

/-- Build the common source from the actual uniformizer supplied to the
parameter tables. -/
def phaseReductionResidualCoordinateSource
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)) :
    PhaseReductionResidualCoordinateSource F K where
  upperUniformizer := phaseReductionUpperUniformizer K pi hpi
  lowerUniformizer := phaseReductionLowerUniformizer F K pi hpi
  upper_order := phaseReductionUpperUniformizer_order K pi hpi
  lower_order := phaseReductionLowerUniformizer_order F K hres pi hpi
  lower_eq_norm := rfl

namespace PhaseReductionResidualCoordinateSource

variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The parity-exact coordinate forced by a source uniformizer and the
proved parity bound.  This form also applies after transporting a conductor
equality between fields. -/
def criticalCoordinateOfParity
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d epsilon : ℕ} (hparity : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    LamprechtCriticalCoordinate E d epsilon := by
  by_cases hepsilon : epsilon = 0
  · subst epsilon
    exact .even
  · have hepsilon_one : epsilon = 1 := by
      have := hparity
      omega
    subst epsilon
    exact .odd (phaseReductionSourceCoordinate E varpi d)
      (phaseReductionSourceCoordinate_order E varpi hvarpi d)

/-- The parity-exact coordinate at an actual stationary decomposition.  The
even branch contains no coordinate; the odd branch uses the actual depth. -/
def criticalCoordinate
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    LamprechtCriticalCoordinate E d epsilon :=
  criticalCoordinateOfParity h.epsilon_le_one varpi hvarpi

/-- The actual upper critical coordinate at a supplied decomposition. -/
def upperCriticalCoordinate
    (S : PhaseReductionResidualCoordinateSource F K)
    {chi : LocalQuasiCharData K} {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon) :
    LamprechtCriticalCoordinate K d epsilon :=
  criticalCoordinate h S.upperUniformizer S.upper_order

/-- The actual lower critical coordinate at a supplied decomposition. -/
def lowerCriticalCoordinate
    (S : PhaseReductionResidualCoordinateSource F K)
    {chi : LocalQuasiCharData F} {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon) :
    LamprechtCriticalCoordinate F d epsilon :=
  criticalCoordinate h S.lowerUniformizer S.lower_order

/-- At every depth, the lower source coordinate is exactly the norm of the
upper source coordinate.  This is the common-coordinate identity used before
any row-specific residual reindexing. -/
theorem lowerSourceCoordinate_eq_norm
    (S : PhaseReductionResidualCoordinateSource F K) (d : ℕ) :
    phaseReductionSourceCoordinate F S.lowerUniformizer d =
      normUnits F K
        (phaseReductionSourceCoordinate K S.upperUniformizer d) := by
  simp only [phaseReductionSourceCoordinate, map_pow, S.lower_eq_norm]

/-- Residue degree one promotes the canonical extension residue map to a
ring equivalence.  No independent identification of the two residue fields
is selected. -/
noncomputable def residueEquiv
    (hres : residueDegree F K = 1) :
    ResidueField F ≃+* ResidueField K := by
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
theorem residueEquiv_apply
    (hres : residueDegree F K = 1) (x : ResidueField F) :
    residueEquiv (F := F) (K := K) hres x = extensionResidueMap F K x :=
  rfl

/-- The derived source-to-selected unit for a parity-exact coordinate.  The
even row has no critical element and therefore carries the neutral unit; the
odd row carries exactly `selected / source`. -/
noncomputable def transportUnit
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d epsilon : ℕ} (C : LamprechtCriticalCoordinate E d epsilon)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    unitGroup E := by
  cases C with
  | even => exact 1
  | odd delta hdelta =>
      let ratio : Eˣ := delta / phaseReductionSourceCoordinate E varpi d
      refine ⟨ratio, (mem_unitGroup_iff_ord_eq_zero E ratio).2 ?_⟩
      dsimp only [ratio]
      rw [Units.val_div_eq_div_val, ord_div, hdelta,
        phaseReductionSourceCoordinate_order E varpi hvarpi d]
      simp

/-- Residue scalar of that source-to-selected unit. -/
noncomputable def transportScalar
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d epsilon : ℕ} (C : LamprechtCriticalCoordinate E d epsilon)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    ResidueField E :=
  ((residueUnits E (transportUnit C varpi hvarpi) :
    (ResidueField E)ˣ) : ResidueField E)

@[simp]
theorem transportUnit_even
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ} (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    transportUnit (LamprechtCriticalCoordinate.even :
      LamprechtCriticalCoordinate E d 0) varpi hvarpi = 1 :=
  rfl

@[simp]
theorem transportUnit_odd_coe
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ} (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    ((transportUnit (LamprechtCriticalCoordinate.odd delta hdelta)
      varpi hvarpi : unitGroup E) : Eˣ) =
      delta / phaseReductionSourceCoordinate E varpi d := by
  unfold transportUnit
  rfl

/-- In the odd branch the selected critical element is exactly the source
element scaled by the derived unit. -/
theorem scaledSourceCoordinate_eq
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ} (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    criticalPolarScaledCoordinate E
        (transportUnit (LamprechtCriticalCoordinate.odd delta hdelta)
          varpi hvarpi)
        (phaseReductionSourceCoordinate E varpi d) = delta := by
  apply Units.ext
  simp only [criticalPolarScaledCoordinate, Units.val_mul,
    transportUnit_odd_coe]
  rw [Units.val_div_eq_div_val]
  exact div_mul_cancel₀ (delta : E)
    (Units.ne_zero (phaseReductionSourceCoordinate E varpi d))

end PhaseReductionResidualCoordinateSource

namespace LocalLamprechtPhaseData

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- The actual residual critical function carried by a local Lamprecht
package.  It is constant one in even conductor and is the quotient-derived
Hasse function in odd conductor. -/
noncomputable def criticalFunction
    (D : LocalLamprechtPhaseData E chi psi) : ResidueField E → ℂ :=
  match D with
  | .even _ _ _ _ _ _ => fun _ ↦ 1
  | .odd d hm hlarge Gamma delta hdelta c hc =>
      lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c hc

/-- Every actual residual critical function is normalized to one at the
origin.  This follows from the literal Lamprecht function in the odd branch
and from the constant-one convention in the even branch. -/
@[simp]
theorem criticalFunction_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.criticalFunction 0 = 1 := by
  cases D with
  | even => rfl
  | odd d hm hlarge Gamma delta hdelta c hc =>
      change lamprechtHasseValue E chi psi d hm hlarge Gamma delta hdelta c
        (teichmuller E 0 : E) _ = 1
      have hunit :
          lamprechtHasseUnit E chi d hm hlarge delta hdelta
            (teichmuller E 0 : E)
            ((mem_lattice_zero_iff E).2 (teichmuller E 0).property) = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp
      rw [lamprechtHasseValue, hunit]
      simp

/-- The positive polar coefficient of the actual critical function relative
to a supplied nontrivial residual additive character. -/
noncomputable def polarCoefficient
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1) :
    ResidueField E := by
  letI := residueFieldFintype E
  exact match D with
    | .even _ _ _ _ _ _ => 0
    | .odd d hm hlarge Gamma delta hdelta _c _hc =>
        finiteAddCharCoefficient psi0 hpsi0
          (lamprechtResidualAddChar E chi psi d hm hlarge Gamma delta hdelta)

/-- The actual critical function bundled with its exact positive-polar law.
Neither the function nor its coefficient is an independently supplied
field. -/
noncomputable def toCriticalPolarFunction
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1) :
    CriticalPolarFunction (ResidueField E) psi0
      (D.polarCoefficient psi0 hpsi0) := by
  letI := residueFieldFintype E
  cases D with
  | even d hm hlarge Gamma c hc =>
      exact
        { toFun := fun _ ↦ 1
          ne_zero' := fun _ ↦ one_ne_zero
          map_add' := by
            intro x y
            simp [polarCoefficient] }
  | odd d hm hlarge Gamma delta hdelta c hc =>
      let phi :=
        lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c hc
      let polar :=
        lamprechtResidualAddChar E chi psi d hm hlarge Gamma delta hdelta
      exact
        { toFun := phi
          ne_zero' := phi.ne_zero
          map_add' := by
            intro x y
            rw [phi.map_add]
            congr 1
            exact
              (finiteAddCharCoefficient_apply psi0 hpsi0 polar (x * y)).symm }

@[simp]
theorem toCriticalPolarFunction_apply
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (x : ResidueField E) :
    D.toCriticalPolarFunction psi0 hpsi0 x = D.criticalFunction x := by
  cases D <;> rfl

/-- The affine coefficient of the actual residual critical function in odd
residue characteristic. -/
noncomputable def affineCoefficient
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) : ResidueField E := by
  letI := residueFieldFintype E
  exact (D.toCriticalPolarFunction psi0 hpsi0).affineCoefficient hchar hpsi0

/-- Exact quadratic-polynomial formula for the actual critical function.
The positive polar sign and the `A / 2` convention are explicit. -/
theorem criticalFunction_eq_quadratic
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) (x : ResidueField E) :
    D.criticalFunction x =
      psi0
        (D.polarCoefficient psi0 hpsi0 / 2 * x ^ 2 +
          D.affineCoefficient psi0 hpsi0 hchar * x) := by
  letI := residueFieldFintype E
  rw [← D.toCriticalPolarFunction_apply psi0 hpsi0 x]
  exact (D.toCriticalPolarFunction psi0 hpsi0).eq_quadratic hchar hpsi0 x

/-- Phase of the finite sum of the actual residual critical function. -/
noncomputable def criticalFunctionPhase
    (D : LocalLamprechtPhaseData E chi psi) : ℂ := by
  letI := residueFieldFintype E
  exact phase (∑ x : ResidueField E, D.criticalFunction x)

/-- Apply an actual local row constructor to the coordinate forced by one
source uniformizer.  Even rows receive no field coordinate; odd rows receive
the source element at their actual depth. -/
noncomputable def sourceTiedRow
    {d epsilon : ℕ}
    (row : LamprechtCriticalCoordinate E d epsilon →
      LocalLamprechtPhaseData E chi psi)
    (hparity : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    LocalLamprechtPhaseData E chi psi :=
  row (PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
    hparity varpi hvarpi)

/-- The complete residual critical function of a source-tied actual row. -/
noncomputable def sourceTiedRowFunction
    {d epsilon : ℕ}
    (row : LamprechtCriticalCoordinate E d epsilon →
      LocalLamprechtPhaseData E chi psi)
    (hparity : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    ResidueField E → ℂ :=
  (sourceTiedRow row hparity varpi hvarpi).criticalFunction

/-- Phase of the complete finite sum of that same source-tied function. -/
noncomputable def sourceTiedRowPhase
    {d epsilon : ℕ}
    (row : LamprechtCriticalCoordinate E d epsilon →
      LocalLamprechtPhaseData E chi psi)
    (hparity : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) : ℂ :=
  (sourceTiedRow row hparity varpi hvarpi).criticalFunctionPhase

@[simp]
theorem sourceTiedRowFunction_apply
    {d epsilon : ℕ}
    (row : LamprechtCriticalCoordinate E d epsilon →
      LocalLamprechtPhaseData E chi psi)
    (hparity : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (x : ResidueField E) :
    sourceTiedRowFunction row hparity varpi hvarpi x =
      (sourceTiedRow row hparity varpi hvarpi).criticalFunction x :=
  rfl

theorem sourceTiedRowPhase_eq [Fintype (ResidueField E)]
    {d epsilon : ℕ}
    (row : LamprechtCriticalCoordinate E d epsilon →
      LocalLamprechtPhaseData E chi psi)
    (hparity : epsilon ≤ 1)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) :
    sourceTiedRowPhase row hparity varpi hvarpi =
      phase (∑ x : ResidueField E,
        sourceTiedRowFunction row hparity varpi hvarpi x) := by
  unfold sourceTiedRowPhase criticalFunctionPhase sourceTiedRowFunction
  apply congrArg phase
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

/-- The previously exported critical factor is exactly the phase of the
finite sum of the actual critical function. -/
theorem criticalFactor_eq_criticalFunctionPhase
    (D : LocalLamprechtPhaseData E chi psi) :
    D.criticalFactor = D.criticalFunctionPhase := by
  cases D with
  | even d hm hlarge Gamma c hc =>
      letI := residueFieldFintype E
      simp only [criticalFactor, criticalFunctionPhase, criticalFunction]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hcard : 0 < (Fintype.card (ResidueField E) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
      exact (phase_ofReal_pos hcard).symm
  | odd d hm hlarge Gamma delta hdelta c hc =>
      rfl

/-- In odd residue characteristic, the phase of the actual critical function
is the certified quadratic phase of its extracted coefficient pair. -/
theorem criticalFunctionPhase_eq_quadraticPhase
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    D.criticalFunctionPhase =
      @quadraticPhase (ResidueField E) _ (residueFieldFintype E)
        psi0 (D.polarCoefficient psi0 hpsi0)
        (D.affineCoefficient psi0 hpsi0 hchar) := by
  letI := residueFieldFintype E
  rw [criticalFunctionPhase]
  calc
    phase (∑ x : ResidueField E, D.criticalFunction x) =
        phase (∑ x : ResidueField E,
          D.toCriticalPolarFunction psi0 hpsi0 x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      exact (D.toCriticalPolarFunction_apply psi0 hpsi0 x).symm
    _ = _ :=
      (D.toCriticalPolarFunction psi0 hpsi0).phase_sum_eq_quadraticPhase
        hchar hpsi0

/-- The Lamprecht critical factor is therefore the exact quadratic phase of
the actual critical function, rather than an independently supplied phase. -/
theorem criticalFactor_eq_quadraticPhase
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    D.criticalFactor =
      @quadraticPhase (ResidueField E) _ (residueFieldFintype E)
        psi0 (D.polarCoefficient psi0 hpsi0)
        (D.affineCoefficient psi0 hpsi0 hchar) := by
  rw [D.criticalFactor_eq_criticalFunctionPhase]
  exact D.criticalFunctionPhase_eq_quadraticPhase psi0 hpsi0 hchar

/-- In the odd constructor, the actual Lamprecht function is definitionally
the complete critical function used by the coordinate-transport API. -/
theorem odd_toCriticalPolarFunction_eq_criticalPolarData
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property) :
    LocalLamprechtPhaseData.toCriticalPolarFunction
        (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta hbeta)
        psi0 hpsi0 =
      criticalPolarData E chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
        beta hbeta := by
  apply CriticalPolarFunction.ext
  intro x
  rfl

/-- The Formula and CriticalPolarCoordinate presentations are the same
actual odd critical function.  This bridge carries the literal stationary
representative and coordinate on both sides. -/
theorem odd_criticalFunction_eq_criticalPolarFunction
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E chi d 1 (by omega) hm
            hlarge).int_le_conductor (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1 (by omega) hm hlarge)
          Gamma Gamma.property)
    (x : ResidueField E) :
    (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta
        hbeta).criticalFunction x =
      criticalPolarFunction E chi psi d hm hlarge Gamma delta hdelta beta x := by
  unfold criticalFunction lamprechtHasseFunction criticalPolarFunction
    lamprechtHasseValue criticalPolarValue
  congr 2

/-- Evaluate an actual odd Lamprecht function on an arbitrary integral lift
written as `y / delta`.  The unit on the right is constructed from that same
lift, so this statement introduces no independently chosen representative or
residual coordinate. -/
theorem odd_criticalFunction_integral_div_coordinate
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (c : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (y : E) (hy : y / (delta : E) ∈ lattice E 0) :
    let beta := lamprechtStationaryRepresentativeUnit E chi psi
      (lamprechtFormula_stationaryDepth E chi d 1
        (by omega) hm hlarge) Gamma c hc
    let onePlusY : Eˣ :=
      (lamprechtHasseUnit E chi d hm hlarge delta hdelta
        (y / (delta : E)) hy : Eˣ)
    (onePlusY : E) = 1 + y ∧
      LocalLamprechtPhaseData.criticalFunction
          (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta c hc)
          (reduce E (y / (delta : E)) hy) =
        (psi.character
          (((beta : Eˣ) : E) / ((Gamma : Eˣ) : E) * y) : ℂ) *
          (chi.character onePlusY : ℂ)⁻¹ := by
  dsimp only
  constructor
  · rw [lamprechtHasseUnit_coe]
    field_simp [Units.ne_zero delta]
  · change
      lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c hc
          (reduce E (y / (delta : E)) hy) = _
    rw [lamprechtHasseFunction_integral_lift]
    unfold lamprechtHasseValue
    rw [lamprechtStationaryRepresentativeUnit_coe]
    congr 2
    field_simp [Units.ne_zero delta, AdmissibleGamma.coe_ne_zero Gamma]

/-- Exact representative translation for the actual odd Lamprecht function,
with the source-to-selected `+Delta B*x` orientation. -/
theorem odd_criticalFunction_changeRepresentative
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (beta beta' : lattice E
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField E) :
    LocalLamprechtPhaseData.criticalFunction
        (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta'
          hbeta') x =
      LocalLamprechtPhaseData.criticalFunction
          (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta
            hbeta) x *
        psi0
          (criticalAffineTranslationCoefficient E chi psi d hm Gamma delta
            hdelta psi0 hpsi0
              (criticalStationaryRepresentativeDifference E chi psi d hm
                hlarge Gamma beta beta' hbeta hbeta') * x) :=
  criticalPolarFunction_changeRepresentative E chi psi d hm hlarge Gamma
    delta hdelta psi0 hpsi0 beta beta' hbeta hbeta' x

/-- Exact affine translation for those same actual functions:
`B' = B + A*a`.  The polar coefficient is unchanged because it is derived
from the stationary quotient class rather than a representative. -/
theorem odd_affineCoefficient_changeRepresentative
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (beta beta' : lattice E
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property) :
    LocalLamprechtPhaseData.affineCoefficient
        (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta'
          hbeta') psi0 hpsi0 hchar =
      LocalLamprechtPhaseData.affineCoefficient
          (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta
            hbeta) psi0 hpsi0 hchar +
        LocalLamprechtPhaseData.polarCoefficient
            (LocalLamprechtPhaseData.odd d hm hlarge Gamma delta hdelta beta
              hbeta) psi0 hpsi0 *
          criticalRepresentativeTranslationParameter E chi psi d hm hlarge
            Gamma delta hdelta beta beta' hbeta hbeta' :=
  criticalAffineCoefficient_changeRepresentative_eq_add_polar_mul_parameter
    E chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0 hchar beta beta'
      hbeta hbeta'

end LocalLamprechtPhaseData

/-! ### Exact changes of residual coordinate -/

/-- Multiplying the local critical element by an integral unit precomposes
the complete critical function by the corresponding residue scalar.  This
is an equality of the complete function, not only of its polar quotient. -/
theorem criticalPolarFunction_scaleCoordinate_apply
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (u : unitGroup E) (x : ResidueField E) :
    criticalPolarFunction E chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate E u delta)
        (criticalPolarScaledCoordinate_ord E d u delta hdelta) beta x =
      criticalPolarFunction E chi psi d hm hlarge Gamma delta hdelta beta
        (((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) * x) := by
  let tu : E := ((u : Eˣ) : E)
  let tx : E := (teichmuller E x : E)
  have htu : tu ∈ lattice E 0 := by
    exact (mem_lattice_zero_iff E).2
      (((unitGroupMulEquivRingOfIntegers E u :
        (ringOfIntegers E)ˣ) : ringOfIntegers E).property)
  have htx : tx ∈ lattice E 0 := by
    exact (mem_lattice_zero_iff E).2 (teichmuller E x).property
  let z : E := tu * tx
  have hz : z ∈ lattice E 0 :=
    mul_mem_lattice E htu htx
  have hreduce : reduce E z hz =
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) * x := by
    change residueMap E
        (((unitGroupMulEquivRingOfIntegers E u : (ringOfIntegers E)ˣ) :
          ringOfIntegers E) * teichmuller E x) = _
    rw [map_mul, ← residueUnits_coe, residueMap_teichmuller]
  have hlift := criticalPolarFunction_integral_lift E chi psi d hm hlarge
    Gamma delta hdelta beta hbeta z hz
  rw [hreduce] at hlift
  rw [hlift]
  unfold criticalPolarFunction criticalPolarValue
  congr 1
  · congr 2
    simp only [criticalPolarScaledCoordinate, z, tu, tx, Units.val_mul]
    ring
  · congr 2
    have hunit :
        criticalPolarUnit E chi d hm hlarge
            (criticalPolarScaledCoordinate E u delta)
            (criticalPolarScaledCoordinate_ord E d u delta hdelta)
            (teichmuller E x : E)
            ((mem_lattice_zero_iff E).2 (teichmuller E x).property) =
          criticalPolarUnit E chi d hm hlarge delta hdelta z hz := by
      apply Subtype.ext
      apply Units.ext
      simp only [criticalPolarUnit_coe, criticalPolarScaledCoordinate, z, tu,
        tx, Units.val_mul]
      ring
    rw [hunit]

namespace CriticalPolarFunction

/-- Transport only the polar-coefficient index of a complete function along
a proved coefficient equality; the function values do not change. -/
noncomputable def castCoefficient
    {k : Type*} [Field k] {psi0 : FiniteAddChar k} {A A' : k}
    (h : A = A') (phi : CriticalPolarFunction k psi0 A) :
    CriticalPolarFunction k psi0 A' :=
  h ▸ phi

@[simp]
theorem castCoefficient_apply
    {k : Type*} [Field k] {psi0 : FiniteAddChar k} {A A' : k}
    (h : A = A') (phi : CriticalPolarFunction k psi0 A) (x : k) :
    castCoefficient h phi x = phi x := by
  cases h
  rfl

end CriticalPolarFunction

/-- The actual critical data after scaling its local coordinate, cast to the
manuscript's explicit `lambda^2 * A` polar-coefficient type. -/
noncomputable def criticalPolarDataAtScaledCoordinate
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (u : unitGroup E) : CriticalPolarFunction (ResidueField E) psi0
      ((((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) ^ 2) *
        criticalPolarCoefficient E chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0) :=
  CriticalPolarFunction.castCoefficient
    (criticalPolarCoefficient_scaleCoordinate E chi psi d hm hlarge Gamma
      delta hdelta psi0 hpsi0 u)
    (criticalPolarData E chi psi d hm hlarge Gamma
      (criticalPolarScaledCoordinate E u delta)
      (criticalPolarScaledCoordinate_ord E d u delta hdelta) psi0 hpsi0
        beta hbeta)

/-- Exact complete-function coordinate transport.  In the direction
`c ↦ lift(lambda) * c`, the new function is `x ↦ Phi(lambda*x)` and its
polar coefficient is `lambda^2*A`. -/
theorem criticalPolarData_scaleCoordinate
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (u : unitGroup E) :
    criticalPolarDataAtScaledCoordinate chi psi d hm hlarge Gamma delta
        hdelta psi0 hpsi0 beta hbeta u =
      (criticalPolarData E chi psi d hm hlarge Gamma delta hdelta psi0
        hpsi0 beta hbeta).scale
          (((residueUnits E u : (ResidueField E)ˣ) : ResidueField E)) := by
  apply CriticalPolarFunction.ext
  intro x
  unfold criticalPolarDataAtScaledCoordinate
  rw [CriticalPolarFunction.castCoefficient_apply,
    CriticalPolarFunction.scale_apply]
  exact criticalPolarFunction_scaleCoordinate_apply chi psi d hm hlarge
    Gamma delta hdelta beta hbeta u x

/-- Exact affine-coordinate transport in the same direction:
`B ↦ lambda * B`.  Together with the result type above this exports the
pair `(A,B) ↦ (lambda^2*A,lambda*B)`. -/
theorem criticalPolarData_scaleCoordinate_affine
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (u : unitGroup E) :
    (criticalPolarDataAtScaledCoordinate chi psi d hm hlarge Gamma delta
      hdelta psi0 hpsi0 beta hbeta u).affineCoefficient hchar hpsi0 =
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) *
        (criticalPolarData E chi psi d hm hlarge Gamma delta hdelta psi0
          hpsi0 beta hbeta).affineCoefficient hchar hpsi0 := by
  rw [criticalPolarData_scaleCoordinate chi psi d hm hlarge Gamma delta
    hdelta psi0 hpsi0 beta hbeta u,
    CriticalPolarFunction.affineCoefficient_scale]

/-! ### Derived source-to-selected coordinate transport -/

/-- The unique field-unit ratio carrying a source critical coordinate to a
selected coordinate of the same exact order, bundled as an integral unit. -/
def criticalCoordinateTransportUnit
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ} (source selected : Eˣ)
    (hsource : ord E (source : E) = ((d : ℤ) : WithTop ℤ))
    (hselected : ord E (selected : E) = ((d : ℤ) : WithTop ℤ)) :
    unitGroup E :=
  ⟨selected / source, (mem_unitGroup_iff_ord_eq_zero E _).2 (by
    rw [Units.val_div_eq_div_val, ord_div, hselected, hsource]
    simp)⟩

/-- The selected coordinate is exactly the source coordinate scaled by the
derived transport unit. -/
theorem criticalCoordinateTransportUnit_scale
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ} (source selected : Eˣ)
    (hsource : ord E (source : E) = ((d : ℤ) : WithTop ℤ))
    (hselected : ord E (selected : E) = ((d : ℤ) : WithTop ℤ)) :
    criticalPolarScaledCoordinate E
        (criticalCoordinateTransportUnit E source selected hsource hselected)
        source = selected := by
  apply Units.ext
  simp only [criticalPolarScaledCoordinate, Units.val_mul,
    criticalCoordinateTransportUnit]
  rw [Units.val_div_eq_div_val]
  exact div_mul_cancel₀ (selected : E) (Units.ne_zero source)

/-- Residual scalar of the exact source-to-selected transport. -/
def criticalCoordinateTransportScalar
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {d : ℕ} (source selected : Eˣ)
    (hsource : ord E (source : E) = ((d : ℤ) : WithTop ℤ))
    (hselected : ord E (selected : E) = ((d : ℤ) : WithTop ℤ)) :
    (ResidueField E)ˣ :=
  residueUnits E
    (criticalCoordinateTransportUnit E source selected hsource hselected)

/-- Exact complete-function transport from a source coordinate to any
selected coordinate of the same order. -/
theorem criticalPolarFunction_transportCoordinate_apply
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (source selected : Eˣ)
    (hsource : ord E (source : E) = ((d : ℤ) : WithTop ℤ))
    (hselected : ord E (selected : E) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField E) :
    criticalPolarFunction E chi psi d hm hlarge Gamma selected hselected beta x =
      criticalPolarFunction E chi psi d hm hlarge Gamma source hsource beta
        (((criticalCoordinateTransportScalar E source selected hsource
          hselected : (ResidueField E)ˣ) : ResidueField E) * x) := by
  let u := criticalCoordinateTransportUnit E source selected hsource hselected
  have hselected_eq : criticalPolarScaledCoordinate E u source = selected :=
    criticalCoordinateTransportUnit_scale E source selected hsource hselected
  have htransport :=
    criticalPolarFunction_scaleCoordinate_apply chi psi d hm hlarge Gamma
      source hsource beta hbeta u x
  simpa only [hselected_eq, criticalCoordinateTransportScalar, u] using
    htransport

/-- The actual polar coefficient changes by the square of the derived
source-to-selected residual scalar. -/
theorem criticalPolarCoefficient_transportCoordinate
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (source selected : Eˣ)
    (hsource : ord E (source : E) = ((d : ℤ) : WithTop ℤ))
    (hselected : ord E (selected : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1) :
    criticalPolarCoefficient E chi psi d hm hlarge Gamma selected hselected
        psi0 hpsi0 =
      ((criticalCoordinateTransportScalar E source selected hsource hselected :
        (ResidueField E)ˣ) : ResidueField E) ^ 2 *
        criticalPolarCoefficient E chi psi d hm hlarge Gamma source hsource
          psi0 hpsi0 := by
  let u := criticalCoordinateTransportUnit E source selected hsource hselected
  have hselected_eq : criticalPolarScaledCoordinate E u source = selected :=
    criticalCoordinateTransportUnit_scale E source selected hsource hselected
  have htransport :=
    criticalPolarCoefficient_scaleCoordinate E chi psi d hm hlarge Gamma
      source hsource psi0 hpsi0 u
  simpa only [hselected_eq, criticalCoordinateTransportScalar, u] using
    htransport

/-- In odd residue characteristic the affine coefficient changes by the
derived scalar itself, in the same source-to-selected direction. -/
theorem criticalPolarData_transportCoordinate_affine
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Fintype (ResidueField E)]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (source selected : Eˣ)
    (hsource : ord E (source : E) = ((d : ℤ) : WithTop ℤ))
    (hselected : ord E (selected : E) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property) :
    (criticalPolarData E chi psi d hm hlarge Gamma selected hselected psi0
      hpsi0 beta hbeta).affineCoefficient hchar hpsi0 =
      ((criticalCoordinateTransportScalar E source selected hsource hselected :
        (ResidueField E)ˣ) : ResidueField E) *
        (criticalPolarData E chi psi d hm hlarge Gamma source hsource psi0
          hpsi0 beta hbeta).affineCoefficient hchar hpsi0 := by
  apply CriticalPolarFunction.affineCoefficient_unique hchar hpsi0
  intro x
  rw [criticalPolarData_apply]
  rw [criticalPolarFunction_transportCoordinate_apply E chi psi d hm hlarge
    Gamma source selected hsource hselected beta hbeta x]
  rw [criticalPolarFunction_eq_quadratic E chi psi d hm hlarge Gamma source
    hsource psi0 hpsi0 hchar beta hbeta]
  congr 1
  rw [criticalPolarCoefficient_transportCoordinate E chi psi d hm hlarge
    Gamma source selected hsource hselected psi0 hpsi0]
  unfold criticalAffineCoefficient
  ring_nf
  rfl

/-! ### Exact complete-function row transport -/

/-- The exact norm polynomial used in the manuscript's source-coordinate
transport: `P(y) = N(1+y)-1`. -/
noncomputable def phaseReductionNormPolynomial
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] (y : K) : F :=
  norm F K (1 + y) - 1

/-- The exact higher correction `H(y)=P(y)-Tr(y)`.  No term is truncated at
this stage. -/
noncomputable def phaseReductionNormHigherPart
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] (y : K) : F :=
  phaseReductionNormPolynomial F K y - trace F K y

theorem phaseReductionNormPolynomial_eq_normPolynomialValue
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] (y : K) :
    phaseReductionNormPolynomial F K y = normPolynomialValue F K y :=
  rfl

theorem phaseReductionNormHigherPart_eq_higherCorrection
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] (y : K) :
    phaseReductionNormHigherPart F K y =
      normPolynomialHigherCorrectionValue F K y := by
  rw [phaseReductionNormHigherPart,
    phaseReductionNormPolynomial_eq_normPolynomialValue,
    normPolynomialValue_eq_trace_add_higherCorrection]
  abel

/-- Transporting proof-bearing character data preserves the complete
residual critical function pointwise.  In particular, transport cannot
replace an actual stationary function by an independently chosen phase. -/
theorem transportLocalLamprechtPhaseData_criticalFunction
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (S : LocalLamprechtPhaseData E chi psi) :
    (transportLocalLamprechtPhaseData hchi hpsi S).criticalFunction =
      S.criticalFunction := by
  have hc : chi = chi' := LocalQuasiCharData.ext_character E hchi
  have hp : psi = psi' := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  rfl

end

end LanglandsFirstMainLemma
