import LanglandsFirstMainLemma.Basic.CharacterTypes
import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.LocalField.FiniteQuotients
import LanglandsFirstMainLemma.Basic.Phase
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Langlands's Haar-integral local constant

This file implements the integral definition from the authoritative manuscript.
The integration space is the compact multiplicative group `U_F^0`, the measure
is an arbitrary positive left Haar measure on that group, and an admissible
denominator has exact order `m_F(χ) + n_F(ψ)`.

No Haar normalization, finite Gauss sum, or integral--finite comparison is used.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory Set

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## Integral-specific admissible denominators -/

/-- An admissible denominator for the integral definition.  This reducible
subtype uses the same order equation as the finite API, so the later bridge
needs no conversion or choice of representative. -/
abbrev IntegralAdmissibleGamma
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) :=
  {γ : Fˣ //
    ord F (γ : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)}

namespace IntegralAdmissibleGamma

variable {F} {chi : LocalQuasiCharData F} {psi : LocalAddCharData F}

@[simp]
theorem coe_ne_zero (γ : IntegralAdmissibleGamma F chi psi) :
    ((γ : Fˣ) : F) ≠ 0 :=
  Units.ne_zero (γ : Fˣ)

/-- Admissibility in principal-lattice form. -/
theorem smul_lattice_zero (γ : IntegralAdmissibleGamma F chi psi) :
    ((γ : Fˣ) : F) • lattice F 0 =
      lattice F ((chi.conductor : ℤ) + psi.conductor) :=
  (smul_lattice_zero_eq_iff_ord_eq F ((γ : Fˣ) : F)
    ((chi.conductor : ℤ) + psi.conductor)).2 γ.property

/-- Integral-admissible denominators exist. -/
theorem exists_admissible :
    Nonempty (IntegralAdmissibleGamma F chi psi) := by
  obtain ⟨γ, hγ⟩ := exists_ord_eq F ((chi.conductor : ℤ) + psi.conductor)
  have hγ0 : γ ≠ 0 := (ord_ne_top_iff F).1 (by rw [hγ]; simp)
  exact ⟨⟨Units.mk0 γ hγ0, hγ⟩⟩

/-- The ratio `γ'/γ` of two integral-admissible denominators. -/
def ratio (γ' γ : IntegralAdmissibleGamma F chi psi) : Fˣ :=
  (γ' : Fˣ) / (γ : Fˣ)

@[simp]
theorem coe_ratio (γ' γ : IntegralAdmissibleGamma F chi psi) :
    (ratio γ' γ : F) = ((γ' : Fˣ) : F) / ((γ : Fˣ) : F) := by
  simp [ratio]

/-- Two integral-admissible denominators differ by a local unit. -/
theorem ratio_mem_unitFiltration
    (γ' γ : IntegralAdmissibleGamma F chi psi) :
    ratio γ' γ ∈ unitFiltration F 0 := by
  rw [mem_unitFiltration_zero, coe_ratio, ord_div, γ'.property, γ.property]
  simp

/-- The ratio identity `γ' = (γ'/γ) γ`. -/
theorem ratio_mul (γ' γ : IntegralAdmissibleGamma F chi psi) :
    ratio γ' γ * (γ : Fˣ) = (γ' : Fˣ) := by
  simp [ratio]

/-- The ratio bundled in `U_F^0`. -/
def ratioUnit (γ' γ : IntegralAdmissibleGamma F chi psi) :
    unitFiltration F 0 :=
  ⟨ratio γ' γ, ratio_mem_unitFiltration γ' γ⟩

@[simp]
theorem coe_ratioUnit (γ' γ : IntegralAdmissibleGamma F chi psi) :
    (ratioUnit γ' γ : Fˣ) = ratio γ' γ :=
  rfl

end IntegralAdmissibleGamma

/-! ## The Borel compact Haar space `U_F^0` -/

private theorem integral_isOpen_lattice (n : ℤ) :
    IsOpen (lattice F n : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hopen := (ValuativeRel.valuation F).isOpen_closedBall
    (r := (ValuativeRel.valuation F).restrict a) (by simp [ha0])
  convert hopen using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    (ValuativeRel.valuation F).restrict_le_iff]

/-- Every unit-filtration layer is open in `Fˣ`. -/
theorem isOpen_unitFiltration (m : ℕ) :
    IsOpen (unitFiltration F m : Set Fˣ) := by
  cases m with
  | zero =>
      rw [unitFiltration_zero]
      have hsphere : IsOpen
          {x : F | (ValuativeRel.valuation F).restrict x = 1} :=
        (ValuativeRel.valuation F).isOpen_sphere one_ne_zero
      rw [show (unitGroup F : Set Fˣ) =
          (↑) ⁻¹' {x : F | (ValuativeRel.valuation F).restrict x = 1} by
        ext u
        change u ∈ (ValuativeRel.valuation F).valuationSubring.unitGroup ↔
          (ValuativeRel.valuation F).restrict (u : F) = 1
        rw [Valuation.mem_unitGroup_iff F (ValuativeRel.valuation F) u,
          (ValuativeRel.valuation F).restrict_eq_one_iff]]
      exact hsphere.preimage Units.continuous_val
  | succ m =>
      rw [show (unitFiltration F (m + 1) : Set Fˣ) =
          (fun u : Fˣ ↦ (u : F) - 1) ⁻¹'
            (lattice F ((m + 1 : ℕ) : ℤ) : Set F) by
        ext u
        exact mem_unitFiltration_succ_iff_sub_mem_lattice F m u]
      exact (integral_isOpen_lattice F _).preimage
        (Units.continuous_val.sub continuous_const)

/-- The certified copy of `U_F^m` inside `U_F^0` is open. -/
theorem isOpen_unitFiltrationInside_zero (m : ℕ) :
    IsOpen (unitFiltrationInside F (Nat.zero_le m) :
      Set (unitFiltration F 0)) := by
  rw [show (unitFiltrationInside F (Nat.zero_le m) :
        Set (unitFiltration F 0)) =
      ((↑) : unitFiltration F 0 → Fˣ) ⁻¹'
        (unitFiltration F m : Set Fˣ) by
    ext u
    exact mem_unitFiltrationInside F (Nat.zero_le m) u]
  exact (isOpen_unitFiltration F m).preimage continuous_subtype_val

private theorem image_unitFiltration_zero :
    Units.val '' (unitFiltration F 0 : Set Fˣ) =
      {x : F | (ValuativeRel.valuation F).restrict x = 1} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [unitFiltration_zero] at hu
    change (ValuativeRel.valuation F).restrict (u : F) = 1
    rw [(ValuativeRel.valuation F).restrict_eq_one_iff]
    exact (Valuation.mem_unitGroup_iff F
      (ValuativeRel.valuation F) u).1 hu
  · intro hx
    change (ValuativeRel.valuation F).restrict x = 1 at hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [(ValuativeRel.valuation F).restrict_eq_one_iff] at hx
      simp [h] at hx
    let u : Fˣ := Units.mk0 x hx0
    refine ⟨u, ?_, rfl⟩
    rw [unitFiltration_zero]
    apply (Valuation.mem_unitGroup_iff F
      (ValuativeRel.valuation F) u).2
    rwa [← (ValuativeRel.valuation F).restrict_eq_one_iff]

private theorem isCompact_unitFiltration_zero :
    IsCompact (unitFiltration F 0 : Set Fˣ) := by
  have hemb : Topology.IsEmbedding (Units.val : Fˣ → F) :=
    Units.isEmbedding_val₀
  refine (hemb.isCompact_iff
    (s := (unitFiltration F 0 : Set Fˣ))).mpr ?_
  rw [image_unitFiltration_zero]
  apply (IsNonarchimedeanLocalField.isCompact_closedBall F 1).of_isClosed_subset
  · exact (ValuativeRel.valuation F).isClosed_sphere 1
  · intro x hx
    rw [Set.mem_setOf_eq,
      (ValuativeRel.valuation F).restrict_eq_one_iff] at hx
    change (ValuativeRel.valuation F) x ≤ 1
    rw [hx]

/-- The measurable structure used for Haar integration on `U_F^0`. -/
noncomputable instance unitFiltrationZeroMeasurableSpace :
    MeasurableSpace (unitFiltration F 0) :=
  borel (unitFiltration F 0)

instance unitFiltrationZeroBorelSpace :
    BorelSpace (unitFiltration F 0) := ⟨rfl⟩

/-- `U_F^0` is compact. -/
instance unitFiltrationZeroCompactSpace :
    CompactSpace (unitFiltration F 0) :=
  isCompact_iff_compactSpace.mp (isCompact_unitFiltration_zero F)

/-! ## Raw integrand and Haar integral -/

variable {F}

/-! ## Unit norm of the quasi-character -/

/-- The restriction of a quasi-character to `U_F^0`, descended through its
exact conductor layer.  This is integral-specific support and does not use
the finite Gauss sum. -/
def integralQuasiCharOnUnitQuotient (chi : LocalQuasiCharData F) :
    UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _) →* ℂˣ :=
  QuotientGroup.lift (unitFiltrationInside F (Nat.zero_le chi.conductor))
    (chi.character.toMonoidHom.comp (unitFiltration F 0).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact chi.isConductor.trivial _
        ((mem_unitFiltrationInside F (Nat.zero_le chi.conductor) u).1 hu))

@[simp]
theorem integralQuasiCharOnUnitQuotient_mk
    (chi : LocalQuasiCharData F) (u : unitFiltration F 0) :
    integralQuasiCharOnUnitQuotient chi
        (unitFiltrationQuotientMk F (Nat.zero_le chi.conductor) u) =
      chi.character (u : Fˣ) :=
  rfl

/-- A continuous quasi-character has norm one on `U_F^0`.  The restriction
factors through the finite conductor quotient, so each value has finite
order. -/
theorem integralQuasiChar_norm_eq_one_of_mem_unitFiltration_zero
    (chi : LocalQuasiCharData F) (u : unitFiltration F 0) :
    ‖(chi.character (u : Fˣ) : ℂ)‖ = 1 := by
  let q := unitFiltrationQuotientMk F (Nat.zero_le chi.conductor) u
  let phi : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _) →* ℂ :=
    (Units.coeHom ℂ).comp (integralQuasiCharOnUnitQuotient chi)
  have hfin : IsOfFinOrder (phi q) :=
    phi.isOfFinOrder (isOfFinOrder_of_finite q)
  change ‖phi q‖ = 1
  exact hfin.norm_eq_one

/-- The manuscript's raw unit-integral summand. -/
def unitHaarIntegrand
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi)
    (u : unitFiltration F 0) : ℂ :=
  (psi.character (((u : Fˣ) : F) / ((gamma : Fˣ) : F)) : ℂ) *
    (chi.character (u : Fˣ) : ℂ)⁻¹

/-- The raw unit-integral summand is continuous. -/
theorem unitHaarIntegrand_continuous
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    Continuous (unitHaarIntegrand chi psi gamma) := by
  have hu : Continuous (fun u : unitFiltration F 0 ↦ ((u : Fˣ) : F)) :=
    Units.continuous_val.comp continuous_subtype_val
  have harg : Continuous (fun u : unitFiltration F 0 ↦
      ((u : Fˣ) : F) / ((gamma : Fˣ) : F)) :=
    hu.div continuous_const (fun _ ↦ IntegralAdmissibleGamma.coe_ne_zero gamma)
  have hpsi : Continuous (fun u : unitFiltration F 0 ↦
      (psi.character
        (((u : Fˣ) : F) / ((gamma : Fˣ) : F)) : ℂ)) :=
    psi.character.continuous_coe.comp harg
  have hchi : Continuous (fun u : unitFiltration F 0 ↦
      (chi.character (u : Fˣ) : ℂ)) :=
    chi.character.continuous_coe.comp continuous_subtype_val
  exact hpsi.mul (hchi.inv₀ (fun u ↦
    ContinuousQuasiChar.apply_ne_zero chi.character (u : Fˣ)))

/-- The raw unit-integral summand is Borel measurable. -/
theorem unitHaarIntegrand_measurable
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    Measurable (unitHaarIntegrand chi psi gamma) :=
  (unitHaarIntegrand_continuous chi psi gamma).measurable

/-- A positive Haar measure gives positive mass to all of `U_F^0`. -/
theorem unitHaarMeasure_univ_pos
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure] :
    0 < mu Set.univ :=
  isOpen_univ.measure_pos mu univ_nonempty

/-- A Haar measure on compact `U_F^0` is finite. -/
theorem unitHaarMeasure_univ_lt_top
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure] :
    mu Set.univ < ∞ :=
  isCompact_univ.measure_lt_top

/-- The raw unit-integral summand is integrable for every Haar measure. -/
theorem unitHaarIntegrand_integrable
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    Integrable (unitHaarIntegrand chi psi gamma) mu :=
  (unitHaarIntegrand_continuous chi psi gamma).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The unnormalised manuscript unit Haar integral. -/
def unitGaussIntegral
    (mu : Measure (unitFiltration F 0))
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) : ℂ :=
  ∫ u, unitHaarIntegrand chi psi gamma u ∂mu

/-- Rescaling the measure rescales the raw integral by the same nonnegative
real scalar. -/
theorem unitGaussIntegral_smul_nnreal_measure
    (mu : Measure (unitFiltration F 0)) (c : NNReal)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    unitGaussIntegral (c • mu) chi psi gamma =
      c • unitGaussIntegral mu chi psi gamma := by
  simp only [unitGaussIntegral, integral_smul_nnreal_measure]

/-! ## Admissible-denominator change -/

/-- Exact pointwise denominator-change formula, with the manuscript's
left-coset orientation and inverse quasi-character convention. -/
theorem unitHaarIntegrand_ratioUnit_mul
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma gamma' : IntegralAdmissibleGamma F chi psi)
    (u : unitFiltration F 0) :
    unitHaarIntegrand chi psi gamma'
        (IntegralAdmissibleGamma.ratioUnit gamma' gamma * u) =
      (chi.character (IntegralAdmissibleGamma.ratio gamma' gamma) : ℂ)⁻¹ *
        unitHaarIntegrand chi psi gamma u := by
  let a := IntegralAdmissibleGamma.ratioUnit gamma' gamma
  have harg :
      ((((a * u : unitFiltration F 0) : Fˣ) : F) /
          ((gamma' : Fˣ) : F)) =
        ((u : Fˣ) : F) / ((gamma : Fˣ) : F) := by
    change (((((a : Fˣ) * (u : Fˣ)) : Fˣ) : F) /
        ((gamma' : Fˣ) : F)) =
      ((u : Fˣ) : F) / ((gamma : Fˣ) : F)
    have hargUnits : ((a : Fˣ) * (u : Fˣ)) / (gamma' : Fˣ) =
        (u : Fˣ) / (gamma : Fˣ) := by
      rw [← IntegralAdmissibleGamma.ratio_mul gamma' gamma]
      simp [a, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa using congrArg Units.val hargUnits
  have hchiMul :
      (chi.character ((a * u : unitFiltration F 0) : Fˣ) : ℂ) =
        (chi.character (a : Fˣ) : ℂ) *
          (chi.character (u : Fˣ) : ℂ) := by
    exact congrArg Units.val
      (map_mul chi.character (a : Fˣ) (u : Fˣ))
  rw [unitHaarIntegrand, unitHaarIntegrand, harg, hchiMul, mul_inv_rev]
  change _ = (chi.character (a : Fˣ) : ℂ)⁻¹ * _
  ring

/-- Exact Haar-integral change under two admissible denominators. -/
theorem unitGaussIntegral_admissibleGamma_change
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma gamma' : IntegralAdmissibleGamma F chi psi) :
    unitGaussIntegral mu chi psi gamma' =
      (chi.character (IntegralAdmissibleGamma.ratio gamma' gamma) : ℂ)⁻¹ *
        unitGaussIntegral mu chi psi gamma := by
  let a := IntegralAdmissibleGamma.ratioUnit gamma' gamma
  change (∫ u, unitHaarIntegrand chi psi gamma' u ∂mu) =
    (chi.character (IntegralAdmissibleGamma.ratio gamma' gamma) : ℂ)⁻¹ *
      ∫ u, unitHaarIntegrand chi psi gamma u ∂mu
  calc
    _ = ∫ u, unitHaarIntegrand chi psi gamma' (a * u) ∂mu :=
      (integral_mul_left_eq_self (unitHaarIntegrand chi psi gamma') a).symm
    _ = ∫ u, (chi.character (IntegralAdmissibleGamma.ratio gamma' gamma) : ℂ)⁻¹ *
        unitHaarIntegrand chi psi gamma u ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (unitHaarIntegrand_ratioUnit_mul chi psi gamma gamma')
    _ = _ := integral_const_mul _ _

/-! ## Integral local constant -/

/-- Langlands's Haar-integral local constant for an explicit positive Haar
measure and admissible denominator. -/
def deltaIntegral
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) : ℂ :=
  (chi.character (gamma : Fˣ) : ℂ) *
    phase (unitGaussIntegral mu chi psi gamma)

/-- The integral local constant is independent of the positive normalization
of Haar measure. -/
theorem deltaIntegral_measure_independent
    (mu nu : Measure (unitFiltration F 0))
    [mu.IsHaarMeasure] [nu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    deltaIntegral nu chi psi gamma = deltaIntegral mu chi psi gamma := by
  let c := Measure.haarScalarFactor nu mu
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure nu mu
  have hnu : nu = c • mu :=
    Measure.isMulInvariant_eq_smul_of_compactSpace nu mu
  have hIntegral :
      unitGaussIntegral nu chi psi gamma =
        c • unitGaussIntegral mu chi psi gamma := by
    rw [hnu, unitGaussIntegral_smul_nnreal_measure]
  have hPhase :
      phase (c • unitGaussIntegral mu chi psi gamma) =
        phase (unitGaussIntegral mu chi psi gamma) := by
    change phase ((c : ℝ) • unitGaussIntegral mu chi psi gamma) =
      phase (unitGaussIntegral mu chi psi gamma)
    exact phase_smul_of_pos (c : ℝ) (by exact_mod_cast hc) _
  rw [deltaIntegral, deltaIntegral, hIntegral, hPhase]

/-- Integral-only gamma independence.  The nonzero hypothesis is logically
necessary for the total phase until the integral--finite bridge supplies
nonvanishing. -/
theorem deltaIntegral_gamma_independent_of_ne_zero
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma gamma' : IntegralAdmissibleGamma F chi psi)
    (hI : unitGaussIntegral mu chi psi gamma ≠ 0) :
    deltaIntegral mu chi psi gamma' = deltaIntegral mu chi psi gamma := by
  let a := IntegralAdmissibleGamma.ratioUnit gamma' gamma
  have hgamma' : (gamma' : Fˣ) = (a : Fˣ) * (gamma : Fˣ) :=
    (IntegralAdmissibleGamma.ratio_mul gamma' gamma).symm
  have hchiGamma' : (chi.character (gamma' : Fˣ) : ℂ) =
      (chi.character (a : Fˣ) : ℂ) *
        (chi.character (gamma : Fˣ) : ℂ) := by
    have hunit : chi.character (gamma' : Fˣ) =
        chi.character (a : Fˣ) * chi.character (gamma : Fˣ) := by
      rw [hgamma', map_mul]
    exact congrArg Units.val hunit
  have haNorm : ‖(chi.character (a : Fˣ) : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv,
      integralQuasiChar_norm_eq_one_of_mem_unitFiltration_zero chi a, inv_one]
  rw [deltaIntegral, deltaIntegral, hchiGamma',
    unitGaussIntegral_admissibleGamma_change mu chi psi gamma gamma']
  change ((chi.character (a : Fˣ) : ℂ) *
      (chi.character (gamma : Fˣ) : ℂ)) *
        phase ((chi.character (a : Fˣ) : ℂ)⁻¹ *
          unitGaussIntegral mu chi psi gamma) = _
  rw [phase_mul_of_norm_eq_one haNorm hI]
  have ha0 : (chi.character (a : Fˣ) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero chi.character (a : Fˣ)
  field_simp

end

end LanglandsFirstMainLemma
