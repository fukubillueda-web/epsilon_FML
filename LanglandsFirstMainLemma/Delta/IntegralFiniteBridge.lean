import LanglandsFirstMainLemma.Delta.FiniteDefinition
import LanglandsFirstMainLemma.Delta.IntegralDefinition

/-!
# Integral--finite comparison for Langlands's local constant

The multiplicative Haar space is exactly `U_F^0`.  It is partitioned by the
fibres of the canonical map to `U_F^0/U_F^m`, where `m` is the exact
multiplicative conductor.  The integrand is the existing descended finite
Gauss summand on every fibre, and left Haar invariance gives every fibre the
same finite, strictly positive mass.  Thus the raw integral is a positive
real scalar times the literal unnormalised `finiteGaussSum`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory Set

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable {F}

/-! ## Cosets of the exact conductor subgroup -/

/-- The coset of `U_F^m` indexed by `z : U_F^0/U_F^m`, defined without
choosing a representative: it is the literal fibre of the canonical quotient
map. -/
def integralFiniteCoset (chi : LocalQuasiCharData F)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _)) :
    Set (unitFiltration F 0) :=
  (unitFiltrationQuotientMk F (Nat.zero_le chi.conductor)) ⁻¹' {z}

/-- Membership in a conductor coset is exactly equality of quotient classes. -/
theorem mem_integralFiniteCoset_iff
    (chi : LocalQuasiCharData F)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _))
    (u : unitFiltration F 0) :
    u ∈ integralFiniteCoset chi z ↔
      unitFiltrationQuotientMk F (Nat.zero_le chi.conductor) u = z := by
  rfl

/-- The representative-free fibre is the left coset obtained from any
internally chosen quotient representative.  This description is used to
prove the cover, topology, and Haar invariance. -/
theorem integralFiniteCoset_eq_out_smul
    (chi : LocalQuasiCharData F)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _)) :
    integralFiniteCoset chi z = Quotient.out z •
      (unitFiltrationInside F (Nat.zero_le chi.conductor) :
        Set (unitFiltration F 0)) := by
  ext u
  rw [mem_integralFiniteCoset_iff, mem_leftCoset_iff]
  change unitFiltrationQuotientMk F (Nat.zero_le chi.conductor) u = z ↔
    (Quotient.out z)⁻¹ * u ∈ unitFiltrationInside F (Nat.zero_le chi.conductor)
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  exact eq_comm

/-- The quotient-indexed conductor cosets cover all of `U_F^0`. -/
theorem integralFiniteCoset_cover
    (chi : LocalQuasiCharData F) :
    Set.univ = ⋃ z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _),
      integralFiniteCoset chi z := by
  simp_rw [integralFiniteCoset_eq_out_smul]
  exact QuotientGroup.univ_eq_iUnion_smul
    (unitFiltrationInside F (Nat.zero_le chi.conductor))

/-- Distinct quotient classes index disjoint conductor cosets. -/
theorem integralFiniteCoset_pairwiseDisjoint
    (chi : LocalQuasiCharData F) :
    Set.Pairwise Set.univ (Function.onFun Disjoint
      (integralFiniteCoset chi :
        UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _) →
          Set (unitFiltration F 0))) := by
  intro z _hz w _hw hzw
  change Disjoint (integralFiniteCoset chi z) (integralFiniteCoset chi w)
  rw [Set.disjoint_left]
  intro u huz huw
  apply hzw
  exact ((mem_integralFiniteCoset_iff chi z u).1 huz).symm.trans
    ((mem_integralFiniteCoset_iff chi w u).1 huw)

/-- Every conductor coset is open in the multiplicative group `U_F^0`. -/
theorem integralFiniteCoset_isOpen
    (chi : LocalQuasiCharData F)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _)) :
    IsOpen (integralFiniteCoset chi z) := by
  rw [integralFiniteCoset_eq_out_smul]
  exact (isOpen_unitFiltrationInside_zero F chi.conductor).smul (Quotient.out z)

/-- Every conductor coset is Borel measurable. -/
theorem integralFiniteCoset_measurableSet
    (chi : LocalQuasiCharData F)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _)) :
    MeasurableSet (integralFiniteCoset chi z) :=
  (integralFiniteCoset_isOpen chi z).measurableSet

/-! ## Constancy of the exact integrand -/

/-- On a conductor coset, the Haar integrand is exactly the existing
representative-free finite Gauss summand.  In particular this preserves
`psi(u/gamma)`, the inverse on `chi(u)`, and the absence of an additive sign. -/
theorem unitHaarIntegrand_eq_on_integralFiniteCoset
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _))
    (u : unitFiltration F 0) (hu : u ∈ integralFiniteCoset chi z) :
    unitHaarIntegrand chi psi gamma u = finiteGaussSummand chi psi gamma z := by
  rw [← (mem_integralFiniteCoset_iff chi z u).1 hu]
  exact (finiteGaussSummand_mk chi psi gamma u).symm

/-- The already-measurable Haar integrand is integrable on every measurable
conductor coset. -/
theorem unitHaarIntegrand_integrableOn_integralFiniteCoset
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _)) :
    IntegrableOn (unitHaarIntegrand chi psi gamma)
      (integralFiniteCoset chi z) mu :=
  (unitHaarIntegrand_integrable mu chi psi gamma).integrableOn

/-! ## The common finite positive Haar measure -/

/-- Every `U_F^m`-coset has exactly the Haar measure of `U_F^m` itself. -/
theorem integralFiniteCoset_measure_eq
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F)
    (z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _)) :
    mu (integralFiniteCoset chi z) =
    mu (unitFiltrationInside F (Nat.zero_le chi.conductor) :
        Set (unitFiltration F 0)) := by
  rw [integralFiniteCoset_eq_out_smul]
  exact measure_smul mu (Quotient.out z) _

/-- The common conductor-coset measure is strictly positive. -/
theorem integralFiniteCoset_measure_pos
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) :
    0 < mu (unitFiltrationInside F (Nat.zero_le chi.conductor) :
      Set (unitFiltration F 0)) := by
  apply (isOpen_unitFiltrationInside_zero F chi.conductor).measure_pos mu
  exact ⟨1, (unitFiltrationInside F (Nat.zero_le chi.conductor)).one_mem⟩

/-- The common conductor-coset measure is finite because `U_F^0` is compact. -/
theorem integralFiniteCoset_measure_lt_top
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) :
    mu (unitFiltrationInside F (Nat.zero_le chi.conductor) :
      Set (unitFiltration F 0)) < ∞ := by
  exact lt_of_le_of_lt (measure_mono (Set.subset_univ _))
    (unitHaarMeasure_univ_lt_top mu)

/-- The common conductor-coset measure is nonzero. -/
theorem integralFiniteCoset_measure_ne_zero
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) :
    mu (unitFiltrationInside F (Nat.zero_le chi.conductor) :
      Set (unitFiltration F 0)) ≠ 0 :=
  (integralFiniteCoset_measure_pos mu chi).ne'

/-- The finite common Haar measure, converted to the real scalar used by the
Bochner integral. -/
def integralFinitePositiveScalar
    (mu : Measure (unitFiltration F 0))
    (chi : LocalQuasiCharData F) : ℝ :=
  mu.real (unitFiltrationInside F (Nat.zero_le chi.conductor) :
    Set (unitFiltration F 0))

/-- The common real scalar is strictly positive. -/
theorem integralFinitePositiveScalar_pos
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) :
    0 < integralFinitePositiveScalar mu chi := by
  exact ENNReal.toReal_pos (integralFiniteCoset_measure_ne_zero mu chi)
    (integralFiniteCoset_measure_lt_top mu chi).ne

/-- The common real scalar is nonzero. -/
theorem integralFinitePositiveScalar_ne_zero
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) :
    integralFinitePositiveScalar mu chi ≠ 0 :=
  (integralFinitePositiveScalar_pos mu chi).ne'

/-- Positivity is the explicit reason why the common scalar has total phase
one. -/
theorem phase_integralFinitePositiveScalar
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) :
    phase (integralFinitePositiveScalar mu chi : ℂ) = 1 :=
  phase_ofReal_pos (integralFinitePositiveScalar_pos mu chi)

/-! ## Exact integration over the finite coset partition -/

/-- Pointwise decomposition of the integrand as a finite sum of measurable
coset indicators. -/
theorem unitHaarIntegrand_eq_coset_sum
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi)
    (u : unitFiltration F 0) :
    letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
    unitHaarIntegrand chi psi gamma u =
      ∑ z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _),
        (integralFiniteCoset chi z).indicator
          (fun _ ↦ finiteGaussSummand chi psi gamma z) u := by
  classical
  let q := unitFiltrationQuotientMk F (Nat.zero_le chi.conductor) u
  rw [Finset.sum_eq_single q]
  · rw [indicator_of_mem ((mem_integralFiniteCoset_iff chi q u).2 rfl)]
    exact unitHaarIntegrand_eq_on_integralFiniteCoset chi psi gamma q u
      ((mem_integralFiniteCoset_iff chi q u).2 rfl)
  · intro z _hz hzq
    rw [indicator_of_notMem]
    intro huz
    apply hzq
    exact ((mem_integralFiniteCoset_iff chi z u).1 huz).symm
  · simp

/-- Exact raw comparison with the literal existing `finiteGaussSum`.  There
is no quotient-cardinality, residue-cardinality, sign, or Haar-normalization
factor.  Measurability and integrability of every indicator term are supplied
explicitly in the proof. -/
theorem unitGaussIntegral_eq_positiveScalar_mul_finiteGaussSum
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    unitGaussIntegral mu chi psi gamma =
      (integralFinitePositiveScalar mu chi : ℂ) * finiteGaussSum chi psi gamma := by
  classical
  letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
  rw [unitGaussIntegral]
  have hfun : unitHaarIntegrand chi psi gamma = fun u ↦
      ∑ z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _),
        (integralFiniteCoset chi z).indicator
          (fun _ ↦ finiteGaussSummand chi psi gamma z) u := by
    funext u
    exact unitHaarIntegrand_eq_coset_sum chi psi gamma u
  rw [hfun]
  rw [integral_finsetSum]
  · calc
      (∑ z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _),
          ∫ u, (integralFiniteCoset chi z).indicator
            (fun _ ↦ finiteGaussSummand chi psi gamma z) u ∂mu) =
          ∑ z : UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le _),
            (integralFinitePositiveScalar mu chi : ℂ) *
              finiteGaussSummand chi psi gamma z := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [integral_indicator_const _ (integralFiniteCoset_measurableSet chi z),
          measureReal_def, integralFiniteCoset_measure_eq mu chi]
        rfl
      _ = _ := by
        rw [← Finset.mul_sum]
        rfl
  · intro z _hz
    apply IntegrableOn.integrable_indicator
    · exact integrableOn_const
        ((integralFiniteCoset_measure_eq mu chi z).trans_lt
          (integralFiniteCoset_measure_lt_top mu chi)).ne
    · exact integralFiniteCoset_measurableSet chi z

/-- The raw Haar integral is nonzero, derived from the positive common coset
scalar and the independently proved finite Gauss-sum nonvanishing. -/
theorem unitGaussIntegral_ne_zero_of_finiteGaussSum
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    unitGaussIntegral mu chi psi gamma ≠ 0 := by
  rw [unitGaussIntegral_eq_positiveScalar_mul_finiteGaussSum]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (integralFinitePositiveScalar_ne_zero mu chi))
    (finiteGaussSum_ne_zero chi psi gamma)

/-- The Haar-integral and representative-free finite definitions agree with
the same admissible denominator, the same outside factor `chi(gamma)`, and
the same total phase. -/
theorem deltaIntegral_eq_deltaFinite
    (mu : Measure (unitFiltration F 0)) [mu.IsHaarMeasure]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : IntegralAdmissibleGamma F chi psi) :
    deltaIntegral mu chi psi gamma = deltaFinite chi psi gamma := by
  rw [deltaIntegral, deltaFinite,
    unitGaussIntegral_eq_positiveScalar_mul_finiteGaussSum]
  congr 1
  change phase (integralFinitePositiveScalar mu chi • finiteGaussSum chi psi gamma) = _
  exact phase_smul_of_pos _ (integralFinitePositiveScalar_pos mu chi) _

end

end LanglandsFirstMainLemma
