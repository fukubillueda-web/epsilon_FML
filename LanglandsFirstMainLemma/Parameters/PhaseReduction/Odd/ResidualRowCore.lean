import LanglandsFirstMainLemma.Parameters.PhaseReduction.ResidualCoordinates

/-!
# Shared odd-prime residual-row core

This module contains the generic even-row, parity-one-coordinate,
representative-change, and source-tied odd stationary lemmas shared by the
high, low, and literal-transport layers.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ### Even critical functions -/

/-- A stationary row at even conductor parity has the manuscript's literal
constant-one complete critical function, independently of its representative. -/
theorem localPhaseOfStationaryClass_criticalFunction_eq_one_of_even
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hepsilon : epsilon = 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon)
    (X : ResidueField E) :
    (localPhaseOfStationaryClass h Gamma R C).criticalFunction X = 1 := by
  subst epsilon
  cases C
  rfl

/-- A literal representative of a stationary quotient makes its raw
additive/multiplicative critical factor equal one on the actual stationary
linearization layer. -/
theorem stationaryRawFactor_eq_one
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d0 epsilon0 : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d0 epsilon0)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (R : StationaryClassRepresentative E chi psi h gamma hgamma)
    (y : E) (hy : y ∈ lattice E ((d0 + epsilon0 : ℕ) : ℤ))
    (unit : Eˣ) (hunit : (unit : E) = 1 + y) :
    (psi.character (((R.representative : E) / (gamma : E)) * y) : ℂ) *
        (chi.character unit : ℂ)⁻¹ = 1 := by
  let ylat : lattice E ((d0 + epsilon0 : ℕ) : ℤ) := ⟨y, hy⟩
  have hlinear := stationaryNumeratorClass_linearization E chi psi
    (chi.conductor : ℤ) (stationaryDepthOfConductorDecomposition E chi h)
      gamma hgamma R.toLamprecht R.toLamprecht_represents ylat
  have hunitEq : unit = positiveUnitOfLattice E
      (stationaryDepthOfConductorDecomposition E chi h).pos ylat := by
    apply Units.ext
    rw [hunit]
    rfl
  have hlinearC := congrArg (Units.val : ℂˣ → ℂ) hlinear
  rw [hunitEq]
  change
    (psi.character (((R.representative : E) / (gamma : E)) * y) : ℂ) *
        ((chi.character
          (positiveUnitOfLattice E
            (stationaryDepthOfConductorDecomposition E chi h).pos ylat) :
              ℂ))⁻¹ = 1
  rw [hlinearC]
  have hpsi : (psi.character
      ((R.toLamprecht : E) * (ylat : E) / (gamma : E)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  field_simp
  rfl

theorem criticalCoordinateOfParity_one
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (hparity : (1 : ℕ) ≤ 1) (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ)) (depth : ℕ) :
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
        (d := depth) (epsilon := 1) hparity varpi hvarpi =
      .odd (phaseReductionSourceCoordinate E varpi depth)
        (phaseReductionSourceCoordinate_order E varpi hvarpi depth) := by
  unfold PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
  simp
/-- Proof-bearing data for changing only the stationary representative in
one actual odd Lamprecht function.  Both complete functions share the exact
character, denominator, and source coordinate. -/
structure OddRepresentativeChangeData
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (source selected : LocalLamprechtPhaseData E chi psi) where
  d : ℕ
  hm : chi.conductor = 2 * d + 1
  hlarge : 1 < chi.conductor
  Gamma : AdmissibleGamma E chi psi
  delta : Eˣ
  hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)
  beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ))
  beta' : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ))
  hbeta : latticeQuotientMk E
      (sub_le_sub_left
        (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
        (chi.conductor : ℤ)) beta =
    stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
      (criticalPolar_stationaryDepth E chi d hm hlarge)
      Gamma Gamma.property
  hbeta' : latticeQuotientMk E
      (sub_le_sub_left
        (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
        (chi.conductor : ℤ)) beta' =
    stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
      (criticalPolar_stationaryDepth E chi d hm hlarge)
      Gamma Gamma.property
  source_eq : source = .odd d hm hlarge Gamma delta hdelta beta hbeta
  selected_eq : selected = .odd d hm hlarge Gamma delta hdelta beta' hbeta'

namespace OddRepresentativeChangeData

/-- The exact affine coefficient attached to the stationary representative
difference, with the source-to-selected orientation. -/
noncomputable def translationCoefficient
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1) :
    ResidueField E :=
  criticalAffineTranslationCoefficient E chi psi R.d R.hm R.Gamma R.delta
    R.hdelta psi0 hpsi0
      (criticalStationaryRepresentativeDifference E chi psi R.d R.hm
        R.hlarge R.Gamma R.beta R.beta' R.hbeta R.hbeta')

/-- The exact representative-change theorem for the complete odd Lamprecht
functions; the elementary and Hasse terms move together. -/
theorem criticalFunction_eq_mul_translation
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (x : ResidueField E) :
    selected.criticalFunction x = source.criticalFunction x *
      psi0 (R.translationCoefficient psi0 hpsi0 * x) := by
  calc
    selected.criticalFunction x =
        (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
          R.hdelta R.beta' R.hbeta').criticalFunction x :=
      congrArg (fun D => D.criticalFunction x) R.selected_eq
    _ = (LocalLamprechtPhaseData.odd R.d R.hm R.hlarge R.Gamma R.delta
          R.hdelta R.beta R.hbeta).criticalFunction x *
        psi0 (R.translationCoefficient psi0 hpsi0 * x) := by
      simpa only [translationCoefficient] using
        (LocalLamprechtPhaseData.odd_criticalFunction_changeRepresentative
          R.d R.hm R.hlarge R.Gamma R.delta R.hdelta psi0 hpsi0 R.beta
            R.beta' R.hbeta R.hbeta' x)
    _ = source.criticalFunction x *
        psi0 (R.translationCoefficient psi0 hpsi0 * x) := by
      exact congrArg
        (fun z => z * psi0 (R.translationCoefficient psi0 hpsi0 * x))
        (congrArg (fun D => D.criticalFunction x) R.source_eq).symm

end OddRepresentativeChangeData
/-- Evaluate an odd source-tied stationary row at its literal polar
representative and the coordinate forced by the common source. -/
theorem sourceTiedStationary_odd_criticalFunction
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hepsilon : epsilon = 1)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (varpi : Eˣ)
    (hvarpi : ord E (varpi : E) = ((1 : ℤ) : WithTop ℤ))
    (X : ResidueField E) :
    (LocalLamprechtPhaseData.sourceTiedRow
      (localPhaseOfStationaryClass h Gamma R) h.epsilon_le_one varpi
        hvarpi).criticalFunction X =
      criticalPolarFunction E chi psi d
        (by rw [h.conductor_eq, hepsilon]) h.conductor_gt_one Gamma
          (phaseReductionSourceCoordinate E varpi d)
          (phaseReductionSourceCoordinate_order E varpi hvarpi d)
            R.toLamprecht X := by
  subst epsilon
  unfold LocalLamprechtPhaseData.sourceTiedRow
  rw [criticalCoordinateOfParity_one]
  unfold localPhaseOfStationaryClass
  simp only [LocalLamprechtPhaseData.oddOfStationaryClass]
  exact LocalLamprechtPhaseData.odd_criticalFunction_eq_criticalPolarFunction
    chi psi d _ _ Gamma _ _ R.toLamprecht _ X
end

end LanglandsFirstMainLemma
