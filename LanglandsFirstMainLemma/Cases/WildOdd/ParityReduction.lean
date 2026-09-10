import LanglandsFirstMainLemma.Cases.WildOdd.ResidualCoefficients
import LanglandsFirstMainLemma.Cases.WildOdd.ScalarPhaseProducts
import LanglandsFirstMainLemma.Cases.WildOdd.BoundaryPencil
import LanglandsFirstMainLemma.FiniteField.QuadraticPhasePowers

/-!
# Wild odd-prime parity reduction

This file is the assembly node for Proposition `prop:odd-phase-cancel`.
It introduces no residual coefficients, coordinates, stationary classes, or
finite-field phase identities.  The lower and upper coefficient shapes come
from `ResidualCoefficients`; the repeated and scalar phase products come from
`ScalarPhaseProducts`; and the boundary calculation is the literal theorem
from `BoundaryPencil`.

The five named manuscript patterns are proved separately:

1. the odd base factor below the break;
2. the odd nonidentity twist factors below the break;
3. the product of those two below-break contributions;
4. the all-factors-odd pattern above the break;
5. the odd boundary-pencil pattern.

The final theorem then dispatches on both conductor parities and on the
disjoint trichotomy `b < v`, `v < b`, `b = v`.  Even-conductor factors are
definitionally `1`, following the manuscript convention.
-/

open scoped BigOperators

namespace LanglandsFirstMainLemma

noncomputable section

/-! ## Phases attached to the certified coefficient rows -/

/-- The quadratic phase attached to a certified lower coefficient pair. -/
def wildOddLowerPairPhase {k : Type*} [Field k] [Fintype k]
    (psi : FiniteAddChar k) (P : WildOddCoefficientPair k) : ℂ :=
  quadraticPhase psi P.polar P.affine

/-- The quadratic phase attached to a certified upper coefficient pair. -/
def wildOddUpperPairPhase {k : Type*} [Field k] [Fintype k]
    (psi : FiniteAddChar k) (P : WildOddUpperCoefficientPair k) : ℂ :=
  quadraticPhase psi P.polar P.affine

/-- Every totalized quadratic phase is nonzero.  This elementary fact is used
only to turn a certified numerator/denominator equality into quotient `1`. -/
theorem wildOdd_quadraticPhase_ne_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : FiniteAddChar k) (a b : k) :
    quadraticPhase psi a b ≠ 0 := by
  exact phase_ne_zero _

/-! ## The three below-break contributions -/

section BelowAndAbove

variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k] [CharP k p]

/-- **Pattern 1: `b < v`, odd base factor.**

`ResidualCoefficients` gives the lower base row as
`(eta, eta * gamma)` and the upper below-break row with exactly the same
coefficients.  Their complete quadratic-phase quotient is therefore one. -/
theorem wildOdd_belowBaseOddPhase
    (psi : FiniteAddChar k)
    (base : WildOddNamedCoefficientPair k) :
    wildOddUpperPairPhase psi
          (wildOddUpperPairBelow base.eta base.gamma) /
        wildOddLowerPairPhase psi (wildOddBasePair base) = 1 := by
  apply div_self
  exact wildOdd_quadraticPhase_ne_zero psi _ _

/-- **Pattern 2: `b < v`, odd twist factors.**

The certified lower row is the scalar row
`(j*etaZero, j*etaZero*gammaZero)`.  The imported scalar-pencil identity
cancels the complete product over all nonzero prime-field indices, including
its additive translations and the exact `q0^(p-1)` factor. -/
theorem wildOdd_belowTwistFactorsOdd
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (hp2 : p ≠ 2)
    (omega : (ZMod p)ˣ →* kˣ) (homega : Function.Injective omega)
    (generator : WildOddNamedCoefficientPair k) :
    (∏ u : (ZMod p)ˣ,
      wildOddLowerPairPhase psi
        (wildOddTauPowerPair generator (omega u : k))) = 1 := by
  simpa only [wildOddLowerPairPhase, wildOddTauPowerPair, mul_assoc,
    mul_comm, mul_left_comm] using
      wildOdd_scalarPencil hp2 hpsi omega homega generator.eta_ne_zero
        generator.gamma

/-- **Pattern 3: `b < v`, product of the base and twist contributions.**

This is the manuscript quotient after the coefficient table has identified
the base/upper pair and every nonidentity norm/twist pair.  The preceding two
certificates are combined without any new coefficient calculation. -/
theorem wildOdd_belowOddPhaseQuotient
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (hp2 : p ≠ 2)
    (omega : (ZMod p)ˣ →* kˣ) (homega : Function.Injective omega)
    (generator base : WildOddNamedCoefficientPair k) :
    (wildOddUpperPairPhase psi
          (wildOddUpperPairBelow base.eta base.gamma) *
        ∏ u : (ZMod p)ˣ,
          wildOddLowerPairPhase psi
            (wildOddTauPowerPair generator (omega u : k))) /
      (wildOddLowerPairPhase psi (wildOddBasePair base) *
        ∏ u : (ZMod p)ˣ,
          wildOddLowerPairPhase psi
            (wildOddTauPowerPair generator (omega u : k))) = 1 := by
  rw [wildOdd_belowTwistFactorsOdd psi hpsi hp2 omega homega generator]
  simpa using wildOdd_belowBaseOddPhase psi base

/-! ## The strict-above pattern -/

/-- The base contribution above the break: the product of the `p` identical
lower twist phases is exactly the certified upper scalar phase. -/
theorem wildOdd_aboveBaseOddPhase
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (hp2 : p ≠ 2)
    (base : WildOddNamedCoefficientPair k)
    (dZero : k) (hdZero : dZero ≠ 0) :
    wildOddUpperPairPhase psi
          (wildOddUpperPairAbove p base.eta dZero) /
        (∏ _j : ZMod p,
          wildOddLowerPairPhase psi (wildOddBasePair base)) = 1 := by
  have hRepeated := wildOdd_repeatedPhase_primeFieldProduct hp2 hpsi
    base.eta_ne_zero hdZero base.gamma
  have hDenominator :
      (∏ _j : ZMod p,
          wildOddLowerPairPhase psi (wildOddBasePair base)) =
        quadraticPhase psi (-base.eta * dZero ^ (p - 1)) 0 := by
    simpa only [wildOddLowerPairPhase, wildOddBasePair, Finset.prod_const,
      Finset.card_univ, ZMod.card] using hRepeated
  have hNumerator :
      wildOddUpperPairPhase psi
          (wildOddUpperPairAbove p base.eta dZero) =
        quadraticPhase psi (-base.eta * dZero ^ (p - 1)) 0 := by
    simp only [wildOddUpperPairPhase, wildOddUpperPairAbove]
    congr 2
    ring
  rw [hNumerator, hDenominator]
  apply div_self
  exact wildOdd_quadraticPhase_ne_zero psi _ _

/-- **Pattern 4: `b > v`, all factors odd.**

The nonidentity norm phases give the imported scalar product `1`, while the
`p` identical twist phases give the imported repeated-phase/upper-scalar
identity.  Thus the complete residual phase quotient has manuscript
orientation `U * (∏ R_j) / (∏ T_j) = 1`. -/
theorem wildOdd_aboveAllOddPhaseQuotient
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (hp2 : p ≠ 2)
    (omega : (ZMod p)ˣ →* kˣ) (homega : Function.Injective omega)
    (generator base : WildOddNamedCoefficientPair k)
    (dZero : k) (hdZero : dZero ≠ 0) :
    (wildOddUpperPairPhase psi
          (wildOddUpperPairAbove p base.eta dZero) *
        ∏ u : (ZMod p)ˣ,
          wildOddLowerPairPhase psi
            (wildOddTauPowerPair generator (omega u : k))) /
      (∏ _j : ZMod p,
        wildOddLowerPairPhase psi (wildOddBasePair base)) = 1 := by
  rw [wildOdd_belowTwistFactorsOdd psi hpsi hp2 omega homega generator]
  simpa using wildOdd_aboveBaseOddPhase psi hpsi hp2 base dZero hdZero

end BelowAndAbove

/-! ## The literal boundary pattern -/

/-- **Pattern 5: `b = v`, odd boundary pencil.**

This statement is deliberately the literal `BoundaryPencil` numerator and
denominator.  No affine-pencil coefficient or reciprocal sum is redone here.
The imported equality changes the quotient to `D / D`, and nonvanishing is
inherited from total quadratic phases. -/
theorem wildOdd_boundaryOddPhaseQuotient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hp2 : p ≠ 2)
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (hnonzero : ∀ j : {j : ZMod p // j ≠ 0},
      ((j : ZMod p).val : ResidueField F) +
        wildOddBoundaryDZero generator base ≠ 0) :
    letI := residueFieldFintype F
    (quadraticPhase C.lower
          (wildOddBoundaryA0 F p hchar C generator base)
          (wildOddBoundaryB0 F p hchar C generator base) *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase C.lower
            ((ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p) *
              wildOddBoundaryRho generator base)
            ((ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p) *
              wildOddBoundaryTau generator base))) /
      (∏ j : ZMod p,
        quadraticPhase C.lower
          (1 + (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
            wildOddBoundaryRho generator base)
          (wildOddBoundarySigma generator base +
            (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
              wildOddBoundaryTau generator base)) = 1 := by
  letI := residueFieldFintype F
  rw [wildOdd_boundaryPencil F p hp2 hchar C generator base hnonzero]
  apply div_self
  apply Finset.prod_ne_zero_iff.mpr
  intro j _hj
  exact wildOdd_quadraticPhase_ne_zero C.lower _ _

/-! ## Exhaustive parity dispatch within each break position -/

/-- The complete below-break quotient, with even-conductor phases replaced by
`1` exactly as in the manuscript parity convention. -/
def wildOddBelowResidualPhaseQuotient
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    (psi : FiniteAddChar k)
    (omega : (ZMod p)ˣ →* kˣ)
    (generator base : WildOddNamedCoefficientPair k)
    (b v : ℕ) : ℂ :=
  ((if Odd (b + 1) then
      wildOddUpperPairPhase psi
        (wildOddUpperPairBelow base.eta base.gamma)
    else 1) *
      (if Odd (v + 1) then
        ∏ u : (ZMod p)ˣ,
          wildOddLowerPairPhase psi
            (wildOddTauPowerPair generator (omega u : k))
      else 1)) /
    ((if Odd (b + 1) then
      wildOddLowerPairPhase psi (wildOddBasePair base)
    else 1) *
      (if Odd (v + 1) then
        ∏ u : (ZMod p)ˣ,
          wildOddLowerPairPhase psi
            (wildOddTauPowerPair generator (omega u : k))
      else 1))

/-- The below-break quotient is one for all four independent parities of the
base conductor `b+1` and the norm-row conductor `v+1`. -/
theorem wildOdd_belowResidualPhaseQuotient_eq_one
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (hp2 : p ≠ 2)
    (omega : (ZMod p)ˣ →* kˣ) (homega : Function.Injective omega)
    (generator base : WildOddNamedCoefficientPair k)
    (b v : ℕ) :
    wildOddBelowResidualPhaseQuotient psi omega generator base b v = 1 := by
  rcases (b + 1).even_or_odd with hb | hb <;>
    rcases (v + 1).even_or_odd with hv | hv
  · have hnb : ¬ Odd (b + 1) := Nat.not_odd_iff_even.mpr hb
    have hnv : ¬ Odd (v + 1) := Nat.not_odd_iff_even.mpr hv
    simp [wildOddBelowResidualPhaseQuotient, hnb, hnv]
  · have hnb : ¬ Odd (b + 1) := Nat.not_odd_iff_even.mpr hb
    simp only [wildOddBelowResidualPhaseQuotient, if_neg hnb, if_pos hv,
      one_mul]
    rw [wildOdd_belowTwistFactorsOdd psi hpsi hp2 omega homega generator]
    simp
  · have hnv : ¬ Odd (v + 1) := Nat.not_odd_iff_even.mpr hv
    simp only [wildOddBelowResidualPhaseQuotient, if_pos hb, if_neg hnv,
      mul_one]
    simpa using wildOdd_belowBaseOddPhase psi base
  · simp only [wildOddBelowResidualPhaseQuotient, if_pos hb, if_pos hv]
    exact wildOdd_belowOddPhaseQuotient psi hpsi hp2 omega homega
      generator base

/-- The complete strict-above quotient, again retaining exactly the two
independent manuscript parities. -/
def wildOddAboveResidualPhaseQuotient
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    (psi : FiniteAddChar k)
    (omega : (ZMod p)ˣ →* kˣ)
    (generator base : WildOddNamedCoefficientPair k)
    (dZero : k) (b v : ℕ) : ℂ :=
  ((if Odd (b + 1) then
      wildOddUpperPairPhase psi
        (wildOddUpperPairAbove p base.eta dZero)
    else 1) *
      (if Odd (v + 1) then
        ∏ u : (ZMod p)ˣ,
          wildOddLowerPairPhase psi
            (wildOddTauPowerPair generator (omega u : k))
      else 1)) /
    (if Odd (b + 1) then
      ∏ _j : ZMod p,
        wildOddLowerPairPhase psi (wildOddBasePair base)
    else 1)

/-- The strict-above quotient is one for all four parity combinations.  The
odd/odd case is Pattern 4; the mixed cases use one of its two imported
scalar/repeated components; and the even/even case is literal `1`. -/
theorem wildOdd_aboveResidualPhaseQuotient_eq_one
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) (hp2 : p ≠ 2)
    (omega : (ZMod p)ˣ →* kˣ) (homega : Function.Injective omega)
    (generator base : WildOddNamedCoefficientPair k)
    (dZero : k) (hdZero : dZero ≠ 0) (b v : ℕ) :
    wildOddAboveResidualPhaseQuotient psi omega generator base dZero b v = 1 := by
  rcases (b + 1).even_or_odd with hb | hb <;>
    rcases (v + 1).even_or_odd with hv | hv
  · have hnb : ¬ Odd (b + 1) := Nat.not_odd_iff_even.mpr hb
    have hnv : ¬ Odd (v + 1) := Nat.not_odd_iff_even.mpr hv
    simp [wildOddAboveResidualPhaseQuotient, hnb, hnv]
  · have hnb : ¬ Odd (b + 1) := Nat.not_odd_iff_even.mpr hb
    simp only [wildOddAboveResidualPhaseQuotient, if_neg hnb, if_pos hv,
      one_mul]
    rw [wildOdd_belowTwistFactorsOdd psi hpsi hp2 omega homega generator]
    simp
  · have hnv : ¬ Odd (v + 1) := Nat.not_odd_iff_even.mpr hv
    simp only [wildOddAboveResidualPhaseQuotient, if_pos hb, if_neg hnv,
      mul_one]
    simpa using
      wildOdd_aboveBaseOddPhase psi hpsi hp2 base dZero hdZero
  · simp only [wildOddAboveResidualPhaseQuotient, if_pos hb, if_pos hv]
    exact wildOdd_aboveAllOddPhaseQuotient psi hpsi hp2 omega homega
      generator base dZero hdZero

/-- The complete boundary quotient.  At even common conductor it is literal
`1`; at odd common conductor it is exactly the imported boundary pencil. -/
def wildOddBoundaryResidualPhaseQuotient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (v : ℕ) : ℂ := by
  letI := residueFieldFintype F
  exact if Odd (v + 1) then
    (quadraticPhase C.lower
          (wildOddBoundaryA0 F p hchar C generator base)
          (wildOddBoundaryB0 F p hchar C generator base) *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase C.lower
            ((ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p) *
              wildOddBoundaryRho generator base)
            ((ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p) *
              wildOddBoundaryTau generator base))) /
      (∏ j : ZMod p,
        quadraticPhase C.lower
          (1 + (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
            wildOddBoundaryRho generator base)
          (wildOddBoundarySigma generator base +
            (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
              wildOddBoundaryTau generator base))
  else 1

/-- The boundary quotient is one in both exhaustive common-conductor parity
cases. -/
theorem wildOdd_boundaryResidualPhaseQuotient_eq_one
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hp2 : p ≠ 2)
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (v : ℕ)
    (hnonzero : Odd (v + 1) →
      ∀ j : {j : ZMod p // j ≠ 0},
        ((j : ZMod p).val : ResidueField F) +
          wildOddBoundaryDZero generator base ≠ 0) :
    wildOddBoundaryResidualPhaseQuotient F p hchar C generator base v = 1 := by
  rcases (v + 1).even_or_odd with hv | hv
  · have hnv : ¬ Odd (v + 1) := Nat.not_odd_iff_even.mpr hv
    simp [wildOddBoundaryResidualPhaseQuotient, hnv]
  · rw [wildOddBoundaryResidualPhaseQuotient, if_pos hv]
    exact wildOdd_boundaryOddPhaseQuotient F p hp2 hchar C generator base
      (hnonzero hv)

/-! ## Break-position assembly -/

/-- All data needed by the finite phase assembly after the upstream
coefficient nodes have selected their certified rows.  In particular,
`boundaryShift_ne_zero` supplies the noncancellation fact consumed by
`BoundaryPencil` only in the odd boundary case; no new stationary-class
assertion is present here. -/
structure WildOddParityReductionData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p] where
  b : ℕ
  v : ℕ
  omega : (ZMod p)ˣ →* (ResidueField F)ˣ
  omega_injective : Function.Injective omega
  generator : WildOddNamedCoefficientPair (ResidueField F)
  base : WildOddNamedCoefficientPair (ResidueField F)
  boundaryShift_ne_zero : b = v → Odd (v + 1) →
    ∀ j : {j : ZMod p // j ≠ 0},
      ((j : ZMod p).val : ResidueField F) +
        wildOddBoundaryDZero generator base ≠ 0

/-- The complete residual phase quotient in manuscript orientation.  Its
three branches are definitionally separated by the strict/disjoint break
tests `b < v`, `v < b`, and the remaining equality case. -/
def wildOddCompleteResidualPhaseQuotient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (D : WildOddParityReductionData F p) : ℂ := by
  letI := residueFieldFintype F
  exact if D.b < D.v then
    wildOddBelowResidualPhaseQuotient C.lower D.omega D.generator D.base
      D.b D.v
  else if D.v < D.b then
    wildOddAboveResidualPhaseQuotient C.lower D.omega D.generator D.base
      (wildOddBoundaryDZero D.generator D.base) D.b D.v
  else
    wildOddBoundaryResidualPhaseQuotient F p hchar C D.generator D.base D.v

/-- Exhaustive and disjoint break-position assembly of the five manuscript
patterns.  The resulting complete residual phase quotient is exactly `1` in
every parity and break-position case. -/
theorem wildOdd_completeResidualPhaseQuotient_eq_one
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hp2 : p ≠ 2)
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (D : WildOddParityReductionData F p) :
    wildOddCompleteResidualPhaseQuotient F p hchar C D = 1 := by
  letI := residueFieldFintype F
  rcases lt_trichotomy D.b D.v with hbelow | hboundary | habove
  · rw [wildOddCompleteResidualPhaseQuotient, if_pos hbelow]
    exact wildOdd_belowResidualPhaseQuotient_eq_one C.lower C.lower_ne_one
      hp2 D.omega D.omega_injective D.generator D.base D.b D.v
  · have hnotBelow : ¬ D.b < D.v := by omega
    have hnotAbove : ¬ D.v < D.b := by omega
    rw [wildOddCompleteResidualPhaseQuotient, if_neg hnotBelow,
      if_neg hnotAbove]
    exact wildOdd_boundaryResidualPhaseQuotient_eq_one F p hp2 hchar C
      D.generator D.base D.v
        (fun hodd ↦ D.boundaryShift_ne_zero hboundary hodd)
  · have hnotBelow : ¬ D.b < D.v := by omega
    rw [wildOddCompleteResidualPhaseQuotient, if_neg hnotBelow,
      if_pos habove]
    exact wildOdd_aboveResidualPhaseQuotient_eq_one C.lower C.lower_ne_one
      hp2 D.omega D.omega_injective D.generator D.base
        (wildOddBoundaryDZero D.generator D.base)
        (wildOddBoundaryDZero_ne_zero D.generator D.base) D.b D.v

/-! ## Public assembly API -/

universe u

/-- Public API exported to `WildOdd/Main`.  It records the exact upstream
coefficient table and `q0` powers used by the assembly, exposes each of the
five manuscript patterns, and finishes with the exhaustive complete quotient
theorem. -/
structure WildOddParityReductionAPI : Prop where
  residualCoefficients : WildOddResidualCoefficientTable
  q0Powers : type_of% @quadraticPhase_powers.{u}
  belowBaseOdd : type_of% @wildOdd_belowBaseOddPhase.{u}
  belowTwistsOdd : type_of% @wildOdd_belowTwistFactorsOdd.{u}
  belowProduct : type_of% @wildOdd_belowOddPhaseQuotient.{u}
  aboveAllOdd : type_of% @wildOdd_aboveAllOddPhaseQuotient.{u}
  boundaryPencil : type_of% @wildOdd_boundaryOddPhaseQuotient.{u}
  belowAllParities :
    type_of% @wildOdd_belowResidualPhaseQuotient_eq_one.{u}
  aboveAllParities :
    type_of% @wildOdd_aboveResidualPhaseQuotient_eq_one.{u}
  boundaryAllParities :
    type_of% @wildOdd_boundaryResidualPhaseQuotient_eq_one.{u}
  complete : type_of% @wildOdd_completeResidualPhaseQuotient_eq_one.{u}

/-- **Odd-prime finite phase cancellation** (`prop:odd-phase-cancel`).

This is an assembly theorem: its fields are exactly the imported coefficient,
scalar/repeated-phase, boundary-pencil, and `q0`-power consequences needed by
`WildOdd/Main`, capped by the exhaustive theorem that the complete residual
phase quotient is `1`. -/
theorem wildOdd_parityReduction : WildOddParityReductionAPI.{0} where
  residualCoefficients := wildOdd_twistCoefficients
  q0Powers := quadraticPhase_powers
  belowBaseOdd := wildOdd_belowBaseOddPhase
  belowTwistsOdd := wildOdd_belowTwistFactorsOdd
  belowProduct := wildOdd_belowOddPhaseQuotient
  aboveAllOdd := wildOdd_aboveAllOddPhaseQuotient
  boundaryPencil := wildOdd_boundaryOddPhaseQuotient
  belowAllParities := wildOdd_belowResidualPhaseQuotient_eq_one
  aboveAllParities := wildOdd_aboveResidualPhaseQuotient_eq_one
  boundaryAllParities := wildOdd_boundaryResidualPhaseQuotient_eq_one
  complete := wildOdd_completeResidualPhaseQuotient_eq_one

end

end LanglandsFirstMainLemma
