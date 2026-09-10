import LanglandsFirstMainLemma.Cases.WildQuadratic.CommonCorrection
import LanglandsFirstMainLemma.Cases.WildQuadratic.QuadraticRefinement
import LanglandsFirstMainLemma.Lamprecht.CriticalPolarCoordinate
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary

/-!
# Wild-quadratic residual coefficient table

This module builds the complete ten-row coefficient package for the
wild-quadratic case.  `WildQuadraticCoefficientRow.ofConductors` first records
the below/boundary/above position and the two conductor parities;
`WildQuadraticCoefficientData`, `WildQuadraticSelectedStationaryPairs`,
`QuotientDerivedNormalizedCriticalFunction`, and
`WildQuadraticCoefficientInputs` then retain the residual factors, quotient
classes, selected representatives, and local critical-function sources for
that row.  The actual lower, upper, and product coordinate certificates feed
`WildQuadraticCommonCoefficientView`, `WildQuadraticAllEvenCoefficientView`,
and `WildQuadraticCoefficientView`, from which
`WildQuadraticCoefficientCertificate`,
`wildQuadraticCoefficientCertificate`, and the four terminal table theorems
`WildQuadraticAllEvenCoefficientTable`, `WildQuadraticCoefficientTable`,
`WildQuadraticLowCoefficientTable`, and `WildQuadraticHighCoefficientTable`
are obtained.

For a first reading, follow the declarations in that order, with
`ActualLowerStationaryCoordinate`, `ActualUpperCoordinateCertificate`, and
`ActualProductCoordinateCertificate` between the input and view layers.  The
below/boundary/above terminology locates `b = m - 1` relative to `t = T - 1`;
Low and High instead describe the provenance of the parameter package, so an
above row is not by itself the whole High preparation branch.
-/

namespace LanglandsFirstMainLemma

noncomputable section

universe u

/-! ## Exhaustive conductor rows -/

/-- Parity of a conductor. -/
inductive WildQuadraticConductorParity
  | even
  | odd
  deriving DecidableEq

namespace WildQuadraticConductorParity

/-- The parity of a natural-number conductor. -/
def ofConductor (n : ℕ) : WildQuadraticConductorParity :=
  if Even n then .even else .odd

@[simp]
theorem ofConductor_eq_even_iff (n : ℕ) :
    ofConductor n = .even ↔ Even n := by
  simp [ofConductor]

@[simp]
theorem ofConductor_eq_odd_iff (n : ℕ) :
    ofConductor n = .odd ↔ Odd n := by
  rw [ofConductor]
  by_cases h : Even n
  · simp [h, Nat.not_odd_iff_even]
  · simpa [h] using Nat.not_even_iff_odd.mp h

end WildQuadraticConductorParity

/-- The four characters whose stationary factors occur in the quadratic error. -/
inductive WildQuadraticCharacter
  | chiK
  | tau
  | chiF
  | tauChiF
  deriving DecidableEq

/-- Position of `b=m-1` relative to the lower break `t=T-1`. -/
inductive WildQuadraticRange
  | below
  | boundary
  | above
  deriving DecidableEq

/-- The ten disjoint rows in the manuscript's wild-quadratic parity table.
The names list the parity of `m=b+1` first and `T=t+1` second. -/
inductive WildQuadraticCoefficientRow
  | belowMEvenTEven
  | belowMEvenTOdd
  | belowMOddTEven
  | belowMOddTOdd
  | boundaryEven
  | boundaryOdd
  | aboveMEvenTEven
  | aboveMEvenTOdd
  | aboveMOddTEven
  | aboveMOddTOdd
  deriving DecidableEq

namespace WildQuadraticCoefficientRow

/-- Exact witness for the three manuscript rows in which all four local
Lamprecht factors have even conductor.  No other coefficient row can carry
this witness. -/
inductive IsAllEven : WildQuadraticCoefficientRow → Prop
  | belowMEvenTEven : IsAllEven .belowMEvenTEven
  | boundaryEven : IsAllEven .boundaryEven
  | aboveMEvenTEven : IsAllEven .aboveMEvenTEven

/-- Exact witness for the complementary seven manuscript rows, in each of
which at least one positive-polar critical function is actually present. -/
inductive IsPositivePolar : WildQuadraticCoefficientRow → Prop
  | belowMEvenTOdd : IsPositivePolar .belowMEvenTOdd
  | belowMOddTEven : IsPositivePolar .belowMOddTEven
  | belowMOddTOdd : IsPositivePolar .belowMOddTOdd
  | boundaryOdd : IsPositivePolar .boundaryOdd
  | aboveMEvenTOdd : IsPositivePolar .aboveMEvenTOdd
  | aboveMOddTEven : IsPositivePolar .aboveMOddTEven
  | aboveMOddTOdd : IsPositivePolar .aboveMOddTOdd

/-- The ten rows split into exactly the three all-even rows and the seven
positive-polar rows. -/
theorem isAllEven_or_isPositivePolar (R : WildQuadraticCoefficientRow) :
    R.IsAllEven ∨ R.IsPositivePolar := by
  cases R with
  | belowMEvenTEven => exact Or.inl .belowMEvenTEven
  | belowMEvenTOdd => exact Or.inr .belowMEvenTOdd
  | belowMOddTEven => exact Or.inr .belowMOddTEven
  | belowMOddTOdd => exact Or.inr .belowMOddTOdd
  | boundaryEven => exact Or.inl .boundaryEven
  | boundaryOdd => exact Or.inr .boundaryOdd
  | aboveMEvenTEven => exact Or.inl .aboveMEvenTEven
  | aboveMEvenTOdd => exact Or.inr .aboveMEvenTOdd
  | aboveMOddTEven => exact Or.inr .aboveMOddTEven
  | aboveMOddTOdd => exact Or.inr .aboveMOddTOdd

/-- An exact all-even witness and an exact positive-polar witness cannot
describe the same manuscript row. -/
theorem isAllEven_isPositivePolar_disjoint
    {R : WildQuadraticCoefficientRow} (heven : R.IsAllEven)
    (hpolar : R.IsPositivePolar) : False := by
  cases heven <;> cases hpolar

theorem isPositivePolar_iff_not_isAllEven
    (R : WildQuadraticCoefficientRow) :
    R.IsPositivePolar ↔ ¬ R.IsAllEven := by
  constructor
  · intro hpolar heven
    exact isAllEven_isPositivePolar_disjoint heven hpolar
  · intro hnot
    rcases R.isAllEven_or_isPositivePolar with heven | hpolar
    · exact (hnot heven).elim
    · exact hpolar

/-- Numeric code used only to certify that the ten constructors are disjoint. -/
def code : WildQuadraticCoefficientRow → ℕ
  | .belowMEvenTEven => 0
  | .belowMEvenTOdd => 1
  | .belowMOddTEven => 2
  | .belowMOddTOdd => 3
  | .boundaryEven => 4
  | .boundaryOdd => 5
  | .aboveMEvenTEven => 6
  | .aboveMEvenTOdd => 7
  | .aboveMOddTEven => 8
  | .aboveMOddTOdd => 9

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

/-- Every row is one of the ten manuscript rows. -/
theorem exhaustive (R : WildQuadraticCoefficientRow) :
    R = .belowMEvenTEven ∨
    R = .belowMEvenTOdd ∨
    R = .belowMOddTEven ∨
    R = .belowMOddTOdd ∨
    R = .boundaryEven ∨
    R = .boundaryOdd ∨
    R = .aboveMEvenTEven ∨
    R = .aboveMEvenTOdd ∨
    R = .aboveMOddTEven ∨
    R = .aboveMOddTOdd := by
  cases R <;> simp

def range : WildQuadraticCoefficientRow → WildQuadraticRange
  | .belowMEvenTEven | .belowMEvenTOdd | .belowMOddTEven |
      .belowMOddTOdd => .below
  | .boundaryEven | .boundaryOdd => .boundary
  | .aboveMEvenTEven | .aboveMEvenTOdd | .aboveMOddTEven |
      .aboveMOddTOdd => .above

def mParity : WildQuadraticCoefficientRow → WildQuadraticConductorParity
  | .belowMEvenTEven | .belowMEvenTOdd | .aboveMEvenTEven |
      .aboveMEvenTOdd => .even
  | .belowMOddTEven | .belowMOddTOdd | .aboveMOddTEven |
      .aboveMOddTOdd => .odd
  | .boundaryEven => .even
  | .boundaryOdd => .odd

def TParity : WildQuadraticCoefficientRow → WildQuadraticConductorParity
  | .belowMEvenTEven | .belowMOddTEven | .aboveMEvenTEven |
      .aboveMOddTEven => .even
  | .belowMEvenTOdd | .belowMOddTOdd | .aboveMEvenTOdd |
      .aboveMOddTOdd => .odd
  | .boundaryEven => .even
  | .boundaryOdd => .odd

/-- Exact parity table `(e_K,e_tau,e_chi,e_{tau chi})`. -/
def characterParity (R : WildQuadraticCoefficientRow) :
    WildQuadraticCharacter → WildQuadraticConductorParity :=
  match R.range with
  | .below => fun
      | .chiK | .chiF => R.mParity
      | .tau | .tauChiF => R.TParity
  | .boundary => fun _ => R.TParity
  | .above => fun
      | .chiK | .tau => R.TParity
      | .chiF | .tauChiF => R.mParity

/-- Classification of arbitrary conductors into exactly one manuscript row. -/
def ofConductors (b t : ℕ) : WildQuadraticCoefficientRow :=
  if hlt : b < t then
    match WildQuadraticConductorParity.ofConductor (b + 1),
        WildQuadraticConductorParity.ofConductor (t + 1) with
    | .even, .even => .belowMEvenTEven
    | .even, .odd => .belowMEvenTOdd
    | .odd, .even => .belowMOddTEven
    | .odd, .odd => .belowMOddTOdd
  else if heq : b = t then
    match WildQuadraticConductorParity.ofConductor (t + 1) with
    | .even => .boundaryEven
    | .odd => .boundaryOdd
  else
    match WildQuadraticConductorParity.ofConductor (b + 1),
        WildQuadraticConductorParity.ofConductor (t + 1) with
    | .even, .even => .aboveMEvenTEven
    | .even, .odd => .aboveMEvenTOdd
    | .odd, .even => .aboveMOddTEven
    | .odd, .odd => .aboveMOddTOdd

theorem ofConductors_range_below {b t : ℕ} (h : b < t) :
    (ofConductors b t).range = .below := by
  simp only [ofConductors, h, ↓reduceDIte]
  cases WildQuadraticConductorParity.ofConductor (b + 1) <;>
    cases WildQuadraticConductorParity.ofConductor (t + 1) <;> rfl

theorem ofConductors_range_boundary {b t : ℕ} (h : b = t) :
    (ofConductors b t).range = .boundary := by
  subst t
  simp only [ofConductors, lt_self_iff_false, ↓reduceDIte]
  cases WildQuadraticConductorParity.ofConductor (b + 1) <;> rfl

theorem ofConductors_range_above {b t : ℕ} (h : t < b) :
    (ofConductors b t).range = .above := by
  have hnot : ¬ b < t := by omega
  have hne : b ≠ t := by omega
  simp only [ofConductors, hnot, hne, ↓reduceDIte]
  cases WildQuadraticConductorParity.ofConductor (b + 1) <;>
    cases WildQuadraticConductorParity.ofConductor (t + 1) <;> rfl

/-- The row classifier records exactly the parity of `m=b+1`. -/
theorem ofConductors_mParity (b t : ℕ) :
    (ofConductors b t).mParity =
      WildQuadraticConductorParity.ofConductor (b + 1) := by
  by_cases hlt : b < t
  · simp only [ofConductors, hlt, ↓reduceDIte]
    cases WildQuadraticConductorParity.ofConductor (b + 1) <;>
      cases WildQuadraticConductorParity.ofConductor (t + 1) <;> rfl
  · by_cases heq : b = t
    · subst t
      simp only [ofConductors, lt_self_iff_false, ↓reduceDIte]
      cases WildQuadraticConductorParity.ofConductor (b + 1) <;> rfl
    · simp only [ofConductors, hlt, heq, ↓reduceDIte]
      cases WildQuadraticConductorParity.ofConductor (b + 1) <;>
        cases WildQuadraticConductorParity.ofConductor (t + 1) <;> rfl

/-- The row classifier records exactly the parity of `T=t+1`. -/
theorem ofConductors_TParity (b t : ℕ) :
    (ofConductors b t).TParity =
      WildQuadraticConductorParity.ofConductor (t + 1) := by
  by_cases hlt : b < t
  · simp only [ofConductors, hlt, ↓reduceDIte]
    cases WildQuadraticConductorParity.ofConductor (b + 1) <;>
      cases WildQuadraticConductorParity.ofConductor (t + 1) <;> rfl
  · by_cases heq : b = t
    · subst t
      simp only [ofConductors, lt_self_iff_false, ↓reduceDIte]
      cases WildQuadraticConductorParity.ofConductor (b + 1) <;> rfl
    · simp only [ofConductors, hlt, heq, ↓reduceDIte]
      cases WildQuadraticConductorParity.ofConductor (b + 1) <;>
        cases WildQuadraticConductorParity.ofConductor (t + 1) <;> rfl

end WildQuadraticCoefficientRow

/-! ## Constant and odd residual factors -/

/-- An even-conductor row has no critical coefficient and contributes the
literal constant `1`; an odd row carries one normalized affine coefficient. -/
inductive WildQuadraticResidualFactor (k : Type u)
  | constant
  | critical (affine : k)

namespace WildQuadraticResidualFactor

variable {k : Type u} [Field k] [Fintype k] [CharP k 2]

def affineCoefficient : WildQuadraticResidualFactor k → Option k
  | .constant => none
  | .critical lambda => some lambda

def polarCoefficient : WildQuadraticResidualFactor k → Option k
  | .constant => none
  | .critical _ => some 1

def polarValue : WildQuadraticResidualFactor k → k
  | .constant => 0
  | .critical _ => 1

noncomputable def toFun (q : CharTwoRefinement k) :
    WildQuadraticResidualFactor k → k → ℂ
  | .constant => fun _ => 1
  | .critical lambda => WildQuadraticRefinement.criticalFunction q lambda

@[simp]
theorem toFun_constant (q : CharTwoRefinement k) (z : k) :
    toFun q (.constant : WildQuadraticResidualFactor k) z = 1 := rfl

@[simp]
theorem toFun_critical (q : CharTwoRefinement k) (lambda z : k) :
    toFun q (.critical lambda) z =
      q z * absoluteTraceChar k (lambda * z) := rfl

/-- `CriticalPolarCoordinate` bundles the coefficient with the positive
polar sign.  Constants have polar value zero; genuine odd factors have
polar value one. -/
noncomputable def criticalPolarFunction (q : CharTwoRefinement k)
    (f : WildQuadraticResidualFactor k) :
    CriticalPolarFunction k (absoluteTraceChar k) f.polarValue := by
  cases f with
  | constant =>
      exact
        { toFun := fun _ => 1
          ne_zero' := fun _ => one_ne_zero
          map_add' := by simp [polarValue] }
  | critical lambda =>
      let h := WildQuadraticRefinement.criticalFunction q lambda
      exact
        { toFun := h
          ne_zero' := h.ne_zero
          map_add' := by
            intro x y
            simpa [polarValue] using h.map_add x y }

@[simp]
theorem criticalPolarFunction_apply (q : CharTwoRefinement k)
    (f : WildQuadraticResidualFactor k) (z : k) :
    f.criticalPolarFunction q z = f.toFun q z := by
  cases f <;> rfl

/-- Common-coordinate transport by `scale` computes the polar coefficient
as `scale^2 A` through `CriticalPolarFunction.scale`. -/
noncomputable def inCoordinate (q : CharTwoRefinement k)
    (f : WildQuadraticResidualFactor k) (scale : k) :
    CriticalPolarFunction k (absoluteTraceChar k)
      (scale ^ 2 * f.polarValue) :=
  (f.criticalPolarFunction q).scale scale

@[simp]
theorem inCoordinate_apply (q : CharTwoRefinement k)
    (f : WildQuadraticResidualFactor k) (scale z : k) :
    f.inCoordinate q scale z = f.toFun q (scale * z) := by
  rw [inCoordinate, CriticalPolarFunction.scale_apply,
    criticalPolarFunction_apply]

end WildQuadraticResidualFactor

/-! ## The ten coefficient-data constructors -/

/-- Coefficient data for exactly one manuscript row.  Constructors contain
only coefficients that exist in that row. -/
inductive WildQuadraticCoefficientData (k : Type u) [Field k]
  | belowMEvenTEven
  | belowMEvenTOdd (gamma0 : k)
  | belowMOddTEven (gamma gammaPrime : k)
      (gammaPrime_sq : gammaPrime ^ 2 = gamma)
  | belowMOddTOdd (gamma0 gamma gammaPrime : k)
      (gammaPrime_sq : gammaPrime ^ 2 = gamma)
  | boundaryEven
  | boundaryOdd (rho r gamma0 gamma gammaPrime : k)
      (rho_ne_zero : rho ≠ 0)
      (r_sq : r ^ 2 = rho)
      (denominator_ne_zero : 1 + rho ≠ 0)
      (gammaPrime_sq : gammaPrime ^ 2 =
        (gamma + rho * gamma0 + rho + r) / (1 + rho))
  | aboveMEvenTEven
  | aboveMEvenTOdd (gamma0 gammaPrime : k)
      (gammaPrime_sq : gammaPrime ^ 2 = 1 + gamma0)
  | aboveMOddTEven (gamma : k)
  | aboveMOddTOdd (gamma0 gamma gammaPrime : k)
      (gammaPrime_sq : gammaPrime ^ 2 = 1 + gamma0)

namespace WildQuadraticCoefficientData

variable {k : Type u} [Field k]

def row : WildQuadraticCoefficientData k → WildQuadraticCoefficientRow
  | .belowMEvenTEven => .belowMEvenTEven
  | .belowMEvenTOdd _ => .belowMEvenTOdd
  | .belowMOddTEven _ _ _ => .belowMOddTEven
  | .belowMOddTOdd _ _ _ _ => .belowMOddTOdd
  | .boundaryEven => .boundaryEven
  | .boundaryOdd _ _ _ _ _ _ _ _ _ => .boundaryOdd
  | .aboveMEvenTEven => .aboveMEvenTEven
  | .aboveMEvenTOdd _ _ _ => .aboveMEvenTOdd
  | .aboveMOddTEven _ => .aboveMOddTEven
  | .aboveMOddTOdd _ _ _ _ => .aboveMOddTOdd

/-- The intrinsic normalized affine coefficient of each character; `none`
means that its conductor is even and its factor is literally constant. -/
def affineCoefficient (D : WildQuadraticCoefficientData k) :
    WildQuadraticCharacter → Option k := by
  cases D with
  | belowMEvenTEven | boundaryEven | aboveMEvenTEven =>
      exact fun _ => none
  | belowMEvenTOdd gamma0 =>
      exact fun
        | .tau | .tauChiF => some gamma0
        | .chiK | .chiF => none
  | belowMOddTEven gamma gammaPrime _ =>
      exact fun
        | .chiK => some gammaPrime
        | .chiF => some gamma
        | .tau | .tauChiF => none
  | belowMOddTOdd gamma0 gamma gammaPrime _ =>
      exact fun
        | .chiK => some gammaPrime
        | .tau => some gamma0
        | .chiF => some gamma
        | .tauChiF => some gamma0
  | boundaryOdd rho r gamma0 gamma gammaPrime _ _ _ _ =>
      exact fun
        | .chiK => some gammaPrime
        | .tau => some gamma0
        | .chiF => some gamma
        | .tauChiF => some ((gamma0 + rho * gamma + r) / (1 + rho))
  | aboveMEvenTOdd gamma0 gammaPrime _ =>
      exact fun
        | .chiK => some gammaPrime
        | .tau => some gamma0
        | .chiF | .tauChiF => none
  | aboveMOddTEven gamma =>
      exact fun
        | .chiF | .tauChiF => some gamma
        | .chiK | .tau => none
  | aboveMOddTOdd gamma0 gamma gammaPrime _ =>
      exact fun
        | .chiK => some gammaPrime
        | .tau => some gamma0
        | .chiF | .tauChiF => some gamma

def factor (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) : WildQuadraticResidualFactor k :=
  match D.affineCoefficient theta with
  | none => .constant
  | some lambda => .critical lambda

/-- Scale from each normalized critical coordinate to the common displayed
residue coordinate.  Boundary scales retain `rho`, `1+rho`, and its explicit
square root `1+r`; all nonboundary scales are one. -/
def commonScale (D : WildQuadraticCoefficientData k) :
    WildQuadraticCharacter → k := by
  cases D with
  | boundaryOdd rho r _ _ _ _ _ _ _ =>
      exact fun
        | .chiK => 1 + r
        | .tau => 1
        | .chiF => rho
        | .tauChiF => 1 + rho
  | _ => exact fun _ => 1

/-- Every manuscript common-coordinate scale is nonzero.  At the odd
boundary the upper scale is `1+r`; its square is `1+rho`, so the retained
denominator hypothesis rules out its vanishing. -/
theorem commonScale_ne_zero_from_row [CharP k 2]
    (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) :
    D.commonScale theta ≠ 0 := by
  cases D with
  | boundaryOdd rho r gamma0 gamma gammaPrime hrho hrsq hden hgamma =>
      cases theta with
      | chiK =>
          simp only [commonScale]
          intro hr
          apply hden
          calc
            1 + rho = (1 + r) ^ 2 := by
              rw [← hrsq]
              have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
              have hexpand : (1 + r) ^ 2 = 1 + (2 : k) * r + r ^ 2 := by
                ring
              rw [hexpand, htwo]
              simp
            _ = 0 := by rw [hr]; simp
      | tau => simp [commonScale]
      | chiF => simpa [commonScale] using hrho
      | tauChiF => simpa [commonScale] using hden
  | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven |
      belowMOddTOdd | boundaryEven | aboveMEvenTEven | aboveMEvenTOdd |
      aboveMOddTEven | aboveMOddTOdd =>
      simp [commonScale]

def commonPolarCoefficient (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) : Option k :=
  (D.affineCoefficient theta).map (fun _ => (D.commonScale theta) ^ 2)

def commonAffineCoefficient (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) : Option k :=
  (D.affineCoefficient theta).map (fun lambda =>
    D.commonScale theta * lambda)

/-- The raw upper affine coefficient before Frobenius; it is absent exactly
when the upper conductor is even. -/
def rawUpperAffineCoefficient : WildQuadraticCoefficientData k → Option k
  | .belowMEvenTEven | .belowMEvenTOdd _ => none
  | .belowMOddTEven gamma _ _ | .belowMOddTOdd _ gamma _ _ => some gamma
  | .boundaryEven => none
  | .boundaryOdd rho r gamma0 gamma _ _ _ _ _ =>
      some ((gamma + rho * gamma0 + rho + r) / (1 + rho))
  | .aboveMEvenTEven | .aboveMOddTEven _ => none
  | .aboveMEvenTOdd gamma0 _ _ | .aboveMOddTOdd gamma0 _ _ _ =>
      some (1 + gamma0)

def rawUpperScale : WildQuadraticCoefficientData k → k
  | .boundaryOdd rho _ _ _ _ _ _ _ _ => 1 + rho
  | _ => 1

/-- The raw upper transport scale is nonzero in every row by the hypotheses
retained in the row constructor. -/
theorem rawUpperScale_ne_zero_from_row
    (D : WildQuadraticCoefficientData k) :
    D.rawUpperScale ≠ 0 := by
  cases D <;> simp_all [rawUpperScale]

/-- Polar coefficient of the raw upper function after transport to its
displayed common coordinate. -/
def rawUpperCommonPolarCoefficient (D : WildQuadraticCoefficientData k) :
    Option k :=
  D.rawUpperAffineCoefficient.map (fun _ => D.rawUpperScale ^ 2)

/-- Affine coefficient of the raw upper function after transport to its
displayed common coordinate. -/
def rawUpperCommonAffineCoefficient (D : WildQuadraticCoefficientData k) :
    Option k :=
  D.rawUpperAffineCoefficient.map (fun lambda => D.rawUpperScale * lambda)

def rawUpperFactor (D : WildQuadraticCoefficientData k) :
    WildQuadraticResidualFactor k :=
  match D.rawUpperAffineCoefficient with
  | none => .constant
  | some lambda => .critical lambda

@[simp]
theorem factor_affineCoefficient (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) :
    (D.factor theta).affineCoefficient = D.affineCoefficient theta := by
  simp [factor]
  split <;> simp_all [WildQuadraticResidualFactor.affineCoefficient]

theorem coefficient_exists_iff_odd (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) :
    (D.affineCoefficient theta).isSome =
      decide (D.row.characterParity theta = .odd) := by
  cases D <;> cases theta <;>
    simp [affineCoefficient, row, WildQuadraticCoefficientRow.characterParity,
      WildQuadraticCoefficientRow.range, WildQuadraticCoefficientRow.mParity,
      WildQuadraticCoefficientRow.TParity]

def range (D : WildQuadraticCoefficientData k) : WildQuadraticRange :=
  D.row.range

/-- Exact lower affine entry in each of the three conductor ranges. -/
def expectedTauChiCoefficient (D : WildQuadraticCoefficientData k) : Option k :=
  match D.range with
  | .below => D.affineCoefficient .tau
  | .above => D.affineCoefficient .chiF
  | .boundary => D.affineCoefficient .tauChiF

theorem tauChiCoefficient_table (D : WildQuadraticCoefficientData k) :
    D.affineCoefficient .tauChiF = D.expectedTauChiCoefficient := by
  cases D <;> rfl

/-- The upper normalized affine coefficient is the unique square root of
the raw coefficient, in every row where the upper factor exists. -/
theorem chiKCoefficient_sq (D : WildQuadraticCoefficientData k) :
    (D.affineCoefficient .chiK).map (fun gammaPrime => gammaPrime ^ 2) =
      D.rawUpperAffineCoefficient := by
  cases D <;> simp_all [affineCoefficient, rawUpperAffineCoefficient]

section ComputedSquareRoots

variable [Fintype k] [CharP k 2]

/-- The below-break odd/even row with its normalized upper coefficient
computed by the unique characteristic-two square root. -/
noncomputable def belowMOddTEvenComputed (gamma : k) :
    WildQuadraticCoefficientData k :=
  .belowMOddTEven gamma (WildQuadraticRefinement.squareRoot gamma)
    (WildQuadraticRefinement.squareRoot_sq gamma)

/-- The below-break odd/odd row with its normalized upper coefficient
computed by the unique characteristic-two square root. -/
noncomputable def belowMOddTOddComputed (gamma0 gamma : k) :
    WildQuadraticCoefficientData k :=
  .belowMOddTOdd gamma0 gamma (WildQuadraticRefinement.squareRoot gamma)
    (WildQuadraticRefinement.squareRoot_sq gamma)

/-- The odd boundary row with both square roots computed in the common
residue field.  The nonzero hypotheses and the denominator remain explicit. -/
noncomputable def boundaryOddComputed (rho gamma0 gamma : k)
    (rho_ne_zero : rho ≠ 0) (denominator_ne_zero : 1 + rho ≠ 0) :
    WildQuadraticCoefficientData k :=
  let r := WildQuadraticRefinement.squareRoot rho
  let L := (gamma + rho * gamma0 + rho + r) / (1 + rho)
  .boundaryOdd rho r gamma0 gamma
    (WildQuadraticRefinement.squareRoot L) rho_ne_zero
    (WildQuadraticRefinement.squareRoot_sq rho) denominator_ne_zero
    (WildQuadraticRefinement.squareRoot_sq L)

/-- The above-break even/odd row with its normalized upper coefficient
computed by the unique characteristic-two square root. -/
noncomputable def aboveMEvenTOddComputed (gamma0 : k) :
    WildQuadraticCoefficientData k :=
  .aboveMEvenTOdd gamma0 (WildQuadraticRefinement.squareRoot (1 + gamma0))
    (WildQuadraticRefinement.squareRoot_sq (1 + gamma0))

/-- The above-break odd/odd row with its normalized upper coefficient
computed by the unique characteristic-two square root. -/
noncomputable def aboveMOddTOddComputed (gamma0 gamma : k) :
    WildQuadraticCoefficientData k :=
  .aboveMOddTOdd gamma0 gamma
    (WildQuadraticRefinement.squareRoot (1 + gamma0))
    (WildQuadraticRefinement.squareRoot_sq (1 + gamma0))

/-- Every proof-bearing table row uses the same unique square root as the
computed constructors; there is no additional normalized-upper choice. -/
theorem chiKCoefficient_eq_squareRoot (D : WildQuadraticCoefficientData k) :
    D.affineCoefficient .chiK =
      D.rawUpperAffineCoefficient.map WildQuadraticRefinement.squareRoot := by
  cases D with
  | belowMEvenTEven | belowMEvenTOdd | boundaryEven |
      aboveMEvenTEven | aboveMOddTEven => rfl
  | belowMOddTEven gamma gammaPrime hs
  | belowMOddTOdd _ gamma gammaPrime hs =>
      exact congrArg some
        (WildQuadraticRefinement.squareRoot_unique gamma gammaPrime hs)
  | boundaryOdd rho r gamma0 gamma gammaPrime _ _ _ hs =>
      exact congrArg some (WildQuadraticRefinement.squareRoot_unique
        ((gamma + rho * gamma0 + rho + r) / (1 + rho)) gammaPrime hs)
  | aboveMEvenTOdd gamma0 gammaPrime hs
  | aboveMOddTOdd gamma0 _ gammaPrime hs =>
      exact congrArg some (WildQuadraticRefinement.squareRoot_unique
        (1 + gamma0) gammaPrime hs)

end ComputedSquareRoots

/-- The boundary row written in the manuscript's common residue coordinate.
The lower affine coefficient is the normalized quotient by `1+rho`, whereas
its transported coefficient has that denominator cancelled.  The raw upper
coefficient keeps its distinct numerator phase. -/
theorem boundaryOdd_coefficient_table
    (rho r gamma0 gamma gammaPrime : k)
    (rho_ne_zero : rho ≠ 0) (r_sq : r ^ 2 = rho)
    (denominator_ne_zero : 1 + rho ≠ 0)
    (gammaPrime_sq : gammaPrime ^ 2 =
      (gamma + rho * gamma0 + rho + r) / (1 + rho)) :
    let D := WildQuadraticCoefficientData.boundaryOdd rho r gamma0 gamma
      gammaPrime rho_ne_zero r_sq denominator_ne_zero gammaPrime_sq
    D.commonPolarCoefficient .chiK = some ((1 + r) ^ 2) ∧
    D.commonAffineCoefficient .chiK = some ((1 + r) * gammaPrime) ∧
    D.commonPolarCoefficient .tau = some 1 ∧
    D.commonAffineCoefficient .tau = some gamma0 ∧
    D.commonPolarCoefficient .chiF = some (rho ^ 2) ∧
    D.commonAffineCoefficient .chiF = some (rho * gamma) ∧
    D.affineCoefficient .tauChiF =
      some ((gamma0 + rho * gamma + r) / (1 + rho)) ∧
    D.commonPolarCoefficient .tauChiF = some ((1 + rho) ^ 2) ∧
    D.commonAffineCoefficient .tauChiF =
      some (gamma0 + rho * gamma + r) ∧
    D.rawUpperAffineCoefficient =
      some ((gamma + rho * gamma0 + rho + r) / (1 + rho)) ∧
    D.rawUpperCommonPolarCoefficient = some ((1 + rho) ^ 2) ∧
    D.rawUpperCommonAffineCoefficient =
      some (gamma + rho * gamma0 + rho + r) ∧
    D.affineCoefficient .chiK = some gammaPrime := by
  dsimp only [commonPolarCoefficient, commonAffineCoefficient,
    affineCoefficient, commonScale, rawUpperAffineCoefficient,
    rawUpperCommonPolarCoefficient, rawUpperCommonAffineCoefficient,
    rawUpperScale]
  simp only [Option.map_some, one_pow, true_and]
  field_simp [denominator_ne_zero] <;> simp

section Functions

variable [Fintype k] [CharP k 2]

noncomputable def function (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter) :
    k → ℂ :=
  (D.factor theta).toFun q

noncomputable def commonFunction (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter) :
    k → ℂ :=
  fun z => D.function q theta (D.commonScale theta * z)

noncomputable def rawUpperFunction (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) : k → ℂ :=
  fun z => D.rawUpperFactor.toFun q (D.rawUpperScale * z)

@[simp]
theorem function_eq_one_of_even (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    (h : D.affineCoefficient theta = none) (z : k) :
    D.function q theta z = 1 := by
  simp [function, factor, h]

theorem function_eq_critical_of_odd (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    {lambda : k} (h : D.affineCoefficient theta = some lambda) (z : k) :
    D.function q theta z =
      WildQuadraticRefinement.criticalFunction q lambda z := by
  simp [function, factor, h, WildQuadraticResidualFactor.toFun]

theorem commonFunction_eq_affine_of_odd (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    {lambda : k} (h : D.affineCoefficient theta = some lambda) (z : k) :
    D.commonFunction q theta z =
      q (D.commonScale theta * z) *
        absoluteTraceChar k
          ((D.commonScale theta * lambda) * z) := by
  rw [commonFunction, function_eq_critical_of_odd q D theta h,
    WildQuadraticRefinement.criticalFunction_apply]
  congr 2
  ring

/-- Common-coordinate positive-polar function.  Its type records the
coefficient computed by `CriticalPolarFunction.scale`. -/
noncomputable def commonCriticalPolarFunction (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter) :
    CriticalPolarFunction k (absoluteTraceChar k)
      ((D.commonScale theta) ^ 2 * (D.factor theta).polarValue) :=
  (D.factor theta).inCoordinate q (D.commonScale theta)

@[simp]
theorem commonCriticalPolarFunction_apply (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    (z : k) :
    D.commonCriticalPolarFunction q theta z =
      D.commonFunction q theta z := by
  rw [commonCriticalPolarFunction,
    WildQuadraticResidualFactor.inCoordinate_apply]
  rfl

/-- Exact positive sign with every odd common-coordinate polar coefficient
computed by `CriticalPolarCoordinate`. -/
theorem commonFunction_positivePolar (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    (x y : k) :
    D.commonFunction q theta (x + y) =
      D.commonFunction q theta x * D.commonFunction q theta y *
        absoluteTraceChar k
          (((D.commonScale theta) ^ 2 * (D.factor theta).polarValue) *
            (x * y)) := by
  simpa only [commonCriticalPolarFunction_apply] using
    (D.commonCriticalPolarFunction q theta).map_add x y

/-- Replacing a stationary representative does not change the polar
coefficient.  If `a` is the representative-translation parameter, the
affine coefficient changes in the exact direction `B ↦ B + A*a`. -/
noncomputable def representativeTranslate (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    (a : k) :
    CriticalPolarFunction k (absoluteTraceChar k)
      ((D.commonScale theta) ^ 2 * (D.factor theta).polarValue) :=
  (D.commonCriticalPolarFunction q theta).translate
    (((D.commonScale theta) ^ 2 * (D.factor theta).polarValue) * a)

theorem representativeTranslate_apply (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter)
    (a z : k) :
    D.representativeTranslate q theta a z =
      D.commonFunction q theta z *
        absoluteTraceChar k
          ((((D.commonScale theta) ^ 2 *
            (D.factor theta).polarValue) * a) * z) := by
  rw [representativeTranslate, CriticalPolarFunction.translate_apply,
    commonCriticalPolarFunction_apply]

theorem representativeTranslate_eq_affine_of_odd
    (q : CharTwoRefinement k) (D : WildQuadraticCoefficientData k)
    (theta : WildQuadraticCharacter) {lambda : k}
    (h : D.affineCoefficient theta = some lambda) (a z : k) :
    D.representativeTranslate q theta a z =
      q (D.commonScale theta * z) *
        absoluteTraceChar k
          (((D.commonScale theta * lambda) +
            (D.commonScale theta) ^ 2 * a) * z) := by
  rw [representativeTranslate_apply,
    commonFunction_eq_affine_of_odd q D theta h]
  rw [mul_assoc, ← AddChar.map_add_eq_mul]
  congr 1
  have hpolar : (D.factor theta).polarValue = 1 := by
    simp [factor, h, WildQuadraticResidualFactor.polarValue]
  rw [hpolar]
  ring

/-- Changing to the other Frobenius-normalized refinement shifts every
existing intrinsic affine coefficient by `+1`, leaving the function itself
unchanged.  Constants remain constants. -/
def secondNormalizedFactor : WildQuadraticResidualFactor k →
    WildQuadraticResidualFactor k
  | .constant => .constant
  | .critical lambda => .critical (lambda + 1)

theorem secondNormalizedFactor_function (q : CharTwoRefinement k)
    (f : WildQuadraticResidualFactor k) (z : k) :
    (secondNormalizedFactor f).toFun
        (WildQuadraticRefinement.secondNormalized q) z =
      f.toFun q z := by
  cases f with
  | constant => rfl
  | critical lambda =>
      exact DFunLike.congr_fun
        (WildQuadraticRefinement.secondNormalized_criticalFunction q lambda) z

/-- The raw phase quotient keeps `chiK,tau` in the numerator and
`chiF,tauChiF` in the denominator, with even entries equal to one. -/
noncomputable def phaseFactor (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter) : ℂ :=
  match D.affineCoefficient theta with
  | none => 1
  | some lambda => WildQuadraticRefinement.phase q lambda

noncomputable def phaseRatio (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) : ℂ :=
  D.phaseFactor q .chiK * D.phaseFactor q .tau /
    (D.phaseFactor q .chiF * D.phaseFactor q .tauChiF)

/-! ### Exact residue transports -/

theorem rawUpper_below (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (h : D.range = .below) (z : k) :
    D.rawUpperFunction q z = D.function q .chiF z := by
  cases D <;>
    simp_all [range, row, WildQuadraticCoefficientRow.range,
      rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
      rawUpperScale, function, factor, affineCoefficient]

theorem criticalFunction_one_add (q : CharTwoRefinement k)
    (lambda z : k) :
    WildQuadraticRefinement.criticalFunction q (1 + lambda) z =
      WildQuadraticRefinement.criticalFunction q lambda z *
        absoluteTraceChar k z := by
  simp only [WildQuadraticRefinement.criticalFunction_apply]
  calc
    q z * absoluteTraceChar k ((1 + lambda) * z) =
        q z * absoluteTraceChar k (lambda * z + z) := by
      congr 2
      ring
    _ = q z *
        (absoluteTraceChar k (lambda * z) * absoluteTraceChar k z) := by
      rw [AddChar.map_add_eq_mul]
    _ = (q z * absoluteTraceChar k (lambda * z)) *
        absoluteTraceChar k z := by ring

theorem rawUpper_above (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (h : D.range = .above) (z : k) :
    D.rawUpperFunction q z =
      if D.row.TParity = .odd then
        D.function q .tau z * absoluteTraceChar k z
      else D.function q .tau z := by
  cases D with
  | belowMEvenTEven =>
      simp [range, row, WildQuadraticCoefficientRow.range] at h
  | belowMEvenTOdd gamma0 =>
      simp [range, row, WildQuadraticCoefficientRow.range] at h
  | belowMOddTEven gamma gammaPrime hs =>
      simp [range, row, WildQuadraticCoefficientRow.range] at h
  | belowMOddTOdd gamma0 gamma gammaPrime hs =>
      simp [range, row, WildQuadraticCoefficientRow.range] at h
  | boundaryEven =>
      simp [range, row, WildQuadraticCoefficientRow.range] at h
  | boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs =>
      simp [range, row, WildQuadraticCoefficientRow.range] at h
  | aboveMEvenTEven => rfl
  | aboveMOddTEven gamma => rfl
  | aboveMEvenTOdd gamma0 gammaPrime hs =>
      simpa only [rawUpperFunction, rawUpperFactor,
        rawUpperAffineCoefficient, rawUpperScale, one_mul, function, factor,
        affineCoefficient, row, WildQuadraticCoefficientRow.TParity,
        WildQuadraticResidualFactor.toFun, if_pos rfl, if_true] using
          criticalFunction_one_add q gamma0 z
  | aboveMOddTOdd gamma0 gamma gammaPrime hs =>
      simpa only [rawUpperFunction, rawUpperFactor,
        rawUpperAffineCoefficient, rawUpperScale, one_mul, function, factor,
        affineCoefficient, row, WildQuadraticCoefficientRow.TParity,
        WildQuadraticResidualFactor.toFun, if_pos rfl, if_true] using
          criticalFunction_one_add q gamma0 z

theorem boundaryLower_transport (q : CharTwoRefinement k)
    (rho r gamma0 gamma gammaPrime : k) (hrho : rho ≠ 0)
    (hr : r ^ 2 = rho) (hden : 1 + rho ≠ 0)
    (hgammaPrime : gammaPrime ^ 2 =
      (gamma + rho * gamma0 + rho + r) / (1 + rho)) (z : k) :
    let D : WildQuadraticCoefficientData k :=
      .boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hgammaPrime
    D.commonFunction q .tau z * D.commonFunction q .chiF z =
      D.commonFunction q .tauChiF z := by
  dsimp only [commonFunction, function, factor, affineCoefficient, commonScale,
    WildQuadraticResidualFactor.toFun]
  simpa only [one_mul, WildQuadraticRefinement.boundaryLowerProduct] using
    WildQuadraticRefinement.boundaryLowerProduct_eq_affine
      q rho r gamma0 gamma z hr hden

theorem rawUpper_boundary (q : CharTwoRefinement k)
    (rho r gamma0 gamma gammaPrime : k) (hrho : rho ≠ 0)
    (hr : r ^ 2 = rho) (hden : 1 + rho ≠ 0)
    (hgammaPrime : gammaPrime ^ 2 =
      (gamma + rho * gamma0 + rho + r) / (1 + rho)) (z : k) :
    let D : WildQuadraticCoefficientData k :=
      .boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hgammaPrime
    D.rawUpperFunction q z =
      WildQuadraticRefinement.rawUpperBoundary q rho gamma0 gamma z := by
  dsimp only [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
    rawUpperScale, WildQuadraticResidualFactor.toFun]
  exact (WildQuadraticRefinement.rawUpperBoundary_eq_affine
    q rho r gamma0 gamma z hr hden).symm

/-- The normalized upper function is obtained from the raw function by
precomposition with Frobenius in every one of the ten rows. -/
theorem rawUpper_frobenius (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (z : k) :
    D.rawUpperFunction q (z ^ 2) = D.commonFunction q .chiK z := by
  cases D with
  | belowMEvenTEven | belowMEvenTOdd | boundaryEven |
      aboveMEvenTEven | aboveMOddTEven => rfl
  | belowMOddTEven gamma gammaPrime hs
  | belowMOddTOdd _ gamma gammaPrime hs
  | aboveMEvenTOdd _ gammaPrime hs
  | aboveMOddTOdd _ _ gammaPrime hs =>
      simpa [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, commonFunction, function, factor, affineCoefficient,
        commonScale, WildQuadraticResidualFactor.toFun] using
          WildQuadraticRefinement.criticalFunction_frobenius_of_sq
            q hs z
  | boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs =>
      rw [rawUpper_boundary q rho r gamma0 gamma gammaPrime hrho hr hden hs]
      rw [WildQuadraticRefinement.rawUpperBoundary_eq_affine
        q rho r gamma0 gamma (z ^ 2) hr hden]
      have hscale : (1 + r) ^ 2 = 1 + rho := by
        rw [CharTwo.add_sq, one_pow, hr]
      have harg : (1 + rho) * z ^ 2 = ((1 + r) * z) ^ 2 := by
        rw [mul_pow, hscale]
      rw [harg,
        WildQuadraticRefinement.criticalFunction_frobenius_of_sq q hs]
      rfl

end Functions

end WildQuadraticCoefficientData

/-! ## Choice-relative stationary numerator/denominator packages -/

/-- One selected Lamprecht denominator and stationary numerator. -/
structure WildQuadraticStationaryPair (E : Type*) [Field E] where
  gamma : Eˣ
  beta : E

namespace WildQuadraticStationaryPair

variable {E : Type*} [Field E]

def ratio (P : WildQuadraticStationaryPair E) : E :=
  P.beta / (P.gamma : E)

end WildQuadraticStationaryPair

/-- The complete stationary factor on a field-level unit, before passage to
a residual critical coordinate.  The selected numerator and denominator
remain visible through `P.ratio`, and the multiplicative character occurs
with the inverse convention of Lamprecht's odd critical function. -/
noncomputable def stationaryUnitFactor
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (theta : ContinuousQuasiChar E) (psi : LocalAddCharData E)
    (P : WildQuadraticStationaryPair E) (v : Eˣ) : ℂ :=
  (psi.character (P.ratio * ((v : E) - 1)) : ℂ) *
    (theta v : ℂ)⁻¹

/-- The four selected pairs in the exact numerator/denominator orientation
used by the quadratic stationary quotient. -/
structure WildQuadraticSelectedStationaryPairs
    (F K : Type*) [Field F] [Field K] where
  chiK : WildQuadraticStationaryPair K
  tau : WildQuadraticStationaryPair F
  chiF : WildQuadraticStationaryPair F
  tauChiF : WildQuadraticStationaryPair F

section StationaryFactorCalculus

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Multiplication of actual characters and addition of their exact selected
stationary ratios multiply the complete field-level stationary factors. -/
theorem stationaryUnitFactor_mul
    (theta₁ theta₂ theta₁₂ : ContinuousQuasiChar E)
    (psi : LocalAddCharData E)
    (P₁ P₂ P₁₂ : WildQuadraticStationaryPair E)
    (htheta : theta₁₂ = theta₁ * theta₂)
    (hratio : P₁₂.ratio = P₁.ratio + P₂.ratio)
    (v : Eˣ) :
    stationaryUnitFactor theta₁₂ psi P₁₂ v =
      stationaryUnitFactor theta₁ psi P₁ v *
        stationaryUnitFactor theta₂ psi P₂ v := by
  subst theta₁₂
  unfold stationaryUnitFactor
  rw [hratio, add_mul, ContinuousAddChar.map_add_eq_mul,
    ContinuousQuasiChar.mul_apply]
  push_cast
  field_simp [ContinuousQuasiChar.apply_ne_zero theta₁ v,
    ContinuousQuasiChar.apply_ne_zero theta₂ v]

end StationaryFactorCalculus

section UpperNormStationaryFactor

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- Exact field-level norm transport before characteristic-two inversion.
For units `v=1+x` and `vu=1+u*x`, the selected upper factor is the selected
downstairs `chiF` factor times the inverse selected `tau` factor.  This is
derived only from the pullback characters, the three selected ratios, the
quadratic norm polynomial, and triviality of `tau` on norms; no residual
coefficient or critical-function equality is assumed. -/
theorem stationaryUnitFactor_compNorm_exact
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tau : NormCharacter F K)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hchiKRatio : S.chiK.ratio =
      algebraMap F K S.tau.ratio *
        (algebraMap F K (C.n : F) - (C.u : K)))
    (hchiFRatio : S.chiF.ratio = S.tau.ratio * (C.n : F))
    (v vu : Kˣ) (x : K)
    (hv : (v : K) = 1 + x)
    (hvu : (vu : K) = 1 + (C.u : K) * x) :
    stationaryUnitFactor chiK.character psiK S.chiK v =
      stationaryUnitFactor chiF.character psiF S.chiF (normUnits F K v) *
        (stationaryUnitFactor tau.1 psiF S.tau
          (normUnits F K vu))⁻¹ := by
  have hnormu : norm F K (C.u : K) = (C.n : F) := C.norm_u_field
  have hnormx : norm F K ((C.u : K) * x) =
      (C.n : F) * norm F K x := by
    rw [map_mul, hnormu]
  have hp : (normUnits F K v : F) - 1 =
      trace F K x + norm F K x := by
    have h := wildQuadratic_normPolynomialValue_eq_trace_add_norm
      F K C.degree_eq_two x
    rw [normPolynomialValue] at h
    rw [coe_normUnits, hv]
    linear_combination h
  have hq : (normUnits F K vu : F) - 1 =
      trace F K ((C.u : K) * x) + (C.n : F) * norm F K x := by
    have h := wildQuadratic_normPolynomialValue_eq_trace_add_norm
      F K C.degree_eq_two ((C.u : K) * x)
    rw [normPolynomialValue, hnormx] at h
    rw [coe_normUnits, hvu]
    linear_combination h
  have htraceScalar (a : F) (y : K) :
      trace F K (algebraMap F K a * y) = a * trace F K y := by
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul a y
  have htraceArg :
      trace F K (S.chiK.ratio * ((v : K) - 1)) =
        S.chiF.ratio * ((normUnits F K v : F) - 1) -
          S.tau.ratio * ((normUnits F K vu : F) - 1) := by
    rw [hv, add_sub_cancel_left, hchiKRatio, hchiFRatio, hp, hq]
    rw [show algebraMap F K S.tau.ratio *
          (algebraMap F K (C.n : F) - (C.u : K)) * x =
        algebraMap F K S.tau.ratio *
          (algebraMap F K (C.n : F) * x - (C.u : K) * x) by ring]
    rw [htraceScalar, map_sub, htraceScalar]
    ring
  have htauNorm : tau.1 (normUnits F K vu) = 1 :=
    tau.eq_one_on_normRange F K (normUnits F K vu) ⟨vu, rfl⟩
  have htauNormC : ((tau.1 (normUnits F K vu) : ℂˣ) : ℂ) = 1 := by
    exact congrArg Units.val htauNorm
  have hpsiSub :
      ((psiF.character
          (S.chiF.ratio * ((normUnits F K v : F) - 1) -
            S.tau.ratio * ((normUnits F K vu : F) - 1)) : ℂˣ) : ℂ) =
        (psiF.character
            (S.chiF.ratio * ((normUnits F K v : F) - 1)) : ℂ) /
          (psiF.character
            (S.tau.ratio * ((normUnits F K vu : F) - 1)) : ℂ) := by
    simpa only [ContinuousAddChar.toAddChar_apply, div_eq_mul_inv,
      Units.val_mul, Units.val_inv_eq_inv_val] using
      congrArg Units.val
        (psiF.character.toAddChar.map_sub_eq_div
          (S.chiF.ratio * ((normUnits F K v : F) - 1))
          (S.tau.ratio * ((normUnits F K vu : F) - 1)))
  rw [stationaryUnitFactor, stationaryUnitFactor, stationaryUnitFactor]
  rw [hchi, ContinuousQuasiChar.compNorm_apply]
  rw [hpsi, ContinuousAddChar.compTrace_apply]
  rw [htraceArg]
  change
    ((psiF.character
        (S.chiF.ratio * ((normUnits F K v : F) - 1) -
          S.tau.ratio * ((normUnits F K vu : F) - 1)) : ℂˣ) : ℂ) *
        ((chiF.character (normUnits F K v) : ℂˣ) : ℂ)⁻¹ = _
  rw [hpsiSub, htauNormC]
  simp only [inv_one, mul_one]
  field_simp [ContinuousAddChar.apply_ne_zero psiF.character _,
    ContinuousQuasiChar.apply_ne_zero chiF.character (normUnits F K v)]

end UpperNormStationaryFactor

section LowSelectedStationaryPairs

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

/-- The exact low four-pair package made from the supplied simultaneous pair
`P`.  In particular, `P.alpha₁`, `P.beta₁`, and `epsilon₁` remain the
selected representatives; no quotient class is given a canonical lift. -/
noncomputable def lowWildQuadraticSelectedStationaryPairs
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (delta : Fˣ) (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    WildQuadraticSelectedStationaryPairs F K where
  chiK :=
    { gamma := lowGammaK F K delta epsilon1
      beta := lowUpstairsCandidate F K epsilon1 P }
  tau :=
    { gamma := delta / P.alpha
      beta := 1 }
  chiF :=
    { gamma := lowGammaF F K delta epsilon1
      beta := (P.beta : F) }
  tauChiF :=
    { gamma := delta
      beta := (P.alpha : F) +
        (lowEpsilon F K epsilon1 : F) * (P.beta : F) }

theorem lowWildQuadraticSelectedStationaryPairs_exact
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (delta : Fˣ) (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    let S := lowWildQuadraticSelectedStationaryPairs delta epsilon1 P
    let u : K := lowNormalizedRatio F K epsilon1 P
    let n : F := (lowEpsilon F K epsilon1 : F) * (P.beta : F) /
      (P.alpha : F)
    S.chiK.beta =
        (algebraMap F K (P.alpha : F) / (epsilon1 : K)) *
          (algebraMap F K n - u) ∧
    S.tau.gamma = delta / P.alpha ∧ S.tau.beta = 1 ∧
    S.chiF.gamma = delta / lowEpsilon F K epsilon1 ∧
    S.chiF.beta = (P.alpha : F) /
        (lowEpsilon F K epsilon1 : F) * n ∧
    S.tauChiF.gamma = delta ∧
    S.tauChiF.beta = (P.alpha : F) * (n + 1) := by
  dsimp only [lowWildQuadraticSelectedStationaryPairs]
  constructor
  · rw [lowUpstairsCandidate_eq_normalized]
    rw [lowNormalizedUpstairsCandidate, lowNormalizedRatio_norm]
  · refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
    · field_simp [Units.ne_zero P.alpha,
        Units.ne_zero (lowEpsilon F K epsilon1)]
    · field_simp [Units.ne_zero P.alpha]
      ring

theorem lowWildQuadraticSelectedStationaryPairs_ratios
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {betaClass : StationaryCoefficientQuotient F d}
    (delta : Fˣ) (epsilon1 : Kˣ)
    (P : LowStationaryNormRepresentativePair F K r d
      alphaClass betaClass) :
    let S := lowWildQuadraticSelectedStationaryPairs delta epsilon1 P
    let A : F := (P.alpha : F) / (delta : F)
    let u : K := lowNormalizedRatio F K epsilon1 P
    let n : F := (lowEpsilon F K epsilon1 : F) * (P.beta : F) /
      (P.alpha : F)
    S.chiK.ratio = algebraMap F K A * (algebraMap F K n - u) ∧
    S.tau.ratio = A ∧
    S.chiF.ratio = A * n ∧
    S.tauChiF.ratio = A * (n + 1) := by
  dsimp only [lowWildQuadraticSelectedStationaryPairs,
    WildQuadraticStationaryPair.ratio, lowGammaK, lowGammaF]
  simp only [Units.val_div_eq_div_val]
  constructor
  · rw [lowUpstairsCandidate_eq_normalized]
    dsimp only [lowNormalizedUpstairsCandidate]
    rw [lowNormalizedRatio_norm]
    simp only [Units.val_div_eq_div_val, Units.coe_map,
      MonoidHom.coe_coe, map_div₀]
    field_simp [Units.ne_zero delta, Units.ne_zero epsilon1,
      Units.ne_zero P.alpha, Units.ne_zero (lowEpsilon F K epsilon1)]
  · constructor
    · field_simp [Units.ne_zero delta, Units.ne_zero P.alpha]
    · constructor
      · field_simp [Units.ne_zero delta,
          Units.ne_zero (lowEpsilon F K epsilon1), Units.ne_zero P.alpha]
      · field_simp [Units.ne_zero delta, Units.ne_zero P.alpha]
        ring

end LowSelectedStationaryPairs

section HighSelectedStationaryPairs

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  {t : ℕ}
  {ht : PrimeCyclicExtension.IsLowerBreak F K t}
  {hres : residueDegree F K = 1}
  {pi : ringOfIntegers K}
  {hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)}
  {hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤}
  {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
  {d epsilon : ℕ}
  {hF : IsStationaryConductorDecomposition chiF.conductor d epsilon}
  {hhigh : t + 1 ≤ chiF.conductor} {htpos : 0 < t}
  {tau : NormCharacter F K} {htau : tau ≠ 1}
  {gammaF : Fˣ}
  {hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)}

/-- The exact high four-pair package retains the supplied representative
record `R`, including its essential break-level unit `R.delta`. -/
noncomputable def highWildQuadraticSelectedStationaryPairs
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    WildQuadraticSelectedStationaryPairs F K where
  chiK :=
    { gamma := Units.map (algebraMap F K) gammaF
      beta := R.betaK }
  tau :=
    { gamma := R.gammaTau
      beta := 1 }
  chiF :=
    { gamma := gammaF
      beta := (R.beta : F) }
  tauChiF :=
    { gamma := gammaF
      beta := R.betaTwist }

theorem highWildQuadraticSelectedStationaryPairs_exact
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    let S := highWildQuadraticSelectedStationaryPairs R
    S.chiK.gamma = Units.map (algebraMap F K) gammaF ∧
    S.chiK.beta = algebraMap F K (R.cF : F) *
      (algebraMap F K (R.n : F) - (R.u : K)) ∧
    S.tau.gamma = gammaF / R.cF ∧ S.tau.beta = 1 ∧
    S.chiF.gamma = gammaF ∧
    S.chiF.beta = (R.cF : F) * (R.n : F) ∧
    S.tauChiF.gamma = gammaF ∧
    S.tauChiF.beta = (R.cF : F) * ((R.n : F) + 1) ∧
    R.cF = R.alpha * (R.delta : Fˣ) := by
  dsimp only [highWildQuadraticSelectedStationaryPairs]
  exact ⟨rfl, R.betaK_eq_cF_mul_sub, rfl, rfl, rfl,
    congrArg Units.val R.cF_mul_n.symm, rfl,
    R.betaTwist_eq_cF_mul_add_one, rfl⟩

theorem highWildQuadraticSelectedStationaryPairs_ratios
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    let S := highWildQuadraticSelectedStationaryPairs R
    let A : F := (R.cF : F) / (gammaF : F)
    S.chiK.ratio = algebraMap F K A *
        (algebraMap F K (R.n : F) - (R.u : K)) ∧
    S.tau.ratio = A ∧
    S.chiF.ratio = A * (R.n : F) ∧
    S.tauChiF.ratio = A * ((R.n : F) + 1) := by
  dsimp only [highWildQuadraticSelectedStationaryPairs,
    WildQuadraticStationaryPair.ratio]
  rw [R.betaK_eq_cF_mul_sub, R.betaTwist_eq_cF_mul_add_one]
  have hbeta : (R.beta : F) = (R.cF : F) * (R.n : F) :=
    congrArg Units.val R.cF_mul_n.symm
  rw [hbeta]
  simp only [WildQuadraticHighRepresentatives.gammaTau,
    Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe, map_div₀]
  constructor
  · field_simp [Units.ne_zero gammaF, Units.ne_zero R.cF]
  · constructor
    · field_simp [Units.ne_zero gammaF, Units.ne_zero R.cF]
    · constructor <;>
        field_simp [Units.ne_zero gammaF, Units.ne_zero R.cF] <;> ring

end HighSelectedStationaryPairs

namespace WildQuadraticCoefficientData

variable {k : Type u} [Field k]

/-- Scalar `p(z)` in the exact residue transport table. -/
def pTransport (D : WildQuadraticCoefficientData k) (z : k) : k :=
  match D.range with
  | .below | .boundary => z
  | .above => 0

/-- Scalar `q(z)` in the exact residue transport table.  At the even
boundary its value is immaterial because all four factors are constant, so
it is recorded as zero rather than inventing a residue representative. -/
def qTransport (D : WildQuadraticCoefficientData k) (z : k) : k :=
  match D with
  | .boundaryOdd rho _ _ _ _ _ _ _ _ => rho * z
  | _ => match D.range with
    | .below | .boundary => 0
    | .above => z

theorem residueTransport_table (D : WildQuadraticCoefficientData k) (z : k) :
    (D.pTransport z, D.qTransport z) =
      match D.range with
      | .below => (z, 0)
      | .above => (0, z)
      | .boundary => match D with
        | .boundaryOdd rho _ _ _ _ _ _ _ _ => (z, rho * z)
        | _ => (z, 0) := by
  cases D <;> rfl

section TransportFunctions

variable [Fintype k] [CharP k 2]

@[simp]
theorem function_zero (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (theta : WildQuadraticCharacter) :
    D.function q theta 0 = 1 := by
  rw [function]
  cases h : D.factor theta with
  | constant => rfl
  | critical lambda =>
      simp [WildQuadraticResidualFactor.toFun,
        WildQuadraticRefinement.criticalFunction_apply]

/-- Natural-coordinate form of the manuscript's exact transport
`Phi_K^raw = Phi_chi(p) Phi_tau(q) psi0(q)^e_tau`. -/
noncomputable def transportedRawUpper (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (z : k) : ℂ :=
  D.function q .chiF (D.pTransport z) *
    D.function q .tau (D.qTransport z) *
      (if D.row.TParity = .odd then
        absoluteTraceChar k (D.qTransport z) else 1)

theorem rawUpper_exact_transport (q : CharTwoRefinement k)
    (D : WildQuadraticCoefficientData k) (z : k) :
    D.rawUpperFunction q z = D.transportedRawUpper q z := by
  cases D with
  | belowMEvenTEven =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun]
  | belowMEvenTOdd gamma0 =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun,
        WildQuadraticRefinement.criticalFunction_apply]
  | belowMOddTEven gamma gammaPrime hs =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun,
        WildQuadraticRefinement.criticalFunction_apply]
  | belowMOddTOdd gamma0 gamma gammaPrime hs =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun,
        WildQuadraticRefinement.criticalFunction_apply]
  | boundaryEven =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun]
  | boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs =>
      rw [rawUpper_boundary q rho r gamma0 gamma gammaPrime hrho hr hden hs]
      rfl
  | aboveMEvenTEven =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun]
  | aboveMEvenTOdd gamma0 gammaPrime hs =>
      rw [rawUpper_above q (.aboveMEvenTOdd gamma0 gammaPrime hs) rfl]
      simp [transportedRawUpper, pTransport, qTransport, range, row,
        WildQuadraticCoefficientRow.range, WildQuadraticCoefficientRow.TParity]
  | aboveMOddTEven gamma =>
      simp [rawUpperFunction, rawUpperFactor, rawUpperAffineCoefficient,
        rawUpperScale, transportedRawUpper, pTransport, qTransport, range,
        row, WildQuadraticCoefficientRow.range,
        WildQuadraticCoefficientRow.TParity, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun,
        WildQuadraticRefinement.criticalFunction_apply]
  | aboveMOddTOdd gamma0 gamma gammaPrime hs =>
      rw [rawUpper_above q (.aboveMOddTOdd gamma0 gamma gammaPrime hs) rfl]
      simp [transportedRawUpper, pTransport, qTransport, range, row,
        WildQuadraticCoefficientRow.range, WildQuadraticCoefficientRow.TParity]

end TransportFunctions

end WildQuadraticCoefficientData

/-! ## Local critical coordinates and coherent parameter packages -/

namespace CriticalPolarFunction

/-- A positive-polar function whose coefficient is one is a Hasse function. -/
noncomputable def toHasse {k : Type u} [Field k]
    {psi0 : FiniteAddChar k} (phi : CriticalPolarFunction k psi0 1) :
    HasseFunction k psi0 where
  toFun := phi
  ne_zero' := phi.ne_zero
  map_add' := by
    intro x y
    simpa only [one_mul] using phi.map_add x y

@[simp]
theorem toHasse_apply {k : Type u} [Field k]
    {psi0 : FiniteAddChar k} (phi : CriticalPolarFunction k psi0 1) (z : k) :
    phi.toHasse z = phi z := rfl

end CriticalPolarFunction

section LocalOddCriticalCoordinate

variable {k : Type u} [Field k] [Fintype k] [CharP k 2]

/-- The affine coefficient is extracted, rather than supplied, from an
actual positive-polar function relative to the selected normalized
characteristic-two refinement. -/
noncomputable def normalizedCriticalPolarGamma
    (q : CharTwoRefinement k)
    (phi : CriticalPolarFunction k (absoluteTraceChar k) 1) : k :=
  (WildQuadraticRefinement.existsUnique_criticalFunction q phi.toHasse).choose

theorem normalizedCriticalPolarGamma_spec
    (q : CharTwoRefinement k)
    (phi : CriticalPolarFunction k (absoluteTraceChar k) 1) (z : k) :
    phi z = WildQuadraticRefinement.criticalFunction q
      (normalizedCriticalPolarGamma q phi) z := by
  have h :=
    (WildQuadraticRefinement.existsUnique_criticalFunction q phi.toHasse).choose_spec.1
  exact DFunLike.congr_fun h.symm z

/-- Translating a positive-polar function by the affine character with
coefficient `C` changes its normalized affine coefficient in the exact
direction `B' = B + C`. -/
theorem normalizedCriticalPolarGamma_translate
    (q : CharTwoRefinement k)
    (phi : CriticalPolarFunction k (absoluteTraceChar k) 1) (C : k) :
    normalizedCriticalPolarGamma q (phi.translate C) =
      normalizedCriticalPolarGamma q phi + C := by
  symm
  apply (WildQuadraticRefinement.existsUnique_criticalFunction q
    (phi.translate C).toHasse).choose_spec.2
  apply HasseFunction.ext
  intro z
  rw [WildQuadraticRefinement.criticalFunction_apply, add_mul,
    AddChar.map_add_eq_mul]
  change q z * (absoluteTraceChar k
      (normalizedCriticalPolarGamma q phi * z) *
        absoluteTraceChar k (C * z)) =
    phi z * absoluteTraceChar k (C * z)
  rw [normalizedCriticalPolarGamma_spec q phi z]
  simp only [WildQuadraticRefinement.criticalFunction_apply]
  ring

end LocalOddCriticalCoordinate

section ActualLocalOddCriticalCoordinate

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Fintype (ResidueField F)]
  [CharP (ResidueField F) 2]

/-- All choices defining one actual odd critical function.  The stationary
numerator remains an explicit quotient representative, while `hpolar`
certifies that the chosen critical coordinate has the positive unit polar
coefficient required by the common characteristic-two refinement. -/
structure QuotientDerivedNormalizedCriticalFunction where
  chi : LocalQuasiCharData F
  psi : LocalAddCharData F
  d : ℕ
  conductor_eq : chi.conductor = 2 * d + 1
  conductor_gt_one : 1 < chi.conductor
  Gamma : AdmissibleGamma F chi psi
  delta : Fˣ
  delta_order : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)
  beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ))
  beta_class : latticeQuotientMk F
      (sub_le_sub_left
        (criticalPolar_stationaryDepth F chi d conductor_eq
          conductor_gt_one).int_le_conductor
        (chi.conductor : ℤ)) beta =
    stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
      (criticalPolar_stationaryDepth F chi d conductor_eq conductor_gt_one)
      Gamma Gamma.property
  polar_eq_one : criticalPolarCoefficient F chi psi d conductor_eq
      conductor_gt_one Gamma delta delta_order
      (absoluteTraceChar (ResidueField F))
      (absoluteTraceChar_ne_one (ResidueField F)) = 1

/-- The nonzero polar coefficient computed by `CriticalPolarCoordinate`
before normalization. -/
noncomputable def criticalPolarNormalizationCoefficient
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    ResidueField F :=
  criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
    (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F))

theorem criticalPolarNormalizationCoefficient_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    criticalPolarNormalizationCoefficient F chi psi d hm hlarge Gamma delta
      hdelta ≠ 0 :=
  criticalPolarCoefficient_ne_zero F chi psi d hm hlarge Gamma delta hdelta
    (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F))

/-- The unique characteristic-two square root of the inverse raw polar
coefficient, regarded as a residue unit. -/
noncomputable def criticalPolarNormalizationResidueUnit
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    (ResidueField F)ˣ :=
  Units.mk0
    (WildQuadraticRefinement.squareRoot
      (criticalPolarNormalizationCoefficient F chi psi d hm hlarge Gamma
        delta hdelta)⁻¹)
    (by
      intro hz
      have hsquare := WildQuadraticRefinement.squareRoot_sq
        (criticalPolarNormalizationCoefficient F chi psi d hm hlarge Gamma
          delta hdelta)⁻¹
      rw [hz, zero_pow (by omega)] at hsquare
      exact (inv_ne_zero
        (criticalPolarNormalizationCoefficient_ne_zero F chi psi d hm hlarge
          Gamma delta hdelta)) hsquare.symm)

/-- An arbitrary unit lift of the required residue scaling.  Only its
specified residue, never a canonical lift, is used below. -/
noncomputable def criticalPolarNormalizationUnit
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    unitGroup F :=
  (residueUnits_surjective F
    (criticalPolarNormalizationResidueUnit F chi psi d hm hlarge Gamma delta
      hdelta)).choose

theorem criticalPolarNormalizationUnit_spec
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    residueUnits F
      (criticalPolarNormalizationUnit F chi psi d hm hlarge Gamma delta
        hdelta) =
      criticalPolarNormalizationResidueUnit F chi psi d hm hlarge Gamma
        delta hdelta :=
  (residueUnits_surjective F
    (criticalPolarNormalizationResidueUnit F chi psi d hm hlarge Gamma delta
      hdelta)).choose_spec

/-- Normalize an arbitrary odd critical coordinate by an actual unit lift of
the square root of the inverse polar coefficient.  The local characters,
denominator, and quotient representative are unchanged. -/
noncomputable def normalizedQuotientDerivedCriticalFunction
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    QuotientDerivedNormalizedCriticalFunction F where
  chi := chi
  psi := psi
  d := d
  conductor_eq := hm
  conductor_gt_one := hlarge
  Gamma := Gamma
  delta := criticalPolarScaledCoordinate F
    (criticalPolarNormalizationUnit F chi psi d hm hlarge Gamma delta hdelta)
      delta
  delta_order := criticalPolarScaledCoordinate_ord F d
    (criticalPolarNormalizationUnit F chi psi d hm hlarge Gamma delta hdelta)
      delta hdelta
  beta := beta
  beta_class := hbeta
  polar_eq_one := by
    rw [criticalPolarCoefficient_scaleCoordinate F chi psi d hm hlarge Gamma
      delta hdelta (absoluteTraceChar (ResidueField F))
      (absoluteTraceChar_ne_one (ResidueField F))]
    rw [criticalPolarNormalizationUnit_spec]
    change (WildQuadraticRefinement.squareRoot
        (criticalPolarNormalizationCoefficient F chi psi d hm hlarge Gamma
          delta hdelta)⁻¹) ^ 2 *
      criticalPolarNormalizationCoefficient F chi psi d hm hlarge Gamma
        delta hdelta = 1
    rw [WildQuadraticRefinement.squareRoot_sq]
    exact inv_mul_cancel₀
      (criticalPolarNormalizationCoefficient_ne_zero F chi psi d hm hlarge
        Gamma delta hdelta)

/-- Existence form of the positive-polar normalization, retaining the actual
unit lift, local data, denominator, and stationary quotient representative. -/
theorem exists_normalizedQuotientDerivedCriticalFunction
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    ∃ (u : unitGroup F) (W : QuotientDerivedNormalizedCriticalFunction F),
      residueUnits F u =
          criticalPolarNormalizationResidueUnit F chi psi d hm hlarge Gamma
            delta hdelta ∧
      W.chi = chi ∧ W.psi = psi ∧
      W.d = d ∧
      W.delta = criticalPolarScaledCoordinate F u delta ∧
      (W.Gamma : Fˣ) = (Gamma : Fˣ) ∧
      (W.beta : F) = (beta : F) := by
  refine ⟨criticalPolarNormalizationUnit F chi psi d hm hlarge Gamma delta
      hdelta,
    normalizedQuotientDerivedCriticalFunction F chi psi d hm hlarge Gamma
      delta hdelta beta hbeta,
    criticalPolarNormalizationUnit_spec F chi psi d hm hlarge Gamma delta
      hdelta, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual quotient-derived local critical function, coerced to polar
coefficient one only after `CriticalPolarCoordinate` has computed that
coefficient. -/
noncomputable def normalizedLocalCriticalPolarData
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hpolar : criticalPolarCoefficient F chi psi d hm hlarge Gamma delta
      hdelta psi0 hpsi0 = 1) :
    CriticalPolarFunction (ResidueField F) psi0 1 :=
  let phi := criticalPolarData F chi psi d hm hlarge Gamma delta hdelta
    psi0 hpsi0 beta hbeta
  { toFun := phi
    ne_zero' := phi.ne_zero
    map_add' := by
      intro x y
      rw [phi.map_add]
      congr 1
      rw [hpolar] }

@[simp]
theorem normalizedLocalCriticalPolarData_apply
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hpolar : criticalPolarCoefficient F chi psi d hm hlarge Gamma delta
      hdelta psi0 hpsi0 = 1) (z : ResidueField F) :
    normalizedLocalCriticalPolarData F chi psi d hm hlarge Gamma delta hdelta
        psi0 hpsi0 beta hbeta hpolar z =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta z :=
  rfl

/-- The characteristic-two affine coefficient of the actual local critical
function. -/
noncomputable def localCriticalAffineCoefficient
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hpolar : criticalPolarCoefficient F chi psi d hm hlarge Gamma delta
      hdelta psi0 hpsi0 = 1)
    (hpsi0_absolute : psi0 = absoluteTraceChar (ResidueField F))
    (q : CharTwoRefinement (ResidueField F)) : ResidueField F :=
  by
    subst psi0
    exact normalizedCriticalPolarGamma q
      (normalizedLocalCriticalPolarData F chi psi d hm hlarge Gamma delta
        hdelta (absoluteTraceChar (ResidueField F)) hpsi0 beta hbeta hpolar)

/-- Exact identification of the actual quotient-derived local critical
function with the normalized characteristic-two refinement and its computed
affine coefficient. -/
theorem localCriticalAffineCoefficient_spec
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hpolar : criticalPolarCoefficient F chi psi d hm hlarge Gamma delta
      hdelta psi0 hpsi0 = 1)
    (hpsi0_absolute : psi0 = absoluteTraceChar (ResidueField F))
    (q : CharTwoRefinement (ResidueField F)) (z : ResidueField F) :
    normalizedLocalCriticalPolarData F chi psi d hm hlarge Gamma delta hdelta
        psi0 hpsi0 beta hbeta hpolar z =
      WildQuadraticRefinement.criticalFunction q
        (localCriticalAffineCoefficient F chi psi d hm hlarge Gamma delta
          hdelta psi0 hpsi0 beta hbeta hpolar hpsi0_absolute q) z := by
  subst psi0
  simpa [localCriticalAffineCoefficient] using
    normalizedCriticalPolarGamma_spec q
      (normalizedLocalCriticalPolarData F chi psi d hm hlarge Gamma delta
        hdelta (absoluteTraceChar (ResidueField F)) hpsi0 beta hbeta hpolar) z

namespace QuotientDerivedNormalizedCriticalFunction

/-- The positive-polar function determined by the retained local quotient
representative and its explicitly normalized critical coordinate. -/
noncomputable def toCriticalPolarFunction
    (W : QuotientDerivedNormalizedCriticalFunction F) :
    CriticalPolarFunction (ResidueField F)
      (absoluteTraceChar (ResidueField F)) 1 :=
  normalizedLocalCriticalPolarData F W.chi W.psi W.d W.conductor_eq
    W.conductor_gt_one W.Gamma W.delta W.delta_order
    (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F)) W.beta W.beta_class
    W.polar_eq_one

@[simp]
theorem toCriticalPolarFunction_apply
    (W : QuotientDerivedNormalizedCriticalFunction F) (z : ResidueField F) :
    toCriticalPolarFunction F W z =
      criticalPolarFunction F W.chi W.psi W.d W.conductor_eq
        W.conductor_gt_one W.Gamma W.delta W.delta_order W.beta z :=
  rfl

/-- An actual quotient-derived critical function is exactly the selected
field-level stationary factor evaluated on its critical unit.  This bridge
keeps the numerator and denominator orientation explicit. -/
theorem toCriticalPolarFunction_eq_stationaryUnitFactor
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (P : WildQuadraticStationaryPair F)
    (hP : (W.Gamma : Fˣ) = P.gamma ∧ (W.beta : F) = P.beta)
    (z : ResidueField F) :
    toCriticalPolarFunction F W z =
      stationaryUnitFactor W.chi.character W.psi P
        (criticalPolarUnit F W.chi W.d W.conductor_eq W.conductor_gt_one
          W.delta W.delta_order (teichmuller F z : F)
          ((mem_lattice_zero_iff F).2 (teichmuller F z).property) : Fˣ) := by
  rw [toCriticalPolarFunction_apply]
  rcases hP with ⟨hGamma, hbeta⟩
  simp only [criticalPolarFunction, criticalPolarValue, stationaryUnitFactor,
    WildQuadraticStationaryPair.ratio]
  rw [← hGamma, ← hbeta, criticalPolarUnit_coe]
  congr 2
  field_simp
  <;> ring_nf

/-- Its affine coefficient is computed from the actual quotient-derived
function by uniqueness relative to the chosen normalized refinement. -/
noncomputable def affineCoefficient
  (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F)) : ResidueField F :=
  normalizedCriticalPolarGamma q (toCriticalPolarFunction F W)

theorem function_eq_critical
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F)) (z : ResidueField F) :
    toCriticalPolarFunction F W z =
      WildQuadraticRefinement.criticalFunction q (affineCoefficient F W q) z :=
  normalizedCriticalPolarGamma_spec q (toCriticalPolarFunction F W) z

/-- Phase of the complete finite sum attached to this actual quotient-derived
critical function. -/
noncomputable def phase
    (W : QuotientDerivedNormalizedCriticalFunction F) : ℂ :=
  W.toCriticalPolarFunction.toHasse.sumPhase

/-- The actual quotient-derived phase is the normalized refinement phase at
the affine coefficient extracted from that same function. -/
theorem phase_eq_refinement
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F)) :
    phase F W = WildQuadraticRefinement.phase q (affineCoefficient F W q) := by
  have hfun : W.toCriticalPolarFunction.toHasse =
      WildQuadraticRefinement.criticalFunction q (affineCoefficient F W q) := by
    apply HasseFunction.ext
    intro z
    exact function_eq_critical F W q z
  change W.toCriticalPolarFunction.toHasse.sumPhase =
    (WildQuadraticRefinement.criticalFunction q
      (affineCoefficient F W q)).sumPhase
  rw [hfun]

/-- The quotient witness uses exactly this selected Lamprecht denominator
and numerator, rather than merely another representative of the same type. -/
def MatchesStationaryPair (W : QuotientDerivedNormalizedCriticalFunction F)
    (P : WildQuadraticStationaryPair F) : Prop :=
  (W.Gamma : Fˣ) = P.gamma ∧ (W.beta : F) = P.beta

/-- The quotient witness is attached to these exact local character data. -/
def MatchesLocalData (W : QuotientDerivedNormalizedCriticalFunction F)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) : Prop :=
  W.chi = chi ∧ W.psi = psi

/-- An actual representative of an odd stationary coefficient class admits
a positive-polar quotient-derived witness with exactly the supplied
denominator and representative.  The normalizing coordinate uses an
arbitrary unit lift of the required residue scaling; the stationary
representative itself is never replaced by a canonical choice. -/
theorem exists_of_stationaryCoefficientClass
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ)
    (hD : IsStationaryConductorDecomposition chi.conductor d 1)
    (gamma : Fˣ)
    (hgamma : ord F (gamma : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (beta0 : lattice F 0)
    (hbeta0 : latticeQuotientMk F
        (show (0 : ℤ) ≤ (d : ℤ) by omega) beta0 =
      stationaryCoefficientClass F chi psi hD gamma hgamma) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction F,
      MatchesLocalData F W chi psi ∧
        MatchesStationaryPair F W { gamma := gamma, beta := beta0 } := by
  have hm : chi.conductor = 2 * d + 1 := by
    simpa using hD.conductor_eq
  have hlarge : 1 < chi.conductor := hD.conductor_gt_one
  let beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)) :=
    ⟨(beta0 : F), by simpa using beta0.property⟩
  have hbeta0' := congrArg
    (stationaryCoefficientLamprechtEquivAtConductor F hD) hbeta0
  rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
    stationaryCoefficientClass_toLamprecht] at hbeta0'
  have hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge) gamma hgamma := by
    simpa [beta] using hbeta0'
  obtain ⟨delta0, hdelta0⟩ := exists_ord_eq F (d : ℤ)
  have hdelta0_ne : delta0 ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hdelta0]; simp)
  let delta : Fˣ := Units.mk0 delta0 hdelta0_ne
  have hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ) := hdelta0
  let Gamma : AdmissibleGamma F chi psi := ⟨gamma, hgamma⟩
  obtain ⟨u, W, hu, hchi, hpsi, hd, hWdelta, hWgamma, hWbeta⟩ :=
    exists_normalizedQuotientDerivedCriticalFunction F chi psi d hm hlarge
      Gamma delta hdelta beta hbeta
  exact ⟨W, ⟨hchi, hpsi⟩, hWgamma, hWbeta⟩

/-- Replace only the selected numerator representative, retaining the same
local characters, denominator, critical coordinate, and polar normalization. -/
def replaceRepresentative (W : QuotientDerivedNormalizedCriticalFunction F)
    (beta' : lattice F
      ((W.chi.conductor : ℤ) - (W.chi.conductor : ℤ)))
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
            W.conductor_gt_one).int_le_conductor
          (W.chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F W.chi W.psi (W.chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
          W.conductor_gt_one) W.Gamma W.Gamma.property) :
    QuotientDerivedNormalizedCriticalFunction F :=
  { W with beta := beta', beta_class := hbeta' }

end QuotientDerivedNormalizedCriticalFunction

/-- Actual stationary representatives translate the local critical function
in the exact direction `B' = B + A*a`.  Both representatives remain explicit
and are proved to represent the same quotient class. -/
theorem wildQuadraticCriticalFunction_changeRepresentative
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField F) :
    let A := criticalPolarCoefficient F chi psi d hm hlarge Gamma delta
      hdelta psi0 hpsi0
    let a := criticalRepresentativeTranslationParameter F chi psi d hm
      hlarge Gamma delta hdelta beta beta' hbeta hbeta'
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta' x =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
        psi0 ((A * a) * x) := by
  dsimp only
  rw [criticalPolarFunction_changeRepresentative_intrinsic F chi psi d hm
    hlarge Gamma delta hdelta beta beta' hbeta hbeta' x]
  congr 1
  symm
  rw [mul_assoc]
  change psi0
      (finiteAddCharCoefficient psi0 hpsi0
          (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta) *
        (criticalRepresentativeTranslationParameter F chi psi d hm hlarge
          Gamma delta hdelta beta beta' hbeta hbeta' * x)) =
    criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta
      (criticalRepresentativeTranslationParameter F chi psi d hm hlarge
        Gamma delta hdelta beta beta' hbeta hbeta' * x)
  simpa only [mul_assoc] using
    finiteAddCharCoefficient_apply psi0 hpsi0
      (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta)
      (criticalRepresentativeTranslationParameter F chi psi d hm hlarge
        Gamma delta hdelta beta beta' hbeta hbeta' * x)

namespace QuotientDerivedNormalizedCriticalFunction

/-- Replacing the retained quotient representative is exactly translation of
the associated positive-polar function by the intrinsic translation
parameter.  Both representatives and both quotient-class proofs remain in
the statement. -/
theorem toCriticalPolarFunction_replaceRepresentative
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (beta' : lattice F
      ((W.chi.conductor : ℤ) - (W.chi.conductor : ℤ)))
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
            W.conductor_gt_one).int_le_conductor
          (W.chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F W.chi W.psi (W.chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
          W.conductor_gt_one) W.Gamma W.Gamma.property) :
    toCriticalPolarFunction F (W.replaceRepresentative F beta' hbeta') =
      (toCriticalPolarFunction F W).translate
        (criticalRepresentativeTranslationParameter F W.chi W.psi W.d
          W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
          W.beta beta' W.beta_class hbeta') := by
  apply CriticalPolarFunction.ext
  intro x
  simp only [toCriticalPolarFunction_apply,
    CriticalPolarFunction.translate_apply]
  change criticalPolarFunction F W.chi W.psi W.d W.conductor_eq
      W.conductor_gt_one W.Gamma W.delta W.delta_order beta' x =
    criticalPolarFunction F W.chi W.psi W.d W.conductor_eq
        W.conductor_gt_one W.Gamma W.delta W.delta_order W.beta x *
      absoluteTraceChar (ResidueField F)
        (criticalRepresentativeTranslationParameter F W.chi W.psi W.d
          W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
          W.beta beta' W.beta_class hbeta' * x)
  have h := wildQuadraticCriticalFunction_changeRepresentative F W.chi W.psi
    W.d W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
    (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F)) W.beta beta' W.beta_class
    hbeta' x
  simpa only [W.polar_eq_one, one_mul] using h

/-- Exact representative-translation law for the affine coefficient extracted
from the actual quotient-derived function: `B' = B + A*a`, with the retained
positive polar normalization `A = 1`. -/
theorem affineCoefficient_replaceRepresentative
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F))
    (beta' : lattice F
      ((W.chi.conductor : ℤ) - (W.chi.conductor : ℤ)))
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
            W.conductor_gt_one).int_le_conductor
          (W.chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F W.chi W.psi (W.chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
          W.conductor_gt_one) W.Gamma W.Gamma.property) :
    affineCoefficient F (W.replaceRepresentative F beta' hbeta') q =
      affineCoefficient F W q +
        criticalRepresentativeTranslationParameter F W.chi W.psi W.d
          W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
          W.beta beta' W.beta_class hbeta' := by
  rw [affineCoefficient,
    toCriticalPolarFunction_replaceRepresentative F W beta' hbeta',
    normalizedCriticalPolarGamma_translate]
  rfl

/-- In a supplied nonzero common-coordinate scale `s`, replacement of the
actual stationary numerator has the manuscript form
`B_common' = B_common + A_common * a_common`, with
`B_common = s*B`, `A_common = s^2`, and `a_common = a/s`.  Thus the apparent
weight-two translation is derived from the actual intrinsic replacement;
it is not a synthetic translation of a table-defined function. -/
theorem commonAffineCoefficient_replaceRepresentative
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F))
    (s : ResidueField F) (hs : s ≠ 0)
    (beta' : lattice F
      ((W.chi.conductor : ℤ) - (W.chi.conductor : ℤ)))
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
            W.conductor_gt_one).int_le_conductor
          (W.chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F W.chi W.psi (W.chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
          W.conductor_gt_one) W.Gamma W.Gamma.property) :
    s * affineCoefficient F (W.replaceRepresentative F beta' hbeta') q =
      s * affineCoefficient F W q + s ^ 2 *
        (criticalRepresentativeTranslationParameter F W.chi W.psi W.d
          W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
          W.beta beta' W.beta_class hbeta' / s) := by
  rw [affineCoefficient_replaceRepresentative F W q beta' hbeta']
  field_simp [hs]

/-- Pointwise actual-function form of
`commonAffineCoefficient_replaceRepresentative`.  The translated function
is the quotient-derived function for the explicitly supplied `beta'`. -/
theorem toCriticalPolarFunction_replaceRepresentative_commonCoordinate
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (q : CharTwoRefinement (ResidueField F))
    (s : ResidueField F) (hs : s ≠ 0)
    (beta' : lattice F
      ((W.chi.conductor : ℤ) - (W.chi.conductor : ℤ)))
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
            W.conductor_gt_one).int_le_conductor
          (W.chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F W.chi W.psi (W.chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F W.chi W.d W.conductor_eq
          W.conductor_gt_one) W.Gamma W.Gamma.property)
    (z : ResidueField F) :
    toCriticalPolarFunction F (W.replaceRepresentative F beta' hbeta')
        (s * z) =
      q (s * z) * absoluteTraceChar (ResidueField F)
        ((s * affineCoefficient F W q + s ^ 2 *
          (criticalRepresentativeTranslationParameter F W.chi W.psi W.d
            W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order
            W.beta beta' W.beta_class hbeta' / s)) * z) := by
  rw [function_eq_critical,
    WildQuadraticRefinement.criticalFunction_apply,
    affineCoefficient_replaceRepresentative F W q beta' hbeta']
  congr 2
  field_simp [hs]

end QuotientDerivedNormalizedCriticalFunction

end ActualLocalOddCriticalCoordinate

/-! ## Quotient-derived inputs for the ten rows -/

section QuotientDerivedTableInputs

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Fintype (ResidueField F)]
  [CharP (ResidueField F) 2]

/-- The two lower critical functions are the only free functional inputs to
the manuscript table.  Whenever they occur, they are retained as actual
quotient-derived local critical functions.  The upper and product functions,
including all affine coefficients, are computed from them. -/
inductive WildQuadraticCoefficientInputs
  | belowMEvenTEven
  | belowMEvenTOdd (tau : QuotientDerivedNormalizedCriticalFunction F)
  | belowMOddTEven (chiF : QuotientDerivedNormalizedCriticalFunction F)
  | belowMOddTOdd (tau chiF : QuotientDerivedNormalizedCriticalFunction F)
  | boundaryEven
  | boundaryOdd (rho : ResidueField F)
      (rho_ne_zero : rho ≠ 0) (denominator_ne_zero : 1 + rho ≠ 0)
      (tau chiF : QuotientDerivedNormalizedCriticalFunction F)
  | aboveMEvenTEven
  | aboveMEvenTOdd (tau : QuotientDerivedNormalizedCriticalFunction F)
  | aboveMOddTEven (chiF : QuotientDerivedNormalizedCriticalFunction F)
  | aboveMOddTOdd (tau chiF : QuotientDerivedNormalizedCriticalFunction F)

namespace WildQuadraticCoefficientInputs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Fintype (ResidueField F)]
  [CharP (ResidueField F) 2]

def row : WildQuadraticCoefficientInputs F → WildQuadraticCoefficientRow
  | .belowMEvenTEven => .belowMEvenTEven
  | .belowMEvenTOdd _ => .belowMEvenTOdd
  | .belowMOddTEven _ => .belowMOddTEven
  | .belowMOddTOdd _ _ => .belowMOddTOdd
  | .boundaryEven => .boundaryEven
  | .boundaryOdd _ _ _ _ _ => .boundaryOdd
  | .aboveMEvenTEven => .aboveMEvenTEven
  | .aboveMEvenTOdd _ => .aboveMEvenTOdd
  | .aboveMOddTEven _ => .aboveMOddTEven
  | .aboveMOddTOdd _ _ => .aboveMOddTOdd

def tauSource (I : WildQuadraticCoefficientInputs F) :
    Option (QuotientDerivedNormalizedCriticalFunction F) :=
  match I with
  | .belowMEvenTOdd tau | .belowMOddTOdd tau _ |
      .boundaryOdd _ _ _ tau _ | .aboveMEvenTOdd tau |
      .aboveMOddTOdd tau _ => some tau
  | _ => none

def chiFSource (I : WildQuadraticCoefficientInputs F) :
    Option (QuotientDerivedNormalizedCriticalFunction F) :=
  match I with
  | .belowMOddTEven chiF | .belowMOddTOdd _ chiF |
      .boundaryOdd _ _ _ _ chiF | .aboveMOddTEven chiF |
      .aboveMOddTOdd _ chiF => some chiF
  | _ => none

/-- An actual retained positive-polar Hasse source.  The disjunction is
provenance, not a free choice of a Hasse function: the witness must literally
be one of the quotient-derived lower sources stored in `I`. -/
structure PositivePolarSource (I : WildQuadraticCoefficientInputs F) where
  witness : QuotientDerivedNormalizedCriticalFunction F
  retained : I.tauSource = some witness ∨ I.chiFSource = some witness

namespace PositivePolarSource

/-- The actual Hasse function belonging to the retained quotient witness. -/
noncomputable def toHasse
    {I : WildQuadraticCoefficientInputs F} (S : PositivePolarSource I) :
    HasseFunction (ResidueField F) (absoluteTraceChar (ResidueField F)) :=
  S.witness.toCriticalPolarFunction.toHasse

/-- A retained positive-polar source can occur only in one of the seven
positive-polar rows. -/
theorem row_isPositivePolar
    {I : WildQuadraticCoefficientInputs F} (S : PositivePolarSource I) :
    I.row.IsPositivePolar := by
  cases I with
  | belowMEvenTEven =>
      have h := S.retained
      simp [tauSource, chiFSource] at h
  | belowMEvenTOdd => exact .belowMEvenTOdd
  | belowMOddTEven => exact .belowMOddTEven
  | belowMOddTOdd => exact .belowMOddTOdd
  | boundaryEven =>
      have h := S.retained
      simp [tauSource, chiFSource] at h
  | boundaryOdd => exact .boundaryOdd
  | aboveMEvenTEven =>
      have h := S.retained
      simp [tauSource, chiFSource] at h
  | aboveMEvenTOdd => exact .aboveMEvenTOdd
  | aboveMOddTEven => exact .aboveMOddTEven
  | aboveMOddTOdd => exact .aboveMOddTOdd

end PositivePolarSource

/-- Exact input-level dichotomy: the three source-free rows are all-even;
each of the other seven rows retains an actual positive-polar source. -/
theorem isAllEven_or_positivePolarSource
    (I : WildQuadraticCoefficientInputs F) :
    I.row.IsAllEven ∨ Nonempty (PositivePolarSource I) := by
  cases I with
  | belowMEvenTEven => exact Or.inl .belowMEvenTEven
  | belowMEvenTOdd tau =>
      exact Or.inr ⟨⟨tau, Or.inl rfl⟩⟩
  | belowMOddTEven chiF =>
      exact Or.inr ⟨⟨chiF, Or.inr rfl⟩⟩
  | belowMOddTOdd tau chiF =>
      exact Or.inr ⟨⟨tau, Or.inl rfl⟩⟩
  | boundaryEven => exact Or.inl .boundaryEven
  | boundaryOdd rho hrho hden tau chiF =>
      exact Or.inr ⟨⟨tau, Or.inl rfl⟩⟩
  | aboveMEvenTEven => exact Or.inl .aboveMEvenTEven
  | aboveMEvenTOdd tau =>
      exact Or.inr ⟨⟨tau, Or.inl rfl⟩⟩
  | aboveMOddTEven chiF =>
      exact Or.inr ⟨⟨chiF, Or.inr rfl⟩⟩
  | aboveMOddTOdd tau chiF =>
      exact Or.inr ⟨⟨tau, Or.inl rfl⟩⟩

/-- The q-free all-even branch and the actual positive-polar-source branch
are disjoint. -/
theorem isAllEven_positivePolarSource_disjoint
    {I : WildQuadraticCoefficientInputs F} (heven : I.row.IsAllEven)
    (S : PositivePolarSource I) : False :=
  WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint heven
    S.row_isPositivePolar

theorem positivePolarSource_iff_not_isAllEven
    (I : WildQuadraticCoefficientInputs F) :
    Nonempty (PositivePolarSource I) ↔ ¬ I.row.IsAllEven := by
  constructor
  · rintro ⟨S⟩ heven
    exact isAllEven_positivePolarSource_disjoint heven S
  · intro hnot
    rcases I.isAllEven_or_positivePolarSource with heven | hsource
    · exact (hnot heven).elim
    · exact hsource

/-- In an exact all-even row no actual lower critical source is retained. -/
theorem tauSource_eq_none_of_isAllEven
    (I : WildQuadraticCoefficientInputs F) (h : I.row.IsAllEven) :
    I.tauSource = none := by
  cases I <;> cases h <;> rfl

/-- In an exact all-even row no actual base-character critical source is
retained. -/
theorem chiFSource_eq_none_of_isAllEven
    (I : WildQuadraticCoefficientInputs F) (h : I.row.IsAllEven) :
    I.chiFSource = none := by
  cases I <;> cases h <;> rfl

/-- Reconstruct the coefficient row for the all-even branch without ever
choosing a characteristic-two refinement. -/
def toAllEvenCoefficientData
    (I : WildQuadraticCoefficientInputs F) (h : I.row.IsAllEven) :
    WildQuadraticCoefficientData (ResidueField F) :=
  match I with
  | .belowMEvenTEven => .belowMEvenTEven
  | .belowMEvenTOdd _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .belowMEvenTOdd)
  | .belowMOddTEven _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .belowMOddTEven)
  | .belowMOddTOdd _ _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .belowMOddTOdd)
  | .boundaryEven => .boundaryEven
  | .boundaryOdd _ _ _ _ _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .boundaryOdd)
  | .aboveMEvenTEven => .aboveMEvenTEven
  | .aboveMEvenTOdd _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .aboveMEvenTOdd)
  | .aboveMOddTEven _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .aboveMOddTEven)
  | .aboveMOddTOdd _ _ => False.elim
      (WildQuadraticCoefficientRow.isAllEven_isPositivePolar_disjoint h
        .aboveMOddTOdd)

@[simp]
theorem toAllEvenCoefficientData_row
    (I : WildQuadraticCoefficientInputs F) (h : I.row.IsAllEven) :
    (I.toAllEvenCoefficientData h).row = I.row := by
  cases I <;> cases h <;> rfl

@[simp]
theorem toAllEvenCoefficientData_affineCoefficient
    (I : WildQuadraticCoefficientInputs F) (h : I.row.IsAllEven)
    (theta : WildQuadraticCharacter) :
    (I.toAllEvenCoefficientData h).affineCoefficient theta = none := by
  cases I <;> cases h <;> cases theta <;> rfl

@[simp]
theorem toAllEvenCoefficientData_rawUpperAffineCoefficient
    (I : WildQuadraticCoefficientInputs F) (h : I.row.IsAllEven) :
    (I.toAllEvenCoefficientData h).rawUpperAffineCoefficient = none := by
  cases I <;> cases h <;> rfl

/-- Construct the entire coefficient row.  In particular `gammaPrime`, `r`,
and every boundary quotient are computed rather than supplied as hypotheses. -/
noncomputable def toCoefficientData
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) :
    WildQuadraticCoefficientData (ResidueField F) :=
  match I with
  | .belowMEvenTEven => .belowMEvenTEven
  | .belowMEvenTOdd tau =>
      .belowMEvenTOdd
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F tau q)
  | .belowMOddTEven chiF =>
      .belowMOddTEvenComputed
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F chiF q)
  | .belowMOddTOdd tau chiF =>
      .belowMOddTOddComputed
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F tau q)
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F chiF q)
  | .boundaryEven => .boundaryEven
  | .boundaryOdd rho hrho hden tau chiF =>
      .boundaryOddComputed rho
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F tau q)
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F chiF q)
        hrho hden
  | .aboveMEvenTEven => .aboveMEvenTEven
  | .aboveMEvenTOdd tau =>
      .aboveMEvenTOddComputed
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F tau q)
  | .aboveMOddTEven chiF =>
      .aboveMOddTEven
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F chiF q)
  | .aboveMOddTOdd tau chiF =>
      .aboveMOddTOddComputed
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F tau q)
        (QuotientDerivedNormalizedCriticalFunction.affineCoefficient F chiF q)

@[simp]
theorem toCoefficientData_row (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) :
    (I.toCoefficientData q).row = I.row := by
  cases I <;> rfl

@[simp]
theorem tauCoefficient_from_quotient
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) :
    (I.toCoefficientData q).affineCoefficient .tau =
      I.tauSource.map (fun W =>
        QuotientDerivedNormalizedCriticalFunction.affineCoefficient F W q) := by
  cases I <;> rfl

@[simp]
theorem chiFCoefficient_from_quotient
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) :
    (I.toCoefficientData q).affineCoefficient .chiF =
      I.chiFSource.map (fun W =>
        QuotientDerivedNormalizedCriticalFunction.affineCoefficient F W q) := by
  cases I <;> rfl

/-- Every retained lower critical witness uses the exact selected
numerator/denominator pair. -/
def MatchesStationaryPairs {K : Type} [Field K]
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K) : Prop :=
  match I with
  | .belowMEvenTEven | .boundaryEven | .aboveMEvenTEven => True
  | .belowMEvenTOdd tau | .aboveMEvenTOdd tau =>
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F tau S.tau
  | .belowMOddTEven chiF | .aboveMOddTEven chiF =>
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F chiF S.chiF
  | .belowMOddTOdd tau chiF | .boundaryOdd _ _ _ tau chiF |
      .aboveMOddTOdd tau chiF =>
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          F tau S.tau ∧
        QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          F chiF S.chiF

/-- Every retained witness is attached to the exact norm character or
downstairs character and to the common additive character. -/
def MatchesLocalData (I : WildQuadraticCoefficientInputs F)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) : Prop :=
  match I with
  | .belowMEvenTEven | .boundaryEven | .aboveMEvenTEven => True
  | .belowMEvenTOdd tau | .aboveMEvenTOdd tau =>
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F tau tauData psiF
  | .belowMOddTEven chiF | .aboveMOddTEven chiF =>
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F chiF chiFData psiF
  | .belowMOddTOdd tau chiF | .boundaryOdd _ _ _ tau chiF |
      .aboveMOddTOdd tau chiF =>
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
          F tau tauData psiF ∧
        QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
          F chiF chiFData psiF

/-- Choice-relative common coordinate for the two actual lower critical
functions at the odd boundary.  The equality is oriented as
`c_tau = rhoTilde * c_chi`, exactly the scaling direction used by
`CriticalPolarCoordinate`. -/
structure WildQuadraticBoundaryCommonCoordinate
    (rho : ResidueField F)
    (tau chiF : QuotientDerivedNormalizedCriticalFunction F) where
  rhoLift : unitGroup F
  rhoLift_residue :
    ((residueUnits F rhoLift : (ResidueField F)ˣ) : ResidueField F) = rho
  coordinate_eq : tau.delta =
    criticalPolarScaledCoordinate F rhoLift chiF.delta

namespace WildQuadraticBoundaryCommonCoordinate

/-- Scaling the actual `chiF` critical coordinate to the retained common
`tau` coordinate computes the positive polar coefficient `rho^2`. -/
theorem chiF_common_polarCoefficient
    {rho : ResidueField F}
    {tau chiF : QuotientDerivedNormalizedCriticalFunction F}
    (C : WildQuadraticBoundaryCommonCoordinate (F := F) rho tau chiF) :
    criticalPolarCoefficient F chiF.chi chiF.psi chiF.d
        chiF.conductor_eq chiF.conductor_gt_one chiF.Gamma
        (criticalPolarScaledCoordinate F C.rhoLift chiF.delta)
        (criticalPolarScaledCoordinate_ord F chiF.d C.rhoLift chiF.delta
          chiF.delta_order)
        (absoluteTraceChar (ResidueField F))
        (absoluteTraceChar_ne_one (ResidueField F)) = rho ^ 2 := by
  rw [criticalPolarCoefficient_scaleCoordinate F chiF.chi chiF.psi chiF.d
    chiF.conductor_eq chiF.conductor_gt_one chiF.Gamma chiF.delta
    chiF.delta_order (absoluteTraceChar (ResidueField F))
    (absoluteTraceChar_ne_one (ResidueField F)) C.rhoLift,
    chiF.polar_eq_one, mul_one, C.rhoLift_residue]

end WildQuadraticBoundaryCommonCoordinate

/-- The manuscript's choice of one common boundary critical coordinate is
retained without choosing a canonical residue lift.  Outside the odd boundary
there is no common two-function coordinate to compare. -/
def MatchesBoundaryCriticalCoordinates (I : WildQuadraticCoefficientInputs F) :
    Prop :=
  match I with
  | .boundaryOdd rho _ _ tau chiF =>
      Nonempty (WildQuadraticBoundaryCommonCoordinate (F := F) rho tau chiF)
  | _ => True

end WildQuadraticCoefficientInputs

/-- Provenance for a normalized refinement used by a refined coefficient
row.  Both indices are part of the type: the source must come from these
actual coefficient inputs, and the normalization equation refers to this
exact `q`.  A source from one row therefore cannot be paired with the
refinement of another view. -/
structure WildQuadraticNormalizedRefinementSource
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) where
  source : WildQuadraticCoefficientInputs.PositivePolarSource I
  translationClass : ResidueField F
  normalized : q.toHasseFunction =
    source.toHasse.translate translationClass

namespace WildQuadraticNormalizedRefinementSource

/-- Normalize the actual retained Hasse source.  The refinement is chosen
from that source by `lem:normalized-refinement`; no unrelated refinement or
Hasse function is manufactured. -/
noncomputable def ofPositivePolarSource
    {I : WildQuadraticCoefficientInputs F}
    (S : WildQuadraticCoefficientInputs.PositivePolarSource I) :
    Σ q : CharTwoRefinement (ResidueField F),
      WildQuadraticNormalizedRefinementSource (F := F) I q :=
  let h := WildQuadraticRefinement.exists_normalized S.toHasse
  ⟨h.choose, S, h.choose_spec.choose, h.choose_spec.choose_spec⟩

theorem exists_of_positivePolarSource
    {I : WildQuadraticCoefficientInputs F}
    (S : WildQuadraticCoefficientInputs.PositivePolarSource I) :
    ∃ q : CharTwoRefinement (ResidueField F),
      Nonempty (WildQuadraticNormalizedRefinementSource (F := F) I q) :=
  ⟨(ofPositivePolarSource (F := F) S).1,
    ⟨(ofPositivePolarSource (F := F) S).2⟩⟩

/-- A normalized source-tied refinement belongs to one of the seven
positive-polar rows. -/
theorem row_isPositivePolar
    {I : WildQuadraticCoefficientInputs F}
    {q : CharTwoRefinement (ResidueField F)}
    (N : WildQuadraticNormalizedRefinementSource (F := F) I q) :
    I.row.IsPositivePolar :=
  N.source.row_isPositivePolar

theorem not_isAllEven
    {I : WildQuadraticCoefficientInputs F}
    {q : CharTwoRefinement (ResidueField F)}
    (N : WildQuadraticNormalizedRefinementSource (F := F) I q) :
    ¬ I.row.IsAllEven := by
  intro heven
  exact WildQuadraticCoefficientInputs.isAllEven_positivePolarSource_disjoint
    heven N.source

end WildQuadraticNormalizedRefinementSource

end QuotientDerivedTableInputs

/-! ## Actual lower functions and phase-preserving coordinate transport -/

namespace WildQuadraticCoefficientInputs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Fintype (ResidueField F)]
  [CharP (ResidueField F) 2]

/-- The actual quotient-derived `tau` function when its conductor is odd,
and the literal constant one when it is even. -/
noncomputable def actualTauFunction
    (I : WildQuadraticCoefficientInputs F) : ResidueField F → ℂ :=
  match I.tauSource with
  | none => fun _ => 1
  | some W => QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F W

/-- The actual quotient-derived `chiF` function when its conductor is odd,
and the literal constant one when it is even. -/
noncomputable def actualChiFFunction
    (I : WildQuadraticCoefficientInputs F) : ResidueField F → ℂ :=
  match I.chiFSource with
  | none => fun _ => 1
  | some W => QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F W

/-- The actual lower `tau` source is exactly the table's `tau` function in
every row; this is where even rows become genuine constants. -/
theorem actualTauFunction_eq_table
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) (z : ResidueField F) :
    I.actualTauFunction z = (I.toCoefficientData q).function q .tau z := by
  cases I <;>
    simp only [actualTauFunction, tauSource,
      WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.belowMOddTEvenComputed,
      WildQuadraticCoefficientData.belowMOddTOddComputed,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.aboveMEvenTOddComputed,
      WildQuadraticCoefficientData.aboveMOddTOddComputed,
      WildQuadraticCoefficientData.function,
      WildQuadraticCoefficientData.factor,
      WildQuadraticCoefficientData.affineCoefficient,
      WildQuadraticResidualFactor.toFun,
      QuotientDerivedNormalizedCriticalFunction.function_eq_critical] <;>
    exact QuotientDerivedNormalizedCriticalFunction.function_eq_critical
      F _ q z

/-- The actual lower `chiF` source is exactly the table's `chiF` function in
every row; this also proves the claimed even rows are literal constants. -/
theorem actualChiFFunction_eq_table
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F)) (z : ResidueField F) :
    I.actualChiFFunction z = (I.toCoefficientData q).function q .chiF z := by
  cases I <;>
    simp only [actualChiFFunction, chiFSource,
      WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.belowMOddTEvenComputed,
      WildQuadraticCoefficientData.belowMOddTOddComputed,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.aboveMEvenTOddComputed,
      WildQuadraticCoefficientData.aboveMOddTOddComputed,
      WildQuadraticCoefficientData.function,
      WildQuadraticCoefficientData.factor,
      WildQuadraticCoefficientData.affineCoefficient,
      WildQuadraticResidualFactor.toFun,
      QuotientDerivedNormalizedCriticalFunction.function_eq_critical] <;>
    exact QuotientDerivedNormalizedCriticalFunction.function_eq_critical
      F _ q z

end WildQuadraticCoefficientInputs

namespace QuotientDerivedNormalizedCriticalFunction

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Fintype (ResidueField E)]
  [CharP (ResidueField E) 2]

/-- The lift-level value belonging to an actual normalized quotient witness. -/
def liftValue (W : QuotientDerivedNormalizedCriticalFunction E)
    (x : E) (hx : x ∈ lattice E 0) : ℂ :=
  criticalPolarValue E W.chi W.psi W.d W.conductor_eq W.conductor_gt_one
    W.Gamma W.delta W.delta_order W.beta x hx

/-- Evaluation on an arbitrary integral lift agrees with evaluation of the
residue-field critical function. -/
theorem toCriticalPolarFunction_reduce
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (x : E) (hx : x ∈ lattice E 0) :
    toCriticalPolarFunction E W (reduce E x hx) = W.liftValue x hx := by
  exact criticalPolarFunction_integral_lift E W.chi W.psi W.d
    W.conductor_eq W.conductor_gt_one W.Gamma W.delta W.delta_order W.beta
    W.beta_class x hx

/-- The actual critical unit evaluated on an arbitrary retained integral
lift.  Keeping the lift explicit is essential at the boundary, where scaled
Teichmüller representatives are congruent but need not be literally equal. -/
noncomputable def criticalUnitAtLift
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (x : lattice E 0) : Eˣ :=
  criticalPolarUnit E W.chi W.d W.conductor_eq W.conductor_gt_one
    W.delta W.delta_order (x : E) x.property

@[simp]
theorem criticalUnitAtLift_coe
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (x : lattice E 0) :
    ((criticalUnitAtLift W x : Eˣ) : E) =
      1 + (W.delta : E) * (x : E) :=
  criticalPolarUnit_coe E W.chi W.d W.conductor_eq W.conductor_gt_one
    W.delta W.delta_order (x : E) x.property

/-- A lift-level quotient-derived value is exactly the selected stationary
factor.  This is the bridge used to derive product transport from primitive
unit coordinates rather than assuming the desired function identity. -/
theorem liftValue_eq_stationaryUnitFactor
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (P : WildQuadraticStationaryPair E)
    (hP : MatchesStationaryPair E W P)
    (x : lattice E 0) :
    W.liftValue (x : E) x.property =
      stationaryUnitFactor W.chi.character W.psi P
        (criticalUnitAtLift W x) := by
  rcases hP with ⟨hgamma, hbeta⟩
  simp only [liftValue, criticalPolarValue, stationaryUnitFactor,
    WildQuadraticStationaryPair.ratio]
  congr 2
  rw [criticalUnitAtLift_coe, hgamma, hbeta]
  field_simp [Units.ne_zero P.gamma]
  ring

/-- Inversion of an actual positive-unit-polar critical function has exactly
the manuscript's extra positive binary phase.  This is a consequence of the
positive polar law, not a coefficient-table hypothesis. -/
theorem toCriticalPolarFunction_inv
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (z : ResidueField E) :
    (toCriticalPolarFunction E W z)⁻¹ =
      toCriticalPolarFunction E W z *
        absoluteTraceChar (ResidueField E) z := by
  let phi := toCriticalPolarFunction E W
  apply mul_right_cancel₀ (phi.ne_zero z)
  rw [inv_mul_cancel₀ (phi.ne_zero z)]
  have hadd := phi.map_add z z
  rw [CharTwo.add_self_eq_zero, CriticalPolarFunction.map_zero] at hadd
  simp only [one_mul] at hadd
  symm
  calc
    (phi z * absoluteTraceChar (ResidueField E) z) * phi z =
        phi z * phi z * absoluteTraceChar (ResidueField E) z := by ring
    _ = phi z * phi z *
        absoluteTraceChar (ResidueField E) (z * z) := by
          rw [show z * z = z ^ 2 by ring, absoluteTraceChar_sq]
    _ = 1 := hadd.symm

end QuotientDerivedNormalizedCriticalFunction

section AbstractCriticalTransport

variable {k kK : Type u} [Field k] [Fintype k] [CharP k 2]
  [Field kK] [Fintype kK] [CharP kK 2]

/-- Table-independent transport for an actual product critical function.
The three coordinate maps are data, not inferred canonical choices. -/
def CriticalProductTransport
    (prod tau chi : k → ℂ) (scale tauArg chiArg : k → k) : Prop :=
  ∀ z, prod (scale z) = tau (tauArg z) * chi (chiArg z)

end AbstractCriticalTransport

namespace WildQuadraticCoefficientData

variable {k : Type u} [Field k]

/-- Common coordinate of the actual lower product. -/
def lowerProductScale (D : WildQuadraticCoefficientData k) (z : k) : k :=
  match D with
  | .boundaryOdd rho _ _ _ _ _ _ _ _ => (1 + rho) * z
  | _ => z

/-- Argument of the lower `tau` factor in the product table. -/
def lowerTauArgument (D : WildQuadraticCoefficientData k) (z : k) : k :=
  match D.range with
  | .below | .boundary => z
  | .above => 0

/-- Argument of the lower `chiF` factor in the product table. -/
def lowerChiArgument (D : WildQuadraticCoefficientData k) (z : k) : k :=
  match D with
  | .boundaryOdd rho _ _ _ _ _ _ _ _ => rho * z
  | _ => match D.range with
    | .below | .boundary => 0
    | .above => z

/-- The scalar multiplying the lower product's intrinsic coordinate. -/
def lowerProductScaleValue (D : WildQuadraticCoefficientData k) : k :=
  match D with
  | .boundaryOdd rho _ _ _ _ _ _ _ _ => 1 + rho
  | _ => 1

/-- The lower-product scale is nonzero in every row by the hypotheses
retained in the row constructor. -/
theorem lowerProductScaleValue_ne_zero_from_row
    (D : WildQuadraticCoefficientData k) :
    D.lowerProductScaleValue ≠ 0 := by
  cases D <;> simp_all [lowerProductScaleValue]

@[simp]
theorem lowerProductScale_eq_mul (D : WildQuadraticCoefficientData k)
    (z : k) :
    D.lowerProductScale z = D.lowerProductScaleValue * z := by
  cases D <;> simp [lowerProductScale, lowerProductScaleValue]

section LowerProductTable

variable [Fintype k] [CharP k 2]

/-- Exact lower-product identity in all ten rows.  It is a finite algebra
theorem: below the break only `tau` survives, above only `chiF` survives,
and at the odd boundary both are transported to the common coordinate. -/
theorem lowerProduct_exact
    (q : CharTwoRefinement k) (D : WildQuadraticCoefficientData k) (z : k) :
    D.function q .tau (D.lowerTauArgument z) *
        D.function q .chiF (D.lowerChiArgument z) =
      D.function q .tauChiF (D.lowerProductScale z) := by
  cases D with
  | boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs =>
      simpa [lowerTauArgument, lowerChiArgument, lowerProductScale, range,
        row, WildQuadraticCoefficientRow.range, commonFunction,
        commonScale] using
        boundaryLower_transport q rho r gamma0 gamma gammaPrime hrho hr hden
          hs z
  | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven | belowMOddTOdd |
      boundaryEven | aboveMEvenTEven | aboveMEvenTOdd | aboveMOddTEven |
      aboveMOddTOdd =>
      simp [lowerTauArgument, lowerChiArgument, lowerProductScale, range, row,
        WildQuadraticCoefficientRow.range, function_zero,
        tauChiCoefficient_table, expectedTauChiCoefficient, function, factor,
        affineCoefficient, WildQuadraticResidualFactor.toFun]

end LowerProductTable

end WildQuadraticCoefficientData

section ActualCriticalCoordinateCertificates

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- The function represented by an optional odd critical source.  Absence is
the genuine even-conductor constant. -/
noncomputable def actualSourceFunction
    (source : Option (QuotientDerivedNormalizedCriticalFunction F)) :
    ResidueField F → ℂ :=
  match source with
  | none => fun _ => 1
  | some W =>
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F W

/-- Primitive realization of one lower stationary factor at one field-level
unit.  The critical branch retains an integral lift, its exact residue, and
equality of the actual local unit.  The constant branch retains the even
Lamprecht linearization at that unit.  No branch assumes an equality of
residual functions. -/
inductive ActualLowerStationaryCoordinate
    (source : Option (QuotientDerivedNormalizedCriticalFunction F))
    (data : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (P : WildQuadraticStationaryPair F)
    (z : ResidueField F) (v : Fˣ) : Prop
  | constant
      (source_eq : source = none)
      (factor_eq_one : stationaryUnitFactor data.character psi P v = 1)
  | critical
      (W : QuotientDerivedNormalizedCriticalFunction F)
      (source_eq : source = some W)
      (pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
        F W P)
      (localData : QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
        F W data psi)
      (lift : lattice F 0)
      (reduce_eq : reduce F (lift : F) lift.property = z)
      (unit_eq : QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        W lift = v)

namespace ActualLowerStationaryCoordinate

/-- Primitive lower coordinate data derive the residual value from
`CriticalPolarCoordinate` and the selected stationary pair. -/
theorem factor_eq_actualSourceFunction
    {source : Option (QuotientDerivedNormalizedCriticalFunction F)}
    {data : LocalQuasiCharData F} {psi : LocalAddCharData F}
    {P : WildQuadraticStationaryPair F}
    {z : ResidueField F} {v : Fˣ}
    (L : ActualLowerStationaryCoordinate F source data psi P z v) :
    stationaryUnitFactor data.character psi P v =
      actualSourceFunction F source z := by
  cases L with
  | constant hsource hone =>
      rw [hsource]
      exact hone
  | critical W hsource hpair hlocal lift hreduce hunit =>
      rcases hlocal with ⟨hchi, hpsi⟩
      rw [hsource]
      change stationaryUnitFactor data.character psi P v =
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F W z
      rw [← hreduce,
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce]
      symm
      simpa [hchi, hpsi, hunit] using
        QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
          W P hpair lift

end ActualLowerStationaryCoordinate

/-- The inverse of the optional actual `tau` source is the source itself times
the positive binary phase exactly in the odd-conductor rows. -/
theorem actualTauFunction_inv
    (I : WildQuadraticCoefficientInputs F)
    (q : CharTwoRefinement (ResidueField F))
    (z : ResidueField F) :
    (I.actualTauFunction z)⁻¹ = I.actualTauFunction z *
      (if (I.toCoefficientData q).row.TParity = .odd then
        absoluteTraceChar (ResidueField F) z else 1) := by
  cases I with
  | belowMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
  | belowMEvenTOdd tau =>
      simpa [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
        using QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_inv
          tau z
  | belowMOddTEven _ =>
      simp [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.belowMOddTEvenComputed,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
  | belowMOddTOdd tau _ =>
      simpa [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.belowMOddTOddComputed,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
        using QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_inv
          tau z
  | boundaryEven =>
      simp [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
  | boundaryOdd _ _ _ tau _ =>
      simpa [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.boundaryOddComputed,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
        using QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_inv
          tau z
  | aboveMEvenTEven =>
      simp [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
  | aboveMEvenTOdd tau =>
      simpa [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.aboveMEvenTOddComputed,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
        using QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_inv
          tau z
  | aboveMOddTEven _ =>
      simp [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
  | aboveMOddTOdd tau _ =>
      simpa [WildQuadraticCoefficientInputs.actualTauFunction,
        WildQuadraticCoefficientInputs.tauSource,
        WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.aboveMOddTOddComputed,
        WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.TParity]
        using QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_inv
          tau z

/-- Residue degree one turns the canonical extension residue map into the
residue-field equivalence used by every upper critical coordinate.  This is
determined by `CommonCorrection`; it is not an additional choice. -/
noncomputable def wildQuadraticResidueEquiv
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m) :
    ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K,
        C.residueDegree_eq_one]
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
theorem wildQuadraticResidueEquiv_apply
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (z : ResidueField F) :
    wildQuadraticResidueEquiv F K C z = extensionResidueMap F K z := rfl

/-- Primitive field-level realization of one upper residue coordinate and its
two natural norm coordinates.  The target residues occur only as reductions
of explicit integral lifts. -/
structure ActualUpperCoordinatePoint
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (I : WildQuadraticCoefficientInputs F)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (zK : ResidueField K) (p qcoord : ResidueField F) where
  upperLift : lattice K 0
  upper_reduce : reduce K (upperLift : K) upperLift.property = zK
  uxUnit : Kˣ
  uxUnit_coe : (uxUnit : K) =
    1 + (C.u : K) * ((upper.delta : K) * (upperLift : K))
  chiF_coordinate : ActualLowerStationaryCoordinate F I.chiFSource
    chiFData psiF S.chiF p
      (normUnits F K
        (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
          upper upperLift))
  tau_coordinate : ActualLowerStationaryCoordinate F I.tauSource
    tauData psiF S.tau qcoord (normUnits F K uxUnit)

/-- Primitive upper-coordinate certificate.  It stores actual lifts,
reductions, and local-unit identities, but no `CriticalNormTransport`, no
residue-coordinate functions, and no equality with a table function. -/
structure ActualUpperCoordinateCertificate
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) where
  upper : QuotientDerivedNormalizedCriticalFunction K
  upper_pair :
    QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      K upper S.chiK
  upper_character : upper.chi.character = chiFData.character.compNorm
  upper_additive : upper.psi.character = psiF.character.compTrace
  tau : NormCharacter F K
  tau_character : tau.1 = tauData.character
  chiK_ratio : S.chiK.ratio = algebraMap F K S.tau.ratio *
    (algebraMap F K (C.n : F) - (C.u : K))
  chiF_ratio : S.chiF.ratio = S.tau.ratio * (C.n : F)
  point : ∀ z : ResidueField F,
    ActualUpperCoordinatePoint F K C S I tauData chiFData psiF upper
      (wildQuadraticResidueEquiv F K C z)
      ((I.toCoefficientData q).pTransport
        ((((I.toCoefficientData q).commonScale .chiK)⁻¹ * z) ^ 2))
      ((I.toCoefficientData q).qTransport
        ((((I.toCoefficientData q).commonScale .chiK)⁻¹ * z) ^ 2))

namespace ActualUpperCoordinateCertificate

/-- The field-level stationary norm identity and primitive coordinate data
derive the exact natural upper transport. -/
theorem transport
    {T m : ℕ}
    {C : WildQuadraticCommonCorrectionData F K T m}
    {q : CharTwoRefinement (ResidueField F)}
    {I : WildQuadraticCoefficientInputs F}
    {S : WildQuadraticSelectedStationaryPairs F K}
    {tauData chiFData : LocalQuasiCharData F}
    {psiF : LocalAddCharData F}
    (A : ActualUpperCoordinateCertificate F K C q I S
      tauData chiFData psiF)
    (z : ResidueField F) :
    let D := I.toCoefficientData q
    let w := (D.commonScale .chiK)⁻¹ * z
    QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction K
        A.upper (wildQuadraticResidueEquiv F K C z) =
      I.actualChiFFunction (D.pTransport (w ^ 2)) *
        I.actualTauFunction (D.qTransport (w ^ 2)) *
          (if D.row.TParity = .odd then
            absoluteTraceChar (ResidueField F) (D.qTransport (w ^ 2))
          else 1) := by
  dsimp only
  let D := I.toCoefficientData q
  let w := (D.commonScale .chiK)⁻¹ * z
  let P := A.point z
  let v : Kˣ :=
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
      A.upper P.upperLift
  have hv : (v : K) =
      1 + (A.upper.delta : K) * (P.upperLift : K) :=
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_coe
      A.upper P.upperLift
  have hstationary := stationaryUnitFactor_compNorm_exact C S A.tau chiFData
    A.upper.chi psiF A.upper.psi A.upper_character A.upper_additive
      A.chiK_ratio A.chiF_ratio v P.uxUnit
      ((A.upper.delta : K) * (P.upperLift : K)) hv P.uxUnit_coe
  calc
    QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction K
          A.upper (wildQuadraticResidueEquiv F K C z) =
        stationaryUnitFactor A.upper.chi.character A.upper.psi S.chiK v := by
          rw [← P.upper_reduce,
            QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce]
          exact
            QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
              A.upper S.chiK A.upper_pair P.upperLift
    _ = stationaryUnitFactor chiFData.character psiF S.chiF
          (normUnits F K v) *
        (stationaryUnitFactor A.tau.1 psiF S.tau
          (normUnits F K P.uxUnit))⁻¹ := hstationary
    _ = actualSourceFunction F I.chiFSource (D.pTransport (w ^ 2)) *
        (actualSourceFunction F I.tauSource (D.qTransport (w ^ 2)))⁻¹ := by
          rw [A.tau_character]
          rw [P.chiF_coordinate.factor_eq_actualSourceFunction,
            P.tau_coordinate.factor_eq_actualSourceFunction]
    _ = I.actualChiFFunction (D.pTransport (w ^ 2)) *
        (I.actualTauFunction (D.qTransport (w ^ 2)))⁻¹ := rfl
    _ = I.actualChiFFunction (D.pTransport (w ^ 2)) *
          I.actualTauFunction (D.qTransport (w ^ 2)) *
            (if D.row.TParity = .odd then
              absoluteTraceChar (ResidueField F) (D.qTransport (w ^ 2))
            else 1) := by
          rw [actualTauFunction_inv F I q (D.qTransport (w ^ 2))]
          ring

end ActualUpperCoordinateCertificate

/-- Primitive common-unit coordinates for one dominant actual source. -/
structure ProductDominantCoordinates
    (product dominant : QuotientDerivedNormalizedCriticalFunction F)
    (productArg dominantArg : ResidueField F → ResidueField F) where
  productLift : ResidueField F → lattice F 0
  dominantLift : ResidueField F → lattice F 0
  product_reduce : ∀ z,
    reduce F (productLift z : F) (productLift z).property = productArg z
  dominant_reduce : ∀ z,
    reduce F (dominantLift z : F) (dominantLift z).property = dominantArg z
  commonUnit : ∀ z,
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        dominant (dominantLift z) =
      QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        product (productLift z)

/-- Primitive common-unit coordinates for the two boundary sources. -/
structure ProductBoundaryCoordinates
    (product tau chiF : QuotientDerivedNormalizedCriticalFunction F)
    (productArg tauArg chiArg : ResidueField F → ResidueField F) where
  productLift : ResidueField F → lattice F 0
  tauLift : ResidueField F → lattice F 0
  chiLift : ResidueField F → lattice F 0
  product_reduce : ∀ z,
    reduce F (productLift z : F) (productLift z).property = productArg z
  tau_reduce : ∀ z,
    reduce F (tauLift z : F) (tauLift z).property = tauArg z
  chi_reduce : ∀ z,
    reduce F (chiLift z : F) (chiLift z).property = chiArg z
  tau_commonUnit : ∀ z,
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        tau (tauLift z) =
      QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        product (productLift z)
  chi_commonUnit : ∀ z,
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        chiF (chiLift z) =
      QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        product (productLift z)

/-- Below the break, `tau` is the dominant critical source.  The lower
`chiF` factor is retained through its exact combined stationary-factor
cancellation at the actual common unit. -/
structure BelowProductCoordinateData
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (product : QuotientDerivedNormalizedCriticalFunction F) where
  tau : QuotientDerivedNormalizedCriticalFunction F
  tau_source : I.tauSource = some tau
  tau_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
    F tau S.tau
  tau_character : tau.chi.character = tauData.character
  tau_psi : tau.psi = psiF
  coordinates : ProductDominantCoordinates F product tau
    (I.toCoefficientData q).lowerProductScale
    (I.toCoefficientData q).lowerTauArgument
  stable_factor : ∀ z,
    stationaryUnitFactor chiFData.character psiF S.chiF
      (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        product (coordinates.productLift z)) = 1

/-- Above the break, `chiF` is the dominant critical source.  The lower
`tau` factor is retained through its exact combined stationary-factor
cancellation at the actual common unit. -/
structure AboveProductCoordinateData
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (product : QuotientDerivedNormalizedCriticalFunction F) where
  chiF : QuotientDerivedNormalizedCriticalFunction F
  chiF_source : I.chiFSource = some chiF
  chiF_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
    F chiF S.chiF
  chiF_character : chiF.chi.character = chiFData.character
  chiF_psi : chiF.psi = psiF
  coordinates : ProductDominantCoordinates F product chiF
    (I.toCoefficientData q).lowerProductScale
    (I.toCoefficientData q).lowerChiArgument
  stable_factor : ∀ z,
    stationaryUnitFactor tauData.character psiF S.tau
      (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        product (coordinates.productLift z)) = 1

/-- At the boundary, all three actual functions retain explicit integral
lifts reducing to the manuscript's three residue arguments, and the three
resulting local units are proved equal. -/
structure BoundaryProductCoordinateData
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (product : QuotientDerivedNormalizedCriticalFunction F) where
  tau : QuotientDerivedNormalizedCriticalFunction F
  chiF : QuotientDerivedNormalizedCriticalFunction F
  tau_source : I.tauSource = some tau
  chiF_source : I.chiFSource = some chiF
  tau_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
    F tau S.tau
  chiF_pair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
    F chiF S.chiF
  tau_character : tau.chi.character = tauData.character
  chiF_character : chiF.chi.character = chiFData.character
  tau_psi : tau.psi = psiF
  chiF_psi : chiF.psi = psiF
  coordinates : ProductBoundaryCoordinates F product tau chiF
    (I.toCoefficientData q).lowerProductScale
    (I.toCoefficientData q).lowerTauArgument
    (I.toCoefficientData q).lowerChiArgument

/-- Exhaustive range-separated primitive product-coordinate evidence. -/
inductive ProductRangeCoordinates
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (product : QuotientDerivedNormalizedCriticalFunction F) : Type
  | below
      (hrange : (I.toCoefficientData q).range = .below)
      (data : BelowProductCoordinateData F K q I S
        tauData chiFData psiF product)
  | boundary
      (hrange : (I.toCoefficientData q).range = .boundary)
      (data : BoundaryProductCoordinateData F K q I S
        tauData chiFData psiF product)
  | above
      (hrange : (I.toCoefficientData q).range = .above)
      (data : AboveProductCoordinateData F K q I S
        tauData chiFData psiF product)

/-- Primitive product-coordinate certificate.  It stores no complete
function identity.  Product transport is derived below from the retained
pair, exact ratio sum, product character, stable cancellation off the
boundary, and explicit common units at the boundary. -/
structure ActualProductCoordinateCertificate
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) where
  product : QuotientDerivedNormalizedCriticalFunction F
  product_pair :
    QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F product S.tauChiF
  product_character : product.chi.character =
    tauData.character * chiFData.character
  product_psi : product.psi = psiF
  product_ratio_sum : S.tauChiF.ratio = S.tau.ratio + S.chiF.ratio
  rangeCoordinates : ProductRangeCoordinates F K q I S
    tauData chiFData psiF product

@[simp]
theorem actualTauFunction_zero (I : WildQuadraticCoefficientInputs F) :
    I.actualTauFunction 0 = 1 := by
  cases I <;> simp [WildQuadraticCoefficientInputs.actualTauFunction,
    WildQuadraticCoefficientInputs.tauSource]

@[simp]
theorem actualChiFFunction_zero (I : WildQuadraticCoefficientInputs F) :
    I.actualChiFFunction 0 = 1 := by
  cases I <;> simp [WildQuadraticCoefficientInputs.actualChiFFunction,
    WildQuadraticCoefficientInputs.chiFSource]

theorem lowerChiArgument_eq_zero_of_below
    (D : WildQuadraticCoefficientData (ResidueField F))
    (h : D.range = .below) (z : ResidueField F) :
    D.lowerChiArgument z = 0 := by
  cases D <;> simp_all [WildQuadraticCoefficientData.range,
    WildQuadraticCoefficientData.lowerChiArgument,
    WildQuadraticCoefficientData.row, WildQuadraticCoefficientRow.range]

theorem lowerTauArgument_eq_zero_of_above
    (D : WildQuadraticCoefficientData (ResidueField F))
    (h : D.range = .above) (z : ResidueField F) :
    D.lowerTauArgument z = 0 := by
  simp [WildQuadraticCoefficientData.lowerTauArgument, h]

/-- The common `n` formulas imply the exact ratio sum stored by the
primitive product certificate, without changing any selected representative. -/
theorem product_ratio_sum_of_common_n
    (S : WildQuadraticSelectedStationaryPairs F K) (n : F)
    (hchiF : S.chiF.ratio = S.tau.ratio * n)
    (htauChiF : S.tauChiF.ratio = S.tau.ratio * (n + 1)) :
    S.tauChiF.ratio = S.tau.ratio + S.chiF.ratio := by
  rw [htauChiF, hchiF]
  ring

namespace ActualProductCoordinateCertificate

/-- The primitive certificate derives the complete actual product transport;
the old direct transport field is therefore unnecessary. -/
theorem transport
    {q : CharTwoRefinement (ResidueField F)}
    {I : WildQuadraticCoefficientInputs F}
    {S : WildQuadraticSelectedStationaryPairs F K}
    {tauData chiFData : LocalQuasiCharData F}
    {psiF : LocalAddCharData F}
    (C : ActualProductCoordinateCertificate F K q I S
      tauData chiFData psiF) :
    CriticalProductTransport
      (QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F
        C.product)
      I.actualTauFunction I.actualChiFFunction
      (I.toCoefficientData q).lowerProductScale
      (I.toCoefficientData q).lowerTauArgument
      (I.toCoefficientData q).lowerChiArgument := by
  intro z
  cases C.rangeCoordinates with
  | below hrange B =>
      let v := QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        C.product (B.coordinates.productLift z)
      have hprod :
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
              F C.product ((I.toCoefficientData q).lowerProductScale z) =
            stationaryUnitFactor (tauData.character * chiFData.character)
              psiF S.tauChiF v := by
        rw [← B.coordinates.product_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            C.product S.tauChiF C.product_pair,
          C.product_character, C.product_psi]
      have htau :
          I.actualTauFunction ((I.toCoefficientData q).lowerTauArgument z) =
            stationaryUnitFactor tauData.character psiF S.tau v := by
        simp only [WildQuadraticCoefficientInputs.actualTauFunction,
          B.tau_source]
        rw [← B.coordinates.dominant_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            B.tau S.tau B.tau_pair,
          B.tau_character, B.tau_psi, B.coordinates.commonUnit z]
      have hstable :
          stationaryUnitFactor chiFData.character psiF S.chiF v = 1 :=
        B.stable_factor z
      have hzero :
          I.actualChiFFunction
              ((I.toCoefficientData q).lowerChiArgument z) = 1 := by
        rw [lowerChiArgument_eq_zero_of_below F
          (I.toCoefficientData q) hrange z]
        exact actualChiFFunction_zero F I
      rw [hprod, stationaryUnitFactor_mul tauData.character
        chiFData.character (tauData.character * chiFData.character) psiF
        S.tau S.chiF S.tauChiF rfl C.product_ratio_sum v,
        hstable, mul_one, ← htau, hzero, mul_one]
  | boundary _ B =>
      let v := QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        C.product (B.coordinates.productLift z)
      have hprod :
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
              F C.product ((I.toCoefficientData q).lowerProductScale z) =
            stationaryUnitFactor (tauData.character * chiFData.character)
              psiF S.tauChiF v := by
        rw [← B.coordinates.product_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            C.product S.tauChiF C.product_pair,
          C.product_character, C.product_psi]
      have htau :
          I.actualTauFunction ((I.toCoefficientData q).lowerTauArgument z) =
            stationaryUnitFactor tauData.character psiF S.tau v := by
        simp only [WildQuadraticCoefficientInputs.actualTauFunction,
          B.tau_source]
        rw [← B.coordinates.tau_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            B.tau S.tau B.tau_pair,
          B.tau_character, B.tau_psi, B.coordinates.tau_commonUnit z]
      have hchi :
          I.actualChiFFunction ((I.toCoefficientData q).lowerChiArgument z) =
            stationaryUnitFactor chiFData.character psiF S.chiF v := by
        simp only [WildQuadraticCoefficientInputs.actualChiFFunction,
          B.chiF_source]
        rw [← B.coordinates.chi_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            B.chiF S.chiF B.chiF_pair,
          B.chiF_character, B.chiF_psi, B.coordinates.chi_commonUnit z]
      rw [hprod, stationaryUnitFactor_mul tauData.character
        chiFData.character (tauData.character * chiFData.character) psiF
        S.tau S.chiF S.tauChiF rfl C.product_ratio_sum v, ← htau, ← hchi]
  | above hrange B =>
      let v := QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        C.product (B.coordinates.productLift z)
      have hprod :
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
              F C.product ((I.toCoefficientData q).lowerProductScale z) =
            stationaryUnitFactor (tauData.character * chiFData.character)
              psiF S.tauChiF v := by
        rw [← B.coordinates.product_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            C.product S.tauChiF C.product_pair,
          C.product_character, C.product_psi]
      have hchi :
          I.actualChiFFunction ((I.toCoefficientData q).lowerChiArgument z) =
            stationaryUnitFactor chiFData.character psiF S.chiF v := by
        simp only [WildQuadraticCoefficientInputs.actualChiFFunction,
          B.chiF_source]
        rw [← B.coordinates.dominant_reduce z,
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction_reduce,
          QuotientDerivedNormalizedCriticalFunction.liftValue_eq_stationaryUnitFactor
            B.chiF S.chiF B.chiF_pair,
          B.chiF_character, B.chiF_psi, B.coordinates.commonUnit z]
      have hstable :
          stationaryUnitFactor tauData.character psiF S.tau v = 1 :=
        B.stable_factor z
      have hzero :
          I.actualTauFunction
              ((I.toCoefficientData q).lowerTauArgument z) = 1 := by
        rw [lowerTauArgument_eq_zero_of_above F
          (I.toCoefficientData q) hrange z]
        exact actualTauFunction_zero F I
      rw [hprod, stationaryUnitFactor_mul tauData.character
        chiFData.character (tauData.character * chiFData.character) psiF
        S.tau S.chiF S.tauChiF rfl C.product_ratio_sum v,
        hstable, one_mul, ← hchi, hzero, one_mul]

end ActualProductCoordinateCertificate

end ActualCriticalCoordinateCertificates

/-! ## Actual sources for the two derived critical factors -/

section ActualDerivedCriticalSources

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- Phase-preserving coordinate provenance for the two factors derived from
the lower quotient witnesses.  The record retains only table-independent
product/norm transport and explicit residue-coordinate formulas; equality
with the coefficient-table functions is proved below.  Conditions are
required only when the corresponding conductor is odd. -/
structure WildQuadraticDerivedCriticalSources
    {T m : ℕ}
    (correction : WildQuadraticCommonCorrectionData F K T m)
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) : Prop where
  tauChiF : ∀ {lambda : ResidueField F},
    (I.toCoefficientData q).affineCoefficient .tauChiF = some lambda →
      Nonempty (ActualProductCoordinateCertificate F K q I S
        tauData chiFData psiF)
  chiK : ∀ {lambda : ResidueField F},
    (I.toCoefficientData q).affineCoefficient .chiK = some lambda →
      Nonempty (ActualUpperCoordinateCertificate F K correction q I S
        tauData chiFData psiF)

namespace WildQuadraticDerivedCriticalSources

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {T m : ℕ}
  {correction : WildQuadraticCommonCorrectionData F K T m}
  {q : CharTwoRefinement (ResidueField F)}
  {I : WildQuadraticCoefficientInputs F}
  {S : WildQuadraticSelectedStationaryPairs F K}
  {tauData chiFData : LocalQuasiCharData F}
  {psiF : LocalAddCharData F}

/-- The product-coordinate certificate and the finite lower-product algebra
derive the complete actual `tauChiF` function; no equality with a table
function is stored in the source record. -/
theorem tauChiF_function_exact
    (A : WildQuadraticDerivedCriticalSources F K correction q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .tauChiF = some lambda) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction F,
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          F W S.tauChiF ∧
        W.chi.character = tauData.character * chiFData.character ∧
        W.psi = psiF ∧
        ∀ z, QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
            F W z = (I.toCoefficientData q).function q .tauChiF z := by
  obtain ⟨C⟩ := A.tauChiF h
  refine ⟨C.product, C.product_pair, C.product_character, C.product_psi, ?_⟩
  intro z
  let D := I.toCoefficientData q
  let s := D.lowerProductScaleValue
  let w : ResidueField F := s⁻¹ * z
  have hscale : D.lowerProductScale w = z := by
    rw [D.lowerProductScale_eq_mul]
    dsimp only [w, s]
    rw [← mul_assoc,
      mul_inv_cancel₀ D.lowerProductScaleValue_ne_zero_from_row, one_mul]
  calc
    QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
          F C.product z =
        QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
          F C.product (D.lowerProductScale w) := by rw [hscale]
    _ = I.actualTauFunction (D.lowerTauArgument w) *
          I.actualChiFFunction (D.lowerChiArgument w) :=
      ActualProductCoordinateCertificate.transport F K C w
    _ = D.function q .tau (D.lowerTauArgument w) *
          D.function q .chiF (D.lowerChiArgument w) := by
            rw [I.actualTauFunction_eq_table,
              I.actualChiFFunction_eq_table]
    _ = D.function q .tauChiF (D.lowerProductScale w) :=
      D.lowerProduct_exact q w
    _ = D.function q .tauChiF z := by rw [hscale]

/-- The upper coordinate certificate, exact p/q coordinate table, raw norm
transport, and Frobenius normalization derive the actual upper function in
the common downstairs residue field. -/
theorem chiK_function_exact
    (A : WildQuadraticDerivedCriticalSources F K correction q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .chiK = some lambda) :
    ∃ C : ActualUpperCoordinateCertificate F K correction q I S
        tauData chiFData psiF,
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          K C.upper S.chiK ∧
        C.upper.chi.character = chiFData.character.compNorm ∧
        C.upper.psi.character = psiF.character.compTrace ∧
        ∀ z, QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
            K C.upper (wildQuadraticResidueEquiv F K correction z) =
          (I.toCoefficientData q).function q .chiK z := by
  obtain ⟨C⟩ := A.chiK h
  refine ⟨C, C.upper_pair, C.upper_character, C.upper_additive, ?_⟩
  intro z
  let D := I.toCoefficientData q
  let s := D.commonScale .chiK
  let w : ResidueField F := s⁻¹ * z
  have hscale : s * w = z := by
    dsimp only [w, s]
    rw [← mul_assoc,
      mul_inv_cancel₀ (D.commonScale_ne_zero_from_row .chiK), one_mul]
  calc
    QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
          K C.upper (wildQuadraticResidueEquiv F K correction z) =
        I.actualChiFFunction (D.pTransport (w ^ 2)) *
          I.actualTauFunction (D.qTransport (w ^ 2)) *
            (if D.row.TParity = .odd then
              absoluteTraceChar (ResidueField F)
                (D.qTransport (w ^ 2)) else 1) :=
      ActualUpperCoordinateCertificate.transport F K C z
    _ = D.transportedRawUpper q (w ^ 2) := by
          rw [I.actualChiFFunction_eq_table,
            I.actualTauFunction_eq_table]
          rfl
    _ = D.rawUpperFunction q (w ^ 2) :=
      (D.rawUpper_exact_transport q (w ^ 2)).symm
    _ = D.commonFunction q .chiK w := D.rawUpper_frobenius q w
    _ = D.function q .chiK z := by
      rw [WildQuadraticCoefficientData.commonFunction]
      exact congrArg (D.function q .chiK) hscale

/-- The normalized affine coefficient of the selected actual `tauChiF`
critical function is computed by the table, rather than supplied as a free
coefficient. -/
theorem tauChiF_affineCoefficient_exact
    (A : WildQuadraticDerivedCriticalSources F K correction q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .tauChiF = some lambda) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction F,
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          F W S.tauChiF ∧
        W.chi.character = tauData.character * chiFData.character ∧
        W.psi = psiF ∧
        QuotientDerivedNormalizedCriticalFunction.affineCoefficient
          F W q = lambda := by
  obtain ⟨W, hpair, hchi, hpsi, hfun⟩ := A.tauChiF_function_exact h
  refine ⟨W, hpair, hchi, hpsi, ?_⟩
  change normalizedCriticalPolarGamma q W.toCriticalPolarFunction = lambda
  symm
  apply (WildQuadraticRefinement.existsUnique_criticalFunction q
    W.toCriticalPolarFunction.toHasse).choose_spec.2
  apply HasseFunction.ext
  intro z
  change WildQuadraticRefinement.criticalFunction q lambda z =
    QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction F W z
  rw [hfun z]
  exact ((I.toCoefficientData q).function_eq_critical_of_odd
    q .tauChiF h z).symm

/-- The selected actual `tauChiF` critical function has exactly the phase
stored in the table's denominator factor. -/
theorem tauChiF_phase_exact
    (A : WildQuadraticDerivedCriticalSources F K correction q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .tauChiF = some lambda) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction F,
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          F W S.tauChiF ∧
        W.chi.character = tauData.character * chiFData.character ∧
        W.psi = psiF ∧
        QuotientDerivedNormalizedCriticalFunction.phase F W =
          (I.toCoefficientData q).phaseFactor q .tauChiF := by
  obtain ⟨W, hpair, hchi, hpsi, hcoeff⟩ :=
    A.tauChiF_affineCoefficient_exact h
  refine ⟨W, hpair, hchi, hpsi, ?_⟩
  rw [QuotientDerivedNormalizedCriticalFunction.phase_eq_refinement, hcoeff]
  simp [WildQuadraticCoefficientData.phaseFactor, h]

/-- After transport along the actual extension residue map, the selected
upstairs critical function has the coefficient-table function and therefore
its exact normalized numerator phase. -/
theorem chiK_phase_exact
    (A : WildQuadraticDerivedCriticalSources F K correction q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .chiK = some lambda) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction K,
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
          K W S.chiK ∧
        W.chi.character = chiFData.character.compNorm ∧
        W.psi.character = psiF.character.compTrace ∧
        QuotientDerivedNormalizedCriticalFunction.phase K W =
          (I.toCoefficientData q).phaseFactor q .chiK := by
  obtain ⟨C, hpair, hchi, hpsi, hfun⟩ := A.chiK_function_exact h
  refine ⟨C.upper, hpair, hchi, hpsi, ?_⟩
  have hsum : C.upper.toCriticalPolarFunction.toHasse.sum =
      (WildQuadraticRefinement.criticalFunction q lambda).sum := by
    rw [HasseFunction.sum, HasseFunction.sum]
    symm
    apply Fintype.sum_equiv (wildQuadraticResidueEquiv F K correction).toEquiv
    intro z
    change WildQuadraticRefinement.criticalFunction q lambda z =
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction K C.upper
        (wildQuadraticResidueEquiv F K correction z)
    rw [hfun z]
    exact ((I.toCoefficientData q).function_eq_critical_of_odd
      q .chiK h z).symm
  rw [QuotientDerivedNormalizedCriticalFunction.phase,
    WildQuadraticCoefficientData.phaseFactor, h]
  change phase C.upper.toCriticalPolarFunction.toHasse.sum =
    phase (WildQuadraticRefinement.criticalFunction q lambda).sum
  rw [hsum]

end WildQuadraticDerivedCriticalSources

end ActualDerivedCriticalSources

/-! ## Actual four-phase assembly -/

/-- Phase of one retained lower quotient witness.  `none` is exactly the
literal even-conductor factor and therefore has phase one. -/
noncomputable def quotientSourcePhase
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (source : Option (QuotientDerivedNormalizedCriticalFunction F)) : ℂ :=
  match source with
  | none => 1
  | some W => QuotientDerivedNormalizedCriticalFunction.phase F W

/-- A derived phase is either the literal constant one in an even row, or
comes from an actual quotient-derived function with the selected stationary
pair and exact local characters. -/
def ActualDerivedPhaseSource
    (E k : Type)
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)] [CharP (ResidueField E) 2]
    (coefficient : Option k)
    (P : WildQuadraticStationaryPair E)
    (theta : ContinuousQuasiChar E) (psi : ContinuousAddChar E)
    (value : ℂ) : Prop :=
  match coefficient with
  | none => value = 1
  | some _ =>
      ∃ W : QuotientDerivedNormalizedCriticalFunction E,
        QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
            E W P ∧
          W.chi.character = theta ∧ W.psi.character = psi ∧
          QuotientDerivedNormalizedCriticalFunction.phase E W = value

theorem quotientSourcePhase_tau_eq_table
    {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F) :
    quotientSourcePhase F I.tauSource =
      (I.toCoefficientData q).phaseFactor q .tau := by
  cases I <;>
    simp [quotientSourcePhase, WildQuadraticCoefficientInputs.tauSource,
      WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.belowMOddTEvenComputed,
      WildQuadraticCoefficientData.belowMOddTOddComputed,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.aboveMEvenTOddComputed,
      WildQuadraticCoefficientData.aboveMOddTOddComputed,
      WildQuadraticCoefficientData.affineCoefficient,
      WildQuadraticCoefficientData.phaseFactor]
  all_goals exact
    QuotientDerivedNormalizedCriticalFunction.phase_eq_refinement F _ q

theorem quotientSourcePhase_chiF_eq_table
    {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F) :
    quotientSourcePhase F I.chiFSource =
      (I.toCoefficientData q).phaseFactor q .chiF := by
  cases I <;>
    simp [quotientSourcePhase, WildQuadraticCoefficientInputs.chiFSource,
      WildQuadraticCoefficientInputs.toCoefficientData,
      WildQuadraticCoefficientData.belowMOddTEvenComputed,
      WildQuadraticCoefficientData.belowMOddTOddComputed,
      WildQuadraticCoefficientData.boundaryOddComputed,
      WildQuadraticCoefficientData.aboveMEvenTOddComputed,
      WildQuadraticCoefficientData.aboveMOddTOddComputed,
      WildQuadraticCoefficientData.affineCoefficient,
      WildQuadraticCoefficientData.phaseFactor]
  all_goals exact
    QuotientDerivedNormalizedCriticalFunction.phase_eq_refinement F _ q

/-- Exact numerator/denominator phase assembly for the four stationary
factors.  The lower phases come directly from the retained quotient witnesses;
the two derived phases retain existential, choice-relative stationary
provenance. -/
structure WildQuadraticActualPhaseAssembly
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) : Prop where
  stationaryPairs : I.MatchesStationaryPairs S
  localData : I.MatchesLocalData tauData chiFData psiF
  chiK : ActualDerivedPhaseSource K (ResidueField F)
    ((I.toCoefficientData q).affineCoefficient .chiK) S.chiK
    chiFData.character.compNorm psiF.character.compTrace
    ((I.toCoefficientData q).phaseFactor q .chiK)
  tauChiF : ActualDerivedPhaseSource F (ResidueField F)
    ((I.toCoefficientData q).affineCoefficient .tauChiF) S.tauChiF
    (tauData.character * chiFData.character) psiF.character
    ((I.toCoefficientData q).phaseFactor q .tauChiF)
  phaseRatio_exact :
    (I.toCoefficientData q).phaseFactor q .chiK *
          quotientSourcePhase F I.tauSource /
        (quotientSourcePhase F I.chiFSource *
          (I.toCoefficientData q).phaseFactor q .tauChiF) =
      (I.toCoefficientData q).phaseRatio q

/-- Exact actual four-phase quotient in manuscript orientation:
`chiK * tau / (chiF * tauChiF)`. -/
theorem wildQuadraticActualPhaseRatio_exact
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {T m : ℕ}
    {correction : WildQuadraticCommonCorrectionData F K T m}
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (hpairs : I.MatchesStationaryPairs S)
    (hlocal : I.MatchesLocalData tauData chiFData psiF)
    (A : WildQuadraticDerivedCriticalSources F K correction q I S
      tauData chiFData psiF) :
    WildQuadraticActualPhaseAssembly F K q I S tauData chiFData psiF where
  stationaryPairs := hpairs
  localData := hlocal
  chiK := by
    cases hK : (I.toCoefficientData q).affineCoefficient .chiK with
    | none =>
        simp [ActualDerivedPhaseSource,
          WildQuadraticCoefficientData.phaseFactor, hK]
    | some lambda =>
        obtain ⟨W, hpair, hchi, hpsi, hphase⟩ := A.chiK_phase_exact hK
        exact ⟨W, hpair, hchi, hpsi, hphase⟩
  tauChiF := by
    cases hP : (I.toCoefficientData q).affineCoefficient .tauChiF with
    | none =>
        simp [ActualDerivedPhaseSource,
          WildQuadraticCoefficientData.phaseFactor, hP]
    | some lambda =>
        obtain ⟨W, hpair, hchi, hpsi, hphase⟩ := A.tauChiF_phase_exact hP
        exact ⟨W, hpair, hchi,
          congrArg LocalAddCharData.character hpsi, hphase⟩
  phaseRatio_exact := by
    rw [quotientSourcePhase_tau_eq_table q I,
      quotientSourcePhase_chiF_eq_table q I]
    rfl

/-! ## Coherent formula-facing data -/

namespace WildQuadraticCoefficientData

/-- Coefficient data whose row is forced by the actual downstairs conductor
`m` and lower break `t`; the subtraction recovers `b=m-1`. -/
def AtConductors (k : Type u) [Field k] (m t : ℕ) :=
  {D : WildQuadraticCoefficientData k //
    D.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t}

/-- The residue of the already selected lower norm ratio at the boundary. -/
noncomputable def boundaryNResidue
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {t m : ℕ} (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hboundary : m = t + 1) : ResidueField F :=
  reduce F (C.n : F) (by
    rw [mem_lattice, C.target_order, hboundary]
    simp)

/-- At the odd boundary, `rho` is the residue of the already selected
common-correction unit.  The equality is stated through the extension residue
map and keeps the downstairs lift choice implicit rather than canonical. -/
def MatchesCorrection
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t m : ℕ} (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (D : WildQuadraticCoefficientData (ResidueField F)) : Prop :=
  match D with
  | .boundaryOdd rho _ _ _ _ _ _ _ _ =>
      ∃ hboundary : m = t + 1,
        residueMap K
            (wildQuadraticBoundaryRingUnit F K C hboundary :
              ringOfIntegers K) =
          extensionResidueMap F K rho ∧
        boundaryNResidue F K C hboundary = rho ^ 2
  | _ => True

/-- All three all-even coefficient rows satisfy the correction-matching
contract without any residue refinement data. -/
theorem matchesCorrection_of_isAllEven
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t m : ℕ} (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (D : WildQuadraticCoefficientData (ResidueField F))
    (h : D.row.IsAllEven) : MatchesCorrection F K C D := by
  cases D <;> cases h <;> trivial

end WildQuadraticCoefficientData

/-- The selected CommonCorrection unit upstairs and the choice-relative unit
which places the two odd-boundary lower functions in one coordinate are linked
after canonical residue transport.  No lift is made canonical. -/
structure WildQuadraticBoundaryCorrectionCoordinate
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (rho : ResidueField F)
    (tau chiF : QuotientDerivedNormalizedCriticalFunction F) where
  boundary : m = t + 1
  common : WildQuadraticCoefficientInputs.WildQuadraticBoundaryCommonCoordinate
    (F := F) rho tau chiF
  source_residue :
    residueMap K
        (wildQuadraticBoundaryRingUnit F K C boundary : ringOfIntegers K) =
      extensionResidueMap F K
        (((residueUnits F common.rhoLift : (ResidueField F)ˣ) :
          ResidueField F))
  norm_residue :
    WildQuadraticCoefficientData.boundaryNResidue F K C boundary = rho ^ 2

/-- Existing correction matching and the retained common coordinate produce
the direct link to that same coordinate lift. -/
def WildQuadraticBoundaryCorrectionCoordinate.ofMatches
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t m : ℕ}
    {C : WildQuadraticCommonCorrectionData F K (t + 1) m}
    {rho : ResidueField F}
    {tau chiF : QuotientDerivedNormalizedCriticalFunction F}
    (B : WildQuadraticCoefficientInputs.WildQuadraticBoundaryCommonCoordinate
      (F := F) rho tau chiF)
    (hboundary : m = t + 1)
    (hsource :
      residueMap K
          (wildQuadraticBoundaryRingUnit F K C hboundary :
            ringOfIntegers K) =
        extensionResidueMap F K rho)
    (hnorm : WildQuadraticCoefficientData.boundaryNResidue
      F K C hboundary = rho ^ 2) :
    WildQuadraticBoundaryCorrectionCoordinate F K C rho tau chiF where
  boundary := hboundary
  common := B
  source_residue := by simpa only [B.rhoLift_residue] using hsource
  norm_residue := hnorm

namespace WildQuadraticCoefficientInputs

/-- At the odd boundary, the retained lower common coordinate is the residue
of the same selected correction unit `u`; outside that row there is no extra
coordinate datum. -/
def MatchesBoundaryCorrectionCoordinate
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t m : ℕ} (I : WildQuadraticCoefficientInputs F)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m) : Prop :=
  match I with
  | .boundaryOdd rho _ _ tau chiF =>
      Nonempty (WildQuadraticBoundaryCorrectionCoordinate F K C rho tau chiF)
  | _ => True

/-- The two previously separate boundary facts imply one linked,
choice-relative correction coordinate. -/
theorem matchesBoundaryCorrectionCoordinate_of_matches
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ}
    (q : CharTwoRefinement (ResidueField F))
    (I : WildQuadraticCoefficientInputs F)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hcommon : I.MatchesBoundaryCriticalCoordinates)
    (hcorrection : WildQuadraticCoefficientData.MatchesCorrection F K C
      (I.toCoefficientData q)) :
    I.MatchesBoundaryCorrectionCoordinate F K C := by
  cases I with
  | boundaryOdd rho hrho hden tau chiF =>
      obtain ⟨B⟩ := hcommon
      obtain ⟨hboundary, hsource, hnorm⟩ := hcorrection
      exact ⟨WildQuadraticBoundaryCorrectionCoordinate.ofMatches B
        hboundary hsource hnorm⟩
  | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven | belowMOddTOdd |
      boundaryEven | aboveMEvenTEven | aboveMEvenTOdd | aboveMOddTEven |
      aboveMOddTOdd => trivial

end WildQuadraticCoefficientInputs

/-! ### Q-free formula-facing views -/

/-- The genuinely common coefficient-view data.  It retains the selected
stationary pairs, exact correction ratios, local characters, and actual
quotient-derived lower inputs, but contains neither a characteristic-two
refinement nor any refinement-dependent critical-coordinate certificate. -/
structure WildQuadraticCommonCoefficientView
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (t m : ℕ) where
  conductor_gt_one : 1 < m
  correction : WildQuadraticCommonCorrectionData F K (t + 1) m
  oppositeNoncancellation : correction.OppositeNoncancellation
  stationaryPairs : WildQuadraticSelectedStationaryPairs F K
  chiK_ratio : stationaryPairs.chiK.ratio =
    algebraMap F K stationaryPairs.tau.ratio *
      (algebraMap F K (correction.n : F) - (correction.u : K))
  chiF_ratio : stationaryPairs.chiF.ratio =
    stationaryPairs.tau.ratio * (correction.n : F)
  tauChiF_ratio : stationaryPairs.tauChiF.ratio =
    stationaryPairs.tau.ratio * ((correction.n : F) + 1)
  tauData : LocalQuasiCharData F
  chiFData : LocalQuasiCharData F
  psiF : LocalAddCharData F
  criticalInputs : WildQuadraticCoefficientInputs F
  criticalInputs_row : criticalInputs.row =
    WildQuadraticCoefficientRow.ofConductors (m - 1) t
  criticalInputs_stationaryPairs :
    criticalInputs.MatchesStationaryPairs stationaryPairs
  criticalInputs_localData :
    criticalInputs.MatchesLocalData tauData chiFData psiF
  criticalInputs_boundaryCoordinates :
    criticalInputs.MatchesBoundaryCriticalCoordinates

namespace WildQuadraticCommonCoefficientView

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ}

/-- The exact manuscript row carried by the common view. -/
def row (V : WildQuadraticCommonCoefficientView F K t m) :
    WildQuadraticCoefficientRow :=
  V.criticalInputs.row

@[simp]
theorem row_eq_ofConductors
    (V : WildQuadraticCommonCoefficientView F K t m) :
    V.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t :=
  V.criticalInputs_row

/-- First common-correction unit, with no refinement parameter. -/
noncomputable def z0Unit
    (V : WildQuadraticCommonCoefficientView F K t m) : Fˣ :=
  V.correction.z0Unit V.oppositeNoncancellation

/-- Second common-correction unit, with no refinement parameter. -/
noncomputable def z1Unit
    (V : WildQuadraticCommonCoefficientView F K t m) : Fˣ :=
  V.correction.z1Unit V.oppositeNoncancellation

@[simp]
theorem coe_z0Unit (V : WildQuadraticCommonCoefficientView F K t m) :
    (V.z0Unit : F) = V.correction.z0 := rfl

@[simp]
theorem coe_z1Unit (V : WildQuadraticCommonCoefficientView F K t m) :
    (V.z1Unit : F) = V.correction.z1 := rfl

/-- Canonical residue-field identification for this exact common correction. -/
noncomputable def residueEquiv
    (V : WildQuadraticCommonCoefficientView F K t m) :
    ResidueField F ≃+* ResidueField K :=
  wildQuadraticResidueEquiv F K V.correction

@[simp]
theorem residueEquiv_apply
    (V : WildQuadraticCommonCoefficientView F K t m)
    (z : ResidueField F) :
    V.residueEquiv z = extensionResidueMap F K z := rfl

end WildQuadraticCommonCoefficientView

/-- Q-free formula-facing data for exactly one of the three all-even rows. -/
structure WildQuadraticAllEvenCoefficientView
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (t m : ℕ) extends WildQuadraticCommonCoefficientView F K t m where
  isAllEven : criticalInputs.row.IsAllEven

namespace WildQuadraticAllEvenCoefficientView

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ}

/-- Forget only the exact all-even witness. -/
abbrev toCommon (V : WildQuadraticAllEvenCoefficientView F K t m) :
    WildQuadraticCommonCoefficientView F K t m :=
  V.toWildQuadraticCommonCoefficientView

/-- The exact row carried by this all-even view. -/
def row (V : WildQuadraticAllEvenCoefficientView F K t m) :
    WildQuadraticCoefficientRow :=
  V.criticalInputs.row

@[simp]
theorem row_eq_ofConductors
    (V : WildQuadraticAllEvenCoefficientView F K t m) :
    V.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t :=
  V.criticalInputs_row

/-- Q-free coefficient data reconstructed from the exact all-even input. -/
def coefficients (V : WildQuadraticAllEvenCoefficientView F K t m) :
    WildQuadraticCoefficientData.AtConductors (ResidueField F) m t :=
  ⟨V.criticalInputs.toAllEvenCoefficientData V.isAllEven, by
    rw [WildQuadraticCoefficientInputs.toAllEvenCoefficientData_row,
      V.criticalInputs_row]⟩

/-- Exact q-free constructor for the below-break even/even pattern. -/
def ofBelowMEvenTEven
    (V : WildQuadraticCommonCoefficientView F K t m)
    (h : V.criticalInputs = .belowMEvenTEven) :
    WildQuadraticAllEvenCoefficientView F K t m where
  toWildQuadraticCommonCoefficientView := V
  isAllEven := by rw [h]; exact .belowMEvenTEven

/-- Exact q-free constructor for the boundary-even pattern. -/
def ofBoundaryEven
    (V : WildQuadraticCommonCoefficientView F K t m)
    (h : V.criticalInputs = .boundaryEven) :
    WildQuadraticAllEvenCoefficientView F K t m where
  toWildQuadraticCommonCoefficientView := V
  isAllEven := by rw [h]; exact .boundaryEven

/-- Exact q-free constructor for the above-break even/even pattern. -/
def ofAboveMEvenTEven
    (V : WildQuadraticCommonCoefficientView F K t m)
    (h : V.criticalInputs = .aboveMEvenTEven) :
    WildQuadraticAllEvenCoefficientView F K t m where
  toWildQuadraticCommonCoefficientView := V
  isAllEven := by rw [h]; exact .aboveMEvenTEven

/-- Q-free forwarding API for the first correction unit. -/
noncomputable abbrev z0Unit
    (V : WildQuadraticAllEvenCoefficientView F K t m) : Fˣ :=
  V.toCommon.z0Unit

/-- Q-free forwarding API for the second correction unit. -/
noncomputable abbrev z1Unit
    (V : WildQuadraticAllEvenCoefficientView F K t m) : Fˣ :=
  V.toCommon.z1Unit

@[simp]
theorem coe_z0Unit (V : WildQuadraticAllEvenCoefficientView F K t m) :
    (V.z0Unit : F) = V.correction.z0 := rfl

@[simp]
theorem coe_z1Unit (V : WildQuadraticAllEvenCoefficientView F K t m) :
    (V.z1Unit : F) = V.correction.z1 := rfl

/-- Q-free forwarding API for the canonical residue-field identification. -/
noncomputable abbrev residueEquiv
    (V : WildQuadraticAllEvenCoefficientView F K t m) :
    ResidueField F ≃+* ResidueField K :=
  V.toCommon.residueEquiv

@[simp]
theorem residueEquiv_apply
    (V : WildQuadraticAllEvenCoefficientView F K t m)
    (z : ResidueField F) :
    V.residueEquiv z = extensionResidueMap F K z := rfl

/-- Correction matching is automatic in each exact all-even row and needs no
refinement-dependent boundary coordinate. -/
theorem matchesCorrection
    (V : WildQuadraticAllEvenCoefficientView F K t m) :
    WildQuadraticCoefficientData.MatchesCorrection F K V.correction
      V.coefficients.1 := by
  change WildQuadraticCoefficientData.MatchesCorrection F K V.correction
    (V.criticalInputs.toAllEvenCoefficientData V.isAllEven)
  exact WildQuadraticCoefficientData.matchesCorrection_of_isAllEven F K
    V.correction (V.criticalInputs.toAllEvenCoefficientData V.isAllEven)
      (by
        rw [WildQuadraticCoefficientInputs.toAllEvenCoefficientData_row]
        exact V.isAllEven)

end WildQuadraticAllEvenCoefficientView

/-- Coherent output for the later error formula.  All four exact stationary
ratios use the same selected `u,n`; the coefficient row is fixed by the same
conductor indices, and the boundary residue coordinate is tied to that `u`. -/
structure WildQuadraticCoefficientView
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (q : CharTwoRefinement (ResidueField F)) (t m : ℕ) where
  conductor_gt_one : 1 < m
  correction : WildQuadraticCommonCorrectionData F K (t + 1) m
  oppositeNoncancellation : correction.OppositeNoncancellation
  stationaryPairs : WildQuadraticSelectedStationaryPairs F K
  chiK_ratio : stationaryPairs.chiK.ratio =
    algebraMap F K stationaryPairs.tau.ratio *
      (algebraMap F K (correction.n : F) - (correction.u : K))
  chiF_ratio : stationaryPairs.chiF.ratio =
    stationaryPairs.tau.ratio * (correction.n : F)
  tauChiF_ratio : stationaryPairs.tauChiF.ratio =
    stationaryPairs.tau.ratio * ((correction.n : F) + 1)
  tauData : LocalQuasiCharData F
  chiFData : LocalQuasiCharData F
  psiF : LocalAddCharData F
  criticalInputs : WildQuadraticCoefficientInputs F
  criticalInputs_row : criticalInputs.row =
    WildQuadraticCoefficientRow.ofConductors (m - 1) t
  criticalInputs_stationaryPairs :
    criticalInputs.MatchesStationaryPairs stationaryPairs
  criticalInputs_localData :
    criticalInputs.MatchesLocalData tauData chiFData psiF
  criticalInputs_boundaryCoordinates :
    criticalInputs.MatchesBoundaryCriticalCoordinates
  derivedCriticalSources : WildQuadraticDerivedCriticalSources F K correction q
    criticalInputs stationaryPairs tauData chiFData psiF
  boundaryCoordinate :
    WildQuadraticCoefficientData.MatchesCorrection F K correction
      (criticalInputs.toCoefficientData q)

namespace WildQuadraticCoefficientView

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {q : CharTwoRefinement (ResidueField F)}
  {t m : ℕ}

/-- Forget the refinement-dependent critical-coordinate certificates while
retaining every common stationary, correction, and local-character field. -/
def toCommon (V : WildQuadraticCoefficientView F K q t m) :
    WildQuadraticCommonCoefficientView F K t m where
  conductor_gt_one := V.conductor_gt_one
  correction := V.correction
  oppositeNoncancellation := V.oppositeNoncancellation
  stationaryPairs := V.stationaryPairs
  chiK_ratio := V.chiK_ratio
  chiF_ratio := V.chiF_ratio
  tauChiF_ratio := V.tauChiF_ratio
  tauData := V.tauData
  chiFData := V.chiFData
  psiF := V.psiF
  criticalInputs := V.criticalInputs
  criticalInputs_row := V.criticalInputs_row
  criticalInputs_stationaryPairs := V.criticalInputs_stationaryPairs
  criticalInputs_localData := V.criticalInputs_localData
  criticalInputs_boundaryCoordinates :=
    V.criticalInputs_boundaryCoordinates

/-- Forget a refined view's `q` exactly when its actual row carries one of
the three all-even witnesses. -/
def toAllEven (V : WildQuadraticCoefficientView F K q t m)
    (h : V.criticalInputs.row.IsAllEven) :
    WildQuadraticAllEvenCoefficientView F K t m where
  toWildQuadraticCommonCoefficientView := V.toCommon
  isAllEven := h

/-- The coefficient data are constructed from the retained quotient-derived
critical inputs; they are not an independently supplied table row. -/
noncomputable def coefficients (V : WildQuadraticCoefficientView F K q t m) :
    WildQuadraticCoefficientData.AtConductors (ResidueField F) m t :=
  ⟨V.criticalInputs.toCoefficientData q, by
    rw [WildQuadraticCoefficientInputs.toCoefficientData_row,
      V.criticalInputs_row]⟩

/-- First common-correction unit, still attached to the selected package. -/
noncomputable def z0Unit (V : WildQuadraticCoefficientView F K q t m) : Fˣ :=
  V.correction.z0Unit V.oppositeNoncancellation

/-- Second common-correction unit. -/
noncomputable def z1Unit (V : WildQuadraticCoefficientView F K q t m) : Fˣ :=
  V.correction.z1Unit V.oppositeNoncancellation

@[simp]
theorem coe_z0Unit (V : WildQuadraticCoefficientView F K q t m) :
    (V.z0Unit : F) = V.correction.z0 := rfl

@[simp]
theorem coe_z1Unit (V : WildQuadraticCoefficientView F K q t m) :
    (V.z1Unit : F) = V.correction.z1 := rfl

/-- Canonical identification of the downstairs and upstairs residue fields
for this exact CommonCorrection package. -/
noncomputable def residueEquiv
    (V : WildQuadraticCoefficientView F K q t m) :
    ResidueField F ≃+* ResidueField K :=
  wildQuadraticResidueEquiv F K V.correction

@[simp]
theorem residueEquiv_apply
    (V : WildQuadraticCoefficientView F K q t m) (z : ResidueField F) :
    V.residueEquiv z = extensionResidueMap F K z := rfl

/-- The boundary critical coordinate and the CommonCorrection unit are the
same choice after residue transport. -/
theorem boundaryCorrectionCoordinate
    (V : WildQuadraticCoefficientView F K q t m) :
    V.criticalInputs.MatchesBoundaryCorrectionCoordinate F K V.correction :=
  V.criticalInputs.matchesBoundaryCorrectionCoordinate_of_matches q
    V.correction V.criticalInputs_boundaryCoordinates V.boundaryCoordinate

/-- Actual four-phase quotient carried by this coherent view. -/
theorem actualPhaseAssembly
    (V : WildQuadraticCoefficientView F K q t m) :
    WildQuadraticActualPhaseAssembly F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF :=
  wildQuadraticActualPhaseRatio_exact q V.criticalInputs V.stationaryPairs
    V.tauData V.chiFData V.psiF V.criticalInputs_stationaryPairs
      V.criticalInputs_localData V.derivedCriticalSources

end WildQuadraticCoefficientView

/-! ### Provenance-preserving low package -/

/-- The low package retains the actual simultaneous representative pair
selected by the low-parameter theorem. -/
structure WildQuadraticLowCoefficientPackage
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2] where
  lowerBreak : ℕ
  stationaryDepth : ℕ
  conductorRemainder : ℕ
  ht : PrimeCyclicExtension.IsLowerBreak F K lowerBreak
  hres : residueDegree F K = 1
  pi : ringOfIntegers K
  hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)
  hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤
  hdegree : Module.finrank F K = 2
  chi : LocalQuasiCharData F
  psi : LocalAddCharData F
  hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi
  hF : IsStationaryConductorDecomposition chi.conductor stationaryDepth
    conductorRemainder
  hLow : chi.conductor ≤ lowerBreak + 1
  delta : Fˣ
  epsilon1 : Kˣ
  hdelta : ord F (delta : F) =
    ((((lowerBreak + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ)
  hepsilon1 : ord K (epsilon1 : K) =
    (((lowerBreak + 1 - chi.conductor : ℕ) : ℤ) : WithTop ℤ)
  hT : 2 ≤ lowerBreak + 1
  hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)
  selected : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth lowerBreak) stationaryDepth
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1
          (lowerBreak + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      psi (lowCriticalConductorDecomposition (t := lowerBreak) hT) delta hdelta)
    (stationaryCoefficientClass F chi psi hF
      (lowGammaF F K delta epsilon1) hgammaF)
  q : CharTwoRefinement (ResidueField F)
  criticalInputs : WildQuadraticCoefficientInputs F
  criticalInputs_row : criticalInputs.row =
    WildQuadraticCoefficientRow.ofConductors (chi.conductor - 1) lowerBreak
  criticalInputs_stationaryPairs : criticalInputs.MatchesStationaryPairs
    (lowWildQuadraticSelectedStationaryPairs delta epsilon1 selected)
  criticalInputs_localData : criticalInputs.MatchesLocalData
    (quasiCharDataOfIsConductor F
      (lowNormCharacterGenerator F K ht hres pi hpi hgen).1
        (lowerBreak + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (lowNormCharacterGenerator F K ht hres pi hpi hgen)
        (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
    chi psi
  criticalInputs_boundaryCoordinates :
    criticalInputs.MatchesBoundaryCriticalCoordinates
  derivedCriticalSources : WildQuadraticDerivedCriticalSources F K
    (lowWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree chi psi
      hminimal hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF selected) q
    criticalInputs
    (lowWildQuadraticSelectedStationaryPairs delta epsilon1 selected)
    (quasiCharDataOfIsConductor F
      (lowNormCharacterGenerator F K ht hres pi hpi hgen).1
        (lowerBreak + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (lowNormCharacterGenerator F K ht hres pi hpi hgen)
        (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
    chi psi
  boundaryCoordinate : WildQuadraticCoefficientData.MatchesCorrection F K
    (lowWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree chi psi
      hminimal hF hLow delta epsilon1 hdelta hepsilon1 hT hgammaF selected)
    (criticalInputs.toCoefficientData q)

namespace WildQuadraticLowCoefficientPackage

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- The common correction built from this exact selected pair. -/
noncomputable def correction (P : WildQuadraticLowCoefficientPackage F K) :
    WildQuadraticCommonCorrectionData F K (P.lowerBreak + 1)
      P.chi.conductor :=
  lowWildQuadraticCommonCorrection P.ht P.hres P.pi P.hpi P.hgen P.hdegree
    P.chi P.psi P.hminimal P.hF P.hLow P.delta P.epsilon1 P.hdelta
      P.hepsilon1 P.hT P.hgammaF P.selected

/-- The noncancellation proof comes from the same selected pair. -/
theorem oppositeNoncancellation (P : WildQuadraticLowCoefficientPackage F K) :
    P.correction.OppositeNoncancellation :=
  lowWildQuadraticCommonCorrection_oppositeNoncancellation P.ht P.hres P.pi
    P.hpi P.hgen P.hdegree P.chi P.psi P.hminimal P.hF P.hLow P.delta
      P.epsilon1 P.hdelta P.hepsilon1 P.hT P.hgammaF P.selected

/-- Exact four low numerator/denominator pairs from the same pair `selected`. -/
noncomputable def stationaryPairs
    (P : WildQuadraticLowCoefficientPackage F K) :
    WildQuadraticSelectedStationaryPairs F K :=
  lowWildQuadraticSelectedStationaryPairs P.delta P.epsilon1 P.selected

/-- The four pairs and the common correction are coherent: all three
nontrivial ratios use the same selected `u,n` and the tau ratio. -/
theorem stationaryPairs_ratios
    (P : WildQuadraticLowCoefficientPackage F K) :
    let S := P.stationaryPairs
    let C := P.correction
    S.chiK.ratio = algebraMap F K S.tau.ratio *
        (algebraMap F K (C.n : F) - (C.u : K)) ∧
    S.chiF.ratio = S.tau.ratio * (C.n : F) ∧
    S.tauChiF.ratio = S.tau.ratio * ((C.n : F) + 1) := by
  have h := lowWildQuadraticSelectedStationaryPairs_ratios P.delta
    P.epsilon1 P.selected
  rcases h with ⟨hK, hTau, hChi, hTauChi⟩
  dsimp only [stationaryPairs, correction]
  rw [hTau]
  simp only [lowWildQuadraticCommonCorrection, lowWildQuadraticCommonU_coe]
  refine ⟨?_, ?_, ?_⟩
  · simpa [lowWildQuadraticCommonN] using hK
  · simpa [lowWildQuadraticCommonN] using hChi
  · simpa [lowWildQuadraticCommonN] using hTauChi

/-- Coherent formula-facing view of the low package. -/
noncomputable def toView (P : WildQuadraticLowCoefficientPackage F K) :
    WildQuadraticCoefficientView F K P.q P.lowerBreak P.chi.conductor :=
  let hratios := P.stationaryPairs_ratios
  { conductor_gt_one := P.hF.conductor_gt_one
    correction := P.correction
    oppositeNoncancellation := P.oppositeNoncancellation
    stationaryPairs := P.stationaryPairs
    chiK_ratio := hratios.1
    chiF_ratio := hratios.2.1
    tauChiF_ratio := hratios.2.2
    tauData := quasiCharDataOfIsConductor F
      (lowNormCharacterGenerator F K P.ht P.hres P.pi P.hpi P.hgen).1
        (P.lowerBreak + 1)
      (ramifiedNormCharacter_conductor F K P.ht P.hres P.pi P.hpi P.hgen
        (lowNormCharacterGenerator F K P.ht P.hres P.pi P.hpi P.hgen)
        (lowNormCharacterGenerator_ne_one F K P.ht P.hres P.pi P.hpi P.hgen))
    chiFData := P.chi
    psiF := P.psi
    criticalInputs := P.criticalInputs
    criticalInputs_row := P.criticalInputs_row
    criticalInputs_stationaryPairs := P.criticalInputs_stationaryPairs
    criticalInputs_localData := P.criticalInputs_localData
    criticalInputs_boundaryCoordinates :=
      P.criticalInputs_boundaryCoordinates
    derivedCriticalSources := P.derivedCriticalSources
    boundaryCoordinate := P.boundaryCoordinate }

end WildQuadraticLowCoefficientPackage

/-! ### Provenance-preserving high package -/

/-- The high package retains the complete high-parameter object, including
its selected representatives and essential break-level correction unit. -/
structure WildQuadraticHighCoefficientPackage
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2] where
  lowerBreak : ℕ
  ht : PrimeCyclicExtension.IsLowerBreak F K lowerBreak
  hres : residueDegree F K = 1
  pi : ringOfIntegers K
  hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)
  hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤
  hdegree : Module.finrank F K = 2
  htpos : 0 < lowerBreak
  chiF : LocalQuasiCharData F
  chiK : LocalQuasiCharData K
  psiF : LocalAddCharData F
  psiK : LocalAddCharData K
  stationaryDepthF : ℕ
  conductorRemainderF : ℕ
  stationaryDepthK : ℕ
  conductorRemainderK : ℕ
  hF : IsStationaryConductorDecomposition chiF.conductor stationaryDepthF
    conductorRemainderF
  hK : IsStationaryConductorDecomposition chiK.conductor stationaryDepthK
    conductorRemainderK
  hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF
  hhigh : lowerBreak + 1 ≤ chiF.conductor
  /-- The coefficient-table dispatch uses the high package only in the strict
  range `b > t`; the boundary remains in the low package. -/
  hstrict : lowerBreak + 1 < chiF.conductor
  hchi : chiK.character = chiF.character.compNorm
  hpsi : psiK.character = psiF.character.compTrace
  tau : NormCharacter F K
  htau : tau ≠ 1
  gammaF : Fˣ
  hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)
  selected : WildQuadraticHighParameterData
    F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF
  q : CharTwoRefinement (ResidueField F)
  criticalInputs : WildQuadraticCoefficientInputs F
  criticalInputs_row : criticalInputs.row =
    WildQuadraticCoefficientRow.ofConductors (chiF.conductor - 1) lowerBreak
  criticalInputs_stationaryPairs : criticalInputs.MatchesStationaryPairs
    (highWildQuadraticSelectedStationaryPairs selected.representatives)
  criticalInputs_localData : criticalInputs.MatchesLocalData
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) chiF psiF
  criticalInputs_boundaryCoordinates :
    criticalInputs.MatchesBoundaryCriticalCoordinates
  derivedCriticalSources : WildQuadraticDerivedCriticalSources F K
    (highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree htpos
      chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau gammaF
        hgammaF selected) q criticalInputs
    (highWildQuadraticSelectedStationaryPairs selected.representatives)
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) chiF psiF
  boundaryCoordinate : WildQuadraticCoefficientData.MatchesCorrection F K
    (highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree htpos
      chiF chiK psiF psiK hF hK hminimal hhigh hchi hpsi tau htau gammaF
        hgammaF selected) (criticalInputs.toCoefficientData q)

namespace WildQuadraticHighCoefficientPackage

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- Common correction extracted from the retained full high package. -/
noncomputable def correction (P : WildQuadraticHighCoefficientPackage F K) :
    WildQuadraticCommonCorrectionData F K (P.lowerBreak + 1)
      P.chiF.conductor :=
  highWildQuadraticCommonCorrection P.ht P.hres P.pi P.hpi P.hgen P.hdegree
    P.htpos P.chiF P.chiK P.psiF P.psiK P.hF P.hK P.hminimal P.hhigh P.hchi
      P.hpsi P.tau P.htau P.gammaF P.hgammaF P.selected

/-- Opposite noncancellation proved for the same full high package. -/
theorem oppositeNoncancellation
    (P : WildQuadraticHighCoefficientPackage F K) :
    P.correction.OppositeNoncancellation :=
  highWildQuadraticCommonCorrection_oppositeNoncancellation P.ht P.hres P.pi
    P.hpi P.hgen P.hdegree P.htpos P.chiF P.chiK P.psiF P.psiK P.hF P.hK
      P.hminimal P.hhigh P.hchi P.hpsi P.tau P.htau P.gammaF P.hgammaF
        P.selected

/-- Exact four high numerator/denominator pairs from the retained
representative record. -/
noncomputable def stationaryPairs
    (P : WildQuadraticHighCoefficientPackage F K) :
    WildQuadraticSelectedStationaryPairs F K :=
  highWildQuadraticSelectedStationaryPairs P.selected.representatives

/-- The essential high correction unit remains directly visible. -/
noncomputable def delta (P : WildQuadraticHighCoefficientPackage F K) : Fˣ :=
  P.selected.representatives.delta

/-- The common norm ratio retains the exact denominator
`alpha * delta`; the correction unit is not discarded. -/
theorem correction_n_with_delta
    (P : WildQuadraticHighCoefficientPackage F K) :
    P.correction.n = P.selected.representatives.beta /
      (P.selected.representatives.alpha *
        (P.selected.representatives.delta : Fˣ)) :=
  highWildQuadraticCommonCorrection_n_with_delta P.ht P.hres P.pi P.hpi
    P.hgen P.hdegree P.htpos P.chiF P.chiK P.psiF P.psiK P.hF P.hK
      P.hminimal P.hhigh P.hchi P.hpsi P.tau P.htau P.gammaF P.hgammaF
        P.selected

/-- All high stationary ratios use the same selected correction `u,n`. -/
theorem stationaryPairs_ratios
    (P : WildQuadraticHighCoefficientPackage F K) :
    let S := P.stationaryPairs
    let C := P.correction
    S.chiK.ratio = algebraMap F K S.tau.ratio *
        (algebraMap F K (C.n : F) - (C.u : K)) ∧
    S.chiF.ratio = S.tau.ratio * (C.n : F) ∧
    S.tauChiF.ratio = S.tau.ratio * ((C.n : F) + 1) := by
  have h := highWildQuadraticSelectedStationaryPairs_ratios
    P.selected.representatives
  rcases h with ⟨hK, hTau, hChi, hTauChi⟩
  dsimp only [stationaryPairs, correction]
  rw [hTau]
  refine ⟨?_, ?_, ?_⟩
  · simpa [highWildQuadraticCommonCorrection] using hK
  · simpa [highWildQuadraticCommonCorrection] using hChi
  · simpa [highWildQuadraticCommonCorrection] using hTauChi

/-- Coherent formula-facing view of the high package. -/
noncomputable def toView (P : WildQuadraticHighCoefficientPackage F K) :
    WildQuadraticCoefficientView F K P.q P.lowerBreak P.chiF.conductor :=
  let hratios := P.stationaryPairs_ratios
  { conductor_gt_one := P.hF.conductor_gt_one
    correction := P.correction
    oppositeNoncancellation := P.oppositeNoncancellation
    stationaryPairs := P.stationaryPairs
    chiK_ratio := hratios.1
    chiF_ratio := hratios.2.1
    tauChiF_ratio := hratios.2.2
    tauData := wildQuadraticHighTauData F K P.ht P.hres P.pi P.hpi P.hgen
      P.tau P.htau
    chiFData := P.chiF
    psiF := P.psiF
    criticalInputs := P.criticalInputs
    criticalInputs_row := P.criticalInputs_row
    criticalInputs_stationaryPairs := P.criticalInputs_stationaryPairs
    criticalInputs_localData := P.criticalInputs_localData
    criticalInputs_boundaryCoordinates :=
      P.criticalInputs_boundaryCoordinates
    derivedCriticalSources := P.derivedCriticalSources
    boundaryCoordinate := P.boundaryCoordinate }

end WildQuadraticHighCoefficientPackage

/-! ## Certified coefficient table -/

/-- The q-free finite-field certificate carried by exactly the three
all-even rows.  Every affine coefficient is absent and both the normalized
and raw upper factors are literal constants before any refinement is chosen. -/
structure WildQuadraticAllEvenCoefficientCertificate
    {k : Type u} [Field k]
    (D : WildQuadraticCoefficientData k) : Prop where
  row_isAllEven : D.row.IsAllEven
  affineCoefficient_eq_none : ∀ theta, D.affineCoefficient theta = none
  factor_eq_constant : ∀ theta,
    D.factor theta = (.constant : WildQuadraticResidualFactor k)
  commonScale_eq_one : ∀ theta, D.commonScale theta = 1
  rawUpperAffineCoefficient_eq_none : D.rawUpperAffineCoefficient = none
  rawUpperFactor_eq_constant :
    D.rawUpperFactor = (.constant : WildQuadraticResidualFactor k)
  rawUpperScale_eq_one : D.rawUpperScale = 1

/-- Q-free certificate for any coefficient datum carrying an exact all-even
row witness. -/
theorem wildQuadraticAllEvenCoefficientCertificate
    {k : Type u} [Field k]
    (D : WildQuadraticCoefficientData k) (h : D.row.IsAllEven) :
    WildQuadraticAllEvenCoefficientCertificate D where
  row_isAllEven := h
  affineCoefficient_eq_none := by
    intro theta
    cases D <;> cases h <;> cases theta <;> rfl
  factor_eq_constant := by
    intro theta
    cases D <;> cases h <;> cases theta <;> rfl
  commonScale_eq_one := by
    intro theta
    cases D <;> cases h <;> cases theta <;> rfl
  rawUpperAffineCoefficient_eq_none := by
    cases D <;> cases h <;> rfl
  rawUpperFactor_eq_constant := by
    cases D <;> cases h <;> rfl
  rawUpperScale_eq_one := by
    cases D <;> cases h <;> rfl

/-- All proof-bearing facts exposed to the later error formula for one row. -/
structure WildQuadraticCoefficientCertificate
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) (D : WildQuadraticCoefficientData k) : Prop where
  occurrence_exact : ∀ theta,
    (D.affineCoefficient theta).isSome =
      decide (D.row.characterParity theta = .odd)
  upper_square_exact :
    (D.affineCoefficient .chiK).map (fun gammaPrime => gammaPrime ^ 2) =
      D.rawUpperAffineCoefficient
  normalized_upper_exact :
    D.affineCoefficient .chiK =
      D.rawUpperAffineCoefficient.map WildQuadraticRefinement.squareRoot
  even_is_constant : ∀ theta,
    D.affineCoefficient theta = none → ∀ z, D.function q theta z = 1
  odd_is_affine : ∀ theta lambda,
    D.affineCoefficient theta = some lambda → ∀ z,
      D.function q theta z =
        WildQuadraticRefinement.criticalFunction q lambda z
  positive_common_polar : ∀ theta x y,
    D.commonFunction q theta (x + y) =
      D.commonFunction q theta x * D.commonFunction q theta y *
        absoluteTraceChar k
          (((D.commonScale theta) ^ 2 * (D.factor theta).polarValue) *
            (x * y))
  representative_translation : ∀ theta lambda,
    D.affineCoefficient theta = some lambda → ∀ a z,
      D.representativeTranslate q theta a z =
        q (D.commonScale theta * z) *
          absoluteTraceChar k
            (((D.commonScale theta * lambda) +
              (D.commonScale theta) ^ 2 * a) * z)
  exact_residue_transport : ∀ z,
    D.rawUpperFunction q z = D.transportedRawUpper q z
  upper_frobenius : ∀ z,
    D.rawUpperFunction q (z ^ 2) = D.commonFunction q .chiK z

/-- Finite-field certificate for one of the ten table constructors. -/
theorem wildQuadraticCoefficientCertificate
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) (D : WildQuadraticCoefficientData k) :
    WildQuadraticCoefficientCertificate q D where
  occurrence_exact := D.coefficient_exists_iff_odd
  upper_square_exact := D.chiKCoefficient_sq
  normalized_upper_exact := D.chiKCoefficient_eq_squareRoot
  even_is_constant := fun theta h z => D.function_eq_one_of_even q theta h z
  odd_is_affine := fun theta lambda h z =>
    D.function_eq_critical_of_odd q theta h z
  positive_common_polar := D.commonFunction_positivePolar q
  representative_translation := fun theta lambda h a z =>
    D.representativeTranslate_eq_affine_of_odd q theta h a z
  exact_residue_transport := D.rawUpper_exact_transport q
  upper_frobenius := D.rawUpper_frobenius q

/-- Principal q-free table for one of the three exact all-even manuscript
patterns.  It retains the same correction, stationary-pair, local-character,
and residue-coordinate data as the refined table, while requiring neither
`q` nor a refinement-dependent critical-coordinate certificate. -/
theorem WildQuadraticAllEvenCoefficientTable
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ} (V : WildQuadraticAllEvenCoefficientView F K t m) :
    let D := V.coefficients.1
    WildQuadraticAllEvenCoefficientCertificate D ∧
    D.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t ∧
    D.row.IsAllEven ∧
    1 < m ∧
    V.criticalInputs.tauSource = none ∧
    V.criticalInputs.chiFSource = none ∧
    V.criticalInputs.MatchesStationaryPairs V.stationaryPairs ∧
    V.criticalInputs.MatchesLocalData V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCriticalCoordinates ∧
    V.stationaryPairs.chiK.ratio =
      algebraMap F K V.stationaryPairs.tau.ratio *
        (algebraMap F K (V.correction.n : F) - (V.correction.u : K)) ∧
    V.stationaryPairs.chiF.ratio =
      V.stationaryPairs.tau.ratio * (V.correction.n : F) ∧
    V.stationaryPairs.tauChiF.ratio =
      V.stationaryPairs.tau.ratio * ((V.correction.n : F) + 1) ∧
    WildQuadraticCoefficientData.MatchesCorrection F K V.correction D ∧
    (V.z0Unit : F) = V.correction.z0 ∧
    (V.z1Unit : F) = V.correction.z1 := by
  have hrow : V.coefficients.1.row.IsAllEven := by
    change (V.criticalInputs.toAllEvenCoefficientData V.isAllEven).row.IsAllEven
    rw [WildQuadraticCoefficientInputs.toAllEvenCoefficientData_row]
    exact V.isAllEven
  exact ⟨wildQuadraticAllEvenCoefficientCertificate V.coefficients.1 hrow,
    V.coefficients.2, hrow, V.conductor_gt_one,
    V.criticalInputs.tauSource_eq_none_of_isAllEven V.isAllEven,
    V.criticalInputs.chiFSource_eq_none_of_isAllEven V.isAllEven,
    V.criticalInputs_stationaryPairs, V.criticalInputs_localData,
    V.criticalInputs_boundaryCoordinates, V.chiK_ratio, V.chiF_ratio,
    V.tauChiF_ratio, V.matchesCorrection, rfl, rfl⟩

/-- Principal complete wild-quadratic coefficient table.  Unlike the raw
finite certificate, this theorem consumes the coherent view attached to the
actual conductor, correction, residue coordinate, and selected stationary
pairs. -/
theorem WildQuadraticCoefficientTable
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (q : CharTwoRefinement (ResidueField F)) {t m : ℕ}
    (V : WildQuadraticCoefficientView F K q t m) :
    let D := V.coefficients.1
    WildQuadraticCoefficientCertificate q D ∧
    D.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t ∧
    1 < m ∧
    V.criticalInputs.MatchesStationaryPairs V.stationaryPairs ∧
    V.criticalInputs.MatchesLocalData V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCriticalCoordinates ∧
    WildQuadraticDerivedCriticalSources F K V.correction q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF ∧
    WildQuadraticActualPhaseAssembly F K q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCorrectionCoordinate F K V.correction ∧
    V.stationaryPairs.chiK.ratio =
      algebraMap F K V.stationaryPairs.tau.ratio *
        (algebraMap F K (V.correction.n : F) - (V.correction.u : K)) ∧
    V.stationaryPairs.chiF.ratio =
      V.stationaryPairs.tau.ratio * (V.correction.n : F) ∧
    V.stationaryPairs.tauChiF.ratio =
      V.stationaryPairs.tau.ratio * ((V.correction.n : F) + 1) ∧
    WildQuadraticCoefficientData.MatchesCorrection F K V.correction D ∧
    (V.z0Unit : F) = V.correction.z0 ∧
    (V.z1Unit : F) = V.correction.z1 := by
  exact ⟨wildQuadraticCoefficientCertificate q V.coefficients.1,
    V.coefficients.2, V.conductor_gt_one,
    V.criticalInputs_stationaryPairs, V.criticalInputs_localData,
    V.criticalInputs_boundaryCoordinates,
    V.derivedCriticalSources,
    V.actualPhaseAssembly, V.boundaryCorrectionCoordinate,
    V.chiK_ratio, V.chiF_ratio, V.tauChiF_ratio, V.boundaryCoordinate,
    rfl, rfl⟩

/-- Low-range specialization of the principal table.  Its statement remains
indexed by the full low parameter package, so the selected representative
record is not erased by passage to the formula-facing view. -/
theorem WildQuadraticLowCoefficientTable
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (P : WildQuadraticLowCoefficientPackage F K) :
    let V := P.toView
    let D := V.coefficients.1
    WildQuadraticCoefficientCertificate P.q D ∧
    D.row = WildQuadraticCoefficientRow.ofConductors
      (P.chi.conductor - 1) P.lowerBreak ∧
    1 < P.chi.conductor ∧
    V.criticalInputs.MatchesStationaryPairs V.stationaryPairs ∧
    V.criticalInputs.MatchesLocalData V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCriticalCoordinates ∧
    WildQuadraticDerivedCriticalSources F K V.correction P.q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF ∧
    WildQuadraticActualPhaseAssembly F K P.q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCorrectionCoordinate F K V.correction ∧
    V.stationaryPairs.chiK.ratio =
      algebraMap F K V.stationaryPairs.tau.ratio *
        (algebraMap F K (V.correction.n : F) - (V.correction.u : K)) ∧
    V.stationaryPairs.chiF.ratio =
      V.stationaryPairs.tau.ratio * (V.correction.n : F) ∧
    V.stationaryPairs.tauChiF.ratio =
      V.stationaryPairs.tau.ratio * ((V.correction.n : F) + 1) ∧
    WildQuadraticCoefficientData.MatchesCorrection F K V.correction D ∧
    (V.z0Unit : F) = V.correction.z0 ∧
    (V.z1Unit : F) = V.correction.z1 := by
  exact WildQuadraticCoefficientTable P.q P.toView

/-- High-range specialization of the principal table.  Its statement remains
indexed by the full high parameter package and therefore retains the selected
high representatives and their essential correction unit `delta`. -/
theorem WildQuadraticHighCoefficientTable
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (P : WildQuadraticHighCoefficientPackage F K) :
    let V := P.toView
    let D := V.coefficients.1
    WildQuadraticCoefficientCertificate P.q D ∧
    D.row = WildQuadraticCoefficientRow.ofConductors
      (P.chiF.conductor - 1) P.lowerBreak ∧
    1 < P.chiF.conductor ∧
    V.criticalInputs.MatchesStationaryPairs V.stationaryPairs ∧
    V.criticalInputs.MatchesLocalData V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCriticalCoordinates ∧
    WildQuadraticDerivedCriticalSources F K V.correction P.q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF ∧
    WildQuadraticActualPhaseAssembly F K P.q V.criticalInputs
      V.stationaryPairs V.tauData V.chiFData V.psiF ∧
    V.criticalInputs.MatchesBoundaryCorrectionCoordinate F K V.correction ∧
    V.stationaryPairs.chiK.ratio =
      algebraMap F K V.stationaryPairs.tau.ratio *
        (algebraMap F K (V.correction.n : F) - (V.correction.u : K)) ∧
    V.stationaryPairs.chiF.ratio =
      V.stationaryPairs.tau.ratio * (V.correction.n : F) ∧
    V.stationaryPairs.tauChiF.ratio =
      V.stationaryPairs.tau.ratio * ((V.correction.n : F) + 1) ∧
    WildQuadraticCoefficientData.MatchesCorrection F K V.correction D ∧
    (V.z0Unit : F) = V.correction.z0 ∧
    (V.z1Unit : F) = V.correction.z1 := by
  exact WildQuadraticCoefficientTable P.q P.toView

end

end LanglandsFirstMainLemma
