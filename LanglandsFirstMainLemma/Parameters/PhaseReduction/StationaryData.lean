import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Lamprecht.Formula

/-!
# Stationary quotient representatives and complete Lamprecht phase data

This module packages source-faithful stationary quotient representatives,
complete parity-sensitive Lamprecht phase data, and the dispatcher that inserts
a supplied representative without making any additional representative choice.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Quotient classes and supplied representatives -/

/-- A representative supplied for an actual stationary coefficient quotient.
The quotient class is part of the type; this structure does not choose a
canonical field element. -/
structure StationaryClassRepresentative
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) where
  representative : lattice E 0
  represents : latticeQuotientMk E (by omega) representative =
    stationaryCoefficientClass E chi psi h gamma hgamma

namespace StationaryClassRepresentative

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
  {d epsilon : ℕ}
  {h : IsStationaryConductorDecomposition chi.conductor d epsilon}
  {gamma : Eˣ}
  {hgamma : ord E (gamma : E) =
    (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)}

/-- The same supplied representative in Lamprecht's literal coefficient
lattice.  This changes only the displayed lattice index. -/
def toLamprecht
    (R : StationaryClassRepresentative E chi psi h gamma hgamma) :
    lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)) :=
  ⟨(R.representative : E), by simpa using R.representative.property⟩

/-- Inserting a supplied representative into the explicit equivalence from
the coefficient quotient to Lamprecht's quotient gives the actual stationary
numerator class. -/
theorem toLamprecht_represents
    (R : StationaryClassRepresentative E chi psi h gamma hgamma) :
    latticeQuotientMk E
        (sub_le_sub_left
          (stationaryDepthOfConductorDecomposition E chi h).int_le_conductor
          (chi.conductor : ℤ)) R.toLamprecht =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (stationaryDepthOfConductorDecomposition E chi h) gamma hgamma := by
  have hclass := congrArg
    (stationaryCoefficientLamprechtEquivAtConductor E h) R.represents
  rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
    stationaryCoefficientClass_toLamprecht] at hclass
  simpa only [toLamprecht] using hclass

/-- Two supplied representatives of the same class differ only at the exact
coefficient ambiguity depth `d`. -/
theorem congruentAtCoefficientDepth
    (R R' : StationaryClassRepresentative E chi psi h gamma hgamma) :
    CongruentAtDepth (d : ℤ)
      (R.representative : E) (R'.representative : E) := by
  exact (latticeQuotientMk_eq_mk_iff_congruentAtDepth E (by omega)).1
    (R.represents.trans R'.represents.symm)

/-- Wrap a representative equality already supplied by a parameter table.
This constructor performs no quotient-surjectivity choice. -/
def ofCoefficientRepresentative
    (c : lattice E 0)
    (hc : latticeQuotientMk E (by omega) c =
      stationaryCoefficientClass E chi psi h gamma hgamma) :
    StationaryClassRepresentative E chi psi h gamma hgamma where
  representative := c
  represents := hc

/-- The supplied stationary coefficient representative, bundled as a field
unit using its proved exact order.  This makes no representative choice: the
underlying field element is definitionally the one already stored in `R`. -/
def unit
    (R : StationaryClassRepresentative E chi psi h gamma hgamma) : Eˣ :=
  Units.mk0 (R.representative : E) (by
    apply (ord_ne_top_iff E).1
    have hord := stationaryNumeratorClass_representative_ord E chi psi
      (chi.conductor : ℤ) (stationaryDepthOfConductorDecomposition E chi h)
      gamma hgamma R.toLamprecht R.toLamprecht_represents
    rw [show ord E (R.representative : E) = 0 by
      simpa only [toLamprecht, sub_self, WithTop.coe_zero] using hord]
    exact WithTop.coe_ne_top)

@[simp]
theorem coe_unit
    (R : StationaryClassRepresentative E chi psi h gamma hgamma) :
    ((R.unit : Eˣ) : E) = (R.representative : E) :=
  rfl

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- The `beta` member of a low-table simultaneous pair, after taking its
explicitly supplied norm, is an actual representative of the requested
stationary quotient class. -/
def ofLowBeta
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {epsilonF : ℕ}
    {hF : IsStationaryConductorDecomposition chiF.conductor d epsilonF}
    {gammaF : Fˣ}
    {hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)}
    (P : LowStationaryNormRepresentativePair F K r d alphaClass
      (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)) :
    StationaryClassRepresentative F chiF psiF hF gammaF hgammaF :=
  ofCoefficientRepresentative
    ⟨(P.beta : F), P.betaRepresentative.norm_exactDepth.1⟩
    P.beta_norm_class

/-- The `alpha` member of a low-table simultaneous pair, after taking its
explicitly supplied norm, is an actual representative of the requested
stationary quotient class. -/
def ofLowAlpha
    {r d : ℕ}
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {epsilonF : ℕ}
    {hF : IsStationaryConductorDecomposition chiF.conductor r epsilonF}
    {gammaF : Fˣ}
    {hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)}
    {betaClass : StationaryCoefficientQuotient F d}
    (P : LowStationaryNormRepresentativePair F K r d
      (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
      betaClass) :
    StationaryClassRepresentative F chiF psiF hF gammaF hgammaF :=
  ofCoefficientRepresentative
    ⟨(P.alpha : F), P.alphaRepresentative.norm_exactDepth.1⟩
    P.alpha_norm_class

end StationaryClassRepresentative

/-! ## Complete local Lamprecht factors -/

/-- A supplied representative of one stationary quotient, together with the
parity-specific data needed by Lamprecht's formula.  There is deliberately no
endpoint constructor: conductors zero and one have no stationary class. -/
inductive LocalLamprechtPhaseData
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E) where
  | even
      (d : ℕ)
      (hm : chi.conductor = 2 * d)
      (hlarge : 1 < chi.conductor)
      (Gamma : AdmissibleGamma E chi psi)
      (c : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
      (hc : latticeQuotientMk E
          (sub_le_sub_left
            (lamprechtFormula_stationaryDepth E chi d 0
              (by omega) (by simpa using hm) hlarge).int_le_conductor
            (chi.conductor : ℤ)) c =
        stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge) Gamma Gamma.property)
  | odd
      (d : ℕ)
      (hm : chi.conductor = 2 * d + 1)
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

namespace LocalLamprechtPhaseData

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- Insert a representative of the literal stationary coefficient class into
the even Lamprecht formula. -/
def evenOfStationaryClass
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    LocalLamprechtPhaseData E chi psi :=
  .even d (by simpa using h.conductor_eq) h.conductor_gt_one Gamma
    R.toLamprecht (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R.toLamprecht_represents)

/-- Insert a representative of the literal stationary coefficient class into
the odd Lamprecht formula, retaining the chosen critical uniformizer. -/
def oddOfStationaryClass
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    LocalLamprechtPhaseData E chi psi :=
  .odd d h.conductor_eq h.conductor_gt_one Gamma delta hdelta
    R.toLamprecht (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R.toLamprecht_represents)

/-- Insert a supplied stationary quotient representative without hiding the
parity split.  In the odd branch the critical coordinate is also supplied;
the definition does not select a uniformizer or a field representative. -/
noncomputable def ofStationaryClass
    (d epsilon : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (criticalCoordinate : epsilon = 1 →
      { delta : Eˣ // ord E (delta : E) = ((d : ℤ) : WithTop ℤ) }) :
    LocalLamprechtPhaseData E chi psi := by
  have hepsilon_le := h.epsilon_le_one
  by_cases hepsilon : epsilon = 0
  · subst epsilon
    exact evenOfStationaryClass d h Gamma R
  · have hepsilon_one : epsilon = 1 := by omega
    subst epsilon
    let delta := criticalCoordinate rfl
    exact oddOfStationaryClass d h Gamma delta.1 delta.2 R

/-- Every stationary local phase package has actual conductor greater than
one. -/
theorem conductor_gt_one (D : LocalLamprechtPhaseData E chi psi) :
    1 < chi.conductor := by
  cases D with
  | even _ _ hlarge _ _ _ => exact hlarge
  | odd _ _ hlarge _ _ _ _ _ => exact hlarge

/-- Conductors zero and one have no stationary local phase package. -/
theorem noData_of_conductor_le_one (h : chi.conductor ≤ 1) :
    ¬ Nonempty (LocalLamprechtPhaseData E chi psi) := by
  rintro ⟨D⟩
  exact (not_lt_of_ge h) D.conductor_gt_one

/-- The exact admissible denominator chosen in the local package. -/
def gamma (D : LocalLamprechtPhaseData E chi psi) :
    AdmissibleGamma E chi psi :=
  match D with
  | .even _ _ _ Gamma _ _ => Gamma
  | .odd _ _ _ Gamma _ _ _ _ => Gamma

/-- The character value on the admissible denominator. -/
def admissibleFactor (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  (chi.character (D.gamma : Eˣ) : ℂ)

/-- The elementary stationary value, with positive additive phase and inverse
multiplicative character, for the supplied representative. -/
def elementaryFactor (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  match D with
  | .even d hm hlarge Gamma c hc =>
      lamprechtElementaryFactor E chi psi Gamma
        (lamprechtStationaryRepresentativeUnit E chi psi
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge) Gamma c hc)
  | .odd d hm hlarge Gamma _delta _hdelta c hc =>
      lamprechtElementaryFactor E chi psi Gamma
        (lamprechtStationaryRepresentativeUnit E chi psi
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge) Gamma c hc)

/-- The residual critical factor: one in even conductor and the actual Hasse
sum phase in odd conductor. -/
noncomputable def criticalFactor
    (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  match D with
  | .even _ _ _ _ _ _ => 1
  | .odd d hm hlarge Gamma delta hdelta c hc => by
      letI := residueFieldFintype E
      exact
        (lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c hc).sumPhase

/-- The complete stationary part, keeping the elementary and critical
factors together. -/
noncomputable def stationaryFactor
    (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  D.elementaryFactor * D.criticalFactor

/-- The complete local Lamprecht factor. -/
noncomputable def completeFactor
    (D : LocalLamprechtPhaseData E chi psi) : ℂ :=
  D.admissibleFactor * D.stationaryFactor

theorem admissibleFactor_ne_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.admissibleFactor ≠ 0 :=
  ContinuousQuasiChar.apply_ne_zero _ _

theorem elementaryFactor_ne_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.elementaryFactor ≠ 0 := by
  cases D <;> exact lamprechtElementaryFactor_ne_zero _ _ _ _ _

theorem criticalFactor_ne_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.criticalFactor ≠ 0 := by
  cases D with
  | even => simp [criticalFactor]
  | odd d hm hlarge Gamma delta hdelta c hc =>
      letI := residueFieldFintype E
      simpa only [criticalFactor, HasseFunction.sumPhase] using
        phase_ne_zero
          (lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c hc).sum

theorem stationaryFactor_ne_zero
    (D : LocalLamprechtPhaseData E chi psi) :
    D.stationaryFactor ≠ 0 :=
  mul_ne_zero D.elementaryFactor_ne_zero D.criticalFactor_ne_zero

/-- Lamprecht's formula, split into its admissible-character, elementary, and
critical/Hasse factors. -/
theorem deltaFinite_eq_completeFactor
    (D : LocalLamprechtPhaseData E chi psi) :
    deltaFinite chi psi D.gamma = D.completeFactor := by
  cases D with
  | even d hm hlarge Gamma c hc =>
      simpa [gamma, completeFactor, stationaryFactor, admissibleFactor,
        elementaryFactor, criticalFactor, mul_assoc] using
        lamprechtEven E chi psi d hm hlarge Gamma c hc
  | odd d hm hlarge Gamma delta hdelta c hc =>
      letI := residueFieldFintype E
      simpa [gamma, completeFactor, stationaryFactor, admissibleFactor,
        elementaryFactor, criticalFactor, mul_assoc] using
        lamprechtOdd E chi psi d hm hlarge Gamma delta hdelta c hc

/-- In even conductor the elementary factor itself is independent of the
supplied representative at exactly depth `d`. -/
theorem evenStationaryFactor_representative_independent
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    (evenOfStationaryClass d h Gamma R).stationaryFactor =
      (evenOfStationaryClass d h Gamma R').stationaryFactor := by
  have hind := lamprechtEven_elementary_representative_independent E chi psi d
    (by simpa using h.conductor_eq) h.conductor_gt_one Gamma
    R.toLamprecht R'.toLamprecht
    (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R.toLamprecht_represents)
    (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R'.toLamprecht_represents)
  simpa [evenOfStationaryClass, stationaryFactor, elementaryFactor,
    criticalFactor] using hind

/-- In odd conductor the elementary value and Hasse phase are transported
together; only their product is asserted independent. -/
theorem oddStationaryFactor_representative_independent
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    (oddOfStationaryClass d h Gamma delta hdelta R).stationaryFactor =
      (oddOfStationaryClass d h Gamma delta hdelta R').stationaryFactor := by
  letI := residueFieldFintype E
  have hind := lamprechtOdd_complete_representative_independent E chi psi d
    h.conductor_eq h.conductor_gt_one Gamma delta hdelta
    R.toLamprecht R'.toLamprecht
    (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R.toLamprecht_represents)
    (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        R'.toLamprecht_represents)
  simpa [oddOfStationaryClass, stationaryFactor, elementaryFactor,
    criticalFactor] using hind

/-- At even conductor the whole local Lamprecht factor is independent of
the supplied representative at the coefficient depth. -/
theorem evenCompleteFactor_representative_independent
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    (evenOfStationaryClass d h Gamma R).completeFactor =
      (evenOfStationaryClass d h Gamma R').completeFactor := by
  unfold completeFactor
  rw [evenStationaryFactor_representative_independent d h Gamma R R']
  simp [admissibleFactor, gamma, evenOfStationaryClass]

/-- At odd conductor the whole local factor is independent only because the
elementary value and translated Hasse phase were transported together. -/
theorem oddCompleteFactor_representative_independent
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    (oddOfStationaryClass d h Gamma delta hdelta R).completeFactor =
      (oddOfStationaryClass d h Gamma delta hdelta R').completeFactor := by
  unfold completeFactor
  rw [oddStationaryFactor_representative_independent
    d h Gamma delta hdelta R R']
  simp [admissibleFactor, gamma, oddOfStationaryClass]

/-- The explicit odd representative change: the new Hasse function is a
translation and the new elementary factor is multiplied by the old Hasse
value at the same translation parameter. -/
theorem oddRepresentative_transport
    (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (c c' : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (hc' : latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c' =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    ∃ a : ResidueField E,
      lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c' hc' =
        (lamprechtHasseFunction E chi psi d hm hlarge
          Gamma delta hdelta c hc).translate a ∧
      lamprechtElementaryFactor E chi psi Gamma
          (lamprechtStationaryRepresentativeUnit E chi psi
            (lamprechtFormula_stationaryDepth E chi d 1
              (by omega) hm hlarge) Gamma c' hc') =
        lamprechtHasseFunction E chi psi d hm hlarge
            Gamma delta hdelta c hc a *
          lamprechtElementaryFactor E chi psi Gamma
            (lamprechtStationaryRepresentativeUnit E chi psi
              (lamprechtFormula_stationaryDepth E chi d 1
                (by omega) hm hlarge) Gamma c hc) :=
  lamprechtOdd_representative_transport E chi psi d hm hlarge
    Gamma delta hdelta c c' hc hc'

end LocalLamprechtPhaseData

/-! ## Parity-exact insertion of stationary representatives -/

/-- The critical coordinate required by Lamprecht at the actual parity.
The even constructor contains no field choice; the odd constructor contains
exactly the coordinate and valuation required by the odd formula. -/
inductive LamprechtCriticalCoordinate
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (d : ℕ) : ℕ → Type _ where
  | even : LamprechtCriticalCoordinate E d 0
  | odd (delta : Eˣ)
      (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)) :
      LamprechtCriticalCoordinate E d 1

/-- Insert a supplied quotient-class representative into the parity branch
of Lamprecht's formula.  This dispatch makes no representative choice. -/
def localPhaseOfStationaryClass
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon) :
    LocalLamprechtPhaseData E chi psi :=
  match C with
  | .even => LocalLamprechtPhaseData.evenOfStationaryClass d h Gamma R
  | .odd delta hdelta =>
      LocalLamprechtPhaseData.oddOfStationaryClass d h Gamma delta hdelta R


/-! ## Transport and endpoint cancellation for actual odd rows -/

/-- Proof-bearing additive-character data are determined by their
underlying character, just as multiplicative-character data are. -/
theorem LocalAddCharData.ext_character
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {psi omega : LocalAddCharData E}
    (h : psi.character = omega.character) : psi = omega := by
  cases psi with
  | mk psi m hpsi =>
      cases omega with
      | mk omega n homega =>
          dsimp at h
          subst omega
          have hmn : m = n := hpsi.unique homega
          subst n
          rfl

/-- Transport a stationary Lamprecht package only across equality of its
proof-bearing character data.  No representative or denominator changes. -/
def transportLocalLamprechtPhaseData
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (S : LocalLamprechtPhaseData E chi psi) :
    LocalLamprechtPhaseData E chi' psi' := by
  have hchiData : chi = chi' := LocalQuasiCharData.ext_character E hchi
  have hpsiData : psi = psi' := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  exact S

/-- A stationary class inserted into Lamprecht evaluates its admissible
factor at the literal denominator carried by the class. -/
theorem localPhaseOfStationaryClass_admissibleFactor
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon) :
    (localPhaseOfStationaryClass h Gamma R C).admissibleFactor =
      (chi.character (Gamma : Eˣ) : ℂ) := by
  cases C <;> rfl

/-- Transporting only proof-bearing character data does not alter the
admissible factor or its literal denominator. -/
theorem transportLocalLamprechtPhaseData_admissibleFactor
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (S : LocalLamprechtPhaseData E chi psi) :
    (transportLocalLamprechtPhaseData hchi hpsi S).admissibleFactor =
      S.admissibleFactor := by
  have hc : chi = chi' := LocalQuasiCharData.ext_character E hchi
  have hp : psi = psi' := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  rfl

end

end LanglandsFirstMainLemma
