import LanglandsFirstMainLemma.Cases.WildQuadratic.CoefficientTable
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsFirstMainLemma.Lamprecht.StationaryClassCalculus

namespace LanglandsFirstMainLemma

noncomputable section

/-!
# Exact wild-quadratic stationary assembly

This file joins the real table-backed phase-reduction output to the completed
wild-quadratic coefficient table. Every stationary representative and every
critical coordinate used below is supplied explicitly. In particular, no
stationary quotient class is turned into a distinguished field element.
-/

/-! ## Selected local rows and complete-factor transport -/

namespace LocalLamprechtPhaseData

variable {E : Type*}
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- Exact evidence that an actual local Lamprecht package is its even
constructor.  This is deliberately stronger than the numerical statement
that its critical factor happens to be one. -/
def IsEven (S : LocalLamprechtPhaseData E chi psi) : Prop :=
  match S with
  | .even _ _ _ _ _ _ => True
  | .odd _ _ _ _ _ _ _ _ => False

/-- The critical factor of an actual even Lamprecht row is the literal
constant one. -/
theorem criticalFactor_eq_one_of_isEven
    (S : LocalLamprechtPhaseData E chi psi) (hS : S.IsEven) :
    S.criticalFactor = 1 := by
  cases S <;> simp_all [IsEven, criticalFactor]

/-- The literal admissible denominator and supplied stationary numerator of
one real local phase row. -/
def selectedStationaryPair
    (S : LocalLamprechtPhaseData E chi psi) :
    WildQuadraticStationaryPair E :=
  match S with
  | .even _ _ _ Gamma c _ =>
      { gamma := Gamma
        beta := (c : E) }
  | .odd _ _ _ Gamma _ _ c _ =>
      { gamma := Gamma
        beta := (c : E) }

@[simp]
theorem selectedStationaryPair_gamma
    (S : LocalLamprechtPhaseData E chi psi) :
    S.selectedStationaryPair.gamma = (S.gamma : Eˣ) := by
  cases S <;> rfl

/-- A permitted representative change keeps the local characters and exact
admissible denominator fixed, and transports the complete elementary--Hasse
stationary factor as one object. -/
structure CompleteFactorTransport
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E) where
  before : LocalLamprechtPhaseData E chi psi
  after : LocalLamprechtPhaseData E chi psi
  gamma_eq : before.gamma = after.gamma
  stationaryFactor_eq : before.stationaryFactor = after.stationaryFactor

namespace CompleteFactorTransport

variable {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- The complete local Lamprecht factor is invariant when its elementary and
critical factors are transported together. -/
theorem completeFactor_eq
    (T : CompleteFactorTransport (E := E) chi psi) :
    T.before.completeFactor = T.after.completeFactor := by
  unfold LocalLamprechtPhaseData.completeFactor
    LocalLamprechtPhaseData.admissibleFactor
  rw [T.stationaryFactor_eq, T.gamma_eq]

/-- Build a permitted even-conductor change from two supplied representatives
of the same stationary quotient class. -/
def ofEven
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    CompleteFactorTransport (E := E) chi psi where
  before := LocalLamprechtPhaseData.evenOfStationaryClass d h Gamma R
  after := LocalLamprechtPhaseData.evenOfStationaryClass d h Gamma R'
  gamma_eq := rfl
  stationaryFactor_eq :=
    LocalLamprechtPhaseData.evenStationaryFactor_representative_independent
      d h Gamma R R'

/-- Build a permitted odd-conductor change. The real PhaseReduction theorem
used here transports the elementary stationary value and the translated
Hasse phase together. -/
def ofOdd
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    CompleteFactorTransport (E := E) chi psi where
  before := LocalLamprechtPhaseData.oddOfStationaryClass
    d h Gamma delta hdelta R
  after := LocalLamprechtPhaseData.oddOfStationaryClass
    d h Gamma delta hdelta R'
  gamma_eq := rfl
  stationaryFactor_eq :=
    LocalLamprechtPhaseData.oddStationaryFactor_representative_independent
      d h Gamma delta hdelta R R'

/-- The translation retained by an odd representative change, with the
direction `old Hasse -> translate a` and the compensating elementary value
displayed exactly as in the real public API. -/
theorem ofOdd_translation
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property) :
    ∃ a : ResidueField E,
      lamprechtHasseFunction E chi psi d h.conductor_eq
          h.conductor_gt_one Gamma delta hdelta R'.toLamprecht
          (by
            simpa only [stationaryDepthOfConductorDecomposition] using
              R'.toLamprecht_represents) =
        (lamprechtHasseFunction E chi psi d h.conductor_eq
          h.conductor_gt_one Gamma delta hdelta R.toLamprecht
          (by
            simpa only [stationaryDepthOfConductorDecomposition] using
              R.toLamprecht_represents)).translate a ∧
      lamprechtElementaryFactor E chi psi Gamma
          (lamprechtStationaryRepresentativeUnit E chi psi
            (lamprechtFormula_stationaryDepth E chi d 1 (by omega)
              h.conductor_eq h.conductor_gt_one) Gamma R'.toLamprecht
              (by
                simpa only [stationaryDepthOfConductorDecomposition] using
                  R'.toLamprecht_represents)) =
        lamprechtHasseFunction E chi psi d h.conductor_eq
            h.conductor_gt_one Gamma delta hdelta R.toLamprecht
            (by
              simpa only [stationaryDepthOfConductorDecomposition] using
                R.toLamprecht_represents) a *
          lamprechtElementaryFactor E chi psi Gamma
            (lamprechtStationaryRepresentativeUnit E chi psi
              (lamprechtFormula_stationaryDepth E chi d 1 (by omega)
                h.conductor_eq h.conductor_gt_one) Gamma R.toLamprecht
                (by
                  simpa only [stationaryDepthOfConductorDecomposition] using
                    R.toLamprecht_represents)) := by
  exact LocalLamprechtPhaseData.oddRepresentative_transport d
    h.conductor_eq h.conductor_gt_one Gamma delta hdelta
      R.toLamprecht R'.toLamprecht
      (by
        simpa only [stationaryDepthOfConductorDecomposition] using
          R.toLamprecht_represents)
      (by
        simpa only [stationaryDepthOfConductorDecomposition] using
          R'.toLamprecht_represents)

end CompleteFactorTransport

end LocalLamprechtPhaseData

/-- The quotient of the four complete local Lamprecht factors in the
manuscript's literal orientation `chiK * tau / (chiF * tauChiF)`.  Each local
factor already contains its admissible, elementary, and critical pieces. -/
noncomputable def wildQuadraticCompleteErrorExpression
    {K F : Type*}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    {tauData chiFData twistData : LocalQuasiCharData F}
    {psiF : LocalAddCharData F}
    (extension : LocalLamprechtPhaseData K chiK psiK)
    (tau : LocalLamprechtPhaseData F tauData psiF)
    (base : LocalLamprechtPhaseData F chiFData psiF)
    (twist : LocalLamprechtPhaseData F twistData psiF) : ℂ :=
  extension.completeFactor * tau.completeFactor /
    (base.completeFactor * twist.completeFactor)

/-- Changing any of the four permitted representatives transports all four
complete factors together and leaves the whole error expression unchanged. -/
theorem wildQuadraticCompleteErrorExpression_representative_independent
    {K F : Type*}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    {tauData chiFData twistData : LocalQuasiCharData F}
    {psiF : LocalAddCharData F}
    (extension : LocalLamprechtPhaseData.CompleteFactorTransport chiK psiK)
    (tau : LocalLamprechtPhaseData.CompleteFactorTransport tauData psiF)
    (base : LocalLamprechtPhaseData.CompleteFactorTransport chiFData psiF)
    (twist : LocalLamprechtPhaseData.CompleteFactorTransport twistData psiF) :
    wildQuadraticCompleteErrorExpression extension.before tau.before
        base.before twist.before =
      wildQuadraticCompleteErrorExpression extension.after tau.after
        base.after twist.after := by
  unfold wildQuadraticCompleteErrorExpression
  rw [extension.completeFactor_eq, tau.completeFactor_eq,
    base.completeFactor_eq, twist.completeFactor_eq]

/-! ## Exact inverse-character corrections -/

/-- One real odd critical correction. It retains the actual conductor and
stationary depth, exact admissible gamma, selected numerator, inverse
orientation, normalized residue class, and positive refinement value. -/
structure WildQuadraticRefinementCorrection
    (E : Type*)
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (k : Type*) [Field k] [Fintype k] [CharP k 2]
    (psiE : LocalAddCharData E) (theta : LocalQuasiCharData E)
    (q : CharTwoRefinement k) where
  depth : ℕ
  conductorDecomposition :
    IsStationaryConductorDecomposition theta.conductor depth 1
  Gamma : AdmissibleGamma E theta psiE
  beta : E
  correction : E
  one_add_correction_ne_zero : 1 + correction ≠ 0
  normalizedClass : k
  affineCoefficient : k
  inverseCharacter_eq :
    (theta.character
      (Units.mk0 (1 + correction) one_add_correction_ne_zero) : ℂ)⁻¹ =
      (psiE.character
        (-(beta * correction / ((Gamma : Eˣ) : E))) : ℂ) *
        q.correctionValue affineCoefficient normalizedClass

namespace WildQuadraticRefinementCorrection

variable {E k : Type*}
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field k] [Fintype k] [CharP k 2]
  {psiE : LocalAddCharData E} {theta : LocalQuasiCharData E}
  {q : CharTwoRefinement k}

noncomputable def value
    (C : WildQuadraticRefinementCorrection E k psiE theta q) : ℂ :=
  q.correctionValue C.affineCoefficient C.normalizedClass

theorem value_eq
    (C : WildQuadraticRefinementCorrection E k psiE theta q) :
    C.value = q C.normalizedClass *
      absoluteTraceChar k (C.affineCoefficient * C.normalizedClass) :=
  rfl

theorem value_ne_zero
    (C : WildQuadraticRefinementCorrection E k psiE theta q) :
    C.value ≠ 0 := by
  rw [C.value_eq]
  exact mul_ne_zero (q.ne_zero C.normalizedClass)
    (AddChar.val_isUnit (absoluteTraceChar k)
      (C.affineCoefficient * C.normalizedClass)).ne_zero

end WildQuadraticRefinementCorrection

/-- Absence of a critical correction contributes the literal factor one. -/
noncomputable def wildQuadraticOptionalCorrectionValue
    {E k : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field k] [Fintype k] [CharP k 2]
    {psiE : LocalAddCharData E} {theta : LocalQuasiCharData E}
    {q : CharTwoRefinement k}
    (C : Option (WildQuadraticRefinementCorrection E k psiE theta q)) : ℂ :=
  C.elim 1 WildQuadraticRefinementCorrection.value

@[simp]
theorem wildQuadraticOptionalCorrectionValue_none
    {E k : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field k] [Fintype k] [CharP k 2]
    {psiE : LocalAddCharData E} {theta : LocalQuasiCharData E}
    {q : CharTwoRefinement k} :
    wildQuadraticOptionalCorrectionValue
      (none : Option (WildQuadraticRefinementCorrection E k psiE theta q)) =
        1 :=
  rfl

@[simp]
theorem wildQuadraticOptionalCorrectionValue_some
    {E k : Type*}
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Field k] [Fintype k] [CharP k 2]
    {psiE : LocalAddCharData E} {theta : LocalQuasiCharData E}
    {q : CharTwoRefinement k}
    (C : WildQuadraticRefinementCorrection E k psiE theta q) :
    wildQuadraticOptionalCorrectionValue (some C) = C.value :=
  rfl

/-! ## Coefficient-table correction values -/

namespace WildQuadraticCoefficientData

variable {k : Type*} [Field k] [Fintype k] [CharP k 2]

/-- The normalized base-character correction class. It occurs only in the
strict-high odd-conductor rows and at the odd boundary. -/
def chiCorrectionClass (D : WildQuadraticCoefficientData k) : Option k :=
  match D with
  | .aboveMOddTEven _ => some 1
  | .aboveMOddTOdd _ _ _ _ => some 1
  | .boundaryOdd rho _ _ _ _ _ _ _ _ =>
      some (rho ^ 2 / (1 + rho ^ 2))
  | _ => none

/-- The normalized norm-character correction class occurs only at the odd
boundary. -/
def tauCorrectionClass (D : WildQuadraticCoefficientData k) : Option k :=
  match D with
  | .boundaryOdd rho _ _ _ _ _ _ _ _ =>
      some (rho / (1 + rho ^ 2))
  | _ => none

/-- The positive correction value selected by an affine coefficient and a
normalized correction class. -/
noncomputable def selectedCorrectionValue
    (q : CharTwoRefinement k) (coefficient correctionClass : Option k) : ℂ :=
  match coefficient, correctionClass with
  | some lambda, some c => WildQuadraticRefinement.correctionValue q lambda c
  | _, _ => 1

noncomputable def chiCorrectionValue
    (D : WildQuadraticCoefficientData k) (q : CharTwoRefinement k) : ℂ :=
  selectedCorrectionValue q (D.affineCoefficient .chiF) D.chiCorrectionClass

noncomputable def tauCorrectionValue
    (D : WildQuadraticCoefficientData k) (q : CharTwoRefinement k) : ℂ :=
  selectedCorrectionValue q (D.affineCoefficient .tau) D.tauCorrectionClass

/-- Every non-boundary row's raw phase quotient and its actually supplied
critical corrections cancel exactly. -/
theorem phaseRatio_mul_corrections_eq_one_of_not_boundaryOdd
    (q : CharTwoRefinement k) (D : WildQuadraticCoefficientData k)
    (hD : D.row ≠ .boundaryOdd) :
    D.phaseRatio q * D.chiCorrectionValue q *
        D.tauCorrectionValue q = 1 := by
  cases D with
  | belowMEvenTEven =>
      simp [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient]
  | belowMEvenTOdd gamma0 =>
      simp only [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient, mul_one]
      field_simp [WildQuadraticRefinement.phase,
        q.affinePhase_ne_zero gamma0]
  | belowMOddTEven gamma gammaPrime hs =>
      simp only [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient, mul_one]
      rw [WildQuadraticRefinement.phase_eq_of_sq q hs]
      field_simp [WildQuadraticRefinement.phase,
        q.affinePhase_ne_zero gamma]
  | belowMOddTOdd gamma0 gamma gammaPrime hs =>
      simp only [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient, mul_one]
      rw [WildQuadraticRefinement.phase_eq_of_sq q hs]
      field_simp [WildQuadraticRefinement.phase,
        q.affinePhase_ne_zero gamma, q.affinePhase_ne_zero gamma0]
  | boundaryEven =>
      simp [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient]
  | boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs =>
      exact (hD rfl).elim
  | aboveMEvenTEven =>
      simp [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient]
  | aboveMEvenTOdd gamma0 gammaPrime hs =>
      simp only [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient, mul_one]
      rw [WildQuadraticRefinement.phase_eq_of_sq q hs,
        WildQuadraticRefinement.phase_pair q gamma0]
      simp
  | aboveMOddTEven gamma =>
      simp only [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient, mul_one,
        WildQuadraticRefinement.correctionValue_apply]
      rw [← pow_two,
        show WildQuadraticRefinement.phase q gamma ^ 2 =
          q 1 * absoluteTraceChar k gamma from
          WildQuadraticRefinement.phase_sq q gamma]
      field_simp [q.ne_zero 1,
        (AddChar.val_isUnit (absoluteTraceChar k) gamma).ne_zero]
  | aboveMOddTOdd gamma0 gamma gammaPrime hs =>
      simp only [phaseRatio, phaseFactor, chiCorrectionValue,
        tauCorrectionValue, selectedCorrectionValue, chiCorrectionClass,
        tauCorrectionClass, affineCoefficient, mul_one,
        WildQuadraticRefinement.correctionValue_apply]
      rw [WildQuadraticRefinement.phase_eq_of_sq q hs,
        WildQuadraticRefinement.phase_pair q gamma0,
        ← pow_two,
        show WildQuadraticRefinement.phase q gamma ^ 2 =
          q 1 * absoluteTraceChar k gamma from
          WildQuadraticRefinement.phase_sq q gamma]
      field_simp [q.ne_zero 1,
        (AddChar.val_isUnit (absoluteTraceChar k) gamma).ne_zero]

private def boundaryA (rho : k) : k := rho / (1 + rho)
private def boundaryB (rho : k) : k := rho ^ 2 / (1 + rho ^ 2)
private def boundaryC (rho : k) : k := rho / (1 + rho ^ 2)
private def boundaryL (rho r gamma0 gamma : k) : k :=
  (gamma + rho * gamma0 + rho + r) / (1 + rho)
private def boundaryGammaOne (rho r gamma0 gamma : k) : k :=
  (gamma0 + rho * gamma + r) / (1 + rho)

omit [Fintype k] in
private theorem boundary_phase_sum
    (rho r gamma0 gamma : k) (hden : 1 + rho ≠ 0) :
    gamma + boundaryGammaOne rho r gamma0 gamma =
      boundaryL rho r gamma0 gamma + gamma0 + boundaryA rho := by
  dsimp [boundaryGammaOne, boundaryL, boundaryA]
  field_simp [hden]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  ring_nf
  simp [htwo]

omit [Fintype k] in
private theorem boundary_AS_difference
    (rho r gamma0 gamma : k) (hr : r ^ 2 = rho)
    (hden : 1 + rho ≠ 0) :
    let A := boundaryA rho
    let L := boundaryL rho r gamma0 gamma
    let gamma1 := boundaryGammaOne rho r gamma0 gamma
    let E := (L + gamma0) * A + gamma * gamma1 + L * gamma0
    let z := r / (1 + r) * (gamma + gamma0) + A
    E + gamma1 * A + A = z ^ 2 + z := by
  dsimp only
  subst rho
  have hrden : 1 + r ≠ 0 := by
    intro hz
    apply hden
    calc
      1 + r ^ 2 = (1 + r) ^ 2 := by
        rw [CharTwo.add_sq, one_pow]
      _ = 0 := by rw [hz]; simp
  dsimp [boundaryA, boundaryL, boundaryGammaOne]
  field_simp [hden, hrden]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hthree : (3 : k) = 1 := by linear_combination htwo
  have hfour : (4 : k) = 0 := by linear_combination 2 * htwo
  have hfive : (5 : k) = 1 := by linear_combination 2 * htwo
  have hsix : (6 : k) = 0 := by linear_combination 3 * htwo
  have hseven : (7 : k) = 1 := by linear_combination 3 * htwo
  have height : (8 : k) = 0 := by linear_combination 4 * htwo
  ring_nf
  simp only [htwo, hthree, hfour, hfive, hsix, hseven, height,
    mul_zero, mul_one, add_zero]

private theorem boundary_phaseRatio_eq
    (q : CharTwoRefinement k)
    (rho r gamma0 gamma gammaPrime : k)
    (hrho : rho ≠ 0) (hr : r ^ 2 = rho) (hden : 1 + rho ≠ 0)
    (hs : gammaPrime ^ 2 = boundaryL rho r gamma0 gamma) :
    let D : WildQuadraticCoefficientData k :=
      .boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs
    D.phaseRatio q = q (boundaryA rho) *
      absoluteTraceChar k
        (boundaryGammaOne rho r gamma0 gamma * boundaryA rho +
          boundaryA rho) := by
  dsimp only
  simp only [phaseRatio, phaseFactor, affineCoefficient]
  rw [WildQuadraticRefinement.phase_eq_of_sq q hs]
  have hfour := WildQuadraticRefinement.phase_four q
    (boundaryL rho r gamma0 gamma) gamma0 gamma
    (boundaryGammaOne rho r gamma0 gamma) (boundaryA rho)
    (boundary_phase_sum rho r gamma0 gamma hden)
  rw [show (gamma0 + rho * gamma + r) / (1 + rho) =
      boundaryGammaOne rho r gamma0 gamma by rfl]
  rw [hfour]
  congr 1
  let E :=
    (boundaryL rho r gamma0 gamma + gamma0) * boundaryA rho +
      gamma * boundaryGammaOne rho r gamma0 gamma +
      boundaryL rho r gamma0 gamma * gamma0
  let T := boundaryGammaOne rho r gamma0 gamma * boundaryA rho +
    boundaryA rho
  let z := r / (1 + r) * (gamma + gamma0) + boundaryA rho
  have hAS : E + T = z ^ 2 + z := by
    simpa only [E, T, z, add_assoc] using
      boundary_AS_difference rho r gamma0 gamma hr hden
  apply mul_right_cancel₀
    ((AddChar.val_isUnit (absoluteTraceChar k) T).ne_zero)
  calc
    absoluteTraceChar k E * absoluteTraceChar k T =
        absoluteTraceChar k (E + T) :=
      (AddChar.map_add_eq_mul _ _ _).symm
    _ = absoluteTraceChar k (z ^ 2 + z) := by rw [hAS]
    _ = 1 := by
      rw [add_comm, WildQuadraticRefinement.artinSchreier_sign]
    _ = absoluteTraceChar k T * absoluteTraceChar k T := by
      rw [← pow_two, CharTwoRefinement.absoluteTraceChar_value_sq]

/-- At the odd boundary the raw four-phase quotient, the two complete
positive correction values, and the elementary `C` phase assemble with the
manuscript's exact numerator/denominator orientation. -/
theorem phaseRatio_mul_corrections_boundaryOdd
    (q : CharTwoRefinement k)
    (rho r gamma0 gamma gammaPrime : k)
    (hrho : rho ≠ 0) (hr : r ^ 2 = rho) (hden : 1 + rho ≠ 0)
    (hs : gammaPrime ^ 2 =
      (gamma + rho * gamma0 + rho + r) / (1 + rho)) :
    let D : WildQuadraticCoefficientData k :=
      .boundaryOdd rho r gamma0 gamma gammaPrime hrho hr hden hs
    let A := rho / (1 + rho)
    let B := rho ^ 2 / (1 + rho ^ 2)
    let C := rho / (1 + rho ^ 2)
    let gamma1 := (gamma0 + rho * gamma + r) / (1 + rho)
    D.phaseRatio q * D.chiCorrectionValue q *
        D.tauCorrectionValue q * absoluteTraceChar k C =
      q A * q B * q C *
        absoluteTraceChar k
          (gamma1 * A + gamma * B + gamma0 * C + C + A) := by
  dsimp only
  rw [boundary_phaseRatio_eq q rho r gamma0 gamma gammaPrime hrho hr hden hs]
  simp only [chiCorrectionValue, tauCorrectionValue, selectedCorrectionValue,
    chiCorrectionClass, tauCorrectionClass, affineCoefficient,
    WildQuadraticRefinement.correctionValue_apply]
  let A := rho / (1 + rho)
  let B := rho ^ 2 / (1 + rho ^ 2)
  let C := rho / (1 + rho ^ 2)
  let gamma1 := (gamma0 + rho * gamma + r) / (1 + rho)
  change (q A * absoluteTraceChar k (gamma1 * A + A)) *
      (q B * absoluteTraceChar k (gamma * B)) *
      (q C * absoluteTraceChar k (gamma0 * C)) *
      absoluteTraceChar k C =
    q A * q B * q C *
      absoluteTraceChar k
        (gamma1 * A + gamma * B + gamma0 * C + C + A)
  have hchars :
      absoluteTraceChar k (gamma1 * A + A) *
          absoluteTraceChar k (gamma * B) *
          absoluteTraceChar k (gamma0 * C) *
          absoluteTraceChar k C =
        absoluteTraceChar k
          ((gamma1 * A + A) + gamma * B + gamma0 * C + C) := by
    calc
      absoluteTraceChar k (gamma1 * A + A) *
            absoluteTraceChar k (gamma * B) *
            absoluteTraceChar k (gamma0 * C) *
            absoluteTraceChar k C =
          absoluteTraceChar k ((gamma1 * A + A) + gamma * B) *
            absoluteTraceChar k (gamma0 * C) *
            absoluteTraceChar k C := by
              rw [(AddChar.map_add_eq_mul _ _ _).symm]
      _ = absoluteTraceChar k
            (((gamma1 * A + A) + gamma * B) + gamma0 * C) *
            absoluteTraceChar k C := by
              rw [(AddChar.map_add_eq_mul _ _ _).symm]
      _ = absoluteTraceChar k
            ((gamma1 * A + A) + gamma * B + gamma0 * C + C) := by
              rw [(AddChar.map_add_eq_mul _ _ _).symm]
  calc
    (q A * absoluteTraceChar k (gamma1 * A + A)) *
          (q B * absoluteTraceChar k (gamma * B)) *
          (q C * absoluteTraceChar k (gamma0 * C)) *
          absoluteTraceChar k C =
        q A * q B * q C *
          (absoluteTraceChar k (gamma1 * A + A) *
            absoluteTraceChar k (gamma * B) *
            absoluteTraceChar k (gamma0 * C) *
            absoluteTraceChar k C) := by ring
    _ = q A * q B * q C *
          absoluteTraceChar k
            ((gamma1 * A + A) + gamma * B + gamma0 * C + C) := by
      rw [hchars]
    _ = q A * q B * q C *
          absoluteTraceChar k
            (gamma1 * A + gamma * B + gamma0 * C + C + A) := by
      rw [show
        (gamma1 * A + A) + gamma * B + gamma0 * C + C =
          gamma1 * A + gamma * B + gamma0 * C + C + A by ring]

end WildQuadraticCoefficientData

/-! ## The exact exceptional-boundary coefficients -/

/-- All residue-field data in the unique odd boundary row.  The square root
`r`, the upper Frobenius coefficient `gammaPrime`, and their equations are
retained so that this is the literal coefficient-table row, not merely the
four terms visible in the final displayed value. -/
structure WildQuadraticBoundaryData
    (k : Type*) [Field k] [Fintype k] [CharP k 2] where
  rho : k
  r : k
  gammaZero : k
  gamma : k
  gammaPrime : k
  rho_ne_zero : rho ≠ 0
  r_sq : r ^ 2 = rho
  one_add_rho_ne_zero : 1 + rho ≠ 0
  gammaPrime_sq : gammaPrime ^ 2 =
    (gamma + rho * gammaZero + rho + r) / (1 + rho)

namespace WildQuadraticBoundaryData

variable {k : Type*} [Field k] [Fintype k] [CharP k 2]

def A_rho (B : WildQuadraticBoundaryData k) : k :=
  B.rho / (1 + B.rho)

def B (D : WildQuadraticBoundaryData k) : k :=
  D.rho ^ 2 / (1 + D.rho ^ 2)

def C (D : WildQuadraticBoundaryData k) : k :=
  D.rho / (1 + D.rho ^ 2)

def gammaOne (D : WildQuadraticBoundaryData k) : k :=
  (D.gammaZero + D.rho * D.gamma + D.r) / (1 + D.rho)

def aOne (D : WildQuadraticBoundaryData k) : k :=
  D.gammaOne * D.A_rho + D.gamma * D.B + D.gammaZero * D.C +
    D.C + D.A_rho

/-- The exact completed coefficient-table constructor for this boundary
package, including both square-root witnesses. -/
def coefficientData (D : WildQuadraticBoundaryData k) :
    WildQuadraticCoefficientData k :=
  .boundaryOdd D.rho D.r D.gammaZero D.gamma D.gammaPrime D.rho_ne_zero
    D.r_sq D.one_add_rho_ne_zero D.gammaPrime_sq

noncomputable def value
    (q : CharTwoRefinement k) (D : WildQuadraticBoundaryData k) : ℂ :=
  q D.A_rho * q D.B * q D.C * absoluteTraceChar k D.aOne

theorem one_add_rho_sq_ne_zero (D : WildQuadraticBoundaryData k) :
    1 + D.rho ^ 2 ≠ 0 := by
  rw [show 1 + D.rho ^ 2 = (1 + D.rho) ^ 2 by
    rw [CharTwo.add_sq, one_pow]]
  exact pow_ne_zero 2 D.one_add_rho_ne_zero

theorem value_ne_zero
    (q : CharTwoRefinement k) (D : WildQuadraticBoundaryData k) :
    D.value q ≠ 0 := by
  unfold value
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (q.ne_zero D.A_rho) (q.ne_zero D.B))
      (q.ne_zero D.C))
    (AddChar.val_isUnit (absoluteTraceChar k) D.aOne).ne_zero

@[simp] theorem coefficientData_row (D : WildQuadraticBoundaryData k) :
    D.coefficientData.row = .boundaryOdd := rfl

@[simp] theorem coefficientData_chiCorrectionClass
    (D : WildQuadraticBoundaryData k) :
    D.coefficientData.chiCorrectionClass = some D.B := rfl

@[simp] theorem coefficientData_tauCorrectionClass
    (D : WildQuadraticBoundaryData k) :
    D.coefficientData.tauCorrectionClass = some D.C := rfl

@[simp] theorem coefficientData_chiAffine
    (D : WildQuadraticBoundaryData k) :
    D.coefficientData.affineCoefficient .chiF = some D.gamma := rfl

@[simp] theorem coefficientData_tauAffine
    (D : WildQuadraticBoundaryData k) :
    D.coefficientData.affineCoefficient .tau = some D.gammaZero := rfl

@[simp] theorem coefficientData_twistAffine
    (D : WildQuadraticBoundaryData k) :
    D.coefficientData.affineCoefficient .tauChiF = some D.gammaOne := rfl

end WildQuadraticBoundaryData

/-! ## Coherent join with the real PhaseReduction assembly -/

section RealQuadraticAssembly

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}

/-! ## Common actual rows, independent of a quadratic refinement -/

/-- The four actual local Lamprecht packages used by the quadratic phase
reduction, together with their exact selected stationary pairs.  Critical
values are intentionally absent: those are supplied only by the refined
compatibility below, while the all-even path records the actual constructors
instead. -/
structure WildQuadraticActualPhaseRows
    (V : WildQuadraticCommonCoefficientView F K t m)
    (data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character)
    (D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data)
    (A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)) : Type where
  extension : LocalLamprechtPhaseData K data.extensionQuasiChar
    data.extensionAddChar
  tau : LocalLamprechtPhaseData F
    (data.normCharacterData A.indexing.tau) data.baseAddChar
  base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar
  twist : LocalLamprechtPhaseData F
    (data.twistData A.indexing.tau) data.baseAddChar
  extension_eq : D.extension = LocalPhaseData.stationary extension
  tau_eq : D.normCharacter A.indexing.tau = LocalPhaseData.stationary tau
  base_eq : D.twist 1 = LocalPhaseData.stationary base
  twist_eq : D.twist A.indexing.tau = LocalPhaseData.stationary twist
  extension_pair : extension.selectedStationaryPair = V.stationaryPairs.chiK
  tau_pair : tau.selectedStationaryPair = V.stationaryPairs.tau
  base_pair : base.selectedStationaryPair = V.stationaryPairs.chiF
  twist_pair : twist.selectedStationaryPair = V.stationaryPairs.tauChiF

/-- Exact compatibility for one of the three all-even coefficient rows.
Every critical factor is certified by the constructor of the actual local
Lamprecht package, not by a coincidental equality of complex phases. -/
structure WildQuadraticAllEvenPhaseRowCompatibility
    (V : WildQuadraticAllEvenCoefficientView F K t m)
    (data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character)
    (D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data)
    (A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)) : Type where
  actualRows : WildQuadraticActualPhaseRows V.toCommon data D A
  extension_even : actualRows.extension.IsEven
  tau_even : actualRows.tau.IsEven
  base_even : actualRows.base.IsEven
  twist_even : actualRows.twist.IsEven

namespace WildQuadraticAllEvenPhaseRowCompatibility

/-- The residual Hasse quotient is one because all four *actual* local rows
are even Lamprecht rows. -/
theorem residualHasseQuotient_eq_one
    {V : WildQuadraticAllEvenCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)}
    (C : WildQuadraticAllEvenPhaseRowCompatibility V data D A) :
    A.residualHasseQuotient = 1 := by
  have hextension := C.actualRows.extension.criticalFactor_eq_one_of_isEven
    C.extension_even
  have htau := C.actualRows.tau.criticalFactor_eq_one_of_isEven C.tau_even
  have hbase := C.actualRows.base.criticalFactor_eq_one_of_isEven C.base_even
  have htwist := C.actualRows.twist.criticalFactor_eq_one_of_isEven C.twist_even
  unfold ExactQuadraticPhaseAssembly.residualHasseQuotient
  rw [C.actualRows.extension_eq, C.actualRows.tau_eq,
    C.actualRows.base_eq, C.actualRows.twist_eq]
  simp only [LocalPhaseData.criticalFactor]
  rw [hextension, htau, hbase, htwist]
  simp

end WildQuadraticAllEvenPhaseRowCompatibility

variable {V : WildQuadraticCoefficientView F K q t m}
  {data : FirstMainComputationalData F K V.chiFData.character
    V.psiF.character}
  {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
  {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
    V.psiF.character data D (t := t) (m := m)}

/-- The four real local PhaseReduction rows use exactly the four explicitly
supplied coefficient-table pairs and exactly the corresponding actual
critical phases.  No parity powers occur here: even rows already have
critical factor one, and odd rows contain their actual Hasse phase. -/
structure WildQuadraticPhaseRowCompatibility
    (V : WildQuadraticCoefficientView F K q t m)
    (data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character)
    (D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data)
    (A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)) : Prop where
  extensionRow : ∃ S : LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar,
    D.extension = LocalPhaseData.stationary S ∧
      S.selectedStationaryPair = V.stationaryPairs.chiK ∧
      S.criticalFactor = (V.coefficients.1).phaseFactor q .chiK
  tauRow : ∃ S : LocalLamprechtPhaseData F
      (data.normCharacterData A.indexing.tau) data.baseAddChar,
    D.normCharacter A.indexing.tau = LocalPhaseData.stationary S ∧
      S.selectedStationaryPair = V.stationaryPairs.tau ∧
      S.criticalFactor = quotientSourcePhase F V.criticalInputs.tauSource
  baseRow : ∃ S : LocalLamprechtPhaseData F (data.twistData 1)
      data.baseAddChar,
    D.twist 1 = LocalPhaseData.stationary S ∧
      S.selectedStationaryPair = V.stationaryPairs.chiF ∧
      S.criticalFactor = quotientSourcePhase F V.criticalInputs.chiFSource
  twistRow : ∃ S : LocalLamprechtPhaseData F
      (data.twistData A.indexing.tau) data.baseAddChar,
    D.twist A.indexing.tau = LocalPhaseData.stationary S ∧
      S.selectedStationaryPair = V.stationaryPairs.tauChiF ∧
      S.criticalFactor = (V.coefficients.1).phaseFactor q .tauChiF

namespace WildQuadraticPhaseRowCompatibility

/-- Forget only the refinement-dependent critical values, retaining the
four actual rows and their exact stationary pairs. -/
noncomputable def toActualPhaseRows
    (C : WildQuadraticPhaseRowCompatibility V data D A) :
    WildQuadraticActualPhaseRows V.toCommon data D A :=
  let extension := Classical.choose C.extensionRow
  let tau := Classical.choose C.tauRow
  let base := Classical.choose C.baseRow
  let twist := Classical.choose C.twistRow
  { extension := extension
    tau := tau
    base := base
    twist := twist
    extension_eq := (Classical.choose_spec C.extensionRow).1
    tau_eq := (Classical.choose_spec C.tauRow).1
    base_eq := (Classical.choose_spec C.baseRow).1
    twist_eq := (Classical.choose_spec C.twistRow).1
    extension_pair := (Classical.choose_spec C.extensionRow).2.1
    tau_pair := (Classical.choose_spec C.tauRow).2.1
    base_pair := (Classical.choose_spec C.baseRow).2.1
    twist_pair := (Classical.choose_spec C.twistRow).2.1 }

/-- The residual Hasse quotient is the actual coefficient-table phase ratio,
with extension and norm-character factors in the numerator and base and
twist factors in the denominator. -/
theorem residualHasseQuotient_eq_phaseRatio
    (C : WildQuadraticPhaseRowCompatibility V data D A) :
    A.residualHasseQuotient = (V.coefficients.1).phaseRatio q := by
  obtain ⟨extension, hextension, _, hextensionCritical⟩ := C.extensionRow
  obtain ⟨tau, htau, _, htauCritical⟩ := C.tauRow
  obtain ⟨base, hbase, _, hbaseCritical⟩ := C.baseRow
  obtain ⟨twist, htwist, _, htwistCritical⟩ := C.twistRow
  unfold ExactQuadraticPhaseAssembly.residualHasseQuotient
  rw [hextension, htau, hbase, htwist]
  simp only [LocalPhaseData.criticalFactor]
  rw [hextensionCritical, htauCritical, hbaseCritical, htwistCritical]
  exact V.actualPhaseAssembly.phaseRatio_exact

/-- The real error term is the quotient of the four actual stationary
complete factors, in the literal `chiK * tau / (chiF * tauChiF)` orientation.
The witnesses are precisely the supplied rows in `C`; no representative of a
stationary quotient class is manufactured here. -/
theorem errorTerm_eq_four_actual_completeFactors
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    {hDeltaF : IsDeltaFiniteLocalConstant DeltaF}
    {hDeltaK : IsDeltaFiniteLocalConstant DeltaK}
    (C : WildQuadraticPhaseRowCompatibility V data D A)
    (R : A.Result hDeltaF hDeltaK) :
    ∃ (extension : LocalLamprechtPhaseData K data.extensionQuasiChar
          data.extensionAddChar)
      (tau : LocalLamprechtPhaseData F
        (data.normCharacterData A.indexing.tau) data.baseAddChar)
      (base : LocalLamprechtPhaseData F (data.twistData 1)
        data.baseAddChar)
      (twist : LocalLamprechtPhaseData F
        (data.twistData A.indexing.tau) data.baseAddChar),
      D.extension = LocalPhaseData.stationary extension ∧
      D.normCharacter A.indexing.tau = LocalPhaseData.stationary tau ∧
      D.twist 1 = LocalPhaseData.stationary base ∧
      D.twist A.indexing.tau = LocalPhaseData.stationary twist ∧
      errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
        wildQuadraticCompleteErrorExpression extension tau base twist := by
  obtain ⟨extension, hextension, _, _⟩ := C.extensionRow
  obtain ⟨tau, htau, _, _⟩ := C.tauRow
  obtain ⟨base, hbase, _, _⟩ := C.baseRow
  obtain ⟨twist, htwist, _, _⟩ := C.twistRow
  refine ⟨extension, tau, base, twist, hextension, htau, hbase, htwist, ?_⟩
  have hadmissible :
      D.factors.admissibleCharacter =
        extension.admissibleFactor * tau.admissibleFactor /
          (base.admissibleFactor * twist.admissibleFactor) := by
    have h :=
      ExactQuadraticPhaseAssembly.admissibleFactor_eq_four_actual_rows
        A.indexing
    rw [hextension, htau, hbase, htwist] at h
    simpa only [LocalPhaseData.admissibleFactor] using h
  have helementaryD :
      D.factors.elementary =
        (D.extension.elementaryFactor *
            (D.normCharacter A.indexing.tau).elementaryFactor) /
          ((D.twist 1).elementaryFactor *
            (D.twist A.indexing.tau).elementaryFactor) := by
    letI := Fintype.ofFinite (NormCharacter F K)
    have hnorm :
        (∏ mu : NormCharacter F K,
            (D.normCharacter mu).elementaryFactor) =
          (D.normCharacter 1).elementaryFactor *
            (D.normCharacter A.indexing.tau).elementaryFactor := by
      rw [← Equiv.prod_comp A.indexing.index
        (fun mu : NormCharacter F K ↦
          (D.normCharacter mu).elementaryFactor)]
      rw [Fintype.prod_bool, A.indexing.index_true,
        A.indexing.index_false]
    have htwistProduct :
        (∏ mu : NormCharacter F K, (D.twist mu).elementaryFactor) =
          (D.twist 1).elementaryFactor *
            (D.twist A.indexing.tau).elementaryFactor := by
      rw [← Equiv.prod_comp A.indexing.index
        (fun mu : NormCharacter F K ↦ (D.twist mu).elementaryFactor)]
      rw [Fintype.prod_bool, A.indexing.index_true,
        A.indexing.index_false]
    have hid : (D.normCharacter 1).elementaryFactor = 1 := by
      rcases identityNormCharacterEndpoint_of_phaseData D with
        ⟨_, Gamma, hEq⟩
      rw [hEq]
      rfl
    simp only [FirstMainPhaseData.factors,
      FirstMainPhaseData.elementaryNumerator,
      FirstMainPhaseData.elementaryDenominator, hnorm, htwistProduct,
      hid, one_mul]
  have helementary :
      D.factors.elementary =
        extension.elementaryFactor * tau.elementaryFactor /
          (base.elementaryFactor * twist.elementaryFactor) := by
    rw [hextension, htau, hbase, htwist] at helementaryD
    simpa only [LocalPhaseData.elementaryFactor] using helementaryD
  have hcritical :
      D.factors.critical =
        extension.criticalFactor * tau.criticalFactor /
          (base.criticalFactor * twist.criticalFactor) := by
    have h := A.indexing.critical_eq_four_actual_factors
    rw [hextension, htau, hbase, htwist] at h
    simpa only [LocalPhaseData.criticalFactor] using h
  rw [R.completeAssembly]
  calc
    A.residualHasseQuotient *
          (V.psiF.character (-A.A * A.s) : ℂ) *
        (V.chiFData.character A.zZero : ℂ)⁻¹ *
          (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
        A.residualHasseQuotient *
          ((V.psiF.character (-A.A * A.s) : ℂ) *
            (V.chiFData.character A.zZero : ℂ)⁻¹ *
              (A.indexing.tau.1 A.zOne : ℂ)⁻¹) := by ring
    _ = D.factors.critical *
          (D.factors.admissibleCharacter * D.factors.elementary) := by
      rw [R.residual, R.admissibleElementary]
    _ = wildQuadraticCompleteErrorExpression extension tau base twist := by
      rw [hadmissible, helementary, hcritical]
      unfold wildQuadraticCompleteErrorExpression
      unfold LocalLamprechtPhaseData.completeFactor
        LocalLamprechtPhaseData.stationaryFactor
      field_simp [extension.admissibleFactor_ne_zero,
        tau.admissibleFactor_ne_zero, base.admissibleFactor_ne_zero,
        twist.admissibleFactor_ne_zero, extension.elementaryFactor_ne_zero,
        tau.elementaryFactor_ne_zero, base.elementaryFactor_ne_zero,
        twist.elementaryFactor_ne_zero, extension.criticalFactor_ne_zero,
        tau.criticalFactor_ne_zero, base.criticalFactor_ne_zero,
        twist.criticalFactor_ne_zero]

end WildQuadraticPhaseRowCompatibility

/-- The real assembly and the q-free common coefficient view use one exact
`A,u,n,z0,z1` package and the same local character data.  These are
equalities between supplied choices, not canonical representatives of
quotient classes. -/
structure WildQuadraticCommonCoordinateCompatibility
    (V : WildQuadraticCommonCoefficientView F K t m)
    (data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character)
    (D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data)
    (A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)) : Prop where
  baseData_eq : data.twistData 1 = V.chiFData
  baseAddData_eq : data.baseAddChar = V.psiF
  tauData_eq : data.normCharacterData A.indexing.tau = V.tauData
  A_eq : A.A = V.stationaryPairs.tau.ratio
  u_eq : A.u = (V.correction.u : K)
  n_eq : A.n = (V.correction.n : F)
  zZero_eq : A.zZero = V.z0Unit
  zOne_eq : A.zOne = V.z1Unit

namespace WildQuadraticCommonCoordinateCompatibility

variable {W : WildQuadraticCommonCoefficientView F K t m}
  {commonData : FirstMainComputationalData F K W.chiFData.character
    W.psiF.character}
  {commonPhase : FirstMainPhaseData F K W.chiFData.character
    W.psiF.character commonData}
  {commonAssembly : ExactQuadraticPhaseAssembly F K W.chiFData.character
    W.psiF.character commonData commonPhase (t := t) (m := m)}

theorem s_eq
    (C : WildQuadraticCommonCoordinateCompatibility W commonData commonPhase
      commonAssembly) :
    commonAssembly.s = W.correction.s := by
  rw [commonAssembly.s_eq, C.u_eq]
  rfl

theorem x_eq
    (C : WildQuadraticCommonCoordinateCompatibility W commonData commonPhase
      commonAssembly) :
    commonAssembly.x = W.correction.x := by
  rw [WildQuadraticCommonCorrectionData.x]
  calc
    commonAssembly.x = (commonAssembly.zZero : F) - 1 := by
      rw [commonAssembly.zZero_eq]; ring
    _ = (W.z0Unit : F) - 1 := by rw [C.zZero_eq]
    _ = W.correction.z0 - 1 := by rw [W.coe_z0Unit]

theorem y_eq
    (C : WildQuadraticCommonCoordinateCompatibility W commonData commonPhase
      commonAssembly) :
    commonAssembly.y = W.correction.y := by
  rw [WildQuadraticCommonCorrectionData.y]
  calc
    commonAssembly.y = (commonAssembly.zOne : F) - 1 := by
      rw [commonAssembly.zOne_eq]; ring
    _ = (W.z1Unit : F) - 1 := by rw [C.zOne_eq]
    _ = W.correction.z1 - 1 := by rw [W.coe_z1Unit]

/-- The real PhaseReduction correction coordinate is exactly the completed
CommonCorrection coordinate `s+n*x+y`. -/
theorem X_eq
    (C : WildQuadraticCommonCoordinateCompatibility W commonData commonPhase
      commonAssembly) :
    commonAssembly.X = W.correction.X := by
  rw [commonAssembly.X_eq, C.s_eq, C.n_eq, C.x_eq, C.y_eq]
  rfl

theorem tauCharacter_eq
    (C : WildQuadraticCommonCoordinateCompatibility W commonData commonPhase
      commonAssembly) :
    W.tauData.character = commonAssembly.indexing.tau.1 := by
  rw [← C.tauData_eq, commonData.normCharacterData_character]

end WildQuadraticCommonCoordinateCompatibility

structure WildQuadraticCoordinateCompatibility
    (V : WildQuadraticCoefficientView F K q t m)
    (data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character)
    (D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data)
    (A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)) : Prop where
  baseData_eq : data.twistData 1 = V.chiFData
  baseAddData_eq : data.baseAddChar = V.psiF
  tauData_eq : data.normCharacterData A.indexing.tau = V.tauData
  A_eq : A.A = V.stationaryPairs.tau.ratio
  u_eq : A.u = (V.correction.u : K)
  n_eq : A.n = (V.correction.n : F)
  zZero_eq : A.zZero = V.z0Unit
  zOne_eq : A.zOne = V.z1Unit

namespace WildQuadraticCoordinateCompatibility

/-- Forget the refinement while retaining the exact common coordinates. -/
theorem toCommon
    (C : WildQuadraticCoordinateCompatibility V data D A) :
    WildQuadraticCommonCoordinateCompatibility V.toCommon data D A where
  baseData_eq := C.baseData_eq
  baseAddData_eq := C.baseAddData_eq
  tauData_eq := C.tauData_eq
  A_eq := C.A_eq
  u_eq := C.u_eq
  n_eq := C.n_eq
  zZero_eq := C.zZero_eq
  zOne_eq := C.zOne_eq

/-- Promote q-free common coordinates to the legacy refined wrapper. -/
theorem ofCommon
    (C : WildQuadraticCommonCoordinateCompatibility V.toCommon data D A) :
    WildQuadraticCoordinateCompatibility V data D A where
  baseData_eq := C.baseData_eq
  baseAddData_eq := C.baseAddData_eq
  tauData_eq := C.tauData_eq
  A_eq := C.A_eq
  u_eq := C.u_eq
  n_eq := C.n_eq
  zZero_eq := C.zZero_eq
  zOne_eq := C.zOne_eq

theorem s_eq (C : WildQuadraticCoordinateCompatibility V data D A) :
    A.s = V.correction.s := C.toCommon.s_eq

theorem x_eq (C : WildQuadraticCoordinateCompatibility V data D A) :
    A.x = V.correction.x := C.toCommon.x_eq

theorem y_eq (C : WildQuadraticCoordinateCompatibility V data D A) :
    A.y = V.correction.y := C.toCommon.y_eq

theorem X_eq (C : WildQuadraticCoordinateCompatibility V data D A) :
    A.X = V.correction.X := C.toCommon.X_eq

theorem tauCharacter_eq
    (C : WildQuadraticCoordinateCompatibility V data D A) :
    V.tauData.character = A.indexing.tau.1 := C.toCommon.tauCharacter_eq

end WildQuadraticCoordinateCompatibility

/-! ## The two retained inverse-character corrections -/

/-- The two lower correction factors attached to one real quadratic
PhaseReduction assembly. Present odd factors retain their full local records;
absence carries the exact pure linearization and contributes one. -/
structure WildQuadraticRefinementAssembly
    (V : WildQuadraticCoefficientView F K q t m)
    (data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character)
    (D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data)
    (A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m))
    (coordinates : WildQuadraticCoordinateCompatibility V data D A) : Type where
  chiCorrection : Option (WildQuadraticRefinementCorrection F
    (ResidueField F) V.psiF V.chiFData q)
  tauCorrection : Option (WildQuadraticRefinementCorrection F
    (ResidueField F) V.psiF V.tauData q)
  chi_selection : chiCorrection.map
    WildQuadraticRefinementCorrection.normalizedClass =
      (V.coefficients.1).chiCorrectionClass
  tau_selection : tauCorrection.map
    WildQuadraticRefinementCorrection.normalizedClass =
      (V.coefficients.1).tauCorrectionClass
  chi_absent : chiCorrection = none →
    (V.chiFData.character A.zZero : ℂ)⁻¹ =
      (V.psiF.character (-A.A * A.n * A.x) : ℂ)
  tau_absent : tauCorrection = none →
    (V.tauData.character A.zOne : ℂ)⁻¹ =
      (V.psiF.character (-A.A * A.y) : ℂ)
  chi_present : ∀ C, chiCorrection = some C →
    C.correction = A.x ∧
      (C.Gamma : Fˣ) = V.stationaryPairs.chiF.gamma ∧
      C.beta = V.stationaryPairs.chiF.beta ∧
      C.beta / ((C.Gamma : Fˣ) : F) = A.A * A.n ∧
      (V.coefficients.1).affineCoefficient .chiF =
        some C.affineCoefficient ∧
      (V.coefficients.1).chiCorrectionClass = some C.normalizedClass
  tau_present : ∀ C, tauCorrection = some C →
    C.correction = A.y ∧
      (C.Gamma : Fˣ) = V.stationaryPairs.tau.gamma ∧
      C.beta = V.stationaryPairs.tau.beta ∧
      C.beta / ((C.Gamma : Fˣ) : F) = A.A ∧
      (V.coefficients.1).affineCoefficient .tau =
        some C.affineCoefficient ∧
      (V.coefficients.1).tauCorrectionClass = some C.normalizedClass

namespace WildQuadraticRefinementAssembly

/-- The selected base correction has exactly the coefficient-table value. -/
theorem chiValue_eq_table
    (R : WildQuadraticRefinementAssembly V data D A coordinates) :
    wildQuadraticOptionalCorrectionValue R.chiCorrection =
      (V.coefficients.1).chiCorrectionValue q := by
  cases hC : R.chiCorrection with
  | none =>
      have hclass : (V.coefficients.1).chiCorrectionClass = none := by
        simpa [hC] using R.chi_selection.symm
      simp [wildQuadraticOptionalCorrectionValue,
        WildQuadraticCoefficientData.chiCorrectionValue,
        WildQuadraticCoefficientData.selectedCorrectionValue, hclass]
  | some C =>
      obtain ⟨_, _, _, _, haffine, _⟩ := R.chi_present C hC
      have hclass : (V.coefficients.1).chiCorrectionClass =
          some C.normalizedClass := by
        simpa [hC] using R.chi_selection.symm
      simp [wildQuadraticOptionalCorrectionValue,
        WildQuadraticCoefficientData.chiCorrectionValue,
        WildQuadraticCoefficientData.selectedCorrectionValue,
        haffine, hclass, WildQuadraticRefinementCorrection.value]

/-- The selected norm-character correction has exactly the table value. -/
theorem tauValue_eq_table
    (R : WildQuadraticRefinementAssembly V data D A coordinates) :
    wildQuadraticOptionalCorrectionValue R.tauCorrection =
      (V.coefficients.1).tauCorrectionValue q := by
  cases hC : R.tauCorrection with
  | none =>
      have hclass : (V.coefficients.1).tauCorrectionClass = none := by
        simpa [hC] using R.tau_selection.symm
      simp [wildQuadraticOptionalCorrectionValue,
        WildQuadraticCoefficientData.tauCorrectionValue,
        WildQuadraticCoefficientData.selectedCorrectionValue, hclass]
  | some C =>
      obtain ⟨_, _, _, _, haffine, _⟩ := R.tau_present C hC
      have hclass : (V.coefficients.1).tauCorrectionClass =
          some C.normalizedClass := by
        simpa [hC] using R.tau_selection.symm
      simp [wildQuadraticOptionalCorrectionValue,
        WildQuadraticCoefficientData.tauCorrectionValue,
        WildQuadraticCoefficientData.selectedCorrectionValue,
        haffine, hclass, WildQuadraticRefinementCorrection.value]

/-- Exact base inverse-character orientation, including the positive
refinement correction in the odd case. -/
theorem chiInverse_eq_phase_mul_value
    (R : WildQuadraticRefinementAssembly V data D A coordinates) :
    (V.chiFData.character A.zZero : ℂ)⁻¹ =
      (V.psiF.character (-A.A * A.n * A.x) : ℂ) *
        wildQuadraticOptionalCorrectionValue R.chiCorrection := by
  cases hC : R.chiCorrection with
  | none => simpa [wildQuadraticOptionalCorrectionValue, hC] using R.chi_absent hC
  | some C =>
      obtain ⟨hcorrection, _, _, hratio, _, _⟩ := R.chi_present C hC
      have hunit : A.zZero =
          Units.mk0 (1 + C.correction) C.one_add_correction_ne_zero := by
        apply Units.ext
        change (A.zZero : F) = 1 + C.correction
        rw [A.zZero_eq, hcorrection]
      have hargument :
          C.beta * C.correction / ((C.Gamma : Fˣ) : F) =
            A.A * A.n * A.x := by
        rw [hcorrection]
        calc
          C.beta * A.x / ((C.Gamma : Fˣ) : F) =
              (C.beta / ((C.Gamma : Fˣ) : F)) * A.x := by
                field_simp [Units.ne_zero (C.Gamma : Fˣ)]
          _ = A.A * A.n * A.x := by rw [hratio]
      have hneg : -(A.A * A.n * A.x) = -A.A * A.n * A.x := by ring
      calc
        (V.chiFData.character A.zZero : ℂ)⁻¹ =
            (V.chiFData.character
              (Units.mk0 (1 + C.correction)
                C.one_add_correction_ne_zero) : ℂ)⁻¹ := by rw [hunit]
        _ = (V.psiF.character
              (-(C.beta * C.correction / ((C.Gamma : Fˣ) : F))) : ℂ) *
              C.value := C.inverseCharacter_eq
        _ = (V.psiF.character (-A.A * A.n * A.x) : ℂ) *
              wildQuadraticOptionalCorrectionValue (some C) := by
          rw [hargument, hneg]
          rw [wildQuadraticOptionalCorrectionValue_some]

/-- Exact norm-character inverse orientation, with its own conductor, depth,
gamma, numerator, and positive correction retained. -/
theorem tauInverse_eq_phase_mul_value
    (R : WildQuadraticRefinementAssembly V data D A coordinates) :
    (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
      (V.psiF.character (-A.A * A.y) : ℂ) *
        wildQuadraticOptionalCorrectionValue R.tauCorrection := by
  rw [← coordinates.tauCharacter_eq]
  cases hC : R.tauCorrection with
  | none => simpa [wildQuadraticOptionalCorrectionValue, hC] using R.tau_absent hC
  | some C =>
      obtain ⟨hcorrection, _, _, hratio, _, _⟩ := R.tau_present C hC
      have hunit : A.zOne =
          Units.mk0 (1 + C.correction) C.one_add_correction_ne_zero := by
        apply Units.ext
        change (A.zOne : F) = 1 + C.correction
        rw [A.zOne_eq, hcorrection]
      have hargument :
          C.beta * C.correction / ((C.Gamma : Fˣ) : F) =
            A.A * A.y := by
        rw [hcorrection]
        calc
          C.beta * A.y / ((C.Gamma : Fˣ) : F) =
              (C.beta / ((C.Gamma : Fˣ) : F)) * A.y := by
                field_simp [Units.ne_zero (C.Gamma : Fˣ)]
          _ = A.A * A.y := by rw [hratio]
      have hneg : -(A.A * A.y) = -A.A * A.y := by ring
      calc
        (V.tauData.character A.zOne : ℂ)⁻¹ =
            (V.tauData.character
              (Units.mk0 (1 + C.correction)
                C.one_add_correction_ne_zero) : ℂ)⁻¹ := by rw [hunit]
        _ = (V.psiF.character
              (-(C.beta * C.correction / ((C.Gamma : Fˣ) : F))) : ℂ) *
              C.value := C.inverseCharacter_eq
        _ = (V.psiF.character (-A.A * A.y) : ℂ) *
              wildQuadraticOptionalCorrectionValue (some C) := by
          rw [hargument, hneg]
          rw [wildQuadraticOptionalCorrectionValue_some]

/-- Assemble only the two justified inverse-character corrections. The
residual four-Hasse quotient remains untouched. -/
theorem elementaryCorrection_eq
    (R : WildQuadraticRefinementAssembly V data D A coordinates) :
    (V.psiF.character (-A.A * A.s) : ℂ) *
        (V.chiFData.character A.zZero : ℂ)⁻¹ *
          (A.indexing.tau.1 A.zOne : ℂ)⁻¹ =
      wildQuadraticOptionalCorrectionValue R.chiCorrection *
        wildQuadraticOptionalCorrectionValue R.tauCorrection *
          (V.psiF.character (-A.A * A.X) : ℂ) := by
  rw [R.chiInverse_eq_phase_mul_value,
    R.tauInverse_eq_phase_mul_value]
  have hmap (z w : F) :
      (V.psiF.character (z + w) : ℂ) =
        (V.psiF.character z : ℂ) * (V.psiF.character w : ℂ) :=
    congrArg (Units.val : ℂˣ → ℂ)
      (ContinuousAddChar.map_add_eq_mul V.psiF.character z w)
  calc
    (V.psiF.character (-A.A * A.s) : ℂ) *
          ((V.psiF.character (-A.A * A.n * A.x) : ℂ) *
            wildQuadraticOptionalCorrectionValue R.chiCorrection) *
          ((V.psiF.character (-A.A * A.y) : ℂ) *
            wildQuadraticOptionalCorrectionValue R.tauCorrection) =
        wildQuadraticOptionalCorrectionValue R.chiCorrection *
          wildQuadraticOptionalCorrectionValue R.tauCorrection *
            ((V.psiF.character (-A.A * A.s) : ℂ) *
              (V.psiF.character (-A.A * A.n * A.x) : ℂ) *
                (V.psiF.character (-A.A * A.y) : ℂ)) := by ring
    _ = wildQuadraticOptionalCorrectionValue R.chiCorrection *
          wildQuadraticOptionalCorrectionValue R.tauCorrection *
            (V.psiF.character
              ((-A.A * A.s) + (-A.A * A.n * A.x) + (-A.A * A.y)) : ℂ) := by
      rw [hmap ((-A.A * A.s) + (-A.A * A.n * A.x)) (-A.A * A.y),
        hmap (-A.A * A.s) (-A.A * A.n * A.x)]
    _ = wildQuadraticOptionalCorrectionValue R.chiCorrection *
          wildQuadraticOptionalCorrectionValue R.tauCorrection *
            (V.psiF.character (-A.A * A.X) : ℂ) := by
      congr 3
      rw [A.X_eq]
      ring

end WildQuadraticRefinementAssembly

/-! ## The q-free formula for the three all-even rows -/

section AllEvenFormula

variable {W : WildQuadraticAllEvenCoefficientView F K t m}
  {commonData : FirstMainComputationalData F K W.chiFData.character
    W.psiF.character}
  {commonPhase : FirstMainPhaseData F K W.chiFData.character
    W.psiF.character commonData}
  {commonAssembly : ExactQuadraticPhaseAssembly F K W.chiFData.character
    W.psiF.character commonData commonPhase (t := t) (m := m)}

/-- Q-free output of the complete stationary assembly in an exact all-even
row.  The norm-ratio linearizations come from the existing PhaseReduction
`CompleteCorrectionData`; the residual quotient is then evaluated solely
from the four actual even Lamprecht constructors. -/
structure WildQuadraticAllEvenErrorFormula
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (rows : WildQuadraticAllEvenPhaseRowCompatibility W commonData commonPhase
      commonAssembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W.toCommon
      commonData commonPhase commonAssembly)
    (completeCorrection : commonAssembly.CompleteCorrectionData) : Prop where
  phaseReduction : commonAssembly.Result hDeltaF hDeltaK
  coordinateCompatibility : WildQuadraticCommonCoordinateCompatibility
    W.toCommon commonData commonPhase commonAssembly
  correctionData : commonAssembly.CompleteCorrectionData
  allEvenRow : W.row.IsAllEven
  residual_eq_one : commonAssembly.residualHasseQuotient = 1
  exact_reduced :
    errorTerm F K DeltaF DeltaK W.chiFData.character W.psiF.character =
      commonAssembly.residualHasseQuotient *
        (W.psiF.character (-commonAssembly.A * commonAssembly.X) : ℂ)
  exact_formula :
    errorTerm F K DeltaF DeltaK W.chiFData.character W.psiF.character =
      (W.psiF.character
        (-commonAssembly.A * W.correction.X) : ℂ)

/-- Assemble an exact all-even row through the pre-existing q-free
PhaseReduction correction theorem, then remove the residual quotient using
the actual even local packages. -/
theorem wildQuadratic_allEvenErrorFormula
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (rows : WildQuadraticAllEvenPhaseRowCompatibility W commonData commonPhase
      commonAssembly)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W.toCommon
      commonData commonPhase commonAssembly)
    (completeCorrection : commonAssembly.CompleteCorrectionData) :
    WildQuadraticAllEvenErrorFormula hDeltaF hDeltaK rows coordinates
      completeCorrection := by
  have hresidual := rows.residualHasseQuotient_eq_one
  have hreduced := completeCorrection.errorTerm_eq_residual_mul_phase
    hDeltaF hDeltaK commonAssembly
  refine
    { phaseReduction := commonAssembly.result hDeltaF hDeltaK
      coordinateCompatibility := coordinates
      correctionData := completeCorrection
      allEvenRow := W.isAllEven
      residual_eq_one := hresidual
      exact_reduced := hreduced
      exact_formula := ?_ }
  calc
    errorTerm F K DeltaF DeltaK W.chiFData.character W.psiF.character =
        commonAssembly.residualHasseQuotient *
          (W.psiF.character
            (-commonAssembly.A * commonAssembly.X) : ℂ) := hreduced
    _ = (W.psiF.character
          (-commonAssembly.A * W.correction.X) : ℂ) := by
      rw [hresidual, coordinates.X_eq]
      simp

end AllEvenFormula

/-! ## The complete formula before the later cancellation theorem -/

/-- Structured output of Proposition `prop:quadratic-complete-assembly` at
the point where the actual four critical factors, both inverse-character
corrections, and the common norm--trace phase have all been assembled.  The
two finite correction records are parameters of the result, so every one of
their conductors, depths, gammas, numerators, and inverse orientations
remains available. -/
structure WildQuadraticErrorFormula
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (rows : WildQuadraticPhaseRowCompatibility V data D A)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A)
    (refinements : WildQuadraticRefinementAssembly V data D A coordinates) :
    Prop where
  phaseReduction : A.Result hDeltaF hDeltaK
  rowCompatibility : WildQuadraticPhaseRowCompatibility V data D A
  coordinateCompatibility : WildQuadraticCoordinateCompatibility V data D A
  coefficientCertificate :
    WildQuadraticCoefficientCertificate q V.coefficients.1
  actualPhaseAssembly : WildQuadraticActualPhaseAssembly F K q
    V.criticalInputs V.stationaryPairs V.tauData V.chiFData V.psiF
  parameterRange : PhaseParameterRange t m
  breakUnitRetained : A.twistStationaryNumerator =
    A.baseStationaryNumerator + A.stationaryScale *
      (((A.breakUnit : unitFiltration F t) : Fˣ) : F)
  criticalDenominator_ne_zero :
    (D.twist 1).criticalFactor *
      (D.twist A.indexing.tau).criticalFactor ≠ 0
  phaseRatio_ne_zero : (V.coefficients.1).phaseRatio q ≠ 0
  residual_eq_phaseRatio : A.residualHasseQuotient =
    (V.coefficients.1).phaseRatio q
  exact_unsimplified :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
      (V.coefficients.1).phaseRatio q *
          (V.psiF.character
            (-A.A * trace F K (V.correction.u : K)) : ℂ) *
        (V.chiFData.character V.z0Unit : ℂ)⁻¹ *
          (V.tauData.character V.z1Unit : ℂ)⁻¹
  exact_assembled :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
      (V.coefficients.1).phaseRatio q *
          (V.coefficients.1).chiCorrectionValue q *
        (V.coefficients.1).tauCorrectionValue q *
          (V.psiF.character (-A.A * V.correction.X) : ℂ)

/-- Join the real structured PhaseReduction result to the completed
coefficient table.  This is the complete stationary assembly; it deliberately
does not apply either the nonboundary or boundary finite-field identity. -/
theorem wildQuadratic_errorFormula
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (rows : WildQuadraticPhaseRowCompatibility V data D A)
    (coordinates : WildQuadraticCoordinateCompatibility V data D A)
    (refinements : WildQuadraticRefinementAssembly V data D A coordinates) :
    WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates refinements := by
  let R := A.result hDeltaF hDeltaK
  have hresidual := rows.residualHasseQuotient_eq_phaseRatio
  have htable := WildQuadraticCoefficientTable q V
  dsimp only at htable
  refine
    { phaseReduction := R
      rowCompatibility := rows
      coordinateCompatibility := coordinates
      coefficientCertificate := htable.1
      actualPhaseAssembly := V.actualPhaseAssembly
      parameterRange := R.range
      breakUnitRetained := R.breakUnitRetained
      criticalDenominator_ne_zero := R.criticalDenominator
      phaseRatio_ne_zero := ?_
      residual_eq_phaseRatio := hresidual
      exact_unsimplified := ?_
      exact_assembled := ?_ }
  · rw [← hresidual]
    exact div_ne_zero
      (mul_ne_zero D.extension.criticalFactor_ne_zero
        (D.normCharacter A.indexing.tau).criticalFactor_ne_zero)
      R.criticalDenominator
  · calc
      errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
          A.residualHasseQuotient *
              (V.psiF.character (-A.A * A.s) : ℂ) *
            (V.chiFData.character A.zZero : ℂ)⁻¹ *
              (A.indexing.tau.1 A.zOne : ℂ)⁻¹ :=
        R.completeAssembly
      _ = (V.coefficients.1).phaseRatio q *
              (V.psiF.character
                (-A.A * trace F K (V.correction.u : K)) : ℂ) *
            (V.chiFData.character V.z0Unit : ℂ)⁻¹ *
              (V.tauData.character V.z1Unit : ℂ)⁻¹ := by
        rw [hresidual, A.s_eq, coordinates.u_eq, coordinates.zZero_eq,
          coordinates.zOne_eq, coordinates.tauCharacter_eq]
  · calc
      errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
          A.residualHasseQuotient *
            ((V.psiF.character (-A.A * A.s) : ℂ) *
              (V.chiFData.character A.zZero : ℂ)⁻¹ *
                (A.indexing.tau.1 A.zOne : ℂ)⁻¹) := by
        rw [R.completeAssembly]
        ring
      _ = A.residualHasseQuotient *
            (wildQuadraticOptionalCorrectionValue
                refinements.chiCorrection *
              wildQuadraticOptionalCorrectionValue
                refinements.tauCorrection *
              (V.psiF.character (-A.A * A.X) : ℂ)) := by
        rw [refinements.elementaryCorrection_eq]
      _ = (V.coefficients.1).phaseRatio q *
              (V.coefficients.1).chiCorrectionValue q *
            (V.coefficients.1).tauCorrectionValue q *
              (V.psiF.character (-A.A * V.correction.X) : ℂ) := by
        rw [hresidual, refinements.chiValue_eq_table,
          refinements.tauValue_eq_table, coordinates.X_eq]
        ring

/-! ## Separate formula contracts for the two downstream cases -/

section DownstreamViews

variable {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
  {hDeltaF : IsDeltaFiniteLocalConstant DeltaF}
  {hDeltaK : IsDeltaFiniteLocalConstant DeltaK}
  {rows : WildQuadraticPhaseRowCompatibility V data D A}
  {coordinates : WildQuadraticCoordinateCompatibility V data D A}
  {refinements : WildQuadraticRefinementAssembly V data D A coordinates}

/-- Output consumed by `WildQuadratic/NonBoundary`.  Only the stationary
phase quotient and its two justified critical corrections are evaluated;
the common phase `psiF(-A*X)` is deliberately retained. -/
structure WildQuadraticNonboundaryFormula
    (formula : WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates
      refinements)
    (hrow : (V.coefficients.1).row ≠ .boundaryOdd) : Prop where
  row_ne_boundaryOdd : (V.coefficients.1).row ≠ .boundaryOdd
  exact_formula :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
      (V.psiF.character (-A.A * V.correction.X) : ℂ)

/-- Evaluate the completed coefficient table in every nonboundary row.  No
later theorem asserting that the remaining additive phase is one is used. -/
theorem wildQuadratic_errorFormula_nonboundary
    (formula : WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates
      refinements)
    (hrow : (V.coefficients.1).row ≠ .boundaryOdd) :
    WildQuadraticNonboundaryFormula formula hrow where
  row_ne_boundaryOdd := hrow
  exact_formula := by
    calc
      errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
          (V.coefficients.1).phaseRatio q *
              (V.coefficients.1).chiCorrectionValue q *
            (V.coefficients.1).tauCorrectionValue q *
              (V.psiF.character (-A.A * V.correction.X) : ℂ) :=
        formula.exact_assembled
      _ = (V.psiF.character (-A.A * V.correction.X) : ℂ) := by
        have hfinite :
            (V.coefficients.1).phaseRatio q *
                (V.coefficients.1).chiCorrectionValue q *
              (V.coefficients.1).tauCorrectionValue q = 1 :=
          WildQuadraticCoefficientData.phaseRatio_mul_corrections_eq_one_of_not_boundaryOdd
            (k := ResidueField F) q (V.coefficients.1) hrow
        rw [hfinite]
        simp

/-- The only extra input needed to evaluate the odd boundary: the
coefficient view is the displayed boundary row, and the retained common
norm--trace phase has the exact residue value `psi0(C)`. -/
structure WildQuadraticBoundaryCompatibility
    (boundary : WildQuadraticBoundaryData (ResidueField F)) : Prop where
  coefficientData_eq : V.coefficients.1 = boundary.coefficientData
  elementaryPhase_eq :
    (V.psiF.character (-A.A * V.correction.X) : ℂ) =
      absoluteTraceChar (ResidueField F) boundary.C

/-- Output consumed by `WildQuadratic/Boundary`.  Besides the displayed
boundary value, it retains the two exact correction records selected in the
assembly.  Their embedded conductor decompositions, admissible gammas,
numerators, critical classes, and positively oriented inverse-character
equations are therefore still available downstream. -/
structure WildQuadraticBoundaryFormula
    (formula : WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates
      refinements)
    (boundary : WildQuadraticBoundaryData (ResidueField F))
    (chiCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
      V.psiF V.chiFData q)
    (tauCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
      V.psiF V.tauData q)
    (compatibility : WildQuadraticBoundaryCompatibility
      (V := V) (A := A) boundary) : Prop where
  coefficientData_eq : V.coefficients.1 = boundary.coefficientData
  chiCorrection_selected : refinements.chiCorrection = some chiCorrection
  tauCorrection_selected : refinements.tauCorrection = some tauCorrection
  chiCorrection_coordinate : chiCorrection.correction = A.x
  tauCorrection_coordinate : tauCorrection.correction = A.y
  chiGamma_selected :
    (chiCorrection.Gamma : Fˣ) = V.stationaryPairs.chiF.gamma
  tauGamma_selected :
    (tauCorrection.Gamma : Fˣ) = V.stationaryPairs.tau.gamma
  chiNumerator_selected :
    chiCorrection.beta = V.stationaryPairs.chiF.beta
  tauNumerator_selected :
    tauCorrection.beta = V.stationaryPairs.tau.beta
  chiCorrection_ratio :
    chiCorrection.beta / ((chiCorrection.Gamma : Fˣ) : F) = A.A * A.n
  tauCorrection_ratio :
    tauCorrection.beta / ((tauCorrection.Gamma : Fˣ) : F) = A.A
  chiCorrection_class : chiCorrection.normalizedClass = boundary.B
  tauCorrection_class : tauCorrection.normalizedClass = boundary.C
  chiCorrection_affine : chiCorrection.affineCoefficient = boundary.gamma
  tauCorrection_affine :
    tauCorrection.affineCoefficient = boundary.gammaZero
  chiCorrectionValue_eq :
    boundary.coefficientData.chiCorrectionValue q = chiCorrection.value
  tauCorrectionValue_eq :
    boundary.coefficientData.tauCorrectionValue q = tauCorrection.value
  elementaryBoundary_eq :
    (V.psiF.character (-A.A * V.correction.X) : ℂ) =
      absoluteTraceChar (ResidueField F) boundary.C
  exact_stationary :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
      boundary.coefficientData.phaseRatio q *
          chiCorrection.value * tauCorrection.value *
          absoluteTraceChar (ResidueField F) boundary.C
  exact_formula :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
      boundary.value q

/-- Evaluate the exact odd-boundary row.  The two supplied corrections are
the very records selected by the complete assembly, so no gamma, inverse,
conductor, or depth datum is reconstructed from a quotient class. -/
theorem wildQuadratic_errorFormula_boundary
    (formula : WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates
      refinements)
    (boundary : WildQuadraticBoundaryData (ResidueField F))
    (chiCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
      V.psiF V.chiFData q)
    (tauCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
      V.psiF V.tauData q)
    (compatibility : WildQuadraticBoundaryCompatibility
      (V := V) (A := A) boundary)
    (hchi : refinements.chiCorrection = some chiCorrection)
    (htau : refinements.tauCorrection = some tauCorrection) :
    WildQuadraticBoundaryFormula formula boundary chiCorrection tauCorrection
      compatibility := by
  obtain ⟨hchiCoordinate, hchiGamma, hchiBeta, hchiRatio,
      hchiAffine, hchiClass⟩ := refinements.chi_present chiCorrection hchi
  obtain ⟨htauCoordinate, htauGamma, htauBeta, htauRatio,
      htauAffine, htauClass⟩ := refinements.tau_present tauCorrection htau
  have hchiClass' : chiCorrection.normalizedClass = boundary.B := by
    rw [compatibility.coefficientData_eq] at hchiClass
    simpa using hchiClass.symm
  have htauClass' : tauCorrection.normalizedClass = boundary.C := by
    rw [compatibility.coefficientData_eq] at htauClass
    simpa using htauClass.symm
  have hchiAffine' : chiCorrection.affineCoefficient = boundary.gamma := by
    rw [compatibility.coefficientData_eq] at hchiAffine
    simpa using hchiAffine.symm
  have htauAffine' :
      tauCorrection.affineCoefficient = boundary.gammaZero := by
    rw [compatibility.coefficientData_eq] at htauAffine
    simpa using htauAffine.symm
  have hchiValue :
      boundary.coefficientData.chiCorrectionValue q = chiCorrection.value := by
    have h := refinements.chiValue_eq_table
    rw [hchi, wildQuadraticOptionalCorrectionValue_some,
      compatibility.coefficientData_eq] at h
    exact h.symm
  have htauValue :
      boundary.coefficientData.tauCorrectionValue q = tauCorrection.value := by
    have h := refinements.tauValue_eq_table
    rw [htau, wildQuadraticOptionalCorrectionValue_some,
      compatibility.coefficientData_eq] at h
    exact h.symm
  refine
    { coefficientData_eq := compatibility.coefficientData_eq
      chiCorrection_selected := hchi
      tauCorrection_selected := htau
      chiCorrection_coordinate := hchiCoordinate
      tauCorrection_coordinate := htauCoordinate
      chiGamma_selected := hchiGamma
      tauGamma_selected := htauGamma
      chiNumerator_selected := hchiBeta
      tauNumerator_selected := htauBeta
      chiCorrection_ratio := hchiRatio
      tauCorrection_ratio := htauRatio
      chiCorrection_class := hchiClass'
      tauCorrection_class := htauClass'
      chiCorrection_affine := hchiAffine'
      tauCorrection_affine := htauAffine'
      chiCorrectionValue_eq := hchiValue
      tauCorrectionValue_eq := htauValue
      elementaryBoundary_eq := compatibility.elementaryPhase_eq
      exact_stationary := ?_
      exact_formula := ?_ }
  · calc
      errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
          (V.coefficients.1).phaseRatio q *
              (V.coefficients.1).chiCorrectionValue q *
            (V.coefficients.1).tauCorrectionValue q *
              (V.psiF.character (-A.A * V.correction.X) : ℂ) :=
        formula.exact_assembled
      _ = boundary.coefficientData.phaseRatio q *
              chiCorrection.value * tauCorrection.value *
              absoluteTraceChar (ResidueField F) boundary.C := by
        rw [compatibility.coefficientData_eq,
          compatibility.elementaryPhase_eq, hchiValue, htauValue]
  · calc
      errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character =
          boundary.coefficientData.phaseRatio q *
              boundary.coefficientData.chiCorrectionValue q *
            boundary.coefficientData.tauCorrectionValue q *
              absoluteTraceChar (ResidueField F) boundary.C := by
        calc
          errorTerm F K DeltaF DeltaK V.chiFData.character
              V.psiF.character =
              (V.coefficients.1).phaseRatio q *
                  (V.coefficients.1).chiCorrectionValue q *
                (V.coefficients.1).tauCorrectionValue q *
                  (V.psiF.character (-A.A * V.correction.X) : ℂ) :=
            formula.exact_assembled
          _ = _ := by
            rw [compatibility.coefficientData_eq,
              compatibility.elementaryPhase_eq]
      _ = boundary.value q := by
        simpa [WildQuadraticBoundaryData.coefficientData,
          WildQuadraticBoundaryData.value,
          WildQuadraticBoundaryData.A_rho,
          WildQuadraticBoundaryData.B,
          WildQuadraticBoundaryData.C,
          WildQuadraticBoundaryData.gammaOne,
          WildQuadraticBoundaryData.aOne] using
          WildQuadraticCoefficientData.phaseRatio_mul_corrections_boundaryOdd
            q boundary.rho boundary.r boundary.gammaZero boundary.gamma
              boundary.gammaPrime boundary.rho_ne_zero boundary.r_sq
                boundary.one_add_rho_ne_zero boundary.gammaPrime_sq

end DownstreamViews

end RealQuadraticAssembly

end

end LanglandsFirstMainLemma
