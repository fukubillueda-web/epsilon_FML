import LanglandsFirstMainLemma.Delta.ErrorTerm
import LanglandsFirstMainLemma.Parameters.PhaseReduction.StationaryData

/-!
# Local phase packages and the four First-Main factors

This module separates endpoint and stationary local phase packages and
expands the complete First-Main error quotient into its endpoint,
admissible-character, elementary, and critical factors. The identity norm
character remains an actual endpoint; no residual cancellation is asserted.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Endpoints and stationary conductors in one local package -/

/-- A local phase package.  Endpoint conductors retain their actual
`deltaFinite` value but contain no stationary class.  Every conductor above
one is represented by a genuine `LocalLamprechtPhaseData`. -/
inductive LocalPhaseData
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E) where
  | endpoint
      (hendpoint : chi.conductor ≤ 1)
      (Gamma : AdmissibleGamma E chi psi)
  | stationary
      (data : LocalLamprechtPhaseData E chi psi)

namespace LocalPhaseData

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

def gamma (D : LocalPhaseData E chi psi) : AdmissibleGamma E chi psi :=
  match D with
  | .endpoint _ Gamma => Gamma
  | .stationary S => S.gamma

/-- Endpoint contribution.  It is the actual finite local constant at
conductor zero or one and is never disguised as a stationary parameter. -/
noncomputable def endpointFactor (D : LocalPhaseData E chi psi) : ℂ :=
  match D with
  | .endpoint _ Gamma => deltaFinite chi psi Gamma
  | .stationary _ => 1

def admissibleFactor (D : LocalPhaseData E chi psi) : ℂ :=
  match D with
  | .endpoint _ _ => 1
  | .stationary S => S.admissibleFactor

def elementaryFactor (D : LocalPhaseData E chi psi) : ℂ :=
  match D with
  | .endpoint _ _ => 1
  | .stationary S => S.elementaryFactor

noncomputable def criticalFactor (D : LocalPhaseData E chi psi) : ℂ :=
  match D with
  | .endpoint _ _ => 1
  | .stationary S => S.criticalFactor

noncomputable def completeFactor (D : LocalPhaseData E chi psi) : ℂ :=
  D.endpointFactor * D.admissibleFactor * D.elementaryFactor * D.criticalFactor

theorem endpointFactor_ne_zero (D : LocalPhaseData E chi psi) :
    D.endpointFactor ≠ 0 := by
  cases D with
  | endpoint _ Gamma => exact deltaFinite_ne_zero chi psi Gamma
  | stationary => simp [endpointFactor]

theorem admissibleFactor_ne_zero (D : LocalPhaseData E chi psi) :
    D.admissibleFactor ≠ 0 := by
  cases D with
  | endpoint => simp [admissibleFactor]
  | stationary S => exact S.admissibleFactor_ne_zero

theorem elementaryFactor_ne_zero (D : LocalPhaseData E chi psi) :
    D.elementaryFactor ≠ 0 := by
  cases D with
  | endpoint => simp [elementaryFactor]
  | stationary S => exact S.elementaryFactor_ne_zero

theorem criticalFactor_ne_zero (D : LocalPhaseData E chi psi) :
    D.criticalFactor ≠ 0 := by
  cases D with
  | endpoint => simp [criticalFactor]
  | stationary S => exact S.criticalFactor_ne_zero

/-- Exact local factorization, with endpoints and stationary conductors kept
as different constructors. -/
theorem deltaFinite_eq_completeFactor (D : LocalPhaseData E chi psi) :
    deltaFinite chi psi D.gamma = D.completeFactor := by
  cases D with
  | endpoint h Gamma =>
      simp [gamma, completeFactor, endpointFactor, admissibleFactor,
        elementaryFactor, criticalFactor]
  | stationary S =>
      simpa [gamma, completeFactor, endpointFactor, admissibleFactor,
        elementaryFactor, criticalFactor,
        LocalLamprechtPhaseData.completeFactor,
        LocalLamprechtPhaseData.stationaryFactor, mul_assoc] using
        S.deltaFinite_eq_completeFactor

end LocalPhaseData

/-! ## The complete First-Main quotient -/

/-- Exact local packages for all three kinds of local constants in the
First-Main error quotient.  In particular the identity norm character uses an
endpoint constructor and therefore has no stationary representative. -/
structure FirstMainPhaseData
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (chiF : ContinuousQuasiChar F) (psiF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K chiF psiF) where
  extension : LocalPhaseData K
    data.extensionQuasiChar data.extensionAddChar
  normCharacter : ∀ mu : NormCharacter F K,
    LocalPhaseData F (data.normCharacterData mu) data.baseAddChar
  twist : ∀ mu : NormCharacter F K,
    LocalPhaseData F (data.twistData mu) data.baseAddChar

/-- The four separately assembled quotients in the error term. -/
structure FirstMainPhaseFactors where
  endpoint : ℂ
  admissibleCharacter : ℂ
  elementary : ℂ
  critical : ℂ

namespace FirstMainPhaseFactors

/-- Reassemble the four named factor quotients. -/
def assembled (P : FirstMainPhaseFactors) : ℂ :=
  P.endpoint * P.admissibleCharacter * P.elementary * P.critical

end FirstMainPhaseFactors

namespace FirstMainPhaseData

variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]
  {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
  {data : FirstMainComputationalData F K chiF psiF}

noncomputable def endpointNumerator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact D.extension.endpointFactor *
    ∏ mu : NormCharacter F K, (D.normCharacter mu).endpointFactor

noncomputable def endpointDenominator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ mu : NormCharacter F K, (D.twist mu).endpointFactor

noncomputable def admissibleNumerator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact D.extension.admissibleFactor *
    ∏ mu : NormCharacter F K, (D.normCharacter mu).admissibleFactor

noncomputable def admissibleDenominator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ mu : NormCharacter F K, (D.twist mu).admissibleFactor

noncomputable def elementaryNumerator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact D.extension.elementaryFactor *
    ∏ mu : NormCharacter F K, (D.normCharacter mu).elementaryFactor

noncomputable def elementaryDenominator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ mu : NormCharacter F K, (D.twist mu).elementaryFactor

noncomputable def criticalNumerator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact D.extension.criticalFactor *
    ∏ mu : NormCharacter F K, (D.normCharacter mu).criticalFactor

noncomputable def criticalDenominator
    (D : FirstMainPhaseData F K chiF psiF data) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ mu : NormCharacter F K, (D.twist mu).criticalFactor

theorem endpointDenominator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.endpointDenominator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Finset.prod_ne_zero_iff.mpr fun mu _ ↦
    (D.twist mu).endpointFactor_ne_zero

theorem admissibleDenominator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.admissibleDenominator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Finset.prod_ne_zero_iff.mpr fun mu _ ↦
    (D.twist mu).admissibleFactor_ne_zero

theorem elementaryDenominator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.elementaryDenominator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Finset.prod_ne_zero_iff.mpr fun mu _ ↦
    (D.twist mu).elementaryFactor_ne_zero

theorem criticalDenominator_ne_zero
    (D : FirstMainPhaseData F K chiF psiF data) :
    D.criticalDenominator ≠ 0 := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact Finset.prod_ne_zero_iff.mpr fun mu _ ↦
    (D.twist mu).criticalFactor_ne_zero

/-- The exact endpoint, character, elementary, and critical quotients obtained
before any finite-phase cancellation. -/
noncomputable def factors (D : FirstMainPhaseData F K chiF psiF data) :
    FirstMainPhaseFactors := by
  exact
    { endpoint := D.endpointNumerator / D.endpointDenominator
      admissibleCharacter :=
        D.admissibleNumerator / D.admissibleDenominator
      elementary := D.elementaryNumerator / D.elementaryDenominator
      critical := D.criticalNumerator / D.criticalDenominator }

/-- Exact reduction of the First-Main error quotient to four separately
assembled factor quotients.  This expands `errorTerm`; it neither assumes nor
proves that the error is one. -/
theorem errorTerm_eq_assembledFactors
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (D : FirstMainPhaseData F K chiF psiF data) :
    errorTerm F K DeltaF DeltaK chiF psiF = D.factors.assembled := by
  letI := Fintype.ofFinite (NormCharacter F K)
  have hextension :
      DeltaK (normQuasiChar F K chiF) (tracePullbackAddChar F K psiF) =
        D.extension.completeFactor := by
    calc
      DeltaK (normQuasiChar F K chiF) (tracePullbackAddChar F K psiF) =
          DeltaK data.extensionQuasiChar.character
            data.extensionAddChar.character := by
              rw [data.extensionQuasiChar_character,
                data.extensionAddChar_character]
      _ = deltaFinite data.extensionQuasiChar data.extensionAddChar
            D.extension.gamma :=
        hDeltaK data.extensionQuasiChar data.extensionAddChar D.extension.gamma
      _ = D.extension.completeFactor :=
        D.extension.deltaFinite_eq_completeFactor
  have hnorm : ∀ mu : NormCharacter F K,
      DeltaF mu.1 psiF = (D.normCharacter mu).completeFactor := by
    intro mu
    calc
      DeltaF mu.1 psiF =
          DeltaF (data.normCharacterData mu).character
            data.baseAddChar.character := by
              rw [data.normCharacterData_character,
                data.baseAddChar_character]
      _ = deltaFinite (data.normCharacterData mu) data.baseAddChar
            (D.normCharacter mu).gamma :=
        hDeltaF (data.normCharacterData mu) data.baseAddChar
          (D.normCharacter mu).gamma
      _ = (D.normCharacter mu).completeFactor :=
        (D.normCharacter mu).deltaFinite_eq_completeFactor
  have htwist : ∀ mu : NormCharacter F K,
      DeltaF (mu.1 * chiF) psiF = (D.twist mu).completeFactor := by
    intro mu
    calc
      DeltaF (mu.1 * chiF) psiF =
          DeltaF (data.twistData mu).character
            data.baseAddChar.character := by
              rw [data.twistData_character, data.baseAddChar_character]
      _ = deltaFinite (data.twistData mu) data.baseAddChar
            (D.twist mu).gamma :=
        hDeltaF (data.twistData mu) data.baseAddChar (D.twist mu).gamma
      _ = (D.twist mu).completeFactor :=
        (D.twist mu).deltaFinite_eq_completeFactor
  rw [errorTerm, firstMainLeftSide, firstMainRightSide, hextension]
  simp_rw [hnorm, htwist, LocalPhaseData.completeFactor,
    Finset.prod_mul_distrib]
  simp only [factors, FirstMainPhaseFactors.assembled, endpointNumerator,
    endpointDenominator, admissibleNumerator, admissibleDenominator,
    elementaryNumerator, elementaryDenominator, criticalNumerator,
    criticalDenominator]
  ring

end FirstMainPhaseData

/-- In every complete First-Main phase package, the identity norm character
is forced to be the conductor-zero endpoint.  This is derived from the
computational datum; callers do not supply it as an assembly hypothesis. -/
theorem identityNormCharacterEndpoint_of_phaseData
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    (D : FirstMainPhaseData F K chiF psiF data) :
    ∃ (h : (data.normCharacterData 1).conductor ≤ 1)
      (Gamma : AdmissibleGamma F
        (data.normCharacterData 1) data.baseAddChar),
      D.normCharacter 1 = LocalPhaseData.endpoint h Gamma := by
  have hdata : data.normCharacterData 1 = trivialQuasiCharData F := by
    apply LocalQuasiCharData.ext_character F
    rw [data.normCharacterData_character]
    ext x
    simp
  have hcond : (data.normCharacterData 1).conductor ≤ 1 := by
    rw [hdata, trivialQuasiCharData_conductor]
    omega
  cases hphase : D.normCharacter 1 with
  | endpoint h Gamma => exact ⟨h, Gamma, rfl⟩
  | stationary S =>
      have hlarge := S.conductor_gt_one
      rw [hdata, trivialQuasiCharData_conductor] at hlarge
      omega

end

end LanglandsFirstMainLemma
