import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Delta.ErrorTerm
import LanglandsFirstMainLemma.Delta.IntegralFiniteBridge

namespace LanglandsFirstMainLemma

/-!
# Canonical total local-constant function

This file turns the representative-free finite value `deltaFinite` into the
total `LocalConstantFunction` used by the exported First Main Lemma.

For a nontrivial continuous additive character, the construction uses the
canonical exact-conductor packages from `CharacterConductorExistence`,
chooses an admissible denominator, and evaluates `deltaFinite`.  The choice
of denominator is not observable, by `deltaFinite_gamma_independent`.

The value at the trivial additive character is set to zero solely to make the
function total.  None of the finite or integral realization theorems below
applies to that branch.
-/

noncomputable section

open MeasureTheory

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## The canonical nontrivial branch -/

/-- The canonical finite value attached to ordinary characters and a proof
that the additive character is nontrivial.  Exact conductor packages are the
canonical packages from `CharacterConductorExistence`; the only remaining
choice is an admissible denominator. -/
private noncomputable def canonicalDeltaFiniteValue
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1) : ℂ :=
  let χData := canonicalLocalQuasiCharData F χ
  let ψData := canonicalLocalAddCharData F ψ hψ
  let γ : AdmissibleGamma F χData ψData :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := F))
  deltaFinite χData ψData γ

/-- The internally chosen admissible denominator has no effect on the
canonical nontrivial value. -/
private theorem canonicalDeltaFiniteValue_eq_deltaFinite
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1)
    (γ : AdmissibleGamma F (canonicalLocalQuasiCharData F χ)
      (canonicalLocalAddCharData F ψ hψ)) :
    canonicalDeltaFiniteValue F χ ψ hψ =
      deltaFinite (canonicalLocalQuasiCharData F χ)
        (canonicalLocalAddCharData F ψ hψ) γ := by
  unfold canonicalDeltaFiniteValue
  exact deltaFinite_gamma_independent _ _ γ _

/-! ## The total local-constant function -/

/-- The canonical total local-constant function on `F`.

For `ψ ≠ 1`, it is the representative-free `deltaFinite` value formed from
the canonical exact conductor packages.  For `ψ = 1`, it is zero; this is
only a harmless totalizing convention. -/
noncomputable def localConstantFunction : LocalConstantFunction F := by
  classical
  exact fun χ ψ =>
    if hψ : ψ = 1 then 0
    else canonicalDeltaFiniteValue F χ ψ hψ

/-- The harmless totalizing value at the trivial additive character. -/
@[simp]
theorem localConstantFunction_apply_one (χ : ContinuousQuasiChar F) :
    localConstantFunction F χ 1 = 0 := by
  simp [localConstantFunction]

/-! ## Exact finite realization -/

/-- Exact `deltaFinite` realization for ordinary characters, their canonical
exact-conductor packages, and every admissible denominator.  In particular,
the result is independent both of the internally chosen denominator and of
the supplied proof that `ψ` is nontrivial. -/
theorem localConstantFunction_eq_deltaFinite
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1)
    (γ : AdmissibleGamma F (canonicalLocalQuasiCharData F χ)
      (canonicalLocalAddCharData F ψ hψ)) :
    localConstantFunction F χ ψ =
      deltaFinite (canonicalLocalQuasiCharData F χ)
        (canonicalLocalAddCharData F ψ hψ) γ := by
  rw [localConstantFunction, dif_neg hψ]
  exact canonicalDeltaFiniteValue_eq_deltaFinite F χ ψ hψ γ

/-- The canonical total function satisfies the computational local-constant
specification on every package of exact conductor data.

The package equalities used here are the extensionality consequences of
uniqueness of exact multiplicative and additive conductors.  Rewriting the
whole denominator-dependent statement before introducing its denominator
keeps the transport invisible; proof irrelevance identifies the remaining
nontriviality and conductor proofs. -/
theorem localConstantFunction_isDeltaFinite :
    IsDeltaFiniteLocalConstant (localConstantFunction F) := by
  intro χ ψ
  have hχ := canonicalLocalQuasiCharData_eq F χ
  have hψ := canonicalLocalAddCharData_eq F ψ
  rw [← hχ, ← hψ]
  intro γ
  exact localConstantFunction_eq_deltaFinite F χ.character ψ.character
    ψ.character_ne_one γ

/-! ## Exact integral realization -/

/-- Exact Haar-integral realization for ordinary characters, their canonical
exact-conductor packages, any positive left Haar measure on `U_F^0`, and
every admissible denominator.  This is only the existing integral--finite
bridge, applied after the finite realization above. -/
theorem localConstantFunction_eq_deltaIntegral
    (μ : Measure (unitFiltration F 0)) [μ.IsHaarMeasure]
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1)
    (γ : IntegralAdmissibleGamma F (canonicalLocalQuasiCharData F χ)
      (canonicalLocalAddCharData F ψ hψ)) :
    localConstantFunction F χ ψ =
      deltaIntegral μ (canonicalLocalQuasiCharData F χ)
        (canonicalLocalAddCharData F ψ hψ) γ := by
  calc
    localConstantFunction F χ ψ =
        deltaFinite (canonicalLocalQuasiCharData F χ)
          (canonicalLocalAddCharData F ψ hψ) γ :=
      localConstantFunction_eq_deltaFinite F χ ψ hψ γ
    _ = deltaIntegral μ (canonicalLocalQuasiCharData F χ)
          (canonicalLocalAddCharData F ψ hψ) γ :=
      (deltaIntegral_eq_deltaFinite μ _ _ γ).symm

/-! ## Short exported name -/

/-- The short name retained for the blueprint and the final exported First
Main Lemma.  It is definitionally the canonical total function above. -/
noncomputable abbrev localConstant : LocalConstantFunction F :=
  localConstantFunction F

/-- Computational specification under the short exported name. -/
theorem localConstant_isDeltaFinite :
    IsDeltaFiniteLocalConstant (localConstant F) :=
  localConstantFunction_isDeltaFinite F

/-- Finite realization under the short exported name. -/
theorem localConstant_eq_deltaFinite
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1)
    (γ : AdmissibleGamma F (canonicalLocalQuasiCharData F χ)
      (canonicalLocalAddCharData F ψ hψ)) :
    localConstant F χ ψ =
      deltaFinite (canonicalLocalQuasiCharData F χ)
        (canonicalLocalAddCharData F ψ hψ) γ :=
  localConstantFunction_eq_deltaFinite F χ ψ hψ γ

/-- Integral realization under the short exported name. -/
theorem localConstant_eq_deltaIntegral
    (μ : Measure (unitFiltration F 0)) [μ.IsHaarMeasure]
    (χ : ContinuousQuasiChar F) (ψ : ContinuousAddChar F)
    (hψ : ψ ≠ 1)
    (γ : IntegralAdmissibleGamma F (canonicalLocalQuasiCharData F χ)
      (canonicalLocalAddCharData F ψ hψ)) :
    localConstant F χ ψ =
      deltaIntegral μ (canonicalLocalQuasiCharData F χ)
        (canonicalLocalAddCharData F ψ hψ) γ :=
  localConstantFunction_eq_deltaIntegral F μ χ ψ hψ γ

end

end LanglandsFirstMainLemma
