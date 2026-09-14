import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsFirstMainLemma.Delta.ResidueFormula
import LanglandsFirstMainLemma.FiniteField.HasseDavenportLift
import LanglandsFirstMainLemma.FiniteField.HasseFunctionLift
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Parameters.HighUnramifiedStable
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Delta.ErrorTerm
import Mathlib.RingTheory.Localization.NormTrace

/-!
# The unramified cyclic-prime case

This file proves Proposition `prop:unramified-new` of the authoritative
manuscript.  The proof keeps the exact conductor packages visible.  In the
higher-conductor range the common stationary numerator is first identified
in its lattice quotient; only then is an integral representative chosen for
Lamprecht's formula.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Pointwise
open Polynomial IsLocalRing

attribute [local instance] Ideal.Quotient.field

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The norm pullback, with the exact conductor preserved in the
unramified case. -/
private def unramifiedQuasiCharData
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) : LocalQuasiCharData K where
  character := chi.character.compNorm
  conductor := chi.conductor
  isConductor :=
    (unramified_multiplicativeConductor_compNorm F K hunr
      chi.character chi.conductor).2 chi.isConductor

/-- The trace pullback, with the exact additive conductor preserved in the
unramified case. -/
private def unramifiedAddCharData
    (hunr : ramificationIndex F K = 1)
    (psi : LocalAddCharData F) : LocalAddCharData K where
  character := psi.character.compTrace
  conductor := psi.conductor
  isConductor :=
    (unramified_additiveConductor_compTrace F K hunr
      psi.character psi.conductor).2 psi.isConductor

@[simp] private theorem unramifiedQuasiCharData_character
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) :
    (unramifiedQuasiCharData F K hunr chi).character =
      chi.character.compNorm := rfl

@[simp] private theorem unramifiedQuasiCharData_conductor
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) :
    (unramifiedQuasiCharData F K hunr chi).conductor = chi.conductor := rfl

@[simp] private theorem unramifiedAddCharData_character
    (hunr : ramificationIndex F K = 1)
    (psi : LocalAddCharData F) :
    (unramifiedAddCharData F K hunr psi).character =
      psi.character.compTrace := rfl

@[simp] private theorem unramifiedAddCharData_conductor
    (hunr : ramificationIndex F K = 1)
    (psi : LocalAddCharData F) :
    (unramifiedAddCharData F K hunr psi).conductor = psi.conductor := rfl

/-- Exact conductor-zero data for a norm character.  The trivial norm
character is deliberately included. -/
private def unramifiedNormCharacterData
    (hunr : ramificationIndex F K = 1) (mu : NormCharacter F K) :
    LocalQuasiCharData F where
  character := mu.1
  conductor := 0
  isConductor := unramifiedNormCharacter_conductor F K hunr mu

/-- Twisting by an unramified norm character preserves the exact conductor,
including at conductor zero. -/
@[reducible] private def unramifiedTwistData
    (hunr : ramificationIndex F K = 1) (chi : LocalQuasiCharData F)
    (mu : NormCharacter F K) : LocalQuasiCharData F where
  character := mu.1 * chi.character
  conductor := chi.conductor
  isConductor := by
    by_cases hm : chi.conductor = 0
    · rw [hm]
      apply IsMultiplicativeConductor.of_zero
      exact QuasiCharTrivialOnUnitFiltration.mul F
        (unramifiedNormCharacter_conductor F K hunr mu).trivial
        (chi.isConductor.trivialOnUnitFiltration_iff.2 (by simpa [hm]))
    · exact (unramifiedNormCharacter_conductor F K hunr mu).mul_of_lt
        chi.isConductor (Nat.pos_of_ne_zero hm)

@[simp] private theorem unramifiedNormCharacterData_character
    (hunr : ramificationIndex F K = 1) (mu : NormCharacter F K) :
    (unramifiedNormCharacterData F K hunr mu).character = mu.1 := rfl

@[simp] private theorem unramifiedNormCharacterData_conductor
    (hunr : ramificationIndex F K = 1) (mu : NormCharacter F K) :
    (unramifiedNormCharacterData F K hunr mu).conductor = 0 := rfl

@[simp] private theorem unramifiedTwistData_character
    (hunr : ramificationIndex F K = 1) (chi : LocalQuasiCharData F)
    (mu : NormCharacter F K) :
    (unramifiedTwistData F K hunr chi mu).character =
      mu.1 * chi.character := rfl

@[simp] private theorem unramifiedTwistData_conductor
    (hunr : ramificationIndex F K = 1) (chi : LocalQuasiCharData F)
    (mu : NormCharacter F K) :
    (unramifiedTwistData F K hunr chi mu).conductor = chi.conductor := rfl

/-- The canonical denominator `pi^(m+n)` used simultaneously downstairs
and upstairs. -/
private def uniformizerGamma
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    AdmissibleGamma F chi psi := by
  refine ⟨pi ^ ((chi.conductor : ℤ) + psi.conductor), ?_⟩
  change ord F ((Units.coeHom F)
    (pi ^ ((chi.conductor : ℤ) + psi.conductor))) = _
  rw [(Units.coeHom F).map_zpow, ord_zpow]
  change ((chi.conductor : ℤ) + psi.conductor) • ord F (pi : F) = _
  rw [ord_uniformizer F hpi]
  generalize ((chi.conductor : ℤ) + psi.conductor) = a
  cases a with
  | ofNat n => simp
  | negSucc n =>
      rw [negSucc_zsmul]
      have h : (n + 1) • (1 : WithTop ℤ) =
          (((n + 1) • (1 : ℤ) : ℤ) : WithTop ℤ) :=
        (WithTop.coe_nsmul (1 : ℤ) (n + 1)).symm
      rw [h, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr
      rw [Int.negSucc_eq]
      simp

/-- The mapped canonical denominator is admissible upstairs. -/
private def unramifiedUniformizerGamma
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    AdmissibleGamma K (unramifiedQuasiCharData F K hunr chi)
      (unramifiedAddCharData F K hunr psi) := by
  let gammaF := uniformizerGamma F chi psi pi hpi
  exact ⟨Units.map (algebraMap F K) (gammaF : Fˣ),
    highParameter_unramified_commonDenominator F K chi
      (unramifiedQuasiCharData F K hunr chi) psi
      (unramifiedAddCharData F K hunr psi) rfl rfl hunr
      (gammaF : Fˣ) gammaF.property⟩

@[simp] private theorem unramifiedUniformizerGamma_coe
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    (unramifiedUniformizerGamma F K hunr chi psi pi hpi : Kˣ) =
      Units.map (algebraMap F K) (uniformizerGamma F chi psi pi hpi : Fˣ) := rfl

@[simp] private theorem uniformizerGamma_coe
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    (uniformizerGamma F chi psi pi hpi : Fˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor) := rfl

/-- An unramified twist changes only the denominator character factor.  The
finite unit sum is termwise unchanged because every norm character is
trivial on `U_F^0`. -/
private theorem deltaFinite_unramifiedTwist
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (mu : NormCharacter F K)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    deltaFinite (unramifiedTwistData F K hunr chi mu) psi
        (uniformizerGamma F (unramifiedTwistData F K hunr chi mu)
          psi pi hpi) =
      ((mu.1 pi : ℂˣ) : ℂ) ^ ((chi.conductor : ℤ) + psi.conductor) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) := by
  let chiTw := unramifiedTwistData F K hunr chi mu
  let gamma := uniformizerGamma F chi psi pi hpi
  let gammaTw := uniformizerGamma F chiTw psi pi hpi
  have hsum : finiteGaussSum chiTw psi gammaTw =
      finiteGaussSum chi psi gamma := by
    letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
    change (∑ z : UnitFiltrationQuotient F 0 chi.conductor
        (Nat.zero_le chi.conductor), finiteGaussSummand chiTw psi gammaTw z) =
      ∑ z : UnitFiltrationQuotient F 0 chi.conductor
        (Nat.zero_le chi.conductor), finiteGaussSummand chi psi gamma z
    apply Finset.sum_congr rfl
    intro z _hz
    obtain ⟨u, rfl⟩ :=
      unitFiltrationQuotientMk_surjective F (Nat.zero_le chi.conductor) z
    rw [finiteGaussSummand_mk, finiteGaussSummand_mk]
    have hmu : mu.1 (u : Fˣ) = 1 :=
      (unramifiedNormCharacter_conductor F K hunr mu).trivial u u.property
    simp only [finiteGaussSummandRepresentative, chiTw,
      unramifiedTwistData_character, ContinuousQuasiChar.mul_apply, hmu,
      one_mul]
    rfl
  rw [deltaFinite, deltaFinite, hsum]
  simp only [gammaTw, gamma, uniformizerGamma_coe,
    unramifiedTwistData_character, ContinuousQuasiChar.mul_apply, map_zpow]
  simp only [Units.val_mul, mul_zpow, add_comm]
  have hcoe := (Units.coeHom ℂ).map_zpow (mu.1 pi)
    (psi.conductor + (chi.conductor : ℤ))
  change (((mu.1 pi) ^ (psi.conductor + (chi.conductor : ℤ)) : ℂˣ) : ℂ) =
    ((mu.1 pi : ℂˣ) : ℂ) ^
      (psi.conductor + (chi.conductor : ℤ)) at hcoe
  rw [hcoe]
  ring

/-- The conductor-zero factor attached to a norm character is its
uniformizer value to the additive-conductor exponent. -/
private theorem deltaFinite_normCharacter
    (hunr : ramificationIndex F K = 1)
    (psi : LocalAddCharData F) (mu : NormCharacter F K)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    deltaFinite (unramifiedNormCharacterData F K hunr mu) psi
        (uniformizerGamma F (unramifiedNormCharacterData F K hunr mu)
          psi pi hpi) =
      ((mu.1 pi : ℂˣ) : ℂ) ^ psi.conductor := by
  rw [deltaFinite_conductor_zero F
    (unramifiedNormCharacterData F K hunr mu) rfl]
  simp only [uniformizerGamma_coe, unramifiedNormCharacterData_conductor,
    Int.ofNat_eq_coe, Nat.cast_zero, zero_add, map_zpow]
  exact (Units.coeHom ℂ).map_zpow (mu.1 pi) psi.conductor

/-! ## The signed power formula: conductors zero and one -/

/-- The signed power formula at conductor zero.  This branch includes the
globally trivial quasi-character. -/
private theorem deltaFinite_unramifiedPower_zero
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hm : chi.conductor = 0) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) ^
          Module.finrank F K := by
  rw [deltaFinite_conductor_zero K
      (unramifiedQuasiCharData F K hunr chi) (by simpa [hm]),
    deltaFinite_conductor_zero F chi hm]
  let gamma := (uniformizerGamma F chi psi pi hpi : Fˣ)
  have hnorm : Units.map (Algebra.norm F)
      (Units.map (algebraMap F K).toMonoidHom gamma) =
      gamma ^ Module.finrank F K := by
    ext
    simp [norm_algebraMap]
  simp only [hm, zero_mul, pow_zero, one_mul]
  change (((chi.character.compNorm)
      (Units.map (algebraMap F K).toMonoidHom gamma) : ℂˣ) : ℂ) =
    (((chi.character gamma : ℂˣ) : ℂ) ^ Module.finrank F K)
  rw [ContinuousQuasiChar.compNorm_apply, hnorm, map_pow]
  exact (Units.coeHom ℂ).map_pow (chi.character gamma)
    (Module.finrank F K)

/-- Reduction of the norm pullback is the finite-field norm pullback.  The
norm points from `k_K` down to `k_F`. -/
private theorem residualMulChar_unramified
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (hm : chi.conductor = 1) :
    residualMulChar K (unramifiedQuasiCharData F K hunr chi) =
      normMulChar (ResidueField F) (ResidueField K)
        (residualMulChar F chi) := by
  ext x
  obtain ⟨u, hu⟩ := residueUnits_surjective K x
  subst x
  rw [residualMulChar_residueUnits K
    (unramifiedQuasiCharData F K hunr chi) (by simp [hm]),
    normMulChar_apply]
  have hnorm := congrArg Units.val
    (unramified_residue_norm_units F K hunr u)
  change
    (((unramifiedQuasiCharData F K hunr chi).character (u : Kˣ) : ℂˣ) : ℂ) =
      residualMulChar F chi
        (residueNorm (ResidueField F) (ResidueField K)
          ((residueUnits K u : (ResidueField K)ˣ) : ResidueField K))
  rw [show residueNorm (ResidueField F) (ResidueField K)
      ((residueUnits K u : (ResidueField K)ˣ) : ResidueField K) =
        ((residueUnits F (unramifiedNormUnitGroup F K u) :
          (ResidueField F)ˣ) : ResidueField F) by exact hnorm.symm,
    residualMulChar_residueUnits F chi (by omega)]
  change (((chi.character.compNorm) (u : Kˣ) : ℂˣ) : ℂ) =
    ((chi.character
      (unramifiedNormUnitGroup F K u : unitGroup F) : ℂˣ) : ℂ)
  rw [ContinuousQuasiChar.compNorm_apply,
    coe_unramifiedNormUnitGroup F K u]

/-- The canonical denominator has the order required by the conductor-one
residue formula. -/
private theorem uniformizerGamma_order_one
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hm : chi.conductor = 1) :
    ord F ((uniformizerGamma F chi psi pi hpi : Fˣ) : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ) := by
  rw [(uniformizerGamma F chi psi pi hpi).property]
  norm_cast
  omega

private theorem unramifiedUniformizerGamma_order_one
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hm : chi.conductor = 1) :
    ord K ((unramifiedUniformizerGamma F K hunr chi psi pi hpi : Kˣ) : K) =
      (((unramifiedAddCharData F K hunr psi).conductor + 1 : ℤ) :
        WithTop ℤ) := by
  rw [(unramifiedUniformizerGamma F K hunr chi psi pi hpi).property]
  norm_cast
  simp only [unramifiedQuasiCharData_conductor,
    unramifiedAddCharData_conductor]
  omega

/-- Reduction of the trace pullback is the finite-field trace pullback.  The
trace points from `k_K` down to `k_F`. -/
private theorem residualAddChar_unramified
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hm : chi.conductor = 1) :
    residualAddChar K (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi : Kˣ)
        (unramifiedUniformizerGamma_order_one F K hunr chi psi pi hpi hm) =
      traceAddChar (ResidueField F) (ResidueField K)
        (residualAddChar F psi (uniformizerGamma F chi psi pi hpi : Fˣ)
          (uniformizerGamma_order_one F chi psi pi hpi hm)) := by
  let gammaF := (uniformizerGamma F chi psi pi hpi : Fˣ)
  let gammaK :=
    (unramifiedUniformizerGamma F K hunr chi psi pi hpi : Kˣ)
  let hgammaF := uniformizerGamma_order_one F chi psi pi hpi hm
  let hgammaK :=
    unramifiedUniformizerGamma_order_one F K hunr chi psi pi hpi hm
  ext x
  obtain ⟨z, rfl⟩ := residueMap_surjective K x
  have hzK : (z : K) ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2 z.property
  have hzF : (integralTrace F K z : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (integralTrace F K z).property
  change residualAddChar K (unramifiedAddCharData F K hunr psi)
      gammaK hgammaK (residueMap K z) =
    residualAddChar F psi gammaF hgammaF
      (residueTrace (ResidueField F) (ResidueField K) (residueMap K z))
  calc
    residualAddChar K (unramifiedAddCharData F K hunr psi)
        gammaK hgammaK (residueMap K z) =
        (((unramifiedAddCharData F K hunr psi).character
          ((z : K) / (gammaK : K)) : ℂˣ) : ℂ) := by
      rw [← reduce_mk K z]
      exact residualAddChar_integral_lift K
        (unramifiedAddCharData F K hunr psi) gammaK hgammaK (z : K) hzK
    _ = ((psi.character
        ((integralTrace F K z : F) / (gammaF : F)) : ℂˣ) : ℂ) := by
      change
        (((psi.character.compTrace)
          ((z : K) / (gammaK : K)) : ℂˣ) : ℂ) =
          ((psi.character
            ((integralTrace F K z : F) / (gammaF : F)) : ℂˣ) : ℂ)
      rw [ContinuousAddChar.compTrace_apply]
      apply congrArg Units.val
      apply congrArg psi.character
      rw [show (gammaK : K) = algebraMap F K (gammaF : F) by rfl,
        coe_integralTrace]
      change trace F K ((z : K) /
          algebraMap F K (gammaF : F)) =
        trace F K (z : K) / (gammaF : F)
      rw [div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def,
        map_smul, Algebra.smul_def, div_eq_mul_inv]
      simp [mul_comm]
    _ = residualAddChar F psi gammaF hgammaF
        (residueMap F (integralTrace F K z)) := by
      rw [← reduce_mk F (integralTrace F K z)]
      exact (residualAddChar_integral_lift F psi gammaF hgammaF
        (integralTrace F K z : F) hzF).symm
    _ = residualAddChar F psi gammaF hgammaF
        (residueTrace (ResidueField F) (ResidueField K)
          (residueMap K z)) := by
      rw [residue_trace F K hunr z]

/-- The signed power formula at exact conductor one.  Hasse--Davenport
lifting has no extra sign in the project's Langlands normalization; the
displayed sign comes solely from the two conductor-one Delta formulas. -/
private theorem deltaFinite_unramifiedPower_one
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hm : chi.conductor = 1) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) ^
          Module.finrank F K := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : Fintype (ResidueField K) := residueFieldFintype K
  let chiK := unramifiedQuasiCharData F K hunr chi
  let psiK := unramifiedAddCharData F K hunr psi
  let GammaF := uniformizerGamma F chi psi pi hpi
  let GammaK := unramifiedUniformizerGamma F K hunr chi psi pi hpi
  let hGammaF := uniformizerGamma_order_one F chi psi pi hpi hm
  let hGammaK :=
    unramifiedUniformizerGamma_order_one F K hunr chi psi pi hpi hm
  let tauF := langlandsGaussSum (residualMulChar F chi)
    (residualAddChar F psi (GammaF : Fˣ) hGammaF)
  let tauK := langlandsGaussSum (residualMulChar K chiK)
    (residualAddChar K psiK (GammaK : Kˣ) hGammaK)
  have hpsiBar : residualAddChar F psi (GammaF : Fˣ) hGammaF ≠ 1 :=
    residualAddChar_ne_one F psi (GammaF : Fˣ) hGammaF
  have htau : tauK = tauF ^ Module.finrank F K := by
    change langlandsGaussSum (residualMulChar K chiK)
        (residualAddChar K psiK (GammaK : Kˣ) hGammaK) = _
    rw [residualMulChar_unramified F K hunr chi hm,
      residualAddChar_unramified F K hunr chi psi pi hpi hm,
      hasseDavenportLift (residualMulChar F chi)
        (residualAddChar F psi (GammaF : Fˣ) hGammaF) hpsiBar,
      unramified_residue_degree F K hunr]
  have hphase : phase tauK = phase tauF ^ Module.finrank F K := by
    rw [htau, phase_pow]
  let gamma := (GammaF : Fˣ)
  have hnorm : Units.map (Algebra.norm F)
      (Units.map (algebraMap F K).toMonoidHom gamma) =
      gamma ^ Module.finrank F K := by
    ext
    simp
  have hchar :
      (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ)) =
        (((chi.character gamma : ℂˣ) : ℂ) ^ Module.finrank F K) := by
    change (((chi.character.compNorm)
      (Units.map (algebraMap F K).toMonoidHom gamma) : ℂˣ) : ℂ) = _
    rw [ContinuousQuasiChar.compNorm_apply, hnorm, map_pow]
    exact (Units.coeHom ℂ).map_pow (chi.character gamma)
      (Module.finrank F K)
  rw [deltaFinite_conductor_one K chiK (by simpa [chiK, hm]),
    deltaFinite_conductor_one F chi hm]
  change -((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ) * phase tauK =
    (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
      (-((chi.character gamma : ℂˣ) : ℂ) * phase tauF) ^
        Module.finrank F K
  rw [hchar, hphase]
  simp only [hm, one_mul]
  have hell : 0 < Module.finrank F K := Module.finrank_pos
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hell.ne'
  rw [hr]
  simp only [Nat.succ_sub_one]
  rcases neg_one_pow_eq_or ℂ r with hneg | hneg
  · simp [pow_succ, neg_pow, mul_pow, hneg]
    ring
  · simp [pow_succ, neg_pow, mul_pow, hneg]
    ring

/-! ## The signed power formula: higher conductor -/

/-- The product of the denominator value and Lamprecht's elementary factor
is compatible with unramified norm/trace pullback. -/
private theorem lamprechtBaseFactor_unramified
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (beta : Fˣ) :
    (((unramifiedQuasiCharData F K hunr chi).character
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi : Kˣ) : ℂˣ) : ℂ) *
      lamprechtElementaryFactor K
        (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi)
        (Units.map (algebraMap F K).toMonoidHom beta) =
      (((chi.character (uniformizerGamma F chi psi pi hpi : Fˣ) : ℂˣ) : ℂ) *
        lamprechtElementaryFactor F chi psi
          (uniformizerGamma F chi psi pi hpi) beta) ^
        Module.finrank F K := by
  let GammaF := uniformizerGamma F chi psi pi hpi
  let GammaK := unramifiedUniformizerGamma F K hunr chi psi pi hpi
  let betaK := Units.map (algebraMap F K).toMonoidHom beta
  have hnormGamma : Units.map (Algebra.norm F) (GammaK : Kˣ) =
      (GammaF : Fˣ) ^ Module.finrank F K := by
    change Units.map (Algebra.norm F)
      (Units.map (algebraMap F K).toMonoidHom (GammaF : Fˣ)) = _
    ext
    simp
  have hnormBeta : Units.map (Algebra.norm F) betaK =
      beta ^ Module.finrank F K := by
    ext
    simp [betaK, norm_algebraMap]
  unfold lamprechtElementaryFactor
  change
    (((chi.character.compNorm) (GammaK : Kˣ) : ℂˣ) : ℂ) *
      ((((psi.character.compTrace)
          ((betaK : K) / ((GammaK : Kˣ) : K)) : ℂˣ) : ℂ) *
        ((((chi.character.compNorm) betaK : ℂˣ) : ℂ)⁻¹)) = _
  rw [ContinuousQuasiChar.compNorm_apply,
    ContinuousQuasiChar.compNorm_apply, hnormGamma, hnormBeta,
    map_pow, map_pow]
  have htrace : trace F K ((betaK : K) / ((GammaK : Kˣ) : K)) =
      Module.finrank F K • ((beta : F) / ((GammaF : Fˣ) : F)) := by
    change trace F K
        (algebraMap F K (beta : F) /
          algebraMap F K ((GammaF : Fˣ) : F)) = _
    rw [← map_div₀, trace_algebraMap]
  rw [ContinuousAddChar.compTrace_apply, htrace]
  have hpsiPower := congrArg Units.val
    (AddChar.map_nsmul_eq_pow psi.character.toAddChar
      (Module.finrank F K) ((beta : F) / ((GammaF : Fˣ) : F)))
  change
    (((psi.character
      (Module.finrank F K • ((beta : F) / ((GammaF : Fˣ) : F))) : ℂˣ) : ℂ)) =
      (((psi.character ((beta : F) / ((GammaF : Fˣ) : F)) : ℂˣ) : ℂ) ^
        Module.finrank F K) at hpsiPower
  rw [hpsiPower]
  simp only [Units.val_pow_eq_pow_val, inv_pow, mul_pow]
  ring

set_option maxHeartbeats 4000000 in
/-- Choose a common integral representative only after the upstairs and
downstairs stationary classes have been identified in their literal
quotients. -/
private theorem exists_unramifiedLamprechtRepresentatives
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (GammaF : AdmissibleGamma F chiF psiF) :
    let hK := highParameter_unramified_sourceDecomposition F K chiF chiK
      hF hchi hunr
    let GammaK : AdmissibleGamma K chiK psiK :=
      ⟨Units.map (algebraMap F K) (GammaF : Fˣ),
        highParameter_unramified_commonDenominator F K chiF chiK psiF psiK
          hchi hpsi hunr (GammaF : Fˣ) GammaF.property⟩
    ∃ (cF : lattice F ((chiF.conductor : ℤ) - (chiF.conductor : ℤ)))
      (cK : lattice K ((chiK.conductor : ℤ) - (chiK.conductor : ℤ))),
      (cK : K) = algebraMap F K (cF : F) ∧
      latticeQuotientMk F
          (sub_le_sub_left
            (stationaryDepthOfConductorDecomposition F chiF hF).int_le_conductor
            (chiF.conductor : ℤ)) cF =
        stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
          (stationaryDepthOfConductorDecomposition F chiF hF)
          GammaF GammaF.property ∧
      latticeQuotientMk K
          (sub_le_sub_left
            (stationaryDepthOfConductorDecomposition K chiK hK).int_le_conductor
            (chiK.conductor : ℤ)) cK =
        stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
          (stationaryDepthOfConductorDecomposition K chiK hK)
          GammaK GammaK.property := by
  dsimp only
  let hK := highParameter_unramified_sourceDecomposition F K chiF chiK
    hF hchi hunr
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) (GammaF : Fˣ),
      highParameter_unramified_commonDenominator F K chiF chiK psiF psiK
        hchi hpsi hunr (GammaF : Fˣ) GammaF.property⟩
  obtain ⟨xF, hxF⟩ := latticeQuotientMk_surjective F (by omega)
    (stationaryCoefficientClass F chiF psiF hF
      (GammaF : Fˣ) GammaF.property)
  let xK : lattice K 0 :=
    ⟨algebraMap F K (xF : F), by
      rw [mem_lattice, ord_algebraMap, hunr, one_nsmul]
      exact xF.property⟩
  have hxK : latticeQuotientMk K (Int.ofNat_zero_le d) xK =
      stationaryCoefficientClass K chiK psiK hK
        (GammaK : Kˣ) GammaK.property := by
    have hhigh := highParameter_unramified F K chiF chiK psiF psiK hF
      hchi hpsi hunr (GammaF : Fˣ) GammaF.property
    calc
      latticeQuotientMk K (Int.ofNat_zero_le d) xK =
          denominatorScaledAlgebraMap F K d d (by simp [hunr])
            (GammaF : Fˣ) (Units.map (algebraMap F K) (GammaF : Fˣ))
            (by simp [normPolynomialDenominatorRatio])
            (latticeQuotientMk F (Int.ofNat_zero_le d) xF) := by
        symm
        simpa [xK] using denominatorScaledAlgebraMap_common_mk F K d d
          (by simp [hunr]) (GammaF : Fˣ) xF
      _ = denominatorScaledAlgebraMap F K d d (by simp [hunr])
            (GammaF : Fˣ) (Units.map (algebraMap F K) (GammaF : Fˣ))
            (by simp [normPolynomialDenominatorRatio])
            (stationaryCoefficientClass F chiF psiF hF
              (GammaF : Fˣ) GammaF.property) := by rw [hxF]
      _ = stationaryCoefficientClass K chiK psiK hK
            (GammaK : Kˣ) GammaK.property := by
        exact hhigh.symm
  let cF : lattice F ((chiF.conductor : ℤ) - (chiF.conductor : ℤ)) :=
    ⟨xF, by simpa using xF.property⟩
  let cK : lattice K ((chiK.conductor : ℤ) - (chiK.conductor : ℤ)) :=
    ⟨xK, by simpa using xK.property⟩
  refine ⟨cF, cK, ?_, ?_, ?_⟩
  · rfl
  · have h := congrArg
        (stationaryCoefficientLamprechtEquivAtConductor F hF) hxF
    rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
      stationaryCoefficientClass_toLamprecht] at h
    simpa [cF] using h
  · have h := congrArg
        (stationaryCoefficientLamprechtEquivAtConductor K hK) hxK
    rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
      stationaryCoefficientClass_toLamprecht] at h
    simpa [cK] using h

/-! ### Reduction of the unordered second norm coefficient -/

/-- The second coefficient of a monic polynomial commutes with scalar
extension. -/
private theorem secondCoeff_map_of_monic
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) {p : R[X]} (hp : p.Monic) :
    secondCoeff (p.map f) = f (secondCoeff p) := by
  by_cases htwo : 2 ≤ p.natDegree
  · rw [secondCoeff_eq_coeff_of_two_le p htwo,
      secondCoeff_eq_coeff_of_two_le (p.map f)
        (by simpa [hp.natDegree_map f] using htwo),
      hp.natDegree_map f, coeff_map]
  · have hlt : p.natDegree < 2 := Nat.lt_of_not_ge htwo
    rw [secondCoeff_eq_zero_of_natDegree_lt_two p hlt,
      secondCoeff_eq_zero_of_natDegree_lt_two (p.map f)
        (by simpa [hp.natDegree_map f] using hlt), map_zero]

/-- The integral second norm coefficient, defined before reduction. -/
private noncomputable def integralSecondCoeff
    (x : ringOfIntegers K) : ringOfIntegers F := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  exact secondCoeff
    (Algebra.lmul (ringOfIntegers F) (ringOfIntegers K) x).charpoly

private theorem integralSecondCoeff_eq_leftMulMatrix
    {i : Type*} [Fintype i] [DecidableEq i]
    (b : Module.Basis i (ringOfIntegers F) (ringOfIntegers K))
    (x : ringOfIntegers K) :
    integralSecondCoeff F K x =
      secondCoeff (Algebra.leftMulMatrix b x).charpoly := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  rw [integralSecondCoeff, Algebra.leftMulMatrix_apply,
    LinearMap.charpoly_toMatrix]

/-- Before reduction, the integral coefficient is the field-theoretic
unordered-pair coefficient `E_2`. -/
private theorem algebraMap_integralSecondCoeff
    (x : ringOfIntegers K) :
    algebraMap (ringOfIntegers F) F (integralSecondCoeff F K x) =
      elementarySymmetric F K 2 (x : K) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  let i := Module.Free.ChooseBasisIndex (ringOfIntegers F) (ringOfIntegers K)
  let b : Module.Basis i (ringOfIntegers F) (ringOfIntegers K) :=
    Module.Free.chooseBasis (ringOfIntegers F) (ringOfIntegers K)
  let bF : Module.Basis i F K :=
    b.localizationLocalization F (nonZeroDivisors (ringOfIntegers F)) K
  have hmat :
      (algebraMap (ringOfIntegers F) F).mapMatrix
          (Algebra.leftMulMatrix b x) =
        Algebra.leftMulMatrix bF (x : K) := by
    exact Algebra.map_leftMulMatrix_localization
      (ringOfIntegers F) (nonZeroDivisors (ringOfIntegers F)) b x
  calc
    algebraMap (ringOfIntegers F) F (integralSecondCoeff F K x) =
        secondCoeff
          ((Algebra.lmul (ringOfIntegers F) (ringOfIntegers K) x).charpoly.map
            (algebraMap (ringOfIntegers F) F)) := by
      rw [integralSecondCoeff, secondCoeff_map_of_monic
        (algebraMap (ringOfIntegers F) F)
        (LinearMap.charpoly_monic
          (Algebra.lmul (ringOfIntegers F) (ringOfIntegers K) x))]
    _ = secondCoeff
          ((Algebra.leftMulMatrix b x).charpoly.map
            (algebraMap (ringOfIntegers F) F)) := by
      rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    _ = secondCoeff
          (((algebraMap (ringOfIntegers F) F).mapMatrix
            (Algebra.leftMulMatrix b x)).charpoly) := by
      change secondCoeff
          ((Algebra.leftMulMatrix b x).charpoly.map
            (algebraMap (ringOfIntegers F) F)) =
        secondCoeff
          (((Algebra.leftMulMatrix b x).map
            (algebraMap (ringOfIntegers F) F)).charpoly)
      rw [Matrix.charpoly_map]
    _ = secondCoeff (Algebra.leftMulMatrix bF (x : K)).charpoly := by
      rw [hmat]
    _ = secondCoeff (Algebra.lmul F K (x : K)).charpoly := by
      rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    _ = elementarySymmetric F K 2 (x : K) := by
      rw [← hassePairCorrection_eq_secondCoeff_charpoly F K (x : K),
        hassePairCorrection_eq_elementarySymmetric_two F K (x : K)]

section SecondCoeffQuotient

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S] [IsLocalRing R]

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

private theorem secondCoeff_leftMulMatrix_basisQuotient
    {i : Type*} [Fintype i] [DecidableEq i]
    (b : Module.Basis i R S) (x : S) :
    secondCoeff
        (Algebra.leftMulMatrix (IsLocalRing.basisQuotient b)
          (Ideal.Quotient.mk pS x)).charpoly =
      Ideal.Quotient.mk p
        (secondCoeff (Algebra.leftMulMatrix b x).charpoly) := by
  classical
  let bq : Module.Basis i (R ⧸ p) (S ⧸ pS) :=
    IsLocalRing.basisQuotient b
  have hmat :
      Algebra.leftMulMatrix (IsLocalRing.basisQuotient b)
          (Ideal.Quotient.mk pS x) =
        (Algebra.leftMulMatrix b x).map (Ideal.Quotient.mk p) := by
    ext a c
    simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.toMatrix_apply, IsLocalRing.basisQuotient_apply,
      LinearMap.mul_apply', Matrix.map_apply, ← map_mul,
      IsLocalRing.basisQuotient_repr]
  change secondCoeff
      (Algebra.leftMulMatrix bq (Ideal.Quotient.mk pS x)).charpoly = _
  calc
    _ = secondCoeff
          (((Algebra.leftMulMatrix b x).map
            (Ideal.Quotient.mk p)).charpoly) := by
      rw [show Algebra.leftMulMatrix bq (Ideal.Quotient.mk pS x) =
          (Algebra.leftMulMatrix b x).map (Ideal.Quotient.mk p) by
        simpa [bq] using hmat]
    _ = secondCoeff
          ((Algebra.leftMulMatrix b x).charpoly.map
            (Ideal.Quotient.mk p)) := by
      rw [Matrix.charpoly_map]
    _ = Ideal.Quotient.mk p
          (secondCoeff (Algebra.leftMulMatrix b x).charpoly) := by
      rw [secondCoeff_map_of_monic]
      exact Matrix.charpoly_monic (Algebra.leftMulMatrix b x)

end SecondCoeffQuotient

/-- In an unramified extension the maximal ideal is the extended downstairs
maximal ideal. -/
private theorem unramified_map_maximalIdeal
    (hunr : ramificationIndex F K = 1) :
    Ideal.map (algebraMap (ringOfIntegers F) (ringOfIntegers K))
        (maximalIdeal (ringOfIntegers F)) =
      maximalIdeal (ringOfIntegers K) := by
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible (ringOfIntegers F)
  have hp : maximalIdeal (ringOfIntegers F) = Ideal.span {pi} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
  let piK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) pi
  have hcoe : (piK : K) = algebraMap F K (pi : F) :=
    Valuation.HasExtension.val_algebraMap pi
  have hpiunifF :
      (ValuativeRel.valuation F).IsUniformizer (pi : F) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    exact hp
  have hordK : ord K (piK : K) = 1 := by
    rw [hcoe, ord_algebraMap, hunr, one_nsmul,
      ord_uniformizer F hpiunifF]
  have hpiunifK :
      (ValuativeRel.valuation K).IsUniformizer (piK : K) :=
    (ord_eq_one_iff_isUniformizer K (piK : K)).mp hordK
  have hq : maximalIdeal (ringOfIntegers K) = Ideal.span {piK} :=
    Valuation.IsUniformizer.is_generator hpiunifK
  rw [hp, Ideal.map_span, Set.image_singleton, ← hq]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 10000000 in
private theorem residue_integralSecondCoeff_of_map_maximalIdeal
    (hpq : Ideal.map
        (algebraMap (ringOfIntegers F) (ringOfIntegers K))
        (maximalIdeal (ringOfIntegers F)) =
      maximalIdeal (ringOfIntegers K))
    (x : ringOfIntegers K) :
    residueMap F (integralSecondCoeff F K x) =
      hassePairCorrection (ResidueField F) (ResidueField K)
        (residueMap K x) := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : Module.Free (ringOfIntegers F) (ringOfIntegers K) :=
    Module.free_of_finite_type_torsion_free'
  let p := maximalIdeal (ringOfIntegers F)
  let q := maximalIdeal (ringOfIntegers K)
  let pK := Ideal.map
    (algebraMap (ringOfIntegers F) (ringOfIntegers K)) p
  change Ideal.Quotient.mk p (integralSecondCoeff F K x) =
    hassePairCorrection ((ringOfIntegers F) ⧸ p)
      ((ringOfIntegers K) ⧸ q) (Ideal.Quotient.mk q x)
  change pK = q at hpq
  letI : pK.IsMaximal := hpq ▸ maximalIdeal.isMaximal (ringOfIntegers K)
  let i := Module.Free.ChooseBasisIndex
    (ringOfIntegers F) (ringOfIntegers K)
  let b : Module.Basis i (ringOfIntegers F) (ringOfIntegers K) :=
    Module.Free.chooseBasis (ringOfIntegers F) (ringOfIntegers K)
  let bq : Module.Basis i ((ringOfIntegers F) ⧸ p)
      ((ringOfIntegers K) ⧸ pK) := IsLocalRing.basisQuotient b
  letI : Module.Free ((ringOfIntegers F) ⧸ p)
      ((ringOfIntegers K) ⧸ pK) := Module.Free.of_basis bq
  letI : Module.Finite ((ringOfIntegers F) ⧸ p)
      ((ringOfIntegers K) ⧸ pK) := Module.Finite.of_basis bq
  let e : ((ringOfIntegers K) ⧸ pK) ≃+*
      ((ringOfIntegers K) ⧸ q) := Ideal.quotEquivOfEq hpq
  have hecomm (z : (ringOfIntegers F) ⧸ p) :
      e (algebraMap ((ringOfIntegers F) ⧸ p)
          ((ringOfIntegers K) ⧸ pK) z) =
        algebraMap ((ringOfIntegers F) ⧸ p)
          ((ringOfIntegers K) ⧸ q) z := by
    refine Quotient.inductionOn z ?_
    intro z
    change e (Ideal.Quotient.mk pK
      (algebraMap (ringOfIntegers F) (ringOfIntegers K) z)) =
      Ideal.Quotient.mk q
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) z)
    exact Ideal.quotEquivOfEq_mk hpq _
  let eA : ((ringOfIntegers K) ⧸ pK) ≃ₐ[((ringOfIntegers F) ⧸ p)]
      ((ringOfIntegers K) ⧸ q) := AlgEquiv.ofRingEquiv hecomm
  have hconj (z : (ringOfIntegers K) ⧸ pK) :
      eA.toLinearEquiv.conj
          (Algebra.lmul ((ringOfIntegers F) ⧸ p)
            ((ringOfIntegers K) ⧸ pK) z) =
        Algebra.lmul ((ringOfIntegers F) ⧸ p)
          ((ringOfIntegers K) ⧸ q) (eA z) := by
    ext y
    simp [LinearEquiv.conj_apply, Algebra.coe_lmul_eq_mul]
  have hhasse (z : (ringOfIntegers K) ⧸ pK) :
      hassePairCorrection ((ringOfIntegers F) ⧸ p)
          ((ringOfIntegers K) ⧸ q) (eA z) =
        hassePairCorrection ((ringOfIntegers F) ⧸ p)
          ((ringOfIntegers K) ⧸ pK) z := by
    rw [hassePairCorrection_eq_secondCoeff_charpoly,
      hassePairCorrection_eq_secondCoeff_charpoly]
    congr 1
    rw [← hconj, LinearEquiv.charpoly_conj]
  rw [show Ideal.Quotient.mk q x = eA (Ideal.Quotient.mk pK x) by
    exact (Ideal.quotEquivOfEq_mk hpq x).symm]
  rw [hhasse]
  have hquot := secondCoeff_leftMulMatrix_basisQuotient b x
  rw [hassePairCorrection_eq_secondCoeff_charpoly]
  calc
    Ideal.Quotient.mk p (integralSecondCoeff F K x) =
        Ideal.Quotient.mk p
          (secondCoeff (Algebra.leftMulMatrix b x).charpoly) := by
      exact congrArg (Ideal.Quotient.mk p)
        (integralSecondCoeff_eq_leftMulMatrix F K b x)
    _ = secondCoeff
          (Algebra.leftMulMatrix bq (Ideal.Quotient.mk pK x)).charpoly := by
      simpa [bq, pK, p] using hquot.symm
    _ = secondCoeff
          (Algebra.lmul ((ringOfIntegers F) ⧸ p)
            ((ringOfIntegers K) ⧸ pK)
            (Ideal.Quotient.mk pK x)).charpoly := by
      exact congrArg secondCoeff
        (LinearMap.charpoly_toMatrix
          (Algebra.lmul ((ringOfIntegers F) ⧸ p)
            ((ringOfIntegers K) ⧸ pK) (Ideal.Quotient.mk pK x)) bq)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 10000000 in
/-- Reduction carries the local unordered-pair coefficient to the precise
finite-field correction used by `hasseFunctionLift`. -/
private theorem unramified_residue_integralSecondCoeff
    (hunr : ramificationIndex F K = 1)
    (x : ringOfIntegers K) :
    residueMap F (integralSecondCoeff F K x) =
      hassePairCorrection (ResidueField F) (ResidueField K)
        (residueMap K x) :=
  residue_integralSecondCoeff_of_map_maximalIdeal F K
    (unramified_map_maximalIdeal F K hunr) x

/-! ### The odd unramified norm congruence -/

private theorem localFieldInfinite
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Infinite E := by
  let f : ℤ → E := fun n => (exists_ord_eq E n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord E (f m) = (m : WithTop ℤ) :=
      (exists_ord_eq E m).choose_spec
    have hn : ord E (f n) = (n : WithTop ℤ) :=
      (exists_ord_eq E n).choose_spec
    have hcoe : (m : WithTop ℤ) = (n : WithTop ℤ) := hm.symm.trans <|
      (congrArg (ord E) hmn).trans hn
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

/-- Scaling by a downstairs scalar contributes its `j`th power to the
`j`th norm coefficient. -/
private theorem elementarySymmetric_algebraMap_mul
    [IsGalois F K] (a : F) (j : ℕ) (x : K) :
    elementarySymmetric F K j (algebraMap F K a * x) =
      a ^ j * elementarySymmetric F K j x := by
  letI : Infinite F := localFieldInfinite F
  apply (algebraMap F K).injective
  rw [map_mul, map_pow,
    algebraMap_elementarySymmetric_eq_esymm_galois,
    algebraMap_elementarySymmetric_eq_esymm_galois]
  rw [galoisConjugates, galoisConjugates]
  have hmap :
      Finset.univ.val.map
          (fun sigma : Gal(K/F) =>
            galoisConjugate sigma (algebraMap F K a * x)) =
        (Finset.univ.val.map
          (fun sigma : Gal(K/F) => galoisConjugate sigma x)).map
            ((algebraMap F K a) • ·) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro sigma _hsigma
    simp only [Function.comp_apply, galoisConjugate, map_mul]
    rw [sigma.commutes]
    simp [Algebra.smul_def]
  rw [hmap, ← Multiset.pow_smul_esymm]
  rfl

/-- In the unramified Galois case, an integral `j`th norm coefficient has
the full expected depth `j*a`. -/
private theorem unramified_elementarySymmetric_bound
    [IsGalois F K]
    (hunr : ramificationIndex F K = 1)
    (a : ℤ) {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    (j : ℕ) (hj : j ≤ Module.finrank F K) :
    (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  classical
  letI : Infinite F := localFieldInfinite F
  have hprod (s : Finset Gal(K/F)) :
      s.card • (a : WithTop ℤ) ≤ ord K (∏ sigma ∈ s, sigma x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert sigma s hs ih =>
        have hsigma : (a : WithTop ℤ) ≤ ord K (sigma x) := by
          simpa using hx
        simpa [Finset.card_insert_of_notMem, hs, succ_nsmul, add_comm] using
          add_le_add hsigma ih
  have hup : (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord K (algebraMap F K (elementarySymmetric F K j x)) := by
    rw [algebraMap_elementarySymmetric_eq_esymm_galois,
      galoisConjugates, Finset.esymm_map_val]
    apply ord_sum K
    intro s hs
    have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
    have hsbound := hprod s
    rw [hcard] at hsbound
    calc
      (((j : ℤ) * a : ℤ) : WithTop ℤ) = j • (a : WithTop ℤ) := by
        rw [← WithTop.coe_nsmul]
        congr
      _ ≤ ord K (∏ sigma ∈ s, sigma x) := hsbound
  rw [ord_algebraMap, hunr, one_nsmul] at hup
  exact hup

/-- The exact odd-depth norm expansion, modulo `p_F^(2*d+1)`.  The second
coefficient is the unordered-pair coefficient required by the Hasse lift. -/
private theorem unramified_norm_odd_congruent
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (d : ℕ) (hd : 0 < d)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : K) (hx : x ∈ lattice K 0) :
    CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (norm F K (1 + algebraMap F K (delta : F) * x))
      ((1 + (delta : F) * trace F K x) *
        (1 + (delta : F) ^ 2 * elementarySymmetric F K 2 x)) := by
  classical
  let y : K := algebraMap F K (delta : F) * x
  have hy : ((d : ℤ) : WithTop ℤ) ≤ ord K y := by
    dsimp only [y]
    rw [ord_mul, ord_algebraMap, hunr, one_nsmul, hdelta]
    rw [mem_lattice] at hx
    simpa [add_comm] using add_le_add_left hx ((d : ℤ) : WithTop ℤ)
  have hn2 : 2 ≤ Module.finrank F K :=
    PrimeCyclicExtension.degree_prime F K |>.two_le
  obtain ⟨r, hr⟩ : ∃ r, Module.finrank F K = r + 2 :=
    Nat.exists_eq_add_of_le' hn2
  let tail : F :=
    ∑ i ∈ Finset.range r, elementarySymmetric F K (i + 3) y
  have htail : tail ∈ lattice F ((2 * d + 1 : ℕ) : ℤ) := by
    rw [mem_lattice]
    apply ord_sum F
    intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hij : i + 3 ≤ Module.finrank F K := by
      rw [hr]
      omega
    have hbound := unramified_elementarySymmetric_bound
      F K hunr (d : ℤ) hy (i + 3) hij
    have hnat : 2 * d + 1 ≤ (i + 3) * d := by nlinarith
    have hcast :
        ((((2 * d + 1 : ℕ) : ℤ)) : WithTop ℤ) ≤
          (((((i + 3) * d : ℕ) : ℤ)) : WithTop ℤ) := by
      exact_mod_cast hnat
    exact hcast.trans (by simpa only [Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat] using hbound)
  have hsplit :
      (∑ j ∈ Finset.range (Module.finrank F K),
          elementarySymmetric F K (j + 1) y) =
        elementarySymmetric F K 1 y +
          elementarySymmetric F K 2 y + tail := by
    rw [hr]
    dsimp only [tail]
    rw [show r + 2 = (r + 1) + 1 by omega, Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    ring
  have hnorm :
      norm F K (1 + y) =
        1 + elementarySymmetric F K 1 y +
          elementarySymmetric F K 2 y + tail := by
    rw [norm_one_add_eq_one_add_sum_elementarySymmetric, hsplit]
    ring
  have hfirst : CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (norm F K (1 + y))
      (1 + elementarySymmetric F K 1 y +
        elementarySymmetric F K 2 y) := by
    rw [CongruentAtDepth.iff, hnorm]
    have halg :
        1 + elementarySymmetric F K 1 y +
              elementarySymmetric F K 2 y + tail -
            (1 + elementarySymmetric F K 1 y +
              elementarySymmetric F K 2 y) = tail := by ring
    rw [halg]
    exact htail
  have hcross :
      elementarySymmetric F K 1 y * elementarySymmetric F K 2 y ∈
        lattice F ((2 * d + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_mul]
    have h1 := unramified_elementarySymmetric_bound
      F K hunr (d : ℤ) hy 1 (by omega)
    have h2 := unramified_elementarySymmetric_bound
      F K hunr (d : ℤ) hy 2 hn2
    have hnat : 2 * d + 1 ≤ 1 * d + 2 * d := by omega
    have hcast :
        ((((2 * d + 1 : ℕ) : ℤ)) : WithTop ℤ) ≤
          ((((1 * d + 2 * d : ℕ) : ℤ)) : WithTop ℤ) := by
      exact_mod_cast hnat
    have hadd := add_le_add h1 h2
    rw [← WithTop.coe_add] at hadd
    exact hcast.trans (by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hadd)
  have hsecond : CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (1 + elementarySymmetric F K 1 y +
        elementarySymmetric F K 2 y)
      ((1 + elementarySymmetric F K 1 y) *
        (1 + elementarySymmetric F K 2 y)) := by
    rw [CongruentAtDepth.iff]
    have halg :
        (1 + elementarySymmetric F K 1 y +
              elementarySymmetric F K 2 y) -
            ((1 + elementarySymmetric F K 1 y) *
              (1 + elementarySymmetric F K 2 y)) =
          -(elementarySymmetric F K 1 y *
            elementarySymmetric F K 2 y) := by ring
    rw [halg, ord_neg]
    exact hcross
  have h := hfirst.trans hsecond
  simpa only [y, elementarySymmetric_algebraMap_mul,
    elementarySymmetric_one, pow_one] using h

/-- The raw odd Lamprecht value upstairs is the trace value downstairs
times the inverse quadratic correction. -/
private theorem lamprechtHasseValue_unramified_odd
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (d : ℕ)
    (hmF : chiF.conductor = 2 * d + 1)
    (hmK : chiK.conductor = 2 * d + 1)
    (hlargeF : 1 < chiF.conductor)
    (hlargeK : 1 < chiK.conductor)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K) (GammaF : Fˣ))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((d : ℤ) : WithTop ℤ))
    (hdelta : deltaK = Units.map (algebraMap F K) deltaF)
    (cF : lattice F ((chiF.conductor : ℤ) - (chiF.conductor : ℤ)))
    (hcF : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chiF d 1
            (by omega) hmF hlargeF).int_le_conductor
          (chiF.conductor : ℤ)) cF =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF d 1
          (by omega) hmF hlargeF) GammaF GammaF.property)
    (cK : lattice K ((chiK.conductor : ℤ) - (chiK.conductor : ℤ)))
    (hc : (cK : K) = algebraMap F K (cF : F))
    (x : ringOfIntegers K)
    (e2 : ringOfIntegers F)
    (he2 : (e2 : F) = elementarySymmetric F K 2 (x : K)) :
    lamprechtHasseValue K chiK psiK d hmK hlargeK GammaK
        deltaK hdeltaK cK (x : K)
        ((mem_lattice_zero_iff K).2 x.property) =
      lamprechtHasseValue F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF cF (trace F K (x : K))
          (by
            rw [← coe_integralTrace F K x]
            exact (mem_lattice_zero_iff F).2
              (integralTrace F K x).property) *
        lamprechtResidualAddChar F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF (-residueMap F e2) := by
  let hd : 0 < d := lamprechtOdd_d_pos F chiF d hmF hlargeF
  let hrF := lamprechtFormula_stationaryDepth F chiF d 1
    (by omega) hmF hlargeF
  have hxK : (x : K) ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2 x.property
  have htraceF : trace F K (x : K) ∈ lattice F 0 := by
    rw [← coe_integralTrace F K x]
    exact (mem_lattice_zero_iff F).2 (integralTrace F K x).property
  have he2F : (e2 : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 e2.property
  have hw2 : (deltaF : F) ^ 2 * (e2 : F) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
    have hdeltaMem : (deltaF : F) ∈ lattice F (d : ℤ) := by
      rw [mem_lattice, hdeltaF]
    have hdeltaSq : (deltaF : F) ^ 2 ∈
        lattice F ((d : ℤ) + (d : ℤ)) := by
      simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
    apply lattice_antitone F
      (m := ((d + 1 : ℕ) : ℤ)) (n := (d : ℤ) + (d : ℤ)) (by omega)
    simpa only [add_zero] using
      (mul_mem_lattice (m := (d : ℤ) + (d : ℤ)) (n := 0)
        F hdeltaSq he2F)
  let w2 : lattice F ((d + 1 : ℕ) : ℤ) :=
    ⟨(deltaF : F) ^ 2 * (e2 : F), hw2⟩
  let uK : unitFiltration K d :=
    lamprechtHasseUnit K chiK d hmK hlargeK deltaK hdeltaK
      (x : K) hxK
  let u1 : unitFiltration F d :=
    lamprechtHasseUnit F chiF d hmF hlargeF deltaF hdeltaF
      (trace F K (x : K)) htraceF
  let u2 : unitFiltration F (d + 1) :=
    positiveUnitOfLattice F (by omega) w2
  let v : Fˣ := (u1 : Fˣ) * (u2 : Fˣ)
  have hnormCong : CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (normUnits F K (uK : Kˣ) : F) (v : F) := by
    have hnorm := unramified_norm_odd_congruent
      F K hunr d hd deltaF hdeltaF (x : K) hxK
    have huKcoe : ((uK : Kˣ) : K) =
        1 + algebraMap F K (deltaF : F) * (x : K) := by
      change 1 + (deltaK : K) * (x : K) = _
      rw [hdelta]
      rfl
    have hu1coe : ((u1 : Fˣ) : F) =
        1 + (deltaF : F) * trace F K (x : K) := by
      simpa only [u1, lamprechtHasseUnit_coe]
    have hu2coe : ((u2 : Fˣ) : F) =
        1 + (deltaF : F) ^ 2 * (e2 : F) := by
      simpa only [u2, coe_positiveUnitOfLattice, w2]
    change CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (norm F K ((uK : Kˣ) : K)) (((u1 : Fˣ) : F) * ((u2 : Fˣ) : F))
    rw [huKcoe, hu1coe, hu2coe, he2]
    exact hnorm
  have huK0 : (uK : Kˣ) ∈ unitFiltration K 0 :=
    unitFiltration_antitone K (Nat.zero_le d) uK.property
  have hnorm0 : normUnits F K (uK : Kˣ) ∈ unitGroup F := by
    simpa only [unitFiltration_zero] using
      unramified_norm_mem_unitFiltration F K hunr 0 huK0
  have hu10 : (u1 : Fˣ) ∈ unitGroup F :=
    unitFiltration_antitone F (Nat.zero_le d) u1.property
  have hu20 : (u2 : Fˣ) ∈ unitGroup F :=
    unitFiltration_antitone F (Nat.zero_le (d + 1)) u2.property
  have hv0 : v ∈ unitGroup F := (unitGroup F).mul_mem hu10 hu20
  have hratio : normUnits F K (uK : Kˣ) / v ∈
      unitFiltration F (2 * d + 1) :=
    (div_mem_unitFiltration_iff_congruentAtDepth F (2 * d + 1)
      (normUnits F K (uK : Kˣ)) v hnorm0 hv0).2 hnormCong
  have hratioChar :
      chiF.character (normUnits F K (uK : Kˣ) / v) = 1 := by
    apply chiF.isConductor.trivial
    simpa only [hmF] using hratio
  have hlinear := stationaryNumeratorClass_linearization
    F chiF psiF (chiF.conductor : ℤ) hrF GammaF GammaF.property
      cF hcF w2
  have hchiNorm :
      chiF.character (normUnits F K (uK : Kˣ)) =
        chiF.character (u1 : Fˣ) *
          psiF.character ((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
            ((GammaF : Fˣ) : F)) := by
    calc
      chiF.character (normUnits F K (uK : Kˣ)) =
          chiF.character ((normUnits F K (uK : Kˣ) / v) * v) := by
        congr 1
        exact (div_mul_cancel _ _).symm
      _ = chiF.character (normUnits F K (uK : Kˣ) / v) *
          chiF.character v := by rw [map_mul]
      _ = chiF.character v := by rw [hratioChar, one_mul]
      _ = chiF.character (u1 : Fˣ) * chiF.character (u2 : Fˣ) := by
        rw [map_mul]
      _ = chiF.character (u1 : Fˣ) *
          psiF.character ((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
            ((GammaF : Fˣ) : F)) := by
        rw [hlinear]
        dsimp only [w2]
        congr 2
        ring
  have hpsiE2 :
      lamprechtResidualAddChar F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF (-residueMap F e2) =
        (psiF.character
          (-((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
            ((GammaF : Fˣ) : F))) : ℂ) := by
    have hneg : (-(e2 : F)) ∈ lattice F 0 := by
      exact (lattice F 0).neg_mem he2F
    have hred : reduce F (-(e2 : F)) hneg = -residueMap F e2 := by
      change residueMap F (-e2) = -residueMap F e2
      simp
    rw [← hred]
    rw [lamprechtResidualAddChar_integral_lift F chiF psiF d hmF hlargeF
      GammaF deltaF hdeltaF cF hcF (-(e2 : F)) hneg]
    congr 2
    ring
  have hpsiMain :
      psiK.character
          ((cK : K) * (deltaK : K) * (x : K) /
            ((GammaK : Kˣ) : K)) =
        psiF.character
          ((cF : F) * (deltaF : F) * trace F K (x : K) /
            ((GammaF : Fˣ) : F)) := by
    rw [hpsi, ContinuousAddChar.compTrace_apply]
    apply congrArg psiF.character
    have htraceScalar := (Algebra.trace F K).map_smul
      ((cF : F) * (deltaF : F) / ((GammaF : Fˣ) : F)) (x : K)
    have hdeltaCoe := congrArg Units.val hdelta
    have hGammaCoe := congrArg Units.val hGamma
    rw [hc, hdeltaCoe, hGammaCoe]
    simpa [Units.coe_map, Algebra.smul_def, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using htraceScalar
  have hchiMain : chiK.character (uK : Kˣ) =
      chiF.character (normUnits F K (uK : Kˣ)) := by
    rw [hchi, ContinuousQuasiChar.compNorm_apply]
  unfold lamprechtHasseValue
  rw [show lamprechtHasseUnit K chiK d hmK hlargeK deltaK hdeltaK
      (x : K) hxK = uK by rfl,
    show lamprechtHasseUnit F chiF d hmF hlargeF deltaF hdeltaF
      (trace F K (x : K)) htraceF = u1 by rfl,
    hpsiMain, hchiMain, hchiNorm, hpsiE2]
  push_cast
  have hq0 :
      (psiF.character
        ((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
          ((GammaF : Fˣ) : F)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  have hpsiNeg :
      (psiF.character
        (-((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
          ((GammaF : Fˣ) : F))) : ℂ) =
        (psiF.character
          ((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
            ((GammaF : Fˣ) : F)) : ℂ)⁻¹ := by
    simpa only [ContinuousAddChar.toAddChar_apply, Units.val_inv_eq_inv_val] using
      congrArg Units.val (AddChar.map_neg_eq_inv psiF.character.toAddChar
        ((cF : F) * (deltaF : F) ^ 2 * (e2 : F) /
          ((GammaF : Fˣ) : F)))
  rw [hpsiNeg]
  push_cast
  field_simp [hq0]

set_option maxHeartbeats 3000000 in
/-- The upstairs odd Hasse function is pointwise the finite-field trace lift
with the exact negative unordered-pair correction. -/
private theorem lamprechtHasseFunction_unramified_pointwise
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (d : ℕ)
    (hmF : chiF.conductor = 2 * d + 1)
    (hmK : chiK.conductor = 2 * d + 1)
    (hlargeF : 1 < chiF.conductor)
    (hlargeK : 1 < chiK.conductor)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K) (GammaF : Fˣ))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((d : ℤ) : WithTop ℤ))
    (hdelta : deltaK = Units.map (algebraMap F K) deltaF)
    (cF : lattice F ((chiF.conductor : ℤ) - (chiF.conductor : ℤ)))
    (hcF : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chiF d 1
            (by omega) hmF hlargeF).int_le_conductor
          (chiF.conductor : ℤ)) cF =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF d 1
          (by omega) hmF hlargeF) GammaF GammaF.property)
    (cK : lattice K ((chiK.conductor : ℤ) - (chiK.conductor : ℤ)))
    (hcK : latticeQuotientMk K
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth K chiK d 1
            (by omega) hmK hlargeK).int_le_conductor
          (chiK.conductor : ℤ)) cK =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK d 1
          (by omega) hmK hlargeK) GammaK GammaK.property)
    (hc : (cK : K) = algebraMap F K (cF : F))
    (x : ringOfIntegers K)
    (e2 : ringOfIntegers F)
    (he2 : (e2 : F) = elementarySymmetric F K 2 (x : K))
    (hres : residueMap F e2 =
      hassePairCorrection (ResidueField F) (ResidueField K)
        (residueMap K x)) :
    lamprechtHasseFunction K chiK psiK d hmK hlargeK GammaK
        deltaK hdeltaK cK hcK (residueMap K x) =
      hasseFunctionLiftValue (ResidueField F) (ResidueField K)
        (lamprechtHasseFunction F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF cF hcF) (residueMap K x) := by
  have hxK : (x : K) ∈ lattice K 0 :=
    (mem_lattice_zero_iff K).2 x.property
  have htraceF : trace F K (x : K) ∈ lattice F 0 := by
    rw [← coe_integralTrace F K x]
    exact (mem_lattice_zero_iff F).2 (integralTrace F K x).property
  rw [show lamprechtHasseFunction K chiK psiK d hmK hlargeK GammaK
      deltaK hdeltaK cK hcK (residueMap K x) =
        lamprechtHasseValue K chiK psiK d hmK hlargeK GammaK
          deltaK hdeltaK cK (x : K) hxK by
    simpa only [reduce_mk] using
      lamprechtHasseFunction_integral_lift K chiK psiK d hmK hlargeK
        GammaK deltaK hdeltaK cK hcK (x : K) hxK]
  rw [lamprechtHasseValue_unramified_odd F K hunr
    chiF psiF chiK psiK hchi hpsi d hmF hmK hlargeF hlargeK
    GammaF GammaK hGamma deltaF hdeltaF deltaK hdeltaK hdelta
    cF hcF cK hc x e2 he2]
  rw [← lamprechtHasseFunction_integral_lift F chiF psiF d hmF hlargeF
    GammaF deltaF hdeltaF cF hcF (trace F K (x : K)) htraceF]
  rw [hasseFunctionLiftValue]
  have htraceResidue : reduce F (trace F K (x : K)) htraceF =
      residueTrace (ResidueField F) (ResidueField K) (residueMap K x) := by
    rw [residue_trace F K hunr]
    apply congrArg (residueMap F)
    apply Subtype.ext
    exact (coe_integralTrace F K x).symm
  rw [htraceResidue, hres]

/-- Pointwise identification with the Hasse lift gives the exact residual
minus sign on Hasse-sum phases. -/
private theorem hasseFunctionLift_sumPhase_of_pointwise
    (k L : Type*) [Field k] [Fintype k] [Field L] [Fintype L]
    [Algebra k L]
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    (phi : HasseFunction k psi)
    {psiL : FiniteAddChar L} (phiL : HasseFunction L psiL)
    (hpoint : ∀ x : L,
      phiL x = hasseFunctionLiftValue k L phi x) :
    phiL.sumPhase =
      (-1 : ℂ) ^ (Module.finrank k L - 1) *
        phi.sumPhase ^ Module.finrank k L := by
  have hsum : phiL.sum =
      ∑ x : L, hasseFunctionLiftValue k L phi x := by
    rw [HasseFunction.sum]
    apply Finset.sum_congr rfl
    intro x _hx
    exact hpoint x
  have hlift := hasseFunctionLift k L hpsi phi
  rw [← hsum] at hlift
  have hpos : 0 < Module.finrank k L := Module.finrank_pos
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hsumEq : phiL.sum =
      (-1 : ℂ) ^ (Module.finrank k L - 1) *
        phi.sum ^ Module.finrank k L := by
    rw [hr] at hlift ⊢
    simp only [Nat.succ_sub_one]
    have hnegpow : (-phi.sum) ^ (r + 1) =
        (-1 : ℂ) ^ (r + 1) * phi.sum ^ (r + 1) := by
      rw [show -phi.sum = (-1 : ℂ) * phi.sum by ring, mul_pow]
    rw [hnegpow] at hlift
    have hsign : -((-1 : ℂ) ^ (r + 1)) = (-1 : ℂ) ^ r := by
      rw [pow_succ]
      ring
    calc
      phiL.sum = -(-phiL.sum) := by ring
      _ = -((-1 : ℂ) ^ (r + 1) * phi.sum ^ (r + 1)) := by rw [hlift]
      _ = (-((-1 : ℂ) ^ (r + 1))) * phi.sum ^ (r + 1) := by ring
      _ = (-1 : ℂ) ^ r * phi.sum ^ (r + 1) := by rw [hsign]
  rw [HasseFunction.sumPhase, HasseFunction.sumPhase, hsumEq]
  have hsum0 : phi.sum ≠ 0 := HasseFunction.sum_ne_zero phi hpsi
  rw [phase_mul (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
      (pow_ne_zero _ hsum0), phase_pow, phase_pow]
  rw [phase_of_norm_eq_one (by simp : ‖(-1 : ℂ)‖ = 1)]

/-! ### Lamprecht's even higher-conductor branch -/

private theorem deltaFinite_unramifiedPower_even
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (d : ℕ) (hm : chi.conductor = 2 * d)
    (hlarge : 1 < chi.conductor) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) ^
          Module.finrank F K := by
  let chiK := unramifiedQuasiCharData F K hunr chi
  let psiK := unramifiedAddCharData F K hunr psi
  let GammaF := uniformizerGamma F chi psi pi hpi
  let GammaK := unramifiedUniformizerGamma F K hunr chi psi pi hpi
  let hF : IsStationaryConductorDecomposition chi.conductor d 0 :=
    ⟨hlarge, by omega, by simpa using hm⟩
  let hK : IsStationaryConductorDecomposition chiK.conductor d 0 :=
    highParameter_unramified_sourceDecomposition F K chi chiK hF rfl hunr
  obtain ⟨cF, cK, hcmap, hcF, hcK⟩ :=
    exists_unramifiedLamprechtRepresentatives F K hunr
      chi chiK psi psiK rfl rfl hF GammaF
  have hcF' : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge).int_le_conductor
          (chi.conductor : ℤ)) cF =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 0
          (by omega) (by simpa using hm) hlarge) GammaF GammaF.property := by
    simpa [stationaryDepthOfConductorDecomposition] using hcF
  have hmK : chiK.conductor = 2 * d := by simpa [chiK] using hm
  have hlargeK : 1 < chiK.conductor := by simpa [chiK] using hlarge
  let GammaK' : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) (GammaF : Fˣ),
      highParameter_unramified_commonDenominator F K chi chiK psi psiK
        rfl rfl hunr (GammaF : Fˣ) GammaF.property⟩
  have hGammaAdm : GammaK = GammaK' := by
    apply Subtype.ext
    rfl
  have hcK' : latticeQuotientMk K
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth K chiK d 0
            (by omega) (by simpa using hmK) hlargeK).int_le_conductor
          (chiK.conductor : ℤ)) cK =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK d 0
          (by omega) (by simpa using hmK) hlargeK) GammaK GammaK.property := by
    rw [hGammaAdm]
    simpa [hK, GammaK', stationaryDepthOfConductorDecomposition] using hcK
  let betaF := lamprechtStationaryRepresentativeUnit F chi psi
    (lamprechtFormula_stationaryDepth F chi d 0
      (by omega) (by simpa using hm) hlarge) GammaF cF hcF'
  let betaK := lamprechtStationaryRepresentativeUnit K chiK psiK
    (lamprechtFormula_stationaryDepth K chiK d 0
      (by omega) (by simpa using hmK) hlargeK) GammaK cK hcK'
  have hbeta : betaK = Units.map (algebraMap F K).toMonoidHom betaF := by
    apply Units.ext
    change (cK : K) = algebraMap F K (cF : F)
    exact hcmap
  rw [lamprechtEven K chiK psiK d hmK hlargeK GammaK cK hcK',
    lamprechtEven F chi psi d hm hlarge GammaF cF hcF']
  change
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ) *
        lamprechtElementaryFactor K chiK psiK GammaK betaK) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        ((((chi.character (GammaF : Fˣ) : ℂˣ) : ℂ) *
          lamprechtElementaryFactor F chi psi GammaF betaF) ^
            Module.finrank F K)
  rw [hbeta]
  have hbase := lamprechtBaseFactor_unramified F K hunr chi psi pi hpi betaF
  change
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ) *
        lamprechtElementaryFactor K chiK psiK GammaK
          (Units.map (algebraMap F K).toMonoidHom betaF)) = _
  rw [hbase]
  have hsign :
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) = 1 := by
    rw [hm, mul_assoc, pow_mul]
    norm_num
  rw [hsign, one_mul]

/-! ### Lamprecht's odd higher-conductor branch -/

set_option maxHeartbeats 5000000 in
private theorem deltaFinite_unramifiedPower_odd
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) ^
          Module.finrank F K := by
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : Fintype (ResidueField K) := residueFieldFintype K
  let chiK := unramifiedQuasiCharData F K hunr chi
  let psiK := unramifiedAddCharData F K hunr psi
  let GammaF := uniformizerGamma F chi psi pi hpi
  let GammaK := unramifiedUniformizerGamma F K hunr chi psi pi hpi
  let hF : IsStationaryConductorDecomposition chi.conductor d 1 :=
    ⟨hlarge, by omega, hm⟩
  let hK : IsStationaryConductorDecomposition chiK.conductor d 1 :=
    highParameter_unramified_sourceDecomposition F K chi chiK hF rfl hunr
  obtain ⟨cF, cK, hcmap, hcF, hcK⟩ :=
    exists_unramifiedLamprechtRepresentatives F K hunr
      chi chiK psi psiK rfl rfl hF GammaF
  have hcF' : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) cF =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) GammaF GammaF.property := by
    simpa [stationaryDepthOfConductorDecomposition] using hcF
  have hmK : chiK.conductor = 2 * d + 1 := by simpa [chiK] using hm
  have hlargeK : 1 < chiK.conductor := by simpa [chiK] using hlarge
  let GammaK' : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K) (GammaF : Fˣ),
      highParameter_unramified_commonDenominator F K chi chiK psi psiK
        rfl rfl hunr (GammaF : Fˣ) GammaF.property⟩
  have hGammaAdm : GammaK = GammaK' := by
    apply Subtype.ext
    rfl
  have hcK' : latticeQuotientMk K
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth K chiK d 1
            (by omega) hmK hlargeK).int_le_conductor
          (chiK.conductor : ℤ)) cK =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK d 1
          (by omega) hmK hlargeK) GammaK GammaK.property := by
    rw [hGammaAdm]
    simpa [hK, GammaK', stationaryDepthOfConductorDecomposition] using hcK
  let deltaF : Fˣ := pi ^ d
  have hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ) := by
    change ord F ((pi : F) ^ d) = _
    rw [ord_pow, ord_uniformizer F hpi]
    change d • ((1 : ℤ) : WithTop ℤ) = ((d : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_nsmul]
    norm_num
  let deltaK : Kˣ := Units.map (algebraMap F K) deltaF
  have hdeltaK : ord K (deltaK : K) = ((d : ℤ) : WithTop ℤ) := by
    change ord K (algebraMap F K (deltaF : F)) = _
    rw [ord_algebraMap, hunr, one_nsmul, hdeltaF]
  let betaF := lamprechtStationaryRepresentativeUnit F chi psi
    (lamprechtFormula_stationaryDepth F chi d 1
      (by omega) hm hlarge) GammaF cF hcF'
  let betaK := lamprechtStationaryRepresentativeUnit K chiK psiK
    (lamprechtFormula_stationaryDepth K chiK d 1
      (by omega) hmK hlargeK) GammaK cK hcK'
  have hbeta : betaK = Units.map (algebraMap F K).toMonoidHom betaF := by
    apply Units.ext
    change (cK : K) = algebraMap F K (cF : F)
    exact hcmap
  let phiF := lamprechtHasseFunction F chi psi d hm hlarge GammaF
    deltaF hdeltaF cF hcF'
  let phiK := lamprechtHasseFunction K chiK psiK d hmK hlargeK GammaK
    deltaK hdeltaK cK hcK'
  have hpoint (xbar : ResidueField K) :
      phiK xbar = hasseFunctionLiftValue (ResidueField F) (ResidueField K)
        phiF xbar := by
    obtain ⟨x, rfl⟩ := residueMap_surjective K xbar
    let e2 := integralSecondCoeff F K x
    apply lamprechtHasseFunction_unramified_pointwise F K hunr
      chi psi chiK psiK rfl rfl d hm hmK hlarge hlargeK
      GammaF GammaK rfl deltaF hdeltaF deltaK hdeltaK rfl
      cF hcF' cK hcK' hcmap x e2
    · exact algebraMap_integralSecondCoeff F K x
    · exact unramified_residue_integralSecondCoeff F K hunr x
  have hpsi0 :
      lamprechtResidualAddChar F chi psi d hm hlarge GammaF
        deltaF hdeltaF ≠ 1 :=
    lamprechtResidualAddChar_ne_one F chi psi d hm hlarge GammaF
      deltaF hdeltaF cF hcF'
  have hphase : phiK.sumPhase =
      (-1 : ℂ) ^ (Module.finrank F K - 1) *
        phiF.sumPhase ^ Module.finrank F K := by
    have h := hasseFunctionLift_sumPhase_of_pointwise
      (ResidueField F) (ResidueField K) hpsi0 phiF phiK hpoint
    rw [unramified_residue_degree F K hunr] at h
    exact h
  rw [lamprechtOdd K chiK psiK d hmK hlargeK GammaK
      deltaK hdeltaK cK hcK',
    lamprechtOdd F chi psi d hm hlarge GammaF
      deltaF hdeltaF cF hcF']
  change
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ) *
        lamprechtElementaryFactor K chiK psiK GammaK betaK *
          phiK.sumPhase) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        ((((chi.character (GammaF : Fˣ) : ℂˣ) : ℂ) *
          lamprechtElementaryFactor F chi psi GammaF betaF *
            phiF.sumPhase) ^ Module.finrank F K)
  rw [hbeta]
  have hbase := lamprechtBaseFactor_unramified F K hunr chi psi pi hpi betaF
  have hsign :
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) =
        (-1 : ℂ) ^ (Module.finrank F K - 1) := by
    rw [hm, pow_mul]
    have hodd : (-1 : ℂ) ^ (2 * d + 1) = -1 := by
      rw [show 2 * d + 1 = 2 * d + 1 by rfl, pow_add, pow_mul]
      norm_num
    rw [hodd]
  rw [hbase, hphase, hsign]
  simp only [mul_pow]
  ring

/-- The two Lamprecht branches exhaust every conductor strictly larger
than one. -/
private theorem deltaFinite_unramifiedPower_high
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F))
    (hlarge : 1 < chi.conductor) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) ^
          Module.finrank F K := by
  rcases Nat.even_or_odd chi.conductor with heven | hodd
  · obtain ⟨d, hd⟩ := heven
    have hm : chi.conductor = 2 * d := by omega
    exact deltaFinite_unramifiedPower_even F K hunr chi psi pi hpi
      d hm hlarge
  · obtain ⟨d, hm⟩ := hodd
    exact deltaFinite_unramifiedPower_odd F K hunr chi psi pi hpi
      d hm hlarge

/-- The signed unramified power identity, with the conductor-zero,
conductor-one, and higher-conductor ranges kept exhaustive and disjoint. -/
private theorem deltaFinite_unramifiedPower
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) =
      (-1 : ℂ) ^ (chi.conductor * (Module.finrank F K - 1)) *
        deltaFinite chi psi (uniformizerGamma F chi psi pi hpi) ^
          Module.finrank F K := by
  by_cases hm0 : chi.conductor = 0
  · exact deltaFinite_unramifiedPower_zero F K hunr chi psi pi hpi hm0
  by_cases hm1 : chi.conductor = 1
  · exact deltaFinite_unramifiedPower_one F K hunr chi psi pi hpi hm1
  exact deltaFinite_unramifiedPower_high F K hunr chi psi pi hpi (by omega)

/-! ## The complete norm-character product -/

/-- Evaluation at an unramified uniformizer enumerates the whole norm
character group, including the identity, and its product has the exact
root-polynomial sign. -/
private theorem unramifiedNormCharacter_product
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    (unramifiedNormCharacterFinset F K hunr).prod
        (fun mu => ((mu.1 pi : ℂˣ) : ℂ)) =
      (-1 : ℂ) ^ (Module.finrank F K - 1) := by
  letI : Finite (NormCharacter F K) :=
    unramifiedNormCharacter_finite F K hunr
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let n := Module.finrank F K
  have hn : 0 < n := by
    dsimp [n]
    exact Module.finrank_pos
  letI : NeZero n := ⟨hn.ne'⟩
  let rootFintype : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity n ℂ) := rootFintype
  letI : Fintype {x : ℂ // x ∈ nthRoots n (1 : ℂ)} := Fintype.ofFinite _
  have transport_coe {m n' : ℕ} (h : m = n')
      (e : NormCharacter F K ≃* rootsOfUnity m ℂ)
      (x : NormCharacter F K) :
      (((((by rw [← h]; exact e) :
          NormCharacter F K ≃* rootsOfUnity n' ℂ) x :
          rootsOfUnity n' ℂ) : ℂˣ) : ℂ) =
        (((e x : rootsOfUnity m ℂ) : ℂˣ) : ℂ) := by
    subst n'
    rfl
  have heval (mu : NormCharacter F K) :
      ((((unramifiedNormCharacterEvaluationEquiv F K hunr pi hpi mu :
          rootsOfUnity n ℂ) : ℂˣ) : ℂ)) =
        ((mu.1 pi : ℂˣ) : ℂ) := by
    have htransport := transport_coe
      (unramifiedNormQuotient_natCard F K hunr)
      (unramifiedNormCharacterEvaluationEquivCard F K hunr pi hpi) mu
    exact htransport.trans
      (unramifiedNormCharacterEvaluationEquivCard_coe F K hunr pi hpi mu)
  have hroot : (nthRoots n (1 : ℂ)).prod =
      (-1 : ℂ) ^ (n - 1) := by
    have hcoeff : (-1 : ℂ) =
        (-1 : ℂ) ^ n * (nthRoots n (1 : ℂ)).prod := by
      have hpoly :=
        (IsAlgClosed.splits (X ^ n - C (1 : ℂ))).coeff_zero_eq_prod_roots_of_monic
          (monic_X_pow_sub_C (1 : ℂ) hn.ne')
      rw [natDegree_X_pow_sub_C] at hpoly
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (Ne.symm hn.ne'),
        if_pos rfl, zero_sub] at hpoly
      exact hpoly
    have haa : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
      rcases neg_one_pow_eq_or ℂ n with ha | ha <;> rw [ha] <;> norm_num
    calc
      (nthRoots n (1 : ℂ)).prod =
          1 * (nthRoots n (1 : ℂ)).prod := by rw [one_mul]
      _ = (((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n)) *
          (nthRoots n (1 : ℂ)).prod := by rw [haa]
      _ = (-1 : ℂ) ^ n *
          ((-1 : ℂ) ^ n * (nthRoots n (1 : ℂ)).prod) := by
        rw [mul_assoc]
      _ = (-1 : ℂ) ^ n * (-1 : ℂ) := by rw [← hcoeff]
      _ = (-1 : ℂ) ^ (n + 1) := by rw [pow_succ]
      _ = (-1 : ℂ) ^ (n - 1) := by
        rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
        norm_num
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  change (∏ mu : NormCharacter F K, ((mu.1 pi : ℂˣ) : ℂ)) = _
  calc
    (∏ mu : NormCharacter F K, ((mu.1 pi : ℂˣ) : ℂ)) =
        (@Finset.univ (rootsOfUnity n ℂ) rootFintype).prod
          (fun zeta => (((zeta : rootsOfUnity n ℂ) : ℂˣ) : ℂ)) := by
      exact Fintype.prod_equiv
        (unramifiedNormCharacterEvaluationEquiv F K hunr pi hpi).toEquiv
        (fun mu => ((mu.1 pi : ℂˣ) : ℂ))
        (fun zeta => (((zeta : rootsOfUnity n ℂ) : ℂˣ) : ℂ))
        (fun mu => (heval mu).symm)
    _ = ∏ x : {x : ℂ // x ∈ nthRoots n (1 : ℂ)}, (x : ℂ) := by
      exact Fintype.prod_equiv (rootsOfUnityEquivNthRoots ℂ n)
        (fun zeta => (((zeta : rootsOfUnity n ℂ) : ℂˣ) : ℂ))
        (fun x : {x : ℂ // x ∈ nthRoots n (1 : ℂ)} => (x : ℂ))
        (fun _ => rfl)
    _ = ∏ x ∈ nthRootsFinset n (1 : ℂ), x := by
      exact (Finset.prod_subtype (nthRootsFinset n (1 : ℂ))
        (fun x => by simp [nthRootsFinset_def]) (fun x : ℂ => x)).symm
    _ = (nthRoots n (1 : ℂ)).prod := by
      rw [nthRootsFinset_def, Finset.prod_eq_multiset_prod]
      simp only [Multiset.map_id']
      rw [Multiset.toFinset_val, hprim.nthRoots_one_nodup.dedup]
    _ = (-1 : ℂ) ^ (n - 1) := hroot
    _ = (-1 : ℂ) ^ (Module.finrank F K - 1) := by rfl

/-- **First Main Lemma, unramified cyclic-prime case.**

This is the complete computational identity for the project's normalized
finite local constant.  It includes every norm character (also the trivial
one), uses the exact norm and trace pullbacks, and uses the canonical common
denominator in every factor. -/
theorem firstMain_unramified
    [PrimeCyclicExtension F K]
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) *
      (unramifiedNormCharacterFinset F K hunr).prod (fun mu =>
        deltaFinite (unramifiedNormCharacterData F K hunr mu) psi
          (uniformizerGamma F
            (unramifiedNormCharacterData F K hunr mu) psi pi hpi)) =
      (unramifiedNormCharacterFinset F K hunr).prod (fun mu =>
        deltaFinite (unramifiedTwistData F K hunr chi mu) psi
          (uniformizerGamma F
            (unramifiedTwistData F K hunr chi mu) psi pi hpi)) := by
  letI : Finite (NormCharacter F K) :=
    unramifiedNormCharacter_finite F K hunr
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let S := unramifiedNormCharacterFinset F K hunr
  let ell := Module.finrank F K
  let A := deltaFinite chi psi (uniformizerGamma F chi psi pi hpi)
  let P := S.prod (fun mu => ((mu.1 pi : ℂˣ) : ℂ))
  have hcard : S.card = ell := by
    change Fintype.card (NormCharacter F K) = Module.finrank F K
    rw [← Nat.card_eq_fintype_card,
      unramifiedNormCharacter_card F K hunr]
  have hP : P = (-1 : ℂ) ^ (ell - 1) := by
    exact unramifiedNormCharacter_product F K hunr pi hpi
  have hnormProd :
      S.prod (fun mu =>
        deltaFinite (unramifiedNormCharacterData F K hunr mu) psi
          (uniformizerGamma F
            (unramifiedNormCharacterData F K hunr mu) psi pi hpi)) =
        P ^ psi.conductor := by
    calc
      S.prod (fun mu =>
          deltaFinite (unramifiedNormCharacterData F K hunr mu) psi
            (uniformizerGamma F
              (unramifiedNormCharacterData F K hunr mu) psi pi hpi)) =
          S.prod (fun mu =>
            ((mu.1 pi : ℂˣ) : ℂ) ^ psi.conductor) := by
        apply Finset.prod_congr rfl
        intro mu _hmu
        exact deltaFinite_normCharacter F K hunr psi mu pi hpi
      _ = P ^ psi.conductor := by
        exact Finset.prod_zpow (fun mu : NormCharacter F K =>
          ((mu.1 pi : ℂˣ) : ℂ)) S psi.conductor
  have htwistProd :
      S.prod (fun mu =>
        deltaFinite (unramifiedTwistData F K hunr chi mu) psi
          (uniformizerGamma F
            (unramifiedTwistData F K hunr chi mu) psi pi hpi)) =
        P ^ ((chi.conductor : ℤ) + psi.conductor) * A ^ ell := by
    calc
      S.prod (fun mu =>
          deltaFinite (unramifiedTwistData F K hunr chi mu) psi
            (uniformizerGamma F
              (unramifiedTwistData F K hunr chi mu) psi pi hpi)) =
          S.prod (fun mu =>
            ((mu.1 pi : ℂˣ) : ℂ) ^
                ((chi.conductor : ℤ) + psi.conductor) * A) := by
        apply Finset.prod_congr rfl
        intro mu _hmu
        exact deltaFinite_unramifiedTwist F K hunr chi psi mu pi hpi
      _ = S.prod (fun mu =>
            ((mu.1 pi : ℂˣ) : ℂ) ^
              ((chi.conductor : ℤ) + psi.conductor)) *
          S.prod (fun _mu => A) := Finset.prod_mul_distrib
      _ = P ^ ((chi.conductor : ℤ) + psi.conductor) * A ^ S.card := by
        rw [Finset.prod_zpow, Finset.prod_const]
      _ = P ^ ((chi.conductor : ℤ) + psi.conductor) * A ^ ell := by
        rw [hcard]
  have hpower := deltaFinite_unramifiedPower F K hunr chi psi pi hpi
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact pow_ne_zero _ (by norm_num)
  have hPm : P ^ (chi.conductor : ℤ) =
      (-1 : ℂ) ^ (chi.conductor * (ell - 1)) := by
    rw [hP, zpow_natCast]
    calc
      ((-1 : ℂ) ^ (ell - 1)) ^ chi.conductor =
          (-1 : ℂ) ^ ((ell - 1) * chi.conductor) :=
        (pow_mul _ _ _).symm
      _ = (-1 : ℂ) ^ (chi.conductor * (ell - 1)) := by
        rw [Nat.mul_comm (ell - 1) chi.conductor]
  have hfactor :
      (-1 : ℂ) ^ (chi.conductor * (ell - 1)) * P ^ psi.conductor =
        P ^ ((chi.conductor : ℤ) + psi.conductor) := by
    rw [zpow_add₀ hP0, hPm]
  change
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) *
      S.prod (fun mu =>
        deltaFinite (unramifiedNormCharacterData F K hunr mu) psi
          (uniformizerGamma F
            (unramifiedNormCharacterData F K hunr mu) psi pi hpi)) =
      S.prod (fun mu =>
        deltaFinite (unramifiedTwistData F K hunr chi mu) psi
          (uniformizerGamma F
            (unramifiedTwistData F K hunr chi mu) psi pi hpi))
  rw [hpower, hnormProd, htwistProd]
  change
    ((-1 : ℂ) ^ (chi.conductor * (ell - 1)) * A ^ ell) *
        P ^ psi.conductor =
      P ^ ((chi.conductor : ℤ) + psi.conductor) * A ^ ell
  calc
    ((-1 : ℂ) ^ (chi.conductor * (ell - 1)) * A ^ ell) *
        P ^ psi.conductor =
      ((-1 : ℂ) ^ (chi.conductor * (ell - 1)) * P ^ psi.conductor) *
        A ^ ell := by ring
    _ = P ^ ((chi.conductor : ℤ) + psi.conductor) * A ^ ell := by
      rw [hfactor]

/-- **Dispatch-ready First Main identity, unramified cyclic-prime case.**

This is the interface wrapper around `firstMain_unramified`.  It packages
the same exact conductor data and canonical uniformizer denominators used by
that computational theorem, normalizes its complete norm-character finset
to the full `NormCharacter` product, and applies the generic computational
bridge. -/
theorem firstMain_unramified_dispatchReady
    [PrimeCyclicExtension F K]
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (hunr : ramificationIndex F K = 1)
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (pi : Fˣ) (hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F)) :
    letI : Finite (NormCharacter F K) :=
      unramifiedNormCharacter_finite F K hunr
    FirstMainIdentity F K DeltaF DeltaK chi.character psi.character := by
  letI : Finite (NormCharacter F K) :=
    unramifiedNormCharacter_finite F K hunr
  let data : FirstMainComputationalData F K chi.character psi.character := {
    baseAddChar := psi
    baseAddChar_character := rfl
    extensionQuasiChar := unramifiedQuasiCharData F K hunr chi
    extensionQuasiChar_character := rfl
    extensionAddChar := unramifiedAddCharData F K hunr psi
    extensionAddChar_character := rfl
    normCharacterData := unramifiedNormCharacterData F K hunr
    normCharacterData_character := fun _mu => rfl
    twistData := unramifiedTwistData F K hunr chi
    twistData_character := fun _mu => rfl
  }
  let gammaK : AdmissibleGamma K
      data.extensionQuasiChar data.extensionAddChar :=
    unramifiedUniformizerGamma F K hunr chi psi pi hpi
  let gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.normCharacterData mu) data.baseAddChar :=
    fun mu => uniformizerGamma F
      (unramifiedNormCharacterData F K hunr mu) psi pi hpi
  let gammaTwist : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.twistData mu) data.baseAddChar :=
    fun mu => uniformizerGamma F
      (unramifiedTwistData F K hunr chi mu) psi pi hpi
  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chi.character psi.character
    data gammaK gammaNorm gammaTwist
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  change
    deltaFinite (unramifiedQuasiCharData F K hunr chi)
        (unramifiedAddCharData F K hunr psi)
        (unramifiedUniformizerGamma F K hunr chi psi pi hpi) *
      (∏ mu : NormCharacter F K,
        deltaFinite (unramifiedNormCharacterData F K hunr mu) psi
          (uniformizerGamma F
            (unramifiedNormCharacterData F K hunr mu) psi pi hpi)) =
      ∏ mu : NormCharacter F K,
        deltaFinite (unramifiedTwistData F K hunr chi mu) psi
          (uniformizerGamma F
            (unramifiedTwistData F K hunr chi mu) psi pi hpi)
  exact firstMain_unramified F K hunr chi psi pi hpi

end

end LanglandsFirstMainLemma
