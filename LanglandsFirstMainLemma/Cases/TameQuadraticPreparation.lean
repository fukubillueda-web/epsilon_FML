import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Cases.TameQuadratic
import LanglandsFirstMainLemma.Delta.ErrorTerm

/-!
# Preparation for the tamely ramified quadratic case

This file is the dispatch boundary around the completed quadratic tame
calculation.  A ramified prime-cyclic preparation package supplies residue
degree one and a monogenic integral uniformizer.  Tameness changes its
canonical lower break to zero, and degree two forces the residue
characteristic to be odd.

For an arbitrary downstairs quasi-character, we select the least-conductor
member of its complete norm-character orbit.  The exact norm pullback of
that representative and the exact trace pullback of the additive character
are then packaged for `firstMain_tameQuadratic`.  Its full `deltaFinite`
product is bridged to `FirstMainIdentity`, after which the proved
norm-character twist invariance transports the identity back to the
original quasi-character.

No conductor split, stationary representative, residual Hasse function, or
quadratic phase is reconstructed here.  Those computations remain entirely
inside `Cases.TameQuadratic`.

Source: Propositions `prop:tame-conductor-one-comparison` and
`prop:tame-two-new`, together with Section `sec:first-main-completion`, in
`references/epsilon_FML.tex`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

/- The complete case theorem deliberately keeps its actual-conductor
packages and normalized uniformizer-power denominators private.  This
preparation node reuses precisely those declarations in the bridge below;
it does not replace them or unfold any of their quadratic calculations. -/
open private tameQuadraticUpperGamma tameQuadraticLowerGamma
  tameQuadraticNormCharacterData tameQuadraticNormCharacterData_character
  tameQuadraticTwistData tameQuadraticTwistData_character
  from LanglandsFirstMainLemma.Cases.TameQuadratic

section TameQuadraticPreparation

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

/-! ## Exact pullback packages -/

/-- The exact multiplicative-conductor package for norm pullback.

The conductor is the canonical least exact conductor of the literal
pullback character.  The completed tame-quadratic theorem subsequently
identifies its value from minimality; no conductor formula is postulated in
this definition. -/
private noncomputable def tameQuadraticPreparationNormPullbackData
    (chiF : LocalQuasiCharData F) : LocalQuasiCharData K where
  character := chiF.character.compNorm
  conductor := multiplicativeConductorExponent K chiF.character.compNorm
  isConductor :=
    multiplicativeConductorExponent_isConductor K chiF.character.compNorm

omit [PrimeCyclicExtension F K] in
@[simp]
private theorem tameQuadraticPreparationNormPullbackData_character
    (chiF : LocalQuasiCharData F) :
    (tameQuadraticPreparationNormPullbackData F K chiF).character =
      chiF.character.compNorm :=
  rfl

/-- The exact additive-conductor package for trace pullback at tame break
zero.  The shift is the different exponent `[K:F]-1`, exactly as in the
manuscript's normalization. -/
private def tameQuadraticPreparationTracePullbackData
    (psiF : LocalAddCharData F) : LocalAddCharData K where
  character := psiF.character.compTrace
  conductor :=
    (Module.finrank F K : ℤ) * psiF.conductor +
      ((Module.finrank F K - 1 : ℕ) : ℤ)
  isConductor := by
    simpa using additiveConductor_compTrace_cyclicPrime
      F K ht hres piK hpiK hgen psiF.isConductor

@[simp]
private theorem tameQuadraticPreparationTracePullbackData_character
    (psiF : LocalAddCharData F) :
    (tameQuadraticPreparationTracePullbackData
      F K ht hres piK hpiK hgen psiF).character =
        psiF.character.compTrace :=
  rfl

/-! ## The computational product bridge -/

/-- Bridge the complete tame-quadratic `deltaFinite` product for an already
minimal representative to the literal fixed-character First Main identity.

This is the dispatch-ready argument extracted from the earlier proof on
`codex/done-cases-tamequadratic`.  It packages the full norm-character type,
including the identity, and retains the exact upper, norm-character, and
twist denominators selected by the computational theorem. -/
private theorem firstMain_tameQuadratic_minimal_of_isDeltaFinite
    (hdegree : Module.finrank F K = 2)
    (hchar : residueCharacteristic F ≠ 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K

  let data : FirstMainComputationalData F K
      chiF.character psiF.character :=
    { baseAddChar := psiF
      baseAddChar_character := rfl
      extensionQuasiChar := chiK
      extensionQuasiChar_character := hchi
      extensionAddChar := psiK
      extensionAddChar_character := hpsi
      normCharacterData :=
        tameQuadraticNormCharacterData F K hres piK hpiK ht hgen
      normCharacterData_character :=
        tameQuadraticNormCharacterData_character
          F K hres piK hpiK ht hgen
      twistData :=
        tameQuadraticTwistData F K hres piK hpiK ht hgen chiF
      twistData_character :=
        tameQuadraticTwistData_character
          F K hres piK hpiK ht hgen chiF }

  let gammaK : AdmissibleGamma K
      data.extensionQuasiChar data.extensionAddChar :=
    tameQuadraticUpperGamma K piK hpiK chiK psiK
  let gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.normCharacterData mu) data.baseAddChar :=
    fun mu ↦ tameQuadraticLowerGamma F K hres piK hpiK
      (tameQuadraticNormCharacterData
        F K hres piK hpiK ht hgen mu) psiF
  let gammaTwist : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.twistData mu) data.baseAddChar :=
    fun mu ↦ tameQuadraticLowerGamma F K hres piK hpiK
      (tameQuadraticTwistData
        F K hres piK hpiK ht hgen chiF mu) psiF

  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chiF.character psiF.character
      data gammaK gammaNorm gammaTwist
  simpa only [data, gammaK, gammaNorm, gammaTwist,
    ramifiedNormCharacterFinset, normCharacterFinset] using
      (firstMain_tameQuadratic F K ht hres piK hpiK hgen hdegree hchar
        chiF chiK psiF psiK hminimal hchi hpsi)

/-! ## Dispatch-ready theorem -/

/-- **First Main Lemma, prepared tamely ramified quadratic branch.**

The ramified branch is supplied as `PrimeCyclicPreparation`.  Tameness gives
break zero, while degree two and tameness give odd residue characteristic.
For an arbitrary `chiF`, the proof selects its minimal norm-character-orbit
representative, constructs the exact norm and trace pullbacks, invokes the
complete tame-quadratic product theorem, and bridges that product with
`firstMainIdentity_of_deltaFinite_product`.  Finally the left- and right-side
twist-invariance theorems transport the identity to the original character.
-/
theorem firstMain_tameQuadratic_of_isDeltaFinite
    (P : PrimeCyclicPreparation F K)
    (htame : IsTamelyRamified F K)
    (hdegree : Module.finrank F K = 2)
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K P.ht P.hres P.piK P.hpiK P.hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  let ht := P.isLowerBreak_zero_of_isTamelyRamified F K htame
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht P.hres P.piK P.hpiK P.hgen

  let chiMin := minimalOrbitRepresentative
    F K ht P.hres P.piK P.hpiK P.hgen chiF
  have hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiMin :=
    minimalOrbitRepresentative_isMinimal
      F K ht P.hres P.piK P.hpiK P.hgen chiF

  let chiK := tameQuadraticPreparationNormPullbackData F K chiMin
  let psiK := tameQuadraticPreparationTracePullbackData
    F K ht P.hres P.piK P.hpiK P.hgen psiF

  have hchar : residueCharacteristic F ≠ 2 := by
    intro htwo
    apply htame
    simpa only [P.ramificationIndex_eq_degree F K, hdegree, htwo] using
      (dvd_refl 2)

  have hminIdentity : FirstMainIdentity F K DeltaF DeltaK
      chiMin.character psiF.character :=
    firstMain_tameQuadratic_minimal_of_isDeltaFinite
      F K ht P.hres P.piK P.hpiK P.hgen hdegree hchar
        chiMin chiK psiF psiK hminimal rfl rfl
          DeltaF DeltaK hDeltaF hDeltaK

  obtain ⟨mu, hmu⟩ := minimalOrbitRepresentative_mem_orbit
    F K ht P.hres P.piK P.hpiK P.hgen chiF
  unfold FirstMainIdentity at hminIdentity ⊢
  calc
    firstMainLeftSide F K DeltaF DeltaK chiF.character psiF.character =
        firstMainLeftSide F K DeltaF DeltaK (mu.1 * chiF.character)
          psiF.character :=
      (firstMainLeftSide_normCharacter_mul F K DeltaF DeltaK mu
        chiF.character psiF.character).symm
    _ = firstMainLeftSide F K DeltaF DeltaK chiMin.character
          psiF.character := by rw [hmu]
    _ = firstMainRightSide F K DeltaF chiMin.character psiF.character :=
      hminIdentity
    _ = firstMainRightSide F K DeltaF (mu.1 * chiF.character)
          psiF.character := by rw [hmu]
    _ = firstMainRightSide F K DeltaF chiF.character psiF.character :=
      firstMainRightSide_normCharacter_mul F K DeltaF mu
        chiF.character psiF.character

end TameQuadraticPreparation

end

end LanglandsFirstMainLemma
