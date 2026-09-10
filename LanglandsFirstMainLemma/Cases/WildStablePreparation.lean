import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Parameters.RamifiedHassePreparation
import LanglandsFirstMainLemma.Cases.WildStable
import LanglandsFirstMainLemma.Delta.ErrorTerm

/-!
# Preparation for the wild stable case

This file is the dispatch boundary around the completed wild stable
calculation.  It selects a least-conductor member of the full norm-character
orbit, constructs the literal norm and trace pullbacks at their exact
conductors, and supplies the stable-high theorem with actual conductor
decompositions, admissible denominators, and a representative of the
stationary quotient class.

The residual branch is determined by the two actual conductor remainders.
In even conductor it is definitionally trivial.  In odd conductor the
source-tied lower and upper uniformizer powers are passed to
`ramifiedHassePreparation`; the same quotient representative remains live
through the high parameter row and the final wild-stable consumer.

The completed `deltaFinite` product is bridged to `FirstMainIdentity`, and
the proved left- and right-side invariance under a norm-character twist then
transports the identity from the minimal representative back to the original
character.

Source: Proposition `prop:wild-stable-new` and Section
`sec:first-main-completion` of `references/epsilon_FML.tex`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section WildStablePreparation

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-! ## Exact pullback and conductor packages -/

/-- The canonical division-with-remainder stationary decomposition at the
actual conductor.  The hypothesis `1 < m` is retained rather than hidden in
a synthetic parity package. -/
private theorem wildStablePreparation_conductorDecomposition
    {m : ℕ} (hm : 1 < m) :
    IsStationaryConductorDecomposition m (m / 2) (m % 2) where
  conductor_gt_one := hm
  epsilon_le_one := by omega
  conductor_eq := by omega

/-- The literal norm pullback, packaged directly at the exact Herbrand
conductor supplied by the high-conductor theorem. -/
private def wildStablePreparationNormPullbackData
    (P : PrimeCyclicPreparation F K)
    (chiF : LocalQuasiCharData F)
    (hhigh : P.t + 1 < chiF.conductor) : LocalQuasiCharData K where
  character := chiF.character.compNorm
  conductor :=
    herbrandPsiNat P.t (Module.finrank F K) (chiF.conductor - 1) + 1
  isConductor := multiplicativeConductor_compNorm_high
    F K P.ht P.hres P.piK P.hpiK P.hgen hhigh chiF.isConductor

@[simp]
private theorem wildStablePreparationNormPullbackData_character
    (P : PrimeCyclicPreparation F K)
    (chiF : LocalQuasiCharData F)
    (hhigh : P.t + 1 < chiF.conductor) :
    (wildStablePreparationNormPullbackData F K P chiF hhigh).character =
      chiF.character.compNorm :=
  rfl

@[simp]
private theorem wildStablePreparationNormPullbackData_conductor
    (P : PrimeCyclicPreparation F K)
    (chiF : LocalQuasiCharData F)
    (hhigh : P.t + 1 < chiF.conductor) :
    (wildStablePreparationNormPullbackData F K P chiF hhigh).conductor =
      herbrandPsiNat P.t (Module.finrank F K) (chiF.conductor - 1) + 1 :=
  rfl

/-- The literal trace pullback at the exact different-shifted additive
conductor `[K:F] n_F + ([K:F]-1)(t+1)`. -/
private def wildStablePreparationTracePullbackData
    (P : PrimeCyclicPreparation F K)
    (psiF : LocalAddCharData F) : LocalAddCharData K where
  character := psiF.character.compTrace
  conductor :=
    (Module.finrank F K : ℤ) * psiF.conductor +
      (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)
  isConductor := additiveConductor_compTrace_cyclicPrime
    F K P.ht P.hres P.piK P.hpiK P.hgen psiF.isConductor

@[simp]
private theorem wildStablePreparationTracePullbackData_character
    (P : PrimeCyclicPreparation F K)
    (psiF : LocalAddCharData F) :
    (wildStablePreparationTracePullbackData F K P psiF).character =
      psiF.character.compTrace :=
  rfl

@[simp]
private theorem wildStablePreparationTracePullbackData_conductor
    (P : PrimeCyclicPreparation F K)
    (psiF : LocalAddCharData F) :
    (wildStablePreparationTracePullbackData F K P psiF).conductor =
      (Module.finrank F K : ℤ) * psiF.conductor +
        (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ) :=
  rfl

/-! ## Computational product bridge -/

/-- Bridge the completed wild-stable `deltaFinite` product for an already
prepared minimal representative to the literal fixed-character First Main
identity.  The full norm-character type, its identity element, and the
actual admissible denominator chosen for every factor are retained. -/
private theorem firstMain_wildStable_minimal_of_isDeltaFinite
    (P : PrimeCyclicPreparation F K)
    (htwild : 0 < P.t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : P.t + 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildStableNormCharacterData F K P.ht P.hres P.piK P.hpiK P.hgen
          htwild mu)
        psiF)
    (C : WildStableResidualComparison F K P.ht P.hres P.piK P.hpiK P.hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        (highConductorParameter_stableOdd F K P.ht P.hres P.piK P.hpiK
          P.hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF
            hgammaF)
        R CF CK)
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite
        F K P.ht P.hres P.piK P.hpiK P.hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite
      F K P.ht P.hres P.piK P.hpiK P.hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K

  let H := highConductorParameter_stableOdd
    F K P.ht P.hres P.piK P.hpiK P.hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K).toMonoidHom gammaF, H.commonDenominator⟩
  let data : FirstMainComputationalData F K
      chiF.character psiF.character :=
    { baseAddChar := psiF
      baseAddChar_character := rfl
      extensionQuasiChar := chiK
      extensionQuasiChar_character := hchi
      extensionAddChar := psiK
      extensionAddChar_character := hpsi
      normCharacterData := wildStableNormCharacterData
        F K P.ht P.hres P.piK P.hpiK P.hgen htwild
      normCharacterData_character := wildStableNormCharacterData_character
        F K P.ht P.hres P.piK P.hpiK P.hgen htwild
      twistData := wildStableTwistData
        F K P.ht P.hres P.piK P.hpiK P.hgen htwild chiF hF hd
      twistData_character := wildStableTwistData_character
        F K P.ht P.hres P.piK P.hpiK P.hgen htwild chiF hF hd }
  let GammaTwist : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (data.twistData mu) data.baseAddChar := fun mu ↦
    wildStableTwistGamma
      F K P.ht P.hres P.piK P.hpiK P.hgen htwild
        chiF hF hd mu psiF GammaF

  have hproduct := firstMain_wildStable
    F K P.ht P.hres P.piK P.hpiK P.hgen htwild
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        R CF CK GammaNorm C
  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chiF.character psiF.character
      data GammaK GammaNorm GammaTwist
  change deltaFinite chiK psiK GammaK *
      (∏ mu : NormCharacter F K,
        deltaFinite
          (wildStableNormCharacterData
            F K P.ht P.hres P.piK P.hpiK P.hgen htwild mu)
          psiF (GammaNorm mu)) =
    ∏ mu : NormCharacter F K,
      deltaFinite
        (wildStableTwistData
          F K P.ht P.hres P.piK P.hpiK P.hgen htwild chiF hF hd mu)
        psiF
        (wildStableTwistGamma
          F K P.ht P.hres P.piK P.hpiK P.hgen htwild
            chiF hF hd mu psiF GammaF)
  change deltaFinite chiK psiK GammaK *
      (∏ mu : NormCharacter F K,
        deltaFinite
          (wildStableNormCharacterData
            F K P.ht P.hres P.piK P.hpiK P.hgen htwild mu)
          psiF (GammaNorm mu)) =
    ∏ mu : NormCharacter F K,
      deltaFinite
        (wildStableTwistData
          F K P.ht P.hres P.piK P.hpiK P.hgen htwild chiF hF hd mu)
        psiF
        (wildStableTwistGamma
          F K P.ht P.hres P.piK P.hpiK P.hgen htwild
            chiF hF hd mu psiF GammaF) at hproduct
  exact hproduct

/-! ## Dispatch-ready theorem -/

/-- **First Main Lemma, prepared wild odd-prime stable branch.**

For an arbitrary downstairs character, select the least-conductor member of
its full norm-character orbit and put `d = m / 2`, `epsilon = m % 2`.
The stable hypothesis constructs the genuine stationary decomposition and
places the minimal representative strictly in the high range.  The norm and
trace pullbacks are packaged at their exact current conductors, and their
own division-with-remainder decomposition is used upstairs.

An admissible downstairs denominator and an actual preimage of the
stationary quotient class are chosen.  The high stable row maps that literal
representative upstairs.  Even/even residual coordinates contribute `True`;
odd/odd coordinates are the powers of the source-tied ramified Hasse
uniformizers and use `ramifiedHassePreparation` without reconstructing any
Hasse, trace, or norm-polynomial calculation.  The stable twist remains the
one implemented by `wildStableTwistGamma`, hence has factor
`mu (GammaF / beta)` in the manuscript's direction.

Finally, the completed finite product is bridged to `FirstMainIdentity` and
transported from the minimal representative back to the original character
using invariance of both sides under left multiplication by a norm
character. -/
theorem firstMain_wildStable_of_isDeltaFinite
    (P : PrimeCyclicPreparation F K)
    (hwild : IsWildlyRamified F K)
    (hodd : Odd (Module.finrank F K))
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (hstable :
      P.t + 1 ≤
        (minimalOrbitRepresentative
          F K P.ht P.hres P.piK P.hpiK P.hgen chiF).conductor / 2) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite
        F K P.ht P.hres P.piK P.hpiK P.hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  let htwild := P.t_pos_of_isWildlyRamified F K hwild
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite
      F K P.ht P.hres P.piK P.hpiK P.hgen
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩

  let chiMin := minimalOrbitRepresentative
    F K P.ht P.hres P.piK P.hpiK P.hgen chiF
  have hminConductor : IsMultiplicativeConductor F
      chiMin.character chiMin.conductor :=
    minimalOrbitRepresentative_isConductor
      F K P.ht P.hres P.piK P.hpiK P.hgen chiF
  have hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiMin :=
    minimalOrbitRepresentative_isMinimal
      F K P.ht P.hres P.piK P.hpiK P.hgen chiF
  change P.t + 1 ≤ chiMin.conductor / 2 at hstable

  let d := chiMin.conductor / 2
  let epsilon := chiMin.conductor % 2
  have hd : P.t + 1 ≤ d := hstable
  have hm : 1 < chiMin.conductor := by
    dsimp only [d] at hd
    omega
  have hF : IsStationaryConductorDecomposition
      chiMin.conductor d epsilon :=
    wildStablePreparation_conductorDecomposition hm
  have hstrict : P.t + 1 < chiMin.conductor := by
    rw [hF.conductor_eq]
    omega

  let chiK := wildStablePreparationNormPullbackData
    F K P chiMin hstrict
  let psiK := wildStablePreparationTracePullbackData F K P psiF
  have hchi : chiK.character = chiMin.character.compNorm := rfl
  have hpsi : psiK.character = psiF.character.compTrace := rfl
  have hmK : 1 < chiK.conductor := by
    rw [wildStablePreparationNormPullbackData_conductor]
    have hself := self_le_herbrandPsiNat P.t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos (chiMin.conductor - 1)
    omega

  let dK := chiK.conductor / 2
  let epsilonK := chiK.conductor % 2
  have hK : IsStationaryConductorDecomposition
      chiK.conductor dK epsilonK :=
    wildStablePreparation_conductorDecomposition hmK

  let GammaF : AdmissibleGamma F chiMin psiF :=
    Classical.choice (AdmissibleGamma.exists_admissible (F := F))
  let gammaF : Fˣ := GammaF
  have hgammaF : ord F (gammaF : F) =
      (((chiMin.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) :=
    GammaF.property
  let GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildStableNormCharacterData
          F K P.ht P.hres P.piK P.hpiK P.hgen htwild mu)
        psiF := fun _ ↦
    Classical.choice (AdmissibleGamma.exists_admissible (F := F))

  let H := highConductorParameter_stableOdd
    F K P.ht P.hres P.piK P.hpiK P.hgen
      chiMin chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF

  have hepsilonK : epsilonK = epsilon := by
    have hodd' := hodd
    rcases hodd' with ⟨k, hk⟩
    have hTm : P.t + 1 ≤ chiMin.conductor := by
      rw [hF.conductor_eq]
      omega
    let z : ℕ := k * (chiMin.conductor - (P.t + 1))
    have hmSplit :
        chiMin.conductor =
          (P.t + 1) + (chiMin.conductor - (P.t + 1)) :=
      (Nat.add_sub_of_le hTm).symm
    have hkSplit :
        k * chiMin.conductor = k * (P.t + 1) + z := by
      rw [hmSplit, mul_add]
    have hmKform : chiK.conductor = chiMin.conductor + 2 * z := by
      have hmrel := H.conductorRelation
      rw [hk] at hmrel
      have hs : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hs, add_mul, one_mul] at hmrel
      nlinarith [hkSplit]
    have heF := hF.epsilon_le_one
    have heK := hK.epsilon_le_one
    rw [hK.conductor_eq, hF.conductor_eq] at hmKform
    omega

  have hminIdentity : FirstMainIdentity F K DeltaF DeltaK
      chiMin.character psiF.character := by
    by_cases hepsilon : epsilon = 0
    · have hepsilonK0 : epsilonK = 0 := hepsilonK.trans hepsilon
      have hF0 : IsStationaryConductorDecomposition
          chiMin.conductor d 0 := by
        simpa only [hepsilon] using hF
      have hK0 : IsStationaryConductorDecomposition
          chiK.conductor dK 0 := by
        simpa only [hepsilonK0] using hK
      let H0 := highConductorParameter_stableOdd
        F K P.ht P.hres P.piK P.hpiK P.hgen
          chiMin chiK psiF psiK hF0 hK0 hchi hpsi hodd hd
            gammaF hgammaF
      obtain ⟨c0, hc0⟩ := latticeQuotientMk_surjective F (by omega)
        (stationaryCoefficientClass F chiMin psiF hF0 gammaF hgammaF)
      let R0 : StationaryClassRepresentative
          F chiMin psiF hF0 gammaF hgammaF :=
        StationaryClassRepresentative.ofCoefficientRepresentative c0 hc0
      let CF : LamprechtCriticalCoordinate F d 0 := .even
      let CK : LamprechtCriticalCoordinate K dK 0 := .even
      have C0 : WildStableResidualComparison
          F K P.ht P.hres P.piK P.hpiK P.hgen
            chiMin chiK psiF psiK hF0 hK0 hchi hpsi hodd hd
              gammaF hgammaF H0 R0 CF CK := by
        dsimp only [CF, CK, WildStableResidualComparison]
      exact firstMain_wildStable_minimal_of_isDeltaFinite
        F K P htwild chiMin chiK psiF psiK hF0 hK0 hchi hpsi hodd hd
          gammaF hgammaF R0 CF CK GammaNorm C0
            DeltaF DeltaK hDeltaF hDeltaK
    · have hepsilon1 : epsilon = 1 := by
        have := hF.epsilon_le_one
        omega
      have hepsilonK1 : epsilonK = 1 := hepsilonK.trans hepsilon1
      have hF1 : IsStationaryConductorDecomposition
          chiMin.conductor d 1 := by
        simpa only [hepsilon1] using hF
      have hK1 : IsStationaryConductorDecomposition
          chiK.conductor dK 1 := by
        simpa only [hepsilonK1] using hK
      let H1 := highConductorParameter_stableOdd
        F K P.ht P.hres P.piK P.hpiK P.hgen
          chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
            gammaF hgammaF
      obtain ⟨c1, hc1⟩ := latticeQuotientMk_surjective F (by omega)
        (stationaryCoefficientClass F chiMin psiF hF1 gammaF hgammaF)
      let R1 : StationaryClassRepresentative
          F chiMin psiF hF1 gammaF hgammaF :=
        StationaryClassRepresentative.ofCoefficientRepresentative c1 hc1
      let deltaF := phaseReductionSourceCoordinate F
        (ramifiedHasseLowerUniformizer F K P) d
      let deltaK := phaseReductionSourceCoordinate K
        (ramifiedHasseUpperUniformizer F K P) dK
      have hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ) :=
        phaseReductionSourceCoordinate_order F
          (ramifiedHasseLowerUniformizer F K P)
          (ramifiedHasseLowerUniformizer_order F K P) d
      have hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ) :=
        phaseReductionSourceCoordinate_order K
          (ramifiedHasseUpperUniformizer F K P)
          (ramifiedHasseUpperUniformizer_order F K P) dK
      let CF : LamprechtCriticalCoordinate F d 1 := .odd deltaF hdeltaF
      let CK : LamprechtCriticalCoordinate K dK 1 := .odd deltaK hdeltaK
      have C1 : WildStableResidualComparison
          F K P.ht P.hres P.piK P.hpiK P.hgen
            chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
              gammaF hgammaF H1 R1 CF CK := by
        exact ⟨ramifiedHassePreparation F K P
          chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
            gammaF hgammaF H1 R1⟩
      exact firstMain_wildStable_minimal_of_isDeltaFinite
        F K P htwild chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
          gammaF hgammaF R1 CF CK GammaNorm C1
            DeltaF DeltaK hDeltaF hDeltaK

  obtain ⟨mu, hmu⟩ := minimalOrbitRepresentative_mem_orbit
    F K P.ht P.hres P.piK P.hpiK P.hgen chiF
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

end WildStablePreparation

end

end LanglandsFirstMainLemma
