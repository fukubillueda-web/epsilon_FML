import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Parameters.RamifiedHassePreparation
import LanglandsFirstMainLemma.Cases.TameOdd
import LanglandsFirstMainLemma.Delta.ErrorTerm

/-!
# Preparation for the tamely ramified odd-degree case

This file is the dispatch boundary around the four completed tame-odd
computations. Starting from an arbitrary downstairs quasi-character, it
selects the least-conductor member of the complete norm-character orbit and
splits its actual conductor into the manuscript's three endpoint/range cases:
zero, one, and greater than one. Stationary data are constructed only in the
last range.

For high conductor, the source and pullback conductors are decomposed by
their literal quotient and remainder modulo two. The denominator is an
actual admissible denominator, the stationary representative is chosen as a
preimage of the actual coefficient quotient class, and the odd branch uses
the source uniformizer coordinates in `ramifiedHassePreparation`. Thus the
elementary stationary value, representative translation, and residual Hasse
phase remain the compatible package supplied by the completed high APIs.

Each computational product is bridged with
`firstMainIdentity_of_deltaFinite_product`, including the trivial norm
character. The proved left- and right-side norm-character invariances then
transport the identity from the selected representative back to the original
character.

Source: Proposition `prop:tame-odd-new` and Section
`sec:first-main-completion` in `references/epsilon_FML.tex`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

/- The endpoint computation keeps these two character-identification lemmas
private because they expose an implementation detail of its exact conductor
packages. The preparation layer needs only their stated character
equalities, not the private package implementation. -/
open private tameOddNormCharacterData_character
  tameOddEndpointZeroTwistData_character
  from LanglandsFirstMainLemma.Cases.TameOdd

local instance tameOddPreparation_degreePrime
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-! ## Actual pullback and stationary packages -/

section ActualPackages

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The exact norm pullback package. Its conductor is the canonical least
exact conductor of the literal pullback character; no conductor formula is
inserted into this definition. -/
private noncomputable def tameOddPreparationNormPullbackData
    (chiF : LocalQuasiCharData F) : LocalQuasiCharData K where
  character := chiF.character.compNorm
  conductor := multiplicativeConductorExponent K chiF.character.compNorm
  isConductor :=
    multiplicativeConductorExponent_isConductor K chiF.character.compNorm

@[simp]
private theorem tameOddPreparationNormPullbackData_character
    (chiF : LocalQuasiCharData F) :
    (tameOddPreparationNormPullbackData F K chiF).character =
      chiF.character.compNorm :=
  rfl

/-- The literal div/mod stationary decomposition at an actual conductor.
This helper is deliberately unavailable at conductors zero and one. -/
private theorem tameOddPreparation_conductorDecomposition
    {m : ℕ} (hm : 1 < m) :
    IsStationaryConductorDecomposition m (m / 2) (m % 2) where
  conductor_gt_one := hm
  epsilon_le_one := by omega
  conductor_eq := by omega

/-- Choose an actual admissible denominator from the certified existence
theorem. Its subtype property is the exact conductor-sum valuation used by
the parameter and local-constant consumers. -/
private noncomputable def tameOddPreparationGamma
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E) :
    AdmissibleGamma E chi psi :=
  Classical.choice (AdmissibleGamma.exists_admissible (F := E))

/-- Choose a representative only by taking a preimage of the actual
stationary coefficient quotient class. The equality retained in the
result is precisely the equality to `stationaryCoefficientClass`; no
unrelated field representative is substituted. -/
private noncomputable def tameOddPreparationStationaryRepresentative
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi) :
    StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property := by
  let hex := latticeQuotientMk_surjective E
    (show (0 : ℤ) ≤ (d : ℤ) by omega)
    (stationaryCoefficientClass E chi psi h
      (Gamma : Eˣ) Gamma.property)
  let representative := Classical.choose hex
  have hrepresentative := Classical.choose_spec hex
  exact StationaryClassRepresentative.ofCoefficientRepresentative
    representative hrepresentative

end ActualPackages

/-! ## Fixed-character delta-product bridges -/

section ProductBridges

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

/-! ### Conductor zero -/

/-- Exact computational packages for the conductor-zero endpoint. The
complete norm-character type is used, so its identity row is retained with
conductor zero. -/
private noncomputable def tameOddPreparationZeroComputationalData
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F) [Finite (NormCharacter F K)] :
    FirstMainComputationalData F K chiF.character psiF.character where
  baseAddChar := psiF
  baseAddChar_character := rfl
  extensionQuasiChar :=
    tameOddNormPullbackZeroData F K ht hres piK hpiK hgen chiF hchiF
  extensionQuasiChar_character := rfl
  extensionAddChar :=
    tameOddTracePullbackData F K ht hres piK hpiK hgen psiF
  extensionAddChar_character := rfl
  normCharacterData :=
    tameOddNormCharacterData F K ht hres piK hpiK hgen
  normCharacterData_character := fun mu ↦
    tameOddNormCharacterData_character F K ht hres piK hpiK hgen mu
  twistData :=
    tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF
  twistData_character := fun mu ↦
    tameOddEndpointZeroTwistData_character
      F K ht hres piK hpiK hgen chiF hchiF mu

/-- Bridge the completed conductor-zero tame-odd computation to the literal
fixed-character First Main identity. -/
private theorem firstMain_tameOdd_zero_of_isDeltaFinite
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (hodd : Odd (Module.finrank F K))
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let data := tameOddPreparationZeroComputationalData
    F K ht hres piK hpiK hgen chiF hchiF psiF
  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chiF.character psiF.character data
    (tameOddUniformizerGamma K
      data.extensionQuasiChar data.extensionAddChar
      (tameOddUpperUniformizer K piK hpiK)
      (by simpa [tameOddUpperUniformizer] using hpiK))
    (fun mu ↦ tameOddUniformizerGamma F
      (data.normCharacterData mu) data.baseAddChar
      (tameOddLowerUniformizer F K piK hpiK)
      (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK))
    (fun mu ↦ tameOddUniformizerGamma F
      (data.twistData mu) data.baseAddChar
      (tameOddLowerUniformizer F K piK hpiK)
      (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK))
  simpa only [data, tameOddPreparationZeroComputationalData,
    tameOddEndpointDelta, ramifiedNormCharacterFinset,
    normCharacterFinset] using
      (firstMain_tameOdd_zero F K ht hres piK hpiK hgen hodd
        chiF hchiF psiF)

/-! ### Conductor one -/

/-- The exact norm, trace, norm-character, and orbit-twist packages appearing
in the completed conductor-one computation. -/
private noncomputable def tameOddPreparationOneComputationalData
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace)
    [Finite (NormCharacter F K)] :
    FirstMainComputationalData F K chiF.character psiF.character where
  baseAddChar := psiF
  baseAddChar_character := rfl
  extensionQuasiChar := chiK
  extensionQuasiChar_character := hcomp
  extensionAddChar := psiK
  extensionAddChar_character := htrace
  normCharacterData :=
    TameOddConductorOne.normData F K ht hres piK hpiK hgen
  normCharacterData_character :=
    TameOddConductorOne.normData_character F K ht hres piK hpiK hgen
  twistData :=
    TameOddConductorOne.twistData F K ht hres piK hpiK hgen chiF
  twistData_character :=
    TameOddConductorOne.twistData_character
      F K ht hres piK hpiK hgen chiF

/-- Bridge the completed conductor-one tame-odd computation to the literal
fixed-character First Main identity. -/
private theorem firstMain_tameOdd_one_of_isDeltaFinite
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K)) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let data := tameOddPreparationOneComputationalData
    F K ht hres piK hpiK hgen chiF chiK hcomp psiF psiK htrace
  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chiF.character psiF.character data
    (TameOddConductorOne.gammaK F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hminimal hcomp htrace (by omega))
    (TameOddConductorOne.normGammaActual
      F K ht hres piK hpiK hgen psiF)
    (TameOddConductorOne.twistGammaActual
      F K ht hres piK hpiK hgen chiF psiF)
  simpa only [data, tameOddPreparationOneComputationalData,
    ramifiedNormCharacterFinset, normCharacterFinset] using
      (firstMain_tameOdd_one F K ht hres piK hpiK hgen
        chiF hchiF hminimal chiK hcomp psiF psiK htrace hodd)

/-! ### High conductor -/

/-- Exact computational packages for a stable high tame-odd row. The actual
stable twist data have the unchanged high conductor and the literal
left-oriented character `mu * chiF`. -/
private noncomputable def tameOddPreparationHighComputationalData
    (chiF : LocalQuasiCharData F) (hlarge : 1 < chiF.conductor)
    (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    [Finite (NormCharacter F K)] :
    FirstMainComputationalData F K chiF.character psiF.character where
  baseAddChar := psiF
  baseAddChar_character := rfl
  extensionQuasiChar := chiK
  extensionQuasiChar_character := hchi
  extensionAddChar := psiK
  extensionAddChar_character := hpsi
  normCharacterData := TameOddHigh.normData F K ht hres piK hpiK hgen
  normCharacterData_character :=
    TameOddHigh.normData_character F K ht hres piK hpiK hgen
  twistData :=
    TameOddHigh.twistData F K ht hres piK hpiK hgen chiF hlarge
  twistData_character :=
    TameOddHigh.twistData_character
      F K ht hres piK hpiK hgen chiF hlarge

/-- Bridge the completed stable-high even tame-odd computation to the
literal fixed-character First Main identity. -/
private theorem firstMain_tameOdd_high_even_of_isDeltaFinite
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d dK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d 0)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK 0)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighStableOddParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d 0)
    (CK : LamprechtCriticalCoordinate K dK 0)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (TameOddHigh.normData F K ht hres piK hpiK hgen mu) psiF) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let phases := HighStableOddParameterData.compatiblePhasePair
    F K ht hres piK hpiK hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R CF CK
  let data := tameOddPreparationHighComputationalData
    F K ht hres piK hpiK hgen chiF hF.conductor_gt_one
      chiK hchi psiF psiK hpsi
  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chiF.character psiF.character data
    phases.upstairs.gamma GammaNorm
    (TameOddHigh.twistGamma F K ht hres piK hpiK hgen
      chiF hF.conductor_gt_one psiF GammaF)
  simpa only [data, tameOddPreparationHighComputationalData,
    GammaF, phases] using
      (firstMain_tameOdd_high_even F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd
          gammaF hgammaF H R CF CK GammaNorm)

/-- Bridge the completed stable-high odd tame-odd computation to the literal
fixed-character First Main identity. The supplied comparison certificate
is already tied to the same representative, denominator pair, and source
coordinates as the computational theorem. -/
private theorem firstMain_tameOdd_high_odd_of_isDeltaFinite
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d dK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d 1)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK 1)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighStableOddParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d 1)
    (CK : LamprechtCriticalCoordinate K dK 1)
    {ell : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      (HighStableOddParameterData.downstairsOddStationaryPhase
        F K ht hres piK hpiK hgen chiF chiK psiF psiK
          hF hK hchi hpsi hodd hd gammaF hgammaF H R
            (TameOddHigh.oddCriticalDelta CF)
            (TameOddHigh.oddCriticalDelta_order CF))
      (HighStableOddParameterData.upstairsOddStationaryPhase
        F K ht hres piK hpiK hgen chiF chiK psiF psiK
          hF hK hchi hpsi hodd hd gammaF hgammaF H R
            (TameOddHigh.oddCriticalDelta CK)
            (TameOddHigh.oddCriticalDelta_order CK))
      ell 0)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (TameOddHigh.normData F K ht hres piK hpiK hgen mu) psiF) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let phases := HighStableOddParameterData.compatiblePhasePair
    F K ht hres piK hpiK hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R CF CK
  let data := tameOddPreparationHighComputationalData
    F K ht hres piK hpiK hgen chiF hF.conductor_gt_one
      chiK hchi psiF psiK hpsi
  apply firstMainIdentity_of_deltaFinite_product F K
    DeltaF DeltaK hDeltaF hDeltaK chiF.character psiF.character data
    phases.upstairs.gamma GammaNorm
    (TameOddHigh.twistGamma F K ht hres piK hpiK hgen
      chiF hF.conductor_gt_one psiF GammaF)
  simpa only [data, tameOddPreparationHighComputationalData,
    GammaF, phases] using
      (firstMain_tameOdd_high_odd F K ht hres piK hpiK hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd
          gammaF hgammaF H R CF CK D GammaNorm)

end ProductBridges

/-! ## Stable-high conductor parity -/

section HighParity

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ}
  (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

/-- Odd extension degree and the exact stable-high conductor relation force
the actual source and pullback remainders to agree. This derives parity
from the two decompositions and does not assume it as an input. -/
private theorem tameOddPreparation_conductorParity_eq
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : t + 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighStableOddParameterData F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF) :
    epsilonK = epsilon := by
  have hodd' := hodd
  rcases hodd' with ⟨k, hk⟩
  have hTm : t + 1 ≤ chiF.conductor := by
    rw [hF.conductor_eq]
    omega
  let z : ℕ := k * (chiF.conductor - (t + 1))
  have hmSplit :
      chiF.conductor = (t + 1) + (chiF.conductor - (t + 1)) :=
    (Nat.add_sub_of_le hTm).symm
  have hkSplit : k * chiF.conductor = k * (t + 1) + z := by
    rw [hmSplit, mul_add]
  have hmKform : chiK.conductor = chiF.conductor + 2 * z := by
    have hmrel := H.conductorRelation
    rw [hk] at hmrel
    have hs : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hs, add_mul, one_mul] at hmrel
    nlinarith [hkSplit]
  have heF := hF.epsilon_le_one
  have heK := hK.epsilon_le_one
  rw [hK.conductor_eq, hF.conductor_eq] at hmKform
  omega

end HighParity

/-! ## Dispatch-ready routing theorem -/

section TameOddPreparation

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- **First Main Lemma, prepared tamely ramified odd-degree branch.**

The selected `chiMin` retains its exact conductor proof, whole-orbit
minimality, and explicit orbit membership. Conductors zero and one go
directly to their endpoint computations. Only a conductor greater than one
creates the div/mod stationary decompositions, quotient representative, and
stable-high parameters. In the odd high branch the ramified Hasse producer
is used with the literal lower and upper source uniformizer coordinates.
Finally the fixed-character result is transported through the actual orbit
element taking `chiF` to `chiMin`. -/
theorem firstMain_tameOdd_of_isDeltaFinite
    (P : PrimeCyclicPreparation F K)
    (htame : IsTamelyRamified F K)
    (hodd : Odd (Module.finrank F K))
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite
        F K P.ht P.hres P.piK P.hpiK P.hgen
    FirstMainIdentity F K DeltaF DeltaK
      chiF.character psiF.character := by
  let ht0 := P.isLowerBreak_zero_of_isTamelyRamified F K htame
  have htzero : P.t = 0 :=
    P.t_eq_zero_of_isTamelyRamified F K htame
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite
      F K ht0 P.hres P.piK P.hpiK P.hgen

  let chiMin := minimalOrbitRepresentative
    F K ht0 P.hres P.piK P.hpiK P.hgen chiF
  have hchiMinConductor : IsMultiplicativeConductor F
      chiMin.character chiMin.conductor :=
    minimalOrbitRepresentative_isConductor
      F K ht0 P.hres P.piK P.hpiK P.hgen chiF
  have hminimal :
      IsMinimalNormCharacterOrbitRepresentative F K chiMin :=
    minimalOrbitRepresentative_isMinimal
      F K ht0 P.hres P.piK P.hpiK P.hgen chiF
  have hmemOrbit : ∃ mu : NormCharacter F K,
      chiMin.character = mu.1 * chiF.character :=
    minimalOrbitRepresentative_mem_orbit
      F K ht0 P.hres P.piK P.hpiK P.hgen chiF

  have hminIdentity : FirstMainIdentity F K DeltaF DeltaK
      chiMin.character psiF.character := by
    by_cases hzero : chiMin.conductor = 0
    · exact firstMain_tameOdd_zero_of_isDeltaFinite
        F K ht0 P.hres P.piK P.hpiK P.hgen
          DeltaF DeltaK hDeltaF hDeltaK hodd chiMin hzero psiF
    · by_cases hone : chiMin.conductor = 1
      · let chiK := tameOddPreparationNormPullbackData F K chiMin
        let psiK := tameOddTracePullbackData
          F K ht0 P.hres P.piK P.hpiK P.hgen psiF
        have hchi : chiK.character = chiMin.character.compNorm := rfl
        have hpsi : psiK.character = psiF.character.compTrace := rfl
        exact firstMain_tameOdd_one_of_isDeltaFinite
          F K ht0 P.hres P.piK P.hpiK P.hgen
            DeltaF DeltaK hDeltaF hDeltaK chiMin hone hminimal
              chiK hchi psiF psiK hpsi hodd
      · have hlarge : 1 < chiMin.conductor := by omega
        let d := chiMin.conductor / 2
        let epsilon := chiMin.conductor % 2
        have hF : IsStationaryConductorDecomposition
            chiMin.conductor d epsilon :=
          tameOddPreparation_conductorDecomposition hlarge

        let chiK := tameOddPreparationNormPullbackData F K chiMin
        let psiK := tameOddTracePullbackData
          F K ht0 P.hres P.piK P.hpiK P.hgen psiF
        have hchi : chiK.character = chiMin.character.compNorm := rfl
        have hpsi : psiK.character = psiF.character.compTrace := rfl
        have hmK : 1 < chiK.conductor := by
          have hconductorK := highParameter_ramified_conductor_eq
            F K ht0 P.hres P.piK P.hpiK P.hgen
              chiMin chiK hchi (by omega)
          rw [hconductorK]
          have hp := (PrimeCyclicExtension.degree_prime F K).pos
          have hself := self_le_herbrandPsiNat 0
            (Module.finrank F K) hp (chiMin.conductor - 1)
          omega
        let dK := chiK.conductor / 2
        let epsilonK := chiK.conductor % 2
        have hK : IsStationaryConductorDecomposition
            chiK.conductor dK epsilonK :=
          tameOddPreparation_conductorDecomposition hmK

        let GammaF : AdmissibleGamma F chiMin psiF :=
          tameOddPreparationGamma F chiMin psiF
        let gammaF : Fˣ := (GammaF : Fˣ)
        have hgammaF : ord F (gammaF : F) =
            (((chiMin.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) :=
          GammaF.property
        have hd : 1 ≤ d := hF.floorDepth_pos
        let H := highConductorParameter_stableOdd
          F K ht0 P.hres P.piK P.hpiK P.hgen
            chiMin chiK psiF psiK hF hK hchi hpsi hodd hd
              gammaF hgammaF
        let GammaNorm : ∀ mu : NormCharacter F K,
            AdmissibleGamma F
              (TameOddHigh.normData
                F K ht0 P.hres P.piK P.hpiK P.hgen mu) psiF :=
          fun mu ↦ tameOddPreparationGamma F
            (TameOddHigh.normData
              F K ht0 P.hres P.piK P.hpiK P.hgen mu) psiF

        have hepsilonK : epsilonK = epsilon :=
          tameOddPreparation_conductorParity_eq
            F K ht0 P.hres P.piK P.hpiK P.hgen
              chiMin chiK psiF psiK hF hK hchi hpsi hodd hd
                gammaF hgammaF H
        have hepsilonCases : epsilon = 0 ∨ epsilon = 1 := by
          have hepsilonBound := hF.epsilon_le_one
          omega
        rcases hepsilonCases with hepsilon | hepsilon
        · have hepsilonF0 : chiMin.conductor % 2 = 0 := by
            simpa only [epsilon] using hepsilon
          have hepsilonK0 : chiK.conductor % 2 = 0 := by
            change epsilonK = 0
            exact hepsilonK.trans hepsilon
          have hF0 : IsStationaryConductorDecomposition
              chiMin.conductor d 0 := by
            simpa only [d, hepsilonF0] using
              (tameOddPreparation_conductorDecomposition hlarge)
          have hK0 : IsStationaryConductorDecomposition
              chiK.conductor dK 0 := by
            simpa only [dK, hepsilonK0] using
              (tameOddPreparation_conductorDecomposition hmK)
          let H0 := highConductorParameter_stableOdd
            F K ht0 P.hres P.piK P.hpiK P.hgen
              chiMin chiK psiF psiK hF0 hK0 hchi hpsi hodd hd
                gammaF hgammaF
          let R0 : StationaryClassRepresentative F chiMin psiF hF0
              gammaF hgammaF :=
            tameOddPreparationStationaryRepresentative
              F chiMin psiF hF0 GammaF
          let CF : LamprechtCriticalCoordinate F d 0 := .even
          let CK : LamprechtCriticalCoordinate K dK 0 := .even
          exact firstMain_tameOdd_high_even_of_isDeltaFinite
            F K ht0 P.hres P.piK P.hpiK P.hgen
              DeltaF DeltaK hDeltaF hDeltaK chiMin chiK psiF psiK
                hF0 hK0 hchi hpsi hodd hd gammaF hgammaF H0 R0
                  CF CK GammaNorm
        · have hepsilonF1 : chiMin.conductor % 2 = 1 := by
            simpa only [epsilon] using hepsilon
          have hepsilonK1 : chiK.conductor % 2 = 1 := by
            change epsilonK = 1
            exact hepsilonK.trans hepsilon
          have hF1 : IsStationaryConductorDecomposition
              chiMin.conductor d 1 := by
            simpa only [d, hepsilonF1] using
              (tameOddPreparation_conductorDecomposition hlarge)
          have hK1 : IsStationaryConductorDecomposition
              chiK.conductor dK 1 := by
            simpa only [dK, hepsilonK1] using
              (tameOddPreparation_conductorDecomposition hmK)
          let H1 := highConductorParameter_stableOdd
            F K ht0 P.hres P.piK P.hpiK P.hgen
              chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
                gammaF hgammaF
          let R1 : StationaryClassRepresentative F chiMin psiF hF1
              gammaF hgammaF :=
            tameOddPreparationStationaryRepresentative
              F chiMin psiF hF1 GammaF
          let deltaF := phaseReductionSourceCoordinate F
            (ramifiedHasseLowerUniformizer F K P) d
          let deltaK := phaseReductionSourceCoordinate K
            (ramifiedHasseUpperUniformizer F K P) dK
          have hdeltaF : ord F (deltaF : F) =
              ((d : ℤ) : WithTop ℤ) :=
            phaseReductionSourceCoordinate_order F
              (ramifiedHasseLowerUniformizer F K P)
              (ramifiedHasseLowerUniformizer_order F K P) d
          have hdeltaK : ord K (deltaK : K) =
              ((dK : ℤ) : WithTop ℤ) :=
            phaseReductionSourceCoordinate_order K
              (ramifiedHasseUpperUniformizer F K P)
              (ramifiedHasseUpperUniformizer_order F K P) dK
          let CF : LamprechtCriticalCoordinate F d 1 :=
            .odd deltaF hdeltaF
          let CK : LamprechtCriticalCoordinate K dK 1 :=
            .odd deltaK hdeltaK

          have hdP : P.t + 1 ≤ d := by
            rw [htzero]
            exact hd
          have HP : HighStableOddParameterData
              F K P.ht P.hres P.piK P.hpiK P.hgen
                chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hdP
                  gammaF hgammaF := by
            simpa only [htzero] using H1
          have D : RamifiedHasseComparisonData
              F K chiMin psiF chiK psiK
              (HighStableOddParameterData.downstairsOddStationaryPhase
                F K ht0 P.hres P.piK P.hpiK P.hgen
                  chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
                    gammaF hgammaF H1 R1 deltaF hdeltaF)
              (HighStableOddParameterData.upstairsOddStationaryPhase
                F K ht0 P.hres P.piK P.hpiK P.hgen
                  chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hd
                    gammaF hgammaF H1 R1 deltaK hdeltaK)
              (Module.finrank F K) 0 := by
            have D' := ramifiedHassePreparation
              F K P chiMin chiK psiF psiK hF1 hK1 hchi hpsi hodd hdP
                gammaF hgammaF HP R1
            simpa only [htzero] using D'
          exact firstMain_tameOdd_high_odd_of_isDeltaFinite
            F K ht0 P.hres P.piK P.hpiK P.hgen
              DeltaF DeltaK hDeltaF hDeltaK chiMin chiK psiF psiK
                hF1 hK1 hchi hpsi hodd hd gammaF hgammaF H1 R1
                  CF CK D GammaNorm

  obtain ⟨mu, hmu⟩ := hmemOrbit
  unfold FirstMainIdentity at hminIdentity ⊢
  calc
    firstMainLeftSide F K DeltaF DeltaK chiF.character psiF.character =
        firstMainLeftSide F K DeltaF DeltaK
          (mu.1 * chiF.character) psiF.character :=
      (firstMainLeftSide_normCharacter_mul
        F K DeltaF DeltaK mu chiF.character psiF.character).symm
    _ = firstMainLeftSide F K DeltaF DeltaK
          chiMin.character psiF.character := by rw [hmu]
    _ = firstMainRightSide F K DeltaF
          chiMin.character psiF.character :=
      hminIdentity
    _ = firstMainRightSide F K DeltaF
          (mu.1 * chiF.character) psiF.character := by rw [hmu]
    _ = firstMainRightSide F K DeltaF
          chiF.character psiF.character :=
      firstMainRightSide_normCharacter_mul
        F K DeltaF mu chiF.character psiF.character

end TameOddPreparation

end

end LanglandsFirstMainLemma
