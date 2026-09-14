import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Cases.WildQuadratic.CoefficientTable
import LanglandsFirstMainLemma.Cases.WildQuadratic.ErrorFormula
import LanglandsFirstMainLemma.Cases.WildQuadratic.CoordinateTransport
import LanglandsFirstMainLemma.Cases.WildQuadratic.LowCoordinateTransport
import LanglandsFirstMainLemma.Cases.WildQuadratic.LowProductCoordinateTransport
import LanglandsFirstMainLemma.Cases.WildQuadratic.HighCoordinateTransport
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Cases.WildQuadratic.Main

namespace LanglandsFirstMainLemma

noncomputable section

private theorem stationaryConductorDecomposition_div_mod
    {m : ℕ} (hm : 1 < m) :
    IsStationaryConductorDecomposition m (m / 2) (m % 2) where
  conductor_gt_one := hm
  epsilon_le_one := by omega
  conductor_eq := by omega

/-- A unit of any prescribed finite valuation, used only for the literal
denominators demanded by the high and low parameter constructors. -/
private noncomputable def wildQuadraticPreparationUnitOfOrd
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (a : ℤ) : Eˣ :=
  Units.mk0 (Classical.choose (exists_ord_eq E a))
    ((ord_ne_top_iff E).1 (by
      rw [(Classical.choose_spec (exists_ord_eq E a))]
      exact WithTop.coe_ne_top))

private theorem wildQuadraticPreparationUnitOfOrd_order
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (a : ℤ) :
    ord E (wildQuadraticPreparationUnitOfOrd E a : E) =
      (a : WithTop ℤ) :=
  Classical.choose_spec (exists_ord_eq E a)

/-- Parity of the actual conductor determines the constructor of a supplied
stationary Lamprecht row. -/
private theorem LocalLamprechtPhaseData.isEven_of_even_conductor
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (S : LocalLamprechtPhaseData E chi psi) (h : Even chi.conductor) :
    S.IsEven := by
  cases S with
  | even => trivial
  | odd d hm =>
      obtain ⟨j, hj⟩ := h
      simp only [LocalLamprechtPhaseData.IsEven]
      omega

@[simp]
private theorem selectedStationaryPair_transport
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi' : LocalQuasiCharData E} {psi psi' : LocalAddCharData E}
    (hchi : chi.character = chi'.character)
    (hpsi : psi.character = psi'.character)
    (S : LocalLamprechtPhaseData E chi psi) :
    (transportLocalLamprechtPhaseData hchi hpsi S).selectedStationaryPair =
      S.selectedStationaryPair := by
  have hc : chi = chi' := LocalQuasiCharData.ext_character E hchi
  have hp : psi = psi' := LocalAddCharData.ext_character hpsi
  subst chi'
  subst psi'
  rfl

@[simp]
private theorem selectedStationaryPair_localPhaseOfStationaryClass
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon) :
    (localPhaseOfStationaryClass h Gamma R C).selectedStationaryPair =
      { gamma := Gamma, beta := (R.representative : E) } := by
  cases C <;> rfl

/--
The q-free output of wild-quadratic phase preparation.  The three all-even
rows already contain everything required by `WildQuadraticHigherData.allEven`.
Every other row retains an actual positive-polar quotient source together
with the common phase package, but no characteristic-two refinement.
-/
inductive WildQuadraticPhasePrepared
    (F K : Type)
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
    (t : ℕ) (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) : Type
  | allEven
      (view : WildQuadraticAllEvenCoefficientView F K t chiF.conductor)
      (common : WildQuadraticCommonHigherData F K t chiF psiF view.toCommon)
      (rows : WildQuadraticAllEvenPhaseRowCompatibility view common.data
        common.phaseData common.assembly)
      (completeCorrection : common.assembly.CompleteCorrectionData)
  | needsRefinement
      (view : WildQuadraticCommonCoefficientView F K t chiF.conductor)
      (source : view.criticalInputs.PositivePolarSource)
      (common : WildQuadraticCommonHigherData F K t chiF psiF view)
      (rows : WildQuadraticActualPhaseRows view common.data common.phaseData
        common.assembly)
      (continuation : WildQuadraticPositivePolarContinuation F K view source
        rows)

/-- Forget the preparation wrapper in the all-even branch.  This is the
literal q-free constructor consumed by the completed higher calculation. -/
def WildQuadraticPhasePrepared.allEvenHigherData
    {F K : Type}
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
    {t : ℕ} {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    (P : WildQuadraticPhasePrepared F K t chiF psiF) :
    Option (WildQuadraticHigherData F K t chiF psiF) :=
  match P with
  | .allEven view common rows completeCorrection =>
      some (.allEven view common rows completeCorrection)
  | .needsRefinement _ _ _ _ _ => none

/-- Internal common target of the low and strict-high constructors. -/
private structure WildQuadraticQFreePhasePackage
    (F K : Type)
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
    (t : ℕ) (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) where
  view : WildQuadraticCommonCoefficientView F K t chiF.conductor
  common : WildQuadraticCommonHigherData F K t chiF psiF view
  rows : WildQuadraticActualPhaseRows view common.data common.phaseData
    common.assembly
  continuation : ∀ source : view.criticalInputs.PositivePolarSource,
    WildQuadraticPositivePolarContinuation F K view source rows

/-- The exact character data shared by the low and high constructions. -/
private noncomputable def wildQuadraticPreparationComputationalData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    FirstMainComputationalData F K chiF.character psiF.character where
  baseAddChar := psiF
  baseAddChar_character := rfl
  extensionQuasiChar := chiK
  extensionQuasiChar_character := hchi
  extensionAddChar := psiK
  extensionAddChar_character := hpsi
  normCharacterData := wildNormCharacterData F K ht hres pi hpi hgen
  normCharacterData_character :=
    wildNormCharacterData_character F K ht hres pi hpi hgen
  twistData := fun mu => by
    classical
    exact if mu = 1 then chiF else
      ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chiF mu
  twistData_character := by
    classical
    intro mu
    by_cases hmu : mu = 1
    · subst mu
      simp only [if_pos, NormCharacter.coe_one]
      ext z
      simp
    · simp only [hmu, ↓reduceIte]
      exact ramifiedNormCharacterOrbitTwistData_character
        F K ht hres pi hpi hgen chiF mu

@[simp]
private theorem wildQuadraticPreparationComputationalData_twist_one
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    (wildQuadraticPreparationComputationalData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hchi hpsi).twistData 1 = chiF := by
  classical
  simp [wildQuadraticPreparationComputationalData]

private theorem normCharacter_eq_tau_of_ne_one
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (tau mu : NormCharacter F K)
    (index : Bool ≃ NormCharacter F K)
    (index_true : index true = 1) (index_false : index false = tau)
    (hmu : mu ≠ 1) : mu = tau := by
  have hsymm : index.symm mu = false := by
    cases h : index.symm mu with
    | false => rfl
    | true =>
        exfalso
        apply hmu
        calc
          mu = index (index.symm mu) := (index.apply_symm_apply mu).symm
          _ = index true := congrArg index h
          _ = 1 := index_true
  calc
    mu = index (index.symm mu) := (index.apply_symm_apply mu).symm
    _ = index false := congrArg index hsymm
    _ = tau := index_false

/-- Insert the four actual stationary rows into the full two-character phase
package.  The identity norm character remains the genuine conductor-zero
endpoint and receives no stationary representative. -/
private noncomputable def wildQuadraticPreparationPhaseData
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (tau : NormCharacter F K)
    (index : Bool ≃ NormCharacter F K)
    (index_true : index true = 1) (index_false : index false = tau)
    (extension : LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar)
    (tauRow : LocalLamprechtPhaseData F (data.normCharacterData tau)
      data.baseAddChar)
    (base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar)
    (twist : LocalLamprechtPhaseData F (data.twistData tau)
      data.baseAddChar) :
    FirstMainPhaseData F K globalChi globalPsi data where
  extension := .stationary extension
  normCharacter := fun mu => by
    by_cases hmu : mu = 1
    · subst mu
      have hdata : data.normCharacterData 1 = trivialQuasiCharData F := by
        apply LocalQuasiCharData.ext_character F
        rw [data.normCharacterData_character]
        ext z
        simp
      have hcond : (data.normCharacterData 1).conductor ≤ 1 := by
        rw [hdata, trivialQuasiCharData_conductor]
        omega
      exact .endpoint hcond
        (Classical.choice AdmissibleGamma.exists_admissible)
    · have hmutau := normCharacter_eq_tau_of_ne_one tau mu index index_true
        index_false hmu
      subst mu
      exact .stationary tauRow
  twist := fun mu => by
    by_cases hmu : mu = 1
    · subst mu
      exact .stationary base
    · have hmutau := normCharacter_eq_tau_of_ne_one tau mu index index_true
        index_false hmu
      subst mu
      exact .stationary twist

/-! ## Low/high setup at the actual conductor -/

private structure WildQuadraticLowSetup
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF) where
  chiK : LocalQuasiCharData K
  psiK : LocalAddCharData K
  hchi : chiK.character = chiF.character.compNorm
  hpsi : psiK.character = psiF.character.compTrace
  hLow : chiF.conductor ≤ t + 1
  hF : IsStationaryConductorDecomposition chiF.conductor
    (chiF.conductor / 2) (chiF.conductor % 2)
  hK : IsStationaryConductorDecomposition chiK.conductor
    (chiK.conductor / 2) (chiK.conductor % 2)
  delta : Fˣ
  epsilon1 : Kˣ
  hdelta : ord F (delta : F) =
    ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)
  hepsilon1 : ord K (epsilon1 : K) =
    (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ)
  hT : 2 ≤ t + 1
  hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)
  hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
  selected : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth t) (chiF.conductor / 2)
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
    (stationaryCoefficientClass F chiF psiF hF
      (lowGammaF F K delta epsilon1) hgammaF)
  table : LowConductorParameterTableData F K ht hres pi hpi hgen
    chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon1
      hdelta hepsilon1 hT hgammaF hgammaK selected

private structure WildQuadraticHighSetup
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF) where
  chiK : LocalQuasiCharData K
  psiK : LocalAddCharData K
  hchi : chiK.character = chiF.character.compNorm
  hpsi : psiK.character = psiF.character.compTrace
  hstrict : t + 1 < chiF.conductor
  hhigh : t + 1 ≤ chiF.conductor
  hF : IsStationaryConductorDecomposition chiF.conductor
    (chiF.conductor / 2) (chiF.conductor % 2)
  hK : IsStationaryConductorDecomposition chiK.conductor
    (chiK.conductor / 2) (chiK.conductor % 2)
  tau : NormCharacter F K
  htau : tau ≠ 1
  gammaF : Fˣ
  hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)

private inductive WildQuadraticSetup
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF) : Type
  | low (setup : WildQuadraticLowSetup F K ht hres pi hpi hgen
      chiF psiF hminimal)
  | high (setup : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen
      hdegree chiF psiF hminimal)

private noncomputable def wildQuadraticPreparationSetup
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor) :
    WildQuadraticSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal := by
  let chiK : LocalQuasiCharData K :=
    canonicalLocalQuasiCharData K chiF.character.compNorm
  let psiK : LocalAddCharData K :=
    wildTracePullbackData F K ht hres pi hpi hgen psiF
  have hchi : chiK.character = chiF.character.compNorm := rfl
  have hpsi : psiK.character = psiF.character.compTrace := rfl
  let hF := stationaryConductorDecomposition_div_mod hm
  by_cases hLow : chiF.conductor ≤ t + 1
  · have hmK_eq : chiK.conductor = chiF.conductor :=
      lowCompNorm_conductor_eq F K ht hres pi hpi hgen chiF hminimal chiK
        hchi hLow
    have hmK : 1 < chiK.conductor := by omega
    let hK := stationaryConductorDecomposition_div_mod hmK
    let delta := wildQuadraticPreparationUnitOfOrd F
      (((t + 1 : ℕ) : ℤ) + psiF.conductor)
    let epsilon1 := wildQuadraticPreparationUnitOfOrd K
      ((t + 1 - chiF.conductor : ℕ) : ℤ)
    have hdelta : ord F (delta : F) =
        ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) :=
      wildQuadraticPreparationUnitOfOrd_order F _
    have hepsilon1 : ord K (epsilon1 : K) =
        (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ) :=
      wildQuadraticPreparationUnitOfOrd_order K _
    have hT : 2 ≤ t + 1 := by omega
    have hgammaF := lowGammaF_order (t := t) F K hres chiF psiF delta
      epsilon1 hdelta hepsilon1 hLow
    have hgammaK := lowGammaK_order F K ht hres pi hpi hgen chiF chiK
      psiF psiK hminimal hchi hpsi delta epsilon1 hdelta hepsilon1 hLow
    let hexists := lowConductorParameterTable F K ht hres pi hpi hgen
      chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon1
        hdelta hepsilon1
    let selected := Classical.choose hexists
    let table := Classical.choose_spec hexists
    exact .low
      { chiK := chiK, psiK := psiK, hchi := hchi, hpsi := hpsi,
        hLow := hLow, hF := hF, hK := hK, delta := delta,
        epsilon1 := epsilon1, hdelta := hdelta, hepsilon1 := hepsilon1,
        hT := hT, hgammaF := hgammaF, hgammaK := hgammaK,
        selected := selected, table := table }
  · have hstrict : t + 1 < chiF.conductor := by omega
    have hhigh : t + 1 ≤ chiF.conductor := hstrict.le
    have hrel := highParameter_wildQuadratic_conductor_relation F K ht hres
      pi hpi hgen hdegree chiF chiK hminimal hchi hhigh
    have hmK : 1 < chiK.conductor := by omega
    let hK := stationaryConductorDecomposition_div_mod hmK
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    have htau : tau ≠ 1 :=
      lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
    let gammaF := wildQuadraticPreparationUnitOfOrd F
      ((chiF.conductor : ℤ) + psiF.conductor)
    have hgammaF : ord F (gammaF : F) =
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) :=
      wildQuadraticPreparationUnitOfOrd_order F _
    exact .high
      { chiK := chiK, psiK := psiK, hchi := hchi, hpsi := hpsi,
        hstrict := hstrict, hhigh := hhigh, hF := hF, hK := hK,
        tau := tau, htau := htau, gammaF := gammaF,
        hgammaF := hgammaF }

/-! ## Q-free coefficient cores -/

/-- Low-range coefficient provenance with every refinement-dependent field
removed.  The simultaneous quotient representatives and actual lower
critical inputs remain part of the package. -/
private structure WildQuadraticLowCoefficientCore
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2] where
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
  chiK : LocalQuasiCharData K
  psi : LocalAddCharData F
  psiK : LocalAddCharData K
  hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi
  hchi : chiK.character = chi.character.compNorm
  hpsi : psiK.character = psi.character.compTrace
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
  hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
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
  table : LowConductorParameterTableData F K ht hres pi hpi hgen
    chi chiK psi psiK hminimal hchi hpsi hF hLow delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK selected
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

namespace WildQuadraticLowCoefficientCore

private noncomputable def correction
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (P : WildQuadraticLowCoefficientCore F K) :
    WildQuadraticCommonCorrectionData F K (P.lowerBreak + 1)
      P.chi.conductor :=
  lowWildQuadraticCommonCorrection P.ht P.hres P.pi P.hpi P.hgen P.hdegree
    P.chi P.psi P.hminimal P.hF P.hLow P.delta P.epsilon1 P.hdelta
      P.hepsilon1 P.hT P.hgammaF P.selected

private noncomputable def stationaryPairs
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (P : WildQuadraticLowCoefficientCore F K) :
    WildQuadraticSelectedStationaryPairs F K :=
  lowWildQuadraticSelectedStationaryPairs P.delta P.epsilon1 P.selected

private theorem stationaryPairs_ratios
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (P : WildQuadraticLowCoefficientCore F K) :
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

private noncomputable def toView
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (P : WildQuadraticLowCoefficientCore F K) :
    WildQuadraticCommonCoefficientView F K P.lowerBreak P.chi.conductor :=
  let hratios := P.stationaryPairs_ratios
  { conductor_gt_one := P.hF.conductor_gt_one
    correction := P.correction
    oppositeNoncancellation :=
      lowWildQuadraticCommonCorrection_oppositeNoncancellation P.ht P.hres
        P.pi P.hpi P.hgen P.hdegree P.chi P.psi P.hminimal P.hF P.hLow
          P.delta P.epsilon1 P.hdelta P.hepsilon1 P.hT P.hgammaF P.selected
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
    criticalInputs_boundaryCoordinates := P.criticalInputs_boundaryCoordinates }

end WildQuadraticLowCoefficientCore

/-- Strict high-range coefficient provenance, again with no q and no
refinement-derived coordinate package. -/
private structure WildQuadraticHighCoefficientCore
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2] where
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
  criticalInputs : WildQuadraticCoefficientInputs F
  criticalInputs_row : criticalInputs.row =
    WildQuadraticCoefficientRow.ofConductors (chiF.conductor - 1) lowerBreak
  criticalInputs_stationaryPairs : criticalInputs.MatchesStationaryPairs
    (highWildQuadraticSelectedStationaryPairs selected.representatives)
  criticalInputs_localData : criticalInputs.MatchesLocalData
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) chiF psiF
  criticalInputs_boundaryCoordinates :
    criticalInputs.MatchesBoundaryCriticalCoordinates

namespace WildQuadraticHighCoefficientCore

private noncomputable def correction
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (P : WildQuadraticHighCoefficientCore F K) :
    WildQuadraticCommonCorrectionData F K (P.lowerBreak + 1)
      P.chiF.conductor :=
  highWildQuadraticCommonCorrection P.ht P.hres P.pi P.hpi P.hgen P.hdegree
    P.htpos P.chiF P.chiK P.psiF P.psiK P.hF P.hK P.hminimal P.hhigh
      P.hchi P.hpsi P.tau P.htau P.gammaF P.hgammaF P.selected

private noncomputable def stationaryPairs
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (P : WildQuadraticHighCoefficientCore F K) :
    WildQuadraticSelectedStationaryPairs F K :=
  highWildQuadraticSelectedStationaryPairs P.selected.representatives

private theorem stationaryPairs_ratios
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (P : WildQuadraticHighCoefficientCore F K) :
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

private noncomputable def toView
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (P : WildQuadraticHighCoefficientCore F K) :
    WildQuadraticCommonCoefficientView F K P.lowerBreak P.chiF.conductor :=
  let hratios := P.stationaryPairs_ratios
  { conductor_gt_one := P.hF.conductor_gt_one
    correction := P.correction
    oppositeNoncancellation :=
      highWildQuadraticCommonCorrection_oppositeNoncancellation P.ht P.hres
        P.pi P.hpi P.hgen P.hdegree P.htpos P.chiF P.chiK P.psiF P.psiK
          P.hF P.hK P.hminimal P.hhigh P.hchi P.hpsi P.tau P.htau P.gammaF
            P.hgammaF P.selected
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
    criticalInputs_boundaryCoordinates := P.criticalInputs_boundaryCoordinates }

end WildQuadraticHighCoefficientCore

/-! ## Actual coefficient inputs -/

/-- Eliminate the proven odd remainder before constructing the normalized
positive-polar quotient witness.  The stationary class still uses the
original decomposition proof. -/
private theorem wildQuadraticPositivePolar_exists_of_remainder_eq_one
    {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ)
    (hD : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hepsilon : epsilon = 1)
    (gamma : Fˣ)
    (hgamma : ord F (gamma : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (beta0 : lattice F 0)
    (hbeta0 : latticeQuotientMk F
        (show (0 : ℤ) ≤ (d : ℤ) by omega) beta0 =
      stationaryCoefficientClass F chi psi hD gamma hgamma) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction F,
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData F W chi psi ∧
        QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair F W
          { gamma := gamma, beta := beta0 } := by
  subst epsilon
  exact
    QuotientDerivedNormalizedCriticalFunction.exists_of_stationaryCoefficientClass
      F chi psi d hD gamma hgamma beta0 hbeta0

private theorem wildQuadraticHighRow_even_even {t m : ℕ}
    (hstrict : t + 1 < m) (hm : Even m) (hT : Even (t + 1)) :
    WildQuadraticCoefficientRow.ofConductors (m - 1) t =
      .aboveMEvenTEven := by
  have hlt : ¬m - 1 < t := by omega
  have heq : m - 1 ≠ t := by omega
  have hsucc : m - 1 + 1 = m := by omega
  simp [WildQuadraticCoefficientRow.ofConductors, hlt, heq, hsucc,
    WildQuadraticConductorParity.ofConductor, hm, hT]

private theorem wildQuadraticHighRow_even_odd {t m : ℕ}
    (hstrict : t + 1 < m) (hm : Even m) (hT : Odd (t + 1)) :
    WildQuadraticCoefficientRow.ofConductors (m - 1) t =
      .aboveMEvenTOdd := by
  have hnT : ¬ Even (t + 1) := Nat.not_even_iff_odd.mpr hT
  have hlt : ¬m - 1 < t := by omega
  have heq : m - 1 ≠ t := by omega
  have hsucc : m - 1 + 1 = m := by omega
  simp [WildQuadraticCoefficientRow.ofConductors, hlt, heq, hsucc,
    WildQuadraticConductorParity.ofConductor, hm, hnT]

private theorem wildQuadraticHighRow_odd_even {t m : ℕ}
    (hstrict : t + 1 < m) (hm : Odd m) (hT : Even (t + 1)) :
    WildQuadraticCoefficientRow.ofConductors (m - 1) t =
      .aboveMOddTEven := by
  have hnm : ¬ Even m := Nat.not_even_iff_odd.mpr hm
  have hlt : ¬m - 1 < t := by omega
  have heq : m - 1 ≠ t := by omega
  have hsucc : m - 1 + 1 = m := by omega
  simp [WildQuadraticCoefficientRow.ofConductors, hlt, heq, hsucc,
    WildQuadraticConductorParity.ofConductor, hnm, hT]

private theorem wildQuadraticHighRow_odd_odd {t m : ℕ}
    (hstrict : t + 1 < m) (hm : Odd m) (hT : Odd (t + 1)) :
    WildQuadraticCoefficientRow.ofConductors (m - 1) t =
      .aboveMOddTOdd := by
  have hnm : ¬ Even m := Nat.not_even_iff_odd.mpr hm
  have hnT : ¬ Even (t + 1) := Nat.not_even_iff_odd.mpr hT
  have hlt : ¬m - 1 < t := by omega
  have heq : m - 1 ≠ t := by omega
  have hsucc : m - 1 + 1 = m := by omega
  simp [WildQuadraticCoefficientRow.ofConductors, hlt, heq, hsucc,
    WildQuadraticConductorParity.ofConductor, hnm, hnT]

private theorem wildQuadraticHighCoefficientInputs_exists
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hstrict : t + 1 < chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF chiK psiF psiK hF hK hminimal hstrict.le hchi hpsi tau
        htau gammaF hgammaF) :
    ∃ inputs : WildQuadraticCoefficientInputs F,
      inputs.row = WildQuadraticCoefficientRow.ofConductors
        (chiF.conductor - 1) t ∧
      inputs.MatchesStationaryPairs
        (highWildQuadraticSelectedStationaryPairs
          Q.parameters.representatives) ∧
      inputs.MatchesLocalData
        (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau)
        chiF psiF ∧
      inputs.MatchesBoundaryCriticalCoordinates := by
  let R := Q.parameters.representatives
  let pairs := highWildQuadraticSelectedStationaryPairs R
  let tauData := wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau
  let hTau := wildQuadraticHighTauDecomposition
    F K ht hres pi hpi hgen htpos tau htau
  by_cases hmEven : Even chiF.conductor
  · by_cases hTEven : Even (t + 1)
    · refine ⟨.aboveMEvenTEven, ?_, trivial, trivial, trivial⟩
      exact (wildQuadraticHighRow_even_even hstrict hmEven hTEven).symm
    · have hTOdd : Odd (t + 1) := Nat.not_even_iff_odd.mp hTEven
      have hTmod : (t + 1) % 2 = 1 := by
        obtain ⟨j, hj⟩ := hTOdd
        omega
      let betaTau : lattice F 0 :=
        ⟨1, by rw [mem_lattice, ord_one]; exact le_rfl⟩
      obtain ⟨Wtau, hWtauLocal, hWtauPair⟩ :=
        wildQuadraticPositivePolar_exists_of_remainder_eq_one (F := F)
          tauData psiF (wildQuadraticHighNormPrecision t) ((t + 1) % 2)
          hTau hTmod R.gammaTau R.gammaTau_order betaTau (by
            simpa only [tauData, betaTau, R] using R.tau_unit_class)
      refine ⟨.aboveMEvenTOdd Wtau, ?_, ?_, ?_, trivial⟩
      · exact (wildQuadraticHighRow_even_odd hstrict hmEven hTOdd).symm
      · simpa only [WildQuadraticCoefficientInputs.MatchesStationaryPairs,
          pairs, R, highWildQuadraticSelectedStationaryPairs, betaTau] using
            hWtauPair
      · simpa only [WildQuadraticCoefficientInputs.MatchesLocalData,
          tauData] using hWtauLocal
  · have hmOdd : Odd chiF.conductor := Nat.not_even_iff_odd.mp hmEven
    have hepsilon : epsilon = 1 := by
      obtain ⟨j, hj⟩ := hmOdd
      have he := hF.epsilon_le_one
      have hc := hF.conductor_eq
      omega
    let betaChi : lattice F 0 := ⟨(R.beta : F), R.beta_integral⟩
    obtain ⟨Wchi, hWchiLocal, hWchiPair⟩ :=
      wildQuadraticPositivePolar_exists_of_remainder_eq_one (F := F)
        chiF psiF d epsilon hF hepsilon gammaF hgammaF betaChi (by
          simpa only [betaChi, R] using R.beta_class)
    by_cases hTEven : Even (t + 1)
    · refine ⟨.aboveMOddTEven Wchi, ?_, ?_, ?_, trivial⟩
      · exact (wildQuadraticHighRow_odd_even hstrict hmOdd hTEven).symm
      · simpa only [WildQuadraticCoefficientInputs.MatchesStationaryPairs,
          pairs, R, highWildQuadraticSelectedStationaryPairs, betaChi] using
            hWchiPair
      · simpa only [WildQuadraticCoefficientInputs.MatchesLocalData] using
          hWchiLocal
    · have hTOdd : Odd (t + 1) := Nat.not_even_iff_odd.mp hTEven
      have hTmod : (t + 1) % 2 = 1 := by
        obtain ⟨j, hj⟩ := hTOdd
        omega
      let betaTau : lattice F 0 :=
        ⟨1, by rw [mem_lattice, ord_one]; exact le_rfl⟩
      obtain ⟨Wtau, hWtauLocal, hWtauPair⟩ :=
        wildQuadraticPositivePolar_exists_of_remainder_eq_one (F := F)
          tauData psiF (wildQuadraticHighNormPrecision t) ((t + 1) % 2)
          hTau hTmod R.gammaTau R.gammaTau_order betaTau (by
            simpa only [tauData, betaTau, R] using R.tau_unit_class)
      refine ⟨.aboveMOddTOdd Wtau Wchi, ?_, ?_, ?_, trivial⟩
      · exact (wildQuadraticHighRow_odd_odd hstrict hmOdd hTOdd).symm
      · exact ⟨by
          simpa only [pairs, R, highWildQuadraticSelectedStationaryPairs,
            betaTau] using hWtauPair, by
          simpa only [pairs, R, highWildQuadraticSelectedStationaryPairs,
            betaChi] using hWchiPair⟩
      · exact ⟨by simpa only [tauData] using hWtauLocal, hWchiLocal⟩

/-! ## Actual low coefficient inputs -/

/-- An odd actual Lamprecht row supplies its normalized quotient witness;
the selected denominator and numerator are unchanged. -/
private theorem wildQuadraticPreparation_oddSourceOfPhase
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)] [CharP (ResidueField E) 2]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (S : LocalLamprechtPhaseData E chi psi) (hodd : Odd chi.conductor) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction E,
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData E W chi psi ∧
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair E W
        S.selectedStationaryPair ∧
      S.criticalFactor = quotientSourcePhase E (some W) := by
  exact S.exists_normalizedQuotientSource hodd

/-- The four strict-low parity rows, with every odd source extracted from
the corresponding actual local row. -/
private theorem wildQuadraticLowBelowInputs_exists
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t m : ℕ} (hmgt : 1 < m) (hstrict : m < t + 1)
    (tauData chiData : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (htau : tauData.conductor = t + 1) (hchi : chiData.conductor = m)
    (pairs : WildQuadraticSelectedStationaryPairs F K)
    (tauPhase : LocalLamprechtPhaseData F tauData psi)
    (basePhase : LocalLamprechtPhaseData F chiData psi)
    (htauPair : tauPhase.selectedStationaryPair = pairs.tau)
    (hbasePair : basePhase.selectedStationaryPair = pairs.chiF) :
    ∃ I : WildQuadraticCoefficientInputs F,
      I.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t ∧
      I.MatchesStationaryPairs pairs ∧ I.MatchesLocalData tauData chiData psi ∧
      I.MatchesBoundaryCriticalCoordinates ∧
      tauPhase.criticalFactor = quotientSourcePhase F I.tauSource ∧
      basePhase.criticalFactor = quotientSourcePhase F I.chiFSource := by
  have hmPred : m - 1 + 1 = m := by omega
  have hbelow : m - 1 < t := by omega
  cases hmParity : WildQuadraticConductorParity.ofConductor m with
  | even =>
      have hmEven :=
        (WildQuadraticConductorParity.ofConductor_eq_even_iff m).mp hmParity
      cases hTParity : WildQuadraticConductorParity.ofConductor (t + 1) with
      | even =>
          have hTEven :=
            (WildQuadraticConductorParity.ofConductor_eq_even_iff
              (t + 1)).mp hTParity
          refine ⟨.belowMEvenTEven, ?_, trivial, trivial, trivial, ?_, ?_⟩
          · simp [WildQuadraticCoefficientInputs.row,
              WildQuadraticCoefficientRow.ofConductors, hbelow, hmPred,
              hmParity, hTParity]
          · simpa [WildQuadraticCoefficientInputs.tauSource,
              quotientSourcePhase] using tauPhase.criticalFactor_eq_one_of_isEven
                (tauPhase.isEven_of_even_conductor (by
                  simpa only [htau] using hTEven))
          · simpa [WildQuadraticCoefficientInputs.chiFSource,
              quotientSourcePhase] using basePhase.criticalFactor_eq_one_of_isEven
                (basePhase.isEven_of_even_conductor (by
                  simpa only [hchi] using hmEven))
      | odd =>
          have hTOdd :=
            (WildQuadraticConductorParity.ofConductor_eq_odd_iff
              (t + 1)).mp hTParity
          obtain ⟨Wtau, hlocal, hpair, hphase⟩ :=
            wildQuadraticPreparation_oddSourceOfPhase tauPhase (by
              simpa only [htau] using hTOdd)
          refine ⟨.belowMEvenTOdd Wtau, ?_, ?_, hlocal, trivial, ?_, ?_⟩
          · simp [WildQuadraticCoefficientInputs.row,
              WildQuadraticCoefficientRow.ofConductors, hbelow, hmPred,
              hmParity, hTParity]
          · change QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
              F Wtau pairs.tau
            simpa only [htauPair] using hpair
          · simpa [WildQuadraticCoefficientInputs.tauSource] using hphase
          · simpa [WildQuadraticCoefficientInputs.chiFSource,
              quotientSourcePhase] using basePhase.criticalFactor_eq_one_of_isEven
                (basePhase.isEven_of_even_conductor (by
                  simpa only [hchi] using hmEven))
  | odd =>
      have hmOdd :=
        (WildQuadraticConductorParity.ofConductor_eq_odd_iff m).mp hmParity
      obtain ⟨Wchi, hlocalChi, hpairChi, hphaseChi⟩ :=
        wildQuadraticPreparation_oddSourceOfPhase basePhase (by
          simpa only [hchi] using hmOdd)
      cases hTParity : WildQuadraticConductorParity.ofConductor (t + 1) with
      | even =>
          have hTEven :=
            (WildQuadraticConductorParity.ofConductor_eq_even_iff
              (t + 1)).mp hTParity
          refine ⟨.belowMOddTEven Wchi, ?_, ?_, hlocalChi, trivial, ?_, ?_⟩
          · simp [WildQuadraticCoefficientInputs.row,
              WildQuadraticCoefficientRow.ofConductors, hbelow, hmPred,
              hmParity, hTParity]
          · change QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
              F Wchi pairs.chiF
            simpa only [hbasePair] using hpairChi
          · simpa [WildQuadraticCoefficientInputs.tauSource,
              quotientSourcePhase] using tauPhase.criticalFactor_eq_one_of_isEven
                (tauPhase.isEven_of_even_conductor (by
                  simpa only [htau] using hTEven))
          · simpa [WildQuadraticCoefficientInputs.chiFSource] using hphaseChi
      | odd =>
          have hTOdd :=
            (WildQuadraticConductorParity.ofConductor_eq_odd_iff
              (t + 1)).mp hTParity
          obtain ⟨Wtau, hlocalTau, hpairTau, hphaseTau⟩ :=
            wildQuadraticPreparation_oddSourceOfPhase tauPhase (by
              simpa only [htau] using hTOdd)
          refine ⟨.belowMOddTOdd Wtau Wchi, ?_, ?_, ?_, trivial, ?_, ?_⟩
          · simp [WildQuadraticCoefficientInputs.row,
              WildQuadraticCoefficientRow.ofConductors, hbelow, hmPred,
              hmParity, hTParity]
          · exact ⟨by simpa only [htauPair] using hpairTau,
              by simpa only [hbasePair] using hpairChi⟩
          · exact ⟨hlocalTau, hlocalChi⟩
          · simpa [WildQuadraticCoefficientInputs.tauSource] using hphaseTau
          · simpa [WildQuadraticCoefficientInputs.chiFSource] using hphaseChi

/-- Scaling the literal stationary ratio scales the intrinsic polar
coefficient by the residue of the same unit. -/
private theorem wildQuadraticPreparation_polarCoefficient_ratio
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Fintype (ResidueField E)] [CharP (ResidueField E) 2]
    {chi₁ chi₂ : LocalQuasiCharData E}
    (psi₁ psi₂ : LocalAddCharData E) (hpsi : psi₁ = psi₂)
    (d₁ d₂ : ℕ) (hm₁ : chi₁.conductor = 2 * d₁ + 1)
    (hm₂ : chi₂.conductor = 2 * d₂ + 1)
    (hlarge₁ : 1 < chi₁.conductor) (hlarge₂ : 1 < chi₂.conductor)
    (Gamma₁ : AdmissibleGamma E chi₁ psi₁)
    (Gamma₂ : AdmissibleGamma E chi₂ psi₂) (delta : Eˣ)
    (hdelta₁ : ord E (delta : E) = ((d₁ : ℤ) : WithTop ℤ))
    (hdelta₂ : ord E (delta : E) = ((d₂ : ℤ) : WithTop ℤ))
    (beta₁ : lattice E ((chi₁.conductor : ℤ) - chi₁.conductor))
    (hbeta₁ : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi₁ d₁ hm₁ hlarge₁).int_le_conductor
          chi₁.conductor) beta₁ =
      stationaryNumeratorClass E chi₁ psi₁ chi₁.conductor
        (criticalPolar_stationaryDepth E chi₁ d₁ hm₁ hlarge₁)
          Gamma₁ Gamma₁.property)
    (beta₂ : lattice E ((chi₂.conductor : ℤ) - chi₂.conductor))
    (hbeta₂ : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi₂ d₂ hm₂ hlarge₂).int_le_conductor
          chi₂.conductor) beta₂ =
      stationaryNumeratorClass E chi₂ psi₂ chi₂.conductor
        (criticalPolar_stationaryDepth E chi₂ d₂ hm₂ hlarge₂)
          Gamma₂ Gamma₂.property)
    (u : unitGroup E)
    (hratio : (beta₂ : E) / ((Gamma₂ : Eˣ) : E) =
      ((u : Eˣ) : E) * ((beta₁ : E) / ((Gamma₁ : Eˣ) : E))) :
    criticalPolarCoefficient E chi₂ psi₂ d₂ hm₂ hlarge₂ Gamma₂ delta hdelta₂
        (absoluteTraceChar (ResidueField E))
        (absoluteTraceChar_ne_one (ResidueField E)) =
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) *
        criticalPolarCoefficient E chi₁ psi₁ d₁ hm₁ hlarge₁ Gamma₁ delta
          hdelta₁ (absoluteTraceChar (ResidueField E))
            (absoluteTraceChar_ne_one (ResidueField E)) := by
  subst psi₂
  let psi0 := absoluteTraceChar (ResidueField E)
  let hpsi0 := absoluteTraceChar_ne_one (ResidueField E)
  let phi₁ := criticalPolarAddChar E chi₁ psi₁ d₁ hm₁ hlarge₁ Gamma₁ delta
    hdelta₁
  let phi₂ := criticalPolarAddChar E chi₂ psi₁ d₂ hm₂ hlarge₂ Gamma₂ delta
    hdelta₂
  have hphi : phi₂ = phi₁.mulShift
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) := by
    apply AddChar.ext
    intro x
    rw [AddChar.mulShift_apply]
    let tx : E := (teichmuller E x : E)
    have htx : tx ∈ lattice E 0 :=
      (mem_lattice_zero_iff E).2 (teichmuller E x).property
    let ux : E := ((u : Eˣ) : E) * tx
    have hu : ((u : Eˣ) : E) ∈ lattice E 0 :=
      (mem_lattice_zero_iff E).2
        (((unitGroupMulEquivRingOfIntegers E u : (ringOfIntegers E)ˣ) :
          ringOfIntegers E).property)
    have hux : ux ∈ lattice E 0 := mul_mem_lattice E hu htx
    have hreduce : reduce E ux hux =
        ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) * x := by
      change residueMap E
        (((unitGroupMulEquivRingOfIntegers E u : (ringOfIntegers E)ˣ) :
          ringOfIntegers E) * teichmuller E x) = _
      rw [map_mul, ← residueUnits_coe, residueMap_teichmuller]
    have htwo := criticalPolarAddChar_integral_lift E chi₂ psi₁ d₂ hm₂
      hlarge₂ Gamma₂ delta hdelta₂ beta₂ hbeta₂ tx htx
    have hone := criticalPolarAddChar_integral_lift E chi₁ psi₁ d₁ hm₁
      hlarge₁ Gamma₁ delta hdelta₁ beta₁ hbeta₁ ux hux
    rw [show reduce E tx htx = x from residueMap_teichmuller E x] at htwo
    rw [hreduce] at hone
    dsimp only [phi₁, phi₂] at htwo hone ⊢
    rw [htwo, hone]
    congr 2
    dsimp only [ux]
    calc
      (beta₂ : E) * (delta : E) ^ 2 * tx / ((Gamma₂ : Eˣ) : E) =
          ((beta₂ : E) / ((Gamma₂ : Eˣ) : E)) *
            (delta : E) ^ 2 * tx := by
        field_simp [AdmissibleGamma.coe_ne_zero Gamma₂]
      _ = (((u : Eˣ) : E) *
          ((beta₁ : E) / ((Gamma₁ : Eˣ) : E))) *
            (delta : E) ^ 2 * tx := by rw [hratio]
      _ = (beta₁ : E) * (delta : E) ^ 2 *
          (((u : Eˣ) : E) * tx) / ((Gamma₁ : Eˣ) : E) := by
        field_simp [AdmissibleGamma.coe_ne_zero Gamma₁]
  change finiteAddCharCoefficient psi0 hpsi0 phi₂ =
    ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) *
      finiteAddCharCoefficient psi0 hpsi0 phi₁
  rw [hphi, finiteAddCharCoefficient_mulShift]
  ring

/-- The normalized coordinates of the two actual odd boundary rows have a
common nonzero scale, whose square is the residue of the actual norm ratio. -/
private theorem wildQuadraticPreparation_boundaryCommonCoordinate
    {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    (Wtau Wchi : QuotientDerivedNormalizedCriticalFunction F)
    (hpsi : Wtau.psi = Wchi.psi)
    (hconductor : Wtau.chi.conductor = Wchi.chi.conductor)
    (n0 : unitGroup F)
    (hnres : ((residueUnits F n0 : (ResidueField F)ˣ) :
      ResidueField F) ≠ 1)
    (hratio : (Wchi.beta : F) / ((Wchi.Gamma : Fˣ) : F) =
      ((n0 : Fˣ) : F) * ((Wtau.beta : F) / ((Wtau.Gamma : Fˣ) : F))) :
    ∃ rho : ResidueField F, rho ≠ 0 ∧ 1 + rho ≠ 0 ∧ Nonempty
      (WildQuadraticCoefficientInputs.WildQuadraticBoundaryCommonCoordinate
        (F := F) rho Wtau Wchi) := by
  have hd : Wtau.d = Wchi.d := by
    have ht := Wtau.conductor_eq
    have hc := Wchi.conductor_eq
    omega
  let ratio : Fˣ := Wtau.delta / Wchi.delta
  have hratioOrd : ord F (ratio : F) = (0 : WithTop ℤ) := by
    simp only [ratio, Units.val_div_eq_div_val]
    rw [ord_div, Wtau.delta_order, Wchi.delta_order, hd]
    simp
  let rhoLift : unitGroup F :=
    ⟨ratio, (mem_unitGroup_iff_ord_eq_zero F ratio).2 hratioOrd⟩
  let rho : ResidueField F :=
    ((residueUnits F rhoLift : (ResidueField F)ˣ) : ResidueField F)
  have hrho : rho ≠ 0 := Units.ne_zero (residueUnits F rhoLift)
  have hcoordinate : Wtau.delta =
      criticalPolarScaledCoordinate F rhoLift Wchi.delta := by
    apply Units.ext
    simp only [criticalPolarScaledCoordinate, rhoLift, ratio, Units.val_mul,
      Units.val_div_eq_div_val]
    field_simp [Units.ne_zero Wchi.delta]
  have hdelta : ord F (Wchi.delta : F) =
      ((Wtau.d : ℤ) : WithTop ℤ) := by rw [Wchi.delta_order, hd]
  have hcoeff := wildQuadraticPreparation_polarCoefficient_ratio
    Wtau.psi Wchi.psi hpsi Wtau.d Wchi.d Wtau.conductor_eq
      Wchi.conductor_eq Wtau.conductor_gt_one Wchi.conductor_gt_one
        Wtau.Gamma Wchi.Gamma Wchi.delta hdelta Wchi.delta_order Wtau.beta
          Wtau.beta_class Wchi.beta Wchi.beta_class n0 hratio
  let coeff := criticalPolarCoefficient F Wtau.chi Wtau.psi Wtau.d
    Wtau.conductor_eq Wtau.conductor_gt_one Wtau.Gamma Wchi.delta hdelta
      (absoluteTraceChar (ResidueField F))
        (absoluteTraceChar_ne_one (ResidueField F))
  have hn : ((residueUnits F n0 : (ResidueField F)ˣ) : ResidueField F) *
      coeff = 1 := by
    rw [← Wchi.polar_eq_one]
    simpa only [coeff] using hcoeff.symm
  have hscale := criticalPolarCoefficient_scaleCoordinate F Wtau.chi
    Wtau.psi Wtau.d Wtau.conductor_eq Wtau.conductor_gt_one Wtau.Gamma
      Wchi.delta hdelta (absoluteTraceChar (ResidueField F))
        (absoluteTraceChar_ne_one (ResidueField F)) rhoLift
  have hr : rho ^ 2 * coeff = 1 := by
    rw [← Wtau.polar_eq_one]
    simpa only [rho, coeff, hcoordinate] using hscale.symm
  have hcoeffne : coeff ≠ 0 := criticalPolarCoefficient_ne_zero F Wtau.chi
    Wtau.psi Wtau.d Wtau.conductor_eq Wtau.conductor_gt_one Wtau.Gamma
      Wchi.delta hdelta (absoluteTraceChar (ResidueField F))
        (absoluteTraceChar_ne_one (ResidueField F))
  have hrsq : rho ^ 2 =
      ((residueUnits F n0 : (ResidueField F)ˣ) : ResidueField F) := by
    apply mul_right_cancel₀ hcoeffne
    rw [hr, hn]
  have hden : 1 + rho ≠ 0 := by
    intro hzero
    have hrhoNeg : rho = -1 := by linear_combination hzero
    apply hnres
    rw [← hrsq, hrhoNeg]
    simp
  exact ⟨rho, hrho, hden,
    ⟨{ rhoLift := rhoLift, rhoLift_residue := rfl,
       coordinate_eq := hcoordinate }⟩⟩

/-- At the boundary, equality of the residue of `n` with one would move the
literal twist ratio one lattice deeper than its actual stationary row. -/
private theorem wildQuadraticPreparation_boundaryNResidue_ne_one
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t m : ℕ} (C : WildQuadraticCommonCorrectionData F K (t + 1) m)
    (hboundary : m = t + 1)
    (tauData twistData : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (htauConductor : tauData.conductor = t + 1)
    (htwistConductor : twistData.conductor = t + 1)
    (pairs : WildQuadraticSelectedStationaryPairs F K)
    (hratio : pairs.tauChiF.ratio =
      pairs.tau.ratio * ((C.n : F) + 1))
    (tauPhase : LocalLamprechtPhaseData F tauData psi)
    (twistPhase : LocalLamprechtPhaseData F twistData psi)
    (htauPair : tauPhase.selectedStationaryPair = pairs.tau)
    (htwistPair : twistPhase.selectedStationaryPair = pairs.tauChiF) :
    let n0 : unitGroup F :=
      ⟨C.n, (mem_unitGroup_iff_ord_eq_zero F C.n).2 (by
        rw [C.target_order, hboundary]
        simp)⟩
    ((residueUnits F n0 : (ResidueField F)ˣ) : ResidueField F) ≠ 1 := by
  dsimp only
  have hnord : ord F (C.n : F) = (0 : WithTop ℤ) := by
    rw [C.target_order, hboundary]
    simp
  let n0 : unitGroup F :=
    ⟨C.n, (mem_unitGroup_iff_ord_eq_zero F C.n).2 hnord⟩
  intro hnres
  let nO : ringOfIntegers F := unitGroupMulEquivRingOfIntegers F n0
  have hres : residueMap F nO = 1 := by
    rw [← residueUnits_coe F n0]
    exact hnres
  have hone : (1 : F) + (C.n : F) ∈ lattice F 1 := by
    have hz : residueMap F (1 + nO) = 0 := by
      rw [map_add, map_one, hres]
      simpa [one_add_one_eq_two] using
        (CharP.cast_eq_zero (ResidueField F) 2)
    have hmem := (residueMap_eq_zero_iff F (1 + nO)).1 hz
    have hnO : (nO : F) = (C.n : F) := by rfl
    rw [show ((1 + nO : ringOfIntegers F) : F) = 1 + (nO : F) by rfl,
      hnO] at hmem
    exact hmem
  let a : ℤ := -(((t + 1 : ℕ) : ℤ) + psi.conductor)
  have htauOrd : ord F pairs.tau.ratio = (a : WithTop ℤ) := by
    have h := tauPhase.selectedStationaryPair_ratio_order
    rw [htauPair, htauConductor] at h
    exact h
  have htwistOrd : ord F pairs.tauChiF.ratio = (a : WithTop ℤ) := by
    have h := twistPhase.selectedStationaryPair_ratio_order
    rw [htwistPair, htwistConductor] at h
    exact h
  have htauMem : pairs.tau.ratio ∈ lattice F a := by
    rw [mem_lattice, htauOrd]
  have hproduct := mul_mem_lattice F htauMem hone
  have hrewrite : pairs.tau.ratio * ((1 : F) + (C.n : F)) =
      pairs.tauChiF.ratio := by rw [hratio]; ring
  rw [hrewrite] at hproduct
  have hnot : pairs.tauChiF.ratio ∉ lattice F (a + 1) := by
    rw [mem_lattice, htwistOrd]
    norm_cast
    omega
  exact hnot hproduct

/-- The two low boundary rows are either the genuine even row or the genuine
odd row with its source-tied common coordinate. -/
private theorem wildQuadraticLowBoundaryInputs_exists
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    {t m : ℕ} (hmgt : 1 < m) (hboundary : m - 1 = t)
    (tauData chiData : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (htau : tauData.conductor = t + 1) (hchi : chiData.conductor = m)
    (pairs : WildQuadraticSelectedStationaryPairs F K) (n0 : unitGroup F)
    (hnres : ((residueUnits F n0 : (ResidueField F)ˣ) : ResidueField F) ≠ 1)
    (hchiRatio : pairs.chiF.ratio =
      pairs.tau.ratio * ((n0 : Fˣ) : F))
    (tauPhase : LocalLamprechtPhaseData F tauData psi)
    (basePhase : LocalLamprechtPhaseData F chiData psi)
    (htauPair : tauPhase.selectedStationaryPair = pairs.tau)
    (hbasePair : basePhase.selectedStationaryPair = pairs.chiF) :
    ∃ I : WildQuadraticCoefficientInputs F,
      I.row = WildQuadraticCoefficientRow.ofConductors (m - 1) t ∧
      I.MatchesStationaryPairs pairs ∧ I.MatchesLocalData tauData chiData psi ∧
      I.MatchesBoundaryCriticalCoordinates ∧
      tauPhase.criticalFactor = quotientSourcePhase F I.tauSource ∧
      basePhase.criticalFactor = quotientSourcePhase F I.chiFSource := by
  have hT : t + 1 = m := by omega
  by_cases hmEven : Even m
  · have hpar := (WildQuadraticConductorParity.ofConductor_eq_even_iff
      (t + 1)).mpr (by simpa only [hT] using hmEven)
    refine ⟨.boundaryEven, ?_, trivial, trivial, trivial, ?_, ?_⟩
    · simp [WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.ofConductors, hboundary, hpar]
    · simpa [WildQuadraticCoefficientInputs.tauSource,
        quotientSourcePhase] using tauPhase.criticalFactor_eq_one_of_isEven
          (tauPhase.isEven_of_even_conductor (by
            rw [htau, hT]
            exact hmEven))
    · simpa [WildQuadraticCoefficientInputs.chiFSource,
        quotientSourcePhase] using basePhase.criticalFactor_eq_one_of_isEven
          (basePhase.isEven_of_even_conductor (by
            simpa only [hchi] using hmEven))
  · have hmOdd := Nat.not_even_iff_odd.mp hmEven
    have hpar := (WildQuadraticConductorParity.ofConductor_eq_odd_iff
      (t + 1)).mpr (by simpa only [hT] using hmOdd)
    obtain ⟨Wtau, hlocalTau, hpairTau, hphaseTau⟩ :=
      wildQuadraticPreparation_oddSourceOfPhase tauPhase (by
        rw [htau, hT]; exact hmOdd)
    obtain ⟨Wchi, hlocalChi, hpairChi, hphaseChi⟩ :=
      wildQuadraticPreparation_oddSourceOfPhase basePhase (by
        rw [hchi]; exact hmOdd)
    have hratio : (Wchi.beta : F) / ((Wchi.Gamma : Fˣ) : F) =
        ((n0 : Fˣ) : F) *
          ((Wtau.beta : F) / ((Wtau.Gamma : Fˣ) : F)) := by
      calc
        (Wchi.beta : F) / ((Wchi.Gamma : Fˣ) : F) =
            pairs.chiF.ratio := by
          rw [hpairChi.1, hpairChi.2, hbasePair]
          rfl
        _ = pairs.tau.ratio * ((n0 : Fˣ) : F) := hchiRatio
        _ = ((n0 : Fˣ) : F) * pairs.tau.ratio := by ring
        _ = ((n0 : Fˣ) : F) *
            ((Wtau.beta : F) / ((Wtau.Gamma : Fˣ) : F)) := by
          rw [hpairTau.1, hpairTau.2, htauPair]
          rfl
    obtain ⟨rho, hrho, hden, hcommon⟩ :=
      wildQuadraticPreparation_boundaryCommonCoordinate Wtau Wchi
        (hlocalTau.2.trans hlocalChi.2.symm) (by
          rw [hlocalTau.1, hlocalChi.1, htau, hchi, hT]) n0 hnres hratio
    refine ⟨.boundaryOdd rho hrho hden Wtau Wchi, ?_, ?_, ?_, hcommon,
      ?_, ?_⟩
    · simp [WildQuadraticCoefficientInputs.row,
        WildQuadraticCoefficientRow.ofConductors, hboundary, hpar]
    · exact ⟨by simpa only [htauPair] using hpairTau,
        by simpa only [hbasePair] using hpairChi⟩
    · exact ⟨hlocalTau, hlocalChi⟩
    · simpa [WildQuadraticCoefficientInputs.tauSource] using hphaseTau
    · simpa [WildQuadraticCoefficientInputs.chiFSource] using hphaseChi

/-! ## Common raw coordinates -/

/-- The two source-tied norm ratios attached to the common correction.  This
is the only raw-coordinate input needed by either exact phase constructor. -/
private noncomputable def wildQuadraticPreparationRawCoordinates
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (hopp : C.OppositeNoncancellation) :
    QuadraticRawRatioCoordinates F K (C.u : K) C.n where
  zZero := C.z0Unit hopp
  zOne := C.z1Unit hopp
  x := C.x
  y := C.y
  zZero_eq := by
    rw [C.coe_z0Unit]
    unfold WildQuadraticCommonCorrectionData.x
    ring
  zOne_eq := by
    rw [C.coe_z1Unit]
    unfold WildQuadraticCommonCorrectionData.y
    ring
  one_add_n_ne_zero := C.denominator_ne_zero
  zZero_ratio := by
    rw [C.coe_z0Unit, C.norm_n_sub_u_eq]
    simp only [WildQuadraticCommonCorrectionData.denominator]
    field_simp [Units.ne_zero C.n, C.denominator_ne_zero]
  zOne_ratio := by
    rw [C.coe_z1Unit]
    rfl

/-- Transport the ratio parameters while retaining the literal coordinates
used by the public assembly. -/
private def wildQuadraticPreparationTransportRawCoordinates
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    {u u' : K} {n n' : Fˣ} (hu : u' = u) (hn : n' = n)
    (raw : QuadraticRawRatioCoordinates F K u n) :
    QuadraticRawRatioCoordinates F K u' n' where
  zZero := raw.zZero
  zOne := raw.zOne
  x := raw.x
  y := raw.y
  zZero_eq := raw.zZero_eq
  zOne_eq := raw.zOne_eq
  one_add_n_ne_zero := by
    rw [hn]
    exact raw.one_add_n_ne_zero
  zZero_ratio := by
    rw [hu, hn]
    exact raw.zZero_ratio
  zOne_ratio := by
    rw [hu, hn]
    exact raw.zOne_ratio

/-! ## Low q-free phase package -/

/-- Transport the selected representative and its dependent low table
together; transporting them separately would lose their shared index. -/
private noncomputable def wildQuadraticPreparationTransportLowTable
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal)
    (chiData : LocalQuasiCharData F) (hbase : chiData = chiF)
    (psiData : LocalAddCharData F) (hadd : psiData = psiF)
    (hF : IsStationaryConductorDecomposition chiData.conductor
      (chiF.conductor / 2) (chiF.conductor % 2))
    (hmin : IsMinimalNormCharacterOrbitRepresentative F K chiData)
    (hchi : S.chiK.character = chiData.character.compNorm)
    (hpsi : S.psiK.character = psiData.character.compTrace)
    (hLow : chiData.conductor ≤ t + 1)
    (hdelta : ord F (S.delta : F) =
      ((((t + 1 : ℕ) : ℤ) + psiData.conductor : ℤ) : WithTop ℤ))
    (hepsilon : ord K (S.epsilon1 : K) =
      (((t + 1 - chiData.conductor : ℕ) : ℤ) : WithTop ℤ))
    (hgammaF : ord F (lowGammaF F K S.delta S.epsilon1 : F) =
      ((((chiData.conductor : ℤ) + psiData.conductor : ℤ)) : WithTop ℤ))
    (hgammaK : ord K (lowGammaK F K S.delta S.epsilon1 : K) =
      (((S.chiK.conductor : ℤ) + S.psiK.conductor : ℤ) : WithTop ℤ)) :
    { P : LowStationaryNormRepresentativePair F K (lowCriticalFloorDepth t)
        (chiF.conductor / 2)
        (stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F
            (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
            (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
              (lowNormCharacterGenerator F K ht hres pi hpi hgen)
              (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
          psiData (lowCriticalConductorDecomposition (t := t) S.hT)
            S.delta hdelta)
        (stationaryCoefficientClass F chiData psiData hF
          (lowGammaF F K S.delta S.epsilon1) hgammaF) //
      LowConductorParameterTableData F K ht hres pi hpi hgen
        chiData S.chiK psiData S.psiK hmin hchi hpsi hF
          hLow S.delta S.epsilon1 hdelta hepsilon S.hT hgammaF hgammaK P ∧
      lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 P =
        lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected ∧
      lowNormalizedRatio F K S.epsilon1 P =
        lowNormalizedRatio F K S.epsilon1 S.selected ∧
      lowEpsilon F K S.epsilon1 * P.beta / P.alpha =
        lowWildQuadraticCommonN S.epsilon1 S.selected } := by
  subst chiData
  subst psiData
  exact ⟨S.selected, S.table, rfl, rfl, rfl⟩

/-! ## Strict-high q-free phase package -/

/-- Transport one simultaneous high product only across equal source
character data.  This keeps the selected quotient representatives literal
while changing the proof-indexed computational datum. -/
private noncomputable def wildQuadraticPreparationTransportHighProduct
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chi chi' : LocalQuasiCharData F) (hchiData : chi = chi')
    (chiK : LocalQuasiCharData K)
    (psi psi' : LocalAddCharData F) (hpsiData : psi = psi')
    (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hF' : IsStationaryConductorDecomposition chi'.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hminimal' : IsMinimalNormCharacterOrbitRepresentative F K chi')
    (hhigh : t + 1 ≤ chi.conductor)
    (hhigh' : t + 1 ≤ chi'.conductor)
    (hchi : chiK.character = chi.character.compNorm)
    (hchi' : chiK.character = chi'.character.compNorm)
    (hpsi : psiK.character = psi.character.compTrace)
    (hpsi' : psiK.character = psi'.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgammaF' : ord F (gammaF : F) =
      (((chi'.conductor : ℤ) + psi'.conductor : ℤ) : WithTop ℤ))
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chi chiK psi psiK hF hK hminimal hhigh hchi hpsi tau htau
        gammaF hgammaF) :
    WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree htpos
      chi' chiK psi' psiK hF' hK hminimal' hhigh' hchi' hpsi' tau htau
        gammaF hgammaF' := by
  subst chi'
  subst psi'
  exact Q

/-- The stationary pairs and both normalized ratios are unchanged by the
preceding proof-index transport. -/
private theorem wildQuadraticPreparationTransportHighProduct_values
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chi chi' : LocalQuasiCharData F) (hchiData : chi = chi')
    (chiK : LocalQuasiCharData K)
    (psi psi' : LocalAddCharData F) (hpsiData : psi = psi')
    (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hF' : IsStationaryConductorDecomposition chi'.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chi)
    (hminimal' : IsMinimalNormCharacterOrbitRepresentative F K chi')
    (hhigh : t + 1 ≤ chi.conductor)
    (hhigh' : t + 1 ≤ chi'.conductor)
    (hchi : chiK.character = chi.character.compNorm)
    (hchi' : chiK.character = chi'.character.compNorm)
    (hpsi : psiK.character = psi.character.compTrace)
    (hpsi' : psiK.character = psi'.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgammaF' : ord F (gammaF : F) =
      (((chi'.conductor : ℤ) + psi'.conductor : ℤ) : WithTop ℤ))
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chi chiK psi psiK hF hK hminimal hhigh hchi hpsi tau htau
        gammaF hgammaF) :
    let Q' := wildQuadraticPreparationTransportHighProduct ht hres pi hpi
      hgen hdegree htpos chi chi' hchiData chiK psi psi' hpsiData psiK hF
        hF' hK hminimal hminimal' hhigh hhigh' hchi hchi' hpsi hpsi' tau
          htau gammaF hgammaF hgammaF' Q
    highWildQuadraticSelectedStationaryPairs Q'.parameters.representatives =
        highWildQuadraticSelectedStationaryPairs Q.parameters.representatives ∧
      Q'.parameters.representatives.u = Q.parameters.representatives.u ∧
      Q'.parameters.representatives.n = Q.parameters.representatives.n := by
  subst chi'
  subst psi'
  exact ⟨rfl, rfl, rfl⟩

/-- Change only the public conductor index of an exact assembly. -/
private noncomputable def wildQuadraticPreparationTransportAssembly
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chi : ContinuousQuasiChar F} {psi : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chi psi}
    {D : FirstMainPhaseData F K chi psi data}
    {t m m' : ℕ} (hm : m = m')
    (A : ExactQuadraticPhaseAssembly F K chi psi data D (t := t) (m := m)) :
    ExactQuadraticPhaseAssembly F K chi psi data D (t := t) (m := m') :=
  hm ▸ A

private theorem wildQuadraticPreparationTransportAssembly_fields
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chi : ContinuousQuasiChar F} {psi : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chi psi}
    {D : FirstMainPhaseData F K chi psi data}
    {t m m' : ℕ} (hm : m = m')
    (A : ExactQuadraticPhaseAssembly F K chi psi data D (t := t) (m := m)) :
    let A' := wildQuadraticPreparationTransportAssembly hm A
    A'.indexing = A.indexing ∧ A'.A = A.A ∧ A'.u = A.u ∧ A'.n = A.n ∧
      A'.zZero = A.zZero ∧ A'.zOne = A.zOne := by
  subst m'
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Package rows originally indexed by a named nontrivial character after
the exact assembly has been transported to its public conductor. -/
private noncomputable def wildQuadraticPreparationActualRowsOfTauEq
    {F K : Type}
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
    {t m : ℕ} {V : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)}
    (tau0 : NormCharacter F K) (hAtau : A.indexing.tau = tau0)
    (extension : LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar)
    (tauRow : LocalLamprechtPhaseData F (data.normCharacterData tau0)
      data.baseAddChar)
    (base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar)
    (twist : LocalLamprechtPhaseData F (data.twistData tau0)
      data.baseAddChar)
    (hExtension : D.extension = LocalPhaseData.stationary extension)
    (hTau : D.normCharacter tau0 = LocalPhaseData.stationary tauRow)
    (hBase : D.twist 1 = LocalPhaseData.stationary base)
    (hTwist : D.twist tau0 = LocalPhaseData.stationary twist)
    (extensionPair : extension.selectedStationaryPair = V.stationaryPairs.chiK)
    (tauPair : tauRow.selectedStationaryPair = V.stationaryPairs.tau)
    (basePair : base.selectedStationaryPair = V.stationaryPairs.chiF)
    (twistPair : twist.selectedStationaryPair = V.stationaryPairs.tauChiF) :
    WildQuadraticActualPhaseRows V data D A := by
  subst tau0
  exact
    { extension := extension
      tau := tauRow
      base := base
      twist := twist
      extension_eq := hExtension
      tau_eq := hTau
      base_eq := hBase
      twist_eq := hTwist
      extension_pair := extensionPair
      tau_pair := tauPair
      base_pair := basePair
      twist_pair := twistPair }

/- Select the coefficient inputs attached to one simultaneous high product
and retain their row, stationary-pair, local-data, and boundary witnesses. -/
set_option maxHeartbeats 4000000 in
private noncomputable def wildQuadraticPreparationHighCoefficientCore
    {F K : Type}
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
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal)
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF) :
    WildQuadraticHighCoefficientCore F K := by
  classical
  let hinputs := wildQuadraticHighCoefficientInputs_exists ht hres pi hpi hgen
    hdegree htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hstrict
      S.hchi S.hpsi S.tau S.htau S.gammaF S.hgammaF Q
  let inputs := Classical.choose hinputs
  refine
    { lowerBreak := t
      ht := ht
      hres := hres
      pi := pi
      hpi := hpi
      hgen := hgen
      hdegree := hdegree
      htpos := htpos
      chiF := chiF
      chiK := S.chiK
      psiF := psiF
      psiK := S.psiK
      stationaryDepthF := chiF.conductor / 2
      conductorRemainderF := chiF.conductor % 2
      stationaryDepthK := S.chiK.conductor / 2
      conductorRemainderK := S.chiK.conductor % 2
      hF := S.hF
      hK := S.hK
      hminimal := hminimal
      hhigh := S.hhigh
      hstrict := S.hstrict
      hchi := S.hchi
      hpsi := S.hpsi
      tau := S.tau
      htau := S.htau
      gammaF := S.gammaF
      hgammaF := S.hgammaF
      selected := Q.parameters
      criticalInputs := inputs
      criticalInputs_row := ?_
      criticalInputs_stationaryPairs := ?_
      criticalInputs_localData := ?_
      criticalInputs_boundaryCoordinates := ?_ }
  all_goals
    rcases Classical.choose_spec hinputs with
      ⟨hrow, hstationaryPairs, hlocalData, hboundaryCoordinates⟩
    assumption

/- Data and proof transport from the source high product to the computational
datum used by the exact phase assembly. -/
private structure WildQuadraticHighTransportData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal)
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF) where
  data : FirstMainComputationalData F K chiF.character psiF.character
  base_eq : data.twistData 1 = chiF
  baseAdd_eq : psiF = data.baseAddChar
  base_decomposition : IsStationaryConductorDecomposition
    (data.twistData 1).conductor (chiF.conductor / 2) (chiF.conductor % 2)
  minimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1)
  strict : t + 1 < (data.twistData 1).conductor
  chiK_character : S.chiK.character =
    (data.twistData 1).character.compNorm
  psiK_character : S.psiK.character =
    data.baseAddChar.character.compTrace
  gammaF_order : ord F (S.gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  product : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree
    htpos data S.chiK S.psiK base_decomposition S.hK minimal strict
      chiK_character psiK_character S.tau S.htau S.gammaF gammaF_order
  product_pairs : highWildQuadraticSelectedStationaryPairs
    product.parameters.representatives =
      highWildQuadraticSelectedStationaryPairs Q.parameters.representatives
  product_u : product.parameters.representatives.u =
    Q.parameters.representatives.u
  product_n : product.parameters.representatives.n =
    Q.parameters.representatives.n

/- Construct the computational datum and transport a simultaneous high
product to it while preserving all selected representative values. -/
set_option maxHeartbeats 4000000 in
private noncomputable def wildQuadraticPreparationHighTransportData
    {F K : Type}
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
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal)
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF) :
    WildQuadraticHighTransportData F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal S Q := by
  let data := wildQuadraticPreparationComputationalData F K ht hres pi hpi
    hgen chiF S.chiK psiF S.psiK S.hchi S.hpsi
  have hbase : data.twistData 1 = chiF := by
    exact wildQuadraticPreparationComputationalData_twist_one F K ht hres
      pi hpi hgen chiF S.chiK psiF S.psiK S.hchi S.hpsi
  have hadd : psiF = data.baseAddChar := by
    rfl
  have hFdata : IsStationaryConductorDecomposition
      (data.twistData 1).conductor (chiF.conductor / 2)
        (chiF.conductor % 2) := by
    rw [hbase]
    exact S.hF
  have hmindata : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1) := by
    rw [hbase]
    exact hminimal
  have hstrictdata : t + 1 < (data.twistData 1).conductor := by
    rw [hbase]
    exact S.hstrict
  have hchidata : S.chiK.character =
      (data.twistData 1).character.compNorm := by
    rw [hbase]
    exact S.hchi
  have hpsidata : S.psiK.character =
      data.baseAddChar.character.compTrace := by
    simpa only [data, wildQuadraticPreparationComputationalData] using S.hpsi
  have hgammaFdata : ord F (S.gammaF : F) =
      ((((data.twistData 1).conductor : ℤ) +
        data.baseAddChar.conductor : ℤ) : WithTop ℤ) := by
    rw [hbase]
    simpa only [data, wildQuadraticPreparationComputationalData] using
      S.hgammaF
  let Qdata : QuadraticHighPhaseSource F K ht hres pi hpi hgen hdegree
      htpos data S.chiK S.psiK hFdata S.hK hmindata hstrictdata hchidata
        hpsidata S.tau S.htau S.gammaF hgammaFdata := by
    exact wildQuadraticPreparationTransportHighProduct ht hres pi hpi hgen
      hdegree htpos chiF (data.twistData 1) hbase.symm S.chiK psiF
        data.baseAddChar hadd S.psiK S.hF hFdata S.hK hminimal hmindata
          S.hhigh hstrictdata.le S.hchi hchidata S.hpsi hpsidata S.tau
            S.htau S.gammaF S.hgammaF hgammaFdata Q
  have hQvalues := wildQuadraticPreparationTransportHighProduct_values ht
    hres pi hpi hgen hdegree htpos chiF (data.twistData 1) hbase.symm
      S.chiK psiF data.baseAddChar hadd S.psiK S.hF hFdata S.hK hminimal
        hmindata S.hhigh hstrictdata.le S.hchi hchidata S.hpsi hpsidata
          S.tau S.htau S.gammaF S.hgammaF hgammaFdata Q
  exact
    { data := data
      base_eq := hbase
      baseAdd_eq := hadd
      base_decomposition := hFdata
      minimal := hmindata
      strict := hstrictdata
      chiK_character := hchidata
      psiK_character := hpsidata
      gammaF_order := hgammaFdata
      product := Qdata
      product_pairs := hQvalues.1
      product_u := hQvalues.2.1
      product_n := hQvalues.2.2 }

set_option maxHeartbeats 4000000 in
/-- The four computational high phases retain the stationary pairs of the
original simultaneous product, independently of their critical coordinates. -/
private theorem wildQuadraticPreparationHighPhasePairs
    {F K : Type}
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
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal)
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF)
    (T : WildQuadraticHighTransportData F K ht htpos hres pi hpi hgen
      hdegree chiF psiF hminimal S Q)
    (CUp : LamprechtCriticalCoordinate K (S.chiK.conductor / 2)
      (S.chiK.conductor % 2))
    (CBase : LamprechtCriticalCoordinate F (chiF.conductor / 2)
      (chiF.conductor % 2))
    (Ctau : LamprechtCriticalCoordinate F
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2))
    (CTwist : LamprechtCriticalCoordinate F (chiF.conductor / 2)
      (chiF.conductor % 2)) :
    let extension := highQuadraticUpstairsPhaseForComputationalData F K ht
      hres pi hpi hgen hdegree htpos T.data S.chiK S.psiK T.base_decomposition
        S.hK T.minimal T.strict T.chiK_character T.psiK_character S.tau S.htau
          S.gammaF T.gammaF_order T.product CUp
    let tauRow := highQuadraticTauPhaseForComputationalData F K ht hres pi
      hpi hgen hdegree htpos T.data S.chiK S.psiK T.base_decomposition S.hK
        T.minimal T.strict T.chiK_character T.psiK_character S.tau S.htau
          S.gammaF T.gammaF_order T.product Ctau
    let base := highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree
      htpos T.data S.chiK S.psiK T.base_decomposition S.hK T.minimal T.strict
        T.chiK_character T.psiK_character S.tau S.htau S.gammaF T.gammaF_order
          T.product CBase
    let twist := highQuadraticTwistPhaseForComputationalData F K ht hres pi
      hpi hgen hdegree htpos T.data S.chiK S.psiK T.base_decomposition S.hK
        T.minimal T.strict T.chiK_character T.psiK_character S.tau S.htau
          S.gammaF T.gammaF_order T.product CTwist
    let pairs := highWildQuadraticSelectedStationaryPairs
      Q.parameters.representatives
    extension.selectedStationaryPair = pairs.chiK ∧
      tauRow.selectedStationaryPair = pairs.tau ∧
      base.selectedStationaryPair = pairs.chiF ∧
      twist.selectedStationaryPair = pairs.tauChiF := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← T.product_pairs]
    unfold highQuadraticUpstairsPhaseForComputationalData
    rw [selectedStationaryPair_transport]
    unfold highQuadraticUpstairsPhaseSource
      WildQuadraticHighProductData.upstairsPhase
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    unfold WildQuadraticHighProductData.upstairsRepresentative
      StationaryClassRepresentative.ofCoefficientRepresentative
      highWildQuadraticSelectedStationaryPairs
    congr 1
    exact T.product.upstairs_formula
  · rw [← T.product_pairs]
    unfold highQuadraticTauPhaseForComputationalData
    rw [selectedStationaryPair_transport]
    unfold WildQuadraticHighProductData.tauPhase
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    unfold WildQuadraticHighProductData.tauRepresentative
      StationaryClassRepresentative.ofCoefficientRepresentative
      highWildQuadraticSelectedStationaryPairs
    rfl
  · rw [← T.product_pairs]
    unfold highQuadraticBasePhaseSource
      WildQuadraticHighProductData.basePhase
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    unfold WildQuadraticHighProductData.baseRepresentative
      StationaryClassRepresentative.ofCoefficientRepresentative
      highWildQuadraticSelectedStationaryPairs
    congr 1
    exact T.product.beta_factor_formula
  · rw [← T.product_pairs]
    unfold highQuadraticTwistPhaseForComputationalData
    rw [selectedStationaryPair_transport]
    unfold WildQuadraticHighProductData.twistPhase
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    unfold WildQuadraticHighProductData.twistRepresentative
      StationaryClassRepresentative.ofCoefficientRepresentative
      highWildQuadraticSelectedStationaryPairs
    congr 1
    exact T.product.twist_factor_formula

/- The exact assembly stage: phase data, transported public assembly, actual
stationary rows, and the coordinate compatibility tying them together. -/
private structure WildQuadraticHighAssemblyData
    (F K : Type)
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
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal)
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF)
    (T : WildQuadraticHighTransportData F K ht htpos hres pi hpi hgen
      hdegree chiF psiF hminimal S Q) where
  phaseData : FirstMainPhaseData F K chiF.character psiF.character T.data
  assembly : ExactQuadraticPhaseAssembly F K chiF.character psiF.character
    T.data phaseData (t := t) (m := chiF.conductor)
  indexing_tau : assembly.indexing.tau = S.tau
  rows : WildQuadraticActualPhaseRows
    (wildQuadraticPreparationHighCoefficientCore ht htpos hres pi hpi hgen
      hdegree chiF psiF hminimal S Q).toView T.data phaseData assembly
  coordinates : WildQuadraticCommonCoordinateCompatibility
    (wildQuadraticPreparationHighCoefficientCore ht htpos hres pi hpi hgen
      hdegree chiF psiF hminimal S Q).toView T.data phaseData assembly

/- Assemble the four transported stationary phases and prove that their
public coordinates are exactly those of the coefficient view. -/
set_option maxHeartbeats 4000000 in
private noncomputable def wildQuadraticPreparationHighAssemblyData
    {F K : Type}
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
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal)
    (Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF)
    (T : WildQuadraticHighTransportData F K ht htpos hres pi hpi hgen
      hdegree chiF psiF hminimal S Q) :
    WildQuadraticHighAssemblyData F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal S Q T := by
  classical
  let P := wildQuadraticPreparationHighCoefficientCore ht htpos hres pi hpi
    hgen hdegree chiF psiF hminimal S Q
  let V := P.toView
  let data := T.data
  have hbase := T.base_eq
  have hFdata := T.base_decomposition
  have hmindata := T.minimal
  have hstrictdata := T.strict
  have hchidata := T.chiK_character
  have hpsidata := T.psiK_character
  have hgammaFdata := T.gammaF_order
  let Qdata := T.product
  have hQpairs := T.product_pairs
  have hQu := T.product_u
  have hQn := T.product_n
  let residual := phaseReductionResidualCoordinateSource F K hres pi hpi
  let CUp := residual.upperCriticalCoordinate S.hK
  let CBase := residual.lowerCriticalCoordinate hFdata
  let hTau := wildQuadraticHighTauDecomposition
    F K ht hres pi hpi hgen htpos S.tau S.htau
  let Ctau := residual.lowerCriticalCoordinate hTau
  let CTwist := residual.lowerCriticalCoordinate hFdata
  let extension := highQuadraticUpstairsPhaseForComputationalData F K ht
    hres pi hpi hgen hdegree htpos data S.chiK S.psiK hFdata S.hK
      hmindata hstrictdata hchidata hpsidata S.tau S.htau S.gammaF
        hgammaFdata Qdata CUp
  let tauRow := highQuadraticTauPhaseForComputationalData F K ht hres pi
    hpi hgen hdegree htpos data S.chiK S.psiK hFdata S.hK hmindata
      hstrictdata hchidata hpsidata S.tau S.htau S.gammaF hgammaFdata
        Qdata Ctau
  let base := highQuadraticBasePhaseSource F K ht hres pi hpi hgen hdegree
    htpos data S.chiK S.psiK hFdata S.hK hmindata hstrictdata hchidata
      hpsidata S.tau S.htau S.gammaF hgammaFdata Qdata CBase
  let twist := highQuadraticTwistPhaseForComputationalData F K ht hres pi
    hpi hgen hdegree htpos data S.chiK S.psiK hFdata S.hK hmindata
      hstrictdata hchidata hpsidata S.tau S.htau S.gammaF hgammaFdata
        Qdata CTwist
  let index := lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen
    hdegree
  have index_true : index true = 1 := by
    exact lowQuadraticNormCharacterIndex_true F K ht hres pi hpi hgen
      hdegree
  have index_false : index false = S.tau := by
    obtain ⟨b, hb⟩ := index.surjective S.tau
    cases b with
    | false => exact hb
    | true =>
        exfalso
        apply S.htau
        rw [← hb, index_true]
  let D := wildQuadraticPreparationPhaseData data S.tau index index_true
    index_false extension tauRow base twist
  have hExtension : D.extension = LocalPhaseData.stationary extension := by
    rfl
  have hBase : D.twist 1 = LocalPhaseData.stationary base := by
    simp [D, wildQuadraticPreparationPhaseData]
  have hNorm : D.normCharacter S.tau =
      LocalPhaseData.stationary tauRow := by
    simp [D, wildQuadraticPreparationPhaseData, S.htau]
  have hTwist : D.twist S.tau = LocalPhaseData.stationary twist := by
    simp [D, wildQuadraticPreparationPhaseData, S.htau]
  let C := highWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree
    htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
      S.hpsi S.tau S.htau S.gammaF S.hgammaF Q.parameters
  have hopp : C.OppositeNoncancellation :=
    highWildQuadraticCommonCorrection_oppositeNoncancellation ht hres pi
      hpi hgen hdegree htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal
        S.hhigh S.hchi S.hpsi S.tau S.htau S.gammaF S.hgammaF Q.parameters
  let raw := wildQuadraticPreparationRawCoordinates C hopp
  let hraw : QuadraticRawRatioCoordinates F K
      (Qdata.parameters.representatives.u : K)
        Qdata.parameters.representatives.n :=
    wildQuadraticPreparationTransportRawCoordinates
      (congrArg Units.val hQu) hQn raw
  let B := qBackedExactQuadraticAssemblyFromActualRows F K ht hres pi hpi
    hgen hdegree htpos data D S.chiK S.psiK hFdata S.hK hmindata
      hstrictdata hchidata hpsidata S.tau S.htau S.gammaF hgammaFdata Qdata
        CUp CBase Ctau CTwist hExtension hBase hNorm hTwist index index_true
          index_false hraw
  have hm : (data.twistData 1).conductor = chiF.conductor :=
    congrArg LocalQuasiCharData.conductor hbase
  let A : ExactQuadraticPhaseAssembly F K chiF.character psiF.character
      data D (t := t) (m := chiF.conductor) :=
    wildQuadraticPreparationTransportAssembly hm B.assembly
  rcases wildQuadraticPreparationTransportAssembly_fields hm B.assembly with
    ⟨hAindexing, hAA, hAu, hAn, hAzZero, hAzOne⟩
  have hAtau : A.indexing.tau = S.tau := by
    rw [hAindexing]
    exact B.indexing_tau
  obtain ⟨extensionPair, tauPair, basePair, twistPair⟩ :=
    wildQuadraticPreparationHighPhasePairs ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal S Q T CUp CBase Ctau CTwist
  let rows : WildQuadraticActualPhaseRows V data D A :=
    wildQuadraticPreparationActualRowsOfTauEq S.tau hAtau extension tauRow
      base twist hExtension hNorm hBase hTwist extensionPair tauPair basePair
        twistPair
  have coordinates : WildQuadraticCommonCoordinateCompatibility V data D A := by
    refine
      { baseData_eq := ?_
        baseAddData_eq := ?_
        tauData_eq := ?_
        A_eq := ?_
        u_eq := ?_
        n_eq := ?_
        zZero_eq := ?_
        zOne_eq := ?_ }
    · change data.twistData 1 = chiF
      exact hbase
    · change data.baseAddChar = psiF
      exact T.baseAdd_eq.symm
    · rw [hAtau]
      apply LocalQuasiCharData.ext_character F
      rw [data.normCharacterData_character]
      rfl
    · rw [hAA]
      calc
        B.assembly.A =
            (highWildQuadraticSelectedStationaryPairs
              Qdata.parameters.representatives).tau.ratio := by
          rw [(highWildQuadraticSelectedStationaryPairs_ratios
            Qdata.parameters.representatives).2.1]
          simp only [B, qBackedExactQuadraticAssemblyFromActualRows,
            qBackedExactQuadraticAssembly, Units.val_div_eq_div_val]
        _ = (highWildQuadraticSelectedStationaryPairs
              Q.parameters.representatives).tau.ratio := by
          rw [hQpairs]
        _ = V.stationaryPairs.tau.ratio := rfl
    · rw [hAu, B.ratio_u_source, hQu]
      rfl
    · rw [hAn, B.ratio_n_source, hQn]
      rfl
    · rw [hAzZero]
      rfl
    · rw [hAzOne]
      rfl
  exact
    { phaseData := D
      assembly := A
      indexing_tau := hAtau
      rows := rows
      coordinates := coordinates }


/- Build the complete q-free strict-high package from the live public high
table.  The product witness, coefficient input, four stationary rows, and all
coordinates are retained from one simultaneous high choice. -/
set_option maxHeartbeats 4000000 in
private noncomputable def wildQuadraticPreparationHighPackage
    {F K : Type}
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
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticHighSetup F K ht htpos hres pi hpi hgen hdegree
      chiF psiF hminimal) :
    WildQuadraticQFreePhasePackage F K t chiF psiF := by
  classical
  let Q : WildQuadraticHighProductData F K ht hres pi hpi hgen hdegree
      htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh S.hchi
        S.hpsi S.tau S.htau S.gammaF S.hgammaF :=
    Classical.choice
      ((highConductorParameterTable.highProduct F K ht hres pi hpi hgen).wildQuadratic
        hdegree htpos chiF S.chiK psiF S.psiK S.hF S.hK
          hminimal S.hhigh S.hchi S.hpsi S.tau S.htau S.gammaF S.hgammaF)
  let P := wildQuadraticPreparationHighCoefficientCore ht htpos hres pi hpi
    hgen hdegree chiF psiF hminimal S Q
  let V := P.toView
  let T := wildQuadraticPreparationHighTransportData ht htpos hres pi hpi
    hgen hdegree chiF psiF hminimal S Q
  let E := wildQuadraticPreparationHighAssemblyData ht htpos hres pi hpi
    hgen hdegree chiF psiF hminimal S Q T
  let data := T.data
  have hbase := T.base_eq
  have hmindata := T.minimal
  let D := E.phaseData
  let A := E.assembly
  have hAtau := E.indexing_tau
  let rows : WildQuadraticActualPhaseRows V data D A := E.rows
  have coordinates : WildQuadraticCommonCoordinateCompatibility V data D A :=
    E.coordinates
  let common : WildQuadraticCommonHigherData F K t chiF psiF V :=
    { chiFData_eq := rfl
      psiF_eq := rfl
      data := data
      phaseData := D
      assembly := A
      coordinates := coordinates }
  have htauConductor : V.tauData.conductor = t + 1 := by
    change
      (wildQuadraticHighTauData F K ht hres pi hpi hgen S.tau
        S.htau).conductor = t + 1
    rw [wildQuadraticHighTauData, quasiCharDataOfIsConductor_conductor]
  have hAIndexingNe : A.indexing.tau ≠ 1 := by
    rw [hAtau]
    exact S.htau
  have htwistConductor :
      (data.twistData A.indexing.tau).conductor =
        max chiF.conductor (t + 1) := by
    have hcond := minimalOrbit_nontrivialTwist_isConductor F K ht hres pi hpi
      hgen (data.twistData 1) hmindata A.indexing.tau hAIndexingNe
    rw [hbase] at hcond
    have hcond' : IsMultiplicativeConductor F
        (data.twistData A.indexing.tau).character
          (max chiF.conductor (t + 1)) := by
      rw [data.twistData_character]
      exact hcond
    exact ((data.twistData A.indexing.tau).conductor_eq_of_isConductor
      hcond').symm
  let coordinate : WildQuadraticPositivePolarCoordinateTransport F K V rows :=
    WildQuadraticHighParameterData.coordinateTransport F K ht hres pi hpi hgen
      hdegree htpos chiF S.chiK psiF S.psiK S.hF S.hK hminimal S.hhigh
        S.hchi S.hpsi S.tau S.htau S.gammaF S.hgammaF Q.parameters S.hstrict V
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) rows coordinates
  let continuation : ∀ source : V.criticalInputs.PositivePolarSource,
      WildQuadraticPositivePolarContinuation F K V source rows :=
    wildQuadraticHighContinuationFromCoordinate rows coordinates S.hstrict
      htauConductor htwistConductor coordinate
  exact
    { view := V
      common := common
      rows := by
        simpa only [common, P,
          wildQuadraticPreparationHighCoefficientCore] using rows
      continuation := continuation }

/-! ## The q-free all-even completion -/

private theorem wildQuadraticEvenRow_linearization
    {E : Type}
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (S : LocalLamprechtPhaseData E chi psi)
    (hS : S.IsEven)
    (x : E) (hx : x ∈ lattice E ((chi.conductor / 2 : ℕ) : ℤ))
    (z : Eˣ) (hz : (z : E) = 1 + x) :
    chi.character z =
      psi.character (S.selectedStationaryPair.ratio * x) := by
  cases S with
  | even d hm hlarge Gamma c hc =>
      have hd : chi.conductor / 2 = d := by omega
      let xlat : lattice E (d : ℤ) :=
        ⟨x, by simpa only [hd] using hx⟩
      have hlin := stationaryNumeratorClass_linearization E chi psi
        (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 0
          (by omega) (by simpa using hm) hlarge)
        Gamma Gamma.property c hc xlat
      have hunit : z = positiveUnitOfLattice E
          (lamprechtFormula_stationaryDepth E chi d 0
            (by omega) (by simpa using hm) hlarge).pos xlat := by
        apply Units.ext
        rw [hz]
        rfl
      rw [hunit, hlin]
      apply congrArg psi.character
      dsimp only [LocalLamprechtPhaseData.selectedStationaryPair,
        WildQuadraticStationaryPair.ratio, xlat]
      field_simp [Units.ne_zero (Gamma : Eˣ)]
  | odd =>
      simp [LocalLamprechtPhaseData.IsEven] at hS

private theorem wildQuadraticPreparation_tau_ne_one
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    {data : FirstMainComputationalData F K globalChi globalPsi}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    {t m : ℕ}
    {A : ExactQuadraticPhaseAssembly F K globalChi globalPsi data D
      (t := t) (m := m)} : A.indexing.tau ≠ 1 := by
  intro htau
  have hindex : A.indexing.index false = A.indexing.index true := by
    rw [A.indexing.index_false, htau, A.indexing.index_true]
  exact Bool.false_ne_true (A.indexing.index.injective hindex)

private theorem wildQuadraticPreparation_tau_conductor_eq
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    {data : FirstMainComputationalData F K globalChi globalPsi}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    {t m : ℕ}
    {A : ExactQuadraticPhaseAssembly F K globalChi globalPsi data D
      (t := t) (m := m)}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    (data.normCharacterData A.indexing.tau).conductor = t + 1 := by
  have hcond : IsMultiplicativeConductor F
      (data.normCharacterData A.indexing.tau).character (t + 1) := by
    rw [data.normCharacterData_character]
    exact ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
      A.indexing.tau wildQuadraticPreparation_tau_ne_one
  exact ((data.normCharacterData A.indexing.tau).conductor_eq_of_isConductor
    hcond).symm

private theorem wildQuadraticPreparation_base_conductor_eq
    {F K : Type}
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
    {t m : ℕ}
    {W : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K W.chiFData.character
      W.psiF.character}
    {D : FirstMainPhaseData F K W.chiFData.character W.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K W.chiFData.character
      W.psiF.character data D (t := t) (m := m)}
    (coordinates : WildQuadraticCommonCoordinateCompatibility W data D A) :
    W.chiFData.conductor = m := by
  calc
    W.chiFData.conductor = (data.twistData 1).conductor := by
      rw [coordinates.baseData_eq]
    _ = A.baseData.conductor := by rw [A.baseData_eq]
    _ = m := A.baseConductor

private theorem wildQuadraticPreparation_twist_conductor_eq
    {F K : Type}
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
    {t m : ℕ}
    {W : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K W.chiFData.character
      W.psiF.character}
    {D : FirstMainPhaseData F K W.chiFData.character W.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K W.chiFData.character
      W.psiF.character data D (t := t) (m := m)}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W data D A)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W.chiFData) :
    (data.twistData A.indexing.tau).conductor = max m (t + 1) := by
  have hcond := minimalOrbit_nontrivialTwist_isConductor F K ht hres pi hpi
    hgen W.chiFData hminimal A.indexing.tau
      wildQuadraticPreparation_tau_ne_one
  have hcond' : IsMultiplicativeConductor F
      (data.twistData A.indexing.tau).character (max m (t + 1)) := by
    rw [data.twistData_character]
    simpa only [wildQuadraticPreparation_base_conductor_eq coordinates] using
      hcond
  exact ((data.twistData A.indexing.tau).conductor_eq_of_isConductor
    hcond').symm

private theorem wildQuadraticPreparation_isAllEven_mParity
    {R : WildQuadraticCoefficientRow} (hR : R.IsAllEven) :
    R.mParity = .even := by
  cases hR <;> rfl

private theorem wildQuadraticPreparation_isAllEven_TParity
    {R : WildQuadraticCoefficientRow} (hR : R.IsAllEven) :
    R.TParity = .even := by
  cases hR <;> rfl

private theorem wildQuadraticPreparation_boundary_denominator_order
    {F K : Type}
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
    {t m : ℕ}
    {W : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K W.chiFData.character
      W.psiF.character}
    {D : FirstMainPhaseData F K W.chiFData.character W.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K W.chiFData.character
      W.psiF.character data D (t := t) (m := m)}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (rows : WildQuadraticActualPhaseRows W data D A)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W data D A)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W.chiFData)
    (hboundary : m = t + 1) :
    ord F W.correction.denominator = (0 : WithTop ℤ) := by
  have htauConductor := wildQuadraticPreparation_tau_conductor_eq
    (A := A) ht hres pi hpi hgen
  have htwistConductor := wildQuadraticPreparation_twist_conductor_eq
    (A := A) ht hres pi hpi hgen coordinates hminimal
  have htauRatio := rows.tau.selectedStationaryPair_ratio_order
  have htwistRatio := rows.twist.selectedStationaryPair_ratio_order
  rw [rows.tau_pair, htauConductor, coordinates.baseAddData_eq] at htauRatio
  have hmax : max m (t + 1) = t + 1 := by rw [hboundary, max_self]
  rw [rows.twist_pair, htwistConductor, coordinates.baseAddData_eq,
    hmax] at htwistRatio
  have htauRatio_ne : W.stationaryPairs.tau.ratio ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [htauRatio]
    exact WithTop.coe_ne_top
  have hden : W.correction.denominator =
      W.stationaryPairs.tauChiF.ratio / W.stationaryPairs.tau.ratio := by
    rw [W.tauChiF_ratio]
    apply (eq_div_iff htauRatio_ne).2
    dsimp only [WildQuadraticCommonCorrectionData.denominator]
    ring
  rw [hden, ord_div, htwistRatio, htauRatio]
  simp

private theorem wildQuadraticPreparation_allEven_xy_mem
    {F K : Type}
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
    {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (W0 : WildQuadraticAllEvenCoefficientView F K t m)
    (data0 : FirstMainComputationalData F K W0.chiFData.character
      W0.psiF.character)
    (D0 : FirstMainPhaseData F K W0.chiFData.character W0.psiF.character
      data0)
    (A0 : ExactQuadraticPhaseAssembly F K W0.chiFData.character
      W0.psiF.character data0 D0 (t := t) (m := m))
    (rows : WildQuadraticActualPhaseRows W0.toCommon data0 D0 A0)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W0.toCommon
      data0 D0 A0)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W0.chiFData) :
    W0.correction.x ∈ lattice F ((m / 2 : ℕ) : ℤ) ∧
      W0.correction.y ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
  have hmParity : WildQuadraticConductorParity.ofConductor m = .even := by
    have hmgt := W0.conductor_gt_one
    rw [← show m - 1 + 1 = m by omega,
      ← WildQuadraticCoefficientRow.ofConductors_mParity (m - 1) t,
      ← W0.criticalInputs_row]
    exact wildQuadraticPreparation_isAllEven_mParity W0.isAllEven
  have hTParity :
      WildQuadraticConductorParity.ofConductor (t + 1) = .even := by
    rw [← WildQuadraticCoefficientRow.ofConductors_TParity (m - 1) t,
      ← W0.criticalInputs_row]
    exact wildQuadraticPreparation_isAllEven_TParity W0.isAllEven
  have hmEven : Even m :=
    (WildQuadraticConductorParity.ofConductor_eq_even_iff m).mp hmParity
  have hTEven : Even (t + 1) :=
    (WildQuadraticConductorParity.ofConductor_eq_even_iff (t + 1)).mp
      hTParity
  obtain ⟨jm, hjm⟩ := hmEven
  obtain ⟨jT, hjT⟩ := hTEven
  have hrowEven : W0.coefficients.1.row.IsAllEven := by
    change
      (W0.criticalInputs.toAllEvenCoefficientData W0.isAllEven).row.IsAllEven
    rw [WildQuadraticCoefficientInputs.toAllEvenCoefficientData_row]
    exact W0.isAllEven
  have hrow : W0.coefficients.1.row ≠ .boundaryOdd := by
    intro h
    rw [h] at hrowEven
    cases hrowEven
  have hcase := wildQuadratic_nonboundary_depthCase W0.conductor_gt_one
    W0.coefficients hrow
  let a : ℤ := ((t + 1 : ℕ) : ℤ) - (m : ℤ)
  have hu : (W0.correction.u : K) ∈ lattice K a := by
    rw [mem_lattice, W0.correction.source_order]
  have hs : W0.correction.s ∈
      lattice F ((a + ((t + 1 : ℕ) : ℤ)) / 2) := by
    have hs' := trace_mem_lattice_floor F K pi hpi hgen a hu
    rw [W0.correction.differentExponent_eq,
      W0.correction.ramificationIndex_eq_two] at hs'
    norm_num at hs'
    rw [mem_lattice]
    simpa only [WildQuadraticCommonCorrectionData.s, Nat.cast_add,
      Nat.cast_one] using hs'
  cases hcase with
  | below hbelow =>
      have ha : 0 < a := by dsimp only [a]; omega
      have hne : ord F (1 : F) ≠ ord F (W0.correction.n : F) := by
        rw [ord_one, W0.correction.target_order]
        change (0 : WithTop ℤ) ≠ (a : WithTop ℤ)
        exact ne_of_lt (by exact_mod_cast ha)
      have hden : ord F W0.correction.denominator = (0 : WithTop ℤ) := by
        rw [WildQuadraticCommonCorrectionData.denominator,
          ord_add_eq_min F hne, ord_one, W0.correction.target_order,
          min_eq_left]
        change (0 : WithTop ℤ) ≤ (a : WithTop ℤ)
        exact_mod_cast ha.le
      constructor
      · rw [W0.correction.x_eq]
        apply (div_mem_lattice_iff F W0.correction.denominator
          (-W0.correction.s) 0 ((m / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          (0 : ℤ) + (m / 2 : ℕ) ≤
            (a + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
        exact neg_mem_lattice F hs
      · rw [W0.correction.y_eq]
        apply (div_mem_lattice_iff F W0.correction.denominator
          W0.correction.s 0 (((t + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          (0 : ℤ) + ((t + 1) / 2 : ℕ) ≤
            (a + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
        exact hs
  | boundaryEven hboundary _ =>
      have ha : a = 0 := by dsimp only [a]; omega
      have hden := wildQuadraticPreparation_boundary_denominator_order
        (A := A0) ht hres pi hpi hgen rows coordinates hminimal hboundary
      constructor
      · rw [W0.correction.x_eq]
        apply (div_mem_lattice_iff F W0.correction.denominator
          (-W0.correction.s) 0 ((m / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          (0 : ℤ) + (m / 2 : ℕ) ≤
            (a + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
        exact neg_mem_lattice F hs
      · rw [W0.correction.y_eq]
        apply (div_mem_lattice_iff F W0.correction.denominator
          W0.correction.s 0 (((t + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          (0 : ℤ) + ((t + 1) / 2 : ℕ) ≤
            (a + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
        exact hs
  | above habove =>
      have ha : a < 0 := by dsimp only [a]; omega
      have hne : ord F (1 : F) ≠ ord F (W0.correction.n : F) := by
        rw [ord_one, W0.correction.target_order]
        change (0 : WithTop ℤ) ≠ (a : WithTop ℤ)
        exact Ne.symm (ne_of_lt (by exact_mod_cast ha))
      have hden : ord F W0.correction.denominator = (a : WithTop ℤ) := by
        rw [WildQuadraticCommonCorrectionData.denominator,
          ord_add_eq_min F hne, ord_one, W0.correction.target_order,
          min_eq_right]
        change (a : WithTop ℤ) ≤ (0 : WithTop ℤ)
        exact_mod_cast ha.le
      constructor
      · rw [W0.correction.x_eq]
        apply (div_mem_lattice_iff F W0.correction.denominator
          (-W0.correction.s) a ((m / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          a + (m / 2 : ℕ) ≤
            (a + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
        exact neg_mem_lattice F hs
      · rw [W0.correction.y_eq]
        apply (div_mem_lattice_iff F W0.correction.denominator
          W0.correction.s a (((t + 1) / 2 : ℕ) : ℤ) hden).2
        apply lattice_antitone F (show
          a + ((t + 1) / 2 : ℕ) ≤
            (a + ((t + 1 : ℕ) : ℤ)) / 2 by omega)
        exact hs

/-- The correction lattice bounds put both even Lamprecht rows in their
linearization ranges. Transport their character values to the exact assembly. -/
private theorem wildQuadraticPreparation_allEven_characterLinearizations
    {F K : Type}
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
    {t m : ℕ}
    (W0 : WildQuadraticAllEvenCoefficientView F K t m)
    (data0 : FirstMainComputationalData F K W0.chiFData.character
      W0.psiF.character)
    (D0 : FirstMainPhaseData F K W0.chiFData.character W0.psiF.character
      data0)
    (A0 : ExactQuadraticPhaseAssembly F K W0.chiFData.character
      W0.psiF.character data0 D0 (t := t) (m := m))
    (rows : WildQuadraticAllEvenPhaseRowCompatibility W0 data0 D0 A0)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W0.toCommon
      data0 D0 A0)
    (htauConductor :
      (data0.normCharacterData A0.indexing.tau).conductor = t + 1)
    (hxy : W0.correction.x ∈ lattice F ((m / 2 : ℕ) : ℤ) ∧
      W0.correction.y ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ)) :
    W0.chiFData.character A0.zZero =
        W0.psiF.character (A0.A * A0.n * A0.x) ∧
      A0.indexing.tau.1 A0.zOne = W0.psiF.character (A0.A * A0.y) := by
  have hbaseConductor : (data0.twistData 1).conductor = m := by
    rw [coordinates.baseData_eq,
      wildQuadraticPreparation_base_conductor_eq (A := A0) coordinates]
  have hx : A0.x ∈
      lattice F (((data0.twistData 1).conductor / 2 : ℕ) : ℤ) := by
    rw [hbaseConductor, coordinates.x_eq]
    exact hxy.1
  have hy : A0.y ∈ lattice F
      (((data0.normCharacterData A0.indexing.tau).conductor / 2 : ℕ) : ℤ) := by
    rw [htauConductor, coordinates.y_eq]
    exact hxy.2
  have hbaseLin := wildQuadraticEvenRow_linearization rows.actualRows.base
    rows.base_even A0.x hx A0.zZero A0.zZero_eq
  have htauLin := wildQuadraticEvenRow_linearization rows.actualRows.tau
    rows.tau_even A0.y hy A0.zOne A0.zOne_eq
  constructor
  · calc
      W0.chiFData.character A0.zZero =
          (data0.twistData 1).character A0.zZero := by
            rw [coordinates.baseData_eq]
      _ = data0.baseAddChar.character
          (rows.actualRows.base.selectedStationaryPair.ratio * A0.x) :=
        hbaseLin
      _ = W0.psiF.character
          (rows.actualRows.base.selectedStationaryPair.ratio * A0.x) := by
        rw [congrArg LocalAddCharData.character coordinates.baseAddData_eq]
      _ = W0.psiF.character (A0.A * A0.n * A0.x) := by
        rw [rows.actualRows.base_pair,
          W0.chiF_ratio, ← coordinates.A_eq, ← coordinates.n_eq]
  · calc
      A0.indexing.tau.1 A0.zOne =
          (data0.normCharacterData A0.indexing.tau).character A0.zOne := by
            rw [data0.normCharacterData_character]
      _ = data0.baseAddChar.character
          (rows.actualRows.tau.selectedStationaryPair.ratio * A0.y) :=
        htauLin
      _ = W0.psiF.character
          (rows.actualRows.tau.selectedStationaryPair.ratio * A0.y) := by
        rw [congrArg LocalAddCharData.character coordinates.baseAddData_eq]
      _ = W0.psiF.character (A0.A * A0.y) := by
        rw [rows.actualRows.tau_pair, ← coordinates.A_eq]

private theorem wildQuadraticPreparation_allEvenCompleteCorrection
    {F K : Type}
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
    {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (W0 : WildQuadraticAllEvenCoefficientView F K t m)
    (data0 : FirstMainComputationalData F K W0.chiFData.character
      W0.psiF.character)
    (D0 : FirstMainPhaseData F K W0.chiFData.character W0.psiF.character
      data0)
    (A0 : ExactQuadraticPhaseAssembly F K W0.chiFData.character
      W0.psiF.character data0 D0 (t := t) (m := m))
    (rows : WildQuadraticAllEvenPhaseRowCompatibility W0 data0 D0 A0)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W0.toCommon
      data0 D0 A0)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W0.chiFData) :
    A0.CompleteCorrectionData := by
  have hxy := wildQuadraticPreparation_allEven_xy_mem ht hres pi hpi hgen
    W0 data0 D0 A0 rows.actualRows coordinates hminimal
  obtain ⟨hchiLin, htauLin⟩ :=
    wildQuadraticPreparation_allEven_characterLinearizations
      W0 data0 D0 A0 rows coordinates
      (wildQuadraticPreparation_tau_conductor_eq (A := A0)
        ht hres pi hpi hgen) hxy
  refine
    { one_add_n_ne_zero := ?_
      zZero_ratio := ?_
      zOne_ratio := ?_
      chiLinearization := hchiLin
      tauLinearization := htauLin }
  · rw [coordinates.n_eq]
    exact W0.correction.denominator_ne_zero
  · rw [coordinates.zZero_eq, coordinates.n_eq]
    unfold ExactQuadraticPhaseAssembly.dualRatio
    rw [coordinates.n_eq, coordinates.u_eq]
    rfl
  · rw [coordinates.zOne_eq, coordinates.n_eq, coordinates.u_eq]
    rfl

private noncomputable def wildQuadraticPreparation_allEvenRows
    {F K : Type}
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
    {t m : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (W0 : WildQuadraticAllEvenCoefficientView F K t m)
    (data0 : FirstMainComputationalData F K W0.chiFData.character
      W0.psiF.character)
    (D0 : FirstMainPhaseData F K W0.chiFData.character W0.psiF.character
      data0)
    (A0 : ExactQuadraticPhaseAssembly F K W0.chiFData.character
      W0.psiF.character data0 D0 (t := t) (m := m))
    (rows : WildQuadraticActualPhaseRows W0.toCommon data0 D0 A0)
    (coordinates : WildQuadraticCommonCoordinateCompatibility W0.toCommon
      data0 D0 A0)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K W0.chiFData) :
    WildQuadraticAllEvenPhaseRowCompatibility W0 data0 D0 A0 := by
  have hmParity : WildQuadraticConductorParity.ofConductor m = .even := by
    have hmgt := W0.conductor_gt_one
    rw [← show m - 1 + 1 = m by omega,
      ← WildQuadraticCoefficientRow.ofConductors_mParity (m - 1) t,
      ← W0.criticalInputs_row]
    exact wildQuadraticPreparation_isAllEven_mParity W0.isAllEven
  have hTParity :
      WildQuadraticConductorParity.ofConductor (t + 1) = .even := by
    rw [← WildQuadraticCoefficientRow.ofConductors_TParity (m - 1) t,
      ← W0.criticalInputs_row]
    exact wildQuadraticPreparation_isAllEven_TParity W0.isAllEven
  have hmEven : Even m :=
    (WildQuadraticConductorParity.ofConductor_eq_even_iff m).mp hmParity
  have hTEven : Even (t + 1) :=
    (WildQuadraticConductorParity.ofConductor_eq_even_iff (t + 1)).mp
      hTParity
  have hbaseConductor : (data0.twistData 1).conductor = m := by
    rw [coordinates.baseData_eq,
      wildQuadraticPreparation_base_conductor_eq (A := A0) coordinates]
  have htauConductor :
      (data0.normCharacterData A0.indexing.tau).conductor = t + 1 :=
    wildQuadraticPreparation_tau_conductor_eq (A := A0) ht hres pi hpi hgen
  have htwistConductor :
      (data0.twistData A0.indexing.tau).conductor = max m (t + 1) :=
    wildQuadraticPreparation_twist_conductor_eq (A := A0) ht hres pi hpi
      hgen coordinates hminimal
  have hbaseEven : Even (data0.twistData 1).conductor := by
    rw [hbaseConductor]
    exact hmEven
  have htauEven : Even
      (data0.normCharacterData A0.indexing.tau).conductor := by
    rw [htauConductor]
    exact hTEven
  have htwistEven : Even
      (data0.twistData A0.indexing.tau).conductor := by
    rw [htwistConductor]
    rcases hmEven with ⟨a, ha⟩
    rcases hTEven with ⟨b, hb⟩
    by_cases hle : m ≤ t + 1
    · rw [max_eq_right hle]
      exact ⟨b, hb⟩
    · rw [max_eq_left (by omega)]
      exact ⟨a, ha⟩
  have hchi : data0.extensionQuasiChar.character =
      W0.chiFData.character.compNorm := data0.extensionQuasiChar_character
  have hextensionEven : Even data0.extensionQuasiChar.conductor := by
    cases A0.parameterRange with
    | low hLow =>
        have heq := lowCompNorm_conductor_eq F K ht hres pi hpi hgen
          W0.chiFData hminimal data0.extensionQuasiChar hchi (by
            simpa only [
              wildQuadraticPreparation_base_conductor_eq (A := A0)
                coordinates] using hLow)
        rw [heq, wildQuadraticPreparation_base_conductor_eq
          (A := A0) coordinates]
        exact hmEven
    | high hhigh =>
        have hrel := highParameter_wildQuadratic_conductor_relation F K ht
          hres pi hpi hgen hdegree W0.chiFData data0.extensionQuasiChar
          hminimal hchi (by
            rw [wildQuadraticPreparation_base_conductor_eq
              (A := A0) coordinates]
            exact hhigh.le)
        rcases hmEven with ⟨a, ha⟩
        rcases hTEven with ⟨b, hb⟩
        refine ⟨2 * a - b, ?_⟩
        rw [wildQuadraticPreparation_base_conductor_eq
          (A := A0) coordinates] at hrel
        omega
  exact
    { actualRows := rows
      extension_even := rows.extension.isEven_of_even_conductor hextensionEven
      tau_even := rows.tau.isEven_of_even_conductor htauEven
      base_even := rows.base.isEven_of_even_conductor hbaseEven
      twist_even := rows.twist.isEven_of_even_conductor htwistEven }

/-! ## The low q-free package -/

/-- Assemble the low coefficient provenance after the critical inputs and
their matching certificates have been selected. -/
private noncomputable def wildQuadraticPreparationLowCoefficientCore
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal)
    (inputs : WildQuadraticCoefficientInputs F)
    (hrow : inputs.row = WildQuadraticCoefficientRow.ofConductors
      (chiF.conductor - 1) t)
    (hpairs : inputs.MatchesStationaryPairs
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected))
    (hlocal : inputs.MatchesLocalData
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      chiF psiF)
    (hboundary : inputs.MatchesBoundaryCriticalCoordinates) :
    WildQuadraticLowCoefficientCore F K :=
  { lowerBreak := t, stationaryDepth := chiF.conductor / 2
    conductorRemainder := chiF.conductor % 2, ht := ht, hres := hres
    pi := pi, hpi := hpi, hgen := hgen, hdegree := hdegree, chi := chiF
    chiK := S.chiK, psi := psiF, psiK := S.psiK, hminimal := hminimal
    hchi := S.hchi, hpsi := S.hpsi, hF := S.hF, hLow := S.hLow
    delta := S.delta, epsilon1 := S.epsilon1, hdelta := S.hdelta
    hepsilon1 := S.hepsilon1, hT := S.hT, hgammaF := S.hgammaF
    hgammaK := S.hgammaK, selected := S.selected, table := S.table
    criticalInputs := inputs, criticalInputs_row := hrow
    criticalInputs_stationaryPairs := hpairs
    criticalInputs_localData := hlocal
    criticalInputs_boundaryCoordinates := hboundary }

/-- Transfer the two selected critical factors to the actual phase rows
using the character indexing and stationary-row identifications. -/
private theorem wildQuadraticPreparation_lowPhaseFactors
    {F K : Type}
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
    {t m : ℕ} {V : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character
      V.psiF.character}
    {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows V data D A)
    (tau : NormCharacter F K) (hAtau : A.indexing.tau = tau)
    (tauRow : LocalLamprechtPhaseData F (data.normCharacterData tau)
      data.baseAddChar)
    (base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar)
    (hNorm : D.normCharacter tau = LocalPhaseData.stationary tauRow)
    (hBase : D.twist 1 = LocalPhaseData.stationary base)
    (htauPhase : tauRow.criticalFactor =
      quotientSourcePhase F V.criticalInputs.tauSource)
    (hbasePhase : base.criticalFactor =
      quotientSourcePhase F V.criticalInputs.chiFSource) :
    rows.tau.criticalFactor =
      quotientSourcePhase F V.criticalInputs.tauSource ∧
    rows.base.criticalFactor =
      quotientSourcePhase F V.criticalInputs.chiFSource := by
  constructor
  · calc
      rows.tau.criticalFactor =
          (D.normCharacter A.indexing.tau).criticalFactor := by
        simpa only [LocalPhaseData.criticalFactor] using
          congrArg (fun q ↦ q.criticalFactor) rows.tau_eq.symm
      _ = (D.normCharacter tau).criticalFactor := by rw [hAtau]
      _ = tauRow.criticalFactor := by
        simpa only [LocalPhaseData.criticalFactor] using
          congrArg (fun q ↦ q.criticalFactor) hNorm
      _ = quotientSourcePhase F V.criticalInputs.tauSource := htauPhase
  · calc
      rows.base.criticalFactor = (D.twist 1).criticalFactor := by
        simpa only [LocalPhaseData.criticalFactor] using
          congrArg (fun q ↦ q.criticalFactor) rows.base_eq.symm
      _ = base.criticalFactor := by
        simpa only [LocalPhaseData.criticalFactor] using
          congrArg (fun q ↦ q.criticalFactor) hBase
      _ = quotientSourcePhase F V.criticalInputs.chiFSource := hbasePhase

/-- Common low phase data and the retained source for coordinate transport. -/
private structure WildQuadraticLowCommonPackage
    (F K : Type)
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
    (t : ℕ) (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) where
  view : WildQuadraticCommonCoefficientView F K t chiF.conductor
  common : WildQuadraticCommonHigherData F K t chiF psiF view
  rows : WildQuadraticActualPhaseRows view common.data common.phaseData
    common.assembly
  lowSource : WildQuadraticLowCoordinateTransportSource F K view rows

set_option maxHeartbeats 4000000 in
/-- Select the strict-low or boundary coefficient inputs from the actual
tau, base, and twist rows, retaining their selected stationary pairs. -/
private theorem wildQuadraticPreparation_lowInputs_exists
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal)
    (data : FirstMainComputationalData F K chiF.character psiF.character)
    (hbase : data.twistData 1 = chiF) (hadd : data.baseAddChar = psiF)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (htauConductor : (data.normCharacterData tau).conductor = t + 1)
    (tauRow : LocalLamprechtPhaseData F (data.normCharacterData tau)
      data.baseAddChar)
    (base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar)
    (twist : LocalLamprechtPhaseData F (data.twistData tau) data.baseAddChar)
    (tauPairS : tauRow.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).tau)
    (basePairS : base.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).chiF)
    (twistPairS : twist.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).tauChiF) :
    ∃ I : WildQuadraticCoefficientInputs F,
      I.row = WildQuadraticCoefficientRow.ofConductors
        (chiF.conductor - 1) t ∧
      I.MatchesStationaryPairs
        (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected) ∧
      I.MatchesLocalData
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau))
        chiF psiF ∧
      I.MatchesBoundaryCriticalCoordinates ∧
      tauRow.criticalFactor = quotientSourcePhase F I.tauSource ∧
      base.criticalFactor = quotientSourcePhase F I.chiFSource := by
  classical
  let pairs := lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1
    S.selected
  let C := lowWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree
    chiF psiF hminimal S.hF S.hLow S.delta S.epsilon1 S.hdelta S.hepsilon1
      S.hT S.hgammaF S.selected
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  have htauData : data.normCharacterData tau = tauData := by
    apply LocalQuasiCharData.ext_character F
    rw [data.normCharacterData_character, quasiCharDataOfIsConductor_character]
  have hmindata : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1) := by rw [hbase]; exact hminimal
  by_cases hstrict : chiF.conductor < t + 1
  · obtain ⟨I, hrow, hp, hl, hb, htauPhase, hbasePhase⟩ :=
      wildQuadraticLowBelowInputs_exists
      S.hF.conductor_gt_one hstrict (data.normCharacterData tau)
        (data.twistData 1) data.baseAddChar htauConductor
          (congrArg LocalQuasiCharData.conductor hbase) pairs tauRow base
            tauPairS basePairS
    rw [htauData, hbase, hadd] at hl
    exact ⟨I, hrow, hp, hl, hb, htauPhase, hbasePhase⟩
  · have hboundary : chiF.conductor = t + 1 :=
      le_antisymm S.hLow (Nat.le_of_not_gt hstrict)
    have htwistConductor : (data.twistData tau).conductor = t + 1 := by
      have hc := minimalOrbit_nontrivialTwist_isConductor F K ht hres pi
        hpi hgen (data.twistData 1) hmindata tau htau
      rw [hbase] at hc
      have hc' : IsMultiplicativeConductor F
          (data.twistData tau).character (t + 1) := by
        rw [data.twistData_character]
        simpa only [hboundary, max_self] using hc
      exact ((data.twistData tau).conductor_eq_of_isConductor hc').symm
    have hnord : ord F (C.n : F) = (0 : WithTop ℤ) := by
      rw [C.target_order, hboundary]
      simp
    let n0 : unitGroup F :=
      ⟨C.n, (mem_unitGroup_iff_ord_eq_zero F C.n).2 hnord⟩
    obtain ⟨_, htauRatio, hbaseRatio, htwistRatio⟩ :=
      lowWildQuadraticSelectedStationaryPairs_ratios S.delta
        S.epsilon1 S.selected
    have hratio : pairs.tauChiF.ratio =
        pairs.tau.ratio * ((C.n : F) + 1) := by
      rw [htauRatio, htwistRatio]
      simp [C, lowWildQuadraticCommonCorrection,
        lowWildQuadraticCommonN, Units.val_div_eq_div_val,
          Units.val_mul]
    have hnres := wildQuadraticPreparation_boundaryNResidue_ne_one C
      hboundary (data.normCharacterData tau) (data.twistData tau)
        data.baseAddChar htauConductor htwistConductor pairs hratio tauRow
          twist tauPairS twistPairS
    have hchiRatio : pairs.chiF.ratio =
        pairs.tau.ratio * ((n0 : Fˣ) : F) := by
      rw [htauRatio, hbaseRatio]
      simp [n0, C, lowWildQuadraticCommonCorrection,
        lowWildQuadraticCommonN, Units.val_div_eq_div_val,
          Units.val_mul]
    obtain ⟨I, hrow, hp, hl, hb, htauPhase, hbasePhase⟩ :=
      wildQuadraticLowBoundaryInputs_exists
      S.hF.conductor_gt_one (by omega) (data.normCharacterData tau)
        (data.twistData 1) data.baseAddChar htauConductor
          (congrArg LocalQuasiCharData.conductor hbase) pairs n0 hnres
            hchiRatio tauRow base tauPairS basePairS
    rw [htauData, hbase, hadd] at hl
    exact ⟨I, hrow, hp, hl, hb, htauPhase, hbasePhase⟩

/-- Computational data and the transported low table, retaining its shared witnesses. -/
private structure WildQuadraticLowTransportData
    (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal) where
  data : FirstMainComputationalData F K chiF.character psiF.character
  base_eq : data.twistData 1 = chiF
  baseAdd_eq : data.baseAddChar = psiF
  base_decomposition : IsStationaryConductorDecomposition
    (data.twistData 1).conductor (chiF.conductor / 2) (chiF.conductor % 2)
  minimal : IsMinimalNormCharacterOrbitRepresentative F K (data.twistData 1)
  low : (data.twistData 1).conductor ≤ t + 1
  chiK_character : S.chiK.character = (data.twistData 1).character.compNorm
  psiK_character : S.psiK.character = data.baseAddChar.character.compTrace
  delta_order : ord F (S.delta : F) =
    ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  epsilon_order : ord K (S.epsilon1 : K) =
    (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ)
  gammaF_order : ord F (lowGammaF F K S.delta S.epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  selected : LowStationaryNormRepresentativePair F K (lowCriticalFloorDepth t)
    (chiF.conductor / 2)
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) S.hT)
        S.delta delta_order)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar
      base_decomposition (lowGammaF F K S.delta S.epsilon1) gammaF_order)
  table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) S.chiK data.baseAddChar S.psiK minimal chiK_character
      psiK_character base_decomposition low S.delta S.epsilon1 delta_order
        epsilon_order S.hT gammaF_order S.hgammaK selected
  selected_pairs : lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1
    selected = lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected
  selected_u : lowNormalizedRatio F K S.epsilon1 selected =
    lowNormalizedRatio F K S.epsilon1 S.selected
  selected_n : lowEpsilon F K S.epsilon1 * selected.beta / selected.alpha =
    lowWildQuadraticCommonN S.epsilon1 S.selected
  WUp : LowQuadraticUpstairsWitness F K ht hres pi hpi hgen data S.chiK S.psiK
    base_decomposition minimal chiK_character psiK_character low S.delta S.epsilon1
      delta_order epsilon_order S.hT gammaF_order S.hgammaK selected table
  WTwist : LowQuadraticTwistWitness F K ht hres pi hpi hgen data S.chiK S.psiK
    base_decomposition minimal chiK_character psiK_character low S.delta S.epsilon1
      delta_order epsilon_order S.hT gammaF_order S.hgammaK selected table

set_option maxHeartbeats 4000000 in
/-- Transport the selected low table to the computational character data and
choose the upstairs and twist witnesses over that same table. -/
private noncomputable def wildQuadraticPreparationLowTransportData
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal) :
    WildQuadraticLowTransportData F K ht hres pi hpi hgen hdegree
      chiF psiF hminimal S := by
  classical
  let data := wildQuadraticPreparationComputationalData F K ht hres pi hpi
    hgen chiF S.chiK psiF S.psiK S.hchi S.hpsi
  have hbase : data.twistData 1 = chiF :=
    wildQuadraticPreparationComputationalData_twist_one F K ht hres pi hpi
      hgen chiF S.chiK psiF S.psiK S.hchi S.hpsi
  have hadd : data.baseAddChar = psiF := rfl
  have hFdata : IsStationaryConductorDecomposition
      (data.twistData 1).conductor (chiF.conductor / 2)
        (chiF.conductor % 2) := by rw [hbase]; exact S.hF
  have hmindata : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1) := by rw [hbase]; exact hminimal
  have hLowdata : (data.twistData 1).conductor ≤ t + 1 := by
    rw [hbase]; exact S.hLow
  have hchidata : S.chiK.character =
      (data.twistData 1).character.compNorm := by rw [hbase]; exact S.hchi
  have hpsidata : S.psiK.character =
      data.baseAddChar.character.compTrace := by rw [hadd]; exact S.hpsi
  have hdeltaData : ord F (S.delta : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ) := by
    rw [hadd]; exact S.hdelta
  have hepsilonData : ord K (S.epsilon1 : K) =
      (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hbase]; exact S.hepsilon1
  have hgammaFData : ord F (lowGammaF F K S.delta S.epsilon1 : F) =
      ((((data.twistData 1).conductor : ℤ) +
        data.baseAddChar.conductor : ℤ) : WithTop ℤ) := by
    rw [hbase, hadd]; exact S.hgammaF
  obtain ⟨R, table, hRpairs, hRu, hRn⟩ :=
    wildQuadraticPreparationTransportLowTable ht hres pi hpi hgen
      chiF psiF hminimal S (data.twistData 1) hbase data.baseAddChar hadd
        hFdata hmindata hchidata hpsidata hLowdata hdeltaData hepsilonData
          hgammaFData S.hgammaK
  let WUp := Classical.choice (lowQuadraticUpstairsWitness_nonempty F K ht
    hres pi hpi hgen data S.chiK S.psiK hFdata hmindata hchidata hpsidata
      hLowdata S.delta S.epsilon1 hdeltaData hepsilonData S.hT hgammaFData
        S.hgammaK R table)
  let WTwist := Classical.choice (lowQuadraticTwistWitness_nonempty F K ht
    hres pi hpi hgen data S.chiK S.psiK hFdata hmindata hchidata hpsidata
      hLowdata S.delta S.epsilon1 hdeltaData hepsilonData S.hT hgammaFData
        S.hgammaK R table)
  exact
    { data := data
      base_eq := hbase
      baseAdd_eq := hadd
      base_decomposition := hFdata
      minimal := hmindata
      low := hLowdata
      chiK_character := hchidata
      psiK_character := hpsidata
      delta_order := hdeltaData
      epsilon_order := hepsilonData
      gammaF_order := hgammaFData
      selected := R
      table := table
      selected_pairs := hRpairs
      selected_u := hRu
      selected_n := hRn
      WUp := WUp
      WTwist := WTwist }

/-- Actual low phases and their exact assembly, with the selected pairs and
raw coordinates retained independently of the later coefficient inputs. -/
private structure WildQuadraticLowAssemblyData
    (F K : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal)
    (T : WildQuadraticLowTransportData F K ht hres pi hpi hgen hdegree
      chiF psiF hminimal S)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) chiF.conductor)
    (hopp : C.OppositeNoncancellation) where
  extension : LocalLamprechtPhaseData K T.data.extensionQuasiChar
    T.data.extensionAddChar
  tau : LocalLamprechtPhaseData F (T.data.normCharacterData
    (lowNormCharacterGenerator F K ht hres pi hpi hgen)) T.data.baseAddChar
  base : LocalLamprechtPhaseData F (T.data.twistData 1) T.data.baseAddChar
  twist : LocalLamprechtPhaseData F (T.data.twistData
    (lowNormCharacterGenerator F K ht hres pi hpi hgen)) T.data.baseAddChar
  phaseData : FirstMainPhaseData F K chiF.character psiF.character T.data
  assembly : ExactQuadraticPhaseAssembly F K chiF.character psiF.character
    T.data phaseData (t := t) (m := chiF.conductor)
  extension_eq : phaseData.extension = .stationary extension
  norm_eq : phaseData.normCharacter
    (lowNormCharacterGenerator F K ht hres pi hpi hgen) = .stationary tau
  base_eq : phaseData.twist 1 = .stationary base
  twist_eq : phaseData.twist
    (lowNormCharacterGenerator F K ht hres pi hpi hgen) = .stationary twist
  indexing_tau : assembly.indexing.tau =
    lowNormCharacterGenerator F K ht hres pi hpi hgen
  extension_pair : extension.selectedStationaryPair =
    (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).chiK
  tau_pair : tau.selectedStationaryPair =
    (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).tau
  base_pair : base.selectedStationaryPair =
    (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).chiF
  twist_pair : twist.selectedStationaryPair =
    (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).tauChiF
  A_eq : assembly.A =
    (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 S.selected).tau.ratio
  u_eq : assembly.u = (C.u : K)
  n_eq : assembly.n = (C.n : F)
  zZero_eq : assembly.zZero = C.z0Unit hopp
  zOne_eq : assembly.zOne = C.z1Unit hopp

set_option maxHeartbeats 4000000 in
/-- Construct the four low phases and identify the assembly coordinates and
stationary pairs with the transported table and common correction. -/
private noncomputable def wildQuadraticPreparationLowAssemblyData
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal)
    (T : WildQuadraticLowTransportData F K ht hres pi hpi hgen hdegree
      chiF psiF hminimal S)
    (C : WildQuadraticCommonCorrectionData F K (t + 1) chiF.conductor)
    (hopp : C.OppositeNoncancellation)
    (hCu : lowNormalizedRatio F K S.epsilon1 T.selected = (C.u : K))
    (hCn : lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen T.data
      T.base_decomposition S.delta S.epsilon1 T.delta_order S.hT
        T.gammaF_order T.selected = C.n) :
    WildQuadraticLowAssemblyData F K ht hres pi hpi hgen hdegree
      chiF psiF hminimal S T C hopp := by
  classical
  let data := T.data
  have hbase := T.base_eq
  have hFdata := T.base_decomposition
  have hmindata := T.minimal
  have hLowdata := T.low
  have hchidata := T.chiK_character
  have hpsidata := T.psiK_character
  have hdeltaData := T.delta_order
  have hepsilonData := T.epsilon_order
  have hgammaFData := T.gammaF_order
  let R := T.selected
  have table := T.table
  have hRpairs := T.selected_pairs
  let WUp := T.WUp
  let WTwist := T.WTwist
  let residual := phaseReductionResidualCoordinateSource F K hres pi hpi
  let CUp : LamprechtCriticalCoordinate K (chiF.conductor / 2)
      (chiF.conductor % 2) :=
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      S.hF.epsilon_le_one residual.upperUniformizer residual.upper_order
  let CBase := residual.lowerCriticalCoordinate hFdata
  let CNorm : LamprechtCriticalCoordinate F (lowCriticalFloorDepth t)
      (lowCriticalParity t) :=
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      (lowCriticalParity_le_one (t := t)) residual.lowerUniformizer
        residual.lower_order
  let CTwist := CNorm
  let extension := lowQuadraticUpstairsPhaseForComputationalData F K ht hres
    pi hpi hgen data S.chiK S.psiK hFdata hmindata hchidata hpsidata
      hLowdata S.delta S.epsilon1 hdeltaData hepsilonData S.hT hgammaFData
        S.hgammaK R table WUp CUp
  let tauRow := lowQuadraticNormalizedTauPhaseForComputationalData F K ht
    hres pi hpi hgen data hFdata S.delta S.epsilon1 hdeltaData S.hT
      hgammaFData R CNorm
  let base := lowBasePhase F K ht hres pi hpi hgen (data.twistData 1)
    S.chiK data.baseAddChar S.psiK hmindata hchidata hpsidata hFdata
      hLowdata S.delta S.epsilon1 hdeltaData hepsilonData S.hT hgammaFData
        S.hgammaK R table CBase
  let twist := lowQuadraticTwistPhaseForComputationalData F K ht hres pi
    hpi hgen data S.chiK S.psiK hFdata hmindata hchidata hpsidata hLowdata
      S.delta S.epsilon1 hdeltaData hepsilonData S.hT hgammaFData S.hgammaK
        R table WTwist CTwist
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  let index := lowQuadraticNormCharacterIndex F K ht hres pi hpi hgen hdegree
  have index_true := lowQuadraticNormCharacterIndex_true F K ht hres pi hpi
    hgen hdegree
  have index_false := lowQuadraticNormCharacterIndex_false F K ht hres pi
    hpi hgen hdegree
  have htau : tau ≠ 1 := lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  let D := wildQuadraticPreparationPhaseData data tau index index_true
    index_false extension tauRow base twist
  have hExtension : D.extension = .stationary extension := rfl
  have hBase : D.twist 1 = .stationary base := by
    simp [D, wildQuadraticPreparationPhaseData]
  have hNorm : D.normCharacter tau = .stationary tauRow := by
    simp [D, wildQuadraticPreparationPhaseData, htau]
  have hTwist : D.twist tau = .stationary twist := by
    simp [D, wildQuadraticPreparationPhaseData, htau]
  let raw := wildQuadraticPreparationRawCoordinates C hopp
  let rawR : QuadraticRawRatioCoordinates F K
      (lowNormalizedRatio F K S.epsilon1 R)
      (lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data hFdata
        S.delta S.epsilon1 hdeltaData S.hT hgammaFData R) :=
    { zZero := raw.zZero, zOne := raw.zOne, x := raw.x, y := raw.y
      zZero_eq := raw.zZero_eq, zOne_eq := raw.zOne_eq
      one_add_n_ne_zero := by rw [hCn]; exact raw.one_add_n_ne_zero
      zZero_ratio := by rw [hCu, hCn]; exact raw.zZero_ratio
      zOne_ratio := by rw [hCu, hCn]; exact raw.zOne_ratio }
  let B := lowTableBackedExactQuadraticAssemblyFromActualRows F K ht hres pi
    hpi hgen hdegree data D S.chiK S.psiK hFdata hmindata hchidata hpsidata
      hLowdata S.delta S.epsilon1 hdeltaData hepsilonData S.hT hgammaFData
        S.hgammaK R table WUp WTwist CUp CBase CNorm CTwist hExtension hBase
          hNorm hTwist rawR
  have hm := congrArg LocalQuasiCharData.conductor hbase
  let A := wildQuadraticPreparationTransportAssembly hm B.assembly
  rcases wildQuadraticPreparationTransportAssembly_fields hm B.assembly with
    ⟨hAindexing, hAA, hAu, hAn, hAzZero, hAzOne⟩
  have hAtau : A.indexing.tau = tau := by rw [hAindexing]; exact B.indexing_tau
  have extensionPair : extension.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 R).chiK := by
    unfold extension lowQuadraticUpstairsPhaseForComputationalData
    rw [selectedStationaryPair_transport]
    unfold lowQuadraticUpstairsPhaseFromWitness
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    congr 1
    exact WUp.representative_eq
  have tauPair : tauRow.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 R).tau := by
    unfold tauRow lowQuadraticNormalizedTauPhaseForComputationalData
    rw [selectedStationaryPair_transport]
    unfold lowQuadraticNormalizedTauPhaseSource
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    rfl
  have basePair : base.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 R).chiF := by
    unfold base lowBasePhase
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    rfl
  have twistPair : twist.selectedStationaryPair =
      (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 R).tauChiF := by
    unfold twist lowQuadraticTwistPhaseForComputationalData
    rw [selectedStationaryPair_transport]
    unfold lowQuadraticTwistPhaseSource
    rw [selectedStationaryPair_localPhaseOfStationaryClass]
    congr 1
    exact WTwist.representative_eq
  let pairs := lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1
    S.selected
  have extensionPairS : extension.selectedStationaryPair = pairs.chiK := by
    exact extensionPair.trans
      (congrArg WildQuadraticSelectedStationaryPairs.chiK hRpairs)
  have tauPairS : tauRow.selectedStationaryPair = pairs.tau := by
    exact tauPair.trans
      (congrArg WildQuadraticSelectedStationaryPairs.tau hRpairs)
  have basePairS : base.selectedStationaryPair = pairs.chiF := by
    exact basePair.trans
      (congrArg WildQuadraticSelectedStationaryPairs.chiF hRpairs)
  have twistPairS : twist.selectedStationaryPair = pairs.tauChiF := by
    exact twistPair.trans
      (congrArg WildQuadraticSelectedStationaryPairs.tauChiF hRpairs)
  exact
    { extension := extension, tau := tauRow, base := base, twist := twist
      phaseData := D, assembly := A
      extension_eq := hExtension, norm_eq := hNorm
      base_eq := hBase, twist_eq := hTwist, indexing_tau := hAtau
      extension_pair := extensionPairS, tau_pair := tauPairS
      base_pair := basePairS, twist_pair := twistPairS
      A_eq := by
        rw [hAA]
        calc
          B.assembly.A =
              (lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1 R).tau.ratio := by
            rw [(lowWildQuadraticSelectedStationaryPairs_ratios S.delta
              S.epsilon1 R).2.1]
            simp only [B, lowTableBackedExactQuadraticAssemblyFromActualRows,
              lowTableBackedExactQuadraticAssembly, Units.val_div_eq_div_val]
          _ = pairs.tau.ratio :=
            congrArg (fun q : WildQuadraticSelectedStationaryPairs F K ↦
              q.tau.ratio) hRpairs
      u_eq := by rw [hAu, B.ratio_u_source, hCu]
      n_eq := by
        rw [hAn, B.ratio_n_source]
        change (lowEpsilon F K S.epsilon1 : F) * (R.beta : F) /
          (R.alpha : F) = (C.n : F)
        have hn := congrArg Units.val hCn
        simpa only [lowQuadraticNormalizedNormUnit_coe] using hn
      zZero_eq := by rw [hAzZero]; rfl
      zOne_eq := by rw [hAzOne]; rfl }

set_option maxHeartbeats 4000000 in
/-- Construct the four actual low rows and their exact common assembly,
retaining the table witnesses needed by coordinate transport. -/
private noncomputable def wildQuadraticPreparationLowCommon
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal) :
    WildQuadraticLowCommonPackage F K t chiF psiF := by
  classical
  let T := wildQuadraticPreparationLowTransportData ht hres pi hpi hgen
    hdegree chiF psiF hminimal S
  let data := T.data
  have hbase := T.base_eq
  have hadd := T.baseAdd_eq
  have hFdata := T.base_decomposition
  have hmindata := T.minimal
  have hLowdata := T.low
  have hchidata := T.chiK_character
  have hpsidata := T.psiK_character
  have hdeltaData := T.delta_order
  have hepsilonData := T.epsilon_order
  have hgammaFData := T.gammaF_order
  let R := T.selected
  have table := T.table
  have hRpairs := T.selected_pairs
  let WUp := T.WUp
  have hRu := T.selected_u
  have hRn := T.selected_n
  let C := lowWildQuadraticCommonCorrection ht hres pi hpi hgen hdegree
    chiF psiF hminimal S.hF S.hLow S.delta S.epsilon1 S.hdelta S.hepsilon1
      S.hT S.hgammaF S.selected
  have hopp : C.OppositeNoncancellation :=
    lowWildQuadraticCommonCorrection_oppositeNoncancellation ht hres pi hpi
      hgen hdegree chiF psiF hminimal S.hF S.hLow S.delta S.epsilon1
        S.hdelta S.hepsilon1 S.hT S.hgammaF S.selected
  have hCu : lowNormalizedRatio F K S.epsilon1 R = (C.u : K) := by
    rw [hRu]
    change lowNormalizedRatio F K S.epsilon1 S.selected =
      (lowWildQuadraticCommonU S.epsilon1 S.selected : K)
    exact (lowWildQuadraticCommonU_coe S.epsilon1 S.selected).symm
  have hCn : lowQuadraticNormalizedNormUnit F K ht hres pi hpi hgen data
      hFdata S.delta S.epsilon1 hdeltaData S.hT hgammaFData R = C.n := by
    unfold lowQuadraticNormalizedNormUnit
    rw [hRn]
    rfl
  let L := wildQuadraticPreparationLowAssemblyData ht hres pi hpi hgen
    hdegree chiF psiF hminimal S T C hopp hCu hCn
  let D := L.phaseData
  let A := L.assembly
  let extension := L.extension
  let tauRow := L.tau
  let base := L.base
  let twist := L.twist
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : tau ≠ 1 := lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen
  have hAtau : A.indexing.tau = tau := L.indexing_tau
  have hExtension := L.extension_eq
  have hNorm := L.norm_eq
  have hBase := L.base_eq
  have hTwist := L.twist_eq
  let pairs := lowWildQuadraticSelectedStationaryPairs S.delta S.epsilon1
    S.selected
  have extensionPairS := L.extension_pair
  have tauPairS := L.tau_pair
  have basePairS := L.base_pair
  have twistPairS := L.twist_pair
  have htauConductor : (data.normCharacterData tau).conductor = t + 1 := by
    rw [← hAtau]
    exact wildQuadraticPreparation_tau_conductor_eq (A := A) ht hres pi hpi hgen
  have hinput := wildQuadraticPreparation_lowInputs_exists ht hres pi hpi
    hgen hdegree chiF psiF hminimal S data hbase hadd tau htau htauConductor
      tauRow base twist tauPairS basePairS twistPairS
  let inputs := Classical.choose hinput
  rcases Classical.choose_spec hinput with
    ⟨hinputRow, hinputPairs, hinputLocal, hinputBoundary, htauPhase, hbasePhase⟩
  let P := wildQuadraticPreparationLowCoefficientCore ht hres pi hpi hgen
    hdegree chiF psiF hminimal S inputs hinputRow hinputPairs hinputLocal
      hinputBoundary
  let V := P.toView
  let rows : WildQuadraticActualPhaseRows V data D A :=
    wildQuadraticPreparationActualRowsOfTauEq tau hAtau extension tauRow base
      twist hExtension hNorm hBase hTwist
        (by simpa [V, P, wildQuadraticPreparationLowCoefficientCore,
          WildQuadraticLowCoefficientCore.toView,
          WildQuadraticLowCoefficientCore.stationaryPairs, pairs] using
            extensionPairS)
        (by simpa [V, P, wildQuadraticPreparationLowCoefficientCore,
          WildQuadraticLowCoefficientCore.toView,
          WildQuadraticLowCoefficientCore.stationaryPairs, pairs] using tauPairS)
        (by simpa [V, P, wildQuadraticPreparationLowCoefficientCore,
          WildQuadraticLowCoefficientCore.toView,
          WildQuadraticLowCoefficientCore.stationaryPairs, pairs] using basePairS)
        (by simpa [V, P, wildQuadraticPreparationLowCoefficientCore,
          WildQuadraticLowCoefficientCore.toView,
          WildQuadraticLowCoefficientCore.stationaryPairs, pairs] using
            twistPairS)
  have coordinates : WildQuadraticCommonCoordinateCompatibility V data D A := by
    refine
      { baseData_eq := hbase
        baseAddData_eq := hadd
        tauData_eq := ?_
        A_eq := L.A_eq
        u_eq := L.u_eq
        n_eq := L.n_eq
        zZero_eq := L.zZero_eq
        zOne_eq := L.zOne_eq }
    rw [hAtau]
    apply LocalQuasiCharData.ext_character F
    rw [data.normCharacterData_character]
    rfl
  let common : WildQuadraticCommonHigherData F K t chiF psiF V :=
    { chiFData_eq := rfl
      psiF_eq := rfl
      data := data
      phaseData := D
      assembly := A
      coordinates := coordinates }
  have hphases := wildQuadraticPreparation_lowPhaseFactors rows tau hAtau
    tauRow base hNorm hBase htauPhase hbasePhase
  let lowSource : WildQuadraticLowCoordinateTransportSource F K V rows :=
    { conductor_eq := rfl
      stationaryDepth := chiF.conductor / 2
      conductorRemainder := chiF.conductor % 2
      ht := ht
      hres := hres
      pi := pi
      hpi := hpi
      hgen := hgen
      hdegree := hdegree
      chiK := S.chiK
      psiK := S.psiK
      baseData_eq := hbase
      baseAddData_eq := hadd
      hminimal := hmindata
      hchi := hchidata
      hpsi := hpsidata
      hF := hFdata
      hLow := hLowdata
      delta := S.delta
      epsilon1 := S.epsilon1
      hdelta := hdeltaData
      hepsilon1 := hepsilonData
      hT := S.hT
      hgammaF := hgammaFData
      hgammaK := S.hgammaK
      selected := R
      table := table
      WUp := WUp
      stationaryPairs_eq := by
        simpa only [V, P, wildQuadraticPreparationLowCoefficientCore,
          WildQuadraticLowCoefficientCore.toView,
          WildQuadraticLowCoefficientCore.stationaryPairs] using hRpairs
      correction_u := hCu
      correction_n := hCn
      coordinates := coordinates
      tau_phase := hphases.1
      base_phase := hphases.2 }
  exact
    { view := V
      common := common
      rows := rows
      lowSource := lowSource }

/-- Finish the low package by transporting its retained upper coordinates
and lower product for each supplied positive-polar source. -/
private theorem wildQuadraticPreparationLowContinuation
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t m : ℕ} {V : WildQuadraticCommonCoefficientView F K t m}
    {data : FirstMainComputationalData F K V.chiFData.character V.psiF.character}
    {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
    {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
      V.psiF.character data D (t := t) (m := m)}
    {rows : WildQuadraticActualPhaseRows V data D A}
    (S : WildQuadraticLowCoordinateTransportSource F K V rows)
    (source : V.criticalInputs.PositivePolarSource) :
    WildQuadraticPositivePolarContinuation F K V source rows := by
  let upper := wildQuadraticLowCoordinateTransport F K V rows S
  have hlow : m ≤ t + 1 := by
    rw [S.conductor_eq, ← S.baseData_eq]
    exact S.hLow
  have htauConductor : V.tauData.conductor = t + 1 := by
    rw [← S.coordinates.tauData_eq]
    exact wildQuadraticPreparation_tau_conductor_eq (A := A)
      S.ht S.hres S.pi S.hpi S.hgen
  have hminimal : IsMinimalNormCharacterOrbitRepresentative F K
      V.chiFData := by
    rw [← S.baseData_eq]
    exact S.hminimal
  let productSource :
      WildQuadraticLowProductCoordinateTransportSource F K V rows :=
    { upper := upper
      coordinates := S.coordinates
      low := hlow
      tau_conductor := htauConductor
      twist_conductor := wildQuadraticPreparation_twist_conductor_eq
        S.ht S.hres S.pi S.hpi S.hgen S.coordinates hminimal
      tau_phase := S.tau_phase
      base_phase := S.base_phase }
  exact wildQuadraticLowContinuation upper
    (wildQuadraticLowProductCoordinateTransport productSource source)

/-- Assemble the common low construction and its source-indexed continuation. -/
private noncomputable def wildQuadraticPreparationLowPackage
    {F K : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K] [Module.Free F K]
    [Module.Finite F K] [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (S : WildQuadraticLowSetup F K ht hres pi hpi hgen chiF psiF hminimal) :
    WildQuadraticQFreePhasePackage F K t chiF psiF := by
  let P := wildQuadraticPreparationLowCommon ht hres pi hpi hgen hdegree
    chiF psiF hminimal S
  exact
    { view := P.view
      common := P.common
      rows := P.rows
      continuation := wildQuadraticPreparationLowContinuation P.lowSource }


/-- Apply the exhaustive, disjoint input dichotomy only after all common
phase data have been constructed.  The positive branch retains the actual
source supplied by that input; the all-even branch retains the same four
actual rows. -/
private noncomputable def wildQuadraticPreparationClassify
    {F K : Type}
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
    {t : ℕ} {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (P : WildQuadraticQFreePhasePackage F K t chiF psiF)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF) :
    WildQuadraticPhasePrepared F K t chiF psiF := by
  have hminimalView :
      IsMinimalNormCharacterOrbitRepresentative F K P.view.chiFData := by
    simpa only [P.common.chiFData_eq] using hminimal
  by_cases heven : P.view.criticalInputs.row.IsAllEven
  · let evenView :
        WildQuadraticAllEvenCoefficientView F K t chiF.conductor :=
      { toWildQuadraticCommonCoefficientView := P.view
        isAllEven := heven }
    let evenRows := wildQuadraticPreparation_allEvenRows ht hres pi hpi hgen
      hdegree evenView P.common.data P.common.phaseData P.common.assembly
        P.rows P.common.coordinates hminimalView
    let completeCorrection :=
      wildQuadraticPreparation_allEvenCompleteCorrection ht hres pi hpi
        hgen evenView P.common.data P.common.phaseData P.common.assembly
          evenRows P.common.coordinates hminimalView
    exact .allEven evenView P.common evenRows completeCorrection
  · have hpositive :
        Nonempty P.view.criticalInputs.PositivePolarSource := by
      rcases P.view.criticalInputs.isAllEven_or_positivePolarSource with
        heven' | hpositive
      · exact (heven heven').elim
      · exact hpositive
    let source := Classical.choice hpositive
    exact .needsRefinement P.view source P.common P.rows
      (P.continuation source)

/-- **Wild quadratic phase preparation.**  Construct the common q-free
phase package at the actual conductor, then return either the completed
all-even higher datum or the retained positive-polar source that still needs
refinement. -/
noncomputable def wildQuadraticPhasePreparation
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ}
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    WildQuadraticPhasePrepared F K t chiF psiF := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  let S := wildQuadraticPreparationSetup ht htpos hres pi hpi hgen hdegree
    chiF psiF hminimal hm
  cases S with
  | low L =>
      let P := wildQuadraticPreparationLowPackage ht hres pi hpi hgen
        hdegree chiF psiF hminimal L
      exact wildQuadraticPreparationClassify ht hres pi hpi hgen hdegree P
        hminimal
  | high H =>
      let P := wildQuadraticPreparationHighPackage ht htpos hres pi hpi hgen
        hdegree chiF psiF hminimal H
      exact wildQuadraticPreparationClassify ht hres pi hpi hgen hdegree P
        hminimal

end

end LanglandsFirstMainLemma
