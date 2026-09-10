import LanglandsFirstMainLemma.Basic.CharacterConductorExistence
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.High
import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Cases.WildOdd.ResidualCoefficients
import LanglandsFirstMainLemma.Cases.WildOdd.UpperResidualCoefficients
import LanglandsFirstMainLemma.Cases.WildOdd.ParityReduction
import LanglandsFirstMainLemma.Cases.WildOdd.Main
import LanglandsFirstMainLemma.Cases.WildOdd.AffineTranslationBridge
import LanglandsFirstMainLemma.Cases.WildOdd.LowSourceNormalization

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

local instance wildOddPhasePreparation_residuePrimeFact
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩

local instance wildOddPhasePreparation_degreePrime
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance wildOddPhasePreparation_degreeNeZero
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] : NeZero (Module.finrank F K) :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

local instance wildOddPhasePreparation_residueFieldFintype
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Fintype (ResidueField E) :=
  residueFieldFintype E

private theorem wildOddPreparation_conductorDecomposition
    {m : ℕ} (hm : 1 < m) :
    IsStationaryConductorDecomposition m (m / 2) (m % 2) where
  conductor_gt_one := hm
  epsilon_le_one := by omega
  conductor_eq := by omega

/-- A source denominator of any prescribed finite valuation.  This is used
only where the High/Low parameter constructors require a literal unit. -/
private noncomputable def wildOddPreparationUnitOfOrd
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (a : ℤ) : Eˣ :=
  Units.mk0 (Classical.choose (exists_ord_eq E a))
    ((ord_ne_top_iff E).1 (by
      rw [Classical.choose_spec (exists_ord_eq E a)]
      exact WithTop.coe_ne_top))

private theorem wildOddPreparationUnitOfOrd_order
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (a : ℤ) :
    ord E (wildOddPreparationUnitOfOrd E a : E) = (a : WithTop ℤ) :=
  Classical.choose_spec (exists_ord_eq E a)

/-- The actual norm pullback, trace pullback, norm-character data and orbit
twists used in every prepared row.  The identity twist is kept literally as
`chiF`; every nonidentity twist uses its conductor-aware orbit datum. -/
private noncomputable def wildOddPreparationComputationalData
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
private theorem wildOddPreparationComputationalData_twist_one
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
    (wildOddPreparationComputationalData F K ht hres pi hpi hgen chiF
      chiK psiF psiK hchi hpsi).twistData 1 = chiF := by
  classical
  simp [wildOddPreparationComputationalData]

@[simp]
private theorem wildOddPreparationComputationalData_baseAddChar
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
    (wildOddPreparationComputationalData F K ht hres pi hpi hgen chiF
      chiK psiF psiK hchi hpsi).baseAddChar = psiF :=
  rfl

private theorem wildOddPreparation_piCongrLeft_at_image
    {A B : Type*} (P : B → Type*) (e : A ≃ B)
    (f : (a : A) → P (e a)) (a : A) :
    ((Equiv.piCongrLeft P e) f) (e a) = f a := by
  rw [Equiv.piCongrLeft_apply, eqRec_eq_cast]
  apply cast_eq_iff_heq.mpr
  apply dcongr_heq (heq_of_eq (e.symm_apply_apply a))
  · intro t₁ t₂ ht
    cases eq_of_heq ht
    rfl
  · intro _ _
    rfl

private theorem wildOddPreparation_dependent_apply_heq
    {A : Type*} {P : A → Type*} (f : (a : A) → P a)
    {a b : A} (h : a = b) : f a ≍ f b := by
  apply dcongr_heq (heq_of_eq h)
  · intro t₁ t₂ ht
    cases eq_of_heq ht
    rfl
  · intro _ _
    rfl

/-- Insert the actual extension row, identity twist, and all nonidentity norm
and twist rows into the full norm-character family.  The identity norm
character remains the genuine endpoint package. -/
private noncomputable def wildOddPreparationPhaseData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (extension : LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar)
    (normRow : ∀ j : OddNormIndex F K,
      LocalLamprechtPhaseData F
        (data.normCharacterData
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))) data.baseAddChar)
    (base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar)
    (twistRow : ∀ j : OddNormIndex F K,
      LocalLamprechtPhaseData F
        (data.twistData
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))) data.baseAddChar) :
    FirstMainPhaseData F K globalChi globalPsi data := by
  classical
  let indexing := oddNormCharacterIndexing F K ht hres pi hpi hgen
  let normIndexed : ∀ o : Option (OddNormIndex F K),
      LocalPhaseData F (data.normCharacterData (indexing o))
        data.baseAddChar := fun o => by
    cases o with
    | none =>
        rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
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
    | some j =>
        exact Eq.ndrec
          (motive := fun mu =>
            LocalPhaseData F (data.normCharacterData mu) data.baseAddChar)
          (.stationary (normRow j))
          (oddNormCharacterIndexing_some F K ht hres pi hpi hgen j).symm
  let twistIndexed : ∀ o : Option (OddNormIndex F K),
      LocalPhaseData F (data.twistData (indexing o))
        data.baseAddChar := fun o => by
    cases o with
    | none =>
        rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
        exact .stationary base
    | some j =>
        exact Eq.ndrec
          (motive := fun mu =>
            LocalPhaseData F (data.twistData mu) data.baseAddChar)
          (.stationary (twistRow j))
          (oddNormCharacterIndexing_some F K ht hres pi hpi hgen j).symm
  exact
    { extension := .stationary extension
      normCharacter := (Equiv.piCongrLeft
        (fun mu => LocalPhaseData F (data.normCharacterData mu)
          data.baseAddChar) indexing) normIndexed
      twist := (Equiv.piCongrLeft
        (fun mu => LocalPhaseData F (data.twistData mu)
          data.baseAddChar) indexing) twistIndexed }

section PhaseDataRows

variable (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (extension : LocalLamprechtPhaseData K data.extensionQuasiChar
      data.extensionAddChar)
    (normRow : ∀ j : OddNormIndex F K,
      LocalLamprechtPhaseData F
        (data.normCharacterData
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))) data.baseAddChar)
    (base : LocalLamprechtPhaseData F (data.twistData 1) data.baseAddChar)
    (twistRow : ∀ j : OddNormIndex F K,
      LocalLamprechtPhaseData F
        (data.twistData
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))) data.baseAddChar)

@[simp]
private theorem wildOddPreparationPhaseData_extension :
    (wildOddPreparationPhaseData F K ht hres pi hpi hgen data extension
      normRow base twistRow).extension = .stationary extension :=
  rfl

@[simp]
private theorem wildOddPreparationPhaseData_base :
    (wildOddPreparationPhaseData F K ht hres pi hpi hgen data extension
      normRow base twistRow).twist 1 = .stationary base := by
  classical
  let e := oddNormCharacterIndexing F K ht hres pi hpi hgen
  let f : ∀ o : Option (OddNormIndex F K),
      LocalPhaseData F (data.twistData (e o)) data.baseAddChar := fun o => by
    cases o with
    | none =>
        rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
        exact .stationary base
    | some i =>
        exact Eq.ndrec
          (motive := fun mu =>
            LocalPhaseData F (data.twistData mu) data.baseAddChar)
          (.stationary (twistRow i))
          (oddNormCharacterIndexing_some F K ht hres pi hpi hgen i).symm
  let P := fun mu => LocalPhaseData F (data.twistData mu) data.baseAddChar
  let forward := (Equiv.piCongrLeft P e) f
  have hindex : e none = 1 :=
    oddNormCharacterIndexing_none F K ht hres pi hpi hgen
  have heval : forward (e none) = f none :=
    wildOddPreparation_piCongrLeft_at_image P e f none
  have hforward : forward (e none) ≍ forward 1 :=
    wildOddPreparation_dependent_apply_heq forward hindex
  have hf : f none ≍ LocalPhaseData.stationary base := by
    dsimp only [f]
    apply cast_heq
  change forward 1 = LocalPhaseData.stationary base
  apply eq_of_heq
  exact hforward.symm.trans ((heq_of_eq heval).trans hf)

@[simp]
private theorem wildOddPreparationPhaseData_norm (j : OddNormIndex F K) :
    (wildOddPreparationPhaseData F K ht hres pi hpi hgen data extension
      normRow base twistRow).normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) = .stationary (normRow j) := by
  classical
  let e := oddNormCharacterIndexing F K ht hres pi hpi hgen
  let f : ∀ o : Option (OddNormIndex F K),
      LocalPhaseData F (data.normCharacterData (e o)) data.baseAddChar :=
    fun o => by
      cases o with
      | none =>
          rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
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
      | some i =>
          exact Eq.ndrec
            (motive := fun mu =>
              LocalPhaseData F (data.normCharacterData mu) data.baseAddChar)
            (.stationary (normRow i))
            (oddNormCharacterIndexing_some F K ht hres pi hpi hgen i).symm
  let P := fun mu =>
    LocalPhaseData F (data.normCharacterData mu) data.baseAddChar
  let forward := (Equiv.piCongrLeft P e) f
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hindex : e (some j) = mu :=
    oddNormCharacterIndexing_some F K ht hres pi hpi hgen j
  have heval : forward (e (some j)) = f (some j) :=
    wildOddPreparation_piCongrLeft_at_image P e f (some j)
  have hforward : forward (e (some j)) ≍ forward mu :=
    wildOddPreparation_dependent_apply_heq forward hindex
  have hf : f (some j) ≍ LocalPhaseData.stationary (normRow j) := by
    dsimp only [f]
    rfl
  change forward mu = LocalPhaseData.stationary (normRow j)
  apply eq_of_heq
  exact hforward.symm.trans ((heq_of_eq heval).trans hf)

@[simp]
private theorem wildOddPreparationPhaseData_twist (j : OddNormIndex F K) :
    (wildOddPreparationPhaseData F K ht hres pi hpi hgen data extension
      normRow base twistRow).twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) = .stationary (twistRow j) := by
  classical
  let e := oddNormCharacterIndexing F K ht hres pi hpi hgen
  let f : ∀ o : Option (OddNormIndex F K),
      LocalPhaseData F (data.twistData (e o)) data.baseAddChar := fun o => by
    cases o with
    | none =>
        rw [oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
        exact .stationary base
    | some i =>
        exact Eq.ndrec
          (motive := fun mu =>
            LocalPhaseData F (data.twistData mu) data.baseAddChar)
          (.stationary (twistRow i))
          (oddNormCharacterIndexing_some F K ht hres pi hpi hgen i).symm
  let P := fun mu => LocalPhaseData F (data.twistData mu) data.baseAddChar
  let forward := (Equiv.piCongrLeft P e) f
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hindex : e (some j) = mu :=
    oddNormCharacterIndexing_some F K ht hres pi hpi hgen j
  have heval : forward (e (some j)) = f (some j) :=
    wildOddPreparation_piCongrLeft_at_image P e f (some j)
  have hforward : forward (e (some j)) ≍ forward mu :=
    wildOddPreparation_dependent_apply_heq forward hindex
  have hf : f (some j) ≍ LocalPhaseData.stationary (twistRow j) := by
    dsimp only [f]
    rfl
  change forward mu = LocalPhaseData.stationary (twistRow j)
  apply eq_of_heq
  exact hforward.symm.trans ((heq_of_eq heval).trans hf)

end PhaseDataRows

/-- The canonical trace additive character on the residue field, together
with its Frobenius invariance. -/
private noncomputable def wildOddPreparationResidualAddChar
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    FrobeniusResidualAddCharData F (residueCharacteristic F) := by
  let p := residueCharacteristic F
  letI : Algebra (ZMod p) (ResidueField F) := ZMod.algebra _ p
  let psiPrime : FiniteAddChar (ZMod p) :=
    AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
  let psi0 : FiniteAddChar (ResidueField F) :=
    traceAddChar (ZMod p) (ResidueField F) psiPrime
  have hpsiPrime : psiPrime ≠ 1 := by
    have hprimitive :=
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
    have hshift := hprimitive (a := (1 : ZMod p)) one_ne_zero
    simpa only [AddChar.mulShift_one] using hshift
  have hpsi0 : psi0 ≠ 1 :=
    (traceAddChar_ne_one_iff (ZMod p) (ResidueField F) psiPrime).2
      hpsiPrime
  refine
    { lower := psi0
      lower_ne_one := hpsi0
      frobenius := ?_ }
  intro x
  have htrace :
      residueTrace (ZMod p) (ResidueField F) (x ^ p) =
        residueTrace (ZMod p) (ResidueField F) x := by
    simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      ZMod.card] using
      (Algebra.trace_eq_of_algEquiv
        (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod p) (ResidueField F)) x)
  exact congrArg psiPrime htrace

/-- The same residual character indexed by the actual prime extension
degree. -/
private noncomputable def wildOddPreparationResidualAddCharAtDegree
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    FrobeniusResidualAddCharData F (Module.finrank F K) := by
  rw [← residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
    hpi hgen]
  exact wildOddPreparationResidualAddChar F

private def wildOddPreparationDummyNamedPair
    (k : Type*) [Field k] : WildOddNamedCoefficientPair k where
  eta := 1
  eta_ne_zero := one_ne_zero
  gamma := 0

private noncomputable def wildOddPreparationPrimeFieldUnitMap
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    [CharP (ResidueField F) p] :
    (ZMod p)ˣ →* (ResidueField F)ˣ :=
  Units.map (ZMod.castHom (dvd_refl p) (ResidueField F)).toMonoidHom

private theorem wildOddPreparationPrimeFieldUnitMap_injective
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ)
    [CharP (ResidueField F) p] :
    Function.Injective (wildOddPreparationPrimeFieldUnitMap F p) := by
  intro u v huv
  apply Units.ext
  apply ZMod.castHom_injective (ResidueField F)
  exact congrArg Units.val huv

/-- Reindex the full critical quotient by the canonical nonidentity norm
characters without constructing an exact assembly. -/
private theorem wildOddPreparation_rawCritical_eq_indexedQuotient
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    {data : FirstMainComputationalData F K globalChi globalPsi}
    (D : FirstMainPhaseData F K globalChi globalPsi data) :
    D.criticalNumerator / D.criticalDenominator =
      (D.extension.criticalFactor *
          ∏ j : OddNormIndex F K,
            (D.normCharacter
              (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
                (Multiplicative.ofAdd
                  (j : ZMod (Module.finrank F K))))).criticalFactor) /
        ((D.twist 1).criticalFactor *
          ∏ j : OddNormIndex F K,
            (D.twist
              (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
                (Multiplicative.ofAdd
                  (j : ZMod (Module.finrank F K))))).criticalFactor) := by
  letI := Fintype.ofFinite (NormCharacter F K)
  let indexing := oddNormCharacterIndexing F K ht hres pi hpi hgen
  have hnorm :
      (∏ mu : NormCharacter F K, (D.normCharacter mu).criticalFactor) =
        (D.normCharacter 1).criticalFactor *
          ∏ j : OddNormIndex F K,
            (D.normCharacter
              (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
                (Multiplicative.ofAdd
                  (j : ZMod (Module.finrank F K))))).criticalFactor := by
    rw [← Equiv.prod_comp indexing
      (fun mu : NormCharacter F K ↦ (D.normCharacter mu).criticalFactor)]
    rw [Fintype.prod_option,
      oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
    congr 1
  have hid : (D.normCharacter 1).criticalFactor = 1 := by
    rcases identityNormCharacterEndpoint_of_phaseData D with
      ⟨h, Gamma, hEq⟩
    rw [hEq]
    rfl
  have htwist :
      (∏ mu : NormCharacter F K, (D.twist mu).criticalFactor) =
        (D.twist 1).criticalFactor *
          ∏ j : OddNormIndex F K,
            (D.twist
              (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
                (Multiplicative.ofAdd
                  (j : ZMod (Module.finrank F K))))).criticalFactor := by
    rw [← Equiv.prod_comp indexing
      (fun mu : NormCharacter F K ↦ (D.twist mu).criticalFactor)]
    rw [Fintype.prod_option,
      oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
    congr 1
  simp only [FirstMainPhaseData.criticalNumerator,
    FirstMainPhaseData.criticalDenominator]
  rw [hnorm, hid, one_mul, htwist]

/-- A complete critical function which is pointwise one contributes no
residual phase. -/
private theorem wildOddPreparation_criticalFactor_eq_one
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (hfun : ∀ x : ResidueField E, D.criticalFunction x = 1) :
    D.criticalFactor = 1 := by
  rw [D.criticalFactor_eq_criticalFunctionPhase]
  unfold LocalLamprechtPhaseData.criticalFunctionPhase
  simp_rw [hfun]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : 0 < (Fintype.card (ResidueField E) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
  exact phase_ofReal_pos hcard

/-- The low parity package uses the actual generator and base rows exactly
in the odd branches.  Its boundary certificate is requested only after both
the boundary equality and odd-boundary parity have been supplied. -/
private noncomputable def wildOddPreparationLowParity
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1))
    (hchi : chiK.character = (data.twistData 1).character.compNorm)
    (hpsi : psiK.character = data.baseAddChar.character.compTrace)
    (hLow : (data.twistData 1).conductor ≤ t + 1)
    (delta : Fˣ) (epsilon1 : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
    (hepsilon1 : ord K (epsilon1 : K) =
      (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ))
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
      ((((data.twistData 1).conductor : ℤ) +
        data.baseAddChar.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (P : LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d
      (stationaryCoefficientClass F
        (quasiCharDataOfIsConductor F
          (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
            (lowNormCharacterGenerator F K ht hres pi hpi hgen)
            (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
        data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
          delta hdelta)
      (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
        (lowGammaF F K delta epsilon1) hgammaF))
    (table : LowConductorParameterTableData F K ht hres pi hpi hgen
      (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF
        hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table j)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    WildOddParityReductionData F (Module.finrank F K) := by
  let generator : WildOddNamedCoefficientPair (ResidueField F) :=
    if hp : lowCriticalParity t = 1 then
      wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF delta
        epsilon1 hdelta hT hgammaF P hp C.lower C.lower_ne_one hcharOdd
    else wildOddPreparationDummyNamedPair (ResidueField F)
  let base : WildOddNamedCoefficientPair (ResidueField F) :=
    if hb : Odd (data.twistData 1).conductor then
      wildOddLowBaseNamedPair F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table C.lower C.lower_ne_one hcharOdd hb
    else wildOddPreparationDummyNamedPair (ResidueField F)
  exact
    { b := (data.twistData 1).conductor - 1
      v := t
      omega := wildOddPreparationPrimeFieldUnitMap F (Module.finrank F K)
      omega_injective :=
        wildOddPreparationPrimeFieldUnitMap_injective F
          (Module.finrank F K)
      generator := generator
      base := base
      boundaryShift_ne_zero := by
        intro hbv hvodd j
        have hboundary : (data.twistData 1).conductor = t + 1 := by
          have hm := hF.conductor_gt_one
          omega
        have hp : lowCriticalParity t = 1 := by
          obtain ⟨q, hq⟩ := hvodd
          unfold lowCriticalParity
          omega
        have hb : Odd (data.twistData 1).conductor := by
          rw [hboundary]
          exact hvodd
        dsimp only [generator, base]
        rw [dif_pos hp, dif_pos hb]
        simpa only [wildOddLowBoundaryBaseNamedPair] using
          (wildOdd_lowBoundaryNumerator_ne_zero F K ht hres pi hpi hgen
            data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
              hepsilon1 hT hgammaF hgammaK P table WTwist hboundary j hp
                C.lower C.lower_ne_one hcharOdd) }

section HighRawSource

private theorem wildOddPreparation_criticalFactor_eq_lowerPairPhase
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {chi : LocalQuasiCharData E}
    {psi : LocalAddCharData E} (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hcharOdd : ringChar (ResidueField E) ≠ 2)
    (P : WildOddCoefficientPair (ResidueField E))
    (hP : wildOddCoefficientPair D psi0 hpsi0 hcharOdd = P) :
    D.criticalFactor = wildOddLowerPairPhase psi0 P := by
  rw [D.criticalFactor_eq_quadraticPhase psi0 hpsi0 hcharOdd]
  unfold wildOddLowerPairPhase
  change quadraticPhase psi0 (wildOddCoefficientPair D psi0 hpsi0
    hcharOdd).polar (wildOddCoefficientPair D psi0 hpsi0 hcharOdd).affine = _
  rw [hP]

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition (data.twistData 1).conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hodd : Odd (Module.finrank F K)) (htpos : 0 < s + 1)
  (hstrict : s + 1 + 1 < (data.twistData 1).conductor)
  (hupper : (data.twistData 1).conductor < 2 * (s + 1 + 1))
  (gammaF : Fˣ) (hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF)

private noncomputable def wildOddPreparation_highNormGeneratorNamedPair
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    WildOddNamedCoefficientPair (ResidueField F) :=
  wildOddNamedPairOfPhase
    (highNormGeneratorPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        hparity)
    C.lower C.lower_ne_one hcharOdd
    ⟨lowCriticalFloorDepth (s + 1), by
      simpa only [hparity] using
        (lowCriticalConductorDecomposition (t := s + 1) (by omega)
          ).conductor_eq⟩

/-- The strict-High parity package retains each actual odd row.  When the
norm row is even but the base row is odd, its otherwise-unused generator is
the source normalization pair with polar `etaZero`, so `eta/etaZero` remains
the actual `dZero`. -/
private noncomputable def wildOddPreparationHighParity
    [CharP (ResidueField F) (Module.finrank F K)]
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    WildOddParityReductionData F (Module.finrank F K) := by
  by_cases he : epsilon = 1
  · let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF (Module.finrank F K) C source he hcharOdd
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source he C
    have hbase : base.eta = N.eta := by
      change (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          0).polarCoefficient C.lower C.lower_ne_one = N.eta
      exact highActual_basePolar_eq_eta F K ht hres pi hpi hgen data chiK
        psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
          hgammaF source he C
    have hetaZero : N.etaZero ≠ 0 := by
      intro hz
      apply base.eta_ne_zero
      rw [hbase, N.eta_eq, hz, zero_mul]
    let normalizedGenerator : WildOddNamedCoefficientPair (ResidueField F) :=
      ⟨N.etaZero, hetaZero, 0⟩
    let generator := if hp : lowCriticalParity (s + 1) = 1 then
      wildOddPreparation_highNormGeneratorNamedPair F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF source hp C hcharOdd else normalizedGenerator
    exact
      { b := (data.twistData 1).conductor - 1
        v := s + 1
        omega := wildOddPreparationPrimeFieldUnitMap F (Module.finrank F K)
        omega_injective :=
          wildOddPreparationPrimeFieldUnitMap_injective F (Module.finrank F K)
        generator := generator
        base := base
        boundaryShift_ne_zero := by intro hb; omega }
  · let generator := if hp : lowCriticalParity (s + 1) = 1 then
      wildOddPreparation_highNormGeneratorNamedPair F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF source hp C hcharOdd
      else wildOddPreparationDummyNamedPair (ResidueField F)
    exact
      { b := (data.twistData 1).conductor - 1
        v := s + 1
        omega := wildOddPreparationPrimeFieldUnitMap F (Module.finrank F K)
        omega_injective :=
          wildOddPreparationPrimeFieldUnitMap_injective F (Module.finrank F K)
        generator := generator
        base := wildOddPreparationDummyNamedPair (ResidueField F)
        boundaryShift_ne_zero := by intro hb; omega }

private theorem wildOddPreparation_highOddNormSourceProduct_eq_scalarPencil
    [CharP (ResidueField F) (Module.finrank F K)]
    (hparity : lowCriticalParity (s + 1) = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    (∏ j : OddNormIndex F K,
      (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j).criticalFactor) =
      ∏ u : (ZMod (Module.finrank F K))ˣ,
        wildOddLowerPairPhase C.lower
          (wildOddTauPowerPair
            (wildOddPreparation_highNormGeneratorNamedPair F K ht hres pi
              hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
                hstrict hupper gammaF hgammaF source hparity C hcharOdd)
            ((Units.map (ZMod.castHom (dvd_refl (Module.finrank F K))
              (ResidueField F)).toMonoidHom u :
                (ResidueField F)ˣ) : ResidueField F)) := by
  let p := Module.finrank F K
  let generator := wildOddPreparation_highNormGeneratorNamedPair F K ht hres
    pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
      hupper gammaF hgammaF source hparity C hcharOdd
  have hgenOdd : Odd (s + 1 + 1) := by
    refine ⟨lowCriticalFloorDepth (s + 1), ?_⟩
    simpa only [hparity] using
      (lowCriticalConductorDecomposition (t := s + 1) (by omega)
        ).conductor_eq
  have hPair : ∀ j : OddNormIndex F K,
      wildOddCoefficientPair
        (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j hparity) C.lower C.lower_ne_one hcharOdd =
      wildOddTauPowerPair generator
        (((j : ZMod p).val : ℕ) : ResidueField F) := by
    intro j
    simpa only [generator, wildOddPreparation_highNormGeneratorNamedPair,
      wildOddNamedPairOfPhase] using
      wildOddCoefficientPair_eq_tauPowerPair_of_function_eq_pow
        (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j hparity)
        (highNormGeneratorPhase F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source hparity) C.lower C.lower_ne_one hcharOdd
        (by simpa only [quasiCharDataOfIsConductor_conductor] using hgenOdd)
        (j : ZMod p).val
        (highNormLiteralPower_criticalFunction_eq_pow F K ht hres pi hpi
          hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
            hupper gammaF hgammaF source j hparity)
  calc
    _ = ∏ j : OddNormIndex F K,
        (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source j hparity).criticalFactor := by
      apply Finset.prod_congr rfl
      intro j _
      apply LocalLamprechtPhaseData.criticalFactor_eq_of_criticalFunction_eq
      exact highSourceNormFunction_eq_actualTeichmuller F K ht hres pi hpi
        hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
          hupper gammaF hgammaF source j hparity
    _ = ∏ j : OddNormIndex F K,
        (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j hparity).criticalFactor :=
      wildOdd_highActualNormCriticalProduct_eq_clean F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF source hparity C.lower C.lower_ne_one
    _ = ∏ j : OddNormIndex F K,
        wildOddLowerPairPhase C.lower
          (wildOddTauPowerPair generator
            (((j : ZMod p).val : ℕ) : ResidueField F)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact wildOddPreparation_criticalFactor_eq_lowerPairPhase _ C.lower
        C.lower_ne_one hcharOdd _ (hPair j)
    _ = ∏ u : (ZMod p)ˣ,
        wildOddLowerPairPhase C.lower
          (wildOddTauPowerPair generator
            ((((u : ZMod p).val : ℕ) : ResidueField F))) :=
      (Equiv.prod_comp unitsEquivNeZero (fun j : {j : ZMod p // j ≠ 0} ↦
        wildOddLowerPairPhase C.lower
          (wildOddTauPowerPair generator
            ((j.val.val : ℕ) : ResidueField F)))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro u _
      congr 3
      change (((u : ZMod p).val : ℕ) : ResidueField F) =
        (ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p)
      rw [← ZMod.natCast_zmod_val (u : ZMod p)]
      simp

private theorem wildOddPreparation_highNormProduct_eq_one_of_even
    (hparity : lowCriticalParity (s + 1) = 0) :
    (∏ j : OddNormIndex F K,
      (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          j).criticalFactor) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  apply wildOddPreparation_criticalFactor_eq_one
  exact highSourceNormFunction_eq_one_of_even F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source hparity j

private theorem wildOddPreparation_highTwistProduct_eq_repeated
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF (Module.finrank F K) C source hepsilon hcharOdd
    (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          0).criticalFactor *
      ∏ j : OddNormIndex F K,
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
            (j : ZMod (Module.finrank F K))).criticalFactor =
      ∏ _j : ZMod (Module.finrank F K),
        wildOddLowerPairPhase C.lower (wildOddBasePair base) := by
  dsimp only
  let p := Module.finrank F K
  let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF p C source hepsilon hcharOdd
  let f : ZMod p → ℂ := fun j ↦
    (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source j
        ).criticalFactor
  calc
    _ = f 0 * ∏ j : {j : ZMod p // j ≠ 0}, f j := rfl
    _ = ∏ j : ZMod p, f j := (Fintype.prod_eq_mul_prod_subtype_ne f 0).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      apply wildOddPreparation_criticalFactor_eq_lowerPairPhase _ C.lower
        C.lower_ne_one hcharOdd _
      exact wildOdd_highTwistCoefficients_above_odd F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF p C source hepsilon hcharOdd j

private theorem wildOddPreparation_highTwistProduct_eq_one_of_even
    (hepsilon : epsilon = 0) :
    (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          0).criticalFactor *
      ∏ j : OddNormIndex F K,
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
            (j : ZMod (Module.finrank F K))).criticalFactor = 1 := by
  have hfactor : ∀ j : ZMod (Module.finrank F K),
      (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source j
          ).criticalFactor = 1 := by
    intro j
    apply wildOddPreparation_criticalFactor_eq_one
    exact highSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source hepsilon j
  rw [hfactor]
  simp_rw [hfactor]
  simp

private theorem wildOddPreparation_highUpstairsFactor_eq_upperPairPhase
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hchar : residueCharacteristic F = Module.finrank F K)
    (hcharOdd : ringChar (ResidueField F) ≠ 2)
    (P : WildOddUpperCoefficientPair (ResidueField F))
    (hP :
      let upper := highSourceDisplayedUpstairsCriticalPolarFunction F K ht
        hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd
          htpos hstrict hupper gammaF hgammaF (Module.finrank F K) hchar C
            source
      upper.upperCoefficientPair C.lower_ne_one hcharOdd = P) :
    (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
      ).criticalFactor = wildOddUpperPairPhase C.lower P := by
  let upper := highSourceDisplayedUpstairsCriticalPolarFunction F K ht hres
    pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
      hupper gammaF hgammaF (Module.finrank F K) hchar C source
  let upstairs := highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source
  calc
    upstairs.criticalFactor = phase
        (∑ x : ResidueField K, upstairs.criticalFunction x) :=
      upstairs.criticalFactor_eq_criticalFunctionPhase
    _ = phase (∑ x : ResidueField F, upper x) :=
      (upstairs.displayedInLowerCoordinate_phase
        (Module.finrank F K) hchar hres C).symm
    _ = quadraticPhase C.lower
        (upper.upperCoefficientPair C.lower_ne_one hcharOdd).polar
        (upper.upperCoefficientPair C.lower_ne_one hcharOdd).affine :=
      upper.phase_sum_eq_quadraticPhase hcharOdd C.lower_ne_one
    _ = wildOddUpperPairPhase C.lower P := by
      unfold wildOddUpperPairPhase
      rw [hP]

private theorem wildOddPreparation_highUpstairsFactor_eq_above
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF (Module.finrank F K) C source hepsilon hcharOdd
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
    (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
      ).criticalFactor = wildOddUpperPairPhase C.lower
        (wildOddUpperPairAbove (Module.finrank F K) base.eta N.dZero) := by
  dsimp only
  let p := Module.finrank F K
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF p C source hepsilon hcharOdd
  let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
    hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source hepsilon C
  let units : ResidueField F → Kˣ := highActualSourceUnit F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source hepsilon C
  have hbase : base.eta = N.eta := by
    change (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
      hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
        0).polarCoefficient C.lower C.lower_ne_one = N.eta
    exact highActual_basePolar_eq_eta F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source hepsilon C
  refine wildOddPreparation_highUpstairsFactor_eq_upperPairPhase F K ht hres
    pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
      hupper gammaF hgammaF source C hchar hcharOdd
        (wildOddUpperPairAbove p base.eta N.dZero) ?_
  calc
    _ = wildOddUpperPairAbove p N.eta N.dZero := by
      simpa only [p, hchar, N, units] using
        wildOdd_actualHighCoefficients_above F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source hepsilon C hcharOdd units (by
              intro X
              exact highActualSourceUnit_coe F K ht hres pi hpi hgen data
                chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
                  gammaF hgammaF source hepsilon C X)
    _ = _ := by rw [hbase]

private theorem wildOddPreparation_highUpstairsFactor_eq_one_of_even
    (hepsilon : epsilon = 0) :
    (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
      ).criticalFactor = 1 := by
  apply wildOddPreparation_criticalFactor_eq_one
  exact highSourceUpstairsFunction_eq_one_of_even F K ht hres pi hpi hgen
    data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source hepsilon

theorem wildOddPreparation_strictHigh_sourceCriticalQuotient_eq_one
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    (((highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
          ).criticalFactor *
        ∏ j : OddNormIndex F K,
          (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
            hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source j
            ).criticalFactor) /
      ((highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0
          ).criticalFactor *
        ∏ j : OddNormIndex F K,
          (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
            hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source
              (j : ZMod (Module.finrank F K))).criticalFactor)) = 1 := by
  let p := Module.finrank F K
  let hchar := residueCharacteristic_eq_degree_of_positive_break F K ht
    htpos pi hpi hgen
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  let omega := wildOddPreparationPrimeFieldUnitMap F p
  have homega := wildOddPreparationPrimeFieldUnitMap_injective F p
  have hp2 : p ≠ 2 := by intro hp; dsimp only [p] at hp; rw [hp] at hodd; norm_num at hodd
  have hepsilon : epsilon = 0 ∨ epsilon = 1 := by
    have := hF.epsilon_le_one
    omega
  have hparity : lowCriticalParity (s + 1) = 0 ∨
      lowCriticalParity (s + 1) = 1 := by
    have := lowCriticalParity_le_one (t := s + 1)
    omega
  rcases hepsilon with he | he <;> rcases hparity with hp | hp
  · rw [wildOddPreparation_highUpstairsFactor_eq_one_of_even F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source he]
    rw [wildOddPreparation_highNormProduct_eq_one_of_even F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source hp]
    rw [wildOddPreparation_highTwistProduct_eq_one_of_even F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source he]
    norm_num
  · rw [wildOddPreparation_highUpstairsFactor_eq_one_of_even F K ht hres pi
      hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
        hupper gammaF hgammaF source he]
    rw [wildOddPreparation_highTwistProduct_eq_one_of_even F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source he]
    rw [one_mul, div_one]
    rw [wildOddPreparation_highOddNormSourceProduct_eq_scalarPencil F K ht
      hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
        hstrict hupper gammaF hgammaF source hp C hcharOdd]
    exact wildOdd_belowTwistFactorsOdd C.lower C.lower_ne_one hp2 omega homega
      (wildOddPreparation_highNormGeneratorNamedPair F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF source hp C hcharOdd)
  · let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF p C source he hcharOdd
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source he C
    rw [wildOddPreparation_highUpstairsFactor_eq_above F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source he C hcharOdd]
    rw [wildOddPreparation_highNormProduct_eq_one_of_even F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source hp, mul_one]
    rw [wildOddPreparation_highTwistProduct_eq_repeated F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source he C hcharOdd]
    exact wildOdd_aboveBaseOddPhase C.lower C.lower_ne_one hp2 base N.dZero
      (by
        simpa only [N] using
          (highActualNormalization_dZero_ne_zero F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source he C))
  · let generator := wildOddPreparation_highNormGeneratorNamedPair F K ht
      hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
        hstrict hupper gammaF hgammaF source hp C hcharOdd
    let base := wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF p C source he hcharOdd
    let N := highActualNormalization F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source he C
    rw [wildOddPreparation_highUpstairsFactor_eq_above F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source he C hcharOdd]
    rw [wildOddPreparation_highOddNormSourceProduct_eq_scalarPencil F K ht
      hres pi hpi hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
        hstrict hupper gammaF hgammaF source hp C hcharOdd]
    rw [wildOddPreparation_highTwistProduct_eq_repeated F K ht hres pi hpi
      hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source he C hcharOdd]
    exact wildOdd_aboveAllOddPhaseQuotient C.lower C.lower_ne_one hp2 omega
      homega generator base N.dZero (by
        simpa only [N] using
          (highActualNormalization_dZero_ne_zero F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source he C))

end HighRawSource

/-- Complete strict-High provenance retained before any correction
linearization is chosen.  Both source-tied rows and the exact coordinates
needed by the later table-backed assembly are fields. -/
structure WildOddHighPhaseProvenance
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (phases : FirstMainPhaseData F K globalChi globalPsi data)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon) where
  chiK : LocalQuasiCharData K
  psiK : LocalAddCharData K
  dK : ℕ
  epsilonK : ℕ
  hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK
  hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1)
  hchi : chiK.character = (data.twistData 1).character.compNorm
  hpsi : psiK.character = data.baseAddChar.character.compTrace
  hodd : Odd (Module.finrank F K)
  htpos : 0 < t
  hstrict : t + 1 < (data.twistData 1).conductor
  hupper : (data.twistData 1).conductor < 2 * (t + 1)
  gammaF : Fˣ
  hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF
  A : F
  A_eq : A = highOddExactCoefficient F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows
  u : K
  u_eq : u = highOddNormalizedRatio F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows
  n : F
  n_eq : n = highOddNormalizedNorm F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows
  norm_u : norm F K u = n
  ord_u : ord K u =
    ((-(((data.twistData 1).conductor - (t + 1) : ℕ) : ℤ) : ℤ) :
      WithTop ℤ)
  CUp : LamprechtCriticalCoordinate K dK epsilonK
  CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
    (lowCriticalFloorDepth t) (lowCriticalParity t)
  CTwist : ZMod (Module.finrank F K) →
    LamprechtCriticalCoordinate F d epsilon
  extensionSource : phases.extension = LocalPhaseData.stationary
    (highSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source)
  normSource : ∀ j : OddNormIndex F K,
    phases.normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j)
  twistSource : ∀ j : ZMod (Module.finrank F K),
    phases.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j)) =
      LocalPhaseData.stationary
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j)
  hExtension : phases.extension = LocalPhaseData.stationary
    (highOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows CUp)
  hNorm : ∀ j : OddNormIndex F K,
    phases.normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (highOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
          hF htpos hstrict.le gammaF hgammaF source.normRows j (CNorm j))
  hTwist : ∀ j : ZMod (Module.finrank F K),
    phases.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd j)) =
      LocalPhaseData.stationary
        (highOddLinearTwistPhaseForComputationalData F K ht hres pi hpi
          hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
            hupper gammaF hgammaF source.productRows j (CTwist j))
  boundary_vacuous : wildOddCorrectionOffset (t + 1)
      (data.twistData 1).conductor = 0 → False

/-- Complete low-or-boundary provenance retained before any correction
linearization is chosen.  In particular, the source rows remain present
alongside the clean coordinate rows used by the existing quotient tables. -/
structure WildOddLowPhaseProvenance
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (phases : FirstMainPhaseData F K globalChi globalPsi data)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon) where
  chiK : LocalQuasiCharData K
  psiK : LocalAddCharData K
  hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1)
  hchi : chiK.character = (data.twistData 1).character.compNorm
  hpsi : psiK.character = data.baseAddChar.character.compTrace
  hodd : Odd (Module.finrank F K)
  hLow : (data.twistData 1).conductor ≤ t + 1
  delta : Fˣ
  epsilon1 : Kˣ
  hdelta : ord F (delta : F) =
    ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  hepsilon1 : ord K (epsilon1 : K) =
    (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ)
  hT : 2 ≤ t + 1
  hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ)
  hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
  P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth t) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
        delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF)
  table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
  WUp : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table
  WTwist : ∀ j : OddNormIndex F K,
    LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table j
  A : F
  A_eq : A = lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
  u : K
  u_eq : u = lowNormalizedRatio F K epsilon1 P
  n : F
  n_eq : n = lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
  norm_u : norm F K u = n
  ord_u : ord K u =
    (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ)
  CUp : LamprechtCriticalCoordinate K d epsilon
  CBase : LamprechtCriticalCoordinate F d epsilon
  CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
    (lowCriticalFloorDepth t) (lowCriticalParity t)
  CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
    (lowCriticalFloorDepth t) (lowCriticalParity t)
  extensionSource : phases.extension = LocalPhaseData.stationary
    (lowSourceUpstairsPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table WUp)
  baseSource : phases.twist 1 = LocalPhaseData.stationary
    (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table)
  normSource : ∀ j : OddNormIndex F K,
    phases.normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
          hdelta hT hgammaF P j)
  twistSource : ∀ j : OddNormIndex F K,
    phases.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table WTwist j)
  hExtension : phases.extension = LocalPhaseData.stationary
    (lowOddUpstairsPhaseForComputationalData F K ht hres pi hpi hgen data
      chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table WUp CUp)
  hBase : phases.twist 1 = LocalPhaseData.stationary
    (lowBasePhase F K ht hres pi hpi hgen (data.twistData 1) chiK
      data.baseAddChar psiK hminimal hchi hpsi hF hLow delta epsilon1
        hdelta hepsilon1 hT hgammaF hgammaK P table CBase)
  hNorm : ∀ j : OddNormIndex F K,
    phases.normCharacter
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (lowOddNormPhaseForComputationalData F K ht hres pi hpi hgen data
          hF delta epsilon1 hdelta hT hgammaF P j (CNorm j))
  hTwist : ∀ j : OddNormIndex F K,
    phases.twist
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))) =
      LocalPhaseData.stationary
        (lowOddTwistPhaseForComputationalData F K ht hres pi hpi hgen data
          chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
            hepsilon1 hT hgammaF hgammaK P table j (WTwist j) (CTwist j))

/-- The preassembly branch retained for `CorrectionPreparation`. -/
inductive WildOddPhaseBranch
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (phases : FirstMainPhaseData F K globalChi globalPsi data)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon) : Type
  | high (H : WildOddHighPhaseProvenance F K ht hres pi hpi hgen
      data phases hF)
  | low (L : WildOddLowPhaseProvenance F K ht hres pi hpi hgen
      data phases hF)

/-- Source-retaining Wild odd preparation.  This deliberately stops before
the correction-depth linearizations and exact assembly. -/
structure WildOddPhasePrepared
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) where
  d : ℕ
  epsilon : ℕ
  conductorDecomposition :
    IsStationaryConductorDecomposition chiF.conductor d epsilon
  nonstable : d < t + 1
  degree_eq : Module.finrank F K = residueCharacteristic F
  odd_degree : Odd (Module.finrank F K)
  data : FirstMainComputationalData F K chiF.character psiF.character
  data_twist_one : data.twistData 1 = chiF
  data_baseAddChar : data.baseAddChar = psiF
  dataConductorDecomposition : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon
  phases : FirstMainPhaseData F K chiF.character psiF.character data
  branch : WildOddPhaseBranch F K ht hres pi hpi hgen data phases
    dataConductorDecomposition
  residualAddChar : FrobeniusResidualAddCharData F (Module.finrank F K)
  parity : WildOddParityReductionData F (Module.finrank F K)
  rawResidualPhase_eq : phases.criticalNumerator / phases.criticalDenominator =
    wildOddCompleteResidualPhaseQuotient F (Module.finrank F K)
      degree_eq.symm residualAddChar parity

/-- Internal phase preparation before the raw quotient theorem is attached. -/
private structure WildOddPhasePreparedCore
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) where
  d : ℕ
  epsilon : ℕ
  conductorDecomposition :
    IsStationaryConductorDecomposition chiF.conductor d epsilon
  nonstable : d < t + 1
  degree_eq : Module.finrank F K = residueCharacteristic F
  odd_degree : Odd (Module.finrank F K)
  data : FirstMainComputationalData F K chiF.character psiF.character
  data_twist_one : data.twistData 1 = chiF
  data_baseAddChar : data.baseAddChar = psiF
  dataConductorDecomposition : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon
  phases : FirstMainPhaseData F K chiF.character psiF.character data
  branch : WildOddPhaseBranch F K ht hres pi hpi hgen data phases
    dataConductorDecomposition
  residualAddChar : FrobeniusResidualAddCharData F (Module.finrank F K)
  parity : WildOddParityReductionData F (Module.finrank F K)

private noncomputable def wildOddPreparationLowCore
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor)
    (hnonstable : chiF.conductor / 2 < t + 1)
    (hLow : chiF.conductor ≤ t + 1)
    (hdegree : Module.finrank F K = residueCharacteristic F)
    (hoddDegree : Odd (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    WildOddPhasePreparedCore F K t ht hres pi hpi hgen chiF psiF := by
  let chiK : LocalQuasiCharData K :=
    canonicalLocalQuasiCharData K chiF.character.compNorm
  let psiK : LocalAddCharData K :=
    wildTracePullbackData F K ht hres pi hpi hgen psiF
  have hchi0 : chiK.character = chiF.character.compNorm := rfl
  have hpsi0 : psiK.character = psiF.character.compTrace := rfl
  let data := wildOddPreparationComputationalData F K ht hres pi hpi hgen
    chiF chiK psiF psiK hchi0 hpsi0
  have hdataOne : data.twistData 1 = chiF := by
    exact wildOddPreparationComputationalData_twist_one F K ht hres pi hpi
      hgen chiF chiK psiF psiK hchi0 hpsi0
  have hdataBase : data.baseAddChar = psiF := rfl
  let d := chiF.conductor / 2
  let epsilon := chiF.conductor % 2
  have hF : IsStationaryConductorDecomposition chiF.conductor d epsilon :=
    wildOddPreparation_conductorDecomposition hm
  have hFData : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon := by
    rw [hdataOne]
    exact hF
  have hminimalData : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1) := by
    rw [hdataOne]
    exact hminimal
  have hchi : chiK.character = (data.twistData 1).character.compNorm := by
    rw [hdataOne]
    exact hchi0
  have hpsi : psiK.character = data.baseAddChar.character.compTrace := by
    rw [hdataBase]
    exact hpsi0
  have hLowData : (data.twistData 1).conductor ≤ t + 1 := by
    rw [hdataOne]
    exact hLow
  let delta := wildOddPreparationUnitOfOrd F
    (((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor)
  let epsilon1 := wildOddPreparationUnitOfOrd K
    ((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ)
  have hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) :
        WithTop ℤ) :=
    wildOddPreparationUnitOfOrd_order F _
  have hepsilon1 : ord K (epsilon1 : K) =
      (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ) :=
    wildOddPreparationUnitOfOrd_order K _
  have hT : 2 ≤ t + 1 := by omega
  have hgammaF := lowGammaF_order (t := t) F K hres
    (data.twistData 1) data.baseAddChar delta epsilon1 hdelta hepsilon1
      hLowData
  have hgammaK := lowGammaK_order F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimalData hchi hpsi
      delta epsilon1 hdelta hepsilon1 hLowData
  let hexists := lowConductorParameterTable F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimalData hchi hpsi
      hFData hLowData delta epsilon1 hdelta hepsilon1
  let P := Classical.choose hexists
  let table := Classical.choose_spec hexists
  let WUp := Classical.choice
    (lowOddUpstairsWitness_nonempty F K ht hres pi hpi hgen data chiK psiK
      hFData hminimalData hchi hpsi hLowData delta epsilon1 hdelta
        hepsilon1 hT hgammaF hgammaK P table)
  let WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hFData
        hminimalData hchi hpsi hLowData delta epsilon1 hdelta hepsilon1 hT
          hgammaF hgammaK P table j := fun j ↦
    Classical.choice
      (lowOddTwistWitness_nonempty F K ht hres pi hpi hgen data chiK psiK
        hFData hminimalData hchi hpsi hLowData delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table j)
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let CUp : LamprechtCriticalCoordinate K d epsilon :=
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      hFData.epsilon_le_one S.upperUniformizer S.upper_order
  let CBase : LamprechtCriticalCoordinate F d epsilon :=
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      hFData.epsilon_le_one S.lowerUniformizer S.lower_order
  let CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t) := fun _ ↦
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      (lowCriticalConductorDecomposition (t := t) hT).epsilon_le_one
      S.lowerUniformizer S.lower_order
  let CTwist : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t) := CNorm
  let extension := lowSourceUpstairsPhase F K ht hres pi hpi hgen data
    chiK psiK hFData hminimalData hchi hpsi hLowData delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WUp
  let base := lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK
    hFData hminimalData hchi hpsi hLowData delta epsilon1 hdelta hepsilon1
      hT hgammaF hgammaK P table
  let normRow := fun j : OddNormIndex F K ↦
    lowSourceNormPhase F K ht hres pi hpi hgen data hFData delta epsilon1
      hdelta hT hgammaF P j
  let twistRow := fun j : OddNormIndex F K ↦
    lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hFData
      hminimalData hchi hpsi hLowData delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WTwist j
  let phases := wildOddPreparationPhaseData F K ht hres pi hpi hgen data
    extension normRow base twistRow
  have extensionSource : phases.extension = .stationary extension := by
    dsimp only [phases]
    exact wildOddPreparationPhaseData_extension F K ht hres pi hpi hgen
      data extension normRow base twistRow
  have baseSource : phases.twist 1 = .stationary base := by
    dsimp only [phases]
    exact wildOddPreparationPhaseData_base F K ht hres pi hpi hgen data
      extension normRow base twistRow
  have normSource : ∀ j : OddNormIndex F K,
      phases.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) = .stationary (normRow j) := by
    intro j
    dsimp only [phases]
    exact wildOddPreparationPhaseData_norm F K ht hres pi hpi hgen data
      extension normRow base twistRow j
  have twistSource : ∀ j : OddNormIndex F K,
      phases.twist
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) = .stationary (twistRow j) := by
    intro j
    dsimp only [phases]
    exact wildOddPreparationPhaseData_twist F K ht hres pi hpi hgen data
      extension normRow base twistRow j
  let C := wildOddPreparationResidualAddCharAtDegree F K ht htpos pi hpi hgen
  let parity := wildOddPreparationLowParity F K ht hres pi hpi hgen data
    chiK psiK hFData hminimalData hchi hpsi hLowData delta epsilon1 hdelta
      hepsilon1 hT hgammaF hgammaK P table WTwist C hcharOdd
  let L : WildOddLowPhaseProvenance F K ht hres pi hpi hgen data phases
      hFData :=
    { chiK := chiK
      psiK := psiK
      hminimal := hminimalData
      hchi := hchi
      hpsi := hpsi
      hodd := hoddDegree
      hLow := hLowData
      delta := delta
      epsilon1 := epsilon1
      hdelta := hdelta
      hepsilon1 := hepsilon1
      hT := hT
      hgammaF := hgammaF
      hgammaK := hgammaK
      P := P
      table := table
      WUp := WUp
      WTwist := WTwist
      A := lowOddExactCoefficient (F := F) (K := K) (P := P) (hT := hT)
      A_eq := rfl
      u := lowNormalizedRatio F K epsilon1 P
      u_eq := rfl
      n := lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)
      n_eq := rfl
      norm_u := by
        simpa only [lowOddNormalizedNorm] using
          lowNormalizedRatio_norm F K epsilon1 P
      ord_u := by
        simpa using lowNormalizedRatio_order F K epsilon1 hepsilon1 P
      CUp := CUp
      CBase := CBase
      CNorm := CNorm
      CTwist := CTwist
      extensionSource := extensionSource
      baseSource := baseSource
      normSource := normSource
      twistSource := twistSource
      hExtension := by
        simpa only [extension, lowSourceUpstairsPhase,
          LocalLamprechtPhaseData.sourceTiedRow, CUp, S] using extensionSource
      hBase := by
        simpa only [base, lowSourceBasePhase,
          LocalLamprechtPhaseData.sourceTiedRow, CBase, S] using baseSource
      hNorm := by
        intro j
        simpa only [normRow, lowSourceNormPhase,
          LocalLamprechtPhaseData.sourceTiedRow, CNorm, S] using normSource j
      hTwist := by
        intro j
        simpa only [twistRow, lowSourceTwistPhase,
          LocalLamprechtPhaseData.sourceTiedRow, CTwist, CNorm, S] using
            twistSource j }
  exact
    { d := d
      epsilon := epsilon
      conductorDecomposition := hF
      nonstable := hnonstable
      degree_eq := hdegree
      odd_degree := hoddDegree
      data := data
      data_twist_one := hdataOne
      data_baseAddChar := hdataBase
      dataConductorDecomposition := hFData
      phases := phases
      branch := .low L
      residualAddChar := C
      parity := parity }

private noncomputable def wildOddPreparationHighCore
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor)
    (hnonstable : chiF.conductor / 2 < t + 1)
    (hstrict : t + 1 < chiF.conductor)
    (hdegree : Module.finrank F K = residueCharacteristic F)
    (hoddDegree : Odd (Module.finrank F K))
    (_hcharOdd : ringChar (ResidueField F) ≠ 2) :
    WildOddPhasePreparedCore F K t ht hres pi hpi hgen chiF psiF := by
  let chiK : LocalQuasiCharData K :=
    canonicalLocalQuasiCharData K chiF.character.compNorm
  let psiK : LocalAddCharData K :=
    wildTracePullbackData F K ht hres pi hpi hgen psiF
  have hchi0 : chiK.character = chiF.character.compNorm := rfl
  have hpsi0 : psiK.character = psiF.character.compTrace := rfl
  let data := wildOddPreparationComputationalData F K ht hres pi hpi hgen
    chiF chiK psiF psiK hchi0 hpsi0
  have hdataOne : data.twistData 1 = chiF := by
    exact wildOddPreparationComputationalData_twist_one F K ht hres pi hpi
      hgen chiF chiK psiF psiK hchi0 hpsi0
  have hdataBase : data.baseAddChar = psiF := rfl
  let d := chiF.conductor / 2
  let epsilon := chiF.conductor % 2
  have hF : IsStationaryConductorDecomposition chiF.conductor d epsilon :=
    wildOddPreparation_conductorDecomposition hm
  have hFData : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon := by
    rw [hdataOne]
    exact hF
  have hminimalData : IsMinimalNormCharacterOrbitRepresentative F K
      (data.twistData 1) := by
    rw [hdataOne]
    exact hminimal
  have hchi : chiK.character = (data.twistData 1).character.compNorm := by
    rw [hdataOne]
    exact hchi0
  have hpsi : psiK.character = data.baseAddChar.character.compTrace := by
    rw [hdataBase]
    exact hpsi0
  have hstrictData : t + 1 < (data.twistData 1).conductor := by
    rw [hdataOne]
    exact hstrict
  have hupper : chiF.conductor < 2 * (t + 1) := by
    rw [hF.conductor_eq]
    omega
  have hupperData : (data.twistData 1).conductor < 2 * (t + 1) := by
    rw [hdataOne]
    exact hupper
  have hrel := highParameter_ramified_conductor_relation F K ht hres pi hpi
    hgen (data.twistData 1) chiK hchi hstrictData
  have hconductorK := highParameter_ramified_conductor_eq F K ht hres pi hpi
    hgen (data.twistData 1) chiK hchi hstrictData
  have hmK : 1 < chiK.conductor := by
    rw [hconductorK]
    have hp := (PrimeCyclicExtension.degree_prime F K).pos
    have hmData : 1 < (data.twistData 1).conductor :=
      hFData.conductor_gt_one
    have hself := self_le_herbrandPsiNat t (Module.finrank F K) hp
      ((data.twistData 1).conductor - 1)
    omega
  let dK := chiK.conductor / 2
  let epsilonK := chiK.conductor % 2
  have hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK :=
    wildOddPreparation_conductorDecomposition hmK
  let gammaF := wildOddPreparationUnitOfOrd F
    (((data.twistData 1).conductor : ℤ) + data.baseAddChar.conductor)
  have hgammaF : ord F (gammaF : F) =
      ((((data.twistData 1).conductor : ℤ) +
        data.baseAddChar.conductor : ℤ) : WithTop ℤ) :=
    wildOddPreparationUnitOfOrd_order F _
  let H := highConductorParameter_oddIntermediate F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hFData hK hminimalData
      hchi hpsi hoddDegree htpos hstrictData.le hupperData gammaF hgammaF
  let source := Classical.choice
    (highOddCoherentPhaseSource_nonempty F K ht hres pi hpi hgen
      (data.twistData 1) chiK data.baseAddChar psiK hFData hK hminimalData
        hchi hpsi hoddDegree htpos hstrictData.le hupperData gammaF hgammaF H)
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let CUp : LamprechtCriticalCoordinate K dK epsilonK :=
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      hK.epsilon_le_one S.upperUniformizer S.upper_order
  let CNorm : OddNormIndex F K → LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t) := fun _ ↦
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      (lowCriticalConductorDecomposition (t := t) (by omega)).epsilon_le_one
      S.lowerUniformizer S.lower_order
  let CTwist : ZMod (Module.finrank F K) →
      LamprechtCriticalCoordinate F d epsilon := fun _ ↦
    PhaseReductionResidualCoordinateSource.criticalCoordinateOfParity
      hFData.epsilon_le_one S.lowerUniformizer S.lower_order
  let extension := highSourceUpstairsPhase F K ht hres pi hpi hgen data
    chiK psiK hFData hK hminimalData hchi hpsi hoddDegree htpos hstrictData
      hupperData gammaF hgammaF source
  let normRow := fun j : OddNormIndex F K ↦
    highSourceNormPhase F K ht hres pi hpi hgen data chiK psiK hFData hK
      hminimalData hchi hpsi hoddDegree htpos hstrictData hupperData gammaF
        hgammaF source j
  let sourceTwist := fun j : ZMod (Module.finrank F K) ↦
    highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hFData hK
      hminimalData hchi hpsi hoddDegree htpos hstrictData hupperData gammaF
        hgammaF source j
  let base : LocalLamprechtPhaseData F (data.twistData 1)
      data.baseAddChar := by
    rw [← ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen]
    exact sourceTwist 0
  let twistRow := fun j : OddNormIndex F K ↦
    sourceTwist (j : ZMod (Module.finrank F K))
  let common := wildOddPreparationPhaseData F K ht hres pi hpi hgen data
    extension normRow base twistRow
  let twistIndexing : Multiplicative (ZMod (Module.finrank F K)) ≃
      NormCharacter F K :=
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv
  let twistIndexed : ∀ j : Multiplicative (ZMod (Module.finrank F K)),
      LocalPhaseData F (data.twistData (twistIndexing j))
        data.baseAddChar := fun j ↦ .stationary (sourceTwist j.toAdd)
  let phases : FirstMainPhaseData F K chiF.character psiF.character data :=
    { extension := common.extension
      normCharacter := common.normCharacter
      twist := (Equiv.piCongrLeft
        (fun mu => LocalPhaseData F (data.twistData mu) data.baseAddChar)
          twistIndexing) twistIndexed }
  have extensionSource : phases.extension = .stationary extension := by
    dsimp only [phases]
    exact wildOddPreparationPhaseData_extension F K ht hres pi hpi hgen
      data extension normRow base twistRow
  have normSource : ∀ j : OddNormIndex F K,
      phases.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) = .stationary (normRow j) := by
    intro j
    dsimp only [phases]
    exact wildOddPreparationPhaseData_norm F K ht hres pi hpi hgen data
      extension normRow base twistRow j
  have twistSource : ∀ j : ZMod (Module.finrank F K),
      phases.twist
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)) = .stationary (sourceTwist j) := by
    intro j
    dsimp only [phases]
    exact wildOddPreparation_piCongrLeft_at_image
      (fun mu => LocalPhaseData F (data.twistData mu) data.baseAddChar)
      twistIndexing twistIndexed (Multiplicative.ofAdd j)
  let C := wildOddPreparationResidualAddCharAtDegree F K ht htpos pi hpi hgen
  let parity : WildOddParityReductionData F (Module.finrank F K) := by
    cases t with
    | zero => omega
    | succ s =>
        exact wildOddPreparationHighParity F K ht hres pi hpi hgen data
          chiK psiK hFData hK hminimalData hchi hpsi hoddDegree htpos
            hstrictData hupperData gammaF hgammaF source C _hcharOdd
  let Q := source.productRows
  let A := highOddExactCoefficient F K ht hres pi hpi hgen data chiK psiK
    hFData hK hminimalData hchi hpsi hoddDegree htpos hstrictData hupperData
      gammaF hgammaF Q
  let u := highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
    hFData hK hminimalData hchi hpsi hoddDegree htpos hstrictData hupperData
      gammaF hgammaF Q
  let n := highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
    hFData hK hminimalData hchi hpsi hoddDegree htpos hstrictData hupperData
      gammaF hgammaF Q
  let HH : WildOddHighPhaseProvenance F K ht hres pi hpi hgen data phases
      hFData :=
    { chiK := chiK
      psiK := psiK
      dK := dK
      epsilonK := epsilonK
      hK := hK
      hminimal := hminimalData
      hchi := hchi
      hpsi := hpsi
      hodd := hoddDegree
      htpos := htpos
      hstrict := hstrictData
      hupper := hupperData
      gammaF := gammaF
      hgammaF := hgammaF
      source := source
      A := A
      A_eq := rfl
      u := u
      u_eq := rfl
      n := n
      n_eq := rfl
      norm_u := rfl
      ord_u := by
        exact highOddNormalizedRatio_order F K ht hres pi hpi hgen data
          chiK psiK hFData hK hminimalData hchi hpsi hoddDegree htpos
            hstrictData hupperData gammaF hgammaF Q
      CUp := CUp
      CNorm := CNorm
      CTwist := CTwist
      extensionSource := extensionSource
      normSource := normSource
      twistSource := twistSource
      hExtension := by
        simpa only [extension, highSourceUpstairsPhase,
          LocalLamprechtPhaseData.sourceTiedRow, CUp, S] using extensionSource
      hNorm := by
        intro j
        simpa only [normRow, highSourceNormPhase,
          LocalLamprechtPhaseData.sourceTiedRow, CNorm, S] using normSource j
      hTwist := by
        intro j
        simpa only [sourceTwist, highSourceTwistPhase,
          LocalLamprechtPhaseData.sourceTiedRow, CTwist, S] using twistSource j
      boundary_vacuous := by
        intro hzero
        unfold wildOddCorrectionOffset at hzero
        have heq : t + 1 = (data.twistData 1).conductor := by
          exact_mod_cast (sub_eq_zero.mp hzero)
        omega }
  exact
    { d := d
      epsilon := epsilon
      conductorDecomposition := hF
      nonstable := hnonstable
      degree_eq := hdegree
      odd_degree := hoddDegree
      data := data
      data_twist_one := hdataOne
      data_baseAddChar := hdataBase
      dataConductorDecomposition := hFData
      phases := phases
      branch := .high HH
      residualAddChar := C
      parity := parity }

private noncomputable def wildOddPreparationCore
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t)
    (hodd : residueCharacteristic F ≠ 2)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor)
    (hnonstable : chiF.conductor / 2 < t + 1) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : CharP (ResidueField F) (Module.finrank F K) :=
      ringChar.of_eq
        (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
          hpi hgen)
    WildOddPhasePreparedCore F K t ht hres pi hpi hgen chiF psiF := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  letI : CharP (ResidueField F) (Module.finrank F K) := ringChar.of_eq hchar
  have hdegree : Module.finrank F K = residueCharacteristic F := hchar.symm
  have hoddDegree : Odd (Module.finrank F K) := by
    rw [← hchar]
    exact (residueCharacteristic_prime F).odd_of_ne_two hodd
  have hp2 : Module.finrank F K ≠ 2 := by
    intro hp
    rw [hp] at hoddDegree
    norm_num at hoddDegree
  have hcharOdd : ringChar (ResidueField F) ≠ 2 := by
    simpa only [ringChar.eq] using hp2
  by_cases hLow : chiF.conductor ≤ t + 1
  · exact wildOddPreparationLowCore ht htpos hres pi hpi hgen chiF psiF
      hminimal hm hnonstable hLow hdegree hoddDegree hcharOdd
  · have hstrict : t + 1 < chiF.conductor := by omega
    exact wildOddPreparationHighCore ht htpos hres pi hpi hgen chiF psiF
      hminimal hm hnonstable hstrict hdegree hoddDegree hcharOdd

local instance lowGreen_residueFieldFintype
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Fintype (ResidueField E) :=
  residueFieldFintype E

private theorem lowGreen_factor_eq_one
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (hfun : ∀ x : ResidueField E, D.criticalFunction x = 1) :
    D.criticalFactor = 1 := by
  rw [D.criticalFactor_eq_criticalFunctionPhase]
  unfold LocalLamprechtPhaseData.criticalFunctionPhase
  simp_rw [hfun]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : 0 < (Fintype.card (ResidueField E) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
  exact phase_ofReal_pos hcard

private theorem lowGreen_lowerFactor
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (P : WildOddCoefficientPair (ResidueField E))
    (hP : wildOddCoefficientPair D psi0 hpsi0 hchar = P) :
    D.criticalFactor = wildOddLowerPairPhase psi0 P := by
  rw [D.criticalFactor_eq_quadraticPhase psi0 hpsi0 hchar]
  unfold wildOddLowerPairPhase
  change quadraticPhase psi0 (wildOddCoefficientPair D psi0 hpsi0
    hchar).polar (wildOddCoefficientPair D psi0 hpsi0 hchar).affine = _
  rw [hP]

private theorem lowGreen_upperFactor
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {chi : LocalQuasiCharData K} {psi : LocalAddCharData K}
    (p : ℕ) [Fact p.Prime] (hchar : residueCharacteristic F = p)
    (hres : residueDegree F K = 1)
    (C : FrobeniusResidualAddCharData F p)
    (hcharOdd : ringChar (ResidueField F) ≠ 2)
    (D : LocalLamprechtPhaseData K chi psi)
    (P : WildOddUpperCoefficientPair (ResidueField F))
    (hP : (D.displayedInLowerCoordinate p hchar hres C).upperCoefficientPair
      C.lower_ne_one hcharOdd = P) :
    D.criticalFactor = wildOddUpperPairPhase C.lower P := by
  let phi := D.displayedInLowerCoordinate p hchar hres C
  calc
    D.criticalFactor = phase (∑ y : ResidueField K,
        D.criticalFunction y) := D.criticalFactor_eq_criticalFunctionPhase
    _ = phase (∑ x : ResidueField F, phi x) :=
      (D.displayedInLowerCoordinate_phase p hchar hres C).symm
    _ = quadraticPhase C.lower
          (phi.upperCoefficientPair C.lower_ne_one hcharOdd).polar
          (phi.upperCoefficientPair C.lower_ne_one hcharOdd).affine :=
      phi.phase_sum_eq_quadraticPhase hcharOdd C.lower_ne_one
    _ = wildOddUpperPairPhase C.lower P := by
      unfold wildOddUpperPairPhase
      rw [hP]

private theorem lowGreen_tauPowerPair_eq_scaled
    {k : Type*} [Field k]
    (generator base : WildOddNamedCoefficientPair k) (u : k) :
    wildOddTauPowerPair generator u =
      ⟨base.eta * (u * wildOddBoundaryRho generator base),
        base.eta * (u * wildOddBoundaryTau generator base)⟩ := by
  have heta := wildOddBoundary_eta_eq generator base
  have hd := wildOddBoundaryDZero_ne_zero generator base
  apply WildOddCoefficientPair.ext
  · dsimp only [wildOddTauPowerPair]
    rw [heta]
    unfold wildOddBoundaryRho
    field_simp [hd]
  · dsimp only [wildOddTauPowerPair]
    rw [heta]
    unfold wildOddBoundaryTau wildOddBoundaryRho
    field_simp [hd]

private theorem lowGreen_boundaryPair_eq_scaled
    {k : Type*} [Field k]
    (generator base : WildOddNamedCoefficientPair k) (j : k) :
    wildOddBoundaryPair generator base j =
      ⟨base.eta * (1 + j * wildOddBoundaryRho generator base),
        base.eta * (wildOddBoundarySigma generator base +
          j * wildOddBoundaryTau generator base)⟩ := by
  have heta := wildOddBoundary_eta_eq generator base
  have hd := wildOddBoundaryDZero_ne_zero generator base
  apply WildOddCoefficientPair.ext
  · dsimp only [wildOddBoundaryPair]
    rw [heta]
    unfold wildOddBoundaryRho
    field_simp [hd]
    ring
  · dsimp only [wildOddBoundaryPair]
    rw [heta]
    unfold wildOddBoundarySigma wildOddBoundaryTau wildOddBoundaryRho
    field_simp [hd]
    ring

private theorem lowGreen_scaledBoundaryQuotient
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hp2 : p ≠ 2) (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (hnonzero : forall j : {j : ZMod p // j ≠ 0},
      ((j : ZMod p).val : ResidueField F) +
        wildOddBoundaryDZero generator base ≠ 0) :
    (quadraticPhase C.lower
          (base.eta * (wildOddBoundaryA0 F p hchar C generator base) ^ p)
          (base.eta * (wildOddBoundaryB0 F p hchar C generator base) ^ p) *
        ∏ j : {j : ZMod p // j ≠ 0},
          wildOddLowerPairPhase C.lower
            (wildOddTauPowerPair generator (j.val.val : ResidueField F))) /
      (wildOddLowerPairPhase C.lower (wildOddBasePair base) *
        ∏ j : {j : ZMod p // j ≠ 0},
          wildOddLowerPairPhase C.lower
            (wildOddBoundaryPair generator base
              (j.val.val : ResidueField F))) = 1 := by
  let certificate := wildOdd_boundaryAffinePencilCertificate F p hchar C
    generator base hnonzero
  let c0 := (C.frobeniusEquiv hchar).symm base.eta
  have hc0pow : c0 ^ p = base.eta := by
    rw [← C.frobeniusEquiv_apply hchar]
    exact (C.frobeniusEquiv hchar).apply_symm_apply base.eta
  have hscale := affinePencil_homogeneous_quotient hp2 C.lower
    C.lower_ne_one C.frobenius certificate.rho_ne_zero
      certificate.one_add_index_mul_rho_ne_zero certificate.a0_pow
        certificate.b0_pow hc0pow base.eta_ne_zero
  have hnorm :
      (∏ j : {j : ZMod p // j ≠ 0},
        wildOddLowerPairPhase C.lower
          (wildOddTauPowerPair generator (j.val.val : ResidueField F))) =
      ∏ u : (ZMod p)ˣ,
        quadraticPhase C.lower
          (base.eta * ((ZMod.castHom (dvd_refl p) (ResidueField F))
            (u : ZMod p) * wildOddBoundaryRho generator base))
          (base.eta * ((ZMod.castHom (dvd_refl p) (ResidueField F))
            (u : ZMod p) * wildOddBoundaryTau generator base)) := by
    rw [← Equiv.prod_comp unitsEquivNeZero
      (fun j : {j : ZMod p // j ≠ 0} =>
        wildOddLowerPairPhase C.lower
          (wildOddTauPowerPair generator (j.val.val : ResidueField F)))]
    apply Finset.prod_congr rfl
    intro u _
    unfold wildOddLowerPairPhase
    rw [lowGreen_tauPowerPair_eq_scaled generator base]
    congr 2 <;> simp
  have hden :
      wildOddLowerPairPhase C.lower (wildOddBasePair base) *
          (∏ j : {j : ZMod p // j ≠ 0},
            wildOddLowerPairPhase C.lower
              (wildOddBoundaryPair generator base
                (j.val.val : ResidueField F))) =
        ∏ j : ZMod p,
          quadraticPhase C.lower
            (base.eta * (1 + (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
              wildOddBoundaryRho generator base))
            (base.eta * (wildOddBoundarySigma generator base +
              (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
                wildOddBoundaryTau generator base)) := by
    let f : ZMod p → ℂ := fun j => wildOddLowerPairPhase C.lower
      (wildOddBoundaryPair generator base (j.val : ResidueField F))
    calc
      _ = f 0 * ∏ j : {j : ZMod p // j ≠ 0}, f j := by
        simp [f, wildOddBoundaryPair_zero]
      _ = ∏ j : ZMod p, f j :=
        (Fintype.prod_eq_mul_prod_subtype_ne f 0).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        unfold f wildOddLowerPairPhase
        rw [lowGreen_boundaryPair_eq_scaled generator base]
        congr 2 <;> simp
  rw [hnorm, hden, hscale]
  exact wildOdd_boundaryOddPhaseQuotient F p hp2 hchar C generator base
    hnonzero

section

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K] [Finite (NormCharacter F K)]
  [CharP (ResidueField F) (Module.finrank F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  {data : FirstMainComputationalData F K globalChi globalPsi}
  {phases : FirstMainPhaseData F K globalChi globalPsi data}
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (L : WildOddLowPhaseProvenance F K ht hres pi hpi hgen data phases hF)

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

private theorem lowGreen_strictUpper_eq_base
    (hstrict : (data.twistData 1).conductor < t + 1)
    (hepsilon : epsilon = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    (lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
      L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
        L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp
        ).criticalFactor =
      (lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
        L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
          L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table).criticalFactor := by
  cases t with
  | zero =>
    have hT := L.hT
    omega
  | succ s =>
    let p := Module.finrank F K
    let hchar : residueCharacteristic F = p :=
      residueCharacteristic_eq_degree_of_positive_break F K ht (by omega)
        pi hpi hgen
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF L.hLow
      L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.P hepsilon C
    have hbaseOdd : Odd (data.twistData 1).conductor :=
      ⟨d, by simpa only [hepsilon] using hF.conductor_eq⟩
    let base := wildOddLowBaseNamedPair F K ht hres pi hpi hgen data
      L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1
        L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table C.lower
          C.lower_ne_one hcharOdd hbaseOdd
    have hBaseEta : base.eta = N.eta := by
      simpa only [base, N] using
        lowActual_baseNamedEta_eq_eta F K ht hres pi hpi hgen data L.chiK
          L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1
            L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
              hepsilon C hcharOdd
    have hN := lowActualNormalization_eq_strict F K ht hres pi hpi hgen
      data hF L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT
        L.hgammaF L.P hepsilon hstrict C
    have hN' : N = lowActualNormalization_strict F K ht hres pi hpi hgen
        data hF L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
          L.P hepsilon hstrict C := by
      simpa only [N] using hN
    have hbaseCoeff :
        (lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data
          L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table p C).affineCoefficient hcharOdd C.lower_ne_one =
          (lowActualNormalization_strict F K ht hres pi hpi hgen data hF
            L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.P
              hepsilon hstrict C).eta * base.gamma := by
      rw [← hN, ← hBaseEta]
      change (wildOddCoefficientPair
        (lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
          L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
            L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table) C.lower
              C.lower_ne_one hcharOdd).affine = base.eta * base.gamma
      simpa only [base, wildOddBasePair] using congrArg
        WildOddCoefficientPair.affine
          (wildOdd_lowBaseCoefficients F K ht hres pi hpi hgen data L.chiK
            L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1
              L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
                C.lower C.lower_ne_one hcharOdd hbaseOdd)
    let units : ResidueField F → Kˣ := fun X => lowActualSourceUnit F K ht
      hres pi hpi hgen data hF L.hLow L.delta L.epsilon1 L.hdelta
        L.hepsilon1 L.hT L.hgammaF L.P hepsilon C X
    have hunits := lowActualSourceUnit_coe F K ht hres pi hpi hgen data hF
      L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.P
        hepsilon C
    have hPair :
        let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht
          hres pi hpi hgen data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi
            L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
              L.hgammaK L.P L.table p hchar C L.WUp
        upper.upperCoefficientPair C.lower_ne_one hcharOdd =
          wildOddUpperPairBelow base.eta base.gamma := by
      dsimp only
      rw [hBaseEta, hN']
      exact wildOdd_actualLowCoefficients_strict F K ht hres pi hpi hgen
        data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
          L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
            L.table L.WUp L.hodd hepsilon hstrict C hcharOdd base.gamma
              hbaseCoeff units hunits
    have hUpper := lowGreen_upperFactor F K p hchar hres C hcharOdd
      (lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK L.psiK
        hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
          L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp) _ hPair
    have hBase := lowGreen_lowerFactor
      (lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
        L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
          L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table) C.lower
            C.lower_ne_one hcharOdd _
              (wildOdd_lowBaseCoefficients F K ht hres pi hpi hgen data
                L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
                  L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK
                    L.P L.table C.lower C.lower_ne_one hcharOdd hbaseOdd)
    rw [hUpper, hBase]
    rfl

private theorem lowGreen_boundaryQuotient
    (hboundary : (data.twistData 1).conductor = t + 1)
    (hepsilon : epsilon = 1)
    (hparity : lowCriticalParity t = 1)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    let U := lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK
      L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1
        L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp
    let B := lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK
      hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
        L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
    let R := fun j : OddNormIndex F K => lowSourceNormPhase F K ht hres pi
      hpi hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P j
    let T := fun j : OddNormIndex F K => lowSourceTwistPhase F K ht hres pi
      hpi hgen data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow
        L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK
          L.P L.table L.WTwist j
    (U.criticalFactor * ∏ j, (R j).criticalFactor) /
      (B.criticalFactor * ∏ j, (T j).criticalFactor) = 1 := by
  dsimp only
  cases t with
  | zero =>
    have hT := L.hT
    omega
  | succ s =>
    let p := Module.finrank F K
    let hchar : residueCharacteristic F = p :=
      residueCharacteristic_eq_degree_of_positive_break F K ht (by omega)
        pi hpi hgen
    letI : CharP (ResidueField F) p := ringChar.of_eq hchar
    have hp2 : p ≠ 2 := by
      intro hp
      dsimp only [p] at hp
      have hodd := L.hodd
      rw [hp] at hodd
      norm_num at hodd
    let N := lowActualNormalization F K ht hres pi hpi hgen data hF L.hLow
      L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.P hepsilon C
    let generator := wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen
      data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P hparity
        C.lower C.lower_ne_one hcharOdd
    let base := wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen
      data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
        L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
          L.table hboundary hparity C.lower C.lower_ne_one hcharOdd
    have hGeneratorEta : generator.eta = N.etaZero := by
      simpa only [generator, N] using
        lowActual_generatorNamedEta_eq_etaZero F K ht hres pi hpi hgen data
          hF L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
            L.P hepsilon hparity C hcharOdd
    have hBaseEta : base.eta = N.eta := by
      simpa only [base, N] using
        lowActual_boundaryBaseNamedEta_eq_eta F K ht hres pi hpi hgen data
          L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table hepsilon hboundary hparity C hcharOdd
    have hDZero : wildOddBoundaryDZero generator base = N.dZero := by
      simpa only [generator, base, N] using
        lowActual_boundaryDZero_eq F K ht hres pi hpi hgen data L.chiK
          L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1
            L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
              hepsilon hboundary hparity C hcharOdd
    have hbaseCoeff :
        (lowSourceBaseCriticalPolarFunction F K ht hres pi hpi hgen data
          L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table p C).affineCoefficient hcharOdd C.lower_ne_one =
          N.eta * base.gamma := by
      change (wildOddCoefficientPair
        (lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
          L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
            L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table) C.lower
              C.lower_ne_one hcharOdd).affine = N.eta * base.gamma
      rw [wildOdd_lowBaseCoefficients F K ht hres pi hpi hgen data L.chiK
        L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1
          L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table C.lower
            C.lower_ne_one hcharOdd
              (wildOdd_lowBoundaryBase_odd (F := F) (K := K) (data := data)
                L.hT hboundary hparity)]
      dsimp only [wildOddBasePair]
      change base.eta * base.gamma = N.eta * base.gamma
      rw [hBaseEta]
    let jOne : OddNormIndex F K := ⟨1, one_ne_zero⟩
    have hnormCoeff :
        CriticalPolarFunction.affineCoefficient hcharOdd C.lower_ne_one
          (lowSourceNormCriticalPolarFunction F K ht hres pi hpi hgen data
            hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P p C jOne) =
          N.etaZero * generator.gamma := by
      have hDelta := wildOdd_lowNormTranslationCoefficient_eq_zero F K ht
        hres pi hpi hgen data hF L.delta L.epsilon1 L.hdelta L.hT
          L.hgammaF L.P L.hodd jOne hparity C.lower C.lower_ne_one
      have hPair := wildOdd_lowSourceNormCoefficients F K ht hres pi hpi
        hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P jOne
          hparity C.lower C.lower_ne_one hcharOdd
      rw [hDelta] at hPair
      change (wildOddCoefficientPair
        (lowSourceNormPhase F K ht hres pi hpi hgen data hF L.delta
          L.epsilon1 L.hdelta L.hT L.hgammaF L.P jOne) C.lower
            C.lower_ne_one hcharOdd).affine = N.etaZero * generator.gamma
      rw [hPair]
      simp only [WildOddCoefficientPair.translateAffine, zero_mul, add_zero,
        wildOddTauPowerPair, jOne, ZMod.val_one, Nat.cast_one, one_mul]
      rw [hGeneratorEta]
    let units : ResidueField F → Kˣ := fun X => lowActualSourceUnit F K ht
      hres pi hpi hgen data hF L.hLow L.delta L.epsilon1 L.hdelta
        L.hepsilon1 L.hT L.hgammaF L.P hepsilon C X
    have hunits := lowActualSourceUnit_coe F K ht hres pi hpi hgen data hF
      L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.P
        hepsilon C
    have hN := lowActualNormalization_eq_boundary F K ht hres pi hpi hgen
      data hF L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT
        L.hgammaF L.P hepsilon hboundary C
    have hPair :
        let upper := lowSourceDisplayedUpstairsCriticalPolarFunction F K ht
          hres pi hpi hgen data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi
            L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
              L.hgammaK L.P L.table p hchar C L.WUp
        upper.upperCoefficientPair C.lower_ne_one hcharOdd =
          wildOddUpperPairBoundary p N.etaZero N.dZero base.gamma
            generator.gamma := by
      dsimp only
      have hbaseCoeff' := hbaseCoeff
      have hnormCoeff' := hnormCoeff
      dsimp only [N] at hbaseCoeff' hnormCoeff' ⊢
      rw [hN] at hbaseCoeff' hnormCoeff' ⊢
      exact wildOdd_actualLowCoefficients_boundary F K ht hres pi hpi hgen
        data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
          L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
            L.table L.WUp L.hodd hepsilon hboundary C hcharOdd base.gamma
              generator.gamma hbaseCoeff' hnormCoeff' units hunits
    have hUpper := lowGreen_upperFactor F K p hchar hres C hcharOdd
      (lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK L.psiK
        hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
          L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp) _ hPair
    have hnonzero : ∀ j : {j : ZMod p // j ≠ 0},
        ((j : ZMod p).val : ResidueField F) +
          wildOddBoundaryDZero generator base ≠ 0 := by
      intro j
      simpa only [p, generator, base] using
        wildOdd_lowBoundaryNumerator_ne_zero F K ht hres pi hpi hgen data
          L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table L.WTwist hboundary j hparity C.lower C.lower_ne_one
                hcharOdd
    let certificate := wildOdd_boundaryAffinePencilCertificate F p hchar C
      generator base hnonzero
    have hUpperScaled :
        (lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK L.psiK
          hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
            L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp
              ).criticalFactor =
          quadraticPhase C.lower
            (base.eta * (wildOddBoundaryA0 F p hchar C generator base) ^ p)
            (base.eta * (wildOddBoundaryB0 F p hchar C generator base) ^ p) := by
      rw [hUpper]
      unfold wildOddUpperPairPhase wildOddUpperPairBoundary
      congr 2
      · rw [certificate.a0_pow, hBaseEta, N.eta_eq]
        unfold wildOddBoundaryRho
        rw [hDZero, inv_pow, inv_inv]
        have hpEq : p - 1 + 1 = p := Nat.sub_add_cancel
          ((Fact.out : p.Prime).one_le)
        have hpow : N.dZero ^ p = N.dZero * N.dZero ^ (p - 1) := by
          calc
            _ = N.dZero ^ (p - 1 + 1) := congrArg _ hpEq.symm
            _ = _ := by rw [pow_succ]; ring
        rw [hpow]
        ring
      · rw [certificate.b0_pow, hBaseEta, N.eta_eq]
        unfold wildOddBoundarySigma wildOddBoundaryTau wildOddBoundaryRho
        field_simp [wildOddBoundaryDZero_ne_zero generator base]
    have hBase := lowGreen_lowerFactor
      (lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
        L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
          L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table) C.lower
            C.lower_ne_one hcharOdd _
              (wildOdd_lowBaseCoefficients F K ht hres pi hpi hgen data
                L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
                  L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK
                    L.P L.table C.lower C.lower_ne_one hcharOdd
                      (wildOdd_lowBoundaryBase_odd (F := F) (K := K)
                        (data := data) L.hT hboundary hparity))
    have hNorm (j : OddNormIndex F K) :
        (lowSourceNormPhase F K ht hres pi hpi hgen data hF L.delta
          L.epsilon1 L.hdelta L.hT L.hgammaF L.P j).criticalFactor =
        let row := (wildOddTauPowerPair generator
          ((j : ZMod p).val : ResidueField F)).translateAffine
            ((lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P
                j hparity).translationCoefficient C.lower C.lower_ne_one)
        quadraticPhase C.lower row.polar row.affine := by
      apply lowGreen_lowerFactor
      simpa only [generator, p] using
        wildOdd_lowSourceNormCoefficients F K ht hres pi hpi hgen data hF
          L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P j hparity C.lower
            C.lower_ne_one hcharOdd
    have hTwist (j : OddNormIndex F K) :
        (lowSourceTwistPhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
          L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
            L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WTwist j
              ).criticalFactor =
        let row := (wildOddBoundaryPair generator base
          ((j : ZMod p).val : ResidueField F)).translateAffine
            ((lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P
                j hparity).translationCoefficient C.lower C.lower_ne_one)
        quadraticPhase C.lower row.polar row.affine := by
      apply lowGreen_lowerFactor
      simpa only [generator, base, p] using
        wildOdd_lowBoundaryTwistCoefficients F K ht hres pi hpi hgen data
          L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table L.WTwist hboundary j hparity C.lower C.lower_ne_one
                hcharOdd
    simp_rw [hNorm, hTwist]
    rw [show
      ((lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK L.psiK
            hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
              L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp
                ).criticalFactor * ∏ j : OddNormIndex F K,
          let row := (wildOddTauPowerPair generator
            ((j : ZMod p).val : ResidueField F)).translateAffine
              ((lowTeichmullerLiteralRepresentativeChange F K ht hres pi
                hpi hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF
                  L.P j hparity).translationCoefficient C.lower
                    C.lower_ne_one)
          quadraticPhase C.lower row.polar row.affine) /
        ((lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
            L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
              L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
                ).criticalFactor * ∏ j : OddNormIndex F K,
          let row := (wildOddBoundaryPair generator base
            ((j : ZMod p).val : ResidueField F)).translateAffine
              ((lowTeichmullerLiteralRepresentativeChange F K ht hres pi
                hpi hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF
                  L.P j hparity).translationCoefficient C.lower
                    C.lower_ne_one)
          quadraticPhase C.lower row.polar row.affine) =
      ((lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK L.psiK
            hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
              L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp
                ).criticalFactor * ∏ j : OddNormIndex F K,
          wildOddLowerPairPhase C.lower (wildOddTauPowerPair generator
            ((j : ZMod p).val : ResidueField F))) /
        ((lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
            L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
              L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
                ).criticalFactor * ∏ j : OddNormIndex F K,
          wildOddLowerPairPhase C.lower (wildOddBoundaryPair generator base
            ((j : ZMod p).val : ResidueField F))) from by
        simpa only [p, wildOddLowerPairPhase] using
          wildOdd_lowBoundaryTranslatedCriticalQuotient_eq_untranslated F K
            ht hres pi hpi hgen data hF L.delta L.epsilon1 L.hdelta L.hT
              L.hgammaF L.P L.hodd hparity C.lower C.lower_ne_one generator
                base
                  (lowSourceUpstairsPhase F K ht hres pi hpi hgen data
                    L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow
                      L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
                        L.hgammaK L.P L.table L.WUp).criticalFactor
                  (lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK
                    L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
                      L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
                        L.hgammaK L.P L.table).criticalFactor]
    rw [hUpperScaled, hBase]
    exact lowGreen_scaledBoundaryQuotient F p hp2 hchar C generator base
      hnonzero

include hF L in
theorem wildOddPreparation_lowProvenanceCriticalQuotient_eq_one
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    (phases.extension.criticalFactor *
        ∏ j : OddNormIndex F K,
          (phases.normCharacter
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd
                (j : ZMod (Module.finrank F K))))).criticalFactor) /
      ((phases.twist 1).criticalFactor *
        ∏ j : OddNormIndex F K,
          (phases.twist
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd
                (j : ZMod (Module.finrank F K))))).criticalFactor) = 1 := by
  rw [L.extensionSource, L.baseSource]
  simp_rw [L.normSource, L.twistSource]
  let U := lowSourceUpstairsPhase F K ht hres pi hpi hgen data L.chiK
    L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta
      L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table L.WUp
  let B := lowSourceBasePhase F K ht hres pi hpi hgen data L.chiK L.psiK hF
    L.hminimal L.hchi L.hpsi L.hLow L.delta L.epsilon1 L.hdelta L.hepsilon1
      L.hT L.hgammaF L.hgammaK L.P L.table
  let R := fun j : OddNormIndex F K => lowSourceNormPhase F K ht hres pi
    hpi hgen data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P j
  let T := fun j : OddNormIndex F K => lowSourceTwistPhase F K ht hres pi
    hpi hgen data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
      L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P L.table
        L.WTwist j
  change (U.criticalFactor * ∏ j, (R j).criticalFactor) /
    (B.criticalFactor * ∏ j, (T j).criticalFactor) = 1
  have hepsilonLe := hF.epsilon_le_one
  have hparityLe := (lowCriticalConductorDecomposition (t := t)
    L.hT).epsilon_le_one
  rcases lt_or_eq_of_le L.hLow with hstrict | hboundary
  · have hrow (j : OddNormIndex F K) :
        (T j).criticalFactor = (R j).criticalFactor := by
      apply LocalLamprechtPhaseData.criticalFactor_eq_of_criticalFunction_eq
      exact lowSourceTwistFunction_eq_norm_of_strict F K ht hres pi hpi
        hgen data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
          L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
            L.table L.WTwist hstrict j
    have hUB : U.criticalFactor = B.criticalFactor := by
      by_cases he : epsilon = 0
      · rw [lowGreen_factor_eq_one U
          (lowSourceUpstairsFunction_eq_one_of_even F K ht hres pi hpi
            hgen data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow
              L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
                L.hgammaK L.P L.table L.WUp he),
          lowGreen_factor_eq_one B
            (lowSourceBaseFunction_eq_one_of_even F K ht hres pi hpi hgen
              data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow
                L.delta L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF
                  L.hgammaK L.P L.table he)]
      · exact lowGreen_strictUpper_eq_base ht hres pi hpi hgen hF L hstrict
          (by omega) C hcharOdd
    simp_rw [hrow]
    rw [hUB]
    apply div_self
    exact mul_ne_zero B.criticalFactor_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun j _ => (R j).criticalFactor_ne_zero)
  · have hmatch : epsilon = lowCriticalParity t := by
      have hcf := hF.conductor_eq
      have hcl := (lowCriticalConductorDecomposition (t := t)
        L.hT).conductor_eq
      omega
    by_cases he : epsilon = 0
    · have hp : lowCriticalParity t = 0 := hmatch ▸ he
      have hU := lowGreen_factor_eq_one U
        (lowSourceUpstairsFunction_eq_one_of_even F K ht hres pi hpi hgen
          data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table L.WUp he)
      have hB := lowGreen_factor_eq_one B
        (lowSourceBaseFunction_eq_one_of_even F K ht hres pi hpi hgen data
          L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
            L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
              L.table he)
      have hR (j : OddNormIndex F K) : (R j).criticalFactor = 1 :=
        lowGreen_factor_eq_one (R j)
          (lowSourceNormFunction_eq_one_of_even F K ht hres pi hpi hgen
            data hF L.delta L.epsilon1 L.hdelta L.hT L.hgammaF L.P hp j)
      have hT (j : OddNormIndex F K) : (T j).criticalFactor = 1 :=
        lowGreen_factor_eq_one (T j)
          (lowSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen
            data L.chiK L.psiK hF L.hminimal L.hchi L.hpsi L.hLow L.delta
              L.epsilon1 L.hdelta L.hepsilon1 L.hT L.hgammaF L.hgammaK L.P
                L.table L.WTwist hp j)
      rw [hU, hB]
      simp_rw [hR, hT]
      norm_num
    · exact lowGreen_boundaryQuotient ht hres pi hpi hgen hF L hboundary
        (by omega) (by omega) C hcharOdd

private theorem wildOddPreparation_highProvenanceCriticalQuotient_eq_one
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [CharP (ResidueField F) (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    {data : FirstMainComputationalData F K globalChi globalPsi}
    {phases : FirstMainPhaseData F K globalChi globalPsi data}
    {d epsilon : ℕ}
    {hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon}
    (H : WildOddHighPhaseProvenance F K ht hres pi hpi hgen data phases hF)
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hcharOdd : ringChar (ResidueField F) ≠ 2) :
    ((phases.extension.criticalFactor *
          ∏ j : OddNormIndex F K,
            (phases.normCharacter
              (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
                (Multiplicative.ofAdd
                  (j : ZMod (Module.finrank F K))))).criticalFactor) /
        ((phases.twist 1).criticalFactor *
          ∏ j : OddNormIndex F K,
            (phases.twist
              (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
                (Multiplicative.ofAdd
                  (j : ZMod (Module.finrank F K))))).criticalFactor)) = 1 := by
  rw [H.extensionSource,
    ← ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen]
  simp_rw [H.normSource, H.twistSource]
  cases t with
  | zero =>
      have htpos := H.htpos
      omega
  | succ s =>
      exact wildOddPreparation_strictHigh_sourceCriticalQuotient_eq_one F K
        ht hres pi hpi hgen data H.chiK H.psiK hF H.hK H.hminimal H.hchi
          H.hpsi H.hodd H.htpos H.hstrict H.hupper H.gammaF H.hgammaF
            H.source C hcharOdd

/-- Prepare the source-faithful residual phase package for the nonstable
Wild odd-prime case, stopping before correction linearization and assembly. -/
noncomputable def wildOddPhasePreparation
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (t : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hodd : residueCharacteristic F ≠ 2)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : 1 < chiF.conductor)
    (hnonstable : chiF.conductor / 2 < t + 1) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : CharP (ResidueField F) (Module.finrank F K) :=
      ringChar.of_eq
        (residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi
          hpi hgen)
    WildOddPhasePrepared F K t ht hres pi hpi hgen chiF psiF := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_break F K ht htpos pi hpi
      hgen
  letI : CharP (ResidueField F) (Module.finrank F K) := ringChar.of_eq hchar
  let Q := wildOddPreparationCore ht htpos hodd hres pi hpi hgen chiF psiF
    hminimal hm hnonstable
  have hcharOdd : ringChar (ResidueField F) ≠ 2 := by
    simpa only [ringChar.eq] using hodd
  have hp2 : Module.finrank F K ≠ 2 := by
    rw [Q.degree_eq]
    exact hodd
  have hsource :
      Q.phases.criticalNumerator / Q.phases.criticalDenominator = 1 := by
    rw [wildOddPreparation_rawCritical_eq_indexedQuotient F K ht hres pi hpi
      hgen Q.phases]
    cases Q.branch with
    | high H =>
        exact wildOddPreparation_highProvenanceCriticalQuotient_eq_one ht
          hres pi hpi hgen H Q.residualAddChar hcharOdd
    | low L =>
        exact wildOddPreparation_lowProvenanceCriticalQuotient_eq_one ht
          hres pi hpi hgen Q.dataConductorDecomposition L Q.residualAddChar
            hcharOdd
  have hclean := wildOdd_completeResidualPhaseQuotient_eq_one F
    (Module.finrank F K) hp2 Q.degree_eq.symm Q.residualAddChar Q.parity
  exact
    { d := Q.d
      epsilon := Q.epsilon
      conductorDecomposition := Q.conductorDecomposition
      nonstable := Q.nonstable
      degree_eq := Q.degree_eq
      odd_degree := Q.odd_degree
      data := Q.data
      data_twist_one := Q.data_twist_one
      data_baseAddChar := Q.data_baseAddChar
      dataConductorDecomposition := Q.dataConductorDecomposition
      phases := Q.phases
      branch := Q.branch
      residualAddChar := Q.residualAddChar
      parity := Q.parity
      rawResidualPhase_eq := hsource.trans hclean.symm }

end

end

end LanglandsFirstMainLemma
