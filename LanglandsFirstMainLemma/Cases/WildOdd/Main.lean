import LanglandsFirstMainLemma.Cases.WildEndpoints
import LanglandsFirstMainLemma.Cases.WildOdd.ParityReduction
import LanglandsFirstMainLemma.Cases.WildOdd.CorrectionValuation
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

local instance wildOddMain_residuePrimeFact
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Fact (residueCharacteristic F).Prime :=
  ⟨residueCharacteristic_prime F⟩

local instance wildOddMain_degreeNeZero
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] : NeZero (Module.finrank F K) :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

/-- Higher-conductor data passed from the completed parameter, residual,
and correction nodes to the final wild odd-prime assembly. -/
structure WildOddNonstableHigherData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    (t : ℕ)
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) where
  d : ℕ
  epsilon : ℕ
  conductorDecomposition :
    IsStationaryConductorDecomposition chiF.conductor d epsilon
  nonstable : d < t + 1
  data : FirstMainComputationalData F K chiF.character psiF.character
  phases : FirstMainPhaseData F K chiF.character psiF.character data
  assembly : ExactOddPhaseAssembly F K chiF.character psiF.character
    data phases (t := t) (m := chiF.conductor) (OddNormIndex F K)
  residualAddChar :
    FrobeniusResidualAddCharData F (residueCharacteristic F)
  parity : WildOddParityReductionData F (residueCharacteristic F)
  residualPhase_eq : assembly.residualPhase =
    wildOddCompleteResidualPhaseQuotient F (residueCharacteristic F) rfl
      residualAddChar parity
  correction : WildOddCorrectionData F K (t + 1)
  correction_conductor : correction.m = chiF.conductor
  correction_element : correction.u = assembly.u
  correctionCoordinate : assembly.X = wildOddCorrectionX correction
  linearizationDepth : ℕ
  linearizationDepth_pos : 0 < linearizationDepth
  linearizationDepth_le : linearizationDepth ≤ t + 1
  tau : NormCharacter F K
  tau_ne_one : tau ≠ 1
  tauLinearization : ∀ x : lattice F (linearizationDepth : ℤ),
    (wildNormCharacterData F K ht hres piK hpiK hgen tau).character
        (positiveUnitOfLattice F linearizationDepth_pos x) =
      psiF.character (assembly.A * (x : F))

private def wildOddEndpointZeroComputationalData
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F) :
    FirstMainComputationalData F K chiF.character psiF.character where
  baseAddChar := psiF
  baseAddChar_character := rfl
  extensionQuasiChar :=
    wildNormPullbackData F K ht hres piK hpiK hgen chiF (by omega)
  extensionQuasiChar_character := rfl
  extensionAddChar := wildTracePullbackData F K ht hres piK hpiK hgen psiF
  extensionAddChar_character := rfl
  normCharacterData := wildNormCharacterData F K ht hres piK hpiK hgen
  normCharacterData_character :=
    wildNormCharacterData_character F K ht hres piK hpiK hgen
  twistData :=
    wildEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF
  twistData_character :=
    wildEndpointZeroTwistData_character F K ht hres piK hpiK hgen chiF hchiF

private def wildOddEndpointOneComputationalData
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htwild : 0 < t) (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F) :
    FirstMainComputationalData F K chiF.character psiF.character where
  baseAddChar := psiF
  baseAddChar_character := rfl
  extensionQuasiChar :=
    endpointIntrinsicNormData F K ht hres piK hpiK hgen chiF hchiF htwild
  extensionQuasiChar_character := rfl
  extensionAddChar := endpointIntrinsicTraceData F K ht hres piK hpiK hgen psiF
  extensionAddChar_character := rfl
  normCharacterData := wildNormCharacterData F K ht hres piK hpiK hgen
  normCharacterData_character :=
    wildNormCharacterData_character F K ht hres piK hpiK hgen
  twistData :=
    wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen chiF hchiF
  twistData_character :=
    wildEndpointOneTwistData_character F K ht htwild hres piK hpiK hgen
      chiF hchiF

private def firstMainComputationalData_untwist
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    (nu : NormCharacter F K) (chiF : ContinuousQuasiChar F)
    (psiF : ContinuousAddChar F)
    (data : FirstMainComputationalData F K (nu.1 * chiF) psiF) :
    FirstMainComputationalData F K chiF psiF where
  baseAddChar := data.baseAddChar
  baseAddChar_character := data.baseAddChar_character
  extensionQuasiChar := data.extensionQuasiChar
  extensionQuasiChar_character := by
    rw [data.extensionQuasiChar_character,
      normQuasiChar_normCharacter_mul F K]
  extensionAddChar := data.extensionAddChar
  extensionAddChar_character := data.extensionAddChar_character
  normCharacterData := data.normCharacterData
  normCharacterData_character := data.normCharacterData_character
  twistData := fun mu ↦ data.twistData (mu * nu⁻¹)
  twistData_character := by
    intro mu
    rw [data.twistData_character]
    ext x
    simp only [NormCharacter.coe_mul, NormCharacter.coe_inv,
      ContinuousQuasiChar.mul_apply]
    simp [mul_assoc]

private theorem firstMain_wildEndpoint_zero_of_isDeltaFinite_wildOdd
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htwild : 0 < t) (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (DeltaF : LocalConstantFunction F) (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let piKU : Kˣ := wildUpperUniformizer K piK hpiK
  let piF : Fˣ := wildLowerUniformizer F K piK hpiK
  let hpiKU : (ValuativeRel.valuation K).IsUniformizer (piKU : K) := by
    simpa [piKU, wildUpperUniformizer] using hpiK
  let hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) :=
    wildLowerUniformizer_isUniformizer F K hres piK hpiK
  let chiK := wildNormPullbackData F K ht hres piK hpiK hgen chiF (by omega)
  let psiK := wildTracePullbackData F K ht hres piK hpiK hgen psiF
  let normData : NormCharacter F K → LocalQuasiCharData F :=
    wildNormCharacterData F K ht hres piK hpiK hgen
  let twistData : NormCharacter F K → LocalQuasiCharData F :=
    wildEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF
  unfold FirstMainIdentity firstMainLeftSide firstMainRightSide
  rw [show normQuasiChar F K chiF.character = chiK.character by rfl,
    show tracePullbackAddChar F K psiF.character = psiK.character by rfl]
  simp_rw [← wildEndpointZeroTwistData_character F K ht hres piK hpiK hgen
    chiF hchiF]
  simp_rw [← wildNormCharacterData_character F K ht hres piK hpiK hgen]
  calc
    DeltaK chiK.character psiK.character *
          ∏ mu : NormCharacter F K, DeltaF (normData mu).character psiF.character =
        deltaFinite chiK psiK
            (uniformizerAdmissibleGamma K chiK psiK piKU hpiKU) *
          ∏ mu : NormCharacter F K,
            deltaFinite (normData mu) psiF
              (uniformizerAdmissibleGamma F (normData mu) psiF piF hpiF) := by
      rw [hDeltaK chiK psiK
        (uniformizerAdmissibleGamma K chiK psiK piKU hpiKU)]
      congr 1
      apply Finset.prod_congr rfl
      intro mu _
      exact hDeltaF (normData mu) psiF
        (uniformizerAdmissibleGamma F (normData mu) psiF piF hpiF)
    _ = ∏ mu : NormCharacter F K,
          deltaFinite (twistData mu) psiF
            (uniformizerAdmissibleGamma F (twistData mu) psiF piF hpiF) := by
      simpa only [endpointDelta, piKU, piF, hpiKU, hpiF, chiK, psiK,
        normData, twistData, ramifiedNormCharacterFinset,
        normCharacterFinset] using
        firstMain_wildEndpoint_zero F K ht htwild hres piK hpiK hgen
          chiF hchiF psiF
    _ = ∏ mu : NormCharacter F K,
          DeltaF (twistData mu).character psiF.character := by
      apply Finset.prod_congr rfl
      intro mu _
      exact (hDeltaF (twistData mu) psiF
        (uniformizerAdmissibleGamma F (twistData mu) psiF piF hpiF)).symm

private theorem firstMain_wildEndpoint_one_of_isDeltaFinite_wildOdd
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (DeltaF : LocalConstantFunction F) (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    FirstMainIdentity F K DeltaF DeltaK chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let hspos : 0 < s + 1 := by omega
  let piF := wildLowerUniformizer F K piK hpiK
  let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
  let gamma0 := endpointOneInitialAdmissibleGamma F chiF psiF
  let gammaF := endpointNormalizedAdmissibleGamma F chiF hchiF psiF gamma0
  let chiK := endpointIntrinsicNormData F K ht hres piK hpiK hgen
    chiF hchiF hspos
  let psiK := endpointIntrinsicTraceData F K ht hres piK hpiK hgen psiF
  let gammaK := endpointNormalizedDerivativeGamma
    F K ht hspos hres piK hpiK hgen chiF hchiF psiF gamma0
  let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
    F piF hpiF chiF hchiF psiF gammaF
  let gammaNorm := endpointOneGammaNorm F K ht hres piK hpiK hgen
    piF hpiF psiF normalizedGammaF
  let normData : NormCharacter F K → LocalQuasiCharData F :=
    wildNormCharacterData F K ht hres piK hpiK hgen
  let twistData : NormCharacter F K → LocalQuasiCharData F :=
    wildEndpointOneTwistData F K ht hspos hres piK hpiK hgen chiF hchiF
  let twistGamma : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (twistData mu) psiF := fun mu ↦
    wildEndpointOneTwistGamma F K ht hspos hres piK hpiK hgen
      chiF hchiF psiF gammaF gammaNorm mu
  unfold FirstMainIdentity firstMainLeftSide firstMainRightSide
  rw [show normQuasiChar F K chiF.character = chiK.character by rfl,
    show tracePullbackAddChar F K psiF.character = psiK.character by rfl]
  simp_rw [← wildEndpointOneTwistData_character F K ht hspos hres piK hpiK hgen
    chiF hchiF]
  simp_rw [← wildNormCharacterData_character F K ht hres piK hpiK hgen]
  calc
    DeltaK chiK.character psiK.character *
          ∏ mu : NormCharacter F K, DeltaF (normData mu).character psiF.character =
        deltaFinite chiK psiK gammaK *
          ∏ mu : NormCharacter F K, deltaFinite (normData mu) psiF (gammaNorm mu) := by
      rw [hDeltaK chiK psiK gammaK]
      congr 1
      apply Finset.prod_congr rfl
      intro mu _
      exact hDeltaF (normData mu) psiF (gammaNorm mu)
    _ = ∏ mu : NormCharacter F K,
          deltaFinite (twistData mu) psiF (twistGamma mu) := by
      simpa only [gamma0, hspos, piF, hpiF, gammaF, chiK, psiK, gammaK,
        normalizedGammaF, gammaNorm, normData, twistData, twistGamma,
        ramifiedNormCharacterFinset, normCharacterFinset] using
        firstMain_wildEndpoint_one F K ht hres piK hpiK hgen chiF hchiF psiF
    _ = ∏ mu : NormCharacter F K,
          DeltaF (twistData mu).character psiF.character := by
      apply Finset.prod_congr rfl
      intro mu _
      exact (hDeltaF (twistData mu) psiF (twistGamma mu)).symm

/-- **First Main Lemma, wild odd-prime non-stable range.**

The character is reduced to the least-conductor member of its complete
norm-character orbit. Conductors zero and one are discharged by the endpoint
theorems. At higher conductor, `PhaseReductionResult` gives the exact complete
error decomposition; `wildOdd_parityReduction` makes its residual quotient
one, and `wildOdd_correction_phase` makes its norm--trace phase one. The
proved error-term twist invariance then transports the result back to the
original character. -/
theorem firstMain_wildOdd_nonstable
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htwild : 0 < t)
    (hdegree : Module.finrank F K = residueCharacteristic F)
    (hodd : residueCharacteristic F ≠ 2)
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (DeltaF : LocalConstantFunction F) (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
    ∀ (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F),
      (1 < (minimalOrbitRepresentative F K ht hres piK hpiK hgen chiF).conductor →
        WildOddNonstableHigherData F K t ht hres piK hpiK hgen
          (minimalOrbitRepresentative F K ht hres piK hpiK hgen chiF) psiF) →
      FirstMainIdentity F K DeltaF DeltaK chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  have _hoddDegree : Module.finrank F K ≠ 2 := by omega
  intro chiF psiF higher
  let chiMin := minimalOrbitRepresentative F K ht hres piK hpiK hgen chiF
  have hmin : ∃ data : FirstMainComputationalData F K
      chiMin.character psiF.character,
      errorTerm F K DeltaF DeltaK chiMin.character psiF.character = 1 := by
    by_cases hzero : chiMin.conductor = 0
    · let data := wildOddEndpointZeroComputationalData
        F K ht hres piK hpiK hgen chiMin hzero psiF
      refine ⟨data, (errorTerm_eq_one_iff_firstMainIdentity
        F K hDeltaF chiMin.character psiF.character data).2 ?_⟩
      exact firstMain_wildEndpoint_zero_of_isDeltaFinite_wildOdd
        F K ht htwild hres piK hpiK hgen DeltaF DeltaK hDeltaF hDeltaK
          chiMin hzero psiF
    · by_cases hone : chiMin.conductor = 1
      · cases t with
        | zero => omega
        | succ s =>
            let data := wildOddEndpointOneComputationalData
              F K ht htwild hres piK hpiK hgen chiMin hone psiF
            refine ⟨data, (errorTerm_eq_one_iff_firstMainIdentity
              F K hDeltaF chiMin.character psiF.character data).2 ?_⟩
            exact firstMain_wildEndpoint_one_of_isDeltaFinite_wildOdd
              F K ht hres piK hpiK hgen DeltaF DeltaK hDeltaF hDeltaK
                chiMin hone psiF
      · have hm : 1 < chiMin.conductor := by omega
        let H := higher hm
        have hresidual : H.assembly.residualPhase = 1 := by
          rw [H.residualPhase_eq]
          exact wildOdd_parityReduction.complete F (residueCharacteristic F)
            hodd rfl H.residualAddChar H.parity
        have hcorrectionUnits := wildOdd_correction_phase H.correction
          H.linearizationDepth_pos H.linearizationDepth_le
          (wildNormCharacterData F K ht hres piK hpiK hgen H.tau)
          (wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
            H.tau H.tau_ne_one)
          psiF.character H.assembly.A H.tauLinearization
        have hcorrection :
            (psiF.character (-H.assembly.A * H.assembly.X) : ℂ) = 1 := by
          rw [H.correctionCoordinate]
          exact congrArg (Units.val : ℂˣ → ℂ) hcorrectionUnits
        have hphase := PhaseReductionResult.exactAssemblies.oddResult
          hDeltaF hDeltaK H.assembly
        refine ⟨H.data, ?_⟩
        rw [hphase.normTraceAssembly, hresidual, hcorrection, one_mul]
  obtain ⟨minData, hminError⟩ := hmin
  have horiginalError :
      errorTerm F K DeltaF DeltaK chiF.character psiF.character = 1 := by
    calc
      errorTerm F K DeltaF DeltaK chiF.character psiF.character =
          errorTerm F K DeltaF DeltaK chiMin.character psiF.character :=
        (errorTerm_minimalOrbitRepresentative F K ht hres piK hpiK hgen
          DeltaF DeltaK chiF psiF.character).symm
      _ = 1 := hminError
  obtain ⟨nu, hnu⟩ := minimalOrbitRepresentative_mem_orbit
    F K ht hres piK hpiK hgen chiF
  have minData' : FirstMainComputationalData F K
      (nu.1 * chiF.character) psiF.character := by
    simpa only [chiMin, hnu] using minData
  let originalData := firstMainComputationalData_untwist
    F K nu chiF.character psiF.character minData'
  exact (errorTerm_eq_one_iff_firstMainIdentity F K hDeltaF
    chiF.character psiF.character originalData).1 horiginalError

end

end LanglandsFirstMainLemma
