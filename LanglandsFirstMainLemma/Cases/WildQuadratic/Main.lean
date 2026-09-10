import LanglandsFirstMainLemma.Cases.WildQuadratic.NonBoundary
import LanglandsFirstMainLemma.Cases.WildQuadratic.Boundary
import LanglandsFirstMainLemma.Cases.WildEndpoints
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section HigherData

variable (F K : Type)
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

/-- Higher-conductor data shared by the q-free and refined branches. -/
structure WildQuadraticCommonHigherData
    (t : ℕ) (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (view : WildQuadraticCommonCoefficientView F K t chiF.conductor) where
  chiFData_eq : view.chiFData = chiF
  psiF_eq : view.psiF = psiF
  data : FirstMainComputationalData F K view.chiFData.character
    view.psiF.character
  phaseData : FirstMainPhaseData F K view.chiFData.character
    view.psiF.character data
  assembly : ExactQuadraticPhaseAssembly F K view.chiFData.character
    view.psiF.character data phaseData (t := t) (m := chiF.conductor)
  coordinates : WildQuadraticCommonCoordinateCompatibility view data phaseData
    assembly

/-- Exact higher-conductor inputs, split so the three all-even rows contain
no refinement while every refined row carries a normalization of an actual
retained positive-polar source. -/
inductive WildQuadraticHigherData
    (t : ℕ) (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) : Type
  | allEven
      (view : WildQuadraticAllEvenCoefficientView F K t chiF.conductor)
      (common : WildQuadraticCommonHigherData F K t chiF psiF view.toCommon)
      (rows : WildQuadraticAllEvenPhaseRowCompatibility view common.data
        common.phaseData common.assembly)
      (completeCorrection : common.assembly.CompleteCorrectionData)
  | refined
      (q : CharTwoRefinement (ResidueField F))
      (view : WildQuadraticCoefficientView F K q t chiF.conductor)
      (provenance : WildQuadraticNormalizedRefinementSource
        F view.criticalInputs q)
      (common : WildQuadraticCommonHigherData F K t chiF psiF view.toCommon)
      (rows : WildQuadraticPhaseRowCompatibility view common.data
        common.phaseData common.assembly)
      (refinements : WildQuadraticRefinementAssembly view common.data
        common.phaseData common.assembly
          (WildQuadraticCoordinateCompatibility.ofCommon common.coordinates))
      (mixedBoundary : (2 : F) ≠ 0 →
        (view.coefficients.1).row = .boundaryOdd →
          ∃ (boundary : WildQuadraticBoundaryData (ResidueField F))
            (chiCorrection : WildQuadraticRefinementCorrection F
              (ResidueField F) view.psiF view.chiFData q)
            (tauCorrection : WildQuadraticRefinementCorrection F
              (ResidueField F) view.psiF view.tauData q),
            WildQuadraticBoundaryCompatibility
                (V := view) (A := common.assembly) boundary ∧
              refinements.chiCorrection = some chiCorrection ∧
              refinements.tauCorrection = some tauCorrection)

end HigherData

private theorem firstMain_wildEndpoint_zero_of_isDeltaFinite
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
          ∏ mu : NormCharacter F K,
            DeltaF (normData mu).character psiF.character =
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

private theorem firstMain_wildEndpoint_one_of_isDeltaFinite
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
          ∏ mu : NormCharacter F K,
            DeltaF (normData mu).character psiF.character =
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

/-- **First Main Lemma, wildly ramified quadratic case.**

The original character is first replaced by the proved least-conductor
member of its complete norm-character orbit.  Conductors zero and one are
sent to the endpoint product theorems, before any stationary data are
requested.  At higher conductor the ten coefficient rows split disjointly
into the nine nonboundary rows and the exceptional odd boundary.  The latter
is impossible in equal characteristic two by lower-break parity; in mixed
characteristic it is discharged by the completed boundary theorem.

The conclusion is the literal `FirstMainIdentity`, and twist invariance of
both complete products transports it back from the selected minimal
representative to the original character. -/
theorem firstMain_wildQuadratic
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htwild : 0 < t) (hdegree : Module.finrank F K = 2)
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
        WildQuadraticHigherData F K t
          (minimalOrbitRepresentative F K ht hres piK hpiK hgen chiF) psiF) →
      FirstMainIdentity F K DeltaF DeltaK chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  intro chiF psiF higher
  let chiMin := minimalOrbitRepresentative F K ht hres piK hpiK hgen chiF
  have hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiMin :=
    minimalOrbitRepresentative_isMinimal F K ht hres piK hpiK hgen chiF
  have hminIdentity :
      FirstMainIdentity F K DeltaF DeltaK chiMin.character psiF.character := by
    by_cases hzero : chiMin.conductor = 0
    · exact firstMain_wildEndpoint_zero_of_isDeltaFinite
        F K ht htwild hres piK hpiK hgen DeltaF DeltaK hDeltaF hDeltaK
          chiMin hzero psiF
    · by_cases hone : chiMin.conductor = 1
      · cases t with
        | zero => omega
        | succ s =>
            exact firstMain_wildEndpoint_one_of_isDeltaFinite
              F K ht hres piK hpiK hgen DeltaF DeltaK hDeltaF hDeltaK
                chiMin hone psiF
      · have hm : 1 < chiMin.conductor := by omega
        let H := higher hm
        cases H with
        | allEven view common rows completeCorrection =>
            have hminimalV :
                IsMinimalNormCharacterOrbitRepresentative F K
                  view.chiFData := by
              simpa only [common.chiFData_eq] using hminimal
            have hV : errorTerm F K DeltaF DeltaK view.chiFData.character
                view.psiF.character = 1 :=
              wildQuadratic_nonboundary_allEven (commonAssembly :=
                  common.assembly) ht hres piK hpiK hgen hDeltaF hDeltaK rows
                common.coordinates completeCorrection hminimalV
            have hVIdentity : FirstMainIdentity F K DeltaF DeltaK
                view.chiFData.character view.psiF.character :=
              (errorTerm_eq_one_iff_firstMainIdentity F K hDeltaF
                view.chiFData.character view.psiF.character common.data).1 hV
            simpa only [common.chiFData_eq, common.psiF_eq] using hVIdentity
        | refined q view provenance common rows refinements mixedBoundary =>
            let coordinates :=
              WildQuadraticCoordinateCompatibility.ofCommon common.coordinates
            have hchiFData_eq : view.chiFData = chiMin := by
              simpa only [WildQuadraticCoefficientView.toCommon] using
                common.chiFData_eq
            have hpsiF_eq : view.psiF = psiF := by
              simpa only [WildQuadraticCoefficientView.toCommon] using
                common.psiF_eq
            have hminimalV :
                IsMinimalNormCharacterOrbitRepresentative F K
                  view.chiFData := by
              simpa only [hchiFData_eq] using hminimal
            have hV : errorTerm F K DeltaF DeltaK view.chiFData.character
                view.psiF.character = 1 := by
              by_cases hrow : (view.coefficients.1).row = .boundaryOdd
              · by_cases hEqual : (2 : F) = 0
                · letI : CharP F 2 :=
                    (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 hEqual
                  have hTParity :
                      WildQuadraticConductorParity.ofConductor
                        (t + 1) = .odd := by
                    rw [← WildQuadraticCoefficientRow.ofConductors_TParity
                        (chiMin.conductor - 1) t,
                      ← view.coefficients.2, hrow]
                    rfl
                  have hTOdd : Odd (t + 1) :=
                    (WildQuadraticConductorParity.ofConductor_eq_odd_iff
                      (t + 1)).mp hTParity
                  have htOdd : Odd t :=
                    quadraticBreak_odd_equalCharacteristic
                      F K hdegree hres t ht.1 ht.2
                  exact ((Nat.odd_add_one.mp hTOdd) htOdd).elim
                · obtain ⟨boundary, chiCorrection, tauCorrection,
                      compatibility, hchi, htau⟩ :=
                    mixedBoundary hEqual hrow
                  let formula := wildQuadratic_errorFormula hDeltaF hDeltaK
                    rows coordinates refinements
                  exact wildQuadratic_boundary (A := common.assembly) ht
                    formula boundary chiCorrection tauCorrection compatibility
                      hchi htau
              · exact wildQuadratic_nonboundary (A := common.assembly)
                  ht hres piK hpiK hgen hDeltaF hDeltaK rows coordinates
                    refinements hminimalV hrow
            have hVIdentity : FirstMainIdentity F K DeltaF DeltaK
                view.chiFData.character view.psiF.character :=
              (errorTerm_eq_one_iff_firstMainIdentity F K hDeltaF
                view.chiFData.character view.psiF.character common.data).1 hV
            simpa only [hchiFData_eq, hpsiF_eq] using hVIdentity
  obtain ⟨mu, hmu⟩ := minimalOrbitRepresentative_mem_orbit
    F K ht hres piK hpiK hgen chiF
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

end

end LanglandsFirstMainLemma
