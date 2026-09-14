import LanglandsFirstMainLemma.Cases.WildEndpoints.One.StationaryReciprocity

/-!
# Final conductor-one sign and product assembly
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section NormalizedGammaFromAdmissible

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Remove the unique conductor-one uniformizer from an admissible
denominator.  The result has exact order equal to the additive conductor. -/
def endpointOneNormalizedGammaOfAdmissible
    (piF : Fˣ)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) :
    EndpointOneNormalizedGamma F psi :=
  ⟨(gamma : Fˣ) / piF, by
    rw [Units.val_div_eq_div_val, ord_div, gamma.property,
      ord_uniformizer F hpiF, hchi]
    norm_cast
    omega⟩

@[simp] theorem endpointOneNormalizedGammaOfAdmissible_coe
    (piF : Fˣ)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) :
    (endpointOneNormalizedGammaOfAdmissible
      F piF hpiF chi hchi psi gamma : Fˣ) = (gamma : Fˣ) / piF :=
  rfl

theorem endpointOneNormalizedGammaOfAdmissible_order
    (piF : Fˣ)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) :
    ord F
        ((endpointOneNormalizedGammaOfAdmissible
          F piF hpiF chi hchi psi gamma : Fˣ) : F) =
      ((psi.conductor : ℤ) : WithTop ℤ) :=
  (endpointOneNormalizedGammaOfAdmissible
    F piF hpiF chi hchi psi gamma).property

theorem endpointOneNormalizedGammaOfAdmissible_recovery
    (piF : Fˣ)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) :
    piF * (endpointOneNormalizedGammaOfAdmissible
      F piF hpiF chi hchi psi gamma : Fˣ) = (gamma : Fˣ) := by
  simp [endpointOneNormalizedGammaOfAdmissible]

theorem endpointOneGammaF_normalized_recover
    (piF : Fˣ)
    (hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F))
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) :
    endpointOneGammaF F piF hpiF chi hchi psi
        (endpointOneNormalizedGammaOfAdmissible
          F piF hpiF chi hchi psi gamma) = gamma := by
  apply Subtype.ext
  exact endpointOneNormalizedGammaOfAdmissible_recovery
    F piF hpiF chi hchi psi gamma

end NormalizedGammaFromAdmissible

section FinalEndpointOneProduct

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
variable {s : ℕ} (hs : PrimeCyclicExtension.IsLowerBreak F K s)
  (hspos : 0 < s) (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

local notation "p" => Module.finrank F K

local instance finalSetupDegreeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance finalSetupDegreeNeZero : NeZero p :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

/-- Canonical conductor-one endpoint assembly.  All denominator, parity,
stationary-representative, and norm-character choices are fixed internally.
The sole endpoint-specific input is the manuscript's signed discriminant
congruence, in the exact quotient direction used by the product bridge. -/
theorem wildEndpointOne_finalProduct_of_signCongruence
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi)
    (hsign :
      let piF := wildLowerUniformizer F K piK hpiK
      let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
      let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
      let gammaK := endpointNormalizedDerivativeGamma
        F K hs hspos hres piK hpiK hgen chi hchi psi gamma0
      let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
        F piF hpiF chi hchi psi gammaF
      let gammaTau := endpointOneGammaTau
        F K hs hres piK hpiK hgen piF hpiF psi normalizedGammaF
      let bTau := endpointOneBTau F K hs hspos hres piK hpiK hgen
        piF hpiF psi normalizedGammaF
      let hbTau : (bTau : F) ≠ 0 := endpointOneBTau_ne_zero
        F K hs hspos hres piK hpiK hgen piF hpiF psi normalizedGammaF
      (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) /
          (((-1 : Fˣ) ^ p) *
            ((gammaTau : Fˣ) / Units.mk0 (bTau : F) hbTau) ^ (p - 1)) ∈
        unitFiltration F 1) :
    let piF := wildLowerUniformizer F K piK hpiK
    let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
    let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
    let chiK := endpointIntrinsicNormData F K hs hres piK hpiK hgen
      chi hchi hspos
    let psiK := endpointIntrinsicTraceData F K hs hres piK hpiK hgen psi
    let gammaK := endpointNormalizedDerivativeGamma
      F K hs hspos hres piK hpiK hgen chi hchi psi gamma0
    let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
      F piF hpiF chi hchi psi gammaF
    let gammaNorm := endpointOneGammaNorm F K hs hres piK hpiK hgen
      piF hpiF psi normalizedGammaF
    deltaFinite chiK psiK gammaK *
        (ramifiedNormCharacterFinset F K hs hres piK hpiK hgen).prod
          (fun mu => deltaFinite
            (wildNormCharacterData F K hs hres piK hpiK hgen mu)
            psi (gammaNorm mu)) =
      (ramifiedNormCharacterFinset F K hs hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (wildEndpointOneTwistData F K hs hspos hres piK hpiK hgen
            chi hchi mu) psi
          (wildEndpointOneTwistGamma F K hs hspos hres piK hpiK hgen
            chi hchi psi gammaF gammaNorm mu)) := by
  dsimp only
  let piF := wildLowerUniformizer F K piK hpiK
  let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
  let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
  let chiK := endpointIntrinsicNormData F K hs hres piK hpiK hgen
    chi hchi hspos
  let psiK := endpointIntrinsicTraceData F K hs hres piK hpiK hgen psi
  let gammaK := endpointNormalizedDerivativeGamma
    F K hs hspos hres piK hpiK hgen chi hchi psi gamma0
  let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
    F piF hpiF chi hchi psi gammaF
  let gammaTau := endpointOneGammaTau
    F K hs hres piK hpiK hgen piF hpiF psi normalizedGammaF
  let bTau := endpointOneBTau F K hs hspos hres piK hpiK hgen
    piF hpiF psi normalizedGammaF
  let hbTau : (bTau : F) ≠ 0 := endpointOneBTau_ne_zero
    F K hs hspos hres piK hpiK hgen piF hpiF psi normalizedGammaF
  let gammaNorm := endpointOneGammaNorm F K hs hres piK hpiK hgen
    piF hpiF psi normalizedGammaF
  have hupper :
      deltaFinite chiK psiK gammaK =
        (chi.character
          (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) *
          deltaFinite chi psi gammaF := by
    simpa only [chiK, psiK, gammaF, gammaK] using
      (wildEndpointOne_upperRatio_normalized
        F K hs hspos hres piK hpiK hgen chi hchi psi gamma0)
  have hdiscriminant := endpointNormCharacterDiscriminantBridge
    F K hs hres piK hpiK hgen hspos (gammaTau : Fˣ) (bTau : F)
      hbTau (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) (by
        simpa only [piF, hpiF, gammaF, gammaK, normalizedGammaF,
          gammaTau, bTau, hbTau] using hsign)
  exact wildEndpointOne_productAssembly_explicit
    F K hs hspos hres piK hpiK hgen chi hchi chiK psi psiK
      gammaF gammaK gammaNorm
      (endpointOneDepth s) (endpointOneParity s)
      (endpointOneParity_le_one (s := s))
      (endpointOne_conductor_decomposition (s := s))
      (gammaTau : Fˣ) gammaTau.property bTau
      (endpointOneBTau_bridgeSpec F K hs hspos hres piK hpiK hgen
        piF hpiF psi normalizedGammaF)
      hbTau hupper hdiscriminant

end FinalEndpointOneProduct
section FinalEndpointOneUnconditional

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
variable {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

local notation "p" => Module.finrank F K

local instance finalOneDegreeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance finalOneDegreeNeZero : NeZero p :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

/-- A fixed initial admissible denominator.  It is used only before the
canonical residual normalization, so the final local constants are
independent of this classical choice. -/
def endpointOneInitialAdmissibleGamma
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) :
    AdmissibleGamma F chi psi :=
  Classical.choice (AdmissibleGamma.exists_admissible (χ := chi) (ψ := psi))

/-- The conductor-one First Main Lemma at actual lower break `s+1`, for
an arbitrary initial admissible denominator used only to make the canonical
residual normalization. -/
theorem firstMain_wildEndpoint_one_withGamma
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) :
    let hspos : 0 < s + 1 := by omega
    let piF := wildLowerUniformizer F K piK hpiK
    let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
    let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
    let chiK := endpointIntrinsicNormData F K ht hres piK hpiK hgen
      chi hchi hspos
    let psiK := endpointIntrinsicTraceData F K ht hres piK hpiK hgen psi
    let gammaK := endpointNormalizedDerivativeGamma
      F K ht hspos hres piK hpiK hgen chi hchi psi gamma0
    let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
      F piF hpiF chi hchi psi gammaF
    let gammaNorm := endpointOneGammaNorm F K ht hres piK hpiK hgen
      piF hpiF psi normalizedGammaF
    deltaFinite chiK psiK gammaK *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu => deltaFinite
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
            psi (gammaNorm mu)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (wildEndpointOneTwistData F K ht hspos hres piK hpiK hgen
            chi hchi mu) psi
          (wildEndpointOneTwistGamma F K ht hspos hres piK hpiK hgen
            chi hchi psi gammaF gammaNorm mu)) := by
  let hspos : 0 < s + 1 := by omega
  let piF := wildLowerUniformizer F K piK hpiK
  let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
  let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
  let gammaK := endpointNormalizedDerivativeGamma
    F K ht hspos hres piK hpiK hgen chi hchi psi gamma0
  let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
    F piF hpiF chi hchi psi gammaF
  let gammaTau := endpointOneGammaTau
    F K ht hres piK hpiK hgen piF hpiF psi normalizedGammaF
  let hr := endpointOneTauStationaryDepth
    F K ht hspos hres piK hpiK hgen
  let bTau := endpointOneBTau F K ht hspos hres piK hpiK hgen
    piF hpiF psi normalizedGammaF
  let hbTau : (bTau : F) ≠ 0 := endpointOneBTau_ne_zero
    F K ht hspos hres piK hpiK hgen piF hpiF psi normalizedGammaF
  have hnormalized :
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) = endpointCanonicalResidualAddChar (ResidueField F) := by
    exact endpointNormalizedAdmissibleGamma_residualAddChar
      F chi hchi psi gamma0
  have hgammaTau :
      (gammaTau : Fˣ) =
        (wildLowerUniformizer F K piK hpiK) ^ (s + 1) * (gammaF : Fˣ) := by
    simp only [gammaTau, endpointOneGammaTau_coe,
      normalizedGammaF, endpointOneNormalizedGammaOfAdmissible_coe,
      piF]
    rw [show (s + 1) + 1 = (s + 1) + 1 by rfl, pow_succ]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hbSpec :
      latticeQuotientMk F
          (sub_le_sub_left hr.int_le_conductor ((((s + 1) + 1 : ℕ) : ℤ)))
          bTau =
        stationaryNumeratorClass F
          (endpointTauData F K ht hres piK hpiK hgen) psi
          ((((s + 1) + 1 : ℕ) : ℤ)) hr gammaTau gammaTau.property := by
    exact endpointOneBTau_spec F K ht hspos hres piK hpiK hgen
      piF hpiF psi normalizedGammaF
  have hdisc := endpoint_discriminant_congruence
    F K ht hres piK hpiK hgen chi hchi psi gammaF hnormalized
      gammaTau hgammaTau hr bTau hbSpec
  have hsign :
      (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) /
          (((-1 : Fˣ) ^ p) *
            ((gammaTau : Fˣ) / Units.mk0 (bTau : F) hbTau) ^ (p - 1)) ∈
        unitFiltration F 1 := by
    dsimp only at hdisc
    exact hdisc
  exact wildEndpointOne_finalProduct_of_signCongruence
    F K ht hspos hres piK hpiK hgen chi hchi psi gamma0 (by
      simpa only [piF, hpiF, gammaF, gammaK, normalizedGammaF,
        gammaTau, bTau, hbTau] using hsign)

/-- **First Main Lemma, wild conductor-one endpoint.**  This principal
version has no denominator argument: an initial admissible denominator is
chosen internally and immediately replaced by the canonical residual
normalization.  Both sides retain the complete norm-character product,
including the exceptional identity factor. -/
theorem firstMain_wildEndpoint_one
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F) :
    let gamma0 := endpointOneInitialAdmissibleGamma F chi psi
    let hspos : 0 < s + 1 := by omega
    let piF := wildLowerUniformizer F K piK hpiK
    let hpiF := wildLowerUniformizer_isUniformizer F K hres piK hpiK
    let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
    let chiK := endpointIntrinsicNormData F K ht hres piK hpiK hgen
      chi hchi hspos
    let psiK := endpointIntrinsicTraceData F K ht hres piK hpiK hgen psi
    let gammaK := endpointNormalizedDerivativeGamma
      F K ht hspos hres piK hpiK hgen chi hchi psi gamma0
    let normalizedGammaF := endpointOneNormalizedGammaOfAdmissible
      F piF hpiF chi hchi psi gammaF
    let gammaNorm := endpointOneGammaNorm F K ht hres piK hpiK hgen
      piF hpiF psi normalizedGammaF
    deltaFinite chiK psiK gammaK *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu => deltaFinite
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
            psi (gammaNorm mu)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (wildEndpointOneTwistData F K ht hspos hres piK hpiK hgen
            chi hchi mu) psi
          (wildEndpointOneTwistGamma F K ht hspos hres piK hpiK hgen
            chi hchi psi gammaF gammaNorm mu)) := by
  dsimp only
  exact firstMain_wildEndpoint_one_withGamma
    F K ht hres piK hpiK hgen chi hchi psi
      (endpointOneInitialAdmissibleGamma F chi psi)

end FinalEndpointOneUnconditional

end

end LanglandsFirstMainLemma
