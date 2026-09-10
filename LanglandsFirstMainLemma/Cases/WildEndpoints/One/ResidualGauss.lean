import LanglandsFirstMainLemma.Cases.WildEndpoints.Common

/-!
# Residual Gauss sums at the wild conductor-one endpoint
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section WildEndpointOneAssembly

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (htwild : 0 < t) (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

local instance wildEndpointOneResidueFintype : Fintype (ResidueField F) :=
  residueFieldFintype F

local instance wildEndpointOneResidueKFintype : Fintype (ResidueField K) :=
  residueFieldFintype K

include ht htwild hres piK hpiK hgen

/-- Changing only the proof-bearing exact-conductor package and admissible
denominator does not change the local constant when the underlying
quasi-character is unchanged. -/
theorem endpointDeltaFinite_eq_of_character_eq
    (chi omega : LocalQuasiCharData F)
    (hchar : chi.character = omega.character)
    (psi : LocalAddCharData F)
    (gammaChi : AdmissibleGamma F chi psi)
    (gammaOmega : AdmissibleGamma F omega psi) :
    deltaFinite chi psi gammaChi = deltaFinite omega psi gammaOmega := by
  have hdata : chi = omega := LocalQuasiCharData.ext_character F hchar
  subst omega
  exact (deltaFinite_gamma_independent chi psi gammaChi gammaOmega).symm

/-- The conductor-one right-hand factor.  The identity norm character gives
`chiF` literally; every nonidentity factor is the stable product with the
conductor-`t+1` norm character. -/
def wildEndpointOneTwistData
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (mu : NormCharacter F K) : LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact chiF
  · let theta := wildNormCharacterData F K ht hres piK hpiK hgen mu
    have hcond : chiF.conductor < theta.conductor := by
      rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu,
        hchiF]
      omega
    exact stableTwistData F chiF theta hcond

@[simp]
theorem wildEndpointOneTwistData_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1) :
    wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen chiF hchiF 1 = chiF := by
  simp [wildEndpointOneTwistData]

theorem wildEndpointOneTwistData_character
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (mu : NormCharacter F K) :
    (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
      chiF hchiF mu).character = mu.1 * chiF.character := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    rw [wildEndpointOneTwistData_one F K ht htwild hres piK hpiK hgen]
    exact (one_mul chiF.character).symm
  · simp only [wildEndpointOneTwistData, hmu, ↓reduceDIte,
      stableTwistData_character, wildNormCharacterData_character]
    exact mul_comm chiF.character mu.1

/-- Denominators matched to `wildEndpointOneTwistData`.  The identity keeps
the genuine conductor-one denominator; each nonidentity factor keeps the
high-conductor norm-character denominator required by stable twisting. -/
def wildEndpointOneTwistGamma
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F)
    (gammaChi : AdmissibleGamma F chiF psiF)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF)
    (mu : NormCharacter F K) :
    AdmissibleGamma F
      (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
        chiF hchiF mu) psiF := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    refine ⟨(gammaChi : Fˣ), ?_⟩
    simpa [wildEndpointOneTwistData] using gammaChi.property
  · let theta := wildNormCharacterData F K ht hres piK hpiK hgen mu
    have hcond : chiF.conductor < theta.conductor := by
      rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu,
        hchiF]
      omega
    refine ⟨(gammaNorm mu : Fˣ), ?_⟩
    simpa [wildEndpointOneTwistData, hmu, theta] using (gammaNorm mu).property

@[simp]
theorem wildEndpointOneTwistGamma_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F)
    (gammaChi : AdmissibleGamma F chiF psiF)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF) :
    (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen chiF hchiF
      psiF gammaChi gammaNorm 1 : Fˣ) = (gammaChi : Fˣ) := by
  simp [wildEndpointOneTwistGamma]

theorem wildEndpointOneTwistGamma_ne_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F)
    (gammaChi : AdmissibleGamma F chiF psiF)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen chiF hchiF
      psiF gammaChi gammaNorm mu : Fˣ) = (gammaNorm mu : Fˣ) := by
  simp [wildEndpointOneTwistGamma, hmu]

/-- Stable twisting at each nonidentity norm-character factor.  The factor
is the reciprocal stationary element `Gamma / beta`; no stationary class is
introduced for the endpoint conductor-one character. -/
theorem wildEndpointOne_stableTwistFactor
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F)
    (gammaChi : AdmissibleGamma F chiF psiF)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hbreak : t + 1 = 2 * d + epsilon)
    (c : lattice F
      (((wildNormCharacterData F K ht hres piK hpiK hgen
        mu).conductor : ℤ) -
        ((wildNormCharacterData F K ht hres piK hpiK hgen
          mu).conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (stableTwist_stationaryDepth F
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
              d epsilon hepsilon (by
                rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
                  mu hmu]
                omega) (by
                  rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
                    mu hmu]
                  omega)).int_le_conductor
          ((wildNormCharacterData F K ht hres piK hpiK hgen
            mu).conductor : ℤ)) c =
      stationaryNumeratorClass F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF
        ((wildNormCharacterData F K ht hres piK hpiK hgen
          mu).conductor : ℤ)
        (stableTwist_stationaryDepth F
          (wildNormCharacterData F K ht hres piK hpiK hgen mu)
            d epsilon hepsilon (by
              rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
                mu hmu]
              omega) (by
                rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
                  mu hmu]
                omega))
        (gammaNorm mu) (gammaNorm mu).property) :
    deltaFinite
        (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
          chiF hchiF mu) psiF
        (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen
          chiF hchiF psiF gammaChi gammaNorm mu) =
      (chiF.character ((gammaNorm mu : Fˣ) /
        stableStationaryRepresentativeUnit F
          (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF
          (stableTwist_stationaryDepth F
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
              d epsilon hepsilon (by
                rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
                  mu hmu]
                omega) (by
                  rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen
                    mu hmu]
                  omega))
          (gammaNorm mu) c hc) : ℂ) *
        deltaFinite
          (wildNormCharacterData F K ht hres piK hpiK hgen mu)
          psiF (gammaNorm mu) := by
  let theta := wildNormCharacterData F K ht hres piK hpiK hgen mu
  have htheta : theta.conductor = 2 * d + epsilon := by
    rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu]
    omega
  have hlarge : 1 < theta.conductor := by
    rw [wildNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu]
    omega
  have hnu : chiF.conductor ≤ d := by
    rw [hchiF]
    omega
  have h := stableTwist F chiF theta psiF d epsilon hepsilon htheta hlarge
    hnu (gammaNorm mu) c hc
  let hcond : chiF.conductor < theta.conductor := by omega
  let twist := stableTwistData F chiF theta hcond
  let gammaTwist :=
    stableTwistAdmissibleGamma F chiF theta psiF hcond (gammaNorm mu)
  have hchar :
      (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
        chiF hchiF mu).character = twist.character := by
    rw [wildEndpointOneTwistData_character F K ht htwild hres piK hpiK hgen]
    change mu.1 * chiF.character = chiF.character * theta.character
    rw [show theta.character = mu.1 by
      exact wildNormCharacterData_character F K ht hres piK hpiK hgen mu]
    exact mul_comm (mu.1 : ContinuousQuasiChar F) chiF.character
  calc
    deltaFinite
        (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
          chiF hchiF mu) psiF
        (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen
          chiF hchiF psiF gammaChi gammaNorm mu) =
        deltaFinite twist psiF gammaTwist := by
      exact endpointDeltaFinite_eq_of_character_eq F K ht htwild hres piK hpiK hgen
        _ _ hchar psiF _ _
    _ = _ := by
      simpa [gammaTwist, twist, theta] using h

/-- Once the two residual Gauss sums have been identified, the exact
conductor-one residue formulas give the upper endpoint ratio.  Applying
`deltaFinite_conductor_one` on both fields keeps the unique leading minus
sign and the inverse multiplicative-character convention explicit. -/
theorem wildEndpointOne_upperRatio_of_residualGauss
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (chiK : LocalQuasiCharData K) (hchiK : chiK.conductor = 1)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : AdmissibleGamma F chiF psiF)
    (gammaK : AdmissibleGamma K chiK psiK)
    (hGauss :
      let hgammaK : ord K ((gammaK : Kˣ) : K) =
          ((psiK.conductor + 1 : ℤ) : WithTop ℤ) := by
        calc
          ord K ((gammaK : Kˣ) : K) =
              ((((chiK.conductor : ℕ) : ℤ) + psiK.conductor : ℤ) :
                WithTop ℤ) := gammaK.property
          _ = ((psiK.conductor + 1 : ℤ) : WithTop ℤ) := by
            norm_cast
            omega
      let hgammaF : ord F ((gammaF : Fˣ) : F) =
          ((psiF.conductor + 1 : ℤ) : WithTop ℤ) := by
        calc
          ord F ((gammaF : Fˣ) : F) =
              ((((chiF.conductor : ℕ) : ℤ) + psiF.conductor : ℤ) :
                WithTop ℤ) := gammaF.property
          _ = ((psiF.conductor + 1 : ℤ) : WithTop ℤ) := by
            norm_cast
            omega
      langlandsGaussSum (residualMulChar K chiK)
          (residualAddChar K psiK (gammaK : Kˣ) hgammaK) =
        langlandsGaussSum (residualMulChar F chiF)
          (residualAddChar F psiF (gammaF : Fˣ) hgammaF)) :
    deltaFinite chiK psiK gammaK =
      (chiF.character
        (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) *
        deltaFinite chiF psiF gammaF := by
  let hgammaK : ord K ((gammaK : Kˣ) : K) =
      ((psiK.conductor + 1 : ℤ) : WithTop ℤ) := by
    calc
      ord K ((gammaK : Kˣ) : K) =
          ((((chiK.conductor : ℕ) : ℤ) + psiK.conductor : ℤ) :
            WithTop ℤ) := gammaK.property
      _ = ((psiK.conductor + 1 : ℤ) : WithTop ℤ) := by
        norm_cast
        omega
  let hgammaF : ord F ((gammaF : Fˣ) : F) =
      ((psiF.conductor + 1 : ℤ) : WithTop ℤ) := by
    calc
      ord F ((gammaF : Fˣ) : F) =
          ((((chiF.conductor : ℕ) : ℤ) + psiF.conductor : ℤ) :
            WithTop ℤ) := gammaF.property
      _ = ((psiF.conductor + 1 : ℤ) : WithTop ℤ) := by
        norm_cast
        omega
  have hK := deltaFinite_conductor_one K chiK hchiK psiK gammaK
  have hF := deltaFinite_conductor_one F chiF hchiF psiF gammaF
  have hcompGamma :
      (chiK.character (gammaK : Kˣ) : ℂ) =
        (chiF.character (normUnits F K (gammaK : Kˣ)) : ℂ) := by
    rw [hcomp]
    rfl
  have hmul :
      (chiF.character
          (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) *
          (chiF.character (gammaF : Fˣ) : ℂ) =
        (chiF.character (normUnits F K (gammaK : Kˣ)) : ℂ) := by
    have hu :
        chiF.character
            (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) *
            chiF.character (gammaF : Fˣ) =
          chiF.character (normUnits F K (gammaK : Kˣ)) := by
      rw [← map_mul]
      simp
    simpa using congrArg Units.val hu
  rw [hK, hF, hcompGamma, hGauss]
  rw [← hmul]
  ring

/-- The complete ramified norm-character enumeration with only the identity
removed; the identity is handled separately and explicitly in the product
assembly below. -/
def wildEndpointOneNontrivialNormCharacterFinset :
    Finset (NormCharacter F K) := by
  classical
  exact (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).erase 1

/-- Full conductor-one product assembly.  The complete norm-character
product is retained.  Its identity factor is proved to be `1` on the norm
side and the original conductor-one local constant on the twist side; every
nonidentity factor is supplied by stable twisting.  The discriminant
certificate has the audited direction `upper / product ∈ U_F^1`. -/
theorem wildEndpointOne_productAssembly
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (chiK : LocalQuasiCharData K) (psiF : LocalAddCharData F)
    (psiK : LocalAddCharData K)
    (gammaF : AdmissibleGamma F chiF psiF)
    (gammaK : AdmissibleGamma K chiK psiK)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF)
    (factor : NormCharacter F K → Fˣ)
    (hupper :
      deltaFinite chiK psiK gammaK =
        (chiF.character
          (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) *
          deltaFinite chiF psiF gammaF)
    (hdiscriminant :
      (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) /
          (wildEndpointOneNontrivialNormCharacterFinset
            F K ht hres piK hpiK hgen).prod factor ∈ unitFiltration F 1)
    (hstable : ∀ (mu : NormCharacter F K), mu ≠ 1 →
      deltaFinite
          (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
            chiF hchiF mu) psiF
          (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen
            chiF hchiF psiF gammaF gammaNorm mu) =
        (chiF.character (factor mu) : ℂ) *
          deltaFinite
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
            psiF (gammaNorm mu)) :
    deltaFinite chiK psiK gammaK *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu => deltaFinite
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
            psiF (gammaNorm mu)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
            chiF hchiF mu) psiF
          (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen
            chiF hchiF psiF gammaF gammaNorm mu)) := by
  classical
  let S := ramifiedNormCharacterFinset F K ht hres piK hpiK hgen
  let normDelta : NormCharacter F K → ℂ := fun mu =>
    deltaFinite
      (wildNormCharacterData F K ht hres piK hpiK hgen mu)
      psiF (gammaNorm mu)
  let twistDelta : NormCharacter F K → ℂ := fun mu =>
    deltaFinite
      (wildEndpointOneTwistData F K ht htwild hres piK hpiK hgen
        chiF hchiF mu) psiF
      (wildEndpointOneTwistGamma F K ht htwild hres piK hpiK hgen
        chiF hchiF psiF gammaF gammaNorm mu)
  have honeMem : (1 : NormCharacter F K) ∈ S := by
    simp [S, ramifiedNormCharacterFinset, normCharacterFinset]
  have hnormOne : normDelta 1 = 1 := by
    dsimp only [normDelta]
    exact delta_trivial_of_character_eq_one F _
      (by
        ext x
        rw [wildNormCharacterData_character F K ht hres piK hpiK hgen]
        rfl)
      psiF (gammaNorm 1)
  have htwistOne : twistDelta 1 = deltaFinite chiF psiF gammaF := by
    dsimp only [twistDelta]
    exact endpointDeltaFinite_eq_of_character_eq
      F K ht htwild hres piK hpiK hgen _ _
      (by
        rw [wildEndpointOneTwistData_character
          F K ht htwild hres piK hpiK hgen]
        exact one_mul chiF.character)
      psiF _ gammaF
  have hnormProd : S.prod normDelta = (S.erase 1).prod normDelta := by
    exact (Finset.prod_erase S hnormOne).symm
  have hstableProd :
      (S.erase 1).prod twistDelta =
        (S.erase 1).prod (fun mu =>
          (chiF.character (factor mu) : ℂ) * normDelta mu) := by
    apply Finset.prod_congr rfl
    intro mu hmu
    apply hstable mu
    exact (Finset.mem_erase.mp hmu).1
  have htwistProd :
      S.prod twistDelta =
        deltaFinite chiF psiF gammaF *
          (S.erase 1).prod (fun mu =>
            (chiF.character (factor mu) : ℂ) * normDelta mu) := by
    rw [← Finset.mul_prod_erase S twistDelta honeMem, htwistOne, hstableProd]
  let factorProduct : Fˣ := (S.erase 1).prod factor
  have hchiTriv :
      chiF.character
        ((normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) /
          factorProduct) = 1 := by
    apply chiF.isConductor.trivial
    simpa only [hchiF, factorProduct, S,
      wildEndpointOneNontrivialNormCharacterFinset] using hdiscriminant
  have hchiUpperUnits :
      chiF.character (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) =
        chiF.character factorProduct := by
    have hmap := map_div chiF.character
      (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) factorProduct
    rw [hchiTriv] at hmap
    exact div_eq_one.mp hmap.symm
  have hchiUpper :
      (chiF.character
        (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) =
        (S.erase 1).prod (fun mu => (chiF.character (factor mu) : ℂ)) := by
    calc
      (chiF.character
          (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) =
          (chiF.character factorProduct : ℂ) :=
        congrArg Units.val hchiUpperUnits
      _ = _ := by
        have hu : chiF.character factorProduct =
            (S.erase 1).prod (fun mu => chiF.character (factor mu)) := by
          exact map_prod chiF.character factor (S.erase 1)
        simpa using congrArg Units.val hu
  change deltaFinite chiK psiK gammaK * S.prod normDelta = S.prod twistDelta
  rw [hupper, hnormProd, htwistProd, hchiUpper]
  rw [Finset.prod_mul_distrib]
  ring

end WildEndpointOneAssembly

private theorem endpoint_nonarchimedeanLocalFieldInfinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  let f : Int → F := fun n => (exists_ord_eq F n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord F (f m) = (m : WithTop Int) := (exists_ord_eq F m).choose_spec
    have hn : ord F (f n) = (n : WithTop Int) := (exists_ord_eq F n).choose_spec
    have hcoe : (m : WithTop Int) = (n : WithTop Int) :=
      hm.symm.trans ((congrArg (ord F) hmn).trans hn)
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

private theorem endpoint_field_adjoin_eq_top_of_integer_adjoin_eq_top
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Finite F K]
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Algebra.adjoin F ({(pi : K)} : Set K) = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (ringOfIntegers K) x
  have hintegral (z : ringOfIntegers K) :
      (z : K) ∈ Algebra.adjoin F ({(pi : K)} : Set K) := by
    have hz : z ∈ Algebra.adjoin (ringOfIntegers F)
        ({pi} : Set (ringOfIntegers K)) := by
      rw [hgen]
      trivial
    exact Algebra.adjoin_induction (p := fun (z : ringOfIntegers K) _ =>
        (z : K) ∈ Algebra.adjoin F ({(pi : K)} : Set K))
      (fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact Algebra.subset_adjoin (Set.mem_singleton (pi : K)))
      (fun r => by
        change algebraMap F K (r : F) ∈ Algebra.adjoin F ({(pi : K)} : Set K)
        exact (Algebra.adjoin F ({(pi : K)} : Set K)).algebraMap_mem (r : F))
      (fun u v _ _ hu hv => by
        simpa only [Subring.coe_add] using
          (Algebra.adjoin F ({(pi : K)} : Set K)).add_mem hu hv)
      (fun u v _ _ hu hv => by
        simpa only [Subring.coe_mul] using
          (Algebra.adjoin F ({(pi : K)} : Set K)).mul_mem hu hv)
      hz
  have ha : algebraMap (ringOfIntegers K) K a ∈
      Algebra.adjoin F ({(pi : K)} : Set K) := by
    rw [congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) a]
    exact hintegral a
  have hbmem : algebraMap (ringOfIntegers K) K b ∈
      Algebra.adjoin F ({(pi : K)} : Set K) := by
    rw [congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) b]
    exact hintegral b
  have hbInv : (algebraMap (ringOfIntegers K) K b)⁻¹ ∈
      Algebra.adjoin F ({(pi : K)} : Set K) :=
    (Algebra.IsIntegral.isIntegral (algebraMap (ringOfIntegers K) K b)).inv_mem hbmem
  rw [← hab]
  simpa only [div_eq_mul_inv] using
    (Algebra.adjoin F ({(pi : K)} : Set K)).mul_mem ha hbInv

private theorem endpoint_aeval_derivative_minpoly_eq_prod_nonidentity
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    Polynomial.aeval (pi : K) (Polynomial.derivative (minpoly F (pi : K))) =
      ∏ sigma ∈ nonidentityGaloisAutomorphisms F K, ((pi : K) - sigma (pi : K)) := by
  classical
  letI : Infinite F := endpoint_nonarchimedeanLocalFieldInfinite F
  let x : K := (pi : K)
  have hfield : Algebra.adjoin F ({x} : Set K) = ⊤ := by
    exact endpoint_field_adjoin_eq_top_of_integer_adjoin_eq_top F K pi hgen
  let pb : PowerBasis F K :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral x) hfield
  have hpbgen : pb.gen = x :=
    PowerBasis.ofAdjoinEqTop_gen (Algebra.IsIntegral.isIntegral x) hfield
  have hchar : (Algebra.lmul F K x).charpoly = minpoly F x := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul F K x) pb.basis]
    change (Algebra.leftMulMatrix pb.basis x).charpoly = minpoly F x
    rw [← hpbgen]
    exact charpoly_leftMulMatrix pb
  have hpoly :
      (minpoly F x).map (algebraMap F K) =
        Multiset.prod ((galoisConjugates F K x).map
          (fun z => Polynomial.X - Polynomial.C z)) := by
    rw [← hchar]
    simpa [galoisConjugates, galoisConjugate] using
      (map_lmul_charpoly_eq_prod_galois F K x)
  have hinjective :
      Function.Injective (fun sigma : Gal(K/F) => galoisConjugate sigma x) := by
    intro sigma tau hst
    have hhom : sigma.toAlgHom = tau.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hfield
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hst
    apply AlgEquiv.ext
    intro z
    exact DFunLike.congr_fun hhom z
  have hxmem : x ∈ galoisConjugates F K x := by
    rw [galoisConjugates, Multiset.mem_map]
    exact ⟨1, by simp, by simp [galoisConjugate]⟩
  change Polynomial.aeval x (Polynomial.derivative (minpoly F x)) = _
  calc
    Polynomial.aeval x (Polynomial.derivative (minpoly F x)) =
        Polynomial.eval x
          (Polynomial.derivative ((minpoly F x).map (algebraMap F K))) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.derivative_map]
    _ = Polynomial.eval x
          (Polynomial.derivative
            (Multiset.prod ((galoisConjugates F K x).map
              (fun z => Polynomial.X - Polynomial.C z)))) := by
      rw [hpoly]
    _ = Multiset.prod
          (((galoisConjugates F K x).erase x).map (fun z => x - z)) :=
      Polynomial.eval_multiset_prod_X_sub_C_derivative hxmem
    _ = ∏ sigma ∈ nonidentityGaloisAutomorphisms F K, (x - sigma x) := by
      have herase :
          Multiset.map (fun sigma : Gal(K/F) => galoisConjugate sigma x)
              (Finset.univ.erase 1).val =
            (Multiset.map (fun sigma : Gal(K/F) => galoisConjugate sigma x)
              (Finset.univ : Finset Gal(K/F)).val).erase x := by
        simpa [galoisConjugate] using
          (Multiset.map_erase (fun sigma : Gal(K/F) => galoisConjugate sigma x)
            hinjective 1 (Finset.univ : Finset Gal(K/F)).val)
      rw [galoisConjugates, ← herase, Multiset.map_map,
        ← Finset.prod_eq_multiset_prod]
      rfl

private theorem endpoint_ord_derivative_eq_differentExponent
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    ord K (Polynomial.aeval (pi : K)
        (Polynomial.derivative (minpoly F (pi : K)))) =
      (((differentExponent F K : Nat) : Int) : WithTop Int) := by
  classical
  rw [endpoint_aeval_derivative_minpoly_eq_prod_nonidentity F K pi hgen]
  have hordprod (s : Finset Gal(K/F)) :
      ord K (∏ sigma ∈ s, ((pi : K) - sigma (pi : K))) =
        ∑ sigma ∈ s, ord K ((pi : K) - sigma (pi : K)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert sigma s hs ih =>
        rw [Finset.prod_insert hs, Finset.sum_insert hs, ord_mul, ih]
  rw [hordprod]
  unfold differentExponent
  rw [Nat.cast_sum, WithTop.coe_sum]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  have hsigma_ne : sigma ≠ 1 :=
    (mem_nonidentityGaloisAutomorphisms F K).1 hsigma
  rw [show (pi : K) - sigma (pi : K) = -(sigma (pi : K) - (pi : K)) by ring,
    ord_neg,
    ord_galois_uniformizer_sub_eq_lowerDifferentSummand F K pi hpi hgen hsigma_ne]

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : Nat} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

local instance endpointIntrinsicResidueFintype : Fintype (ResidueField F) :=
  residueFieldFintype F

local instance endpointIntrinsicResidueKFintype : Fintype (ResidueField K) :=
  residueFieldFintype K

/-- Residue degree one turns the canonical residue map into an equivalence. -/
def endpointResidueEquiv (hres' : residueDegree F K = 1) :
    ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K, hres']
    have hdim : Module.finrank (ResidueField F) (ResidueField F) =
        Module.finrank (ResidueField F) (ResidueField K) := by
      simp [hfin]
    have hinj : Function.Injective
        (Algebra.linearMap (ResidueField F) (ResidueField K)) :=
      (algebraMap (ResidueField F) (ResidueField K)).injective
    have hsurj :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by simpa only [Algebra.linearMap_apply] using hx⟩

@[simp] theorem endpointResidueEquiv_apply (x : ResidueField F) :
    endpointResidueEquiv F K hres x = extensionResidueMap F K x := rfl

/-- Additive trace pullback at the exact different-shifted conductor. -/
def endpointIntrinsicTraceData (psi : LocalAddCharData F) : LocalAddCharData K where
  character := psi.character.compTrace
  conductor :=
    (Module.finrank F K : Int) * psi.conductor +
      (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)
  isConductor := additiveConductor_compTrace_cyclicPrime
    F K ht hres pi hpi hgen psi.isConductor

/-- Conductor-one norm pullback. -/
def endpointIntrinsicNormData (chi : LocalQuasiCharData F)
    (hchi : chi.conductor = 1) (htpos : 0 < t) : LocalQuasiCharData K where
  character := chi.character.compNorm
  conductor := 1
  isConductor := multiplicativeConductor_compNorm_belowBreak
    F K ht hres pi hpi hgen (by omega) (by simpa [hchi] using chi.isConductor)

def endpointDerivative (pi : ringOfIntegers K) : K :=
  Polynomial.aeval (pi : K) (Polynomial.derivative (minpoly F (pi : K)))

include ht hpi hgen in
theorem endpointDerivative_order :
    ord K (endpointDerivative F K pi) =
      ((((Module.finrank F K - 1) * (t + 1) : Nat) : Int) : WithTop Int) := by
  rw [endpointDerivative, endpoint_ord_derivative_eq_differentExponent F K pi hpi hgen,
    differentExponent_eq F K ht pi hpi hgen]

include ht hpi hgen in
theorem endpointDerivative_ne_zero : endpointDerivative F K pi ≠ 0 := by
  apply (ord_ne_top_iff K).mp
  rw [endpointDerivative_order F K ht pi hpi hgen]
  exact WithTop.coe_ne_top

include hgen in
/-- The top power is trace-dual to itself through the derivative denominator:
`Tr(pi^(p-1) / f'(pi)) = 1`. -/
theorem endpoint_trace_topPower_div_derivative :
    trace F K ((pi : K) ^ (Module.finrank F K - 1) /
      endpointDerivative F K pi) = 1 := by
  let p := Module.finrank F K
  have hp : 0 < p := Module.finrank_pos
  have hfield : Algebra.adjoin F ({(pi : K)} : Set K) = ⊤ :=
    endpoint_field_adjoin_eq_top_of_integer_adjoin_eq_top F K pi hgen
  let pb : PowerBasis F K :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral (pi : K)) hfield
  have hpbgen : pb.gen = (pi : K) :=
    PowerBasis.ofAdjoinEqTop_gen (Algebra.IsIntegral.isIntegral (pi : K)) hfield
  have hpbdim : pb.dim = p := (pb.finrank.trans rfl).symm
  let i : Fin pb.dim := ⟨p - 1, by omega⟩
  have hminpolyDegree : (minpoly F pb.gen).natDegree = p := by
    rw [pb.natDegree_minpoly, hpbdim]
  have hdivDegree : (minpolyDiv F pb.gen).natDegree = p - 1 := by
    have hs := natDegree_minpolyDiv_succ (R := F) (x := pb.gen)
      (Algebra.IsIntegral.isIntegral pb.gen)
    rw [hminpolyDegree] at hs
    omega
  have hicoe : (i : Nat) = p - 1 := rfl
  have hcoeff : (minpolyDiv F pb.gen).coeff (i : Nat) = (1 : K) := by
    rw [hicoe, ← hdivDegree]
    exact (minpolyDiv_monic (R := F)
      (Algebra.IsIntegral.isIntegral pb.gen)).coeff_natDegree
  have hdual := Module.Basis.traceDual_powerBasis_eq pb i
  rw [hcoeff, one_div] at hdual
  have htrace := Module.Basis.trace_mul_traceDual pb.basis i i
  rw [if_pos rfl, hdual, pb.basis_eq_pow] at htrace
  change trace F K ((pi : K) ^ (p - 1) / endpointDerivative F K pi) = 1
  simpa only [hpbgen, endpointDerivative, div_eq_mul_inv] using htrace

/-- Manuscript denominator `gamma_F f'(pi) / pi^(p-1)`. -/
def endpointDerivativeGammaUnit
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi) : Kˣ :=
  Units.mk0
    (algebraMap F K (((gammaF : Fˣ) : F)) * endpointDerivative F K pi /
      (pi : K) ^ (Module.finrank F K - 1))
    (by
      apply div_ne_zero
      · apply mul_ne_zero
        · simpa using ((algebraMap F K).injective.ne gammaF.coe_ne_zero)
        · exact endpointDerivative_ne_zero F K ht pi hpi hgen
      · exact pow_ne_zero _ hpi.ne_zero)

include ht hres hpi hgen in
theorem endpointDerivativeGammaUnit_order
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi) :
    ord K ((endpointDerivativeGammaUnit F K ht pi hpi hgen chi psi gammaF : Kˣ) : K) =
      ((((1 : Nat) : Int) +
        ((Module.finrank F K : Int) * psi.conductor +
          (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) : Int) :
        WithTop Int) := by
  let p := Module.finrank F K
  have hp2 : 2 ≤ p := (PrimeCyclicExtension.degree_prime F K).two_le
  have hram : ramificationIndex F K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  change ord K
      (algebraMap F K (((gammaF : Fˣ) : F)) * endpointDerivative F K pi /
        (pi : K) ^ (p - 1)) = _
  rw [ord_div, ord_mul, ord_algebraMap, gammaF.property,
    endpointDerivative_order F K ht pi hpi hgen, ord_pow,
    ord_uniformizer K hpi, hram]
  rw [← WithTop.coe_nsmul, nsmul_one]
  norm_cast
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  rw [hchi]
  dsimp only [p]
  ring

/-- The derivative denominator is admissible for the conductor-one norm/trace pullbacks. -/
def endpointDerivativeGamma
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (htpos : 0 < t) (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi) :
    AdmissibleGamma K
      (endpointIntrinsicNormData F K ht hres pi hpi hgen chi hchi htpos)
      (endpointIntrinsicTraceData F K ht hres pi hpi hgen psi) :=
  ⟨endpointDerivativeGammaUnit F K ht pi hpi hgen chi psi gammaF,
    endpointDerivativeGammaUnit_order F K ht hres pi hpi hgen chi hchi psi gammaF⟩

include ht hres hpi hgen in
/-- The residual additive character attached to the derivative denominator
is exactly the base residual character, after the degree-one residue map. -/
theorem endpoint_residualAddChar_derivativeGamma
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (htpos : 0 < t) (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi) (x : ResidueField F) :
    let psiK := endpointIntrinsicTraceData F K ht hres pi hpi hgen psi
    let gammaK := endpointDerivativeGamma F K ht hres pi hpi hgen
      chi hchi htpos psi gammaF
    let hgammaF : ord F (((gammaF : Fˣ) : F)) =
        ((psi.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaF.property]
      norm_cast
      omega
    let hgammaK : ord K (((gammaK : Kˣ) : K)) =
        ((psiK.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaK.property]
      change (((1 : Int) +
          ((Module.finrank F K : Int) * psi.conductor +
            (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) : Int) :
          WithTop Int) =
        ((((Module.finrank F K : Int) * psi.conductor +
            (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) + 1 : Int) :
          WithTop Int)
      norm_cast
      ring
    residualAddChar K psiK (gammaK : Kˣ) hgammaK
        (extensionResidueMap F K x) =
      residualAddChar F psi (gammaF : Fˣ) hgammaF x := by
  dsimp only
  let a : ringOfIntegers F := teichmuller F x
  have haF : (a : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 a.property
  let aK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) a
  have haKcoe : (aK : K) = algebraMap F K (a : F) :=
    Valuation.HasExtension.val_algebraMap a
  have haK : algebraMap F K (a : F) ∈ lattice K 0 := by
    rw [← haKcoe]
    exact (mem_lattice_zero_iff K).2 aK.property
  have hreduceF : reduce F (a : F) haF = x := by
    simp [a, reduce]
  have hreduceK : reduce K (algebraMap F K (a : F)) haK =
      extensionResidueMap F K x := by
    change residueMap K aK = extensionResidueMap F K x
    rw [← hreduceF]
    change residueMap K aK = extensionResidueMap F K (residueMap F a)
    rfl
  rw [← hreduceK, residualAddChar_integral_lift,
    ← hreduceF, residualAddChar_integral_lift]
  change ((psi.character.compTrace)
      (algebraMap F K (a : F) /
        (algebraMap F K (((gammaF : Fˣ) : F)) * endpointDerivative F K pi /
          (pi : K) ^ (Module.finrank F K - 1))) : ℂ) =
    (psi.character ((a : F) / (((gammaF : Fˣ) : F))) : ℂ)
  rw [ContinuousAddChar.compTrace_apply]
  have hpi0 : (pi : K) ≠ 0 := hpi.ne_zero
  have hdelta0 : endpointDerivative F K pi ≠ 0 :=
    endpointDerivative_ne_zero F K ht pi hpi hgen
  have hgamma0 : (((gammaF : Fˣ) : F)) ≠ 0 := gammaF.coe_ne_zero
  have harg :
      algebraMap F K (a : F) /
          (algebraMap F K (((gammaF : Fˣ) : F)) * endpointDerivative F K pi /
            (pi : K) ^ (Module.finrank F K - 1)) =
        algebraMap F K ((a : F) / (((gammaF : Fˣ) : F))) *
          ((pi : K) ^ (Module.finrank F K - 1) /
            endpointDerivative F K pi) := by
    have hmapdiv :
        algebraMap F K ((a : F) / (((gammaF : Fˣ) : F))) =
          algebraMap F K (a : F) /
            algebraMap F K (((gammaF : Fˣ) : F)) := by
      exact map_div₀ (algebraMap F K) (a : F) (((gammaF : Fˣ) : F))
    rw [hmapdiv]
    field_simp
  rw [harg]
  have htrace : trace F K
      (algebraMap F K ((a : F) / (((gammaF : Fˣ) : F))) *
        ((pi : K) ^ (Module.finrank F K - 1) /
          endpointDerivative F K pi)) =
      (a : F) / (((gammaF : Fˣ) : F)) := by
    rw [← Algebra.smul_def]
    rw [map_smul, endpoint_trace_topPower_div_derivative F K pi hgen]
    simp
  rw [htrace]

include ht hres hpi hgen in
/-- A conductor-one norm pullback has residual character
`x ↦ chibar(x^[K:F])` under the degree-one residue equivalence. -/
theorem endpoint_residualMulChar_compNorm
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (htpos : 0 < t) (x : ResidueField F) :
    residualMulChar K
        (endpointIntrinsicNormData F K ht hres pi hpi hgen chi hchi htpos)
        (endpointResidueEquiv F K hres x) =
      residualMulChar F chi (x ^ Module.finrank F K) := by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero, MulChar.map_zero]
    have hp0 : Module.finrank F K ≠ 0 := by
      exact Nat.ne_of_gt Module.finrank_pos
    rw [zero_pow hp0, MulChar.map_zero]
  let xu : (ResidueField F)ˣ := Units.mk0 x hx
  let uF : unitGroup F := teichmullerLocalUnits F xu
  have huFord : ord F (((uF : unitGroup F) : Fˣ) : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F (uF : Fˣ)).1 uF.property
  let uKval : Kˣ := Units.map (algebraMap F K) (uF : Fˣ)
  have huKord : ord K (uKval : K) = 0 := by
    dsimp only [uKval]
    change ord K (algebraMap F K ((((uF : unitGroup F) : Fˣ) : F))) = 0
    rw [ord_algebraMap, huFord]
    simp
  let uK : unitGroup K :=
    ⟨uKval, (mem_unitGroup_iff_ord_eq_zero K uKval).2 huKord⟩
  have hresF :
      ((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F) = x := by
    rw [residueUnits_teichmullerLocalUnits]
    rfl
  have hresKunits :
      residueUnits K uK =
        Units.map (extensionResidueMap F K) (residueUnits F uF) := by
    apply Units.ext
    rw [residueUnits_coe]
    change residueMap K
        (unitGroupMulEquivRingOfIntegers K uK) =
      extensionResidueMap F K
        (((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F))
    rw [residueUnits_coe]
    rfl
  have hresK :
      ((residueUnits K uK : (ResidueField K)ˣ) : ResidueField K) =
        endpointResidueEquiv F K hres x := by
    rw [hresKunits]
    change extensionResidueMap F K
        (((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F)) =
      endpointResidueEquiv F K hres x
    rw [hresF, endpointResidueEquiv_apply]
  have hresFpow :
      ((residueUnits F (uF ^ Module.finrank F K) : (ResidueField F)ˣ) :
          ResidueField F) = x ^ Module.finrank F K := by
    rw [map_pow]
    exact congrArg (fun z : ResidueField F => z ^ Module.finrank F K) hresF
  rw [← hresK, residualMulChar_residueUnits K _ (by rfl),
    ← hresFpow, residualMulChar_residueUnits F chi (by omega)]
  have hnorm : normUnits F K (uK : Kˣ) = (uF : Fˣ) ^ Module.finrank F K := by
    apply Units.ext
    change norm F K (algebraMap F K (((uF : unitGroup F) : Fˣ) : F)) =
      (((uF : unitGroup F) : Fˣ) : F) ^ Module.finrank F K
    exact norm_algebraMap F K (((uF : unitGroup F) : Fˣ) : F)
  change (((chi.character.compNorm) (uK : Kˣ) : ℂˣ) : ℂ) =
    ((chi.character ((uF : Fˣ) ^ Module.finrank F K) : ℂˣ) : ℂ)
  rw [ContinuousQuasiChar.compNorm_apply, hnorm, map_pow]

include ht hres hpi hgen in
/-- Under the manuscript's Frobenius-invariant residual normalization, the
two conductor-one Langlands Gauss sums are identical. -/
theorem endpoint_langlandsGaussSum_derivativeGamma
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (htpos : 0 < t) (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi)
    (hfrob : ∀ x : ResidueField F,
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) (x ^ Module.finrank F K) =
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) x) :
    let chiK := endpointIntrinsicNormData F K ht hres pi hpi hgen
      chi hchi htpos
    let psiK := endpointIntrinsicTraceData F K ht hres pi hpi hgen psi
    let gammaK := endpointDerivativeGamma F K ht hres pi hpi hgen
      chi hchi htpos psi gammaF
    let hgammaK : ord K (((gammaK : Kˣ) : K)) =
        ((psiK.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaK.property]
      change (((1 : Int) +
          ((Module.finrank F K : Int) * psi.conductor +
            (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) : Int) :
          WithTop Int) =
        ((((Module.finrank F K : Int) * psi.conductor +
            (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) + 1 : Int) :
          WithTop Int)
      norm_cast
      ring
    let hgammaF : ord F (((gammaF : Fˣ) : F)) =
        ((psi.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaF.property]
      norm_cast
      omega
    langlandsGaussSum (residualMulChar K chiK)
        (residualAddChar K psiK (gammaK : Kˣ) hgammaK) =
      langlandsGaussSum (residualMulChar F chi)
        (residualAddChar F psi (gammaF : Fˣ) hgammaF) := by
  classical
  dsimp only
  let e := endpointResidueEquiv F K hres
  let chiBar := residualMulChar F chi
  let psiBar := residualAddChar F psi (gammaF : Fˣ) (by
    rw [gammaF.property]
    norm_cast
    omega)
  let chiBarK := residualMulChar K
    (endpointIntrinsicNormData F K ht hres pi hpi hgen chi hchi htpos)
  let psiBarK := residualAddChar K
    (endpointIntrinsicTraceData F K ht hres pi hpi hgen psi)
    (endpointDerivativeGamma F K ht hres pi hpi hgen
      chi hchi htpos psi gammaF : Kˣ) (by
        rw [(endpointDerivativeGamma F K ht hres pi hpi hgen
          chi hchi htpos psi gammaF).property]
        change (((1 : Int) +
            ((Module.finrank F K : Int) * psi.conductor +
              (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) : Int) :
            WithTop Int) =
          ((((Module.finrank F K : Int) * psi.conductor +
              (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) + 1 : Int) :
            WithTop Int)
        norm_cast
        ring)
  have htransport (x : ResidueField F) :
      chiBarK⁻¹ (e x) * psiBarK (e x) =
        (chiBar (x ^ Module.finrank F K))⁻¹ * psiBar x := by
    have hmul := endpoint_residualMulChar_compNorm F K ht hres pi hpi hgen
      chi hchi htpos x
    have hadd := endpoint_residualAddChar_derivativeGamma F K ht hres pi hpi hgen
      chi hchi htpos psi gammaF x
    dsimp only at hadd
    change chiBarK⁻¹ (e x) * psiBarK (e x) = _
    rw [MulChar.inv_apply_eq_inv']
    rw [hmul]
    have hadd' : psiBarK (e x) = psiBar x := by
      simpa only [e, endpointResidueEquiv_apply] using hadd
    rw [hadd']
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos pi hpi hgen
  let p := residueCharacteristic F
  letI hpFact : Fact p.Prime := ⟨residueCharacteristic_prime F⟩
  letI : Algebra (ZMod p) (ResidueField F) := ZMod.algebra _ _
  let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (ResidueField F)
  have hsigma (x : ResidueField F) :
      sigma x = x ^ Module.finrank F K := by
    rw [show sigma x = x ^ Fintype.card (ZMod p) by
      exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
        (ZMod p) (ResidueField F)) x]
    simp only [ZMod.card, p, hchar]
  rw [langlandsGaussSum_eq_neg_gaussSum_inv,
    langlandsGaussSum_eq_neg_gaussSum_inv]
  congr 1
  calc
    gaussSum chiBarK⁻¹ psiBarK =
        ∑ x : ResidueField F, chiBarK⁻¹ (e x) * psiBarK (e x) := by
      rw [gaussSum]
      exact (e.toEquiv.sum_comp
        (fun y : ResidueField K ↦ chiBarK⁻¹ y * psiBarK y)).symm
    _ = ∑ x : ResidueField F,
        (chiBar (x ^ Module.finrank F K))⁻¹ * psiBar x := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact htransport x
    _ = ∑ x : ResidueField F, chiBar⁻¹ (sigma x) * psiBar (sigma x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [MulChar.inv_apply_eq_inv', hsigma, hfrob]
    _ = gaussSum chiBar⁻¹ psiBar := by
      rw [gaussSum]
      exact sigma.toEquiv.sum_comp
        (fun x : ResidueField F ↦ chiBar⁻¹ x * psiBar x)

def endpointCanonicalResidualAddChar
    (k : Type*) [Field k] [Finite k] : AddChar k ℂ := by
  let p := ringChar k
  letI hpFact : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI hp0 : NeZero p := ⟨hpFact.out.ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra _ _
  let zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hzeta : IsPrimitiveRoot zeta p := by
    exact Complex.isPrimitiveRoot_exp p hpFact.out.ne_zero
  exact (AddChar.zmodChar p hzeta.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod p) k).toAddMonoidHom

theorem endpointCanonicalResidualAddChar_ne_one
    (k : Type*) [Field k] [Finite k] :
    endpointCanonicalResidualAddChar k ≠ 1 := by
  letI : Fintype k := Fintype.ofFinite k
  let p := ringChar k
  letI hpFact : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI hp0 : NeZero p := ⟨hpFact.out.ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra _ _
  let zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hzeta : IsPrimitiveRoot zeta p := by
    exact Complex.isPrimitiveRoot_exp p hpFact.out.ne_zero
  let psiP : AddChar (ZMod p) ℂ := AddChar.zmodChar p hzeta.pow_eq_one
  have hprim : psiP.IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p hzeta
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate k one_ne_zero
  rw [one_mul] at hb
  intro htriv
  have happ : psiP (Algebra.trace (ZMod p) k b) = 1 := by
    have := DFunLike.congr_fun htriv b
    simp only [endpointCanonicalResidualAddChar, p, hpFact, hp0, zeta,
      psiP, AddChar.compAddMonoidHom_apply, AddChar.one_apply] at this
    change psiP (Algebra.trace (ZMod p) k b) = 1 at this
    exact this
  exact hb ((hprim.zmod_char_eq_one_iff p _).1 happ)

theorem endpointCanonicalResidualAddChar_frobenius
    (k : Type*) [Field k] [Finite k] (x : k) :
    endpointCanonicalResidualAddChar k (x ^ ringChar k) =
      endpointCanonicalResidualAddChar k x := by
  letI : Fintype k := Fintype.ofFinite k
  let p := ringChar k
  letI hpFact : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI hp0 : NeZero p := ⟨hpFact.out.ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra _ _
  let zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hzeta : IsPrimitiveRoot zeta p := by
    exact Complex.isPrimitiveRoot_exp p hpFact.out.ne_zero
  let psiP : AddChar (ZMod p) ℂ := AddChar.zmodChar p hzeta.pow_eq_one
  let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k
  have hsigma : sigma x = x ^ p := by
    rw [show sigma x = x ^ Fintype.card (ZMod p) by
      exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
        (ZMod p) k) x]
    simp only [ZMod.card]
  change endpointCanonicalResidualAddChar k (x ^ p) = _
  rw [← hsigma]
  change psiP (Algebra.trace (ZMod p) k (sigma x)) =
    psiP (Algebra.trace (ZMod p) k x)
  rw [Algebra.trace_eq_of_algEquiv sigma]

end

noncomputable section

open scoped BigOperators

theorem endpoint_langlandsGaussSum_derivativeGamma_normalized
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : Nat} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi)
    (hnormalized :
      residualAddChar F psi (gammaF : Fˣ) (by
        rw [gammaF.property]
        norm_cast
        omega) = endpointCanonicalResidualAddChar (ResidueField F)) :
    let chiK := endpointIntrinsicNormData F K ht hres pi hpi hgen
      chi hchi htpos
    let psiK := endpointIntrinsicTraceData F K ht hres pi hpi hgen psi
    let gammaK := endpointDerivativeGamma F K ht hres pi hpi hgen
      chi hchi htpos psi gammaF
    let hgammaK : ord K (((gammaK : Kˣ) : K)) =
        ((psiK.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaK.property]
      change (((1 : Int) +
          ((Module.finrank F K : Int) * psi.conductor +
            (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) : Int) :
          WithTop Int) =
        ((((Module.finrank F K : Int) * psi.conductor +
            (((Module.finrank F K - 1) * (t + 1) : Nat) : Int)) + 1 : Int) :
          WithTop Int)
      norm_cast
      ring
    let hgammaF : ord F (((gammaF : Fˣ) : F)) =
        ((psi.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaF.property]
      norm_cast
      omega
    @langlandsGaussSum (ResidueField K) _ (residueFieldFintype K)
        (residualMulChar K chiK)
        (residualAddChar K psiK (gammaK : Kˣ) hgammaK) =
      @langlandsGaussSum (ResidueField F) _ (residueFieldFintype F)
        (residualMulChar F chi)
        (residualAddChar F psi (gammaF : Fˣ) hgammaF) := by
  apply endpoint_langlandsGaussSum_derivativeGamma
    F K ht hres pi hpi hgen chi hchi htpos psi gammaF
  intro x
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos pi hpi hgen
  rw [hnormalized]
  simpa only [residueCharacteristic, hchar] using
    endpointCanonicalResidualAddChar_frobenius (ResidueField F) x

/-- Dividing an admissible conductor-one denominator by a local unit
preserves admissibility. -/
def endpointAdmissibleGammaDivUnit
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) (a : unitGroup F) :
    AdmissibleGamma F chi psi :=
  ⟨(gamma : Fˣ) / (a : Fˣ), by
    rw [Units.val_div_eq_div_val, ord_div, gamma.property,
      (mem_unitGroup_iff_ord_eq_zero F (a : Fˣ)).1 a.property]
    simp⟩

@[simp] theorem endpointAdmissibleGammaDivUnit_coe
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) (a : unitGroup F) :
    (endpointAdmissibleGammaDivUnit F chi psi gamma a : Fˣ) =
      (gamma : Fˣ) / (a : Fˣ) := rfl

/-- Dividing the denominator by `a` multiplies the residual input by the
reduction of `a`. -/
theorem residualAddChar_endpointAdmissibleGammaDivUnit
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma : AdmissibleGamma F chi psi) (a : unitGroup F) :
    let gammaA := endpointAdmissibleGammaDivUnit F chi psi gamma a
    let hgamma : ord F (((gamma : Fˣ) : F)) =
        ((psi.conductor + 1 : Int) : WithTop Int) := by
      rw [gamma.property]
      norm_cast
      omega
    let hgammaA : ord F (((gammaA : Fˣ) : F)) =
        ((psi.conductor + 1 : Int) : WithTop Int) := by
      rw [gammaA.property]
      norm_cast
      omega
    residualAddChar F psi (gammaA : Fˣ) hgammaA =
      (residualAddChar F psi (gamma : Fˣ) hgamma).mulShift
        (((residueUnits F a : (ResidueField F)ˣ) : ResidueField F)) := by
  dsimp only
  ext x
  rw [AddChar.mulShift_apply]
  let tx : ringOfIntegers F := teichmuller F x
  have htx : (tx : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 tx.property
  let aO : ringOfIntegers F := unitGroupMulEquivRingOfIntegers F a
  let yO : ringOfIntegers F := aO * tx
  have hy : (yO : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 yO.property
  have hreduceTx : reduce F (tx : F) htx = x := by
    simp [tx, reduce]
  have hreduceY : reduce F (yO : F) hy =
      ((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) * x := by
    change residueMap F yO = _
    simp only [yO, map_mul, residueUnits_coe, aO, tx]
    simp
  nth_rewrite 1 [← hreduceTx]
  rw [residualAddChar_integral_lift,
    ← hreduceY, residualAddChar_integral_lift]
  change (psi.character
      ((tx : F) / ((((gamma : Fˣ) / (a : Fˣ) : Fˣ) : F))) : ℂ) =
    (psi.character ((yO : F) / (((gamma : Fˣ) : F))) : ℂ)
  have hyCoe : (yO : F) = (((a : unitGroup F) : Fˣ) : F) * (tx : F) := by
    simp only [yO, aO]
    rfl
  rw [hyCoe]
  congr 2
  rw [Units.val_div_eq_div_val]
  field_simp

/-- Every conductor-one residual additive character admits the manuscript's
canonical Frobenius-invariant normalization by dividing its denominator by
a local unit. -/
theorem exists_endpointNormalizedAdmissibleGamma
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) :
    ∃ a : unitGroup F,
      let gamma := endpointAdmissibleGammaDivUnit F chi psi gamma0 a
      let hgamma : ord F (((gamma : Fˣ) : F)) =
          ((psi.conductor + 1 : Int) : WithTop Int) := by
        rw [gamma.property]
        norm_cast
        omega
      residualAddChar F psi (gamma : Fˣ) hgamma =
        endpointCanonicalResidualAddChar (ResidueField F) := by
  let hgamma0 : ord F (((gamma0 : Fˣ) : F)) =
      ((psi.conductor + 1 : Int) : WithTop Int) := by
    rw [gamma0.property]
    norm_cast
    omega
  have hpsi0 : residualAddChar F psi (gamma0 : Fˣ) hgamma0 ≠ 1 :=
    residualAddChar_ne_one F psi (gamma0 : Fˣ) hgamma0
  obtain ⟨a, ha⟩ := residual_addChar_normalization F
    (residualAddChar F psi (gamma0 : Fˣ) hgamma0)
    (endpointCanonicalResidualAddChar (ResidueField F)) hpsi0
    (endpointCanonicalResidualAddChar_ne_one (ResidueField F))
  refine ⟨a, ?_⟩
  dsimp only
  rw [residualAddChar_endpointAdmissibleGammaDivUnit
    (F := F) chi hchi psi gamma0 a]
  exact ha

/-- The normalizing local unit selected from residual additive-character
normalization. -/
def endpointNormalizedUnit
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) : unitGroup F :=
  (exists_endpointNormalizedAdmissibleGamma F chi hchi psi gamma0).choose

/-- The chosen admissible denominator whose residual additive character is
the canonical trace character. -/
def endpointNormalizedAdmissibleGamma
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) : AdmissibleGamma F chi psi :=
  endpointAdmissibleGammaDivUnit F chi psi gamma0
    (endpointNormalizedUnit F chi hchi psi gamma0)

theorem endpointNormalizedAdmissibleGamma_residualAddChar
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) :
    residualAddChar F psi
        (endpointNormalizedAdmissibleGamma F chi hchi psi gamma0 : Fˣ) (by
          rw [(endpointNormalizedAdmissibleGamma F chi hchi psi gamma0).property]
          norm_cast
          omega) =
      endpointCanonicalResidualAddChar (ResidueField F) := by
  exact (exists_endpointNormalizedAdmissibleGamma F chi hchi psi gamma0).choose_spec

/-- The derivative denominator upstairs, formed from the chosen normalized
base denominator. -/
def endpointNormalizedDerivativeGamma
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : Nat} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) :
    AdmissibleGamma K
      (endpointIntrinsicNormData F K ht hres pi hpi hgen chi hchi htpos)
      (endpointIntrinsicTraceData F K ht hres pi hpi hgen psi) :=
  endpointDerivativeGamma F K ht hres pi hpi hgen chi hchi htpos psi
    (endpointNormalizedAdmissibleGamma F chi hchi psi gamma0)

/-- For the intrinsically normalized conductor-one denominators, the exact
residue formulas give the upper local-constant ratio without any remaining
Gauss-sum hypothesis. -/
theorem wildEndpointOne_upperRatio_normalized
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : Nat} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (htpos : 0 < t) (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (gamma0 : AdmissibleGamma F chi psi) :
    let gammaF := endpointNormalizedAdmissibleGamma F chi hchi psi gamma0
    let chiK := endpointIntrinsicNormData F K ht hres pi hpi hgen
      chi hchi htpos
    let psiK := endpointIntrinsicTraceData F K ht hres pi hpi hgen psi
    let gammaK := endpointNormalizedDerivativeGamma F K ht htpos hres pi hpi hgen
      chi hchi psi gamma0
    deltaFinite chiK psiK gammaK =
      (chi.character
        (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : Complex) *
        deltaFinite chi psi gammaF := by
  dsimp only
  apply wildEndpointOne_upperRatio_of_residualGauss
    F K ht htpos hres pi hpi hgen chi hchi
      (endpointIntrinsicNormData F K ht hres pi hpi hgen chi hchi htpos)
      rfl rfl psi
      (endpointIntrinsicTraceData F K ht hres pi hpi hgen psi)
      (endpointNormalizedAdmissibleGamma F chi hchi psi gamma0)
      (endpointNormalizedDerivativeGamma F K ht htpos hres pi hpi hgen
        chi hchi psi gamma0)
  exact endpoint_langlandsGaussSum_derivativeGamma_normalized
    F K ht htpos hres pi hpi hgen chi hchi psi
      (endpointNormalizedAdmissibleGamma F chi hchi psi gamma0)
      (endpointNormalizedAdmissibleGamma_residualAddChar F chi hchi psi gamma0)

end

/-- The endpoint derivative is the product of the nonidentity conjugate
differences.  This public wrapper exposes the exact factorization used in
the discriminant congruence. -/
theorem endpointDerivative_eq_prod_nonidentity
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (pi : ringOfIntegers K)
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    endpointDerivative F K pi =
      ∏ sigma ∈ nonidentityGaloisAutomorphisms F K,
        ((pi : K) - sigma (pi : K)) :=
  endpoint_aeval_derivative_minpoly_eq_prod_nonidentity F K pi hgen

end LanglandsFirstMainLemma
