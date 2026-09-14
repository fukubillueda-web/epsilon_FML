import LanglandsFirstMainLemma.Cases.WildEndpoints.Common

/-!
# The wild multiplicative-conductor-zero endpoint
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section WildEndpointZero

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

include ht htwild hres piK hpiK hgen

/-- The First Main Lemma at multiplicative conductor zero in a wildly
ramified cyclic extension of prime degree.  The displayed products range
over the complete norm-character group; in particular their identity term
is present and is evaluated as `1` on the left and as `Δ_F(chiF,psiF)`
on the right. -/
theorem firstMain_wildEndpoint_zero
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F) :
    endpointDelta K
          (wildNormPullbackData F K ht hres piK hpiK hgen chiF (by omega))
          (wildTracePullbackData F K ht hres piK hpiK hgen psiF)
          (wildUpperUniformizer K piK hpiK)
          (by simpa [wildUpperUniformizer] using hpiK) *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu ↦ endpointDelta F
            (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF
            (wildLowerUniformizer F K piK hpiK)
            (wildLowerUniformizer_isUniformizer F K hres piK hpiK)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu ↦ endpointDelta F
          (wildEndpointZeroTwistData F K ht hres piK hpiK hgen
            chiF hchiF mu) psiF
          (wildLowerUniformizer F K piK hpiK)
          (wildLowerUniformizer_isUniformizer F K hres piK hpiK)) := by
  classical
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
  let S := ramifiedNormCharacterFinset F K ht hres piK hpiK hgen
  let normDelta : NormCharacter F K → ℂ := fun mu ↦ endpointDelta F
    (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF piF hpiF
  let twistDelta : NormCharacter F K → ℂ := fun mu ↦ endpointDelta F
    (wildEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF mu)
      psiF piF hpiF
  let exponent : NormCharacter F K → ℤ := fun mu ↦
    ((wildNormCharacterData F K ht hres piK hpiK hgen mu).conductor : ℤ) +
      psiF.conductor
  have hupper : endpointDelta K chiK psiK piKU hpiKU =
      endpointCharacterPower F chiF piF
        ((Module.finrank F K : ℤ) * psiF.conductor +
          (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) := by
    rw [endpointDelta_conductor_zero K chiK (by simp [chiK, hchiF])]
    have hchar : chiK.character piKU = chiF.character piF := by
      change chiF.character.compNorm piKU = chiF.character piF
      rfl
    rw [show endpointCharacterPower K chiK piKU psiK.conductor =
        endpointCharacterPower F chiF piF psiK.conductor by
      simp only [endpointCharacterPower]
      rw [hchar]]
    rfl
  have hpoint (mu : NormCharacter F K) :
      twistDelta mu = endpointCharacterPower F chiF piF (exponent mu) *
        normDelta mu := by
    exact endpointDelta_wildEndpointZeroTwist F K ht hres piK hpiK hgen
      chiF hchiF psiF mu
  have htwistProduct : S.prod twistDelta =
      endpointCharacterPower F chiF piF
          ((Module.finrank F K : ℤ) * psiF.conductor +
            (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) *
        S.prod normDelta := by
    calc
      S.prod twistDelta =
          S.prod (fun mu ↦ endpointCharacterPower F chiF piF (exponent mu) *
            normDelta mu) := by
        apply Finset.prod_congr rfl
        intro mu _hmu
        exact hpoint mu
      _ = S.prod (fun mu ↦ endpointCharacterPower F chiF piF (exponent mu)) *
          S.prod normDelta := Finset.prod_mul_distrib
      _ = endpointCharacterPower F chiF piF (S.sum exponent) *
          S.prod normDelta := by
        rw [endpointCharacterPower_finsetSum]
      _ = _ := by
        rw [show S.sum exponent =
            (Module.finrank F K : ℤ) * psiF.conductor +
              (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) by
          exact wildEndpointZero_totalExponent F K ht hres piK hpiK hgen
            psiF.conductor]
  change endpointDelta K chiK psiK piKU hpiKU * S.prod normDelta =
    S.prod twistDelta
  rw [hupper, htwistProduct]

end WildEndpointZero

end

end LanglandsFirstMainLemma
