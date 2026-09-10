import LanglandsFirstMainLemma.Parameters.RamifiedHasseComparison
import LanglandsFirstMainLemma.FiniteField.HasseDavenportProduct
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Delta.ResidueFormula

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section EndpointBasics

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

def tameOddUniformizerGamma
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    AdmissibleGamma E chi psi :=
  ⟨pi ^ ((chi.conductor : ℤ) + psi.conductor), by
    rw [Units.val_zpow_eq_zpow_val, ord_uniformizer_zpow E hpi]⟩

@[simp] theorem tameOddUniformizerGamma_coe
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    (tameOddUniformizerGamma E chi psi pi hpi : Eˣ) =
      pi ^ ((chi.conductor : ℤ) + psi.conductor) :=
  rfl

def tameOddEndpointDelta
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) : ℂ :=
  deltaFinite chi psi (tameOddUniformizerGamma E chi psi pi hpi)

private def tameOddCharacterPower
    (chi : LocalQuasiCharData E) (pi : Eˣ) (a : ℤ) : ℂ :=
  (((chi.character pi) ^ a : ℂˣ) : ℂ)

private theorem tameOddCharacterPower_add
    (chi : LocalQuasiCharData E) (pi : Eˣ) (a b : ℤ) :
    tameOddCharacterPower E chi pi (a + b) =
      tameOddCharacterPower E chi pi a * tameOddCharacterPower E chi pi b := by
  simp [tameOddCharacterPower, zpow_add₀]

private theorem tameOddCharacterPower_finsetSum
    {I : Type*} (s : Finset I) (chi : LocalQuasiCharData E) (pi : Eˣ)
    (a : I → ℤ) :
    s.prod (fun i ↦ tameOddCharacterPower E chi pi (a i)) =
      tameOddCharacterPower E chi pi (s.sum a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tameOddCharacterPower]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        tameOddCharacterPower_add]

private theorem tameOddEndpointDelta_conductor_zero
    (chi : LocalQuasiCharData E) (hchi : chi.conductor = 0)
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    tameOddEndpointDelta E chi psi pi hpi =
      tameOddCharacterPower E chi pi psi.conductor := by
  rw [tameOddEndpointDelta, deltaFinite_conductor_zero E chi hchi]
  change ((chi.character
      (pi ^ ((chi.conductor : ℤ) + psi.conductor)) : ℂˣ) : ℂ) = _
  rw [hchi]
  norm_num [tameOddCharacterPower, map_zpow]

@[simp] private theorem tameOddEndpointDelta_trivial
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    tameOddEndpointDelta E (trivialQuasiCharData E) psi pi hpi = 1 :=
  delta_trivial_character E psi
    (tameOddUniformizerGamma E (trivialQuasiCharData E) psi pi hpi)

private abbrev tameOddUnramifiedTwistData
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor) :
    LocalQuasiCharData E where
  character := theta.character * nu.character
  conductor := theta.conductor
  isConductor := theta.isConductor.mul_of_gt nu.isConductor (by omega)

private def tameOddUnramifiedTwistGamma
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    AdmissibleGamma E (tameOddUnramifiedTwistData E theta nu hnu htheta) psi :=
  ⟨Gamma, by simpa using Gamma.property⟩

@[simp] private theorem tameOddUnramifiedTwistGamma_coe
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    (tameOddUnramifiedTwistGamma E theta nu hnu htheta psi Gamma : Eˣ) =
      (Gamma : Eˣ) :=
  rfl

private theorem tameOddFiniteGaussSum_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    finiteGaussSum (tameOddUnramifiedTwistData E theta nu hnu htheta) psi
        (tameOddUnramifiedTwistGamma E theta nu hnu htheta psi Gamma) =
      finiteGaussSum theta psi Gamma := by
  letI := unitFiltrationQuotientFintype E (Nat.zero_le theta.conductor)
  change (∑ z : UnitFiltrationQuotient E 0 theta.conductor (Nat.zero_le _),
      finiteGaussSummand (tameOddUnramifiedTwistData E theta nu hnu htheta) psi
        (tameOddUnramifiedTwistGamma E theta nu hnu htheta psi Gamma) z) =
    ∑ z : UnitFiltrationQuotient E 0 theta.conductor (Nat.zero_le _),
      finiteGaussSummand theta psi Gamma z
  apply Finset.sum_congr rfl
  intro z _hz
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective E (Nat.zero_le theta.conductor) z
  rw [finiteGaussSummand_mk, finiteGaussSummand_mk]
  have hnuUnit : nu.character (u : Eˣ) = 1 := by
    apply nu.isConductor.trivial
    simpa only [hnu] using u.property
  simp only [finiteGaussSummandRepresentative,
    tameOddUnramifiedTwistGamma_coe,
    ContinuousQuasiChar.mul_apply, hnuUnit, mul_one]

private theorem tameOddDeltaFinite_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E) (Gamma : AdmissibleGamma E theta psi) :
    deltaFinite (tameOddUnramifiedTwistData E theta nu hnu htheta) psi
        (tameOddUnramifiedTwistGamma E theta nu hnu htheta psi Gamma) =
      (nu.character (Gamma : Eˣ) : ℂ) * deltaFinite theta psi Gamma := by
  rw [deltaFinite, deltaFinite,
    tameOddFiniteGaussSum_unramifiedTwist E theta nu hnu htheta psi Gamma]
  have hvalue :
      (((tameOddUnramifiedTwistData E theta nu hnu htheta).character
        (tameOddUnramifiedTwistGamma E theta nu hnu htheta psi Gamma : Eˣ) :
          ℂˣ) : ℂ) =
        (theta.character (Gamma : Eˣ) : ℂ) *
          (nu.character (Gamma : Eˣ) : ℂ) := by
    exact congrArg Units.val
      (ContinuousQuasiChar.mul_apply theta.character nu.character (Gamma : Eˣ))
  rw [hvalue]
  ring

private theorem tameOddEndpointDelta_unramifiedTwist
    (theta nu : LocalQuasiCharData E)
    (hnu : nu.conductor = 0) (htheta : 0 < theta.conductor)
    (psi : LocalAddCharData E)
    (pi : Eˣ) (hpi : (ValuativeRel.valuation E).IsUniformizer (pi : E)) :
    tameOddEndpointDelta E (tameOddUnramifiedTwistData E theta nu hnu htheta)
        psi pi hpi =
      tameOddCharacterPower E nu pi
          ((theta.conductor : ℤ) + psi.conductor) *
        tameOddEndpointDelta E theta psi pi hpi := by
  have hGamma :
      tameOddUniformizerGamma E
          (tameOddUnramifiedTwistData E theta nu hnu htheta) psi pi hpi =
        tameOddUnramifiedTwistGamma E theta nu hnu htheta psi
          (tameOddUniformizerGamma E theta psi pi hpi) := by
    apply Subtype.ext
    rfl
  rw [tameOddEndpointDelta, hGamma]
  simpa [tameOddEndpointDelta, tameOddCharacterPower, map_zpow] using
    (tameOddDeltaFinite_unramifiedTwist E theta nu hnu htheta psi
      (tameOddUniformizerGamma E theta psi pi hpi))

end EndpointBasics

section TameZero

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

def tameOddUpperUniformizer : Kˣ :=
  Units.mk0 (piK : K) hpiK.ne_zero

def tameOddLowerUniformizer : Fˣ :=
  normUnits F K (tameOddUpperUniformizer K piK hpiK)

omit [Module.Free F K] [PrimeCyclicExtension F K] in
include hres in
theorem tameOddLowerUniformizer_isUniformizer :
    (ValuativeRel.valuation F).IsUniformizer
      ((tameOddLowerUniformizer F K piK hpiK : Fˣ) : F) := by
  rw [← ord_eq_one_iff_isUniformizer]
  change ord F (norm F K (piK : K)) = 1
  rw [ord_norm, hres, one_nsmul, ord_uniformizer K hpiK]

def tameOddTracePullbackData (psiF : LocalAddCharData F) :
    LocalAddCharData K where
  character := psiF.character.compTrace
  conductor :=
    (Module.finrank F K : ℤ) * psiF.conductor +
      ((Module.finrank F K - 1 : ℕ) : ℤ)
  isConductor := by
    simpa using additiveConductor_compTrace_cyclicPrime
      F K ht hres piK hpiK hgen psiF.isConductor

def tameOddNormPullbackZeroData
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0) :
    LocalQuasiCharData K where
  character := chiF.character.compNorm
  conductor := 0
  isConductor := multiplicativeConductor_compNorm_belowBreak
    F K ht hres piK hpiK hgen (by omega) (by simpa [hchiF] using chiF.isConductor)

def tameOddNormCharacterData (mu : NormCharacter F K) :
    LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact trivialQuasiCharData F
  · exact
      { character := mu.1
        conductor := 1
        isConductor := tameNormCharacter_conductor
          F K ht hres piK hpiK hgen mu hmu }

@[simp] private theorem tameOddNormCharacterData_one :
    tameOddNormCharacterData F K ht hres piK hpiK hgen
      (1 : NormCharacter F K) = trivialQuasiCharData F := by
  simp [tameOddNormCharacterData]

private theorem tameOddNormCharacterData_of_ne
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor = 1 := by
  simp [tameOddNormCharacterData, hmu]

private theorem tameOddNormCharacterData_character
    (mu : NormCharacter F K) :
    (tameOddNormCharacterData F K ht hres piK hpiK hgen mu).character = mu.1 := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    ext x
    simp [tameOddNormCharacterData]
  · simp [tameOddNormCharacterData, hmu]

def tameOddEndpointZeroTwistData
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (mu : NormCharacter F K) : LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact chiF
  · exact tameOddUnramifiedTwistData F
      (tameOddNormCharacterData F K ht hres piK hpiK hgen mu)
      chiF hchiF (by rw [tameOddNormCharacterData_of_ne
        F K ht hres piK hpiK hgen mu hmu]; omega)

@[simp] private theorem tameOddEndpointZeroTwistData_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0) :
    tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF 1 = chiF := by
  simp [tameOddEndpointZeroTwistData]

private theorem tameOddEndpointZeroTwistData_character
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (mu : NormCharacter F K) :
    (tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen
      chiF hchiF mu).character = mu.1 * chiF.character := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    simp only [tameOddEndpointZeroTwistData, ↓reduceDIte]
    exact (one_mul chiF.character).symm
  · simp [tameOddEndpointZeroTwistData, hmu,
      tameOddUnramifiedTwistData, tameOddNormCharacterData_character]

private theorem tameOddEndpointDelta_zeroTwist
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F)
    (mu : NormCharacter F K) :
    tameOddEndpointDelta F
        (tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen
          chiF hchiF mu) psiF
        (tameOddLowerUniformizer F K piK hpiK)
        (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK) =
      tameOddCharacterPower F chiF (tameOddLowerUniformizer F K piK hpiK)
          (((tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor : ℤ) +
            psiF.conductor) *
        tameOddEndpointDelta F
          (tameOddNormCharacterData F K ht hres piK hpiK hgen mu) psiF
          (tameOddLowerUniformizer F K piK hpiK)
          (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK) := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    rw [tameOddEndpointZeroTwistData_one, tameOddNormCharacterData_one,
      tameOddEndpointDelta_trivial, mul_one,
      tameOddEndpointDelta_conductor_zero F chiF hchiF]
    simp [tameOddCharacterPower]
  · rw [show tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen
        chiF hchiF mu =
        tameOddUnramifiedTwistData F
          (tameOddNormCharacterData F K ht hres piK hpiK hgen mu) chiF hchiF
          (by rw [tameOddNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu];
              omega) by
        simp [tameOddEndpointZeroTwistData, hmu]]
    simpa only using tameOddEndpointDelta_unramifiedTwist F
      (tameOddNormCharacterData F K ht hres piK hpiK hgen mu) chiF hchiF
      (by rw [tameOddNormCharacterData_of_ne F K ht hres piK hpiK hgen mu hmu]; omega)
      psiF (tameOddLowerUniformizer F K piK hpiK)
      (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK)

private theorem tameOddNormCharacter_conductor_sum :
    (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).sum
        (fun mu ↦
          (tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor) =
      Module.finrank F K - 1 := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let S := ramifiedNormCharacterFinset F K ht hres piK hpiK hgen
  have honeMem : (1 : NormCharacter F K) ∈ S := by
    simp [S, ramifiedNormCharacterFinset, normCharacterFinset]
  have hSCard : S.card = Module.finrank F K := by
    simpa [S, ramifiedNormCharacterFinset, normCharacterFinset,
      Nat.card_eq_fintype_card] using
      ramifiedNormCharacter_card F K ht hres piK hpiK hgen
  have hcard : (S.erase 1).card = Module.finrank F K - 1 := by
    rw [Finset.card_erase_of_mem honeMem, hSCard]
  calc
    S.sum (fun mu ↦
        (tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor) =
        (S.erase 1).sum (fun _ ↦ 1) := by
      rw [← Finset.sum_erase_add _ _ honeMem]
      simp only [tameOddNormCharacterData_one]
      change (S.erase 1).sum (fun mu ↦
        (tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor) + 0 = _
      rw [add_zero]
      apply Finset.sum_congr rfl
      intro mu hmu
      exact tameOddNormCharacterData_of_ne F K ht hres piK hpiK hgen mu
        (Finset.ne_of_mem_erase hmu)
    _ = (S.erase 1).card := by simp
    _ = Module.finrank F K - 1 := hcard

private theorem tameOddEndpointZero_totalExponent (n : ℤ) :
    (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).sum
        (fun mu ↦
          ((tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor : ℤ) + n) =
      (Module.finrank F K : ℤ) * n + ((Module.finrank F K - 1 : ℕ) : ℤ) := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hSCard :
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).card =
        Module.finrank F K := by
    simpa [ramifiedNormCharacterFinset, normCharacterFinset,
      Nat.card_eq_fintype_card] using
      ramifiedNormCharacter_card F K ht hres piK hpiK hgen
  rw [hSCard]
  norm_cast
  rw [tameOddNormCharacter_conductor_sum F K ht hres piK hpiK hgen]
  ring

/-- Exact tame `m=0` assembly.  The complete norm-character
group is retained, the identity contributes conductor zero, every other index
contributes conductor one, and the total exponent is exactly
`ell*n + ell-1`. -/
theorem firstMain_tameOdd_zero
    (_hodd : Odd (Module.finrank F K))
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 0)
    (psiF : LocalAddCharData F) :
    tameOddEndpointDelta K
          (tameOddNormPullbackZeroData F K ht hres piK hpiK hgen chiF hchiF)
          (tameOddTracePullbackData F K ht hres piK hpiK hgen psiF)
          (tameOddUpperUniformizer K piK hpiK)
          (by simpa [tameOddUpperUniformizer] using hpiK) *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu ↦ tameOddEndpointDelta F
            (tameOddNormCharacterData F K ht hres piK hpiK hgen mu) psiF
            (tameOddLowerUniformizer F K piK hpiK)
            (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu ↦ tameOddEndpointDelta F
          (tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen
            chiF hchiF mu) psiF
          (tameOddLowerUniformizer F K piK hpiK)
          (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK)) := by
  classical
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres piK hpiK hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let piKU : Kˣ := tameOddUpperUniformizer K piK hpiK
  let piF : Fˣ := tameOddLowerUniformizer F K piK hpiK
  let hpiKU : (ValuativeRel.valuation K).IsUniformizer (piKU : K) := by
    simpa [piKU, tameOddUpperUniformizer] using hpiK
  let hpiF : (ValuativeRel.valuation F).IsUniformizer (piF : F) :=
    tameOddLowerUniformizer_isUniformizer F K hres piK hpiK
  let chiK := tameOddNormPullbackZeroData F K ht hres piK hpiK hgen chiF hchiF
  let psiK := tameOddTracePullbackData F K ht hres piK hpiK hgen psiF
  let S := ramifiedNormCharacterFinset F K ht hres piK hpiK hgen
  let normDelta : NormCharacter F K → ℂ := fun mu ↦ tameOddEndpointDelta F
    (tameOddNormCharacterData F K ht hres piK hpiK hgen mu) psiF piF hpiF
  let twistDelta : NormCharacter F K → ℂ := fun mu ↦ tameOddEndpointDelta F
    (tameOddEndpointZeroTwistData F K ht hres piK hpiK hgen chiF hchiF mu)
      psiF piF hpiF
  let exponent : NormCharacter F K → ℤ := fun mu ↦
    ((tameOddNormCharacterData F K ht hres piK hpiK hgen mu).conductor : ℤ) +
      psiF.conductor
  have hupper : tameOddEndpointDelta K chiK psiK piKU hpiKU =
      tameOddCharacterPower F chiF piF
        ((Module.finrank F K : ℤ) * psiF.conductor +
          ((Module.finrank F K - 1 : ℕ) : ℤ)) := by
    rw [tameOddEndpointDelta_conductor_zero K chiK (by rfl)]
    have hchar : chiK.character piKU = chiF.character piF := by
      change chiF.character.compNorm piKU = chiF.character piF
      rfl
    rw [show tameOddCharacterPower K chiK piKU psiK.conductor =
        tameOddCharacterPower F chiF piF psiK.conductor by
      simp only [tameOddCharacterPower]
      rw [hchar]]
    rfl
  have hpoint (mu : NormCharacter F K) :
      twistDelta mu = tameOddCharacterPower F chiF piF (exponent mu) *
        normDelta mu := by
    exact tameOddEndpointDelta_zeroTwist F K ht hres piK hpiK hgen
      chiF hchiF psiF mu
  have htwistProduct : S.prod twistDelta =
      tameOddCharacterPower F chiF piF
          ((Module.finrank F K : ℤ) * psiF.conductor +
            ((Module.finrank F K - 1 : ℕ) : ℤ)) *
        S.prod normDelta := by
    calc
      S.prod twistDelta =
          S.prod (fun mu ↦ tameOddCharacterPower F chiF piF (exponent mu) *
            normDelta mu) := by
        apply Finset.prod_congr rfl
        intro mu _hmu
        exact hpoint mu
      _ = S.prod (fun mu ↦ tameOddCharacterPower F chiF piF (exponent mu)) *
          S.prod normDelta := Finset.prod_mul_distrib
      _ = tameOddCharacterPower F chiF piF (S.sum exponent) *
          S.prod normDelta := by
        rw [tameOddCharacterPower_finsetSum]
      _ = _ := by
        rw [show S.sum exponent =
            (Module.finrank F K : ℤ) * psiF.conductor +
              ((Module.finrank F K - 1 : ℕ) : ℤ) by
          exact tameOddEndpointZero_totalExponent F K ht hres piK hpiK hgen
            psiF.conductor]
  change tameOddEndpointDelta K chiK psiK piKU hpiKU * S.prod normDelta =
    S.prod twistDelta
  rw [hupper, htwistProduct]

end TameZero

end

end LanglandsFirstMainLemma

open scoped BigOperators

namespace LanglandsFirstMainLemma

open Finset

section PhaseProduct

private theorem phase_finset_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    phase (∏ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact phase_of_norm_eq_one (by simp)
  | @insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi ↦
        hf i (Finset.mem_insert_of_mem hi)
      have hprod : (∏ i ∈ s, f i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr hfs
      rw [Finset.prod_insert ha, phase_mul hfa hprod,
        Finset.prod_insert ha, ih hfs]

end PhaseProduct

section HasseDavenportPhase

variable {k : Type} [Field k] [Fintype k]

/--
The phase-only form of Hasse--Davenport needed in the conductor-one tame-odd
assembly.  The degree-scaling factor remains *inside* the upper phase, which
is exactly what the conductor-one residue formula produces after identifying
the upper residual additive character with `x \mapsto psi (ell * x)`.
-/
theorem hasseDavenportProduct_phase
    (ell : ℕ) (hdiv : ell ∣ Fintype.card k - 1)
    (eta chi : FiniteMulChar k) (heta : orderOf eta = ell)
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1) :
    phase
          ((chi ((ell : k) ^ ell) : ℂ) *
            langlandsGaussSum (chi ^ ell) psi) *
        (∏ j ∈ Finset.Icc 1 (ell - 1),
          phase (langlandsGaussSum (eta ^ j) psi)) =
      phase (langlandsGaussSum chi psi) *
        ∏ j ∈ Finset.Icc 1 (ell - 1),
          phase (langlandsGaussSum (chi * eta ^ j) psi) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (ell - 1)
  let Tchi : ℂ := langlandsGaussSum chi psi
  let TchiEll : ℂ := langlandsGaussSum (chi ^ ell) psi
  let Pchi : ℂ :=
    ∏ j ∈ S, langlandsGaussSum (chi * eta ^ j) psi
  let Peta : ℂ :=
    ∏ j ∈ S, langlandsGaussSum (eta ^ j) psi
  let C : ℂ := chi ((ell : k) ^ ell)
  have hTchi : Tchi ≠ 0 :=
    langlandsGaussSum_ne_zero chi hpsi
  have hTchiEll : TchiEll ≠ 0 :=
    langlandsGaussSum_ne_zero (chi ^ ell) hpsi
  have hPchi : Pchi ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      langlandsGaussSum_ne_zero (chi * eta ^ j) hpsi
  have hPeta : Peta ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      langlandsGaussSum_ne_zero (eta ^ j) hpsi
  have hHD : C * TchiEll * Peta = Tchi * Pchi := by
    simpa [C, TchiEll, Peta, Tchi, Pchi, S] using
      hasseDavenportProduct ell hdiv eta chi heta psi hpsi
  have hleft : C * TchiEll * Peta ≠ 0 := by
    rw [hHD]
    exact mul_ne_zero hTchi hPchi
  have hCTchiEll : C * TchiEll ≠ 0 := by
    exact (mul_ne_zero_iff.mp hleft).1
  have hphasePeta :
      phase Peta = ∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi) := by
    exact phase_finset_prod S
      (fun j ↦ langlandsGaussSum (eta ^ j) psi)
      (fun j _ ↦ langlandsGaussSum_ne_zero (eta ^ j) hpsi)
  have hphasePchi :
      phase Pchi =
        ∏ j ∈ S, phase (langlandsGaussSum (chi * eta ^ j) psi) := by
    exact phase_finset_prod S
      (fun j ↦ langlandsGaussSum (chi * eta ^ j) psi)
      (fun j _ ↦ langlandsGaussSum_ne_zero (chi * eta ^ j) hpsi)
  change phase (C * TchiEll) *
      (∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi)) =
    phase Tchi *
      ∏ j ∈ S, phase (langlandsGaussSum (chi * eta ^ j) psi)
  calc
    phase (C * TchiEll) *
          (∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi)) =
        phase (C * TchiEll) * phase Peta := by rw [hphasePeta]
    _ = phase (C * TchiEll * Peta) :=
      (phase_mul hCTchiEll hPeta).symm
    _ = phase (Tchi * Pchi) := by rw [hHD]
    _ = phase Tchi * phase Pchi := phase_mul hTchi hPchi
    _ = phase Tchi *
          ∏ j ∈ S, phase (langlandsGaussSum (chi * eta ^ j) psi) := by
      rw [hphasePchi]

end HasseDavenportPhase

section DeltaAssembly

variable {k : Type} [Field k] [Fintype k]

/--
Endpoint data supplied by four applications of `deltaFinite_conductor_one`:

* `upperDelta` is the extension-field endpoint;
* `normDelta j` is the local constant of the nonidentity norm character;
* `baseDelta` is the identity (`j = 0`) twist;
* `twistDelta j` is the nonidentity twist.

The field `scalar` is the common value `chi_F Gamma`.  Keeping the equations
as fields lets local residue-field comparison code instantiate this structure
without choosing any hidden representative here.
-/
structure TameOddConductorOneDeltaData
    (ell : ℕ) (eta chi : FiniteMulChar k) (psi : FiniteAddChar k) where
  scalar : ℂ
  upperDelta : ℂ
  normDelta : ℕ → ℂ
  baseDelta : ℂ
  twistDelta : ℕ → ℂ
  upper_formula :
    upperDelta =
      -(scalar ^ ell) *
        phase
          ((chi ((ell : k) ^ ell) : ℂ) *
            langlandsGaussSum (chi ^ ell) psi)
  norm_formula : ∀ j ∈ Finset.Icc 1 (ell - 1),
    normDelta j = -phase (langlandsGaussSum (eta ^ j) psi)
  base_formula :
    baseDelta = -scalar * phase (langlandsGaussSum chi psi)
  twist_formula : ∀ j ∈ Finset.Icc 1 (ell - 1),
    twistDelta j =
      -scalar * phase (langlandsGaussSum (chi * eta ^ j) psi)

/--
Exact conductor-one endpoint assembly.  There is one leading minus sign on
each side and exactly `ell - 1` nonidentity factors on each side.  The same
`scalar ^ ell` occurs on both sides, while Hasse--Davenport supplies the
positive degree-scaling factor `chi (ell ^ ell)` in the upper Gauss phase.
-/
theorem TameOddConductorOneDeltaData.product_identity
    (ell : ℕ) (hdiv : ell ∣ Fintype.card k - 1)
    (eta chi : FiniteMulChar k) (heta : orderOf eta = ell)
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1)
    (D : TameOddConductorOneDeltaData ell eta chi psi) :
    D.upperDelta *
        (∏ j ∈ Finset.Icc 1 (ell - 1), D.normDelta j) =
      D.baseDelta *
        ∏ j ∈ Finset.Icc 1 (ell - 1), D.twistDelta j := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (ell - 1)
  have hellpos : 0 < ell := by
    simpa [← heta] using orderOf_pos eta
  have hcard : S.card = ell - 1 := by
    dsimp [S]
    simp
  have hnormProduct :
      (∏ j ∈ S, D.normDelta j) =
        (-1 : ℂ) ^ S.card *
          ∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi) := by
    calc
      (∏ j ∈ S, D.normDelta j) =
          ∏ j ∈ S, -phase (langlandsGaussSum (eta ^ j) psi) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact D.norm_formula j hj
      _ = (-1 : ℂ) ^ S.card *
          ∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi) := by
        rw [Finset.prod_neg]
  have htwistProduct :
      (∏ j ∈ S, D.twistDelta j) =
        (-D.scalar) ^ S.card *
          ∏ j ∈ S,
            phase (langlandsGaussSum (chi * eta ^ j) psi) := by
    calc
      (∏ j ∈ S, D.twistDelta j) =
          ∏ j ∈ S,
            (-D.scalar) *
              phase (langlandsGaussSum (chi * eta ^ j) psi) := by
        apply Finset.prod_congr rfl
        intro j hj
        simpa only [neg_mul] using D.twist_formula j hj
      _ = (-D.scalar) ^ S.card *
          ∏ j ∈ S,
            phase (langlandsGaussSum (chi * eta ^ j) psi) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hphase :=
    hasseDavenportProduct_phase ell hdiv eta chi heta psi hpsi
  have hphaseS :
      phase
            ((chi ((ell : k) ^ ell) : ℂ) *
              langlandsGaussSum (chi ^ ell) psi) *
          (∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi)) =
        phase (langlandsGaussSum chi psi) *
          ∏ j ∈ S,
            phase (langlandsGaussSum (chi * eta ^ j) psi) := by
    simpa [S] using hphase
  have hscalarPow : D.scalar ^ ell = D.scalar * D.scalar ^ (ell - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hnegPow :
      (-D.scalar) ^ (ell - 1) =
        (-1 : ℂ) ^ (ell - 1) * D.scalar ^ (ell - 1) := by
    rw [show -D.scalar = (-1 : ℂ) * D.scalar by ring, mul_pow]
  change D.upperDelta * (∏ j ∈ S, D.normDelta j) =
    D.baseDelta * ∏ j ∈ S, D.twistDelta j
  rw [D.upper_formula, D.base_formula, hnormProduct, htwistProduct,
    hcard, hscalarPow, hnegPow]
  calc
    -(D.scalar * D.scalar ^ (ell - 1)) *
          phase
            ((chi ((ell : k) ^ ell) : ℂ) *
              langlandsGaussSum (chi ^ ell) psi) *
          ((-1 : ℂ) ^ (ell - 1) *
            ∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi)) =
        (-D.scalar * (-1 : ℂ) ^ (ell - 1) *
            D.scalar ^ (ell - 1)) *
          (phase
              ((chi ((ell : k) ^ ell) : ℂ) *
                langlandsGaussSum (chi ^ ell) psi) *
            ∏ j ∈ S, phase (langlandsGaussSum (eta ^ j) psi)) := by
      ring
    _ = (-D.scalar * (-1 : ℂ) ^ (ell - 1) *
            D.scalar ^ (ell - 1)) *
          (phase (langlandsGaussSum chi psi) *
            ∏ j ∈ S,
              phase (langlandsGaussSum (chi * eta ^ j) psi)) := by
      rw [hphaseS]
    _ = -D.scalar * phase (langlandsGaussSum chi psi) *
          ((-1 : ℂ) ^ (ell - 1) * D.scalar ^ (ell - 1) *
            ∏ j ∈ S,
              phase (langlandsGaussSum (chi * eta ^ j) psi)) := by
      ring

end DeltaAssembly

section FullNormCharacterProduct

private theorem prod_multiplicative_zmod_eq_head_mul_Icc
    {M : Type*} [CommMonoid M] (ell : ℕ) [NeZero ell] (hell : 0 < ell)
    (f : Multiplicative (ZMod ell) → M) :
    (∏ j : Multiplicative (ZMod ell), f j) =
      f (Multiplicative.ofAdd (0 : ZMod ell)) *
        ∏ j ∈ Finset.Icc 1 (ell - 1),
          f (Multiplicative.ofAdd (j : ZMod ell)) := by
  classical
  let e : Fin ell ≃ Multiplicative (ZMod ell) :=
    (ZMod.finEquiv ell).toEquiv.trans Multiplicative.ofAdd
  have hrange :
      Finset.range ell = insert 0 (Finset.Icc 1 (ell - 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have he (i : Fin ell) :
      e i = Multiplicative.ofAdd (i.val : ZMod ell) := by
    dsimp [e]
    apply congrArg Multiplicative.ofAdd
    rcases ell with _ | ell
    · exact (NeZero.ne 0 rfl).elim
    · change i = (i.val : ZMod (ell + 1))
      apply Fin.ext
      exact (ZMod.val_natCast_of_lt i.isLt).symm
  have hzero : 0 ∉ Finset.Icc 1 (ell - 1) := by simp
  calc
    (∏ j : Multiplicative (ZMod ell), f j) =
        ∏ i : Fin ell, f (e i) :=
      (Equiv.prod_comp e f).symm
    _ = ∏ i : Fin ell,
          f (Multiplicative.ofAdd (i.val : ZMod ell)) := by
      apply Fintype.prod_congr
      intro i
      rw [he]
    _ = ∏ j ∈ Finset.range ell,
          f (Multiplicative.ofAdd (j : ZMod ell)) := by
      exact Fin.prod_univ_eq_prod_range
        (fun j ↦ f (Multiplicative.ofAdd (j : ZMod ell))) ell
    _ = f (Multiplicative.ofAdd (0 : ZMod ell)) *
        ∏ j ∈ Finset.Icc 1 (ell - 1),
          f (Multiplicative.ofAdd (j : ZMod ell)) := by
      rw [hrange, Finset.prod_insert hzero]
      simp

variable {k : Type} [Field k] [Fintype k]

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

/--
Full norm-character wrapper for the conductor-one Hasse--Davenport row.

The two functions are intended to be instantiated by the actual expressions
`deltaFinite (muData mu) psiF (gammaNorm mu)` and
`deltaFinite (twistData mu) psiF (gammaTwist mu)`.  The hypotheses identify
their identity and nonidentity rows with the four explicit conductor-one
formulas in `D`; this theorem performs all aggregate reindexing itself.
-/
theorem TameOddConductorOneDeltaData.full_normCharacter_product
    (eta chi : FiniteMulChar k) (psi : FiniteAddChar k)
    (hdiv : Module.finrank F K ∣ Fintype.card k - 1)
    (heta : orderOf eta = Module.finrank F K)
    (hpsi : psi ≠ 1)
    (D : TameOddConductorOneDeltaData
      (Module.finrank F K) eta chi psi)
    (upperEndpoint : ℂ)
    (normEndpoint twistEndpoint : NormCharacter F K → ℂ)
    (hupper : upperEndpoint = D.upperDelta)
    (hnormIdentity : normEndpoint 1 = 1)
    (htwistIdentity : twistEndpoint 1 = D.baseDelta)
    (hnormRows : ∀ j ∈ Finset.Icc 1 (Module.finrank F K - 1),
      normEndpoint
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))) =
        D.normDelta j)
    (htwistRows : ∀ j ∈ Finset.Icc 1 (Module.finrank F K - 1),
      twistEndpoint
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))) =
        D.twistDelta j) :
    upperEndpoint *
        (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
          normEndpoint =
      (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
        twistEndpoint := by
  classical
  let ell := Module.finrank F K
  let e := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
  have hellpos : 0 < ell := Module.finrank_pos
  letI : NeZero ell := ⟨hellpos.ne'⟩
  have hnormReindex :=
    ramifiedNormCharacterProduct_eq_zmodProduct F K ht hres pi hpi hgen
      normEndpoint
  have htwistReindex :=
    ramifiedNormCharacterProduct_eq_zmodProduct F K ht hres pi hpi hgen
      twistEndpoint
  have hnormSplit :
      (∏ j : Multiplicative (ZMod ell), normEndpoint (e j)) =
        normEndpoint 1 *
          ∏ j ∈ Finset.Icc 1 (ell - 1),
            normEndpoint
              (e (Multiplicative.ofAdd (j : ZMod ell))) := by
    rw [prod_multiplicative_zmod_eq_head_mul_Icc ell hellpos]
    rw [show e (Multiplicative.ofAdd (0 : ZMod ell)) = 1 by
      exact ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen]
  have htwistSplit :
      (∏ j : Multiplicative (ZMod ell), twistEndpoint (e j)) =
        twistEndpoint 1 *
          ∏ j ∈ Finset.Icc 1 (ell - 1),
            twistEndpoint
              (e (Multiplicative.ofAdd (j : ZMod ell))) := by
    rw [prod_multiplicative_zmod_eq_head_mul_Icc ell hellpos]
    rw [show e (Multiplicative.ofAdd (0 : ZMod ell)) = 1 by
      exact ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen]
  have hnormNonidentity :
      (∏ j ∈ Finset.Icc 1 (ell - 1),
          normEndpoint (e (Multiplicative.ofAdd (j : ZMod ell)))) =
        ∏ j ∈ Finset.Icc 1 (ell - 1), D.normDelta j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact hnormRows j hj
  have htwistNonidentity :
      (∏ j ∈ Finset.Icc 1 (ell - 1),
          twistEndpoint (e (Multiplicative.ofAdd (j : ZMod ell)))) =
        ∏ j ∈ Finset.Icc 1 (ell - 1), D.twistDelta j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact htwistRows j hj
  have hcore :=
    D.product_identity (Module.finrank F K) hdiv eta chi heta psi hpsi
  rw [hnormReindex, htwistReindex]
  change upperEndpoint *
      (∏ j : Multiplicative (ZMod ell), normEndpoint (e j)) =
    ∏ j : Multiplicative (ZMod ell), twistEndpoint (e j)
  rw [hnormSplit, htwistSplit, hupper, hnormIdentity, htwistIdentity,
    hnormNonidentity, htwistNonidentity, one_mul]
  exact hcore

end FullNormCharacterProduct

end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma
namespace TameOddConductorOne

noncomputable section

open scoped BigOperators

private theorem residualMulChar_eq_of_character_eq
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (theta theta' : LocalQuasiCharData E)
    (hchar : theta.character = theta'.character) :
    residualMulChar E theta = residualMulChar E theta' := by
  ext x
  simp only [residualMulChar_apply_unit]
  rw [hchar]

private theorem residualMulChar_eq_mul_of_character_eq
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (theta theta1 theta2 : LocalQuasiCharData E)
    (hchar : theta.character = theta1.character * theta2.character) :
    residualMulChar E theta =
      residualMulChar E theta1 * residualMulChar E theta2 := by
  ext x
  simp only [residualMulChar_apply_unit, MulChar.mul_apply]
  rw [hchar, ContinuousQuasiChar.mul_apply]
  rfl

private theorem langlandsGaussSum_equiv
    {k k' : Type*} [Field k] [Fintype k] [Field k'] [Fintype k']
    (e : k ≃+* k')
    (chi : FiniteMulChar k) (chi' : FiniteMulChar k')
    (psi : FiniteAddChar k) (psi' : FiniteAddChar k')
    (hchi : ∀ x, chi' (e x) = chi x)
    (hpsi : ∀ x, psi' (e x) = psi x) :
    langlandsGaussSum chi' psi' = langlandsGaussSum chi psi := by
  rw [langlandsGaussSum_eq_neg_gaussSum_inv,
    langlandsGaussSum_eq_neg_gaussSum_inv]
  congr 1
  rw [gaussSum, gaussSum]
  calc
    (∑ x : k', chi'⁻¹ x * psi' x) =
        ∑ x : k, chi'⁻¹ (e x) * psi' (e x) := by
      exact (e.toEquiv.sum_comp (fun x : k' => chi'⁻¹ x * psi' x)).symm
    _ = ∑ x : k, chi⁻¹ x * psi x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hchi, hpsi]

section LocalData

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

def gammaF
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F) :
    AdmissibleGamma F chiF psiF :=
  tameOddUniformizerGamma F chiF psiF
    (tameOddLowerUniformizer F K piK hpiK)
    (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK)

def gammaK
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : 1 ≤ chiF.conductor) : AdmissibleGamma K chiK psiK :=
  ⟨Units.map (algebraMap F K).toMonoidHom
      (gammaF F K hres piK hpiK chiF psiF : Fˣ),
    highParameter_intermediate_commonDenominator
      F K ht hres piK hpiK hgen chiF chiK psiF psiK hminimal hchi hpsi hm
      (gammaF F K hres piK hpiK chiF psiF : Fˣ)
      (gammaF F K hres piK hpiK chiF psiF).property⟩

def gammaNorm
    (normData : NormCharacter F K → LocalQuasiCharData F)
    (psiF : LocalAddCharData F) (mu : NormCharacter F K) :
    AdmissibleGamma F (normData mu) psiF :=
  tameOddUniformizerGamma F (normData mu) psiF
    (tameOddLowerUniformizer F K piK hpiK)
    (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK)

def gammaTwist
    (twistData : NormCharacter F K → LocalQuasiCharData F)
    (psiF : LocalAddCharData F) (mu : NormCharacter F K) :
    AdmissibleGamma F (twistData mu) psiF :=
  tameOddUniformizerGamma F (twistData mu) psiF
    (tameOddLowerUniformizer F K piK hpiK)
    (tameOddLowerUniformizer_isUniformizer F K hres piK hpiK)

@[simp] theorem gammaK_coe
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : 1 ≤ chiF.conductor) :
    (gammaK F K ht hres piK hpiK hgen chiF chiK psiF psiK
      hminimal hchi hpsi hm : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom
        (gammaF F K hres piK hpiK chiF psiF : Fˣ) := rfl

end LocalData

section ActualCharacters

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

abbrev normData (mu : NormCharacter F K) : LocalQuasiCharData F :=
  tameOddNormCharacterData F K ht hres piK hpiK hgen mu

abbrev twistData (chiF : LocalQuasiCharData F)
    (mu : NormCharacter F K) : LocalQuasiCharData F :=
  ramifiedNormCharacterOrbitTwistData
    F K ht hres piK hpiK hgen chiF mu

@[simp] theorem normData_character (mu : NormCharacter F K) :
    (normData F K ht hres piK hpiK hgen mu).character = mu.1 := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    ext x
    simp [normData, tameOddNormCharacterData]
  · simp [normData, tameOddNormCharacterData, hmu]

@[simp] theorem normData_one_conductor :
    (normData F K ht hres piK hpiK hgen 1).conductor = 0 := by
  simp [normData, tameOddNormCharacterData]

theorem normData_nontrivial_conductor (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (normData F K ht hres piK hpiK hgen mu).conductor = 1 := by
  simp [normData, tameOddNormCharacterData, hmu]

@[simp] theorem twistData_character (chiF : LocalQuasiCharData F)
    (mu : NormCharacter F K) :
    (twistData F K ht hres piK hpiK hgen chiF mu).character =
      mu.1 * chiF.character :=
  ramifiedNormCharacterOrbitTwistData_character
    F K ht hres piK hpiK hgen chiF mu

theorem twistData_conductor_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (mu : NormCharacter F K) :
    (twistData F K ht hres piK hpiK hgen chiF mu).conductor = 1 := by
  have h := ramifiedNormCharacterOrbitTwistData_conductor_eq_ite
    F K ht hres piK hpiK hgen chiF hminimal mu
  rw [h]
  simp [minimalOrbitTwistConductor, hchiF]

end ActualCharacters

section Certificates

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

structure ResidualCertificates
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace) where
  residueEquiv : ResidueField F ≃+* ResidueField K
  eta : FiniteMulChar (ResidueField F)
  eta_order : orderOf eta = Module.finrank F K
  norm_rows : ∀ j ∈ Finset.Icc 1 (Module.finrank F K - 1),
    residualMulChar F
        (normData F K ht hres piK hpiK hgen
          (ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K))))) = eta ^ j
  upper_mul : ∀ x : ResidueField F,
    residualMulChar K chiK (residueEquiv x) =
      (residualMulChar F chiF ^ Module.finrank F K) x
  upper_add : ∀ x : ResidueField F,
    residualAddChar K psiK
        (gammaK F K ht hres piK hpiK hgen chiF chiK psiF psiK
          hminimal hcomp htrace (by omega) : Kˣ)
        (by
          rw [(gammaK F K ht hres piK hpiK hgen chiF chiK psiF psiK
            hminimal hcomp htrace (by omega)).property]
          have hchiK := minimalOrbit_compNorm_conductor_eq_of_leCritical
            F K ht hres piK hpiK hgen chiF hminimal chiK hcomp (by omega)
          norm_cast
          omega)
        (residueEquiv x) =
      (residualAddChar F psiF
        (gammaF F K hres piK hpiK chiF psiF : Fˣ)
        (by
          rw [(gammaF F K hres piK hpiK chiF psiF).property]
          norm_cast
          omega)).mulShift
        (Module.finrank F K : ResidueField F) x

/-! The residue certificates above are not extra mathematical input.  The
following private API derives them from the actual norm/trace pullbacks. -/

/-- Residue degree one makes the canonical residue map an equivalence. -/
private def actualResidueEquiv : ResidueField F ≃+* ResidueField K := by
  apply RingEquiv.ofBijective (extensionResidueMap F K)
  constructor
  · exact (extensionResidueMap F K).injective
  · have hfin : Module.finrank (ResidueField F) (ResidueField K) = 1 := by
      rw [← residueDegree_eq_finrank_residueField F K, hres]
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

@[simp] private theorem actualResidueEquiv_apply (x : ResidueField F) :
    actualResidueEquiv F K hres x = extensionResidueMap F K x := rfl

private def indexedNormCharacter (j : ℕ) : NormCharacter F K :=
  ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))

private def normCharacterGenerator : NormCharacter F K :=
  indexedNormCharacter F K ht hres piK hpiK hgen 1

private def residualGenerator : FiniteMulChar (ResidueField F) :=
  residualMulChar F
    (normData F K ht hres piK hpiK hgen
      (normCharacterGenerator F K ht hres piK hpiK hgen))

private theorem indexedNormCharacter_eq_generator_pow (j : ℕ) :
    indexedNormCharacter F K ht hres piK hpiK hgen j =
      normCharacterGenerator F K ht hres piK hpiK hgen ^ j := by
  let e := ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen
  simp only [indexedNormCharacter, normCharacterGenerator]
  rw [← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

private theorem residual_norm_rows (j : ℕ) :
    residualMulChar F
        (normData F K ht hres piK hpiK hgen
          (indexedNormCharacter F K ht hres piK hpiK hgen j)) =
      residualGenerator F K ht hres piK hpiK hgen ^ j := by
  rw [indexedNormCharacter_eq_generator_pow F K ht hres piK hpiK hgen j]
  ext x
  rw [residualMulChar_apply_unit, MulChar.pow_apply_coe,
    residualGenerator, residualMulChar_apply_unit]
  rw [normData_character F K ht hres piK hpiK hgen,
    normData_character F K ht hres piK hpiK hgen]
  change
    ((((normCharacterGenerator F K ht hres piK hpiK hgen ^ j).1)
      (teichmullerLocalUnits F x) : ℂˣ) : ℂ) =
      ((((normCharacterGenerator F K ht hres piK hpiK hgen).1)
        (teichmullerLocalUnits F x) : ℂˣ) : ℂ) ^ j
  rw [NormCharacter.coe_pow]
  simp

private theorem normCharacterGenerator_ne_one :
    normCharacterGenerator F K ht hres piK hpiK hgen ≠ 1 := by
  let ell := Module.finrank F K
  letI : NeZero ell := ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩
  simp only [normCharacterGenerator, indexedNormCharacter]
  intro h
  have hs : Multiplicative.ofAdd ((1 : ℕ) : ZMod ell) = 1 :=
    (ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).injective
      (h.trans
        (ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen).map_one.symm)
  have hs' := congrArg Multiplicative.toAdd hs
  change ((1 : ℕ) : ZMod ell) = 0 at hs'
  have hd : ell ∣ 1 := (ZMod.natCast_eq_zero_iff 1 ell).1 hs'
  exact (PrimeCyclicExtension.degree_prime F K).ne_one (Nat.dvd_one.mp hd)

private theorem residualGenerator_ne_one :
    residualGenerator F K ht hres piK hpiK hgen ≠ 1 := by
  let tau := normCharacterGenerator F K ht hres piK hpiK hgen
  have htau : tau ≠ 1 :=
    normCharacterGenerator_ne_one F K ht hres piK hpiK hgen
  have hcond :
      (normData F K ht hres piK hpiK hgen tau).conductor = 1 :=
    normData_nontrivial_conductor F K ht hres piK hpiK hgen tau htau
  exact residualMulChar_ne_one F
    (normData F K ht hres piK hpiK hgen tau) hcond

private theorem residualGenerator_order :
    orderOf (residualGenerator F K ht hres piK hpiK hgen) =
      Module.finrank F K := by
  let ell := Module.finrank F K
  let eta := residualGenerator F K ht hres piK hpiK hgen
  have hetaNe : eta ≠ 1 :=
    residualGenerator_ne_one F K ht hres piK hpiK hgen
  have hpow : eta ^ ell = 1 := by
    have h := residual_norm_rows F K ht hres piK hpiK hgen ell
    have hindex : indexedNormCharacter F K ht hres piK hpiK hgen ell = 1 := by
      simp [indexedNormCharacter]
    rw [hindex] at h
    have honeData : normData F K ht hres piK hpiK hgen 1 =
        trivialQuasiCharData F := by
      simp [normData, tameOddNormCharacterData]
    rw [honeData] at h
    have hresOne : residualMulChar F (trivialQuasiCharData F) = 1 := by
      ext x
      rw [residualMulChar_apply_unit]
      simp
    rw [hresOne] at h
    exact h.symm
  have hdvd : orderOf eta ∣ ell := (orderOf_dvd_iff_pow_eq_one).2 hpow
  rcases (Nat.dvd_prime (PrimeCyclicExtension.degree_prime F K)).1 hdvd with h1 | hell
  · exact (hetaNe (orderOf_eq_one_iff.mp h1)).elim
  · exact hell

omit [Module.Free F K] [PrimeCyclicExtension F K] in
private theorem gammaF_order_one
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (psiF : LocalAddCharData F) :
    ord F (((gammaF F K hres piK hpiK chiF psiF :
      AdmissibleGamma F chiF psiF) : Fˣ) : F) =
      ((psiF.conductor + 1 : ℤ) : WithTop ℤ) := by
  rw [(gammaF F K hres piK hpiK chiF psiF).property]
  norm_cast
  omega

include ht piK hpiK hgen in
private theorem upper_residualMulChar
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (x : ResidueField F) :
    residualMulChar K chiK (actualResidueEquiv F K hres x) =
      (residualMulChar F chiF ^ Module.finrank F K) x := by
  classical
  have hchiK : chiK.conductor = 1 := by
    have h := minimalOrbit_compNorm_conductor_eq_of_leCritical
      F K ht hres piK hpiK hgen chiF hminimal chiK hcomp (by omega)
    simpa [hchiF] using h
  by_cases hx : x = 0
  · subst x
    rw [map_zero]
    exact (MulChar.map_zero _).trans (MulChar.map_zero _).symm
  let xu : (ResidueField F)ˣ := Units.mk0 x hx
  change residualMulChar K chiK (actualResidueEquiv F K hres x) =
    (residualMulChar F chiF ^ Module.finrank F K) (xu : ResidueField F)
  rw [MulChar.pow_apply_coe]
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
    change residueMap K (unitGroupMulEquivRingOfIntegers K uK) =
      extensionResidueMap F K
        (((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F))
    rw [residueUnits_coe]
    rfl
  have hresK :
      ((residueUnits K uK : (ResidueField K)ˣ) : ResidueField K) =
        actualResidueEquiv F K hres x := by
    rw [hresKunits]
    change extensionResidueMap F K
        (((residueUnits F uF : (ResidueField F)ˣ) : ResidueField F)) =
      actualResidueEquiv F K hres x
    rw [hresF, actualResidueEquiv_apply]
  have hnorm : normUnits F K (uK : Kˣ) =
      (uF : Fˣ) ^ Module.finrank F K := by
    apply Units.ext
    change norm F K (algebraMap F K (((uF : unitGroup F) : Fˣ) : F)) =
      (((uF : unitGroup F) : Fˣ) : F) ^ Module.finrank F K
    exact norm_algebraMap F K (((uF : unitGroup F) : Fˣ) : F)
  rw [← hresK, residualMulChar_residueUnits K chiK (by omega)]
  change (((chiK.character) (uK : Kˣ) : ℂˣ) : ℂ) =
    (residualMulChar F chiF xu) ^ Module.finrank F K
  rw [hcomp, ContinuousQuasiChar.compNorm_apply, hnorm, map_pow,
    Units.val_pow_eq_pow_val]
  simp only [residualMulChar_apply_unit, uF]

omit ht hgen in
private theorem upper_residualAddChar_commonDenominator
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGammaK : (GammaK : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom
        (gammaF F K hres piK hpiK chiF psiF : Fˣ))
    (hGammaKOrder : ord K (((GammaK : Kˣ) : K)) =
      ((psiK.conductor + 1 : ℤ) : WithTop ℤ))
    (x : ResidueField F) :
    residualAddChar K psiK (GammaK : Kˣ) hGammaKOrder
        (actualResidueEquiv F K hres x) =
      residualAddChar F psiF
        (gammaF F K hres piK hpiK chiF psiF : Fˣ)
        (gammaF_order_one F K hres piK hpiK chiF hchiF psiF)
        ((Module.finrank F K : ResidueField F) * x) := by
  classical
  let GammaF := gammaF F K hres piK hpiK chiF psiF
  let a : ringOfIntegers F := teichmuller F x
  let aK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) a
  let b : ringOfIntegers F := (Module.finrank F K : ringOfIntegers F) * a
  have haF : (a : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 a.property
  have haKcoe : (aK : K) = algebraMap F K (a : F) :=
    Valuation.HasExtension.val_algebraMap a
  have haK : algebraMap F K (a : F) ∈ lattice K 0 := by
    rw [← haKcoe]
    exact (mem_lattice_zero_iff K).2 aK.property
  have hbF : (b : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 b.property
  have hreduceF : reduce F (a : F) haF = x := by
    simp [a, reduce]
  have hreduceK : reduce K (algebraMap F K (a : F)) haK =
      actualResidueEquiv F K hres x := by
    change residueMap K aK = actualResidueEquiv F K hres x
    rw [← hreduceF]
    change residueMap K aK = actualResidueEquiv F K hres (residueMap F a)
    rfl
  have hreduceB : reduce F (b : F) hbF =
      (Module.finrank F K : ResidueField F) * x := by
    change residueMap F ((Module.finrank F K : ringOfIntegers F) * a) = _
    rw [map_mul, map_natCast]
    have hares : residueMap F a = x := by
      simpa only [reduce] using hreduceF
    rw [hares]
  rw [← hreduceK, residualAddChar_integral_lift,
    ← hreduceB, residualAddChar_integral_lift]
  change (((psiK.character)
      (algebraMap F K (a : F) / (((GammaK : Kˣ) : K))) : ℂˣ) : ℂ) =
    ((psiF.character ((b : F) /
      (((GammaF : AdmissibleGamma F chiF psiF) : Fˣ) : F)) : ℂˣ) : ℂ)
  rw [htrace, ContinuousAddChar.compTrace_apply]
  apply congrArg Units.val
  apply congrArg psiF.character
  have hGamma : (((GammaK : Kˣ) : K)) = algebraMap F K
      (((GammaF : AdmissibleGamma F chiF psiF) : Fˣ) : F) := by
    exact congrArg Units.val hGammaK
  rw [hGamma, ← map_div₀, trace_algebraMap]
  change (Module.finrank F K : ℕ) •
      ((a : F) / (((GammaF : AdmissibleGamma F chiF psiF) : Fˣ) : F)) =
    ((Module.finrank F K : F) * (a : F)) /
      (((GammaF : AdmissibleGamma F chiF psiF) : Fˣ) : F)
  simp only [nsmul_eq_mul]
  ring

private def derivedResidualCertificates
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace) :
    ResidualCertificates F K ht hres piK hpiK hgen
      chiF hchiF hminimal chiK hcomp psiF psiK htrace where
  residueEquiv := actualResidueEquiv F K hres
  eta := residualGenerator F K ht hres piK hpiK hgen
  eta_order := residualGenerator_order F K ht hres piK hpiK hgen
  norm_rows := by
    intro j _hj
    simpa only [indexedNormCharacter, residualGenerator] using
      residual_norm_rows F K ht hres piK hpiK hgen j
  upper_mul := by
    intro x
    exact upper_residualMulChar F K ht hres piK hpiK hgen
      chiF hchiF hminimal chiK hcomp x
  upper_add := by
    intro x
    let GammaK := gammaK F K ht hres piK hpiK hgen
      chiF chiK psiF psiK hminimal hcomp htrace (by omega)
    apply upper_residualAddChar_commonDenominator
      F K hres piK hpiK chiF hchiF chiK psiF psiK htrace GammaK
    simpa only using
      (gammaK_coe F K ht hres piK hpiK hgen chiF chiK psiF psiK
        hminimal hcomp htrace (by omega))

end Certificates

section ActualGammas

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

abbrev normGammaActual (psiF : LocalAddCharData F)
    (mu : NormCharacter F K) :=
  gammaNorm F K hres piK hpiK
    (normData F K ht hres piK hpiK hgen) psiF mu

abbrev twistGammaActual
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (mu : NormCharacter F K) :=
  gammaTwist F K hres piK hpiK
    (twistData F K ht hres piK hpiK hgen chiF) psiF mu

end ActualGammas

section Main

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤)

theorem full_product
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace)
    (_hodd : Odd (Module.finrank F K))
    (C : ResidualCertificates F K ht hres piK hpiK hgen
      chiF hchiF hminimal chiK hcomp psiF psiK htrace) :
    deltaFinite chiK psiK
        (gammaK F K ht hres piK hpiK hgen chiF chiK psiF psiK
          hminimal hcomp htrace (by omega)) *
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (normData F K ht hres piK hpiK hgen mu) psiF
          (normGammaActual F K ht hres piK hpiK hgen psiF mu)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (twistData F K ht hres piK hpiK hgen chiF mu) psiF
          (twistGammaActual F K ht hres piK hpiK hgen chiF psiF mu)) := by
  classical
  letI : Fintype (ResidueField F) := residueFieldFintype F
  letI : Fintype (ResidueField K) := residueFieldFintype K
  let ell := Module.finrank F K
  let e := ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen
  let GammaF := gammaF F K hres piK hpiK chiF psiF
  let GammaK := gammaK F K ht hres piK hpiK hgen chiF chiK psiF psiK
    hminimal hcomp htrace (by omega)
  let GammaNorm := normGammaActual F K ht hres piK hpiK hgen psiF
  let GammaTwist := twistGammaActual F K ht hres piK hpiK hgen chiF psiF
  let chiBar := residualMulChar F chiF
  let psiBar := residualAddChar F psiF (GammaF : Fˣ) (by
    rw [GammaF.property]
    norm_cast
    omega)
  have hchiK : chiK.conductor = 1 := by
    simpa only [hchiF] using
      (minimalOrbit_compNorm_conductor_eq_of_leCritical
        F K ht hres piK hpiK hgen chiF hminimal chiK hcomp (by omega))
  have hdiv : ell ∣ Fintype.card (ResidueField F) - 1 := by
    change Module.finrank F K ∣ Fintype.card (ResidueField F) - 1
    rw [← C.eta_order]
    exact MulChar.orderOf_dvd_card_sub_one (ResidueField F) C.eta
  have hellk : (ell : ResidueField F) ≠ 0 := by
    intro hell
    have hchar : ringChar (ResidueField F) ∣ ell :=
      (CharP.cast_eq_zero_iff (ResidueField F)
        (ringChar (ResidueField F)) ell).mp hell
    letI : Fact (Nat.Prime (ringChar (ResidueField F))) :=
      ⟨CharP.prime_ringChar (ResidueField F)⟩
    have hcq : ringChar (ResidueField F) ∣ Fintype.card (ResidueField F) :=
      (prime_dvd_char_iff_dvd_card (ringChar (ResidueField F))).mp (dvd_refl _)
    have hqpos : 1 ≤ Fintype.card (ResidueField F) := Fintype.card_pos
    have hcop : Nat.Coprime (Fintype.card (ResidueField F) - 1)
        (Fintype.card (ResidueField F)) :=
      (Nat.coprime_self_sub_left hqpos).mpr
        (Nat.coprime_one_left (Fintype.card (ResidueField F)))
    have hellcop : Nat.Coprime ell (Fintype.card (ResidueField F)) :=
      Nat.Coprime.of_dvd_left hdiv hcop
    have hone : ringChar (ResidueField F) = 1 :=
      Nat.eq_one_of_dvd_coprimes hellcop hchar hcq
    exact (CharP.prime_ringChar (ResidueField F)).ne_one hone
  let ellUnit : (ResidueField F)ˣ :=
    Units.mk0 (ell : ResidueField F) hellk
  have hupperScalar :
      (chiK.character (GammaK : Kˣ) : ℂ) =
        (chiF.character (GammaF : Fˣ) : ℂ) ^ ell := by
    have hnormGamma : normUnits F K (GammaK : Kˣ) =
        (GammaF : Fˣ) ^ ell := by
      rw [show (GammaK : Kˣ) = Units.map (algebraMap F K).toMonoidHom
          (GammaF : Fˣ) by rfl]
      ext
      simp [ell]
    rw [hcomp, ContinuousQuasiChar.compNorm_apply, hnormGamma, map_pow]
    rfl
  have hupperGauss :
      langlandsGaussSum (residualMulChar K chiK)
          (residualAddChar K psiK (GammaK : Kˣ) (by
            rw [GammaK.property]
            norm_cast
            omega)) =
        (chiBar ((ell : ResidueField F) ^ ell) : ℂ) *
          langlandsGaussSum (chiBar ^ ell) psiBar := by
    have htransport := langlandsGaussSum_equiv C.residueEquiv
      (chiBar ^ ell) (residualMulChar K chiK)
      (psiBar.mulShift (ell : ResidueField F))
      (residualAddChar K psiK (GammaK : Kˣ) (by
        rw [GammaK.property]
        norm_cast
        omega)) C.upper_mul C.upper_add
    have hscale := langlandsGaussSum_mulShift_unit
      (chiBar ^ ell) psiBar ellUnit
    rw [htransport, show psiBar.mulShift (ell : ResidueField F) =
        psiBar.mulShift (ellUnit : ResidueField F) by rfl, hscale]
    simp only [MulChar.pow_apply_coe, map_pow]
    rfl
  have hmu_ne_one (j : ℕ) (hj : j ∈ Finset.Icc 1 (ell - 1)) :
      e (Multiplicative.ofAdd (j : ZMod ell)) ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres piK hpiK hgen _).2
    intro hone
    have hz : (j : ZMod ell) = 0 := by
      simpa using congrArg Multiplicative.toAdd hone
    have hjlt : j < ell := by
      simp only [Finset.mem_Icc] at hj
      omega
    have hzval := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hjlt] at hzval
    simp at hzval
    simp only [Finset.mem_Icc] at hj
    omega
  have hnormGamma_common (j : ℕ) (hj : j ∈ Finset.Icc 1 (ell - 1)) :
      (GammaNorm (e (Multiplicative.ofAdd (j : ZMod ell))) : Fˣ) =
        (GammaF : Fˣ) := by
    simp only [GammaNorm, gammaNorm,
      tameOddUniformizerGamma_coe, GammaF, gammaF]
    rw [normData_nontrivial_conductor F K ht hres piK hpiK hgen _
      (hmu_ne_one j hj), hchiF]
  have htwistGamma_common (mu : NormCharacter F K) :
      (GammaTwist mu : Fˣ) = (GammaF : Fˣ) := by
    simp only [GammaTwist, gammaTwist,
      tameOddUniformizerGamma_coe, GammaF, gammaF]
    rw [twistData_conductor_one F K ht hres piK hpiK hgen
      chiF hchiF hminimal mu, hchiF]
  have hnormGamma_value (j : ℕ) (hj : j ∈ Finset.Icc 1 (ell - 1)) :
      ((e (Multiplicative.ofAdd (j : ZMod ell))).1
        (GammaNorm (e (Multiplicative.ofAdd (j : ZMod ell))) : Fˣ)) = 1 := by
    let mu := e (Multiplicative.ofAdd (j : ZMod ell))
    apply mu.eq_one_on_normRange F K
    refine ⟨(tameOddUpperUniformizer K piK hpiK) ^
        (((1 : ℕ) : ℤ) + psiF.conductor), ?_⟩
    rw [map_zpow]
    rw [hnormGamma_common j hj]
    simp only [GammaF, gammaF, tameOddUniformizerGamma_coe, hchiF]
    rfl
  let D : TameOddConductorOneDeltaData ell C.eta chiBar psiBar :=
    { scalar := (chiF.character (GammaF : Fˣ) : ℂ)
      upperDelta := deltaFinite chiK psiK GammaK
      normDelta := fun j =>
        deltaFinite
          (normData F K ht hres piK hpiK hgen
            (e (Multiplicative.ofAdd (j : ZMod ell)))) psiF
          (GammaNorm (e (Multiplicative.ofAdd (j : ZMod ell))))
      baseDelta := deltaFinite
        (twistData F K ht hres piK hpiK hgen chiF 1) psiF
        (GammaTwist 1)
      twistDelta := fun j => deltaFinite
        (twistData F K ht hres piK hpiK hgen chiF
          (e (Multiplicative.ofAdd (j : ZMod ell)))) psiF
        (GammaTwist (e (Multiplicative.ofAdd (j : ZMod ell))))
      upper_formula := by
        rw [deltaFinite_conductor_one K chiK hchiK psiK GammaK,
          hupperScalar, hupperGauss]
      norm_formula := by
        intro j hj
        let mu := e (Multiplicative.ofAdd (j : ZMod ell))
        have hmu : mu ≠ 1 := hmu_ne_one j hj
        have hcond := normData_nontrivial_conductor
          F K ht hres piK hpiK hgen mu hmu
        rw [deltaFinite_conductor_one F _ hcond psiF (GammaNorm mu)]
        rw [show (normData F K ht hres piK hpiK hgen mu).character
              (GammaNorm mu : Fˣ) = 1 by
            simpa only [normData_character] using hnormGamma_value j hj]
        simp only [Units.val_one, neg_mul, one_mul]
        have hadd :
            residualAddChar F psiF (GammaNorm mu : Fˣ) (by
              rw [(GammaNorm mu).property]
              norm_cast
              omega) = psiBar := by
          ext x
          change (psiF.character
              (((teichmuller F x : ringOfIntegers F) : F) /
                ((GammaNorm mu : Fˣ) : F)) : ℂ) =
            (psiF.character
              (((teichmuller F x : ringOfIntegers F) : F) /
                ((GammaF : Fˣ) : F)) : ℂ)
          have hg := hnormGamma_common j hj
          rw [hg]
        rw [hadd, C.norm_rows j hj]
      base_formula := by
        have hcond := twistData_conductor_one
          F K ht hres piK hpiK hgen chiF hchiF hminimal 1
        rw [deltaFinite_conductor_one F _ hcond psiF (GammaTwist 1)]
        have hadd :
            residualAddChar F psiF (GammaTwist 1 : Fˣ) (by
              rw [(GammaTwist 1).property]
              norm_cast
              omega) = psiBar := by
          ext x
          change (psiF.character
              (((teichmuller F x : ringOfIntegers F) : F) /
                ((GammaTwist 1 : Fˣ) : F)) : ℂ) =
            (psiF.character
              (((teichmuller F x : ringOfIntegers F) : F) /
                ((GammaF : Fˣ) : F)) : ℂ)
          have hg := htwistGamma_common 1
          rw [hg]
        have hresidual :
            residualMulChar F
                (twistData F K ht hres piK hpiK hgen chiF 1) = chiBar := by
          apply residualMulChar_eq_of_character_eq
          rw [twistData_character]
          exact one_mul chiF.character
        have hvalue :
            ((twistData F K ht hres piK hpiK hgen chiF 1).character
              (GammaTwist 1 : Fˣ) : ℂ) =
              (chiF.character (GammaF : Fˣ) : ℂ) := by
          rw [twistData_character, ContinuousQuasiChar.mul_apply]
          have hg := htwistGamma_common 1
          rw [hg]
          simp
        rw [hvalue, hresidual, hadd]
      twist_formula := by
        intro j hj
        let mu := e (Multiplicative.ofAdd (j : ZMod ell))
        have hcond := twistData_conductor_one
          F K ht hres piK hpiK hgen chiF hchiF hminimal mu
        rw [deltaFinite_conductor_one F _ hcond psiF (GammaTwist mu)]
        have hadd :
            residualAddChar F psiF (GammaTwist mu : Fˣ) (by
              rw [(GammaTwist mu).property]
              norm_cast
              omega) = psiBar := by
          ext x
          change (psiF.character
              (((teichmuller F x : ringOfIntegers F) : F) /
                ((GammaTwist mu : Fˣ) : F)) : ℂ) =
            (psiF.character
              (((teichmuller F x : ringOfIntegers F) : F) /
                ((GammaF : Fˣ) : F)) : ℂ)
          have hg := htwistGamma_common mu
          rw [hg]
        have hresidual :
            residualMulChar F
                (twistData F K ht hres piK hpiK hgen chiF mu) =
              chiBar * C.eta ^ j := by
          calc
            _ = residualMulChar F
                  (normData F K ht hres piK hpiK hgen mu) * chiBar := by
              apply residualMulChar_eq_mul_of_character_eq
              rw [twistData_character, normData_character]
            _ = C.eta ^ j * chiBar := by rw [C.norm_rows j hj]
            _ = chiBar * C.eta ^ j := mul_comm _ _
        rw [hresidual, hadd]
        have hvalue :
            ((twistData F K ht hres piK hpiK hgen chiF mu).character
              (GammaTwist mu : Fˣ) : ℂ) =
              (chiF.character (GammaF : Fˣ) : ℂ) := by
          rw [twistData_character, ContinuousQuasiChar.mul_apply]
          have hv := hnormGamma_value j hj
          rw [hnormGamma_common j hj] at hv
          rw [htwistGamma_common mu, hv]
          simp
        rw [hvalue] }
  apply D.full_normCharacter_product F K ht hres piK hpiK hgen
    C.eta chiBar psiBar hdiv C.eta_order
    (residualAddChar_ne_one F psiF (GammaF : Fˣ) (by
      rw [GammaF.property]
      norm_cast
      omega))
    (deltaFinite chiK psiK GammaK)
    (fun mu => deltaFinite
      (normData F K ht hres piK hpiK hgen mu) psiF (GammaNorm mu))
    (fun mu => deltaFinite
      (twistData F K ht hres piK hpiK hgen chiF mu) psiF (GammaTwist mu))
    rfl
    (by
      rw [deltaFinite_conductor_zero F _
        (normData_one_conductor F K ht hres piK hpiK hgen)]
      rw [normData_character]
      simp)
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- The conductor-one tame-odd First Main product with every residue row
derived from the actual norm and trace pullbacks. -/
theorem firstMain
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (htrace : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K)) :
    deltaFinite chiK psiK
        (gammaK F K ht hres piK hpiK hgen chiF chiK psiF psiK
          hminimal hcomp htrace (by omega)) *
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (normData F K ht hres piK hpiK hgen mu) psiF
          (normGammaActual F K ht hres piK hpiK hgen psiF mu)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (twistData F K ht hres piK hpiK hgen chiF mu) psiF
          (twistGammaActual F K ht hres piK hpiK hgen chiF psiF mu)) := by
  exact full_product F K ht hres piK hpiK hgen
    chiF hchiF hminimal chiK hcomp psiF psiK htrace hodd
    (derivedResidualCertificates F K ht hres piK hpiK hgen
      chiF hchiF hminimal chiK hcomp psiF psiK htrace)

end Main

end

end TameOddConductorOne
end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma
namespace TameOddHigh

noncomputable section

open scoped BigOperators

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable
  (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

/-- Exact conductor data for every tame norm character, including the
identity at conductor zero. -/
def normData (mu : NormCharacter F K) : LocalQuasiCharData F := by
  classical
  by_cases hmu : mu = 1
  · exact trivialQuasiCharData F
  · exact quasiCharDataOfIsConductor F mu.1 1
      (tameNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)

@[simp] theorem normData_character (mu : NormCharacter F K) :
    (normData F K ht hres pi hpi hgen mu).character = mu.1 := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    have hdata : normData F K ht hres pi hpi hgen 1 =
        trivialQuasiCharData F := by
      unfold normData
      simp
    rw [hdata]
    ext x
    simp
  · simp [normData, hmu]

theorem normData_conductor_le_one (mu : NormCharacter F K) :
    (normData F K ht hres pi hpi hgen mu).conductor ≤ 1 := by
  classical
  by_cases hmu : mu = 1
  · subst mu
    simp [normData]
  · simp [normData, hmu]

theorem normData_conductor_lt
    (chi : LocalQuasiCharData F) (hlarge : 1 < chi.conductor)
    (mu : NormCharacter F K) :
    (normData F K ht hres pi hpi hgen mu).conductor < chi.conductor :=
  lt_of_le_of_lt (normData_conductor_le_one F K ht hres pi hpi hgen mu)
    hlarge

/-- The actual stable-twist datum for the factor indexed by `mu`. -/
def twistData
    (chi : LocalQuasiCharData F) (hlarge : 1 < chi.conductor)
    (mu : NormCharacter F K) : LocalQuasiCharData F :=
  stableTwistData F (normData F K ht hres pi hpi hgen mu) chi
    (normData_conductor_lt F K ht hres pi hpi hgen chi hlarge mu)

@[simp] theorem twistData_character
    (chi : LocalQuasiCharData F) (hlarge : 1 < chi.conductor)
    (mu : NormCharacter F K) :
    (twistData F K ht hres pi hpi hgen chi hlarge mu).character =
      mu.1 * chi.character := by
  simp [twistData]

def twistGamma
    (chi : LocalQuasiCharData F) (hlarge : 1 < chi.conductor)
    (psi : LocalAddCharData F) (Gamma : AdmissibleGamma F chi psi)
    (mu : NormCharacter F K) :
    AdmissibleGamma F
      (twistData F K ht hres pi hpi hgen chi hlarge mu) psi :=
  stableTwistAdmissibleGamma F
    (normData F K ht hres pi hpi hgen mu) chi psi
    (normData_conductor_lt F K ht hres pi hpi hgen chi hlarge mu) Gamma

/-- Product of the values of every member of an odd finite character group
at one fixed unit. -/
theorem normCharacter_value_product_eq_one
    (hodd : Odd (Module.finrank F K)) (x : Fˣ) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : Fintype (NormCharacter F K) := normCharacterFintype F K
    ∏ mu : NormCharacter F K, (mu.1 x : ℂ) = 1 := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  have hcard : Fintype.card (NormCharacter F K) = Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card,
      ramifiedNormCharacter_card F K ht hres pi hpi hgen]
  have hoddCard : Odd (Fintype.card (NormCharacter F K)) := by
    simpa [hcard] using hodd
  let f : NormCharacter F K → ℂ := fun mu ↦ (mu.1 x : ℂ)
  have hpair (mu : NormCharacter F K) : f mu * f mu⁻¹ = 1 := by
    simp [f]
  have hfixed (mu : NormCharacter F K) (hmu : mu⁻¹ = mu) : mu = 1 := by
    have hmu2 : mu ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun t : NormCharacter F K ↦ t * mu) hmu.symm).trans
        (by simp)
    have horder2 : orderOf mu ∣ 2 := orderOf_dvd_of_pow_eq_one hmu2
    have horderCard : orderOf mu ∣ Fintype.card (NormCharacter F K) := by
      simpa only [Nat.card_eq_fintype_card] using orderOf_dvd_natCard mu
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hoddCard.coprime_two_right
        horderCard horder2)
  have hone : f (1 : NormCharacter F K) = 1 := by
    rfl
  simpa [f] using
    (Finset.prod_involution (s := Finset.univ) (f := f)
      (fun mu _hmu ↦ mu⁻¹)
      (fun mu _hmu ↦ hpair mu)
      (fun mu _hmu hfmu hmu ↦ hfmu (hfixed mu hmu ▸ hone))
      (fun mu _hmu ↦ Finset.mem_univ mu⁻¹)
      (fun mu _hmu ↦ inv_inv mu))

/-- The exact stable-twist product in the tame high range. -/
theorem stableTwist_product
    (hodd : Odd (Module.finrank F K))
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : Fintype (NormCharacter F K) := normCharacterFintype F K
    ∏ mu : NormCharacter F K,
        deltaFinite
          (twistData F K ht hres pi hpi hgen chi h.conductor_gt_one mu)
          psi
          (twistGamma F K ht hres pi hpi hgen chi h.conductor_gt_one
            psi Gamma mu) =
      deltaFinite chi psi Gamma ^ Module.finrank F K := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype (normCharacterSubgroup F K) := normCharacterFintype F K
  let hr := stableTwist_stationaryDepth F chi d epsilon h.epsilon_le_one
    h.conductor_eq h.conductor_gt_one
  let c := R.toLamprecht
  have hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property := by
    simpa only [hr, stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  let beta := stableStationaryRepresentativeUnit F chi psi hr Gamma c hc
  let x : Fˣ := (Gamma : Fˣ) / beta
  let A : ℂ := deltaFinite chi psi Gamma
  have hd : 1 ≤ d := by
    have := h.conductor_gt_one
    have := h.epsilon_le_one
    rw [h.conductor_eq] at *
    omega
  have hstable (mu : NormCharacter F K) :
      deltaFinite
          (twistData F K ht hres pi hpi hgen chi h.conductor_gt_one mu)
          psi
          (twistGamma F K ht hres pi hpi hgen chi h.conductor_gt_one
            psi Gamma mu) =
        (mu.1 x : ℂ) * A := by
    have hnu :
        (normData F K ht hres pi hpi hgen mu).conductor ≤ d :=
      (normData_conductor_le_one F K ht hres pi hpi hgen mu).trans hd
    have hs := stableTwist F
      (normData F K ht hres pi hpi hgen mu) chi psi d epsilon
      h.epsilon_le_one h.conductor_eq h.conductor_gt_one hnu Gamma c hc
    simpa only [twistData, twistGamma, normData_character, beta, x, A] using hs
  calc
    (∏ mu : NormCharacter F K,
        deltaFinite
          (twistData F K ht hres pi hpi hgen chi h.conductor_gt_one mu)
          psi
          (twistGamma F K ht hres pi hpi hgen chi h.conductor_gt_one
            psi Gamma mu)) =
        ∏ mu : NormCharacter F K, (mu.1 x : ℂ) * A := by
          apply Finset.prod_congr rfl
          intro mu _hmu
          exact hstable mu
    _ = (∏ mu : NormCharacter F K, (mu.1 x : ℂ)) *
          ∏ _mu : NormCharacter F K, A := Finset.prod_mul_distrib
    _ = 1 * ∏ _mu : NormCharacter F K, A := by
      rw [normCharacter_value_product_eq_one F K ht hres pi hpi hgen hodd x]
    _ = A ^ Fintype.card (NormCharacter F K) := by simp
    _ = A ^ Module.finrank F K := by
      rw [← Nat.card_eq_fintype_card,
        ramifiedNormCharacter_card F K ht hres pi hpi hgen]

/-- The complete norm-character local-constant product is one. -/
theorem normDelta_product
    (hodd : Odd (Module.finrank F K))
    (psi : LocalAddCharData F)
    (Gamma : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (normData F K ht hres pi hpi hgen mu) psi) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : Fintype (NormCharacter F K) := normCharacterFintype F K
    ∏ mu : NormCharacter F K,
      deltaFinite (normData F K ht hres pi hpi hgen mu) psi (Gamma mu) = 1 := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype (normCharacterSubgroup F K) := normCharacterFintype F K
  have hcard : Fintype.card (normCharacterSubgroup F K) =
      Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (NormCharacter F K) = Module.finrank F K
    exact ramifiedNormCharacter_card F K ht hres pi hpi hgen
  apply delta_odd_prime_character_product F (normCharacterSubgroup F K)
    (by simpa [hcard] using PrimeCyclicExtension.degree_prime F K)
    (by simpa [hcard] using hodd) psi
    (normData F K ht hres pi hpi hgen)
    (normData_character F K ht hres pi hpi hgen) Gamma

/-! The remaining lemmas isolate the exact high-phase assembly.  They use
only literal mapped representatives and the common mapped denominator. -/

omit [PrimeCyclicExtension F K] in
/-- Norm/trace pullback carries the denominator times elementary Lamprecht
factor to the extension-degree power.  This statement is independent of
ramification; all ramified information enters in the existence of the
compatible representative and common denominator. -/
theorem mapped_lamprecht_baseFactor
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K).toMonoidHom (GammaF : Fˣ))
    (betaF : Fˣ) :
    (((chiK.character (GammaK : Kˣ) : ℂˣ) : ℂ)) *
      lamprechtElementaryFactor K chiK psiK GammaK
        (Units.map (algebraMap F K) betaF) =
      ((((chiF.character (GammaF : Fˣ) : ℂˣ) : ℂ)) *
        lamprechtElementaryFactor F chiF psiF GammaF betaF) ^
        Module.finrank F K := by
  let betaK := Units.map (algebraMap F K).toMonoidHom betaF
  have hnormGamma : Units.map (Algebra.norm F) (GammaK : Kˣ) =
      (GammaF : Fˣ) ^ Module.finrank F K := by
    rw [hGamma]
    ext
    simp
  have hnormBeta : Units.map (Algebra.norm F) betaK =
      betaF ^ Module.finrank F K := by
    ext
    simp [betaK]
  unfold lamprechtElementaryFactor
  rw [hchi, hpsi]
  change
    (((chiF.character.compNorm (GammaK : Kˣ) : ℂˣ) : ℂ)) *
      ((((psiF.character.compTrace
          ((betaK : K) / ((GammaK : Kˣ) : K)) : ℂˣ) : ℂ)) *
        ((((chiF.character.compNorm betaK : ℂˣ) : ℂ))⁻¹)) = _
  rw [ContinuousQuasiChar.compNorm_apply,
    ContinuousQuasiChar.compNorm_apply, hnormGamma, hnormBeta,
    map_pow, map_pow]
  have htrace : trace F K ((betaK : K) / ((GammaK : Kˣ) : K)) =
      Module.finrank F K • ((betaF : F) / ((GammaF : Fˣ) : F)) := by
    rw [hGamma]
    change trace F K
      (algebraMap F K (betaF : F) /
        algebraMap F K ((GammaF : Fˣ) : F)) = _
    rw [← map_div₀, trace_algebraMap]
  rw [ContinuousAddChar.compTrace_apply, htrace]
  have hpsiPower := congrArg Units.val
    (AddChar.map_nsmul_eq_pow psiF.character.toAddChar
      (Module.finrank F K) ((betaF : F) / ((GammaF : Fˣ) : F)))
  change
    (((psiF.character
      (Module.finrank F K •
        ((betaF : F) / ((GammaF : Fˣ) : F))) : ℂˣ) : ℂ)) =
      (((psiF.character
        ((betaF : F) / ((GammaF : Fˣ) : F)) : ℂˣ) : ℂ) ^
        Module.finrank F K) at hpsiPower
  rw [hpsiPower]
  simp only [Units.val_pow_eq_pow_val, inv_pow, mul_pow]

omit [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K] in
/-- Once the base (admissible times elementary) factor and the residual
critical factor have both been compared, the complete local constants are
the exact extension-degree power. -/
theorem deltaFinite_power_of_phase_factors
    {chiF : LocalQuasiCharData F} {chiK : LocalQuasiCharData K}
    {psiF : LocalAddCharData F} {psiK : LocalAddCharData K}
    (DF : LocalLamprechtPhaseData F chiF psiF)
    (DK : LocalLamprechtPhaseData K chiK psiK)
    (ell : ℕ)
    (hbase : DK.admissibleFactor * DK.elementaryFactor =
      (DF.admissibleFactor * DF.elementaryFactor) ^ ell)
    (hcritical : DK.criticalFactor = DF.criticalFactor ^ ell) :
    deltaFinite chiK psiK DK.gamma =
      deltaFinite chiF psiF DF.gamma ^ ell := by
  rw [DK.deltaFinite_eq_completeFactor,
    DF.deltaFinite_eq_completeFactor]
  unfold LocalLamprechtPhaseData.completeFactor
    LocalLamprechtPhaseData.stationaryFactor
  calc
    DK.admissibleFactor * (DK.elementaryFactor * DK.criticalFactor) =
        (DK.admissibleFactor * DK.elementaryFactor) * DK.criticalFactor := by
          ring
    _ = (DF.admissibleFactor * DF.elementaryFactor) ^ ell *
        DF.criticalFactor ^ ell := by rw [hbase, hcritical]
    _ = (DF.admissibleFactor *
        (DF.elementaryFactor * DF.criticalFactor)) ^ ell := by
          rw [← mul_pow]
          congr 1
          ring

/-- The literal compatible high pair has the required base-factor power.
No representative is selected: the theorem uses the caller-supplied `R`. -/
theorem compatible_baseFactor_power
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK) :
    let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R CF CK
    P.upstairs.admissibleFactor * P.upstairs.elementaryFactor =
      (P.downstairs.admissibleFactor * P.downstairs.elementaryFactor) ^
        Module.finrank F K := by
  let RK := HighStableOddParameterData.upstairsRepresentative F K ht hres pi
    hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R
  have hunit : RK.unit = Units.map (algebraMap F K) R.unit := by
    apply Units.ext
    rw [StationaryClassRepresentative.coe_unit,
      HighStableOddParameterData.upstairsRepresentative_coe]
    change algebraMap F K (R.representative : F) =
      algebraMap F K ((R.unit : Fˣ) : F)
    rw [StationaryClassRepresentative.coe_unit]
  dsimp only [HighStableOddParameterData.compatiblePhasePair,
    HighStableOddParameterData.upstairsPhase]
  rw [LocalLamprechtPhaseData.elementaryFactor_eq_separated,
    LocalLamprechtPhaseData.elementaryFactor_eq_separated,
    localPhaseOfStationaryClass_admissibleFactor,
    localPhaseOfStationaryClass_admissibleFactor,
    LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
    LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
    LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor,
    LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
  rw [show (HighStableOddParameterData.upstairsRepresentative F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R).unit = Units.map (algebraMap F K) R.unit from hunit]
  simpa [lamprechtElementaryFactor] using
      mapped_lamprecht_baseFactor F K chiF chiK psiF psiK hchi hpsi
        ⟨gammaF, hgammaF⟩
        ⟨Units.map (algebraMap F K) gammaF, H.commonDenominator⟩ rfl R.unit

/-- Exact high-phase power once the critical-factor comparison is supplied.
This is the common endpoint of the even (`criticalFactor = 1`) and odd
(ramified Hasse comparison) conductor branches. -/
theorem compatible_deltaFinite_power_of_critical
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK)
    (hcritical :
      let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
        hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R CF CK
      P.upstairs.criticalFactor = P.downstairs.criticalFactor ^
        Module.finrank F K) :
    let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R CF CK
    deltaFinite chiK psiK P.upstairs.gamma =
      deltaFinite chiF psiF P.downstairs.gamma ^ Module.finrank F K := by
  let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
    hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
    H R CF CK
  exact deltaFinite_power_of_phase_factors F K P.downstairs P.upstairs
    (Module.finrank F K)
    (compatible_baseFactor_power F K ht hres pi hpi hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R CF CK)
    hcritical

/-- Odd-conductor high power, with the critical comparison discharged by
the authoritative ramified Hasse certificate. -/
theorem compatible_odd_deltaFinite_power
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaF : Fˣ) (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ) (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    {ell : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      (HighStableOddParameterData.downstairsOddStationaryPhase F K ht hres pi
        hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R deltaF hdeltaF)
      (HighStableOddParameterData.upstairsOddStationaryPhase F K ht hres pi
        hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R deltaK hdeltaK)
      ell 0) :
    let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R (.odd deltaF hdeltaF) (.odd deltaK hdeltaK)
    deltaFinite chiK psiK P.upstairs.gamma =
      deltaFinite chiF psiF P.downstairs.gamma ^ Module.finrank F K := by
  have hcriticalEll :=
    HighStableOddParameterData.ramifiedHasseComparison_compatiblePhasePair
      F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd
      gammaF hgammaF H R deltaF hdeltaF deltaK hdeltaK D
  have hcritical :
      let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
        hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R (.odd deltaF hdeltaF) (.odd deltaK hdeltaK)
      P.upstairs.criticalFactor = P.downstairs.criticalFactor ^
        Module.finrank F K := by
    simpa only [D.degree_eq] using hcriticalEll
  exact compatible_deltaFinite_power_of_critical F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R
    (.odd deltaF hdeltaF) (.odd deltaK hdeltaK) hcritical

/-- Even-conductor high power: both residual critical factors are literally
one, while the same mapped base-factor comparison remains in force. -/
theorem compatible_even_deltaFinite_power
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF) :
    let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R .even .even
    deltaFinite chiK psiK P.upstairs.gamma =
      deltaFinite chiF psiF P.downstairs.gamma ^ Module.finrank F K := by
  apply compatible_deltaFinite_power_of_critical F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R
    .even .even
  simp [HighStableOddParameterData.compatiblePhasePair,
    HighStableOddParameterData.upstairsPhase,
    localPhaseOfStationaryClass, LocalLamprechtPhaseData.evenOfStationaryClass,
    LocalLamprechtPhaseData.criticalFactor]

/-- Final high-conductor product assembly.  The norm product is exactly one,
the twist product is the base delta to the odd extension degree, and the
upstairs delta is that same power. -/
theorem high_firstMain_product_of_delta_power
    (hodd : Odd (Module.finrank F K))
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma F chi psi)
    (R : StationaryClassRepresentative F chi psi h
      (Gamma : Fˣ) Gamma.property)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hpower : deltaFinite chiK psiK GammaK =
      deltaFinite chi psi Gamma ^ Module.finrank F K)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (normData F K ht hres pi hpi hgen mu) psi) :
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : Fintype (NormCharacter F K) := normCharacterFintype F K
    deltaFinite chiK psiK GammaK *
        ∏ mu : NormCharacter F K,
          deltaFinite (normData F K ht hres pi hpi hgen mu) psi
            (GammaNorm mu) =
      ∏ mu : NormCharacter F K,
        deltaFinite
          (twistData F K ht hres pi hpi hgen chi h.conductor_gt_one mu)
          psi
          (twistGamma F K ht hres pi hpi hgen chi h.conductor_gt_one
            psi Gamma mu) := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  rw [normDelta_product F K ht hres pi hpi hgen hodd psi GammaNorm,
    stableTwist_product F K ht hres pi hpi hgen hodd chi psi h Gamma R,
    hpower, mul_one]

/-- Extract the supplied odd critical coordinate without making a choice. -/
def oddCriticalDelta
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {d : ℕ}
    (C : LamprechtCriticalCoordinate E d 1) : Eˣ :=
  match C with
  | .odd delta _ => delta

theorem oddCriticalDelta_order
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {d : ℕ}
    (C : LamprechtCriticalCoordinate E d 1) :
    ord E (oddCriticalDelta C : E) = ((d : ℤ) : WithTop ℤ) := by
  cases C with
  | odd delta hdelta => exact hdelta

@[simp] theorem oddCriticalCoordinate_eta
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {d : ℕ}
    (C : LamprechtCriticalCoordinate E d 1) :
    LamprechtCriticalCoordinate.odd (oddCriticalDelta C)
      (oddCriticalDelta_order C) = C := by
  cases C
  rfl

/-- Full high, even-conductor tame-odd First Main product.  `CF` and `CK`
remain explicit even coordinates, and every norm character receives an
arbitrary admissible denominator. -/
theorem firstMain_tameOdd_high_even
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d 0)
    (CK : LamprechtCriticalCoordinate K dK 0)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (normData F K ht hres pi hpi hgen mu) psiF) :
    let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
    let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R CF CK
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : Fintype (NormCharacter F K) := normCharacterFintype F K
    deltaFinite chiK psiK P.upstairs.gamma *
        ∏ mu : NormCharacter F K,
          deltaFinite (normData F K ht hres pi hpi hgen mu) psiF
            (GammaNorm mu) =
      ∏ mu : NormCharacter F K,
        deltaFinite
          (twistData F K ht hres pi hpi hgen chiF hF.conductor_gt_one mu)
          psiF
          (twistGamma F K ht hres pi hpi hgen chiF hF.conductor_gt_one
            psiF GammaF mu) := by
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
    hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
    H R CF CK
  have hcritical : P.upstairs.criticalFactor =
      P.downstairs.criticalFactor ^ Module.finrank F K := by
    cases CF
    cases CK
    simp [P, HighStableOddParameterData.compatiblePhasePair,
      HighStableOddParameterData.upstairsPhase,
      localPhaseOfStationaryClass,
      LocalLamprechtPhaseData.evenOfStationaryClass,
      LocalLamprechtPhaseData.criticalFactor]
  have hpower : deltaFinite chiK psiK P.upstairs.gamma =
      deltaFinite chiF psiF P.downstairs.gamma ^ Module.finrank F K :=
    compatible_deltaFinite_power_of_critical F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R
      CF CK hcritical
  apply high_firstMain_product_of_delta_power F K ht hres pi hpi hgen hodd
    chiF psiF hF GammaF R chiK psiK P.upstairs.gamma
      (by
        have hgamma : P.downstairs.gamma = GammaF := by
          cases CF
          rfl
        rw [hgamma] at hpower
        exact hpower) GammaNorm

/-- Full high, odd-conductor tame-odd First Main product.  The critical
factor is discharged only through the ramified Hasse compatible-pair
theorem, while `CF`, `CK`, `H`, `R`, and all norm denominators remain
explicit. -/
theorem firstMain_tameOdd_high_odd
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d 1)
    (CK : LamprechtCriticalCoordinate K dK 1)
    {ell : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      (HighStableOddParameterData.downstairsOddStationaryPhase F K ht hres pi
        hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R (oddCriticalDelta CF) (oddCriticalDelta_order CF))
      (HighStableOddParameterData.upstairsOddStationaryPhase F K ht hres pi
        hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R (oddCriticalDelta CK) (oddCriticalDelta_order CK))
      ell 0)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F (normData F K ht hres pi hpi hgen mu) psiF) :
    let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
    let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
      hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R CF CK
    letI : Finite (NormCharacter F K) :=
      ramifiedNormCharacter_finite F K ht hres pi hpi hgen
    letI : Fintype (NormCharacter F K) := normCharacterFintype F K
    deltaFinite chiK psiK P.upstairs.gamma *
        ∏ mu : NormCharacter F K,
          deltaFinite (normData F K ht hres pi hpi hgen mu) psiF
            (GammaNorm mu) =
      ∏ mu : NormCharacter F K,
        deltaFinite
          (twistData F K ht hres pi hpi hgen chiF hF.conductor_gt_one mu)
          psiF
          (twistGamma F K ht hres pi hpi hgen chiF hF.conductor_gt_one
            psiF GammaF mu) := by
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let P := HighStableOddParameterData.compatiblePhasePair F K ht hres pi
    hpi hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
    H R CF CK
  have hpower : deltaFinite chiK psiK P.upstairs.gamma =
      deltaFinite chiF psiF P.downstairs.gamma ^ Module.finrank F K := by
    cases CF with
    | odd deltaF hdeltaF =>
      cases CK with
      | odd deltaK hdeltaK =>
        exact compatible_odd_deltaFinite_power F K ht hres pi hpi hgen
          chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R
          deltaF hdeltaF deltaK hdeltaK D
  apply high_firstMain_product_of_delta_power F K ht hres pi hpi hgen hodd
    chiF psiF hF GammaF R chiK psiK P.upstairs.gamma
      (by
        have hgamma : P.downstairs.gamma = GammaF := by
          cases CF
          rfl
        rw [hgamma] at hpower
        exact hpower) GammaNorm

end

end TameOddHigh
end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma

/-- The exact conductor-one branch, with residue compatibility derived from
the actual norm and trace pullbacks. -/
theorem firstMain_tameOdd_one :
    type_of% @TameOddConductorOne.firstMain :=
  TameOddConductorOne.firstMain

/-- The exact stable-high even-conductor branch. -/
theorem firstMain_tameOdd_high_even :
    type_of% @TameOddHigh.firstMain_tameOdd_high_even :=
  TameOddHigh.firstMain_tameOdd_high_even

/-- The exact stable-high odd-conductor branch, using the supplied ramified
Hasse finite-normal-form certificate. -/
theorem firstMain_tameOdd_high_odd :
    type_of% @TameOddHigh.firstMain_tameOdd_high_odd :=
  TameOddHigh.firstMain_tameOdd_high_odd

/-- The four exact computational conductor branches of the tamely ramified
odd-prime-degree First Main Lemma. -/
structure TameOddFirstMainBranches : Prop where
  conductorZero : type_of% @firstMain_tameOdd_zero
  conductorOne : type_of% @firstMain_tameOdd_one
  highEven : type_of% @firstMain_tameOdd_high_even
  highOdd : type_of% @firstMain_tameOdd_high_odd

/-- **First Main Lemma, tamely ramified odd-prime-degree case.**

The bundle keeps the conductor-zero, conductor-one, stable-high even, and
stable-high odd identities separate.  Every field is a literal full
deltaFinite product identity.  The conductor-one residue rows and norm/trace
transports are derived internally.  Quotient-representative, denominator,
and ramified-Hasse inputs remain explicit in the corresponding high branch
instead of being hidden behind a choice. -/
theorem firstMain_tameOdd : TameOddFirstMainBranches where
  conductorZero := firstMain_tameOdd_zero
  conductorOne := firstMain_tameOdd_one
  highEven := firstMain_tameOdd_high_even
  highOdd := firstMain_tameOdd_high_odd

end LanglandsFirstMainLemma
