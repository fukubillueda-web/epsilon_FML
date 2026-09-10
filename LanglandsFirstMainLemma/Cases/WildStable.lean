import LanglandsFirstMainLemma.Parameters.RamifiedHasseComparison
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Lamprecht.StableTwist
import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm

/-!
# Wild odd-prime extensions in the stable range

This file proves Proposition `prop:wild-stable-new` of the authoritative
manuscript.  The lower conductor is kept in the exact form
`m_F(chi_F) = 2 * d + epsilon`, and the stable hypothesis is literally
`t + 1 <= d`.

The complete norm-character group is used throughout.  Its identity is
packaged with conductor zero, while every nonidentity character has the
exact wild conductor `t + 1`.  Stable twisting is applied with the norm
character on the left and with the factor `mu(Gamma / beta)`, where `beta`
is a supplied representative of the stationary quotient class.

The high stable parameter row transports that quotient class through the
denominator-sensitive adjoint of the truncated norm.  Even residual factors
are one.  In the odd branch an exact `RamifiedHasseComparisonData`
certificate compares the complete phases attached to the same transported
representative and ordered denominator pair; in particular no Hasse factor
or translation is discarded.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section NormCharacterData

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (htwild : 0 < t)

/-- Exact local data for every wild norm character.  The identity is retained
as a conductor-zero datum; every other character has conductor `t + 1`. -/
def wildStableNormCharacterData (mu : NormCharacter F K) :
    LocalQuasiCharData F := by
  classical
  exact if hmu : mu = 1 then
      trivialQuasiCharData F
    else
      { character := mu.1
        conductor := t + 1
        isConductor :=
          wildNormCharacter_conductor F K ht hres pi hpi hgen htwild mu hmu }

@[simp]
theorem wildStableNormCharacterData_character (mu : NormCharacter F K) :
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu).character =
      mu.1 := by
  by_cases hmu : mu = 1
  · subst mu
    ext x
    simp [wildStableNormCharacterData]
  · simp only [wildStableNormCharacterData, hmu, ↓reduceDIte]

@[simp]
theorem wildStableNormCharacterData_conductor_one :
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild
      (1 : NormCharacter F K)).conductor = 0 := by
  simp [wildStableNormCharacterData]

theorem wildStableNormCharacterData_conductor_of_ne
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu).conductor =
      t + 1 := by
  simp [wildStableNormCharacterData, hmu]

/-- The manuscript's exact stable inequality bounds every norm-character
conductor, including the identity conductor `0`. -/
theorem wildStableNormCharacterData_conductor_le
    {d : ℕ} (hd : t + 1 ≤ d) (mu : NormCharacter F K) :
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu).conductor ≤
      d := by
  by_cases hmu : mu = 1
  · subst mu
    simp
  · rw [wildStableNormCharacterData_conductor_of_ne
      F K ht hres pi hpi hgen htwild mu hmu]
    exact hd

/-- The norm character is strictly below the unchanged stable conductor. -/
theorem wildStableTwist_conductor_lt
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hd : t + 1 ≤ d) (mu : NormCharacter F K) :
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu).conductor <
      chiF.conductor := by
  have hle := wildStableNormCharacterData_conductor_le
    F K ht hres pi hpi hgen htwild hd mu
  rw [hF.conductor_eq]
  omega

/-- The exact left-oriented stable twist `mu * chiF`. -/
abbrev wildStableTwistData
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hd : t + 1 ≤ d) (mu : NormCharacter F K) : LocalQuasiCharData F :=
  stableTwistData F
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu) chiF
    (wildStableTwist_conductor_lt F K ht hres pi hpi hgen htwild
      chiF hF hd mu)

@[simp]
theorem wildStableTwistData_character
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hd : t + 1 ≤ d) (mu : NormCharacter F K) :
    (wildStableTwistData F K ht hres pi hpi hgen htwild
      chiF hF hd mu).character = mu.1 * chiF.character := by
  rw [stableTwistData_character,
    wildStableNormCharacterData_character]

@[simp]
theorem wildStableTwistData_conductor
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hd : t + 1 ≤ d) (mu : NormCharacter F K) :
    (wildStableTwistData F K ht hres pi hpi hgen htwild
      chiF hF hd mu).conductor = chiF.conductor :=
  rfl

/-- The unchanged common denominator, now regarded as admissible for the
exact stable twist. -/
abbrev wildStableTwistGamma
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hd : t + 1 ≤ d) (mu : NormCharacter F K)
    (psiF : LocalAddCharData F) (GammaF : AdmissibleGamma F chiF psiF) :
    AdmissibleGamma F
      (wildStableTwistData F K ht hres pi hpi hgen htwild
        chiF hF hd mu) psiF :=
  stableTwistAdmissibleGamma F
    (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu) chiF psiF
    (wildStableTwist_conductor_lt F K ht hres pi hpi hgen htwild
      chiF hF hd mu) GammaF

end NormCharacterData

section CompleteNormCharacterProducts

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (htwild : 0 < t)

/-- Evaluation of the complete odd norm-character group at one field unit
has product one.  The fixed-point argument retains the identity term. -/
private theorem wildStableNormCharacter_evaluation_product
    (hodd : Odd (Module.finrank F K)) (x : Fˣ) :
    (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
        (fun mu => (mu.1 x : ℂ)) = 1 := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let f : NormCharacter F K → ℂ := fun mu => (mu.1 x : ℂ)
  have hcard : Fintype.card (NormCharacter F K) = Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card,
      ramifiedNormCharacter_card F K ht hres pi hpi hgen]
  have hoddCard : Odd (Fintype.card (NormCharacter F K)) := by
    rwa [hcard]
  have hpair (mu : NormCharacter F K) : f mu * f mu⁻¹ = 1 := by
    exact congrArg Units.val (by simp : mu.1 x * (mu⁻¹).1 x = (1 : ℂˣ))
  have hfixed (mu : NormCharacter F K) (hmu : mu⁻¹ = mu) : mu = 1 := by
    have hmu2 : mu ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun z : NormCharacter F K => z * mu) hmu.symm).trans
        (by simp)
    have horder2 : orderOf mu ∣ 2 := orderOf_dvd_of_pow_eq_one hmu2
    have horderCard : orderOf mu ∣ Fintype.card (NormCharacter F K) := by
      simpa only [Nat.card_eq_fintype_card] using orderOf_dvd_natCard mu
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hoddCard.coprime_two_right
        horderCard horder2)
  have hone : f (1 : NormCharacter F K) = 1 := by
    simp [f]
  change (∏ mu : NormCharacter F K, f mu) = 1
  simpa [f] using
    (Finset.prod_involution (s := Finset.univ) (f := f)
      (fun mu _hmu => mu⁻¹)
      (fun mu _hmu => hpair mu)
      (fun mu _hmu hfmu hmu => hfmu (hfixed mu hmu ▸ hone))
      (fun mu _hmu => Finset.mem_univ mu⁻¹)
      (fun mu _hmu => inv_inv mu))

/-- The product of the local constants of all norm characters is one.  This
is Corollary `cor:S-product-one`, with the trivial character still present. -/
private theorem wildStableNormCharacter_delta_product
    (hodd : Odd (Module.finrank F K))
    (psiF : LocalAddCharData F)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu)
        psiF) :
    (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
        (fun mu => deltaFinite
          (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu)
          psiF (GammaNorm mu)) = 1 := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype (normCharacterSubgroup F K) := by
    change Fintype (NormCharacter F K)
    exact normCharacterFintype F K
  have hcard : Fintype.card (NormCharacter F K) = Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card,
      ramifiedNormCharacter_card F K ht hres pi hpi hgen]
  have hprimeCard : (Fintype.card (NormCharacter F K)).Prime := by
    rw [hcard]
    exact PrimeCyclicExtension.degree_prime F K
  have hoddCard : Odd (Fintype.card (NormCharacter F K)) := by
    rwa [hcard]
  change (∏ mu : NormCharacter F K,
    deltaFinite
      (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu)
      psiF (GammaNorm mu)) = 1
  exact delta_odd_prime_character_product F (normCharacterSubgroup F K)
    hprimeCard hoddCard psiF
    (fun mu => wildStableNormCharacterData
      F K ht hres pi hpi hgen htwild mu)
    (wildStableNormCharacterData_character
      F K ht hres pi hpi hgen htwild) GammaNorm

/-- Multiplying the exact stable-twist formula over the complete norm-character
group gives the degree-th power of the base local constant. -/
private theorem wildStableTwist_delta_product
    (hodd : Odd (Module.finrank F K))
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hd : t + 1 ≤ d)
    (GammaF : AdmissibleGamma F chiF psiF)
    (R : StationaryClassRepresentative F chiF psiF hF
      (GammaF : Fˣ) GammaF.property) :
    (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
        (fun mu => deltaFinite
          (wildStableTwistData F K ht hres pi hpi hgen htwild
            chiF hF hd mu)
          psiF
          (wildStableTwistGamma F K ht hres pi hpi hgen htwild
            chiF hF hd mu psiF GammaF)) =
      deltaFinite chiF psiF GammaF ^ Module.finrank F K := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  let S := ramifiedNormCharacterFinset F K ht hres pi hpi hgen
  let hr := stableTwist_stationaryDepth F chiF d epsilon
    hF.epsilon_le_one hF.conductor_eq hF.conductor_gt_one
  have hR : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ))
        R.toLamprecht =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        hr GammaF GammaF.property := by
    simpa only [hr, stationaryDepthOfConductorDecomposition] using
      R.toLamprecht_represents
  let beta := stableStationaryRepresentativeUnit F chiF psiF
    hr GammaF R.toLamprecht hR
  let x : Fˣ := (GammaF : Fˣ) / beta
  let A : ℂ := deltaFinite chiF psiF GammaF
  have hcard : S.card = Module.finrank F K := by
    change Fintype.card (NormCharacter F K) = Module.finrank F K
    rw [← Nat.card_eq_fintype_card,
      ramifiedNormCharacter_card F K ht hres pi hpi hgen]
  have heval : S.prod (fun mu => (mu.1 x : ℂ)) = 1 :=
    wildStableNormCharacter_evaluation_product
      F K ht hres pi hpi hgen hodd x
  have htwist (mu : NormCharacter F K) :
      deltaFinite
          (wildStableTwistData F K ht hres pi hpi hgen htwild
            chiF hF hd mu)
          psiF
          (wildStableTwistGamma F K ht hres pi hpi hgen htwild
            chiF hF hd mu psiF GammaF) =
        (mu.1 x : ℂ) * A := by
    simpa only [wildStableTwistData, wildStableTwistGamma,
      wildStableNormCharacterData_character, hr, beta, x, A] using
      (stableTwist F
        (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu)
        chiF psiF d epsilon hF.epsilon_le_one hF.conductor_eq
        hF.conductor_gt_one
        (wildStableNormCharacterData_conductor_le
          F K ht hres pi hpi hgen htwild hd mu)
        GammaF R.toLamprecht hR)
  calc
    S.prod (fun mu => deltaFinite
        (wildStableTwistData F K ht hres pi hpi hgen htwild
          chiF hF hd mu)
        psiF
        (wildStableTwistGamma F K ht hres pi hpi hgen htwild
          chiF hF hd mu psiF GammaF)) =
        S.prod (fun mu => (mu.1 x : ℂ) * A) := by
          apply Finset.prod_congr rfl
          intro mu _hmu
          exact htwist mu
    _ = S.prod (fun mu => (mu.1 x : ℂ)) * S.prod (fun _mu => A) :=
      Finset.prod_mul_distrib
    _ = 1 * A ^ S.card := by rw [heval, Finset.prod_const]
    _ = deltaFinite chiF psiF GammaF ^ Module.finrank F K := by
      rw [one_mul, hcard]

end CompleteNormCharacterProducts

section StablePower

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

omit [PrimeCyclicExtension F K] in
/-- Norm pullback on a base-field unit gives the degree-th power after
evaluation by `chiF`.  The norm points from `K` down to `F`. -/
private theorem wildStable_admissible_power
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (gammaF : Fˣ) :
    (chiK.character (Units.map (algebraMap F K).toMonoidHom gammaF) : ℂ) =
      (chiF.character gammaF : ℂ) ^ Module.finrank F K := by
  have hnorm : Units.map (Algebra.norm F)
      (Units.map (algebraMap F K).toMonoidHom gammaF) =
        gammaF ^ Module.finrank F K := by
    ext
    simp
  rw [hchi, ContinuousQuasiChar.compNorm_apply, hnorm, map_pow]
  exact (Units.coeHom ℂ).map_pow (chiF.character gammaF)
    (Module.finrank F K)

omit [PrimeCyclicExtension F K] in
/-- Trace pullback on a quotient of embedded base-field elements gives the
degree-th power of the downstairs additive value.  The trace points from
`K` down to `F`. -/
private theorem wildStable_additive_power
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    (beta : F) (gammaF : Fˣ) :
    (psiK.character
        (algebraMap F K beta /
          algebraMap F K ((gammaF : Fˣ) : F)) : ℂ) =
      (psiF.character (beta / ((gammaF : Fˣ) : F)) : ℂ) ^
        Module.finrank F K := by
  have htrace : trace F K
      (algebraMap F K beta / algebraMap F K ((gammaF : Fˣ) : F)) =
        Module.finrank F K • (beta / ((gammaF : Fˣ) : F)) := by
    rw [← map_div₀, trace_algebraMap]
  rw [hpsi, ContinuousAddChar.compTrace_apply, htrace]
  exact congrArg Units.val
    (AddChar.map_nsmul_eq_pow psiF.character.toAddChar
      (Module.finrank F K) (beta / ((gammaF : Fˣ) : F)))

omit [PrimeCyclicExtension F K] in
/-- The inverse multiplicative stationary value transports with the same
positive degree-power orientation. -/
private theorem wildStable_multiplicative_power
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (beta : Fˣ) :
    (chiK.character (Units.map (algebraMap F K).toMonoidHom beta) : ℂ)⁻¹ =
      ((chiF.character beta : ℂ)⁻¹) ^ Module.finrank F K := by
  rw [wildStable_admissible_power F K chiF chiK hchi beta, inv_pow]

end StablePower

section FirstMain

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

local instance wildStableDegreeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-! ## Residual comparison without losing the representative translation -/

/-- The parity-exact residual input for the compatible stable-high pair.
The even/even branch is propositionally trivial because both critical
factors are definitionally one.  The odd/odd branch contains the complete
ramified Hasse certificate for the phases built from the supplied quotient
representative and ordered denominator pair.  Mixed parities are excluded. -/
def WildStableResidualComparison
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK) : Prop :=
  match CF, CK with
  | .even, .even => True
  | .odd deltaF hdeltaF, .odd deltaK hdeltaK =>
      Nonempty (RamifiedHasseComparisonData F K chiF psiF chiK psiK
        (HighStableOddParameterData.downstairsOddStationaryPhase
          F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
            hodd hd gammaF hgammaF H R deltaF hdeltaF)
        (HighStableOddParameterData.upstairsOddStationaryPhase
          F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
            hodd hd gammaF hgammaF H R deltaK hdeltaK)
        (Module.finrank F K) t)
  | _, _ => False

/-- Odd degree and the exact stable-high conductor relation force the two
actual conductor remainders to agree; no parity agreement is assumed. -/
private theorem wildStable_conductorParity_eq
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
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

/-- The residual factor has the exact positive degree-power orientation.
The odd branch invokes the public stable-pair `ramifiedHasseComparison`, so
the residual minus sign and every representative translation remain in the
certificate. -/
theorem wildStableResidualComparison_criticalFactor_eq
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
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK)
    (C : WildStableResidualComparison F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R CF CK) :
    let P := HighStableOddParameterData.compatiblePhasePair
      F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
        hodd hd gammaF hgammaF H R CF CK
    P.upstairs.criticalFactor =
      P.downstairs.criticalFactor ^ Module.finrank F K := by
  have hepsilonK := wildStable_conductorParity_eq
    F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
      hodd hd gammaF hgammaF H
  subst epsilonK
  cases epsilon with
  | zero =>
      cases CF
      cases CK
      simp [HighStableOddParameterData.compatiblePhasePair,
        HighStableOddParameterData.upstairsPhase,
        localPhaseOfStationaryClass,
        LocalLamprechtPhaseData.evenOfStationaryClass,
        LocalLamprechtPhaseData.criticalFactor]
  | succ e =>
      have he : e = 0 := by
        have := hF.epsilon_le_one
        omega
      subst e
      cases CF with
      | odd deltaF hdeltaF =>
          cases CK with
          | odd deltaK hdeltaK =>
              rcases C with ⟨D⟩
              exact ramifiedHasseComparison F K ht hres pi hpi hgen
                chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
                  H R deltaF hdeltaF deltaK hdeltaK D

/-- The common nonresidual Lamprecht factor supplied by the quotient-level
stable high row is the degree-th power of the downstairs factor. -/
private theorem wildStable_baseFactor_power
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
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK) :
    let H := highConductorParameter_stableOdd F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
    let P := HighStableOddParameterData.compatiblePhasePair
      F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
        hodd hd gammaF hgammaF H R CF CK
    P.upstairs.admissibleFactor * P.upstairs.elementaryFactor =
      (P.downstairs.admissibleFactor * P.downstairs.elementaryFactor) ^
        Module.finrank F K := by
  dsimp only
  let H := highConductorParameter_stableOdd F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K).toMonoidHom gammaF, H.commonDenominator⟩
  let RK := HighStableOddParameterData.upstairsRepresentative
    F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
      hodd hd gammaF hgammaF H R
  let lower := localPhaseOfStationaryClass hF GammaF R CF
  let upper := localPhaseOfStationaryClass hK GammaK RK CK
  change upper.admissibleFactor * upper.elementaryFactor =
    (lower.admissibleFactor * lower.elementaryFactor) ^ Module.finrank F K
  have hRKcoe : (RK.representative : K) =
      algebraMap F K (R.representative : F) :=
    HighStableOddParameterData.upstairsRepresentative_coe
      F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
        hodd hd gammaF hgammaF H R
  have hRKunit : RK.unit =
      Units.map (algebraMap F K).toMonoidHom R.unit := by
    apply Units.ext
    exact hRKcoe
  have hadmissibleRaw := wildStable_admissible_power
    F K chiF chiK hchi gammaF
  have hadditiveRaw := wildStable_additive_power F K psiF psiK hpsi
    (R.representative : F) gammaF
  have hmultiplicativeRaw := wildStable_multiplicative_power
    F K chiF chiK hchi R.unit
  have harg :
      (RK.representative : K) / ((GammaK : Kˣ) : K) =
        algebraMap F K (R.representative : F) /
          algebraMap F K ((gammaF : Fˣ) : F) := by
    rw [hRKcoe]
    rfl
  have hadditiveRK :
      (psiK.character
        ((RK.representative : K) / ((GammaK : Kˣ) : K)) : ℂ) =
        (psiF.character
          ((R.representative : F) / ((GammaF : Fˣ) : F)) : ℂ) ^
            Module.finrank F K := by
    calc
      _ = (psiK.character
          (algebraMap F K (R.representative : F) /
            algebraMap F K ((gammaF : Fˣ) : F)) : ℂ) :=
        congrArg (fun y : K => (psiK.character y : ℂ)) harg
      _ = _ := by simpa only [GammaF] using hadditiveRaw
  have hmultiplicativeRK :
      (chiK.character RK.unit : ℂ)⁻¹ =
        ((chiF.character R.unit : ℂ)⁻¹) ^ Module.finrank F K :=
    (congrArg (fun u : Kˣ => (chiK.character u : ℂ)⁻¹)
      hRKunit).trans hmultiplicativeRaw
  have hadmissiblePhase :
      upper.admissibleFactor =
        lower.admissibleFactor ^ Module.finrank F K := by
    dsimp only [upper, lower]
    rw [localPhaseOfStationaryClass_admissibleFactor,
      localPhaseOfStationaryClass_admissibleFactor]
    simpa only [GammaF, GammaK] using hadmissibleRaw
  have hadditivePhase :
      upper.elementaryAdditiveFactor =
        lower.elementaryAdditiveFactor ^ Module.finrank F K := by
    dsimp only [upper, lower]
    rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor,
      LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryAdditiveFactor]
    exact hadditiveRK
  have hmultiplicativePhase :
      upper.elementaryMultiplicativeFactor =
        lower.elementaryMultiplicativeFactor ^ Module.finrank F K := by
    dsimp only [upper, lower]
    rw [LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor,
      LocalLamprechtPhaseData.localPhaseOfStationaryClass_elementaryMultiplicativeFactor]
    exact hmultiplicativeRK
  rw [LocalLamprechtPhaseData.elementaryFactor_eq_separated,
    LocalLamprechtPhaseData.elementaryFactor_eq_separated,
    hadmissiblePhase, hadditivePhase, hmultiplicativePhase]
  simp only [mul_pow]

/-- The stable high local constant itself is the degree-th power downstairs.
The residual certificate distinguishes the even factor `1` from the full odd
Hasse comparison. -/
private theorem wildStable_delta_power
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
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK) :
    let H := highConductorParameter_stableOdd F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
    let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
    let GammaK : AdmissibleGamma K chiK psiK :=
      ⟨Units.map (algebraMap F K).toMonoidHom gammaF, H.commonDenominator⟩
    WildStableResidualComparison F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
          H R CF CK →
      deltaFinite chiK psiK GammaK =
        deltaFinite chiF psiF GammaF ^ Module.finrank F K := by
  dsimp only
  intro C
  let H := highConductorParameter_stableOdd F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K).toMonoidHom gammaF, H.commonDenominator⟩
  let P := HighStableOddParameterData.compatiblePhasePair
    F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
      hodd hd gammaF hgammaF H R CF CK
  have hgammaDown : P.downstairs.gamma = GammaF := by
    cases CF <;> rfl
  have hgammaUp : P.upstairs.gamma = GammaK := by
    cases CK <;> rfl
  have hbase := wildStable_baseFactor_power F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF R CF CK
  have hcritical := wildStableResidualComparison_criticalFactor_eq
    F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hchi hpsi
      hodd hd gammaF hgammaF H R CF CK C
  change deltaFinite chiK psiK GammaK =
    deltaFinite chiF psiF GammaF ^ Module.finrank F K
  rw [← hgammaUp, ← hgammaDown,
    P.upstairs.deltaFinite_eq_completeFactor,
    P.downstairs.deltaFinite_eq_completeFactor]
  simp only [LocalLamprechtPhaseData.completeFactor,
    LocalLamprechtPhaseData.stationaryFactor]
  calc
    P.upstairs.admissibleFactor *
          (P.upstairs.elementaryFactor * P.upstairs.criticalFactor) =
        (P.upstairs.admissibleFactor * P.upstairs.elementaryFactor) *
          P.upstairs.criticalFactor := by ring
    _ = (P.downstairs.admissibleFactor * P.downstairs.elementaryFactor) ^
          Module.finrank F K *
        P.downstairs.criticalFactor ^ Module.finrank F K := by
          rw [hbase, hcritical]
    _ = (P.downstairs.admissibleFactor *
          (P.downstairs.elementaryFactor * P.downstairs.criticalFactor)) ^
            Module.finrank F K := by
          simp only [mul_pow]
          ring

/-- **First Main Lemma, wild odd-prime stable range.**

Let `m_F(chiF) = 2*d + epsilon > 1`, let the wild lower break be `t > 0`,
and assume exactly `t + 1 <= d`.  The complete product below includes the
trivial norm character.  Nontrivial norm characters have exact conductor
`t + 1`; every twist is `mu * chiF`, uses the same denominator, and evaluates
the stable factor in the direction `mu(GammaF / beta)`.

The representative `R` belongs to the downstairs stationary quotient.  The
stable high parameter row maps it to the upstairs quotient using the common
ordered denominator pair.  `C` is either the literal even residual factor or
the full odd `RamifiedHasseComparisonData` comparison, including all residual
signs and representative translations. -/
theorem firstMain_wildStable
    (htwild : 0 < t)
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
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (CF : LamprechtCriticalCoordinate F d epsilon)
    (CK : LamprechtCriticalCoordinate K dK epsilonK)
    (GammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildStableNormCharacterData F K ht hres pi hpi hgen htwild mu)
        psiF) :
    let H := highConductorParameter_stableOdd F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
    let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
    let GammaK : AdmissibleGamma K chiK psiK :=
      ⟨Units.map (algebraMap F K).toMonoidHom gammaF, H.commonDenominator⟩
    WildStableResidualComparison F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
          H R CF CK →
      deltaFinite chiK psiK GammaK *
          (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
            (fun mu => deltaFinite
              (wildStableNormCharacterData F K ht hres pi hpi hgen
                htwild mu) psiF (GammaNorm mu)) =
        (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod
          (fun mu => deltaFinite
            (wildStableTwistData F K ht hres pi hpi hgen htwild
              chiF hF hd mu)
            psiF
            (wildStableTwistGamma F K ht hres pi hpi hgen htwild
              chiF hF hd mu psiF GammaF)) := by
  dsimp only
  intro C
  let H := highConductorParameter_stableOdd F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
  let GammaF : AdmissibleGamma F chiF psiF := ⟨gammaF, hgammaF⟩
  let GammaK : AdmissibleGamma K chiK psiK :=
    ⟨Units.map (algebraMap F K).toMonoidHom gammaF, H.commonDenominator⟩
  have hupper := wildStable_delta_power F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF R CF CK C
  have hnorm := wildStableNormCharacter_delta_product
    F K ht hres pi hpi hgen htwild hodd psiF GammaNorm
  have htwists := wildStableTwist_delta_product
    F K ht hres pi hpi hgen htwild hodd chiF psiF hF hd GammaF R
  rw [hupper, hnorm, htwists, mul_one]

end FirstMain

end

end LanglandsFirstMainLemma
