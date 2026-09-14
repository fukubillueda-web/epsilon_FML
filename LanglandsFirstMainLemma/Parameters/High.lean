import LanglandsFirstMainLemma.Parameters.HighUnramifiedStable
import LanglandsFirstMainLemma.Parameters.HighIntermediate
import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Parameters.HighProduct

/-!
# Public high-conductor stationary-class table

This file is the public case-indexed interface to the four completed
high-parameter components.  It does not choose any new stationary
representative.  In particular, independent existential packages supplied
by different component theorems are not identified.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

/-! ## Exhaustive numerical splits -/

/-- Prime degree gives the unramified/totally-ramified split used to select
the first row or one of the four ramified rows. -/
theorem highConductor_ramification_cases
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] :
    ramificationIndex F K = 1 ∨ residueDegree F K = 1 :=
  unramified_or_totallyRamified F K

/-- The prime extension degree is exactly quadratic or odd. -/
theorem highConductor_degree_cases
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K] :
    Module.finrank F K = 2 ∨ Odd (Module.finrank F K) :=
  degree_eq_two_or_odd F K

/-- In the odd ramified high range, the stable and non-stable inequalities
cover all stationary conductors. -/
theorem highConductor_oddRange_cases
    {t m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (hhigh : t + 1 ≤ m) :
    t + 1 ≤ d ∨
      (0 < t ∧ t + 1 ≤ m ∧ m < 2 * (t + 1)) := by
  by_cases hd : t + 1 ≤ d
  · exact Or.inl hd
  · right
    have hepsilon := h.epsilon_le_one
    have hm := h.conductor_gt_one
    rw [h.conductor_eq] at hhigh hm ⊢
    omega

/-- The stable and odd non-stable inequalities do not overlap. -/
theorem highConductor_oddRange_disjoint
    {t m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon) :
    ¬ (t + 1 ≤ d ∧ m < 2 * (t + 1)) := by
  rw [h.conductor_eq]
  omega

/-- The quadratic ramified cases split at `t=0` versus `t>0`. -/
theorem highConductor_quadraticBreak_cases (t : ℕ) : t = 0 ∨ 0 < t :=
  Nat.eq_zero_or_pos t

/-! ## Trace-stable rows -/

/-- The complete unramified row.  Its stationary equality is an equality in
the literal depth-`d` coefficient quotient for the ordered common-denominator
pair. -/
structure HighUnramifiedParameterData
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hunr : ramificationIndex F K = 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) : Prop where
  multiplicativeConductor : chiK.conductor = chiF.conductor
  additiveConductor : psiK.conductor = psiF.conductor
  sourceDecomposition :
    IsStationaryConductorDecomposition chiK.conductor d epsilon
  commonDenominator :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
  stationaryClass :
    stationaryCoefficientClass K chiK psiK
        (highParameter_unramified_sourceDecomposition F K chiF chiK
          hF hchi hunr)
        (Units.map (algebraMap F K) gammaF)
        (highParameter_unramified_commonDenominator F K chiF chiK psiF psiK
          hchi hpsi hunr gammaF hgammaF) =
      denominatorScaledAlgebraMap F K d d (by simp [hunr]) gammaF
        (Units.map (algebraMap F K) gammaF)
        (by simp [normPolynomialDenominatorRatio])
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)

/-- Assemble the unramified row from the completed component theorem. -/
theorem highConductorParameter_unramified
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hunr : ramificationIndex F K = 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    HighUnramifiedParameterData F K chiF chiK psiF psiK
      hF hchi hpsi hunr gammaF hgammaF := by
  exact ⟨
    highParameter_unramified_conductor_eq F K chiF chiK hchi hunr,
    highParameter_unramified_additiveConductor_eq F K psiF psiK hpsi hunr,
    highParameter_unramified_sourceDecomposition F K chiF chiK hF hchi hunr,
    highParameter_unramified_commonDenominator F K chiF chiK psiF psiK
      hchi hpsi hunr gammaF hgammaF,
    highParameter_unramified F K chiF chiK psiF psiK hF hchi hpsi hunr
      gammaF hgammaF⟩

/-- The stable odd-degree ramified row at the exact boundary `t+1 <= d`. -/
structure HighStableOddParameterData
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
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : t + 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) : Prop where
  conductor : chiK.conductor =
    herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1
  conductorRelation :
    chiK.conductor + (Module.finrank F K - 1) * (t + 1) =
      Module.finrank F K * chiF.conductor
  commonDenominator :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
  stationaryClass :
    ∃ hdepth : dK ≤ ramificationIndex F K * d,
      stationaryCoefficientClass K chiK psiK hK
          (Units.map (algebraMap F K) gammaF)
          (highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
            chiF chiK psiF psiK hchi hpsi (by
              rw [hF.conductor_eq]
              omega) gammaF hgammaF) =
        denominatorScaledAlgebraMap F K d dK hdepth gammaF
          (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)

/-- Assemble the stable odd-degree row from the completed component. -/
theorem highConductorParameter_stableOdd
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
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : t + 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF := by
  have hm : t + 1 < chiF.conductor := by
    rw [hF.conductor_eq]
    omega
  exact ⟨
    highParameter_ramified_conductor_eq F K ht hres pi hpi hgen
      chiF chiK hchi hm,
    highParameter_ramified_conductor_relation F K ht hres pi hpi hgen
      chiF chiK hchi hm,
    highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
      chiF chiK psiF psiK hchi hpsi hm gammaF hgammaF,
    highParameter_stableOdd F K ht hres pi hpi hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF⟩

/-- The tame quadratic row, whose actual upstairs decomposition is
`(chiF.conductor - 1, 1)`. -/
structure HighTameQuadraticParameterData
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
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2) (htzero : t = 0)
    (htame : residueCharacteristic F ≠ 2)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) : Prop where
  conductorRelation : chiK.conductor + 1 = 2 * chiF.conductor
  sourceDecomposition :
    IsStationaryConductorDecomposition chiK.conductor
      (chiF.conductor - 1) 1
  variableDepth : chiF.conductor - 1 + 1 = chiF.conductor
  commonDenominator :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
  stationaryClass :
    ∃ hdepth : chiF.conductor - 1 ≤ ramificationIndex F K * d,
      stationaryCoefficientClass K chiK psiK
          (highParameter_tameQuadratic_sourceDecomposition
            F K ht hres pi hpi hgen chiF chiK hF hchi hdegree htzero)
          (Units.map (algebraMap F K) gammaF)
          (highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
            chiF chiK psiF psiK hchi hpsi (by
              rw [htzero]
              exact hF.conductor_gt_one) gammaF hgammaF) =
        denominatorScaledAlgebraMap F K d (chiF.conductor - 1)
          hdepth gammaF (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)

/-- Assemble the tame quadratic row from the completed component. -/
theorem highConductorParameter_tameQuadratic
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
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2) (htzero : t = 0)
    (htame : residueCharacteristic F ≠ 2)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    HighTameQuadraticParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree htzero htame
        gammaF hgammaF := by
  have hm : t + 1 < chiF.conductor := by
    rw [htzero]
    exact hF.conductor_gt_one
  exact ⟨
    highParameter_tameQuadratic_conductor_relation F K ht hres pi hpi hgen
      chiF chiK hchi hdegree htzero hF.conductor_gt_one,
    highParameter_tameQuadratic_sourceDecomposition F K ht hres pi hpi hgen
      chiF chiK hF hchi hdegree htzero,
    highParameter_tameQuadratic_variableDepth F K ht hres pi hpi hgen
      chiF hF.conductor_gt_one,
    highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
      chiF chiK psiF psiK hchi hpsi hm gammaF hgammaF,
    highParameter_tameQuadratic F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree htzero htame
        gammaF hgammaF⟩

/-! ## Odd non-stable row -/

/-- The full conclusion of `highParameter_intermediate`, retained literally
as one field so that none of its dependent quotient witnesses, actual
conductors, representative ambiguities, or denominator proofs is weakened. -/
structure HighOddIntermediateParameterData
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
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1))
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) : Prop where
  parameters :
    chiK.conductor = t + 1 +
        Module.finrank F K * (chiF.conductor - (t + 1)) ∧
      (∀ mu : NormCharacter F K,
        (ramifiedNormCharacterOrbitTwistData
          F K ht hres pi hpi hgen chiF mu).conductor = chiF.conductor) ∧
      ∃ h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
          chiF.conductor d epsilon,
        let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
        ∃ (a : lattice F
              ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
          (b : lattice F 0) (alpha beta : Fˣ) (alpha1 beta1 : Kˣ),
          (a : F) = (alpha : F) ∧
          (b : F) = (beta : F) ∧
          IsSubcriticalNormRepresentative F K
              ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
              ((t + 1) / 2) alpha alpha1 ∧
          IsSubcriticalNormRepresentative F K 0 d beta beta1 ∧
          latticeQuotientMk F
              (sub_le_sub_left
                (highParameter_intermediate_normCharacterDepth
                  F K ht hres pi hpi hgen htpos).int_le_conductor
                (chiF.conductor : ℤ)) a =
            stationaryNumeratorClass F
              (quasiCharDataOfIsConductor F tau.1 (t + 1)
                (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
                  (highParameter_intermediate_indexOne_ne_one
                    F K ht hres pi hpi hgen)))
              psiF (chiF.conductor : ℤ)
              (highParameter_intermediate_normCharacterDepth
                F K ht hres pi hpi hgen htpos)
              gammaF hgammaF ∧
          latticeQuotientMk F (by omega) b =
            stationaryCoefficientClass F chiF psiF hF gammaF hgammaF ∧
          (∀ y : lattice K (((t + 2) / 2 : ℕ) : ℤ),
            psiF.character
                (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) =
              psiF.character
                ((-(norm F K (alpha1 : K))) * trace F K (y : K) /
                  (gammaF : F))) ∧
          ∃ hcandidate :
              algebraMap F K (norm F K (beta1 : K)) -
                  (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
                    (alpha1 : K) ∈ lattice K 0,
            let candidate : lattice K 0 :=
              ⟨algebraMap F K (norm F K (beta1 : K)) -
                  (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
                    (alpha1 : K), hcandidate⟩
            latticeQuotientMk K (by omega) candidate =
                normPolynomialAdjoint F K h psiF psiK gammaF
                  (Units.map (algebraMap F K) gammaF) hgammaF
                  (highParameter_intermediate_commonDenominator
                    F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal
                    hchi hpsi hlower gammaF hgammaF)
                  (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) ∧
              latticeQuotientMk K (by omega) candidate =
                stationaryCoefficientClass K chiK psiK hK
                  (Units.map (algebraMap F K) gammaF)
                  (highParameter_intermediate_commonDenominator
                    F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal
                    hchi hpsi hlower gammaF hgammaF) ∧
              ∀ j : ZMod (Module.finrank F K),
                let p := Module.finrank F K
                let hchar := residueCharacteristic_eq_degree_of_positive_break
                  F K ht htpos pi hpi hgen
                let lam := highIntermediateTeichmullerScalar F p hchar j
                let mu := ramifiedNormCharacterZModEquiv
                  F K ht hres pi hpi hgen (Multiplicative.ofAdd j)
                let twist := ramifiedNormCharacterOrbitTwistData
                  F K ht hres pi hpi hgen chiF mu
                ∃ (hJ : IsStationaryConductorDecomposition
                    twist.conductor d epsilon)
                  (hgammaJ : ord F (gammaF : F) =
                    (((twist.conductor : ℤ) + psiF.conductor : ℤ) :
                      WithTop ℤ))
                  (hlinearMem : norm F K (beta1 : K) +
                    lam * norm F K (alpha1 : K) ∈ lattice F 0)
                  (hnormMem : norm F K ((beta1 : K) +
                    algebraMap F K lam * (alpha1 : K)) ∈ lattice F 0),
                  latticeQuotientMk F (Int.natCast_nonneg d)
                      ⟨norm F K ((beta1 : K) +
                        algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
                    latticeQuotientMk F (Int.natCast_nonneg d)
                      ⟨norm F K (beta1 : K) +
                        lam * norm F K (alpha1 : K), hlinearMem⟩ ∧
                  latticeQuotientMk F (Int.natCast_nonneg d)
                      ⟨norm F K ((beta1 : K) +
                        algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
                    stationaryCoefficientClass F twist psiF hJ
                      gammaF hgammaJ

/-- Assemble the odd non-stable row without changing its dependent
witnesses. -/
theorem highConductorParameter_oddIntermediate
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
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1))
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    HighOddIntermediateParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF := by
  exact ⟨highParameter_intermediate F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
      hlower hupper gammaF hgammaF⟩

/-! ## Wild quadratic row -/

/-- The completed simultaneous wild quadratic package.  Its representative
data retain the essential correction `delta : U_F^t` in every formula. -/
structure HighWildQuadraticParameterData
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
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) : Prop where
  parameters : Nonempty (WildQuadraticHighParameterData
    F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF)

/-- Assemble the wild quadratic row from the completed component. -/
theorem highConductorParameter_wildQuadratic
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
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    HighWildQuadraticParameterData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh
        hchi hpsi tau htau gammaF hgammaF := by
  exact ⟨highParameter_wildQuadratic F K ht hres pi hpi hgen
    hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh
      hchi hpsi tau htau gammaF hgammaF⟩

/-! ## Critical drops and endpoints -/

/-- Exact critical cancellation interface.  A genuine conductor drop above
one is reconstructed at its actual conductor, while conductors zero and one
have no stationary depth. -/
structure HighIntermediateCriticalData
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
      ({pi} : Set (ringOfIntegers K)) = ⊤) : Prop where
  criticalNoCancellation : ∀
      (chiF : LocalQuasiCharData F)
      (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
      (hcritical : chiF.conductor = t + 1)
      (mu : NormCharacter F K) (hmu : mu ≠ 1)
      (psiF : LocalAddCharData F) (M : ℤ) {r : ℕ}
      (hr : IsLamprechtStationaryDepth (t + 1) r)
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        ((M + psiF.conductor : ℤ) : WithTop ℤ)),
    stationaryLeadingClassProjection F M hr
      (stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psiF M hr gammaF hgammaF +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chiF.character (t + 1) (by
            simpa only [hcritical] using chiF.isConductor))
          psiF M hr gammaF hgammaF) ≠ 0
  stationaryClassAfterDrop : ∀
      (chiF : LocalQuasiCharData F)
      (hcritical : chiF.conductor = t + 1)
      (mu : NormCharacter F K) (hmu : mu ≠ 1)
      (q' : ℕ)
      (hprod : IsMultiplicativeConductor F (mu.1 * chiF.character) q')
      (hdrop : q' < t + 1) (hq' : 1 < q')
      (psiF : LocalAddCharData F) (M : ℤ) {r : ℕ}
      (hr : IsLamprechtStationaryDepth (t + 1) r)
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        ((M + psiF.conductor : ℤ) : WithTop ℤ)),
    droppedStationaryClassRestriction F
        (quasiCharDataOfIsConductor F (mu.1 * chiF.character) q' hprod)
        psiF M hr hdrop hq' gammaF hgammaF =
      stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psiF M hr gammaF hgammaF +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chiF.character (t + 1) (by
            simpa only [hcritical] using chiF.isConductor))
          psiF M hr gammaF hgammaF
  noStationaryClassAtEndpoint : ∀
      (prod : LocalQuasiCharData F) (hprod : prod.conductor ≤ 1),
    ¬ ∃ r : ℕ, IsLamprechtStationaryDepth prod.conductor r

/-- Assemble the critical/drop/endpoint interface from `HighIntermediate`. -/
theorem highConductorParameter_critical
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
      ({pi} : Set (ringOfIntegers K)) = ⊤) :
    HighIntermediateCriticalData F K ht hres pi hpi hgen := by
  exact ⟨
    highParameter_intermediate_critical_noCancellation
      F K ht hres pi hpi hgen,
    highParameter_intermediate_stationaryClass_afterDrop
      F K ht hres pi hpi hgen,
    highParameter_intermediate_noStationaryClass_of_endpoint
      F K ht hres pi hpi hgen⟩

/-! ## Universal public table -/

/-- The public high-conductor table.  Its five named case fields are the five
mathematical rows with their own exact hypotheses.  `critical` records the
permitted conductor-drop behavior, and `highProduct` retains the two
formula-different norm congruences at their exact unit-quotient depths. -/
structure HighConductorParameterTable : Prop where
  ramificationCases : ∀
      (F K : Type)
      [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Algebra F K] [ValuativeExtension F K]
      [Module.Free F K] [Module.Finite F K]
      [PrimeCyclicExtension F K],
    ramificationIndex F K = 1 ∨ residueDegree F K = 1
  degreeCases : ∀
      (F K : Type)
      [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Algebra F K] [ValuativeExtension F K]
      [Module.Free F K] [Module.Finite F K]
      [PrimeCyclicExtension F K],
    Module.finrank F K = 2 ∨ Odd (Module.finrank F K)
  oddRangeCases : ∀ {t m d epsilon : ℕ},
    IsStationaryConductorDecomposition m d epsilon → t + 1 ≤ m →
      t + 1 ≤ d ∨ (0 < t ∧ t + 1 ≤ m ∧ m < 2 * (t + 1))
  oddRangeDisjoint : ∀ {t m d epsilon : ℕ},
    IsStationaryConductorDecomposition m d epsilon →
      ¬ (t + 1 ≤ d ∧ m < 2 * (t + 1))
  quadraticBreakCases : ∀ t : ℕ, t = 0 ∨ 0 < t
  unramified : ∀
      (F K : Type)
      [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Algebra F K] [ValuativeExtension F K]
      [Module.Free F K] [Module.Finite F K]
      [PrimeCyclicExtension F K]
      (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
      (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
      {d epsilon : ℕ}
      (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
      (hchi : chiK.character = chiF.character.compNorm)
      (hpsi : psiK.character = psiF.character.compTrace)
      (hunr : ramificationIndex F K = 1)
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    HighUnramifiedParameterData F K chiF chiK psiF psiK
      hF hchi hpsi hunr gammaF hgammaF
  stableOdd : ∀
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
      {d epsilon dK epsilonK : ℕ}
      (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
      (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
      (hchi : chiK.character = chiF.character.compNorm)
      (hpsi : psiK.character = psiF.character.compTrace)
      (hodd : Odd (Module.finrank F K))
      (hd : t + 1 ≤ d)
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
  tameQuadratic : ∀
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
      {d epsilon : ℕ}
      (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
      (hchi : chiK.character = chiF.character.compNorm)
      (hpsi : psiK.character = psiF.character.compTrace)
      (hdegree : Module.finrank F K = 2) (htzero : t = 0)
      (htame : residueCharacteristic F ≠ 2)
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    HighTameQuadraticParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hchi hpsi hdegree htzero htame
        gammaF hgammaF
  oddIntermediate : ∀
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
      {d epsilon dK epsilonK : ℕ}
      (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
      (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
      (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
      (hchi : chiK.character = chiF.character.compNorm)
      (hpsi : psiK.character = psiF.character.compTrace)
      (hodd : Odd (Module.finrank F K))
      (htpos : 0 < t)
      (hlower : t + 1 ≤ chiF.conductor)
      (hupper : chiF.conductor < 2 * (t + 1))
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    HighOddIntermediateParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF
  wildQuadratic : ∀
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
      (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
      (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
      (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
      {d epsilon dK epsilonK : ℕ}
      (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
      (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
      (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
      (hhigh : t + 1 ≤ chiF.conductor)
      (hchi : chiK.character = chiF.character.compNorm)
      (hpsi : psiK.character = psiF.character.compTrace)
      (tau : NormCharacter F K) (htau : tau ≠ 1)
      (gammaF : Fˣ)
      (hgammaF : ord F (gammaF : F) =
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    HighWildQuadraticParameterData F K ht hres pi hpi hgen
      hdegree htpos chiF chiK psiF psiK hF hK hminimal hhigh
        hchi hpsi tau htau gammaF hgammaF
  critical : ∀
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
        ({pi} : Set (ringOfIntegers K)) = ⊤),
    HighIntermediateCriticalData F K ht hres pi hpi hgen
  highProduct : ∀
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
        ({pi} : Set (ringOfIntegers K)) = ⊤),
    HighProductBranch F K ht hres pi hpi hgen

/-- **Complete public high-conductor stationary-class table.**  This is a
pure assembly of the four completed component nodes. -/
theorem highConductorParameterTable : HighConductorParameterTable where
  ramificationCases := highConductor_ramification_cases
  degreeCases := highConductor_degree_cases
  oddRangeCases := highConductor_oddRange_cases
  oddRangeDisjoint := highConductor_oddRange_disjoint
  quadraticBreakCases := highConductor_quadraticBreak_cases
  unramified := highConductorParameter_unramified
  stableOdd := highConductorParameter_stableOdd
  tameQuadratic := highConductorParameter_tameQuadratic
  oddIntermediate := highConductorParameter_oddIntermediate
  wildQuadratic := highConductorParameter_wildQuadratic
  critical := highConductorParameter_critical
  highProduct := highParameter_product

end

end LanglandsFirstMainLemma
