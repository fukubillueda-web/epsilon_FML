import LanglandsFirstMainLemma.Parameters.PhaseReduction.Range
import LanglandsFirstMainLemma.Parameters.PhaseReduction.StationaryData
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ResidualCoordinates
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ResidualTransport
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ParameterTablePhases
import LanglandsFirstMainLemma.Parameters.PhaseReduction.FirstMainFactors
import LanglandsFirstMainLemma.Parameters.PhaseReduction.FactorSeparation
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.Core
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.AssemblyInputs
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.ResidualRowCore
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.HighAssembly
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.HighResidualRows
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.LowAssembly
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.LowResidualRows
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.HighNormLiteralTransport
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Quadratic.Core
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Quadratic.HighProvenance
import LanglandsFirstMainLemma.Parameters.PhaseReduction.Quadratic.LowProvenance

/-!
# Exact reduction of the First-Main error term to residual phases

This file stops before any finite-field phase cancellation.  Its local API
starts from the stationary numerator quotient class and accepts a field
representative only as supplied data.  In odd conductor the elementary
stationary value and the Hasse-sum phase remain one complete factor.

The global API expands the definition of `errorTerm` into four separately
named quotients: endpoint, admissible-character, elementary stationary, and
critical/Hasse factors.  The exact odd-prime and wild-quadratic assembly
records refine those quotients without asserting that a residual phase is
one.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Public reduction result -/

/-- The structured public result of this node.  Its high field retains every
row of `HighConductorParameterTable`, including the actual-conductor drop
interface and the wild-quadratic correction unit.  Its low field forwards the
simultaneous existential representative package at precisely the permitted
subcritical depths. -/
structure PhaseParameterTableDispatch : Prop where
  rangeCases : ∀ t m : ℕ, PhaseParameterRange t m
  boundaryIsLow : ∀ t : ℕ, PhaseParameterRange t (t + 1)
  rangesDisjoint : ∀ {t m : ℕ}, ¬ (m ≤ t + 1 ∧ t + 1 < m)
  highParameters : HighConductorParameterTable
  lowParameters : ∀
      (F K : Type)
      [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Algebra F K] [ValuativeExtension F K]
      [Module.Free F K] [Module.Finite F K]
      [PrimeCyclicExtension F K]
      {t d epsilon : ℕ}
      (ht : PrimeCyclicExtension.IsLowerBreak F K t)
      (hres : residueDegree F K = 1)
      (pi : ringOfIntegers K)
      (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
      (hgen : Algebra.adjoin (ringOfIntegers F)
        ({pi} : Set (ringOfIntegers K)) = ⊤)
      (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
      (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
      (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
      (hchi : chiK.character = chiF.character.compNorm)
      (hpsi : psiK.character = psiF.character.compTrace)
      (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
      (hLow : chiF.conductor ≤ t + 1)
      (delta : Fˣ) (epsilon₁ : Kˣ)
      (hdelta : ord F (delta : F) =
        ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
      (hepsilon₁ : ord K (epsilon₁ : K) =
        (((t + 1 - chiF.conductor : ℕ) : ℤ) : WithTop ℤ)),
    let hT : 2 ≤ t + 1 := by
      have hm := hF.conductor_gt_one
      omega
    let gammaF := lowGammaF F K delta epsilon₁
    let gammaK := lowGammaK F K delta epsilon₁
    let hgammaF := lowGammaF_order (t := t) F K hres
      chiF psiF delta epsilon₁ hdelta hepsilon₁ hLow
    let hgammaK := lowGammaK_order F K ht hres pi hpi hgen
      chiF chiK psiF psiK hminimal hchi hpsi delta epsilon₁
        hdelta hepsilon₁ hLow
    let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
    ∃ P : LowStationaryNormRepresentativePair F K
        (lowCriticalFloorDepth t) d
        (stationaryCoefficientClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
              (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
          psiF (lowCriticalConductorDecomposition (t := t) hT) delta hdelta)
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF),
      LowConductorParameterTableData F K ht hres pi hpi hgen
        chiF chiK psiF psiK hminimal hchi hpsi hF hLow delta epsilon₁
          hdelta hepsilon₁ hT hgammaF hgammaK P

/-- **Exact reduction to residual phases.**  The result contains the exact
high/low table dispatch.  The remaining public declarations in this file turn
those quotient-class packages into complete local Lamprecht factors and then
into the two structured error-term assemblies. -/
theorem phaseParameterTableDispatch : PhaseParameterTableDispatch where
  rangeCases := phaseParameterRange_cases
  boundaryIsLow := phaseParameterRange_boundary
  rangesDisjoint := phaseParameterRange_disjoint
  highParameters := highConductorParameterTable
  lowParameters := lowConductorParameterTable

/-- Type-valued access to supplied quotient representatives.  In particular,
this API returns the representatives already present in the High/Low data; it
does not assert quotient surjectivity or select canonical field elements. -/
structure StationaryRepresentativeAPI where
  ofCoefficient : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    {h : IsStationaryConductorDecomposition chi.conductor d epsilon}
    {gamma : Eˣ}
    {hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)},
    (c : lattice E 0) →
      latticeQuotientMk E (by omega) c =
          stationaryCoefficientClass E chi psi h gamma hgamma →
        StationaryClassRepresentative E chi psi h gamma hgamma
  ofLowAlpha : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {r d : ℕ}
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {epsilonF : ℕ}
    {hF : IsStationaryConductorDecomposition chiF.conductor r epsilonF}
    {gammaF : Fˣ}
    {hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)}
    {betaClass : StationaryCoefficientQuotient F d},
    LowStationaryNormRepresentativePair F K r d
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
        betaClass →
      StationaryClassRepresentative F chiF psiF hF gammaF hgammaF
  ofLowBeta : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {r d : ℕ}
    {alphaClass : StationaryCoefficientQuotient F r}
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {epsilonF : ℕ}
    {hF : IsStationaryConductorDecomposition chiF.conductor d epsilonF}
    {gammaF : Fˣ}
    {hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)},
    LowStationaryNormRepresentativePair F K r d alphaClass
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) →
      StationaryClassRepresentative F chiF psiF hF gammaF hgammaF
  exactAmbiguity : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    {h : IsStationaryConductorDecomposition chi.conductor d epsilon}
    {gamma : Eˣ}
    {hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)}
    (R R' : StationaryClassRepresentative E chi psi h gamma hgamma),
      CongruentAtDepth (d : ℤ)
        (R.representative : E) (R'.representative : E)
  toLocalPhase : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (Gamma : AdmissibleGamma E chi psi)
    (R : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property)
    (C : LamprechtCriticalCoordinate E d epsilon),
      LocalLamprechtPhaseData E chi psi
  stableHighPair : ∀
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
    (CK : LamprechtCriticalCoordinate K dK epsilonK),
      { P : HighStableOddParameterData.CompatiblePhasePair F K ht hres pi hpi
          hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H //
        P = HighStableOddParameterData.compatiblePhasePair F K ht hres pi hpi
          hgen chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H
            R CF CK }

/-- Local Lamprecht factorization and representative-independence API.  The
odd field asserts independence only for the transported elementary/Hasse
product. -/
structure LocalLamprechtAPI : Prop where
  exactFormula : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalPhaseData E chi psi),
      deltaFinite chi psi D.gamma = D.completeFactor
  endpointHasNoStationaryClass : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E},
    chi.conductor ≤ 1 →
      ¬ Nonempty (LocalLamprechtPhaseData E chi psi)
  evenRepresentativeIndependent : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property),
      (LocalLamprechtPhaseData.evenOfStationaryClass
          d h Gamma R).stationaryFactor =
        (LocalLamprechtPhaseData.evenOfStationaryClass
          d h Gamma R').stationaryFactor
  oddRepresentativeIndependent : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property),
      (LocalLamprechtPhaseData.oddOfStationaryClass
          d h Gamma delta hdelta R).stationaryFactor =
        (LocalLamprechtPhaseData.oddOfStationaryClass
          d h Gamma delta hdelta R').stationaryFactor
  evenCompleteFactorIndependent : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 0)
    (Gamma : AdmissibleGamma E chi psi)
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property),
      (LocalLamprechtPhaseData.evenOfStationaryClass
          d h Gamma R).completeFactor =
        (LocalLamprechtPhaseData.evenOfStationaryClass
          d h Gamma R').completeFactor
  oddCompleteFactorIndependent : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (d : ℕ)
    (h : IsStationaryConductorDecomposition chi.conductor d 1)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (R R' : StationaryClassRepresentative E chi psi h
      (Gamma : Eˣ) Gamma.property),
      (LocalLamprechtPhaseData.oddOfStationaryClass
          d h Gamma delta hdelta R).completeFactor =
        (LocalLamprechtPhaseData.oddOfStationaryClass
          d h Gamma delta hdelta R').completeFactor
  oddRepresentativeTransport : ∀
    {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ)
    (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (c c' : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (hc' : latticeQuotientMk E
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth E chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c' =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth E chi d 1
          (by omega) hm hlarge) Gamma Gamma.property),
      ∃ a : ResidueField E,
        lamprechtHasseFunction E chi psi d hm hlarge Gamma delta hdelta c' hc' =
          (lamprechtHasseFunction E chi psi d hm hlarge
            Gamma delta hdelta c hc).translate a ∧
        lamprechtElementaryFactor E chi psi Gamma
            (lamprechtStationaryRepresentativeUnit E chi psi
              (lamprechtFormula_stationaryDepth E chi d 1
                (by omega) hm hlarge) Gamma c' hc') =
          lamprechtHasseFunction E chi psi d hm hlarge
              Gamma delta hdelta c hc a *
            lamprechtElementaryFactor E chi psi Gamma
              (lamprechtStationaryRepresentativeUnit E chi psi
                (lamprechtFormula_stationaryDepth E chi d 1
                  (by omega) hm hlarge) Gamma c hc)

/-- Global exact error-term factorization, together with the already-proved
norm-character twist invariance.  No field asserts that the error is one. -/
structure GlobalPhaseFactorizationAPI : Prop where
  exactFactorization : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K},
    IsDeltaFiniteLocalConstant DeltaF →
      IsDeltaFiniteLocalConstant DeltaK →
        ∀ D : FirstMainPhaseData F K chiF psiF data,
          errorTerm F K DeltaF DeltaK chiF psiF = D.factors.assembled
  twistInvariant : ∀
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    (DeltaF : LocalConstantFunction F) (DeltaK : LocalConstantFunction K)
    (nu : NormCharacter F K) (chiF : ContinuousQuasiChar F)
    (psiF : ContinuousAddChar F),
      errorTerm F K DeltaF DeltaK (nu.1 * chiF) psiF =
        errorTerm F K DeltaF DeltaK chiF psiF
  identityNormEndpoint : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    (D : FirstMainPhaseData F K chiF psiF data),
      ∃ (h : (data.normCharacterData 1).conductor ≤ 1)
        (Gamma : AdmissibleGamma F
          (data.normCharacterData 1) data.baseAddChar),
        D.normCharacter 1 = LocalPhaseData.endpoint h Gamma

/-- Both manuscript assemblies as structured results. -/
structure ExactPhaseAssemblyAPI : Prop where
  oddResult : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {D : FirstMainPhaseData F K chiF psiF data}
    {t m : ℕ} {I : Type} [Fintype I],
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF) →
      (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) →
        (A : ExactOddPhaseAssembly F K chiF psiF data D
          (t := t) (m := m) I) →
          A.Result hDeltaF hDeltaK
  quadraticResult : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {D : FirstMainPhaseData F K chiF psiF data}
    {t m : ℕ},
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF) →
      (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) →
        (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
          (t := t) (m := m)) →
          A.Result hDeltaF hDeltaK
  quadraticCompleteResult : ∀
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {D : FirstMainPhaseData F K chiF psiF data}
    {t m : ℕ},
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF) →
      (hDeltaK : IsDeltaFiniteLocalConstant DeltaK) →
        (A : ExactQuadraticPhaseAssembly F K chiF psiF data D
          (t := t) (m := m)) →
          (C : A.CompleteCorrectionData) →
            C.CompleteResult hDeltaF hDeltaK A

/-- Preferred table-backed eliminators for all four parameter ranges.  Each
field has the full polymorphic type of the corresponding source-tied theorem;
`type_of%` keeps this public bundle synchronized with those dependent APIs
without erasing any table, representative, conductor, or correction datum. -/
structure TableBackedPhaseAssemblyAPI : Prop where
  highOddResult :
    type_of% @highSourceCoordinateConstructedExactOddResultEliminator
  lowOddResult :
    type_of% @lowSourceCoordinateConstructedExactOddResultEliminator
  highQuadraticCompleteResult :
    type_of%
      @QBackedQuadraticCompleteCorrection.qBackedQuadraticCompleteResult
  lowQuadraticCompleteResult :
    type_of%
      @LowTableBackedQuadraticCompleteCorrection.lowTableBackedQuadraticCompleteResult

/-- Proof-only certificate for the source-tied residual-function layer.
The actual coordinates, Lamprecht packages, and critical functions are the
public definitions above; this proposition contains only theorems about
those fixed constructions.  Consequently it cannot be inhabited by choosing
independently rescaled upper, norm, twist, or base functions. -/
structure ResidualCriticalFunctionAPI : Prop where
  highUpstairsCriticalPolarFunction_apply :
    type_of% @highSourceUpstairsCriticalPolarFunction_apply
  highDisplayedUpstairsCriticalPolarFunction_apply :
    type_of% @highSourceDisplayedUpstairsCriticalPolarFunction_apply
  highNormCriticalPolarFunction_apply :
    type_of% @highSourceNormCriticalPolarFunction_apply
  highTwistCriticalPolarFunction_apply :
    type_of% @highSourceTwistCriticalPolarFunction_apply
  lowUpstairsCriticalPolarFunction_apply :
    type_of% @lowSourceUpstairsCriticalPolarFunction_apply
  lowDisplayedUpstairsCriticalPolarFunction_apply :
    type_of% @lowSourceDisplayedUpstairsCriticalPolarFunction_apply
  lowBaseCriticalPolarFunction_apply :
    type_of% @lowSourceBaseCriticalPolarFunction_apply
  lowNormCriticalPolarFunction_apply :
    type_of% @lowSourceNormCriticalPolarFunction_apply
  lowTwistCriticalPolarFunction_apply :
    type_of% @lowSourceTwistCriticalPolarFunction_apply
  lowerSourceCoordinate_eq_norm :
    type_of%
      @PhaseReductionResidualCoordinateSource.lowerSourceCoordinate_eq_norm.{0, 0}
  scaledSourceCoordinate_eq :
    type_of%
      @PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq.{0}
  coordinateFunctionTransport :
    type_of% @criticalPolarFunction_transportCoordinate_apply.{0}
  coordinatePolarTransport :
    type_of% @criticalPolarCoefficient_transportCoordinate.{0}
  coordinateAffineTransport :
    type_of% @criticalPolarData_transportCoordinate_affine.{0}
  displayedCoordinatePolarTransport :
    type_of%
      @LocalLamprechtPhaseData.displayedInLowerCoordinate_polarCoefficient.{0, 0}
  displayedCoordinateAffineTransport :
    type_of%
      @LocalLamprechtPhaseData.displayedInLowerCoordinate_affineCoefficient.{0, 0}
  representativeFunctionTransport :
    type_of%
      @LocalLamprechtPhaseData.odd_criticalFunction_changeRepresentative.{0}
  representativeAffineTransport :
    type_of%
      @LocalLamprechtPhaseData.odd_affineCoefficient_changeRepresentative.{0}
  oddCriticalFunctionEvaluation :
    type_of%
      @LocalLamprechtPhaseData.odd_criticalFunction_integral_div_coordinate.{0}
  sourceOddCriticalFunctionEvaluation :
    type_of% @localPhaseOfStationaryClass_source_odd_apply_integral.{0}
  proofDataCriticalFunctionTransport :
    type_of% @transportLocalLamprechtPhaseData_criticalFunction.{0}
  exactCharacterTransport :
    type_of% @phaseReductionExactCriticalTransport_of_stationaryRatios.{0, 0}
  residualClassCongruence :
    type_of% @phaseReductionResidualClass_eq_of_sub_mem.{0}
  lowBaseResidualClass :
    type_of% @phaseReductionLowBaseResidualClass.{0, 0}
  lowBoundaryTauResidualCongruence :
    type_of% @phaseReductionLowBoundaryTauPolynomial_congruent.{0, 0}
  lowStrictTauResidualDepth :
    type_of% @phaseReductionLowStrictTauPolynomial_deep.{0, 0}
  upperSourceDisplacementReduction :
    type_of% @phaseReductionUpperSourceDisplacement_reduces
  lowStrictTauStationaryLayer :
    type_of% @phaseReductionLowStrictTauPolynomial_stationaryLayer
  lowBoundaryTauResidualClass :
    type_of% @phaseReductionLowBoundaryTauResidualClass
  highBaseResidualClassZero :
    type_of% @phaseReductionHighBaseResidualClass_zero.{0, 0}
  highTauResidualClassZero :
    type_of% @phaseReductionHighTauResidualClass_zero.{0, 0}
  highActualExactTransport :
    type_of% @highOdd_actualStationaryRatios_exactCriticalTransport
  lowActualExactTransport :
    type_of% @lowOdd_actualStationaryRatios_exactCriticalTransport
  highDisplayedExactTransport :
    type_of% @highSourceDisplayed_exactCriticalTransport_above
  highTwistFunctionTransport :
    type_of% @highSourceTwistFunction_eq_base_of_odd
  highTwistFunctionTransportAllParities :
    type_of% @highSourceTwistFunction_eq_base
  highNormFunctionActualSource :
    type_of% @highSourceNormFunction_eq_actualTeichmuller
  highRepresentativeExactTranslation :
    type_of% @highActualTeichmuller_criticalFunction_eq_exact_translation
  highRepresentativePolarInvariant :
    type_of% @highActualTeichmuller_polarCoefficient_eq_literal
  highLiteralPowerFunction :
    type_of% @highNormLiteralPower_criticalFunction_eq_pow
  highNormFunctionEven :
    type_of% @highSourceNormFunction_eq_one_of_even
  highTwistFunctionEven :
    type_of% @highSourceTwistFunction_eq_one_of_even
  highUpstairsFunctionEven :
    type_of% @highSourceUpstairsFunction_eq_one_of_even
  highDisplayedUpstairsFunctionEven :
    type_of% @highSourceDisplayedUpstairsFunction_eq_one_of_even
  lowTwistRepresentativeCompatibility :
    type_of% @lowOddTwistRepresentative_eq_norm_add_base
  lowNormRepresentativeCompatibility :
    type_of% @lowOddNormRepresentative_eq_teichmuller_mul
  lowNormRepresentativeClassCompatibility :
    type_of% @lowOddNormRepresentative_class_eq_power
  lowNormPowerClassCompatibility :
    type_of% @lowOddNormRepresentative_class_eq_powerCharacter
  lowNormFunctionPowerSource :
    type_of% @lowSourceNormFunction_eq_powerPhase
  lowNormFunctionActualSource :
    type_of% @lowSourceNormFunction_eq_actualTeichmuller
  lowRepresentativeExactTranslation :
    type_of% @lowActualTeichmullerPower_criticalFunction_eq_exact_translation
  lowRepresentativePolarInvariant :
    type_of% @lowActualTeichmullerPower_polarCoefficient_eq_literal
  lowLiteralPowerFunction :
    type_of% @lowNormalizedLiteralPower_criticalFunction_eq_pow
  lowDisplayedUpstairsRawEvaluation :
    type_of% @lowSourceDisplayedUpstairsFunction_displacement_apply_eq_raw
  lowBaseRawEvaluation :
    type_of% @lowSourceBaseFunction_apply_eq_raw
  lowNormOneRawEvaluation :
    type_of% @lowSourceNormFunction_one_apply_eq_raw
  lowDisplayedStrictExactTransport :
    type_of% @lowSourceDisplayed_exactCriticalTransport_strict
  lowDisplayedBoundaryExactTransport :
    type_of% @lowSourceDisplayed_exactCriticalTransport_boundary
  lowStrictTwistFunctionTransport :
    type_of% @lowSourceTwistFunction_eq_norm_of_strict
  lowBoundaryTwistFunctionTransport :
    type_of% @lowSourceTwistFunction_eq_norm_mul_base_of_boundary
  lowBaseFunctionEven :
    type_of% @lowSourceBaseFunction_eq_one_of_even
  lowNormFunctionEven :
    type_of% @lowSourceNormFunction_eq_one_of_even
  lowTwistFunctionEven :
    type_of% @lowSourceTwistFunction_eq_one_of_even
  lowUpstairsFunctionEven :
    type_of% @lowSourceUpstairsFunction_eq_one_of_even
  lowDisplayedUpstairsFunctionEven :
    type_of% @lowSourceDisplayedUpstairsFunction_eq_one_of_even
  highSourceCoordinateResult :
    type_of% @highSourceCoordinateConstructedExactOddResultEliminator
  lowSourceCoordinateResult :
    type_of% @lowSourceCoordinateConstructedExactOddResultEliminator
  highRawRowRatio : type_of% @highOddSourceTied_rowRatio_eq
  highIndexedCharacterBridge :
    type_of% @HighOddSourceTiedCorrectionCoordinates.powerCharacterBridge
  lowRawRowRatio : type_of% @lowOddSourceTied_rowRatio_eq
  lowIndexedCharacterBridge :
    type_of% @LowOddSourceTiedCorrectionCoordinates.powerCharacterBridge

/-- Structured public API of the phase-reduction node.  It bundles exact
High/Low dispatch, supplied representative constructors, complete local
Lamprecht factors, the four global factor quotients, twist invariance, and
the exact odd and wild-quadratic assemblies. -/
structure PhaseReductionResultData where
  parameterTables : PhaseParameterTableDispatch
  representatives : StationaryRepresentativeAPI
  localLamprecht : LocalLamprechtAPI
  residualCriticalFunctions : ResidualCriticalFunctionAPI
  globalFactorization : GlobalPhaseFactorizationAPI
  exactAssemblies : ExactPhaseAssemblyAPI
  tableBackedAssemblies : TableBackedPhaseAssemblyAPI

def stationaryRepresentativeAPI : StationaryRepresentativeAPI where
  ofCoefficient := StationaryClassRepresentative.ofCoefficientRepresentative
  ofLowAlpha := StationaryClassRepresentative.ofLowAlpha
  ofLowBeta := StationaryClassRepresentative.ofLowBeta
  exactAmbiguity := StationaryClassRepresentative.congruentAtCoefficientDepth
  toLocalPhase := localPhaseOfStationaryClass
  stableHighPair := by
    intros
    exact ⟨_, rfl⟩

theorem localLamprechtAPI : LocalLamprechtAPI where
  exactFormula := LocalPhaseData.deltaFinite_eq_completeFactor
  endpointHasNoStationaryClass :=
    LocalLamprechtPhaseData.noData_of_conductor_le_one
  evenRepresentativeIndependent :=
    LocalLamprechtPhaseData.evenStationaryFactor_representative_independent
  oddRepresentativeIndependent :=
    LocalLamprechtPhaseData.oddStationaryFactor_representative_independent
  evenCompleteFactorIndependent :=
    LocalLamprechtPhaseData.evenCompleteFactor_representative_independent
  oddCompleteFactorIndependent :=
    LocalLamprechtPhaseData.oddCompleteFactor_representative_independent
  oddRepresentativeTransport :=
    LocalLamprechtPhaseData.oddRepresentative_transport

theorem globalPhaseFactorizationAPI : GlobalPhaseFactorizationAPI where
  exactFactorization := FirstMainPhaseData.errorTerm_eq_assembledFactors
  twistInvariant := errorTerm_normCharacter_mul
  identityNormEndpoint := identityNormCharacterEndpoint_of_phaseData

theorem exactPhaseAssemblyAPI : ExactPhaseAssemblyAPI where
  oddResult := ExactOddPhaseAssembly.result
  quadraticResult := ExactQuadraticPhaseAssembly.result
  quadraticCompleteResult :=
    ExactQuadraticPhaseAssembly.CompleteCorrectionData.completeResult

theorem tableBackedPhaseAssemblyAPI : TableBackedPhaseAssemblyAPI where
  highOddResult := highSourceCoordinateConstructedExactOddResultEliminator
  lowOddResult := lowSourceCoordinateConstructedExactOddResultEliminator
  highQuadraticCompleteResult :=
    QBackedQuadraticCompleteCorrection.qBackedQuadraticCompleteResult
  lowQuadraticCompleteResult :=
    LowTableBackedQuadraticCompleteCorrection.lowTableBackedQuadraticCompleteResult

theorem residualCriticalFunctionAPI :
    ResidualCriticalFunctionAPI where
  highUpstairsCriticalPolarFunction_apply :=
    highSourceUpstairsCriticalPolarFunction_apply
  highDisplayedUpstairsCriticalPolarFunction_apply :=
    highSourceDisplayedUpstairsCriticalPolarFunction_apply
  highNormCriticalPolarFunction_apply :=
    highSourceNormCriticalPolarFunction_apply
  highTwistCriticalPolarFunction_apply :=
    highSourceTwistCriticalPolarFunction_apply
  lowUpstairsCriticalPolarFunction_apply :=
    lowSourceUpstairsCriticalPolarFunction_apply
  lowDisplayedUpstairsCriticalPolarFunction_apply :=
    lowSourceDisplayedUpstairsCriticalPolarFunction_apply
  lowBaseCriticalPolarFunction_apply :=
    lowSourceBaseCriticalPolarFunction_apply
  lowNormCriticalPolarFunction_apply :=
    lowSourceNormCriticalPolarFunction_apply
  lowTwistCriticalPolarFunction_apply :=
    lowSourceTwistCriticalPolarFunction_apply
  lowerSourceCoordinate_eq_norm :=
    PhaseReductionResidualCoordinateSource.lowerSourceCoordinate_eq_norm
  scaledSourceCoordinate_eq :=
    PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq
  coordinateFunctionTransport :=
    criticalPolarFunction_transportCoordinate_apply
  coordinatePolarTransport := criticalPolarCoefficient_transportCoordinate
  coordinateAffineTransport := criticalPolarData_transportCoordinate_affine
  displayedCoordinatePolarTransport :=
    LocalLamprechtPhaseData.displayedInLowerCoordinate_polarCoefficient
  displayedCoordinateAffineTransport :=
    LocalLamprechtPhaseData.displayedInLowerCoordinate_affineCoefficient
  representativeFunctionTransport :=
    LocalLamprechtPhaseData.odd_criticalFunction_changeRepresentative
  representativeAffineTransport :=
    LocalLamprechtPhaseData.odd_affineCoefficient_changeRepresentative
  oddCriticalFunctionEvaluation :=
    LocalLamprechtPhaseData.odd_criticalFunction_integral_div_coordinate
  sourceOddCriticalFunctionEvaluation :=
    localPhaseOfStationaryClass_source_odd_apply_integral
  proofDataCriticalFunctionTransport :=
    transportLocalLamprechtPhaseData_criticalFunction
  exactCharacterTransport :=
    phaseReductionExactCriticalTransport_of_stationaryRatios
  residualClassCongruence := phaseReductionResidualClass_eq_of_sub_mem
  lowBaseResidualClass := phaseReductionLowBaseResidualClass
  lowBoundaryTauResidualCongruence :=
    phaseReductionLowBoundaryTauPolynomial_congruent
  lowStrictTauResidualDepth := phaseReductionLowStrictTauPolynomial_deep
  upperSourceDisplacementReduction :=
    phaseReductionUpperSourceDisplacement_reduces
  lowStrictTauStationaryLayer :=
    phaseReductionLowStrictTauPolynomial_stationaryLayer
  lowBoundaryTauResidualClass := phaseReductionLowBoundaryTauResidualClass
  highBaseResidualClassZero := phaseReductionHighBaseResidualClass_zero
  highTauResidualClassZero := phaseReductionHighTauResidualClass_zero
  highActualExactTransport :=
    highOdd_actualStationaryRatios_exactCriticalTransport
  lowActualExactTransport :=
    lowOdd_actualStationaryRatios_exactCriticalTransport
  highDisplayedExactTransport := highSourceDisplayed_exactCriticalTransport_above
  highTwistFunctionTransport := highSourceTwistFunction_eq_base_of_odd
  highTwistFunctionTransportAllParities := highSourceTwistFunction_eq_base
  highNormFunctionActualSource := highSourceNormFunction_eq_actualTeichmuller
  highRepresentativeExactTranslation :=
    highActualTeichmuller_criticalFunction_eq_exact_translation
  highRepresentativePolarInvariant :=
    highActualTeichmuller_polarCoefficient_eq_literal
  highLiteralPowerFunction := highNormLiteralPower_criticalFunction_eq_pow
  highNormFunctionEven := highSourceNormFunction_eq_one_of_even
  highTwistFunctionEven := highSourceTwistFunction_eq_one_of_even
  highUpstairsFunctionEven := highSourceUpstairsFunction_eq_one_of_even
  highDisplayedUpstairsFunctionEven :=
    highSourceDisplayedUpstairsFunction_eq_one_of_even
  lowTwistRepresentativeCompatibility :=
    lowOddTwistRepresentative_eq_norm_add_base
  lowNormRepresentativeCompatibility :=
    lowOddNormRepresentative_eq_teichmuller_mul
  lowNormRepresentativeClassCompatibility :=
    lowOddNormRepresentative_class_eq_power
  lowNormPowerClassCompatibility :=
    lowOddNormRepresentative_class_eq_powerCharacter
  lowNormFunctionPowerSource := lowSourceNormFunction_eq_powerPhase
  lowNormFunctionActualSource := lowSourceNormFunction_eq_actualTeichmuller
  lowRepresentativeExactTranslation :=
    lowActualTeichmullerPower_criticalFunction_eq_exact_translation
  lowRepresentativePolarInvariant :=
    lowActualTeichmullerPower_polarCoefficient_eq_literal
  lowLiteralPowerFunction := lowNormalizedLiteralPower_criticalFunction_eq_pow
  lowDisplayedUpstairsRawEvaluation :=
    lowSourceDisplayedUpstairsFunction_displacement_apply_eq_raw
  lowBaseRawEvaluation := lowSourceBaseFunction_apply_eq_raw
  lowNormOneRawEvaluation := lowSourceNormFunction_one_apply_eq_raw
  lowDisplayedStrictExactTransport :=
    lowSourceDisplayed_exactCriticalTransport_strict
  lowDisplayedBoundaryExactTransport :=
    lowSourceDisplayed_exactCriticalTransport_boundary
  lowStrictTwistFunctionTransport := lowSourceTwistFunction_eq_norm_of_strict
  lowBoundaryTwistFunctionTransport :=
    lowSourceTwistFunction_eq_norm_mul_base_of_boundary
  lowBaseFunctionEven := lowSourceBaseFunction_eq_one_of_even
  lowNormFunctionEven := lowSourceNormFunction_eq_one_of_even
  lowTwistFunctionEven := lowSourceTwistFunction_eq_one_of_even
  lowUpstairsFunctionEven := lowSourceUpstairsFunction_eq_one_of_even
  lowDisplayedUpstairsFunctionEven :=
    lowSourceDisplayedUpstairsFunction_eq_one_of_even
  highSourceCoordinateResult :=
    highSourceCoordinateConstructedExactOddResultEliminator
  lowSourceCoordinateResult :=
    lowSourceCoordinateConstructedExactOddResultEliminator
  highRawRowRatio := highOddSourceTied_rowRatio_eq
  highIndexedCharacterBridge :=
    HighOddSourceTiedCorrectionCoordinates.powerCharacterBridge
  lowRawRowRatio := lowOddSourceTied_rowRatio_eq
  lowIndexedCharacterBridge :=
    LowOddSourceTiedCorrectionCoordinates.powerCharacterBridge

/-- **Exact reduction to residual phases.** -/
noncomputable def PhaseReductionResult : PhaseReductionResultData where
  parameterTables := phaseParameterTableDispatch
  representatives := stationaryRepresentativeAPI
  localLamprecht := localLamprechtAPI
  residualCriticalFunctions := residualCriticalFunctionAPI
  globalFactorization := globalPhaseFactorizationAPI
  exactAssemblies := exactPhaseAssemblyAPI
  tableBackedAssemblies := tableBackedPhaseAssemblyAPI

end

end LanglandsFirstMainLemma
