import LanglandsFirstMainLemma.Dispatch
import LanglandsFirstMainLemma.Basic.StandardCharacterBridge
import LanglandsFirstMainLemma.Delta.LocalConstantRealization

namespace LanglandsFirstMainLemma

noncomputable section

/-- **Langlands's First Main Lemma.**

For a cyclic extension of prime degree, the canonical local constants satisfy
the First Main identity for every continuous quasi-character and every
nontrivial continuous additive character.

Source: Theorem `thm:first-main` and Section `sec:first-main-completion`. -/
theorem firstMainLemma
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (hcyclic : CyclicPrimeExtension F K) :
    letI : PrimeCyclicExtension F K :=
      PrimeCyclicExtension.ofCyclicPrimeExtension F K hcyclic
    letI : Finite (NormCharacter F K) :=
      primeCyclicNormCharacter_finite F K
    ∀ (chiF : ContinuousQuasiChar F) (psiF : ContinuousAddChar F),
      psiF ≠ 1 →
        FirstMainIdentity F K (localConstant F) (localConstant K) chiF psiF := by
  letI : PrimeCyclicExtension F K :=
    PrimeCyclicExtension.ofCyclicPrimeExtension F K hcyclic
  letI : Finite (NormCharacter F K) :=
    primeCyclicNormCharacter_finite F K
  intro chiF psiF hpsiF
  exact firstMainLemma_nonarchimedean F K
    (DeltaF := localConstant F)
    (DeltaK := localConstant K)
    (hDeltaF := localConstant_isDeltaFinite F)
    (hDeltaK := localConstant_isDeltaFinite K)
    (chiF := canonicalLocalQuasiCharData F chiF)
    (psiF := canonicalLocalAddCharData F psiF hpsiF)

end

end LanglandsFirstMainLemma
