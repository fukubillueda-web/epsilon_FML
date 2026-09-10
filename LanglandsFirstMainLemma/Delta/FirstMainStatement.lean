import LanglandsFirstMainLemma.Basic.CharacterTypes
import LanglandsFirstMainLemma.LocalField.Extension
import LanglandsFirstMainLemma.Basic.CharacteristicConvention

/-!
# Statement of the First Main Lemma

This file contains only the data needed to state Langlands's First Main
Lemma.  In particular, the local constants below are parameters: no value of
the local constant, and no instance of the First Main identity, is assumed.

The definitions follow Theorem `thm:first-main` and equation `eq:def-S` of
the authoritative manuscript.  They impose no mixed-characteristic
hypothesis, in accordance with `rem:characteristic-convention`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section PullbackCharacters

variable (F K : Type*) [CommRing F] [CommRing K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K]
  [TopologicalSpace F] [IsTopologicalRing F]
  [TopologicalSpace K] [IsModuleTopology F K]

/-- The norm pullback `χ_K = χ_F ∘ N_{K/F}` of a continuous
quasi-character. -/
def normQuasiChar (χ : ContinuousQuasiChar F) : ContinuousQuasiChar K :=
  χ.pullback (continuousNormUnits F K)

@[simp]
theorem normQuasiChar_apply (χ : ContinuousQuasiChar F) (x : Kˣ) :
    normQuasiChar F K χ x = χ (continuousNormUnits F K x) :=
  rfl

/-- The trace pullback `ψ_K = ψ_F ∘ Tr_{K/F}` of a continuous
additive character. -/
def tracePullbackAddChar (ψ : ContinuousAddChar F) : ContinuousAddChar K :=
  ψ.pullback (continuousTrace F K)

omit [Module.Free F K] [Module.Finite F K] in
@[simp]
theorem tracePullbackAddChar_apply (ψ : ContinuousAddChar F) (x : K) :
    tracePullbackAddChar F K ψ x = ψ (trace F K x) :=
  rfl

/-- `S(K/F)`: the continuous characters of `Fˣ` that are trivial after
pullback along `N_{K/F}`.  This is equation `eq:def-S` in the manuscript.

Finiteness of this type is deliberately not asserted here; it is a theorem
about the norm quotient proved by the later norm-character node. -/
def NormCharacter :=
  {μ : ContinuousQuasiChar F // normQuasiChar F K μ = 1}

namespace NormCharacter

variable {F K}

@[ext]
theorem ext {μ ν : NormCharacter F K} (h : μ.1 = ν.1) :
    μ = ν :=
  Subtype.ext h

@[simp]
theorem normQuasiChar_eq_one (μ : NormCharacter F K) :
    normQuasiChar F K μ.1 = 1 :=
  μ.property

end NormCharacter

end PullbackCharacters

/-- The type of a proposed local-constant function on a topological field.
The actual Langlands local constant is supplied by the local-constant nodes;
this alias carries no mathematical assertion. -/
abbrev LocalConstantFunction (E : Type*) [Field E] [TopologicalSpace E] :=
  ContinuousQuasiChar E → ContinuousAddChar E → ℂ

/-- The field-theoretic condition that `K/F` is cyclic of prime degree.
This spells out both cyclicity and prime degree exactly as in
`thm:first-main`. -/
def CyclicPrimeExtension (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Module.Free F K] [Module.Finite F K] : Prop :=
  IsGalois F K ∧ IsCyclic Gal(K/F) ∧ (Module.finrank F K).Prime

section FirstMainIdentity

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Finite (NormCharacter F K)]

/-- The left side of the First Main identity,
`Δ_K(χ_K,ψ_K) ∏_{μ∈S(K/F)} Δ_F(μ,ψ_F)`, with the manuscript's norm and
trace pullbacks. -/
def firstMainLeftSide
    (ΔF : LocalConstantFunction F) (ΔK : LocalConstantFunction K)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ΔK (normQuasiChar F K χF) (tracePullbackAddChar F K ψF) *
    ∏ μ : NormCharacter F K, ΔF μ.1 ψF

/-- The right side of the First Main identity,
`∏_{μ∈S(K/F)} Δ_F(μχ_F,ψ_F)`. -/
def firstMainRightSide
    (ΔF : LocalConstantFunction F) (χF : ContinuousQuasiChar F)
    (ψF : ContinuousAddChar F) : ℂ := by
  letI := Fintype.ofFinite (NormCharacter F K)
  exact ∏ μ : NormCharacter F K,
    ΔF (μ.1 * χF) ψF

/-- The First Main identity for fixed characters. -/
def FirstMainIdentity
    (ΔF : LocalConstantFunction F) (ΔK : LocalConstantFunction K)
    (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F) : Prop :=
  firstMainLeftSide F K ΔF ΔK χF ψF =
    firstMainRightSide F K ΔF χF ψF

/-- The exact formal statement of Langlands's First Main Lemma for a cyclic
prime extension: for every quasi-character and every nontrivial continuous
additive character, the First Main identity holds.

This is only a proposition-valued definition.  It neither assumes nor proves
the First Main Lemma. -/
def FirstMainStatement
    (ΔF : LocalConstantFunction F) (ΔK : LocalConstantFunction K) : Prop :=
  CyclicPrimeExtension F K →
    ∀ (χF : ContinuousQuasiChar F) (ψF : ContinuousAddChar F),
      ψF ≠ 1 → FirstMainIdentity F K ΔF ΔK χF ψF

end FirstMainIdentity

end

end LanglandsFirstMainLemma
