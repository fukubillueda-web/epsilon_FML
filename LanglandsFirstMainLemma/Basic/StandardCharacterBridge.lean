import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.LocalField.Extension

/-!
# Bridge from standard continuous local characters

The computational proof uses `LocalAddCharData` and `LocalQuasiCharData`,
whose conductor fields carry proofs of exactness.  The public input of the
First Main Lemma is instead an ordinary continuous character together with
its exact conductor.  This file converts between those interfaces without
changing the character, and records compatibility with trace and norm
pullback.

The additive convention is the manuscript's convention already encoded by
`IsAdditiveConductor`: conductor `n` means that `p^(-n)` is the largest
triviality lattice.  Likewise multiplicative conductor zero means triviality
on `U^0`, not global triviality.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Package a standard continuous additive character with a proof of its
exact conductor.  The mathematical character is unchanged. -/
def continuousAddChar_toData (psi : ContinuousAddChar F) (n : ℤ)
    (hn : IsAdditiveConductor F psi n) : LocalAddCharData F where
  character := psi
  conductor := n
  isConductor := hn

@[simp]
theorem continuousAddChar_toData_character (psi : ContinuousAddChar F) (n : ℤ)
    (hn : IsAdditiveConductor F psi n) :
    (continuousAddChar_toData F psi n hn).character = psi :=
  rfl

@[simp]
theorem continuousAddChar_toData_conductor (psi : ContinuousAddChar F) (n : ℤ)
    (hn : IsAdditiveConductor F psi n) :
    (continuousAddChar_toData F psi n hn).conductor = n :=
  rfl

@[simp]
theorem continuousAddChar_toData_apply (psi : ContinuousAddChar F) (n : ℤ)
    (hn : IsAdditiveConductor F psi n) (x : F) :
    (continuousAddChar_toData F psi n hn).character x = psi x :=
  rfl

/-- The additive wrapper retains the supplied *exact* conductor proof, not
merely triviality on the conductor lattice. -/
theorem continuousAddChar_toData_isConductor (psi : ContinuousAddChar F) (n : ℤ)
    (hn : IsAdditiveConductor F psi n) :
    IsAdditiveConductor F
      (continuousAddChar_toData F psi n hn).character
      (continuousAddChar_toData F psi n hn).conductor :=
  hn

/-- The wrapped additive character uses the manuscript's sign convention:
triviality at lattice depth `r` is equivalent to `-n ≤ r`. -/
theorem continuousAddChar_toData_trivialOnLattice_iff
    (psi : ContinuousAddChar F) (n r : ℤ)
    (hn : IsAdditiveConductor F psi n) :
    AddCharTrivialOnLattice F
        (continuousAddChar_toData F psi n hn).character r ↔
      -n ≤ r :=
  (continuousAddChar_toData F psi n hn).trivialOnLattice_iff r

/-- Package a standard continuous quasi-character with a proof of its exact
conductor.  The mathematical character is unchanged. -/
def continuousQuasiChar_toData (chi : ContinuousQuasiChar F) (m : ℕ)
    (hm : IsMultiplicativeConductor F chi m) : LocalQuasiCharData F where
  character := chi
  conductor := m
  isConductor := hm

@[simp]
theorem continuousQuasiChar_toData_character (chi : ContinuousQuasiChar F) (m : ℕ)
    (hm : IsMultiplicativeConductor F chi m) :
    (continuousQuasiChar_toData F chi m hm).character = chi :=
  rfl

@[simp]
theorem continuousQuasiChar_toData_conductor (chi : ContinuousQuasiChar F) (m : ℕ)
    (hm : IsMultiplicativeConductor F chi m) :
    (continuousQuasiChar_toData F chi m hm).conductor = m :=
  rfl

@[simp]
theorem continuousQuasiChar_toData_apply (chi : ContinuousQuasiChar F) (m : ℕ)
    (hm : IsMultiplicativeConductor F chi m) (x : Fˣ) :
    (continuousQuasiChar_toData F chi m hm).character x = chi x :=
  rfl

/-- The multiplicative wrapper retains the supplied *exact* conductor proof,
including the endpoint convention at conductor zero. -/
theorem continuousQuasiChar_toData_isConductor
    (chi : ContinuousQuasiChar F) (m : ℕ)
    (hm : IsMultiplicativeConductor F chi m) :
    IsMultiplicativeConductor F
      (continuousQuasiChar_toData F chi m hm).character
      (continuousQuasiChar_toData F chi m hm).conductor :=
  hm

/-- The wrapped quasi-character is trivial exactly on the unit-filtration
layers at or above its exact conductor. -/
theorem continuousQuasiChar_toData_trivialOnUnitFiltration_iff
    (chi : ContinuousQuasiChar F) (m r : ℕ)
    (hm : IsMultiplicativeConductor F chi m) :
    QuasiCharTrivialOnUnitFiltration F
        (continuousQuasiChar_toData F chi m hm).character r ↔
      m ≤ r :=
  (continuousQuasiChar_toData F chi m hm).trivialOnUnitFiltration_iff r

/-- For a wrapped standard quasi-character, conductor zero means exactly
triviality on the compact unit group `U^0`. -/
theorem continuousQuasiChar_toData_conductor_eq_zero_iff
    (chi : ContinuousQuasiChar F) (m : ℕ)
    (hm : IsMultiplicativeConductor F chi m) :
    (continuousQuasiChar_toData F chi m hm).conductor = 0 ↔
      ∀ u : Fˣ, u ∈ unitGroup F → chi u = 1 := by
  simpa only [continuousQuasiChar_toData_character] using
    (continuousQuasiChar_toData F chi m hm).conductor_eq_zero_iff_trivialOnUnitGroup

/-- The canonical compact unit group of a nonarchimedean local field is
compact as a subset of `Fˣ`. -/
private theorem isCompact_unitGroup : IsCompact (unitGroup F : Set Fˣ) := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  let A := (ValuativeRel.valuation F).valuationSubring
  have hA : IsCompact (A : Set F) := by
    exact IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have hAu : IsCompact (A.toSubmonoid.units : Set Fˣ) :=
    A.toSubmonoid.units_isCompact hA
  convert hAu using 1
  ext u
  change u ∈ A.unitGroup ↔ u ∈ A.toSubmonoid.units
  rw [ValuationSubring.mem_unitGroup_iff, Submonoid.mem_units_iff]
  change A.valuation (u : F) = 1 ↔
    (u : F) ∈ A ∧ ((u⁻¹ : Fˣ) : F) ∈ A
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff]
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro hu
    simp [hu]
  · rintro ⟨hu, huinv⟩
    have hu' : 1 ≤ A.valuation (u : F) := by
      exact (inv_le_one₀ (A.valuation.pos_iff.mpr (Units.ne_zero u))).mp huinv
    exact le_antisymm hu hu'

/-- A standard continuous quasi-character is unitary on the compact unit
group.  This is the compactness argument used in the manuscript and does not
depend on a conductor bound. -/
theorem continuousQuasiChar_norm_eq_one_of_mem_unitGroup
    (chi : ContinuousQuasiChar F) (u : Fˣ) (hu : u ∈ unitGroup F) :
    ‖(chi u : ℂ)‖ = 1 := by
  have himage : IsCompact
      ((fun x : Fˣ ↦ (chi x : ℂ)) '' (unitGroup F : Set Fˣ)) :=
    (isCompact_unitGroup F).image chi.continuous_coe
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp himage.isBounded
  have hle (v : Fˣ) (hv : v ∈ unitGroup F) : ‖(chi v : ℂ)‖ ≤ 1 := by
    by_contra hnot
    have hone : 1 < ‖(chi v : ℂ)‖ := lt_of_not_ge hnot
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hone
    have hpow := hC ((chi (v ^ k) : ℂ)) ⟨v ^ k, (unitGroup F).pow_mem hv k, rfl⟩
    have hpow' : ‖(chi v : ℂ)‖ ^ k ≤ C := by
      simpa only [map_pow, Units.val_pow_eq_pow_val, norm_pow] using hpow
    exact (not_lt_of_ge hpow') hk
  apply le_antisymm (hle u hu)
  have hinv := hle u⁻¹ ((unitGroup F).inv_mem hu)
  have hinv' : ‖(chi u : ℂ)‖⁻¹ ≤ 1 := by
    simpa only [map_inv, Units.val_inv_eq_inv_val, norm_inv] using hinv
  exact (inv_le_one₀ (norm_pos_iff.mpr (Units.ne_zero (chi u)))).mp hinv'

/-- The packaged form of compact-unit unitarity used by the exported local
constant identity. -/
theorem LocalQuasiCharData.norm_character_eq_one_of_mem_unitGroup
    (chi : LocalQuasiCharData F) (u : Fˣ) (hu : u ∈ unitGroup F) :
    ‖(chi.character u : ℂ)‖ = 1 :=
  continuousQuasiChar_norm_eq_one_of_mem_unitGroup F chi.character u hu

section PullbackCompatibility

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Algebra F K]
  [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]

/-- Wrapping an exact trace pullback gives precisely the trace pullback of
the wrapped downstairs character. -/
@[simp]
theorem continuousAddChar_toData_compTrace_character
    (psi : ContinuousAddChar F) (nF nK : ℤ)
    (hnF : IsAdditiveConductor F psi nF)
    (hnK : IsAdditiveConductor K psi.compTrace nK) :
    (continuousAddChar_toData K psi.compTrace nK hnK).character =
      (continuousAddChar_toData F psi nF hnF).character.compTrace :=
  rfl

/-- Trace pullback evaluation is unchanged by exact-conductor wrapping. -/
@[simp]
theorem continuousAddChar_toData_compTrace_apply
    (psi : ContinuousAddChar F) (nK : ℤ)
    (hnK : IsAdditiveConductor K psi.compTrace nK) (x : K) :
    (continuousAddChar_toData K psi.compTrace nK hnK).character x =
      psi (trace F K x) :=
  rfl

/-- Wrapping an exact norm pullback gives precisely the norm pullback of the
wrapped downstairs quasi-character. -/
@[simp]
theorem continuousQuasiChar_toData_compNorm_character
    (chi : ContinuousQuasiChar F) (mF mK : ℕ)
    (hmF : IsMultiplicativeConductor F chi mF)
    (hmK : IsMultiplicativeConductor K chi.compNorm mK) :
    (continuousQuasiChar_toData K chi.compNorm mK hmK).character =
      (continuousQuasiChar_toData F chi mF hmF).character.compNorm :=
  rfl

/-- Norm pullback evaluation is unchanged by exact-conductor wrapping. -/
@[simp]
theorem continuousQuasiChar_toData_compNorm_apply
    (chi : ContinuousQuasiChar F) (mK : ℕ)
    (hmK : IsMultiplicativeConductor K chi.compNorm mK) (x : Kˣ) :
    (continuousQuasiChar_toData K chi.compNorm mK hmK).character x =
      chi (normUnits F K x) :=
  rfl

end PullbackCompatibility

end

end LanglandsFirstMainLemma
