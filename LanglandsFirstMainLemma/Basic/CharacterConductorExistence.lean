import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.Basic.StandardCharacterBridge
import LanglandsFirstMainLemma.LocalField.Lattices
import LanglandsFirstMainLemma.LocalField.UnitFiltration
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace LanglandsFirstMainLemma

/-!
# Existence of exact character conductors

This file proves that continuity supplies exact conductors for the two local
character types used in the project.  The proof first turns a nonzero complex
value into its unit-circle phase.  Continuity puts a sufficiently deep unit
filtration or valuation lattice in the centered half-circle, and closure under
positive powers then lets `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two`
force the phase to be one.  Compactness supplies the separate assertion that
the original character values have norm one on the relevant compact subgroup.

The eventual triviality statements are converted to exact conductors by
`Nat.find` in the multiplicative case and by the least-element property of the
integers in the nontrivial additive case.  The final definitions package the
result without changing the supplied character.
-/

noncomputable section

open Filter Topology

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## Circle-valued phases -/

/-- The unit-circle point represented by the total complex phase. -/
private noncomputable def circlePhase (z : ℂ) : Circle :=
  ⟨phase z, mem_sphere_zero_iff_norm.2 (phase_norm z)⟩

@[simp]
private theorem coe_circlePhase (z : ℂ) :
    (circlePhase z : ℂ) = phase z :=
  rfl

@[simp]
private theorem circlePhase_one : circlePhase 1 = 1 := by
  apply Circle.ext
  exact phase_of_norm_eq_one norm_one

@[simp]
private theorem circlePhase_pow (z : ℂ) (n : ℕ) :
    circlePhase (z ^ n) = circlePhase z ^ n := by
  apply Circle.ext
  simpa only [coe_circlePhase, Circle.coe_pow] using phase_pow z n

/-- The circle-valued phase of a continuous nowhere-zero complex function is
continuous.  The nowhere-zero hypothesis removes the discontinuous branch of
the totalized phase at the origin. -/
private theorem continuous_circlePhase_comp
    {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (hf0 : ∀ x, f x ≠ 0) :
    Continuous (fun x ↦ circlePhase (f x)) := by
  change Continuous (fun x ↦
    (⟨phase (f x), mem_sphere_zero_iff_norm.2 (phase_norm (f x))⟩ : Circle))
  apply Continuous.subtype_mk
  have hnorm : Continuous (fun x ↦ ((‖f x‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hf.norm
  have hnorm0 : ∀ x, ((‖f x‖ : ℝ) : ℂ) ≠ 0 := fun x ↦
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf0 x))
  convert hf.div₀ hnorm hnorm0 using 1
  funext x
  exact phase_of_ne_zero (hf0 x)

/-- The centered half-circle is an open neighborhood of one. -/
private theorem centeredArc_pi_div_two_mem_nhds_one :
    Circle.centeredArc (Real.pi / 2) ∈ nhds (1 : Circle) := by
  apply (Circle.isOpen_centeredArc (Real.pi / 2)).mem_nhds
  rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
  simp [Real.pi_pos]

/-! ## Compact-subgroup unitarity -/

/-- Every integer-indexed valuation lattice is compact.  This is the same
closed-ball identification used by the finite-quotient layer, repeated here
because conductor existence is foundationally earlier than that layer. -/
private theorem isCompact_lattice_for_character (r : ℤ) :
    IsCompact (lattice F r : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F r
  have hcompact := IsNonarchimedeanLocalField.isCompact_closedBall F
    (ValuativeRel.valuation F a)
  convert hcompact using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)]

/-- A continuous additive character is unitary on every compact valuation
lattice.  Boundedness of the image and closure under natural multiples rule
out norm greater than one; applying the same argument to `-x` rules out norm
less than one. -/
theorem continuousAddChar_norm_eq_one_of_mem_lattice
    (psi : ContinuousAddChar F) (r : ℤ) (x : F)
    (hx : x ∈ lattice F r) :
    ‖(psi x : ℂ)‖ = 1 := by
  have himage : IsCompact
      ((fun y : F ↦ (psi y : ℂ)) '' (lattice F r : Set F)) :=
    (isCompact_lattice_for_character F r).image psi.continuous_coe
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp himage.isBounded
  have hle (y : F) (hy : y ∈ lattice F r) : ‖(psi y : ℂ)‖ ≤ 1 := by
    by_contra hnot
    have hone : 1 < ‖(psi y : ℂ)‖ := lt_of_not_ge hnot
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hone
    have hbound := hC ((psi (k • y) : ℂ))
      ⟨k • y, nsmul_mem hy k, rfl⟩
    have hmapUnits := AddChar.map_nsmul_eq_pow psi.toAddChar k y
    have hmap : (psi (k • y) : ℂ) = (psi y : ℂ) ^ k := by
      exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) hmapUnits
    have hpow : ‖(psi y : ℂ)‖ ^ k ≤ C := by
      simpa only [hmap, norm_pow] using hbound
    exact (not_lt_of_ge hpow) hk
  apply le_antisymm (hle x hx)
  have hinv := hle (-x) ((lattice F r).neg_mem hx)
  have hmapNegUnits := AddChar.map_neg_eq_inv psi.toAddChar x
  have hmapNeg : (psi (-x) : ℂ) = (psi x : ℂ)⁻¹ := by
    simpa only [ContinuousAddChar.toAddChar_apply, Units.val_inv_eq_inv_val] using
      congrArg (fun u : ℂˣ ↦ (u : ℂ)) hmapNegUnits
  have hinv' : ‖(psi x : ℂ)‖⁻¹ ≤ 1 := by
    simpa only [hmapNeg, norm_inv] using hinv
  exact (inv_le_one₀ (norm_pos_iff.mpr (Units.ne_zero (psi x)))).mp hinv'

/-! ## Eventual multiplicative triviality -/

/-- Continuity forces a quasi-character to be trivial on some positive unit
filtration.  The character is unitary there because every positive layer is
contained in the compact unit group. -/
theorem exists_quasiCharTrivialOnUnitFiltration
    (chi : ContinuousQuasiChar F) :
    ∃ m : ℕ, QuasiCharTrivialOnUnitFiltration F chi m := by
  let f : Fˣ → Circle := fun u ↦ circlePhase (chi u : ℂ)
  have hf : Continuous f :=
    continuous_circlePhase_comp chi.continuous_coe
      (fun u ↦ ContinuousQuasiChar.apply_ne_zero chi u)
  have hpre : f ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ nhds (1 : Fˣ) := by
    have hfAt : ContinuousAt f (1 : Fˣ) := hf.continuousAt
    have harc : Circle.centeredArc (Real.pi / 2) ∈ nhds (f 1) := by
      simpa only [f, map_one, Units.val_one, circlePhase_one] using
        centeredArc_pi_div_two_mem_nhds_one
    exact hfAt.preimage_mem_nhds harc
  obtain ⟨k, _hk, hsubset⟩ :=
    (unitFiltration_hasBasis_nhds_one F).mem_iff.mp hpre
  refine ⟨k + 1, ?_⟩
  intro u hu
  have hphase : circlePhase (chi u : ℂ) = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n hn
    have hpowmem : u ^ n ∈ unitFiltration F (k + 1) :=
      (unitFiltration F (k + 1)).pow_mem hu n
    have harc := hsubset hpowmem
    change circlePhase (chi (u ^ n) : ℂ) ∈
      Circle.centeredArc (Real.pi / 2) at harc
    have hmap : (chi (u ^ n) : ℂ) = (chi u : ℂ) ^ n := by
      simp only [map_pow, Units.val_pow_eq_pow_val]
    simpa only [hmap, circlePhase_pow] using harc
  have hphaseCoe := congrArg (fun z : Circle ↦ (z : ℂ)) hphase
  change phase (chi u : ℂ) = 1 at hphaseCoe
  have hnorm : ‖(chi u : ℂ)‖ = 1 :=
    continuousQuasiChar_norm_eq_one_of_mem_unitGroup F chi u
      (unitFiltration_le_unitGroup F (k + 1) hu)
  apply Units.ext
  change (chi u : ℂ) = 1
  calc
    (chi u : ℂ) = phase (chi u : ℂ) := (phase_of_norm_eq_one hnorm).symm
    _ = 1 := hphaseCoe

/-! ## Eventual additive triviality -/

/-- Continuity forces an additive character to be trivial on some sufficiently
deep fractional lattice.  Compact-lattice unitarity and the centered-arc
small-subgroup argument are kept separate. -/
theorem exists_addCharTrivialOnLattice
    (psi : ContinuousAddChar F) :
    ∃ r : ℤ, AddCharTrivialOnLattice F psi r := by
  let f : F → Circle := fun x ↦ circlePhase (psi x : ℂ)
  have hf : Continuous f :=
    continuous_circlePhase_comp psi.continuous_coe
      (fun x ↦ ContinuousAddChar.apply_ne_zero psi x)
  have hpre : f ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ nhds (0 : F) := by
    have hfAt : ContinuousAt f (0 : F) := hf.continuousAt
    have harc : Circle.centeredArc (Real.pi / 2) ∈ nhds (f 0) := by
      simpa only [f, ContinuousAddChar.map_zero_eq_one, Units.val_one,
        circlePhase_one] using centeredArc_pi_div_two_mem_nhds_one
    exact hfAt.preimage_mem_nhds harc
  obtain ⟨r, hsubset⟩ := exists_lattice_subset_of_mem_nhds_zero F hpre
  refine ⟨r, ?_⟩
  intro x hx
  have hphase : circlePhase (psi x : ℂ) = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n hn
    have hnsmul : n • x ∈ lattice F r := nsmul_mem hx n
    have harc := hsubset hnsmul
    change circlePhase (psi (n • x) : ℂ) ∈
      Circle.centeredArc (Real.pi / 2) at harc
    have hmapUnits := AddChar.map_nsmul_eq_pow psi.toAddChar n x
    have hmap : (psi (n • x) : ℂ) = (psi x : ℂ) ^ n := by
      exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) hmapUnits
    simpa only [hmap, circlePhase_pow] using harc
  have hphaseCoe := congrArg (fun z : Circle ↦ (z : ℂ)) hphase
  change phase (psi x : ℂ) = 1 at hphaseCoe
  have hnorm : ‖(psi x : ℂ)‖ = 1 :=
    continuousAddChar_norm_eq_one_of_mem_lattice F psi r x hx
  apply Units.ext
  change (psi x : ℂ) = 1
  calc
    (psi x : ℂ) = phase (psi x : ℂ) := (phase_of_norm_eq_one hnorm).symm
    _ = 1 := hphaseCoe

/-! ## Exact conductor existence -/

/-- Every continuous quasi-character has an exact multiplicative conductor.
The least trivial unit depth is selected by `Nat.find`. -/
theorem exists_isMultiplicativeConductor
    (chi : ContinuousQuasiChar F) :
    ∃ m : ℕ, IsMultiplicativeConductor F chi m := by
  classical
  let h := exists_quasiCharTrivialOnUnitFiltration F chi
  let m := Nat.find h
  refine ⟨m, ?_⟩
  refine
    { trivial := Nat.find_spec h
      minimal := ?_ }
  intro r hr
  exact Nat.find_min' h hr

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- A nontrivial additive character has a point at which it is not one. -/
theorem continuousAddChar_exists_ne_one
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    ∃ x : F, psi x ≠ 1 := by
  by_contra hnone
  apply hpsi
  apply ContinuousAddChar.ext
  intro x
  by_contra hx
  exact hnone ⟨x, by simpa only [ContinuousAddChar.one_apply] using hx⟩

/-- Triviality depths of a nontrivial additive character are bounded below.
A single point where the character is nontrivial supplies the bound. -/
private theorem addChar_trivial_depths_bddBelow
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    ∃ b : ℤ, ∀ r : ℤ, AddCharTrivialOnLattice F psi r → b ≤ r := by
  obtain ⟨x, hx⟩ := continuousAddChar_exists_ne_one F psi hpsi
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    exact hx (ContinuousAddChar.map_zero_eq_one psi)
  obtain ⟨k, hk⟩ :=
    WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hx0)
  refine ⟨k + 1, ?_⟩
  intro r hr
  by_contra hkr
  have hrk : r ≤ k := by omega
  have hxk : x ∈ lattice F k := by
    rw [mem_lattice, hk]
  have hxr : x ∈ lattice F r := lattice_antitone F hrk hxk
  exact hx (hr x hxr)

/-- Every nontrivial continuous additive character has an exact additive
conductor in the manuscript's sign convention.  The least trivial lattice
depth `r` is selected in `ℤ`, and the exported conductor is `-r`. -/
theorem exists_isAdditiveConductor
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    ∃ n : ℤ, IsAdditiveConductor F psi n := by
  have hinh : ∃ r : ℤ, AddCharTrivialOnLattice F psi r :=
    exists_addCharTrivialOnLattice F psi
  obtain ⟨r, hr, hmin⟩ := Int.exists_least_of_bdd
    (addChar_trivial_depths_bddBelow F psi hpsi) hinh
  refine ⟨-r, ?_⟩
  refine
    { trivial := ?_
      minimal := ?_ }
  · simpa only [neg_neg] using hr
  · intro s hs
    simpa only [neg_neg] using hmin s hs

/-! ## Canonical conductor exponents -/

/-- The unique multiplicative conductor exponent of a continuous
quasi-character. -/
noncomputable def multiplicativeConductorExponent
    (chi : ContinuousQuasiChar F) : ℕ :=
  Classical.choose (exists_isMultiplicativeConductor F chi)

/-- The selected multiplicative conductor exponent is exact. -/
theorem multiplicativeConductorExponent_isConductor
    (chi : ContinuousQuasiChar F) :
    IsMultiplicativeConductor F chi (multiplicativeConductorExponent F chi) :=
  Classical.choose_spec (exists_isMultiplicativeConductor F chi)

/-- Any exact multiplicative conductor equals the selected exponent. -/
theorem multiplicativeConductorExponent_eq_of_isConductor
    (chi : ContinuousQuasiChar F) {m : ℕ}
    (hm : IsMultiplicativeConductor F chi m) :
    multiplicativeConductorExponent F chi = m :=
  (multiplicativeConductorExponent_isConductor F chi).unique hm

/-- Triviality on a unit layer is characterized by comparison with the
canonical multiplicative conductor exponent. -/
theorem quasiCharTrivialOnUnitFiltration_iff_conductorExponent_le
    (chi : ContinuousQuasiChar F) (r : ℕ) :
    QuasiCharTrivialOnUnitFiltration F chi r ↔
      multiplicativeConductorExponent F chi ≤ r :=
  (multiplicativeConductorExponent_isConductor F chi).trivialOnUnitFiltration_iff

/-- The unique additive conductor exponent of a nontrivial continuous
additive character. -/
noncomputable def additiveConductorExponent
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) : ℤ :=
  Classical.choose (exists_isAdditiveConductor F psi hpsi)

/-- The selected additive conductor exponent is exact. -/
theorem additiveConductorExponent_isConductor
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    IsAdditiveConductor F psi (additiveConductorExponent F psi hpsi) :=
  Classical.choose_spec (exists_isAdditiveConductor F psi hpsi)

/-- The selected additive exponent is independent of the proof of
nontriviality. -/
theorem additiveConductorExponent_proof_irrel
    (psi : ContinuousAddChar F) (hpsi hpsi' : psi ≠ 1) :
    additiveConductorExponent F psi hpsi =
      additiveConductorExponent F psi hpsi' := by
  have hh : hpsi = hpsi' := Subsingleton.elim _ _
  subst hpsi'
  rfl

/-- Any exact additive conductor equals the selected exponent. -/
theorem additiveConductorExponent_eq_of_isConductor
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) {n : ℤ}
    (hn : IsAdditiveConductor F psi n) :
    additiveConductorExponent F psi hpsi = n :=
  (additiveConductorExponent_isConductor F psi hpsi).unique hn

/-- Triviality on a lattice is characterized by comparison with the
canonical additive conductor exponent, with the manuscript's sign. -/
theorem addCharTrivialOnLattice_iff_neg_conductorExponent_le
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) (r : ℤ) :
    AddCharTrivialOnLattice F psi r ↔
      -additiveConductorExponent F psi hpsi ≤ r :=
  (additiveConductorExponent_isConductor F psi hpsi).trivialOnLattice_iff

/-! ## Early extensionality for proof-bearing character data -/

namespace LocalQuasiCharData

variable {F}

/-- Proof-bearing quasi-character data are determined by their character,
because the exact multiplicative conductor is unique.  This early-layer name
avoids importing the later Delta extensionality helper. -/
theorem eq_of_character_eq {chi omega : LocalQuasiCharData F}
    (h : chi.character = omega.character) : chi = omega := by
  cases chi with
  | mk chi m hchi =>
      cases omega with
      | mk omega n homega =>
          dsimp at h
          subst omega
          have hmn : m = n := hchi.unique homega
          subst n
          rfl

end LocalQuasiCharData

namespace LocalAddCharData

variable {F}

/-- Proof-bearing additive-character data are determined by their character,
because the exact additive conductor is unique. -/
theorem eq_of_character_eq {psi omega : LocalAddCharData F}
    (h : psi.character = omega.character) : psi = omega := by
  cases psi with
  | mk psi m hpsi =>
      cases omega with
      | mk omega n homega =>
          dsimp at h
          subst omega
          have hmn : m = n := hpsi.unique homega
          subst n
          rfl

end LocalAddCharData

/-! ## Canonical exact-conductor packages -/

/-- The canonical exact-conductor package attached to a continuous
quasi-character. -/
noncomputable def canonicalLocalQuasiCharData
    (chi : ContinuousQuasiChar F) : LocalQuasiCharData F where
  character := chi
  conductor := multiplicativeConductorExponent F chi
  isConductor := multiplicativeConductorExponent_isConductor F chi

@[simp]
theorem canonicalLocalQuasiCharData_character
    (chi : ContinuousQuasiChar F) :
    (canonicalLocalQuasiCharData F chi).character = chi :=
  rfl

@[simp]
theorem canonicalLocalQuasiCharData_apply
    (chi : ContinuousQuasiChar F) (u : Fˣ) :
    (canonicalLocalQuasiCharData F chi).character u = chi u :=
  rfl

theorem canonicalLocalQuasiCharData_isConductor
    (chi : ContinuousQuasiChar F) :
    IsMultiplicativeConductor F chi
      (canonicalLocalQuasiCharData F chi).conductor :=
  (canonicalLocalQuasiCharData F chi).isConductor

/-- The canonical quasi-character package is the unique exact-conductor datum
with the supplied character. -/
theorem canonicalLocalQuasiCharData_eq
    (chi : LocalQuasiCharData F) :
    canonicalLocalQuasiCharData F chi.character = chi :=
  LocalQuasiCharData.eq_of_character_eq rfl

/-- Equality of canonical quasi-character packages is exactly equality of the
underlying continuous characters. -/
theorem canonicalLocalQuasiCharData_eq_iff
    {chi omega : ContinuousQuasiChar F} :
    canonicalLocalQuasiCharData F chi = canonicalLocalQuasiCharData F omega ↔
      chi = omega := by
  constructor
  · intro h
    exact congrArg LocalQuasiCharData.character h
  · rintro rfl
    rfl

/-- The canonical exact-conductor package attached to a nontrivial continuous
additive character.  The nontriviality proof remains an explicit argument. -/
noncomputable def canonicalLocalAddCharData
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) : LocalAddCharData F where
  character := psi
  conductor := additiveConductorExponent F psi hpsi
  isConductor := additiveConductorExponent_isConductor F psi hpsi

@[simp]
theorem canonicalLocalAddCharData_character
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    (canonicalLocalAddCharData F psi hpsi).character = psi :=
  rfl

@[simp]
theorem canonicalLocalAddCharData_apply
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) (x : F) :
    (canonicalLocalAddCharData F psi hpsi).character x = psi x :=
  rfl

theorem canonicalLocalAddCharData_isConductor
    (psi : ContinuousAddChar F) (hpsi : psi ≠ 1) :
    IsAdditiveConductor F psi
      (canonicalLocalAddCharData F psi hpsi).conductor :=
  (canonicalLocalAddCharData F psi hpsi).isConductor

/-- The canonical additive-character package is the unique exact-conductor
datum with the supplied character. -/
theorem canonicalLocalAddCharData_eq
    (psi : LocalAddCharData F) :
    canonicalLocalAddCharData F psi.character psi.character_ne_one = psi :=
  LocalAddCharData.eq_of_character_eq rfl

/-- Equality of canonical additive-character packages implies equality of the
underlying characters. -/
theorem eq_of_canonicalLocalAddCharData_eq
    {psi omega : ContinuousAddChar F} (hpsi : psi ≠ 1) (homega : omega ≠ 1)
    (h : canonicalLocalAddCharData F psi hpsi =
      canonicalLocalAddCharData F omega homega) :
    psi = omega :=
  congrArg LocalAddCharData.character h

/-- The principal architecture theorem: exact multiplicative conductors exist
for all continuous quasi-characters, and exact additive conductors exist for
all nontrivial continuous additive characters. -/
theorem characterConductorExistence :
    (∀ chi : ContinuousQuasiChar F,
      ∃ m : ℕ, IsMultiplicativeConductor F chi m) ∧
    (∀ psi : ContinuousAddChar F, psi ≠ 1 →
      ∃ n : ℤ, IsAdditiveConductor F psi n) :=
  ⟨exists_isMultiplicativeConductor F, exists_isAdditiveConductor F⟩

end

end LanglandsFirstMainLemma
