import LanglandsFirstMainLemma.Lamprecht.FiniteDuality
import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.LocalField.Lattices

/-!
# Stationary numerator classes

Let `chi` have exact multiplicative conductor `q > 1`, let `psi` have exact
additive conductor `n`, and suppose that `ord Gamma = M + n`.  At every depth
`r` with `ceil(q / 2) <= r <= q - 1`, this file constructs the stationary
numerator as the quotient class

`p^(M-q) / p^(M-r)`.

The class is the inverse image, under finite stationary-phase duality, of the
character induced by `x |-> chi(1+x)` on `p^r / p^q`.  No field-valued
representative is selected.  The representative theorem quantifies over every
numerator whose quotient class is the constructed class and proves both the
linearization identity and its exact order `M-q`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The manuscript's admissible range
`ceil(q / 2) <= r <= q - 1`, together with the required boundary `q > 1`.
The lower inequality is recorded in the equivalent division-free form
`q <= 2 * r`. -/
structure IsLamprechtStationaryDepth (q r : ℕ) : Prop where
  conductor_gt_one : 1 < q
  half_le : q ≤ 2 * r
  le_predecessor : r + 1 ≤ q

namespace IsLamprechtStationaryDepth

variable {q r : ℕ}

/-- Every admissible stationary depth is positive. -/
theorem pos (h : IsLamprechtStationaryDepth q r) : 0 < r := by
  rcases h with ⟨hq, hhalf, hupper⟩
  omega

/-- An admissible stationary depth lies below the conductor. -/
theorem le_conductor (h : IsLamprechtStationaryDepth q r) : r ≤ q := by
  rcases h with ⟨hq, hhalf, hupper⟩
  omega

/-- Integer-cast form of `le_conductor`, used by the lattice quotients. -/
theorem int_le_conductor (h : IsLamprechtStationaryDepth q r) :
    (r : ℤ) ≤ (q : ℤ) := by
  exact_mod_cast h.le_conductor

end IsLamprechtStationaryDepth

/-- The restriction of `chi` to `U^r`, descended through its exact conductor
layer `U^q`.  The input and output are quotient objects; the definition makes
no representative choice. -/
noncomputable def stationaryQuasiCharOnUnitQuotient
    (chi : LocalQuasiCharData F) {r : ℕ}
    (hr : IsLamprechtStationaryDepth chi.conductor r) :
    UnitFiltrationQuotient F r chi.conductor hr.le_conductor →* ℂˣ :=
  QuotientGroup.lift (unitFiltrationInside F hr.le_conductor)
    (chi.character.toMonoidHom.comp (unitFiltration F r).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact chi.isConductor.trivial _
        ((mem_unitFiltrationInside F hr.le_conductor u).1 hu))

@[simp]
theorem stationaryQuasiCharOnUnitQuotient_mk
    (chi : LocalQuasiCharData F) {r : ℕ}
    (hr : IsLamprechtStationaryDepth chi.conductor r)
    (u : unitFiltration F r) :
    stationaryQuasiCharOnUnitQuotient F chi hr
        (unitFiltrationQuotientMk F hr.le_conductor u) =
      chi.character (u : Fˣ) :=
  rfl

/-- The additive character `x |-> chi(1+x)` on `p^r / p^q`.

The positive-unit/lattice equivalence is multiplicative precisely because
`q <= 2*r`.  Composing its inverse with the descended quasi-character gives
this character without choosing a representative of either quotient. -/
noncomputable def stationaryLinearizationCharacterUnits
    (chi : LocalQuasiCharData F) {r : ℕ}
    (hr : IsLamprechtStationaryDepth chi.conductor r) :
    AddChar
      (LamprechtVariableQuotient F (chi.conductor : ℤ) (r : ℤ)
        hr.int_le_conductor)
      ℂˣ :=
  AddChar.toMonoidHomEquiv.symm
    ((stationaryQuasiCharOnUnitQuotient F chi hr).comp
      (positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
        hr.le_conductor hr.half_le).symm.toMonoidHom)

/-- Complex-valued form of `stationaryLinearizationCharacterUnits`, which is
the target required by `lamprechtPairingLeftEquiv`. -/
noncomputable def stationaryLinearizationCharacter
    (chi : LocalQuasiCharData F) {r : ℕ}
    (hr : IsLamprechtStationaryDepth chi.conductor r) :
    AddChar
      (LamprechtVariableQuotient F (chi.conductor : ℤ) (r : ℤ)
        hr.int_le_conductor)
      ℂ :=
  (Units.coeHom ℂ).compAddChar
    (stationaryLinearizationCharacterUnits F chi hr)

/-- Evaluation of the descended linearization character on any lattice
numerator is exactly `chi(1+x)`. -/
@[simp]
theorem stationaryLinearizationCharacter_mk
    (chi : LocalQuasiCharData F) {r : ℕ}
    (hr : IsLamprechtStationaryDepth chi.conductor r)
    (x : lattice F (r : ℤ)) :
    stationaryLinearizationCharacter F chi hr
        (latticeQuotientMk F hr.int_le_conductor x) =
      (chi.character (positiveUnitOfLattice F hr.pos x) : ℂ) :=
  rfl

/-- **The stationary numerator class at an admissible depth.**

This is a class in `p^(M-q) / p^(M-r)`, defined as the inverse image of
`x |-> chi(1+x)` under the perfect finite-duality equivalence.  In particular,
the public object is the quotient class itself and no field representative is
chosen, canonically or otherwise. -/
noncomputable def stationaryNumeratorClass
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    LamprechtCoefficientQuotient F M (chi.conductor : ℤ) (r : ℤ)
      hr.int_le_conductor :=
  (lamprechtPairingLeftEquiv F psi hr.int_le_conductor Gamma hGamma).symm
    (stationaryLinearizationCharacter F chi hr)

/-- The defining quotient-level characterization of the stationary class. -/
@[simp]
theorem lamprechtPairingLeft_stationaryNumeratorClass
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    lamprechtPairingLeft F psi hr.int_le_conductor Gamma hGamma
        (stationaryNumeratorClass F chi psi M hr Gamma hGamma) =
      stationaryLinearizationCharacter F chi hr := by
  change lamprechtPairingLeftEquiv F psi hr.int_le_conductor Gamma hGamma
      ((lamprechtPairingLeftEquiv F psi hr.int_le_conductor Gamma hGamma).symm
        (stationaryLinearizationCharacter F chi hr)) = _
  exact
    (lamprechtPairingLeftEquiv F psi hr.int_le_conductor Gamma hGamma).apply_symm_apply _

/-- Every numerator representing `stationaryNumeratorClass` gives the
manuscript's linearization on every `x` in `p^r`. -/
theorem stationaryNumeratorClass_linearization
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice F (M - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c =
      stationaryNumeratorClass F chi psi M hr Gamma hGamma)
    (x : lattice F (r : ℤ)) :
    chi.character (positiveUnitOfLattice F hr.pos x) =
      psi.character ((c : F) * (x : F) / (Gamma : F)) := by
  apply Units.ext
  have heval := congrArg
    (fun xi : AddChar
        (LamprechtVariableQuotient F (chi.conductor : ℤ) (r : ℤ)
          hr.int_le_conductor) ℂ =>
      xi (latticeQuotientMk F hr.int_le_conductor x))
    (lamprechtPairingLeft_stationaryNumeratorClass F chi psi M hr Gamma hGamma)
  rw [← hc, lamprechtPairingLeft_apply, lamprechtPairing_mk_mk,
    stationaryLinearizationCharacter_mk] at heval
  exact heval.symm

/-- A numerator represents the stationary quotient class if and only if it
gives the required linearization at every element of `p^r`.  This is the
representative-level uniqueness characterization. -/
theorem latticeQuotientMk_eq_stationaryNumeratorClass_iff
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice F (M - (chi.conductor : ℤ))) :
    latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c =
        stationaryNumeratorClass F chi psi M hr Gamma hGamma ↔
      ∀ x : lattice F (r : ℤ),
        chi.character (positiveUnitOfLattice F hr.pos x) =
          psi.character ((c : F) * (x : F) / (Gamma : F)) := by
  constructor
  · intro hc x
    exact stationaryNumeratorClass_linearization
      F chi psi M hr Gamma hGamma c hc x
  · intro hlinear
    apply lamprechtPairingLeft_injective F psi hr.int_le_conductor Gamma hGamma
    apply AddChar.ext
    intro z
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F hr.int_le_conductor z
    rw [lamprechtPairingLeft_apply, lamprechtPairing_mk_mk,
      lamprechtPairingLeft_stationaryNumeratorClass,
      stationaryLinearizationCharacter_mk]
    exact congrArg Units.val (hlinear x).symm

/-- Predicate saying that a coefficient quotient class satisfies the
representative-level stationary linearization.  It quantifies over every
representative rather than selecting one. -/
def IsStationaryNumeratorClass
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (s : LamprechtCoefficientQuotient F M (chi.conductor : ℤ) (r : ℤ)
      hr.int_le_conductor) : Prop :=
  ∀ (c : lattice F (M - (chi.conductor : ℤ))),
    latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c = s →
      ∀ x : lattice F (r : ℤ),
        chi.character (positiveUnitOfLattice F hr.pos x) =
          psi.character ((c : F) * (x : F) / (Gamma : F))

/-- The constructed quotient class satisfies the stationary
linearization for every one of its representatives. -/
theorem stationaryNumeratorClass_isStationary
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    IsStationaryNumeratorClass F chi psi M hr Gamma
      (stationaryNumeratorClass F chi psi M hr Gamma hGamma) := by
  intro c hc x
  exact stationaryNumeratorClass_linearization F chi psi M hr Gamma hGamma c hc x

/-- Uniqueness of the stationary numerator as a quotient class. -/
theorem stationaryNumeratorClass_unique
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (s : LamprechtCoefficientQuotient F M (chi.conductor : ℤ) (r : ℤ)
      hr.int_le_conductor)
    (hs : IsStationaryNumeratorClass F chi psi M hr Gamma s) :
    s = stationaryNumeratorClass F chi psi M hr Gamma hGamma := by
  apply lamprechtPairingLeft_injective F psi hr.int_le_conductor Gamma hGamma
  apply AddChar.ext
  intro z
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F hr.int_le_conductor z
  obtain ⟨c, hc⟩ :=
    latticeQuotientMk_surjective F
      (sub_le_sub_left hr.int_le_conductor M) s
  rw [← hc, lamprechtPairingLeft_apply, lamprechtPairing_mk_mk,
    lamprechtPairingLeft_stationaryNumeratorClass,
    stationaryLinearizationCharacter_mk]
  exact congrArg Units.val (hs c hc x).symm

/-- Existence and uniqueness in the exact representative-level formulation
of the manuscript. -/
theorem stationaryNumeratorClass_existsUnique
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    ∃! s : LamprechtCoefficientQuotient F M (chi.conductor : ℤ) (r : ℤ)
        hr.int_le_conductor,
      IsStationaryNumeratorClass F chi psi M hr Gamma s := by
  refine ⟨stationaryNumeratorClass F chi psi M hr Gamma hGamma,
    stationaryNumeratorClass_isStationary F chi psi M hr Gamma hGamma, ?_⟩
  intro s hs
  exact stationaryNumeratorClass_unique F chi psi M hr Gamma hGamma s hs

/-- Changing the representative of the stationary quotient class does not
change the right-hand side of the linearization. -/
theorem stationaryNumeratorClass_representative_independent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (c c' : lattice F (M - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c =
      stationaryNumeratorClass F chi psi M hr Gamma hGamma)
    (hc' : latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c' =
      stationaryNumeratorClass F chi psi M hr Gamma hGamma)
    (x : lattice F (r : ℤ)) :
    psi.character ((c : F) * (x : F) / (Gamma : F)) =
      psi.character ((c' : F) * (x : F) / (Gamma : F)) := by
  rw [← stationaryNumeratorClass_linearization F chi psi M hr Gamma hGamma c hc x,
    ← stationaryNumeratorClass_linearization F chi psi M hr Gamma hGamma c' hc' x]

/-- Every representative of the stationary numerator class has exact order
`M-q`, as required by the manuscript. -/
theorem stationaryNumeratorClass_representative_ord
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice F (M - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c =
      stationaryNumeratorClass F chi psi M hr Gamma hGamma) :
    ord F (c : F) =
      ((M - (chi.conductor : ℤ) : ℤ) : WithTop ℤ) := by
  rw [← mem_lattice_and_not_mem_succ_iff F]
  refine And.intro c.property ?_
  intro hcDeep
  have hq := hr.conductor_gt_one
  have htrivial : QuasiCharTrivialOnUnitFiltration F chi.character
      (chi.conductor - 1) := by
    intro u hu
    have hpredPos : 0 < chi.conductor - 1 := by
      omega
    let u0 : unitFiltration F (chi.conductor - 1) := ⟨u, hu⟩
    let x0 : lattice F ((chi.conductor - 1 : ℕ) : ℤ) :=
      positiveUnitDisplacement F hpredPos u0
    have hx : (x0 : F) ∈ lattice F (r : ℤ) :=
      lattice_antitone F
        (by
          exact_mod_cast
            (show r ≤ chi.conductor - 1 by
              have hupper := hr.le_predecessor
              omega))
        x0.property
    let x : lattice F (r : ℤ) := ⟨(x0 : F), hx⟩
    have hlinear := stationaryNumeratorClass_linearization
      F chi psi M hr Gamma hGamma c hc x
    have hunit : (positiveUnitOfLattice F hr.pos x : Fˣ) = u := by
      apply Units.ext
      simp [x, x0, u0, positiveUnitDisplacement]
    rw [hunit] at hlinear
    rw [hlinear]
    apply psi.isConductor.trivial
    apply ((forall_mul_div_mem_lattice_iff_left F hGamma).2 ?_)
      (x0 : F) x0.property
    have hdepth : M - ((chi.conductor - 1 : ℕ) : ℤ) =
        M - (chi.conductor : ℤ) + 1 := by
      omega
    simpa only [hdepth] using hcDeep
  exact (chi.isConductor.not_trivialOnUnitFiltration_iff.2 (by omega)) htrivial

end

end LanglandsFirstMainLemma
