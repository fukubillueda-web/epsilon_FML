import LanglandsFirstMainLemma.Basic.CharacterTypes
import LanglandsFirstMainLemma.LocalField.UnitFiltration

/-!
# Exact additive and multiplicative conductor data

For a nonarchimedean local field `F`, this file records the manuscript's two
conductor conventions as proof-bearing data.

* An additive character has conductor `n : ℤ` when `𝔭_F ^ (-n)` is the
  largest fractional valuation lattice on which it is trivial.
* A quasi-character has conductor `m : ℕ` when `U_F ^ m` is the first layer
  of the unit filtration on which it is trivial.

The predicates below concern triviality on an entire lattice or subgroup.
They deliberately do not identify those sets with the pointwise kernel of a
character: individual elements outside the conductor lattice or layer can
still have value `1`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An additive character is trivial at lattice depth `r` when it is `1` on
the whole fractional valuation lattice `𝔭_F ^ r`. -/
def AddCharTrivialOnLattice (ψ : ContinuousAddChar F) (r : ℤ) : Prop :=
  ∀ x : F, x ∈ lattice F r → ψ x = 1

/-- A quasi-character is trivial at unit depth `m` when it is `1` on the
whole subgroup `U_F ^ m`. -/
def QuasiCharTrivialOnUnitFiltration (χ : ContinuousQuasiChar F) (m : ℕ) : Prop :=
  ∀ u : Fˣ, u ∈ unitFiltration F m → χ u = 1

/-- Additive triviality persists after increasing the lattice depth. -/
theorem addCharTrivialOnLattice_mono {ψ : ContinuousAddChar F} {r s : ℤ}
    (hrs : r ≤ s) (hψ : AddCharTrivialOnLattice F ψ r) :
    AddCharTrivialOnLattice F ψ s := by
  intro x hx
  exact hψ x (lattice_antitone F hrs hx)

/-- Multiplicative triviality persists after increasing the unit-filtration
depth. -/
theorem quasiCharTrivialOnUnitFiltration_mono {χ : ContinuousQuasiChar F}
    {m r : ℕ} (hmr : m ≤ r) (hχ : QuasiCharTrivialOnUnitFiltration F χ m) :
    QuasiCharTrivialOnUnitFiltration F χ r := by
  intro u hu
  exact hχ u (unitFiltration_antitone F hmr hu)

/-- Inverting an additive character does not change the lattices on which it
is trivial. -/
theorem addCharTrivialOnLattice_inv_iff (ψ : ContinuousAddChar F) (r : ℤ) :
    AddCharTrivialOnLattice F ψ⁻¹ r ↔ AddCharTrivialOnLattice F ψ r := by
  constructor <;> intro h x hx
  · simpa only [ContinuousAddChar.inv_apply, inv_eq_one] using h x hx
  · simpa only [ContinuousAddChar.inv_apply, inv_eq_one] using h x hx

/-- Inverting a quasi-character does not change the unit layers on which it
is trivial. -/
theorem quasiCharTrivialOnUnitFiltration_inv_iff
    (χ : ContinuousQuasiChar F) (m : ℕ) :
    QuasiCharTrivialOnUnitFiltration F χ⁻¹ m ↔
      QuasiCharTrivialOnUnitFiltration F χ m := by
  constructor <;> intro h u hu
  · simpa only [ContinuousQuasiChar.inv_apply, inv_eq_one] using h u hu
  · simpa only [ContinuousQuasiChar.inv_apply, inv_eq_one] using h u hu

/-- A product of additive characters trivial on the same lattice remains
trivial there. -/
theorem AddCharTrivialOnLattice.mul {ψ φ : ContinuousAddChar F} {r : ℤ}
    (hψ : AddCharTrivialOnLattice F ψ r)
    (hφ : AddCharTrivialOnLattice F φ r) :
    AddCharTrivialOnLattice F (ψ * φ) r := by
  intro x hx
  simp only [ContinuousAddChar.mul_apply, hψ x hx, hφ x hx, mul_one]

/-- A product of quasi-characters trivial on the same unit layer remains
trivial there. -/
theorem QuasiCharTrivialOnUnitFiltration.mul
    {χ ω : ContinuousQuasiChar F} {m : ℕ}
    (hχ : QuasiCharTrivialOnUnitFiltration F χ m)
    (hω : QuasiCharTrivialOnUnitFiltration F ω m) :
    QuasiCharTrivialOnUnitFiltration F (χ * ω) m := by
  intro u hu
  simp only [ContinuousQuasiChar.mul_apply, hχ u hu, hω u hu, mul_one]

/-- `n` is the additive conductor of `ψ` in Langlands's convention: `ψ` is
trivial on `𝔭_F ^ (-n)`, and no strictly larger fractional lattice is a
triviality lattice.  In terms of lattice depths, `-n` is therefore the least
depth at which `ψ` is trivial. -/
structure IsAdditiveConductor (ψ : ContinuousAddChar F) (n : ℤ) : Prop where
  trivial : AddCharTrivialOnLattice F ψ (-n)
  minimal : ∀ r : ℤ, AddCharTrivialOnLattice F ψ r → -n ≤ r

/-- `m` is the multiplicative conductor of `χ`: `χ` is trivial on `U_F ^ m`,
and `m` is the least natural-number depth with that property. -/
structure IsMultiplicativeConductor (χ : ContinuousQuasiChar F) (m : ℕ) : Prop where
  trivial : QuasiCharTrivialOnUnitFiltration F χ m
  minimal : ∀ r : ℕ, QuasiCharTrivialOnUnitFiltration F χ r → m ≤ r

namespace IsAdditiveConductor

variable {F}

/-- Exact additive conductor data characterize every triviality lattice, not
just the boundary lattice. -/
theorem trivialOnLattice_iff {ψ : ContinuousAddChar F} {n r : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    AddCharTrivialOnLattice F ψ r ↔ -n ≤ r := by
  constructor
  · exact h.minimal r
  · intro hnr
    exact addCharTrivialOnLattice_mono F hnr h.trivial

/-- In the manuscript's conductor indexing, `ψ` is trivial on `𝔭_F ^ (-k)`
exactly when `k ≤ n`. -/
theorem trivialOnNegLattice_iff {ψ : ContinuousAddChar F} {n k : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    AddCharTrivialOnLattice F ψ (-k) ↔ k ≤ n := by
  rw [h.trivialOnLattice_iff]
  omega

/-- Below the exact additive boundary the character is not trivial on the
whole lattice. -/
theorem not_trivialOnLattice_iff {ψ : ContinuousAddChar F} {n r : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    ¬ AddCharTrivialOnLattice F ψ r ↔ r < -n := by
  rw [h.trivialOnLattice_iff]
  omega

/-- Exactness rules out triviality on the immediately larger lattice
`𝔭_F ^ (-n-1)`. -/
theorem not_trivialOnPredecessor {ψ : ContinuousAddChar F} {n : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    ¬ AddCharTrivialOnLattice F ψ (-n - 1) := by
  rw [h.not_trivialOnLattice_iff]
  omega

/-- The immediately larger lattice contains an explicit point where an exact
additive-conductor character is nontrivial.  Such a point cannot lie in the
conductor lattice itself. -/
theorem exists_ne_one_on_predecessor {ψ : ContinuousAddChar F} {n : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    ∃ x : F, x ∈ lattice F (-n - 1) ∧ x ∉ lattice F (-n) ∧ ψ x ≠ 1 := by
  have hex : ∃ x : F, x ∈ lattice F (-n - 1) ∧ ψ x ≠ 1 := by
    by_contra hnone
    apply h.not_trivialOnPredecessor
    intro x hx
    by_contra hψx
    exact hnone ⟨x, hx, hψx⟩
  obtain ⟨x, hx, hψx⟩ := hex
  refine ⟨x, hx, ?_, hψx⟩
  intro hx'
  exact hψx (h.trivial x hx')

/-- A witness on the preceding additive lattice has exact order `-n-1`. -/
theorem exists_ord_eq_predecessor {ψ : ContinuousAddChar F} {n : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    ∃ x : F, ord F x = ((-n - 1 : ℤ) : WithTop ℤ) ∧ ψ x ≠ 1 := by
  obtain ⟨x, hx, hx', hψx⟩ := h.exists_ne_one_on_predecessor
  refine ⟨x, ?_, hψx⟩
  rw [← mem_lattice_and_not_mem_succ_iff F]
  simpa only [sub_add_cancel] using And.intro hx hx'

/-- More generally, every lattice strictly larger than the conductor lattice
contains a point at which the additive character is nontrivial. -/
theorem exists_ne_one_of_lt {ψ : ContinuousAddChar F} {n r : ℤ}
    (h : IsAdditiveConductor F ψ n) (hr : r < -n) :
    ∃ x : F, x ∈ lattice F r ∧ ψ x ≠ 1 := by
  have hntriv : ¬ AddCharTrivialOnLattice F ψ r :=
    h.not_trivialOnLattice_iff.2 hr
  by_contra hnone
  apply hntriv
  intro x hx
  by_contra hψx
  exact hnone ⟨x, hx, hψx⟩

/-- A character with exact additive conductor is nontrivial, as required in
the manuscript's definition. -/
theorem character_ne_one {ψ : ContinuousAddChar F} {n : ℤ}
    (h : IsAdditiveConductor F ψ n) : ψ ≠ 1 := by
  intro hψ
  apply h.not_trivialOnPredecessor
  intro x _hx
  rw [hψ]
  exact ContinuousAddChar.one_apply x

/-- The additive conductor exponent of a fixed character is unique. -/
theorem unique {ψ : ContinuousAddChar F} {n n' : ℤ}
    (h : IsAdditiveConductor F ψ n)
    (h' : IsAdditiveConductor F ψ n') : n = n' := by
  have hle : -n ≤ -n' := h.minimal (-n') h'.trivial
  have hle' : -n' ≤ -n := h'.minimal (-n) h.trivial
  omega

/-- It is enough to prove triviality at `-n` and nontriviality at the one-step
larger lattice in order to obtain the full largest-lattice condition. -/
theorem of_boundary {ψ : ContinuousAddChar F} {n : ℤ}
    (htriv : AddCharTrivialOnLattice F ψ (-n))
    (hprev : ¬ AddCharTrivialOnLattice F ψ (-n - 1)) :
    IsAdditiveConductor F ψ n := by
  refine ⟨htriv, ?_⟩
  intro r hr
  by_contra hnr
  have hrs : r ≤ -n - 1 := by omega
  exact hprev (addCharTrivialOnLattice_mono F hrs hr)

/-- The largest-lattice definition is equivalent to the two adjacent
boundary conditions. -/
theorem iff_boundary {ψ : ContinuousAddChar F} {n : ℤ} :
    IsAdditiveConductor F ψ n ↔
      AddCharTrivialOnLattice F ψ (-n) ∧
        ¬ AddCharTrivialOnLattice F ψ (-n - 1) := by
  constructor
  · intro h
    exact ⟨h.trivial, h.not_trivialOnPredecessor⟩
  · rintro ⟨htriv, hprev⟩
    exact of_boundary htriv hprev

/-- Inversion preserves the exact additive conductor. -/
theorem inv {ψ : ContinuousAddChar F} {n : ℤ}
    (h : IsAdditiveConductor F ψ n) :
    IsAdditiveConductor F ψ⁻¹ n := by
  refine ⟨(addCharTrivialOnLattice_inv_iff F ψ (-n)).2 h.trivial, ?_⟩
  intro r hr
  exact h.minimal r ((addCharTrivialOnLattice_inv_iff F ψ r).1 hr)

end IsAdditiveConductor

namespace IsMultiplicativeConductor

variable {F}

/-- Exact multiplicative conductor data characterize triviality on every unit
layer. -/
theorem trivialOnUnitFiltration_iff {χ : ContinuousQuasiChar F} {m r : ℕ}
    (h : IsMultiplicativeConductor F χ m) :
    QuasiCharTrivialOnUnitFiltration F χ r ↔ m ≤ r := by
  constructor
  · exact h.minimal r
  · intro hmr
    exact quasiCharTrivialOnUnitFiltration_mono F hmr h.trivial

/-- A quasi-character is nontrivial on an entire unit layer exactly below its
conductor depth. -/
theorem not_trivialOnUnitFiltration_iff {χ : ContinuousQuasiChar F} {m r : ℕ}
    (h : IsMultiplicativeConductor F χ m) :
    ¬ QuasiCharTrivialOnUnitFiltration F χ r ↔ r < m := by
  rw [h.trivialOnUnitFiltration_iff]
  omega

/-- A positive exact conductor is nontrivial on the layer immediately before
the triviality layer. -/
theorem not_trivialOnPredecessor {χ : ContinuousQuasiChar F} {m : ℕ}
    (h : IsMultiplicativeConductor F χ (m + 1)) :
    ¬ QuasiCharTrivialOnUnitFiltration F χ m := by
  rw [h.not_trivialOnUnitFiltration_iff]
  omega

/-- At positive conductor, the preceding unit layer contains an explicit
element on which the quasi-character is nontrivial.  It cannot belong to the
next layer, where the character is trivial. -/
theorem exists_ne_one_on_predecessor {χ : ContinuousQuasiChar F} {m : ℕ}
    (h : IsMultiplicativeConductor F χ (m + 1)) :
    ∃ u : Fˣ, u ∈ unitFiltration F m ∧
      u ∉ unitFiltration F (m + 1) ∧ χ u ≠ 1 := by
  have hex : ∃ u : Fˣ, u ∈ unitFiltration F m ∧ χ u ≠ 1 := by
    by_contra hnone
    apply h.not_trivialOnPredecessor
    intro u hu
    by_contra hχu
    exact hnone ⟨u, hu, hχu⟩
  obtain ⟨u, hu, hχu⟩ := hex
  refine ⟨u, hu, ?_, hχu⟩
  intro hu'
  exact hχu (h.trivial u hu')

/-- More generally, every unit layer below the conductor contains an element
on which the quasi-character is nontrivial. -/
theorem exists_ne_one_of_lt {χ : ContinuousQuasiChar F} {m r : ℕ}
    (h : IsMultiplicativeConductor F χ m) (hr : r < m) :
    ∃ u : Fˣ, u ∈ unitFiltration F r ∧ χ u ≠ 1 := by
  have hntriv : ¬ QuasiCharTrivialOnUnitFiltration F χ r :=
    h.not_trivialOnUnitFiltration_iff.2 hr
  by_contra hnone
  apply hntriv
  intro u hu
  by_contra hχu
  exact hnone ⟨u, hu, hχu⟩

/-- The multiplicative conductor exponent of a fixed quasi-character is
unique. -/
theorem unique {χ : ContinuousQuasiChar F} {m m' : ℕ}
    (h : IsMultiplicativeConductor F χ m)
    (h' : IsMultiplicativeConductor F χ m') : m = m' := by
  exact Nat.le_antisymm (h.minimal m' h'.trivial) (h'.minimal m h.trivial)

/-- Triviality on `U_F^0` gives exact multiplicative conductor zero. -/
theorem of_zero {χ : ContinuousQuasiChar F}
    (hzero : QuasiCharTrivialOnUnitFiltration F χ 0) :
    IsMultiplicativeConductor F χ 0 := by
  exact ⟨hzero, fun r _hr => Nat.zero_le r⟩

/-- At positive depth, triviality on `U_F^(m+1)` together with
nontriviality on `U_F^m` gives the full least-depth condition. -/
theorem of_succ_boundary {χ : ContinuousQuasiChar F} {m : ℕ}
    (htriv : QuasiCharTrivialOnUnitFiltration F χ (m + 1))
    (hprev : ¬ QuasiCharTrivialOnUnitFiltration F χ m) :
    IsMultiplicativeConductor F χ (m + 1) := by
  refine ⟨htriv, ?_⟩
  intro r hr
  by_contra hmr
  have hrs : r ≤ m := by omega
  exact hprev (quasiCharTrivialOnUnitFiltration_mono F hrs hr)

/-- Conductor zero is equivalent simply to triviality on `U_F^0`; there is
no predecessor condition at this endpoint. -/
theorem zero_iff {χ : ContinuousQuasiChar F} :
    IsMultiplicativeConductor F χ 0 ↔
      QuasiCharTrivialOnUnitFiltration F χ 0 := by
  constructor
  · exact fun h => h.trivial
  · exact of_zero

/-- At positive conductor, the least-layer definition is equivalent to the
two adjacent boundary conditions. -/
theorem succ_iff_boundary {χ : ContinuousQuasiChar F} {m : ℕ} :
    IsMultiplicativeConductor F χ (m + 1) ↔
      QuasiCharTrivialOnUnitFiltration F χ (m + 1) ∧
        ¬ QuasiCharTrivialOnUnitFiltration F χ m := by
  constructor
  · intro h
    exact ⟨h.trivial, h.not_trivialOnPredecessor⟩
  · rintro ⟨htriv, hprev⟩
    exact of_succ_boundary htriv hprev

/-- Inversion preserves the exact multiplicative conductor. -/
theorem inv {χ : ContinuousQuasiChar F} {m : ℕ}
    (h : IsMultiplicativeConductor F χ m) :
    IsMultiplicativeConductor F χ⁻¹ m := by
  refine ⟨(quasiCharTrivialOnUnitFiltration_inv_iff F χ m).2 h.trivial, ?_⟩
  intro r hr
  exact h.minimal r ((quasiCharTrivialOnUnitFiltration_inv_iff F χ r).1 hr)

/-- If `χ`, `ω`, and their product have exact conductors `m`, `n`, and `q`,
then `q ≤ max m n`.  Equality is not asserted when `m=n`, because the final
unit layer can cancel. -/
theorem mul_conductor_le_max {χ ω : ContinuousQuasiChar F} {m n q : ℕ}
    (hχ : IsMultiplicativeConductor F χ m)
    (hω : IsMultiplicativeConductor F ω n)
    (hprod : IsMultiplicativeConductor F (χ * ω) q) :
    q ≤ max m n := by
  apply hprod.minimal
  exact QuasiCharTrivialOnUnitFiltration.mul F
    (hχ.trivialOnUnitFiltration_iff.2 (Nat.le_max_left m n))
    (hω.trivialOnUnitFiltration_iff.2 (Nat.le_max_right m n))

/-- Multiplying quasi-characters of unequal exact conductors preserves the
larger conductor: if `m<n`, the product has conductor `n`. -/
theorem mul_of_lt {χ ω : ContinuousQuasiChar F} {m n : ℕ}
    (hχ : IsMultiplicativeConductor F χ m)
    (hω : IsMultiplicativeConductor F ω n) (hmn : m < n) :
    IsMultiplicativeConductor F (χ * ω) n := by
  cases n with
  | zero => omega
  | succ k =>
      apply of_succ_boundary
      · exact QuasiCharTrivialOnUnitFiltration.mul F
          (hχ.trivialOnUnitFiltration_iff.2 (by omega)) hω.trivial
      · intro hprod
        apply hω.not_trivialOnPredecessor
        intro u hu
        have hχu : χ u = 1 :=
          (hχ.trivialOnUnitFiltration_iff.2 (by omega)) u hu
        simpa only [ContinuousQuasiChar.mul_apply, hχu, one_mul] using hprod u hu

/-- Symmetrically, if `n<m`, the product has conductor `m`. -/
theorem mul_of_gt {χ ω : ContinuousQuasiChar F} {m n : ℕ}
    (hχ : IsMultiplicativeConductor F χ m)
    (hω : IsMultiplicativeConductor F ω n) (hnm : n < m) :
    IsMultiplicativeConductor F (χ * ω) m := by
  rw [mul_comm χ ω]
  exact hω.mul_of_lt hχ hnm

end IsMultiplicativeConductor

/-- A continuous nontrivial additive character packaged together with its
exact integer conductor.  The `isConductor` field contains both triviality
on `𝔭_F ^ (-conductor)` and the proof that this is the largest triviality
lattice. -/
structure LocalAddCharData where
  character : ContinuousAddChar F
  conductor : ℤ
  isConductor : IsAdditiveConductor F character conductor

/-- A continuous quasi-character packaged together with its exact natural
number conductor.  Conductor zero means triviality on `U_F^0`, not global
triviality of the quasi-character. -/
structure LocalQuasiCharData where
  character : ContinuousQuasiChar F
  conductor : ℕ
  isConductor : IsMultiplicativeConductor F character conductor

namespace LocalAddCharData

variable {F}

/-- Construct exact additive-conductor data from the two adjacent boundary
conditions. -/
def of_boundary (ψ : ContinuousAddChar F) (n : ℤ)
    (htriv : AddCharTrivialOnLattice F ψ (-n))
    (hprev : ¬ AddCharTrivialOnLattice F ψ (-n - 1)) :
    LocalAddCharData F :=
  ⟨ψ, n, IsAdditiveConductor.of_boundary htriv hprev⟩

/-- The packaged character is trivial at depth `r` exactly when `r` is at or
above its exact additive boundary. -/
theorem trivialOnLattice_iff (ψ : LocalAddCharData F) (r : ℤ) :
    AddCharTrivialOnLattice F ψ.character r ↔ -ψ.conductor ≤ r :=
  ψ.isConductor.trivialOnLattice_iff

/-- The packaged character is trivial on `𝔭_F ^ (-k)` exactly for conductor
indices `k ≤ conductor`. -/
theorem trivialOnNegLattice_iff (ψ : LocalAddCharData F) (k : ℤ) :
    AddCharTrivialOnLattice F ψ.character (-k) ↔ k ≤ ψ.conductor :=
  ψ.isConductor.trivialOnNegLattice_iff

/-- The exact additive boundary supplies an element of exact order
`-conductor-1` on which the character is nontrivial. -/
theorem exists_ord_eq_predecessor (ψ : LocalAddCharData F) :
    ∃ x : F, ord F x = ((-ψ.conductor - 1 : ℤ) : WithTop ℤ) ∧
      ψ.character x ≠ 1 :=
  ψ.isConductor.exists_ord_eq_predecessor

/-- Every packaged additive character satisfies the manuscript's explicit
nontriviality hypothesis. -/
theorem character_ne_one (ψ : LocalAddCharData F) : ψ.character ≠ 1 :=
  ψ.isConductor.character_ne_one

/-- Any other proposed conductor for the packaged additive character equals
the stored exact conductor. -/
theorem conductor_eq_of_isConductor (ψ : LocalAddCharData F) {n : ℤ}
    (hn : IsAdditiveConductor F ψ.character n) : n = ψ.conductor :=
  hn.unique ψ.isConductor

end LocalAddCharData

namespace LocalQuasiCharData

variable {F}

/-- Construct conductor-zero data from triviality on `U_F^0`. -/
def of_zero (χ : ContinuousQuasiChar F)
    (hzero : QuasiCharTrivialOnUnitFiltration F χ 0) :
    LocalQuasiCharData F :=
  ⟨χ, 0, IsMultiplicativeConductor.of_zero hzero⟩

/-- Construct positive exact conductor data from the two adjacent unit
layers. -/
def of_succ_boundary (χ : ContinuousQuasiChar F) (m : ℕ)
    (htriv : QuasiCharTrivialOnUnitFiltration F χ (m + 1))
    (hprev : ¬ QuasiCharTrivialOnUnitFiltration F χ m) :
    LocalQuasiCharData F :=
  ⟨χ, m + 1, IsMultiplicativeConductor.of_succ_boundary htriv hprev⟩

/-- The packaged quasi-character is trivial on `U_F^r` exactly at and above
its exact conductor. -/
theorem trivialOnUnitFiltration_iff (χ : LocalQuasiCharData F) (r : ℕ) :
    QuasiCharTrivialOnUnitFiltration F χ.character r ↔ χ.conductor ≤ r :=
  χ.isConductor.trivialOnUnitFiltration_iff

/-- The stored multiplicative conductor is zero exactly when the
quasi-character is unramified, i.e. trivial on `U_F^0`. -/
theorem conductor_eq_zero_iff (χ : LocalQuasiCharData F) :
    χ.conductor = 0 ↔ QuasiCharTrivialOnUnitFiltration F χ.character 0 := by
  constructor
  · intro hm
    simpa only [hm] using χ.isConductor.trivial
  · intro hzero
    exact Nat.eq_zero_of_le_zero (χ.isConductor.minimal 0 hzero)

/-- The manuscript's conductor-zero criterion expressed directly on the
canonical valuation-ring unit group. -/
theorem conductor_eq_zero_iff_trivialOnUnitGroup (χ : LocalQuasiCharData F) :
    χ.conductor = 0 ↔
      ∀ u : Fˣ, u ∈ unitGroup F → χ.character u = 1 := by
  rw [χ.conductor_eq_zero_iff]
  rfl

/-- If the stored conductor is `m+1`, the preceding unit shell contains a
point on which the quasi-character is nontrivial. -/
theorem exists_ne_one_on_predecessor (χ : LocalQuasiCharData F) {m : ℕ}
    (hm : χ.conductor = m + 1) :
    ∃ u : Fˣ, u ∈ unitFiltration F m ∧
      u ∉ unitFiltration F (m + 1) ∧ χ.character u ≠ 1 := by
  have hexact : IsMultiplicativeConductor F χ.character (m + 1) := by
    simpa only [hm] using χ.isConductor
  exact hexact.exists_ne_one_on_predecessor

/-- Any other proposed conductor for the packaged quasi-character equals
the stored exact conductor. -/
theorem conductor_eq_of_isConductor (χ : LocalQuasiCharData F) {m : ℕ}
    (hm : IsMultiplicativeConductor F χ.character m) : m = χ.conductor :=
  hm.unique χ.isConductor

end LocalQuasiCharData

end

end LanglandsFirstMainLemma
