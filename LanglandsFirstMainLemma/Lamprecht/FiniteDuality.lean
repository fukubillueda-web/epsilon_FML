import LanglandsFirstMainLemma.LocalField.FiniteQuotients
import LanglandsFirstMainLemma.Basic.CharacterConductors
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Finite stationary-phase duality

Let `ψ` have exact additive conductor `n`, and let `Γ` have order `M + n`.
For integral depths `r ≤ q`, this file constructs the representative-free pairing

`𝔭^(M-q) / 𝔭^(M-r) × 𝔭^r / 𝔭^q → ℂˣ`,

`(c, x) ↦ ψ (c * x / Γ)`.

Both annihilators are computed at their exact depths.  The two finite quotients have
cardinality `q_F ^ (q-r).toNat`, so the two induced maps to the full complex character
groups are additive equivalences.  The usual Lamprecht pairing is the specialization
`M = q = m` and `r = d + ε`, where `m = 2*d + ε`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The coefficient quotient in the general stationary-phase pairing. -/
abbrev LamprechtCoefficientQuotient (M q r : ℤ) (hrq : r ≤ q) :=
  LatticeQuotient F (M - q) (M - r) (sub_le_sub_left hrq M)

/-- The variable quotient in the general stationary-phase pairing. -/
abbrev LamprechtVariableQuotient (q r : ℤ) (hrq : r ≤ q) :=
  LatticeQuotient F r q hrq

private theorem addChar_eq_of_sub_mem_conductor
    (ψ : LocalAddCharData F) {a b : F}
    (hab : a - b ∈ lattice F (-ψ.conductor)) :
    ψ.character a = ψ.character b := by
  apply Units.ext
  apply (div_eq_one_iff_eq (Units.ne_zero (ψ.character b))).1
  have hdiv : ψ.character a / ψ.character b = 1 := by
    calc
      ψ.character a / ψ.character b =
          ψ.character.toAddChar (a - b) :=
        (ψ.character.toAddChar.map_sub_eq_div a b).symm
      _ = 1 := ψ.isConductor.trivial (a - b) hab
  simpa using congrArg Units.val hdiv

/-- The exact annihilator of `𝔭^r` under `c,x ↦ ψ(c*x/Γ)` is
`𝔭^(M-r)`.  The forward implication uses a predecessor witness for the exact
conductor; it does not identify the pointwise kernel of `ψ` with its conductor lattice. -/
theorem lamprechtAnnihilatorLeft
    (ψ : LocalAddCharData F) {Γ c : F} {M r : ℤ}
    (hΓ : ord F Γ = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    (∀ x : F, x ∈ lattice F r → ψ.character (c * x / Γ) = 1) ↔
      c ∈ lattice F (M - r) := by
  constructor
  · intro htriv
    by_contra hc
    have hc0 : c ≠ 0 := by
      intro hzero
      subst c
      exact hc (by simp)
    obtain ⟨k, hk⟩ :=
      WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hc0)
    have hklt : k < M - r := by
      rw [mem_lattice, ← hk] at hc
      exact WithTop.coe_lt_coe.mp (lt_of_not_ge hc)
    obtain ⟨w, hword, hwψ⟩ := ψ.exists_ord_eq_predecessor
    let x : F := Γ * w / c
    have hxord : ord F x = ((M - 1 - k : ℤ) : WithTop ℤ) := by
      rw [show x = Γ * w / c by rfl, ord_div, ord_mul, hΓ, hword, ← hk]
      exact_mod_cast (show (M + ψ.conductor) + (-ψ.conductor - 1) - k =
        M - 1 - k by omega)
    have hx : x ∈ lattice F r := by
      rw [mem_lattice, hxord, WithTop.coe_le_coe]
      omega
    have hvalue := htriv x hx
    have hΓ0 : Γ ≠ 0 := (ord_ne_top_iff F).1 (by rw [hΓ]; simp)
    have harg : c * x / Γ = w := by
      dsimp [x]
      field_simp [hΓ0]
    rw [harg] at hvalue
    exact hwψ hvalue
  · intro hc x hx
    exact ψ.isConductor.trivial _
      ((forall_mul_div_mem_lattice_iff_left F hΓ).2 hc x hx)

/-- Symmetrically, the exact annihilator of `𝔭^(M-q)` in the other variable is
`𝔭^q`.  Again exact-conductor data, rather than a pointwise-kernel assumption, supplies
the nontrivial witness. -/
theorem lamprechtAnnihilatorRight
    (ψ : LocalAddCharData F) {Γ x : F} {M q : ℤ}
    (hΓ : ord F Γ = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    (∀ c : F, c ∈ lattice F (M - q) →
      ψ.character (c * x / Γ) = 1) ↔ x ∈ lattice F q := by
  constructor
  · intro htriv
    by_contra hx
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      exact hx (by simp)
    obtain ⟨k, hk⟩ :=
      WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hx0)
    have hklt : k < q := by
      rw [mem_lattice, ← hk] at hx
      exact WithTop.coe_lt_coe.mp (lt_of_not_ge hx)
    obtain ⟨w, hword, hwψ⟩ := ψ.exists_ord_eq_predecessor
    let c : F := Γ * w / x
    have hcord : ord F c = ((M - 1 - k : ℤ) : WithTop ℤ) := by
      rw [show c = Γ * w / x by rfl, ord_div, ord_mul, hΓ, hword, ← hk]
      exact_mod_cast (show (M + ψ.conductor) + (-ψ.conductor - 1) - k =
        M - 1 - k by omega)
    have hc : c ∈ lattice F (M - q) := by
      rw [mem_lattice, hcord, WithTop.coe_le_coe]
      omega
    have hvalue := htriv c hc
    have hΓ0 : Γ ≠ 0 := (ord_ne_top_iff F).1 (by rw [hΓ]; simp)
    have harg : c * x / Γ = w := by
      dsimp [c]
      field_simp [hΓ0]
    rw [harg] at hvalue
    exact hwψ hvalue
  · intro hx c hc
    exact ψ.isConductor.trivial _
      ((forall_mul_div_mem_lattice_iff_right F hΓ).2 hx c hc)

/-- The character induced by `z ↦ ψ(z / Γ)` on the product quotient
`𝔭^(M-q+r) / 𝔭^M`.  Its descent records explicitly that changing `z` at depth `M`
changes `z / Γ` at the conductor depth `-n(ψ)`. -/
noncomputable def lamprechtProductCharacter
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    AddChar
      (LatticeQuotient F (M - q + r) M (by omega))
      ℂˣ where
  toFun := latticeQuotientLift F (by omega)
    (fun z ↦ ψ.character ((z : F) / (Γ : F)))
    (fun z z' hzz' ↦ by
      apply addChar_eq_of_sub_mem_conductor F ψ
      rw [← sub_div]
      apply (div_mem_lattice_iff F (Γ : F) ((z : F) - (z' : F))
        (M + ψ.conductor) (-ψ.conductor) hΓ).2
      simpa only [show M + ψ.conductor + -ψ.conductor = M by omega] using
        (congruentAtDepth_iff_sub_mem_lattice F M (z : F) (z' : F)).1 hzz')
  map_zero_eq_one' := by
    change latticeQuotientLift F (by omega)
      (fun z : lattice F (M - q + r) ↦
        ψ.character ((z : F) / (Γ : F))) _
      (latticeQuotientMk F (by omega) 0) = 1
    rw [latticeQuotientLift_mk]
    simp
  map_add_eq_mul' := by
    intro z z'
    obtain ⟨z, rfl⟩ := latticeQuotientMk_surjective F (by omega) z
    obtain ⟨z', rfl⟩ := latticeQuotientMk_surjective F (by omega) z'
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk]
    change ψ.character (((z : F) + (z' : F)) / (Γ : F)) = _
    rw [add_div, ContinuousAddChar.map_add_eq_mul]

@[simp]
theorem lamprechtProductCharacter_mk
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (z : lattice F (M - q + r)) :
    lamprechtProductCharacter F ψ hrq Γ hΓ
        (latticeQuotientMk F (by omega) z) =
      ψ.character ((z : F) / (Γ : F)) :=
  rfl

/-- The general finite stationary-phase pairing, bundled as an additive homomorphism
from coefficient classes to unit-valued additive characters of the variable quotient. -/
noncomputable def lamprechtPairing
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    LamprechtCoefficientQuotient F M q r hrq →+
      AddChar (LamprechtVariableQuotient F q r hrq) ℂˣ where
  toFun c := (lamprechtProductCharacter F ψ hrq Γ hΓ).compAddMonoidHom
    ((latticeQuotientMulAddHom F (sub_le_sub_left hrq M) hrq
      (by omega) (by omega) (by omega)) c)
  map_zero' := by
    apply AddChar.ext
    intro x
    simp
  map_add' := by
    intro c c'
    apply AddChar.ext
    intro x
    change (lamprechtProductCharacter F ψ hrq Γ hΓ)
      (((latticeQuotientMulAddHom F (sub_le_sub_left hrq M) hrq
        (by omega) (by omega) (by omega)) (c + c')) x) = _
    rw [map_add, AddMonoidHom.add_apply, AddChar.map_add_eq_mul]
    rfl

@[simp]
theorem lamprechtPairing_mk_mk
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (c : lattice F (M - q)) (x : lattice F r) :
    lamprechtPairing F ψ hrq Γ hΓ
        (latticeQuotientMk F (sub_le_sub_left hrq M) c)
        (latticeQuotientMk F hrq x) =
      ψ.character ((c : F) * (x : F) / (Γ : F)) :=
  rfl

/-- The same pairing, curried in the variable class. -/
noncomputable def lamprechtPairingFlip
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    LamprechtVariableQuotient F q r hrq →+
      AddChar (LamprechtCoefficientQuotient F M q r hrq) ℂˣ where
  toFun x :=
    { toFun := fun c ↦ lamprechtPairing F ψ hrq Γ hΓ c x
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro c c'
        simpa only [AddMonoidHom.add_apply, AddChar.add_apply] using
          congrArg (fun χ : AddChar (LamprechtVariableQuotient F q r hrq) ℂˣ ↦ χ x)
            (map_add (lamprechtPairing F ψ hrq Γ hΓ) c c') }
  map_zero' := by
    apply AddChar.ext
    intro c
    change lamprechtPairing F ψ hrq Γ hΓ c 0 = 1
    exact AddChar.map_zero_eq_one _
  map_add' := by
    intro x x'
    apply AddChar.ext
    intro c
    change lamprechtPairing F ψ hrq Γ hΓ c (x + x') =
      lamprechtPairing F ψ hrq Γ hΓ c x *
        lamprechtPairing F ψ hrq Γ hΓ c x'
    exact AddChar.map_add_eq_mul _ _ _

/-- Coerce a unit-valued additive character to its complex-valued character. -/
def unitAddCharToComplex (A : Type*) [AddCommGroup A] :
    AddChar A ℂˣ →+ AddChar A ℂ where
  toFun χ := (Units.coeHom ℂ).compAddChar χ
  map_zero' := by
    apply AddChar.ext
    intro x
    rfl
  map_add' := by
    intro χ χ'
    apply AddChar.ext
    intro x
    rfl

/-- The homomorphism from coefficient classes to the full complex character group of
the variable quotient induced by the stationary-phase pairing. -/
noncomputable def lamprechtPairingLeft
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    LamprechtCoefficientQuotient F M q r hrq →+
      AddChar (LamprechtVariableQuotient F q r hrq) ℂ :=
  (unitAddCharToComplex (LamprechtVariableQuotient F q r hrq)).comp
    (lamprechtPairing F ψ hrq Γ hΓ)

/-- The symmetric homomorphism from variable classes to the full complex character group
of the coefficient quotient. -/
noncomputable def lamprechtPairingRight
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    LamprechtVariableQuotient F q r hrq →+
      AddChar (LamprechtCoefficientQuotient F M q r hrq) ℂ :=
  (unitAddCharToComplex (LamprechtCoefficientQuotient F M q r hrq)).comp
    (lamprechtPairingFlip F ψ hrq Γ hΓ)

@[simp]
theorem lamprechtPairingLeft_apply
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (c : LamprechtCoefficientQuotient F M q r hrq)
    (x : LamprechtVariableQuotient F q r hrq) :
    lamprechtPairingLeft F ψ hrq Γ hΓ c x =
      (lamprechtPairing F ψ hrq Γ hΓ c x : ℂ) :=
  rfl

@[simp]
theorem lamprechtPairingRight_apply
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (x : LamprechtVariableQuotient F q r hrq)
    (c : LamprechtCoefficientQuotient F M q r hrq) :
    lamprechtPairingRight F ψ hrq Γ hΓ x c =
      (lamprechtPairing F ψ hrq Γ hΓ c x : ℂ) :=
  rfl

/-- The left induced character is trivial exactly for the zero coefficient class. -/
theorem lamprechtPairingLeft_eq_zero_iff
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (c : LamprechtCoefficientQuotient F M q r hrq) :
    lamprechtPairingLeft F ψ hrq Γ hΓ c = 0 ↔ c = 0 := by
  constructor
  · intro hc
    obtain ⟨c, rfl⟩ :=
      latticeQuotientMk_surjective F (sub_le_sub_left hrq M) c
    apply (latticeQuotientMk_eq_zero_iff F (sub_le_sub_left hrq M)).2
    apply (lamprechtAnnihilatorLeft F ψ hΓ).1
    intro x hx
    let x₀ : lattice F r := ⟨x, hx⟩
    have heval := congrArg
      (fun χ : AddChar (LamprechtVariableQuotient F q r hrq) ℂ ↦
        χ (latticeQuotientMk F hrq x₀)) hc
    rw [lamprechtPairingLeft_apply, lamprechtPairing_mk_mk] at heval
    have hcomplex :
        (ψ.character ((c : F) * x / (Γ : F)) : ℂ) = 1 := by
      simpa [x₀] using heval
    apply Units.ext
    simpa using hcomplex
  · rintro rfl
    exact map_zero _

/-- The right induced character is trivial exactly for the zero variable class. -/
theorem lamprechtPairingRight_eq_zero_iff
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (x : LamprechtVariableQuotient F q r hrq) :
    lamprechtPairingRight F ψ hrq Γ hΓ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F hrq x
    apply (latticeQuotientMk_eq_zero_iff F hrq).2
    apply (lamprechtAnnihilatorRight F ψ hΓ).1
    intro c hc
    let c₀ : lattice F (M - q) := ⟨c, hc⟩
    have heval := congrArg
      (fun χ : AddChar (LamprechtCoefficientQuotient F M q r hrq) ℂ ↦
        χ (latticeQuotientMk F (sub_le_sub_left hrq M) c₀)) hx
    rw [lamprechtPairingRight_apply, lamprechtPairing_mk_mk] at heval
    have hcomplex :
        (ψ.character (c * (x : F) / (Γ : F)) : ℂ) = 1 := by
      simpa [c₀] using heval
    apply Units.ext
    simpa using hcomplex
  · rintro rfl
    exact map_zero _

/-- Nondegeneracy in the coefficient variable, stated directly in terms of the
unit-valued pairing. -/
theorem lamprechtPairing_left_nondegenerate
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (c : LamprechtCoefficientQuotient F M q r hrq) :
    (∀ x, lamprechtPairing F ψ hrq Γ hΓ c x = 1) ↔ c = 0 := by
  rw [← lamprechtPairingLeft_eq_zero_iff F ψ hrq Γ hΓ c]
  constructor
  · intro h
    apply AddChar.ext
    intro x
    simpa only [lamprechtPairingLeft_apply, AddChar.zero_apply, Units.val_one] using
      congrArg Units.val (h x)
  · intro h x
    apply Units.ext
    have heval := congrArg
      (fun χ : AddChar (LamprechtVariableQuotient F q r hrq) ℂ ↦ χ x) h
    simpa only [lamprechtPairingLeft_apply, AddChar.zero_apply, Units.val_one] using heval

/-- Nondegeneracy in the variable class. -/
theorem lamprechtPairing_right_nondegenerate
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (x : LamprechtVariableQuotient F q r hrq) :
    (∀ c, lamprechtPairing F ψ hrq Γ hΓ c x = 1) ↔ x = 0 := by
  rw [← lamprechtPairingRight_eq_zero_iff F ψ hrq Γ hΓ x]
  constructor
  · intro h
    apply AddChar.ext
    intro c
    simpa only [lamprechtPairingRight_apply, AddChar.zero_apply, Units.val_one] using
      congrArg Units.val (h c)
  · intro h c
    apply Units.ext
    have heval := congrArg
      (fun χ : AddChar (LamprechtCoefficientQuotient F M q r hrq) ℂ ↦ χ c) h
    simpa only [lamprechtPairingRight_apply, AddChar.zero_apply, Units.val_one] using heval

/-- The coefficient-to-dual homomorphism is injective. -/
theorem lamprechtPairingLeft_injective
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    Function.Injective (lamprechtPairingLeft F ψ hrq Γ hΓ) := by
  intro a b hab
  have hz : lamprechtPairingLeft F ψ hrq Γ hΓ (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp
    ((lamprechtPairingLeft_eq_zero_iff F ψ hrq Γ hΓ (a - b)).1 hz)

/-- The variable-to-dual homomorphism is injective. -/
theorem lamprechtPairingRight_injective
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    Function.Injective (lamprechtPairingRight F ψ hrq Γ hΓ) := by
  intro x y hxy
  have hz : lamprechtPairingRight F ψ hrq Γ hΓ (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    ((lamprechtPairingRight_eq_zero_iff F ψ hrq Γ hΓ (x - y)).1 hz)

/-- The coefficient quotient has exactly `q_F^(q-r)` elements. -/
theorem lamprechtCoefficientQuotient_card
    {M q r : ℤ} (hrq : r ≤ q) :
    Nat.card (LamprechtCoefficientQuotient F M q r hrq) =
      residueCard F ^ (q - r).toNat := by
  simpa only [show (M - r) - (M - q) = q - r by omega] using
    latticeQuotient_card F (sub_le_sub_left hrq M)

/-- The variable quotient has the same exact cardinality `q_F^(q-r)`. -/
theorem lamprechtVariableQuotient_card
    {q r : ℤ} (hrq : r ≤ q) :
    Nat.card (LamprechtVariableQuotient F q r hrq) =
      residueCard F ^ (q - r).toNat := by
  exact latticeQuotient_card F hrq

/-- The induced map from coefficient classes to the full character group is bijective. -/
theorem lamprechtPairingLeft_bijective
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    Function.Bijective (lamprechtPairingLeft F ψ hrq Γ hΓ) := by
  letI := latticeQuotientFintype F (sub_le_sub_left hrq M)
  letI := latticeQuotientFintype F hrq
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨lamprechtPairingLeft_injective F ψ hrq Γ hΓ, ?_⟩
  rw [AddChar.card_eq, latticeQuotient_fintype_card,
    latticeQuotient_fintype_card]
  congr 1
  omega

/-- The symmetric induced map from variable classes to the coefficient dual is bijective. -/
theorem lamprechtPairingRight_bijective
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    Function.Bijective (lamprechtPairingRight F ψ hrq Γ hΓ) := by
  letI := latticeQuotientFintype F hrq
  letI := latticeQuotientFintype F (sub_le_sub_left hrq M)
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨lamprechtPairingRight_injective F ψ hrq Γ hΓ, ?_⟩
  rw [AddChar.card_eq, latticeQuotient_fintype_card,
    latticeQuotient_fintype_card]
  congr 1
  omega

/-- **Finite stationary-phase duality.**  For `r ≤ q` and
`ord(Γ) = M + n(ψ)`, the pairing `([c],[x]) ↦ ψ(c*x/Γ)` identifies each
of the exact finite lattice quotients with the full complex character group of the other.
The two components record perfectness in both variables. -/
theorem lamprechtPerfectPairing
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    Function.Bijective (lamprechtPairingLeft F ψ hrq Γ hΓ) ∧
      Function.Bijective (lamprechtPairingRight F ψ hrq Γ hΓ) :=
  ⟨lamprechtPairingLeft_bijective F ψ hrq Γ hΓ,
    lamprechtPairingRight_bijective F ψ hrq Γ hΓ⟩

/-- The additive equivalence from coefficient classes to the variable character group
supplied by the perfect pairing. -/
noncomputable def lamprechtPairingLeftEquiv
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    LamprechtCoefficientQuotient F M q r hrq ≃+
      AddChar (LamprechtVariableQuotient F q r hrq) ℂ :=
  AddEquiv.ofBijective (lamprechtPairingLeft F ψ hrq Γ hΓ)
    (lamprechtPerfectPairing F ψ hrq Γ hΓ).1

/-- The symmetric additive equivalence from variable classes to the coefficient dual. -/
noncomputable def lamprechtPairingRightEquiv
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ)) :
    LamprechtVariableQuotient F q r hrq ≃+
      AddChar (LamprechtCoefficientQuotient F M q r hrq) ℂ :=
  AddEquiv.ofBijective (lamprechtPairingRight F ψ hrq Γ hΓ)
    (lamprechtPerfectPairing F ψ hrq Γ hΓ).2

@[simp]
theorem lamprechtPairingLeftEquiv_apply
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (c : LamprechtCoefficientQuotient F M q r hrq) :
    lamprechtPairingLeftEquiv F ψ hrq Γ hΓ c =
      lamprechtPairingLeft F ψ hrq Γ hΓ c :=
  rfl

@[simp]
theorem lamprechtPairingRightEquiv_apply
    (ψ : LocalAddCharData F) {M q r : ℤ} (hrq : r ≤ q)
    (Γ : Fˣ)
    (hΓ : ord F (Γ : F) = ((M + ψ.conductor : ℤ) : WithTop ℤ))
    (x : LamprechtVariableQuotient F q r hrq) :
    lamprechtPairingRightEquiv F ψ hrq Γ hΓ x =
      lamprechtPairingRight F ψ hrq Γ hΓ x :=
  rfl

end

end LanglandsFirstMainLemma
