import LanglandsFirstMainLemma.Basic.Phase

/-!
# Continuous character types

This file supplies the basic character objects used throughout the project.
Both kinds of character take values in `ℂˣ`, so nonvanishing is built into
their codomain.  Additive characters are continuous `AddChar`s, while
quasi-characters are continuous homomorphisms on the unit group.

The generic pullback operations are the primary API.  Pullback along algebraic
trace and norm is also provided when the topology on a finite free algebra is
its module topology.
-/

namespace LanglandsFirstMainLemma

noncomputable section

/-- A continuous additive character with values in the nonzero complex numbers. -/
def ContinuousAddChar (A : Type*) [AddMonoid A] [TopologicalSpace A] :=
  {ψ : AddChar A ℂˣ // Continuous ψ}

/-- A continuous quasi-character on the unit group, with values in `ℂˣ`. -/
abbrev ContinuousQuasiChar (F : Type*) [Monoid F] [TopologicalSpace F] :=
  ContinuousMonoidHom Fˣ ℂˣ

private def continuousAddCharSubmonoid (A : Type*)
    [AddMonoid A] [TopologicalSpace A] : Submonoid (AddChar A ℂˣ) where
  carrier := {ψ | Continuous ψ}
  one_mem' := continuous_const
  mul_mem' hψ hφ := hψ.mul hφ

private def continuousAddCharSubgroup (A : Type*)
    [AddCommGroup A] [TopologicalSpace A] : Subgroup (AddChar A ℂˣ) where
  carrier := {ψ | Continuous ψ}
  one_mem' := continuous_const
  mul_mem' hψ hφ := hψ.mul hφ
  inv_mem' {ψ} hψ := by
    change Continuous (fun x : A => (ψ⁻¹ : AddChar A ℂˣ) x)
    simpa only [AddChar.inv_apply'] using hψ.fun_inv

/-- Continuous additive characters form a commutative monoid under pointwise
multiplication. -/
instance {A : Type*} [AddMonoid A] [TopologicalSpace A] :
    CommMonoid (ContinuousAddChar A) :=
  inferInstanceAs (CommMonoid (continuousAddCharSubmonoid A))

/-- Continuous additive characters on an additive commutative group form a
commutative group under pointwise multiplication. -/
instance {A : Type*} [AddCommGroup A] [TopologicalSpace A] :
    CommGroup (ContinuousAddChar A) :=
  inferInstanceAs (CommGroup (continuousAddCharSubgroup A))

/-- A continuous additive character evaluates as a function into `ℂˣ`. -/
instance {A : Type*} [AddMonoid A] [TopologicalSpace A] :
    FunLike (ContinuousAddChar A) A ℂˣ where
  coe ψ := ψ.1
  coe_injective ψ φ h :=
    Subtype.ext (AddChar.ext ψ.1 φ.1 fun x => congr_fun h x)

/-- Evaluation of a continuous additive character is continuous. -/
instance {A : Type*} [AddMonoid A] [TopologicalSpace A] :
    ContinuousMapClass (ContinuousAddChar A) A ℂˣ where
  map_continuous ψ := ψ.2

namespace ContinuousAddChar

/-- Continuous additive characters are equal when all their values agree. -/
@[ext]
theorem ext {A : Type*} [AddMonoid A] [TopologicalSpace A]
    {ψ φ : ContinuousAddChar A} (h : ∀ x, ψ x = φ x) : ψ = φ :=
  DFunLike.ext ψ φ h

/-- The underlying Mathlib additive character. -/
def toAddChar {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : AddChar A ℂˣ :=
  ψ.1

@[simp]
theorem toAddChar_apply {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x : A) : ψ.toAddChar x = ψ x :=
  rfl

/-- An additive character maps zero to one. -/
@[simp]
theorem map_zero_eq_one {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : ψ 0 = 1 :=
  AddChar.map_zero_eq_one ψ.toAddChar

/-- An additive character turns addition into multiplication. -/
theorem map_add_eq_mul {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x y : A) : ψ (x + y) = ψ x * ψ y :=
  AddChar.map_add_eq_mul ψ.toAddChar x y

/-- The unit-valued evaluation map of a continuous additive character is
continuous. -/
theorem continuous {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : Continuous ψ :=
  map_continuous ψ

/-- Every complex value of a continuous additive character is nonzero. -/
@[simp]
theorem apply_ne_zero {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x : A) : (ψ x : ℂ) ≠ 0 :=
  Units.ne_zero _

@[simp]
theorem one_apply {A : Type*} [AddMonoid A] [TopologicalSpace A] (x : A) :
    (1 : ContinuousAddChar A) x = 1 :=
  rfl

@[simp]
theorem mul_apply {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ φ : ContinuousAddChar A) (x : A) : (ψ * φ) x = ψ x * φ x :=
  rfl

@[simp]
theorem inv_apply {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x : A) : ψ⁻¹ x = (ψ x)⁻¹ :=
  AddChar.inv_apply' ψ.toAddChar x

@[simp]
theorem pow_apply {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (n : ℕ) (x : A) : (ψ ^ n) x = (ψ x) ^ n :=
  rfl

/-- The explicit complex-valued additive character underlying `ψ`. -/
def toComplexAddChar {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : AddChar A ℂ :=
  (Units.coeHom ℂ).compAddChar ψ.toAddChar

@[simp]
theorem toComplexAddChar_apply {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x : A) : ψ.toComplexAddChar x = (ψ x : ℂ) :=
  rfl

/-- Complex-valued evaluation of a continuous additive character is
continuous. -/
theorem continuous_coe {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : Continuous (fun x => (ψ x : ℂ)) :=
  Units.continuous_val.comp (map_continuous ψ)

/-- Pull a continuous additive character back along a continuous additive
homomorphism. -/
def pullback {A B : Type*} [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B]
    (ψ : ContinuousAddChar B) (f : ContinuousAddMonoidHom A B) :
    ContinuousAddChar A :=
  ⟨ψ.toAddChar.compAddMonoidHom f.toAddMonoidHom,
    ψ.continuous.comp (map_continuous f)⟩

@[simp]
theorem pullback_apply {A B : Type*} [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B]
    (ψ : ContinuousAddChar B) (f : ContinuousAddMonoidHom A B) (x : A) :
    ψ.pullback f x = ψ (f x) :=
  rfl

@[simp]
theorem one_pullback {A B : Type*} [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] (f : ContinuousAddMonoidHom A B) :
    (1 : ContinuousAddChar B).pullback f = 1 := by
  ext x
  rfl

@[simp]
theorem mul_pullback {A B : Type*} [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B]
    (ψ φ : ContinuousAddChar B) (f : ContinuousAddMonoidHom A B) :
    (ψ * φ).pullback f = ψ.pullback f * φ.pullback f := by
  ext x
  rfl

@[simp]
theorem inv_pullback {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B]
    (ψ : ContinuousAddChar B) (f : ContinuousAddMonoidHom A B) :
    ψ⁻¹.pullback f = (ψ.pullback f)⁻¹ := by
  ext x
  simp

@[simp]
theorem pow_pullback {A B : Type*} [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B]
    (ψ : ContinuousAddChar B) (f : ContinuousAddMonoidHom A B) (n : ℕ) :
    (ψ ^ n).pullback f = ψ.pullback f ^ n := by
  ext x
  rfl

end ContinuousAddChar

namespace ContinuousQuasiChar

@[simp]
theorem one_apply {F : Type*} [Monoid F] [TopologicalSpace F] (x : Fˣ) :
    (1 : ContinuousQuasiChar F) x = 1 :=
  rfl

@[simp]
theorem mul_apply {F : Type*} [Monoid F] [TopologicalSpace F]
    (χ ω : ContinuousQuasiChar F) (x : Fˣ) : (χ * ω) x = χ x * ω x :=
  ContinuousMonoidHom.mul_apply χ ω x

@[simp]
theorem inv_apply {F : Type*} [Monoid F] [TopologicalSpace F]
    (χ : ContinuousQuasiChar F) (x : Fˣ) : χ⁻¹ x = (χ x)⁻¹ :=
  rfl

@[simp]
theorem pow_apply {F : Type*} [Monoid F] [TopologicalSpace F]
    (χ : ContinuousQuasiChar F) (n : ℕ) (x : Fˣ) : (χ ^ n) x = (χ x) ^ n :=
  ContinuousMonoidHom.pow_apply χ n x

/-- Every complex value of a continuous quasi-character is nonzero. -/
@[simp]
theorem apply_ne_zero {F : Type*} [Monoid F] [TopologicalSpace F]
    (χ : ContinuousQuasiChar F) (x : Fˣ) : (χ x : ℂ) ≠ 0 :=
  Units.ne_zero _

/-- Complex-valued evaluation of a continuous quasi-character is continuous. -/
theorem continuous_coe {F : Type*} [Monoid F] [TopologicalSpace F]
    (χ : ContinuousQuasiChar F) : Continuous (fun x => (χ x : ℂ)) :=
  Units.continuous_val.comp (map_continuous χ)

/-- Pull a quasi-character back along a continuous homomorphism of unit groups. -/
def pullback {F K : Type*} [Monoid F] [Monoid K]
    [TopologicalSpace F] [TopologicalSpace K]
    (χ : ContinuousQuasiChar F) (f : ContinuousMonoidHom Kˣ Fˣ) :
    ContinuousQuasiChar K :=
  χ.comp f

@[simp]
theorem pullback_apply {F K : Type*} [Monoid F] [Monoid K]
    [TopologicalSpace F] [TopologicalSpace K]
    (χ : ContinuousQuasiChar F) (f : ContinuousMonoidHom Kˣ Fˣ) (x : Kˣ) :
    χ.pullback f x = χ (f x) :=
  rfl

@[simp]
theorem one_pullback {F K : Type*} [Monoid F] [Monoid K]
    [TopologicalSpace F] [TopologicalSpace K] (f : ContinuousMonoidHom Kˣ Fˣ) :
    (1 : ContinuousQuasiChar F).pullback f = 1 := by
  ext x
  rfl

@[simp]
theorem mul_pullback {F K : Type*} [Monoid F] [Monoid K]
    [TopologicalSpace F] [TopologicalSpace K]
    (χ ω : ContinuousQuasiChar F) (f : ContinuousMonoidHom Kˣ Fˣ) :
    (χ * ω).pullback f = χ.pullback f * ω.pullback f := by
  ext x
  rfl

@[simp]
theorem inv_pullback {F K : Type*} [Monoid F] [Monoid K]
    [TopologicalSpace F] [TopologicalSpace K]
    (χ : ContinuousQuasiChar F) (f : ContinuousMonoidHom Kˣ Fˣ) :
    χ⁻¹.pullback f = (χ.pullback f)⁻¹ := by
  ext x
  rfl

@[simp]
theorem pow_pullback {F K : Type*} [Monoid F] [Monoid K]
    [TopologicalSpace F] [TopologicalSpace K]
    (χ : ContinuousQuasiChar F) (f : ContinuousMonoidHom Kˣ Fˣ) (n : ℕ) :
    (χ ^ n).pullback f = χ.pullback f ^ n := by
  ext x
  simp only [pullback_apply, ContinuousMonoidHom.pow_apply]

end ContinuousQuasiChar

private def continuousTrace (R S : Type*)
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S] :
    ContinuousAddMonoidHom S R :=
  ⟨(Algebra.trace R S).toAddMonoidHom,
    IsModuleTopology.continuous_of_linearMap (Algebra.trace R S)⟩

private theorem continuousAlgebraNorm (R S : Type*)
    [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S] :
    Continuous (Algebra.norm R : S → R) := by
  let b := Module.Free.chooseBasis R S
  rw [show (Algebra.norm R : S → R) =
      fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.leftMulMatrix b).toLinearMap).matrix_det

private def continuousNormUnits (R S : Type*)
    [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S] :
    ContinuousMonoidHom Sˣ Rˣ :=
  ⟨Units.map (Algebra.norm R),
    (continuousAlgebraNorm R S).units_map (Algebra.norm R)⟩

namespace ContinuousAddChar

/-- Pull an additive character back along the trace of a finite free algebra. -/
noncomputable def compTrace {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S]
    (ψ : ContinuousAddChar R) : ContinuousAddChar S :=
  ψ.pullback (continuousTrace R S)

@[simp]
theorem compTrace_apply {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S]
    (ψ : ContinuousAddChar R) (x : S) :
    ψ.compTrace x = ψ (Algebra.trace R S x) :=
  rfl

end ContinuousAddChar

namespace ContinuousQuasiChar

/-- Pull a quasi-character back along the norm of a finite free algebra. -/
noncomputable def compNorm {R S : Type*}
    [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S]
    (χ : ContinuousQuasiChar R) : ContinuousQuasiChar S :=
  χ.pullback (continuousNormUnits R S)

@[simp]
theorem compNorm_apply {R S : Type*}
    [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S]
    (χ : ContinuousQuasiChar R) (x : Sˣ) :
    χ.compNorm x = χ (Units.map (Algebra.norm R) x) :=
  rfl

end ContinuousQuasiChar

end

end LanglandsFirstMainLemma
