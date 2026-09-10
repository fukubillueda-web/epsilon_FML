import LanglandsFirstMainLemma.Lamprecht.StationaryClassCalculus
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.Delta.ResidueFormula

/-!
# Characteristic-independent critical polar coordinates

For an odd conductor `m(chi) = 2*d+1`, the stationary numerator remains a
class in the Lamprecht coefficient quotient.  Pairing that class with
`delta^2` times a residue variable gives the intrinsic residual polar
character.  Relative to a supplied nontrivial residual additive character
`psi0`, `criticalPolarCoefficient` is its unique coefficient in the residue
field.  No field-valued stationary representative is selected.

The public API records arbitrary-lift evaluation, the exact quotient-to-residue
description, coordinate and Frobenius transport, and the affine translation
caused by changing a supplied stationary representative.  The positive polar
sign and the `a / 2` convention agree with `quadraticPhase`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

/-! ## Coefficients of finite additive characters -/

section FiniteAdditiveCoordinates

variable {k : Type*} [Field k] [Fintype k]

/-- Multiplicative shifts of a nontrivial additive character give every
additive character of a finite field exactly once. -/
private noncomputable def finiteAddCharMulShiftEquiv
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1) :
    k ≃ FiniteAddChar k :=
  Equiv.ofBijective psi0.mulShift <| by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hpsi0), rfl⟩

/-- The unique residue coefficient `a` for which `phi(z) = psi0(a*z)`.
This definition is only a coordinate on a finite additive character; it does
not choose a local stationary representative. -/
noncomputable def finiteAddCharCoefficient
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) : k :=
  (finiteAddCharMulShiftEquiv psi0 hpsi0).symm phi

@[simp]
theorem finiteAddCharCoefficient_spec
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) :
    psi0.mulShift (finiteAddCharCoefficient psi0 hpsi0 phi) = phi :=
  (finiteAddCharMulShiftEquiv psi0 hpsi0).apply_symm_apply phi

theorem finiteAddCharCoefficient_apply
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) (z : k) :
    psi0 (finiteAddCharCoefficient psi0 hpsi0 phi * z) = phi z := by
  exact DFunLike.congr_fun (finiteAddCharCoefficient_spec psi0 hpsi0 phi) z

theorem finiteAddCharCoefficient_unique
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) {a : k}
    (ha : psi0.mulShift a = phi) :
    finiteAddCharCoefficient psi0 hpsi0 phi = a := by
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (AddChar.IsPrimitive.of_ne_one hpsi0)
  rw [finiteAddCharCoefficient_spec]
  exact ha.symm

theorem finiteAddCharCoefficient_ne_zero
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) (hphi : phi ≠ 1) :
    finiteAddCharCoefficient psi0 hpsi0 phi ≠ 0 := by
  intro hzero
  apply hphi
  rw [← finiteAddCharCoefficient_spec psi0 hpsi0 phi, hzero,
    AddChar.mulShift_zero]

/-- Scalar transport has weight one at the level of a residual additive
character. -/
theorem finiteAddCharCoefficient_mulShift
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (phi : FiniteAddChar k) (a : k) :
    finiteAddCharCoefficient psi0 hpsi0 (phi.mulShift a) =
      finiteAddCharCoefficient psi0 hpsi0 phi * a := by
  apply finiteAddCharCoefficient_unique psi0 hpsi0
  rw [← AddChar.mulShift_mulShift, finiteAddCharCoefficient_spec]

/-- Precomposition of an additive character by a residual automorphism. -/
noncomputable def finiteAddCharPrecompose
    (phi : FiniteAddChar k) (sigma : k ≃+* k) : FiniteAddChar k :=
  phi.compAddMonoidHom sigma.toAddEquiv.toAddMonoidHom

omit [Fintype k] in
@[simp]
theorem finiteAddCharPrecompose_apply
    (phi : FiniteAddChar k) (sigma : k ≃+* k) (x : k) :
    finiteAddCharPrecompose phi sigma x = phi (sigma x) :=
  rfl

/-- For a `sigma`-invariant residual character, precomposition by `sigma`
applies `sigma⁻¹` to the coefficient.  This is the Frobenius direction in
the manuscript. -/
theorem finiteAddCharCoefficient_precompose
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (sigma : k ≃+* k) (hsigma : ∀ x, psi0 (sigma x) = psi0 x)
    (phi : FiniteAddChar k) :
    finiteAddCharCoefficient psi0 hpsi0
        (finiteAddCharPrecompose phi sigma) =
      sigma.symm (finiteAddCharCoefficient psi0 hpsi0 phi) := by
  apply finiteAddCharCoefficient_unique psi0 hpsi0
  apply AddChar.ext
  intro x
  rw [AddChar.mulShift_apply, finiteAddCharPrecompose_apply]
  rw [← finiteAddCharCoefficient_apply psi0 hpsi0 phi (sigma x)]
  rw [← hsigma (sigma.symm (finiteAddCharCoefficient psi0 hpsi0 phi) * x)]
  congr 1
  simp

/-- Precomposition by inverse Frobenius applies Frobenius to the coefficient. -/
theorem finiteAddCharCoefficient_precompose_symm
    (psi0 : FiniteAddChar k) (hpsi0 : psi0 ≠ 1)
    (sigma : k ≃+* k) (hsigma : ∀ x, psi0 (sigma x) = psi0 x)
    (phi : FiniteAddChar k) :
    finiteAddCharCoefficient psi0 hpsi0
        (finiteAddCharPrecompose phi sigma.symm) =
      sigma (finiteAddCharCoefficient psi0 hpsi0 phi) := by
  have hsigmaSymm : ∀ x, psi0 (sigma.symm x) = psi0 x := by
    intro x
    rw [← hsigma (sigma.symm x)]
    simp
  simpa using finiteAddCharCoefficient_precompose psi0 hpsi0 sigma.symm
    hsigmaSymm phi

end FiniteAdditiveCoordinates

/-! ## Positive-polar functions and their odd-characteristic coordinates -/

universe u

/-- A nowhere-zero function whose polar quotient is exactly
`psi0 (A * (x * y))`.  The coefficient `A` is part of the type, so the
positive-polar sign cannot be lost when the function is transported. -/
structure CriticalPolarFunction (k : Type u) [Field k]
    (psi0 : FiniteAddChar k) (A : k) where
  /-- The complete critical function. -/
  toFun : k → ℂ
  /-- Critical-function values are nonzero. -/
  ne_zero' : ∀ x, toFun x ≠ 0
  /-- The manuscript's positive-polar identity. -/
  map_add' : ∀ x y,
    toFun (x + y) = toFun x * toFun y * psi0 (A * (x * y))

namespace CriticalPolarFunction

variable {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A : k}

instance : FunLike (CriticalPolarFunction k psi0 A) k ℂ where
  coe := CriticalPolarFunction.toFun
  coe_injective phi phi' h := by
    cases phi
    cases phi'
    simp_all

@[ext]
theorem ext (phi phi' : CriticalPolarFunction k psi0 A)
    (h : ∀ x, phi x = phi' x) : phi = phi' :=
  DFunLike.ext phi phi' h

theorem ne_zero (phi : CriticalPolarFunction k psi0 A) (x : k) :
    phi x ≠ 0 :=
  phi.ne_zero' x

theorem map_add (phi : CriticalPolarFunction k psi0 A) (x y : k) :
    phi (x + y) = phi x * phi y * psi0 (A * (x * y)) :=
  phi.map_add' x y

@[simp]
theorem map_zero (phi : CriticalPolarFunction k psi0 A) : phi 0 = 1 := by
  have h := phi.map_add 0 0
  simp only [zero_add, mul_zero, AddChar.map_zero_eq_one, mul_one] at h
  apply mul_left_cancel₀ (phi.ne_zero 0)
  simpa only [mul_one] using h.symm

/-- Multiplication by the affine character with coefficient `C` leaves the
polar coefficient unchanged. -/
noncomputable def translate (phi : CriticalPolarFunction k psi0 A) (C : k) :
    CriticalPolarFunction k psi0 A where
  toFun x := phi x * psi0 (C * x)
  ne_zero' x := mul_ne_zero (phi.ne_zero x) (AddChar.val_isUnit psi0 _).ne_zero
  map_add' x y := by
    rw [phi.map_add, mul_add, psi0.map_add_eq_mul]
    ring

@[simp]
theorem translate_apply (phi : CriticalPolarFunction k psi0 A) (C x : k) :
    phi.translate C x = phi x * psi0 (C * x) :=
  rfl

/-- Precomposing the residual coordinate by the scalar `lambda` sends the
polar coefficient to `lambda^2 * A`. -/
noncomputable def scale (phi : CriticalPolarFunction k psi0 A) (lambda : k) :
    CriticalPolarFunction k psi0 (lambda ^ 2 * A) where
  toFun x := phi (lambda * x)
  ne_zero' x := phi.ne_zero _
  map_add' x y := by
    rw [mul_add, phi.map_add]
    congr 1
    congr 1
    ring

@[simp]
theorem scale_apply (phi : CriticalPolarFunction k psi0 A) (lambda x : k) :
    phi.scale lambda x = phi (lambda * x) :=
  rfl

/-- Precomposition by a residual automorphism.  If `psi0` is invariant, the
new polar coefficient is `sigma⁻¹(A)`, the Frobenius direction of the
manuscript. -/
noncomputable def precompose (phi : CriticalPolarFunction k psi0 A)
    (sigma : k ≃+* k) (hsigma : ∀ x, psi0 (sigma x) = psi0 x) :
    CriticalPolarFunction k psi0 (sigma.symm A) where
  toFun x := phi (sigma x)
  ne_zero' x := phi.ne_zero _
  map_add' x y := by
    rw [sigma.map_add, phi.map_add]
    congr 1
    rw [← hsigma (sigma.symm A * (x * y))]
    congr 1
    simp

@[simp]
theorem precompose_apply (phi : CriticalPolarFunction k psi0 A)
    (sigma : k ≃+* k) (hsigma : ∀ x, psi0 (sigma x) = psi0 x) (x : k) :
    phi.precompose sigma hsigma x = phi (sigma x) :=
  rfl

/-- In odd characteristic, division by the standard quadratic refinement
leaves an additive character. -/
noncomputable def affineAddChar
    (hchar : ringChar k ≠ 2) (phi : CriticalPolarFunction k psi0 A) :
    FiniteAddChar k where
  toFun x := phi x * psi0 (-(A / 2 * x ^ 2))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    have hcorrection :
        psi0 (A * (x * y)) * psi0 (-(A / 2 * (x + y) ^ 2)) =
          psi0 (-(A / 2 * x ^ 2)) * psi0 (-(A / 2 * y ^ 2)) := by
      rw [← psi0.map_add_eq_mul, ← psi0.map_add_eq_mul]
      congr 1
      field_simp [Ring.two_ne_zero hchar]
      ring
    rw [phi.map_add]
    calc
      phi x * phi y * psi0 (A * (x * y)) *
            psi0 (-(A / 2 * (x + y) ^ 2)) =
          phi x * phi y *
            (psi0 (A * (x * y)) *
              psi0 (-(A / 2 * (x + y) ^ 2))) := by ring
      _ = phi x * phi y *
          (psi0 (-(A / 2 * x ^ 2)) *
            psi0 (-(A / 2 * y ^ 2))) := by rw [hcorrection]
      _ = (phi x * psi0 (-(A / 2 * x ^ 2))) *
          (phi y * psi0 (-(A / 2 * y ^ 2))) := by ring

@[simp]
theorem affineAddChar_apply
    (hchar : ringChar k ≠ 2) (phi : CriticalPolarFunction k psi0 A) (x : k) :
    phi.affineAddChar hchar x = phi x * psi0 (-(A / 2 * x ^ 2)) :=
  rfl

/-- The unique affine coefficient `B` of an odd-characteristic positive-polar
function. -/
noncomputable def affineCoefficient [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) : k :=
  finiteAddCharCoefficient psi0 hpsi0 (phi.affineAddChar hchar)

@[simp]
theorem affineCoefficient_spec [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) :
    psi0.mulShift (phi.affineCoefficient hchar hpsi0) =
      phi.affineAddChar hchar :=
  finiteAddCharCoefficient_spec psi0 hpsi0 _

/-- Exact odd-characteristic polynomial form, in the manuscript's
`A / 2` convention and with the positive polar coefficient `A`. -/
theorem eq_quadratic [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) (x : k) :
    phi x = psi0
      (A / 2 * x ^ 2 + phi.affineCoefficient hchar hpsi0 * x) := by
  have hB := finiteAddCharCoefficient_apply psi0 hpsi0
    (phi.affineAddChar hchar) x
  change psi0 (phi.affineCoefficient hchar hpsi0 * x) =
    phi x * psi0 (-(A / 2 * x ^ 2)) at hB
  rw [psi0.map_add_eq_mul]
  rw [hB]
  calc
    phi x = phi x * 1 := by simp
    _ = phi x *
        (psi0 (A / 2 * x ^ 2) * psi0 (-(A / 2 * x ^ 2))) := by
      rw [← psi0.map_add_eq_mul]
      simp
    _ = psi0 (A / 2 * x ^ 2) *
        (phi x * psi0 (-(A / 2 * x ^ 2))) := by ring

/-- Uniqueness of the affine coefficient without replacing an equality of
residue classes by an equality of local-field representatives. -/
theorem affineCoefficient_unique [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) {B : k}
    (hB : ∀ x, phi x = psi0 (A / 2 * x ^ 2 + B * x)) :
    phi.affineCoefficient hchar hpsi0 = B := by
  apply finiteAddCharCoefficient_unique psi0 hpsi0
  apply AddChar.ext
  intro x
  rw [AddChar.mulShift_apply, affineAddChar_apply, hB,
    psi0.map_add_eq_mul]
  calc
    psi0 (B * x) = psi0 (B * x) * 1 := by simp
    _ = psi0 (B * x) *
        (psi0 (A / 2 * x ^ 2) * psi0 (-(A / 2 * x ^ 2))) := by
      rw [← psi0.map_add_eq_mul]
      simp
    _ = (psi0 (A / 2 * x ^ 2) * psi0 (B * x)) *
        psi0 (-(A / 2 * x ^ 2)) := by ring

/-- Stationary-representative translation changes `B` by exactly `+C`. -/
theorem affineCoefficient_translate [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) (C : k) :
    (phi.translate C).affineCoefficient hchar hpsi0 =
      phi.affineCoefficient hchar hpsi0 + C := by
  apply affineCoefficient_unique hchar hpsi0
  intro x
  rw [translate_apply, phi.eq_quadratic hchar hpsi0]
  rw [← psi0.map_add_eq_mul]
  congr 1
  ring

/-- Scalar precomposition transports the full odd coefficient pair as
`(A,B) ↦ (lambda^2*A, lambda*B)`. -/
theorem affineCoefficient_scale [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) (lambda : k) :
    (phi.scale lambda).affineCoefficient hchar hpsi0 =
      lambda * phi.affineCoefficient hchar hpsi0 := by
  apply affineCoefficient_unique hchar hpsi0
  intro x
  rw [scale_apply, phi.eq_quadratic hchar hpsi0]
  congr 1
  ring

/-- Frobenius precomposition transports the affine coefficient in the same
inverse direction as the polar coefficient. -/
theorem affineCoefficient_precompose [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A)
    (sigma : k ≃+* k) (hsigma : ∀ x, psi0 (sigma x) = psi0 x) :
    (phi.precompose sigma hsigma).affineCoefficient hchar hpsi0 =
      sigma.symm (phi.affineCoefficient hchar hpsi0) := by
  apply affineCoefficient_unique hchar hpsi0
  intro x
  rw [precompose_apply, phi.eq_quadratic hchar hpsi0]
  rw [← hsigma
    (sigma.symm A / 2 * x ^ 2 +
      sigma.symm (phi.affineCoefficient hchar hpsi0) * x)]
  apply congrArg psi0
  rw [sigma.map_add, sigma.map_mul, map_div₀ sigma, sigma.map_pow,
    sigma.map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hsigmaTwo : sigma (2 : k) = 2 := by
    simpa using map_ofNat sigma 2
  rw [hsigmaTwo]

/-- Inverse-Frobenius precomposition sends both coefficients in the forward
`sigma` direction. -/
theorem affineCoefficient_precompose_symm [Fintype k]
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A)
    (sigma : k ≃+* k) (hsigma : ∀ x, psi0 (sigma x) = psi0 x) :
    (phi.precompose sigma.symm (fun x ↦ by
      rw [← hsigma (sigma.symm x)]
      simp)).affineCoefficient hchar hpsi0 =
      sigma (phi.affineCoefficient hchar hpsi0) := by
  simpa using affineCoefficient_precompose hchar hpsi0 phi sigma.symm
    (fun x ↦ by
      rw [← hsigma (sigma.symm x)]
      simp)

section FiniteSums

variable [Fintype k]

/-- The raw sum of an odd critical function is exactly the certified
quadratic sum with its extracted pair `(A,B)`. -/
theorem sum_eq_quadraticSum
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) :
    (∑ x : k, phi x) =
      quadraticSum psi0 A (phi.affineCoefficient hchar hpsi0) := by
  rw [quadraticSum]
  apply Finset.sum_congr rfl
  intro x _
  exact phi.eq_quadratic hchar hpsi0 x

/-- The normalized phase is exactly the certified `quadraticPhase`; no
quadratic translation or residual phase is discarded. -/
theorem phase_sum_eq_quadraticPhase
    (hchar : ringChar k ≠ 2) (hpsi0 : psi0 ≠ 1)
    (phi : CriticalPolarFunction k psi0 A) :
    phase (∑ x : k, phi x) =
      quadraticPhase psi0 A (phi.affineCoefficient hchar hpsi0) := by
  rw [quadraticPhase, phi.sum_eq_quadraticSum hchar hpsi0]

end FiniteSums

end CriticalPolarFunction

/-! ## The quotient-derived polar character -/

section LocalPolarCharacter

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance criticalResidueFintype : Fintype (ResidueField F) :=
  residueFieldFintype F

/-- The minimal stationary depth for an odd conductor `2*d+1`. -/
theorem criticalPolar_stationaryDepth
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) :
    IsLamprechtStationaryDepth chi.conductor (d + 1) :=
  ⟨hlarge, by omega, by omega⟩

/-- Multiplication by `delta^2` sends a residue class to the critical
Lamprecht variable quotient.  The construction descends every integral lift. -/
noncomputable def criticalPolarVariable
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    ResidueField F →+
      LamprechtVariableQuotient F (chi.conductor : ℤ) ((d + 1 : ℕ) : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor where
  toFun x := latticeQuotientMk F
      (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
      ⟨(delta : F) ^ 2 * (teichmuller F x : F), by
        have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
          rw [mem_lattice, hdelta]
        have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
          simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
        have htx : (teichmuller F x : F) ∈ lattice F 0 :=
          (mem_lattice_zero_iff F).2 (teichmuller F x).property
        have hp : (delta : F) ^ 2 * (teichmuller F x : F) ∈
            lattice F ((d : ℤ) + d) := by
          simpa using mul_mem_lattice F hdeltaSq htx
        have hdepth : ((d + 1 : ℕ) : ℤ) ≤ (d : ℤ) + d := by
          have := (criticalPolar_stationaryDepth F chi d hm hlarge).pos
          omega
        exact lattice_antitone F hdepth hp⟩
  map_zero' := by
    rw [map_zero]
    apply (latticeQuotientMk_eq_zero_iff F _).2
    simp
  map_add' x y := by
    apply (latticeQuotientMk_eq_mk_iff F
      (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor).2
    change (delta : F) ^ 2 * (teichmuller F (x + y) : F) -
        ((delta : F) ^ 2 * (teichmuller F x : F) +
          (delta : F) ^ 2 * (teichmuller F y : F)) ∈
      lattice F (chi.conductor : ℤ)
    have hdiff : (teichmuller F (x + y) : F) -
        ((teichmuller F x : F) + (teichmuller F y : F)) ∈ lattice F 1 := by
      apply (residueMap_eq_residueMap_iff F
        (teichmuller F (x + y)) (teichmuller F x + teichmuller F y)).1
      simp
    have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
      rw [mem_lattice, hdelta]
    have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
      simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
    have hp := mul_mem_lattice F hdeltaSq hdiff
    rw [show (delta : F) ^ 2 * (teichmuller F (x + y) : F) -
        ((delta : F) ^ 2 * (teichmuller F x : F) +
          (delta : F) ^ 2 * (teichmuller F y : F)) =
        (delta : F) ^ 2 * ((teichmuller F (x + y) : F) -
          ((teichmuller F x : F) + (teichmuller F y : F))) by ring]
    have hcast : (chi.conductor : ℤ) = (d : ℤ) + d + 1 := by omega
    simpa only [hcast] using hp

@[simp]
theorem criticalPolarVariable_integral_lift
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (z : F) (hz : z ∈ lattice F 0) :
    criticalPolarVariable F chi d hm hlarge delta hdelta (reduce F z hz) =
      latticeQuotientMk F
        (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
        ⟨(delta : F) ^ 2 * z, by
          have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
            rw [mem_lattice, hdelta]
          have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
            simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
          have hp : (delta : F) ^ 2 * z ∈ lattice F ((d : ℤ) + d) := by
            simpa using mul_mem_lattice F hdeltaSq hz
          have hdepth : ((d + 1 : ℕ) : ℤ) ≤ (d : ℤ) + d := by
            have := (criticalPolar_stationaryDepth F chi d hm hlarge).pos
            omega
          exact lattice_antitone F hdepth hp⟩ := by
  apply (latticeQuotientMk_eq_mk_iff F
    (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor).2
  change (delta : F) ^ 2 * (teichmuller F (reduce F z hz) : F) -
      (delta : F) ^ 2 * z ∈ lattice F (chi.conductor : ℤ)
  have hdiff : (teichmuller F (reduce F z hz) : F) - z ∈ lattice F 1 := by
    let zint : ringOfIntegers F := ⟨z, (mem_lattice_zero_iff F).1 hz⟩
    apply (residueMap_eq_residueMap_iff F
      (teichmuller F (reduce F z hz)) zint).1
    simp [reduce, zint]
  have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
    simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
  have hp := mul_mem_lattice F hdeltaSq hdiff
  rw [← mul_sub]
  have hcast : (chi.conductor : ℤ) = (d : ℤ) + d + 1 := by omega
  simpa only [hcast] using hp

/-- The intrinsic polar additive character obtained from the stationary
quotient class.  It has no representative argument. -/
noncomputable def criticalPolarAddChar
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    FiniteAddChar (ResidueField F) :=
  let hr := criticalPolar_stationaryDepth F chi d hm hlarge
  (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)).compAddMonoidHom
    (criticalPolarVariable F chi d hm hlarge delta hdelta)

/-- The quotient-derived polar character evaluates through every permitted
stationary representative and every integral lift. -/
theorem criticalPolarAddChar_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (z : F) (hz : z ∈ lattice F 0) :
    criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta
        (reduce F z hz) =
      (psi.character
        ((beta : F) * (delta : F) ^ 2 * z / ((Gamma : Fˣ) : F)) : ℂ) := by
  let hr := criticalPolar_stationaryDepth F chi d hm hlarge
  change (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property))
      (criticalPolarVariable F chi d hm hlarge delta hdelta
        (reduce F z hz)) = _
  rw [criticalPolarVariable_integral_lift]
  rw [← hbeta, lamprechtPairingLeft_apply, lamprechtPairing_mk_mk]
  congr 2
  ring

/-- Exact stationary order makes the intrinsic polar character nontrivial. -/
theorem criticalPolarAddChar_ne_one
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta ≠ 1 := by
  let hr := criticalPolar_stationaryDepth F chi d hm hlarge
  obtain ⟨beta, hbeta⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ))
    (stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
      hr Gamma Gamma.property)
  have hbetaOrd : ord F (beta : F) = ((0 : ℤ) : WithTop ℤ) := by
    simpa only [sub_self] using stationaryNumeratorClass_representative_ord
      F chi psi (chi.conductor : ℤ) hr Gamma Gamma.property beta hbeta
  have hbeta0 : (beta : F) ≠ 0 :=
    (ord_ne_top_iff F).1 (by rw [hbetaOrd]; simp)
  obtain ⟨x, hxord, hpsix⟩ := psi.isConductor.exists_ord_eq_predecessor
  let z : F := x * ((Gamma : Fˣ) : F) /
    ((beta : F) * (delta : F) ^ 2)
  have hzord : ord F z = 0 := by
    dsimp only [z]
    rw [ord_div, ord_mul, hxord, Gamma.property, ord_mul, hbetaOrd,
      ord_pow, hdelta]
    norm_cast
    simp only [two_nsmul]
    omega
  have hz : z ∈ lattice F 0 := by
    rw [mem_lattice, hzord]
    norm_num
  intro htrivial
  have happ : criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta
      (reduce F z hz) = 1 := by
    rw [htrivial]
    exact AddChar.one_apply _
  rw [criticalPolarAddChar_integral_lift F chi psi d hm hlarge Gamma delta
    hdelta beta hbeta z hz] at happ
  have harg : (beta : F) * (delta : F) ^ 2 * z /
      ((Gamma : Fˣ) : F) = x := by
    dsimp only [z]
    field_simp [hbeta0, Units.ne_zero delta,
      AdmissibleGamma.coe_ne_zero Gamma]
  rw [harg] at happ
  apply hpsix
  apply Units.ext
  simpa using happ

/-- The critical polar coefficient relative to a fixed nontrivial residual
character.  It is extracted from the quotient-derived polar character and is
therefore independent of stationary representatives by construction. -/
noncomputable def criticalPolarCoefficient
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    ResidueField F :=
  finiteAddCharCoefficient psi0 hpsi0
    (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta)

@[simp]
theorem criticalPolarCoefficient_spec
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    psi0.mulShift
        (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0) =
      criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta :=
  finiteAddCharCoefficient_spec psi0 hpsi0 _

theorem criticalPolarCoefficient_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
      psi0 hpsi0 ≠ 0 :=
  finiteAddCharCoefficient_ne_zero psi0 hpsi0 _
    (criticalPolarAddChar_ne_one F chi psi d hm hlarge Gamma delta hdelta)

/-- Exact arbitrary-lift and arbitrary-representative characterization of the
critical polar coefficient.  The conclusion is equality of character values;
it does not identify the local-field quotient with a residue-field element. -/
theorem criticalPolarCoefficient_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (z : F) (hz : z ∈ lattice F 0) :
    psi0
        (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
            psi0 hpsi0 * reduce F z hz) =
      (psi.character
        ((beta : F) * (delta : F) ^ 2 * z / ((Gamma : Fˣ) : F)) : ℂ) := by
  change psi0
      (finiteAddCharCoefficient psi0 hpsi0
          (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta) *
        reduce F z hz) = _
  rw [finiteAddCharCoefficient_apply]
  exact criticalPolarAddChar_integral_lift F chi psi d hm hlarge Gamma delta
    hdelta beta hbeta z hz

/-! ### Exact quotient-to-residue normalization -/

/-- The unit which converts a stationary numerator into its residue polar
coefficient relative to the residual denominator `gamma0`. -/
def criticalPolarResidueScale
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (_hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta gamma0 : Fˣ) : Fˣ :=
  delta ^ 2 * gamma0 / (Gamma : Fˣ)

theorem criticalPolarResidueScale_ord
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (gamma0 : Fˣ)
    (hgamma0 : ord F (gamma0 : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ)) :
    ord F (criticalPolarResidueScale F chi psi d hm Gamma delta gamma0 : F) =
      ((0 : ℤ) : WithTop ℤ) := by
  simp only [criticalPolarResidueScale, Units.val_div_eq_div_val,
    Units.val_mul, Units.val_pow_eq_pow_val]
  rw [ord_div, ord_mul, ord_pow, hdelta, hgamma0, Gamma.property]
  norm_cast
  simp only [two_nsmul]
  omega

/-- Residue class computed from a supplied stationary representative.  The
representative is an explicit argument; no declaration chooses one. -/
noncomputable def criticalPolarResidueOfRepresentative
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (gamma0 : Fˣ)
    (hgamma0 : ord F (gamma0 : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ))) :
    ResidueField F :=
  reduce F
    ((criticalPolarResidueScale F chi psi d hm Gamma delta gamma0 : F) *
      (beta : F)) <| by
        have hs : (criticalPolarResidueScale F chi psi d hm Gamma delta gamma0 : F)
            ∈ lattice F 0 := by
          rw [mem_lattice, criticalPolarResidueScale_ord F chi psi d hm Gamma
            delta hdelta gamma0 hgamma0]
        have hb : (beta : F) ∈ lattice F 0 := by
          simpa only [sub_self] using beta.property
        simpa using mul_mem_lattice F hs hb

/-- If `gamma0` realizes the chosen residual character, the abstract
quotient-derived coefficient is exactly the reduction of
`beta*delta^2*gamma0/Gamma` for every permitted `beta`. -/
theorem criticalPolarCoefficient_eq_residue
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (gamma0 : Fˣ)
    (hgamma0 : ord F (gamma0 : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ))
    (hcoordinate : psi0 = residualAddChar F psi gamma0 hgamma0)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
        psi0 hpsi0 =
      criticalPolarResidueOfRepresentative F chi psi d hm Gamma delta hdelta
        gamma0 hgamma0 beta := by
  apply finiteAddCharCoefficient_unique psi0 hpsi0
  apply AddChar.ext
  intro x
  rw [AddChar.mulShift_apply]
  let tx : F := (teichmuller F x : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  let s : F :=
    (criticalPolarResidueScale F chi psi d hm Gamma delta gamma0 : F)
  have hs : s ∈ lattice F 0 := by
    rw [mem_lattice]
    dsimp only [s]
    rw [criticalPolarResidueScale_ord F chi psi d hm Gamma delta hdelta
      gamma0 hgamma0]
  have hbeta0 : (beta : F) ∈ lattice F 0 := by
    simpa only [sub_self] using beta.property
  have hsbeta : s * (beta : F) ∈ lattice F 0 := by
    simpa using mul_mem_lattice F hs hbeta0
  have hw : s * (beta : F) * tx ∈ lattice F 0 := by
    simpa using mul_mem_lattice F hsbeta htx
  have hreduce : reduce F (s * (beta : F) * tx) hw =
      criticalPolarResidueOfRepresentative F chi psi d hm Gamma delta hdelta
          gamma0 hgamma0 beta * x := by
    let sint : ringOfIntegers F :=
      ⟨s * (beta : F), (mem_lattice_zero_iff F).1 hsbeta⟩
    let txint : ringOfIntegers F :=
      ⟨tx, (mem_lattice_zero_iff F).1 htx⟩
    change residueMap F (sint * txint) = residueMap F sint * x
    rw [map_mul]
    congr 1
    exact residueMap_teichmuller F x
  have hres := residualAddChar_integral_lift F psi gamma0 hgamma0
    (s * (beta : F) * tx) hw
  have hpolar := criticalPolarAddChar_integral_lift F chi psi d hm hlarge
    Gamma delta hdelta beta hbeta tx htx
  have harg : s * (beta : F) * tx / (gamma0 : F) =
      (beta : F) * (delta : F) ^ 2 * tx / ((Gamma : Fˣ) : F) := by
    dsimp only [s]
    simp only [criticalPolarResidueScale, Units.val_div_eq_div_val,
      Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero gamma0, Units.ne_zero delta,
      AdmissibleGamma.coe_ne_zero Gamma]
  calc
    psi0
        (criticalPolarResidueOfRepresentative F chi psi d hm Gamma delta
          hdelta gamma0 hgamma0 beta * x) =
        residualAddChar F psi gamma0 hgamma0
          (reduce F (s * (beta : F) * tx) hw) := by
            rw [hcoordinate, hreduce]
    _ = (psi.character (s * (beta : F) * tx / (gamma0 : F)) : ℂ) := hres
    _ = (psi.character
        ((beta : F) * (delta : F) ^ 2 * tx / ((Gamma : Fˣ) : F)) : ℂ) := by
          rw [harg]
    _ = criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta x := by
          simpa [tx] using hpolar.symm

/-- Every two permitted stationary representatives give the same normalized
residue class. -/
theorem criticalPolarResidue_representative_independent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (gamma0 : Fˣ)
    (hgamma0 : ord F (gamma0 : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ))
    (hcoordinate : psi0 = residualAddChar F psi gamma0 hgamma0)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalPolarResidueOfRepresentative F chi psi d hm Gamma delta hdelta
        gamma0 hgamma0 beta =
      criticalPolarResidueOfRepresentative F chi psi d hm Gamma delta hdelta
        gamma0 hgamma0 beta' := by
  rw [← criticalPolarCoefficient_eq_residue F chi psi d hm hlarge Gamma
      delta hdelta psi0 hpsi0 gamma0 hgamma0 hcoordinate beta hbeta,
    ← criticalPolarCoefficient_eq_residue F chi psi d hm hlarge Gamma
      delta hdelta psi0 hpsi0 gamma0 hgamma0 hcoordinate beta' hbeta']

/-! ### Change of critical residual coordinate -/

/-- Scaling the critical element by an arbitrary integral unit lift. -/
def criticalPolarScaledCoordinate (u : unitGroup F) (delta : Fˣ) : Fˣ :=
  (u : Fˣ) * delta

theorem criticalPolarScaledCoordinate_ord
    (d : ℕ) (u : unitGroup F) (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    ord F (criticalPolarScaledCoordinate F u delta : F) =
      ((d : ℤ) : WithTop ℤ) := by
  have hu : ord F (((u : Fˣ) : F)) = ((0 : ℤ) : WithTop ℤ) :=
    (mem_unitGroup_iff_ord_eq_zero F (u : Fˣ)).1 u.property
  change ord F (((u : Fˣ) : F) * (delta : F)) = _
  rw [ord_mul, hu, hdelta]
  simp

/-- On the quotient-derived polar character, changing the critical coordinate
by the residual scalar `lambda` multiplies the polar argument by
`lambda^2`. -/
theorem criticalPolarAddChar_scaleCoordinate
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (u : unitGroup F) :
    criticalPolarAddChar F chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate F u delta)
        (criticalPolarScaledCoordinate_ord F d u delta hdelta) =
      (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta).mulShift
        ((((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2)) := by
  apply AddChar.ext
  intro x
  let hr := criticalPolar_stationaryDepth F chi d hm hlarge
  obtain ⟨beta, hbeta⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ))
    (stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
      hr Gamma Gamma.property)
  let tx : F := (teichmuller F x : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  have huord : ord F (((u : Fˣ) : F)) = ((0 : ℤ) : WithTop ℤ) :=
    (mem_unitGroup_iff_ord_eq_zero F (u : Fˣ)).1 u.property
  have hu : ((u : Fˣ) : F) ∈ lattice F 0 := by
    rw [mem_lattice, huord]
  have huSq : ((u : Fˣ) : F) ^ 2 ∈ lattice F 0 := by
    simpa only [pow_two, zero_add] using mul_mem_lattice F hu hu
  let uz : F := ((u : Fˣ) : F) ^ 2 * tx
  have huz : uz ∈ lattice F 0 := by
    dsimp only [uz]
    simpa using mul_mem_lattice F huSq htx
  have hreduce : reduce F uz huz =
      (((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2) * x := by
    let uint : ringOfIntegers F := unitGroupMulEquivRingOfIntegers F u
    let txint : ringOfIntegers F :=
      ⟨tx, (mem_lattice_zero_iff F).1 htx⟩
    change residueMap F (uint ^ 2 * txint) =
      (residueMap F uint) ^ 2 * x
    rw [map_mul, map_pow]
    congr 1
    exact residueMap_teichmuller F x
  have hnew := criticalPolarAddChar_integral_lift F chi psi d hm hlarge
    Gamma (criticalPolarScaledCoordinate F u delta)
      (criticalPolarScaledCoordinate_ord F d u delta hdelta)
      beta hbeta tx htx
  have hold := criticalPolarAddChar_integral_lift F chi psi d hm hlarge
    Gamma delta hdelta beta hbeta uz huz
  rw [AddChar.mulShift_apply]
  calc
    criticalPolarAddChar F chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate F u delta)
        (criticalPolarScaledCoordinate_ord F d u delta hdelta) x =
      (psi.character
        ((beta : F) * (criticalPolarScaledCoordinate F u delta : F) ^ 2 * tx /
          ((Gamma : Fˣ) : F)) : ℂ) := by
            simpa [tx] using hnew
    _ = (psi.character
        ((beta : F) * (delta : F) ^ 2 * uz / ((Gamma : Fˣ) : F)) : ℂ) := by
          congr 2
          dsimp only [criticalPolarScaledCoordinate, uz]
          simp only [Units.val_mul]
          ring
    _ = criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta
        ((((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2) * x) := by
          rw [← hreduce]
          exact hold.symm

/-- The manuscript's coordinate direction:
`delta ↦ lift(lambda)*delta` sends `A ↦ lambda^2*A`. -/
theorem criticalPolarCoefficient_scaleCoordinate
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (u : unitGroup F) :
    criticalPolarCoefficient F chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate F u delta)
        (criticalPolarScaledCoordinate_ord F d u delta hdelta) psi0 hpsi0 =
      (((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2) *
        criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0 := by
  change finiteAddCharCoefficient psi0 hpsi0
      (criticalPolarAddChar F chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate F u delta)
        (criticalPolarScaledCoordinate_ord F d u delta hdelta)) = _
  rw [criticalPolarAddChar_scaleCoordinate F chi psi d hm hlarge Gamma delta
    hdelta u, finiteAddCharCoefficient_mulShift]
  change finiteAddCharCoefficient psi0 hpsi0
      (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta) *
        (((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2) =
    (((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) ^ 2) *
      finiteAddCharCoefficient psi0 hpsi0
        (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta)
  exact mul_comm _ _

/-- The coordinate formula is independent of which integral unit lift of
`lambda` is supplied. -/
theorem criticalPolarCoefficient_scaleCoordinate_lift_independent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (u v : unitGroup F) (huv : residueUnits F u = residueUnits F v) :
    criticalPolarCoefficient F chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate F u delta)
        (criticalPolarScaledCoordinate_ord F d u delta hdelta) psi0 hpsi0 =
      criticalPolarCoefficient F chi psi d hm hlarge Gamma
        (criticalPolarScaledCoordinate F v delta)
        (criticalPolarScaledCoordinate_ord F d v delta hdelta) psi0 hpsi0 := by
  rw [criticalPolarCoefficient_scaleCoordinate F chi psi d hm hlarge Gamma
      delta hdelta psi0 hpsi0 u,
    criticalPolarCoefficient_scaleCoordinate F chi psi d hm hlarge Gamma
      delta hdelta psi0 hpsi0 v, huv]

/-- Precomposing the intrinsic polar character by a Frobenius automorphism
sends the coefficient in the inverse (`p`th-root) direction. -/
theorem criticalPolarCoefficient_frobenius
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (sigma : ResidueField F ≃+* ResidueField F)
    (hsigma : ∀ x, psi0 (sigma x) = psi0 x) :
    finiteAddCharCoefficient psi0 hpsi0
        (finiteAddCharPrecompose
          (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta)
          sigma) =
      sigma.symm
        (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0) :=
  finiteAddCharCoefficient_precompose psi0 hpsi0 sigma hsigma _

/-- Precomposition by inverse Frobenius sends the intrinsic polar coefficient
in the forward `p`th-power direction. -/
theorem criticalPolarCoefficient_frobenius_symm
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (sigma : ResidueField F ≃+* ResidueField F)
    (hsigma : ∀ x, psi0 (sigma x) = psi0 x) :
    finiteAddCharCoefficient psi0 hpsi0
        (finiteAddCharPrecompose
          (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta)
          sigma.symm) =
      sigma
        (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0) :=
  finiteAddCharCoefficient_precompose_symm psi0 hpsi0 sigma hsigma _

/-! ### Affine coefficient under stationary-representative translation -/

private theorem criticalLocalAddChar_eq_of_sub_mem
    (psi : LocalAddCharData F) {a b : F}
    (hab : a - b ∈ lattice F (-psi.conductor)) :
    (psi.character a : ℂ) = (psi.character b : ℂ) := by
  have htriv := psi.isConductor.trivial (a - b) hab
  have hadd := ContinuousAddChar.map_add_eq_mul psi.character
    (a - b) b
  have hsum : a - b + b = a := by ring
  rw [hsum, htriv, one_mul] at hadd
  exact congrArg (Units.val : ℂˣ → ℂ) hadd

/-- The residual additive character created by a permitted difference
`c0 ∈ p^d` between stationary representatives. -/
noncomputable def criticalAffineTranslationAddChar
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c0 : lattice F (d : ℤ)) : FiniteAddChar (ResidueField F) where
  toFun x :=
    (psi.character
      ((c0 : F) * (delta : F) * (teichmuller F x : F) /
        ((Gamma : Fˣ) : F)) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    let tx : F := (teichmuller F x : F)
    let ty : F := (teichmuller F y : F)
    let txy : F := (teichmuller F (x + y) : F)
    have hdiff : txy - (tx + ty) ∈ lattice F 1 := by
      apply (residueMap_eq_residueMap_iff F
        (teichmuller F (x + y)) (teichmuller F x + teichmuller F y)).1
      simp
    have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
      rw [mem_lattice, hdelta]
    have hc0delta : (c0 : F) * (delta : F) ∈
        lattice F ((d : ℤ) + d) :=
      mul_mem_lattice F c0.property hdeltaMem
    have hnum : (c0 : F) * (delta : F) * (txy - (tx + ty)) ∈
        lattice F ((chi.conductor : ℕ) : ℤ) := by
      have hp := mul_mem_lattice F hc0delta hdiff
      have hdepth : (chi.conductor : ℤ) = (d : ℤ) + d + 1 := by omega
      simpa only [hdepth, add_assoc] using hp
    have herr : ((c0 : F) * (delta : F) * txy /
          ((Gamma : Fˣ) : F)) -
        (((c0 : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) +
          ((c0 : F) * (delta : F) * ty / ((Gamma : Fˣ) : F))) ∈
          lattice F (-psi.conductor) := by
      have hdiv : (c0 : F) * (delta : F) * (txy - (tx + ty)) /
          ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
        apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
          ((c0 : F) * (delta : F) * (txy - (tx + ty)))
          ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
          Gamma.property).2
        simpa only [add_assoc, add_neg_cancel, add_zero] using hnum
      convert hdiv using 1 <;> ring
    have heq := criticalLocalAddChar_eq_of_sub_mem F psi herr
    have hadd := ContinuousAddChar.map_add_eq_mul psi.character
      ((c0 : F) * (delta : F) * tx / ((Gamma : Fˣ) : F))
      ((c0 : F) * (delta : F) * ty / ((Gamma : Fˣ) : F))
    have haddC := congrArg (Units.val : ℂˣ → ℂ) hadd
    change (psi.character
        ((c0 : F) * (delta : F) * txy / ((Gamma : Fˣ) : F)) : ℂ) = _
    rw [heq]
    simpa only [Units.val_mul] using haddC

/-- Arbitrary-integral-lift formula for the affine translation character. -/
theorem criticalAffineTranslationAddChar_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c0 : lattice F (d : ℤ)) (z : F) (hz : z ∈ lattice F 0) :
    criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0
        (reduce F z hz) =
      (psi.character
        ((c0 : F) * (delta : F) * z / ((Gamma : Fˣ) : F)) : ℂ) := by
  let tz : F := (teichmuller F (reduce F z hz) : F)
  have hdiff : tz - z ∈ lattice F 1 := by
    let zint : ringOfIntegers F := ⟨z, (mem_lattice_zero_iff F).1 hz⟩
    apply (residueMap_eq_residueMap_iff F
      (teichmuller F (reduce F z hz)) zint).1
    simp [reduce, zint]
  have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have hc0delta : (c0 : F) * (delta : F) ∈
      lattice F ((d : ℤ) + d) :=
    mul_mem_lattice F c0.property hdeltaMem
  have hnum : (c0 : F) * (delta : F) * (tz - z) ∈
      lattice F (chi.conductor : ℤ) := by
    have hp := mul_mem_lattice F hc0delta hdiff
    have hdepth : (chi.conductor : ℤ) = (d : ℤ) + d + 1 := by omega
    simpa only [hdepth, add_assoc] using hp
  apply criticalLocalAddChar_eq_of_sub_mem F psi
  have hdiv : (c0 : F) * (delta : F) * (tz - z) /
      ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
    apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
      ((c0 : F) * (delta : F) * (tz - z))
      ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
      Gamma.property).2
    simpa only [add_assoc, add_neg_cancel, add_zero] using hnum
  convert hdiv using 1 <;> ring

/-- The affine additive-character coefficient `Delta B`.  It may be zero. -/
noncomputable def criticalAffineTranslationCoefficient
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (c0 : lattice F (d : ℤ)) : ResidueField F :=
  finiteAddCharCoefficient psi0 hpsi0
    (criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0)

@[simp]
theorem criticalAffineTranslationCoefficient_spec
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (c0 : lattice F (d : ℤ)) :
    psi0.mulShift
        (criticalAffineTranslationCoefficient F chi psi d hm Gamma delta
          hdelta psi0 hpsi0 c0) =
      criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0 :=
  finiteAddCharCoefficient_spec psi0 hpsi0 _

theorem criticalAffineTranslationCoefficient_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (c0 : lattice F (d : ℤ)) (z : F) (hz : z ∈ lattice F 0) :
    psi0
        (criticalAffineTranslationCoefficient F chi psi d hm Gamma delta
            hdelta psi0 hpsi0 c0 * reduce F z hz) =
      (psi.character
        ((c0 : F) * (delta : F) * z / ((Gamma : Fˣ) : F)) : ℂ) := by
  change psi0
      (finiteAddCharCoefficient psi0 hpsi0
          (criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0) *
        reduce F z hz) = _
  rw [finiteAddCharCoefficient_apply]
  exact criticalAffineTranslationAddChar_integral_lift F chi psi d hm Gamma
    delta hdelta c0 z hz

/-- The difference `beta' - beta`, bundled at precisely the permitted depth
`p^d`. -/
def criticalStationaryRepresentativeDifference
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) : lattice F (d : ℤ) :=
  ⟨(beta' : F) - (beta : F), by
    have hclasses : latticeQuotientMk F
          (sub_le_sub_left
            (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
            (chi.conductor : ℤ)) beta' =
        latticeQuotientMk F
          (sub_le_sub_left
            (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
            (chi.conductor : ℤ)) beta := hbeta'.trans hbeta.symm
    have hcong := (latticeQuotientMk_eq_mk_iff_congruentAtDepth F _).1 hclasses
    rw [CongruentAtDepth] at hcong
    have hdepth : (chi.conductor : ℤ) - ((d + 1 : ℕ) : ℤ) = d := by
      omega
    rw [mem_lattice]
    simpa only [hdepth] using hcong⟩

theorem criticalStationaryRepresentative_ord_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    ord F (beta : F) = ((0 : ℤ) : WithTop ℤ) := by
  simpa only [sub_self] using stationaryNumeratorClass_representative_ord
    F chi psi (chi.conductor : ℤ)
      (criticalPolar_stationaryDepth F chi d hm hlarge)
      Gamma Gamma.property beta hbeta

/-- The manuscript's translation parameter before reduction:
`aField = (beta' - beta)/(beta*delta)`. -/
def criticalRepresentativeTranslationField
    (beta beta' : F) (delta : Fˣ) : F :=
  (beta' - beta) / (beta * (delta : F))

theorem criticalRepresentativeTranslationField_integral
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalRepresentativeTranslationField F (beta : F) (beta' : F) delta ∈
      lattice F 0 := by
  have hbetaOrd := criticalStationaryRepresentative_ord_zero F chi psi d hm
    hlarge Gamma beta hbeta
  have hdenom : ord F ((beta : F) * (delta : F)) =
      ((d : ℤ) : WithTop ℤ) := by
    rw [ord_mul, hbetaOrd, hdelta]
    simp
  apply (div_mem_lattice_iff F ((beta : F) * (delta : F))
    ((beta' : F) - (beta : F)) (d : ℤ) 0 hdenom).2
  have hdiff :=
    (criticalStationaryRepresentativeDifference F chi psi d hm hlarge Gamma
      beta beta' hbeta hbeta').property
  change (beta' : F) - (beta : F) ∈ lattice F (d : ℤ) at hdiff
  simpa only [add_zero] using hdiff

/-- The residue translation parameter `a`.  It is distinct from the affine
coefficient change `Delta B`. -/
noncomputable def criticalRepresentativeTranslationParameter
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) : ResidueField F :=
  reduce F
    (criticalRepresentativeTranslationField F (beta : F) (beta' : F) delta)
    (criticalRepresentativeTranslationField_integral F chi psi d hm hlarge
      Gamma delta hdelta beta beta' hbeta hbeta')

/-- The affine translation character is the polar character shifted by the
translation parameter `a`. -/
theorem criticalAffineTranslationAddChar_eq_polar_mulShift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta
        (criticalStationaryRepresentativeDifference F chi psi d hm hlarge
          Gamma beta beta' hbeta hbeta') =
      (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta).mulShift
        (criticalRepresentativeTranslationParameter F chi psi d hm hlarge
          Gamma delta hdelta beta beta' hbeta hbeta') := by
  apply AddChar.ext
  intro x
  let tx : F := (teichmuller F x : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  let aField : F :=
    criticalRepresentativeTranslationField F (beta : F) (beta' : F) delta
  have haField : aField ∈ lattice F 0 :=
    criticalRepresentativeTranslationField_integral F chi psi d hm hlarge
      Gamma delta hdelta beta beta' hbeta hbeta'
  have hatx : aField * tx ∈ lattice F 0 := by
    simpa using mul_mem_lattice F haField htx
  have hreduce : reduce F (aField * tx) hatx =
      criticalRepresentativeTranslationParameter F chi psi d hm hlarge
        Gamma delta hdelta beta beta' hbeta hbeta' * x := by
    let afint : ringOfIntegers F :=
      ⟨aField, (mem_lattice_zero_iff F).1 haField⟩
    let txint : ringOfIntegers F :=
      ⟨tx, (mem_lattice_zero_iff F).1 htx⟩
    change residueMap F (afint * txint) = residueMap F afint * x
    rw [map_mul]
    congr 1
    exact residueMap_teichmuller F x
  have haffine := criticalAffineTranslationAddChar_integral_lift
    F chi psi d hm Gamma delta hdelta
      (criticalStationaryRepresentativeDifference F chi psi d hm hlarge
        Gamma beta beta' hbeta hbeta') tx htx
  have hpolar := criticalPolarAddChar_integral_lift F chi psi d hm hlarge
    Gamma delta hdelta beta hbeta (aField * tx) hatx
  have haffine' :
      criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta
          (criticalStationaryRepresentativeDifference F chi psi d hm hlarge
            Gamma beta beta' hbeta hbeta') x =
        (psi.character
          ((criticalStationaryRepresentativeDifference F chi psi d hm hlarge
                Gamma beta beta' hbeta hbeta' : F) *
            (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) := by
    simpa [tx] using haffine
  rw [AddChar.mulShift_apply, ← hreduce]
  rw [haffine', hpolar]
  congr 2
  have hbeta0 : (beta : F) ≠ 0 :=
    (ord_ne_top_iff F).1 <| by
      rw [criticalStationaryRepresentative_ord_zero F chi psi d hm hlarge
        Gamma beta hbeta]
      simp
  dsimp only [criticalStationaryRepresentativeDifference, aField,
    criticalRepresentativeTranslationField]
  field_simp [hbeta0, Units.ne_zero delta,
    AdmissibleGamma.coe_ne_zero Gamma]

/-- Exact relation between the two translation quantities:
`Delta B = A*a`. -/
theorem criticalRepresentativeAffineCoefficient_eq_polar_mul_parameter
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalAffineTranslationCoefficient F chi psi d hm Gamma delta hdelta
        psi0 hpsi0
        (criticalStationaryRepresentativeDifference F chi psi d hm hlarge
          Gamma beta beta' hbeta hbeta') =
      criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0 *
        criticalRepresentativeTranslationParameter F chi psi d hm hlarge
          Gamma delta hdelta beta beta' hbeta hbeta' := by
  change finiteAddCharCoefficient psi0 hpsi0
      (criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta
        (criticalStationaryRepresentativeDifference F chi psi d hm hlarge
          Gamma beta beta' hbeta hbeta')) = _
  rw [criticalAffineTranslationAddChar_eq_polar_mulShift F chi psi d hm hlarge
    Gamma delta hdelta beta beta' hbeta hbeta',
    finiteAddCharCoefficient_mulShift]
  rfl

/-! ### The critical function and representative translation -/

theorem criticalPolar_d_pos
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) : 0 < d := by
  omega

/-- The local unit `1 + delta*z` at the odd critical depth. -/
def criticalPolarUnit
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (z : F) (hz : z ∈ lattice F 0) : unitFiltration F d :=
  positiveUnitOfLattice F (criticalPolar_d_pos F chi d hm hlarge)
    ⟨(delta : F) * z, by
      have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
        rw [mem_lattice, hdelta]
      simpa using mul_mem_lattice F hdeltaMem hz⟩

@[simp]
theorem criticalPolarUnit_coe
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (z : F) (hz : z ∈ lattice F 0) :
    ((criticalPolarUnit F chi d hm hlarge delta hdelta z hz : Fˣ) : F) =
      1 + (delta : F) * z :=
  rfl

/-- Lift-level critical function with the manuscript's inverse
multiplicative-character convention. -/
def criticalPolarValue
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (z : F) (hz : z ∈ lattice F 0) : ℂ :=
  (psi.character
      ((beta : F) * (delta : F) * z / ((Gamma : Fˣ) : F)) : ℂ) *
    (chi.character
      (criticalPolarUnit F chi d hm hlarge delta hdelta z hz) : ℂ)⁻¹

theorem criticalPolarValue_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (z : F) (hz : z ∈ lattice F 0) :
    criticalPolarValue F chi psi d hm hlarge Gamma delta hdelta beta z hz ≠ 0 :=
  mul_ne_zero (ContinuousAddChar.apply_ne_zero _ _)
    (inv_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _))

/-- Residue-field critical function, evaluated on Teichmüller lifts. -/
noncomputable def criticalPolarFunction
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ))) :
    ResidueField F → ℂ := fun x ↦
  criticalPolarValue F chi psi d hm hlarge Gamma delta hdelta beta
    (teichmuller F x : F)
    ((mem_lattice_zero_iff F).2 (teichmuller F x).property)

@[simp]
theorem criticalPolarFunction_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ))) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta 0 = 1 := by
  simp only [criticalPolarFunction, criticalPolarValue]
  have hunit :
      (criticalPolarUnit F chi d hm hlarge delta hdelta
        (teichmuller F 0 : F)
        ((mem_lattice_zero_iff F).2 (teichmuller F 0).property) : Fˣ) = 1 := by
    apply Units.ext
    simp
  rw [hunit, map_one]
  simp

/-- Replacing `beta` by the permitted representative `beta'` multiplies the
critical function by the affine character with coefficient `Delta B`.  The
polar coefficient, which has no representative argument, is unchanged. -/
theorem criticalPolarFunction_changeRepresentative
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField F) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta' x =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
        psi0
          (criticalAffineTranslationCoefficient F chi psi d hm Gamma delta
            hdelta psi0 hpsi0
              (criticalStationaryRepresentativeDifference F chi psi d hm
                hlarge Gamma beta beta' hbeta hbeta') * x) := by
  let tx : F := (teichmuller F x : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  let c0 := criticalStationaryRepresentativeDifference F chi psi d hm hlarge
    Gamma beta beta' hbeta hbeta'
  have haff := criticalAffineTranslationCoefficient_integral_lift
    F chi psi d hm Gamma delta hdelta psi0 hpsi0 c0 tx htx
  have haff' :
      psi0
          (criticalAffineTranslationCoefficient F chi psi d hm Gamma delta
            hdelta psi0 hpsi0 c0 * x) =
        (psi.character
          ((c0 : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) := by
    simpa [tx] using haff
  have hadd := ContinuousAddChar.map_add_eq_mul psi.character
    ((beta : F) * (delta : F) * tx / ((Gamma : Fˣ) : F))
    ((c0 : F) * (delta : F) * tx / ((Gamma : Fˣ) : F))
  have haddC := congrArg (Units.val : ℂˣ → ℂ) hadd
  simp only [Units.val_mul] at haddC
  have harg : (beta : F) * (delta : F) * tx / ((Gamma : Fˣ) : F) +
      (c0 : F) * (delta : F) * tx / ((Gamma : Fˣ) : F) =
      (beta' : F) * (delta : F) * tx / ((Gamma : Fˣ) : F) := by
    dsimp only [c0, criticalStationaryRepresentativeDifference]
    ring
  rw [harg] at haddC
  change
    (psi.character
        ((beta' : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character
          (criticalPolarUnit F chi d hm hlarge delta hdelta tx htx) : ℂ)⁻¹ =
      ((psi.character
          ((beta : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character
          (criticalPolarUnit F chi d hm hlarge delta hdelta tx htx) : ℂ)⁻¹) * _
  rw [haff']
  rw [haddC]
  ring

/-- Characteristic-independent representative translation, expressed without
choosing a coordinate character: the complete function is translated by its
own intrinsic polar character at the residue parameter `a`. -/
theorem criticalPolarFunction_changeRepresentative_intrinsic
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField F) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta' x =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
        criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta
          (criticalRepresentativeTranslationParameter F chi psi d hm hlarge
            Gamma delta hdelta beta beta' hbeta hbeta' * x) := by
  let polar := criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta
  have hpolar : polar ≠ 1 :=
    criticalPolarAddChar_ne_one F chi psi d hm hlarge Gamma delta hdelta
  let c0 := criticalStationaryRepresentativeDifference F chi psi d hm hlarge
    Gamma beta beta' hbeta hbeta'
  let a := criticalRepresentativeTranslationParameter F chi psi d hm hlarge
    Gamma delta hdelta beta beta' hbeta hbeta'
  let DeltaB := criticalAffineTranslationCoefficient F chi psi d hm Gamma
    delta hdelta polar hpolar c0
  have hchange := criticalPolarFunction_changeRepresentative F chi psi d hm
    hlarge Gamma delta hdelta polar hpolar beta beta' hbeta hbeta' x
  have hDelta : polar (DeltaB * x) =
      criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0 x :=
    finiteAddCharCoefficient_apply polar hpolar
      (criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0) x
  have haffine := criticalAffineTranslationAddChar_eq_polar_mulShift F chi psi d
    hm hlarge Gamma delta hdelta beta beta' hbeta hbeta'
  have ha :
      criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta c0 x =
        polar (a * x) := by
    change criticalAffineTranslationAddChar F chi psi d hm Gamma delta hdelta
        c0 x = (polar.mulShift a) x
    exact DFunLike.congr_fun haffine x
  change criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta' x =
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
      polar (a * x)
  calc
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta' x =
        criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
          polar (DeltaB * x) := hchange
    _ = criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
          polar (a * x) := by rw [hDelta, ha]

/-- Changing an integral lift by an element of the maximal ideal leaves the
complete critical function unchanged: its additive and multiplicative changes
cancel through stationary linearization. -/
theorem criticalPolarValue_eq_of_congruent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (z z' : F) (hz : z ∈ lattice F 0) (hz' : z' ∈ lattice F 0)
    (hzz' : CongruentAtDepth 1 z z') :
    criticalPolarValue F chi psi d hm hlarge Gamma delta hdelta beta z hz =
      criticalPolarValue F chi psi d hm hlarge Gamma delta hdelta beta z' hz' := by
  have hdiff : z - z' ∈ lattice F 1 :=
    (congruentAtDepth_iff_sub_mem_lattice F 1 z z').1 hzz'
  let u' := criticalPolarUnit F chi d hm hlarge delta hdelta z' hz'
  have hu'ne : 1 + (delta : F) * z' ≠ 0 := by
    rw [← criticalPolarUnit_coe F chi d hm hlarge delta hdelta z' hz']
    exact Units.ne_zero (u' : Fˣ)
  have hu'ord : ord F ((u' : Fˣ) : F) = ((0 : ℤ) : WithTop ℤ) := by
    apply (mem_unitFiltration_zero F (u' : Fˣ)).1
    exact unitFiltration_antitone F (Nat.zero_le d) u'.property
  let w : F := (delta : F) * (z - z') / ((u' : Fˣ) : F)
  have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have hnum : (delta : F) * (z - z') ∈ lattice F ((d : ℤ) + 1) :=
    mul_mem_lattice F hdeltaMem hdiff
  have hw : w ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    apply (div_mem_lattice_iff F ((u' : Fˣ) : F)
      ((delta : F) * (z - z')) 0 ((d + 1 : ℕ) : ℤ) hu'ord).2
    simpa using hnum
  let wx : lattice F ((d + 1 : ℕ) : ℤ) := ⟨w, hw⟩
  let uw := positiveUnitOfLattice F
    (criticalPolar_stationaryDepth F chi d hm hlarge).pos wx
  have hunit :
      (criticalPolarUnit F chi d hm hlarge delta hdelta z hz : Fˣ) =
        (u' : Fˣ) * (uw : Fˣ) := by
    apply Units.ext
    change 1 + (delta : F) * z =
      (1 + (delta : F) * z') * (1 + w)
    dsimp only [w, u']
    rw [criticalPolarUnit_coe]
    field_simp [hu'ne]
    ring
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ)
    (criticalPolar_stationaryDepth F chi d hm hlarge)
    Gamma Gamma.property beta hbeta wx
  have hlinearC := congrArg (Units.val : ℂˣ → ℂ) hlinear
  have hchi :
      (chi.character
        (criticalPolarUnit F chi d hm hlarge delta hdelta z hz) : ℂ) =
      (chi.character (u' : Fˣ) : ℂ) *
        (psi.character ((beta : F) * w / ((Gamma : Fˣ) : F)) : ℂ) := by
    rw [hunit, map_mul]
    exact congrArg₂ (fun a b : ℂ ↦ a * b) rfl hlinearC
  have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
    simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
  have hz'diff : (delta : F) ^ 2 * z' * (z - z') ∈
      lattice F ((d : ℤ) + d + 1) := by
    have hzprod := mul_mem_lattice F hdeltaSq hz'
    have hall := mul_mem_lattice F hzprod hdiff
    simpa [add_assoc] using hall
  have herror : (delta : F) ^ 2 * z' * (z - z') / ((u' : Fˣ) : F) ∈
      lattice F (chi.conductor : ℤ) := by
    apply (div_mem_lattice_iff F ((u' : Fˣ) : F)
      ((delta : F) ^ 2 * z' * (z - z')) 0 (chi.conductor : ℤ) hu'ord).2
    have hcast : (chi.conductor : ℤ) = (d : ℤ) + d + 1 := by omega
    simpa only [zero_add, hcast] using hz'diff
  have hdifference : (delta : F) * (z - z') - w ∈
      lattice F (chi.conductor : ℤ) := by
    have halg : (delta : F) * (z - z') - w =
        (delta : F) ^ 2 * z' * (z - z') / ((u' : Fˣ) : F) := by
      dsimp only [w, u']
      rw [criticalPolarUnit_coe]
      field_simp [hu'ne]
      ring
    rw [halg]
    exact herror
  have hbeta0 : (beta : F) ∈ lattice F 0 := by
    simpa only [sub_self] using beta.property
  have hbetaError : (beta : F) * ((delta : F) * (z - z') - w) ∈
      lattice F (chi.conductor : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice F hbeta0 hdifference
  have hpsiError : (beta : F) * ((delta : F) * (z - z') - w) /
      ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
    apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
      ((beta : F) * ((delta : F) * (z - z') - w))
      ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
      Gamma.property).2
    simpa only [add_assoc, add_neg_cancel, add_zero] using hbetaError
  have hpsiC :
      (psi.character ((beta : F) * ((delta : F) * (z - z')) /
        ((Gamma : Fˣ) : F)) : ℂ) =
      (psi.character ((beta : F) * w / ((Gamma : Fˣ) : F)) : ℂ) := by
    apply criticalLocalAddChar_eq_of_sub_mem F psi
    have halg :
        (beta : F) * ((delta : F) * (z - z')) / ((Gamma : Fˣ) : F) -
          (beta : F) * w / ((Gamma : Fˣ) : F) =
        (beta : F) * ((delta : F) * (z - z') - w) /
          ((Gamma : Fˣ) : F) := by ring
    rw [halg]
    exact hpsiError
  have hadd :
      (psi.character ((beta : F) * (delta : F) * z /
        ((Gamma : Fˣ) : F)) : ℂ) =
      (psi.character ((beta : F) * ((delta : F) * (z - z')) /
        ((Gamma : Fˣ) : F)) : ℂ) *
      (psi.character ((beta : F) * (delta : F) * z' /
        ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := ContinuousAddChar.map_add_eq_mul psi.character
      ((beta : F) * ((delta : F) * (z - z')) / ((Gamma : Fˣ) : F))
      ((beta : F) * (delta : F) * z' / ((Gamma : Fˣ) : F))
    have hmapC := congrArg (Units.val : ℂˣ → ℂ) hmap
    push_cast at hmapC
    convert hmapC using 1 <;> ring
  rw [criticalPolarValue, criticalPolarValue, hchi, hadd, hpsiC]
  have hp0 : (psi.character ((beta : F) * w / ((Gamma : Fˣ) : F)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  field_simp
  rfl

/-- Evaluation of the residue-field critical function on every integral
lift. -/
theorem criticalPolarFunction_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (z : F) (hz : z ∈ lattice F 0) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta
        (reduce F z hz) =
      criticalPolarValue F chi psi d hm hlarge Gamma delta hdelta beta z hz := by
  apply criticalPolarValue_eq_of_congruent F chi psi d hm hlarge Gamma delta
    hdelta beta hbeta
  apply (congruentAtDepth_iff_sub_mem_lattice F 1 _ _).2
  let zint : ringOfIntegers F := ⟨z, (mem_lattice_zero_iff F).1 hz⟩
  apply (residueMap_eq_residueMap_iff F
    (teichmuller F (reduce F z hz)) zint).1
  simp [reduce, zint]

/-- The complete critical function has the intrinsic quotient-derived polar
character, with the manuscript's positive sign. -/
theorem criticalPolarFunction_map_add
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x y : ResidueField F) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta (x + y) =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
        criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta y *
        criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta (x * y) := by
  let tx : F := (teichmuller F x : F)
  let ty : F := (teichmuller F y : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  have hty : ty ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F y).property
  have hsum : tx + ty ∈ lattice F 0 := add_mem htx hty
  have hcanon :
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta
          (x + y) =
        criticalPolarValue F chi psi d hm hlarge Gamma delta hdelta beta
          (tx + ty) hsum := by
    apply criticalPolarValue_eq_of_congruent F chi psi d hm hlarge Gamma delta
      hdelta beta hbeta
    apply (congruentAtDepth_iff_sub_mem_lattice F 1 _ _).2
    apply (residueMap_eq_residueMap_iff F
      (teichmuller F (x + y)) (teichmuller F x + teichmuller F y)).1
    simp
  rw [hcanon]
  let us := criticalPolarUnit F chi d hm hlarge delta hdelta (tx + ty) hsum
  have husord : ord F ((us : Fˣ) : F) = ((0 : ℤ) : WithTop ℤ) := by
    apply (mem_unitFiltration_zero F (us : Fˣ)).1
    exact unitFiltration_antitone F (Nat.zero_le d) us.property
  have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
    simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
  have hxy : tx * ty ∈ lattice F 0 := by
    simpa using mul_mem_lattice F htx hty
  have hquad : (delta : F) ^ 2 * (tx * ty) ∈
      lattice F ((d : ℤ) + d) := by
    simpa using mul_mem_lattice F hdeltaSq hxy
  let w : F := (delta : F) ^ 2 * (tx * ty) / ((us : Fˣ) : F)
  have hw : w ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    apply (div_mem_lattice_iff F ((us : Fˣ) : F)
      ((delta : F) ^ 2 * (tx * ty)) 0 ((d + 1 : ℕ) : ℤ) husord).2
    have hquad' : (delta : F) ^ 2 * (tx * ty) ∈
        lattice F ((d + 1 : ℕ) : ℤ) := by
      have hineq : ((d + 1 : ℕ) : ℤ) ≤ (d : ℤ) + d := by
        have := criticalPolar_d_pos F chi d hm hlarge
        omega
      exact lattice_antitone F hineq hquad
    simpa only [zero_add] using hquad'
  let wx : lattice F ((d + 1 : ℕ) : ℤ) := ⟨w, hw⟩
  let uw := positiveUnitOfLattice F
    (criticalPolar_stationaryDepth F chi d hm hlarge).pos wx
  have hunit :
      (criticalPolarUnit F chi d hm hlarge delta hdelta tx htx : Fˣ) *
          (criticalPolarUnit F chi d hm hlarge delta hdelta ty hty : Fˣ) =
        (us : Fˣ) * (uw : Fˣ) := by
    apply Units.ext
    change (1 + (delta : F) * tx) * (1 + (delta : F) * ty) =
      (1 + (delta : F) * (tx + ty)) * (1 + w)
    have husne : 1 + (delta : F) * (tx + ty) ≠ 0 := by
      rw [← criticalPolarUnit_coe F chi d hm hlarge delta hdelta
        (tx + ty) hsum]
      exact Units.ne_zero (us : Fˣ)
    dsimp only [w, us]
    rw [criticalPolarUnit_coe]
    field_simp [husne]
    ring
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ)
    (criticalPolar_stationaryDepth F chi d hm hlarge)
    Gamma Gamma.property beta hbeta wx
  have hlinearC := congrArg (Units.val : ℂˣ → ℂ) hlinear
  have hchi :
      (chi.character
        (criticalPolarUnit F chi d hm hlarge delta hdelta tx htx) : ℂ) *
      (chi.character
        (criticalPolarUnit F chi d hm hlarge delta hdelta ty hty) : ℂ) =
      (chi.character (us : Fˣ) : ℂ) *
        (psi.character ((beta : F) * w / ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := congrArg (Units.val : ℂˣ → ℂ)
      (congrArg chi.character hunit)
    rw [map_mul, map_mul] at hmap
    exact hmap.trans (congrArg₂ (fun a b : ℂ ↦ a * b) rfl hlinearC)
  have hsumPsi :
      (psi.character ((beta : F) * (delta : F) * (tx + ty) /
        ((Gamma : Fˣ) : F)) : ℂ) =
      (psi.character ((beta : F) * (delta : F) * tx /
        ((Gamma : Fˣ) : F)) : ℂ) *
      (psi.character ((beta : F) * (delta : F) * ty /
        ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := ContinuousAddChar.map_add_eq_mul psi.character
      ((beta : F) * (delta : F) * tx / ((Gamma : Fˣ) : F))
      ((beta : F) * (delta : F) * ty / ((Gamma : Fˣ) : F))
    have hmapC := congrArg (Units.val : ℂˣ → ℂ) hmap
    push_cast at hmapC
    convert hmapC using 1 <;> ring
  have hredxy : reduce F (tx * ty) hxy = x * y := by
    change residueMap F (teichmuller F x * teichmuller F y) = x * y
    simp
  have hpolar := criticalPolarAddChar_integral_lift
    F chi psi d hm hlarge Gamma delta hdelta beta hbeta (tx * ty) hxy
  rw [hredxy] at hpolar
  have hdeltaSum : (delta : F) * (tx + ty) ∈ lattice F (d : ℤ) := by
    simpa using mul_mem_lattice F hdeltaMem hsum
  have herrNum :
      ((delta : F) ^ 2 * (tx * ty)) * ((delta : F) * (tx + ty)) ∈
        lattice F (((d : ℤ) + d) + d) :=
    mul_mem_lattice F hquad hdeltaSum
  have herrNum' :
      ((delta : F) ^ 2 * (tx * ty)) * ((delta : F) * (tx + ty)) ∈
        lattice F (chi.conductor : ℤ) := by
    have hineq : (chi.conductor : ℤ) ≤ ((d : ℤ) + d) + d := by
      have := criticalPolar_d_pos F chi d hm hlarge
      omega
    exact lattice_antitone F hineq herrNum
  have herror :
      ((delta : F) ^ 2 * (tx * ty)) * ((delta : F) * (tx + ty)) /
          ((us : Fˣ) : F) ∈ lattice F (chi.conductor : ℤ) := by
    apply (div_mem_lattice_iff F ((us : Fˣ) : F)
      (((delta : F) ^ 2 * (tx * ty)) * ((delta : F) * (tx + ty)))
      0 (chi.conductor : ℤ) husord).2
    simpa only [zero_add] using herrNum'
  have hquadDifference : (delta : F) ^ 2 * (tx * ty) - w ∈
      lattice F (chi.conductor : ℤ) := by
    have halg : (delta : F) ^ 2 * (tx * ty) - w =
        ((delta : F) ^ 2 * (tx * ty)) * ((delta : F) * (tx + ty)) /
          ((us : Fˣ) : F) := by
      have husne : 1 + (delta : F) * (tx + ty) ≠ 0 := by
        rw [← criticalPolarUnit_coe F chi d hm hlarge delta hdelta
          (tx + ty) hsum]
        exact Units.ne_zero (us : Fˣ)
      dsimp only [w, us]
      rw [criticalPolarUnit_coe]
      field_simp [husne]
      ring
    rw [halg]
    exact herror
  have hbeta0 : (beta : F) ∈ lattice F 0 := by
    simpa only [sub_self] using beta.property
  have hbetaMul : (beta : F) * ((delta : F) ^ 2 * (tx * ty) - w) ∈
      lattice F (chi.conductor : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice F hbeta0 hquadDifference
  have hpsiError : (beta : F) * ((delta : F) ^ 2 * (tx * ty) - w) /
      ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
    apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
      ((beta : F) * ((delta : F) ^ 2 * (tx * ty) - w))
      ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
      Gamma.property).2
    simpa only [add_assoc, add_neg_cancel, add_zero] using hbetaMul
  have hquadPsiC :
      (psi.character ((beta : F) * ((delta : F) ^ 2 * (tx * ty)) /
        ((Gamma : Fˣ) : F)) : ℂ) =
      (psi.character ((beta : F) * w / ((Gamma : Fˣ) : F)) : ℂ) := by
    apply criticalLocalAddChar_eq_of_sub_mem F psi
    have halg :
        (beta : F) * ((delta : F) ^ 2 * (tx * ty)) / ((Gamma : Fˣ) : F) -
          (beta : F) * w / ((Gamma : Fˣ) : F) =
        (beta : F) * ((delta : F) ^ 2 * (tx * ty) - w) /
          ((Gamma : Fˣ) : F) := by ring
    rw [halg]
    exact hpsiError
  have hpolarC :
      criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta (x * y) =
        (psi.character ((beta : F) * ((delta : F) ^ 2 * (tx * ty)) /
          ((Gamma : Fˣ) : F)) : ℂ) := by
    convert hpolar using 1 <;> ring
  rw [criticalPolarValue, criticalPolarFunction, criticalPolarFunction,
    hsumPsi, hpolarC, hquadPsiC]
  have hcx0 :
      (chi.character
        (criticalPolarUnit F chi d hm hlarge delta hdelta tx htx) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero _ _
  have hcy0 :
      (chi.character
        (criticalPolarUnit F chi d hm hlarge delta hdelta ty hty) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero _ _
  have hcs0 : (chi.character (us : Fˣ) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero _ _
  change
    (psi.character ((beta : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) *
        (psi.character ((beta : F) * (delta : F) * ty / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character (us : Fˣ) : ℂ)⁻¹ =
      ((psi.character ((beta : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character
            (criticalPolarUnit F chi d hm hlarge delta hdelta tx htx) : ℂ)⁻¹) *
        ((psi.character ((beta : F) * (delta : F) * ty / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character
            (criticalPolarUnit F chi d hm hlarge delta hdelta ty hty) : ℂ)⁻¹) *
        (psi.character ((beta : F) * w / ((Gamma : Fˣ) : F)) : ℂ)
  field_simp [hcx0, hcy0, hcs0]
  rw [hchi]

/-- Coefficient form of the positive polar identity.  In particular the sign
is `+A*x*y`, not its negative. -/
theorem criticalPolarFunction_positivePolar
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x y : ResidueField F) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta (x + y) =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x *
        criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta y *
        psi0
          (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
            psi0 hpsi0 * (x * y)) := by
  rw [criticalPolarFunction_map_add F chi psi d hm hlarge Gamma delta hdelta
    beta hbeta x y]
  congr 1
  symm
  exact finiteAddCharCoefficient_apply psi0 hpsi0
    (criticalPolarAddChar F chi psi d hm hlarge Gamma delta hdelta) (x * y)

/-! ### The complete critical coordinate and its odd specialization -/

/-- The complete residue-field critical function is nowhere zero. -/
theorem criticalPolarFunction_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (x : ResidueField F) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x ≠ 0 :=
  criticalPolarValue_ne_zero F chi psi d hm hlarge Gamma delta hdelta beta
    (teichmuller F x : F)
    ((mem_lattice_zero_iff F).2 (teichmuller F x).property)

/-- The local critical function bundled with its exact quotient-derived polar
coefficient.  The stationary representative remains an explicit argument. -/
noncomputable def criticalPolarData
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    CriticalPolarFunction (ResidueField F) psi0
      (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
        psi0 hpsi0) where
  toFun := criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta
  ne_zero' := criticalPolarFunction_ne_zero F chi psi d hm hlarge Gamma delta
    hdelta beta
  map_add' := criticalPolarFunction_positivePolar F chi psi d hm hlarge Gamma
    delta hdelta psi0 hpsi0 beta hbeta

@[simp]
theorem criticalPolarData_apply
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField F) :
    criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
        beta hbeta x =
      criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x :=
  rfl

/-- The affine coefficient `B` of the complete odd-characteristic critical
function.  Unlike the polar coefficient, this depends on the supplied
stationary representative. -/
noncomputable def criticalAffineCoefficient
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) : ResidueField F :=
  (criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
    beta hbeta).affineCoefficient hchar hpsi0

/-- Exact odd-characteristic specialization of the complete critical
function to the certified quadratic polynomial coordinate. -/
theorem criticalPolarFunction_eq_quadratic
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (x : ResidueField F) :
    criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x =
      psi0
        (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
              psi0 hpsi0 / 2 * x ^ 2 +
          criticalAffineCoefficient F chi psi d hm hlarge Gamma delta hdelta
              psi0 hpsi0 hchar beta hbeta * x) :=
  (criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
    beta hbeta).eq_quadratic hchar hpsi0 x

/-- The complete critical sum has exactly the certified quadratic phase.
This equality transports the elementary stationary value and the residual
phase together; no completing-square factor is removed here. -/
theorem criticalPolarFunction_phase_eq_quadraticPhase
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (beta : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    phase (∑ x : ResidueField F,
        criticalPolarFunction F chi psi d hm hlarge Gamma delta hdelta beta x) =
      quadraticPhase psi0
        (criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0)
        (criticalAffineCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0 hchar beta hbeta) :=
  (criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
    beta hbeta).phase_sum_eq_quadraticPhase hchar hpsi0

/-- In odd residue characteristic, replacing the stationary representative
changes the affine coefficient by exactly `+Delta B` and leaves the polar
coefficient (which has no representative argument) unchanged. -/
theorem criticalAffineCoefficient_changeRepresentative
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalAffineCoefficient F chi psi d hm hlarge Gamma delta hdelta
        psi0 hpsi0 hchar beta' hbeta' =
      criticalAffineCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0 hchar beta hbeta +
        criticalAffineTranslationCoefficient F chi psi d hm Gamma delta
          hdelta psi0 hpsi0
            (criticalStationaryRepresentativeDifference F chi psi d hm
              hlarge Gamma beta beta' hbeta hbeta') := by
  let DeltaB := criticalAffineTranslationCoefficient F chi psi d hm Gamma
    delta hdelta psi0 hpsi0
      (criticalStationaryRepresentativeDifference F chi psi d hm hlarge
        Gamma beta beta' hbeta hbeta')
  have hdata :
      criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
          beta' hbeta' =
        (criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
          beta hbeta).translate DeltaB := by
    apply CriticalPolarFunction.ext
    intro x
    exact criticalPolarFunction_changeRepresentative F chi psi d hm hlarge
      Gamma delta hdelta psi0 hpsi0 beta beta' hbeta hbeta' x
  change
    (criticalPolarData F chi psi d hm hlarge Gamma delta hdelta psi0 hpsi0
        beta' hbeta').affineCoefficient hchar hpsi0 = _
  rw [hdata, CriticalPolarFunction.affineCoefficient_translate]
  rfl

/-- Equivalent representative-translation formula in terms of the distinct
translation parameter `a`: `B' = B + A*a`. -/
theorem criticalAffineCoefficient_changeRepresentative_eq_add_polar_mul_parameter
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (beta beta' : lattice F
      ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property)
    (hbeta' : latticeQuotientMk F
        (sub_le_sub_left
          (criticalPolar_stationaryDepth F chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth F chi d hm hlarge)
        Gamma Gamma.property) :
    criticalAffineCoefficient F chi psi d hm hlarge Gamma delta hdelta
        psi0 hpsi0 hchar beta' hbeta' =
      criticalAffineCoefficient F chi psi d hm hlarge Gamma delta hdelta
          psi0 hpsi0 hchar beta hbeta +
        criticalPolarCoefficient F chi psi d hm hlarge Gamma delta hdelta
            psi0 hpsi0 *
          criticalRepresentativeTranslationParameter F chi psi d hm hlarge
            Gamma delta hdelta beta beta' hbeta hbeta' := by
  rw [criticalAffineCoefficient_changeRepresentative F chi psi d hm hlarge
      Gamma delta hdelta psi0 hpsi0 hchar beta beta' hbeta hbeta',
    criticalRepresentativeAffineCoefficient_eq_polar_mul_parameter F chi psi d
      hm hlarge Gamma delta hdelta psi0 hpsi0 beta beta' hbeta hbeta']

end LocalPolarCharacter

end

end LanglandsFirstMainLemma
