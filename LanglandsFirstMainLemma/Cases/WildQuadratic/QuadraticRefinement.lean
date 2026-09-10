import LanglandsFirstMainLemma.FiniteField.CharTwoRefinement
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier

/-!
# Characteristic-two refinements for the wild quadratic calculation

This file gives the later wild-quadratic nodes a sign-sensitive interface to the
certified characteristic-two refinement theory.  The finite field `k` is the common
residue field.  In particular, the polar character is the positive character
`absoluteTraceChar k (x * y)`, affine coefficients act by multiplication on the
argument, and a residual correction is the complete value of the affine critical
function, not its inverse or conjugate.

No local-field parameter theorem and no later wild-quadratic node is used here.
-/

open scoped ComplexConjugate

namespace LanglandsFirstMainLemma

universe u

section CommonResidueField

variable {k : Type u} [Field k] [Fintype k] [CharP k 2]

local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

namespace WildQuadraticRefinement

/-! ## The four affine critical functions -/

/-- The common-residue-field critical function
`h_lambda(z) = q(z) * psi_0(lambda * z)`. -/
noncomputable def criticalFunction
    (q : CharTwoRefinement k) (lambda : k) :
    HasseFunction k (absoluteTraceChar k) :=
  q.affine lambda

@[simp]
theorem criticalFunction_apply
    (q : CharTwoRefinement k) (lambda z : k) :
    criticalFunction q lambda z =
      q z * absoluteTraceChar k (lambda * z) :=
  rfl

/-- The critical function for `tau`, whose affine coefficient is `gamma_0`. -/
noncomputable def tauCriticalFunction
    (q : CharTwoRefinement k) (gamma0 : k) :
    HasseFunction k (absoluteTraceChar k) :=
  criticalFunction q gamma0

/-- The critical function for `chi_F`, whose affine coefficient is `gamma`. -/
noncomputable def chiCriticalFunction
    (q : CharTwoRefinement k) (gamma : k) :
    HasseFunction k (absoluteTraceChar k) :=
  criticalFunction q gamma

/-- The critical function for `tau * chi_F`, whose affine coefficient is `gamma_1`. -/
noncomputable def tauChiCriticalFunction
    (q : CharTwoRefinement k) (gamma1 : k) :
    HasseFunction k (absoluteTraceChar k) :=
  criticalFunction q gamma1

/-- The normalized critical function for `chi_K`, whose affine coefficient is
`gamma'`. -/
noncomputable def chiKCriticalFunction
    (q : CharTwoRefinement k) (gammaPrime : k) :
    HasseFunction k (absoluteTraceChar k) :=
  criticalFunction q gammaPrime

@[simp]
theorem tauCriticalFunction_apply
    (q : CharTwoRefinement k) (gamma0 z : k) :
    tauCriticalFunction q gamma0 z =
      q z * absoluteTraceChar k (gamma0 * z) :=
  rfl

@[simp]
theorem chiCriticalFunction_apply
    (q : CharTwoRefinement k) (gamma z : k) :
    chiCriticalFunction q gamma z =
      q z * absoluteTraceChar k (gamma * z) :=
  rfl

@[simp]
theorem tauChiCriticalFunction_apply
    (q : CharTwoRefinement k) (gamma1 z : k) :
    tauChiCriticalFunction q gamma1 z =
      q z * absoluteTraceChar k (gamma1 * z) :=
  rfl

@[simp]
theorem chiKCriticalFunction_apply
    (q : CharTwoRefinement k) (gammaPrime z : k) :
    chiKCriticalFunction q gammaPrime z =
      q z * absoluteTraceChar k (gammaPrime * z) :=
  rfl

/-! ## Normalization, affine direction, and the two choices -/

/-- Every positive-polar Hasse function on the common residue field admits a
Frobenius-normalized affine twist.  The equality direction records which twist was
used. -/
theorem exists_normalized
    (h : HasseFunction k (absoluteTraceChar k)) :
    ∃ (q : CharTwoRefinement k) (d : k),
      q.toHasseFunction = h.translate d :=
  CharTwoRefinement.exists_charTwoRefinement_translate h

/-- The polar sign used throughout the wild quadratic calculation is positive. -/
theorem positive_polar
    (q : CharTwoRefinement k) (x y : k) :
    q (x + y) = q x * q y * absoluteTraceChar k (x * y) :=
  q.map_add x y

/-- The chosen refinement is invariant under the characteristic-two Frobenius. -/
@[simp]
theorem frobenius_normalized
    (q : CharTwoRefinement k) (x : k) :
    q (x ^ 2) = q x :=
  q.map_sq x

/-- Every same-polar critical function has one and only one affine coefficient in
the displayed positive direction. -/
theorem existsUnique_criticalFunction
    (q : CharTwoRefinement k)
    (h : HasseFunction k (absoluteTraceChar k)) :
    ∃! lambda : k, criticalFunction q lambda = h := by
  simpa only [criticalFunction] using q.existsUnique_affine h

/-- Precomposition by Frobenius sends an affine coefficient to inverse Frobenius,
i.e. to its unique square root. -/
theorem criticalFunction_frobenius
    (q : CharTwoRefinement k) (lambda z : k) :
    criticalFunction q lambda (z ^ 2) =
      criticalFunction q
        ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k).symm lambda) z :=
  q.affine_frobenius lambda z

/-- If `gammaPrime^2 = L`, Frobenius precomposition changes the raw coefficient
`L` into the normalized coefficient `gammaPrime`, in this direction. -/
theorem criticalFunction_frobenius_of_sq
    (q : CharTwoRefinement k) {gammaPrime L : k}
    (hgamma : gammaPrime ^ 2 = L) (z : k) :
    criticalFunction q L (z ^ 2) =
      criticalFunction q gammaPrime z := by
  rw [← hgamma]
  simp only [criticalFunction_apply, q.map_sq, ← mul_pow,
    absoluteTraceChar_sq]

/-- The unique square root used at the wild quadratic boundary. -/
noncomputable def squareRoot (rho : k) : k :=
  (existsUnique_squareRoot k rho).choose

@[simp]
theorem squareRoot_sq (rho : k) : squareRoot rho ^ 2 = rho :=
  (existsUnique_squareRoot k rho).choose_spec.1

/-- There is no hidden second square-root choice in characteristic two. -/
theorem squareRoot_unique (rho r : k) (hr : r ^ 2 = rho) :
    r = squareRoot rho :=
  (existsUnique_squareRoot k rho).choose_spec.2 r hr

/-- The other normalized refinement is the nontrivial prime-field affine twist. -/
noncomputable def secondNormalized
    (q : CharTwoRefinement k) : CharTwoRefinement k :=
  q.translateOne

@[simp]
theorem secondNormalized_apply
    (q : CharTwoRefinement k) (z : k) :
    secondNormalized q z = q z * absoluteTraceChar k z :=
  q.translateOne_apply z

/-- Relative to `q`, every normalized refinement is either `q` or the distinct
prime-field twist `secondNormalized q`. -/
theorem normalized_eq_or_eq_second
    (q r : CharTwoRefinement k) :
    r = q ∨ r = secondNormalized q := by
  simpa only [secondNormalized] using q.eq_or_eq_translateOne r

/-- The two Frobenius-normalized refinements are not identified. -/
theorem secondNormalized_ne
    (q : CharTwoRefinement k) : secondNormalized q ≠ q :=
  q.translateOne_ne

/-- Changing from `q` to the other normalized choice changes the affine coefficient
from `lambda` to `lambda + 1`; the underlying critical function is unchanged. -/
theorem secondNormalized_criticalFunction
    (q : CharTwoRefinement k) (lambda : k) :
    criticalFunction (secondNormalized q) (lambda + 1) =
      criticalFunction q lambda := by
  apply HasseFunction.ext
  intro z
  simp only [criticalFunction_apply, secondNormalized_apply]
  rw [mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  calc
    z + (lambda + 1) * z = lambda * z + (z + z) := by ring
    _ = lambda * z := by rw [CharTwo.add_self_eq_zero, add_zero]

/-! ## Complete correction values and phase translation -/

/-- The finite correction is the complete positively oriented critical-function
value. -/
noncomputable def correctionValue
    (q : CharTwoRefinement k) (lambda c : k) : ℂ :=
  q.correctionValue lambda c

@[simp]
theorem correctionValue_apply
    (q : CharTwoRefinement k) (lambda c : k) :
    correctionValue q lambda c =
      q c * absoluteTraceChar k (lambda * c) :=
  rfl

/-- The correction value is the affine function itself, not its inverse or
conjugate. -/
theorem correctionValue_eq_criticalFunction
    (q : CharTwoRefinement k) (lambda c : k) :
    correctionValue q lambda c = criticalFunction q lambda c :=
  rfl

/-- Exact affine-translation identity with the coefficient and addition directions
fixed. -/
theorem correctionValue_eq_inv_mul
    (q : CharTwoRefinement k) (lambda c : k) :
    correctionValue q lambda c =
      (q lambda)⁻¹ * q (c + lambda) :=
  q.correction_rule lambda c

/-- The paired coefficient shift makes the complete correction value independent of
which of the two normalized refinements is used. -/
theorem secondNormalized_correctionValue
    (q : CharTwoRefinement k) (lambda c : k) :
    correctionValue (secondNormalized q) (lambda + 1) c =
      correctionValue q lambda c := by
  rw [correctionValue_eq_criticalFunction, correctionValue_eq_criticalFunction]
  exact DFunLike.congr_fun (secondNormalized_criticalFunction q lambda) c

/-- The phase of the complete finite sum attached to an affine critical function. -/
noncomputable def phase
    (q : CharTwoRefinement k) (lambda : k) : ℂ :=
  q.affinePhase lambda

/-- Translation of the phase alone contains the inverse correction value. -/
theorem phase_add
    (q : CharTwoRefinement k) (lambda c : k) :
    phase q (lambda + c) =
      (correctionValue q lambda c)⁻¹ * phase q lambda := by
  simpa only [phase, correctionValue,
    CharTwoRefinement.correctionValue_eq_affine]
    using q.affinePhase_add lambda c

/-- The exact correction-translation rule: the complete positive correction value
and its translated phase must be transported together. -/
theorem correction_phase_translation
    (q : CharTwoRefinement k) (lambda c : k) :
    correctionValue q lambda c * phase q (lambda + c) =
      phase q lambda :=
  q.correction_phase_rule lambda c

/-- The phase is unchanged after the paired coefficient shift between the two
normalized choices. -/
theorem secondNormalized_phase
    (q : CharTwoRefinement k) (lambda : k) :
    phase (secondNormalized q) (lambda + 1) = phase q lambda := by
  change (criticalFunction (secondNormalized q) (lambda + 1)).sumPhase =
    (criticalFunction q lambda).sumPhase
  rw [secondNormalized_criticalFunction]

/-! ## Frobenius-normalized phase identities -/

/-- The exact phase translation `H(lambda) = H(0) * conj(q(lambda))`. -/
theorem phase_eq
    (q : CharTwoRefinement k) (lambda : k) :
    phase q lambda = phase q 0 * conj (q lambda) :=
  q.affinePhase_eq lambda

/-- The square of the base phase retains the refinement value `q(1)`. -/
theorem phase_zero_sq
    (q : CharTwoRefinement k) :
    phase q 0 ^ 2 = q 1 :=
  q.affinePhase_zero_sq

/-- The phase square retains the exact Artin--Schreier sign. -/
theorem phase_sq
    (q : CharTwoRefinement k) (lambda : k) :
    phase q lambda ^ 2 =
      q 1 * absoluteTraceChar k lambda :=
  q.affinePhase_sq lambda

/-- Frobenius does not change the affine phase. -/
@[simp]
theorem phase_frobenius
    (q : CharTwoRefinement k) (lambda : k) :
    phase q (lambda ^ 2) = phase q lambda :=
  q.affinePhase_sq_arg lambda

/-- If `gammaPrime^2=L`, the normalized and raw coefficients have the same phase. -/
theorem phase_eq_of_sq
    (q : CharTwoRefinement k) {gammaPrime L : k}
    (hgamma : gammaPrime ^ 2 = L) :
    phase q gammaPrime = phase q L := by
  calc
    phase q gammaPrime = phase q (gammaPrime ^ 2) :=
      (phase_frobenius q gammaPrime).symm
    _ = phase q L := congrArg (phase q) hgamma

/-- The exact two-phase Frobenius-normalized cancellation. -/
theorem phase_pair
    (q : CharTwoRefinement k) (lambda : k) :
    phase q (1 + lambda) * phase q lambda = 1 :=
  q.affinePhase_pair lambda

/-! ## Boundary-coordinate affine identities -/

/-- The characteristic-two phase converts `rho * z^2` to `r * z` when
`r^2 = rho`.  This fixes the square-root direction used by the coefficient table. -/
theorem absoluteTraceChar_mul_sq_of_sq
    {rho r : k} (hr : r ^ 2 = rho) (z : k) :
    absoluteTraceChar k (rho * z ^ 2) =
      absoluteTraceChar k (r * z) := by
  calc
    absoluteTraceChar k (rho * z ^ 2) =
        absoluteTraceChar k ((r * z) ^ 2) := by
          congr 1
          rw [mul_pow, hr]
    _ = absoluteTraceChar k (r * z) := absoluteTraceChar_sq k _

/-- Multiplying the two scaled refinement values retains the positive `+r` phase. -/
theorem value_mul_scale_root
    (q : CharTwoRefinement k) (rho r z : k) (hr : r ^ 2 = rho) :
    q z * q (rho * z) =
      q ((1 + rho) * z) * absoluteTraceChar k (r * z) := by
  calc
    q z * q (rho * z) =
        q ((1 + rho) * z) * absoluteTraceChar k (rho * z ^ 2) := by
      rw [q.value_mul]
      congr 2 <;> ring
    _ = q ((1 + rho) * z) * absoluteTraceChar k (r * z) := by
      rw [absoluteTraceChar_mul_sq_of_sq hr]

/-- Below the break, the raw upper critical function is `h_gamma`. -/
noncomputable def rawUpperBelow
    (q : CharTwoRefinement k) (gamma z : k) : ℂ :=
  criticalFunction q gamma z

/-- Above the break, the raw upper critical function is `h_(1+gamma_0)`. -/
noncomputable def rawUpperAbove
    (q : CharTwoRefinement k) (gamma0 z : k) : ℂ :=
  criticalFunction q (1 + gamma0) z

/-- At the boundary, the two lower functions are evaluated in the common coordinate
as `h_(gamma_0)(z)` and `h_gamma(rho*z)`. -/
noncomputable def boundaryLowerProduct
    (q : CharTwoRefinement k) (rho gamma0 gamma z : k) : ℂ :=
  criticalFunction q gamma0 z * criticalFunction q gamma (rho * z)

/-- The raw upper boundary function, with its positive final
`psi_0(rho*z)` factor. -/
noncomputable def rawUpperBoundary
    (q : CharTwoRefinement k) (rho gamma0 gamma z : k) : ℂ :=
  criticalFunction q gamma z * criticalFunction q gamma0 (rho * z) *
    absoluteTraceChar k (rho * z)

/-- Exact lower boundary coordinate identity.  The affine coefficient is divided by
`1+rho` in the displayed direction, and the `+r` term is retained. -/
theorem boundaryLowerProduct_eq_affine
    (q : CharTwoRefinement k) (rho r gamma0 gamma z : k)
    (hr : r ^ 2 = rho) (hrho : 1 + rho ≠ 0) :
    boundaryLowerProduct q rho gamma0 gamma z =
      criticalFunction q
        ((gamma0 + rho * gamma + r) / (1 + rho)) ((1 + rho) * z) := by
  simp only [boundaryLowerProduct, criticalFunction_apply]
  calc
    (q z * absoluteTraceChar k (gamma0 * z)) *
        (q (rho * z) * absoluteTraceChar k (gamma * (rho * z))) =
      (q z * q (rho * z)) *
        (absoluteTraceChar k (gamma0 * z) *
          absoluteTraceChar k (gamma * (rho * z))) := by ring
    _ = (q ((1 + rho) * z) * absoluteTraceChar k (r * z)) *
        absoluteTraceChar k (gamma0 * z + gamma * (rho * z)) := by
      rw [value_mul_scale_root q rho r z hr, ← AddChar.map_add_eq_mul]
    _ = q ((1 + rho) * z) *
        absoluteTraceChar k
          (((gamma0 + rho * gamma + r) / (1 + rho)) *
            ((1 + rho) * z)) := by
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      field_simp
      ring

/-- Exact raw upper boundary coordinate identity.  It retains both `+rho` and `+r`
in the affine numerator. -/
theorem rawUpperBoundary_eq_affine
    (q : CharTwoRefinement k) (rho r gamma0 gamma z : k)
    (hr : r ^ 2 = rho) (hrho : 1 + rho ≠ 0) :
    rawUpperBoundary q rho gamma0 gamma z =
      criticalFunction q
        ((gamma + rho * gamma0 + rho + r) / (1 + rho))
          ((1 + rho) * z) := by
  change boundaryLowerProduct q rho gamma gamma0 z *
      absoluteTraceChar k (rho * z) = _
  rw [boundaryLowerProduct_eq_affine q rho r gamma gamma0 z hr hrho]
  simp only [criticalFunction_apply]
  rw [mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  field_simp
  ring

/-! ## Signed four-phase and Artin--Schreier identities -/

/-- Exact signed four-phase quotient, with `a,b` in the numerator and `c,d` in the
denominator. -/
theorem phase_four
    (q : CharTwoRefinement k) (a b c d A : k)
    (hsum : c + d = a + b + A) :
    phase q a * phase q b / (phase q c * phase q d) =
      q A * absoluteTraceChar k ((a + b) * A + c * d + a * b) :=
  q.affinePhase_four a b c d A hsum

/-- Multiplying the four-phase quotient by the two complete positive correction
values leaves the displayed binary phase. -/
theorem phase_four_correction
    (q : CharTwoRefinement k) (a b c d A B C : k)
    (hsum : c + d = a + b + A) (hBC : B + C = A) :
    (phase q a * phase q b / (phase q c * phase q d)) * q B * q C =
      absoluteTraceChar k
        (((a + b) * A + c * d + a * b) + A + B * C) :=
  q.affinePhase_four_correction a b c d A B C hsum hBC

/-- The characteristic-two Artin--Schreier sign is exactly the plus-sign expression
`z + z^2`. -/
@[simp]
theorem artinSchreier_sign (z : k) :
    absoluteTraceChar k (z + z ^ 2) = 1 :=
  artinSchreier_phase k z

/-- Denominator-free boundary cancellation after the exact Artin--Schreier residual
identity. -/
theorem phase_four_cancel
    (q : CharTwoRefinement k) (a b c d A B C t z : k)
    (hsum : c + d = a + b + A) (hBC : B + C = A)
    (hAS : ((a + b) * A + c * d + a * b) + A + B * C + t =
      z + z ^ 2) :
    phase q a * phase q b * q B * q C * absoluteTraceChar k t =
      phase q c * phase q d :=
  q.affinePhase_four_cancel a b c d A B C t z hsum hBC hAS

end WildQuadraticRefinement

/-! ## Principal API -/

/-- Principal specialization of the certified characteristic-two refinement theory to
the common residue field in the wild quadratic calculation.  It records the positive
polar sign, Frobenius normalization, the two distinct normalized choices, the full
correction value, its exact phase translation, and the plus-sign Artin--Schreier
normalization. -/
theorem wildQuadratic_refinement
    (q : CharTwoRefinement k) :
    (∀ x y : k,
      q (x + y) = q x * q y * absoluteTraceChar k (x * y)) ∧
    (∀ x : k, q (x ^ 2) = q x) ∧
    (∀ r : CharTwoRefinement k,
      r = q ∨ r = WildQuadraticRefinement.secondNormalized q) ∧
    WildQuadraticRefinement.secondNormalized q ≠ q ∧
    (∀ lambda c : k,
      WildQuadraticRefinement.correctionValue q lambda c =
        q c * absoluteTraceChar k (lambda * c)) ∧
    (∀ lambda c : k,
      WildQuadraticRefinement.correctionValue q lambda c *
          WildQuadraticRefinement.phase q (lambda + c) =
        WildQuadraticRefinement.phase q lambda) ∧
    (∀ lambda : k,
      WildQuadraticRefinement.phase q (lambda ^ 2) =
        WildQuadraticRefinement.phase q lambda) ∧
    (∀ z : k, absoluteTraceChar k (z + z ^ 2) = 1) := by
  exact ⟨WildQuadraticRefinement.positive_polar q,
    WildQuadraticRefinement.frobenius_normalized q,
    WildQuadraticRefinement.normalized_eq_or_eq_second q,
    WildQuadraticRefinement.secondNormalized_ne q,
    WildQuadraticRefinement.correctionValue_apply q,
    WildQuadraticRefinement.correction_phase_translation q,
    WildQuadraticRefinement.phase_frobenius q,
    WildQuadraticRefinement.artinSchreier_sign⟩

end CommonResidueField

end LanglandsFirstMainLemma
