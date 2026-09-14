import LanglandsFirstMainLemma.Prelude

namespace LanglandsFirstMainLemma

open ComplexConjugate

/--
The total complex phase used in the definition of Langlands's local constant.

The value at zero is defined to be one.  Away from zero, this is the complex
number divided by its absolute value (represented in Lean by the complex norm).
-/
noncomputable def phase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

/-- The total phase takes the prescribed value one at zero. -/
@[simp]
theorem phase_zero : phase 0 = 1 := by
  simp [phase]

/-- Away from zero, the total phase is division by the complex absolute value. -/
theorem phase_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    phase z = z / (‖z‖ : ℂ) := by
  simp [phase, hz]

/-- The total phase is always nonzero, including at its totalized zero branch. -/
@[simp]
theorem phase_ne_zero (z : ℂ) : phase z ≠ 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [phase_of_ne_zero hz]
    exact div_ne_zero hz (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

/-- Every value of the total phase has complex absolute value one. -/
@[simp]
theorem phase_norm (z : ℂ) : ‖phase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [phase_of_ne_zero hz, norm_div, Complex.norm_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr hz)

/-- The phase of a complex number already having absolute value one is itself. -/
theorem phase_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : phase z = z := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  rw [phase_of_ne_zero hz0, hz]
  simp

/--
The phase of a product of two nonzero complex numbers is the product of their
phases.  Both nonzero hypotheses are necessary for the total phase.
-/
theorem phase_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    phase (z * w) = phase z * phase w := by
  rw [phase_of_ne_zero (mul_ne_zero hz hw), phase_of_ne_zero hz,
    phase_of_ne_zero hw, norm_mul, Complex.ofReal_mul]
  exact mul_div_mul_comm z w (‖z‖ : ℂ) (‖w‖ : ℂ)

/--
Multiplication by a complex scalar of absolute value one transports the phase
of a nonzero number by that scalar.
-/
theorem phase_mul_of_norm_eq_one {u z : ℂ} (hu : ‖u‖ = 1) (hz : z ≠ 0) :
    phase (u * z) = u * phase z := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp at hu
  rw [phase_mul hu0 hz, phase_of_norm_eq_one hu]

/-- The total phase commutes with every natural power, including at zero. -/
@[simp]
theorem phase_pow (z : ℂ) (n : ℕ) : phase (z ^ n) = phase z ^ n := by
  by_cases hz : z = 0
  · subst z
    cases n <;> simp [phase]
  · rw [phase_of_ne_zero (pow_ne_zero n hz), phase_of_ne_zero hz,
      norm_pow, Complex.ofReal_pow]
    exact (div_pow z (‖z‖ : ℂ) n).symm

/-- The total phase commutes with complex conjugation. -/
@[simp]
theorem phase_conj (z : ℂ) : phase (conj z) = conj (phase z) := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [phase_of_ne_zero (by simpa using hz), phase_of_ne_zero hz,
      Complex.norm_conj, map_div₀, Complex.conj_ofReal]

/-- A positive real number, viewed in the complex numbers, has phase one. -/
theorem phase_ofReal_pos {r : ℝ} (hr : 0 < r) : phase (r : ℂ) = 1 := by
  rw [phase_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.norm_of_nonneg hr.le]
  exact div_self (Complex.ofReal_ne_zero.mpr hr.ne')

/-- Positive real scaling does not change the total phase. -/
theorem phase_smul_of_pos (r : ℝ) (hr : 0 < r) (z : ℂ) :
    phase (r • z) = phase z := by
  rw [Complex.real_smul]
  by_cases hz : z = 0
  · subst z
    simp
  · rw [phase_mul (Complex.ofReal_ne_zero.mpr hr.ne') hz,
      phase_ofReal_pos hr, one_mul]

end LanglandsFirstMainLemma
