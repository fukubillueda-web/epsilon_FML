import LanglandsFirstMainLemma.FiniteField.HasseFunction
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier

/-!
# Normalized quadratic refinements in characteristic two

This file isolates the finite-field content of the normalized characteristic-two
refinement used in the wild quadratic calculation.  The polar character is exactly
`absoluteTraceChar k`, and normalization means invariance under Frobenius.  No local-field
conductor, break-parity, or wild-quadratic conclusion is used here.
-/

open scoped BigOperators ComplexConjugate

namespace LanglandsFirstMainLemma

universe u

section CharacteristicTwo

variable {k : Type u} [Field k] [Fintype k] [CharP k 2]

local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- A one-dimensional quadratic refinement of the normalized absolute-trace character,
fixed by the characteristic-two Frobenius. -/
structure CharTwoRefinement (k : Type u) [Field k] [Fintype k] [CharP k 2] where
  /-- The underlying Hasse function with positive polar character `ψ₀(xy)`. -/
  toHasseFunction : HasseFunction k (absoluteTraceChar k)
  /-- The normalization `q(x²) = q(x)`. -/
  map_sq' : ∀ x : k, toHasseFunction (x ^ 2) = toHasseFunction x

namespace CharTwoRefinement

noncomputable instance : FunLike (CharTwoRefinement k) k ℂ where
  coe q := q.toHasseFunction
  coe_injective q q' h := by
    cases q
    cases q'
    simp_all

@[ext]
theorem ext (q q' : CharTwoRefinement k) (h : ∀ x, q x = q' x) : q = q' :=
  DFunLike.ext q q' h

/-- Values of a normalized refinement never vanish. -/
theorem ne_zero (q : CharTwoRefinement k) (x : k) : q x ≠ 0 :=
  q.toHasseFunction.ne_zero x

/-- The positive-polar functional equation. -/
theorem map_add (q : CharTwoRefinement k) (x y : k) :
    q (x + y) = q x * q y * absoluteTraceChar k (x * y) :=
  q.toHasseFunction.map_add x y

/-- A normalized refinement takes the value one at zero. -/
@[simp]
theorem map_zero (q : CharTwoRefinement k) : q 0 = 1 :=
  q.toHasseFunction.map_zero

/-- Frobenius normalization. -/
@[simp]
theorem map_sq (q : CharTwoRefinement k) (x : k) : q (x ^ 2) = q x :=
  q.map_sq' x

/-- Every value of a normalized refinement is unimodular. -/
@[simp]
theorem norm_apply (q : CharTwoRefinement k) (x : k) : ‖q x‖ = 1 :=
  q.toHasseFunction.norm_apply x

/-- The affine family `h_λ(x) = q(x) ψ₀(λx)`. -/
noncomputable def affine (q : CharTwoRefinement k) (lambda : k) :
    HasseFunction k (absoluteTraceChar k) :=
  q.toHasseFunction.translate lambda

@[simp]
theorem affine_apply (q : CharTwoRefinement k) (lambda x : k) :
    q.affine lambda x = q x * absoluteTraceChar k (lambda * x) :=
  rfl

/-- The exact affine translation, with the inverse value in the manuscript's orientation. -/
theorem affine_apply_eq_inv_mul (q : CharTwoRefinement k) (lambda x : k) :
    q.affine lambda x = (q lambda)⁻¹ * q (x + lambda) :=
  q.toHasseFunction.translate_apply_eq_inv_mul lambda x

/-- The finite residual correction value on an odd critical line.  The value is the full
affine function, not its inverse or conjugate. -/
noncomputable def correctionValue (q : CharTwoRefinement k) (lambda c : k) : ℂ :=
  q c * absoluteTraceChar k (lambda * c)

@[simp]
theorem correctionValue_eq_affine (q : CharTwoRefinement k) (lambda c : k) :
    q.correctionValue lambda c = q.affine lambda c :=
  rfl

/-- Purely finite-field form of the correction rule.  A local linear phase, when later
supplied, must be multiplied by this complete positively oriented value. -/
theorem correction_rule (q : CharTwoRefinement k) (lambda c : k) :
    q.correctionValue lambda c = (q lambda)⁻¹ * q (c + lambda) := by
  rw [correctionValue_eq_affine, affine_apply_eq_inv_mul]

/-- Frobenius normalization as a predicate on an arbitrary Hasse function. -/
def IsFrobeniusNormalized
    (h : HasseFunction k (absoluteTraceChar k)) : Prop :=
  ∀ x : k, h (x ^ 2) = h x

/-- The quotient of two refinements with the same polar character is additive. -/
noncomputable def relativeCharacter
    (q : CharTwoRefinement k) (h : HasseFunction k (absoluteTraceChar k)) :
    FiniteAddChar k where
  toFun x := h x / q x
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [h.map_add, q.map_add]
    field_simp [q.ne_zero x, q.ne_zero y,
      (AddChar.val_isUnit (absoluteTraceChar k) (x * y)).ne_zero]

@[simp]
theorem relativeCharacter_apply
    (q : CharTwoRefinement k) (h : HasseFunction k (absoluteTraceChar k)) (x : k) :
    relativeCharacter q h x = h x / q x :=
  rfl

/-- Every refinement with this polar character is uniquely one member of the affine
family based at `q`. -/
theorem existsUnique_affine
    (q : CharTwoRefinement k) (h : HasseFunction k (absoluteTraceChar k)) :
    ∃! lambda : k, q.affine lambda = h := by
  obtain ⟨lambda, hlambda, hunique⟩ :=
    existsUnique_absoluteTraceChar_mulShift k (relativeCharacter q h)
  refine ⟨lambda, ?_, ?_⟩
  · apply HasseFunction.ext
    intro x
    have hx := DFunLike.congr_fun hlambda x
    change absoluteTraceChar k (lambda * x) = h x / q x at hx
    rw [affine_apply, hx]
    field_simp [q.ne_zero x]
  · intro mu hmu
    apply hunique mu
    apply AddChar.ext
    intro x
    have hx := DFunLike.congr_fun hmu x
    change q x * absoluteTraceChar k (mu * x) = h x at hx
    change absoluteTraceChar k (mu * x) = h x / q x
    field_simp [q.ne_zero x]
    simpa [mul_comm] using hx

/-- The Frobenius defect `h(x²)/h(x)` of an arbitrary refinement is an additive
character. -/
noncomputable def frobeniusDefect
    (h : HasseFunction k (absoluteTraceChar k)) : FiniteAddChar k where
  toFun x := h (x ^ 2) / h x
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [CharTwo.add_sq, h.map_add, h.map_add]
    rw [show x ^ 2 * y ^ 2 = (x * y) ^ 2 by ring, absoluteTraceChar_sq]
    field_simp [h.ne_zero x, h.ne_zero y,
      (AddChar.val_isUnit (absoluteTraceChar k) (x * y)).ne_zero]

@[simp]
theorem frobeniusDefect_apply
    (h : HasseFunction k (absoluteTraceChar k)) (x : k) :
    frobeniusDefect h x = h (x ^ 2) / h x :=
  rfl

omit [Fintype k] in
/-- For the normalized binary character, value one is exactly trace zero. -/
theorem absoluteTraceChar_eq_one_iff (x : k) :
    absoluteTraceChar k x = 1 ↔ absoluteTraceTwo k x = 0 := by
  rw [absoluteTraceChar_apply]
  generalize absoluteTraceTwo k x = t
  constructor
  · intro hp
    apply (ZMod.val_eq_zero t).mp
    by_contra ht
    have hlt := t.val_lt
    have ht1 : t.val = 1 := by omega
    rw [ht1] at hp
    norm_num at hp
  · intro ht
    subst t
    rfl

/-- Every positive-polar Hasse function can be normalized by an affine twist.  The
normalizing coefficient uses inverse Frobenius, exactly as in the manuscript. -/
theorem exists_charTwoRefinement_translate
    (h : HasseFunction k (absoluteTraceChar k)) :
    ∃ (q : CharTwoRefinement k) (d : k), q.toHasseFunction = h.translate d := by
  obtain ⟨c, hc, _⟩ :=
    existsUnique_absoluteTraceChar_mulShift k (frobeniusDefect h)
  have hcOne : absoluteTraceChar k c = 1 := by
    have hc1 := DFunLike.congr_fun hc 1
    simpa [h.ne_zero 1] using hc1
  have hcTrace : absoluteTraceTwo k c = 0 :=
    (absoluteTraceChar_eq_one_iff c).mp hcOne
  obtain ⟨d, hd⟩ := exists_frobeniusInv_coboundary k hcTrace
  let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  let qh := h.translate d
  have hdefect : ∀ x : k,
      h (x ^ 2) = h x * absoluteTraceChar k (c * x) := by
    intro x
    have hx := DFunLike.congr_fun hc x
    change absoluteTraceChar k (c * x) = h (x ^ 2) / h x at hx
    rw [hx]
    field_simp [h.ne_zero x]
  have hsq : ∀ x : k, qh (x ^ 2) = qh x := by
    intro x
    rw [HasseFunction.translate_apply, HasseFunction.translate_apply, hdefect]
    rw [absoluteTraceChar_mul_sq k]
    calc
      h x * absoluteTraceChar k (c * x) *
          absoluteTraceChar k (sigma.symm d * x) =
          h x * absoluteTraceChar k (c * x + sigma.symm d * x) := by
            rw [AddChar.map_add_eq_mul]
            ring
      _ = h x * absoluteTraceChar k (d * x) := by
            congr 2
            rw [hd]
            dsimp [sigma]
            rw [add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  exact ⟨⟨qh, hsq⟩, d, rfl⟩

/-- Precomposing an affine refinement by Frobenius applies inverse Frobenius to its
linear coefficient. -/
theorem affine_frobenius (q : CharTwoRefinement k) (lambda x : k) :
    q.affine lambda (x ^ 2) =
      q.affine
        ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k).symm lambda) x := by
  rw [affine_apply, affine_apply, q.map_sq, absoluteTraceChar_mul_sq]

/-- Exactly the affine parameters `0` and `1` preserve Frobenius normalization. -/
theorem affine_normalized_iff (q : CharTwoRefinement k) (lambda : k) :
    IsFrobeniusNormalized (q.affine lambda) ↔ lambda = 0 ∨ lambda = 1 := by
  let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  constructor
  · intro hnormalized
    have heq : q.affine (sigma.symm lambda) = q.affine lambda := by
      apply HasseFunction.ext
      intro x
      exact (q.affine_frobenius lambda x).symm.trans (hnormalized x)
    obtain ⟨a, ha, haUnique⟩ := q.existsUnique_affine (q.affine lambda)
    have hsigma : sigma.symm lambda = a := haUnique _ heq
    have hlambda : lambda = a := haUnique _ rfl
    have hfixedInv : sigma.symm lambda = lambda := hsigma.trans hlambda.symm
    have hfixed : sigma lambda = lambda := by
      calc
        sigma lambda = sigma (sigma.symm lambda) := congrArg sigma hfixedInv.symm
        _ = lambda := sigma.apply_symm_apply lambda
    have hsquare : lambda ^ 2 = lambda := by
      change sigma lambda = lambda
      exact hfixed
    exact eq_zero_or_one_of_sq_eq_self hsquare
  · rintro (rfl | rfl)
    · intro x
      simp
    · intro x
      simp

/-- The second normalized choice, obtained by the unique nontrivial prime-field affine
twist. -/
noncomputable def translateOne (q : CharTwoRefinement k) : CharTwoRefinement k where
  toHasseFunction := q.affine 1
  map_sq' := (q.affine_normalized_iff 1).2 (Or.inr rfl)

@[simp]
theorem translateOne_apply (q : CharTwoRefinement k) (x : k) :
    q.translateOne x = q x * absoluteTraceChar k x := by
  change q.affine 1 x = _
  simp

/-- Relative to any normalized base refinement, the only normalized refinements are the
base and its prime-field twist. -/
theorem eq_or_eq_translateOne (q r : CharTwoRefinement k) :
    r = q ∨ r = q.translateOne := by
  obtain ⟨lambda, hlambda, _⟩ := q.existsUnique_affine r.toHasseFunction
  have hnormalized : IsFrobeniusNormalized (q.affine lambda) := by
    rw [hlambda]
    exact r.map_sq
  rcases (q.affine_normalized_iff lambda).1 hnormalized with rfl | rfl
  · left
    apply CharTwoRefinement.ext
    intro x
    have hx := DFunLike.congr_fun hlambda x
    calc
      r.toHasseFunction x = q.affine 0 x := hx.symm
      _ = q.toHasseFunction x := by
        simp [affine, HasseFunction.translate_apply]
  · right
    apply CharTwoRefinement.ext
    intro x
    exact (DFunLike.congr_fun hlambda x).symm

/-- The two normalized choices are distinct. -/
theorem translateOne_ne (q : CharTwoRefinement k) : q.translateOne ≠ q := by
  intro heq
  obtain ⟨a, _, haUnique⟩ := q.existsUnique_affine q.toHasseFunction
  have hzero : q.affine 0 = q.toHasseFunction := by
    apply HasseFunction.ext
    intro x
    simp [affine, HasseFunction.translate_apply]
  have hone : q.affine 1 = q.toHasseFunction := by
    calc
      q.affine 1 = q.translateOne.toHasseFunction := rfl
      _ = q.toHasseFunction := congrArg toHasseFunction heq
  have h0 : (0 : k) = a := haUnique 0 hzero
  have h1 : (1 : k) = a := haUnique 1 hone
  exact zero_ne_one (h0.trans h1.symm)

/-- The raw affine sum. -/
noncomputable def affineSum (q : CharTwoRefinement k) (lambda : k) : ℂ :=
  (q.affine lambda).sum

/-- The total phase of the affine sum. -/
noncomputable def affinePhase (q : CharTwoRefinement k) (lambda : k) : ℂ :=
  (q.affine lambda).sumPhase

/-- Every affine sum is nonzero; phase manipulations below therefore never use the
totalized zero branch. -/
theorem affineSum_ne_zero (q : CharTwoRefinement k) (lambda : k) :
    q.affineSum lambda ≠ 0 :=
  (q.affine lambda).sum_ne_zero (absoluteTraceChar_ne_one k)

/-- Every affine sum has the exact square-root cardinality. -/
theorem affineSum_norm (q : CharTwoRefinement k) (lambda : k) :
    ‖q.affineSum lambda‖ = Real.sqrt (Fintype.card k : ℝ) :=
  (q.affine lambda).sum_norm (absoluteTraceChar_ne_one k)

/-- Affine parameters add under Hasse-function translation. -/
theorem affine_translate (q : CharTwoRefinement k) (lambda c : k) :
    (q.affine lambda).translate c = q.affine (lambda + c) := by
  apply HasseFunction.ext
  intro x
  simp only [HasseFunction.translate_apply, affine_apply]
  rw [add_mul, AddChar.map_add_eq_mul]
  ring

/-- Translation of the affine sum phase by the inverse complete affine value. -/
theorem affinePhase_add (q : CharTwoRefinement k) (lambda c : k) :
    q.affinePhase (lambda + c) =
      (q.affine lambda c)⁻¹ * q.affinePhase lambda := by
  have h := (q.affine lambda).sumPhase_translate (absoluteTraceChar_ne_one k) c
  rw [q.affine_translate lambda c] at h
  exact h

/-- Exact finite-field correction rule: the complete value `h_λ(c)` cancels the
translation of the phase. -/
theorem correction_phase_rule (q : CharTwoRefinement k) (lambda c : k) :
    q.correctionValue lambda c * q.affinePhase (lambda + c) =
      q.affinePhase lambda := by
  rw [correctionValue_eq_affine, affinePhase_add]
  rw [← mul_assoc, mul_inv_cancel₀ ((q.affine lambda).ne_zero c), one_mul]

omit [Fintype k] in
/-- Values of the binary absolute-trace character have exact square one. -/
theorem absoluteTraceChar_value_sq (x : k) :
    absoluteTraceChar k x ^ 2 = 1 := by
  rw [pow_two, ← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero]
  simp

/-- The manuscript's exact value-square formula `q(r)² = ψ₀(r)`. -/
theorem value_sq (q : CharTwoRefinement k) (r : k) :
    q r ^ 2 = absoluteTraceChar k r := by
  have hrefine : q r ^ 2 * absoluteTraceChar k (r ^ 2) = 1 := by
    calc
      q r ^ 2 * absoluteTraceChar k (r ^ 2) =
          q r * q r * absoluteTraceChar k (r * r) := by
            rw [pow_two]
            congr 2
            rw [pow_two]
      _ = q (r + r) := (q.map_add r r).symm
      _ = 1 := by rw [CharTwo.add_self_eq_zero, q.map_zero]
  calc
    q r ^ 2 = q r ^ 2 * 1 := by ring
    _ = q r ^ 2 * absoluteTraceChar k (r ^ 2) ^ 2 := by
      rw [absoluteTraceChar_value_sq]
    _ = (q r ^ 2 * absoluteTraceChar k (r ^ 2)) *
        absoluteTraceChar k (r ^ 2) := by ring
    _ = absoluteTraceChar k (r ^ 2) := by rw [hrefine, one_mul]
    _ = absoluteTraceChar k r := absoluteTraceChar_sq k r

/-- Complex conjugation of a refinement value, with its exact residual binary phase. -/
theorem value_star (q : CharTwoRefinement k) (r : k) :
    star (q r) = q r * absoluteTraceChar k r := by
  apply mul_right_cancel₀ (q.ne_zero r)
  have hstar : star (q r) * q r = 1 := by
    change conj (q r) * q r = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, q.norm_apply]
    norm_num
  rw [hstar]
  symm
  calc
    (q r * absoluteTraceChar k r) * q r =
        q r ^ 2 * absoluteTraceChar k r := by ring
    _ = absoluteTraceChar k r ^ 2 := by rw [q.value_sq, pow_two]
    _ = 1 := absoluteTraceChar_value_sq r

/-- Complex-conjugation spelling of `value_star`. -/
theorem value_conj (q : CharTwoRefinement k) (r : k) :
    conj (q r) = q r * absoluteTraceChar k r := by
  simpa [Complex.star_def] using q.value_star r

/-- Inversion and conjugation agree on refinement values. -/
theorem value_inv (q : CharTwoRefinement k) (r : k) :
    (q r)⁻¹ = conj (q r) := by
  apply mul_right_cancel₀ (q.ne_zero r)
  rw [inv_mul_cancel₀ (q.ne_zero r)]
  symm
  change conj (q r) * q r = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, q.norm_apply]
  norm_num

/-- The affine phase in inverse-value form. -/
theorem affinePhase_eq_inv (q : CharTwoRefinement k) (lambda : k) :
    q.affinePhase lambda = q.affinePhase 0 * (q lambda)⁻¹ := by
  have h := q.toHasseFunction.sumPhase_translate (absoluteTraceChar_ne_one k) lambda
  have hzero : q.affine 0 = q.toHasseFunction := by
    apply HasseFunction.ext
    intro x
    simp [affine, HasseFunction.translate_apply]
  rw [affinePhase, affinePhase, hzero]
  rw [mul_comm]
  exact h

/-- The phase translation formula `H(λ) = H₀ overline(q(λ))`. -/
theorem affinePhase_eq (q : CharTwoRefinement k) (lambda : k) :
    q.affinePhase lambda = q.affinePhase 0 * conj (q lambda) := by
  rw [q.affinePhase_eq_inv, q.value_inv]

/-- The affine sum at `1` is the conjugate of the base sum. -/
theorem affineSum_one_eq_conj (q : CharTwoRefinement k) :
    q.affineSum 1 = conj (q.affineSum 0) := by
  classical
  rw [affineSum, affineSum, HasseFunction.sum, HasseFunction.sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [affine_apply, affine_apply]
  simp only [one_mul, zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact (q.value_conj x).symm

/-- Consequently the affine phase at `1` is the conjugate base phase. -/
theorem affinePhase_one_eq_conj (q : CharTwoRefinement k) :
    q.affinePhase 1 = conj (q.affinePhase 0) := by
  change phase (q.affineSum 1) = conj (phase (q.affineSum 0))
  rw [q.affineSum_one_eq_conj, phase_conj]

/-- Every affine phase is nonzero, including independently of the raw-sum proof. -/
theorem affinePhase_ne_zero (q : CharTwoRefinement k) (lambda : k) :
    q.affinePhase lambda ≠ 0 :=
  phase_ne_zero _

/-- The base phase has exact square `q(1)`. -/
theorem affinePhase_zero_sq (q : CharTwoRefinement k) :
    q.affinePhase 0 ^ 2 = q 1 := by
  have htranslate := q.affinePhase_add 0 1
  have hconj := q.affinePhase_one_eq_conj
  have hone : q.affine 0 1 = q 1 := by simp
  rw [zero_add, hone] at htranslate
  have hrelation : (q 1)⁻¹ * q.affinePhase 0 = conj (q.affinePhase 0) :=
    htranslate.symm.trans hconj
  have hphaseUnit : conj (q.affinePhase 0) * q.affinePhase 0 = 1 := by
    have hn : ‖q.affinePhase 0‖ = 1 := phase_norm _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
    norm_num
  apply mul_left_cancel₀ (inv_ne_zero (q.ne_zero 1))
  calc
    (q 1)⁻¹ * q.affinePhase 0 ^ 2 =
        ((q 1)⁻¹ * q.affinePhase 0) * q.affinePhase 0 := by ring
    _ = conj (q.affinePhase 0) * q.affinePhase 0 := by rw [hrelation]
    _ = 1 := hphaseUnit
    _ = (q 1)⁻¹ * q 1 := (inv_mul_cancel₀ (q.ne_zero 1)).symm

/-- The exact phase-square formula `H(λ)² = q(1) ψ₀(λ)`. -/
theorem affinePhase_sq (q : CharTwoRefinement k) (lambda : k) :
    q.affinePhase lambda ^ 2 = q 1 * absoluteTraceChar k lambda := by
  have hconjSq : conj (q lambda) ^ 2 = absoluteTraceChar k lambda := by
    rw [q.value_conj, mul_pow, q.value_sq, absoluteTraceChar_value_sq, mul_one]
  calc
    q.affinePhase lambda ^ 2 =
        (q.affinePhase 0 * conj (q lambda)) ^ 2 := by rw [q.affinePhase_eq]
    _ = q.affinePhase 0 ^ 2 * conj (q lambda) ^ 2 := mul_pow _ _ 2
    _ = q 1 * absoluteTraceChar k lambda := by
      rw [q.affinePhase_zero_sq, hconjSq]

/-- Frobenius does not change the affine phase. -/
@[simp]
theorem affinePhase_sq_arg (q : CharTwoRefinement k) (lambda : k) :
    q.affinePhase (lambda ^ 2) = q.affinePhase lambda := by
  calc
    q.affinePhase (lambda ^ 2) =
        q.affinePhase 0 * conj (q (lambda ^ 2)) := q.affinePhase_eq _
    _ = q.affinePhase 0 * conj (q lambda) := by rw [q.map_sq]
    _ = q.affinePhase lambda := (q.affinePhase_eq lambda).symm

/-- The exact two-phase cancellation `H(1+λ)H(λ)=1`. -/
theorem affinePhase_pair (q : CharTwoRefinement k) (lambda : k) :
    q.affinePhase (1 + lambda) * q.affinePhase lambda = 1 := by
  rw [add_comm, q.affinePhase_add]
  rw [affine_apply, mul_one]
  calc
    (q 1 * absoluteTraceChar k lambda)⁻¹ * q.affinePhase lambda *
        q.affinePhase lambda =
        (q 1 * absoluteTraceChar k lambda)⁻¹ * q.affinePhase lambda ^ 2 := by ring
    _ = (q 1 * absoluteTraceChar k lambda)⁻¹ *
        (q 1 * absoluteTraceChar k lambda) := by rw [q.affinePhase_sq]
    _ = 1 := inv_mul_cancel₀ (mul_ne_zero (q.ne_zero 1)
      (AddChar.val_isUnit (absoluteTraceChar k) lambda).ne_zero)

/-- Multiplication of refinement values, with the positive polar phase retained. -/
theorem value_mul (q : CharTwoRefinement k) (x y : k) :
    q x * q y = q (x + y) * absoluteTraceChar k (x * y) := by
  calc
    q x * q y = q x * q y * 1 := by ring
    _ = q x * q y * absoluteTraceChar k (x * y) ^ 2 := by
      rw [absoluteTraceChar_value_sq]
    _ = (q x * q y * absoluteTraceChar k (x * y)) *
        absoluteTraceChar k (x * y) := by ring
    _ = q (x + y) * absoluteTraceChar k (x * y) := by rw [← q.map_add]

/-- Product of two conjugate refinement values. -/
theorem value_conj_mul (q : CharTwoRefinement k) (x y : k) :
    conj (q x) * conj (q y) =
      q (x + y) * absoluteTraceChar k (x * y + (x + y)) := by
  rw [q.value_conj, q.value_conj]
  calc
    (q x * absoluteTraceChar k x) * (q y * absoluteTraceChar k y) =
        (q x * q y) *
          (absoluteTraceChar k x * absoluteTraceChar k y) := by ring
    _ = (q (x + y) * absoluteTraceChar k (x * y)) *
          absoluteTraceChar k (x + y) := by
            rw [q.value_mul, ← AddChar.map_add_eq_mul]
    _ = q (x + y) * absoluteTraceChar k (x * y + (x + y)) := by
      conv_rhs => rw [AddChar.map_add_eq_mul]
      ring

/-- Cancellation of the common base phase in a signed four-phase quotient. -/
theorem affinePhase_four_ratio (q : CharTwoRefinement k) (a b c d : k) :
    q.affinePhase a * q.affinePhase b /
        (q.affinePhase c * q.affinePhase d) =
      q c * q d * conj (q a) * conj (q b) := by
  rw [q.affinePhase_eq_inv a, q.affinePhase_eq_inv b,
    q.affinePhase_eq_inv c, q.affinePhase_eq_inv d]
  rw [← q.value_inv a, ← q.value_inv b]
  field_simp [q.affinePhase_ne_zero 0, q.ne_zero a, q.ne_zero b,
    q.ne_zero c, q.ne_zero d]

/-- Exact value identity underlying the four-phase calculation.  The signs match the
manuscript: `a,b` occur in the numerator and `c,d` in the denominator. -/
theorem four_value_identity (q : CharTwoRefinement k) (a b c d A : k)
    (hsum : c + d = a + b + A) :
    q c * q d * conj (q a) * conj (q b) =
      q A * absoluteTraceChar k ((a + b) * A + c * d + a * b) := by
  let X := c + d
  let Y := a + b
  have hXY : X = Y + A := hsum
  have hXA : X + Y = A := by
    calc
      X + Y = (Y + A) + Y := by rw [hXY]
      _ = A + (Y + Y) := by abel
      _ = A := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hphase :
      absoluteTraceChar k (X * Y + (c * d + (a * b + Y))) =
        absoluteTraceChar k (Y * A + c * d + a * b) := by
    rw [hXY]
    calc
      absoluteTraceChar k ((Y + A) * Y + (c * d + (a * b + Y))) =
          absoluteTraceChar k ((Y ^ 2 + Y) + (Y * A + c * d + a * b)) := by
            congr 1
            ring
      _ = absoluteTraceChar k (Y ^ 2 + Y) *
          absoluteTraceChar k (Y * A + c * d + a * b) :=
            AddChar.map_add_eq_mul _ _ _
      _ = absoluteTraceChar k (Y * A + c * d + a * b) := by
            rw [show Y ^ 2 + Y = Y + Y ^ 2 by ring, artinSchreier_phase]
            simp
  calc
    q c * q d * conj (q a) * conj (q b) =
        (q c * q d) * (conj (q a) * conj (q b)) := by ring
    _ = (q X * absoluteTraceChar k (c * d)) *
        (q Y * absoluteTraceChar k (a * b + Y)) := by
          rw [q.value_mul, q.value_conj_mul]
    _ = (q X * q Y) *
        (absoluteTraceChar k (c * d) *
          absoluteTraceChar k (a * b + Y)) := by ring
    _ = (q (X + Y) * absoluteTraceChar k (X * Y)) *
        absoluteTraceChar k (c * d + (a * b + Y)) := by
          rw [q.value_mul, ← AddChar.map_add_eq_mul]
    _ = q (X + Y) *
        absoluteTraceChar k (X * Y + (c * d + (a * b + Y))) := by
          conv_rhs => rw [AddChar.map_add_eq_mul]
          ring
    _ = q A * absoluteTraceChar k (Y * A + c * d + a * b) := by
          rw [hXA, hphase]
    _ = q A * absoluteTraceChar k ((a + b) * A + c * d + a * b) := rfl

/-- The exact signed four-phase formula used by the wild quadratic boundary algebra. -/
theorem affinePhase_four (q : CharTwoRefinement k) (a b c d A : k)
    (hsum : c + d = a + b + A) :
    q.affinePhase a * q.affinePhase b /
        (q.affinePhase c * q.affinePhase d) =
      q A * absoluteTraceChar k ((a + b) * A + c * d + a * b) := by
  rw [q.affinePhase_four_ratio, q.four_value_identity a b c d A hsum]

/-- Adding two positively oriented correction values eliminates the remaining refinement
value in the four-phase quotient. -/
theorem affinePhase_four_correction
    (q : CharTwoRefinement k) (a b c d A B C : k)
    (hsum : c + d = a + b + A) (hBC : B + C = A) :
    (q.affinePhase a * q.affinePhase b /
        (q.affinePhase c * q.affinePhase d)) * q B * q C =
      absoluteTraceChar k
        (((a + b) * A + c * d + a * b) + A + B * C) := by
  rw [q.affinePhase_four a b c d A hsum]
  calc
    (q A * absoluteTraceChar k ((a + b) * A + c * d + a * b)) * q B * q C =
        q A * (q B * q C) *
          absoluteTraceChar k ((a + b) * A + c * d + a * b) := by ring
    _ = q A * (q A * absoluteTraceChar k (B * C)) *
          absoluteTraceChar k ((a + b) * A + c * d + a * b) := by
            rw [q.value_mul B C, hBC]
    _ = (q A * q A) *
          (absoluteTraceChar k ((a + b) * A + c * d + a * b) *
            absoluteTraceChar k (B * C)) := by ring
    _ = absoluteTraceChar k A *
        (absoluteTraceChar k ((a + b) * A + c * d + a * b) *
          absoluteTraceChar k (B * C)) := by rw [← pow_two, q.value_sq]
    _ = absoluteTraceChar k
        (((a + b) * A + c * d + a * b) + A + B * C) := by
          calc
            absoluteTraceChar k A *
                (absoluteTraceChar k ((a + b) * A + c * d + a * b) *
                  absoluteTraceChar k (B * C)) =
                absoluteTraceChar k
                  (A + (((a + b) * A + c * d + a * b) + B * C)) := by
                    calc
                      absoluteTraceChar k A *
                          (absoluteTraceChar k ((a + b) * A + c * d + a * b) *
                            absoluteTraceChar k (B * C)) =
                          absoluteTraceChar k A *
                            absoluteTraceChar k
                              (((a + b) * A + c * d + a * b) + B * C) := by
                                congr 1
                                exact (AddChar.map_add_eq_mul _ _ _).symm
                      _ = absoluteTraceChar k
                          (A + (((a + b) * A + c * d + a * b) + B * C)) :=
                            (AddChar.map_add_eq_mul _ _ _).symm
            _ = absoluteTraceChar k
                (((a + b) * A + c * d + a * b) + A + B * C) := by
                  congr 1
                  ring

/-- Exact four-phase cancellation after an Artin--Schreier residual phase.  This is a
finite-field theorem only: all local-field inputs are left to the later wild-quadratic
nodes. -/
theorem affinePhase_four_cancel
    (q : CharTwoRefinement k) (a b c d A B C t z : k)
    (hsum : c + d = a + b + A) (hBC : B + C = A)
    (hAS : ((a + b) * A + c * d + a * b) + A + B * C + t = z + z ^ 2) :
    q.affinePhase a * q.affinePhase b * q B * q C *
        absoluteTraceChar k t =
      q.affinePhase c * q.affinePhase d := by
  have hquot := q.affinePhase_four_correction a b c d A B C hsum hBC
  have hphase :
      absoluteTraceChar k
          ((((a + b) * A + c * d + a * b) + A + B * C) + t) = 1 := by
    rw [hAS, artinSchreier_phase]
  have htotal :
      (q.affinePhase a * q.affinePhase b /
          (q.affinePhase c * q.affinePhase d)) * q B * q C *
          absoluteTraceChar k t = 1 := by
    rw [hquot, ← AddChar.map_add_eq_mul, hphase]
  have hdenom : q.affinePhase c * q.affinePhase d ≠ 0 :=
    mul_ne_zero (q.affinePhase_ne_zero c) (q.affinePhase_ne_zero d)
  apply mul_right_cancel₀ (inv_ne_zero hdenom)
  calc
    (q.affinePhase a * q.affinePhase b * q B * q C *
        absoluteTraceChar k t) *
        (q.affinePhase c * q.affinePhase d)⁻¹ =
      (q.affinePhase a * q.affinePhase b /
          (q.affinePhase c * q.affinePhase d)) * q B * q C *
          absoluteTraceChar k t := by
            rw [div_eq_mul_inv]
            ring
    _ = 1 := htotal
    _ = (q.affinePhase c * q.affinePhase d) *
        (q.affinePhase c * q.affinePhase d)⁻¹ :=
          (mul_inv_cancel₀ hdenom).symm

end CharTwoRefinement

end CharacteristicTwo

end LanglandsFirstMainLemma
