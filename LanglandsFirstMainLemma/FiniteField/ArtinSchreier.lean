import LanglandsFirstMainLemma.FiniteField.QuadraticPhase

namespace LanglandsFirstMainLemma

section CharacteristicTwo

variable (k : Type*) [Field k] [Fintype k] [CharP k 2]

local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The exact character `t ↦ (-1)^t` of the prime field `ZMod 2`. -/
noncomputable def binaryAddChar : FiniteAddChar (ZMod 2) :=
  AddChar.zmodChar 2 (by norm_num : (-1 : ℂ) ^ 2 = 1)

@[simp]
theorem binaryAddChar_apply (x : ZMod 2) :
    binaryAddChar x = (-1 : ℂ) ^ x.val :=
  rfl

/-- The binary character is nontrivial. -/
theorem binaryAddChar_ne_one : binaryAddChar ≠ 1 := by
  rw [AddChar.zmod_char_ne_one_iff 2]
  change (-1 : ℂ) ^ (1 : ZMod 2).val ≠ 1
  rw [ZMod.val_one]
  norm_num

/-- The absolute trace from `k` to its prime field. -/
noncomputable abbrev absoluteTraceTwo : k →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) k

/-- The manuscript's exact normalized character `ψ₀(x) = (-1)^Tr(x)`. -/
noncomputable def absoluteTraceChar : FiniteAddChar k :=
  traceAddChar (ZMod 2) k binaryAddChar

omit [Fintype k] in
@[simp]
theorem absoluteTraceChar_apply (x : k) :
    absoluteTraceChar k x = (-1 : ℂ) ^ (absoluteTraceTwo k x).val :=
  rfl

/-- The normalized absolute-trace character is nontrivial. -/
theorem absoluteTraceChar_ne_one : absoluteTraceChar k ≠ 1 :=
  (traceAddChar_ne_one_iff (ZMod 2) k binaryAddChar).2 binaryAddChar_ne_one

/-- Multiplicative shifts of `ψ₀` parametrize all additive characters of `k`. -/
theorem absoluteTraceChar_mulShift_bijective :
    Function.Bijective (absoluteTraceChar k).mulShift := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one (absoluteTraceChar_ne_one k)),
    AddChar.card_eq.symm⟩

/-- Every additive character is uniquely `x ↦ ψ₀(a x)`. -/
theorem existsUnique_absoluteTraceChar_mulShift (ψ : FiniteAddChar k) :
    ∃! a : k, (absoluteTraceChar k).mulShift a = ψ := by
  obtain ⟨a, ha⟩ := (absoluteTraceChar_mulShift_bijective k).2 ψ
  exact ⟨a, ha, fun b hb ↦ (absoluteTraceChar_mulShift_bijective k).1 (hb.trans ha.symm)⟩

/-- The absolute-trace pairing is perfect, in an exact trace-one form. -/
theorem exists_absoluteTraceTwo_mul_eq_one {a : k} (ha : a ≠ 0) :
    ∃ b : k, absoluteTraceTwo k (a * b) = 1 := by
  obtain ⟨x, hx⟩ := (Algebra.trace_surjective (ZMod 2) k) (1 : ZMod 2)
  refine ⟨a⁻¹ * x, ?_⟩
  simpa [ha] using hx

/-- The character pairing `(a,b) ↦ ψ₀(ab)` is nondegenerate. -/
theorem exists_absoluteTraceChar_mul_ne_one {a : k} (ha : a ≠ 0) :
    ∃ b : k, absoluteTraceChar k (a * b) ≠ 1 := by
  obtain ⟨b, hb⟩ := exists_absoluteTraceTwo_mul_eq_one k ha
  refine ⟨b, ?_⟩
  rw [absoluteTraceChar_apply, hb, ZMod.val_one]
  norm_num

/-- The trace of `1` records the extension degree modulo two. -/
@[simp]
theorem absoluteTraceTwo_one :
    absoluteTraceTwo k 1 = (Module.finrank (ZMod 2) k : ZMod 2) := by
  simpa using (Algebra.trace_algebraMap (R := ZMod 2) (S := k) (1 : ZMod 2))

/-- Consequently `ψ₀(1)=(-1)^[k:F₂]`, with the exact exponent. -/
@[simp]
theorem absoluteTraceChar_one :
    absoluteTraceChar k 1 = (-1 : ℂ) ^ Module.finrank (ZMod 2) k := by
  rw [absoluteTraceChar_apply, absoluteTraceTwo_one, ZMod.val_natCast]
  exact (pow_eq_pow_mod (Module.finrank (ZMod 2) k)
    (by norm_num : (-1 : ℂ) ^ 2 = 1)).symm

/-- Absolute trace is invariant under the characteristic-two Frobenius. -/
@[simp]
theorem absoluteTraceTwo_sq (x : k) :
    absoluteTraceTwo k (x ^ 2) = absoluteTraceTwo k x := by
  simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    (Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k) x)

/-- The normalized character is invariant under Frobenius. -/
@[simp]
theorem absoluteTraceChar_sq (x : k) :
    absoluteTraceChar k (x ^ 2) = absoluteTraceChar k x := by
  simp only [absoluteTraceChar_apply, absoluteTraceTwo_sq]

/-- Artin--Schreier elements have absolute trace zero. -/
@[simp]
theorem absoluteTraceTwo_artinSchreier (c : k) :
    absoluteTraceTwo k (c + c ^ 2) = 0 := by
  rw [map_add, absoluteTraceTwo_sq]
  exact CharTwo.add_self_eq_zero _

/-- The exact Artin--Schreier trace-phase identity from the manuscript. -/
@[simp]
theorem artinSchreier_phase (c : k) :
    absoluteTraceChar k (c + c ^ 2) = 1 := by
  rw [absoluteTraceChar_apply, absoluteTraceTwo_artinSchreier]
  rfl

/-- In a finite field of characteristic two, every element has a unique square root. -/
theorem existsUnique_squareRoot (a : k) : ∃! d : k, d ^ 2 = a := by
  obtain ⟨d, hd⟩ :=
    (isSquare_iff_exists_sq a).mp (FiniteField.isSquare_of_char_two (ringChar.eq k 2) a)
  refine ⟨d, hd.symm, ?_⟩
  intro y hy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hd) with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

/-- The Artin--Schreier map, as an `F₂`-linear map. -/
noncomputable def artinSchreierMap : k →ₗ[ZMod 2] k :=
  LinearMap.id +
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k).toLinearMap

@[simp]
theorem artinSchreierMap_apply (x : k) :
    artinSchreierMap k x = x + x ^ 2 := by
  simp [artinSchreierMap]

/-- The kernel of the Artin--Schreier map is the prime field `{0,1}`. -/
theorem artinSchreierMap_ker :
    (artinSchreierMap k).ker = (ZMod 2) ∙ (1 : k) := by
  ext x
  rw [LinearMap.mem_ker, artinSchreierMap_apply]
  constructor
  · intro hx
    have hroot : x = 0 ∨ x = 1 := by
      have hprod : x * (x + 1) = 0 := by
        calc
          x * (x + 1) = x ^ 2 + x := by ring
          _ = x + x ^ 2 := add_comm _ _
          _ = 0 := hx
      rcases mul_eq_zero.mp hprod with hx0 | hx1
      · exact Or.inl hx0
      · right
        exact (add_eq_zero_iff_eq_neg.mp hx1).trans (CharTwo.neg_eq 1)
    rcases hroot with rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.mem_span_singleton_self _
  · rw [Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    change (a • (1 : k)) + (a • (1 : k)) ^ 2 = 0
    rw [Algebra.smul_def]
    simp only [mul_one, ← map_pow]
    rw [ZMod.pow_card]
    exact CharTwo.add_self_eq_zero _

private theorem artinSchreierMap_ker_finrank :
    Module.finrank (ZMod 2) (artinSchreierMap k).ker = 1 := by
  rw [artinSchreierMap_ker k]
  exact finrank_span_singleton one_ne_zero

/-- Every Artin--Schreier value lies in the trace-zero hyperplane. -/
private theorem artinSchreierMap_range_le_trace_ker :
    (artinSchreierMap k).range ≤ (absoluteTraceTwo k).ker := by
  rintro y ⟨x, rfl⟩
  simp

/-- Exactness of the Artin--Schreier sequence over a finite field. -/
theorem artinSchreierMap_range_eq_trace_ker :
    (artinSchreierMap k).range = (absoluteTraceTwo k).ker := by
  apply Submodule.eq_of_le_of_finrank_eq (artinSchreierMap_range_le_trace_ker k)
  have hAS := LinearMap.finrank_range_add_finrank_ker (artinSchreierMap k)
  rw [artinSchreierMap_ker_finrank k] at hAS
  have htrace := LinearMap.finrank_range_add_finrank_ker (absoluteTraceTwo k)
  have htraceSurjective : Function.Surjective (absoluteTraceTwo k) :=
    Algebra.trace_surjective (ZMod 2) k
  have htraceRange : (absoluteTraceTwo k).range = ⊤ :=
    LinearMap.range_eq_top.mpr htraceSurjective
  rw [htraceRange, finrank_top, Module.finrank_self] at htrace
  omega

/-- An element has trace zero exactly when it is an Artin--Schreier value. -/
theorem absoluteTraceTwo_eq_zero_iff (a : k) :
    absoluteTraceTwo k a = 0 ↔ ∃ c : k, a = c + c ^ 2 := by
  constructor
  · intro ha
    have hmem : a ∈ (absoluteTraceTwo k).ker := ha
    rw [← artinSchreierMap_range_eq_trace_ker k] at hmem
    rcases hmem with ⟨c, hc⟩
    exact ⟨c, hc.symm.trans (artinSchreierMap_apply k c)⟩
  · rintro ⟨c, rfl⟩
    exact absoluteTraceTwo_artinSchreier k c

/-- The adjoint of Frobenius for the absolute trace is inverse Frobenius. -/
theorem absoluteTraceTwo_mul_sq (a x : k) :
    absoluteTraceTwo k (a * x ^ 2) =
      absoluteTraceTwo k
        ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k).symm a * x) := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  have hinv_sq : (σ.symm a) ^ 2 = a := by
    change σ (σ.symm a) = a
    exact σ.apply_symm_apply a
  calc
    absoluteTraceTwo k (a * x ^ 2) =
        absoluteTraceTwo k ((σ.symm a * x) ^ 2) := by rw [mul_pow, hinv_sq]
    _ = absoluteTraceTwo k (σ.symm a * x) := absoluteTraceTwo_sq k _

/-- The same Frobenius-adjoint identity at the level of the normalized character. -/
theorem absoluteTraceChar_mul_sq (a x : k) :
    absoluteTraceChar k (a * x ^ 2) =
      absoluteTraceChar k
        ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k).symm a * x) := by
  simp only [absoluteTraceChar_apply, absoluteTraceTwo_mul_sq]

/-- Every trace-zero element is an inverse-Frobenius coboundary. -/
theorem exists_frobeniusInv_coboundary {c : k} (hc : absoluteTraceTwo k c = 0) :
    ∃ d : k,
      c = d + (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k).symm d := by
  obtain ⟨e, he⟩ := (absoluteTraceTwo_eq_zero_iff k c).mp hc
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  refine ⟨σ e, ?_⟩
  rw [σ.symm_apply_apply, he]
  change e + e ^ 2 = e ^ 2 + e
  exact add_comm _ _

/-- The normalized character is the unique nontrivial character annihilating
the Artin--Schreier image. -/
theorem absoluteTraceChar_eq_of_artinSchreier_trivial
    {ψ : FiniteAddChar k} (hψ : ψ ≠ 1)
    (hAS : ∀ c : k, ψ (c + c ^ 2) = 1) :
    ψ = absoluteTraceChar k := by
  obtain ⟨a, ha, _⟩ := existsUnique_absoluteTraceChar_mulShift k ψ
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  have hann : ∀ c : k, absoluteTraceChar k ((a + σ.symm a) * c) = 1 := by
    intro c
    have hc := hAS c
    rw [← ha, AddChar.mulShift_apply] at hc
    calc
      absoluteTraceChar k ((a + σ.symm a) * c) =
          absoluteTraceChar k (a * c + σ.symm a * c) := by ring_nf
      _ = absoluteTraceChar k (a * c) * absoluteTraceChar k (σ.symm a * c) :=
        AddChar.map_add_eq_mul _ _ _
      _ = absoluteTraceChar k (a * c) * absoluteTraceChar k (a * c ^ 2) := by
        rw [absoluteTraceChar_mul_sq k]
      _ = absoluteTraceChar k (a * (c + c ^ 2)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = 1 := hc
  have hcoeff : a + σ.symm a = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := exists_absoluteTraceChar_mul_ne_one k hne
    exact hc (hann c)
  have hfixInv : a = σ.symm a := CharTwo.add_eq_zero.mp hcoeff
  have hfix : σ a = a := by
    calc
      σ a = σ (σ.symm a) := congrArg σ hfixInv
      _ = a := σ.apply_symm_apply a
  have ha_sq : a ^ 2 = a := by
    change σ a = a
    exact hfix
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using ha_sq) with ha0 | ha1
  · exfalso
    apply hψ
    rw [← ha, ha0, AddChar.mulShift_zero]
  · rw [← ha, ha1, AddChar.mulShift_one]

/-- Every nontrivial additive character has a nonzero Frobenius-adjoint
coefficient: squaring its argument is the same as multiplying by that coefficient.
The value at the coefficient's square is the canonical value at `1`. -/
theorem exists_frobeniusAdjointCoefficient
    {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    ∃ c₀ : k, c₀ ≠ 0 ∧
      (∀ x : k, ψ (x ^ 2) = ψ (c₀ * x)) ∧
      ψ (c₀ ^ 2) = absoluteTraceChar k 1 := by
  obtain ⟨a, ha, _⟩ := existsUnique_absoluteTraceChar_mulShift k ψ
  have ha0 : a ≠ 0 := by
    intro haZero
    apply hψ
    rw [← ha, haZero, AddChar.mulShift_zero]
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) k
  let c₀ := a⁻¹ * σ.symm a
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (inv_ne_zero ha0) ((map_ne_zero σ.symm).2 ha0)
  refine ⟨c₀, hc₀, ?_, ?_⟩
  · intro x
    rw [← ha, AddChar.mulShift_apply, AddChar.mulShift_apply]
    change absoluteTraceChar k (a * x ^ 2) = absoluteTraceChar k (a * (c₀ * x))
    rw [absoluteTraceChar_mul_sq k]
    congr 1
    dsimp [c₀]
    field_simp
    ring
  · rw [← ha, AddChar.mulShift_apply]
    congr 1
    dsimp [c₀]
    have hinv_sq : (σ.symm a) ^ 2 = a := by
      change σ (σ.symm a) = a
      exact σ.apply_symm_apply a
    rw [mul_pow, hinv_sq]
    field_simp

end CharacteristicTwo

end LanglandsFirstMainLemma
