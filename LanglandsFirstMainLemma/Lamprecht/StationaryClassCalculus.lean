import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Delta.Elementary

/-!
# Stationary-class calculus

This file formalizes Lemma `lem:stationary-class-calculus`.  Stationary
parameters remain lattice-quotient classes throughout.  In particular, after
a conductor drop the class at the new conductor and its minimal stationary
depth is constructed first; a change-of-bounds map then compares only its
restriction with the sum on the old layer.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem intCast_le_intCast_of_nat_le {r q : ℕ} (h : r ≤ q) :
    (r : ℤ) ≤ (q : ℤ) := by
  exact_mod_cast h

namespace IsLamprechtStationaryDepth

variable {q r s : ℕ}

/-- Increasing an admissible stationary depth, while staying below `q`,
again gives an admissible stationary depth. -/
theorem deeper (hr : IsLamprechtStationaryDepth q r)
    (hrs : r ≤ s) (hsq : s + 1 ≤ q) :
    IsLamprechtStationaryDepth q s := by
  exact ⟨hr.conductor_gt_one,
    hr.half_le.trans (Nat.mul_le_mul_left 2 hrs), hsq⟩

end IsLamprechtStationaryDepth

/-! ## Representative-free changes of lattice bounds -/

/-- Inclusion of a deeper numerator lattice into a shallower one. -/
private def latticeNumeratorInclusion {m m' : ℤ} (hmm' : m ≤ m') :
    lattice F m' →ₗ[ringOfIntegers F] lattice F m where
  toFun x := ⟨x, lattice_antitone F hmm' x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Change both bounds of a lattice quotient without selecting a
representative.  The hypotheses say that the source numerator and source
denominator are both deeper than their targets. -/
noncomputable def latticeQuotientChangeBounds
    {m m' n n' : ℤ} (hsource : m' ≤ n') (htarget : m ≤ n)
    (hnum : m ≤ m') (hden : n ≤ n') :
    LatticeQuotient F m' n' hsource →ₗ[ringOfIntegers F]
      LatticeQuotient F m n htarget :=
  Submodule.mapQ (latticeInside F hsource) (latticeInside F htarget)
    (latticeNumeratorInclusion F hnum) (by
      intro x hx
      apply (mem_latticeInside F htarget).2
      exact lattice_antitone F hden ((mem_latticeInside F hsource).1 hx))

/-- Changing quotient bounds keeps the underlying field representative. -/
@[simp]
theorem latticeQuotientChangeBounds_mk
    {m m' n n' : ℤ} (hsource : m' ≤ n') (htarget : m ≤ n)
    (hnum : m ≤ m') (hden : n ≤ n') (c : lattice F m') :
    latticeQuotientChangeBounds F hsource htarget hnum hden
        (latticeQuotientMk F hsource c) =
      latticeQuotientMk F htarget
        ⟨(c : F), lattice_antitone F hnum c.property⟩ :=
  rfl

/-! ## Restriction to a deeper stationary layer -/

/-- Restriction from depth `r` to a deeper depth `s`.  This is the canonical
denominator projection
`p^(M-q)/p^(M-r) → p^(M-q)/p^(M-s)`. -/
noncomputable def stationaryClassRestriction
    (M : ℤ) {q r s : ℕ} (hr : IsLamprechtStationaryDepth q r)
    (hrs : r ≤ s) (hsq : s + 1 ≤ q) :
    LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
        hr.int_le_conductor →ₗ[ringOfIntegers F]
      LamprechtCoefficientQuotient F M (q : ℤ) (s : ℤ)
        (hr.deeper hrs hsq).int_le_conductor :=
  latticeQuotientProjection F
    (sub_le_sub_left (hr.deeper hrs hsq).int_le_conductor M)
    (sub_le_sub_left (by exact_mod_cast hrs) M)

/-- Restriction sends the stationary class to the stationary class at the
deeper layer, and the quotient projection keeps every representative. -/
theorem stationaryNumeratorClass_restrict
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r s : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (hrs : r ≤ s) (hsq : s + 1 ≤ chi.conductor)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryClassRestriction F M hr hrs hsq
        (stationaryNumeratorClass F chi psi M hr Gamma hGamma) =
      stationaryNumeratorClass F chi psi M (hr.deeper hrs hsq) Gamma hGamma := by
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass F chi psi M hr Gamma hGamma)
  rw [← hc, stationaryClassRestriction, latticeQuotientProjection_mk]
  apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff
    F chi psi M (hr.deeper hrs hsq) Gamma hGamma c).2
  intro x
  let xr : lattice F (r : ℤ) :=
    ⟨(x : F), lattice_antitone F (by exact_mod_cast hrs) x.property⟩
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi M hr Gamma hGamma c hc xr
  have hunit :
      (positiveUnitOfLattice F (hr.deeper hrs hsq).pos x : Fˣ) =
        positiveUnitOfLattice F hr.pos xr := by
    apply Units.ext
    simp [xr]
  simpa only [hunit] using hlinear

/-! ## Scaling the denominator -/

/-- Multiplication by `a` transports a numerator from the bounds attached to
`M` to the bounds attached to `M + ord(a)`. -/
private def scaledStationaryNumerator
    (a : Fˣ) (M q : ℤ) (c : lattice F (M - q)) :
    lattice F ((M + unitOrder F a) - q) := by
  refine ⟨(a : F) * (c : F), ?_⟩
  have ha : (a : F) ∈ lattice F (unitOrder F a) := by
    rw [mem_lattice, ord_coe_eq_unitOrder F a]
  have hac := mul_mem_lattice F ha c.property
  simpa only [show unitOrder F a + (M - q) =
      (M + unitOrder F a) - q by omega] using hac

/-- Representative-free multiplication of a stationary quotient class by
`a`, with the simultaneous shift `M ↦ M + ord(a)`. -/
noncomputable def stationaryDenominatorScale
    (a : Fˣ) (M : ℤ) {q r : ℕ} (hrq : (r : ℤ) ≤ (q : ℤ)) :
    LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ) hrq →
      LamprechtCoefficientQuotient F (M + unitOrder F a)
        (q : ℤ) (r : ℤ) hrq :=
  latticeQuotientLift F (sub_le_sub_left hrq M)
    (fun c ↦ latticeQuotientMk F
      (sub_le_sub_left hrq (M + unitOrder F a))
      (scaledStationaryNumerator F a M (q : ℤ) c))
    (by
      intro c d hcd
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        (sub_le_sub_left hrq (M + unitOrder F a))).2
      rw [CongruentAtDepth]
      change (a : F) * (c : F) - (a : F) * (d : F) ∈
        lattice F ((M + unitOrder F a) - (r : ℤ))
      rw [← mul_sub]
      have ha : (a : F) ∈ lattice F (unitOrder F a) := by
        rw [mem_lattice, ord_coe_eq_unitOrder F a]
      have hdiff := (congruentAtDepth_iff_sub_mem_lattice
        F (M - (r : ℤ)) (c : F) (d : F)).1 hcd
      have hmul := mul_mem_lattice F ha hdiff
      simpa only [show unitOrder F a + (M - (r : ℤ)) =
          (M + unitOrder F a) - (r : ℤ) by omega] using hmul)

/-- Denominator scaling is computed by `c ↦ ac` on every representative. -/
@[simp]
theorem stationaryDenominatorScale_mk
    (a : Fˣ) (M : ℤ) {q r : ℕ} (hrq : (r : ℤ) ≤ (q : ℤ))
    (c : lattice F (M - (q : ℤ))) :
    stationaryDenominatorScale F a M hrq
        (latticeQuotientMk F (sub_le_sub_left hrq M) c) =
      latticeQuotientMk F
        (sub_le_sub_left hrq (M + unitOrder F a))
        (scaledStationaryNumerator F a M (q : ℤ) c) :=
  rfl

/-- If `Gamma` has order `M+n`, then `a*Gamma` has order
`(M+ord(a))+n`. -/
theorem stationaryDenominatorScale_order
    (psi : LocalAddCharData F) (a Gamma : Fˣ) (M : ℤ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    ord F ((a * Gamma : Fˣ) : F) =
      (((M + unitOrder F a) + psi.conductor : ℤ) : WithTop ℤ) := by
  change ord F ((a : F) * (Gamma : F)) = _
  rw [ord_mul, ord_coe_eq_unitOrder F a, hGamma]
  norm_cast
  omega

/-- Replacing `Gamma` by `a*Gamma` multiplies the stationary numerator class
by `a` and shifts both quotient bounds by `ord(a)`. -/
theorem stationaryNumeratorClass_scaleDenominator
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (a Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryDenominatorScale F a M hr.int_le_conductor
        (stationaryNumeratorClass F chi psi M hr Gamma hGamma) =
      stationaryNumeratorClass F chi psi (M + unitOrder F a) hr
        (a * Gamma) (stationaryDenominatorScale_order F psi a Gamma M hGamma) := by
  obtain ⟨c, hc⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass F chi psi M hr Gamma hGamma)
  rw [← hc, stationaryDenominatorScale_mk]
  apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff
    F chi psi (M + unitOrder F a) hr (a * Gamma)
      (stationaryDenominatorScale_order F psi a Gamma M hGamma)
      (scaledStationaryNumerator F a M (chi.conductor : ℤ) c)).2
  intro x
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi M hr Gamma hGamma c hc x
  calc
    chi.character (positiveUnitOfLattice F hr.pos x) =
        psi.character ((c : F) * (x : F) / (Gamma : F)) := hlinear
    _ = psi.character
        (((a : F) * (c : F)) * (x : F) /
          ((a : F) * (Gamma : F))) := by
      congr 1
      field_simp [Units.ne_zero a, Units.ne_zero Gamma]

/-! ## Products and integer powers on a common layer -/

/-- A quotient class linearizes a quasi-character on the indicated common
layer.  The predicate quantifies over every representative of the class. -/
def IsStationaryRestrictionClass
    (theta : ContinuousQuasiChar F) (psi : LocalAddCharData F)
    (M : ℤ) {q r : ℕ} (hrpos : 0 < r) (hrq : r ≤ q)
    (Gamma : Fˣ)
    (s : LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
      (intCast_le_intCast_of_nat_le hrq)) : Prop :=
  ∀ (c : lattice F (M - (q : ℤ))),
    latticeQuotientMk F
        (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c = s →
      ∀ x : lattice F (r : ℤ),
        theta (positiveUnitOfLattice F hrpos x) =
          psi.character ((c : F) * (x : F) / (Gamma : F))

/-- The constructed stationary class satisfies the common-layer predicate. -/
theorem stationaryNumeratorClass_isRestriction
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    IsStationaryRestrictionClass F chi.character psi M hr.pos
      hr.le_conductor Gamma
      (stationaryNumeratorClass F chi psi M hr Gamma hGamma) := by
  intro c hc x
  exact stationaryNumeratorClass_linearization
    F chi psi M hr Gamma hGamma c hc x

namespace IsStationaryRestrictionClass

/-- On a common stationary layer, multiplication of characters is addition
of their quotient classes. -/
theorem mul
    {theta₁ theta₂ : ContinuousQuasiChar F} (psi : LocalAddCharData F)
    (M : ℤ) {q r : ℕ} (hrpos : 0 < r) (hrq : r ≤ q)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (s₁ s₂ : LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
      (intCast_le_intCast_of_nat_le hrq))
    (hs₁ : IsStationaryRestrictionClass F theta₁ psi M hrpos hrq Gamma s₁)
    (hs₂ : IsStationaryRestrictionClass F theta₂ psi M hrpos hrq Gamma s₂) :
    IsStationaryRestrictionClass F (theta₁ * theta₂) psi M hrpos hrq Gamma
      (s₁ + s₂) := by
  intro c hc x
  obtain ⟨c₁, hc₁⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) s₁
  obtain ⟨c₂, hc₂⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) s₂
  have hclasses :
      latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c =
        latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M)
          (c₁ + c₂) := by
    calc
      latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c =
          s₁ + s₂ := hc
      _ = latticeQuotientMk F
            (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c₁ +
          latticeQuotientMk F
            (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c₂ := by
        rw [hc₁, hc₂]
      _ = latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M)
          (c₁ + c₂) := (latticeQuotientMk_add F _ c₁ c₂).symm
  have heval := congrArg
    (fun z : LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
        (intCast_le_intCast_of_nat_le hrq) ↦
      (lamprechtPairingLeft F psi (intCast_le_intCast_of_nat_le hrq)
        Gamma hGamma z)
        (latticeQuotientMk F (intCast_le_intCast_of_nat_le hrq) x)) hclasses
  rw [lamprechtPairingLeft_apply, lamprechtPairingLeft_apply,
    lamprechtPairing_mk_mk, lamprechtPairing_mk_mk] at heval
  rw [ContinuousQuasiChar.mul_apply, hs₁ c₁ hc₁ x, hs₂ c₂ hc₂ x]
  calc
    psi.character ((c₁ : F) * (x : F) / (Gamma : F)) *
        psi.character ((c₂ : F) * (x : F) / (Gamma : F)) =
      psi.character
        ((c₁ : F) * (x : F) / (Gamma : F) +
          (c₂ : F) * (x : F) / (Gamma : F)) :=
        (psi.character.map_add_eq_mul _ _).symm
    _ = psi.character (((c₁ + c₂ : lattice F (M - (q : ℤ))) : F) *
        (x : F) / (Gamma : F)) := by
      congr 1
      push_cast
      ring
    _ = psi.character ((c : F) * (x : F) / (Gamma : F)) := by
      apply Units.ext
      exact heval.symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Evaluation of an integer power of a continuous quasi-character. -/
@[simp]
theorem continuousQuasiChar_zpow_apply
    (theta : ContinuousQuasiChar F) (j : ℤ) (u : Fˣ) :
    (theta ^ j) u = (theta u) ^ j := by
  cases j with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc, ContinuousQuasiChar.inv_apply]

/-- On a common stationary layer, the integer power `theta^j` has quotient
class `j • s`. -/
theorem zpow
    {theta : ContinuousQuasiChar F} (psi : LocalAddCharData F)
    (M : ℤ) {q r : ℕ} (hrpos : 0 < r) (hrq : r ≤ q)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (s : LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
      (intCast_le_intCast_of_nat_le hrq))
    (hs : IsStationaryRestrictionClass F theta psi M hrpos hrq Gamma s)
    (j : ℤ) :
    IsStationaryRestrictionClass F (theta ^ j) psi M hrpos hrq Gamma
      (j • s) := by
  intro c hc x
  obtain ⟨c₀, hc₀⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) s
  have hclasses :
      latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c =
        latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M)
          (j • c₀) := by
    calc
      latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c =
          j • s := hc
      _ = j • latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M) c₀ := by rw [hc₀]
      _ = latticeQuotientMk F
          (sub_le_sub_left (intCast_le_intCast_of_nat_le hrq) M)
          (j • c₀) := (map_zsmul _ j c₀).symm
  have heval := congrArg
    (fun z : LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
        (intCast_le_intCast_of_nat_le hrq) ↦
      (lamprechtPairingLeft F psi (intCast_le_intCast_of_nat_le hrq)
        Gamma hGamma z)
        (latticeQuotientMk F (intCast_le_intCast_of_nat_le hrq) x)) hclasses
  rw [lamprechtPairingLeft_apply, lamprechtPairingLeft_apply,
    lamprechtPairing_mk_mk, lamprechtPairing_mk_mk] at heval
  rw [continuousQuasiChar_zpow_apply, hs c₀ hc₀ x]
  calc
    psi.character ((c₀ : F) * (x : F) / (Gamma : F)) ^ j =
        psi.character (j • ((c₀ : F) * (x : F) / (Gamma : F))) :=
      (AddChar.map_zsmul_eq_zpow psi.character.toAddChar j _).symm
    _ = psi.character (((j • c₀ : lattice F (M - (q : ℤ))) : F) *
        (x : F) / (Gamma : F)) := by
      congr 1
      push_cast
      simp only [zsmul_eq_mul]
      ring
    _ = psi.character ((c : F) * (x : F) / (Gamma : F)) := by
      apply Units.ext
      exact heval.symm

end IsStationaryRestrictionClass

/-! ## Leading-class cancellation -/

/-- The canonical minimal stationary depth `ceil(q/2)`. -/
def lamprechtHalfDepth (q : ℕ) : ℕ :=
  q ⌈/⌉ 2

/-- For `q>1`, the minimal stationary depth is admissible. -/
theorem lamprechtHalfDepth_isDepth {q : ℕ} (hq : 1 < q) :
    IsLamprechtStationaryDepth q (lamprechtHalfDepth q) := by
  refine ⟨hq, ?_, ?_⟩
  · have h := le_smul_ceilDiv (b := q) (by omega : 0 < (2 : ℕ))
    simpa only [lamprechtHalfDepth, two_nsmul, two_mul] using h
  · have hle : lamprechtHalfDepth q ≤ q - 1 := by
      rw [lamprechtHalfDepth, ceilDiv_le_iff_le_mul (by omega : 0 < (2 : ℕ))]
      omega
    omega

/-- If `q' < q`, then the minimal depth for `q'` is no deeper than every
admissible depth for `q`. -/
theorem lamprechtHalfDepth_le_of_conductor_lt
    {q q' r : ℕ} (hr : IsLamprechtStationaryDepth q r) (hdrop : q' < q) :
    lamprechtHalfDepth q' ≤ r := by
  rw [lamprechtHalfDepth, ceilDiv_le_iff_le_mul (by omega : 0 < (2 : ℕ))]
  have hhalf := hr.half_le
  omega

/-- Package a continuous quasi-character with an explicitly supplied exact
conductor. -/
abbrev quasiCharDataOfIsConductor
    (theta : ContinuousQuasiChar F) (q : ℕ)
    (hq : IsMultiplicativeConductor F theta q) : LocalQuasiCharData F :=
  ⟨theta, q, hq⟩

@[simp]
theorem quasiCharDataOfIsConductor_character
    (theta : ContinuousQuasiChar F) (q : ℕ)
    (hq : IsMultiplicativeConductor F theta q) :
    (quasiCharDataOfIsConductor F theta q hq).character = theta :=
  rfl

@[simp]
theorem quasiCharDataOfIsConductor_conductor
    (theta : ContinuousQuasiChar F) (q : ℕ)
    (hq : IsMultiplicativeConductor F theta q) :
    (quasiCharDataOfIsConductor F theta q hq).conductor = q :=
  rfl

/-- The conductor of a product is at most the common exact conductor of its
two factors. -/
theorem stationaryProductConductor_le
    {theta₁ theta₂ : ContinuousQuasiChar F} {q q' : ℕ}
    (h₁ : IsMultiplicativeConductor F theta₁ q)
    (h₂ : IsMultiplicativeConductor F theta₂ q)
    (hprod : IsMultiplicativeConductor F (theta₁ * theta₂) q') :
    q' ≤ q := by
  simpa only [max_self] using h₁.mul_conductor_le_max h₂ hprod

/-- Exact representative form of leading-class cancellation.  The
representatives are explicitly quantified, as in part (d) of the manuscript;
their membership criterion is independent of either representative because
their ambiguity is contained in `p^(M-q+1)`. -/
theorem stationaryLeadingCancellation_iff
    {theta₁ theta₂ : ContinuousQuasiChar F} (q q' : ℕ)
    (h₁ : IsMultiplicativeConductor F theta₁ q)
    (h₂ : IsMultiplicativeConductor F theta₂ q)
    (hprod : IsMultiplicativeConductor F (theta₁ * theta₂) q')
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth q r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (c₁ c₂ : lattice F (M - (q : ℤ)))
    (hc₁ : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor M) c₁ =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma)
    (hc₂ : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor M) c₂ =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma) :
    q' < q ↔ (c₁ : F) + (c₂ : F) ∈ lattice F (M - (q : ℤ) + 1) := by
  have hs₁ : IsStationaryRestrictionClass F theta₁ psi M hr.pos
      hr.le_conductor Gamma
      (stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma) :=
    stationaryNumeratorClass_isRestriction F
      (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma
  have hs₂ : IsStationaryRestrictionClass F theta₂ psi M hr.pos
      hr.le_conductor Gamma
      (stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma) :=
    stationaryNumeratorClass_isRestriction F
      (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma
  have hprodRestriction := IsStationaryRestrictionClass.mul F psi M hr.pos
    hr.le_conductor Gamma hGamma _ _ hs₁ hs₂
  have hsumClass :
      latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) (c₁ + c₂) =
        stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma +
          stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma := by
    rw [latticeQuotientMk_add, hc₁, hc₂]
  have hrPred : r ≤ q - 1 := by
    have hupper := hr.le_predecessor
    omega
  have hpredPos : 0 < q - 1 := by
    have hq := hr.conductor_gt_one
    omega
  constructor
  · intro hdrop
    have htriv : QuasiCharTrivialOnUnitFiltration F (theta₁ * theta₂) (q - 1) :=
      hprod.trivialOnUnitFiltration_iff.2 (by omega)
    have hann : (c₁ : F) + (c₂ : F) ∈
        lattice F (M - ((q - 1 : ℕ) : ℤ)) := by
      apply (lamprechtAnnihilatorLeft F psi hGamma).1
      intro x hx
      let xPred : lattice F ((q - 1 : ℕ) : ℤ) := ⟨x, hx⟩
      let xr : lattice F (r : ℤ) :=
        ⟨x, lattice_antitone F (intCast_le_intCast_of_nat_le hrPred) hx⟩
      have hlinear := hprodRestriction (c₁ + c₂) hsumClass xr
      have hunit :
          (positiveUnitOfLattice F hr.pos xr : Fˣ) =
            positiveUnitOfLattice F hpredPos xPred := by
        apply Units.ext
        simp [xr, xPred]
      have hvalue := htriv
        (positiveUnitOfLattice F hpredPos xPred)
        (positiveUnitOfLattice F hpredPos xPred).property
      rw [hunit, hvalue] at hlinear
      simpa only [Submodule.coe_add] using hlinear.symm
    simpa only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one,
      show M - ((q : ℤ) - 1) = M - (q : ℤ) + 1 by omega] using hann
  · intro hcancel
    have hcancel' : (c₁ : F) + (c₂ : F) ∈
        lattice F (M - ((q - 1 : ℕ) : ℤ)) := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one,
        show M - ((q : ℤ) - 1) = M - (q : ℤ) + 1 by omega] using hcancel
    have htriv : QuasiCharTrivialOnUnitFiltration F
        (theta₁ * theta₂) (q - 1) := by
      intro u hu
      let uPred : unitFiltration F (q - 1) := ⟨u, hu⟩
      let xPred : lattice F ((q - 1 : ℕ) : ℤ) :=
        positiveUnitDisplacement F hpredPos uPred
      let xr : lattice F (r : ℤ) :=
        ⟨(xPred : F), lattice_antitone F
          (intCast_le_intCast_of_nat_le hrPred) xPred.property⟩
      have hlinear := hprodRestriction (c₁ + c₂) hsumClass xr
      have hunit : (positiveUnitOfLattice F hr.pos xr : Fˣ) = u := by
        apply Units.ext
        simp [xr, xPred, uPred]
      rw [hunit] at hlinear
      rw [hlinear]
      apply (lamprechtAnnihilatorLeft F psi hGamma).2 hcancel'
      exact xPred.property
    have hq'le := hprod.minimal (q - 1) htriv
    omega

/-- Projection of a stationary class to its final nontrivial candidate
layer `q-1`. -/
noncomputable def stationaryLeadingClassProjection
    (M : ℤ) {q r : ℕ} (hr : IsLamprechtStationaryDepth q r) :
    LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
        hr.int_le_conductor →ₗ[ringOfIntegers F]
      LamprechtCoefficientQuotient F M (q : ℤ) ((q - 1 : ℕ) : ℤ)
        (intCast_le_intCast_of_nat_le (Nat.sub_le q 1)) :=
  stationaryClassRestriction F M hr
    (Nat.le_sub_of_add_le hr.le_predecessor) (by
      have hq := hr.conductor_gt_one
      omega)

/-- Quotient-level form of the exact cancellation criterion: the product
conductor drops exactly when the sum of stationary classes has zero leading
projection. -/
theorem stationaryLeadingClassCancellation_iff
    {theta₁ theta₂ : ContinuousQuasiChar F} (q q' : ℕ)
    (h₁ : IsMultiplicativeConductor F theta₁ q)
    (h₂ : IsMultiplicativeConductor F theta₂ q)
    (hprod : IsMultiplicativeConductor F (theta₁ * theta₂) q')
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth q r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    q' < q ↔
      stationaryLeadingClassProjection F M hr
        (stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F theta₁ q h₁)
            psi M hr Gamma hGamma +
          stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F theta₂ q h₂)
            psi M hr Gamma hGamma) = 0 := by
  obtain ⟨c₁, hc₁⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass F
      (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma)
  obtain ⟨c₂, hc₂⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass F
      (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma)
  have hqOne : 1 ≤ q := by
    have hq := hr.conductor_gt_one
    omega
  rw [← hc₁, ← hc₂, ← latticeQuotientMk_add,
    stationaryLeadingClassProjection, stationaryClassRestriction,
    latticeQuotientProjection_mk, latticeQuotientMk_eq_zero_iff]
  constructor
  · intro hdrop
    have hcancel := (stationaryLeadingCancellation_iff F q q' h₁ h₂ hprod
      psi M hr Gamma hGamma c₁ c₂ hc₁ hc₂).1 hdrop
    simpa only [Submodule.coe_add, Nat.cast_sub hqOne, Nat.cast_one,
      show M - ((q : ℤ) - 1) = M - (q : ℤ) + 1 by omega] using hcancel
  · intro hcancel
    apply (stationaryLeadingCancellation_iff F q q' h₁ h₂ hprod
      psi M hr Gamma hGamma c₁ c₂ hc₁ hc₂).2
    simpa only [Submodule.coe_add, Nat.cast_sub hqOne, Nat.cast_one,
      show M - ((q : ℤ) - 1) = M - (q : ℤ) + 1 by omega] using hcancel

/-! ## The class after a conductor drop -/

/-- Construct the stationary class at the dropped conductor and its own
minimal depth, then map that class into the old quotient.  This definition
does not construct a class at the old depth for the new conductor (which
would not even be a valid stationary depth in general). -/
noncomputable def droppedStationaryClassRestriction
    (prod : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (M : ℤ) {q r : ℕ} (hr : IsLamprechtStationaryDepth q r)
    (hdrop : prod.conductor < q) (hprod : 1 < prod.conductor)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    LamprechtCoefficientQuotient F M (q : ℤ) (r : ℤ)
      hr.int_le_conductor :=
  latticeQuotientChangeBounds F
    (sub_le_sub_left (lamprechtHalfDepth_isDepth hprod).int_le_conductor M)
    (sub_le_sub_left hr.int_le_conductor M)
    (sub_le_sub_left
      (intCast_le_intCast_of_nat_le (Nat.le_of_lt hdrop)) M)
    (sub_le_sub_left
      (intCast_le_intCast_of_nat_le
        (lamprechtHalfDepth_le_of_conductor_lt hr hdrop)) M)
    (stationaryNumeratorClass F prod psi M
      (lamprechtHalfDepth_isDepth hprod) Gamma hGamma)

/-- When the product conductor drops but remains greater than one, the class
newly constructed at `q'` and `ceil(q'/2)` restricts to the sum of the two old
stationary classes. -/
theorem stationaryClass_afterConductorDrop
    {theta₁ theta₂ : ContinuousQuasiChar F} (q q' : ℕ)
    (h₁ : IsMultiplicativeConductor F theta₁ q)
    (h₂ : IsMultiplicativeConductor F theta₂ q)
    (hprod : IsMultiplicativeConductor F (theta₁ * theta₂) q')
    (hdrop : q' < q) (hq' : 1 < q')
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth q r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    droppedStationaryClassRestriction F
        (quasiCharDataOfIsConductor F (theta₁ * theta₂) q' hprod)
        psi M hr hdrop hq' Gamma hGamma =
      stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F theta₁ q h₁)
          psi M hr Gamma hGamma +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F theta₂ q h₂)
          psi M hr Gamma hGamma := by
  let prod := quasiCharDataOfIsConductor F (theta₁ * theta₂) q' hprod
  let hr' : IsLamprechtStationaryDepth q' (lamprechtHalfDepth q') :=
    lamprechtHalfDepth_isDepth hq'
  have hhalfOld : lamprechtHalfDepth q' ≤ r :=
    lamprechtHalfDepth_le_of_conductor_lt hr hdrop
  obtain ⟨c', hc'⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr'.int_le_conductor M)
    (stationaryNumeratorClass F prod psi M hr' Gamma hGamma)
  obtain ⟨c₁, hc₁⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass F
      (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma)
  obtain ⟨c₂, hc₂⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor M)
    (stationaryNumeratorClass F
      (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma)
  rw [droppedStationaryClassRestriction, ← hc',
    latticeQuotientChangeBounds_mk, ← hc₁, ← hc₂, ← latticeQuotientMk_add]
  apply lamprechtPairingLeft_injective F psi hr.int_le_conductor Gamma hGamma
  apply AddChar.ext
  intro z
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F hr.int_le_conductor z
  rw [lamprechtPairingLeft_apply, lamprechtPairingLeft_apply,
    lamprechtPairing_mk_mk, lamprechtPairing_mk_mk]
  let x' : lattice F (lamprechtHalfDepth q' : ℤ) :=
    ⟨(x : F), lattice_antitone F
      (intCast_le_intCast_of_nat_le hhalfOld) x.property⟩
  have hnew := stationaryNumeratorClass_linearization
    F prod psi M hr' Gamma hGamma c' hc' x'
  have hs₁ := stationaryNumeratorClass_isRestriction F
    (quasiCharDataOfIsConductor F theta₁ q h₁) psi M hr Gamma hGamma
  have hs₂ := stationaryNumeratorClass_isRestriction F
    (quasiCharDataOfIsConductor F theta₂ q h₂) psi M hr Gamma hGamma
  have hprodOld := IsStationaryRestrictionClass.mul F psi M hr.pos
    hr.le_conductor Gamma hGamma _ _ hs₁ hs₂
  have hsumClass :
      latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) (c₁ + c₂) =
        stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F theta₁ q h₁)
            psi M hr Gamma hGamma +
          stationaryNumeratorClass F
            (quasiCharDataOfIsConductor F theta₂ q h₂)
            psi M hr Gamma hGamma := by
    rw [latticeQuotientMk_add, hc₁, hc₂]
  have hold := hprodOld (c₁ + c₂) hsumClass x
  have hunit :
      (positiveUnitOfLattice F hr'.pos x' : Fˣ) =
        positiveUnitOfLattice F hr.pos x := by
    apply Units.ext
    simp [x']
  rw [hunit] at hnew
  exact congrArg Units.val (hnew.symm.trans hold)

/-- Every representative of the newly constructed dropped-conductor class
is congruent on the old layer to every chosen sum of representatives of the
old classes.  The new representative remains typed in
`p^(M-q')`; it is only embedded into the old numerator for this comparison. -/
theorem stationaryClass_afterConductorDrop_representatives
    {theta₁ theta₂ : ContinuousQuasiChar F} (q q' : ℕ)
    (h₁ : IsMultiplicativeConductor F theta₁ q)
    (h₂ : IsMultiplicativeConductor F theta₂ q)
    (hprod : IsMultiplicativeConductor F (theta₁ * theta₂) q')
    (hdrop : q' < q) (hq' : 1 < q')
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth q r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ))
    (c' : lattice F (M - (q' : ℤ)))
    (hc' : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtHalfDepth_isDepth hq').int_le_conductor M) c' =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F (theta₁ * theta₂) q' hprod)
        psi M (lamprechtHalfDepth_isDepth hq') Gamma hGamma)
    (c₁ c₂ : lattice F (M - (q : ℤ)))
    (hc₁ : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor M) c₁ =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F theta₁ q h₁)
        psi M hr Gamma hGamma)
    (hc₂ : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor M) c₂ =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F theta₂ q h₂)
        psi M hr Gamma hGamma) :
    (c' : F) - ((c₁ : F) + (c₂ : F)) ∈ lattice F (M - (r : ℤ)) := by
  have hclass := stationaryClass_afterConductorDrop F q q' h₁ h₂ hprod
    hdrop hq' psi M hr Gamma hGamma
  have hnum : M - (q : ℤ) ≤ M - (q' : ℤ) :=
    sub_le_sub_left
      (intCast_le_intCast_of_nat_le (Nat.le_of_lt hdrop)) M
  have heq :
      latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M)
          ⟨(c' : F), lattice_antitone F hnum c'.property⟩ =
        latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M)
          (c₁ + c₂) := by
    calc
      _ = droppedStationaryClassRestriction F
          (quasiCharDataOfIsConductor F (theta₁ * theta₂) q' hprod)
          psi M hr hdrop hq' Gamma hGamma := by
        rw [droppedStationaryClassRestriction, ← hc',
          latticeQuotientChangeBounds_mk]
      _ = _ := hclass
      _ = latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c₁ +
          latticeQuotientMk F (sub_le_sub_left hr.int_le_conductor M) c₂ := by
        rw [hc₁, hc₂]
      _ = _ := (latticeQuotientMk_add F _ c₁ c₂).symm
  simpa only [Submodule.coe_add] using
    (latticeQuotientMk_eq_mk_iff F
      (sub_le_sub_left hr.int_le_conductor M)).1 heq

/-- At conductor zero or one there is no admissible stationary depth, hence
no stationary parameter is retained. -/
theorem noStationaryClass_of_conductor_le_one {q : ℕ} (hq : q ≤ 1) :
    ¬ ∃ r : ℕ, IsLamprechtStationaryDepth q r := by
  rintro ⟨r, hr⟩
  exact (not_lt_of_ge hq) hr.conductor_gt_one

/-- Principal exported theorem for the stationary-class calculus: after a
non-endpoint conductor drop, the newly constructed class at the new depth
restricts to the sum on the old layer. -/
theorem stationaryClassCalculus
    {theta₁ theta₂ : ContinuousQuasiChar F} (q q' : ℕ)
    (h₁ : IsMultiplicativeConductor F theta₁ q)
    (h₂ : IsMultiplicativeConductor F theta₂ q)
    (hprod : IsMultiplicativeConductor F (theta₁ * theta₂) q')
    (hdrop : q' < q) (hq' : 1 < q')
    (psi : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth q r)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((M + psi.conductor : ℤ) : WithTop ℤ)) :
    droppedStationaryClassRestriction F
        (quasiCharDataOfIsConductor F (theta₁ * theta₂) q' hprod)
        psi M hr hdrop hq' Gamma hGamma =
      stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F theta₁ q h₁)
          psi M hr Gamma hGamma +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F theta₂ q h₂)
          psi M hr Gamma hGamma :=
  stationaryClass_afterConductorDrop F q q' h₁ h₂ hprod hdrop hq'
    psi M hr Gamma hGamma

end

end LanglandsFirstMainLemma
