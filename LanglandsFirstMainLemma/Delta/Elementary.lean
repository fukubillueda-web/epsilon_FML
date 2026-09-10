import LanglandsFirstMainLemma.Delta.FiniteDefinition

/-!
# Elementary identities for the computational local constant

This file proves the elementary identities following Langlands's definition of
`Delta`.  Additive scaling is proved on the representative-free finite sum,
and the inverse formula is proved by the finite reindexing `u \mapsto -u`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators ComplexConjugate Pointwise

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## Scaling the additive character -/

/-- The integer order of a nonzero field element bundled as a unit. -/
def unitOrder (a : Fˣ) : ℤ :=
  (ord F (a : F)).untop₀

@[simp]
theorem ord_coe_eq_unitOrder (a : Fˣ) :
    ord F (a : F) = (unitOrder F a : WithTop ℤ) :=
  (WithTop.coe_untop₀_of_ne_top ((ord_ne_top_iff F).2 (Units.ne_zero a))).symm

/-- Multiplication by a fixed field element as a continuous additive map. -/
private def continuousMulLeft (a : F) : ContinuousAddMonoidHom F F :=
  ⟨AddMonoidHom.mulLeft a, continuous_const_mul a⟩

/-- The additive character `ψ^a(x) = ψ(ax)`, with its exact conductor
`n(ψ^a) = n(ψ) + ord(a)`. -/
def scaleAddCharData (ψ : LocalAddCharData F) (a : Fˣ) : LocalAddCharData F where
  character := ψ.character.pullback (continuousMulLeft F (a : F))
  conductor := ψ.conductor + unitOrder F a
  isConductor := by
    let r := unitOrder F a
    have haord : ord F (a : F) = (r : WithTop ℤ) := ord_coe_eq_unitOrder F a
    refine ⟨?_, ?_⟩
    · intro x hx
      change ψ.character ((a : F) * x) = 1
      apply ψ.isConductor.trivial
      have hx' : x ∈ lattice F (-(ψ.conductor + r)) := by
        simpa only [r] using hx
      have ha : (a : F) ∈ lattice F r := by
        rw [mem_lattice, haord]
      have hax := mul_mem_lattice F ha hx'
      simpa only [show r + -(ψ.conductor + r) = -ψ.conductor by omega] using hax
    · intro s hs
      have hψs : AddCharTrivialOnLattice F ψ.character (r + s) := by
        intro y hy
        have hy' : y ∈ (a : F) • lattice F s := by
          rw [lattice_smul_of_ord_eq F (a : F) r s haord]
          exact hy
        rw [Submodule.mem_smul_pointwise_iff_exists] at hy'
        obtain ⟨x, hx, rfl⟩ := hy'
        change ψ.character ((a : F) * x) = 1
        exact hs x hx
      have hmin := ψ.isConductor.minimal (r + s) hψs
      change -(ψ.conductor + r) ≤ s
      omega

@[simp]
theorem scaleAddCharData_character_apply
    (ψ : LocalAddCharData F) (a : Fˣ) (x : F) :
    (scaleAddCharData F ψ a).character x = ψ.character ((a : F) * x) := by
  change ψ.character ((continuousMulLeft F (a : F)) x) = _
  rfl

@[simp]
theorem scaleAddCharData_conductor
    (ψ : LocalAddCharData F) (a : Fˣ) :
    (scaleAddCharData F ψ a).conductor = ψ.conductor + unitOrder F a := by
  simp [scaleAddCharData]

/-- If `γ` is admissible for `(χ, ψ)`, then `aγ` is admissible for
`(χ, ψ^a)`. -/
def scaleAdmissibleGamma {χ : LocalQuasiCharData F} {ψ : LocalAddCharData F}
    (a : Fˣ) (γ : AdmissibleGamma F χ ψ) :
    AdmissibleGamma F χ (scaleAddCharData F ψ a) :=
  ⟨a * (γ : Fˣ), by
    change ord F ((a : F) * ((γ : Fˣ) : F)) = _
    rw [ord_mul, ord_coe_eq_unitOrder F a, γ.property]
    change (unitOrder F a : WithTop ℤ) +
        (((χ.conductor : ℤ) + ψ.conductor : ℤ) : WithTop ℤ) =
      (((χ.conductor : ℤ) + (ψ.conductor + unitOrder F a) : ℤ) : WithTop ℤ)
    norm_cast
    omega⟩

/-- At the numerator-representative level, scaling `ψ` and replacing `γ` by
`aγ` leaves the Gauss summand unchanged. -/
theorem finiteGaussSummandRepresentative_scale
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (a : Fˣ) (γ : AdmissibleGamma F χ ψ) (u : unitFiltration F 0) :
    finiteGaussSummandRepresentative χ (scaleAddCharData F ψ a)
        (scaleAdmissibleGamma F a γ) u =
      finiteGaussSummandRepresentative χ ψ γ u := by
  have harg :
      (a : F) *
          (((u : Fˣ) : F) /
            (((scaleAdmissibleGamma F a γ : Fˣ) : F))) =
        ((u : Fˣ) : F) / ((γ : Fˣ) : F) := by
    change (a : F) *
        (((u : Fˣ) : F) / ((a : F) * ((γ : Fˣ) : F))) = _
    field_simp [Units.ne_zero a, Units.ne_zero (γ : Fˣ)]
  simp only [finiteGaussSummandRepresentative,
    scaleAddCharData_character_apply, harg]

/-- The representative-free finite Gauss sum is unchanged under the paired
replacement `(ψ, γ) \mapsto (ψ^a, aγ)`. -/
theorem finiteGaussSum_scale
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (a : Fˣ) (γ : AdmissibleGamma F χ ψ) :
    finiteGaussSum χ (scaleAddCharData F ψ a)
        (scaleAdmissibleGamma F a γ) =
      finiteGaussSum χ ψ γ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  change (∑ z, finiteGaussSummand χ (scaleAddCharData F ψ a)
      (scaleAdmissibleGamma F a γ) z) =
    ∑ z, finiteGaussSummand χ ψ γ z
  apply Finset.sum_congr rfl
  intro z _hz
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
  simp only [finiteGaussSummand_mk]
  exact finiteGaussSummandRepresentative_scale F χ ψ a γ u

/-- Additive scaling at the naturally transported admissible denominator. -/
theorem deltaFinite_scale_at_scaleAdmissibleGamma
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (a : Fˣ) (γ : AdmissibleGamma F χ ψ) :
    deltaFinite χ (scaleAddCharData F ψ a)
        (scaleAdmissibleGamma F a γ) =
      (χ.character a : ℂ) * deltaFinite χ ψ γ := by
  have hχ :
      (χ.character (a * (γ : Fˣ)) : ℂ) =
        (χ.character a : ℂ) * (χ.character (γ : Fˣ) : ℂ) :=
    congrArg Units.val (map_mul χ.character a (γ : Fˣ))
  rw [deltaFinite, deltaFinite, finiteGaussSum_scale F χ ψ a γ]
  change (χ.character (a * (γ : Fˣ)) : ℂ) * _ = _
  rw [hχ]
  ring

/-- Change of additive character, with arbitrary admissible denominators:
`Delta(χ, ψ^a) = χ(a) Delta(χ, ψ)`. -/
theorem delta_additive_scale
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F) (a : Fˣ)
    (γ : AdmissibleGamma F χ ψ)
    (γa : AdmissibleGamma F χ (scaleAddCharData F ψ a)) :
    deltaFinite χ (scaleAddCharData F ψ a) γa =
      (χ.character a : ℂ) * deltaFinite χ ψ γ := by
  calc
    deltaFinite χ (scaleAddCharData F ψ a) γa =
        deltaFinite χ (scaleAddCharData F ψ a)
          (scaleAdmissibleGamma F a γ) :=
      deltaFinite_gamma_independent χ (scaleAddCharData F ψ a)
        (scaleAdmissibleGamma F a γ) γa
    _ = (χ.character a : ℂ) * deltaFinite χ ψ γ :=
      deltaFinite_scale_at_scaleAdmissibleGamma F χ ψ a γ

/-! ## Residual additive-character normalization -/

/-- Any prescribed nontrivial additive character of the residue field is a
unique nonzero scalar shift of a fixed nontrivial one; the scalar has a lift
to a local unit.  This is the normalization used for residual characters. -/
theorem residual_addChar_normalization
    (ψbar ψcan : AddChar (ResidueField F) ℂ)
    (hψbar : ψbar ≠ 1) (hψcan : ψcan ≠ 1) :
    ∃ a : unitGroup F,
      ψbar.mulShift ((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) = ψcan := by
  letI := residueFieldFintype F
  have hbij : Function.Bijective ψbar.mulShift := by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hψbar), rfl⟩
  obtain ⟨c, hc⟩ := hbij.surjective ψcan
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hψcan
    rw [← hc, hc0, AddChar.mulShift_zero]
  let cunit : (ResidueField F)ˣ := Units.mk0 c hc0
  obtain ⟨a, ha⟩ := residueUnits_surjective F cunit
  refine ⟨a, ?_⟩
  rw [ha]
  exact hc

/-! ## The trivial quasi-character -/

/-- The globally trivial quasi-character, with exact multiplicative conductor
zero. -/
def trivialQuasiCharData : LocalQuasiCharData F :=
  LocalQuasiCharData.of_zero (1 : ContinuousQuasiChar F) (by
    intro u _hu
    exact ContinuousQuasiChar.one_apply u)

@[simp]
theorem trivialQuasiCharData_character_apply (x : Fˣ) :
    (trivialQuasiCharData F).character x = 1 := by
  rfl

@[simp]
theorem trivialQuasiCharData_conductor :
    (trivialQuasiCharData F).conductor = 0 := by
  rfl

/-- For the trivial multiplicative character the finite unit quotient is a
singleton and its unique Gauss summand is one. -/
theorem finiteGaussSum_trivial_character
    (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F (trivialQuasiCharData F) ψ) :
    finiteGaussSum (trivialQuasiCharData F) ψ γ = 1 := by
  letI := unitFiltrationQuotientFintype F
    (Nat.zero_le (trivialQuasiCharData F).conductor)
  have hsub : ∀ z : UnitFiltrationQuotient F 0
      (trivialQuasiCharData F).conductor (Nat.zero_le _), z = 1 := by
    intro z
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
      (Nat.zero_le (trivialQuasiCharData F).conductor) z
    apply (unitFiltrationQuotientMk_eq_one_iff F
      (Nat.zero_le (trivialQuasiCharData F).conductor) u).2
    simpa only [trivialQuasiCharData_conductor] using u.property
  have hsingle :
      finiteGaussSum (trivialQuasiCharData F) ψ γ =
        finiteGaussSummand (trivialQuasiCharData F) ψ γ 1 := by
    change (∑ z : UnitFiltrationQuotient F 0
      (trivialQuasiCharData F).conductor (Nat.zero_le _),
        finiteGaussSummand (trivialQuasiCharData F) ψ γ z) = _
    calc
      _ = ∑ _z : UnitFiltrationQuotient F 0
          (trivialQuasiCharData F).conductor (Nat.zero_le _),
          finiteGaussSummand (trivialQuasiCharData F) ψ γ 1 := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [hsub z]
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ]
        have hcard : Fintype.card (UnitFiltrationQuotient F 0
            (trivialQuasiCharData F).conductor (Nat.zero_le _)) = 1 := by
          apply Fintype.card_eq_one_iff.mpr
          exact ⟨1, hsub⟩
        rw [hcard]
        simp
  rw [hsingle]
  change finiteGaussSummand (trivialQuasiCharData F) ψ γ
    (unitFiltrationQuotientMk F
      (Nat.zero_le (trivialQuasiCharData F).conductor)
      (1 : unitFiltration F 0)) = 1
  rw [finiteGaussSummand_mk, finiteGaussSummandRepresentative]
  have hγ : ord F ((γ : Fˣ) : F) = (ψ.conductor : WithTop ℤ) := by
    simpa only [trivialQuasiCharData_conductor, Nat.cast_zero, zero_add] using γ.property
  have harg : (1 : F) / ((γ : Fˣ) : F) ∈ lattice F (-ψ.conductor) := by
    apply (div_mem_lattice_iff F ((γ : Fˣ) : F) 1
      ψ.conductor (-ψ.conductor) hγ).2
    simp
  have hψ := ψ.isConductor.trivial _ harg
  change (ψ.character ((1 : F) / ((γ : Fˣ) : F)) : ℂ) *
    ((trivialQuasiCharData F).character (1 : Fˣ) : ℂ)⁻¹ = 1
  rw [hψ]
  simp

/-- Langlands's local constant of the trivial multiplicative character is
exactly one. -/
@[simp]
theorem delta_trivial_character
    (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F (trivialQuasiCharData F) ψ) :
    deltaFinite (trivialQuasiCharData F) ψ γ = 1 := by
  rw [deltaFinite, finiteGaussSum_trivial_character F ψ γ]
  simp [phase]

/-! ## Inverse pairing -/

/-- Inverting a quasi-character preserves its exact conductor. -/
abbrev inverseQuasiCharData (χ : LocalQuasiCharData F) : LocalQuasiCharData F where
  character := χ.character⁻¹
  conductor := χ.conductor
  isConductor := χ.isConductor.inv

@[simp]
theorem inverseQuasiCharData_character_apply
    (χ : LocalQuasiCharData F) (x : Fˣ) :
    (inverseQuasiCharData F χ).character x = (χ.character x)⁻¹ := by
  rfl

@[simp]
theorem inverseQuasiCharData_conductor (χ : LocalQuasiCharData F) :
    (inverseQuasiCharData F χ).conductor = χ.conductor := by
  rfl

/-- A common admissible denominator for a character and its inverse. -/
def inverseAdmissibleGamma {χ : LocalQuasiCharData F} {ψ : LocalAddCharData F}
    (γ : AdmissibleGamma F χ ψ) :
    AdmissibleGamma F (inverseQuasiCharData F χ) ψ :=
  ⟨γ, by simpa using γ.property⟩

@[simp]
theorem inverseAdmissibleGamma_coe
    {χ : LocalQuasiCharData F} {ψ : LocalAddCharData F}
    (γ : AdmissibleGamma F χ ψ) :
    (inverseAdmissibleGamma F γ : Fˣ) = (γ : Fˣ) :=
  rfl

/-- Proof-bearing local quasi-character data are determined by their
character; uniqueness of the exact conductor supplies the remaining field. -/
theorem LocalQuasiCharData.ext_character
    {χ ω : LocalQuasiCharData F} (h : χ.character = ω.character) : χ = ω := by
  cases χ with
  | mk χ m hχ =>
      cases ω with
      | mk ω n hω =>
          dsimp at h
          subst ω
          have hmn : m = n := hχ.unique hω
          subst n
          rfl

/-- A proof-bearing character datum whose underlying character is trivial is
the conductor-zero trivial datum, so its local constant is one. -/
theorem delta_trivial_of_character_eq_one
    (χ : LocalQuasiCharData F) (hχ : χ.character = 1)
    (ψ : LocalAddCharData F) (γ : AdmissibleGamma F χ ψ) :
    deltaFinite χ ψ γ = 1 := by
  have hdata : χ = trivialQuasiCharData F := by
    apply LocalQuasiCharData.ext_character F
    calc
      χ.character = 1 := hχ
      _ = (trivialQuasiCharData F).character := by
        ext x
        simp
  subst χ
  exact delta_trivial_character F ψ γ

/-- Every value of an exact local additive character has complex norm one.
The proof descends a numerator to a finite lattice quotient before using
finite order. -/
theorem localAddChar_norm_eq_one (ψ : LocalAddCharData F) (x : F) :
    ‖(ψ.character x : ℂ)‖ = 1 := by
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨r, hr⟩ :=
    WithTop.ne_top_iff_exists.mp ((ord_ne_top_iff F).2 hx0)
  by_cases htriv : -ψ.conductor ≤ r
  · have hx : x ∈ lattice F (-ψ.conductor) := by
      rw [mem_lattice, ← hr]
      exact_mod_cast htriv
    rw [show ψ.character x = 1 from ψ.isConductor.trivial x hx]
    simp
  · have hrs : r ≤ -ψ.conductor := le_of_lt (lt_of_not_ge htriv)
    letI := latticeQuotientFintype F hrs
    let x₀ : lattice F r := ⟨x, by rw [mem_lattice, hr]⟩
    let z : LatticeQuotient F r (-ψ.conductor) hrs :=
      latticeQuotientMk F hrs x₀
    obtain ⟨k, hkpos, hk⟩ :=
      (isOfFinAddOrder_of_finite z).exists_nsmul_eq_zero
    have hmk : latticeQuotientMk F hrs (k • x₀) = 0 := by
      simpa [z] using hk
    have hkx : k • x ∈ lattice F (-ψ.conductor) := by
      have := (latticeQuotientMk_eq_zero_iff F hrs).1 hmk
      simpa [x₀] using this
    have hψkx : ψ.character (k • x) = 1 :=
      ψ.isConductor.trivial _ hkx
    have hpowUnits : (ψ.character x) ^ k = 1 := by
      exact (AddChar.map_nsmul_eq_pow ψ.character.toAddChar k x).symm.trans hψkx
    have hpow : ((ψ.character x : ℂ) ^ k) = 1 :=
      congrArg Units.val hpowUnits
    have hfin : IsOfFinOrder (ψ.character x : ℂ) :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨k, hkpos, hpow⟩
    exact hfin.norm_eq_one

/-- The element `-1` in the zeroth unit filtration. -/
private def negOneUnitFiltration : unitFiltration F 0 :=
  ⟨(-1 : Fˣ), by
    rw [mem_unitFiltration_zero]
    simp⟩

@[simp]
private theorem coe_negOneUnitFiltration :
    (negOneUnitFiltration F : Fˣ) = -1 :=
  rfl

/-- The inverse-character summand at `-u` is the conjugate original
summand, multiplied by `χ(-1)`. -/
theorem finiteGaussSummandRepresentative_inverse_neg
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (u : unitFiltration F 0) :
    finiteGaussSummandRepresentative (inverseQuasiCharData F χ) ψ
        (inverseAdmissibleGamma F γ) (negOneUnitFiltration F * u) =
      (χ.character (-1 : Fˣ) : ℂ) *
        conj (finiteGaussSummandRepresentative χ ψ γ u) := by
  let x : F := ((u : Fˣ) : F) / ((γ : Fˣ) : F)
  have harg :
      ((((negOneUnitFiltration F * u : unitFiltration F 0) : Fˣ) : F) /
          (((inverseAdmissibleGamma F γ : Fˣ) : F))) = -x := by
    simp only [inverseAdmissibleGamma_coe, coe_negOneUnitFiltration,
      Subgroup.coe_mul, Units.val_mul, Units.val_neg, Units.val_one]
    change (-1 : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F) = -x
    dsimp [x]
    ring
  have hψneg : (ψ.character (-x) : ℂ) = (ψ.character x : ℂ)⁻¹ := by
    simpa only [ContinuousAddChar.toAddChar_apply, Units.val_inv_eq_inv_val] using
      congrArg Units.val (AddChar.map_neg_eq_inv ψ.character.toAddChar x)
  have hχmul :
      (χ.character ((negOneUnitFiltration F * u : unitFiltration F 0) : Fˣ) : ℂ) =
        (χ.character (-1 : Fˣ) : ℂ) * (χ.character (u : Fˣ) : ℂ) := by
    simpa only [Subgroup.coe_mul, coe_negOneUnitFiltration, Units.val_mul] using
      congrArg Units.val (map_mul χ.character (-1 : Fˣ) (u : Fˣ))
  have hψnorm : ‖(ψ.character x : ℂ)‖ = 1 :=
    localAddChar_norm_eq_one F ψ x
  have hχnorm : ‖(χ.character (u : Fˣ) : ℂ)‖ = 1 :=
    quasiChar_norm_eq_one_of_mem_unitFiltration_zero χ u
  have hconj :
      conj (finiteGaussSummandRepresentative χ ψ γ u) =
        (ψ.character x : ℂ)⁻¹ * (χ.character (u : Fˣ) : ℂ) := by
    rw [finiteGaussSummandRepresentative]
    change conj ((ψ.character x : ℂ) *
      (χ.character (u : Fˣ) : ℂ)⁻¹) = _
    rw [map_mul, map_inv₀, ← Complex.inv_eq_conj hψnorm,
      ← Complex.inv_eq_conj hχnorm, inv_inv]
  rw [finiteGaussSummandRepresentative]
  change (ψ.character
      ((((negOneUnitFiltration F * u : unitFiltration F 0) : Fˣ) : F) /
        (((inverseAdmissibleGamma F γ : Fˣ) : F))) : ℂ) *
      (((inverseQuasiCharData F χ).character
        ((negOneUnitFiltration F * u : unitFiltration F 0) : Fˣ) : ℂ))⁻¹ = _
  rw [harg, hψneg]
  simp only [ContinuousQuasiChar.inv_apply, Units.val_inv_eq_inv_val,
    inv_inv, hχmul, hconj]
  ring

/-- Representative-free form of the `u \mapsto -u` summand identity. -/
theorem finiteGaussSummand_inverse_neg
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ)
    (z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _)) :
    finiteGaussSummand (inverseQuasiCharData F χ) ψ
        (inverseAdmissibleGamma F γ)
        (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
          (negOneUnitFiltration F) * z) =
      (χ.character (-1 : Fˣ) : ℂ) *
        conj (finiteGaussSummand χ ψ γ z) := by
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
  rw [← unitFiltrationQuotientMk_mul]
  simp only [finiteGaussSummand_mk]
  exact finiteGaussSummandRepresentative_inverse_neg F χ ψ γ u

/-- Exact conjugation formula for the two finite Gauss sums. -/
theorem finiteGaussSum_inverse
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    finiteGaussSum (inverseQuasiCharData F χ) ψ
        (inverseAdmissibleGamma F γ) =
      (χ.character (-1 : Fˣ) : ℂ) * conj (finiteGaussSum χ ψ γ) := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  change (∑ z, finiteGaussSummand (inverseQuasiCharData F χ) ψ
      (inverseAdmissibleGamma F γ) z) =
    (χ.character (-1 : Fˣ) : ℂ) *
      conj (∑ z, finiteGaussSummand χ ψ γ z)
  rw [← sum_unitFiltrationQuotient_mul_left F (Nat.zero_le χ.conductor)
    (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
      (negOneUnitFiltration F))
    (finiteGaussSummand (inverseQuasiCharData F χ) ψ
      (inverseAdmissibleGamma F γ))]
  simp_rw [finiteGaussSummand_inverse_neg F χ ψ γ]
  rw [map_sum, Finset.mul_sum]

/-- The inverse-pairing identity at the common admissible denominator. -/
theorem deltaFinite_inverse_pair_at_common_gamma
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    deltaFinite χ ψ γ *
        deltaFinite (inverseQuasiCharData F χ) ψ
          (inverseAdmissibleGamma F γ) =
      (χ.character (-1 : Fˣ) : ℂ) := by
  let G := finiteGaussSum χ ψ γ
  let c := (χ.character (-1 : Fˣ) : ℂ)
  have hcNorm : ‖c‖ = 1 := by
    simpa [c] using quasiChar_norm_eq_one_of_mem_unitFiltration_zero χ
      (negOneUnitFiltration F)
  have hG0 : G ≠ 0 := finiteGaussSum_ne_zero χ ψ γ
  have hconjG0 : conj G ≠ 0 := by
    simpa using hG0
  have hphase : phase G * conj (phase G) = 1 := by
    rw [Complex.mul_conj', phase_norm]
    norm_num
  have hχγ0 : (χ.character (γ : Fˣ) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero χ.character (γ : Fˣ)
  rw [deltaFinite, deltaFinite, finiteGaussSum_inverse F χ ψ γ]
  change (χ.character (γ : Fˣ) : ℂ) * phase G *
      ((χ.character⁻¹ (γ : Fˣ) : ℂ) * phase (c * conj G)) = c
  simp only [ContinuousQuasiChar.inv_apply, Units.val_inv_eq_inv_val]
  rw [phase_mul_of_norm_eq_one hcNorm hconjG0, phase_conj]
  calc
    (χ.character (γ : Fˣ) : ℂ) * phase G *
        ((χ.character (γ : Fˣ) : ℂ)⁻¹ * (c * conj (phase G))) =
        c * (phase G * conj (phase G)) := by
      field_simp [hχγ0]
    _ = c := by rw [hphase, mul_one]

/-- Inverse pairing for a finite-order character, with arbitrary admissible
denominators: `Delta(μ,ψ) Delta(μ⁻¹,ψ) = μ(-1)`. -/
theorem delta_inverse_pair
    (χ χinv : LocalQuasiCharData F)
    (_hfinite : IsOfFinOrder χ.character)
    (hinv : χinv.character = χ.character⁻¹)
    (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ)
    (γinv : AdmissibleGamma F χinv ψ) :
    deltaFinite χ ψ γ * deltaFinite χinv ψ γinv =
      (χ.character (-1 : Fˣ) : ℂ) := by
  have hdata : χinv = inverseQuasiCharData F χ :=
    LocalQuasiCharData.ext_character F hinv
  subst χinv
  rw [deltaFinite_gamma_independent (inverseQuasiCharData F χ) ψ
    (inverseAdmissibleGamma F γ) γinv]
  exact deltaFinite_inverse_pair_at_common_gamma F χ ψ γ

/-! ## Product over an odd-prime character group -/

/-- Evaluation at a fixed field unit is a homomorphism on the group of
continuous quasi-characters. -/
private def quasiCharEval (x : Fˣ) : ContinuousQuasiChar F →* ℂˣ where
  toFun χ := χ x
  map_one' := rfl
  map_mul' _ _ := rfl

/-- If `S` is an odd-prime finite subgroup of local quasi-characters, then
the product of the associated local constants is one.  The proof pairs each
character with its inverse; the only fixed point is the trivial character. -/
theorem delta_odd_prime_character_product
    (S : Subgroup (ContinuousQuasiChar F)) [Fintype S]
    (_hprime : (Fintype.card S).Prime) (hodd : Odd (Fintype.card S))
    (ψ : LocalAddCharData F)
    (χ : S → LocalQuasiCharData F)
    (hχ : ∀ μ, (χ μ).character = (μ : ContinuousQuasiChar F))
    (γ : ∀ μ, AdmissibleGamma F (χ μ) ψ) :
    ∏ μ : S, deltaFinite (χ μ) ψ (γ μ) = 1 := by
  classical
  let f : S → ℂ := fun μ => deltaFinite (χ μ) ψ (γ μ)
  have hfinite (μ : S) : IsOfFinOrder (χ μ).character := by
    rw [hχ μ]
    exact S.subtype.isOfFinOrder (isOfFinOrder_of_finite μ)
  have hnegOne (μ : S) : (χ μ).character (-1 : Fˣ) = 1 := by
    let z : ℂˣ := (χ μ).character (-1 : Fˣ)
    have horderChar : orderOf (χ μ).character ∣ Fintype.card S := by
      rw [hχ μ]
      simpa only [Nat.card_eq_fintype_card] using
        S.orderOf_dvd_natCard μ.property
    have horderCard : orderOf z ∣ Fintype.card S :=
      (orderOf_map_dvd (quasiCharEval F (-1 : Fˣ)) (χ μ).character).trans horderChar
    have hz2 : z ^ 2 = 1 := by
      change ((χ μ).character (-1 : Fˣ)) ^ 2 = 1
      rw [← map_pow]
      norm_num
    have horder2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right horderCard horder2)
  have hcharacterInv (μ : S) :
      (χ μ⁻¹).character = (χ μ).character⁻¹ := by
    rw [hχ μ]
    simpa using hχ μ⁻¹
  have hpair (μ : S) : f μ * f μ⁻¹ = 1 := by
    calc
      f μ * f μ⁻¹ = ((χ μ).character (-1 : Fˣ) : ℂ) :=
        delta_inverse_pair F (χ μ) (χ μ⁻¹) (hfinite μ)
          (hcharacterInv μ) ψ (γ μ) (γ μ⁻¹)
      _ = 1 := congrArg Units.val (hnegOne μ)
  have hfixed (μ : S) (hμ : μ⁻¹ = μ) : μ = 1 := by
    have hμ2 : μ ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun t : S => t * μ) hμ.symm).trans (by simp)
    have horder2 : orderOf μ ∣ 2 := orderOf_dvd_of_pow_eq_one hμ2
    have horderCard : orderOf μ ∣ Fintype.card S := by
      simpa only [Nat.card_eq_fintype_card] using orderOf_dvd_natCard μ
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right horderCard horder2)
  have hone : f (1 : S) = 1 := by
    dsimp [f]
    exact delta_trivial_of_character_eq_one F (χ 1)
      (by simpa using hχ (1 : S)) ψ (γ 1)
  simpa [f] using
    (Finset.prod_involution (s := Finset.univ) (f := f)
      (fun μ _hμ => μ⁻¹)
      (fun μ _hμ => hpair μ)
      (fun μ _hμ hfμ hμ => hfμ (hfixed μ hμ ▸ hone))
      (fun μ _hμ => Finset.mem_univ μ⁻¹)
      (fun μ _hμ => inv_inv μ))

end

end LanglandsFirstMainLemma
