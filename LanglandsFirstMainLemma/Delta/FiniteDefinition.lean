import LanglandsFirstMainLemma.Basic.CharacterConductors
import LanglandsFirstMainLemma.LocalField.FiniteQuotients
import LanglandsFirstMainLemma.Basic.Phase

/-!
# The representative-free finite definition of Langlands's local constant

For exact conductor data `χ`, `ψ`, an admissible denominator has order
`χ.conductor + ψ.conductor`.  The local Gauss sum is the unnormalised sum over
`U_F^0 / U_F^χ.conductor`; its summand is descended before the finite sum is
taken.  This file also proves the sum nonzero.  That fact is needed here—not
merely downstream—because the total phase has value `1` at zero.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped Pointwise

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An admissible denominator for exact conductor data `(χ, ψ)`.  The equality
of orders is equivalent to the manuscript's principal-lattice equality
`γ 𝒪_F = 𝔭_F ^ (m + n)`. -/
abbrev AdmissibleGamma (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F) :=
  {γ : Fˣ //
    ord F (γ : F) =
      (((χ.conductor : ℤ) + ψ.conductor : ℤ) : WithTop ℤ)}

namespace AdmissibleGamma

variable {F} {χ : LocalQuasiCharData F} {ψ : LocalAddCharData F}

/-- The field value of an admissible denominator is nonzero. -/
@[simp]
theorem coe_ne_zero (γ : AdmissibleGamma F χ ψ) : ((γ : Fˣ) : F) ≠ 0 :=
  Units.ne_zero (γ : Fˣ)

/-- Admissibility in the manuscript's principal-lattice form. -/
theorem smul_lattice_zero (γ : AdmissibleGamma F χ ψ) :
    ((γ : Fˣ) : F) • lattice F 0 =
      lattice F ((χ.conductor : ℤ) + ψ.conductor) :=
  (smul_lattice_zero_eq_iff_ord_eq F ((γ : Fˣ) : F)
    ((χ.conductor : ℤ) + ψ.conductor)).2 γ.property

/-- Admissible denominators exist at every integer conductor depth. -/
theorem exists_admissible : Nonempty (AdmissibleGamma F χ ψ) := by
  obtain ⟨γ, hγ⟩ := exists_ord_eq F ((χ.conductor : ℤ) + ψ.conductor)
  have hγ0 : γ ≠ 0 := (ord_ne_top_iff F).1 (by rw [hγ]; simp)
  exact ⟨⟨Units.mk0 γ hγ0, hγ⟩⟩

/-- The ratio `γ'/γ` of two admissible denominators, as an element of `Fˣ`. -/
def ratio (γ' γ : AdmissibleGamma F χ ψ) : Fˣ :=
  (γ' : Fˣ) / (γ : Fˣ)

@[simp]
theorem coe_ratio (γ' γ : AdmissibleGamma F χ ψ) :
    (ratio γ' γ : F) = ((γ' : Fˣ) : F) / ((γ : Fˣ) : F) :=
  by simp [ratio]

/-- Two admissible denominators differ by a local unit. -/
theorem ratio_mem_unitFiltration (γ' γ : AdmissibleGamma F χ ψ) :
    ratio γ' γ ∈ unitFiltration F 0 := by
  rw [mem_unitFiltration_zero, coe_ratio, ord_div, γ'.property, γ.property]
  simp

/-- The ratio identity `γ' = (γ'/γ) γ`. -/
theorem ratio_mul (γ' γ : AdmissibleGamma F χ ψ) :
    ratio γ' γ * (γ : Fˣ) = (γ' : Fˣ) := by
  simp [ratio]

/-- The admissible ratio, bundled in the zeroth unit filtration. -/
def ratioUnit (γ' γ : AdmissibleGamma F χ ψ) : unitFiltration F 0 :=
  ⟨ratio γ' γ, ratio_mem_unitFiltration γ' γ⟩

@[simp]
theorem coe_ratioUnit (γ' γ : AdmissibleGamma F χ ψ) :
    (ratioUnit γ' γ : Fˣ) = ratio γ' γ :=
  rfl

end AdmissibleGamma

variable {F}

/-- The manuscript's local Gauss summand on a representative in `U_F^0`. -/
def finiteGaussSummandRepresentative
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (u : unitFiltration F 0) : ℂ :=
  (ψ.character (((u : Fˣ) : F) / ((γ : Fˣ) : F)) : ℂ) *
    (χ.character (u : Fˣ) : ℂ)⁻¹

/-- The local Gauss summand is unchanged when its unit representative is
changed modulo the exact multiplicative-conductor layer. -/
theorem finiteGaussSummandRepresentative_eq_of_congruent
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (u v : unitFiltration F 0)
    (huv : CongruentAtDepth (χ.conductor : ℤ)
      (((u : Fˣ) : F)) (((v : Fˣ) : F))) :
    finiteGaussSummandRepresentative χ ψ γ u =
      finiteGaussSummandRepresentative χ ψ γ v := by
  have huvUnit : (u : Fˣ) / (v : Fˣ) ∈ unitFiltration F χ.conductor :=
    (div_mem_unitFiltration_iff_congruentAtDepth F χ.conductor
      (u : Fˣ) (v : Fˣ)
      (unitFiltration_le_unitGroup F 0 u.property)
      (unitFiltration_le_unitGroup F 0 v.property)).2 huv
  have hχdiv : χ.character ((u : Fˣ) / (v : Fˣ)) = 1 :=
    χ.isConductor.trivial _ huvUnit
  have hχ : χ.character (u : Fˣ) = χ.character (v : Fˣ) := by
    have hmap := map_div χ.character (u : Fˣ) (v : Fˣ)
    rw [hχdiv] at hmap
    exact div_eq_one.mp hmap.symm
  have huvLattice : (((u : Fˣ) : F) - ((v : Fˣ) : F)) ∈
      lattice F (χ.conductor : ℤ) :=
    (congruentAtDepth_iff_sub_mem_lattice F (χ.conductor : ℤ)
      ((u : Fˣ) : F) ((v : Fˣ) : F)).1 huv
  have hdiff : ((((u : Fˣ) : F) - ((v : Fˣ) : F)) / ((γ : Fˣ) : F)) ∈
      lattice F (-ψ.conductor) := by
    apply (div_mem_lattice_iff F ((γ : Fˣ) : F)
      (((u : Fˣ) : F) - ((v : Fˣ) : F))
      ((χ.conductor : ℤ) + ψ.conductor) (-ψ.conductor)
      γ.property).2
    simpa only [add_neg_cancel_right] using huvLattice
  have hψdiff : ψ.character
      ((((u : Fˣ) : F) - ((v : Fˣ) : F)) / ((γ : Fˣ) : F)) = 1 :=
    ψ.isConductor.trivial _ hdiff
  have hψ : ψ.character (((u : Fˣ) : F) / ((γ : Fˣ) : F)) =
      ψ.character (((v : Fˣ) : F) / ((γ : Fˣ) : F)) := by
    have hadd := ContinuousAddChar.map_add_eq_mul ψ.character
      (((u : Fˣ) : F) / ((γ : Fˣ) : F) - ((v : Fˣ) : F) / ((γ : Fˣ) : F))
      (((v : Fˣ) : F) / ((γ : Fˣ) : F))
    rw [sub_add_cancel] at hadd
    have hsub : ((u : Fˣ) : F) / ((γ : Fˣ) : F) -
        ((v : Fˣ) : F) / ((γ : Fˣ) : F) =
        (((u : Fˣ) : F) - ((v : Fˣ) : F)) / ((γ : Fˣ) : F) := by ring
    rw [hsub, hψdiff, one_mul] at hadd
    exact hadd
  simp only [finiteGaussSummandRepresentative, hψ, hχ]

/-- The representative-independent local Gauss summand on
`U_F^0 / U_F^m`. -/
def finiteGaussSummand
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _) → ℂ :=
  unitFiltrationQuotientLift F (Nat.zero_le χ.conductor)
    (finiteGaussSummandRepresentative χ ψ γ)
    (finiteGaussSummandRepresentative_eq_of_congruent χ ψ γ)

/-- Evaluation on any numerator representative gives the manuscript's
summand.  This is the explicit quotient-representative independence theorem. -/
@[simp]
theorem finiteGaussSummand_mk
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (u : unitFiltration F 0) :
    finiteGaussSummand χ ψ γ
        (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) =
      finiteGaussSummandRepresentative χ ψ γ u :=
  rfl

/-- The unnormalised representative-free finite Gauss sum. -/
def finiteGaussSum
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) : ℂ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  exact ∑ u, finiteGaussSummand χ ψ γ u

/-- The restriction of a quasi-character to `U_F^0`, descended through its
exact conductor layer. -/
def quasiCharOnUnitQuotient (χ : LocalQuasiCharData F) :
    UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _) →* ℂˣ :=
  QuotientGroup.lift (unitFiltrationInside F (Nat.zero_le χ.conductor))
    (χ.character.toMonoidHom.comp (unitFiltration F 0).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact χ.isConductor.trivial _
        ((mem_unitFiltrationInside F (Nat.zero_le χ.conductor) u).1 hu))

@[simp]
theorem quasiCharOnUnitQuotient_mk (χ : LocalQuasiCharData F)
    (u : unitFiltration F 0) :
    quasiCharOnUnitQuotient χ
        (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) =
      χ.character (u : Fˣ) :=
  rfl

/-- A continuous quasi-character has absolute value one on `U_F^0`.  Here
this is proved algebraically from its exact conductor: the restriction factors
through the finite quotient `U_F^0/U_F^m`, hence every value has finite order. -/
theorem quasiChar_norm_eq_one_of_mem_unitFiltration_zero
    (χ : LocalQuasiCharData F) (u : unitFiltration F 0) :
    ‖(χ.character (u : Fˣ) : ℂ)‖ = 1 := by
  let q := unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u
  let φ : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _) →* ℂ :=
    (Units.coeHom ℂ).comp (quasiCharOnUnitQuotient χ)
  have hfin : IsOfFinOrder (φ q) :=
    φ.isOfFinOrder (isOfFinOrder_of_finite q)
  change ‖φ q‖ = 1
  exact hfin.norm_eq_one

/-- Changing denominator from `γ` to `γ'` and multiplying the numerator by
`γ'/γ` scales the representative summand by the inverse character value. -/
theorem finiteGaussSummandRepresentative_ratioUnit_mul
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ γ' : AdmissibleGamma F χ ψ) (u : unitFiltration F 0) :
    finiteGaussSummandRepresentative χ ψ γ'
        (AdmissibleGamma.ratioUnit γ' γ * u) =
      (χ.character (AdmissibleGamma.ratio γ' γ) : ℂ)⁻¹ *
        finiteGaussSummandRepresentative χ ψ γ u := by
  let a := AdmissibleGamma.ratioUnit γ' γ
  have harg :
      ((((a * u : unitFiltration F 0) : Fˣ) : F) / ((γ' : Fˣ) : F)) =
        ((u : Fˣ) : F) / ((γ : Fˣ) : F) := by
    change (((((a : Fˣ) * (u : Fˣ)) : Fˣ) : F) / ((γ' : Fˣ) : F)) =
      ((u : Fˣ) : F) / ((γ : Fˣ) : F)
    have hargUnits : ((a : Fˣ) * (u : Fˣ)) / (γ' : Fˣ) =
        (u : Fˣ) / (γ : Fˣ) := by
      rw [← AdmissibleGamma.ratio_mul γ' γ]
      simp [a, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa using congrArg Units.val hargUnits
  have hχmul :
      (χ.character ((a * u : unitFiltration F 0) : Fˣ) : ℂ) =
        (χ.character (a : Fˣ) : ℂ) * (χ.character (u : Fˣ) : ℂ) := by
    exact congrArg Units.val (map_mul χ.character (a : Fˣ) (u : Fˣ))
  rw [finiteGaussSummandRepresentative, finiteGaussSummandRepresentative, harg,
    hχmul, mul_inv_rev]
  change _ = (χ.character (a : Fˣ) : ℂ)⁻¹ * _
  ring

/-- The representative-free summand transformation under an admissible
change of denominator. -/
theorem finiteGaussSummand_ratioUnit_mul
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ γ' : AdmissibleGamma F χ ψ)
    (z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _)) :
    finiteGaussSummand χ ψ γ'
        (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
          (AdmissibleGamma.ratioUnit γ' γ) * z) =
      (χ.character (AdmissibleGamma.ratio γ' γ) : ℂ)⁻¹ *
        finiteGaussSummand χ ψ γ z := by
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
  rw [← unitFiltrationQuotientMk_mul]
  simp only [finiteGaussSummand_mk]
  exact finiteGaussSummandRepresentative_ratioUnit_mul χ ψ γ γ' u

/-- The finite Gauss sum has exactly the manuscript's
change-of-denominator factor. -/
theorem finiteGaussSum_admissibleGamma_change
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ γ' : AdmissibleGamma F χ ψ) :
    finiteGaussSum χ ψ γ' =
      (χ.character (AdmissibleGamma.ratio γ' γ) : ℂ)⁻¹ *
        finiteGaussSum χ ψ γ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  change (∑ z, finiteGaussSummand χ ψ γ' z) =
    (χ.character (AdmissibleGamma.ratio γ' γ) : ℂ)⁻¹ *
      ∑ z, finiteGaussSummand χ ψ γ z
  rw [← sum_unitFiltrationQuotient_mul_left F (Nat.zero_le χ.conductor)
    (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
      (AdmissibleGamma.ratioUnit γ' γ))
    (finiteGaussSummand χ ψ γ')]
  simp_rw [finiteGaussSummand_ratioUnit_mul χ ψ γ γ']
  simpa using
    (Finset.mul_sum Finset.univ (finiteGaussSummand χ ψ γ)
      (χ.character (AdmissibleGamma.ratio γ' γ) : ℂ)⁻¹).symm

/-! ## Finite Fourier proof of nonvanishing -/

private def finiteFourierRawSummand
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (x : lattice F 0)
    (u : unitFiltration F 0) : ℂ :=
  (ψ.character
      (((x : F) * ((u : Fˣ) : F)) / ((γ : Fˣ) : F)) : ℂ) *
    (χ.character (u : Fˣ) : ℂ)⁻¹

private theorem finiteFourierRawSummand_eq_of_unit_congruent
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (x : lattice F 0)
    (u v : unitFiltration F 0)
    (huv : CongruentAtDepth (χ.conductor : ℤ)
      ((u : Fˣ) : F) ((v : Fˣ) : F)) :
    finiteFourierRawSummand χ ψ γ x u =
      finiteFourierRawSummand χ ψ γ x v := by
  have huvUnit : (u : Fˣ) / (v : Fˣ) ∈ unitFiltration F χ.conductor :=
    (div_mem_unitFiltration_iff_congruentAtDepth F χ.conductor
      (u : Fˣ) (v : Fˣ)
      (unitFiltration_le_unitGroup F 0 u.property)
      (unitFiltration_le_unitGroup F 0 v.property)).2 huv
  have hχ : χ.character (u : Fˣ) = χ.character (v : Fˣ) := by
    apply div_eq_one.mp
    rw [← map_div]
    exact χ.isConductor.trivial _ huvUnit
  have huvLattice : ((u : Fˣ) : F) - ((v : Fˣ) : F) ∈
      lattice F (χ.conductor : ℤ) :=
    (congruentAtDepth_iff_sub_mem_lattice F (χ.conductor : ℤ)
      ((u : Fˣ) : F) ((v : Fˣ) : F)).1 huv
  have hmem :
      (x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F) -
          (x : F) * ((v : Fˣ) : F) / ((γ : Fˣ) : F) ∈
        lattice F (-ψ.conductor) := by
    rw [← sub_div, ← mul_sub]
    apply (div_mem_lattice_iff F ((γ : Fˣ) : F)
      ((x : F) * (((u : Fˣ) : F) - ((v : Fˣ) : F)))
      ((χ.conductor : ℤ) + ψ.conductor) (-ψ.conductor)
      γ.property).2
    simpa [add_neg_cancel_right] using
      mul_mem_lattice F x.property huvLattice
  have hψ : ψ.character
      ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) =
      ψ.character
        ((x : F) * ((v : Fˣ) : F) / ((γ : Fˣ) : F)) := by
    apply div_eq_one.mp
    change ψ.character.toAddChar
        ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) /
      ψ.character.toAddChar
        ((x : F) * ((v : Fˣ) : F) / ((γ : Fˣ) : F)) = 1
    rw [← AddChar.map_sub_eq_div]
    exact ψ.isConductor.trivial _ hmem
  simp only [finiteFourierRawSummand, hψ, hχ]

private theorem finiteFourierRawSummand_eq_of_lattice_congruent
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (x y : lattice F 0)
    (u : unitFiltration F 0)
    (hxy : CongruentAtDepth (χ.conductor : ℤ) (x : F) (y : F)) :
    finiteFourierRawSummand χ ψ γ x u =
      finiteFourierRawSummand χ ψ γ y u := by
  have hxyLattice : (x : F) - (y : F) ∈
      lattice F (χ.conductor : ℤ) :=
    (congruentAtDepth_iff_sub_mem_lattice F (χ.conductor : ℤ)
      (x : F) (y : F)).1 hxy
  have huLattice : ((u : Fˣ) : F) ∈ lattice F 0 := by
    rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
    simp
  have hmem :
      (x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F) -
          (y : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F) ∈
        lattice F (-ψ.conductor) := by
    rw [← sub_div, ← sub_mul]
    apply (div_mem_lattice_iff F ((γ : Fˣ) : F)
      (((x : F) - (y : F)) * ((u : Fˣ) : F))
      ((χ.conductor : ℤ) + ψ.conductor) (-ψ.conductor)
      γ.property).2
    simpa [add_neg_cancel_right] using
      mul_mem_lattice F hxyLattice huLattice
  have hψ : ψ.character
      ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) =
      ψ.character
        ((y : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) := by
    apply div_eq_one.mp
    change ψ.character.toAddChar
        ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) /
      ψ.character.toAddChar
        ((y : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) = 1
    rw [← AddChar.map_sub_eq_div]
    exact ψ.isConductor.trivial _ hmem
  simp only [finiteFourierRawSummand, hψ]

private def finiteFourierSummand
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    LatticeQuotient F 0 (χ.conductor : ℤ) (by omega) →
      UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _) → ℂ :=
  latticeQuotientLift F (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega)
    (fun x ↦ unitFiltrationQuotientLift F (Nat.zero_le χ.conductor)
      (finiteFourierRawSummand χ ψ γ x)
      (finiteFourierRawSummand_eq_of_unit_congruent χ ψ γ x))
    (by
      intro x y hxy
      funext z
      obtain ⟨u, rfl⟩ :=
        unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
      exact finiteFourierRawSummand_eq_of_lattice_congruent χ ψ γ x y u hxy)

@[simp]
private theorem finiteFourierSummand_mk_mk
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (x : lattice F 0)
    (u : unitFiltration F 0) :
    finiteFourierSummand χ ψ γ
        (latticeQuotientMk F (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) x)
        (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) =
      finiteFourierRawSummand χ ψ γ x u :=
  rfl

private def finiteFourierCoefficient
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ)
    (x : LatticeQuotient F 0 (χ.conductor : ℤ) (by omega)) : ℂ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  exact ∑ u, finiteFourierSummand χ ψ γ x u

private def latticeOne : lattice F 0 :=
  ⟨1, by simp⟩

@[simp]
private theorem coe_latticeOne : (latticeOne (F := F) : F) = 1 :=
  rfl

private theorem finiteFourierCoefficient_one
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    finiteFourierCoefficient χ ψ γ
        (latticeQuotientMk F
          (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) latticeOne) =
      finiteGaussSum χ ψ γ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  change (∑ u, finiteFourierSummand χ ψ γ
      (latticeQuotientMk F (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega)
        latticeOne) u) =
    ∑ u, finiteGaussSummand χ ψ γ u
  apply Finset.sum_congr rfl
  intro z _hz
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
  rw [finiteFourierSummand_mk_mk, finiteGaussSummand_mk]
  simp [finiteFourierRawSummand, finiteGaussSummandRepresentative]

private def latticeOfUnit (u : unitFiltration F 0) : lattice F 0 :=
  ⟨((u : Fˣ) : F), by
    rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
    simp⟩

@[simp]
private theorem coe_latticeOfUnit (u : unitFiltration F 0) :
    (latticeOfUnit u : F) = ((u : Fˣ) : F) :=
  rfl

private theorem finiteFourierRawSummand_latticeOfUnit
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (a u : unitFiltration F 0) :
    finiteFourierRawSummand χ ψ γ (latticeOfUnit a) u =
      (χ.character (a : Fˣ) : ℂ) *
        finiteGaussSummandRepresentative χ ψ γ (a * u) := by
  have hχmul :
      (χ.character ((a * u : unitFiltration F 0) : Fˣ) : ℂ) =
        (χ.character (a : Fˣ) : ℂ) * (χ.character (u : Fˣ) : ℂ) := by
    exact congrArg Units.val (map_mul χ.character (a : Fˣ) (u : Fˣ))
  have harg : (latticeOfUnit a : F) * ((u : Fˣ) : F) =
      (((a * u : unitFiltration F 0) : Fˣ) : F) := by
    rfl
  rw [finiteFourierRawSummand, finiteGaussSummandRepresentative, hχmul,
    harg, mul_inv_rev]
  have ha0 : (χ.character (a : Fˣ) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero χ.character (a : Fˣ)
  field_simp

private theorem finiteFourierCoefficient_mk_latticeOfUnit
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (a : unitFiltration F 0) :
    finiteFourierCoefficient χ ψ γ
        (latticeQuotientMk F
          (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) (latticeOfUnit a)) =
      (χ.character (a : Fˣ) : ℂ) * finiteGaussSum χ ψ γ := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  let aq := unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) a
  change (∑ z, finiteFourierSummand χ ψ γ
      (latticeQuotientMk F (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega)
        (latticeOfUnit a)) z) =
    (χ.character (a : Fˣ) : ℂ) * ∑ z, finiteGaussSummand χ ψ γ z
  calc
    _ = ∑ z, (χ.character (a : Fˣ) : ℂ) *
        finiteGaussSummand χ ψ γ (aq * z) := by
      apply Finset.sum_congr rfl
      intro z _hz
      obtain ⟨u, rfl⟩ :=
        unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
      rw [← unitFiltrationQuotientMk_mul, finiteFourierSummand_mk_mk,
        finiteGaussSummand_mk]
      exact finiteFourierRawSummand_latticeOfUnit χ ψ γ a u
    _ = (χ.character (a : Fˣ) : ℂ) *
        ∑ z, finiteGaussSummand χ ψ γ (aq * z) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_unitFiltrationQuotient_mul_left F (Nat.zero_le χ.conductor)
        aq (finiteGaussSummand χ ψ γ)]

private theorem finiteFourierRawSummand_mul_of_deep
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (hm : 0 < χ.conductor)
    (x : lattice F 0) (hx : (x : F) ∈ lattice F 1)
    (a : unitFiltration F 0)
    (ha : (a : Fˣ) ∈ unitFiltration F (χ.conductor - 1))
    (u : unitFiltration F 0) :
    finiteFourierRawSummand χ ψ γ x (a * u) =
      (χ.character (a : Fˣ) : ℂ)⁻¹ *
        finiteFourierRawSummand χ ψ γ x u := by
  have haCong : CongruentAtDepth ((χ.conductor - 1 : ℕ) : ℤ)
      ((a : Fˣ) : F) 1 :=
    (div_mem_unitFiltration_iff_congruentAtDepth F (χ.conductor - 1)
      (a : Fˣ) 1 (unitFiltration_le_unitGroup F 0 a.property)
      (unitFiltration F 0).one_mem).1 (by simpa using ha)
  have haSub : ((a : Fˣ) : F) - 1 ∈
      lattice F (χ.conductor - 1 : ℕ) :=
    (congruentAtDepth_iff_sub_mem_lattice F
      ((χ.conductor - 1 : ℕ) : ℤ) ((a : Fˣ) : F) 1).1 haCong
  have huLattice : ((u : Fˣ) : F) ∈ lattice F 0 := by
    rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
    simp
  have hprod :
      (x : F) * (((a : Fˣ) : F) - 1) * ((u : Fˣ) : F) ∈
        lattice F (χ.conductor : ℤ) := by
    have h₁ := mul_mem_lattice F hx haSub
    have h₂ := mul_mem_lattice F h₁ huLattice
    have hcast : ((χ.conductor - 1 : ℕ) : ℤ) =
        (χ.conductor : ℤ) - 1 := by omega
    simpa [hcast] using h₂
  have hmem :
      (x : F) * (((a * u : unitFiltration F 0) : Fˣ) : F) /
            ((γ : Fˣ) : F) -
          (x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F) ∈
        lattice F (-ψ.conductor) := by
    have hfield :
        (x : F) * (((a * u : unitFiltration F 0) : Fˣ) : F) -
            (x : F) * ((u : Fˣ) : F) =
          (x : F) * (((a : Fˣ) : F) - 1) * ((u : Fˣ) : F) := by
      change (x : F) * (((a : Fˣ) : F) * ((u : Fˣ) : F)) -
          (x : F) * ((u : Fˣ) : F) = _
      ring
    rw [← sub_div, hfield]
    apply (div_mem_lattice_iff F ((γ : Fˣ) : F)
      ((x : F) * (((a : Fˣ) : F) - 1) * ((u : Fˣ) : F))
      ((χ.conductor : ℤ) + ψ.conductor) (-ψ.conductor)
      γ.property).2
    simpa only [add_neg_cancel_right] using hprod
  have hψ : ψ.character
      ((x : F) * (((a * u : unitFiltration F 0) : Fˣ) : F) /
        ((γ : Fˣ) : F)) =
      ψ.character
        ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) := by
    apply div_eq_one.mp
    change ψ.character.toAddChar
        ((x : F) * (((a * u : unitFiltration F 0) : Fˣ) : F) /
          ((γ : Fˣ) : F)) /
      ψ.character.toAddChar
        ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) = 1
    rw [← AddChar.map_sub_eq_div]
    exact ψ.isConductor.trivial _ hmem
  have hχmul :
      (χ.character ((a * u : unitFiltration F 0) : Fˣ) : ℂ) =
        (χ.character (a : Fˣ) : ℂ) * (χ.character (u : Fˣ) : ℂ) := by
    exact congrArg Units.val (map_mul χ.character (a : Fˣ) (u : Fˣ))
  simp only [finiteFourierRawSummand]
  rw [hψ, hχmul, mul_inv_rev]
  ring

private theorem finiteFourierCoefficient_eq_zero_of_deep
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (hm : 0 < χ.conductor)
    (x : lattice F 0) (hx : (x : F) ∈ lattice F 1) :
    finiteFourierCoefficient χ ψ γ
        (latticeQuotientMk F
          (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) x) = 0 := by
  have hmShape : χ.conductor = (χ.conductor - 1) + 1 := by omega
  obtain ⟨a, ha, _haNext, hχa⟩ :=
    χ.exists_ne_one_on_predecessor hmShape
  let a₀ : unitFiltration F 0 :=
    ⟨a, unitFiltration_antitone F (Nat.zero_le _) ha⟩
  let aq := unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) a₀
  let c : ℂ := (χ.character a : ℂ)⁻¹
  have hc : c ≠ 1 := by
    apply (inv_ne_one.mpr ?_)
    intro h
    apply hχa
    apply Units.ext
    exact h
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  apply eq_zero_of_mul_eq_self_left hc
  change c * (∑ z, finiteFourierSummand χ ψ γ
      (latticeQuotientMk F (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) x) z) =
    ∑ z, finiteFourierSummand χ ψ γ
      (latticeQuotientMk F (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) x) z
  rw [Finset.mul_sum]
  calc
    _ = ∑ z, finiteFourierSummand χ ψ γ
        (latticeQuotientMk F
          (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) x) (aq * z) := by
      apply Finset.sum_congr rfl
      intro z _hz
      obtain ⟨u, rfl⟩ :=
        unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
      rw [← unitFiltrationQuotientMk_mul, finiteFourierSummand_mk_mk,
        finiteFourierSummand_mk_mk]
      exact (finiteFourierRawSummand_mul_of_deep χ ψ γ hm x hx a₀ ha u).symm
    _ = _ :=
      sum_unitFiltrationQuotient_mul_left F (Nat.zero_le χ.conductor) aq
        (finiteFourierSummand χ ψ γ
          (latticeQuotientMk F
            (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) x))

private theorem finiteFourierCoefficient_eq_zero_of_gaussSum_eq_zero
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (hm : 0 < χ.conductor)
    (hG : finiteGaussSum χ ψ γ = 0)
    (z : LatticeQuotient F 0 (χ.conductor : ℤ) (by omega)) :
    finiteFourierCoefficient χ ψ γ z = 0 := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ (χ.conductor : ℤ) by omega) z
  by_cases hxOrd : ord F (x : F) = 0
  · have hx0 : (x : F) ≠ 0 := by
      intro hx
      simp [hx] at hxOrd
    let xu : Fˣ := Units.mk0 (x : F) hx0
    let x₀ : unitFiltration F 0 :=
      ⟨xu, (mem_unitFiltration_zero F xu).2 hxOrd⟩
    have hxEq : latticeOfUnit x₀ = x := by
      apply Subtype.ext
      rfl
    rw [← hxEq, finiteFourierCoefficient_mk_latticeOfUnit, hG, mul_zero]
  · apply finiteFourierCoefficient_eq_zero_of_deep χ ψ γ hm x
    have hxmem := x.property
    rw [mem_lattice] at hxmem ⊢
    by_cases htop : ord F (x : F) = ⊤
    · simp [htop]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hr] at hxmem hxOrd ⊢
      have hr0 : r ≠ 0 := by
        intro hrzero
        apply hxOrd
        simp [hrzero]
      simp only [WithTop.coe_le_coe] at hxmem ⊢
      omega

/-! ## Finite additive duality and nonvanishing -/

private abbrev finiteAdditiveQuotient (χ : LocalQuasiCharData F) :=
  LatticeQuotient F 0 (χ.conductor : ℤ) (by omega)

private abbrev finitePairingTargetQuotient
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F) :=
  LatticeQuotient F
    (0 - ((χ.conductor : ℤ) + ψ.conductor))
    ((χ.conductor : ℤ) - ((χ.conductor : ℤ) + ψ.conductor))
    (sub_le_sub_right (show (0 : ℤ) ≤ χ.conductor by omega)
      ((χ.conductor : ℤ) + ψ.conductor))

/-- The additive character induced after division by an admissible denominator.
Its source remembers both shifted lattice depths, so its descent uses exactly
the additive conductor boundary. -/
private def finitePairingTargetChar
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F) :
    AddChar (finitePairingTargetQuotient χ ψ) ℂ where
  toFun := latticeQuotientLift F
    (sub_le_sub_right (show (0 : ℤ) ≤ χ.conductor by omega)
      ((χ.conductor : ℤ) + ψ.conductor))
    (fun x => (ψ.character (x : F) : ℂ))
    (by
      intro x y hxy
      have hmem : (x : F) - (y : F) ∈ lattice F (-ψ.conductor) := by
        change (x : F) - (y : F) ∈
          lattice F ((χ.conductor : ℤ) -
            ((χ.conductor : ℤ) + ψ.conductor)) at hxy
        simpa only [show (χ.conductor : ℤ) -
          ((χ.conductor : ℤ) + ψ.conductor) = -ψ.conductor by omega] using hxy
      have htriv : ψ.character ((x : F) - (y : F)) = 1 :=
        ψ.isConductor.trivial _ hmem
      have heq : ψ.character (x : F) = ψ.character (y : F) := by
        rw [show (x : F) = ((x : F) - (y : F)) + (y : F) by ring,
          ContinuousAddChar.map_add_eq_mul, htriv, one_mul]
      exact congrArg (Units.val : Units ℂ → ℂ) heq)
  map_zero_eq_one' := by
    change latticeQuotientLift F _ _ _ 0 = 1
    change latticeQuotientLift F _ _ _ (latticeQuotientMk F _ 0) = 1
    rw [latticeQuotientLift_mk]
    simp
  map_add_eq_mul' := by
    intro a b
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F
      (sub_le_sub_right (show (0 : ℤ) ≤ χ.conductor by omega)
        ((χ.conductor : ℤ) + ψ.conductor)) a
    obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F
      (sub_le_sub_right (show (0 : ℤ) ≤ χ.conductor by omega)
        ((χ.conductor : ℤ) + ψ.conductor)) b
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk]
    exact congrArg Units.val
      (ContinuousAddChar.map_add_eq_mul ψ.character (x : F) (y : F))

/-- The finite additive pairing `(x,y) ↦ ψ(xy/γ)`, bundled as an additive
character in its second variable. -/
private def finitePairingChar
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (a : finiteAdditiveQuotient χ) :
    AddChar (finiteAdditiveQuotient χ) ℂ :=
  (finitePairingTargetChar χ ψ).compAddMonoidHom <|
    (latticeQuotientDivAddHom F ((γ : Fˣ) : F)
      ((χ.conductor : ℤ) + ψ.conductor) γ.property
      (show (0 : ℤ) ≤ χ.conductor by omega)).comp <|
      latticeQuotientMulAddHom F
        (show (0 : ℤ) ≤ χ.conductor by omega)
        (show (0 : ℤ) ≤ χ.conductor by omega)
        (show (0 : ℤ) + 0 ≤ χ.conductor by omega)
        (show (χ.conductor : ℤ) ≤ (χ.conductor : ℤ) + 0 by omega)
        (show (χ.conductor : ℤ) ≤ 0 + (χ.conductor : ℤ) by omega) a

@[simp]
private theorem finitePairingChar_mk_mk
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (x y : lattice F 0) :
    finitePairingChar χ ψ γ
        (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) x)
        (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) y) =
      (ψ.character ((x : F) * (y : F) / ((γ : Fˣ) : F)) : ℂ) := by
  rfl

private theorem finitePairingChar_symm
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (a b : finiteAdditiveQuotient χ) :
    finitePairingChar χ ψ γ a b = finitePairingChar χ ψ γ b a := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ χ.conductor by omega) a
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ χ.conductor by omega) b
  rw [finitePairingChar_mk_mk, finitePairingChar_mk_mk, mul_comm]

@[simp]
private theorem finitePairingChar_zero_left
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (a : finiteAdditiveQuotient χ) :
    finitePairingChar χ ψ γ 0 a = 1 := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ χ.conductor by omega) a
  change finitePairingChar χ ψ γ
      (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) 0)
      (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) x) = 1
  rw [finitePairingChar_mk_mk]
  simp

/-- The additive pairing is perfect: every nonzero first argument induces a
nontrivial additive character. -/
private theorem finitePairingChar_ne_one_of_ne_zero
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (a : finiteAdditiveQuotient χ)
    (ha : a ≠ 0) : finitePairingChar χ ψ γ a ≠ 1 := by
  intro hpair
  obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ χ.conductor by omega) a
  have hcnot : (c : F) ∉ lattice F (χ.conductor : ℤ) := by
    intro hc
    apply ha
    exact (latticeQuotientMk_eq_zero_iff F
      (show (0 : ℤ) ≤ χ.conductor by omega)).2 hc
  have hc0 : (c : F) ≠ 0 := by
    intro hc
    apply hcnot
    simp [hc]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff F).2 hc0)
  have hk0 : 0 ≤ k := by
    have := c.property
    rw [mem_lattice, ← hk] at this
    exact_mod_cast this
  have hkm : k < (χ.conductor : ℤ) := by
    have hnotle : ¬ (((χ.conductor : ℤ) : WithTop ℤ) ≤ ord F (c : F)) := by
      simpa only [mem_lattice] using hcnot
    have hlt := lt_of_not_ge hnotle
    rw [← hk] at hlt
    exact_mod_cast hlt
  obtain ⟨z, hzord, hzψ⟩ := ψ.exists_ord_eq_predecessor
  let bval : F := z * ((γ : Fˣ) : F) / (c : F)
  have hbOrd : ord F bval =
      (((χ.conductor : ℤ) - 1 - k : ℤ) : WithTop ℤ) := by
    dsimp only [bval]
    rw [ord_div, ord_mul, hzord, γ.property, ← hk]
    norm_num
    calc
      -((ψ.conductor : WithTop ℤ)) - 1 +
          (((χ.conductor : ℤ) : WithTop ℤ) + ψ.conductor) =
          (((-ψ.conductor - 1) + ((χ.conductor : ℤ) + ψ.conductor) : ℤ) :
            WithTop ℤ) := by norm_num
      _ = (((χ.conductor : ℤ) - 1 : ℤ) : WithTop ℤ) := by
        congr 1
        omega
      _ = ((χ.conductor : ℤ) : WithTop ℤ) - 1 := by norm_num
  have hbmem : bval ∈ lattice F 0 := by
    rw [mem_lattice, hbOrd]
    exact_mod_cast (show (0 : ℤ) ≤ (χ.conductor : ℤ) - 1 - k by omega)
  let b : lattice F 0 := ⟨bval, hbmem⟩
  have heval : finitePairingChar χ ψ γ
      (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) c)
      (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) b) = 1 := by
    rw [hpair]
    rfl
  rw [finitePairingChar_mk_mk] at heval
  have hcalc : (c : F) * (b : F) / ((γ : Fˣ) : F) = z := by
    dsimp [b, bval]
    field_simp
  rw [hcalc] at heval
  exact hzψ (Units.val_injective heval)

/-- A unit class maps canonically to its underlying additive class modulo the
same conductor depth. -/
private def finiteUnitClassToAdditiveClass (χ : LocalQuasiCharData F) :
    UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _) →
      finiteAdditiveQuotient χ :=
  unitFiltrationQuotientLift F (Nat.zero_le _)
    (fun u => latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega)
      (latticeOfUnit u))
    (by
      intro u v huv
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        (show (0 : ℤ) ≤ χ.conductor by omega)).2
      exact huv)

@[simp]
private theorem finiteUnitClassToAdditiveClass_mk
    (χ : LocalQuasiCharData F) (u : unitFiltration F 0) :
    finiteUnitClassToAdditiveClass χ
        (unitFiltrationQuotientMk F (Nat.zero_le _) u) =
      latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega)
        (latticeOfUnit u) := by
  rw [finiteUnitClassToAdditiveClass, unitFiltrationQuotientLift_mk]

private def finiteLatticeOneClass (χ : LocalQuasiCharData F) :
    finiteAdditiveQuotient χ :=
  latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) latticeOne

@[simp]
private theorem finiteUnitClassToAdditiveClass_one
    (χ : LocalQuasiCharData F) :
    finiteUnitClassToAdditiveClass χ
        (1 : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _)) =
      finiteLatticeOneClass χ := by
  change finiteUnitClassToAdditiveClass χ
      (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
        (1 : unitFiltration F 0)) = _
  rfl

private theorem finiteUnitClassToAdditiveClass_injective
    (χ : LocalQuasiCharData F) :
    Function.Injective (finiteUnitClassToAdditiveClass χ) := by
  intro u v huv
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le χ.conductor) u
  obtain ⟨v, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le χ.conductor) v
  rw [finiteUnitClassToAdditiveClass_mk,
    finiteUnitClassToAdditiveClass_mk] at huv
  apply (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
    (Nat.zero_le χ.conductor) u v).2
  exact (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
    (show (0 : ℤ) ≤ χ.conductor by omega)).1 huv

private theorem finiteFourierSummand_mul_pairing
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) (u : unitFiltration F 0)
    (a : finiteAdditiveQuotient χ) :
    finiteFourierSummand χ ψ γ a
          (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) *
        finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ)) =
      (χ.character (u : Fˣ) : ℂ)⁻¹ *
        finitePairingChar χ ψ γ
          (finiteUnitClassToAdditiveClass χ
            (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) -
              finiteLatticeOneClass χ) a := by
  obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective F
    (show (0 : ℤ) ≤ χ.conductor by omega) a
  rw [finiteFourierSummand_mk_mk, finiteUnitClassToAdditiveClass_mk]
  change finiteFourierRawSummand χ ψ γ x u *
      finitePairingChar χ ψ γ
        (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) x)
        (-latticeQuotientMk F
          (show (0 : ℤ) ≤ χ.conductor by omega) latticeOne) =
    (χ.character (u : Fˣ) : ℂ)⁻¹ *
      finitePairingChar χ ψ γ
        (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega)
            (latticeOfUnit u) -
          latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega)
            latticeOne)
        (latticeQuotientMk F (show (0 : ℤ) ≤ χ.conductor by omega) x)
  rw [← latticeQuotientMk_neg, ← latticeQuotientMk_sub,
    finitePairingChar_mk_mk, finitePairingChar_mk_mk]
  simp only [finiteFourierRawSummand, coe_latticeOne, coe_latticeOfUnit,
    Submodule.coe_neg, Submodule.coe_sub]
  have hmap := ContinuousAddChar.map_add_eq_mul ψ.character
    ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F))
    ((x : F) * (-1) / ((γ : Fˣ) : F))
  have harg :
      (x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F) +
          (x : F) * (-1) / ((γ : Fˣ) : F) =
        ((((u : Fˣ) : F) - 1) * (x : F)) / ((γ : Fˣ) : F) := by
    ring
  rw [harg] at hmap
  have hmapCoe := congrArg (Units.val : Units ℂ → ℂ) hmap
  simp only [Units.val_mul] at hmapCoe
  calc
    (ψ.character ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) : ℂ) *
          (χ.character (u : Fˣ) : ℂ)⁻¹ *
        (ψ.character ((x : F) * -1 / ((γ : Fˣ) : F)) : ℂ) =
      (χ.character (u : Fˣ) : ℂ)⁻¹ *
        ((ψ.character ((x : F) * ((u : Fˣ) : F) / ((γ : Fˣ) : F)) : ℂ) *
          (ψ.character ((x : F) * -1 / ((γ : Fˣ) : F)) : ℂ)) := by ring
    _ = _ := by rw [← hmapCoe]

/-- Finite Fourier orthogonality for the local pairing.  This is the
nonvanishing input: the transform of the unit-supported character has a
Fourier coefficient whose inverse transform is the nonzero cardinality of
`𝒪_F/𝔭_F^m`. -/
private theorem finiteFourierCoefficient_orthogonality
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    letI := latticeQuotientFintype F
      (show (0 : ℤ) ≤ χ.conductor by omega)
    ∑ a : finiteAdditiveQuotient χ,
        finiteFourierCoefficient χ ψ γ a *
          finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ)) =
      (Fintype.card (finiteAdditiveQuotient χ) : ℂ) := by
  classical
  letI := latticeQuotientFintype F
    (show (0 : ℤ) ≤ χ.conductor by omega)
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  have hinner
      (z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _)) :
      (∑ a : finiteAdditiveQuotient χ,
        finiteFourierSummand χ ψ γ a z *
          finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ))) =
        if z = 1 then (Fintype.card (finiteAdditiveQuotient χ) : ℂ) else 0 := by
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
      (Nat.zero_le χ.conductor) z
    let uq := unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u
    by_cases hu : uq = 1
    · rw [if_pos hu]
      have huDeep : (u : Fˣ) ∈ unitFiltration F χ.conductor :=
        (unitFiltrationQuotientMk_eq_one_iff F
          (Nat.zero_le χ.conductor) u).1 hu
      have hχu : χ.character (u : Fˣ) = 1 :=
        χ.isConductor.trivial _ huDeep
      have hclass : finiteUnitClassToAdditiveClass χ uq =
          finiteLatticeOneClass χ := by
        rw [hu, finiteUnitClassToAdditiveClass_one]
      calc
        (∑ a : finiteAdditiveQuotient χ,
            finiteFourierSummand χ ψ γ a uq *
              finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ))) =
            ∑ _a : finiteAdditiveQuotient χ, (1 : ℂ) := by
              apply Finset.sum_congr rfl
              intro a _ha
              rw [finiteFourierSummand_mul_pairing, hclass, sub_self,
                finitePairingChar_zero_left]
              simp [hχu]
        _ = _ := by simp
    · rw [if_neg hu]
      have hdiff : finiteUnitClassToAdditiveClass χ uq -
          finiteLatticeOneClass χ ≠ 0 := by
        intro hzero
        have heq : finiteUnitClassToAdditiveClass χ uq =
            finiteLatticeOneClass χ := sub_eq_zero.mp hzero
        apply hu
        apply finiteUnitClassToAdditiveClass_injective χ
        simpa only [finiteUnitClassToAdditiveClass_one] using heq
      have hchar : finitePairingChar χ ψ γ
          (finiteUnitClassToAdditiveClass χ uq - finiteLatticeOneClass χ) ≠ 1 :=
        finitePairingChar_ne_one_of_ne_zero χ ψ γ _ hdiff
      calc
        (∑ a : finiteAdditiveQuotient χ,
            finiteFourierSummand χ ψ γ a uq *
              finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ))) =
            ∑ a : finiteAdditiveQuotient χ,
              (χ.character (u : Fˣ) : ℂ)⁻¹ *
                finitePairingChar χ ψ γ
                  (finiteUnitClassToAdditiveClass χ uq -
                    finiteLatticeOneClass χ) a := by
              apply Finset.sum_congr rfl
              intro a _ha
              exact finiteFourierSummand_mul_pairing χ ψ γ u a
        _ = (χ.character (u : Fˣ) : ℂ)⁻¹ *
            ∑ a : finiteAdditiveQuotient χ,
              finitePairingChar χ ψ γ
                (finiteUnitClassToAdditiveClass χ uq -
                  finiteLatticeOneClass χ) a := by
              rw [Finset.mul_sum]
        _ = 0 := by rw [AddChar.sum_eq_zero_of_ne_one hchar, mul_zero]
  change (∑ a : finiteAdditiveQuotient χ,
      (∑ z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
        finiteFourierSummand χ ψ γ a z) *
          finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ))) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
        ∑ a : finiteAdditiveQuotient χ,
          finiteFourierSummand χ ψ γ a z *
            finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ))) =
      ∑ z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
        if z = 1 then (Fintype.card (finiteAdditiveQuotient χ) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [hinner]
    _ = _ := by simp

/-- The representative-independent finite Gauss sum is nonzero.  For positive
conductor this follows from perfect finite Fourier duality; at conductor zero
the unit quotient is a singleton and its unique summand is nonzero. -/
theorem finiteGaussSum_ne_zero
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) : finiteGaussSum χ ψ γ ≠ 0 := by
  by_cases hm : χ.conductor = 0
  · letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
    have hsub : ∀ u : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
        u = 1 := by
      intro u
      obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
        (Nat.zero_le χ.conductor) u
      apply (unitFiltrationQuotientMk_eq_one_iff F
        (Nat.zero_le χ.conductor) u).2
      simpa only [hm] using u.property
    have hsum : finiteGaussSum χ ψ γ = finiteGaussSummand χ ψ γ 1 := by
      change (∑ u : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
        finiteGaussSummand χ ψ γ u) = _
      calc
        _ = ∑ _u : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
            finiteGaussSummand χ ψ γ 1 := by
          apply Finset.sum_congr rfl
          intro u _hu
          rw [hsub u]
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ]
          have hcard : Fintype.card
              (UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _)) = 1 := by
            apply Fintype.card_eq_one_iff.mpr
            exact ⟨1, hsub⟩
          rw [hcard]
          simp
    rw [hsum]
    change finiteGaussSummand χ ψ γ
      (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
        (1 : unitFiltration F 0)) ≠ 0
    rw [finiteGaussSummand_mk, finiteGaussSummandRepresentative]
    exact mul_ne_zero (ContinuousAddChar.apply_ne_zero _ _)
      (inv_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _))
  · have hmpos : 0 < χ.conductor := Nat.pos_of_ne_zero hm
    intro hzero
    letI := latticeQuotientFintype F
      (show (0 : ℤ) ≤ χ.conductor by omega)
    have hFourier := finiteFourierCoefficient_orthogonality χ ψ γ
    have hleft :
        (∑ a : finiteAdditiveQuotient χ,
          finiteFourierCoefficient χ ψ γ a *
            finitePairingChar χ ψ γ a (-(finiteLatticeOneClass χ))) = 0 := by
      apply Finset.sum_eq_zero
      intro a _ha
      rw [finiteFourierCoefficient_eq_zero_of_gaussSum_eq_zero
        χ ψ γ hmpos hzero a, zero_mul]
    rw [hleft] at hFourier
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hFourier.symm

/-! ## The computational local constant -/

/-- The finite computational version of Langlands's local constant, with
the manuscript's exact normalization and an explicit admissible denominator. -/
def deltaFinite
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) : ℂ :=
  (χ.character (γ : Fˣ) : ℂ) * phase (finiteGaussSum χ ψ γ)

/-- The computational local constant is independent of its admissible
denominator.  Nonvanishing of the finite Gauss sum is used here to exclude
the total phase's zero branch. -/
theorem deltaFinite_gamma_independent
    (χ : LocalQuasiCharData F) (ψ : LocalAddCharData F)
    (γ γ' : AdmissibleGamma F χ ψ) :
    deltaFinite χ ψ γ' = deltaFinite χ ψ γ := by
  let a := AdmissibleGamma.ratioUnit γ' γ
  have hγ' : (γ' : Fˣ) = (a : Fˣ) * (γ : Fˣ) := by
    exact (AdmissibleGamma.ratio_mul γ' γ).symm
  have hχγ' : (χ.character (γ' : Fˣ) : ℂ) =
      (χ.character (a : Fˣ) : ℂ) *
        (χ.character (γ : Fˣ) : ℂ) := by
    have hunit : χ.character (γ' : Fˣ) =
        χ.character (a : Fˣ) * χ.character (γ : Fˣ) := by
      rw [hγ', map_mul]
    exact congrArg Units.val hunit
  have haNorm : ‖(χ.character (a : Fˣ) : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv,
      quasiChar_norm_eq_one_of_mem_unitFiltration_zero χ a,
      inv_one]
  have hG : finiteGaussSum χ ψ γ ≠ 0 := finiteGaussSum_ne_zero χ ψ γ
  rw [deltaFinite, deltaFinite, hχγ',
    finiteGaussSum_admissibleGamma_change χ ψ γ γ']
  change ((χ.character (a : Fˣ) : ℂ) *
      (χ.character (γ : Fˣ) : ℂ)) *
        phase ((χ.character (a : Fˣ) : ℂ)⁻¹ * finiteGaussSum χ ψ γ) = _
  rw [phase_mul_of_norm_eq_one haNorm hG]
  have ha0 : (χ.character (a : Fˣ) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero χ.character (a : Fˣ)
  field_simp

end


end LanglandsFirstMainLemma
