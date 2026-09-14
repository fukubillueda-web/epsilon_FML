import LanglandsFirstMainLemma.Delta.FiniteDefinition
import LanglandsFirstMainLemma.Delta.Elementary
import LanglandsFirstMainLemma.FiniteField.CharacterAPI
import LanglandsFirstMainLemma.LocalField.ResidueField

/-!
# Residue-field formulas for conductors zero and one

The residual additive character is defined from the canonical Teichmüller
section.  Its evaluation theorem then proves independence from every integral
lift.  The residual multiplicative character is defined in the same canonical
way and is identified with the restriction of a conductor-one local
quasi-character on arbitrary local-unit lifts.

With these representative-free characters, the finite local Gauss sum at
conductor one is literally the negative of Langlands's finite-field Gauss sum.
This keeps the manuscript's sign, inverse-character convention, denominator
scaling, and total phase normalization explicit.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Pointwise

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance residueFintype : Fintype (ResidueField F) :=
  residueFieldFintype F

local instance residueUnitsFintype : Fintype (ResidueField F)ˣ :=
  Fintype.ofFinite (ResidueField F)ˣ

/-! ## The residual additive character -/

/-- The residual additive character attached to exact additive-conductor data
`ψ` and a denominator `γ` of order `n(ψ) + 1`.  The Teichmüller section makes
the definition canonical; `residualAddChar_integral_lift` proves the
manuscript's arbitrary-lift formula. -/
def residualAddChar (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    AddChar (ResidueField F) ℂ where
  toFun x :=
    (ψ.character (((teichmuller F x : ringOfIntegers F) : F) / (γ : F)) : ℂ)
  map_zero_eq_one' := by
    simp
  map_add_eq_mul' := by
    intro x y
    let tx : ringOfIntegers F := teichmuller F x
    let ty : ringOfIntegers F := teichmuller F y
    let txy : ringOfIntegers F := teichmuller F (x + y)
    have hdiff : ((txy : F) - ((tx : F) + (ty : F))) ∈ lattice F 1 := by
      have hres : residueMap F txy = residueMap F (tx + ty) := by
        simp [tx, ty, txy]
      exact (residueMap_eq_residueMap_iff F txy (tx + ty)).1 hres
    have hquot :
        ((txy : F) - ((tx : F) + (ty : F))) / (γ : F) ∈
          lattice F (-ψ.conductor) := by
      apply (div_mem_lattice_iff F (γ : F)
        ((txy : F) - ((tx : F) + (ty : F)))
        (ψ.conductor + 1) (-ψ.conductor) hγ).2
      simpa only [show ψ.conductor + 1 + -ψ.conductor = 1 by omega] using hdiff
    have htriv := ψ.isConductor.trivial _ hquot
    have hψ :
        ψ.character ((txy : F) / (γ : F)) =
          ψ.character (((tx : F) + (ty : F)) / (γ : F)) := by
      have hadd := ContinuousAddChar.map_add_eq_mul ψ.character
        (((txy : F) - ((tx : F) + (ty : F))) / (γ : F))
        (((tx : F) + (ty : F)) / (γ : F))
      have hsum :
          ((txy : F) - ((tx : F) + (ty : F))) / (γ : F) +
              ((tx : F) + (ty : F)) / (γ : F) =
            (txy : F) / (γ : F) := by ring
      rw [hsum, htriv, one_mul] at hadd
      exact hadd
    change (ψ.character ((txy : F) / (γ : F)) : ℂ) =
      (ψ.character ((tx : F) / (γ : F)) : ℂ) *
        (ψ.character ((ty : F) / (γ : F)) : ℂ)
    have hu : ψ.character ((txy : F) / (γ : F)) =
        ψ.character ((tx : F) / (γ : F)) *
          ψ.character ((ty : F) / (γ : F)) := by
      rw [hψ]
      have hdiv : ((tx : F) + (ty : F)) / (γ : F) =
          (tx : F) / (γ : F) + (ty : F) / (γ : F) := by ring
      rw [hdiv]
      exact ContinuousAddChar.map_add_eq_mul ψ.character
        ((tx : F) / (γ : F)) ((ty : F) / (γ : F))
    exact congrArg Units.val hu

/-- Evaluation of the residual additive character on the reduction of any
integral lift.  This is the explicit lift-independence statement
`ψbar(x mod 𝔭) = ψ(x / γ)`. -/
theorem residualAddChar_integral_lift (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ))
    (x : F) (hx : x ∈ lattice F 0) :
    residualAddChar F ψ γ hγ (reduce F x hx) =
      (ψ.character (x / (γ : F)) : ℂ) := by
  let tx : ringOfIntegers F := teichmuller F (reduce F x hx)
  let xint : ringOfIntegers F :=
    ⟨x, (mem_lattice_zero_iff F).1 hx⟩
  have hdiff : ((tx : F) - x) ∈ lattice F 1 := by
    have hres : residueMap F tx = residueMap F xint := by
      simp [tx, xint, reduce]
    exact (residueMap_eq_residueMap_iff F tx xint).1 hres
  have hquot : ((tx : F) - x) / (γ : F) ∈ lattice F (-ψ.conductor) := by
    apply (div_mem_lattice_iff F (γ : F) ((tx : F) - x)
      (ψ.conductor + 1) (-ψ.conductor) hγ).2
    simpa only [show ψ.conductor + 1 + -ψ.conductor = 1 by omega] using hdiff
  have htriv := ψ.isConductor.trivial _ hquot
  change (ψ.character ((tx : F) / (γ : F)) : ℂ) = _
  have hadd := ContinuousAddChar.map_add_eq_mul ψ.character
    (((tx : F) - x) / (γ : F)) (x / (γ : F))
  have hsum : ((tx : F) - x) / (γ : F) + x / (γ : F) =
      (tx : F) / (γ : F) := by ring
  rw [hsum, htriv, one_mul] at hadd
  exact congrArg Units.val hadd

/-- The arbitrary-integral-lift formula specialized to local units. -/
@[simp]
theorem residualAddChar_residueUnits (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ))
    (u : unitGroup F) :
    residualAddChar F ψ γ hγ
        ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) =
      (ψ.character (((u : Fˣ) : F) / (γ : F)) : ℂ) := by
  have huord : ord F ((u : Fˣ) : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F (u : Fˣ)).1 u.property
  have hu : ((u : Fˣ) : F) ∈ lattice F 0 := by
    rw [mem_lattice, huord]
    exact le_rfl
  have hreduce :
      reduce F ((u : Fˣ) : F) hu =
        ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) := by
    change residueMap F
        (⟨((u : Fˣ) : F), (mem_lattice_zero_iff F).1 hu⟩ : ringOfIntegers F) = _
    rw [residueUnits_coe]
    congr 1
  rw [← hreduce]
  exact residualAddChar_integral_lift F ψ γ hγ ((u : Fˣ) : F) hu

/-- The residual additive character has no hidden zero/trivial branch: exact
additive conductor makes it nontrivial. -/
theorem residualAddChar_ne_one (ψ : LocalAddCharData F) (γ : Fˣ)
    (hγ : ord F (γ : F) = ((ψ.conductor + 1 : ℤ) : WithTop ℤ)) :
    residualAddChar F ψ γ hγ ≠ 1 := by
  obtain ⟨x, hxord, hψx⟩ := ψ.isConductor.exists_ord_eq_predecessor
  let z : F := x * (γ : F)
  have hzord : ord F z = 0 := by
    dsimp [z]
    rw [ord_mul, hxord, hγ]
    norm_cast
    omega
  have hz : z ∈ lattice F 0 := by
    rw [mem_lattice, hzord]
    exact le_rfl
  intro htriv
  have happ : residualAddChar F ψ γ hγ (reduce F z hz) = 1 := by
    rw [htriv]
    simp
  have hlift := residualAddChar_integral_lift F ψ γ hγ z hz
  have hzdiv : z / (γ : F) = x := by
    dsimp [z]
    field_simp [Units.ne_zero γ]
  rw [hlift, hzdiv] at happ
  apply hψx
  apply Units.ext
  simpa using happ

/-! ## The residual multiplicative character -/

/-- The canonical Teichmüller lift of a nonzero residue class, regarded as a
local unit. -/
def teichmullerLocalUnits : (ResidueField F)ˣ →* unitGroup F :=
  (unitGroupMulEquivRingOfIntegers F).symm.toMonoidHom.comp
    (teichmullerUnits F)

@[simp]
theorem residueUnits_teichmullerLocalUnits (x : (ResidueField F)ˣ) :
    residueUnits F (teichmullerLocalUnits F x) = x := by
  apply Units.ext
  rw [residueUnits_coe]
  simp [teichmullerLocalUnits]

/-- The residue-field multiplicative character obtained by evaluating a local
quasi-character on canonical Teichmüller unit lifts and extending by zero. -/
def residualMulChar (χ : LocalQuasiCharData F) :
    FiniteMulChar (ResidueField F) :=
  MulChar.ofUnitHom
    ((χ.character.toMonoidHom.comp (unitGroup F).subtype).comp
      (teichmullerLocalUnits F))

@[simp]
theorem residualMulChar_apply_unit (χ : LocalQuasiCharData F)
    (x : (ResidueField F)ˣ) :
    residualMulChar F χ (x : ResidueField F) =
      (χ.character (teichmullerLocalUnits F x) : ℂ) := by
  rw [residualMulChar, MulChar.ofUnitHom_coe]
  rfl

/-- If `χ` is trivial on `U¹` (in particular, if its exact conductor is
zero or one), its residual character evaluates on every local-unit lift as
the original local character. -/
@[simp]
theorem residualMulChar_residueUnits (χ : LocalQuasiCharData F)
    (hχ : χ.conductor ≤ 1) (u : unitGroup F) :
    residualMulChar F χ
        ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) =
      (χ.character (u : Fˣ) : ℂ) := by
  let tu : unitGroup F := teichmullerLocalUnits F (residueUnits F u)
  have hker : tu / u ∈ (residueUnits F).ker := by
    rw [MonoidHom.mem_ker, map_div]
    simp [tu]
  have hU1 : ((tu / u : unitGroup F) : Fˣ) ∈ unitFiltration F 1 := by
    rw [residueUnits_ker F] at hker
    exact (mem_unitFiltrationInside F (show 0 ≤ 1 by omega) _).1 hker
  have hχtriv : χ.character (((tu / u : unitGroup F) : Fˣ)) = 1 :=
    χ.isConductor.trivial _
      (unitFiltration_antitone F hχ hU1)
  have hcoediv : (((tu / u : unitGroup F) : Fˣ)) =
      (tu : Fˣ) / (u : Fˣ) := rfl
  rw [hcoediv] at hχtriv
  have hmap := map_div χ.character (tu : Fˣ) (u : Fˣ)
  rw [hχtriv] at hmap
  have heq : χ.character (tu : Fˣ) = χ.character (u : Fˣ) :=
    div_eq_one.mp hmap.symm
  rw [residualMulChar_apply_unit]
  exact congrArg Units.val heq

/-- Exact conductor one is reflected by a nontrivial residue-field
multiplicative character. -/
theorem residualMulChar_ne_one (χ : LocalQuasiCharData F)
    (hχ : χ.conductor = 1) : residualMulChar F χ ≠ 1 := by
  intro hbar
  have htriv : QuasiCharTrivialOnUnitFiltration F χ.character 0 := by
    intro u hu
    let u0 : unitGroup F := ⟨u, by simpa using hu⟩
    have hlift := residualMulChar_residueUnits F χ (by omega) u0
    have happ : residualMulChar F χ
        ((residueUnits F u0 : (ResidueField F)ˣ) : ResidueField F) = 1 := by
      rw [hbar]
      exact MulChar.one_apply (residueUnits F u0).isUnit
    rw [hlift] at happ
    apply Units.ext
    simpa [u0] using happ
  have := χ.isConductor.minimal 0 htriv
  omega

/-! ## Exact conductor-zero formula -/

/-- At exact multiplicative conductor zero, the unit quotient is a singleton
and its sole finite Gauss summand is one. -/
theorem finiteGaussSum_conductor_zero (χ : LocalQuasiCharData F)
    (hχ : χ.conductor = 0) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) : finiteGaussSum χ ψ γ = 1 := by
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  have hsub : ∀ z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
      z = 1 := by
    intro z
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
      (Nat.zero_le χ.conductor) z
    apply (unitFiltrationQuotientMk_eq_one_iff F
      (Nat.zero_le χ.conductor) u).2
    simpa only [hχ] using u.property
  have hsingle : finiteGaussSum χ ψ γ = finiteGaussSummand χ ψ γ 1 := by
    change (∑ z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
      finiteGaussSummand χ ψ γ z) = _
    calc
      _ = ∑ _z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
          finiteGaussSummand χ ψ γ 1 := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [hsub z]
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ]
        have hcard : Fintype.card
            (UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _)) = 1 := by
          apply Fintype.card_eq_one_iff.mpr
          exact ⟨1, hsub⟩
        rw [hcard]
        simp
  rw [hsingle]
  change finiteGaussSummand χ ψ γ
    (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor)
      (1 : unitFiltration F 0)) = 1
  rw [finiteGaussSummand_mk, finiteGaussSummandRepresentative]
  have hγ : ord F ((γ : Fˣ) : F) = (ψ.conductor : WithTop ℤ) := by
    simpa only [hχ, Nat.cast_zero, zero_add] using γ.property
  have harg : (1 : F) / ((γ : Fˣ) : F) ∈ lattice F (-ψ.conductor) := by
    apply (div_mem_lattice_iff F ((γ : Fˣ) : F) 1
      ψ.conductor (-ψ.conductor) hγ).2
    simp
  have hψ := ψ.isConductor.trivial _ harg
  change (ψ.character ((1 : F) / ((γ : Fˣ) : F)) : ℂ) *
    (χ.character (1 : Fˣ) : ℂ)⁻¹ = 1
  rw [hψ]
  simp

/-- The exact conductor-zero local constant.  For any admissible denominator
`γ`, no residual sign or phase remains: `Δ(χ,ψ;γ)=χ(γ)`. -/
theorem deltaFinite_conductor_zero (χ : LocalQuasiCharData F)
    (hχ : χ.conductor = 0) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    deltaFinite χ ψ γ = (χ.character (γ : Fˣ) : ℂ) := by
  rw [deltaFinite, finiteGaussSum_conductor_zero F χ hχ ψ γ]
  simp [phase]

/-! ## Exact conductor-one formula -/

/-- An admissible denominator for exact multiplicative conductor one has the
residual-character order `n(ψ) + 1`. -/
private theorem admissibleGamma_order_conductor_one
    (χ : LocalQuasiCharData F) (hχ : χ.conductor = 1)
    (ψ : LocalAddCharData F) (γ : AdmissibleGamma F χ ψ) :
    ord F ((γ : Fˣ) : F) =
      ((ψ.conductor + 1 : ℤ) : WithTop ℤ) := by
  calc
    ord F ((γ : Fˣ) : F) =
        ((((χ.conductor : ℕ) : ℤ) + ψ.conductor : ℤ) : WithTop ℤ) :=
      γ.property
    _ = ((ψ.conductor + 1 : ℤ) : WithTop ℤ) := by
      norm_cast
      omega

/-- Reduction identifies the conductor-one local-unit quotient with the
multiplicative group of the residue field. -/
private def conductorOneUnitQuotientEquivResidueUnits
    (χ : LocalQuasiCharData F) (hχ : χ.conductor = 1) :
    UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _) ≃*
      (ResidueField F)ˣ := by
  have hden : unitFiltrationInside F (Nat.zero_le χ.conductor) =
      (residueUnits F).ker := by
    rw [residueUnits_ker F]
    ext u
    rw [mem_unitFiltrationInside, mem_unitFiltrationInside]
    simp only [hχ]
  exact QuotientGroup.liftEquiv
    (unitFiltrationInside F (Nat.zero_le χ.conductor))
    (residueUnits_surjective F) hden

@[simp]
private theorem conductorOneUnitQuotientEquivResidueUnits_mk
    (χ : LocalQuasiCharData F) (hχ : χ.conductor = 1)
    (u : unitFiltration F 0) :
    conductorOneUnitQuotientEquivResidueUnits F χ hχ
        (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) =
      residueUnits F u := rfl

/-- At exact multiplicative conductor one, the representative-free local
finite sum is the negative of Langlands's normalized residue-field Gauss
sum.  Thus both inversions and the unique minus sign are explicit. -/
theorem finiteGaussSum_conductor_one (χ : LocalQuasiCharData F)
    (hχ : χ.conductor = 1) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    let hγ : ord F ((γ : Fˣ) : F) =
        ((ψ.conductor + 1 : ℤ) : WithTop ℤ) :=
      admissibleGamma_order_conductor_one F χ hχ ψ γ
    finiteGaussSum χ ψ γ =
      -langlandsGaussSum (residualMulChar F χ)
        (residualAddChar F ψ (γ : Fˣ) hγ) := by
  let hγ : ord F ((γ : Fˣ) : F) =
      ((ψ.conductor + 1 : ℤ) : WithTop ℤ) :=
    admissibleGamma_order_conductor_one F χ hχ ψ γ
  dsimp only
  letI := unitFiltrationQuotientFintype F (Nat.zero_le χ.conductor)
  letI := residueFieldFintype F
  let e := conductorOneUnitQuotientEquivResidueUnits F χ hχ
  rw [langlandsGaussSum_eq_neg_sum_units, neg_neg]
  change (∑ z : UnitFiltrationQuotient F 0 χ.conductor (Nat.zero_le _),
      finiteGaussSummand χ ψ γ z) =
    ∑ x : (ResidueField F)ˣ,
      (residualMulChar F χ)⁻¹ x *
        residualAddChar F ψ (γ : Fˣ) hγ (x : ResidueField F)
  rw [← e.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro z _hz
  obtain ⟨u, rfl⟩ :=
    unitFiltrationQuotientMk_surjective F (Nat.zero_le χ.conductor) z
  have he : e (unitFiltrationQuotientMk F (Nat.zero_le χ.conductor) u) =
      residueUnits F u := by
    exact conductorOneUnitQuotientEquivResidueUnits_mk F χ hχ u
  change e.toEquiv (unitFiltrationQuotientMk F
    (Nat.zero_le χ.conductor) u) = residueUnits F u at he
  rw [finiteGaussSummand_mk, he, MulChar.inv_apply_eq_inv',
    residualMulChar_residueUnits F χ (by omega),
    residualAddChar_residueUnits F ψ (γ : Fˣ) hγ]
  rw [finiteGaussSummandRepresentative]
  ring

/-- The manuscript's exact conductor-one local-to-residue-field formula:
`Δ(χ,ψ;γ) = -χ(γ) ph(τ(χbar,ψbar))`. -/
theorem deltaFinite_conductor_one (χ : LocalQuasiCharData F)
    (hχ : χ.conductor = 1) (ψ : LocalAddCharData F)
    (γ : AdmissibleGamma F χ ψ) :
    let hγ : ord F ((γ : Fˣ) : F) =
        ((ψ.conductor + 1 : ℤ) : WithTop ℤ) :=
      admissibleGamma_order_conductor_one F χ hχ ψ γ
    deltaFinite χ ψ γ =
      -(χ.character (γ : Fˣ) : ℂ) *
        phase (langlandsGaussSum (residualMulChar F χ)
          (residualAddChar F ψ (γ : Fˣ) hγ)) := by
  let hγ : ord F ((γ : Fˣ) : F) =
      ((ψ.conductor + 1 : ℤ) : WithTop ℤ) :=
    admissibleGamma_order_conductor_one F χ hχ ψ γ
  dsimp only
  let τ := langlandsGaussSum (residualMulChar F χ)
    (residualAddChar F ψ (γ : Fˣ) hγ)
  have hψbar : residualAddChar F ψ (γ : Fˣ) hγ ≠ 1 :=
    residualAddChar_ne_one F ψ (γ : Fˣ) hγ
  have hτ : τ ≠ 0 := langlandsGaussSum_ne_zero (residualMulChar F χ) hψbar
  have hphase : phase (-τ) = -phase τ := by
    rw [show -τ = (-1 : ℂ) * τ by ring,
      phase_mul (neg_ne_zero.mpr one_ne_zero) hτ,
      phase_of_norm_eq_one (by simp)]
    ring
  rw [deltaFinite, finiteGaussSum_conductor_one F χ hχ ψ γ]
  change (χ.character (γ : Fˣ) : ℂ) * phase (-τ) = _
  rw [hphase]
  ring

end

end LanglandsFirstMainLemma
