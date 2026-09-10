import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Delta.FirstMainStatement
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility
import LanglandsFirstMainLemma.Basic.CharacterConductors
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Characters of the norm quotient

For a finite extension of nonarchimedean local fields this file uses the quotient in the
manuscript's orientation

`Fˣ / N_{K/F}(Kˣ) = Fˣ / (normUnits F K).range`.

First we identify continuous characters of that quotient with the project's
`NormCharacter F K`.  In the ramified cyclic-prime case we then compute the quotient order
without local class field theory: the global join/intersection statements of
`cyclicPrimeNormFiltration` reduce it to the cokernel of the critical graded norm.  The
unramified case uses the already proved normalized-order description of the quotient.

The trivial character is retained throughout.  Only statements about a positive ramified
conductor exclude it explicitly.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section BasicDefinitions

variable (F K : Type*) [Field F] [Field K]
  [TopologicalSpace F] [IsTopologicalRing F]
  [TopologicalSpace K] [IsTopologicalRing K]
  [Algebra F K] [Module.Free F K] [Module.Finite F K]
  [IsModuleTopology F K]

/-- The norm quotient, with the orientation `Fˣ / N_{K/F}(Kˣ)`. -/
abbrev NormQuotient := Fˣ ⧸ (normUnits F K).range

/-- Continuous characters of the norm quotient itself.  Continuity is with respect to the
quotient topology, so factorization does not require an arbitrary choice of representatives. -/
abbrev NormQuotientCharacter :=
  ContinuousMonoidHom (NormQuotient F K) ℂˣ

/-- The characters satisfying Langlands's norm-triviality condition form a subgroup of all
continuous quasi-characters. -/
def normCharacterSubgroup : Subgroup (ContinuousQuasiChar F) where
  carrier := { μ | normQuasiChar F K μ = 1 }
  one_mem' := by
    ext x
    rfl
  mul_mem' := by
    intro μ ν hμ hν
    change (μ * ν).pullback (continuousNormUnits F K) = 1
    change μ.pullback (continuousNormUnits F K) = 1 at hμ
    change ν.pullback (continuousNormUnits F K) = 1 at hν
    rw [ContinuousQuasiChar.mul_pullback, hμ, hν]
    exact one_mul (1 : ContinuousQuasiChar K)
  inv_mem' := by
    intro μ hμ
    change μ⁻¹.pullback (continuousNormUnits F K) = 1
    change μ.pullback (continuousNormUnits F K) = 1 at hμ
    rw [ContinuousQuasiChar.inv_pullback, hμ]
    rfl

/-- `NormCharacter F K` carries the pointwise commutative group structure. -/
instance instCommGroupNormCharacter : CommGroup (NormCharacter F K) :=
  inferInstanceAs (CommGroup (normCharacterSubgroup F K))

@[simp]
theorem NormCharacter.coe_one : ((1 : NormCharacter F K).1) = 1 :=
  rfl

@[simp]
theorem NormCharacter.coe_mul (μ ν : NormCharacter F K) :
    (μ * ν).1 = μ.1 * ν.1 :=
  rfl

@[simp]
theorem NormCharacter.coe_inv (μ : NormCharacter F K) :
    (μ⁻¹).1 = μ.1⁻¹ :=
  rfl

@[simp]
theorem NormCharacter.coe_pow (μ : NormCharacter F K) (n : ℕ) :
    (μ ^ n).1 = μ.1 ^ n :=
  rfl

/-- A project norm character is trivial on every element in the norm range. -/
theorem NormCharacter.eq_one_on_normRange (μ : NormCharacter F K)
    (x : Fˣ) (hx : x ∈ (normUnits F K).range) : μ.1 x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  have h := DFunLike.congr_fun μ.property y
  change μ.1 (normUnits F K y) = 1 at h
  exact h

/-- Factor a project norm character through `Fˣ / N(Kˣ)`.  Well-definedness is exactly
the norm-triviality field of `NormCharacter`; continuity follows from the quotient topology. -/
def NormCharacter.toQuotientCharacter (μ : NormCharacter F K) :
    NormQuotientCharacter F K := by
  let f : NormQuotient F K →* ℂˣ :=
    QuotientGroup.lift (normUnits F K).range μ.1.toMonoidHom (by
      intro x hx
      exact μ.eq_one_on_normRange F K x hx)
  refine ⟨f, ?_⟩
  apply (QuotientGroup.isQuotientMap_mk (normUnits F K).range).continuous_iff.mpr
  change Continuous μ.1
  exact μ.1.continuous

@[simp]
theorem NormCharacter.toQuotientCharacter_mk (μ : NormCharacter F K) (x : Fˣ) :
    μ.toQuotientCharacter F K (QuotientGroup.mk x) = μ.1 x :=
  rfl

/-- Pull a continuous quotient character back to `Fˣ`.  Every norm maps to the identity
class, so the result is a project `NormCharacter`. -/
def NormQuotientCharacter.toNormCharacter (ρ : NormQuotientCharacter F K) :
    NormCharacter F K := by
  refine ⟨ρ.comp ⟨QuotientGroup.mk' (normUnits F K).range,
      QuotientGroup.continuous_mk⟩, ?_⟩
  apply ContinuousMonoidHom.ext
  intro y
  rw [normQuasiChar_apply, ContinuousQuasiChar.one_apply]
  change ρ (QuotientGroup.mk (continuousNormUnits F K y)) = 1
  rw [show continuousNormUnits F K y = normUnits F K y from rfl]
  have hq : (QuotientGroup.mk (normUnits F K y) : NormQuotient F K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
  rw [hq, map_one]

@[simp]
theorem NormQuotientCharacter.toNormCharacter_apply
    (ρ : NormQuotientCharacter F K) (x : Fˣ) :
    (ρ.toNormCharacter F K).1 x = ρ (QuotientGroup.mk x) :=
  by
    change ρ (QuotientGroup.mk x) = ρ (QuotientGroup.mk x)
    rfl

/-- Continuous quotient characters and the `NormCharacter` type used in
`FirstMainStatement` are multiplicatively equivalent. -/
def normQuotientCharacterEquivNormCharacter :
    NormQuotientCharacter F K ≃* NormCharacter F K where
  toFun := NormQuotientCharacter.toNormCharacter F K
  invFun := NormCharacter.toQuotientCharacter F K
  left_inv := by
    intro ρ
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (normUnits F K).range q
    simp
  right_inv := by
    intro μ
    apply NormCharacter.ext
    ext x
    simp
  map_mul' := by
    intro ρ σ
    apply NormCharacter.ext
    ext x
    simp

/-- Algebraic quotient characters are continuous whenever the norm range is open. -/
def normQuotientCharacterEquivMonoidHom
    (hopen : IsOpen ((normUnits F K).range : Set Fˣ)) :
    NormQuotientCharacter F K ≃* (NormQuotient F K →* ℂˣ) where
  toFun ρ := ρ.toMonoidHom
  invFun ρ := by
    letI : DiscreteTopology (NormQuotient F K) :=
      QuotientGroup.discreteTopology hopen
    exact ⟨ρ, continuous_of_discreteTopology⟩
  left_inv ρ := by
    ext q
    rfl
  right_inv ρ := rfl
  map_mul' ρ σ := rfl

/-- For an open norm range, the continuous character group has the same cardinality as the
norm quotient. -/
theorem normQuotientCharacter_card
    (hopen : IsOpen ((normUnits F K).range : Set Fˣ))
    [Finite (NormQuotient F K)] :
    Nat.card (NormQuotientCharacter F K) = Nat.card (NormQuotient F K) := by
  letI : NeZero ((Monoid.exponent (NormQuotient F K) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr
      (Monoid.exponent_ne_zero_of_finite (G := NormQuotient F K))⟩
  rw [Nat.card_congr (normQuotientCharacterEquivMonoidHom F K hopen).toEquiv]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (NormQuotient F K) ℂ

/-- For an open norm range, the project's norm-character type has the same cardinality as
`Fˣ / N(Kˣ)`. -/
theorem normCharacter_card_of_isOpen
    (hopen : IsOpen ((normUnits F K).range : Set Fˣ))
    [Finite (NormQuotient F K)] :
    Nat.card (NormCharacter F K) = Nat.card (NormQuotient F K) := by
  rw [← normQuotientCharacter_card F K hopen]
  exact Nat.card_congr (normQuotientCharacterEquivNormCharacter F K).toEquiv.symm

end BasicDefinitions

section NormRangeTopology

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Fractional valuation lattices are open in a nonarchimedean local field. -/
theorem localFieldLattice_isOpen (n : ℤ) :
    IsOpen (lattice F n : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hopen := (ValuativeRel.valuation F).isOpen_closedBall
    (r := (ValuativeRel.valuation F).restrict a) (by simp [ha0])
  convert hopen using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    (ValuativeRel.valuation F).restrict_le_iff]

/-- Every positive-depth unit-filtration subgroup is open. -/
theorem unitFiltration_succ_isOpen (n : ℕ) :
    IsOpen (unitFiltration F (n + 1) : Set Fˣ) := by
  rw [show (unitFiltration F (n + 1) : Set Fˣ) =
      (fun u : Fˣ ↦ (u : F) - 1) ⁻¹' (lattice F ((n + 1 : ℕ) : ℤ) : Set F) by
    ext u
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact mem_unitFiltration_succ_iff_sub_mem_lattice F n u]
  have hcont : Continuous (fun u : Fˣ ↦ (u : F) - 1) :=
    Units.continuous_val.sub
      (continuous_const : Continuous (fun _ : Fˣ ↦ (1 : F)))
  simpa only [Nat.cast_add, Nat.cast_one] using
    (localFieldLattice_isOpen F ((n + 1 : ℕ) : ℤ)).preimage hcont

/-- Any subgroup containing a positive unit-filtration layer is open. -/
theorem subgroup_isOpen_of_unitFiltration_succ_le (H : Subgroup Fˣ) (n : ℕ)
    (h : unitFiltration F (n + 1) ≤ H) : IsOpen (H : Set Fˣ) :=
  Subgroup.isOpen_mono h (unitFiltration_succ_isOpen F n)

end NormRangeTopology

section RamifiedNormQuotient

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

local instance unitGradedPiece_commGroup : CommGroup (UnitGradedPiece F t) :=
  QuotientGroup.Quotient.commGroup _

local instance criticalGradedNormRange_normal :
    (criticalGradedNorm F K ht hres pi hpi hgen).range.Normal :=
  inferInstance

/-- The actual cokernel of the critical graded norm. -/
abbrev CriticalNormCokernel :=
  UnitGradedPiece F t ⧸
    (criticalGradedNorm F K ht hres pi hpi hgen).range

/-- Project the critical unit layer onto the cokernel of the critical graded norm. -/
noncomputable def criticalNormCokernelProjection :
    unitFiltration F t →* CriticalNormCokernel F K ht hres pi hpi hgen :=
  (QuotientGroup.mk'
      (criticalGradedNorm F K ht hres pi hpi hgen).range).comp
    (unitGradedMk F t)

theorem criticalNormCokernelProjection_surjective :
    Function.Surjective
      (criticalNormCokernelProjection F K ht hres pi hpi hgen) :=
  (QuotientGroup.mk'_surjective
      (criticalGradedNorm F K ht hres pi hpi hgen).range).comp
    (unitGradedMk_surjective F t)

/-- The kernel of the critical cokernel projection is precisely the honest full norm image
inside `U_F^t`. -/
theorem criticalNormCokernelProjection_ker :
    (criticalNormCokernelProjection F K ht hres pi hpi hgen).ker =
      criticalNormTargetImage F K ht hres pi hpi hgen := by
  ext u
  rw [MonoidHom.mem_ker]
  change
    (QuotientGroup.mk
        (unitGradedMk F t u) : CriticalNormCokernel F K ht hres pi hpi hgen) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  rfl

/-- The critical full-unit quotient is the critical graded cokernel. -/
noncomputable def criticalNormTargetQuotientEquivCokernel :
    (unitFiltration F t ⧸ criticalNormTargetImage F K ht hres pi hpi hgen) ≃*
      CriticalNormCokernel F K ht hres pi hpi hgen :=
  (QuotientGroup.quotientMulEquivOfEq
      (criticalNormCokernelProjection_ker F K ht hres pi hpi hgen).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (criticalNormCokernelProjection F K ht hres pi hpi hgen)
      (criticalNormCokernelProjection_surjective F K ht hres pi hpi hgen))

/-- Intersecting the global norm range with `U_F^t`, and then viewing the intersection
internally in `U_F^t`, gives the critical full norm image. -/
theorem normRangeSubgroupOfCritical_eq :
    ((normUnits F K).range.subgroupOf (unitFiltration F t)) =
      criticalNormTargetImage F K ht hres pi hpi hgen := by
  let hNF := cyclicPrimeNormFiltration F K ht hres pi hpi hgen
  ext u
  constructor
  · intro hu
    have hc : (u : Fˣ) ∈ criticalNormImage F K ht hres pi hpi hgen := by
      rw [← hNF.field_image_inf]
      exact ⟨hu, u.property⟩
    change (u : Fˣ) ∈ Subgroup.map (unitFiltration F t).subtype
      (criticalNormTargetImage F K ht hres pi hpi hgen) at hc
    obtain ⟨v, hv, huv⟩ := hc
    have hvu : v = u := Subtype.ext huv
    subst v
    exact hv
  · intro hu
    have hc : (u : Fˣ) ∈ criticalNormImage F K ht hres pi hpi hgen := by
      change (u : Fˣ) ∈ Subgroup.map (unitFiltration F t).subtype
        (criticalNormTargetImage F K ht hres pi hpi hgen)
      exact ⟨u, hu, rfl⟩
    have hi : (u : Fˣ) ∈ (normUnits F K).range ⊓ unitFiltration F t := by
      rw [hNF.field_image_inf]
      exact hc
    exact hi.1

/-- **Cardinality of the norm quotient.**  In the ramified cyclic prime-degree case,
`Fˣ / N(Kˣ)` has cardinality `[K : F]`.  The proof uses only the global
join/intersection conclusions and the critical cokernel cardinality from
`cyclicPrimeNormFiltration`. -/
theorem normQuotient_card :
    Nat.card (NormQuotient F K) = Module.finrank F K := by
  let N := (normUnits F K).range
  let U := unitFiltration F t
  let hNF := cyclicPrimeNormFiltration F K ht hres pi hpi hgen
  calc
    Nat.card (NormQuotient F K) = N.index := rfl
    _ = N.relIndex ⊤ := (Subgroup.relIndex_top_right N).symm
    _ = N.relIndex (N ⊔ U) := by rw [hNF.field_image_sup]
    _ = N.relIndex U := Subgroup.relIndex_sup_left U N
    _ = (criticalNormTargetImage F K ht hres pi hpi hgen).index := by
      rw [Subgroup.relIndex, normRangeSubgroupOfCritical_eq F K ht hres pi hpi hgen]
    _ = Nat.card (CriticalNormCokernel F K ht hres pi hpi hgen) :=
      Nat.card_congr
        (criticalNormTargetQuotientEquivCokernel F K ht hres pi hpi hgen).toEquiv
    _ = Module.finrank F K := hNF.critical_cokernel_card

/-- Finiteness of the ramified prime-degree norm quotient, obtained from its computed
nonzero cardinality. -/
theorem normQuotient_finite : Finite (NormQuotient F K) :=
  Nat.finite_of_card_ne_zero
    ((normQuotient_card F K ht hres pi hpi hgen).trans_ne Module.finrank_pos.ne')

/-- The global norm range is open in the ramified cyclic prime-degree case. -/
theorem ramifiedNormRange_isOpen :
    IsOpen ((normUnits F K).range : Set Fˣ) := by
  let hNF := cyclicPrimeNormFiltration F K ht hres pi hpi hgen
  apply subgroup_isOpen_of_unitFiltration_succ_le F (normUnits F K).range t
  intro u hu
  rw [← hNF.critical_successor_image] at hu
  obtain ⟨x, _hx, rfl⟩ := hu
  exact ⟨x, rfl⟩

/-- The project norm-character group has the same prime cardinality as the ramified norm
quotient; the trivial character is one of these `[K:F]` elements. -/
theorem ramifiedNormCharacter_card :
    Nat.card (NormCharacter F K) = Module.finrank F K := by
  letI : Finite (NormQuotient F K) :=
    normQuotient_finite F K ht hres pi hpi hgen
  exact (normCharacter_card_of_isOpen F K
    (ramifiedNormRange_isOpen F K ht hres pi hpi hgen)).trans
      (normQuotient_card F K ht hres pi hpi hgen)

/-- Finiteness of the complete ramified norm-character group, including its identity. -/
theorem ramifiedNormCharacter_finite : Finite (NormCharacter F K) :=
  Nat.finite_of_card_ne_zero
    ((ramifiedNormCharacter_card F K ht hres pi hpi hgen).trans_ne
      Module.finrank_pos.ne')

end RamifiedNormQuotient

section UnramifiedNormQuotient

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

variable (hunr : ramificationIndex F K = 1)

include hunr

/-- Finiteness of the unramified norm quotient. -/
theorem unramifiedNormQuotient_finite : Finite (NormQuotient F K) :=
  Nat.finite_of_card_ne_zero
    ((unramifiedNormQuotient_natCard F K hunr).trans_ne Module.finrank_pos.ne')

/-- Cardinality of the unramified norm quotient, re-exported under the node's naming
convention. -/
theorem unramifiedNormQuotient_card :
    Nat.card (NormQuotient F K) = Module.finrank F K :=
  unramifiedNormQuotient_natCard F K hunr

/-- The unramified norm range is open because it contains `U_F^1` (indeed it contains
`U_F^0`). -/
theorem unramifiedNormRange_isOpen :
    IsOpen ((normUnits F K).range : Set Fˣ) := by
  apply subgroup_isOpen_of_unitFiltration_succ_le F (normUnits F K).range 0
  intro u hu
  obtain ⟨x, _hx, hxu⟩ :=
    (unramified_norm_unitFiltration F K hunr 1).2 u hu
  exact ⟨x, hxu⟩

/-- The complete unramified norm-character group has `[K:F]` elements. -/
theorem unramifiedNormCharacter_card :
    Nat.card (NormCharacter F K) = Module.finrank F K := by
  letI : Finite (NormQuotient F K) := unramifiedNormQuotient_finite F K hunr
  exact (normCharacter_card_of_isOpen F K
    (unramifiedNormRange_isOpen F K hunr)).trans
      (unramifiedNormQuotient_natCard F K hunr)

/-- Finiteness of the complete unramified norm-character group, including its identity. -/
theorem unramifiedNormCharacter_finite : Finite (NormCharacter F K) :=
  Nat.finite_of_card_ne_zero
    ((unramifiedNormCharacter_card F K hunr).trans_ne Module.finrank_pos.ne')

end UnramifiedNormQuotient

section PrimeCyclicNormCharacterFiniteness

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Finiteness of the complete norm-character group for every prime-cyclic local-field
extension.  In the ramified branch the preparation package supplies the canonical lower
break and monogenic integral uniformizer required by the ramified finiteness theorem.  The
identity norm character remains included.  This is deliberately a non-instance API, so
downstream callers can install it locally with `letI`. -/
theorem primeCyclicNormCharacter_finite : Finite (NormCharacter F K) := by
  by_cases hunr : ramificationIndex F K = 1
  · exact unramifiedNormCharacter_finite F K hunr
  · let P : PrimeCyclicPreparation F K :=
      primeCyclicPreparation F K hunr
    exact ramifiedNormCharacter_finite F K
      P.ht P.hres P.piK P.hpiK P.hgen

end PrimeCyclicNormCharacterFiniteness

section NormCharacterConductors

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The trivial norm character has exact multiplicative conductor zero. -/
theorem trivialNormCharacter_conductor :
    IsMultiplicativeConductor F ((1 : NormCharacter F K).1) 0 := by
  apply IsMultiplicativeConductor.of_zero
  intro u _hu
  rfl

/-- Every norm character is trivial at every unit layer contained in the global norm range. -/
theorem NormCharacter.trivialOnUnitFiltration_of_le_normRange
    (μ : NormCharacter F K) (m : ℕ)
    (h : unitFiltration F m ≤ (normUnits F K).range) :
    QuasiCharTrivialOnUnitFiltration F μ.1 m := by
  intro u hu
  exact μ.eq_one_on_normRange F K u (h hu)

end NormCharacterConductors

section RamifiedNormCharacterConductors

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

/-- Every ramified norm character is trivial on the first unit layer beyond the lower
break. -/
theorem ramifiedNormCharacter_trivialOn_break_succ (μ : NormCharacter F K) :
    QuasiCharTrivialOnUnitFiltration F μ.1 (t + 1) := by
  let hNF := cyclicPrimeNormFiltration F K ht hres pi hpi hgen
  apply μ.trivialOnUnitFiltration_of_le_normRange F K
  intro u hu
  rw [← hNF.critical_successor_image] at hu
  obtain ⟨x, _hx, rfl⟩ := hu
  exact ⟨x, rfl⟩

/-- A norm character which is already trivial on the critical layer is globally trivial.
This is the non-cancellation boundary supplied by the global join statement. -/
theorem NormCharacter.eq_one_of_trivialOn_break
    (μ : NormCharacter F K)
    (hμ : QuasiCharTrivialOnUnitFiltration F μ.1 t) : μ = 1 := by
  let hNF := cyclicPrimeNormFiltration F K ht hres pi hpi hgen
  apply NormCharacter.ext
  apply ContinuousMonoidHom.ext
  intro x
  change μ.1 x = 1
  have hx : x ∈ (normUnits F K).range ⊔ unitFiltration F t := by
    rw [hNF.field_image_sup]
    exact Subgroup.mem_top x
  obtain ⟨y, hy, u, hu, hyu⟩ :=
    (Subgroup.mem_sup_of_normal_right.mp hx)
  rw [← hyu, map_mul, μ.eq_one_on_normRange F K y hy, hμ u hu]
  exact one_mul 1

/-- Every nontrivial norm character in a ramified cyclic prime-degree extension has exact
multiplicative conductor `t+1`. -/
theorem ramifiedNormCharacter_conductor
    (μ : NormCharacter F K) (hμ : μ ≠ 1) :
    IsMultiplicativeConductor F μ.1 (t + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · exact ramifiedNormCharacter_trivialOn_break_succ F K ht hres pi hpi hgen μ
  · intro htriv
    exact hμ (μ.eq_one_of_trivialOn_break F K ht hres pi hpi hgen htriv)

omit ht hres pi hpi hgen in
/-- In the tame prime-degree case the break is zero, so every nontrivial norm character has
exact conductor one. -/
theorem tameNormCharacter_conductor
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    (μ : NormCharacter F K) (hμ : μ ≠ 1) :
    IsMultiplicativeConductor F μ.1 1 := by
  simpa only [zero_add] using
    ramifiedNormCharacter_conductor F K ht hres pi hpi hgen μ hμ

/-- In the wild prime-degree case (`0<t`), every nontrivial norm character has exact
conductor `t+1` (and hence conductor at least two). -/
theorem wildNormCharacter_conductor
    (htwild : 0 < t) (μ : NormCharacter F K) (hμ : μ ≠ 1) :
    IsMultiplicativeConductor F μ.1 (t + 1) := by
  exact ramifiedNormCharacter_conductor F K ht hres pi hpi hgen μ hμ

end RamifiedNormCharacterConductors

section UnramifiedNormCharacterConductors

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- In an unramified extension every norm character, trivial or nontrivial, has exact
multiplicative conductor zero. -/
theorem unramifiedNormCharacter_conductor
    (hunr : ramificationIndex F K = 1) (μ : NormCharacter F K) :
    IsMultiplicativeConductor F μ.1 0 := by
  apply IsMultiplicativeConductor.of_zero
  apply μ.trivialOnUnitFiltration_of_le_normRange F K
  intro u hu
  obtain ⟨x, _hx, hxu⟩ :=
    (unramified_norm_unitFiltration F K hunr 0).2 u hu
  exact ⟨x, hxu⟩

end UnramifiedNormCharacterConductors

section FiniteEnumeration

variable (F K : Type*) [Field F] [Field K]
  [TopologicalSpace F] [IsTopologicalRing F]
  [TopologicalSpace K] [IsTopologicalRing K]
  [Algebra F K] [Module.Free F K] [Module.Finite F K]
  [IsModuleTopology F K]

/-- A coherent finite enumeration of all norm characters whenever their proved `Finite`
instance is installed.  The resulting `Finset.univ` contains the trivial character. -/
@[reducible] noncomputable def normCharacterFintype [Finite (NormCharacter F K)] :
    Fintype (NormCharacter F K) :=
  Fintype.ofFinite _

/-- The explicit finite set of all norm characters. -/
noncomputable def normCharacterFinset [Finite (NormCharacter F K)] :
    Finset (NormCharacter F K) :=
  @Finset.univ _ (normCharacterFintype F K)

/-- Multiplication by a fixed norm character permutes the complete norm-character group. -/
def normCharacterMulEquiv (τ : NormCharacter F K) :
    NormCharacter F K ≃ NormCharacter F K :=
  Equiv.mulLeft τ

@[simp]
theorem normCharacterMulEquiv_apply (τ μ : NormCharacter F K) :
    normCharacterMulEquiv F K τ μ = τ * μ :=
  rfl

/-- Reindexing a full finite product by multiplication with a norm character retains every
factor, including the trivial-character factor. -/
theorem normCharacter_prod_mul [Finite (NormCharacter F K)]
    {M : Type*} [CommMonoid M] (τ : NormCharacter F K)
    (f : NormCharacter F K → M) :
    (normCharacterFinset F K).prod (fun μ ↦ f (τ * μ)) =
      (normCharacterFinset F K).prod f := by
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  change (∏ μ : NormCharacter F K, f (τ * μ)) =
    ∏ μ : NormCharacter F K, f μ
  exact Equiv.prod_comp (normCharacterMulEquiv F K τ) f

/-- Any chosen cyclic enumeration restricts to an equivalence between its nonidentity
indices and the nontrivial norm characters. -/
noncomputable def nontrivialNormCharacterIndexEquiv {n : ℕ}
    (e : Multiplicative (ZMod n) ≃* NormCharacter F K) :
    {j : Multiplicative (ZMod n) // j ≠ 1} ≃
      {μ : NormCharacter F K // μ ≠ 1} :=
  e.toEquiv.subtypeEquiv fun j ↦ by
    exact (not_congr e.map_eq_one_iff).symm

end FiniteEnumeration

section PrimeDegreeIndices

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

/-- The canonical finite enumeration of `Z/[K:F]Z` for a prime-degree extension. -/
@[reducible] noncomputable def primeDegreeZModFintype :
    Fintype (Multiplicative (ZMod (Module.finrank F K))) := by
  letI : NeZero (Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩
  infer_instance

/-- All cyclic indices, including zero. -/
noncomputable def primeDegreeZModFinset :
    Finset (Multiplicative (ZMod (Module.finrank F K))) :=
  @Finset.univ _ (primeDegreeZModFintype F K)

end PrimeDegreeIndices

section RamifiedEnumeration

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

/-- The ramified norm-character group is cyclic of prime order. -/
theorem ramifiedNormCharacter_isCyclic : IsCyclic (NormCharacter F K) := by
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩
  exact isCyclic_of_prime_card
    (ramifiedNormCharacter_card F K ht hres pi hpi hgen)

/-- An explicit complete enumeration `j ↦ τ^j` of the ramified norm-character group by
`Z/[K:F]Z`; index zero maps to the trivial character. -/
noncomputable def ramifiedNormCharacterZModEquiv :
    Multiplicative (ZMod (Module.finrank F K)) ≃* NormCharacter F K := by
  let hcard := ramifiedNormCharacter_card F K ht hres pi hpi hgen
  rw [← hcard]
  exact zmodCyclicMulEquiv
    (ramifiedNormCharacter_isCyclic F K ht hres pi hpi hgen)

@[simp]
theorem ramifiedNormCharacterZModEquiv_zero :
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd (0 : ZMod (Module.finrank F K))) = 1 := by
  simpa using
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).map_one

theorem ramifiedNormCharacterZModEquiv_ne_one_iff
    (j : Multiplicative (ZMod (Module.finrank F K))) :
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen j ≠ 1 ↔ j ≠ 1 := by
  exact not_congr
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).map_eq_one_iff

/-- The explicit finite set of all ramified norm characters. -/
noncomputable def ramifiedNormCharacterFinset : Finset (NormCharacter F K) := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  exact normCharacterFinset F K

/-- Removing the trivial character leaves exactly `[K:F]-1` ramified norm characters. -/
theorem ramifiedNontrivialNormCharacter_card :
    Nat.card { μ : NormCharacter F K // μ ≠ 1 } = Module.finrank F K - 1 := by
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype { μ : NormCharacter F K // μ ≠ 1 } := Fintype.ofFinite _
  letI : Fintype (↑({ μ : NormCharacter F K | μ ≠ 1 } :
      Set (NormCharacter F K))) := Fintype.ofFinite _
  calc
    Nat.card { μ : NormCharacter F K // μ ≠ 1 } =
        Fintype.card { μ : NormCharacter F K // μ ≠ 1 } :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (NormCharacter F K) - 1 :=
      @Set.card_ne_eq (NormCharacter F K) _ (1 : NormCharacter F K) _
    _ = Nat.card (NormCharacter F K) - 1 := by
      rw [Nat.card_eq_fintype_card]
    _ = Module.finrank F K - 1 := by
      rw [ramifiedNormCharacter_card F K ht hres pi hpi hgen]

/-- Reindex a full product over all ramified norm characters by the complete `Z/[K:F]Z`
enumeration.  The zero/trivial term is not removed. -/
theorem ramifiedNormCharacterProduct_eq_zmodProduct
    {M : Type*} [CommMonoid M] (f : NormCharacter F K → M) :
    (ramifiedNormCharacterFinset F K ht hres pi hpi hgen).prod f =
      (primeDegreeZModFinset F K).prod
        (fun j ↦ f (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen j)) := by
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩
  letI : Finite (NormCharacter F K) :=
    ramifiedNormCharacter_finite F K ht hres pi hpi hgen
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype (Multiplicative (ZMod (Module.finrank F K))) :=
    primeDegreeZModFintype F K
  change (∏ μ : NormCharacter F K, f μ) =
    ∏ j : Multiplicative (ZMod (Module.finrank F K)),
      f (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen j)
  exact (Equiv.prod_comp
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen).toEquiv f).symm

end RamifiedEnumeration

section UnramifiedEnumeration

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (hunr : ramificationIndex F K = 1)

include hunr

/-- The unramified prime-degree norm-character group is cyclic. -/
theorem unramifiedNormCharacter_isCyclic : IsCyclic (NormCharacter F K) := by
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩
  exact isCyclic_of_prime_card (unramifiedNormCharacter_card F K hunr)

/-- A complete cyclic enumeration of the unramified prime-degree norm-character group. -/
noncomputable def unramifiedNormCharacterZModEquiv :
    Multiplicative (ZMod (Module.finrank F K)) ≃* NormCharacter F K := by
  let hcard := unramifiedNormCharacter_card F K hunr
  rw [← hcard]
  exact zmodCyclicMulEquiv (unramifiedNormCharacter_isCyclic F K hunr)

/-- Evaluation at an unramified uniformizer, first indexed by the computed cardinality of
the norm quotient. -/
noncomputable def unramifiedNormCharacterEvaluationEquivCard
    (π : Fˣ) (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F)) :
    NormCharacter F K ≃* rootsOfUnity (Nat.card (NormQuotient F K)) ℂ := by
  letI : Finite (NormQuotient F K) := unramifiedNormQuotient_finite F K hunr
  have hgen : ∀ q : NormQuotient F K,
      q ∈ Subgroup.zpowers (QuotientGroup.mk π : NormQuotient F K) := by
    intro q
    rw [unramifiedNormQuotient_uniformizer_generates F K hunr π hπ]
    exact Subgroup.mem_top q
  exact (normQuotientCharacterEquivNormCharacter F K).symm |>.trans
    ((normQuotientCharacterEquivMonoidHom F K
        (unramifiedNormRange_isOpen F K hunr)).trans
      ((IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hgen ℂˣ).trans
        (rootsOfUnityUnitsMulEquiv ℂ (Nat.card (NormQuotient F K)))))

@[simp]
theorem unramifiedNormCharacterEvaluationEquivCard_coe
    (π : Fˣ) (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F))
    (μ : NormCharacter F K) :
    (((unramifiedNormCharacterEvaluationEquivCard F K hunr π hπ μ :
        rootsOfUnity (Nat.card (NormQuotient F K)) ℂ) : ℂˣ) : ℂ) =
      ((μ.1 π : ℂˣ) : ℂ) := by
  simp [unramifiedNormCharacterEvaluationEquivCard,
    normQuotientCharacterEquivNormCharacter,
    normQuotientCharacterEquivMonoidHom,
    IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator,
    rootsOfUnityUnitsMulEquiv]

/-- In the unramified case, evaluation at a uniformizer identifies norm characters with all
`[K:F]`-th complex roots of unity.  Thus this is the enumeration aligned with the factors
appearing in the unramified product formula, rather than an arbitrary cyclic enumeration. -/
noncomputable def unramifiedNormCharacterEvaluationEquiv
    (π : Fˣ) (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F)) :
    NormCharacter F K ≃* rootsOfUnity (Module.finrank F K) ℂ := by
  rw [← unramifiedNormQuotient_natCard F K hunr]
  exact unramifiedNormCharacterEvaluationEquivCard F K hunr π hπ

/-- Every `[K:F]`-th root of unity occurs, uniquely, as the value of a norm character at an
unramified uniformizer. -/
theorem existsUnique_normCharacter_uniformizer_value
    (π : Fˣ) (hπ : (ValuativeRel.valuation F).IsUniformizer (π : F))
    (ζ : rootsOfUnity (Module.finrank F K) ℂ) :
    ∃! μ : NormCharacter F K,
      unramifiedNormCharacterEvaluationEquiv F K hunr π hπ μ = ζ := by
  exact (unramifiedNormCharacterEvaluationEquiv F K hunr π hπ).bijective.existsUnique ζ

/-- The explicit finite set of all unramified norm characters. -/
noncomputable def unramifiedNormCharacterFinset : Finset (NormCharacter F K) := by
  letI : Finite (NormCharacter F K) := unramifiedNormCharacter_finite F K hunr
  exact normCharacterFinset F K

/-- Removing the trivial character leaves exactly `[K:F]-1` unramified norm characters. -/
theorem unramifiedNontrivialNormCharacter_card :
    Nat.card { μ : NormCharacter F K // μ ≠ 1 } = Module.finrank F K - 1 := by
  letI : Finite (NormCharacter F K) := unramifiedNormCharacter_finite F K hunr
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype { μ : NormCharacter F K // μ ≠ 1 } := Fintype.ofFinite _
  letI : Fintype (↑({ μ : NormCharacter F K | μ ≠ 1 } :
      Set (NormCharacter F K))) := Fintype.ofFinite _
  calc
    Nat.card { μ : NormCharacter F K // μ ≠ 1 } =
        Fintype.card { μ : NormCharacter F K // μ ≠ 1 } :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (NormCharacter F K) - 1 :=
      @Set.card_ne_eq (NormCharacter F K) _ (1 : NormCharacter F K) _
    _ = Nat.card (NormCharacter F K) - 1 := by
      rw [Nat.card_eq_fintype_card]
    _ = Module.finrank F K - 1 := by
      rw [unramifiedNormCharacter_card F K hunr]

/-- Reindex a full product over all unramified norm characters, retaining the zero/trivial
term. -/
theorem unramifiedNormCharacterProduct_eq_zmodProduct
    {M : Type*} [CommMonoid M] (f : NormCharacter F K → M) :
    (unramifiedNormCharacterFinset F K hunr).prod f =
      (primeDegreeZModFinset F K).prod
        (fun j ↦ f (unramifiedNormCharacterZModEquiv F K hunr j)) := by
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩
  letI : Finite (NormCharacter F K) := unramifiedNormCharacter_finite F K hunr
  letI : Fintype (NormCharacter F K) := normCharacterFintype F K
  letI : Fintype (Multiplicative (ZMod (Module.finrank F K))) :=
    primeDegreeZModFintype F K
  change (∏ μ : NormCharacter F K, f μ) =
    ∏ j : Multiplicative (ZMod (Module.finrank F K)),
      f (unramifiedNormCharacterZModEquiv F K hunr j)
  exact (Equiv.prod_comp
    (unramifiedNormCharacterZModEquiv F K hunr).toEquiv f).symm

end UnramifiedEnumeration

section MinimalConductorTwist

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- Twist exact quasi-character data by a norm character and construct its *actual* least
conductor.  Existence follows from one common unit layer on which all norm characters are
trivial; the conductor is defined as the least such depth, not supplied as an input field. -/
noncomputable def normCharacterTwistData
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T)
    (μ : NormCharacter F K) : LocalQuasiCharData F := by
  classical
  have htriv : QuasiCharTrivialOnUnitFiltration F (μ.1 * χ.character)
      (max T χ.conductor) :=
    QuasiCharTrivialOnUnitFiltration.mul F
      (quasiCharTrivialOnUnitFiltration_mono F
        (Nat.le_max_left T χ.conductor) (hS μ))
      (χ.isConductor.trivialOnUnitFiltration_iff.2
        (Nat.le_max_right T χ.conductor))
  let hExists : ∃ m : ℕ,
      QuasiCharTrivialOnUnitFiltration F (μ.1 * χ.character) m :=
    ⟨max T χ.conductor, htriv⟩
  exact
    { character := μ.1 * χ.character
      conductor := Nat.find hExists
      isConductor :=
        ⟨Nat.find_spec hExists, fun _r hr ↦ Nat.find_min' hExists hr⟩ }

@[simp]
theorem normCharacterTwistData_character
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T)
    (μ : NormCharacter F K) :
    (normCharacterTwistData F K χ T hS μ).character =
      μ.1 * χ.character :=
  rfl

/-- A norm character whose twist of `χ` has least conductor among the full norm-character
orbit. -/
noncomputable def minimalConductorTwist
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T) : NormCharacter F K :=
  Function.argmin fun μ : NormCharacter F K ↦
    (normCharacterTwistData F K χ T hS μ).conductor

/-- The chosen minimal twist, packaged with its exact conductor proof. -/
noncomputable def minimalConductorTwistData
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T) : LocalQuasiCharData F :=
  normCharacterTwistData F K χ T hS
    (minimalConductorTwist F K χ T hS)

/-- The selected twist carries an exact (least-layer) conductor proof. -/
theorem minimalConductorTwist_isConductor
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T) :
    IsMultiplicativeConductor F
      (minimalConductorTwistData F K χ T hS).character
      (minimalConductorTwistData F K χ T hS).conductor :=
  (minimalConductorTwistData F K χ T hS).isConductor

/-- Universal minimality against every twist in the original norm-character orbit. -/
theorem minimalConductorTwist_minimal
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T)
    (ν : NormCharacter F K) :
    (minimalConductorTwistData F K χ T hS).conductor ≤
      (normCharacterTwistData F K χ T hS ν).conductor := by
  exact Function.argmin_le
    (fun μ : NormCharacter F K ↦
      (normCharacterTwistData F K χ T hS μ).conductor) ν

/-- Twisting the selected character once more by `ν` has the exact conductor carried by
the corresponding member `ν * minimalConductorTwist` of the original orbit. -/
theorem minimalConductorOrbitTwist_isConductor
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T)
    (ν : NormCharacter F K) :
    IsMultiplicativeConductor F
      (ν.1 * (minimalConductorTwistData F K χ T hS).character)
      (normCharacterTwistData F K χ T hS
        (ν * minimalConductorTwist F K χ T hS)).conductor := by
  have h := (normCharacterTwistData F K χ T hS
    (ν * minimalConductorTwist F K χ T hS)).isConductor
  convert h using 1
  apply ContinuousMonoidHom.ext
  intro x
  simp [minimalConductorTwistData, ContinuousQuasiChar.mul_apply, mul_assoc]

/-- Actual orbit minimality: if a further twist has any exact conductor `m`, then the
selected twist's conductor is at most `m`. -/
theorem minimalConductorTwist_actualMinimal
    (χ : LocalQuasiCharData F) (T : ℕ)
    (hS : ∀ μ : NormCharacter F K,
      QuasiCharTrivialOnUnitFiltration F μ.1 T)
    (ν : NormCharacter F K) (m : ℕ)
    (hm : IsMultiplicativeConductor F
      (ν.1 * (minimalConductorTwistData F K χ T hS).character) m) :
    (minimalConductorTwistData F K χ T hS).conductor ≤ m := by
  have heq : m = (normCharacterTwistData F K χ T hS
      (ν * minimalConductorTwist F K χ T hS)).conductor :=
    hm.unique (minimalConductorOrbitTwist_isConductor F K χ T hS ν)
  rw [heq]
  exact minimalConductorTwist_minimal F K χ T hS
    (ν * minimalConductorTwist F K χ T hS)

end MinimalConductorTwist

end

end LanglandsFirstMainLemma
