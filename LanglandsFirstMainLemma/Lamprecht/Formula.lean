import LanglandsFirstMainLemma.Lamprecht.StationaryClassCalculus
import LanglandsFirstMainLemma.Delta.FiniteDefinition
import LanglandsFirstMainLemma.FiniteField.QuadraticPhase
import LanglandsFirstMainLemma.FiniteField.HasseFunction

/-!
# Lamprecht's formula from the stationary numerator class

This file proves the even- and odd-conductor forms of Lamprecht's formula for
the representative-free finite local constant.  The stationary parameter is
constructed first as a lattice-quotient class.  Every subsequent theorem which
uses a field-valued numerator quantifies over a representative of that class
and records its exact order.

In odd conductor the residual additive character is itself defined from the
stationary quotient class.  Thus changing the representative does not change
the polar character: it translates the Hasse function.  The elementary factor
and the Hasse-sum phase are transported together, and their product is proved
independent of the representative.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Pointwise

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## The Lamprecht depth and the quotient-class parameter -/

/-- For `m = 2d + epsilon`, with `epsilon` zero or one, the Lamprecht
stationary depth is `d + epsilon`. -/
theorem lamprechtFormula_stationaryDepth
    (chi : LocalQuasiCharData F) (d epsilon : ℕ)
    (hepsilon : epsilon ≤ 1)
    (hm : chi.conductor = 2 * d + epsilon)
    (hlarge : 1 < chi.conductor) :
    IsLamprechtStationaryDepth chi.conductor (d + epsilon) := by
  exact ⟨hlarge, by omega, by omega⟩

/-- The stationary parameter occurring in Lamprecht's formula.  Its value is
the quotient class `St_{Gamma,d+epsilon}(chi)`; no representative is selected.

The theorem is deliberately stated as an existence-and-uniqueness assertion
whose witness is the already constructed quotient class.  It also records the
exact order of every permitted representative. -/
theorem StationaryParameter
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hm : chi.conductor = 2 * d + epsilon)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi) :
    let hr := lamprechtFormula_stationaryDepth F chi d epsilon
      hepsilon hm hlarge
    ∃! s : LamprechtCoefficientQuotient F (chi.conductor : ℤ)
        (chi.conductor : ℤ) ((d + epsilon : ℕ) : ℤ)
        hr.int_le_conductor,
      IsStationaryNumeratorClass F chi psi (chi.conductor : ℤ) hr
          Gamma s ∧
        ∀ (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ))),
          latticeQuotientMk F
              (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c = s →
            ord F (c : F) = 0 := by
  dsimp only
  let hr := lamprechtFormula_stationaryDepth F chi d epsilon
    hepsilon hm hlarge
  let s := stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
    hr Gamma Gamma.property
  refine ⟨s, ?_, ?_⟩
  · refine ⟨stationaryNumeratorClass_isStationary F chi psi
      (chi.conductor : ℤ) hr Gamma Gamma.property, ?_⟩
    intro c hc
    rw [stationaryNumeratorClass_representative_ord F chi psi
      (chi.conductor : ℤ) hr Gamma Gamma.property c hc]
    simp
  · intro t ht
    exact stationaryNumeratorClass_unique F chi psi (chi.conductor : ℤ)
      hr Gamma Gamma.property t ht.1

/-- An arbitrary representative of the stationary class, bundled as a field
unit.  Exact order, rather than a choice operator, supplies nonvanishing. -/
def lamprechtStationaryRepresentativeUnit
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property) : Fˣ :=
  Units.mk0 (c : F) (by
    apply (ord_ne_top_iff F).1
    rw [stationaryNumeratorClass_representative_ord F chi psi
      (chi.conductor : ℤ) hr Gamma Gamma.property c hc]
    simp)

@[simp]
theorem lamprechtStationaryRepresentativeUnit_coe
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property) :
    ((lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc : Fˣ) : F) =
      (c : F) :=
  rfl

theorem lamprechtStationaryRepresentativeUnit_ord
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property) :
    ord F ((lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc : Fˣ) : F) =
      0 := by
  rw [lamprechtStationaryRepresentativeUnit_coe,
    stationaryNumeratorClass_representative_ord F chi psi
      (chi.conductor : ℤ) hr Gamma Gamma.property c hc]
  simp

/-! ## The quotient-class residual additive character -/

/-- Multiplication by `delta^2` identifies a residue class with a variable
class in `p^(d+1)/p^m`, where `m=2d+1`.  The definition descends arbitrary
integral lifts, rather than choosing a representative of a residue class. -/
noncomputable def lamprechtResidualVariable
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    ResidueField F →+
      LamprechtVariableQuotient F (chi.conductor : ℤ) ((d + 1 : ℕ) : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge).int_le_conductor where
  toFun x := latticeQuotientMk F
      (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge).int_le_conductor
      ⟨(delta : F) ^ 2 * (teichmuller F x : F), by
        have hdpos : 0 < d := by omega
        have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
          rw [mem_lattice, hdelta]
        have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
          simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
        have htx : (teichmuller F x : F) ∈ lattice F 0 :=
          (mem_lattice_zero_iff F).2 (teichmuller F x).property
        have hp : (delta : F) ^ 2 * (teichmuller F x : F) ∈
            lattice F ((d : ℤ) + d) := by
          simpa using mul_mem_lattice F hdeltaSq htx
        exact lattice_antitone F (by
          exact_mod_cast (show d + 1 ≤ d + d by omega)) hp⟩
  map_zero' := by
    rw [map_zero]
    apply (latticeQuotientMk_eq_zero_iff F _).2
    simp
  map_add' x y := by
    apply (latticeQuotientMk_eq_mk_iff F
      (lamprechtFormula_stationaryDepth F chi d 1
        (by omega) hm hlarge).int_le_conductor).2
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
theorem lamprechtResidualVariable_integral_lift
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (z : F) (hz : z ∈ lattice F 0) :
    lamprechtResidualVariable F chi d hm hlarge delta hdelta (reduce F z hz) =
      latticeQuotientMk F
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge).int_le_conductor
        ⟨(delta : F) ^ 2 * z, by
          have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
            rw [mem_lattice, hdelta]
          have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
            simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
          have hp : (delta : F) ^ 2 * z ∈ lattice F ((d : ℤ) + d) := by
            simpa using mul_mem_lattice F hdeltaSq hz
          exact lattice_antitone F (by
            exact_mod_cast (show d + 1 ≤ d + d by omega)) hp⟩ := by
  apply (latticeQuotientMk_eq_mk_iff F
    (lamprechtFormula_stationaryDepth F chi d 1
      (by omega) hm hlarge).int_le_conductor).2
  change (delta : F) ^ 2 * (teichmuller F (reduce F z hz) : F) -
      (delta : F) ^ 2 * z ∈ lattice F (chi.conductor : ℤ)
  have hdiff : (teichmuller F (reduce F z hz) : F) - z ∈ lattice F 1 := by
    let zint : ringOfIntegers F :=
      ⟨z, (mem_lattice_zero_iff F).1 hz⟩
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

/-- The residual polar character in odd conductor.  It is obtained by pairing
the stationary quotient class itself with `delta^2` times a residue class, so
it is independent of every representative of that class. -/
noncomputable def lamprechtResidualAddChar
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    FiniteAddChar (ResidueField F) :=
  let hr := lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge
  (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)).compAddMonoidHom
    (lamprechtResidualVariable F chi d hm hlarge delta hdelta)

/-- Evaluation of the residual polar character on any integral lift and any
representative of the stationary class. -/
theorem lamprechtResidualAddChar_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ) (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge)
        Gamma Gamma.property)
    (z : F) (hz : z ∈ lattice F 0) :
    lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta
        (reduce F z hz) =
      (psi.character
        ((c : F) * (delta : F) ^ 2 * z / ((Gamma : Fˣ) : F)) : ℂ) := by
  let hr := lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge
  change (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property))
      (lamprechtResidualVariable F chi d hm hlarge delta hdelta
        (reduce F z hz)) = _
  rw [lamprechtResidualVariable_integral_lift]
  rw [← hc, lamprechtPairingLeft_apply, lamprechtPairing_mk_mk]
  congr 2
  ring

/-- Exact order of a stationary representative makes the residual polar
character nontrivial. -/
theorem lamprechtResidualAddChar_ne_one
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta ≠ 1 := by
  let hr := lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  obtain ⟨x, hxord, hpsi⟩ := psi.isConductor.exists_ord_eq_predecessor
  let z : F := x * ((Gamma : Fˣ) : F) / ((beta : F) * (delta : F) ^ 2)
  have hzord : ord F z = 0 := by
    dsimp only [z]
    rw [ord_div, ord_mul, hxord, Gamma.property, ord_mul, hbeta, ord_pow,
      hdelta]
    norm_cast
    simp only [two_nsmul]
    omega
  have hz : z ∈ lattice F 0 := by
    rw [mem_lattice, hzord]
    norm_num
  intro htrivial
  have happ : lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta
      (reduce F z hz) = 1 := by
    rw [htrivial]
    exact AddChar.one_apply _
  rw [lamprechtResidualAddChar_integral_lift
    F chi psi d hm hlarge Gamma delta hdelta c hc z hz] at happ
  have harg : (c : F) * (delta : F) ^ 2 * z /
      ((Gamma : Fˣ) : F) = x := by
    dsimp only [z]
    rw [show (c : F) = (beta : F) by rfl]
    field_simp [Units.ne_zero beta, Units.ne_zero delta,
      AdmissibleGamma.coe_ne_zero Gamma]
  rw [harg] at happ
  apply hpsi
  apply Units.ext
  simpa using happ

/-- Every permitted stationary representative gives the same exact odd
residual coefficient order.  In particular the polar additive character has
the manuscript's conductor-one residue depth, with the sign made explicit. -/
theorem lamprechtOdd_residualCoefficient_ord
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    ord F ((c : F) * (delta : F) ^ 2 / ((Gamma : Fˣ) : F)) =
      ((-psi.conductor - 1 : ℤ) : WithTop ℤ) := by
  have hcOrd : ord F (c : F) = 0 := by
    rw [stationaryNumeratorClass_representative_ord F chi psi
      (chi.conductor : ℤ)
      (lamprechtFormula_stationaryDepth F chi d 1
        (by omega) hm hlarge) Gamma Gamma.property c hc]
    simp
  rw [ord_div, ord_mul, hcOrd, ord_pow, hdelta, Gamma.property]
  norm_cast
  simp only [two_nsmul]
  omega

/-! ## The odd residual Hasse function -/

theorem lamprechtOdd_d_pos
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor) : 0 < d := by
  omega

/-- The unit `1 + delta*z`, with `z` integral, at the odd critical depth. -/
def lamprechtHasseUnit
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (z : F) (hz : z ∈ lattice F 0) : unitFiltration F d :=
  positiveUnitOfLattice F (lamprechtOdd_d_pos F chi d hm hlarge)
    ⟨(delta : F) * z, by
      have hd : (delta : F) ∈ lattice F (d : ℤ) := by
        rw [mem_lattice, hdelta]
      simpa using mul_mem_lattice F hd hz⟩

@[simp]
theorem lamprechtHasseUnit_coe
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (z : F) (hz : z ∈ lattice F 0) :
    ((lamprechtHasseUnit F chi d hm hlarge delta hdelta z hz : Fˣ) : F) =
      1 + (delta : F) * z :=
  rfl

/-- The lift-level critical function.  Descent to the residue field is proved
below; this definition itself makes every lift and every stationary
representative explicit. -/
def lamprechtHasseValue
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (z : F) (hz : z ∈ lattice F 0) : ℂ :=
  (psi.character ((c : F) * (delta : F) * z / ((Gamma : Fˣ) : F)) : ℂ) *
    (chi.character
      (lamprechtHasseUnit F chi d hm hlarge delta hdelta z hz) : ℂ)⁻¹

theorem lamprechtHasseValue_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (z : F) (hz : z ∈ lattice F 0) :
    lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c z hz ≠ 0 :=
  mul_ne_zero (ContinuousAddChar.apply_ne_zero _ _)
    (inv_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _))

private theorem lamprechtAddChar_eq_of_sub_mem
    (psi : LocalAddCharData F) {a b : F}
    (hab : a - b ∈ lattice F (-psi.conductor)) :
    psi.character a = psi.character b := by
  apply Units.ext
  apply (div_eq_one_iff_eq (Units.ne_zero (psi.character b))).1
  have hdiv : psi.character a / psi.character b = 1 := by
    calc
      psi.character a / psi.character b =
          psi.character.toAddChar (a - b) :=
        (psi.character.toAddChar.map_sub_eq_div a b).symm
      _ = 1 := psi.isConductor.trivial (a - b) hab
  simpa using congrArg Units.val hdiv

/-- Changing an integral lift by an element of the maximal ideal leaves the
critical function unchanged.  The additive change and the multiplicative
stationary linearization are cancelled together. -/
theorem lamprechtHasseValue_eq_of_congruent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (z z' : F) (hz : z ∈ lattice F 0) (hz' : z' ∈ lattice F 0)
    (hzz' : CongruentAtDepth 1 z z') :
    lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c z hz =
      lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c z' hz' := by
  have hdiff : z - z' ∈ lattice F 1 :=
    (congruentAtDepth_iff_sub_mem_lattice F 1 z z').1 hzz'
  let u' := lamprechtHasseUnit F chi d hm hlarge delta hdelta z' hz'
  have hu'ne : 1 + (delta : F) * z' ≠ 0 := by
    rw [← lamprechtHasseUnit_coe F chi d hm hlarge delta hdelta z' hz']
    exact Units.ne_zero
      (lamprechtHasseUnit F chi d hm hlarge delta hdelta z' hz' : Fˣ)
  have hu'ord : ord F ((u' : Fˣ) : F) = 0 := by
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
    (lamprechtFormula_stationaryDepth F chi d 1
      (by omega) hm hlarge).pos wx
  have hunit :
      (lamprechtHasseUnit F chi d hm hlarge delta hdelta z hz : Fˣ) =
        (u' : Fˣ) * (uw : Fˣ) := by
    apply Units.ext
    change 1 + (delta : F) * z =
      (1 + (delta : F) * z') * (1 + w)
    dsimp only [w, u']
    rw [lamprechtHasseUnit_coe]
    field_simp [hu'ne]
    ring
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ)
    (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge)
    Gamma Gamma.property c hc wx
  have hlinearC := congrArg (Units.val : ℂˣ → ℂ) hlinear
  have hchi :
      (chi.character
        (lamprechtHasseUnit F chi d hm hlarge delta hdelta z hz) : ℂ) =
      (chi.character (u' : Fˣ) : ℂ) *
        (psi.character ((c : F) * w / ((Gamma : Fˣ) : F)) : ℂ) := by
    rw [hunit, map_mul]
    exact congrArg₂ (· * ·) rfl hlinearC
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
      rw [lamprechtHasseUnit_coe]
      field_simp [hu'ne]
      ring
    rw [halg]
    exact herror
  have hcerror : (c : F) * ((delta : F) * (z - z') - w) /
      ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
    have hc0 : (c : F) ∈ lattice F 0 := by
      simpa only [sub_self] using c.property
    have hmul := mul_mem_lattice F hc0 hdifference
    have hmul' : (c : F) * ((delta : F) * (z - z') - w) ∈
        lattice F (chi.conductor : ℤ) := by
      simpa only [zero_add] using hmul
    apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
      ((c : F) * ((delta : F) * (z - z') - w))
      ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
      Gamma.property).2
    simpa only [add_assoc, add_neg_cancel, add_zero] using hmul'
  have hpsiUnits :
      psi.character ((c : F) * ((delta : F) * (z - z')) /
        ((Gamma : Fˣ) : F)) =
      psi.character ((c : F) * w / ((Gamma : Fˣ) : F)) := by
    apply lamprechtAddChar_eq_of_sub_mem F psi
    have halg :
        (c : F) * ((delta : F) * (z - z')) / ((Gamma : Fˣ) : F) -
          (c : F) * w / ((Gamma : Fˣ) : F) =
        (c : F) * ((delta : F) * (z - z') - w) /
          ((Gamma : Fˣ) : F) := by ring
    rw [halg]
    exact hcerror
  have hpsiC := congrArg (Units.val : ℂˣ → ℂ) hpsiUnits
  have hadd :
      (psi.character ((c : F) * (delta : F) * z /
        ((Gamma : Fˣ) : F)) : ℂ) =
      (psi.character ((c : F) * ((delta : F) * (z - z')) /
        ((Gamma : Fˣ) : F)) : ℂ) *
      (psi.character ((c : F) * (delta : F) * z' /
        ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := ContinuousAddChar.map_add_eq_mul psi.character
      ((c : F) * ((delta : F) * (z - z')) / ((Gamma : Fˣ) : F))
      ((c : F) * (delta : F) * z' / ((Gamma : Fˣ) : F))
    have hmapC := congrArg (Units.val : ℂˣ → ℂ) hmap
    push_cast at hmapC
    convert hmapC using 1 <;> ring
  rw [lamprechtHasseValue, lamprechtHasseValue, hchi, hadd, hpsiC]
  have hp0 : (psi.character ((c : F) * w / ((Gamma : Fˣ) : F)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  field_simp
  rfl

/-- The lift-level critical function has the positive polar character supplied
by the quotient-class residual character. -/
theorem lamprechtHasseValue_map_add
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (x y : ResidueField F) :
    lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
        (teichmuller F (x + y) : F)
        ((mem_lattice_zero_iff F).2 (teichmuller F (x + y)).property) =
      lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
          (teichmuller F x : F)
          ((mem_lattice_zero_iff F).2 (teichmuller F x).property) *
        lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
          (teichmuller F y : F)
          ((mem_lattice_zero_iff F).2 (teichmuller F y).property) *
        lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta
          (x * y) := by
  let tx : F := (teichmuller F x : F)
  let ty : F := (teichmuller F y : F)
  have htx : tx ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  have hty : ty ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F y).property
  have hsum : tx + ty ∈ lattice F 0 := add_mem htx hty
  have hcanon :
      lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
          (teichmuller F (x + y) : F)
          ((mem_lattice_zero_iff F).2 (teichmuller F (x + y)).property) =
      lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
          (tx + ty) hsum := by
    apply lamprechtHasseValue_eq_of_congruent F chi psi d hm hlarge
      Gamma delta hdelta c hc
    apply (congruentAtDepth_iff_sub_mem_lattice F 1 _ _).2
    apply (residueMap_eq_residueMap_iff F
      (teichmuller F (x + y)) (teichmuller F x + teichmuller F y)).1
    simp [tx, ty]
  rw [hcanon]
  let us := lamprechtHasseUnit F chi d hm hlarge delta hdelta (tx + ty) hsum
  have husord : ord F ((us : Fˣ) : F) = 0 := by
    apply (mem_unitFiltration_zero F (us : Fˣ)).1
    exact unitFiltration_antitone F (Nat.zero_le d) us.property
  have hdeltaMem : (delta : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have hdeltaSq : (delta : F) ^ 2 ∈ lattice F ((d : ℤ) + d) := by
    simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
  have hxy : tx * ty ∈ lattice F 0 := by
    simpa using mul_mem_lattice F htx hty
  have hquad : (delta : F) ^ 2 * (tx * ty) ∈ lattice F ((d : ℤ) + d) := by
    simpa using mul_mem_lattice F hdeltaSq hxy
  let w : F := (delta : F) ^ 2 * (tx * ty) / ((us : Fˣ) : F)
  have hw : w ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    apply (div_mem_lattice_iff F ((us : Fˣ) : F)
      ((delta : F) ^ 2 * (tx * ty)) 0 ((d + 1 : ℕ) : ℤ) husord).2
    have hquad' : (delta : F) ^ 2 * (tx * ty) ∈
        lattice F ((d + 1 : ℕ) : ℤ) := by
      have hineq : ((d + 1 : ℕ) : ℤ) ≤ (d : ℤ) + d := by
        have := lamprechtOdd_d_pos F chi d hm hlarge
        omega
      exact lattice_antitone F hineq hquad
    simpa only [zero_add] using hquad'
  let wx : lattice F ((d + 1 : ℕ) : ℤ) := ⟨w, hw⟩
  let uw := positiveUnitOfLattice F
    (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge).pos wx
  have hunit :
      (lamprechtHasseUnit F chi d hm hlarge delta hdelta tx htx : Fˣ) *
          (lamprechtHasseUnit F chi d hm hlarge delta hdelta ty hty : Fˣ) =
        (us : Fˣ) * (uw : Fˣ) := by
    apply Units.ext
    change (1 + (delta : F) * tx) * (1 + (delta : F) * ty) =
      (1 + (delta : F) * (tx + ty)) * (1 + w)
    have husne : 1 + (delta : F) * (tx + ty) ≠ 0 := by
      rw [← lamprechtHasseUnit_coe F chi d hm hlarge delta hdelta
        (tx + ty) hsum]
      exact Units.ne_zero (us : Fˣ)
    dsimp only [w, us]
    rw [lamprechtHasseUnit_coe]
    field_simp [husne]
    ring
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ)
    (lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge)
    Gamma Gamma.property c hc wx
  have hlinearC := congrArg (Units.val : ℂˣ → ℂ) hlinear
  have hchi :
      (chi.character
        (lamprechtHasseUnit F chi d hm hlarge delta hdelta tx htx) : ℂ) *
      (chi.character
        (lamprechtHasseUnit F chi d hm hlarge delta hdelta ty hty) : ℂ) =
      (chi.character (us : Fˣ) : ℂ) *
        (psi.character ((c : F) * w / ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := congrArg (Units.val : ℂˣ → ℂ)
      (congrArg chi.character hunit)
    push_cast at hmap
    rw [map_mul, map_mul] at hmap
    exact hmap.trans (congrArg₂ (· * ·) rfl hlinearC)
  have hsumPsi :
      (psi.character ((c : F) * (delta : F) * (tx + ty) /
        ((Gamma : Fˣ) : F)) : ℂ) =
      (psi.character ((c : F) * (delta : F) * tx /
        ((Gamma : Fˣ) : F)) : ℂ) *
      (psi.character ((c : F) * (delta : F) * ty /
        ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := ContinuousAddChar.map_add_eq_mul psi.character
      ((c : F) * (delta : F) * tx / ((Gamma : Fˣ) : F))
      ((c : F) * (delta : F) * ty / ((Gamma : Fˣ) : F))
    have hmapC := congrArg (Units.val : ℂˣ → ℂ) hmap
    push_cast at hmapC
    convert hmapC using 1 <;> ring
  have hredxy : reduce F (tx * ty) hxy = x * y := by
    change residueMap F (teichmuller F x * teichmuller F y) = x * y
    simp [tx, ty]
  have hpsi0 := lamprechtResidualAddChar_integral_lift
    F chi psi d hm hlarge Gamma delta hdelta c hc (tx * ty) hxy
  rw [hredxy] at hpsi0
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
      have hdpos := lamprechtOdd_d_pos F chi d hm hlarge
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
        rw [← lamprechtHasseUnit_coe F chi d hm hlarge delta hdelta
          (tx + ty) hsum]
        exact Units.ne_zero (us : Fˣ)
      dsimp only [w, us]
      rw [lamprechtHasseUnit_coe]
      field_simp [husne]
      ring
    rw [halg]
    exact herror
  have hc0 : (c : F) ∈ lattice F 0 := by
    simpa only [sub_self] using c.property
  have hcmul : (c : F) * ((delta : F) ^ 2 * (tx * ty) - w) ∈
      lattice F (chi.conductor : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice F hc0 hquadDifference
  have hcerror : (c : F) * ((delta : F) ^ 2 * (tx * ty) - w) /
      ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
    apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
      ((c : F) * ((delta : F) ^ 2 * (tx * ty) - w))
      ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
      Gamma.property).2
    simpa only [add_assoc, add_neg_cancel, add_zero] using hcmul
  have hquadPsiUnits :
      psi.character ((c : F) * ((delta : F) ^ 2 * (tx * ty)) /
        ((Gamma : Fˣ) : F)) =
      psi.character ((c : F) * w / ((Gamma : Fˣ) : F)) := by
    apply lamprechtAddChar_eq_of_sub_mem F psi
    have halg :
        (c : F) * ((delta : F) ^ 2 * (tx * ty)) / ((Gamma : Fˣ) : F) -
          (c : F) * w / ((Gamma : Fˣ) : F) =
        (c : F) * ((delta : F) ^ 2 * (tx * ty) - w) /
          ((Gamma : Fˣ) : F) := by ring
    rw [halg]
    exact hcerror
  have hquadPsiC := congrArg (Units.val : ℂˣ → ℂ) hquadPsiUnits
  have hpsi0C :
      lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta (x * y) =
        (psi.character ((c : F) * ((delta : F) ^ 2 * (tx * ty)) /
          ((Gamma : Fˣ) : F)) : ℂ) := by
    convert hpsi0 using 1 <;> ring
  rw [lamprechtHasseValue, lamprechtHasseValue, lamprechtHasseValue,
    hsumPsi, hpsi0C, hquadPsiC]
  have hcx0 :
      (chi.character
        (lamprechtHasseUnit F chi d hm hlarge delta hdelta tx htx) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero _ _
  have hcy0 :
      (chi.character
        (lamprechtHasseUnit F chi d hm hlarge delta hdelta ty hty) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero _ _
  have hcs0 : (chi.character (us : Fˣ) : ℂ) ≠ 0 :=
    ContinuousQuasiChar.apply_ne_zero _ _
  change
    (psi.character ((c : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) *
        (psi.character ((c : F) * (delta : F) * ty / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character (us : Fˣ) : ℂ)⁻¹ =
      ((psi.character ((c : F) * (delta : F) * tx / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character
            (lamprechtHasseUnit F chi d hm hlarge delta hdelta tx htx) : ℂ)⁻¹) *
        ((psi.character ((c : F) * (delta : F) * ty / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character
            (lamprechtHasseUnit F chi d hm hlarge delta hdelta ty hty) : ℂ)⁻¹) *
        (psi.character ((c : F) * w / ((Gamma : Fˣ) : F)) : ℂ)
  field_simp [hcx0, hcy0, hcs0]
  rw [hchi]

/-- The genuinely constructed odd-conductor Hasse function. -/
noncomputable def lamprechtHasseFunction
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    HasseFunction (ResidueField F)
      (lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta) where
  toFun x := lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
    (teichmuller F x : F)
    ((mem_lattice_zero_iff F).2 (teichmuller F x).property)
  ne_zero' x := lamprechtHasseValue_ne_zero F chi psi d hm hlarge Gamma delta
    hdelta c (teichmuller F x : F)
      ((mem_lattice_zero_iff F).2 (teichmuller F x).property)
  map_add' := lamprechtHasseValue_map_add F chi psi d hm hlarge Gamma delta
    hdelta c hc

/-- Evaluation of the Hasse function on the reduction of every integral
lift.  This is the explicit well-definedness theorem used below. -/
theorem lamprechtHasseFunction_integral_lift
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (z : F) (hz : z ∈ lattice F 0) :
    lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc
        (reduce F z hz) =
      lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c z hz := by
  apply lamprechtHasseValue_eq_of_congruent F chi psi d hm hlarge
    Gamma delta hdelta c hc
  apply (congruentAtDepth_iff_sub_mem_lattice F 1 _ _).2
  let zint : ringOfIntegers F := ⟨z, (mem_lattice_zero_iff F).1 hz⟩
  apply (residueMap_eq_residueMap_iff F
    (teichmuller F (reduce F z hz)) zint).1
  simp [reduce, zint]

/-! ## Elementary stationary factor -/

/-- The elementary factor attached to an explicitly chosen stationary
representative. -/
def lamprechtElementaryFactor
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (Gamma : AdmissibleGamma F chi psi) (beta : Fˣ) : ℂ :=
  (psi.character ((beta : F) / ((Gamma : Fˣ) : F)) : ℂ) *
    (chi.character beta : ℂ)⁻¹

theorem lamprechtElementaryFactor_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (Gamma : AdmissibleGamma F chi psi) (beta : Fˣ) :
    lamprechtElementaryFactor F chi psi Gamma beta ≠ 0 :=
  mul_ne_zero (ContinuousAddChar.apply_ne_zero _ _)
    (inv_ne_zero (ContinuousQuasiChar.apply_ne_zero _ _))

theorem lamprechtElementaryFactor_norm
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (Gamma : AdmissibleGamma F chi psi) (beta : Fˣ)
    (hbeta : ord F (beta : F) = 0) :
    ‖lamprechtElementaryFactor F chi psi Gamma beta‖ = 1 := by
  let beta0 : unitFiltration F 0 :=
    ⟨beta, (mem_unitFiltration_zero F beta).2 hbeta⟩
  rw [lamprechtElementaryFactor, norm_mul, norm_inv,
    localAddChar_norm_eq_one F psi,
    show ‖(chi.character beta : ℂ)‖ = 1 by
      change ‖(chi.character (beta0 : Fˣ) : ℂ)‖ = 1
      exact quasiChar_norm_eq_one_of_mem_unitFiltration_zero chi beta0]
  norm_num

/-- In even conductor the elementary factor alone is independent of the
representative of the stationary quotient class. -/
theorem lamprechtEven_elementary_representative_independent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (c c' : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 0
          (by omega) (by simpa using hm) hlarge) Gamma Gamma.property)
    (hc' : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge).int_le_conductor
          (chi.conductor : ℤ)) c' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 0
          (by omega) (by simpa using hm) hlarge) Gamma Gamma.property) :
    lamprechtElementaryFactor F chi psi Gamma
        (lamprechtStationaryRepresentativeUnit F chi psi
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge) Gamma c hc) =
      lamprechtElementaryFactor F chi psi Gamma
        (lamprechtStationaryRepresentativeUnit F chi psi
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge) Gamma c' hc') := by
  let hr := lamprechtFormula_stationaryDepth F chi d 0
    (by omega) (by simpa using hm) hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  let beta' := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c' hc'
  change lamprechtElementaryFactor F chi psi Gamma beta =
    lamprechtElementaryFactor F chi psi Gamma beta'
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  have hclasses : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c' :=
    hc.trans hc'.symm
  have hcong := (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
    (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ))).1 hclasses
  have hdepth : (chi.conductor : ℤ) - (d : ℕ) = (d : ℤ) := by omega
  have hcong' : CongruentAtDepth ((chi.conductor : ℤ) - (d : ℕ))
      (c : F) (c' : F) := by
    simpa only [Nat.add_zero] using hcong
  rw [hdepth] at hcong'
  have hdiff : (beta' : F) - (beta : F) ∈ lattice F (d : ℤ) := by
    exact (congruentAtDepth_iff_sub_mem_lattice F (d : ℤ)
      (beta' : F) (beta : F)).1 hcong'.symm
  let x : F := ((beta' : F) - (beta : F)) / (beta : F)
  have hx : x ∈ lattice F (d : ℤ) := by
    exact (div_mem_lattice_iff F (beta : F)
      ((beta' : F) - (beta : F)) 0 (d : ℤ) hbeta).2 (by simpa using hdiff)
  let xl : lattice F (d : ℤ) := ⟨x, hx⟩
  have hlinear := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ) hr Gamma Gamma.property c hc xl
  have hunit : (positiveUnitOfLattice F hr.pos xl : Fˣ) = beta' / beta := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, Units.val_div_eq_div_val]
    change 1 + x = (beta' : F) / (beta : F)
    dsimp only [x]
    field_simp [Units.ne_zero beta]
    ring
  rw [hunit] at hlinear
  have hlinearC := congrArg (Units.val : ℂˣ → ℂ) hlinear
  have harg : (c : F) * x / ((Gamma : Fˣ) : F) =
      ((beta' : F) - (beta : F)) / ((Gamma : Fˣ) : F) := by
    have hcBeta : (c : F) = (beta : F) := rfl
    rw [hcBeta]
    dsimp only [x]
    field_simp [Units.ne_zero beta, AdmissibleGamma.coe_ne_zero Gamma]
  rw [harg] at hlinearC
  have hadd := ContinuousAddChar.map_add_eq_mul psi.character
    ((beta : F) / ((Gamma : Fˣ) : F))
    (((beta' : F) - (beta : F)) / ((Gamma : Fˣ) : F))
  have hsum : (beta : F) / ((Gamma : Fˣ) : F) +
      ((beta' : F) - (beta : F)) / ((Gamma : Fˣ) : F) =
      (beta' : F) / ((Gamma : Fˣ) : F) := by ring
  rw [hsum] at hadd
  have haddC := congrArg (Units.val : ℂˣ → ℂ) hadd
  simp only [Units.val_mul] at haddC
  have hchi : (chi.character beta' : ℂ) =
      (chi.character beta : ℂ) *
        (psi.character (((beta' : F) - (beta : F)) /
          ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmultip := map_mul chi.character beta (beta' / beta)
    have hbetamul : beta * (beta' / beta) = beta' := by simp
    rw [hbetamul] at hmultip
    have hmultipC := congrArg (Units.val : ℂˣ → ℂ) hmultip
    simp only [Units.val_mul] at hmultipC
    rw [hlinearC] at hmultipC
    exact hmultipC
  rw [lamprechtElementaryFactor, lamprechtElementaryFactor, haddC, hchi]
  field_simp [ContinuousAddChar.apply_ne_zero psi.character,
    ContinuousQuasiChar.apply_ne_zero chi.character]

/-! ## Odd representative transport -/

/-- If two field elements represent the same odd stationary quotient class,
their Hasse functions differ by translation.  The elementary factor changes
by the value at the same translation parameter, in the orientation required
for cancellation with the translated Hasse-sum phase. -/
theorem lamprechtOdd_representative_transport
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c c' : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (hc' : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    ∃ a : ResidueField F,
      lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c' hc' =
          (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).translate a ∧
        lamprechtElementaryFactor F chi psi Gamma
            (lamprechtStationaryRepresentativeUnit F chi psi
              (lamprechtFormula_stationaryDepth F chi d 1
                (by omega) hm hlarge) Gamma c' hc') =
          lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc a *
            lamprechtElementaryFactor F chi psi Gamma
              (lamprechtStationaryRepresentativeUnit F chi psi
                (lamprechtFormula_stationaryDepth F chi d 1
                  (by omega) hm hlarge) Gamma c hc) := by
  let hr := lamprechtFormula_stationaryDepth F chi d 1
    (by omega) hm hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  let beta' := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c' hc'
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  have hclasses : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c' :=
    hc.trans hc'.symm
  have hcong := (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
    (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ))).1 hclasses
  have hdepth : (chi.conductor : ℤ) - (d + 1 : ℕ) = (d : ℤ) := by omega
  have hcong' : CongruentAtDepth ((chi.conductor : ℤ) - (d + 1 : ℕ))
      (c : F) (c' : F) := by
    simpa using hcong
  rw [hdepth] at hcong'
  have hdiff : (beta' : F) - (beta : F) ∈ lattice F (d : ℤ) := by
    exact (congruentAtDepth_iff_sub_mem_lattice F (d : ℤ)
      (beta' : F) (beta : F)).1 hcong'.symm
  let aField : F := ((beta' : F) - (beta : F)) / ((beta : F) * (delta : F))
  have hdenom : ord F ((beta : F) * (delta : F)) = (d : ℤ) := by
    rw [ord_mul, hbeta, hdelta]
    simp
  have haField : aField ∈ lattice F 0 := by
    apply (div_mem_lattice_iff F ((beta : F) * (delta : F))
      ((beta' : F) - (beta : F)) (d : ℤ) 0 hdenom).2
    simpa using hdiff
  let a : ResidueField F := reduce F aField haField
  refine ⟨a, ?_, ?_⟩
  · apply HasseFunction.ext
    intro x
    let tx : F := teichmuller F x
    have htx : tx ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 (teichmuller F x).property
    have hatx : aField * tx ∈ lattice F 0 := by
      simpa using mul_mem_lattice F haField htx
    have hreduce : reduce F (aField * tx) hatx = a * x := by
      let afint : ringOfIntegers F :=
        ⟨aField, (mem_lattice_zero_iff F).1 haField⟩
      let txint : ringOfIntegers F :=
        ⟨tx, (mem_lattice_zero_iff F).1 htx⟩
      change residueMap F (afint * txint) =
        residueMap F afint * x
      rw [map_mul]
      congr 1
      exact residueMap_teichmuller F x
    have hpsi0 := lamprechtResidualAddChar_integral_lift
      F chi psi d hm hlarge Gamma delta hdelta c hc
      (aField * tx) hatx
    rw [hreduce] at hpsi0
    change lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c'
        tx htx =
      lamprechtHasseValue F chi psi d hm hlarge Gamma delta hdelta c
          tx htx *
        lamprechtResidualAddChar F chi psi d hm hlarge Gamma delta hdelta
          (a * x)
    rw [hpsi0]
    have hadd := ContinuousAddChar.map_add_eq_mul psi.character
      ((c : F) * (delta : F) * tx / ((Gamma : Fˣ) : F))
      ((c : F) * (delta : F) ^ 2 * (aField * tx) /
        ((Gamma : Fˣ) : F))
    have haddC := congrArg (Units.val : ℂˣ → ℂ) hadd
    simp only [Units.val_mul] at haddC
    have harg :
        (c : F) * (delta : F) * tx / ((Gamma : Fˣ) : F) +
            (c : F) * (delta : F) ^ 2 * (aField * tx) /
              ((Gamma : Fˣ) : F) =
          (c' : F) * (delta : F) * tx / ((Gamma : Fˣ) : F) := by
      have hcBeta : (c : F) = (beta : F) := rfl
      have hc'Beta : (c' : F) = (beta' : F) := rfl
      rw [hcBeta, hc'Beta]
      dsimp only [aField]
      field_simp [Units.ne_zero beta, Units.ne_zero delta,
        AdmissibleGamma.coe_ne_zero Gamma]
      ring
    rw [harg] at haddC
    rw [lamprechtHasseValue, lamprechtHasseValue, haddC]
    ring
  · have hphi := lamprechtHasseFunction_integral_lift
      F chi psi d hm hlarge Gamma delta hdelta c hc aField haField
    change lamprechtElementaryFactor F chi psi Gamma beta' =
      lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc a *
        lamprechtElementaryFactor F chi psi Gamma beta
    rw [hphi]
    have hunit :
        (lamprechtHasseUnit F chi d hm hlarge delta hdelta aField haField : Fˣ) =
          beta' / beta := by
      apply Units.ext
      rw [lamprechtHasseUnit_coe, Units.val_div_eq_div_val]
      dsimp only [aField]
      field_simp [Units.ne_zero beta, Units.ne_zero delta]
      ring
    have harg : (c : F) * (delta : F) * aField /
        ((Gamma : Fˣ) : F) =
      ((beta' : F) - (beta : F)) / ((Gamma : Fˣ) : F) := by
      have hcBeta : (c : F) = (beta : F) := rfl
      rw [hcBeta]
      dsimp only [aField]
      field_simp [Units.ne_zero beta, Units.ne_zero delta,
        AdmissibleGamma.coe_ne_zero Gamma]
    have hadd := ContinuousAddChar.map_add_eq_mul psi.character
      ((beta : F) / ((Gamma : Fˣ) : F))
      (((beta' : F) - (beta : F)) / ((Gamma : Fˣ) : F))
    have hsum : (beta : F) / ((Gamma : Fˣ) : F) +
        ((beta' : F) - (beta : F)) / ((Gamma : Fˣ) : F) =
        (beta' : F) / ((Gamma : Fˣ) : F) := by ring
    rw [hsum] at hadd
    have haddC := congrArg (Units.val : ℂˣ → ℂ) hadd
    simp only [Units.val_mul] at haddC
    have hchi := map_mul chi.character beta (beta' / beta)
    have hbetamul : beta * (beta' / beta) = beta' := by simp
    rw [hbetamul] at hchi
    have hchiC := congrArg (Units.val : ℂˣ → ℂ) hchi
    simp only [Units.val_mul] at hchiC
    rw [lamprechtElementaryFactor, lamprechtHasseValue, hunit, harg,
      lamprechtElementaryFactor, haddC, hchiC]
    field_simp [ContinuousAddChar.apply_ne_zero psi.character,
      ContinuousQuasiChar.apply_ne_zero chi.character]

/-- The odd Hasse sum is nonzero; this is the denominator fact needed to
take its phase in Lamprecht's formula. -/
theorem lamprechtOdd_hasseSum_ne_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    letI := residueFieldFintype F
    (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sum ≠ 0 := by
  letI := residueFieldFintype F
  exact HasseFunction.sum_ne_zero
    (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc)
    (lamprechtResidualAddChar_ne_one F chi psi d hm hlarge Gamma delta hdelta c hc)

/-- The exact magnitude of the odd residual Hasse sum. -/
theorem lamprechtOdd_hasseSum_norm
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    letI := residueFieldFintype F
    ‖(lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sum‖ =
      Real.sqrt (residueCard F : ℝ) := by
  letI := residueFieldFintype F
  exact HasseFunction.sum_norm
    (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc)
    (lamprechtResidualAddChar_ne_one F chi psi d hm hlarge Gamma delta hdelta c hc)

/-- Translation by a residue class transports the odd Hasse-sum phase by the
inverse Hasse value at precisely that class. -/
theorem lamprechtOdd_hasseSumPhase_translate
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (a : ResidueField F) :
    letI := residueFieldFintype F
    ((lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).translate a).sumPhase =
      (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc a)⁻¹ *
        (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sumPhase := by
  letI := residueFieldFintype F
  exact HasseFunction.sumPhase_translate
    (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc)
    (lamprechtResidualAddChar_ne_one F chi psi d hm hlarge Gamma delta hdelta c hc) a

/-- The complete odd stationary expression is independent of the chosen
representative.  Both the elementary factor and the Hasse-sum phase are
transported; neither is discarded separately. -/
theorem lamprechtOdd_complete_representative_independent
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c c' : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property)
    (hc' : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c' =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    letI := residueFieldFintype F
    lamprechtElementaryFactor F chi psi Gamma
          (lamprechtStationaryRepresentativeUnit F chi psi
            (lamprechtFormula_stationaryDepth F chi d 1
              (by omega) hm hlarge) Gamma c hc) *
        (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sumPhase =
      lamprechtElementaryFactor F chi psi Gamma
          (lamprechtStationaryRepresentativeUnit F chi psi
            (lamprechtFormula_stationaryDepth F chi d 1
              (by omega) hm hlarge) Gamma c' hc') *
        (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c' hc').sumPhase := by
  letI := residueFieldFintype F
  obtain ⟨a, hphi, hfactor⟩ := lamprechtOdd_representative_transport
    F chi psi d hm hlarge Gamma delta hdelta c c' hc hc'
  have hpsi0 := lamprechtResidualAddChar_ne_one
    F chi psi d hm hlarge Gamma delta hdelta c hc
  rw [hphi, HasseFunction.sumPhase_translate _ hpsi0 a, hfactor]
  field_simp [HasseFunction.ne_zero]

/-! ## Stationary localization and exact raw Gauss sums -/

private def lamprechtFormulaUnitFiltrationToZero (r : ℕ) :
    unitFiltration F r →* unitFiltration F 0 where
  toFun u := ⟨(u : Fˣ), unitFiltration_antitone F (Nat.zero_le r) u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def lamprechtFormulaDeepClassInFull
    {q r : ℕ} (hrq : r ≤ q) :
    UnitFiltrationQuotient F r q hrq →*
      UnitFiltrationQuotient F 0 q (Nat.zero_le q) :=
  QuotientGroup.lift (unitFiltrationInside F hrq)
    ((unitFiltrationQuotientMk F (Nat.zero_le q)).comp
      (lamprechtFormulaUnitFiltrationToZero F r)) (by
        intro u hu
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
          unitFiltrationQuotientMk_eq_one_iff]
        exact (mem_unitFiltrationInside F hrq u).1 hu)

@[simp] theorem lamprechtFormulaDeepClassInFull_mk
    {q r : ℕ} (hrq : r ≤ q) (u : unitFiltration F r) :
    lamprechtFormulaDeepClassInFull F hrq
        (unitFiltrationQuotientMk F hrq u) =
      unitFiltrationQuotientMk F (Nat.zero_le q)
        (lamprechtFormulaUnitFiltrationToZero F r u) :=
  rfl

private noncomputable def lamprechtFormulaCoefficientClass
    {q r : ℕ} (hrq : r ≤ q)
    (c : lattice F ((q : ℤ) - (q : ℤ))) :
    UnitFiltrationQuotient F 0 q (Nat.zero_le q) →
      LamprechtCoefficientQuotient F (q : ℤ) (q : ℤ) (r : ℤ)
        (by exact_mod_cast hrq) :=
  unitFiltrationQuotientLift F (Nat.zero_le q)
    (fun u ↦ latticeQuotientMk F
      (sub_le_sub_left (by exact_mod_cast hrq) (q : ℤ))
      ⟨((u : Fˣ) : F) - (c : F), by
        have hu0 : ((u : Fˣ) : F) ∈ lattice F 0 := by
          rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
          simp
        have huq : ((u : Fˣ) : F) ∈ lattice F ((q : ℤ) - (q : ℤ)) := by
          simpa using hu0
        exact sub_mem huq c.property⟩)
    (by
      intro u v huv
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
        (sub_le_sub_left (by exact_mod_cast hrq) (q : ℤ))).2
      apply (congruentAtDepth_iff_sub_mem_lattice F
        ((q : ℤ) - (r : ℤ))
        (((u : Fˣ) : F) - (c : F))
        (((v : Fˣ) : F) - (c : F))).2
      have huvMem := (congruentAtDepth_iff_sub_mem_lattice F (q : ℤ)
        ((u : Fˣ) : F) ((v : Fˣ) : F)).1 huv
      apply lattice_antitone F (by omega : (q : ℤ) - (r : ℤ) ≤ q)
      simpa only [sub_sub_sub_cancel_right] using huvMem)

@[simp] theorem lamprechtFormulaCoefficientClass_mk
    {q r : ℕ} (hrq : r ≤ q)
    (c : lattice F ((q : ℤ) - (q : ℤ)))
    (u : unitFiltration F 0) :
    lamprechtFormulaCoefficientClass F hrq c
        (unitFiltrationQuotientMk F (Nat.zero_le q) u) =
      latticeQuotientMk F
        (sub_le_sub_left (by exact_mod_cast hrq) (q : ℤ))
        ⟨((u : Fˣ) : F) - (c : F), by
          have hu0 : ((u : Fˣ) : F) ∈ lattice F 0 := by
            rw [mem_lattice, (mem_unitFiltration_zero F (u : Fˣ)).1 u.property]
            simp
          have huq : ((u : Fˣ) : F) ∈ lattice F ((q : ℤ) - (q : ℤ)) := by
            simpa using hu0
          exact sub_mem huq c.property⟩ :=
  rfl

private theorem lamprechtFormulaFiniteGaussSummand_stationaryOrbit
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)
    (a : UnitFiltrationQuotient F r chi.conductor hr.le_conductor)
    (u : UnitFiltrationQuotient F 0 chi.conductor
      (Nat.zero_le chi.conductor)) :
    finiteGaussSummand chi psi Gamma
        (lamprechtFormulaDeepClassInFull F hr.le_conductor a * u) =
      (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
        (lamprechtFormulaCoefficientClass F hr.le_conductor c u))
          ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
            hr.le_conductor hr.half_le a).toAdd) *
        finiteGaussSummand chi psi Gamma u := by
  obtain ⟨a, rfl⟩ := unitFiltrationQuotientMk_surjective F hr.le_conductor a
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le chi.conductor) u
  rw [lamprechtFormulaDeepClassInFull_mk, ← unitFiltrationQuotientMk_mul,
    finiteGaussSummand_mk, finiteGaussSummand_mk]
  change finiteGaussSummandRepresentative chi psi Gamma
      (lamprechtFormulaUnitFiltrationToZero F r a * u) =
    (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (lamprechtFormulaCoefficientClass F hr.le_conductor c
        (unitFiltrationQuotientMk F (Nat.zero_le chi.conductor) u)))
        (latticeQuotientMk F hr.int_le_conductor
          (positiveUnitDisplacement F hr.pos a)) *
      finiteGaussSummandRepresentative chi psi Gamma u
  rw [lamprechtFormulaCoefficientClass_mk,
    lamprechtPairingLeft_apply, lamprechtPairing_mk_mk]
  let x := positiveUnitDisplacement F hr.pos a
  have hchi := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ) hr Gamma Gamma.property c hc x
  have hunit : (positiveUnitOfLattice F hr.pos x : Fˣ) = (a : Fˣ) := by
    apply Units.ext
    simp [x]
  rw [hunit] at hchi
  have hchiC := congrArg (Units.val : Units ℂ → ℂ) hchi
  have hchiC' : (chi.character (a : Fˣ) : ℂ) =
      (psi.character ((c : F) * (((a : Fˣ) : F) - 1) /
        ((Gamma : Fˣ) : F)) : ℂ) := by
    simpa only [x, coe_positiveUnitDisplacement] using hchiC
  have hchiMul : (chi.character ((a : Fˣ) * (u : Fˣ)) : ℂ) =
      (chi.character (a : Fˣ) : ℂ) *
        (chi.character (u : Fˣ) : ℂ) :=
    congrArg Units.val (map_mul chi.character (a : Fˣ) (u : Fˣ))
  have harg :
      (((a : Fˣ) : F) * ((u : Fˣ) : F)) / ((Gamma : Fˣ) : F) =
        (((u : Fˣ) : F) - (c : F)) *
              (((a : Fˣ) : F) - 1) / ((Gamma : Fˣ) : F) +
          (c : F) * (((a : Fˣ) : F) - 1) / ((Gamma : Fˣ) : F) +
          ((u : Fˣ) : F) / ((Gamma : Fˣ) : F) := by
    field_simp [AdmissibleGamma.coe_ne_zero Gamma]
    ring
  rw [finiteGaussSummandRepresentative, finiteGaussSummandRepresentative]
  change (psi.character
        ((((a : Fˣ) : F) * ((u : Fˣ) : F)) / ((Gamma : Fˣ) : F)) : ℂ) *
      (chi.character ((a : Fˣ) * (u : Fˣ)) : ℂ)⁻¹ =
    (psi.character ((((u : Fˣ) : F) - (c : F)) *
        (((a : Fˣ) : F) - 1) / ((Gamma : Fˣ) : F)) : ℂ) *
      ((psi.character (((u : Fˣ) : F) / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character (u : Fˣ) : ℂ)⁻¹)
  rw [hchiMul, hchiC']
  rw [harg, ContinuousAddChar.map_add_eq_mul,
    ContinuousAddChar.map_add_eq_mul]
  have hc0 : (psi.character ((c : F) * (((a : Fˣ) : F) - 1) /
      ((Gamma : Fˣ) : F)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  field_simp
  push_cast
  ring

private theorem lamprechtFormulaOrbitSum_eq_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (u : UnitFiltrationQuotient F 0 chi.conductor
      (Nat.zero_le chi.conductor))
    (hu : lamprechtFormulaCoefficientClass F hr.le_conductor c u ≠ 0) :
    letI := unitFiltrationQuotientFintype F hr.le_conductor
    ∑ a : UnitFiltrationQuotient F r chi.conductor hr.le_conductor,
      (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
        (lamprechtFormulaCoefficientClass F hr.le_conductor c u))
          ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
            hr.le_conductor hr.half_le a).toAdd) = 0 := by
  letI := unitFiltrationQuotientFintype F hr.le_conductor
  letI := latticeQuotientFintype F hr.int_le_conductor
  let eta := lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
    (lamprechtFormulaCoefficientClass F hr.le_conductor c u)
  have heta : eta ≠ 1 := by
    intro htriv
    apply hu
    apply lamprechtPairingLeft_injective F psi hr.int_le_conductor
      Gamma Gamma.property
    change eta = lamprechtPairingLeft F psi hr.int_le_conductor
      Gamma Gamma.property 0
    rw [map_zero]
    calc
      eta = 1 := htriv
      _ = 0 := by
        ext x
        simp
  change ∑ a : UnitFiltrationQuotient F r chi.conductor hr.le_conductor,
    eta ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
      hr.le_conductor hr.half_le a).toAdd) = 0
  calc
    _ = ∑ x : Multiplicative
        (LamprechtVariableQuotient F (chi.conductor : ℤ) (r : ℤ)
          hr.int_le_conductor), eta x.toAdd :=
      (positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
        hr.le_conductor hr.half_le).toEquiv.sum_comp (fun x ↦ eta x.toAdd)
    _ = ∑ x : LamprechtVariableQuotient F (chi.conductor : ℤ) (r : ℤ)
        hr.int_le_conductor, eta x :=
      Multiplicative.toAdd.sum_comp eta
    _ = 0 := AddChar.sum_eq_zero_of_ne_one heta

private theorem lamprechtFormulaFiniteGaussSum_localized
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {r : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor r)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property) :
    letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
    letI : DecidableEq
        (LamprechtCoefficientQuotient F (chi.conductor : ℤ)
          (chi.conductor : ℤ) (r : ℤ) hr.int_le_conductor) :=
      Classical.decEq _
    finiteGaussSum chi psi Gamma =
      ∑ u : UnitFiltrationQuotient F 0 chi.conductor
          (Nat.zero_le chi.conductor),
        if lamprechtFormulaCoefficientClass F hr.le_conductor c u = 0 then
          finiteGaussSummand chi psi Gamma u else 0 := by
  classical
  let A := UnitFiltrationQuotient F r chi.conductor hr.le_conductor
  let U := UnitFiltrationQuotient F 0 chi.conductor (Nat.zero_le chi.conductor)
  let f := finiteGaussSummand chi psi Gamma
  let coeff := lamprechtFormulaCoefficientClass F hr.le_conductor c
  let eta := fun (u : U) (a : A) ↦
    (lamprechtPairingLeft F psi hr.int_le_conductor Gamma Gamma.property
      (coeff u))
        ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
          hr.le_conductor hr.half_le a).toAdd)
  letI := unitFiltrationQuotientFintype F hr.le_conductor
  letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
  have havg :
      (Fintype.card A : ℂ) * finiteGaussSum chi psi Gamma =
        (Fintype.card A : ℂ) *
          ∑ u : U, if coeff u = 0 then f u else 0 := by
    calc
      _ = ∑ a : A, ∑ u : U, f u := by simp [finiteGaussSum, U, A, f]
      _ = ∑ a : A, ∑ u : U,
          f (lamprechtFormulaDeepClassInFull F hr.le_conductor a * u) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact (sum_unitFiltrationQuotient_mul_left F
          (Nat.zero_le chi.conductor)
          (lamprechtFormulaDeepClassInFull F hr.le_conductor a) f).symm
      _ = ∑ a : A, ∑ u : U, eta u a * f u := by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro u _hu
        exact lamprechtFormulaFiniteGaussSummand_stationaryOrbit
          F chi psi hr Gamma c hc a u
      _ = ∑ u : U, f u * ∑ a : A, eta u a := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _hu
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = ∑ u : U,
          if coeff u = 0 then (Fintype.card A : ℂ) * f u else 0 := by
        apply Finset.sum_congr rfl
        intro u _hu
        by_cases hu : coeff u = 0
        · rw [if_pos hu]
          have heta : ∀ a : A, eta u a = 1 := by
            intro a
            change (lamprechtPairingLeft F psi hr.int_le_conductor
              Gamma Gamma.property (coeff u))
                ((positiveUnitFiltrationQuotientMulEquivLattice F hr.pos
                  hr.le_conductor hr.half_le a).toAdd) = 1
            rw [hu, map_zero]
            simp
          rw [show (∑ a : A, eta u a) = (Fintype.card A : ℂ) by
            simp_rw [heta]
            simp]
          ring
        · have hs := lamprechtFormulaOrbitSum_eq_zero F chi psi hr Gamma c u hu
          change (∑ a : A, eta u a) = 0 at hs
          rw [hs, mul_zero, if_neg hu]
      _ = (Fintype.card A : ℂ) *
          ∑ u : U, if coeff u = 0 then f u else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _hu
        by_cases hu : coeff u = 0
        · rw [if_pos hu, if_pos hu]
        · rw [if_neg hu, if_neg hu, mul_zero]
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_left_cancel₀ hcard havg)

private def lamprechtFormulaUnitFiltrationZeroOfOrdZero (beta : Fˣ)
    (hbeta : ord F (beta : F) = 0) : unitFiltration F 0 :=
  ⟨beta, (mem_unitFiltration_zero F beta).2 hbeta⟩

@[simp] theorem lamprechtFormulaUnitFiltrationZeroOfOrdZero_coe (beta : Fˣ)
    (hbeta : ord F (beta : F) = 0) :
    (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta : Fˣ) = beta :=
  rfl

private theorem lamprechtFormulaCoefficientClass_eq_zero_iff_projection
    {q r d : ℕ} (hrq : r ≤ q) (hdq : d ≤ q)
    (hdepth : (q : ℤ) - (r : ℤ) = (d : ℤ))
    (c : lattice F ((q : ℤ) - (q : ℤ)))
    (beta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hcbeta : (c : F) = (beta : F))
    (u : UnitFiltrationQuotient F 0 q (Nat.zero_le q)) :
    lamprechtFormulaCoefficientClass F hrq c u = 0 ↔
      unitFiltrationQuotientProjection F (Nat.zero_le d) hdq u =
        unitFiltrationQuotientMk F (Nat.zero_le d)
          (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta) := by
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F (Nat.zero_le q) u
  rw [lamprechtFormulaCoefficientClass_mk, latticeQuotientMk_eq_zero_iff,
    unitFiltrationQuotientProjection_mk,
    unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth,
    congruentAtDepth_iff_sub_mem_lattice]
  simpa only [hdepth, lamprechtFormulaUnitFiltrationZeroOfOrdZero_coe, hcbeta]

private theorem lamprechtFormulaFiniteGaussSummand_even_of_coefficient_eq_zero
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    {d : ℕ} (hr : IsLamprechtStationaryDepth chi.conductor d)
    (heven : chi.conductor = 2 * d)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)
    (beta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hcbeta : (c : F) = (beta : F))
    (u : UnitFiltrationQuotient F 0 chi.conductor
      (Nat.zero_le chi.conductor))
    (hu : lamprechtFormulaCoefficientClass F hr.le_conductor c u = 0) :
    finiteGaussSummand chi psi Gamma u =
      (psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character beta : ℂ)⁻¹ := by
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le chi.conductor) u
  rw [lamprechtFormulaCoefficientClass_mk, latticeQuotientMk_eq_zero_iff] at hu
  have hdepth : (chi.conductor : ℤ) - (d : ℤ) = (d : ℤ) := by
    omega
  rw [hdepth] at hu
  have hdiff : ((u : Fˣ) : F) - (beta : F) ∈ lattice F (d : ℤ) := by
    simpa only [hcbeta] using hu
  have hzmem : ((u : Fˣ) : F) / (beta : F) - 1 ∈ lattice F (d : ℤ) := by
    have hdiv : (((u : Fˣ) : F) - (beta : F)) / (beta : F) ∈
        lattice F (d : ℤ) :=
      (div_mem_lattice_iff F (beta : F)
        (((u : Fˣ) : F) - (beta : F)) 0 (d : ℤ) hbeta).2 (by
          simpa using hdiff)
    convert hdiv using 1
    field_simp [Units.ne_zero beta]
  let z : lattice F (d : ℤ) :=
    ⟨((u : Fˣ) : F) / (beta : F) - 1, hzmem⟩
  have hunit : (positiveUnitOfLattice F hr.pos z : Fˣ) =
      (u : Fˣ) / beta := by
    apply Units.ext
    rw [coe_positiveUnitOfLattice]
    push_cast
    dsimp only [z]
    change 1 + (((u : Fˣ) : F) / (beta : F) - 1) =
      ((u : Fˣ) : F) / (beta : F)
    ring
  have hlin := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ) hr Gamma Gamma.property c hc z
  rw [hunit] at hlin
  have hlinC := congrArg (Units.val : Units ℂ → ℂ) hlin
  have hchi : (chi.character (u : Fˣ) : ℂ) =
      (chi.character beta : ℂ) *
        (psi.character ((c : F) * (z : F) / ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := congrArg (Units.val : Units ℂ → ℂ)
      (map_div chi.character (u : Fˣ) beta)
    push_cast at hmap
    rw [hlinC] at hmap
    have hb0 : (chi.character beta : ℂ) ≠ 0 := ContinuousQuasiChar.apply_ne_zero _ _
    field_simp [hb0] at hmap ⊢
    exact hmap.symm
  have harg : ((u : Fˣ) : F) / ((Gamma : Fˣ) : F) =
      (c : F) / ((Gamma : Fˣ) : F) +
        (c : F) * (z : F) / ((Gamma : Fˣ) : F) := by
    dsimp only [z]
    rw [hcbeta]
    field_simp [Units.ne_zero beta, AdmissibleGamma.coe_ne_zero Gamma]
    ring
  rw [finiteGaussSummand_mk, finiteGaussSummandRepresentative, harg,
    ContinuousAddChar.map_add_eq_mul, hchi]
  have hp0 : (psi.character ((c : F) * (z : F) /
      ((Gamma : Fˣ) : F)) : ℂ) ≠ 0 := ContinuousAddChar.apply_ne_zero _ _
  field_simp [hp0]
  push_cast
  ring

private theorem lamprechtFormulaFiniteGaussSum_even_raw
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hr : IsLamprechtStationaryDepth chi.conductor d)
    (heven : chi.conductor = 2 * d)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)
    (beta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hcbeta : (c : F) = (beta : F)) :
    finiteGaussSum chi psi Gamma =
      (residueCard F : ℂ) ^ d *
        ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character beta : ℂ)⁻¹) := by
  classical
  let U := UnitFiltrationQuotient F 0 chi.conductor
    (Nat.zero_le chi.conductor)
  let coeff := lamprechtFormulaCoefficientClass F hr.le_conductor c
  let f := finiteGaussSummand chi psi Gamma
  let E : ℂ := (psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
    (chi.character beta : ℂ)⁻¹
  let beta0 := lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta
  let target := unitFiltrationQuotientMk F (Nat.zero_le d) beta0
  let p := unitFiltrationQuotientProjection F (Nat.zero_le d)
    (show d ≤ chi.conductor by omega)
  let S := {u : U // coeff u = 0}
  let T := {u : U // p u = target}
  letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
  have hdepth : (chi.conductor : ℤ) - (d : ℤ) = (d : ℤ) := by
    omega
  have hpred : ∀ u : U, coeff u = 0 ↔ p u = target := by
    intro u
    exact lamprechtFormulaCoefficientClass_eq_zero_iff_projection F hr.le_conductor
      (show d ≤ chi.conductor by omega) hdepth c beta hbeta hcbeta u
  let e : S ≃ T := Equiv.subtypeEquiv (Equiv.refl U) hpred
  have hcardS : Nat.card S = residueCard F ^ d := by
    calc
      Nat.card S = Nat.card T := Nat.card_congr e
      _ = residueCard F ^ (chi.conductor - d) := by
        change Nat.card {u : UnitFiltrationQuotient F 0 chi.conductor
            (Nat.zero_le chi.conductor) //
          unitFiltrationQuotientProjection F (Nat.zero_le d)
            (show d ≤ chi.conductor by omega) u =
            unitFiltrationQuotientMk F (Nat.zero_le d) beta0} = _
        simpa [Nat.ne_of_gt hr.pos] using
          (unitFiltrationQuotientProjection_fiber_card F
            (Nat.zero_le d) (show d ≤ chi.conductor by omega)
            (unitFiltrationQuotientMk F (Nat.zero_le d) beta0))
      _ = residueCard F ^ d := by congr 1 <;> omega
  have hfiltercard : (Finset.univ.filter (fun u : U ↦ coeff u = 0)).card =
      residueCard F ^ d := by
    calc
      (Finset.univ.filter (fun u : U ↦ coeff u = 0)).card =
          Fintype.card S :=
        (Fintype.card_of_subtype
          (Finset.univ.filter (fun u : U ↦ coeff u = 0)) (by simp)).symm
      _ = Nat.card S := Nat.card_eq_fintype_card.symm
      _ = residueCard F ^ d := hcardS
  rw [lamprechtFormulaFiniteGaussSum_localized F chi psi hr Gamma c hc]
  change (∑ u : U, if coeff u = 0 then f u else 0) = _
  calc
    _ = (∑ u ∈ Finset.univ.filter (fun u : U ↦ coeff u = 0), f u) := by
      simpa using (Finset.sum_filter (fun u : U ↦ coeff u = 0) f).symm
    _ = (∑ _u ∈ Finset.univ.filter (fun u : U ↦ coeff u = 0), E) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hcoeff := (Finset.mem_filter.1 hu).2
      exact lamprechtFormulaFiniteGaussSummand_even_of_coefficient_eq_zero
        F chi psi hr heven Gamma c hc beta hbeta hcbeta u hcoeff
    _ = ((Finset.univ.filter (fun u : U ↦ coeff u = 0)).card : ℂ) * E := by
      simp
    _ = (residueCard F : ℂ) ^ d * E := by
      rw [hfiltercard, Nat.cast_pow]
    _ = _ := rfl

private def lamprechtFormulaOddDisplacement (d : ℕ) (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) : lattice F (d : ℤ) :=
  ⟨(delta : F) * (teichmuller F x : F), by
    have hd : (delta : F) ∈ lattice F (d : ℤ) := by
      rw [mem_lattice, hdelta]
    have hx : (teichmuller F x : F) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 (teichmuller F x).property
    simpa using mul_mem_lattice F hd hx⟩

@[simp] theorem lamprechtFormulaOddDisplacement_coe (d : ℕ) (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) :
    (lamprechtFormulaOddDisplacement F d delta hdelta x : F) =
      (delta : F) * (teichmuller F x : F) :=
  rfl

private def lamprechtFormulaOddBaseUnitZero (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) : unitFiltration F 0 :=
  lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta *
    lamprechtFormulaUnitFiltrationToZero F d
      (positiveUnitOfLattice F hd (lamprechtFormulaOddDisplacement F d delta hdelta x))

@[simp] theorem lamprechtFormulaOddBaseUnitZero_coe (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) :
    ((lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x : Fˣ) : F) =
      (beta : F) * (1 + (delta : F) * (teichmuller F x : F)) := by
  change (((beta * positiveUnitOfLattice F hd
    (lamprechtFormulaOddDisplacement F d delta hdelta x) : Fˣ) : F)) = _
  push_cast
  rw [coe_positiveUnitOfLattice, lamprechtFormulaOddDisplacement_coe]

private noncomputable def lamprechtFormulaOddCoarseClass (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) :
    UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _) :=
  unitFiltrationQuotientMk F (Nat.zero_le (d + 1))
    (lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x)

private theorem lamprechtFormulaOddCoarseClass_projection
    (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) :
    unitFiltrationQuotientProjection F (Nat.zero_le d) (by omega : d ≤ d + 1)
        (lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x) =
      unitFiltrationQuotientMk F (Nat.zero_le d)
        (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta) := by
  rw [lamprechtFormulaOddCoarseClass, unitFiltrationQuotientProjection_mk]
  apply (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
    (Nat.zero_le d) _ _).2
  apply (congruentAtDepth_iff_sub_mem_lattice F (d : ℤ) _ _).2
  rw [lamprechtFormulaOddBaseUnitZero_coe]
  have hdeltamem : (delta : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdelta]
  have htxmem : (teichmuller F x : F) ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  have hprod : (beta : F) * ((delta : F) * (teichmuller F x : F)) ∈
      lattice F (d : ℤ) := by
    have hbetaMem : (beta : F) ∈ lattice F 0 := by
      rw [mem_lattice, hbeta]
      simp
    have := mul_mem_lattice F hbetaMem (mul_mem_lattice F hdeltamem htxmem)
    simpa using this
  convert hprod using 1
  change (beta : F) * (1 + (delta : F) * (teichmuller F x : F)) -
    (beta : F) = (beta : F) * ((delta : F) * (teichmuller F x : F))
  ring

private theorem lamprechtFormulaOddCoarseClass_injective
    (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    Function.Injective (lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta) := by
  intro x y hxy
  rw [lamprechtFormulaOddCoarseClass, lamprechtFormulaOddCoarseClass,
    unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth,
    congruentAtDepth_iff_sub_mem_lattice] at hxy
  rw [lamprechtFormulaOddBaseUnitZero_coe, lamprechtFormulaOddBaseUnitZero_coe] at hxy
  have hscaleord : ord F ((beta : F) * (delta : F)) =
      ((d : ℤ) : WithTop ℤ) := by rw [ord_mul, hbeta, hdelta]; simp
  have hscaled : ((beta : F) * (1 + (delta : F) * (teichmuller F x : F)) -
        (beta : F) * (1 + (delta : F) * (teichmuller F y : F))) /
        ((beta : F) * (delta : F)) ∈ lattice F 1 :=
    (div_mem_lattice_iff F ((beta : F) * (delta : F)) _ (d : ℤ) 1
      hscaleord).2 (by simpa using hxy)
  have hdiff : (teichmuller F x : F) - (teichmuller F y : F) ∈
      lattice F 1 := by
    convert hscaled using 1
    field_simp [Units.ne_zero beta, Units.ne_zero delta]
    ring
  have hreduction : residueMap F (teichmuller F x) =
      residueMap F (teichmuller F y) :=
    (residueMap_eq_residueMap_iff F (teichmuller F x)
      (teichmuller F y)).2 hdiff
  simpa using hreduction

private noncomputable def lamprechtFormulaOddCoarseFiberEquiv
    (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ)) :
    ResidueField F ≃
      {u : UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _) //
        unitFiltrationQuotientProjection F (Nat.zero_le d)
            (by omega : d ≤ d + 1) u =
          unitFiltrationQuotientMk F (Nat.zero_le d)
            (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta)} := by
  classical
  letI := residueFieldFintype F
  letI := unitFiltrationQuotientFintype F (Nat.zero_le (d + 1))
  let T := {u : UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _) //
        unitFiltrationQuotientProjection F (Nat.zero_le d)
            (by omega : d ≤ d + 1) u =
          unitFiltrationQuotientMk F (Nat.zero_le d)
            (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta)}
  let j : ResidueField F → T := fun x ↦
    ⟨lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x,
      lamprechtFormulaOddCoarseClass_projection F d hd beta delta hbeta hdelta x⟩
  apply Equiv.ofBijective j
  apply (Fintype.bijective_iff_injective_and_card j).2
  constructor
  · intro x y hxy
    apply lamprechtFormulaOddCoarseClass_injective F d hd beta delta hbeta hdelta
    exact congrArg Subtype.val hxy
  · change residueCard F = Fintype.card
      {u : UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _) //
        unitFiltrationQuotientProjection F (Nat.zero_le d)
            (by omega : d ≤ d + 1) u =
          unitFiltrationQuotientMk F (Nat.zero_le d)
            (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta)}
    rw [← Nat.card_eq_fintype_card]
    simpa [Nat.ne_of_gt hd] using
      (unitFiltrationQuotientProjection_fiber_card F
        (Nat.zero_le d) (by omega : d ≤ d + 1)
        (unitFiltrationQuotientMk F (Nat.zero_le d)
          (lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta))).symm

@[simp] theorem lamprechtFormulaOddCoarseFiberEquiv_apply
    (d : ℕ) (hd : 0 < d)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (x : ResidueField F) :
    (lamprechtFormulaOddCoarseFiberEquiv F d hd beta delta hbeta hdelta x).1 =
      lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x :=
  rfl

private theorem lamprechtFormulaFiniteGaussSummand_odd_fine_fiber_constant
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hd : 0 < d)
    (hr : IsLamprechtStationaryDepth chi.conductor (d + 1))
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (hcbeta : (c : F) = (beta : F))
    (x : ResidueField F)
    (u : UnitFiltrationQuotient F 0 chi.conductor
      (Nat.zero_le chi.conductor))
    (hu : unitFiltrationQuotientProjection F (Nat.zero_le (d + 1))
        (show d + 1 ≤ chi.conductor by omega) u =
      lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x) :
    finiteGaussSummand chi psi Gamma u =
      finiteGaussSummandRepresentative chi psi Gamma
        (lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x) := by
  let b0 := lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x
  let b : Fˣ := (b0 : Fˣ)
  have hbOrd : ord F (b : F) = 0 :=
    (mem_unitFiltration_zero F b).1 b0.property
  obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective F
    (Nat.zero_le chi.conductor) u
  rw [unitFiltrationQuotientProjection_mk, lamprechtFormulaOddCoarseClass,
    unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth,
    congruentAtDepth_iff_sub_mem_lattice] at hu
  have hdiff : ((u : Fˣ) : F) - (b : F) ∈ lattice F ((d + 1 : ℕ) : ℤ) := by
    exact hu
  have hwmem : ((u : Fˣ) : F) / (b : F) - 1 ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
    have hdiv : (((u : Fˣ) : F) - (b : F)) / (b : F) ∈
        lattice F ((d + 1 : ℕ) : ℤ) :=
      (div_mem_lattice_iff F (b : F) _ 0 ((d + 1 : ℕ) : ℤ)
        hbOrd).2 (by simpa using hdiff)
    convert hdiv using 1
    field_simp [Units.ne_zero b]
  let w : lattice F ((d + 1 : ℕ) : ℤ) :=
    ⟨((u : Fˣ) : F) / (b : F) - 1, hwmem⟩
  have hunit : (positiveUnitOfLattice F hr.pos w : Fˣ) =
      (u : Fˣ) / b := by
    apply Units.ext
    rw [coe_positiveUnitOfLattice]
    push_cast
    dsimp only [w]
    ring
  have hlin := stationaryNumeratorClass_linearization
    F chi psi (chi.conductor : ℤ) hr Gamma Gamma.property c hc w
  rw [hunit] at hlin
  have hlinC := congrArg (Units.val : Units ℂ → ℂ) hlin
  have hchi : (chi.character (u : Fˣ) : ℂ) =
      (chi.character b : ℂ) *
        (psi.character ((c : F) * (w : F) / ((Gamma : Fˣ) : F)) : ℂ) := by
    have hmap := congrArg (Units.val : Units ℂ → ℂ)
      (map_div chi.character (u : Fˣ) b)
    push_cast at hmap
    rw [hlinC] at hmap
    have hb0 : (chi.character b : ℂ) ≠ 0 := ContinuousQuasiChar.apply_ne_zero _ _
    field_simp [hb0] at hmap ⊢
    exact hmap.symm
  have hbc : (b : F) - (c : F) ∈ lattice F (d : ℤ) := by
    have hdeltamem : (delta : F) ∈ lattice F (d : ℤ) := by
      rw [mem_lattice, hdelta]
    have htxmem : (teichmuller F x : F) ∈ lattice F 0 :=
      (mem_lattice_zero_iff F).2 (teichmuller F x).property
    have hbetaMem : (beta : F) ∈ lattice F 0 := by
      rw [mem_lattice, hbeta]
      simp
    have hp := mul_mem_lattice F hbetaMem
      (mul_mem_lattice F hdeltamem htxmem)
    have hbcoe : (b : F) =
        (beta : F) * (1 + (delta : F) * (teichmuller F x : F)) := by
      exact lamprechtFormulaOddBaseUnitZero_coe F d hd beta delta hbeta hdelta x
    have hp' : (beta : F) * ((delta : F) * (teichmuller F x : F)) ∈
        lattice F (d : ℤ) := by simpa using hp
    rw [hbcoe, hcbeta]
    convert hp' using 1
    ring
  have hbcw : ((b : F) - (c : F)) * (w : F) ∈
      lattice F (chi.conductor : ℤ) := by
    have hp := mul_mem_lattice F hbc w.property
    have hdepth : (chi.conductor : ℤ) = (d : ℤ) + (d + 1 : ℕ) := by omega
    simpa only [hdepth] using hp
  have hquot : ((b : F) - (c : F)) * (w : F) /
      ((Gamma : Fˣ) : F) ∈ lattice F (-psi.conductor) := by
    apply (div_mem_lattice_iff F ((Gamma : Fˣ) : F)
      (((b : F) - (c : F)) * (w : F))
      ((chi.conductor : ℤ) + psi.conductor) (-psi.conductor)
      Gamma.property).2
    simpa only [add_neg_cancel_right] using hbcw
  have htriv : (psi.character (((b : F) - (c : F)) * (w : F) /
      ((Gamma : Fˣ) : F)) : ℂ) = 1 := by
    exact congrArg Units.val (psi.isConductor.trivial _ hquot)
  have harg : ((u : Fˣ) : F) / ((Gamma : Fˣ) : F) =
      (b : F) / ((Gamma : Fˣ) : F) +
        (c : F) * (w : F) / ((Gamma : Fˣ) : F) +
        ((b : F) - (c : F)) * (w : F) / ((Gamma : Fˣ) : F) := by
    dsimp only [w]
    field_simp [Units.ne_zero b, AdmissibleGamma.coe_ne_zero Gamma]
    ring
  rw [finiteGaussSummand_mk, finiteGaussSummandRepresentative,
    finiteGaussSummandRepresentative, harg,
    ContinuousAddChar.map_add_eq_mul,
    ContinuousAddChar.map_add_eq_mul]
  push_cast
  rw [htriv, mul_one, hchi]
  have hp0 : (psi.character ((c : F) * (w : F) /
      ((Gamma : Fˣ) : F)) : ℂ) ≠ 0 := ContinuousAddChar.apply_ne_zero _ _
  field_simp [hp0]
  push_cast
  ring

private def lamprechtFormulaOddRawHasseValue
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hd : 0 < d) (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (x : ResidueField F) : ℂ :=
  (psi.character ((c : F) * (delta : F) * (teichmuller F x : F) /
      ((Gamma : Fˣ) : F)) : ℂ) *
    (chi.character (positiveUnitOfLattice F hd
      (lamprechtFormulaOddDisplacement F d delta hdelta x)) : ℂ)⁻¹

private theorem lamprechtFormulaFiniteGaussSummandRepresentative_odd_base
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hd : 0 < d)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (hcbeta : (c : F) = (beta : F))
    (x : ResidueField F) :
    finiteGaussSummandRepresentative chi psi Gamma
        (lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x) =
      ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character beta : ℂ)⁻¹) *
        lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x := by
  let v := positiveUnitOfLattice F hd
    (lamprechtFormulaOddDisplacement F d delta hdelta x)
  have hchar :
      (chi.character
        (lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x : Fˣ) : ℂ) =
      (chi.character beta : ℂ) * (chi.character v : ℂ) := by
    exact congrArg Units.val (map_mul chi.character beta v)
  have harg :
      ((lamprechtFormulaOddBaseUnitZero F d hd beta delta hbeta hdelta x : Fˣ) : F) /
          ((Gamma : Fˣ) : F) =
        (c : F) / ((Gamma : Fˣ) : F) +
          (c : F) * (delta : F) * (teichmuller F x : F) /
            ((Gamma : Fˣ) : F) := by
    rw [lamprechtFormulaOddBaseUnitZero_coe, hcbeta]
    field_simp [AdmissibleGamma.coe_ne_zero Gamma]
  rw [finiteGaussSummandRepresentative, harg,
    ContinuousAddChar.map_add_eq_mul, hchar]
  dsimp only [lamprechtFormulaOddRawHasseValue, v]
  push_cast
  ring

private theorem lamprechtFormulaOddFineFiber_card
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1)
    (y : UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _)) :
    Nat.card
      {u : UnitFiltrationQuotient F 0 chi.conductor
          (Nat.zero_le chi.conductor) //
        unitFiltrationQuotientProjection F (Nat.zero_le (d + 1))
          (show d + 1 ≤ chi.conductor by omega) u = y} =
      residueCard F ^ d := by
  simpa [show d + 1 ≠ 0 by omega,
    show chi.conductor - (d + 1) = d by omega] using
    (unitFiltrationQuotientProjection_fiber_card F
      (Nat.zero_le (d + 1)) (show d + 1 ≤ chi.conductor by omega) y)

@[reducible] noncomputable def lamprechtFormulaOddFineFiberFintype
    (chi : LocalQuasiCharData F) (d : ℕ)
    (hdq : d + 1 ≤ chi.conductor)
    (y : UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _)) :
    Fintype
      {u : UnitFiltrationQuotient F 0 chi.conductor
          (Nat.zero_le chi.conductor) //
        unitFiltrationQuotientProjection F (Nat.zero_le (d + 1)) hdq u = y} :=
  Fintype.ofFinite _

private theorem lamprechtFormulaOddFineFiber_sum
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hd : 0 < d)
    (hr : IsLamprechtStationaryDepth chi.conductor (d + 1))
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (hcbeta : (c : F) = (beta : F))
    (x : ResidueField F) :
    letI := lamprechtFormulaOddFineFiberFintype F chi d
      (show d + 1 ≤ chi.conductor by omega)
      (lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x)
    ∑ u : {u : UnitFiltrationQuotient F 0 chi.conductor
          (Nat.zero_le chi.conductor) //
        unitFiltrationQuotientProjection F (Nat.zero_le (d + 1))
          (show d + 1 ≤ chi.conductor by omega) u =
            lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x},
      finiteGaussSummand chi psi Gamma u =
        (residueCard F : ℂ) ^ d *
          (((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
            (chi.character beta : ℂ)⁻¹) *
            lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x) := by
  classical
  let Y := {u : UnitFiltrationQuotient F 0 chi.conductor
          (Nat.zero_le chi.conductor) //
        unitFiltrationQuotientProjection F (Nat.zero_le (d + 1))
          (show d + 1 ≤ chi.conductor by omega) u =
            lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x}
  letI : Fintype Y := lamprechtFormulaOddFineFiberFintype F chi d
    (show d + 1 ≤ chi.conductor by omega)
    (lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x)
  let C : ℂ := ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
      (chi.character beta : ℂ)⁻¹) *
      lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x
  have hcard : Fintype.card Y = residueCard F ^ d := by
    rw [← Nat.card_eq_fintype_card]
    exact lamprechtFormulaOddFineFiber_card F chi d hm
      (lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x)
  calc
    (∑ u : Y, finiteGaussSummand chi psi Gamma u) = ∑ _u : Y, C := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [lamprechtFormulaFiniteGaussSummand_odd_fine_fiber_constant
        F chi psi d hm hd hr Gamma c hc beta delta hbeta hdelta hcbeta
        x u u.property,
        lamprechtFormulaFiniteGaussSummandRepresentative_odd_base
          F chi psi d hd Gamma c beta delta hbeta hdelta hcbeta x]
    _ = (Fintype.card Y : ℂ) * C := by simp
    _ = (residueCard F : ℂ) ^ d * C := by rw [hcard, Nat.cast_pow]

private theorem lamprechtFormulaFiniteGaussSum_odd_raw
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hd : 0 < d)
    (hr : IsLamprechtStationaryDepth chi.conductor (d + 1))
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        hr Gamma Gamma.property)
    (beta delta : Fˣ) (hbeta : ord F (beta : F) = 0)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (hcbeta : (c : F) = (beta : F)) :
    letI := residueFieldFintype F
    finiteGaussSum chi psi Gamma =
      (residueCard F : ℂ) ^ d *
        ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character beta : ℂ)⁻¹) *
        ∑ x : ResidueField F,
          lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x := by
  classical
  let U := UnitFiltrationQuotient F 0 chi.conductor
    (Nat.zero_le chi.conductor)
  let V := UnitFiltrationQuotient F 0 (d + 1) (Nat.zero_le _)
  let coeff := lamprechtFormulaCoefficientClass F hr.le_conductor c
  let f := finiteGaussSummand chi psi Gamma
  let beta0 := lamprechtFormulaUnitFiltrationZeroOfOrdZero F beta hbeta
  let target := unitFiltrationQuotientMk F (Nat.zero_le d) beta0
  let pFine := unitFiltrationQuotientProjection F (Nat.zero_le (d + 1))
    (show d + 1 ≤ chi.conductor by omega)
  let pCoarse := unitFiltrationQuotientProjection F (Nat.zero_le d)
    (show d ≤ d + 1 by omega)
  let S := {u : U // coeff u = 0}
  let T := {v : V // pCoarse v = target}
  letI := unitFiltrationQuotientFintype F (Nat.zero_le chi.conductor)
  letI := unitFiltrationQuotientFintype F (Nat.zero_le (d + 1))
  letI := residueFieldFintype F
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype T := Fintype.ofFinite T
  have hdepth : (chi.conductor : ℤ) - (d + 1 : ℕ) = (d : ℤ) := by
    omega
  have hpred : ∀ u : U, coeff u = 0 ↔
      unitFiltrationQuotientProjection F (Nat.zero_le d)
        (show d ≤ chi.conductor by omega) u = target := by
    intro u
    exact lamprechtFormulaCoefficientClass_eq_zero_iff_projection F hr.le_conductor
      (show d ≤ chi.conductor by omega) hdepth c beta hbeta hcbeta u
  let g : S → T := fun u ↦ ⟨pFine u.1, by
    change pCoarse (pFine u.1) = target
    rw [unitFiltrationQuotientProjection_trans F (Nat.zero_le d)
      (show d ≤ d + 1 by omega)
      (show d + 1 ≤ chi.conductor by omega)]
    exact (hpred u.1).1 u.2⟩
  let eResidue : ResidueField F ≃ T :=
    lamprechtFormulaOddCoarseFiberEquiv F d hd beta delta hbeta hdelta
  let fiberEquiv : ∀ t : T,
      {s : S // g s = t} ≃ {u : U // pFine u = t.1} := fun t ↦
    { toFun := fun z ↦ ⟨z.1.1, by
          exact congrArg Subtype.val z.2⟩
      invFun := fun z ↦ ⟨⟨z.1, (hpred z.1).2 (by
          rw [← unitFiltrationQuotientProjection_trans F (Nat.zero_le d)
            (show d ≤ d + 1 by omega)
            (show d + 1 ≤ chi.conductor by omega), z.2]
          exact t.2)⟩, by
            apply Subtype.ext
            exact z.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hinner : ∀ x : ResidueField F,
      (∑ z : {s : S // g s = eResidue x}, f z.1.1) =
        (residueCard F : ℂ) ^ d *
          (((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
            (chi.character beta : ℂ)⁻¹) *
            lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x) := by
    intro x
    letI : Fintype {u : U // pFine u = (eResidue x).1} :=
      lamprechtFormulaOddFineFiberFintype F chi d
        (show d + 1 ≤ chi.conductor by omega) (eResidue x).1
    let Cx : ℂ :=
      ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character beta : ℂ)⁻¹) *
        lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x
    have heval : (eResidue x).1 =
        lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x := by
      exact lamprechtFormulaOddCoarseFiberEquiv_apply F d hd beta delta hbeta hdelta x
    have hcardx : Fintype.card {u : U // pFine u = (eResidue x).1} =
        residueCard F ^ d := by
      rw [← Nat.card_eq_fintype_card]
      exact lamprechtFormulaOddFineFiber_card F chi d hm (eResidue x).1
    calc
      (∑ z : {s : S // g s = eResidue x}, f z.1.1) =
          ∑ u : {u : U // pFine u = (eResidue x).1}, f u.1 := by
        exact (fiberEquiv (eResidue x)).sum_comp (fun u ↦ f u.1)
      _ = ∑ _u : {u : U // pFine u = (eResidue x).1}, Cx := by
        apply Finset.sum_congr rfl
        intro u _hu
        have hu' : pFine u.1 =
            lamprechtFormulaOddCoarseClass F d hd beta delta hbeta hdelta x :=
          u.2.trans heval
        change finiteGaussSummand chi psi Gamma u.1 = Cx
        rw [lamprechtFormulaFiniteGaussSummand_odd_fine_fiber_constant
          F chi psi d hm hd hr Gamma c hc beta delta hbeta hdelta hcbeta
          x u.1 hu',
          lamprechtFormulaFiniteGaussSummandRepresentative_odd_base
            F chi psi d hd Gamma c beta delta hbeta hdelta hcbeta x]
      _ = (Fintype.card {u : U // pFine u = (eResidue x).1} : ℂ) * Cx := by
        simp
      _ = (residueCard F : ℂ) ^ d * Cx := by rw [hcardx, Nat.cast_pow]
  rw [lamprechtFormulaFiniteGaussSum_localized F chi psi hr Gamma c hc]
  change (∑ u : U, if coeff u = 0 then f u else 0) = _
  calc
    _ = (∑ u ∈ Finset.univ.filter (fun u : U ↦ coeff u = 0), f u) := by
      simpa using (Finset.sum_filter (fun u : U ↦ coeff u = 0) f).symm
    _ = ∑ s : S, f s.1 := by
      exact Finset.sum_subtype _ (by simp) f
    _ = ∑ t : T, ∑ z : {s : S // g s = t}, f z.1.1 := by
      exact (Fintype.sum_fiberwise g (fun s : S ↦ f s.1)).symm
    _ = ∑ x : ResidueField F,
        ∑ z : {s : S // g s = eResidue x}, f z.1.1 := by
      exact (eResidue.sum_comp
        (fun t ↦ ∑ z : {s : S // g s = t}, f z.1.1)).symm
    _ = ∑ x : ResidueField F, (residueCard F : ℂ) ^ d *
          (((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
            (chi.character beta : ℂ)⁻¹) *
            lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hinner x
    _ = _ := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring


/-! ## Lamprecht's even and odd formulas -/


private theorem lamprechtPhase_card_pow_mul_of_norm_eq_one
    (d : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    phase ((residueCard F : ℂ) ^ d * z) = z := by
  have hresidue : (0 : ℝ) < residueCard F := by
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_residueCard F))
  have hcardpos : 0 < (residueCard F : ℝ) ^ d := pow_pos hresidue d
  have hcast : (residueCard F : ℂ) ^ d =
      (((residueCard F : ℝ) ^ d : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  change phase (((residueCard F : ℝ) ^ d) • z) = z
  rw [phase_smul_of_pos _ hcardpos, phase_of_norm_eq_one hz]

private theorem lamprechtPhase_card_pow_mul_norm_one_mul
    (d : ℕ) (z w : ℂ) (hz : ‖z‖ = 1) (hw : w ≠ 0) :
    phase ((residueCard F : ℂ) ^ d * z * w) = z * phase w := by
  have hresidue : (0 : ℝ) < residueCard F := by
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_residueCard F))
  have hcardpos : 0 < (residueCard F : ℝ) ^ d := pow_pos hresidue d
  have hcast : (residueCard F : ℂ) ^ d =
      (((residueCard F : ℝ) ^ d : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, mul_assoc]
  change phase (((residueCard F : ℝ) ^ d) • (z * w)) = z * phase w
  rw [phase_smul_of_pos _ hcardpos]
  exact phase_mul_of_norm_eq_one hz hw

/-- The exact unnormalised even-conductor Gauss sum.  The factor
`residueCard F ^ d` is the cardinality of the surviving stationary fiber. -/
theorem finiteGaussSum_lamprecht_even
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 0
          (by omega) (by simpa using hm) hlarge) Gamma Gamma.property) :
    finiteGaussSum chi psi Gamma =
      (residueCard F : ℂ) ^ d *
        lamprechtElementaryFactor F chi psi Gamma
          (lamprechtStationaryRepresentativeUnit F chi psi
            (lamprechtFormula_stationaryDepth F chi d 0
              (by omega) (by simpa using hm) hlarge) Gamma c hc) := by
  let hr := lamprechtFormula_stationaryDepth F chi d 0
    (by omega) (by simpa using hm) hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  have hraw := lamprechtFormulaFiniteGaussSum_even_raw
    F chi psi d hr hm Gamma c hc beta hbeta (by rfl)
  change finiteGaussSum chi psi Gamma =
    (residueCard F : ℂ) ^ d * lamprechtElementaryFactor F chi psi Gamma beta
  change finiteGaussSum chi psi Gamma =
    (residueCard F : ℂ) ^ d *
      ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
        (chi.character beta : ℂ)⁻¹)
  exact hraw

/-- The exact unnormalised odd-conductor Gauss sum.  Its residual sum is the
sum of the genuinely constructed Hasse function, and every fine fiber has
cardinality `residueCard F ^ d`. -/
theorem finiteGaussSum_lamprecht_odd
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    letI := residueFieldFintype F
    finiteGaussSum chi psi Gamma =
      (residueCard F : ℂ) ^ d *
        lamprechtElementaryFactor F chi psi Gamma
          (lamprechtStationaryRepresentativeUnit F chi psi
            (lamprechtFormula_stationaryDepth F chi d 1
              (by omega) hm hlarge) Gamma c hc) *
        (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sum := by
  letI := residueFieldFintype F
  let hr := lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  have hd := lamprechtOdd_d_pos F chi d hm hlarge
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  have hraw := lamprechtFormulaFiniteGaussSum_odd_raw
    F chi psi d hm hd hr Gamma c hc beta delta hbeta hdelta (by rfl)
  change finiteGaussSum chi psi Gamma =
    (residueCard F : ℂ) ^ d * lamprechtElementaryFactor F chi psi Gamma beta *
      (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sum
  change finiteGaussSum chi psi Gamma =
    (residueCard F : ℂ) ^ d *
        ((psi.character ((c : F) / ((Gamma : Fˣ) : F)) : ℂ) *
          (chi.character beta : ℂ)⁻¹) *
      ∑ x : ResidueField F,
        lamprechtFormulaOddRawHasseValue F chi psi d hd Gamma delta hdelta c x
  exact hraw

/-- Lamprecht's even-conductor formula for the computational local constant,
with positive additive phase and inverse multiplicative character. -/
theorem lamprechtEven
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 0
            (by omega) (by simpa using hm) hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 0
          (by omega) (by simpa using hm) hlarge) Gamma Gamma.property) :
    deltaFinite chi psi Gamma =
      (chi.character (Gamma : Fˣ) : ℂ) *
        lamprechtElementaryFactor F chi psi Gamma
          (lamprechtStationaryRepresentativeUnit F chi psi
            (lamprechtFormula_stationaryDepth F chi d 0
              (by omega) (by simpa using hm) hlarge) Gamma c hc) := by
  let hr := lamprechtFormula_stationaryDepth F chi d 0
    (by omega) (by simpa using hm) hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  have hraw := finiteGaussSum_lamprecht_even F chi psi d hm hlarge Gamma c hc
  have hnorm := lamprechtElementaryFactor_norm F chi psi Gamma beta hbeta
  rw [deltaFinite, hraw, lamprechtPhase_card_pow_mul_of_norm_eq_one F d _ hnorm]

/-- Lamprecht's odd-conductor formula for the computational local constant.
The elementary factor and the nonzero Hasse-sum phase occur together. -/
theorem lamprechtOdd
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F) (d : ℕ)
    (hm : chi.conductor = 2 * d + 1) (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma F chi psi)
    (delta : Fˣ)
    (hdelta : ord F (delta : F) = ((d : ℤ) : WithTop ℤ))
    (c : lattice F ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hc : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chi d 1
            (by omega) hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) c =
      stationaryNumeratorClass F chi psi (chi.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chi d 1
          (by omega) hm hlarge) Gamma Gamma.property) :
    letI := residueFieldFintype F
    deltaFinite chi psi Gamma =
      (chi.character (Gamma : Fˣ) : ℂ) *
        lamprechtElementaryFactor F chi psi Gamma
          (lamprechtStationaryRepresentativeUnit F chi psi
            (lamprechtFormula_stationaryDepth F chi d 1
              (by omega) hm hlarge) Gamma c hc) *
        (lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc).sumPhase := by
  letI := residueFieldFintype F
  let hr := lamprechtFormula_stationaryDepth F chi d 1 (by omega) hm hlarge
  let beta := lamprechtStationaryRepresentativeUnit F chi psi hr Gamma c hc
  let phi := lamprechtHasseFunction F chi psi d hm hlarge Gamma delta hdelta c hc
  have hbeta : ord F (beta : F) = 0 :=
    lamprechtStationaryRepresentativeUnit_ord F chi psi hr Gamma c hc
  have hraw := finiteGaussSum_lamprecht_odd
    F chi psi d hm hlarge Gamma delta hdelta c hc
  have hnorm := lamprechtElementaryFactor_norm F chi psi Gamma beta hbeta
  have hsum := lamprechtOdd_hasseSum_ne_zero
    F chi psi d hm hlarge Gamma delta hdelta c hc
  rw [deltaFinite, hraw,
    lamprechtPhase_card_pow_mul_norm_one_mul F d _ _ hnorm hsum]
  change (chi.character (Gamma : Fˣ) : ℂ) *
      (lamprechtElementaryFactor F chi psi Gamma beta * phase phi.sum) =
    (chi.character (Gamma : Fˣ) : ℂ) *
      lamprechtElementaryFactor F chi psi Gamma beta * phi.sumPhase
  rw [HasseFunction.sumPhase]
  ring


end

end LanglandsFirstMainLemma
