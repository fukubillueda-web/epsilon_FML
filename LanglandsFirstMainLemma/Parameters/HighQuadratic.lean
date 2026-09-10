import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsFirstMainLemma.FiniteField.CharTwoRefinement

/-!
# High stationary classes in the wild quadratic case

This file formalizes Propositions `prop:high-parameter-table` and
`prop:wild-quadratic-high-parameters`.  Stationary numerators remain quotient
classes.  The field elements below occur only inside the simultaneous
existential package chosen in the manuscript.

The break-level factor `delta` is essential: `beta = delta * N(beta1)` is an
exact identity, while no congruence `beta = N(beta1)` at the coefficient
depth is asserted.  The norm representative `alpha1` is chosen only at the
subcritical precision `floor ((t+1)/2)`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

/-! ## Numerical depths -/

/-- The excess `v=m-(t+1)` in the wild-quadratic high range. -/
def wildQuadraticHighShift (t m : ℕ) : ℕ := m - (t + 1)

/-- The only precision at which an exact norm representative is selected. -/
def wildQuadraticHighNormPrecision (t : ℕ) : ℕ := (t + 1) / 2

/-- The common stationary unit-layer depth `ceil ((t+1)/2)`. -/
def wildQuadraticHighStationaryDepth (t : ℕ) : ℕ := (t + 2) / 2

/-- The stationary depth used for the conductor-`t+1` norm character. -/
theorem wildQuadraticHigh_stationaryDepth {t : ℕ} (ht : 0 < t) :
    IsLamprechtStationaryDepth (t + 1)
      (wildQuadraticHighStationaryDepth t) := by
  dsimp only [wildQuadraticHighStationaryDepth]
  constructor <;> omega

/-- Arithmetic identities and inequalities used by both stationary classes.
In particular, the upper parity is the parity of `t+1`, not the parity of
the downstairs conductor. -/
theorem wildQuadraticHigh_depth_relations
    {t m mK d epsilon dK epsilonK : ℕ}
    (ht : 0 < t) (hm : t + 1 ≤ m)
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hK : IsStationaryConductorDecomposition mK dK epsilonK)
    (hrel : mK + (t + 1) = 2 * m) :
    let v := wildQuadraticHighShift t m
    let r := wildQuadraticHighNormPrecision t
    let s := wildQuadraticHighStationaryDepth t
    dK = v + r ∧
      epsilonK = (t + 1) % 2 ∧
      dK + epsilonK = v + s ∧
      dK + epsilonK - v = s ∧
      d + epsilon ≥ s ∧
      d ≤ dK ∧
      r ≤ t ∧
      r + s = t + 1 ∧
      (v + (t + 1)) / 2 = d ∧
      epsilon = m % 2 := by
  dsimp only [wildQuadraticHighShift, wildQuadraticHighNormPrecision,
    wildQuadraticHighStationaryDepth]
  have heF := hF.epsilon_le_one
  have heK := hK.epsilon_le_one
  have hFeq := hF.conductor_eq
  have hKeq := hK.conductor_eq
  omega

/-! ## Generic representative helpers -/

/-- A representative of a stationary coefficient class has order zero.
This merely extracts a property of a supplied representative; it makes no
choice and asserts no uniqueness in the field. -/
private theorem stationaryCoefficientClass_representative_ord
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice E 0)
    (hc : latticeQuotientMk E (by omega) c =
      stationaryCoefficientClass E chi psi h gamma hgamma) :
    ord E (c : E) = 0 := by
  have hcLamp := congrArg
    (stationaryCoefficientLamprechtEquivAtConductor E h) hc
  rw [stationaryCoefficientClass_toLamprecht] at hcLamp
  have hord := stationaryNumeratorClass_representative_ord E chi psi
    (chi.conductor : ℤ) (stationaryDepthOfConductorDecomposition E chi h)
    gamma hgamma
    (⟨(c : E), by simpa using c.property⟩ :
      lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (by simpa only [stationaryCoefficientLamprechtEquivAtConductor_mk]
      using hcLamp)
  simpa using hord

/-- In degree two the truncated norm value is exactly trace plus norm. -/
theorem wildQuadratic_normPolynomialValue_eq_trace_add_norm
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (hdegree : Module.finrank F K = 2) (x : K) :
    normPolynomialValue F K x = trace F K x + norm F K x := by
  rw [normPolynomialValue_eq_sum_elementarySymmetric, hdegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd]
  rw [elementarySymmetric_one]
  have hfin : elementarySymmetric F K 2 x = norm F K x := by
    rw [← hdegree]
    exact elementarySymmetric_finrank F K x
  rw [hfin]

/-- Exact quadratic norm identity with the trace sign retained. -/
theorem wildQuadratic_norm_sub
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (hdegree : Module.finrank F K = 2) (b : Fˣ) (c : K) :
    norm F K (algebraMap F K (b : F) - c) =
      (b : F) ^ 2 - (b : F) * trace F K c + norm F K c := by
  let y : K := -c / algebraMap F K (b : F)
  have hy := wildQuadratic_normPolynomialValue_eq_trace_add_norm
    F K hdegree y
  have hfactor : algebraMap F K (b : F) - c =
      algebraMap F K (b : F) * (1 + y) := by
    dsimp only [y]
    field_simp [Units.ne_zero b]
    ring
  have htrace : trace F K y = -(b : F)⁻¹ * trace F K c := by
    have hyarg : y = algebraMap F K (-(b : F)⁻¹) * c := by
      dsimp only [y]
      rw [map_neg, map_inv₀]
      field_simp [Units.ne_zero b]
    rw [hyarg, ← Algebra.smul_def, map_smul]
    simp
  have hnorm : norm F K y = norm F K c / (b : F) ^ 2 := by
    dsimp only [y]
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv]
    have hneg : norm F K (-c) = norm F K c := by
      rw [show -c = algebraMap F K (-1 : F) * c by simp,
        map_mul, norm_algebraMap, hdegree]
      norm_num
    rw [hneg, norm_algebraMap, hdegree]
    simp [div_eq_mul_inv]
  rw [hfactor, map_mul, norm_algebraMap, hdegree]
  change (b : F) ^ 2 * norm F K (1 + y) = _
  have hone : norm F K (1 + y) = 1 + trace F K y + norm F K y := by
    rw [normPolynomialValue] at hy
    linear_combination hy
  rw [hone, htrace, hnorm]
  field_simp [Units.ne_zero b]
  ring

/-! ## Ramified quadratic setup -/

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

/-- The actual upstairs conductor in the whole-orbit-minimal high range. -/
theorem highParameter_wildQuadratic_conductor_relation
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hhigh : t + 1 ≤ chiF.conductor) :
    chiK.conductor + (t + 1) = 2 * chiF.conductor := by
  have hz := minimalOrbit_compNorm_conductor_eq_atOrAboveCritical
    F K ht hres pi hpi hgen chiF hminimal chiK hchi hhigh
  rw [hdegree] at hz
  norm_num at hz
  omega

omit hres in
/-- A positive wild quadratic break forces residue characteristic two. -/
theorem highParameter_wildQuadratic_residueCharacteristic
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t) :
    residueCharacteristic F = 2 := by
  exact (residueCharacteristic_eq_degree_of_positive_break
    F K ht htpos pi hpi hgen).trans hdegree

omit hres in
/-- The same characteristic-two conclusion upstairs. -/
theorem highParameter_wildQuadratic_residueCharacteristic_upstairs
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t) :
    residueCharacteristic K = 2 := by
  rw [residueCharacteristic_extension_eq F K]
  exact highParameter_wildQuadratic_residueCharacteristic
    F K ht pi hpi hgen hdegree htpos

/-- The common denominator `gammaK=gammaF` is admissible at the actual
upstairs conductor. -/
theorem highParameter_wildQuadratic_commonDenominator
    (hdegree : Module.finrank F K = 2)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hhigh : t + 1 ≤ chiF.conductor)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  have hsum := minimalOrbit_compNorm_add_compTrace_conductor_eq
    F K ht hres pi hpi hgen chiF hminimal chiK psiF psiK
      hchi hpsi hhigh
  change ord K (algebraMap F K (gammaF : F)) = _
  rw [ord_algebraMap, hram, hgammaF, ← WithTop.coe_nsmul]
  change (((2 : ℤ) * ((chiF.conductor : ℤ) + psiF.conductor) : ℤ) :
      WithTop ℤ) = _
  congr 1
  rw [hsum, hdegree]
  norm_num

/-- The three norm-filtration inclusions at the actual source and target
depths.  This proof works even when the downstairs coefficient depth exceeds
the ramification break. -/
theorem highParameter_wildQuadratic_precision
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hhigh : t + 1 ≤ chiF.conductor) :
    NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor d epsilon where
  sourceDecomposition := hK
  targetDecomposition := hF
  variable_inclusion := by
    have hrel := highParameter_wildQuadratic_conductor_relation
      F K ht hres pi hpi hgen hdegree chiF chiK hminimal hchi hhigh
    have hsource : herbrandPsiNat t 2 (d + epsilon - 1) + 1 ≤
        dK + epsilonK := by
      have heF := hF.epsilon_le_one
      have heK := hK.epsilon_le_one
      simp only [herbrandPsiNat]
      rw [hF.conductor_eq] at hrel hhigh
      rw [hK.conductor_eq] at hrel
      omega
    have hmap := normMapsUnitFiltration_herbrand_succ
      F K ht hres pi hpi hgen (d + epsilon - 1)
    rw [hdegree] at hmap
    intro u hu
    have hu' := unitFiltration_antitone K hsource hu
    have hout := hmap u hu'
    have htarget : d + epsilon - 1 + 1 = d + epsilon := by
      have := hF.variableDepth_pos
      omega
    simpa only [htarget] using hout
  conductor_inclusion := by
    have hrel := highParameter_wildQuadratic_conductor_relation
      F K ht hres pi hpi hgen hdegree chiF chiK hminimal hchi hhigh
    have hsource : herbrandPsiNat t 2 (chiF.conductor - 1) + 1 =
        chiK.conductor := by
      simp only [herbrandPsiNat]
      omega
    have hmap := normMapsUnitFiltration_herbrand_succ
      F K ht hres pi hpi hgen (chiF.conductor - 1)
    intro u hu
    have hu' : u ∈ unitFiltration K
        (herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1) := by
      simpa only [hdegree, hsource] using hu
    have hout := hmap u hu'
    have htarget : chiF.conductor - 1 + 1 = chiF.conductor := by
      exact Nat.sub_add_cancel (by omega)
    simpa only [htarget] using hout
  ambiguity_inclusion := by
    have hrel := highParameter_wildQuadratic_conductor_relation
      F K ht hres pi hpi hgen hdegree chiF chiK hminimal hchi hhigh
    have hsource : herbrandPsiNat t 2 (d - 1) + 1 ≤ dK := by
      have heF := hF.epsilon_le_one
      have heK := hK.epsilon_le_one
      simp only [herbrandPsiNat]
      rw [hF.conductor_eq] at hrel hhigh
      rw [hK.conductor_eq] at hrel
      omega
    have hmap := normMapsUnitFiltration_herbrand_succ
      F K ht hres pi hpi hgen (d - 1)
    rw [hdegree] at hmap
    intro u hu
    have hu' := unitFiltration_antitone K hsource hu
    have hout := hmap u hu'
    have htarget : d - 1 + 1 = d :=
      Nat.sub_add_cancel hF.floorDepth_pos
    simpa only [htarget] using hout

/-- At the quadratic half-depth, both the trace and the norm remain on the
same downstairs stationary layer. -/
theorem highParameter_wildQuadratic_trace_norm_mem
    (hdegree : Module.finrank F K = 2)
    {y : K}
    (hy : y ∈ lattice K (wildQuadraticHighStationaryDepth t : ℤ)) :
    trace F K y ∈
        lattice F (wildQuadraticHighStationaryDepth t : ℤ) ∧
      norm F K y ∈
        lattice F (wildQuadraticHighStationaryDepth t : ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  have hdifferent : differentExponent F K = t + 1 :=
    differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen
  constructor
  · have htrace := trace_mem_lattice_floor F K pi hpi hgen
      (wildQuadraticHighStationaryDepth t : ℤ) hy
    rw [hdifferent, hram] at htrace
    apply lattice_antitone F (n :=
      (((wildQuadraticHighStationaryDepth t : ℤ) +
        ((t + 1 : ℕ) : ℤ)) / (2 : ℤ)))
    · simp only [wildQuadraticHighStationaryDepth]
      omega
    · exact htrace
  · rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact hy

/-! ## Simultaneous manuscript representatives -/

/-- The conductor-`t+1` datum for the nontrivial norm character. -/
noncomputable def wildQuadraticHighTauData
    (tau : NormCharacter F K) (htau : tau ≠ 1) : LocalQuasiCharData F :=
  quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)

/-- The stationary conductor decomposition of the norm character records
the parity of `t+1`. -/
theorem wildQuadraticHighTauDecomposition
    (htpos : 0 < t) (tau : NormCharacter F K) (htau : tau ≠ 1) :
    IsStationaryConductorDecomposition
      (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau).conductor
      (wildQuadraticHighNormPrecision t) ((t + 1) % 2) := by
  rw [wildQuadraticHighTauData, quasiCharDataOfIsConductor_conductor]
  constructor
  · omega
  · omega
  · simp only [wildQuadraticHighNormPrecision]
    omega

/-- The actual datum for the twist `tau*chiF`; its conductor is not supplied
by the caller. -/
noncomputable def wildQuadraticHighTwistData
    (chiF : LocalQuasiCharData F) (tau : NormCharacter F K) :
    LocalQuasiCharData F :=
  ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chiF tau

@[simp] theorem wildQuadraticHighTwistData_character
    (chiF : LocalQuasiCharData F) (tau : NormCharacter F K) :
    (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau).character =
      tau.1 * chiF.character := by
  exact ramifiedNormCharacterOrbitTwistData_character
    F K ht hres pi hpi hgen chiF tau

/-- Minimality excludes a conductor drop for the nontrivial twist throughout
the high range, including the boundary. -/
theorem highParameter_wildQuadratic_twist_conductor
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau).conductor =
      chiF.conductor := by
  rw [wildQuadraticHighTwistData,
    ramifiedNormCharacterOrbitTwistData_conductor_eq
      F K ht hres pi hpi hgen chiF hminimal tau htau,
    Nat.max_eq_left hhigh]

/-- The actual twist inherits the downstairs stationary decomposition. -/
theorem wildQuadraticHighTwistDecomposition
    (chiF : LocalQuasiCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (tau : NormCharacter F K) (htau : tau ≠ 1) :
    IsStationaryConductorDecomposition
      (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau).conductor
      d epsilon := by
  rw [highParameter_wildQuadratic_twist_conductor
    F K ht hres pi hpi hgen chiF hminimal hhigh tau htau]
  exact hF

/-- The original common denominator is admissible for the actual twist. -/
theorem highParameter_wildQuadratic_twistDenominator
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ord F (gammaF : F) =
      ((((wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau).conductor : ℤ) +
        psiF.conductor : ℤ) : WithTop ℤ) := by
  rw [highParameter_wildQuadratic_twist_conductor
    F K ht hres pi hpi hgen chiF hminimal hhigh tau htau]
  exact hgammaF

/-- Simultaneous choices made in the manuscript.  None of these choices is
declared canonical. -/
structure WildQuadraticHighRepresentatives
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hhigh : t + 1 ≤ chiF.conductor) (htpos : 0 < t)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) where
  beta : Fˣ
  beta1 : Kˣ
  delta : unitFiltration F t
  alpha1 : Kˣ
  beta_mem_unit : beta ∈ unitGroup F
  beta1_mem_unit : beta1 ∈ unitGroup K
  beta_factor : beta = (delta : Fˣ) * normUnits F K beta1
  beta_integral : (beta : F) ∈ lattice F 0
  beta_class : latticeQuotientMk F (by omega)
      (⟨(beta : F), beta_integral⟩ : lattice F 0) =
    stationaryCoefficientClass F chiF psiF hF gammaF hgammaF
  alpha1_order : ord K (alpha1 : K) =
    (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ)
  tau_integral :
    ((((delta : Fˣ) * normUnits F K alpha1 : Fˣ) : F)) ∈
      lattice F ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
  tau_class : latticeQuotientMk F
      (sub_le_sub_left
        (wildQuadraticHigh_stationaryDepth htpos).int_le_conductor
        (chiF.conductor : ℤ))
      (⟨(((delta : Fˣ) * normUnits F K alpha1 : Fˣ) : F), tau_integral⟩ :
        lattice F ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))) =
    stationaryNumeratorClass F
      (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
      (chiF.conductor : ℤ)
      (wildQuadraticHigh_stationaryDepth htpos) gammaF hgammaF

/-- Simultaneous existence.  `beta1` is obtained only at the break, while
`alpha1` is obtained only at `floor ((t+1)/2)`. -/
theorem highParameter_wildQuadratic_exists_representatives
    (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hhigh : t + 1 ≤ chiF.conductor)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    Nonempty (WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) := by
  obtain ⟨b, hb⟩ := latticeQuotientMk_surjective F (by omega)
    (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
  have hbOrd : ord F (b : F) = 0 :=
    stationaryCoefficientClass_representative_ord F chiF psiF
      hF gammaF hgammaF b hb
  have hbne : (b : F) ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [hbOrd]
    simp
  let beta : Fˣ := Units.mk0 (b : F) hbne
  have hbetaUnit : beta ∈ unitGroup F :=
    (mem_unitGroup_iff_ord_eq_zero F beta).2 (by simpa [beta] using hbOrd)
  obtain ⟨beta1, hbeta1Unit, delta, hbetaFactor⟩ :=
    unit_eq_unitFiltration_mul_norm F K ht hres pi hpi hgen beta hbetaUnit
  let hr := wildQuadraticHigh_stationaryDepth htpos
  let tauData := wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau
  obtain ⟨a, ha⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ))
    (stationaryNumeratorClass F tauData psiF (chiF.conductor : ℤ)
      hr gammaF hgammaF)
  have haOrd : ord F (a : F) =
      (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    simpa only [tauData, wildQuadraticHighTauData,
      quasiCharDataOfIsConductor_conductor] using
      (stationaryNumeratorClass_representative_ord F tauData psiF
        (chiF.conductor : ℤ) hr gammaF hgammaF a ha)
  have hane : (a : F) ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [haOrd]
    simp
  let cTau : Fˣ := Units.mk0 (a : F) hane
  have hrle : wildQuadraticHighNormPrecision t ≤ t := by
    simp only [wildQuadraticHighNormPrecision]
    omega
  obtain ⟨alpha1, halphaSubcritical, halphaCongruent⟩ :=
    normRepresentative_subcritical_mul_unit F K ht hres pi hpi hgen
      (h := (chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
      (s := wildQuadraticHighNormPrecision t) hrle cTau (delta : Fˣ)
      (unitFiltration_le_unitGroup F t delta.property)
      (by simpa [cTau] using haOrd)
  have hdeltaOrd : ord F ((delta : Fˣ) : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F (delta : Fˣ)).1
      (unitFiltration_le_unitGroup F t delta.property)
  have halphaNormOrd : ord F (norm F K (alpha1 : K)) =
      (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul]
    exact halphaSubcritical.source_order
  have halphaIntegral :
      ((((delta : Fˣ) * normUnits F K alpha1 : Fˣ) : F)) ∈
        lattice F ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) := by
    rw [mem_lattice]
    change (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      ord F (((delta : Fˣ) : F) * norm F K (alpha1 : K))
    rw [ord_mul, hdeltaOrd, halphaNormOrd, zero_add]
  have hdepth :
      (chiF.conductor : ℤ) - ((wildQuadraticHighStationaryDepth t : ℕ) : ℤ) =
        ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) +
          ((wildQuadraticHighNormPrecision t : ℕ) : ℤ) := by
    simp only [wildQuadraticHighStationaryDepth,
      wildQuadraticHighNormPrecision]
    omega
  have halphaClass : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ))
      (⟨((((delta : Fˣ) * normUnits F K alpha1 : Fˣ) : F)),
        halphaIntegral⟩ :
        lattice F ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))) =
      stationaryNumeratorClass F tauData psiF (chiF.conductor : ℤ)
        hr gammaF hgammaF := by
    rw [← ha]
    apply (latticeQuotientMk_eq_mk_iff F _).2
    change (((delta : Fˣ) : F) * norm F K (alpha1 : K)) - (a : F) ∈
      lattice F ((chiF.conductor : ℤ) -
        ((wildQuadraticHighStationaryDepth t : ℕ) : ℤ))
    rw [hdepth]
    have hneg := neg_mem_lattice F halphaCongruent
    simpa only [cTau, Units.val_mk0, neg_sub] using hneg
  refine ⟨⟨beta, beta1, delta, alpha1, hbetaUnit, hbeta1Unit,
    hbetaFactor, ?_, ?_, halphaSubcritical.source_order,
    halphaIntegral, ?_⟩⟩
  · simpa [beta] using b.property
  · simpa [beta] using hb
  · simpa only [hr, tauData] using halphaClass

namespace WildQuadraticHighRepresentatives

variable {F K ht hres pi hpi hgen}
variable {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
variable {d epsilon : ℕ}
variable {hF : IsStationaryConductorDecomposition chiF.conductor d epsilon}
variable {hhigh : t + 1 ≤ chiF.conductor} {htpos : 0 < t}
variable {tau : NormCharacter F K} {htau : tau ≠ 1}
variable {gammaF : Fˣ}
variable {hgammaF : ord F (gammaF : F) =
  (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)}

/-- `alpha=N(alpha1)`. -/
def alpha (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : Fˣ :=
  normUnits F K R.alpha1

/-- The corrected norm-character coefficient `c=alpha*delta`. -/
def cF (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : Fˣ :=
  R.alpha * (R.delta : Fˣ)

/-- The selected upstairs representative. -/
def betaK (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : K :=
  algebraMap F K (R.beta : F) -
    (R.beta1 : K) * algebraMap F K (R.cF : F) / (R.alpha1 : K)

/-- The correction term subtracted from the scalar `beta`. -/
def correction (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : K :=
  (R.beta1 : K) * algebraMap F K (R.cF : F) / (R.alpha1 : K)

/-- The selected representative of the nontrivial twist. -/
def betaTwist (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : F :=
  (R.beta : F) + (R.cF : F)

/-- The normalized upstairs ratio `u=beta1/alpha1`. -/
def u (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : Kˣ :=
  R.beta1 / R.alpha1

/-- The normalized downstairs ratio `n=beta/(alpha*delta)`. -/
def n (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : Fˣ :=
  R.beta / R.cF

/-- The denominator used when the norm character itself is written with
stationary coefficient one. -/
def gammaTau (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
    chiF psiF hF hhigh htpos tau htau gammaF hgammaF) : Fˣ :=
  gammaF / R.cF

@[simp] theorem alpha_coe
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    (R.alpha : F) = norm F K (R.alpha1 : K) := rfl

/-- The exact norm-ratio identity `N(u)=n`. -/
theorem norm_u_eq_n
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    normUnits F K R.u = R.n := by
  rw [u, n, cF, alpha, _root_.map_div, R.beta_factor]
  simp only [div_eq_mul_inv]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Exact scalar factorization used in all downstream ratios. -/
theorem cF_mul_n
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    R.cF * R.n = R.beta := by
  rw [n]
  simp [div_eq_mul_inv, mul_left_comm]

/-- The selected upstairs representative in normalized ratio form. -/
theorem betaK_eq_cF_mul_sub
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    R.betaK = algebraMap F K (R.cF : F) *
      (algebraMap F K (R.n : F) - (R.u : K)) := by
  rw [betaK, u]
  have hbeta : (R.beta : F) = (R.cF : F) * (R.n : F) := by
    exact congrArg Units.val R.cF_mul_n.symm
  rw [hbeta, map_mul, Units.val_div_eq_div_val]
  field_simp [Units.ne_zero R.alpha1]

/-- The selected twist representative in normalized ratio form. -/
theorem betaTwist_eq_cF_mul_add_one
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    R.betaTwist = (R.cF : F) * ((R.n : F) + 1) := by
  rw [betaTwist]
  have hbeta : (R.beta : F) = (R.cF : F) * (R.n : F) := by
    exact congrArg Units.val R.cF_mul_n.symm
  rw [hbeta]
  ring

/-- The selected downstairs coefficient is a unit. -/
theorem beta_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord F (R.beta : F) = 0 :=
  (mem_unitGroup_iff_ord_eq_zero F R.beta).1 R.beta_mem_unit

/-- The break-level norm preimage of `beta` is a unit. -/
theorem beta1_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord K (R.beta1 : K) = 0 :=
  (mem_unitGroup_iff_ord_eq_zero K R.beta1).1 R.beta1_mem_unit

/-- The essential correction `delta` has order zero. -/
theorem delta_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord F (((R.delta : unitFiltration F t) : Fˣ) : F) = 0 :=
  (mem_unitGroup_iff_ord_eq_zero F (R.delta : Fˣ)).1
    (unitFiltration_le_unitGroup F t R.delta.property)

/-- The corrected coefficient has the exact shift order `v=m-(t+1)`. -/
theorem cF_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord F (R.cF : F) =
      (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [cF, Units.val_mul, ord_mul, alpha_coe, ord_norm, hres, one_nsmul,
    R.alpha1_order, R.delta_order, add_zero]

/-- Natural-number form of the corrected coefficient order. -/
theorem cF_order_shift
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord F (R.cF : F) =
      ((wildQuadraticHighShift t chiF.conductor : ℕ) : WithTop ℤ) := by
  rw [R.cF_order]
  congr 1
  exact (Int.ofNat_sub hhigh).symm

/-- The correction subtracted upstairs has exact order `v`. -/
theorem correction_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    ord K R.correction =
      (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  rw [correction, ord_div, ord_mul, R.beta1_order, ord_algebraMap,
    hram, R.cF_order, R.alpha1_order, zero_add]
  norm_cast
  ring

/-- Natural-number form of the upstairs correction order. -/
theorem correction_order_shift
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    ord K R.correction =
      ((wildQuadraticHighShift t chiF.conductor : ℕ) : WithTop ℤ) := by
  rw [R.correction_order hdegree]
  congr 1
  exact (Int.ofNat_sub hhigh).symm

/-- Both normalized ratios have manuscript order `T-m=-v` upstairs. -/
theorem u_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord K (R.u : K) =
      ((((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) : WithTop ℤ) := by
  rw [u, Units.val_div_eq_div_val, ord_div, R.beta1_order,
    R.alpha1_order, zero_sub]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  ring

/-- The downstairs ratio has the same exact order `T-m=-v`. -/
theorem n_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord F (R.n : F) =
      ((((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) : WithTop ℤ) := by
  rw [n, Units.val_div_eq_div_val, ord_div, R.beta_order, R.cF_order,
    zero_sub]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  ring

theorem correction_integral
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    R.correction ∈ lattice K
      (wildQuadraticHighShift t chiF.conductor : ℤ) := by
  rw [mem_lattice, R.correction_order_shift hdegree]
  exact le_rfl

theorem betaK_integral
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    R.betaK ∈ lattice K 0 := by
  rw [betaK]
  apply sub_mem_lattice K
  · rw [mem_lattice, ord_algebraMap, R.beta_order]
    simp
  · have hv : (0 : ℤ) ≤
        (wildQuadraticHighShift t chiF.conductor : ℤ) := by positivity
    exact lattice_antitone K hv (R.correction_integral hdegree)

theorem betaTwist_integral
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    R.betaTwist ∈ lattice F 0 := by
  rw [betaTwist]
  apply add_mem_lattice F R.beta_integral
  have hv : (0 : ℤ) ≤
      (wildQuadraticHighShift t chiF.conductor : ℤ) := by positivity
  exact lattice_antitone F hv (by
    rw [mem_lattice, R.cF_order_shift]
    exact le_rfl)

/-- `gammaF/cF` is admissible for the conductor-`t+1` norm character. -/
theorem gammaTau_order
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    ord F (R.gammaTau : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) := by
  rw [gammaTau, Units.val_div_eq_div_val, ord_div, hgammaF, R.cF_order]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  ring

/-- With denominator `gammaF/cF`, the selected stationary coefficient of
`tau` is exactly the manuscript's representative `1`. -/
theorem tau_unit_class
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    let hTau := wildQuadraticHighTauDecomposition
      F K ht hres pi hpi hgen htpos tau htau
    latticeQuotientMk F (by
        exact_mod_cast (wildQuadraticHighTauDecomposition
          F K ht hres pi hpi hgen htpos tau htau).floorDepth_pos.le)
        (⟨(1 : F), by rw [mem_lattice, ord_one]; exact le_rfl⟩ : lattice F 0) =
      stationaryCoefficientClass F
        (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau)
        psiF hTau R.gammaTau R.gammaTau_order := by
  dsimp only
  let hTau := wildQuadraticHighTauDecomposition
    F K ht hres pi hpi hgen htpos tau htau
  apply (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
    hTau R.gammaTau R.gammaTau_order
    ⟨(1 : F), by rw [mem_lattice, ord_one]; exact le_rfl⟩).2
  intro x
  have hdepth : wildQuadraticHighNormPrecision t + (t + 1) % 2 =
      wildQuadraticHighStationaryDepth t := by
    simp only [wildQuadraticHighNormPrecision,
      wildQuadraticHighStationaryDepth]
    omega
  let xs : lattice F (wildQuadraticHighStationaryDepth t : ℤ) :=
    ⟨(x : F), by rw [← hdepth]; exact x.property⟩
  let hr := wildQuadraticHigh_stationaryDepth htpos
  let cTau : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
    ⟨(R.cF : F), by simpa only [cF, alpha, Units.val_mul,
      coe_normUnits, mul_comm] using R.tau_integral⟩
  have hcTau : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cTau =
      stationaryNumeratorClass F
        (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
        (chiF.conductor : ℤ) hr gammaF hgammaF := by
    simpa only [cTau, cF, alpha, Units.val_mul, coe_normUnits,
      mul_comm, hr] using R.tau_class
  have hlinear := stationaryNumeratorClass_linearization F
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
      (chiF.conductor : ℤ) hr gammaF hgammaF cTau hcTau xs
  have hunit :
      (positiveUnitOfLattice F hTau.variableDepth_pos x : Fˣ) =
        (positiveUnitOfLattice F hr.pos xs : Fˣ) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, xs]
  rw [hunit]
  rw [hlinear]
  congr 1
  simp only [gammaTau, Units.val_div_eq_div_val, cTau, xs]
  field_simp [Units.ne_zero gammaF, Units.ne_zero R.cF]

/-- Exact quadratic norm-to-trace conversion.  The minus sign is part of
the statement, and the coefficient is the corrected `alpha*delta`. -/
theorem conversion
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2)
    (y : lattice K (wildQuadraticHighStationaryDepth t : ℤ)) :
    psiF.character
        ((R.cF : F) * norm F K (y : K) / (gammaF : F)) =
      psiF.character
        (-((R.cF : F) * trace F K (y : K) / (gammaF : F))) := by
  let hr := wildQuadraticHigh_stationaryDepth htpos
  obtain ⟨htrace, hnorm⟩ := highParameter_wildQuadratic_trace_norm_mem
    F K ht hres pi hpi hgen hdegree y.property
  let traceNorm : lattice F (wildQuadraticHighStationaryDepth t : ℤ) :=
    ⟨trace F K (y : K) + norm F K (y : K),
      add_mem_lattice F htrace hnorm⟩
  let cTau : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
    ⟨(R.cF : F), by simpa only [cF, alpha, Units.val_mul,
      coe_normUnits, mul_comm]
      using R.tau_integral⟩
  have hcTau : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cTau =
      stationaryNumeratorClass F
        (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
        (chiF.conductor : ℤ) hr gammaF hgammaF := by
    simpa only [cTau, cF, alpha, Units.val_mul, coe_normUnits, mul_comm, hr]
      using R.tau_class
  have hlinear := stationaryNumeratorClass_linearization F
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
    (chiF.conductor : ℤ) hr gammaF hgammaF cTau hcTau traceNorm
  have hlinear' :
      tau.1 (positiveUnitOfLattice F hr.pos traceNorm : Fˣ) =
        psiF.character ((cTau : F) * (traceNorm : F) / (gammaF : F)) := by
    simpa only [wildQuadraticHighTauData,
      quasiCharDataOfIsConductor_character] using hlinear
  let uy : Kˣ := (positiveUnitOfLattice K hr.pos y : Kˣ)
  have hunitNorm : normUnits F K uy =
      (positiveUnitOfLattice F hr.pos traceNorm : Fˣ) := by
    apply Units.ext
    simp only [uy, coe_normUnits, coe_positiveUnitOfLattice]
    change norm F K (1 + (y : K)) =
      1 + (trace F K (y : K) + norm F K (y : K))
    have hexact := wildQuadratic_normPolynomialValue_eq_trace_add_norm
      F K hdegree (y : K)
    rw [normPolynomialValue] at hexact
    linear_combination hexact
  rw [← hunitNorm] at hlinear'
  have htauNorm : tau.1 (normUnits F K uy) = 1 :=
    tau.eq_one_on_normRange F K (normUnits F K uy) ⟨uy, rfl⟩
  rw [htauNorm] at hlinear'
  have harg :
      (R.cF : F) * (trace F K (y : K) + norm F K (y : K)) /
          (gammaF : F) =
        (R.cF : F) * trace F K (y : K) / (gammaF : F) +
          (R.cF : F) * norm F K (y : K) / (gammaF : F) := by
    ring
  change (1 : ℂˣ) =
      psiF.character
        ((R.cF : F) * (trace F K (y : K) + norm F K (y : K)) /
          (gammaF : F)) at hlinear'
  rw [harg, psiF.character.map_add_eq_mul] at hlinear'
  let A : ℂˣ := psiF.character
    ((R.cF : F) * trace F K (y : K) / (gammaF : F))
  let B : ℂˣ := psiF.character
    ((R.cF : F) * norm F K (y : K) / (gammaF : F))
  have hprod : A * B = 1 := by
    simpa only [A, B] using hlinear'.symm
  have hB : B = A⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hneg := AddChar.map_neg_eq_inv psiF.character.toAddChar
    ((R.cF : F) * trace F K (y : K) / (gammaF : F))
  change psiF.character
      (-((R.cF : F) * trace F K (y : K) / (gammaF : F))) =
    (psiF.character
      ((R.cF : F) * trace F K (y : K) / (gammaF : F)))⁻¹ at hneg
  simpa only [A, B] using hB.trans hneg.symm

/-- The selected sum `beta+cF` represents the stationary coefficient class
of the actual twist.  This is an equality in `O_F / p_F^d`. -/
theorem twist_class
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF) :
    let hTw := wildQuadraticHighTwistDecomposition
      F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau
    let hgammaTw := highParameter_wildQuadratic_twistDenominator
      F K ht hres pi hpi hgen chiF psiF hminimal hhigh tau htau
        gammaF hgammaF
    latticeQuotientMk F (by omega)
        (⟨R.betaTwist, R.betaTwist_integral⟩ : lattice F 0) =
      stationaryCoefficientClass F
        (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau)
        psiF hTw gammaF hgammaTw := by
  dsimp only
  apply (latticeQuotientMk_eq_stationaryCoefficientClass_iff F
    (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau)
    psiF (wildQuadraticHighTwistDecomposition
      F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau)
    gammaF
    (highParameter_wildQuadratic_twistDenominator
      F K ht hres pi hpi hgen chiF psiF hminimal hhigh tau htau
        gammaF hgammaF)
    ⟨R.betaTwist, R.betaTwist_integral⟩).2
  intro x
  have hbeta :=
    (latticeQuotientMk_eq_stationaryCoefficientClass_iff F chiF psiF
      hF gammaF hgammaF ⟨(R.beta : F), R.beta_integral⟩).1
      R.beta_class x
  have hcommon : wildQuadraticHighStationaryDepth t ≤ d + epsilon := by
    have he := hF.epsilon_le_one
    rw [hF.conductor_eq] at hhigh
    simp only [wildQuadraticHighStationaryDepth]
    omega
  let xs : lattice F (wildQuadraticHighStationaryDepth t : ℤ) :=
    ⟨(x : F), lattice_antitone F (by exact_mod_cast hcommon) x.property⟩
  let hr := wildQuadraticHigh_stationaryDepth htpos
  let cTau : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
    ⟨(R.cF : F), by simpa only [cF, alpha, Units.val_mul,
      coe_normUnits, mul_comm] using R.tau_integral⟩
  have hcTau : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cTau =
      stationaryNumeratorClass F
        (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
        (chiF.conductor : ℤ) hr gammaF hgammaF := by
    simpa only [cTau, cF, alpha, Units.val_mul, coe_normUnits, mul_comm, hr]
      using R.tau_class
  have htauLinear := stationaryNumeratorClass_linearization F
    (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
      (chiF.conductor : ℤ) hr gammaF hgammaF cTau hcTau xs
  have htauLinear' :
      tau.1 (positiveUnitOfLattice F hr.pos xs : Fˣ) =
        psiF.character ((R.cF : F) * (xs : F) / (gammaF : F)) := by
    simpa only [wildQuadraticHighTauData,
      quasiCharDataOfIsConductor_character, cTau] using htauLinear
  have hunit :
      (positiveUnitOfLattice F hr.pos xs : Fˣ) =
        (positiveUnitOfLattice F
          (wildQuadraticHighTwistDecomposition
            F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau).variableDepth_pos
          x : Fˣ) := by
    apply Units.ext
    simp only [coe_positiveUnitOfLattice, xs]
  rw [wildQuadraticHighTwistData_character,
    ContinuousQuasiChar.mul_apply, ← hunit, htauLinear', hunit, hbeta]
  rw [← psiF.character.map_add_eq_mul]
  congr 1
  simp only [betaTwist, xs]
  ring

/-- The selected field element `betaK` represents the actual upstairs
stationary coefficient class.  The proof evaluates the exact quadratic
truncated norm and uses the conversion theorem above. -/
theorem upstairs_class
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    {dK epsilonK : ℕ}
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    let gammaK := Units.map (algebraMap F K) gammaF
    let hgammaK := highParameter_wildQuadratic_commonDenominator
      F K ht hres pi hpi hgen hdegree chiF chiK psiF psiK
        hminimal hchi hpsi hhigh gammaF hgammaF
    latticeQuotientMk K (by omega)
        (⟨R.betaK, R.betaK_integral hdegree⟩ : lattice K 0) =
      stationaryCoefficientClass K chiK psiK hK gammaK hgammaK := by
  dsimp only
  let precision := highParameter_wildQuadratic_precision
    F K ht hres pi hpi hgen hdegree htpos chiF chiK hF hK
      hminimal hchi hhigh
  let gammaK : Kˣ := Units.map (algebraMap F K) gammaF
  let hgammaK := highParameter_wildQuadratic_commonDenominator
    F K ht hres pi hpi hgen hdegree chiF chiK psiF psiK
      hminimal hchi hpsi hhigh gammaF hgammaF
  apply (latticeQuotientMk_eq_stationaryCoefficientClass_iff K chiK psiK
    hK gammaK hgammaK ⟨R.betaK, R.betaK_integral hdegree⟩).2
  intro x
  let px := normPolynomialRepresentative F K precision x
  have hbeta :=
    (latticeQuotientMk_eq_stationaryCoefficientClass_iff F chiF psiF
      hF gammaF hgammaF ⟨(R.beta : F), R.beta_integral⟩).1
      R.beta_class px
  have hnormUnit :
      normUnits F K
          (positiveUnitOfLattice K hK.variableDepth_pos x : Kˣ) =
        (positiveUnitOfLattice F hF.variableDepth_pos px : Fˣ) := by
    apply Units.ext
    simp [px, normPolynomialRepresentative]
  have hsource :
      chiK.character (positiveUnitOfLattice K hK.variableDepth_pos x) =
        psiF.character
          ((R.beta : F) * normPolynomialValue F K (x : K) /
            (gammaF : F)) := by
    rw [hchi, ContinuousQuasiChar.compNorm_apply, hnormUnit, hbeta]
    rfl
  have hrel := highParameter_wildQuadratic_conductor_relation
    F K ht hres pi hpi hgen hdegree chiF chiK hminimal hchi hhigh
  obtain ⟨_, _, hqK, _, _, _, _, _, _, _, _⟩ :=
    wildQuadraticHigh_depth_relations htpos hhigh hF hK hrel
  let y0 : K := (R.u : K) * (x : K)
  have hy0 : y0 ∈ lattice K (wildQuadraticHighStationaryDepth t : ℤ) := by
    rw [mem_lattice]
    change _ ≤ ord K ((R.u : K) * (x : K))
    rw [ord_mul, R.u_order]
    have hx := x.property
    rw [mem_lattice] at hx
    have hdepth :
        (((wildQuadraticHighStationaryDepth t : ℕ) : ℤ) : WithTop ℤ) =
          ((((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) :
              WithTop ℤ) +
            (((dK + epsilonK : ℕ) : ℤ) : WithTop ℤ) := by
      congr 1
      simp only [wildQuadraticHighStationaryDepth,
        wildQuadraticHighShift] at hqK ⊢
      omega
    rw [hdepth]
    simpa only [add_comm] using add_le_add_left hx
      ((((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) : WithTop ℤ)
  let y : lattice K (wildQuadraticHighStationaryDepth t : ℤ) := ⟨y0, hy0⟩
  have hconvert := R.conversion hdegree y
  have hnormu := congrArg Units.val R.norm_u_eq_n
  change norm F K (R.u : K) = (R.n : F) at hnormu
  have hnormy : norm F K (y : K) =
      (R.n : F) * norm F K (x : K) := by
    change norm F K ((R.u : K) * (x : K)) = _
    rw [map_mul, hnormu]
  have hbetaFactor := congrArg Units.val R.cF_mul_n
  change (R.cF : F) * (R.n : F) = (R.beta : F) at hbetaFactor
  have hbetaNorm :
      (R.beta : F) * norm F K (x : K) =
        (R.cF : F) * norm F K (y : K) := by
    rw [hnormy, ← hbetaFactor]
    ring
  have hphase :
      psiF.character
          ((R.beta : F) * normPolynomialValue F K (x : K) /
            (gammaF : F)) =
        psiF.character
          (((R.beta : F) * trace F K (x : K) -
              (R.cF : F) * trace F K (y : K)) / (gammaF : F)) := by
    rw [wildQuadratic_normPolynomialValue_eq_trace_add_norm F K hdegree]
    have hsplit :
        (R.beta : F) * (trace F K (x : K) + norm F K (x : K)) /
            (gammaF : F) =
          (R.beta : F) * trace F K (x : K) / (gammaF : F) +
            (R.beta : F) * norm F K (x : K) / (gammaF : F) := by ring
    rw [hsplit, psiF.character.map_add_eq_mul, hbetaNorm, hconvert,
      ← psiF.character.map_add_eq_mul]
    congr 1
    ring
  have hbetaKForm :
      R.betaK = algebraMap F K (R.beta : F) -
        algebraMap F K (R.cF : F) * (R.u : K) := by
    rw [betaK, u, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero R.alpha1]
  have htraceBeta := trace_denominatorScaled_div F K gammaF gammaK
    (R.beta : F) (x : K)
  have htraceCorrection := trace_denominatorScaled_div F K gammaF gammaK
    (R.cF : F) ((R.u : K) * (x : K))
  have hratio : normPolynomialDenominatorRatio F K gammaF gammaK = 1 := by
    simp [gammaK, normPolynomialDenominatorRatio]
  rw [hratio, one_mul] at htraceBeta htraceCorrection
  have htraceK :
      trace F K (R.betaK * (x : K) / (gammaK : K)) =
        ((R.beta : F) * trace F K (x : K) -
          (R.cF : F) * trace F K (y : K)) / (gammaF : F) := by
    rw [hbetaKForm]
    have harg :
        (algebraMap F K (R.beta : F) -
            algebraMap F K (R.cF : F) * (R.u : K)) * (x : K) /
            (gammaK : K) =
          algebraMap F K (R.beta : F) * (x : K) / (gammaK : K) -
            algebraMap F K (R.cF : F) * ((R.u : K) * (x : K)) /
              (gammaK : K) := by ring
    rw [harg, map_sub, htraceBeta, htraceCorrection]
    change _ = ((R.beta : F) * trace F K (x : K) -
      (R.cF : F) * trace F K y0) / (gammaF : F)
    ring
  rw [hsource, hphase, hpsi, ContinuousAddChar.compTrace_apply, htraceK]

/-- The denominator-sensitive adjoint identity for the actual conductor and
ordered common-denominator pair. -/
theorem upstairs_adjoint
    (_R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    {dK epsilonK : ℕ}
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    let precision := highParameter_wildQuadratic_precision
      F K ht hres pi hpi hgen hdegree htpos chiF chiK hF hK
        hminimal hchi hhigh
    let gammaK := Units.map (algebraMap F K) gammaF
    let hgammaK := highParameter_wildQuadratic_commonDenominator
      F K ht hres pi hpi hgen hdegree chiF chiK psiF psiK
        hminimal hchi hpsi hhigh gammaF hgammaF
    stationaryCoefficientClass K chiK psiK hK gammaK hgammaK =
      normPolynomialAdjoint F K precision psiF psiK gammaF gammaK
        hgammaF hgammaK
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
  simpa only using (stationaryClass_compNorm F K chiF chiK psiF psiK
    (highParameter_wildQuadratic_precision
      F K ht hres pi hpi hgen hdegree htpos chiF chiK hF hK
        hminimal hchi hhigh)
    hchi hpsi gammaF (Units.map (algebraMap F K) gammaF) hgammaF
    (highParameter_wildQuadratic_commonDenominator
      F K ht hres pi hpi hgen hdegree chiF chiK psiF psiK
        hminimal hchi hpsi hhigh gammaF hgammaF))

/-- Combined selected-representative and denominator-sensitive adjoint
identity.  This is still an equality in the upstairs quotient. -/
theorem betaK_adjoint_class
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    {dK epsilonK : ℕ}
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace) :
    let precision := highParameter_wildQuadratic_precision
      F K ht hres pi hpi hgen hdegree htpos chiF chiK hF hK
        hminimal hchi hhigh
    let gammaK := Units.map (algebraMap F K) gammaF
    let hgammaK := highParameter_wildQuadratic_commonDenominator
      F K ht hres pi hpi hgen hdegree chiF chiK psiF psiK
        hminimal hchi hpsi hhigh gammaF hgammaF
    latticeQuotientMk K (by omega)
        (⟨R.betaK, R.betaK_integral hdegree⟩ : lattice K 0) =
      normPolynomialAdjoint F K precision psiF psiK gammaF gammaK
        hgammaF hgammaK
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
  dsimp only
  exact (R.upstairs_class hdegree chiK psiK hK hminimal hchi hpsi).trans
    (R.upstairs_adjoint hdegree chiK psiK hK hminimal hchi hpsi)

/-- At the boundary `m=t+1`, the selected twist numerator does not cancel
in the leading quotient.  The proof is exactly
`minimalOrbit_stationary_representatives`, not a valuation shortcut. -/
theorem boundary_noncancellation
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hcritical : chiF.conductor = t + 1) :
    R.betaTwist ∉ lattice F 1 := by
  let hr := wildQuadraticHigh_stationaryDepth htpos
  have hgammaCritical : ord F (gammaF : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) := by
    simpa only [hcritical] using hgammaF
  have hzeroDepth :
      ((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) = 0 := sub_self _
  let a : lattice F
      (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) := ⟨(R.cF : F), by
    rw [hzeroDepth]
    have ha := R.tau_integral
    rw [hcritical, sub_self] at ha
    simpa only [cF, alpha, Units.val_mul, coe_normUnits, mul_comm] using ha⟩
  let b : lattice F
      (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
    ⟨(R.beta : F), by rw [hzeroDepth]; exact R.beta_integral⟩
  have ha : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor ((t + 1 : ℕ) : ℤ)) a =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor
            F K ht hres pi hpi hgen tau htau))
        psiF ((t + 1 : ℕ) : ℤ) hr gammaF hgammaCritical := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff F
      (quasiCharDataOfIsConductor F tau.1 (t + 1)
        (ramifiedNormCharacter_conductor
          F K ht hres pi hpi hgen tau htau))
      psiF ((t + 1 : ℕ) : ℤ) hr gammaF hgammaCritical a).2
    intro x
    let cTau : lattice F
        ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) :=
      ⟨(R.cF : F), by simpa only [cF, alpha, Units.val_mul,
        coe_normUnits, mul_comm] using R.tau_integral⟩
    have hcTau : latticeQuotientMk F
        (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) cTau =
        stationaryNumeratorClass F
          (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
          (chiF.conductor : ℤ) hr gammaF hgammaF := by
      simpa only [cTau, cF, alpha, Units.val_mul, coe_normUnits,
        mul_comm, hr] using R.tau_class
    have hlinear := stationaryNumeratorClass_linearization F
      (wildQuadraticHighTauData F K ht hres pi hpi hgen tau htau) psiF
      (chiF.conductor : ℤ) hr gammaF hgammaF cTau hcTau x
    simpa only [wildQuadraticHighTauData,
      quasiCharDataOfIsConductor_character, a, cTau] using hlinear
  have hdepth : d + epsilon = wildQuadraticHighStationaryDepth t := by
    have he := hF.epsilon_le_one
    have hFeq := hF.conductor_eq
    rw [hcritical] at hFeq
    simp only [wildQuadraticHighStationaryDepth]
    omega
  have hb : latticeQuotientMk F
      (sub_le_sub_left hr.int_le_conductor ((t + 1 : ℕ) : ℤ)) b =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F chiF.character (t + 1) (by
          simpa only [hcritical] using chiF.isConductor))
        psiF ((t + 1 : ℕ) : ℤ) hr gammaF hgammaCritical := by
    apply (latticeQuotientMk_eq_stationaryNumeratorClass_iff F
      (quasiCharDataOfIsConductor F chiF.character (t + 1) (by
        simpa only [hcritical] using chiF.isConductor))
      psiF ((t + 1 : ℕ) : ℤ) hr gammaF hgammaCritical b).2
    intro x
    let xd : lattice F ((d + epsilon : ℕ) : ℤ) :=
      ⟨(x : F), by rw [hdepth]; exact x.property⟩
    have hbeta :=
      (latticeQuotientMk_eq_stationaryCoefficientClass_iff F chiF psiF
        hF gammaF hgammaF ⟨(R.beta : F), R.beta_integral⟩).1
        R.beta_class xd
    have hunit :
        (positiveUnitOfLattice F hr.pos x : Fˣ) =
          (positiveUnitOfLattice F hF.variableDepth_pos xd : Fˣ) := by
      apply Units.ext
      simp only [coe_positiveUnitOfLattice, xd]
    simpa only [quasiCharDataOfIsConductor_character, hunit, b, xd] using hbeta
  have hnoncancel := minimalOrbit_stationary_representatives
    F K ht hres pi hpi hgen chiF hminimal hcritical tau htau psiF
      ((t + 1 : ℕ) : ℤ) hr gammaF hgammaCritical a b ha hb
  simpa only [a, b, betaTwist, add_comm, sub_self, zero_add] using hnoncancel

/-- The denominator `1+n` used in the quadratic correction is never zero.
At the boundary this invokes `boundary_noncancellation`; away from the
boundary the exact negative order of `n` suffices. -/
theorem one_add_n_ne_zero
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF) :
    (1 : F) + (R.n : F) ≠ 0 := by
  by_cases hcritical : chiF.conductor = t + 1
  · intro hzero
    have htwzero : R.betaTwist = 0 := by
      rw [R.betaTwist_eq_cF_mul_add_one,
        show (R.n : F) + 1 = 0 by simpa only [add_comm] using hzero, mul_zero]
    have hzeroMem : R.betaTwist ∈ lattice F 1 := by
      rw [htwzero]
      exact Submodule.zero_mem _
    exact (R.boundary_noncancellation hminimal hcritical) hzeroMem
  · have hstrict : t + 1 < chiF.conductor :=
      lt_of_le_of_ne hhigh (Ne.symm hcritical)
    intro hzero
    have hn : (R.n : F) = -1 := by
      linear_combination hzero
    have hord := R.n_order
    rw [hn, ord_neg, ord_one] at hord
    have hneg :
        (((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) < 0 := by
      omega
    have hcoeNeg :
        ((((t + 1 : ℕ) : ℤ) - (chiF.conductor : ℤ) : ℤ) : WithTop ℤ) < 0 := by
      exact_mod_cast hneg
    rw [← hord] at hcoeNeg
    exact (lt_irrefl (0 : WithTop ℤ)) hcoeNeg

/-- The correction term has the manuscript trace depth `d`. -/
theorem correction_trace_mem
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    trace F K R.correction ∈ lattice F (d : ℤ) := by
  have hram : ramificationIndex F K = 2 := by
    have hd := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one, hdegree] at hd
    exact hd.symm
  have htrace := trace_mem_lattice_floor F K pi hpi hgen
    (wildQuadraticHighShift t chiF.conductor : ℤ)
    (R.correction_integral hdegree)
  rw [differentExponent_wildQuadratic_eq F K ht hdegree pi hpi hgen,
    hram] at htrace
  have hnat :
      (wildQuadraticHighShift t chiF.conductor + (t + 1)) / 2 = d := by
    have he := hF.epsilon_le_one
    have hFeq := hF.conductor_eq
    simp only [wildQuadraticHighShift]
    omega
  have hdepth :
      (((wildQuadraticHighShift t chiF.conductor : ℕ) : ℤ) +
          ((t + 1 : ℕ) : ℤ)) / (2 : ℤ) = (d : ℤ) := by
    norm_cast
  change trace F K R.correction ∈ lattice F
    ((((wildQuadraticHighShift t chiF.conductor : ℕ) : ℤ) +
      ((t + 1 : ℕ) : ℤ)) / (2 : ℤ)) at htrace
  rwa [hdepth] at htrace

/-- The exact norm of the correction retains the factor `delta`. -/
theorem correction_norm
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    norm F K R.correction = (R.beta : F) * (R.cF : F) := by
  have hcorr : R.correction = algebraMap F K (R.cF : F) * (R.u : K) := by
    rw [correction, u, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero R.alpha1]
  rw [hcorr, map_mul, norm_algebraMap, hdegree]
  have hnormu := congrArg Units.val R.norm_u_eq_n
  change norm F K (R.u : K) = (R.n : F) at hnormu
  rw [hnormu]
  have hfactor := congrArg Units.val R.cF_mul_n
  change (R.cF : F) * (R.n : F) = (R.beta : F) at hfactor
  rw [← hfactor]
  ring

/-- Exact selected-representative form of the quadratic high-product
congruence. -/
theorem norm_betaK_sub_product_mem
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    norm F K R.betaK - (R.beta : F) * R.betaTwist ∈
      lattice F (d : ℤ) := by
  have htraceMul :
      (R.beta : F) * trace F K R.correction ∈ lattice F (d : ℤ) := by
    have hmul := mul_mem_lattice F R.beta_integral
      (R.correction_trace_mem hdegree)
    simpa only [zero_add] using hmul
  have hexact := wildQuadratic_norm_sub F K hdegree R.beta R.correction
  have hbetaK : algebraMap F K (R.beta : F) - R.correction = R.betaK := by
    rfl
  rw [hbetaK, R.correction_norm hdegree] at hexact
  have heq :
      norm F K R.betaK - (R.beta : F) * R.betaTwist =
        -((R.beta : F) * trace F K R.correction) := by
    rw [hexact]
    simp only [betaTwist]
    ring
  rw [heq]
  exact neg_mem_lattice F htraceMul

theorem norm_betaK_integral
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    norm F K R.betaK ∈ lattice F 0 := by
  rw [mem_lattice, ord_norm, hres, one_nsmul]
  exact R.betaK_integral hdegree

theorem beta_mul_betaTwist_integral
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF) :
    (R.beta : F) * R.betaTwist ∈ lattice F 0 := by
  simpa only [zero_add] using
    (mul_mem_lattice F R.beta_integral R.betaTwist_integral)

/-- Quotient-class form of `N(betaK)=beta*(beta+cF) mod p_F^d`. -/
theorem norm_betaK_class
    (R : WildQuadraticHighRepresentatives F K ht hres pi hpi hgen
      chiF psiF hF hhigh htpos tau htau gammaF hgammaF)
    (hdegree : Module.finrank F K = 2) :
    latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨norm F K R.betaK, R.norm_betaK_integral hdegree⟩ : lattice F 0) =
      latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
        (⟨(R.beta : F) * R.betaTwist,
          R.beta_mul_betaTwist_integral⟩ : lattice F 0) := by
  apply (latticeQuotientMk_eq_mk_iff F _).2
  exact R.norm_betaK_sub_product_mem hdegree

end WildQuadraticHighRepresentatives

/-! ## Principal packaged result -/

/-- The complete wild-quadratic high-parameter package.  Its representative
field is existential; the remaining fields certify the actual conductors,
ordered denominator pair, two stationary quotient classes, product quotient,
and the boundary statement for that one simultaneous choice. -/
structure WildQuadraticHighParameterData
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) where
  representatives : WildQuadraticHighRepresentatives
    F K ht hres pi hpi hgen chiF psiF hF hhigh htpos
      tau htau gammaF hgammaF
  conductor_relation : chiK.conductor + (t + 1) = 2 * chiF.conductor
  residueCharacteristic_downstairs : residueCharacteristic F = 2
  residueCharacteristic_upstairs : residueCharacteristic K = 2
  precision : NormPolynomialPrecision F K chiK.conductor dK epsilonK
    chiF.conductor d epsilon
  commonDenominator : ord K
      ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)
  twist_conductor :
    (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau).conductor =
      chiF.conductor
  upstairs_class : latticeQuotientMk K (by omega)
      (⟨representatives.betaK,
        representatives.betaK_integral hdegree⟩ : lattice K 0) =
    stationaryCoefficientClass K chiK psiK hK
      (Units.map (algebraMap F K) gammaF) commonDenominator
  upstairs_adjoint : stationaryCoefficientClass K chiK psiK hK
      (Units.map (algebraMap F K) gammaF) commonDenominator =
    normPolynomialAdjoint F K precision psiF psiK gammaF
      (Units.map (algebraMap F K) gammaF) hgammaF commonDenominator
      (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
  twist_class :
    let hTw := wildQuadraticHighTwistDecomposition
      F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau
    let hgammaTw := highParameter_wildQuadratic_twistDenominator
      F K ht hres pi hpi hgen chiF psiF hminimal hhigh tau htau
        gammaF hgammaF
    latticeQuotientMk F (by omega)
        (⟨representatives.betaTwist,
          representatives.betaTwist_integral⟩ : lattice F 0) =
      stationaryCoefficientClass F
        (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau)
        psiF hTw gammaF hgammaTw
  product_class : latticeQuotientMk F
      (show (0 : ℤ) ≤ (d : ℤ) by omega)
      (⟨norm F K representatives.betaK,
        representatives.norm_betaK_integral hdegree⟩ : lattice F 0) =
    latticeQuotientMk F (show (0 : ℤ) ≤ (d : ℤ) by omega)
      (⟨(representatives.beta : F) * representatives.betaTwist,
        representatives.beta_mul_betaTwist_integral⟩ : lattice F 0)
  correction_trace : trace F K representatives.correction ∈ lattice F (d : ℤ)
  correction_norm : norm F K representatives.correction =
    (representatives.beta : F) * (representatives.cF : F)
  denominator_ne_zero : (1 : F) + (representatives.n : F) ≠ 0
  boundary_noncancellation : chiF.conductor = t + 1 →
    representatives.betaTwist ∉ lattice F 1

/-- **Compatible wild-quadratic high stationary classes and
representatives.**  This is the principal declaration for
`mod:parameters-highquadratic`. -/
theorem highParameter_wildQuadratic
    (hdegree : Module.finrank F K = 2) (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hhigh : t + 1 ≤ chiF.conductor)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    Nonempty (WildQuadraticHighParameterData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) := by
  obtain ⟨R⟩ := highParameter_wildQuadratic_exists_representatives
    F K ht hres pi hpi hgen htpos chiF psiF hF hhigh tau htau gammaF hgammaF
  let hconductor := highParameter_wildQuadratic_conductor_relation
    F K ht hres pi hpi hgen hdegree chiF chiK hminimal hchi hhigh
  let hcharF := highParameter_wildQuadratic_residueCharacteristic
    F K ht pi hpi hgen hdegree htpos
  let hcharK := highParameter_wildQuadratic_residueCharacteristic_upstairs
    F K ht pi hpi hgen hdegree htpos
  let precision := highParameter_wildQuadratic_precision
    F K ht hres pi hpi hgen hdegree htpos chiF chiK hF hK
      hminimal hchi hhigh
  let hgammaK := highParameter_wildQuadratic_commonDenominator
    F K ht hres pi hpi hgen hdegree chiF chiK psiF psiK
      hminimal hchi hpsi hhigh gammaF hgammaF
  let htwist := highParameter_wildQuadratic_twist_conductor
    F K ht hres pi hpi hgen chiF hminimal hhigh tau htau
  refine ⟨⟨R, hconductor, hcharF, hcharK, precision, hgammaK, htwist,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact R.upstairs_class hdegree chiK psiK hK hminimal hchi hpsi
  · exact R.upstairs_adjoint hdegree chiK psiK hK hminimal hchi hpsi
  · exact R.twist_class hminimal
  · exact R.norm_betaK_class hdegree
  · exact R.correction_trace_mem hdegree
  · exact R.correction_norm hdegree
  · exact R.one_add_n_ne_zero hminimal
  · exact R.boundary_noncancellation hminimal

end

/-! ## Characteristic-two normalization retained downstream -/

/-- The wild-quadratic node does not choose a quadratic refinement.  For
every explicitly supplied normalized refinement, it records both the
positive polar sign and the Frobenius normalization required downstream. -/
theorem highParameter_wildQuadratic_charTwoNormalization
    {k : Type*} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) :
    (∀ x y : k,
      q (x + y) = q x * q y * absoluteTraceChar k (x * y)) ∧
      ∀ x : k, q (x ^ 2) = q x := by
  exact ⟨q.map_add, q.map_sq⟩

end LanglandsFirstMainLemma
