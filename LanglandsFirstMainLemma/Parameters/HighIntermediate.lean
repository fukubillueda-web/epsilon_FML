import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Ramification.NormRepresentatives
import LanglandsFirstMainLemma.Ramification.NormCharacters

/-!
# High stationary parameters in the odd non-stable range

This is the range `T = t + 1 <= m <= 2*T - 1` of Proposition
`prop:high-parameter-table`, part (c).  The critical endpoint `m = T` is
included.  All stationary parameters below are literal lattice-quotient
classes.  Field elements occur only as supplied or existentially chosen
representatives; no distinguished representative is defined.

The ordered denominator pair is always retained.  In particular, the
adjoint in the main result is the adjoint for
`(gammaF, algebraMap F K gammaF)`, not a denominator-free map.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

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

/-! ## Actual conductors and the common denominator -/

/-- The actual norm-pullback conductor in the whole-orbit-minimal
intermediate range.  This subtraction-free form includes the critical
boundary `m = t+1`; there it is the no-leading-cancellation theorem, not
the strict above-break formula, that supplies the equality. -/
theorem highParameter_intermediate_conductor_relation
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hm : t + 1 ≤ chiF.conductor) :
    chiK.conductor +
        (Module.finrank F K - 1) * (t + 1) =
      Module.finrank F K * chiF.conductor := by
  have hz := minimalOrbit_compNorm_conductor_eq_atOrAboveCritical
    F K ht hres pi hpi hgen chiF hminimal chiK hchi hm
  have hz' :
      (chiK.conductor : ℤ) +
          (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) =
        (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) := by
    rw [hz]
    ring
  exact_mod_cast hz'

/-- Every member of the complete downstairs norm-character orbit has its
actual conductor computed.  In the intermediate range it is exactly the
conductor of the chosen minimal representative, including for the identity
member and at the critical boundary. -/
theorem highParameter_intermediate_twist_conductor_eq
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hm : t + 1 ≤ chiF.conductor)
    (mu : NormCharacter F K) :
    (ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu).conductor = chiF.conductor := by
  rw [ramifiedNormCharacterOrbitTwistData_conductor_eq_ite
    F K ht hres pi hpi hgen chiF hminimal mu]
  classical
  simp only [minimalOrbitTwistConductor]
  split_ifs
  · rfl
  · exact Nat.max_eq_left hm

/-- Total ramification keeps the ramification factor visible: `e=[K:F]`
and, separately, the hypothesis says `f=1`. -/
theorem highParameter_intermediate_ramificationIndex_eq_degree :
    ramificationIndex F K = Module.finrank F K := by
  have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
  rw [hres, mul_one] at hdegree
  exact hdegree.symm

/-- A downstairs denominator of order `m_F+n_F` is an upstairs denominator
of order `m_K+n_K` after embedding.  The proof uses the exact ordered pair,
`e=[K:F]`, `f=1`, the multiplicative correction `-([K:F]-1)T`, and the
additive correction with the opposite sign. -/
theorem highParameter_intermediate_commonDenominator
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : t + 1 ≤ chiF.conductor)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ) := by
  have hsum := minimalOrbit_compNorm_add_compTrace_conductor_eq
    F K ht hres pi hpi hgen chiF hminimal chiK psiF psiK hchi hpsi hm
  have hram := highParameter_intermediate_ramificationIndex_eq_degree
    F K ht hres pi hpi hgen
  change ord K (algebraMap F K (gammaF : F)) = _
  rw [ord_algebraMap, hram, hgammaF, ← WithTop.coe_nsmul]
  change (((Module.finrank F K : ℤ) *
      ((chiF.conductor : ℤ) + psiF.conductor) : ℤ) : WithTop ℤ) = _
  rw [← hsum]

/-! ## Exact intermediate depths -/

/-- Subtraction-free endpoint/high formula `mK=T+p*(m-T)`. -/
theorem highParameter_intermediate_conductor_eq
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hm : t + 1 ≤ chiF.conductor) :
    chiK.conductor = t + 1 +
      Module.finrank F K * (chiF.conductor - (t + 1)) := by
  have hz := minimalOrbit_compNorm_conductor_eq_atOrAboveCritical
    F K ht hres pi hpi hgen chiF hminimal chiK hchi hm
  have hpone : 1 ≤ Module.finrank F K := Module.finrank_pos
  have hz' :
      (chiK.conductor : ℤ) =
        ((t + 1 + Module.finrank F K *
          (chiF.conductor - (t + 1)) : ℕ) : ℤ) := by
    rw [hz]
    push_cast [Nat.cast_sub hpone, Nat.cast_sub hm]
    ring
  exact_mod_cast hz'

/-- The actual conductor is also the exact Herbrand successor, including
the minimal critical endpoint. -/
theorem highParameter_intermediate_conductor_eq_herbrand
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hm : t + 1 ≤ chiF.conductor) :
    chiK.conductor =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1 := by
  have hmK := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hm
  rw [herbrandPsiNat_of_break_le t (Module.finrank F K) (by omega)]
  have hsub : chiF.conductor - 1 - t =
      chiF.conductor - (t + 1) := by omega
  rw [hsub, hmK]
  omega

/-- The natural-number arithmetic used by every precision and valuation
argument in the intermediate row. -/
structure HighIntermediateDepthArithmetic
    (p T m d epsilon mK dK epsilonK : ℕ) : Prop where
  conductor_relation : mK + (p - 1) * T = p * m
  conductor_eq : mK = T + p * (m - T)
  epsilon_eq : epsilonK = epsilon
  variableDepth_le : d + epsilon ≤ dK + epsilonK
  floorDepth_le : d ≤ dK
  floorDepth_le_break : d ≤ T - 1
  halfBreak_le_break : T / 2 ≤ T - 1
  shiftedVariableDepth : m - T + (T + 1) / 2 ≤ dK + epsilonK
  nonlinear_vanishing_bound :
    p * m ≤ 2 * (dK + epsilonK) + (p - 1) * T

/-- Exact subtraction-free depth calculation for
`T <= m < 2*T`. -/
theorem highParameter_intermediate_depthArithmetic
    {p T m d epsilon mK dK epsilonK : ℕ}
    (hodd : Odd p) (hpThree : 3 ≤ p) (hT : 2 ≤ T)
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hK : IsStationaryConductorDecomposition mK dK epsilonK)
    (hlower : T ≤ m) (hupper : m < 2 * T)
    (hmrel : mK + (p - 1) * T = p * m)
    (hmK : mK = T + p * (m - T)) :
    HighIntermediateDepthArithmetic p T m d epsilon mK dK epsilonK := by
  rcases hodd with ⟨k, hk⟩
  have hkpos : 1 ≤ k := by omega
  let z : ℕ := k * (m - T)
  have hmSplit : m = T + (m - T) := (Nat.add_sub_of_le hlower).symm
  have hmKform : mK = m + 2 * z := by
    calc
      mK = T + p * (m - T) := hmK
      _ = T + (2 * k + 1) * (m - T) := by rw [hk]
      _ = (T + (m - T)) + 2 * (k * (m - T)) := by ring
      _ = m + 2 * z := by rw [← hmSplit]
  have hepsilon_le := hF.epsilon_le_one
  have hepsilonK_le := hK.epsilon_le_one
  have hepsilon : epsilonK = epsilon := by
    rw [hK.conductor_eq, hF.conductor_eq] at hmKform
    omega
  have hdK : dK = d + z := by
    rw [hK.conductor_eq, hF.conductor_eq, hepsilon] at hmKform
    omega
  have hdBreak : d ≤ T - 1 := by
    rw [hF.conductor_eq] at hupper
    omega
  have hhalfBreak : T / 2 ≤ T - 1 := by omega
  have hshifted : m - T + (T + 1) / 2 ≤ dK + epsilonK := by
    have hqF : (T + 1) / 2 ≤ d + epsilon := by
      rw [hF.conductor_eq] at hlower
      omega
    have hvMul : m - T ≤ k * (m - T) := by
      calc
        m - T = 1 * (m - T) := by simp
        _ ≤ k * (m - T) := Nat.mul_le_mul_right (m - T) hkpos
    dsimp only [z] at hdK
    rw [hdK, hepsilon]
    omega
  have hnonlinear :
      p * m ≤ 2 * (dK + epsilonK) + (p - 1) * T := by
    rw [← hmrel, hK.conductor_eq]
    omega
  exact
    { conductor_relation := hmrel
      conductor_eq := hmK
      epsilon_eq := hepsilon
      variableDepth_le := by rw [hdK, hepsilon]; omega
      floorDepth_le := by rw [hdK]; omega
      floorDepth_le_break := hdBreak
      halfBreak_le_break := hhalfBreak
      shiftedVariableDepth := hshifted
      nonlinear_vanishing_bound := hnonlinear }

/-- Herbrand's half inequality gives the exact source depth needed for the
stationary-variable filtration inclusion. -/
theorem highParameter_intermediate_variableSource_le
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hmK : chiK.conductor =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1) :
    herbrandPsiNat t (Module.finrank F K) (d + epsilon - 1) + 1 ≤
      dK + epsilonK := by
  have hepsilon := hF.epsilon_le_one
  have hlast : (chiF.conductor - 1) / 2 = d + epsilon - 1 := by
    rw [hF.conductor_eq]
    omega
  have hhalf := herbrandPsiNat_half_le_half t
    (Module.finrank F K) Module.finrank_pos (chiF.conductor - 1)
  rw [hlast] at hhalf
  rw [hK.conductor_eq] at hmK
  omega

/-- The exact three norm-filtration inclusions in the intermediate row.
The variable and ambiguity source depths remain on or below `t`; only the
actual conductor uses the above-break Herbrand formula. -/
theorem highParameter_intermediate_precision
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1)) :
    NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor d epsilon := by
  have hmrel := highParameter_intermediate_conductor_relation
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
  have hmK := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
  have harith := highParameter_intermediate_depthArithmetic
    F K ht hres pi hpi hgen
    (p := Module.finrank F K) (T := t + 1)
    hodd (by
      have hpTwo := (PrimeCyclicExtension.degree_prime F K).two_le
      by_contra hnot
      have hpEq : Module.finrank F K = 2 := by omega
      rw [hpEq] at hodd
      norm_num at hodd) (by omega) hF hK hlower hupper hmrel hmK
  have hmHerbrand := highParameter_intermediate_conductor_eq_herbrand
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
  have hdt : d ≤ t := by simpa only [Nat.add_sub_cancel] using
    harith.floorDepth_le_break
  exact
    { sourceDecomposition := hK
      targetDecomposition := hF
      variable_inclusion := by
        have hsource := highParameter_intermediate_variableSource_le
          F K ht hres pi hpi hgen chiF chiK hF hK hmHerbrand
        have hmap := normMapsUnitFiltration_herbrand_succ
          F K ht hres pi hpi hgen (d + epsilon - 1)
        intro u hu
        have hu' := unitFiltration_antitone K hsource hu
        have hout := hmap u hu'
        have htarget : d + epsilon - 1 + 1 = d + epsilon := by
          have := hF.variableDepth_pos
          omega
        simpa only [htarget] using hout
      conductor_inclusion := by
        have hmap := normMapsUnitFiltration_herbrand_succ
          F K ht hres pi hpi hgen (chiF.conductor - 1)
        intro u hu
        have hu' : u ∈ unitFiltration K
            (herbrandPsiNat t (Module.finrank F K)
              (chiF.conductor - 1) + 1) := by
          rw [← hmHerbrand]
          exact hu
        have hout := hmap u hu'
        have htarget : chiF.conductor - 1 + 1 = chiF.conductor := by
          have := hF.conductor_gt_one
          omega
        simpa only [htarget] using hout
      ambiguity_inclusion := by
        have hmap := normMapsUnitFiltration_belowBreak
          F K ht hdt hres pi hpi hgen
        intro u hu
        exact hmap u (unitFiltration_antitone K harith.floorDepth_le hu) }

/-- Every nonterminal elementary-symmetric coefficient vanishes at the
exact downstairs conductor precision.  The estimate is the manuscript's
`2*q_K + (p-1)T >= p*m`; it is not a stable-range trace replacement. -/
theorem highParameter_intermediate_intermediateTerms
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1)) :
    NormPolynomialIntermediateTermsVanishAt F K
      (dK + epsilonK) chiF.conductor := by
  have hmrel := highParameter_intermediate_conductor_relation
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
  have hmK := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
  have harith := highParameter_intermediate_depthArithmetic
    F K ht hres pi hpi hgen
    (p := Module.finrank F K) (T := t + 1)
    hodd (by
      have hpTwo := (PrimeCyclicExtension.degree_prime F K).two_le
      by_contra hnot
      have hpEq : Module.finrank F K = 2 := by omega
      rw [hpEq] at hodd
      norm_num at hodd) (by omega) hF hK hlower hupper hmrel hmK
  have hchar := residueCharacteristic_eq_degree_of_positive_break
    F K ht htpos pi hpi hgen
  exact wild_normPolynomialIntermediateTermsVanishAt F K
    (Module.finrank F K) (t + 1) (dK + epsilonK) chiF.conductor
    (PrimeCyclicExtension.degree_prime F K) (by omega) hchar rfl
    (traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen)
    harith.nonlinear_vanishing_bound

omit ht hres pi hpi hgen in
/-- Exact valuation inequality for every mixed term in
`N(beta1+[j]*alpha1)`.  It is valid throughout the inclusive range
`T ≤ m = T+v < 2T`. -/
theorem highParameter_intermediate_twistCrossTermBound
    (p T m d epsilon v : ℕ)
    (hp : 2 ≤ p)
    (hF : m = 2 * d + epsilon)
    (hm : m = T + v)
    (hvT : v ≤ T) :
    ∀ i : ℕ, 1 ≤ i → i < p →
      p * d ≤ i * v + (p - 1) * T := by
  have hpz : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hvz : (v : ℤ) ≤ (T : ℤ) := by exact_mod_cast hvT
  have hdecompz : (m : ℤ) = 2 * (d : ℤ) + (epsilon : ℤ) := by
    exact_mod_cast hF
  have hmz : (m : ℤ) = (T : ℤ) + (v : ℤ) := by
    exact_mod_cast hm
  have hbasez : (p : ℤ) * (d : ℤ) ≤
      (v : ℤ) + ((p : ℤ) - 1) * (T : ℤ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpz) (sub_nonneg.mpr hvz)]
  have hbase : p * d ≤ v + (p - 1) * T := by
    have hbasez' : ((p * d : ℕ) : ℤ) ≤
        ((v + (p - 1) * T : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      exact hbasez
    exact_mod_cast hbasez'
  intro i hi _
  calc
    p * d ≤ v + (p - 1) * T := hbase
    _ ≤ i * v + (p - 1) * T := by
      apply Nat.add_le_add_right
      calc
        v = 1 * v := by simp
        _ ≤ i * v := Nat.mul_le_mul_right v hi

/-! ## Norm-to-trace conversion -/

/-- The manuscript's exact norm-to-trace conversion.  The trace points from
`K` down to `F`; the denominator is the supplied `gammaF`, with exact order
`(T+v)+n(psiF)`.  The proof uses `f=1` in `ord_F(N(y))=ord_K(y)` and the
trace-ideal denominator `e=[K:F]`.  The coefficient is literally the norm
of the independently supplied `alpha1`; it is not a canonical stationary
representative. -/
theorem highParameter_intermediate_normCharacterConversion
    {v : ℕ}
    (htpos : 0 < t)
    (psiF : LocalAddCharData F)
    (tau : NormCharacter F K)
    (alpha1 : Kˣ)
    (halpha : ord F (norm F K (alpha1 : K)) =
      (((v : ℕ) : ℤ) : WithTop ℤ))
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((t + 1 : ℕ) : ℤ) + (v : ℤ) + psiF.conductor : WithTop ℤ))
    (hlinear : ∀ x : lattice F (((t + 2) / 2 : ℕ) : ℤ),
      tau.1 (positiveUnitOfLattice F (by omega : 0 < (t + 2) / 2) x) =
        psiF.character
          (norm F K (alpha1 : K) * (x : F) / (gammaF : F)))
    (y : lattice K (((t + 2) / 2 : ℕ) : ℤ)) :
    psiF.character
        (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) =
      psiF.character
        ((-(norm F K (alpha1 : K))) * trace F K (y : K) /
          (gammaF : F)) := by
  let p := Module.finrank F K
  let T := t + 1
  let s0 := (t + 2) / 2
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hp2 : 2 ≤ p := hp.two_le
  have hT2 : 2 ≤ T := by omega
  have hs0pos : 0 < s0 := by
    dsimp [s0]
    omega
  have hs0T : s0 ≤ T := by
    dsimp [s0, T]
    omega
  have hTtwoS0 : T ≤ 2 * s0 := by
    dsimp [s0, T]
    omega
  have hchar : residueCharacteristic F = p := by
    simpa [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  have htraceLower :
      TraceIdealLowerBound F K p (((p - 1) * T : ℕ) : ℤ) := by
    simpa [p, T] using
      traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have hnonlinearBound : p * T ≤ 2 * s0 + (p - 1) * T := by
    have hpdecomp : p = 1 + (p - 1) := by omega
    calc
      p * T = T + (p - 1) * T := by
        rw [hpdecomp, add_mul, one_mul, Nat.add_sub_cancel_left]
      _ ≤ 2 * s0 + (p - 1) * T :=
        Nat.add_le_add_right hTtwoS0 ((p - 1) * T)
  have hintermediate :
      NormPolynomialIntermediateTermsVanishAt F K s0 T := by
    exact wild_normPolynomialIntermediateTermsVanishAt F K p T s0 T
      hp hT2 hchar rfl htraceLower hnonlinearBound
  have hrem :
      normPolynomialValue F K (y : K) -
          (trace F K (y : K) + norm F K (y : K)) ∈
        lattice F (T : ℤ) := by
    exact normPolynomialValue_sub_trace_add_norm_mem F K hp2
      hintermediate (y : K) y.property
  have htraceFloor :
      (s0 : ℤ) ≤
        (((s0 : ℤ) + (((p - 1) * T : ℕ) : ℤ)) / (p : ℤ)) := by
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
    have hpdecomp : p = 1 + (p - 1) := by omega
    have hnat : p * s0 ≤ s0 + (p - 1) * T := by
      calc
        p * s0 = s0 + (p - 1) * s0 := by
          rw [hpdecomp, add_mul, one_mul, Nat.add_sub_cancel_left]
        _ ≤ s0 + (p - 1) * T :=
          Nat.add_le_add_left (Nat.mul_le_mul_left (p - 1) hs0T) s0
    simpa [mul_comm] using (show
      (p * s0 : ℤ) ≤ (s0 + (p - 1) * T : ℕ) by exact_mod_cast hnat)
  have htrace : trace F K (y : K) ∈ lattice F (s0 : ℤ) := by
    rw [mem_lattice]
    exact (WithTop.coe_le_coe.mpr htraceFloor).trans
      (htraceLower (s0 : ℤ) (y : K) y.property)
  have hnorm : norm F K (y : K) ∈ lattice F (s0 : ℤ) := by
    rw [mem_lattice, ord_norm, hres, one_nsmul]
    exact y.property
  have hsum : trace F K (y : K) + norm F K (y : K) ∈
      lattice F (s0 : ℤ) :=
    add_mem_lattice F htrace hnorm
  have hremAtS0 :
      normPolynomialValue F K (y : K) -
          (trace F K (y : K) + norm F K (y : K)) ∈
        lattice F (s0 : ℤ) :=
    lattice_antitone F (by exact_mod_cast hs0T) hrem
  have hpoly : normPolynomialValue F K (y : K) ∈ lattice F (s0 : ℤ) := by
    have hadd := add_mem_lattice F hremAtS0 hsum
    convert hadd using 1
    ring
  let ypoly : lattice F (s0 : ℤ) :=
    ⟨normPolynomialValue F K (y : K), hpoly⟩
  have hunit :
      (positiveUnitOfLattice F hs0pos ypoly : Fˣ) =
        normUnits F K (positiveUnitOfLattice K hs0pos y : Kˣ) := by
    apply Units.ext
    simp [ypoly, normPolynomialValue]
  have hnormChar : tau.1 (positiveUnitOfLattice F hs0pos ypoly) = 1 := by
    rw [hunit]
    exact tau.eq_one_on_normRange F K _ ⟨_, rfl⟩
  have hpsiPoly :
      psiF.character
        (norm F K (alpha1 : K) * normPolynomialValue F K (y : K) /
          (gammaF : F)) = 1 := by
    have h := hlinear ypoly
    change tau.1 (positiveUnitOfLattice F hs0pos ypoly) = _ at h
    rw [hnormChar] at h
    exact h.symm
  have halphaLat : norm F K (alpha1 : K) ∈ lattice F (v : ℤ) := by
    rw [mem_lattice, halpha]
  have hscaledRem :
      norm F K (alpha1 : K) *
            (normPolynomialValue F K (y : K) -
              (trace F K (y : K) + norm F K (y : K))) /
          (gammaF : F) ∈ lattice F (-psiF.conductor) := by
    apply (div_mem_lattice_iff F (gammaF : F)
      (norm F K (alpha1 : K) *
        (normPolynomialValue F K (y : K) -
          (trace F K (y : K) + norm F K (y : K))))
      (((T : ℕ) : ℤ) + (v : ℤ) + psiF.conductor)
      (-psiF.conductor) (by simpa [T] using hgammaF)).2
    have hmul := mul_mem_lattice F halphaLat hrem
    simpa [add_comm, add_left_comm, add_assoc] using hmul
  have hpsiRem :
      psiF.character
        (norm F K (alpha1 : K) *
            (normPolynomialValue F K (y : K) -
              (trace F K (y : K) + norm F K (y : K))) /
          (gammaF : F)) = 1 :=
    psiF.isConductor.trivial _ hscaledRem
  have hpsiSum :
      psiF.character
        (norm F K (alpha1 : K) *
            (trace F K (y : K) + norm F K (y : K)) /
          (gammaF : F)) = 1 := by
    have hsplit :
        norm F K (alpha1 : K) * normPolynomialValue F K (y : K) /
            (gammaF : F) =
          norm F K (alpha1 : K) *
              (trace F K (y : K) + norm F K (y : K)) /
              (gammaF : F) +
            norm F K (alpha1 : K) *
              (normPolynomialValue F K (y : K) -
                (trace F K (y : K) + norm F K (y : K))) /
              (gammaF : F) := by ring
    rw [hsplit, psiF.character.map_add_eq_mul, hpsiRem, mul_one] at hpsiPoly
    exact hpsiPoly
  have hpsiSplit :
      psiF.character
          (norm F K (alpha1 : K) * trace F K (y : K) / (gammaF : F)) *
        psiF.character
          (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) = 1 := by
    have hsplit :
        norm F K (alpha1 : K) *
            (trace F K (y : K) + norm F K (y : K)) /
            (gammaF : F) =
          norm F K (alpha1 : K) * trace F K (y : K) / (gammaF : F) +
            norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F) := by
      ring
    rw [hsplit, psiF.character.map_add_eq_mul] at hpsiSum
    exact hpsiSum
  have hinv :
      psiF.character
          (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) =
        (psiF.character
          (norm F K (alpha1 : K) * trace F K (y : K) / (gammaF : F)))⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hpsiSplit
  rw [hinv]
  let a : F :=
    norm F K (alpha1 : K) * trace F K (y : K) / (gammaF : F)
  let b : F :=
    (-(norm F K (alpha1 : K))) * trace F K (y : K) / (gammaF : F)
  have hab : -a = b := by
    dsimp [a, b]
    ring
  change (psiF.character.toAddChar a)⁻¹ = psiF.character.toAddChar b
  rw [← hab]
  exact (AddChar.map_neg_eq_inv psiF.character.toAddChar a).symm

/-- Replacing the selected norm-character coefficient by the exact norm of
`alpha1` changes nothing on the common stationary layer.  The proof uses
only the permitted precision `r0=(t+1)/2` and the exact identity
`r0+s0=t+1`. -/
theorem highParameter_intermediate_selectedAlpha_linearization
    {v : ℕ}
    (htpos : 0 < t)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (hm : chiF.conductor = t + 1 + v)
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (a : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (alpha : Fˣ) (hacoe : (a : F) = (alpha : F))
    (alpha1 : Kˣ)
    (halpha1 : IsSubcriticalNormRepresentative F K
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
      ((t + 1) / 2) alpha alpha1)
    (ha : latticeQuotientMk F
        (sub_le_sub_left
          (show (((t + 2) / 2 : ℕ) : ℤ) ≤ (t + 1 : ℕ) by omega)
          (chiF.conductor : ℤ)) a =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor
            F K ht hres pi hpi hgen tau htau))
        psiF (chiF.conductor : ℤ)
        (show IsLamprechtStationaryDepth (t + 1) ((t + 2) / 2) by
          constructor <;> omega)
        gammaF hgammaF) :
    ∀ x : lattice F (((t + 2) / 2 : ℕ) : ℤ),
      tau.1 (positiveUnitOfLattice F (by omega : 0 < (t + 2) / 2) x) =
        psiF.character
          (norm F K (alpha1 : K) * (x : F) / (gammaF : F)) := by
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let hr : IsLamprechtStationaryDepth (t + 1) ((t + 2) / 2) := by
    constructor <;> omega
  intro x
  have hlinear := stationaryNumeratorClass_linearization F tauData psiF
    (chiF.conductor : ℤ) hr gammaF hgammaF a (by
      simpa only [tauData, hr] using ha) x
  have hdepthEq :
      (chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) = (v : ℤ) := by
    rw [hm]
    omega
  have hdiff : (a : F) - norm F K (alpha1 : K) ∈
      lattice F ((v + (t + 1) / 2 : ℕ) : ℤ) := by
    rw [hacoe]
    have hlatEq :
        (chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) +
            (((t + 1) / 2 : ℕ) : ℤ) =
          ((v + (t + 1) / 2 : ℕ) : ℤ) := by
      rw [hdepthEq]
      push_cast
      ring
    rw [← hlatEq]
    exact halpha1.norm_congruent
  have hprod :
      ((a : F) - norm F K (alpha1 : K)) * (x : F) ∈
        lattice F ((chiF.conductor : ℕ) : ℤ) := by
    have hmul := mul_mem_lattice F hdiff x.property
    convert hmul using 1
    rw [hm]
    norm_num
    omega
  have hscaled :
      ((a : F) - norm F K (alpha1 : K)) * (x : F) / (gammaF : F) ∈
        lattice F (-psiF.conductor) := by
    apply (div_mem_lattice_iff F (gammaF : F)
      (((a : F) - norm F K (alpha1 : K)) * (x : F))
      ((chiF.conductor : ℤ) + psiF.conductor) (-psiF.conductor)
      hgammaF).2
    simpa [add_assoc] using hprod
  have heval :
      psiF.character ((a : F) * (x : F) / (gammaF : F)) =
        psiF.character
          (norm F K (alpha1 : K) * (x : F) / (gammaF : F)) := by
    apply Units.ext
    apply (div_eq_one_iff_eq (Units.ne_zero _)).1
    have harg :
        (a : F) * (x : F) / (gammaF : F) -
            norm F K (alpha1 : K) * (x : F) / (gammaF : F) =
          ((a : F) - norm F K (alpha1 : K)) * (x : F) /
            (gammaF : F) := by ring
    have hdiv :
        psiF.character ((a : F) * (x : F) / (gammaF : F)) /
          psiF.character
            (norm F K (alpha1 : K) * (x : F) / (gammaF : F)) = 1 := by
      calc
        _ = psiF.character.toAddChar
            ((a : F) * (x : F) / (gammaF : F) -
              norm F K (alpha1 : K) * (x : F) / (gammaF : F)) :=
          (psiF.character.toAddChar.map_sub_eq_div _ _).symm
        _ = 1 := by
          rw [harg]
          exact psiF.isConductor.trivial _ hscaled
    simpa using congrArg Units.val hdiv
  exact hlinear.trans heval

/-- The independently selected `beta1` supplies the literal exact-norm
linearization of `chiF`.  Its ambiguity is only the returned
`IsSubcriticalNormRepresentative` congruence modulo `p_F^d`. -/
theorem highParameter_intermediate_selectedBeta_linearization
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (b : lattice F 0) (beta : Fˣ) (hbcoe : (b : F) = (beta : F))
    (beta1 : Kˣ)
    (hbeta1 : IsSubcriticalNormRepresentative F K 0 d beta beta1)
    (hbclass : latticeQuotientMk F (by omega) b =
      stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) :
    ∀ x : lattice F ((d + epsilon : ℕ) : ℤ),
      chiF.character
          (positiveUnitOfLattice F hF.variableDepth_pos x) =
        psiF.character
          (norm F K (beta1 : K) * (x : F) / (gammaF : F)) := by
  have hbetaNormLat : norm F K (beta1 : K) ∈ lattice F 0 :=
    hbeta1.norm_exactDepth.1
  have h0d : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  let betaNorm : lattice F 0 := ⟨norm F K (beta1 : K), hbetaNormLat⟩
  have hbetaNormClass : latticeQuotientMk F h0d betaNorm =
      stationaryCoefficientClass F chiF psiF hF gammaF hgammaF := by
    calc
      latticeQuotientMk F h0d betaNorm =
          latticeQuotientMk F h0d b := by
        apply (latticeQuotientMk_eq_mk_iff F h0d).2
        change norm F K (beta1 : K) - (b : F) ∈ lattice F (d : ℤ)
        have hneg := neg_mem_lattice F hbeta1.norm_congruent
        rw [hbcoe]
        simpa using hneg
      _ = _ := hbclass
  exact (latticeQuotientMk_eq_stationaryCoefficientClass_iff
    F chiF psiF hF gammaF hgammaF betaNorm).1 hbetaNormClass

omit ht hres pi hpi hgen in
/-- The exact upstairs representative calculation.  For supplied
subcritical choices, the literal quotient class of
`N(beta1) - beta1*N(alpha1)/alpha1` equals both the denominator-sensitive
adjoint and the stationary class at the actual upstairs conductor.  The
conversion hypothesis is precisely the preceding norm-to-trace theorem
instantiated with the selected `alpha1`. -/
theorem highParameter_intermediate_upstairsClass_core
    {v d epsilon dK epsilonK : ℕ}
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hterms : NormPolynomialIntermediateTermsVanishAt F K
      (dK + epsilonK) chiF.conductor)
    (hshift : v + (t + 2) / 2 ≤ dK + epsilonK)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K
      ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
        (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (alpha : Fˣ) (alpha1 : Kˣ)
    (halpha1 : IsSubcriticalNormRepresentative F K (v : ℤ)
      ((t + 1) / 2) alpha alpha1)
    (beta : Fˣ) (beta1 : Kˣ)
    (hbeta1 : IsSubcriticalNormRepresentative F K 0 d beta beta1)
    (b : lattice F 0) (hbcoe : (b : F) = (beta : F))
    (hbclass : latticeQuotientMk F (by omega) b =
      stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF)
    (hconversion : ∀ y : lattice K (((t + 2) / 2 : ℕ) : ℤ),
      psiF.character
          (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) =
        psiF.character
          ((-(norm F K (alpha1 : K))) * trace F K (y : K) /
            (gammaF : F))) :
    ∃ hcandidate :
        algebraMap F K (norm F K (beta1 : K)) -
            (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
              (alpha1 : K) ∈ lattice K 0,
      let candidate : lattice K 0 :=
        ⟨algebraMap F K (norm F K (beta1 : K)) -
            (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
              (alpha1 : K), hcandidate⟩
      latticeQuotientMk K (by omega) candidate =
          normPolynomialAdjoint F K h psiF psiK gammaF
            (Units.map (algebraMap F K) gammaF) hgammaF hgammaK
            (stationaryCoefficientClass F chiF psiF h.targetDecomposition
              gammaF hgammaF) ∧
        latticeQuotientMk K (by omega) candidate =
          stationaryCoefficientClass K chiK psiK h.sourceDecomposition
            (Units.map (algebraMap F K) gammaF) hgammaK := by
  let gammaK : Kˣ := Units.map (algebraMap F K) gammaF
  let alphaN : F := norm F K (alpha1 : K)
  let betaN : F := norm F K (beta1 : K)
  have hp1 : 1 ≤ ramificationIndex F K := ramificationIndex_pos F K
  have halphaNLat : alphaN ∈ lattice F (v : ℤ) :=
    halpha1.norm_exactDepth.1
  have halphaMapLat : algebraMap F K alphaN ∈ lattice K (v : ℤ) := by
    rw [mem_lattice, ord_algebraMap, halpha1.norm_order,
      ← WithTop.coe_nsmul, WithTop.coe_le_coe]
    norm_num [nsmul_eq_mul]
    exact_mod_cast Nat.le_mul_of_pos_left v hp1
  have hbeta1Lat : (beta1 : K) ∈ lattice K 0 :=
    hbeta1.source_exactDepth.1
  have hsecondNumerator :
      (beta1 : K) * algebraMap F K alphaN ∈ lattice K (v : ℤ) := by
    simpa only [zero_add] using mul_mem_lattice K hbeta1Lat halphaMapLat
  have hsecond :
      (beta1 : K) * algebraMap F K alphaN / (alpha1 : K) ∈
        lattice K 0 := by
    apply (div_mem_lattice_iff K (alpha1 : K)
      ((beta1 : K) * algebraMap F K alphaN) (v : ℤ) 0
      halpha1.source_order).2
    simpa using hsecondNumerator
  have hbetaNLat : betaN ∈ lattice F 0 := hbeta1.norm_exactDepth.1
  have hbetaMapLat : algebraMap F K betaN ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    rw [mem_lattice] at hbetaNLat
    simpa using nsmul_le_nsmul_right hbetaNLat (ramificationIndex F K)
  have hcandidate :
      algebraMap F K betaN -
          (beta1 : K) * algebraMap F K alphaN / (alpha1 : K) ∈
        lattice K 0 :=
    (lattice K 0).sub_mem hbetaMapLat hsecond
  have h0d : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  have h0dK : (0 : ℤ) ≤ (dK : ℤ) := Int.natCast_nonneg dK
  refine ⟨by simpa [alphaN, betaN] using hcandidate, ?_⟩
  let candidate : lattice K 0 :=
    ⟨algebraMap F K betaN -
        (beta1 : K) * algebraMap F K alphaN / (alpha1 : K), hcandidate⟩
  let betaNorm : lattice F 0 := ⟨betaN, hbetaNLat⟩
  have hbetaNormClass : latticeQuotientMk F h0d betaNorm =
      stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF := by
    calc
      latticeQuotientMk F h0d betaNorm =
          latticeQuotientMk F h0d b := by
        apply (latticeQuotientMk_eq_mk_iff F h0d).2
        change betaN - (b : F) ∈ lattice F (d : ℤ)
        have hneg := neg_mem_lattice F hbeta1.norm_congruent
        rw [hbcoe]
        simpa [betaN] using hneg
      _ = _ := hbclass
  have hadjoint :
      latticeQuotientMk K h0dK candidate =
        normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK (latticeQuotientMk F h0d betaNorm) := by
    apply (stationaryPairingLeftEquiv K h.sourceDecomposition
      psiK gammaK hgammaK).injective
    change stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
        (latticeQuotientMk K h0dK candidate) =
      stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK (latticeQuotientMk F h0d betaNorm))
    apply AddChar.ext
    intro z
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective K
      (Int.ofNat_le.mpr
        h.sourceDecomposition.variableDepth_le_conductor) z
    have hpair := normPolynomialAdjoint_pairing F K h psiF psiK gammaF
      gammaK hgammaF hgammaK (latticeQuotientMk F h0d betaNorm)
      (latticeQuotientMk K
        (Int.ofNat_le.mpr
          h.sourceDecomposition.variableDepth_le_conductor) x)
    rw [normPolynomial_mk, stationaryPairingLeft_mk_mk] at hpair
    rw [stationaryPairingLeft_mk_mk, ← hpair]
    apply congrArg Units.val
    rw [hpsi, ContinuousAddChar.compTrace_apply]
    change psiF.character
        (trace F K ((candidate : K) * (x : K) / (gammaK : K))) =
      psiF.character
        (betaN * (normPolynomialRepresentative F K h x : F) /
          (gammaF : F))
    symm
    have hrem :
        normPolynomialValue F K (x : K) -
            (trace F K (x : K) + norm F K (x : K)) ∈
          lattice F (chiF.conductor : ℤ) :=
      normPolynomialValue_sub_trace_add_norm_mem F K
        (PrimeCyclicExtension.degree_prime F K).two_le hterms
        (x : K) x.property
    have hscaledRem :
        betaN * (normPolynomialValue F K (x : K) -
            (trace F K (x : K) + norm F K (x : K))) /
          (gammaF : F) ∈ lattice F (-psiF.conductor) := by
      apply (div_mem_lattice_iff F (gammaF : F)
        (betaN * (normPolynomialValue F K (x : K) -
          (trace F K (x : K) + norm F K (x : K))))
        ((chiF.conductor : ℤ) + psiF.conductor)
        (-psiF.conductor) hgammaF).2
      have hmul := mul_mem_lattice F hbetaNLat hrem
      simpa [add_comm, add_left_comm, add_assoc] using hmul
    have hpolyEq :
        psiF.character
            (betaN * normPolynomialValue F K (x : K) / (gammaF : F)) =
          psiF.character
            (betaN * (trace F K (x : K) + norm F K (x : K)) /
              (gammaF : F)) := by
      apply Units.ext
      apply (div_eq_one_iff_eq (Units.ne_zero _)).1
      have harg :
          betaN * normPolynomialValue F K (x : K) / (gammaF : F) -
              betaN * (trace F K (x : K) + norm F K (x : K)) /
                (gammaF : F) =
            betaN * (normPolynomialValue F K (x : K) -
              (trace F K (x : K) + norm F K (x : K))) /
                (gammaF : F) := by ring
      have hdiv :
          psiF.character
              (betaN * normPolynomialValue F K (x : K) / (gammaF : F)) /
            psiF.character
              (betaN * (trace F K (x : K) + norm F K (x : K)) /
                (gammaF : F)) = 1 := by
        calc
          _ = psiF.character.toAddChar
              (betaN * normPolynomialValue F K (x : K) / (gammaF : F) -
                betaN * (trace F K (x : K) + norm F K (x : K)) /
                  (gammaF : F)) :=
            (psiF.character.toAddChar.map_sub_eq_div _ _).symm
          _ = 1 := by
            rw [harg]
            exact psiF.isConductor.trivial _ hscaledRem
      simpa using congrArg Units.val hdiv
    rw [coe_normPolynomialRepresentative, hpolyEq]
    have hbeta1Lat : (beta1 : K) ∈ lattice K 0 :=
      hbeta1.source_exactDepth.1
    have hyconvMem :
        (beta1 : K) * (x : K) / (alpha1 : K) ∈
          lattice K (((t + 2) / 2 : ℕ) : ℤ) := by
      apply (div_mem_lattice_iff K (alpha1 : K)
        ((beta1 : K) * (x : K)) (v : ℤ)
        (((t + 2) / 2 : ℕ) : ℤ) halpha1.source_order).2
      have hxdeep : (x : K) ∈
          lattice K (((v + (t + 2) / 2 : ℕ) : ℤ)) :=
        lattice_antitone K (by exact_mod_cast hshift) x.property
      have hmul := mul_mem_lattice K hbeta1Lat hxdeep
      simpa [add_assoc] using hmul
    let yconv : lattice K (((t + 2) / 2 : ℕ) : ℤ) :=
      ⟨(beta1 : K) * (x : K) / (alpha1 : K), hyconvMem⟩
    have hconv := hconversion yconv
    have hnormRelation :
        alphaN * norm F K (yconv : K) = betaN * norm F K (x : K) := by
      dsimp [yconv, alphaN, betaN]
      rw [div_eq_mul_inv, map_mul, map_mul, Algebra.norm_inv]
      field_simp [Units.ne_zero (normUnits F K alpha1)]
    have hconv' :
        psiF.character
            (betaN * norm F K (x : K) / (gammaF : F)) =
          psiF.character
            ((-alphaN) * trace F K (yconv : K) / (gammaF : F)) := by
      simpa only [hnormRelation, alphaN] using hconv
    have htraceCandidate :
        trace F K ((candidate : K) * (x : K) / (gammaK : K)) =
          betaN * trace F K (x : K) / (gammaF : F) -
            alphaN * trace F K (yconv : K) / (gammaF : F) := by
      have hbetaTrace := trace_denominatorScaled_div F K gammaF gammaK
        betaN (x : K)
      have halphaTrace := trace_denominatorScaled_div F K gammaF gammaK
        alphaN (yconv : K)
      have hratio : normPolynomialDenominatorRatio F K gammaF gammaK = 1 := by
        simp [gammaK, normPolynomialDenominatorRatio]
      rw [hratio, one_mul] at hbetaTrace halphaTrace
      rw [show (candidate : K) * (x : K) / (gammaK : K) =
          algebraMap F K betaN * (x : K) / (gammaK : K) -
            algebraMap F K alphaN * (yconv : K) / (gammaK : K) by
        dsimp [candidate, yconv]
        ring]
      rw [map_sub, hbetaTrace, halphaTrace]
    rw [htraceCandidate]
    rw [show betaN * (trace F K (x : K) + norm F K (x : K)) /
          (gammaF : F) =
        betaN * trace F K (x : K) / (gammaF : F) +
          betaN * norm F K (x : K) / (gammaF : F) by ring]
    rw [psiF.character.map_add_eq_mul]
    rw [show betaN * trace F K (x : K) / (gammaF : F) -
          alphaN * trace F K (yconv : K) / (gammaF : F) =
        betaN * trace F K (x : K) / (gammaF : F) +
          (-alphaN) * trace F K (yconv : K) / (gammaF : F) by ring]
    rw [psiF.character.map_add_eq_mul, hconv']
  have hadjointClass :
      latticeQuotientMk K h0dK candidate =
        normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK
          (stationaryCoefficientClass F chiF psiF h.targetDecomposition
            gammaF hgammaF) := by
    rw [← hbetaNormClass]
    exact hadjoint
  refine ⟨?_, ?_⟩
  · simpa only [candidate, gammaK] using hadjointClass
  · calc
      latticeQuotientMk K h0dK candidate =
          normPolynomialAdjoint F K h psiF psiK gammaF gammaK
            hgammaF hgammaK
            (stationaryCoefficientClass F chiF psiF h.targetDecomposition
              gammaF hgammaF) := hadjointClass
      _ = stationaryCoefficientClass K chiK psiK h.sourceDecomposition
          gammaK hgammaK :=
        (stationaryClass_compNorm F K chiF chiK psiF psiK h hchi hpsi
          gammaF gammaK hgammaF hgammaK).symm

/-! ## Existential stationary representatives -/

/-- The common stationary depth for a nontrivial norm character of exact
conductor `T=t+1` is `s0=ceil(T/2)=(t+2)/2`. -/
theorem highParameter_intermediate_normCharacterDepth
    (htpos : 0 < t) :
    IsLamprechtStationaryDepth (t + 1) ((t + 2) / 2) := by
  constructor <;> omega

/-- Existentially choose, independently, the two norm representatives used
in part (c).  The norm-character coefficient is chosen only at precision
`r0=floor(T/2)=(t+1)/2`; the minimal-character coefficient is chosen only
at precision `d`.  The hypotheses prove `r0≤t` and `d≤t`, so this theorem
never invokes `NormRepresentatives` at `t+1` or beyond.  The returned field
elements are witnesses, not definitions. -/
theorem highParameter_intermediate_normRepresentatives
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (htpos : 0 < t)
    (hupper : chiF.conductor < 2 * (t + 1))
    (tau : NormCharacter F K) (htau : tau ≠ 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ∃ (a : lattice F
          ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
      (b : lattice F 0) (alpha beta : Fˣ) (alpha1 beta1 : Kˣ),
      (a : F) = (alpha : F) ∧
      (b : F) = (beta : F) ∧
      IsSubcriticalNormRepresentative F K
          ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
          ((t + 1) / 2) alpha alpha1 ∧
      IsSubcriticalNormRepresentative F K 0 d beta beta1 ∧
      latticeQuotientMk F
          (sub_le_sub_left
            (highParameter_intermediate_normCharacterDepth
              F K ht hres pi hpi hgen htpos).int_le_conductor
            (chiF.conductor : ℤ))
          a =
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F tau.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen tau htau))
          psiF (chiF.conductor : ℤ)
          (highParameter_intermediate_normCharacterDepth
            F K ht hres pi hpi hgen htpos)
          gammaF hgammaF ∧
      latticeQuotientMk F (by omega) b =
        stationaryCoefficientClass F chiF psiF hF gammaF hgammaF := by
  let hr := highParameter_intermediate_normCharacterDepth
    F K ht hres pi hpi hgen htpos
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau htau)
  let alphaClass := stationaryNumeratorClass F tauData psiF
    (chiF.conductor : ℤ) hr gammaF hgammaF
  obtain ⟨a, ha⟩ := latticeQuotientMk_surjective F
    (sub_le_sub_left hr.int_le_conductor (chiF.conductor : ℤ)) alphaClass
  have haord : ord F (a : F) =
      (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
    stationaryNumeratorClass_representative_ord F tauData psiF
      (chiF.conductor : ℤ) hr gammaF hgammaF a ha
  let alpha : Fˣ := Units.mk0 (a : F) (by
    apply (ord_ne_top_iff F).1
    rw [haord]
    simp)
  have halpha : ord F (alpha : F) =
      (((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    change ord F (a : F) = _
    exact haord
  have hr0t : (t + 1) / 2 ≤ t := by omega
  obtain ⟨alpha1, halpha1⟩ := normRepresentative_subcritical
    F K ht hres pi hpi hgen hr0t alpha halpha
  let betaClass := stationaryCoefficientClass F chiF psiF hF gammaF hgammaF
  obtain ⟨b, hb⟩ := latticeQuotientMk_surjective F (by omega) betaClass
  have hbLamp := congrArg (stationaryCoefficientLamprechtEquivAtConductor F hF) hb
  rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
    stationaryCoefficientClass_toLamprecht] at hbLamp
  have hbord : ord F (b : F) = (0 : WithTop ℤ) := by
    have h := stationaryNumeratorClass_representative_ord F chiF psiF
      (chiF.conductor : ℤ)
      (stationaryDepthOfConductorDecomposition F chiF hF)
      gammaF hgammaF
      (⟨(b : F), by simpa using b.property⟩ :
        lattice F ((chiF.conductor : ℤ) - (chiF.conductor : ℤ))) hbLamp
    simpa using h
  let beta : Fˣ := Units.mk0 (b : F) (by
    apply (ord_ne_top_iff F).1
    rw [hbord]
    simp)
  have hbeta : ord F (beta : F) = (0 : WithTop ℤ) := by
    change ord F (b : F) = _
    exact hbord
  have hdt : d ≤ t := by
    rw [hF.conductor_eq] at hupper
    omega
  obtain ⟨beta1, hbeta1⟩ := normRepresentative_subcritical
    F K ht hres pi hpi hgen hdt beta hbeta
  refine ⟨a, b, alpha, beta, alpha1, beta1, rfl, rfl,
    halpha1, hbeta1, ?_, ?_⟩
  · simpa only [alpha, tauData, hr, alphaClass] using ha
  · simpa only [beta, betaClass] using hb

/-! ## Prime-field Teichmüller indices -/

omit ht hres pi hpi hgen in
private noncomputable def highIntermediateTeichmullerInteger
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    ringOfIntegers E := by
  letI : CharP (ResidueField E) p := ringChar.of_eq hchar
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime E⟩
  exact teichmuller E (ZMod.cast j : ResidueField E)

omit ht hres pi hpi hgen in
/-- The manuscript's Teichmüller lift of the prime-field index.  This is
an index scalar, not a stationary representative; stationary parameters
remain quotient classes throughout this file. -/
noncomputable def highIntermediateTeichmullerScalar
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
  (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) : E :=
  (highIntermediateTeichmullerInteger E p hchar j : E)

omit ht hres pi hpi hgen in
/-- The Teichmüller index scalar is integral.  This supplies only the
filtration fact used in the quotient calculation; it does not select a
stationary representative. -/
theorem highParameter_intermediate_teichmuller_mem_integer
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    highIntermediateTeichmullerScalar E p hchar j ∈ ringOfIntegers E := by
  simp [highIntermediateTeichmullerScalar]

omit ht hres pi hpi hgen in
/-- The zero prime-field index has zero Teichmüller scalar, and no other
index does. -/
@[simp]
theorem highParameter_intermediate_teichmuller_eq_zero_iff
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    highIntermediateTeichmullerScalar E p hchar j = 0 ↔ j = 0 := by
  letI : CharP (ResidueField E) p := ringChar.of_eq hchar
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime E⟩
  change ((teichmuller E (ZMod.cast j : ResidueField E) :
    ringOfIntegers E) : E) = 0 ↔ j = 0
  norm_cast
  rw [teichmuller_eq_zero_iff]
  exact map_eq_zero_iff (ZMod.castHom (dvd_refl p) (ResidueField E))
    (ZMod.castHom (dvd_refl p) (ResidueField E)).injective

omit ht hres pi hpi hgen in
/-- Every nonzero Teichmüller index scalar is a unit. -/
theorem highParameter_intermediate_teichmuller_ord_eq_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p)
    (hj : j ≠ 0) :
    ord E (highIntermediateTeichmullerScalar E p hchar j) = 0 := by
  letI : CharP (ResidueField E) p := ringChar.of_eq hchar
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime E⟩
  let x : ResidueField E := ZMod.cast j
  have hx : x ≠ 0 := by
    exact (map_ne_zero (ZMod.castHom (dvd_refl p) (ResidueField E))).2 hj
  let xu : (ResidueField E)ˣ := Units.mk0 x hx
  let ou : (ringOfIntegers E)ˣ := teichmullerUnits E xu
  let u : unitGroup E := (unitGroupMulEquivRingOfIntegers E).symm ou
  have hu : ord E ((u : Eˣ) : E) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero E u).1 u.property
  have hou : ord E ((ou : ringOfIntegers E) : E) = 0 := by
    change ord E ((ou : ringOfIntegers E) : E) = 0 at hu
    exact hu
  change ord E ((teichmuller E x : ringOfIntegers E) : E) = 0 at hou
  exact hou

omit ht hres pi hpi hgen in
private theorem residueMap_highIntermediateTeichmullerInteger
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    residueMap E (highIntermediateTeichmullerInteger E p hchar j) =
      (ZMod.cast j : ResidueField E) := by
  letI : CharP (ResidueField E) p := ringChar.of_eq hchar
  exact residueMap_teichmuller E (ZMod.cast j : ResidueField E)

omit ht hres pi hpi hgen in
private theorem highIntermediateTeichmullerScalar_mem_integer
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    highIntermediateTeichmullerScalar E p hchar j ∈ ringOfIntegers E :=
  (highIntermediateTeichmullerInteger E p hchar j).property

omit ht hres pi hpi hgen in
/-- The terminal norm term uses the exact Teichmüller identity `[j]^p=[j]`. -/
@[simp]
theorem highParameter_intermediate_teichmuller_pow
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    highIntermediateTeichmullerScalar E p hchar j ^ p =
      highIntermediateTeichmullerScalar E p hchar j := by
  letI : CharP (ResidueField E) p := ringChar.of_eq hchar
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime E⟩
  let x : ResidueField E := ZMod.cast j
  have hxpow : x ^ p = x := by
    change (ZMod.cast j : ResidueField E) ^ p = ZMod.cast j
    simpa only [ZMod.cast_pow'] using
      congrArg (fun z : ZMod p ↦ (ZMod.cast z : ResidueField E))
        (ZMod.pow_card j)
  change ((teichmuller E x : ringOfIntegers E) : E) ^ p =
    ((teichmuller E x : ringOfIntegers E) : E)
  norm_cast
  rw [← map_pow, hxpow]

omit ht hres pi hpi hgen in
private noncomputable def highIntermediateTeichmullerGeomFactor
    (E : Type*) [Field E] (p : ℕ) (a b : E) : E :=
  ∑ i ∈ Finset.range p, a ^ i * b ^ (p - 1 - i)

omit ht hres pi hpi hgen in
private theorem highIntermediateTeichmullerGeomFactor_mem_lattice_one
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p) :
    highIntermediateTeichmullerGeomFactor E p
        (highIntermediateTeichmullerScalar E p hchar j) (j.val : E) ∈
      lattice E 1 := by
  letI : CharP (ResidueField E) p := ringChar.of_eq hchar
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime E⟩
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let aO := highIntermediateTeichmullerInteger E p hchar j
  let bO : ringOfIntegers E := (j.val : ringOfIntegers E)
  let S : ringOfIntegers E :=
    ∑ i ∈ Finset.range p, aO ^ i * bO ^ (p - 1 - i)
  have hb : residueMap E bO = (ZMod.cast j : ResidueField E) := by
    change (j.val : ResidueField E) = ZMod.cast j
    exact ZMod.natCast_val j
  have ha : residueMap E aO = (ZMod.cast j : ResidueField E) :=
    residueMap_highIntermediateTeichmullerInteger E p hchar j
  have hred : residueMap E S = 0 := by
    rw [map_sum]
    simp only [map_mul, map_pow, ha, hb]
    rw [show (∑ x ∈ Finset.range p,
        (ZMod.cast j : ResidueField E) ^ x *
          (ZMod.cast j : ResidueField E) ^ (p - 1 - x)) =
        ∑ _x ∈ Finset.range p,
          (ZMod.cast j : ResidueField E) ^ (p - 1) by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add]
      congr 1
      have hil : i ≤ p - 1 := by
        have := Finset.mem_range.1 hi
        omega
      omega]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [CharP.cast_eq_zero (ResidueField E) p, zero_mul]
  have hS : (S : E) ∈ lattice E 1 :=
    (residueMap_eq_zero_iff E S).1 hred
  have hSeq : (S : E) = highIntermediateTeichmullerGeomFactor E p
      (highIntermediateTeichmullerScalar E p hchar j) (j.val : E) := by
    dsimp only [S, aO, bO, highIntermediateTeichmullerGeomFactor,
      highIntermediateTeichmullerScalar]
    push_cast
    rfl
  rw [hSeq] at hS
  exact hS

omit ht hres pi hpi hgen in
private theorem highIntermediateTeichmullerScalar_sub_val_mem_lattice
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (p : ℕ) (hchar : residueCharacteristic E = p) (j : ZMod p)
    (s : ℕ) (hpdepth : (p : E) ∈ lattice E (s : ℤ)) :
    highIntermediateTeichmullerScalar E p hchar j - (j.val : E) ∈
      lattice E (s : ℤ) := by
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime E⟩
  let a := highIntermediateTeichmullerScalar E p hchar j
  let b : E := (j.val : E)
  let G := highIntermediateTeichmullerGeomFactor E p a b
  have hG : G ∈ lattice E 1 :=
    highIntermediateTeichmullerGeomFactor_mem_lattice_one E p hchar j
  have haPow : a ^ p = a :=
    highParameter_intermediate_teichmuller_pow E p hchar j
  have hfermat := Int.ModEq.pow_prime_eq_self
    (Fact.out : p.Prime) (j.val : ℤ)
  obtain ⟨k, hk⟩ := hfermat.dvd
  have hbcorrection : b ^ p - b = (p : E) * ((-k : ℤ) : E) := by
    have hk' := congrArg (fun z : ℤ ↦ (z : E)) hk
    push_cast at hk'
    change (j.val : E) ^ p - (j.val : E) =
      (p : E) * ((-k : ℤ) : E)
    calc
      (j.val : E) ^ p - (j.val : E) =
          -((j.val : E) - (j.val : E) ^ p) := by ring
      _ = -((p : E) * (k : E)) := by rw [hk']
      _ = (p : E) * ((-k : ℤ) : E) := by push_cast; ring
  induction s with
  | zero =>
      exact Submodule.sub_mem _
        ((mem_lattice_zero_iff E).2
          (highIntermediateTeichmullerScalar_mem_integer E p hchar j))
        ((mem_lattice_zero_iff E).2
          (show (j.val : E) ∈ ringOfIntegers E from
            (j.val : ringOfIntegers E).property))
  | succ n ih =>
      have hp_n : (p : E) ∈ lattice E (n : ℤ) :=
        lattice_antitone E (by omega) hpdepth
      have hdelta_n : a - b ∈ lattice E (n : ℤ) := ih hp_n
      have hfirst : a ^ p - b ^ p ∈ lattice E ((n + 1 : ℕ) : ℤ) := by
        have hprod := mul_mem_lattice E hdelta_n hG
        rw [show (a - b) * G = a ^ p - b ^ p by
          exact (Commute.all a b).mul_geom_sum₂ p] at hprod
        simpa using hprod
      have hkint : ((-k : ℤ) : E) ∈ lattice E 0 :=
        (mem_lattice_zero_iff E).2
          (show ((-k : ℤ) : E) ∈ ringOfIntegers E from
            ((-k : ℤ) : ringOfIntegers E).property)
      have hsecond : b ^ p - b ∈ lattice E ((n + 1 : ℕ) : ℤ) := by
        rw [hbcorrection]
        exact mul_mem_lattice E hpdepth hkint
      change a - b ∈ lattice E ((n + 1 : ℕ) : ℤ)
      rw [← haPow]
      convert Submodule.add_mem _ hfirst hsecond using 1 <;> ring

omit ht hres pi hpi hgen in
private theorem highIntermediate_half_le_wildBaseDepth
    (p T : ℕ) (hp : p.Prime) :
    ((T / 2 : ℕ) : ℤ) ≤
      (((p - 1) * T : ℕ) : ℤ) / (p : ℤ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpdecomp : p = 2 + (p - 2) := by omega
  have hpmone : p - 1 = 1 + (p - 2) := by omega
  have hhalf : 2 * (T / 2) ≤ T := Nat.mul_div_le T 2
  have hhalfT : T / 2 ≤ T := Nat.div_le_self T 2
  have hnat : p * (T / 2) ≤ (p - 1) * T := by
    calc
      p * (T / 2) = (2 + (p - 2)) * (T / 2) :=
        congrArg (fun z : ℕ ↦ z * (T / 2)) hpdecomp
      _ = 2 * (T / 2) + (p - 2) * (T / 2) := by ring
      _ ≤ T + (p - 2) * T :=
        Nat.add_le_add hhalf (Nat.mul_le_mul_left (p - 2) hhalfT)
      _ = (1 + (p - 2)) * T := by ring
      _ = (p - 1) * T :=
        congrArg (fun z : ℕ ↦ z * T) hpmone.symm
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  simpa [mul_comm] using (show
    (p * (T / 2) : ℤ) ≤ ((p - 1) * T : ℕ) by exact_mod_cast hnat)

omit ht hres pi hpi hgen in
/-- Teichmüller and natural power indices define the same stationary
quotient scalar at exactly `r0=floor(T/2)`.  The extra depth comes from the
trace bound and the exact denominator `[K:F]` in `D/[K:F]`. -/
theorem highParameter_intermediate_teichmuller_congruent
    (p T : ℕ) (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ))
    (j : ZMod p) :
    highIntermediateTeichmullerScalar F p hchar j - (j.val : F) ∈
      lattice F ((T / 2 : ℕ) : ℤ) := by
  have hp : p.Prime := by
    simpa [← hchar] using residueCharacteristic_prime F
  have hpord := degree_natCast_ord_bound F K p
    (((p - 1) * T : ℕ) : ℤ) hp.pos hdegree htrace
  have hhalf := highIntermediate_half_le_wildBaseDepth p T hp
  have hpdepth : (p : F) ∈ lattice F ((T / 2 : ℕ) : ℤ) := by
    rw [mem_lattice]
    exact (WithTop.coe_le_coe.mpr hhalf).trans hpord
  exact highIntermediateTeichmullerScalar_sub_val_mem_lattice
    F p hchar j (T / 2) hpdepth

omit ht hres pi hpi hgen in
/-- For odd `p` and odd `T > 1`, the same trace bound gives one more
Teichmüller congruence layer.  Writing `T = 2r+1`, the key inequality is
`p*(r+1) ≤ (p-1)*T`. -/
theorem highParameter_intermediate_teichmuller_congruent_succ_of_odd
    (p T : ℕ) (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ))
    (hpodd : Odd p) (hTodd : Odd T) (hTone : 1 < T)
    (j : ZMod p) :
    highIntermediateTeichmullerScalar F p hchar j - (j.val : F) ∈
      lattice F ((T / 2 + 1 : ℕ) : ℤ) := by
  have hp : p.Prime := by
    simpa [← hchar] using residueCharacteristic_prime F
  have hpThree : 3 ≤ p := by
    have hpTwo := hp.two_le
    by_contra hnot
    have hpEq : p = 2 := by omega
    rw [hpEq] at hpodd
    norm_num at hpodd
  rcases hTodd with ⟨r, hT⟩
  have hr : 1 ≤ r := by omega
  have hrMul : r ≤ (p - 2) * r := by
    calc
      r = 1 * r := by simp
      _ ≤ (p - 2) * r := Nat.mul_le_mul_right r (by omega)
  have hpSplit : p = (p - 2) + 2 := by omega
  have hpmSplit : p - 1 = (p - 2) + 1 := by omega
  have hnat : p * (r + 1) ≤ (p - 1) * T := by
    calc
      p * (r + 1) = ((p - 2) + 2) * (r + 1) :=
        congrArg (fun q : ℕ ↦ q * (r + 1)) hpSplit
      _ ≤ ((p - 2) + 1) * (2 * r + 1) := by nlinarith [hrMul]
      _ = (p - 1) * (2 * r + 1) :=
        congrArg (fun q : ℕ ↦ q * (2 * r + 1)) hpmSplit.symm
      _ = (p - 1) * T :=
        congrArg (fun q : ℕ ↦ (p - 1) * q) hT.symm
  have hpord := degree_natCast_ord_bound F K p
    (((p - 1) * T : ℕ) : ℤ) hp.pos hdegree htrace
  have hdepth : ((r + 1 : ℕ) : ℤ) ≤
      (((p - 1) * T : ℕ) : ℤ) / (p : ℤ) := by
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
    exact_mod_cast (show (r + 1) * p ≤ (p - 1) * T by
      simpa only [mul_comm] using hnat)
  have hpdepth : (p : F) ∈ lattice F ((r + 1 : ℕ) : ℤ) := by
    rw [mem_lattice]
    exact (WithTop.coe_le_coe.mpr hdepth).trans hpord
  have hcongruent := highIntermediateTeichmullerScalar_sub_val_mem_lattice
    F p hchar j (r + 1) hpdepth
  have hhalf : T / 2 + 1 = r + 1 := by omega
  rw [hhalf]
  exact hcongruent

omit ht hres pi hpi hgen in
/-- Quotient bridge between the Teichmüller field scalar and the natural
multiple used by the character-power stationary theorem. -/
theorem highParameter_intermediate_teichmuller_mul_class
    (p : ℕ) (hchar : residueCharacteristic F = p) (j : ZMod p)
    (h : ℤ) (s : ℕ)
    (hteich : highIntermediateTeichmullerScalar F p hchar j - (j.val : F) ∈
      lattice F (s : ℤ))
    (alpha : lattice F h) :
    latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
        ⟨highIntermediateTeichmullerScalar F p hchar j * (alpha : F), by
          have ht0 : highIntermediateTeichmullerScalar F p hchar j ∈
              lattice F 0 :=
            (mem_lattice_zero_iff F).2
              (highIntermediateTeichmullerScalar_mem_integer F p hchar j)
          simpa [add_comm] using mul_mem_lattice F ht0 alpha.property⟩ =
      j.val • latticeQuotientMk F
        (show h ≤ h + (s : ℤ) by omega) alpha := by
  rw [← map_nsmul]
  apply (latticeQuotientMk_eq_mk_iff F
    (show h ≤ h + (s : ℤ) by omega)).2
  simpa [nsmul_eq_mul, sub_mul, add_comm] using
    mul_mem_lattice F hteich alpha.property

omit ht hres pi hpi hgen in
/-- The exact norm expansion used for every lower twist.  All intermediate
elementary-symmetric terms lie in `p_F^d`; the endpoint scalar is literally
the Teichmüller identity `[j]^p=[j]`.  The conclusion is an ideal-membership
statement and hence an equality of quotient classes, not an equality of
chosen field representatives. -/
theorem highParameter_intermediate_norm_add_teichmuller_congruent
    (p T d v : ℕ) (hp : p.Prime) (hT : 2 ≤ T)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ))
    (hcross : ∀ i : ℕ, 1 ≤ i → i < p →
      p * d ≤ i * v + (p - 1) * T)
    (alpha1 beta1 : Kˣ)
    (halpha1 : ord K (alpha1 : K) = ((v : ℤ) : WithTop ℤ))
    (hbeta1 : ord K (beta1 : K) = (0 : WithTop ℤ))
    (j : ZMod p) :
    norm F K ((beta1 : K) +
          algebraMap F K
              (highIntermediateTeichmullerScalar F p hchar j) *
            (alpha1 : K)) -
        (norm F K (beta1 : K) +
          highIntermediateTeichmullerScalar F p hchar j *
            norm F K (alpha1 : K)) ∈ lattice F (d : ℤ) := by
  let lam : F := highIntermediateTeichmullerScalar F p hchar j
  by_cases hj : j = 0
  · subst j
    have hlam : lam = 0 := by
      exact (highParameter_intermediate_teichmuller_eq_zero_iff
        F p hchar 0).2 rfl
    simp only [lam, hlam, map_zero, zero_mul, add_zero]
    simp
  have hlam0 : lam ≠ 0 := by
    exact (highParameter_intermediate_teichmuller_eq_zero_iff
      F p hchar j).not.mpr hj
  have hlamOrd : ord F lam = (0 : WithTop ℤ) :=
    highParameter_intermediate_teichmuller_ord_eq_zero F p hchar j hj
  let x : K := algebraMap F K lam * (alpha1 : K) / (beta1 : K)
  have hxord : ord K x = ((v : ℤ) : WithTop ℤ) := by
    dsimp only [x]
    rw [ord_div, ord_mul, ord_algebraMap, hlamOrd, nsmul_zero,
      zero_add, halpha1, hbeta1, sub_zero]
  have hxordLower : ((v : ℤ) : WithTop ℤ) ≤ ord K x := hxord.ge
  let mid : F := ∑ k ∈ Finset.range (p - 1),
    elementarySymmetric F K (k + 1) x
  have hmid : mid ∈ lattice F (d : ℤ) := by
    dsimp only [mid]
    apply Submodule.sum_mem
    intro k hk
    have hklt : k < p - 1 := Finset.mem_range.1 hk
    have hkp : k + 1 < p := by omega
    have hbound := wild_elementarySymmetric_bound F K p T (v : ℤ)
      hp hT hchar hdegree htrace hxordLower (j := k + 1) (by omega) hkp
    rw [mem_lattice]
    apply (WithTop.coe_le_coe.mpr ?_).trans hbound
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
    have hnat := hcross (k + 1) (by omega) hkp
    simpa [mul_comm] using (show
      (p * d : ℤ) ≤ ((k + 1) * v + (p - 1) * T : ℕ) by
        exact_mod_cast hnat)
  have hnormBetaOrd : ord F (norm F K (beta1 : K)) =
      (0 : WithTop ℤ) := by
    rw [ord_norm, hbeta1]
    simp
  have hnormBeta0 : norm F K (beta1 : K) ≠ 0 := by
    exact (Algebra.norm_ne_zero_iff).2 (Units.ne_zero beta1)
  have hnormBetaMem : norm F K (beta1 : K) ∈ lattice F 0 := by
    rw [mem_lattice, hnormBetaOrd]
    simp
  have hscaledMid : norm F K (beta1 : K) * mid ∈
      lattice F (d : ℤ) := by
    simpa [add_comm] using mul_mem_lattice F hnormBetaMem hmid
  have hterminal :
      norm F K (beta1 : K) * elementarySymmetric F K p x =
        lam * norm F K (alpha1 : K) := by
    rw [← hdegree, elementarySymmetric_finrank]
    dsimp only [x]
    rw [div_eq_mul_inv, map_mul, map_mul, Algebra.norm_inv,
      norm_algebraMap, hdegree,
      highParameter_intermediate_teichmuller_pow F p hchar j]
    field_simp [hnormBeta0]
    rfl
  have hfactor :
      (beta1 : K) + algebraMap F K lam * (alpha1 : K) =
        (beta1 : K) * (1 + x) := by
    dsimp only [x]
    field_simp
  have hpTwo : 2 ≤ p := hp.two_le
  have hpSucc : p = (p - 1) + 1 := by omega
  have hexpand :
      norm F K ((beta1 : K) + algebraMap F K lam * (alpha1 : K)) -
          (norm F K (beta1 : K) + lam * norm F K (alpha1 : K)) =
        norm F K (beta1 : K) * mid := by
    rw [hfactor, map_mul, norm_one_add_eq_one_add_sum_elementarySymmetric]
    rw [hdegree, hpSucc, Finset.sum_range_succ]
    have hlast : p - 1 + 1 = p := by omega
    rw [hlast]
    change norm F K (beta1 : K) *
          (1 + (mid + elementarySymmetric F K p x)) -
        (norm F K (beta1 : K) + lam * norm F K (alpha1 : K)) =
      norm F K (beta1 : K) * mid
    calc
      _ = norm F K (beta1 : K) * mid +
          (norm F K (beta1 : K) * elementarySymmetric F K p x -
            lam * norm F K (alpha1 : K)) := by ring
      _ = norm F K (beta1 : K) * mid := by rw [hterminal]; ring
  change norm F K ((beta1 : K) + algebraMap F K lam * (alpha1 : K)) -
      (norm F K (beta1 : K) + lam * norm F K (alpha1 : K)) ∈
        lattice F (d : ℤ)
  rw [hexpand]
  exact hscaledMid

/-- The complete cyclic index is the corresponding power of its index-one
generator; the identity index is retained. -/
theorem highParameter_intermediate_index_eq_power
    (j : ZMod (Module.finrank F K)) :
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd j) =
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))) ^ j.val := by
  letI : NeZero (Module.finrank F K) :=
    ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩
  let e := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
  have hj : Multiplicative.ofAdd j =
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K))) ^ j.val := by
    apply Multiplicative.ext
    simp only [toAdd_ofAdd, toAdd_pow, nsmul_eq_mul]
    simpa only [mul_one] using (ZMod.natCast_zmod_val j).symm
  rw [hj]
  exact map_pow e _ _

/-- The index-one norm character is nontrivial. -/
theorem highParameter_intermediate_indexOne_ne_one :
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K))) ≠ 1 := by
  apply (ramifiedNormCharacterZModEquiv_ne_one_iff
    F K ht hres pi hpi hgen _).2
  letI : Fact (Module.finrank F K).Prime :=
    ⟨PrimeCyclicExtension.degree_prime F K⟩
  intro h
  have hz : (1 : ZMod (Module.finrank F K)) = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  exact (one_ne_zero : (1 : ZMod (Module.finrank F K)) ≠ 0) hz

/-- On a common critical layer, the class of the `j`-indexed norm
character is exactly `j.val` times the class of the index-one generator.
Both sides are quotient classes. -/
theorem highParameter_intermediate_normCharacterClass_eq_nsmul
    (j : ZMod (Module.finrank F K))
    (hmu : ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j) ≠ 1)
    (psiF : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      ((M + psiF.conductor : ℤ) : WithTop ℤ)) :
    stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd j)).1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _ hmu))
        psiF M hr gammaF hgammaF =
      j.val • stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))).1
          (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _
            (highParameter_intermediate_indexOne_ne_one
              F K ht hres pi hpi hgen)))
        psiF M hr gammaF hgammaF := by
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  have heq := highParameter_intermediate_index_eq_power
    F K ht hres pi hpi hgen j
  have hpow : tau ^ j.val ≠ 1 := by
    rw [← heq]
    exact hmu
  let tauData := quasiCharDataOfIsConductor F tau.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
      (highParameter_intermediate_indexOne_ne_one
        F K ht hres pi hpi hgen))
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  let s := stationaryNumeratorClass F tauData psiF M hr gammaF hgammaF
  have hs : IsStationaryRestrictionClass F tau.1 psiF M hr.pos
      hr.le_conductor gammaF s :=
    stationaryNumeratorClass_isRestriction F tauData
      psiF M hr gammaF hgammaF
  have hz := IsStationaryRestrictionClass.zpow F psiF M hr.pos
    hr.le_conductor gammaF hgammaF s hs (j.val : ℤ)
  have hpowChar : tau.1 ^ (j.val : ℤ) = mu.1 := by
    calc
      tau.1 ^ (j.val : ℤ) = (tau ^ j.val).1 := by
        simpa using (NormCharacter.coe_pow
          (F := F) (K := K) tau j.val).symm
      _ = mu.1 := congrArg (fun z : NormCharacter F K ↦ z.1) heq.symm
  have hsmul : (j.val : ℤ) • s = j.val • s := by simp
  rw [hpowChar, hsmul] at hz
  have hz' : IsStationaryNumeratorClass F muData psiF M hr gammaF
      (j.val • s) := hz
  change stationaryNumeratorClass F muData psiF M hr gammaF hgammaF =
    j.val • s
  exact (stationaryNumeratorClass_unique F muData psiF M hr gammaF hgammaF
    (j.val • s) hz').symm

/-- For every prime-field index, the literal linear class
`N(beta1)+[j]*N(alpha1)` is the stationary coefficient quotient class of
the actual least-conductor twist.  The norm-character class is constructed
only at `s0` and evaluated on deeper lattices, so the endpoint `d+epsilon=T`
does not manufacture a stationary class for it at depth `T`. -/
theorem highParameter_intermediate_twistLinearClass
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (a : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (alpha : Fˣ) (hacoe : (a : F) = (alpha : F))
    (alpha1 : Kˣ)
    (halpha1 : IsSubcriticalNormRepresentative F K
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
      ((t + 1) / 2) alpha alpha1)
    (tau : NormCharacter F K)
    (htau : tau = ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K))))
    (ha : latticeQuotientMk F
        (sub_le_sub_left
          (highParameter_intermediate_normCharacterDepth
            F K ht hres pi hpi hgen htpos).int_le_conductor
          (chiF.conductor : ℤ)) a =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau (by
            rw [htau]
            exact highParameter_intermediate_indexOne_ne_one
              F K ht hres pi hpi hgen)))
        psiF (chiF.conductor : ℤ)
        (highParameter_intermediate_normCharacterDepth
          F K ht hres pi hpi hgen htpos)
        gammaF hgammaF)
    (b : lattice F 0) (beta : Fˣ) (hbcoe : (b : F) = (beta : F))
    (beta1 : Kˣ)
    (hbeta1 : IsSubcriticalNormRepresentative F K 0 d beta beta1)
    (hbclass : latticeQuotientMk F (by omega) b =
      stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    let lam := highIntermediateTeichmullerScalar F (Module.finrank F K)
      (residueCharacteristic_eq_degree_of_positive_break
        F K ht htpos pi hpi hgen) j
    ∃ (hJ : IsStationaryConductorDecomposition twist.conductor d epsilon)
      (hgammaJ : ord F (gammaF : F) =
        (((twist.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
      (hlinearMem : norm F K (beta1 : K) +
          lam * norm F K (alpha1 : K) ∈ lattice F 0),
      latticeQuotientMk F (by omega)
          ⟨norm F K (beta1 : K) + lam * norm F K (alpha1 : K),
            hlinearMem⟩ =
        stationaryCoefficientClass F twist psiF hJ gammaF hgammaJ := by
  let p := Module.finrank F K
  let T := t + 1
  let v := chiF.conductor - T
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  let twist := ramifiedNormCharacterOrbitTwistData
    F K ht hres pi hpi hgen chiF mu
  have hchar : residueCharacteristic F = p := by
    simpa [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  let lam := highIntermediateTeichmullerScalar F p hchar j
  have hcond : twist.conductor = chiF.conductor := by
    simpa only [twist, mu] using
      highParameter_intermediate_twist_conductor_eq
        F K ht hres pi hpi hgen chiF hminimal hlower mu
  have hJ : IsStationaryConductorDecomposition twist.conductor d epsilon := by
    rw [hcond]
    exact hF
  have hgammaJ : ord F (gammaF : F) =
      (((twist.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) := by
    rw [hcond]
    exact hgammaF
  have halphaNorm : norm F K (alpha1 : K) ∈ lattice F (v : ℤ) := by
    have hv : (chiF.conductor : ℤ) - (T : ℤ) = (v : ℤ) := by
      dsimp only [v, T]
      omega
    rw [← hv]
    exact halpha1.norm_exactDepth.1
  have hbetaNorm : norm F K (beta1 : K) ∈ lattice F 0 :=
    hbeta1.norm_exactDepth.1
  have hlamInt : lam ∈ lattice F 0 := by
    rw [mem_lattice_zero_iff F]
    exact highParameter_intermediate_teichmuller_mem_integer F p hchar j
  have hlamAlpha : lam * norm F K (alpha1 : K) ∈ lattice F 0 := by
    have hprod0 : lam * norm F K (alpha1 : K) ∈
        lattice F ((0 : ℤ) + (v : ℤ)) :=
      mul_mem_lattice F hlamInt halphaNorm
    have hprod : lam * norm F K (alpha1 : K) ∈ lattice F (v : ℤ) := by
      simpa only [zero_add] using hprod0
    exact lattice_antitone F (by omega) hprod
  have hlinearMem : norm F K (beta1 : K) +
      lam * norm F K (alpha1 : K) ∈ lattice F 0 :=
    add_mem_lattice F hbetaNorm hlamAlpha
  refine ⟨hJ, hgammaJ, hlinearMem, ?_⟩
  apply (latticeQuotientMk_eq_stationaryCoefficientClass_iff
    F twist psiF hJ gammaF hgammaJ _).2
  intro x
  have hm : chiF.conductor = t + 1 + v := by
    dsimp only [v, T]
    omega
  have htauNe : tau ≠ 1 := by
    rw [htau]
    exact highParameter_intermediate_indexOne_ne_one
      F K ht hres pi hpi hgen
  have halphaLinear := highParameter_intermediate_selectedAlpha_linearization
    F K ht hres pi hpi hgen htpos chiF psiF hm tau htauNe gammaF hgammaF
      a alpha hacoe alpha1 halpha1 ha
  have hqFs0 : (t + 2) / 2 ≤ d + epsilon := by
    rw [hF.conductor_eq] at hlower
    omega
  let xs0 : lattice F (((t + 2) / 2 : ℕ) : ℤ) :=
    ⟨(x : F), lattice_antitone F (by exact_mod_cast hqFs0) x.property⟩
  have htauEval := halphaLinear xs0
  have heqPower : mu = tau ^ j.val := by
    rw [htau]
    exact highParameter_intermediate_index_eq_power
      F K ht hres pi hpi hgen j
  have hpowChar : tau.1 ^ (j.val : ℤ) = mu.1 := by
    calc
      tau.1 ^ (j.val : ℤ) = (tau ^ j.val).1 := by
        simpa using (NormCharacter.coe_pow (F := F) (K := K) tau j.val).symm
      _ = mu.1 := congrArg (fun z : NormCharacter F K ↦ z.1) heqPower.symm
  have hmuNat :
      mu.1 (positiveUnitOfLattice F hJ.variableDepth_pos x) =
        psiF.character
          ((j.val : F) * norm F K (alpha1 : K) * (x : F) /
            (gammaF : F)) := by
    have hunit :
        (positiveUnitOfLattice F hJ.variableDepth_pos x : Fˣ) =
          positiveUnitOfLattice F
            (by omega : 0 < (t + 2) / 2) xs0 := by
      apply Units.ext
      simp [xs0]
    rw [hunit, ← hpowChar,
      IsStationaryRestrictionClass.continuousQuasiChar_zpow_apply,
      htauEval]
    let arg : F := norm F K (alpha1 : K) * (x : F) / (gammaF : F)
    calc
      psiF.character.toAddChar arg ^ (j.val : ℤ) =
          psiF.character.toAddChar ((j.val : ℤ) • arg) :=
        (AddChar.map_zsmul_eq_zpow psiF.character.toAddChar
          (j.val : ℤ) arg).symm
      _ = psiF.character.toAddChar
          ((j.val : F) * norm F K (alpha1 : K) * (x : F) /
            (gammaF : F)) := by
        apply congrArg psiF.character.toAddChar
        dsimp only [arg]
        simp only [zsmul_eq_mul]
        push_cast
        ring
      _ = psiF.character
          ((j.val : F) * norm F K (alpha1 : K) * (x : F) /
            (gammaF : F)) := rfl
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen
  have hteich : lam - (j.val : F) ∈ lattice F (((t + 1) / 2 : ℕ) : ℤ) := by
    simpa only [lam, p, T] using
      highParameter_intermediate_teichmuller_congruent
        F K (Module.finrank F K) (t + 1) hchar rfl htrace j
  have hdiffNumerator :
      (lam - (j.val : F)) * norm F K (alpha1 : K) * (x : F) ∈
        lattice F (chiF.conductor : ℤ) := by
    have hmul1 := mul_mem_lattice F hteich halphaNorm
    have hmul2 := mul_mem_lattice F hmul1 x.property
    have hsum : (t + 1) / 2 + (t + 2) / 2 = t + 1 := by omega
    apply lattice_antitone F (m := (chiF.conductor : ℤ))
      (n := (((t + 1) / 2 : ℕ) : ℤ) + (v : ℤ) +
        ((d + epsilon : ℕ) : ℤ))
    · rw [hm]
      push_cast
      exact_mod_cast (show t + 1 + v ≤ (t + 1) / 2 + v + (d + epsilon) by
        omega)
    · exact hmul2
  have hscaled :
      ((lam - (j.val : F)) * norm F K (alpha1 : K) * (x : F)) /
          (gammaF : F) ∈ lattice F (-psiF.conductor) := by
    apply (div_mem_lattice_iff F (gammaF : F) _
      ((chiF.conductor : ℤ) + psiF.conductor) (-psiF.conductor)
      hgammaF).2
    simpa [add_assoc] using hdiffNumerator
  have hmuEval :
      mu.1 (positiveUnitOfLattice F hJ.variableDepth_pos x) =
        psiF.character
          (lam * norm F K (alpha1 : K) * (x : F) /
            (gammaF : F)) := by
    rw [hmuNat]
    symm
    apply Units.ext
    apply (div_eq_one_iff_eq (Units.ne_zero _)).1
    have harg :
        lam * norm F K (alpha1 : K) * (x : F) / (gammaF : F) -
          (j.val : F) * norm F K (alpha1 : K) * (x : F) /
            (gammaF : F) =
        ((lam - (j.val : F)) * norm F K (alpha1 : K) * (x : F)) /
          (gammaF : F) := by ring
    have hdiv :
        psiF.character
            (lam * norm F K (alpha1 : K) * (x : F) / (gammaF : F)) /
          psiF.character
            ((j.val : F) * norm F K (alpha1 : K) * (x : F) /
              (gammaF : F)) = 1 := by
      calc
        _ = psiF.character.toAddChar
            (lam * norm F K (alpha1 : K) * (x : F) / (gammaF : F) -
              (j.val : F) * norm F K (alpha1 : K) * (x : F) /
                (gammaF : F)) :=
          (psiF.character.toAddChar.map_sub_eq_div _ _).symm
        _ = 1 := by
          rw [harg]
          exact psiF.isConductor.trivial _ hscaled
    simpa using congrArg Units.val hdiv
  have hbetaEval := highParameter_intermediate_selectedBeta_linearization
    F K ht hres pi hpi hgen chiF psiF hF gammaF hgammaF
      b beta hbcoe beta1 hbeta1 hbclass x
  rw [ramifiedNormCharacterOrbitTwistData_character,
    ContinuousQuasiChar.mul_apply, hmuEval, hbetaEval]
  calc
    psiF.character
        (lam * norm F K (alpha1 : K) * (x : F) / (gammaF : F)) *
      psiF.character
        (norm F K (beta1 : K) * (x : F) / (gammaF : F)) =
      psiF.character
        (lam * norm F K (alpha1 : K) * (x : F) / (gammaF : F) +
          norm F K (beta1 : K) * (x : F) / (gammaF : F)) :=
        (psiF.character.map_add_eq_mul _ _).symm
    _ = psiF.character
        ((norm F K (beta1 : K) + lam * norm F K (alpha1 : K)) *
          (x : F) / (gammaF : F)) := by
      congr 1
      ring


/-- Proposition `prop:high-parameter-table`, part (c), for every lower twist.
The exact norm `N(beta1+[j]*alpha1)` and the linear expression
`N(beta1)+[j]*N(alpha1)` define the same quotient class in `O_F/p_F^d`,
and that class is the stationary class at the twist's actual conductor. -/
theorem highParameter_intermediate_twistClass
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1))
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (a : lattice F
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (alpha : Fˣ) (hacoe : (a : F) = (alpha : F))
    (alpha1 : Kˣ)
    (halpha1 : IsSubcriticalNormRepresentative F K
      ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
      ((t + 1) / 2) alpha alpha1)
    (tau : NormCharacter F K)
    (htau : tau = ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K))))
    (ha : latticeQuotientMk F
        (sub_le_sub_left
          (highParameter_intermediate_normCharacterDepth
            F K ht hres pi hpi hgen htpos).int_le_conductor
          (chiF.conductor : ℤ)) a =
      stationaryNumeratorClass F
        (quasiCharDataOfIsConductor F tau.1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau (by
            rw [htau]
            exact highParameter_intermediate_indexOne_ne_one
              F K ht hres pi hpi hgen)))
        psiF (chiF.conductor : ℤ)
        (highParameter_intermediate_normCharacterDepth
          F K ht hres pi hpi hgen htpos)
        gammaF hgammaF)
    (b : lattice F 0) (beta : Fˣ) (hbcoe : (b : F) = (beta : F))
    (beta1 : Kˣ)
    (hbeta1 : IsSubcriticalNormRepresentative F K 0 d beta beta1)
    (hbclass : latticeQuotientMk F (by omega) b =
      stationaryCoefficientClass F chiF psiF hF gammaF hgammaF)
    (j : ZMod (Module.finrank F K)) :
    let p := Module.finrank F K
    let hchar := residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
    let lam := highIntermediateTeichmullerScalar F p hchar j
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    ∃ (hJ : IsStationaryConductorDecomposition twist.conductor d epsilon)
      (hgammaJ : ord F (gammaF : F) =
        (((twist.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
      (hlinearMem : norm F K (beta1 : K) +
          lam * norm F K (alpha1 : K) ∈ lattice F 0)
      (hnormMem : norm F K ((beta1 : K) +
          algebraMap F K lam * (alpha1 : K)) ∈ lattice F 0),
      latticeQuotientMk F (by omega)
          ⟨norm F K ((beta1 : K) +
            algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
        latticeQuotientMk F (Int.natCast_nonneg d)
          ⟨norm F K (beta1 : K) + lam * norm F K (alpha1 : K),
            hlinearMem⟩ ∧
      latticeQuotientMk F (Int.natCast_nonneg d)
          ⟨norm F K ((beta1 : K) +
            algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
        stationaryCoefficientClass F twist psiF hJ gammaF hgammaJ := by
  let p := Module.finrank F K
  let T := t + 1
  let v := chiF.conductor - T
  have hchar : residueCharacteristic F = p := by
    simpa [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  let lam := highIntermediateTeichmullerScalar F p hchar j
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd j)
  let twist := ramifiedNormCharacterOrbitTwistData
    F K ht hres pi hpi hgen chiF mu
  obtain ⟨hJ, hgammaJ, hlinearMem, hlinearClass⟩ :=
    highParameter_intermediate_twistLinearClass
      F K ht hres pi hpi hgen chiF psiF hF hminimal htpos hlower
        gammaF hgammaF a alpha hacoe alpha1 halpha1 tau htau ha b beta
        hbcoe beta1 hbeta1 hbclass j
  have hp : p.Prime := PrimeCyclicExtension.degree_prime F K
  have hpThree : 3 ≤ p := by
    have hpTwo := hp.two_le
    by_contra hnot
    have hpEq : p = 2 := by omega
    have hodd' : Odd p := by simpa only [p] using hodd
    rw [hpEq] at hodd'
    norm_num at hodd'
  have hm : chiF.conductor = T + v := by
    dsimp only [v, T]
    omega
  have hvT : v ≤ T := by
    dsimp only [v, T]
    omega
  have hcross : ∀ i : ℕ, 1 ≤ i → i < p →
      p * d ≤ i * v + (p - 1) * T :=
    highParameter_intermediate_twistCrossTermBound
      p T chiF.conductor d epsilon v
        hp.two_le hF.conductor_eq hm hvT
  have htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ) := by
    simpa only [p, T] using
      traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have halphaSource : ord K (alpha1 : K) = ((v : ℤ) : WithTop ℤ) := by
    simpa only [v, T, Int.ofNat_sub (by simpa only [T] using hlower)] using
      halpha1.source_order
  have hnormCong := highParameter_intermediate_norm_add_teichmuller_congruent
    F K p T d v hp (by dsimp [T]; omega) hchar rfl htrace hcross
      alpha1 beta1 halphaSource hbeta1.source_order j
  have h0d : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  have hnormMem : norm F K ((beta1 : K) +
      algebraMap F K lam * (alpha1 : K)) ∈ lattice F 0 := by
    have hdiff0 := lattice_antitone F h0d hnormCong
    have hadd := add_mem_lattice F hdiff0 hlinearMem
    convert hadd using 1 <;> ring
  refine ⟨hJ, hgammaJ, hlinearMem, hnormMem, ?_, ?_⟩
  · apply (latticeQuotientMk_eq_mk_iff F h0d).2
    exact hnormCong
  · calc
      latticeQuotientMk F h0d
          ⟨norm F K ((beta1 : K) +
            algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
        latticeQuotientMk F h0d
          ⟨norm F K (beta1 : K) + lam * norm F K (alpha1 : K),
            hlinearMem⟩ := by
          apply (latticeQuotientMk_eq_mk_iff F h0d).2
          exact hnormCong
      _ = stationaryCoefficientClass F twist psiF hJ gammaF hgammaJ :=
        hlinearClass


/-- The normalization interface used by `HighProduct` and `PhaseReduction`.
For supplied existential choices, `u=beta1/alpha1` and `n=N(u)` both have
order `-v`; the upstairs and lower-twist numerators factor literally as
`alphaN*(n-u)` and `alphaN*(n+[j])`. -/
theorem highParameter_intermediate_ratioData
    {v s r : ℕ} (alpha beta : Fˣ) (alpha1 beta1 : Kˣ)
    (halpha1 : IsSubcriticalNormRepresentative F K (v : ℤ) s alpha alpha1)
    (hbeta1 : IsSubcriticalNormRepresentative F K 0 r beta beta1)
    (lam : F) :
    let u : K := (beta1 : K) / (alpha1 : K)
    ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ) ∧
      ord F (norm F K u) = ((-(v : ℤ) : ℤ) : WithTop ℤ) ∧
      algebraMap F K (norm F K (beta1 : K)) -
          (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
            (alpha1 : K) =
        algebraMap F K (norm F K (alpha1 : K)) *
          (algebraMap F K (norm F K u) - u) ∧
      norm F K (beta1 : K) + lam * norm F K (alpha1 : K) =
        norm F K (alpha1 : K) * (norm F K u + lam) := by
  let u : K := (beta1 : K) / (alpha1 : K)
  have hu : ord K u = ((-(v : ℤ) : ℤ) : WithTop ℤ) := by
    dsimp only [u]
    rw [ord_div, hbeta1.source_order, halpha1.source_order]
    simp
  have hnu : ord F (norm F K u) =
      ((-(v : ℤ) : ℤ) : WithTop ℤ) := by
    rw [ord_norm, hu, hres, one_nsmul]
  have hnormDiv : norm F K ((beta1 : K) / (alpha1 : K)) =
      norm F K (beta1 : K) * (norm F K (alpha1 : K))⁻¹ := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  refine ⟨hu, hnu, ?_, ?_⟩
  · rw [hnormDiv]
    rw [map_mul, map_inv₀]
    field_simp [Units.ne_zero alpha1,
      (Algebra.norm_ne_zero_iff).2 (Units.ne_zero alpha1)]
  · rw [hnormDiv]
    field_simp [(Algebra.norm_ne_zero_iff).2 (Units.ne_zero alpha1)]



/-! ## Critical noncancellation and actual conductor drops -/

/-- At the inclusive boundary `m=T`, whole-orbit minimality excludes hidden
leading cancellation for every nonidentity norm character.  This is an
inequality of the final leading quotient class, not a statement about a
preferred field representative. -/
theorem highParameter_intermediate_critical_noCancellation
    (chiF : LocalQuasiCharData F)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hcritical : chiF.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (psiF : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      ((M + psiF.conductor : ℤ) : WithTop ℤ)) :
    stationaryLeadingClassProjection F M hr
      (stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psiF M hr gammaF hgammaF +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chiF.character (t + 1) (by
            simpa only [hcritical] using chiF.isConductor))
          psiF M hr gammaF hgammaF) ≠ 0 :=
  minimalOrbit_stationary F K ht hres pi hpi hgen chiF hminimal
    hcritical mu hmu psiF M hr gammaF hgammaF

/-- Before minimality, if a critical twist really drops but its actual
conductor `q'` is still greater than one, construct the new stationary class
at `q'` first and compare only its restriction with the old critical-layer
sum.  No old cancelled numerator is reused as the new class. -/
theorem highParameter_intermediate_stationaryClass_afterDrop
    (chiF : LocalQuasiCharData F) (hcritical : chiF.conductor = t + 1)
    (mu : NormCharacter F K) (hmu : mu ≠ 1)
    (q' : ℕ)
    (hprod : IsMultiplicativeConductor F (mu.1 * chiF.character) q')
    (hdrop : q' < t + 1) (hq' : 1 < q')
    (psiF : LocalAddCharData F) (M : ℤ) {r : ℕ}
    (hr : IsLamprechtStationaryDepth (t + 1) r)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      ((M + psiF.conductor : ℤ) : WithTop ℤ)) :
    droppedStationaryClassRestriction F
        (quasiCharDataOfIsConductor F (mu.1 * chiF.character) q' hprod)
        psiF M hr hdrop hq' gammaF hgammaF =
      stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F mu.1 (t + 1)
            (ramifiedNormCharacter_conductor
              F K ht hres pi hpi hgen mu hmu))
          psiF M hr gammaF hgammaF +
        stationaryNumeratorClass F
          (quasiCharDataOfIsConductor F chiF.character (t + 1) (by
            simpa only [hcritical] using chiF.isConductor))
          psiF M hr gammaF hgammaF :=
  criticalNormCharacterTwist_stationaryClass_afterDrop
    F K ht hres pi hpi hgen chiF hcritical mu hmu q' hprod hdrop hq'
      psiF M hr gammaF hgammaF

/-- At actual conductor zero or one no stationary depth exists, so the
intermediate API manufactures no stationary class. -/
theorem highParameter_intermediate_noStationaryClass_of_endpoint
    (prod : LocalQuasiCharData F) (hprod : prod.conductor ≤ 1) :
    ¬ ∃ r : ℕ, IsLamprechtStationaryDepth prod.conductor r :=
  normCharacterTwist_noStationaryClass_of_endpoint
    F K ht hres pi hpi hgen prod hprod

set_option maxHeartbeats 4000000 in
/-- The complete odd-prime high but non-stable parameter table.  It packages
the exact conductor identities, denominator-sensitive norm precision,
independent existential norm choices with their quotient ambiguity, the
norm-to-trace conversion, the upstairs adjoint class, and every actual lower
twist class. -/
theorem highParameter_intermediate
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hminimal : IsMinimalNormCharacterOrbitRepresentative F K chiF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (htpos : 0 < t)
    (hlower : t + 1 ≤ chiF.conductor)
    (hupper : chiF.conductor < 2 * (t + 1))
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    chiK.conductor = t + 1 +
        Module.finrank F K * (chiF.conductor - (t + 1)) ∧
      (∀ mu : NormCharacter F K,
        (ramifiedNormCharacterOrbitTwistData
          F K ht hres pi hpi hgen chiF mu).conductor = chiF.conductor) ∧
      ∃ h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
          chiF.conductor d epsilon,
        let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
        ∃ (a : lattice F
              ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)))
          (b : lattice F 0) (alpha beta : Fˣ) (alpha1 beta1 : Kˣ),
          (a : F) = (alpha : F) ∧
          (b : F) = (beta : F) ∧
          IsSubcriticalNormRepresentative F K
              ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
              ((t + 1) / 2) alpha alpha1 ∧
          IsSubcriticalNormRepresentative F K 0 d beta beta1 ∧
          latticeQuotientMk F
              (sub_le_sub_left
                (highParameter_intermediate_normCharacterDepth
                  F K ht hres pi hpi hgen htpos).int_le_conductor
                (chiF.conductor : ℤ)) a =
            stationaryNumeratorClass F
              (quasiCharDataOfIsConductor F tau.1 (t + 1)
                (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen tau
                  (highParameter_intermediate_indexOne_ne_one
                    F K ht hres pi hpi hgen)))
              psiF (chiF.conductor : ℤ)
              (highParameter_intermediate_normCharacterDepth
                F K ht hres pi hpi hgen htpos)
              gammaF hgammaF ∧
          latticeQuotientMk F (by omega) b =
            stationaryCoefficientClass F chiF psiF hF gammaF hgammaF ∧
          (∀ y : lattice K (((t + 2) / 2 : ℕ) : ℤ),
            psiF.character
                (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) =
              psiF.character
                ((-(norm F K (alpha1 : K))) * trace F K (y : K) /
                  (gammaF : F))) ∧
          ∃ hcandidate :
              algebraMap F K (norm F K (beta1 : K)) -
                  (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
                    (alpha1 : K) ∈ lattice K 0,
            let candidate : lattice K 0 :=
              ⟨algebraMap F K (norm F K (beta1 : K)) -
                  (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
                    (alpha1 : K), hcandidate⟩
            latticeQuotientMk K (by omega) candidate =
                normPolynomialAdjoint F K h psiF psiK gammaF
                  (Units.map (algebraMap F K) gammaF) hgammaF
                  (highParameter_intermediate_commonDenominator
                    F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal
                    hchi hpsi hlower gammaF hgammaF)
                  (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) ∧
              latticeQuotientMk K (by omega) candidate =
                stationaryCoefficientClass K chiK psiK hK
                  (Units.map (algebraMap F K) gammaF)
                  (highParameter_intermediate_commonDenominator
                    F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal
                    hchi hpsi hlower gammaF hgammaF) ∧
              ∀ j : ZMod (Module.finrank F K),
                let p := Module.finrank F K
                let hchar := residueCharacteristic_eq_degree_of_positive_break
                  F K ht htpos pi hpi hgen
                let lam := highIntermediateTeichmullerScalar F p hchar j
                let mu := ramifiedNormCharacterZModEquiv
                  F K ht hres pi hpi hgen (Multiplicative.ofAdd j)
                let twist := ramifiedNormCharacterOrbitTwistData
                  F K ht hres pi hpi hgen chiF mu
                ∃ (hJ : IsStationaryConductorDecomposition
                    twist.conductor d epsilon)
                  (hgammaJ : ord F (gammaF : F) =
                    (((twist.conductor : ℤ) + psiF.conductor : ℤ) :
                      WithTop ℤ))
                  (hlinearMem : norm F K (beta1 : K) +
                    lam * norm F K (alpha1 : K) ∈ lattice F 0)
                  (hnormMem : norm F K ((beta1 : K) +
                    algebraMap F K lam * (alpha1 : K)) ∈ lattice F 0),
                  latticeQuotientMk F (Int.natCast_nonneg d)
                      ⟨norm F K ((beta1 : K) +
                        algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
                    latticeQuotientMk F (Int.natCast_nonneg d)
                      ⟨norm F K (beta1 : K) +
                        lam * norm F K (alpha1 : K), hlinearMem⟩ ∧
                  latticeQuotientMk F (Int.natCast_nonneg d)
                      ⟨norm F K ((beta1 : K) +
                        algebraMap F K lam * (alpha1 : K)), hnormMem⟩ =
                    stationaryCoefficientClass F twist psiF hJ
                      gammaF hgammaJ := by
  have hmK := highParameter_intermediate_conductor_eq
    F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
  refine ⟨hmK, ?_, ?_⟩
  · intro mu
    exact highParameter_intermediate_twist_conductor_eq
      F K ht hres pi hpi hgen chiF hminimal hlower mu
  · let h := highParameter_intermediate_precision
      F K ht hres pi hpi hgen chiF chiK hF hK hminimal hchi hodd htpos
        hlower hupper
    refine ⟨h, ?_⟩
    let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
    have htau : tau ≠ 1 := highParameter_intermediate_indexOne_ne_one
      F K ht hres pi hpi hgen
    obtain ⟨a, b, alpha, beta, alpha1, beta1, hacoe, hbcoe,
      halpha1, hbeta1, ha, hb⟩ :=
      highParameter_intermediate_normRepresentatives
        F K ht hres pi hpi hgen chiF psiF hF htpos hupper tau htau
          gammaF hgammaF
    refine ⟨a, b, alpha, beta, alpha1, beta1, hacoe, hbcoe,
      halpha1, hbeta1, ?_, hb, ?_, ?_⟩
    · simpa only [tau] using ha
    · have hm : chiF.conductor = t + 1 +
          (chiF.conductor - (t + 1)) := (Nat.add_sub_of_le hlower).symm
      have hlinear := highParameter_intermediate_selectedAlpha_linearization
        F K ht hres pi hpi hgen htpos chiF psiF hm tau htau gammaF hgammaF
          a alpha hacoe alpha1 halpha1 ha
      have halpha : ord F (norm F K (alpha1 : K)) =
          ((((chiF.conductor - (t + 1) : ℕ) : ℤ) : WithTop ℤ)) := by
        simpa only [Nat.cast_sub hlower] using halpha1.norm_order
      have hgammaF' : ord F (gammaF : F) =
          (((t + 1 : ℕ) : ℤ) +
            ((chiF.conductor - (t + 1) : ℕ) : ℤ) +
              psiF.conductor : WithTop ℤ) := by
        rw [hgammaF]
        congr 1
        rw [Nat.cast_sub hlower]
        ring
      exact highParameter_intermediate_normCharacterConversion
        F K ht hres pi hpi hgen htpos psiF tau alpha1 halpha gammaF
          hgammaF' hlinear
    · have hmrel := highParameter_intermediate_conductor_relation
        F K ht hres pi hpi hgen chiF chiK hminimal hchi hlower
      have harith := highParameter_intermediate_depthArithmetic
        F K ht hres pi hpi hgen
        (p := Module.finrank F K) (T := t + 1)
        hodd (by
          have hpTwo := (PrimeCyclicExtension.degree_prime F K).two_le
          by_contra hnot
          have hpEq : Module.finrank F K = 2 := by omega
          rw [hpEq] at hodd
          norm_num at hodd) (by omega) hF hK hlower hupper hmrel hmK
      have hterms := highParameter_intermediate_intermediateTerms
        F K ht hres pi hpi hgen chiF chiK hF hK hminimal hchi hodd htpos
          hlower hupper
      have hgammaK := highParameter_intermediate_commonDenominator
        F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal hchi hpsi
          hlower gammaF hgammaF
      have hconversion : ∀ y : lattice K (((t + 2) / 2 : ℕ) : ℤ),
          psiF.character
              (norm F K (alpha1 : K) * norm F K (y : K) / (gammaF : F)) =
            psiF.character
              ((-(norm F K (alpha1 : K))) * trace F K (y : K) /
                (gammaF : F)) := by
        have hm : chiF.conductor = t + 1 +
            (chiF.conductor - (t + 1)) := (Nat.add_sub_of_le hlower).symm
        have hlinear := highParameter_intermediate_selectedAlpha_linearization
          F K ht hres pi hpi hgen htpos chiF psiF hm tau htau gammaF
            hgammaF a alpha hacoe alpha1 halpha1 ha
        have halpha : ord F (norm F K (alpha1 : K)) =
            ((((chiF.conductor - (t + 1) : ℕ) : ℤ) : WithTop ℤ)) := by
          simpa only [Nat.cast_sub hlower] using halpha1.norm_order
        have hgammaF' : ord F (gammaF : F) =
            (((t + 1 : ℕ) : ℤ) +
              ((chiF.conductor - (t + 1) : ℕ) : ℤ) +
                psiF.conductor : WithTop ℤ) := by
          rw [hgammaF]
          congr 1
          rw [Nat.cast_sub hlower]
          ring
        exact highParameter_intermediate_normCharacterConversion
          F K ht hres pi hpi hgen htpos psiF tau alpha1 halpha gammaF
            hgammaF' hlinear
      have halpha1' : IsSubcriticalNormRepresentative F K
          ((chiF.conductor - (t + 1) : ℕ) : ℤ) ((t + 1) / 2)
            alpha alpha1 := by
        simpa only [Nat.cast_sub hlower] using halpha1
      obtain ⟨hcandidate, hadjoint, hupstairs⟩ :=
        highParameter_intermediate_upstairsClass_core
        F K (t := t) chiF chiK psiF psiK h hchi hpsi hterms
          harith.shiftedVariableDepth gammaF hgammaF hgammaK alpha alpha1
          halpha1' beta beta1 hbeta1 b hbcoe hb hconversion
      refine ⟨hcandidate, hadjoint, hupstairs, ?_⟩
      intro j
      exact highParameter_intermediate_twistClass
        F K ht hres pi hpi hgen chiF psiF hF hminimal hodd htpos hlower
          hupper gammaF hgammaF a alpha hacoe alpha1 halpha1 tau rfl ha
          b beta hbcoe beta1 hbeta1 hb j


end
end LanglandsFirstMainLemma
