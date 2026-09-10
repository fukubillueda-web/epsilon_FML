import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsFirstMainLemma.Ramification.PullbackConductors
import LanglandsFirstMainLemma.Ramification.UnramifiedCompatibility

/-!
# High stationary classes in the trace-stable cases

This file proves the unramified, stable odd-prime ramified, and tame
quadratic rows of the manuscript's high-conductor stationary-parameter
table.  Every principal result is an equality in the literal coefficient
quotient `O_K / p_K^dK`.  In particular, the occurrence of a downstairs
coefficient on the right means its quotient-class image under `F -> K`; no
field-valued stationary representative is selected.

The adjoint always retains the ordered denominator pair.  The displayed
specializations use the common pair `(gammaF, algebraMap gammaF)` only after
the conductor identities have proved that the downstairs denominator is
admissible upstairs.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 2000000

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-! ## Quotient-level trace specialization -/

set_option maxHeartbeats 2000000 in
/-- If the stationary truncated norm is trace at the exact source and
target depths, then the stationary numerator upstairs is the common-
denominator quotient-class image of the downstairs stationary numerator.
This helper is deliberately stated with both denominator admissibility
proofs and with the ramification-scaled coefficient-depth inequality. -/
private theorem stationaryClass_eq_commonDenominatorImage_of_trace
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K
      ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
        (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K chiK.conductor chiF.conductor)
    (hintermediate : NormPolynomialIntermediateTermsVanishAt F K
      (dK + epsilonK) chiF.conductor)
    (hterminal : NormPolynomialTerminalTermVanishAt F K
      (dK + epsilonK) chiF.conductor)
    (hdepth : dK ≤ ramificationIndex F K * dF) :
    stationaryCoefficientClass K chiK psiK h.sourceDecomposition
        (Units.map (algebraMap F K) gammaF) hgammaK =
      denominatorScaledAlgebraMap F K dF dK hdepth gammaF
        (Units.map (algebraMap F K) gammaF)
        (by simp [normPolynomialDenominatorRatio])
        (stationaryCoefficientClass F chiF psiF h.targetDecomposition
          gammaF hgammaF) := by
  have htrace : normPolynomial F K h =
      normPolynomialTrace F K h hvariable hconductor :=
    normPolynomial_eq_trace F K h hvariable hconductor
      hintermediate hterminal
  have hstationary :=
    stationaryClass_compNorm F K chiF chiK psiF psiK
      (dK := dK) (epsilonK := epsilonK)
      (dF := dF) (epsilonF := epsilonF) h hchi hpsi
      gammaF (Units.map (algebraMap F K) gammaF) hgammaF hgammaK
  have hmaps := normPolynomialAdjoint_eq_denominatorScaledAlgebraMap F K h
      psiF psiK hpsi gammaF (Units.map (algebraMap F K) gammaF)
      hgammaF hgammaK hvariable hconductor htrace hdepth
      (by simp [normPolynomialDenominatorRatio])
  have hadjoint := congrArg
    (fun A : StationaryCoefficientQuotient F dF →+
        StationaryCoefficientQuotient K dK ↦
      A (stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF)) hmaps
  exact hstationary.trans hadjoint

/-- A norm-filtration containment remains valid after replacing the source
by a deeper unit-filtration layer. -/
private theorem normUnitFiltrationInclusion_of_source_le
    {sourceDepth sourceDepth' targetDepth : ℕ}
    (hsource : sourceDepth ≤ sourceDepth')
    (hmap : NormUnitFiltrationInclusion F K sourceDepth targetDepth) :
    NormUnitFiltrationInclusion F K sourceDepth' targetDepth := by
  intro u hu
  exact hmap u (unitFiltration_antitone K hsource hu)

/-! ## Unramified bounds -/

private theorem highParameters_nonarchimedeanLocalFieldInfinite
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Infinite E := by
  let f : ℤ → E := fun n => (exists_ord_eq E n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord E (f m) = (m : WithTop ℤ) :=
      (exists_ord_eq E m).choose_spec
    have hn : ord E (f n) = (n : WithTop ℤ) :=
      (exists_ord_eq E n).choose_spec
    have hcoe : (m : WithTop ℤ) = (n : WithTop ℤ) := hm.symm.trans <|
      (congrArg (ord E) hmn).trans hn
    exact WithTop.coe_injective hcoe
  exact Infinite.of_injective f hf

/-- In an unramified Galois extension, the `j`-th elementary symmetric
coefficient of an element of depth `a` has depth at least `j*a` downstairs.
The proof keeps the unramified factor `e=1` visible through
`ord_algebraMap`. -/
private theorem unramified_elementarySymmetric_bound
    [IsGalois F K]
    (hunr : ramificationIndex F K = 1)
    (a : ℤ) {x : K} (hx : (a : WithTop ℤ) ≤ ord K x)
    (j : ℕ) (hj : j ≤ Module.finrank F K) :
    (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord F (elementarySymmetric F K j x) := by
  classical
  letI : Infinite F := highParameters_nonarchimedeanLocalFieldInfinite F
  have hprod (s : Finset Gal(K/F)) :
      s.card • (a : WithTop ℤ) ≤ ord K (∏ sigma ∈ s, sigma x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert sigma s hs ih =>
        have hsigma : (a : WithTop ℤ) ≤ ord K (sigma x) := by
          simpa using hx
        simpa [Finset.card_insert_of_notMem, hs, succ_nsmul, add_comm] using
          add_le_add hsigma ih
  have hup : (((j : ℤ) * a : ℤ) : WithTop ℤ) ≤
      ord K (algebraMap F K (elementarySymmetric F K j x)) := by
    rw [algebraMap_elementarySymmetric_eq_esymm_galois,
      galoisConjugates, Finset.esymm_map_val]
    apply ord_sum K
    intro s hs
    have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
    have hsbound := hprod s
    rw [hcard] at hsbound
    calc
      (((j : ℤ) * a : ℤ) : WithTop ℤ) = j • (a : WithTop ℤ) := by
        rw [← WithTop.coe_nsmul]
        congr
      _ ≤ ord K (∏ sigma ∈ s, sigma x) := hsbound
  rw [ord_algebraMap, hunr, one_nsmul] at hup
  exact hup

/-! ## The unramified row -/

/-- Exact preservation of the multiplicative conductor in the unramified
row. -/
theorem highParameter_unramified_conductor_eq
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hunr : ramificationIndex F K = 1) :
    chiK.conductor = chiF.conductor := by
  apply chiK.isConductor.unique
  rw [hchi]
  exact (unramified_multiplicativeConductor_compNorm F K hunr
    chiF.character chiF.conductor).2 chiF.isConductor

/-- Exact preservation of the additive conductor under trace in the
unramified row. -/
theorem highParameter_unramified_additiveConductor_eq
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hunr : ramificationIndex F K = 1) :
    psiK.conductor = psiF.conductor := by
  apply psiK.isConductor.unique
  rw [hpsi]
  exact (unramified_additiveConductor_compTrace F K hunr
    psiF.character psiF.conductor).2 psiF.isConductor

/-- The actual upstairs conductor has the same stationary decomposition in
the unramified case. -/
theorem highParameter_unramified_sourceDecomposition
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hunr : ramificationIndex F K = 1) :
    IsStationaryConductorDecomposition chiK.conductor d epsilon := by
  rw [highParameter_unramified_conductor_eq F K chiF chiK hchi hunr]
  exact hF

/-- A downstairs admissible denominator remains admissible upstairs for
the common denominator pair in the unramified row. -/
theorem highParameter_unramified_commonDenominator
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hunr : ramificationIndex F K = 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ) := by
  change ord K (algebraMap F K (gammaF : F)) = _
  calc
    ord K (algebraMap F K (gammaF : F)) =
        ramificationIndex F K • ord F (gammaF : F) :=
      ord_algebraMap F K (gammaF : F)
    _ = ord F (gammaF : F) := by rw [hunr, one_nsmul]
    _ = (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ) :=
      hgammaF
    _ = (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ) := by
      rw [highParameter_unramified_conductor_eq F K chiF chiK hchi hunr,
        highParameter_unramified_additiveConductor_eq F K psiF psiK hpsi hunr]

/-- The three exact stationary norm-filtration inclusions in the
unramified row, at source/target depths `d+epsilon`, `m`, and `d`. -/
private theorem highParameter_unramified_precision
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hunr : ramificationIndex F K = 1) :
    NormPolynomialPrecision F K chiK.conductor d epsilon
      chiF.conductor d epsilon where
  sourceDecomposition :=
    highParameter_unramified_sourceDecomposition F K chiF chiK hF hchi hunr
  targetDecomposition := hF
  variable_inclusion := fun u hu ↦
    unramified_norm_mem_unitFiltration F K hunr (d + epsilon) hu
  conductor_inclusion := fun u hu ↦
    unramified_norm_mem_unitFiltration F K hunr chiF.conductor <| by
      rw [← highParameter_unramified_conductor_eq F K chiF chiK hchi hunr]
      exact hu
  ambiguity_inclusion := fun u hu ↦
    unramified_norm_mem_unitFiltration F K hunr d hu

private theorem highParameter_unramified_intermediateTerms
    [PrimeCyclicExtension F K]
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hunr : ramificationIndex F K = 1) :
    NormPolynomialIntermediateTermsVanishAt F K
      (d + epsilon) chiF.conductor := by
  intro x hx j hjtwo hjlt
  rw [mem_lattice]
  have htwo : chiF.conductor ≤ 2 * (d + epsilon) :=
    hF.conductor_le_two_variableDepth
  have hjdepth : 2 * (d + epsilon) ≤ j * (d + epsilon) :=
    Nat.mul_le_mul_right (d + epsilon) hjtwo
  have hcast :
      (((chiF.conductor : ℕ) : ℤ) : WithTop ℤ) ≤
        ((((j * (d + epsilon) : ℕ) : ℤ)) : WithTop ℤ) := by
    exact_mod_cast htwo.trans hjdepth
  have hbound := unramified_elementarySymmetric_bound F K hunr
    ((d + epsilon : ℕ) : ℤ) hx j hjlt.le
  exact hcast.trans (by simpa only [Nat.cast_mul] using hbound)

private theorem highParameter_unramified_terminalTerm
    [PrimeCyclicExtension F K]
    (chiF : LocalQuasiCharData F) {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hunr : ramificationIndex F K = 1) :
    NormPolynomialTerminalTermVanishAt F K
      (d + epsilon) chiF.conductor := by
  intro x hx
  rw [mem_lattice]
  have hdegreeTwo : 2 ≤ Module.finrank F K :=
    (PrimeCyclicExtension.degree_prime F K).two_le
  have htwo : chiF.conductor ≤ 2 * (d + epsilon) :=
    hF.conductor_le_two_variableDepth
  have hdegreeDepth : 2 * (d + epsilon) ≤
      Module.finrank F K * (d + epsilon) :=
    Nat.mul_le_mul_right (d + epsilon) hdegreeTwo
  have hcast :
      (((chiF.conductor : ℕ) : ℤ) : WithTop ℤ) ≤
        (((Module.finrank F K * (d + epsilon) : ℕ) : ℤ) : WithTop ℤ) := by
    exact_mod_cast htwo.trans hdegreeDepth
  have hbound := unramified_elementarySymmetric_bound F K hunr
    ((d + epsilon : ℕ) : ℤ) hx (Module.finrank F K) le_rfl
  exact hcast.trans (by simpa only [Nat.cast_mul] using hbound)

/-- **Unramified high stationary class (`P^*(beta)=beta`).**

For the actual preserved upstairs conductor and the common ordered
denominator pair, the upstairs stationary numerator class is the natural
quotient image of the downstairs class.  The equality lives in
`O_K / p_K^d`; it does not choose, or assert equality of, representatives
in `K`. -/
theorem highParameter_unramified
    [PrimeCyclicExtension F K]
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hunr : ramificationIndex F K = 1)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    stationaryCoefficientClass K chiK psiK
        (highParameter_unramified_sourceDecomposition F K chiF chiK
          hF hchi hunr)
        (Units.map (algebraMap F K) gammaF)
        (highParameter_unramified_commonDenominator F K chiF chiK psiF psiK
          hchi hpsi hunr gammaF hgammaF) =
      denominatorScaledAlgebraMap F K d d (by simp [hunr]) gammaF
        (Units.map (algebraMap F K) gammaF)
        (by simp [normPolynomialDenominatorRatio])
        (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
  let h := highParameter_unramified_precision F K chiF chiK hF hchi hunr
  have hvariable : TraceLatticeInclusion F K (d + epsilon) (d + epsilon) :=
    fun _ hx ↦ trace_mem_lattice F K hunr _ hx
  have hconductor :
      TraceLatticeInclusion F K chiK.conductor chiF.conductor := by
    intro x hx
    apply trace_mem_lattice F K hunr (chiF.conductor : ℤ)
    simpa [highParameter_unramified_conductor_eq F K chiF chiK hchi hunr] using hx
  have hintermediate :=
    highParameter_unramified_intermediateTerms F K chiF hF hunr
  have hterminal := highParameter_unramified_terminalTerm F K chiF hF hunr
  have hdepth : d ≤ ramificationIndex F K * d := by simp [hunr]
  exact stationaryClass_eq_commonDenominatorImage_of_trace F K
    chiF chiK psiF psiK h hchi hpsi gammaF hgammaF
    (highParameter_unramified_commonDenominator F K chiF chiK psiF psiK
      hchi hpsi hunr gammaF hgammaF)
    hvariable hconductor hintermediate hterminal hdepth

/-! ## Ramified high-range arithmetic -/

private structure StableOddDepthArithmetic
    (ell T m d epsilon mK dK epsilonK : ℕ) : Prop where
  epsilon_eq : epsilonK = epsilon
  coefficientDepth_eq :
    ∃ z : ℕ, dK = d + z ∧ d ≤ z
  variableDepth_ge_conductor : m ≤ dK + epsilonK
  coefficientDepth_le : dK ≤ ell * d
  trace_variable_bound :
    ell * (d + epsilon) ≤ dK + epsilonK + (ell - 1) * T
  nonlinear_vanishing_bound :
    ell * m ≤ 2 * (dK + epsilonK) + (ell - 1) * T

/-- Subtraction-free arithmetic for the stable odd-degree range.  Writing
`ell = 2*k+1`, the proof obtains
`mK = m + 2*k*(m-T)`, `epsilonK=epsilon`, and
`dK=d+k*(m-T)` before deriving all inequalities used below. -/
private theorem stableOddDepthArithmetic
    {ell T m d epsilon mK dK epsilonK : ℕ}
    (hodd : Odd ell) (hellThree : 3 ≤ ell) (hT : 1 ≤ T)
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hK : IsStationaryConductorDecomposition mK dK epsilonK)
    (hd : T ≤ d)
    (hmrel : mK + (ell - 1) * T = ell * m) :
    StableOddDepthArithmetic ell T m d epsilon mK dK epsilonK := by
  rcases hodd with ⟨k, hk⟩
  have hkpos : 1 ≤ k := by omega
  have hepsilon_le : epsilon ≤ 1 := hF.epsilon_le_one
  have hepsilonK_le : epsilonK ≤ 1 := hK.epsilon_le_one
  have hTm : T ≤ m := by rw [hF.conductor_eq]; omega
  let z : ℕ := k * (m - T)
  have hmSplit : m = T + (m - T) := (Nat.add_sub_of_le hTm).symm
  have hkSplit : k * m = k * T + z := by
    rw [hmSplit, mul_add]
  have hmKform : mK = m + 2 * z := by
    rw [hk] at hmrel
    have hellSub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hellSub, add_mul, one_mul] at hmrel
    nlinarith [hkSplit]
  have hepsilon : epsilonK = epsilon := by
    rw [hK.conductor_eq, hF.conductor_eq] at hmKform
    omega
  have hdK : dK = d + z := by
    rw [hK.conductor_eq, hF.conductor_eq, hepsilon] at hmKform
    omega
  have hdmT : d ≤ m - T := by
    rw [hF.conductor_eq]
    omega
  have hdz : d ≤ z := by
    calc
      d ≤ m - T := hdmT
      _ = 1 * (m - T) := by simp
      _ ≤ k * (m - T) := Nat.mul_le_mul_right (m - T) hkpos
      _ = z := rfl
  have hqge : m ≤ dK + epsilonK := by
    rw [hdK, hepsilon, hF.conductor_eq]
    omega
  have hmTle : m - T ≤ 2 * d := by
    rw [hF.conductor_eq]
    omega
  have hzle : z ≤ 2 * k * d := by
    calc
      z = k * (m - T) := rfl
      _ ≤ k * (2 * d) := Nat.mul_le_mul_left k hmTle
      _ = 2 * k * d := by ring
  have hdKle : dK ≤ ell * d := by
    rw [hdK, hk]
    nlinarith
  have hepsilonT : epsilon ≤ T := hF.epsilon_le_one.trans hT
  have htwoq : 2 * (d + epsilon) ≤ m + T := by
    rw [hF.conductor_eq]
    omega
  have htraceVariable :
      ell * (d + epsilon) ≤ dK + epsilonK + (ell - 1) * T := by
    rw [hk, hdK, hepsilon]
    change (2 * k + 1) * (d + epsilon) ≤
      d + z + epsilon + (2 * k + 1 - 1) * T
    have hellSub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hellSub]
    have hkBound : 2 * k * (d + epsilon) ≤ k * (m + T) := by
      calc
        2 * k * (d + epsilon) = k * (2 * (d + epsilon)) := by ring
        _ ≤ k * (m + T) := Nat.mul_le_mul_left k htwoq
    have hmTform : m + T = (m - T) + 2 * T := by omega
    have hzD : z + 2 * k * T = k * (m + T) := by
      dsimp only [z]
      rw [hmTform, mul_add]
      ring
    have hmain : 2 * k * (d + epsilon) ≤ z + 2 * k * T := by
      rw [hzD]
      exact hkBound
    calc
      (2 * k + 1) * (d + epsilon) =
          (d + epsilon) + 2 * k * (d + epsilon) := by ring
      _ ≤ (d + epsilon) + (z + 2 * k * T) :=
        Nat.add_le_add_left hmain _
      _ = d + z + epsilon + 2 * k * T := by ring
  have hnonlinear :
      ell * m ≤ 2 * (dK + epsilonK) + (ell - 1) * T := by
    rw [← hmrel, hK.conductor_eq]
    omega
  exact ⟨hepsilon, ⟨z, hdK, hdz⟩, hqge, hdKle,
    htraceVariable, hnonlinear⟩

section RamifiedPrime

variable [PrimeCyclicExtension F K]

variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

/-- PullbackConductors supplies the actual high-range upstairs conductor. -/
theorem highParameter_ramified_conductor_eq
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hm : t + 1 < chiF.conductor) :
    chiK.conductor =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1 :=
  chiF.conductor_compNorm_eq_high F K ht hres pi hpi hgen chiK hchi hm

/-- Subtraction-free form of the ramified high conductor formula, with
`D=(ell-1)(t+1)` kept explicit. -/
theorem highParameter_ramified_conductor_relation
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hm : t + 1 < chiF.conductor) :
    chiK.conductor +
        (Module.finrank F K - 1) * (t + 1) =
      Module.finrank F K * chiF.conductor := by
  have hz := chiF.conductor_compNorm_eq_high_explicit
    F K ht hres pi hpi hgen chiK hchi hm
  have hz' :
      (chiK.conductor : ℤ) +
          (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) =
        (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) := by
    rw [hz]
    ring
  exact_mod_cast hz'

/-- In the ramified high range the common denominator is admissible
upstairs.  The proof records `e=ell`, `f=1`, the multiplicative correction
`-D`, and the additive correction `+D`. -/
theorem highParameter_ramified_commonDenominator
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : t + 1 < chiF.conductor)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ord K ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  have hsum := high_compNorm_add_compTrace_conductor_eq
    F K ht hres pi hpi hgen chiF chiK psiF psiK hchi hpsi hm
  change ord K (algebraMap F K (gammaF : F)) = _
  rw [ord_algebraMap, hram, hgammaF, ← WithTop.coe_nsmul]
  change (((Module.finrank F K : ℤ) *
      ((chiF.conductor : ℤ) + psiF.conductor) : ℤ) : WithTop ℤ) = _
  rw [← hsum]

private theorem ramifiedIndex_eq_degree :
    ramificationIndex F K = Module.finrank F K := by
  have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
  rw [hres, mul_one] at hdegree
  exact hdegree.symm

/-- The exact trace-ideal floor supplies a requested trace-lattice
containment once its numerator inequality is recorded in natural numbers. -/
private theorem ramified_traceLatticeInclusion_of_bound
    (sourceDepth targetDepth : ℕ)
    (hbound : Module.finrank F K * targetDepth ≤
      sourceDepth + (Module.finrank F K - 1) * (t + 1)) :
    TraceLatticeInclusion F K sourceDepth targetDepth := by
  intro x hx
  rw [mem_lattice]
  have htrace := traceIdealLowerBound_of_integralGenerator
    F K ht hres pi hpi hgen (sourceDepth : ℤ) x hx
  apply (show (((targetDepth : ℕ) : ℤ) : WithTop ℤ) ≤
      (((((sourceDepth : ℕ) : ℤ) +
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) /
          (Module.finrank F K : ℤ) : ℤ) : WithTop ℤ) by
    apply WithTop.coe_le_coe.mpr
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast Module.finrank_pos)]
    have hbound' : targetDepth * Module.finrank F K ≤
        sourceDepth + (Module.finrank F K - 1) * (t + 1) := by
      simpa [mul_comm] using hbound
    exact_mod_cast hbound').trans htrace

private theorem ramified_stationaryVariableSource_le
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
  have hhalf := herbrandPsiNat_half_le_half t (Module.finrank F K)
    Module.finrank_pos (chiF.conductor - 1)
  rw [hlast] at hhalf
  rw [hK.conductor_eq] at hmK
  omega

private theorem ramified_stable_ambiguitySource_le
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hmK : chiK.conductor =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1)
    (hd : t + 1 ≤ d)
    (hdK : d ≤ dK) :
    herbrandPsiNat t (Module.finrank F K) (d - 1) + 1 ≤ dK := by
  rcases eq_or_lt_of_le hd with hboundary | hstrict
  · have hdt : d - 1 = t := by omega
    rw [hdt, herbrandPsiNat_break]
    omega
  · have hid := herbrandPsiNat_stationary_depth t
      (Module.finrank F K) Module.finrank_pos (by omega : t + 2 ≤ d) epsilon
    have hlast : chiF.conductor - 1 = 2 * d + epsilon - 1 := by
      rw [hF.conductor_eq]
    rw [← hlast] at hid
    rw [hK.conductor_eq] at hmK
    have hepsilonK := hK.epsilon_le_one
    omega

private theorem highParameter_stableOdd_precision
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hmK : chiK.conductor =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1)
    (hd : t + 1 ≤ d) (hdK : d ≤ dK) :
    NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor d epsilon where
  sourceDecomposition := hK
  targetDecomposition := hF
  variable_inclusion := by
    have hsource := ramified_stationaryVariableSource_le F K
      ht hres pi hpi hgen chiF chiK hF hK hmK
    have hmap := normMapsUnitFiltration_herbrand_succ
      F K ht hres pi hpi hgen (d + epsilon - 1)
    intro u hu
    have hu' := unitFiltration_antitone K hsource hu
    have hout := hmap u hu'
    have htarget : d + epsilon - 1 + 1 = d + epsilon := by
      omega
    simpa only [htarget] using hout
  conductor_inclusion := by
    have hmap := normMapsUnitFiltration_herbrand_succ
      F K ht hres pi hpi hgen (chiF.conductor - 1)
    intro u hu
    have hu' : u ∈ unitFiltration K
        (herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1) := by
      rw [← hmK]
      exact hu
    have hout := hmap u hu'
    have hmpos := hF.conductor_gt_one
    have htarget : chiF.conductor - 1 + 1 = chiF.conductor := by omega
    simpa only [htarget] using hout
  ambiguity_inclusion := by
    have hsource := ramified_stable_ambiguitySource_le F K ht hres pi hpi hgen
      chiF chiK hF hK hmK hd hdK
    have hmap := normMapsUnitFiltration_herbrand_succ
      F K ht hres pi hpi hgen (d - 1)
    intro u hu
    have hu' := unitFiltration_antitone K hsource hu
    have hout := hmap u hu'
    have htarget : d - 1 + 1 = d := by omega
    simpa only [htarget] using hout

private theorem highParameter_stableOdd_intermediateTerms
    (chiF : LocalQuasiCharData F)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition
      (herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1)
      dK epsilonK)
    (harith : StableOddDepthArithmetic (Module.finrank F K) (t + 1)
      chiF.conductor d epsilon
      (herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1)
      dK epsilonK) :
    NormPolynomialIntermediateTermsVanishAt F K
      (dK + epsilonK) chiF.conductor := by
  rcases eq_or_ne t 0 with rfl | htne
  · intro x hx j hjtwo hjlt
    rw [mem_lattice]
    have hram := ramifiedIndex_eq_degree F K ht hres pi hpi hgen
    have hbound := totallyRamified_elementarySymmetric_bound F K
      (Module.finrank F K) ((dK + epsilonK : ℕ) : ℤ)
      Module.finrank_pos rfl hram hx j hjlt.le
    apply (show (((chiF.conductor : ℕ) : ℤ) : WithTop ℤ) ≤
        (integerCeilingDiv
          ((j : ℤ) * ((dK + epsilonK : ℕ) : ℤ))
          (Module.finrank F K) : ℤ) by
      apply WithTop.coe_le_coe.mpr
      rw [integerCeilingDiv,
        Int.le_ediv_iff_mul_le (by exact_mod_cast Module.finrank_pos)]
      have hjq : 2 * (dK + epsilonK) ≤ j * (dK + epsilonK) :=
        Nat.mul_le_mul_right (dK + epsilonK) hjtwo
      have hnum : Module.finrank F K * chiF.conductor ≤
          j * (dK + epsilonK) + (Module.finrank F K - 1) := by
        have hbase := harith.nonlinear_vanishing_bound
        norm_num at hbase
        omega
      have hcast :
          (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) ≤
            (j : ℤ) * ((dK + epsilonK : ℕ) : ℤ) +
              (Module.finrank F K : ℤ) - 1 := by
        have hcast' :
            (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) ≤
              (j : ℤ) * ((dK + epsilonK : ℕ) : ℤ) +
                ((Module.finrank F K - 1 : ℕ) : ℤ) := by
          exact_mod_cast hnum
        rw [Nat.cast_sub (by exact
          (PrimeCyclicExtension.degree_prime F K).one_le), Nat.cast_one] at hcast'
        omega
      simpa [mul_comm] using hcast).trans hbound
  · have htpos : 0 < t := Nat.pos_of_ne_zero htne
    have hchar := residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
    exact wild_normPolynomialIntermediateTermsVanishAt F K
      (Module.finrank F K) (t + 1) (dK + epsilonK) chiF.conductor
      (PrimeCyclicExtension.degree_prime F K) (by omega) hchar rfl
      (traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen)
      harith.nonlinear_vanishing_bound

/-- **Stable odd-degree ramified high stationary class.**

Assume the manuscript's exact inequality `d >= t+1`.  The proof splits on
the zero/positive break and derives the wild characteristic equality in the
positive-break branch.  PullbackConductors fixes the actual upstairs
conductor, all three norm depths are constructed at that conductor, the
trace and every nonlinear norm term are checked at the source
`p_K^(dK+epsilonK)`, and the common-denominator adjoint sends the
downstairs numerator class to its natural quotient image upstairs. -/
theorem highParameter_stableOdd
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon dK epsilonK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : t + 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ∃ hdepth : dK ≤ ramificationIndex F K * d,
      stationaryCoefficientClass K chiK psiK hK
          (Units.map (algebraMap F K) gammaF)
          (highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
            chiF chiK psiF psiK hchi hpsi (by
              rw [hF.conductor_eq]
              omega) gammaF hgammaF) =
        denominatorScaledAlgebraMap F K d dK hdepth gammaF
          (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
  have hm : t + 1 < chiF.conductor := by rw [hF.conductor_eq]; omega
  have hmK := highParameter_ramified_conductor_eq F K ht hres pi hpi hgen
    chiF chiK hchi hm
  have hmrel := highParameter_ramified_conductor_relation
    F K ht hres pi hpi hgen chiF chiK hchi hm
  have hellThree : 3 ≤ Module.finrank F K := by
    have htwo := (PrimeCyclicExtension.degree_prime F K).two_le
    by_contra hnot
    have heq : Module.finrank F K = 2 := by omega
    rw [heq] at hodd
    norm_num at hodd
  have harith := stableOddDepthArithmetic hodd hellThree (by omega)
    hF hK hd hmrel
  have hram := ramifiedIndex_eq_degree F K ht hres pi hpi hgen
  have hdepth : dK ≤ ramificationIndex F K * d := by
    rw [hram]
    exact harith.coefficientDepth_le
  refine ⟨hdepth, ?_⟩
  have hdK : d ≤ dK := by
    obtain ⟨z, hz, hdz⟩ := harith.coefficientDepth_eq
    omega
  let hprecision := highParameter_stableOdd_precision F K ht hres pi hpi hgen
    chiF chiK hF hK hmK hd hdK
  have hK' : IsStationaryConductorDecomposition
      (herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1)
      dK epsilonK := by
    rw [← hmK]
    exact hK
  have hintermediate := highParameter_stableOdd_intermediateTerms
    F K ht hres pi hpi hgen chiF hF hK'
      (by simpa [hmK] using harith)
  have hterminal : NormPolynomialTerminalTermVanishAt F K
      (dK + epsilonK) chiF.conductor :=
    totallyRamified_normPolynomialTerminalTermVanishAt F K
      (Module.finrank F K) (dK + epsilonK) chiF.conductor rfl hram
      harith.variableDepth_ge_conductor
  have hvariable := ramified_traceLatticeInclusion_of_bound
    F K ht hres pi hpi hgen (dK + epsilonK) (d + epsilon)
    harith.trace_variable_bound
  have hconductor := ramified_traceLatticeInclusion_of_bound
    F K ht hres pi hpi hgen chiK.conductor chiF.conductor (by
      rw [hmrel])
  exact stationaryClass_eq_commonDenominatorImage_of_trace F K
    chiF chiK psiF psiK hprecision hchi hpsi gammaF hgammaF
    (highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
      chiF chiK psiF psiK hchi hpsi hm gammaF hgammaF)
    hvariable hconductor hintermediate hterminal hdepth

/-! ## The tame quadratic row -/

/-- PullbackConductors gives `mK = 2*mF-1` in the tame quadratic row,
written without truncated subtraction. -/
theorem highParameter_tameQuadratic_conductor_relation
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hdegree : Module.finrank F K = 2) (htzero : t = 0)
    (hm : 1 < chiF.conductor) :
    chiK.conductor + 1 = 2 * chiF.conductor := by
  have hhigh : t + 1 < chiF.conductor := by omega
  have hrel := highParameter_ramified_conductor_relation
    F K ht hres pi hpi hgen chiF chiK hchi hhigh
  simpa [hdegree, htzero] using hrel

/-- The actual tame-quadratic upstairs conductor has decomposition
`mK = 2*(mF-1)+1`; hence its coefficient quotient is
`O_K / p_K^(mF-1)`. -/
theorem highParameter_tameQuadratic_sourceDecomposition
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hdegree : Module.finrank F K = 2) (htzero : t = 0) :
    IsStationaryConductorDecomposition chiK.conductor
      (chiF.conductor - 1) 1 := by
  have hrel := highParameter_tameQuadratic_conductor_relation
    F K ht hres pi hpi hgen chiF chiK hchi hdegree htzero
      hF.conductor_gt_one
  have hconductor : chiK.conductor =
      2 * (chiF.conductor - 1) + 1 := by
    omega
  have hmF := hF.conductor_gt_one
  constructor
  · rw [hconductor]
    omega
  · omega
  · exact hconductor

/-- The minimal upstairs stationary variable depth in the tame quadratic
row is exactly `mF`, not merely a convenient deeper layer. -/
theorem highParameter_tameQuadratic_variableDepth
    (chiF : LocalQuasiCharData F)
    (hm : 1 < chiF.conductor) :
    chiF.conductor - 1 + 1 = chiF.conductor := by
  omega

/-- **Tame quadratic high stationary class.**

Assume degree and ramification index two, lower break zero, and odd residue
characteristic.  The actual upstairs conductor is `2*m-1`, its coefficient
depth is `m-1`, and the stationary source is exactly `p_K^m`.  The
quadratic norm term already has target depth `m`, so the common-denominator
adjoint identifies the upstairs stationary numerator class with the natural
quotient image of the downstairs class. -/
theorem highParameter_tameQuadratic
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hdegree : Module.finrank F K = 2) (htzero : t = 0)
    (_htame : residueCharacteristic F ≠ 2)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    ∃ hdepth : chiF.conductor - 1 ≤ ramificationIndex F K * d,
      stationaryCoefficientClass K chiK psiK
          (highParameter_tameQuadratic_sourceDecomposition
            F K ht hres pi hpi hgen chiF chiK hF hchi hdegree htzero)
          (Units.map (algebraMap F K) gammaF)
          (highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
            chiF chiK psiF psiK hchi hpsi (by
              rw [htzero]
              exact hF.conductor_gt_one) gammaF hgammaF) =
        denominatorScaledAlgebraMap F K d (chiF.conductor - 1)
          hdepth gammaF (Units.map (algebraMap F K) gammaF)
          (by simp [normPolynomialDenominatorRatio])
          (stationaryCoefficientClass F chiF psiF hF gammaF hgammaF) := by
  have hm : t + 1 < chiF.conductor := by
    rw [htzero]
    exact hF.conductor_gt_one
  have hmK := highParameter_ramified_conductor_eq F K ht hres pi hpi hgen
    chiF chiK hchi hm
  have hmrel := highParameter_ramified_conductor_relation
    F K ht hres pi hpi hgen chiF chiK hchi hm
  have hK := highParameter_tameQuadratic_sourceDecomposition
    F K ht hres pi hpi hgen chiF chiK hF hchi hdegree htzero
  have hram := ramifiedIndex_eq_degree F K ht hres pi hpi hgen
  have hramTwo : ramificationIndex F K = 2 := hram.trans hdegree
  have hd : t + 1 ≤ d := by
    rw [htzero]
    exact hF.floorDepth_pos
  have hdK : d ≤ chiF.conductor - 1 := by
    rw [hF.conductor_eq]
    omega
  have hdepth : chiF.conductor - 1 ≤ ramificationIndex F K * d := by
    have hepsilon := hF.epsilon_le_one
    rw [hramTwo, hF.conductor_eq]
    omega
  refine ⟨hdepth, ?_⟩
  let hprecision := highParameter_stableOdd_precision F K ht hres pi hpi hgen
    chiF chiK hF hK hmK hd hdK
  have hsource : chiF.conductor - 1 + 1 = chiF.conductor :=
    highParameter_tameQuadratic_variableDepth F K ht hres pi hpi hgen
      chiF hF.conductor_gt_one
  have hvariableBound : Module.finrank F K * (d + epsilon) ≤
      (chiF.conductor - 1 + 1) +
        (Module.finrank F K - 1) * (t + 1) := by
    have hepsilon := hF.epsilon_le_one
    rw [hdegree, htzero, hsource, hF.conductor_eq]
    omega
  have hvariable : TraceLatticeInclusion F K
      (chiF.conductor - 1 + 1) (d + epsilon) :=
    ramified_traceLatticeInclusion_of_bound F K ht hres pi hpi hgen
      (chiF.conductor - 1 + 1) (d + epsilon) hvariableBound
  have hconductor := ramified_traceLatticeInclusion_of_bound
    F K ht hres pi hpi hgen chiK.conductor chiF.conductor (by
      rw [hmrel])
  have hintermediate : NormPolynomialIntermediateTermsVanishAt F K
      (chiF.conductor - 1 + 1) chiF.conductor := by
    intro x hx j hjtwo hjlt
    rw [hdegree] at hjlt
    omega
  have hterminal : NormPolynomialTerminalTermVanishAt F K
      (chiF.conductor - 1 + 1) chiF.conductor := by
    simpa only [hsource] using
      (totallyRamified_normPolynomialTerminalTermVanishAt F K 2
        chiF.conductor chiF.conductor hdegree hramTwo le_rfl)
  exact stationaryClass_eq_commonDenominatorImage_of_trace F K
    chiF chiK psiF psiK hprecision hchi hpsi gammaF hgammaF
    (highParameter_ramified_commonDenominator F K ht hres pi hpi hgen
      chiF chiK psiF psiK hchi hpsi hm gammaF hgammaF)
    hvariable hconductor hintermediate hterminal hdepth

end RamifiedPrime

end

end LanglandsFirstMainLemma
