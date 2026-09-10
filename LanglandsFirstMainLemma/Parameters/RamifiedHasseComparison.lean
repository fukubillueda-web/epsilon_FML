import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.StationaryClassUnderNorm
import LanglandsFirstMainLemma.FiniteField.HasseFunctionLift
import LanglandsFirstMainLemma.FiniteField.AffinePencil
import LanglandsFirstMainLemma.FiniteField.ArtinSchreier
import LanglandsFirstMainLemma.FiniteField.QuadraticPhasePowers

/-!
# Ramified Hasse-phase comparison

This module compares the exact odd Lamprecht phases built by the public
`PhaseReduction` API from supplied stationary quotient representatives.  The
ordered admissible denominators, every representative change, the quadratic
scalar corrections, and the norm--trace specializations remain explicit.  The
finite-field trace lift, odd-prime affine boundary, and characteristic-two
cancellation are exposed separately so that none is used outside the
manuscript's case boundary.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators ComplexConjugate

universe u

/-- Pointwise identification with the trace lift, including the exact residual sign. -/
theorem ramifiedHasseTraceLiftPhase_of_pointwise
    (k L : Type*) [Field k] [Fintype k] [Field L] [Fintype L]
    [Algebra k L]
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    (phi : HasseFunction k psi)
    {psiL : FiniteAddChar L} (phiL : HasseFunction L psiL)
    (hpoint : ∀ x : L,
      phiL x = hasseFunctionLiftValue k L phi x) :
    phiL.sumPhase =
      (-1 : ℂ) ^ (Module.finrank k L - 1) *
        phi.sumPhase ^ Module.finrank k L := by
  have hsum : phiL.sum =
      ∑ x : L, hasseFunctionLiftValue k L phi x := by
    rw [HasseFunction.sum]
    apply Finset.sum_congr rfl
    intro x _hx
    exact hpoint x
  have hlift := hasseFunctionLift k L hpsi phi
  rw [← hsum] at hlift
  have hpos : 0 < Module.finrank k L := Module.finrank_pos
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hsumEq : phiL.sum =
      (-1 : ℂ) ^ (Module.finrank k L - 1) *
        phi.sum ^ Module.finrank k L := by
    rw [hr] at hlift ⊢
    simp only [Nat.succ_sub_one]
    have hnegpow : (-phi.sum) ^ (r + 1) =
        (-1 : ℂ) ^ (r + 1) * phi.sum ^ (r + 1) := by
      rw [show -phi.sum = (-1 : ℂ) * phi.sum by ring, mul_pow]
    rw [hnegpow] at hlift
    have hsign : -((-1 : ℂ) ^ (r + 1)) = (-1 : ℂ) ^ r := by
      rw [pow_succ]
      ring
    calc
      phiL.sum = -(-phiL.sum) := by ring
      _ = -((-1 : ℂ) ^ (r + 1) * phi.sum ^ (r + 1)) := by rw [hlift]
      _ = (-((-1 : ℂ) ^ (r + 1))) * phi.sum ^ (r + 1) := by ring
      _ = (-1 : ℂ) ^ r * phi.sum ^ (r + 1) := by rw [hsign]
  rw [HasseFunction.sumPhase, HasseFunction.sumPhase, hsumEq]
  have hsum0 : phi.sum ≠ 0 := HasseFunction.sum_ne_zero phi hpsi
  rw [phase_mul (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
      (pow_ne_zero _ hsum0), phase_pow, phase_pow]
  rw [phase_of_norm_eq_one (by simp : ‖(-1 : ℂ)‖ = 1)]

theorem ramifiedHasseTraceLiftPhase
    (k L : Type*) [Field k] [Fintype k] [Field L] [Fintype L]
    [Algebra k L]
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    (phi : HasseFunction k psi) :
    (hasseFunctionTraceLift k L phi).sumPhase =
      (-1 : ℂ) ^ (Module.finrank k L - 1) *
        phi.sumPhase ^ Module.finrank k L := by
  exact ramifiedHasseTraceLiftPhase_of_pointwise k L hpsi phi
    (hasseFunctionTraceLift k L phi) (fun _ ↦ rfl)

/-- For an odd finite-field extension the residual sign in the Hasse lift is
trivial, while the exponent remains the actual extension degree. -/
theorem ramifiedHasseTraceLiftPhase_of_oddDegree
    (k L : Type*) [Field k] [Fintype k] [Field L] [Fintype L]
    [Algebra k L]
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    (phi : HasseFunction k psi)
    (hodd : Odd (Module.finrank k L)) :
    (hasseFunctionTraceLift k L phi).sumPhase =
      phi.sumPhase ^ Module.finrank k L := by
  rw [ramifiedHasseTraceLiftPhase k L hpsi phi]
  obtain ⟨r, hr⟩ := hodd
  have hsub : Module.finrank k L - 1 = 2 * r := by omega
  rw [hsub, pow_mul]
  norm_num

theorem ramifiedHasseTameOddFinite
    {k : Type*} [Field k] [Fintype k]
    (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {ell : ℕ} (hell : Odd ell)
    (hell0 : (ell : k) ≠ 0)
    (hsign : finiteQuadraticChar k (ell : k) =
      finiteQuadraticChar k (-1) ^ ((ell - 1) / 2))
    (alpha : k) :
    quadraticPhase psi (ell : k) ((ell : k) * alpha) =
      quadraticPhase psi 1 alpha ^ ell := by
  obtain ⟨r, hr⟩ := hell
  have hell_eq : ell = 2 * r + 1 := by omega
  have hhalf : (ell - 1) / 2 = r := by omega
  have hqSquare : quadraticPhase psi 1 0 ^ 2 =
      finiteQuadraticChar k (-1) :=
    quadraticPhase_basic_sq hchar hpsi
  have hupper := quadraticPhase_eq_basic hchar hpsi hell0
    ((ell : k) * alpha)
  have hlower := quadraticPhase_eq_basic hchar hpsi one_ne_zero alpha
  have hupper' :
      quadraticPhase psi (ell : k) ((ell : k) * alpha) =
        finiteQuadraticChar k (ell : k) *
          psi (-((ell : k) * alpha ^ 2) / 2) *
            quadraticPhase psi 1 0 := by
    rw [hupper]
    congr 2
    field_simp [hell0]
  have hlower' :
      quadraticPhase psi 1 alpha =
        psi (-alpha ^ 2 / 2) * quadraticPhase psi 1 0 := by
    simpa using hlower
  have hpsiPow :
      psi (-alpha ^ 2 / 2) ^ ell =
        psi (-((ell : k) * alpha ^ 2) / 2) := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp only [nsmul_eq_mul]
    congr 1
    ring
  have hqPow :
      quadraticPhase psi 1 0 ^ ell =
        finiteQuadraticChar k (-1) ^ r * quadraticPhase psi 1 0 := by
    rw [hell_eq, pow_add, pow_mul, hqSquare, pow_one]
  rw [hupper', hlower', mul_pow, hpsiPow, hqPow, hsign, hhalf]
  ring

private theorem ramifiedHasse_finiteQuadraticChar_map_mul
    {k : Type*} [Field k] [Fintype k] (x y : k) :
    finiteQuadraticChar k (x * y) =
      finiteQuadraticChar k x * finiteQuadraticChar k y :=
  (finiteQuadraticChar k).map_mul' x y

private theorem ramifiedHasse_finiteQuadraticChar_map_pow
    {k : Type*} [Field k] [Fintype k] (x : k) (n : ℕ) :
    finiteQuadraticChar k (x ^ n) = finiteQuadraticChar k x ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact (finiteQuadraticChar k).map_one'
  | succ n ih =>
      rw [pow_succ, ramifiedHasse_finiteQuadraticChar_map_mul, ih, pow_succ]

theorem ramifiedHasseWildOddFinite
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    (hp2 : p ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1)
    {epsilon lambda : k} (hlambda : lambda ≠ 0)
    (hepsilon : epsilon = -lambda ^ (p - 1))
    (alpha : k) :
    quadraticPhase psi epsilon 0 = quadraticPhase psi 1 alpha ^ p := by
  have hchar : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  have hepsilon0 : epsilon ≠ 0 := by
    rw [hepsilon]
    exact neg_ne_zero.mpr (pow_ne_zero _ hlambda)
  have hupper := quadraticPhase_eq_basic hchar hpsi hepsilon0 0
  have hlower := quadraticPhase_eq_basic hchar hpsi one_ne_zero alpha
  have hupper' :
      quadraticPhase psi epsilon 0 =
        finiteQuadraticChar k epsilon * quadraticPhase psi 1 0 := by
    simpa using hupper
  have hlower' :
      quadraticPhase psi 1 alpha =
        psi (-alpha ^ 2 / 2) * quadraticPhase psi 1 0 := by
    simpa using hlower
  have hpsiPow : psi (-alpha ^ 2 / 2) ^ p = 1 := by
    calc
      psi (-alpha ^ 2 / 2) ^ p =
          psi (p • (-alpha ^ 2 / 2)) :=
        (AddChar.map_nsmul_eq_pow psi p (-alpha ^ 2 / 2)).symm
      _ = psi 0 := by simp [nsmul_eq_mul]
      _ = 1 := AddChar.map_zero_eq_one psi
  have hqPow : quadraticPhase psi 1 0 ^ p =
      quadraticPhase psi 1 0 * finiteQuadraticChar k (-1) := by
    simpa only [ringChar.eq k p] using
      (quadraticPhase_powers hchar hpsi).2.2
  obtain ⟨r, hr⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpEven : p - 1 = 2 * r := by omega
  have hnuLambda :
      finiteQuadraticChar k (lambda ^ (p - 1)) = 1 := by
    rw [ramifiedHasse_finiteQuadraticChar_map_pow, hpEven, pow_mul,
      finiteQuadraticChar_sq k hlambda, one_pow]
  have hnuEpsilon : finiteQuadraticChar k epsilon =
      finiteQuadraticChar k (-1) := by
    rw [hepsilon, show -lambda ^ (p - 1) =
      (-1 : k) * lambda ^ (p - 1) by ring,
      ramifiedHasse_finiteQuadraticChar_map_mul, hnuLambda, mul_one]
  rw [hupper', hlower', mul_pow, hpsiPow, one_mul, hqPow, hnuEpsilon]
  ring

/-- The precise odd-prime boundary in the real assembly coordinates: the
actual base conductor is `m = t + 1`, and the odd ramification conductor is
the same successor.  This is the manuscript condition `b = t` after
`m = b + 1`. -/
structure IsRamifiedHasseOddAffineBoundary (m t T : ℕ) : Prop where
  baseConductor_eq : m = t + 1
  ramificationConductor_eq : T = t + 1
  ramificationConductor_odd : Odd T

/-- The actual upper, nonidentity norm-character, and twist critical phases
appearing in the odd exact assembly.  This target-local view has precisely the
indexing used by `AffinePencil`; it stores phases, not newly chosen stationary
representatives. -/
structure RamifiedHasseOddCriticalData (p : ℕ) [Fact p.Prime] where
  upperPhase : ℂ
  normCharacterPhase : (ZMod p)ˣ → ℂ
  baseTwistPhase : ℂ
  nonidentityTwistPhase : (ZMod p)ˣ → ℂ
  upperPhase_ne_zero : upperPhase ≠ 0
  normCharacterPhase_ne_zero : ∀ j, normCharacterPhase j ≠ 0
  baseTwistPhase_ne_zero : baseTwistPhase ≠ 0
  nonidentityTwistPhase_ne_zero : ∀ j, nonidentityTwistPhase j ≠ 0

namespace RamifiedHasseOddCriticalData

noncomputable def residualQuotient {p : ℕ} [Fact p.Prime]
    (D : RamifiedHasseOddCriticalData p) : ℂ :=
  D.upperPhase * (∏ j, D.normCharacterPhase j) /
    (D.baseTwistPhase * ∏ j, D.nonidentityTwistPhase j)

theorem residualQuotient_ne_zero {p : ℕ} [Fact p.Prime]
    (D : RamifiedHasseOddCriticalData p) : D.residualQuotient ≠ 0 := by
  unfold residualQuotient
  exact div_ne_zero
    (mul_ne_zero D.upperPhase_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ D.normCharacterPhase_ne_zero j))
    (mul_ne_zero D.baseTwistPhase_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦
        D.nonidentityTwistPhase_ne_zero j))

/-- Extract exactly the actual critical rows of a real odd
`PhaseReduction` assembly. -/
noncomputable def ofExactAssembly
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {P : FirstMainPhaseData F K chiF psiF data}
    {I : Type*} [Fintype I]
    {t m p : ℕ} [Fact p.Prime]
    (A : ExactOddPhaseAssembly F K chiF psiF data P (t := t) (m := m) I)
    (e : (ZMod p)ˣ ≃ I) :
    RamifiedHasseOddCriticalData p where
  upperPhase := P.extension.criticalFactor
  normCharacterPhase := fun j ↦
    (P.normCharacter (A.normCharacterIndex (e j))).criticalFactor
  baseTwistPhase := (P.twist 1).criticalFactor
  nonidentityTwistPhase := fun j ↦
    (P.twist (A.normCharacterIndex (e j))).criticalFactor
  upperPhase_ne_zero := P.extension.criticalFactor_ne_zero
  normCharacterPhase_ne_zero := fun j ↦
    (P.normCharacter (A.normCharacterIndex (e j))).criticalFactor_ne_zero
  baseTwistPhase_ne_zero := (P.twist 1).criticalFactor_ne_zero
  nonidentityTwistPhase_ne_zero := fun j ↦
    (P.twist (A.normCharacterIndex (e j))).criticalFactor_ne_zero

/-- The target-local view is definitionally the indexed residual quotient
proved by the real exact assembly. -/
theorem ofExactAssembly_residualQuotient
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {P : FirstMainPhaseData F K chiF psiF data}
    {I : Type*} [Fintype I]
    {t m p : ℕ} [Fact p.Prime]
    (A : ExactOddPhaseAssembly F K chiF psiF data P (t := t) (m := m) I)
    (e : (ZMod p)ˣ ≃ I) :
    (ofExactAssembly A e).residualQuotient = A.residualPhase := by
  rw [A.residualPhase_eq_indexedQuotient]
  unfold residualQuotient ofExactAssembly
  change
    (P.extension.criticalFactor *
        ∏ j : (ZMod p)ˣ,
          (P.normCharacter (A.normCharacterIndex (e j))).criticalFactor) /
      ((P.twist 1).criticalFactor *
        ∏ j : (ZMod p)ˣ,
          (P.twist (A.normCharacterIndex (e j))).criticalFactor) =
    (P.extension.criticalFactor *
        ∏ i : I,
          (P.normCharacter (A.normCharacterIndex i)).criticalFactor) /
      ((P.twist 1).criticalFactor *
        ∏ i : I,
          (P.twist (A.normCharacterIndex i)).criticalFactor)
  rw [Equiv.prod_comp e
      (fun i : I ↦ (P.normCharacter (A.normCharacterIndex i)).criticalFactor),
    Equiv.prod_comp e
      (fun i : I ↦ (P.twist (A.normCharacterIndex i)).criticalFactor)]

end RamifiedHasseOddCriticalData

private theorem ramifiedHasseOddBoundary_affinePencil_of_data
    {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    {m t T : ℕ} (hboundary : IsRamifiedHasseOddAffineBoundary m t T)
    (hp2 : p ≠ 2) (psi : FiniteAddChar k) (hpsi : psi ≠ 1)
    (hfrob : ∀ z : k, psi (z ^ p) = psi z)
    {rho sigma tau a0 b0 : k} (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p,
      1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0)
    (ha0 : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹)
    (hb0 : b0 ^ p = sigma - rho⁻¹ * tau)
    (D : RamifiedHasseOddCriticalData p)
    (hupper : D.upperPhase = quadraticPhase psi a0 b0)
    (hnorm : ∀ u : (ZMod p)ˣ,
      D.normCharacterPhase u = quadraticPhase psi
        ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * rho)
        ((ZMod.castHom (dvd_refl p) k) (u : ZMod p) * tau))
    (hbaseTwist : D.baseTwistPhase = quadraticPhase psi 1 sigma)
    (htwist : ∀ j : (ZMod p)ˣ,
      D.nonidentityTwistPhase j = quadraticPhase psi
        (1 + (ZMod.castHom (dvd_refl p) k) j * rho)
        (sigma + (ZMod.castHom (dvd_refl p) k) j * tau)) :
    D.residualQuotient = 1 := by
  classical
  rcases hboundary with ⟨_hbt, _hT, _hodd⟩
  let f : ZMod p → ℂ := fun j ↦ quadraticPhase psi
    (1 + (ZMod.castHom (dvd_refl p) k) j * rho)
    (sigma + (ZMod.castHom (dvd_refl p) k) j * tau)
  have hcompl :
      (∏ j ∈ ({0} : Finset (ZMod p))ᶜ, f j) =
        ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
    rw [Finset.prod_subtype (p := fun x : ZMod p ↦ x ≠ 0)
      (({0} : Finset (ZMod p))ᶜ) (fun x ↦ by simp) f]
    exact (Equiv.prod_comp unitsEquivNeZero
      (fun j : {x : ZMod p // x ≠ 0} ↦ f (j : ZMod p))).symm
  have hsplit : (∏ j : ZMod p, f j) =
      quadraticPhase psi 1 sigma * ∏ j : (ZMod p)ˣ, f (j : ZMod p) := by
    rw [Fintype.prod_eq_mul_prod_compl (0 : ZMod p) f, hcompl]
    simp [f]
  unfold RamifiedHasseOddCriticalData.residualQuotient
  rw [hupper, hbaseTwist]
  simp_rw [hnorm, htwist]
  rw [affinePencil hp2 psi hpsi hfrob hrho hnonzero ha0 hb0, hsplit]
  exact div_self (mul_ne_zero (phase_ne_zero _)
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ phase_ne_zero _))

/-- Affine-pencil cancellation for the actual critical rows of a real odd
exact assembly, gated by that assembly's own boundary conductor. -/
theorem ramifiedHasseOddBoundary_affinePencil
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Finite (NormCharacter F K)]
    {chiF : ContinuousQuasiChar F} {psiF : ContinuousAddChar F}
    {data : FirstMainComputationalData F K chiF psiF}
    {P : FirstMainPhaseData F K chiF psiF data}
    {I : Type*} [Fintype I]
    {t m T p : ℕ} [Fact p.Prime]
    (A : ExactOddPhaseAssembly F K chiF psiF data P (t := t) (m := m) I)
    (e : (ZMod p)ˣ ≃ I)
    (hdegree : Module.finrank F K = p)
    (hboundary : IsRamifiedHasseOddAffineBoundary m t T)
    {k : Type*} [Field k] [Fintype k] [CharP k p]
    (hp2 : p ≠ 2) (psi : FiniteAddChar k) (hpsi : psi ≠ 1)
    (hfrob : ∀ z : k, psi (z ^ p) = psi z)
    {rho sigma tau a0 b0 : k} (hrho : rho ≠ 0)
    (hnonzero : ∀ j : ZMod p,
      1 + (ZMod.castHom (dvd_refl p) k) j * rho ≠ 0)
    (ha0 : a0 ^ p = 1 - (rho ^ (p - 1))⁻¹)
    (hb0 : b0 ^ p = sigma - rho⁻¹ * tau)
    (hupper : P.extension.criticalFactor = quadraticPhase psi a0 b0)
    (hnorm : ∀ j : (ZMod p)ˣ,
      (P.normCharacter (A.normCharacterIndex (e j))).criticalFactor =
        quadraticPhase psi
          ((ZMod.castHom (dvd_refl p) k) (j : ZMod p) * rho)
          ((ZMod.castHom (dvd_refl p) k) (j : ZMod p) * tau))
    (hbaseTwist : (P.twist 1).criticalFactor = quadraticPhase psi 1 sigma)
    (htwist : ∀ j : (ZMod p)ˣ,
      (P.twist (A.normCharacterIndex (e j))).criticalFactor =
        quadraticPhase psi
          (1 + (ZMod.castHom (dvd_refl p) k) (j : ZMod p) * rho)
          (sigma + (ZMod.castHom (dvd_refl p) k) (j : ZMod p) * tau)) :
    A.residualPhase = 1 := by
  have _hdegree := hdegree
  let C := RamifiedHasseOddCriticalData.ofExactAssembly A e
  have hC : C.residualQuotient = 1 :=
    ramifiedHasseOddBoundary_affinePencil_of_data hboundary hp2 psi hpsi
      hfrob hrho hnonzero ha0 hb0 C hupper hnorm hbaseTwist htwist
  rw [← RamifiedHasseOddCriticalData.ofExactAssembly_residualQuotient A e]
  exact hC

/-- The characteristic-two Artin--Schreier phase in the proved, positive
orientation. -/
theorem ramifiedHasseArtinSchreier_oriented
    {k : Type*} [Field k] [Fintype k] [CharP k 2]
    (c : k) : absoluteTraceChar k (c + c ^ 2) = 1 :=
  artinSchreier_phase k c

/-- Cancel only a positively oriented Artin--Schreier factor. -/
theorem ramifiedHasseArtinSchreier_cancel
    {k : Type*} [Field k] [Fintype k] [CharP k 2]
    {a b : ℂ} {c : k}
    (h : a = b * absoluteTraceChar k (c + c ^ 2)) : a = b := by
  rw [h, ramifiedHasseArtinSchreier_oriented, mul_one]

/-- The manuscript's characteristic-two binomial correction converts the
iterated refinement law into an exact pointwise power. -/
theorem ramifiedHasseCharTwo_binomialCorrection
    {k : Type*} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) (lambda : k) (ell : ℕ) (x : k) :
    q.affine lambda ((ell : k) * x) *
        absoluteTraceChar k (-((ell.choose 2 : k) * x ^ 2)) =
      q.affine lambda x ^ ell := by
  have hiterate := (q.affine lambda).map_nsmul ell x
  rw [nsmul_eq_mul] at hiterate
  rw [hiterate, mul_assoc, ← AddChar.map_add_eq_mul]
  simp

section RamifiedHasseCharTwo

variable {k : Type*} [Field k] [Fintype k] [CharP k 2]

theorem ramifiedHasseCharTwoFinite
    (q : CharTwoRefinement k) (lambda : k)
    (binaryDegree : ℕ)
    (htraceOne : absoluteTraceChar k 1 = (-1 : ℂ) ^ binaryDegree)
    {ell : ℕ} (hell : Odd ell)
    (hparity : ell % 8 = 3 ∨ ell % 8 = 5 →
      Even binaryDegree)
    {upper : ℂ}
    (hupperOne : ell % 4 = 1 → upper = q.affinePhase lambda)
    (hupperThree : ell % 4 = 3 →
      upper = conj (q.affinePhase lambda)) :
    upper = q.affinePhase lambda ^ ell := by
  let H := q.affinePhase lambda
  have hH4 : H ^ 4 = absoluteTraceChar k 1 := by
    calc
      H ^ 4 = (H ^ 2) ^ 2 := by ring
      _ = (q 1 * absoluteTraceChar k lambda) ^ 2 := by
        rw [q.affinePhase_sq]
      _ = absoluteTraceChar k 1 := by
        rw [mul_pow, q.value_sq, CharTwoRefinement.absoluteTraceChar_value_sq,
          mul_one]
  have hH8 : H ^ 8 = 1 := by
    calc
      H ^ 8 = (H ^ 4) ^ 2 := by ring
      _ = absoluteTraceChar k 1 ^ 2 := by rw [hH4]
      _ = 1 := CharTwoRefinement.absoluteTraceChar_value_sq 1
  have hconjH : conj H = H ^ 7 := by
    apply mul_right_cancel₀ (phase_ne_zero _)
    calc
      conj H * H = 1 := by
        change conj (phase _) * phase _ = 1
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
          phase_norm]
        norm_num
      _ = H ^ 8 := hH8.symm
      _ = H ^ 7 * H := by rw [pow_succ]
  have hcases : ell % 8 = 1 ∨ ell % 8 = 3 ∨
      ell % 8 = 5 ∨ ell % 8 = 7 := by
    obtain ⟨r, hr⟩ := hell
    omega
  have hpowMod : H ^ ell = H ^ (ell % 8) :=
    pow_eq_pow_mod ell hH8
  rcases hcases with h1 | h3 | h5 | h7
  · have hmod4 : ell % 4 = 1 := by omega
    rw [hupperOne hmod4, hpowMod, h1, pow_one]
  · have hmod4 : ell % 4 = 3 := by omega
    have hf := hparity (Or.inl h3)
    have hH4one : H ^ 4 = 1 := by
      rw [hH4, htraceOne]
      obtain ⟨r, hr⟩ := hf
      rw [hr, show r + r = 2 * r by omega, pow_mul]
      norm_num
    rw [hupperThree hmod4, hconjH, hpowMod, h3]
    calc
      H ^ 7 = H ^ (3 + 4) := by norm_num
      _ = H ^ 3 * H ^ 4 := pow_add H 3 4
      _ = H ^ 3 := by rw [hH4one, mul_one]
  · have hmod4 : ell % 4 = 1 := by omega
    have hf := hparity (Or.inr h5)
    have hH4one : H ^ 4 = 1 := by
      rw [hH4, htraceOne]
      obtain ⟨r, hr⟩ := hf
      rw [hr, show r + r = 2 * r by omega, pow_mul]
      norm_num
    rw [hupperOne hmod4, hpowMod, h5]
    calc
      H = H ^ 1 := (pow_one H).symm
      _ = H ^ 1 * H ^ 4 := by rw [hH4one, mul_one]
      _ = H ^ (1 + 4) := (pow_add H 1 4).symm
      _ = H ^ 5 := by norm_num
  · have hmod4 : ell % 4 = 3 := by omega
    rw [hupperThree hmod4, hconjH, hpowMod, h7]

end RamifiedHasseCharTwo

private theorem ramifiedHasseCharTwo_affine_value_pow_four
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) (lambda x : k) :
    q.affine lambda x ^ 4 = 1 := by
  have h := (q.affine lambda).map_nsmul 4 x
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hfour : (4 : k) = 0 := by
    calc
      (4 : k) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  have hsix : (6 : k) = 0 := by
    calc
      (6 : k) = 2 + 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  simpa [nsmul_eq_mul, hfour, hsix, Nat.choose] using h.symm

private theorem ramifiedHasseCharTwo_affine_value_pow_of_mod_four_one
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) (lambda x : k) {ell : ℕ}
    (hmod : ell % 4 = 1) :
    q.affine lambda x ^ ell = q.affine lambda x := by
  have hpow : q.affine lambda x ^ ell =
      q.affine lambda x ^ (ell % 4) :=
    pow_eq_pow_mod ell
      (ramifiedHasseCharTwo_affine_value_pow_four q lambda x)
  rw [hpow, hmod, pow_one]

private theorem ramifiedHasseCharTwo_affine_value_pow_of_mod_four_three
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    (q : CharTwoRefinement k) (lambda x : k) {ell : ℕ}
    (hmod : ell % 4 = 3) :
    q.affine lambda x ^ ell = conj (q.affine lambda x) := by
  let z : ℂ := q.affine lambda x
  have hz0 : z ≠ 0 := (q.affine lambda).ne_zero x
  have hznorm : ‖z‖ = 1 := (q.affine lambda).norm_apply x
  have hz4 : z ^ 4 = 1 :=
    ramifiedHasseCharTwo_affine_value_pow_four q lambda x
  have hpow : z ^ ell = z ^ (ell % 4) := pow_eq_pow_mod ell hz4
  have hinv : z ^ 3 = z⁻¹ := by
    apply mul_right_cancel₀ hz0
    rw [inv_mul_cancel₀ hz0]
    simpa only [pow_succ] using hz4
  have hconj : z⁻¹ = conj z := by
    apply mul_right_cancel₀ hz0
    rw [inv_mul_cancel₀ hz0]
    symm
    change conj z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [hznorm]
    norm_num
  change z ^ ell = conj z
  rw [hpow, hmod, hinv, hconj]

/-- The phase of the sum of an explicitly supplied finite function. -/
noncomputable def ramifiedHasseFunctionPhase
    {k : Type u} [Fintype k] (f : k → ℂ) : ℂ :=
  phase (∑ x, f x)

/-- Pointwise equal finite functions have the same sum phase. -/
theorem ramifiedHasseFunctionPhase_congr
    {k : Type u} [Fintype k] {f g : k → ℂ}
    (h : ∀ x, f x = g x) :
    ramifiedHasseFunctionPhase f = ramifiedHasseFunctionPhase g := by
  unfold ramifiedHasseFunctionPhase
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  exact h x

/-- Transport along an explicit finite equivalence preserves the sum phase. -/
theorem ramifiedHasseFunctionPhase_equiv
    {k L : Type*} [Fintype k] [Fintype L]
    (e : k ≃ L) (f : L → ℂ) :
    ramifiedHasseFunctionPhase (fun x ↦ f (e x)) =
      ramifiedHasseFunctionPhase f := by
  unfold ramifiedHasseFunctionPhase
  rw [e.sum_comp]

/-- Multiplication by a supplied nonzero scalar merely reindexes the sum. -/
theorem ramifiedHasseFunctionPhase_mul_inv
    {k : Type u} [Field k] [Fintype k]
    (f : k → ℂ) {c : k} (hc : c ≠ 0) :
    ramifiedHasseFunctionPhase f =
      ramifiedHasseFunctionPhase (fun x ↦ f (c⁻¹ * x)) := by
  unfold ramifiedHasseFunctionPhase
  congr 1
  symm
  apply Fintype.sum_bijective (fun x : k ↦ c⁻¹ * x)
    (mulLeft_bijective₀ c⁻¹ (inv_ne_zero hc))
  intro x
  rfl

structure RamifiedHasseOddStationaryPhase
    (E : Type u)
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E) where
  d : ℕ
  decomposition : IsStationaryConductorDecomposition chi.conductor d 1
  denominator : AdmissibleGamma E chi psi
  representative : StationaryClassRepresentative E chi psi decomposition
    (denominator : Eˣ) denominator.property
  delta : Eˣ
  delta_order : ord E (delta : E) = ((d : ℤ) : WithTop ℤ)

namespace RamifiedHasseOddStationaryPhase

variable {E : Type u}
  [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

theorem conductor_eq (V : RamifiedHasseOddStationaryPhase E chi psi) :
    chi.conductor = 2 * V.d + 1 :=
  V.decomposition.conductor_eq

theorem conductor_large (V : RamifiedHasseOddStationaryPhase E chi psi) :
    1 < chi.conductor :=
  V.decomposition.conductor_gt_one

/-- The genuine `PhaseReduction` local phase built from the supplied
stationary quotient representative and its exact denominator. -/
def localPhase (V : RamifiedHasseOddStationaryPhase E chi psi) :
    LocalLamprechtPhaseData E chi psi :=
  LocalLamprechtPhaseData.oddOfStationaryClass V.d V.decomposition
    V.denominator V.delta V.delta_order V.representative

noncomputable def function
    (V : RamifiedHasseOddStationaryPhase E chi psi) :
    HasseFunction (ResidueField E)
      (lamprechtResidualAddChar E chi psi V.d V.conductor_eq
        V.conductor_large V.denominator V.delta V.delta_order) :=
  lamprechtHasseFunction E chi psi V.d V.conductor_eq V.conductor_large
    V.denominator V.delta V.delta_order V.representative.toLamprecht (by
      simpa only [stationaryDepthOfConductorDecomposition] using
        V.representative.toLamprecht_represents)

noncomputable def phase
    (V : RamifiedHasseOddStationaryPhase E chi psi) : ℂ :=
  letI := residueFieldFintype E
  V.function.sumPhase

/-- The stored phase is definitionally the sum phase of the Hasse function
built from the same denominator and stationary quotient representative. -/
theorem phase_eq_functionPhase
    (V : RamifiedHasseOddStationaryPhase E chi psi) :
    letI := residueFieldFintype E
    V.phase = ramifiedHasseFunctionPhase (fun x ↦ V.function x) :=
  rfl

/-- The phase compared below is exactly the critical factor of the real
`LocalLamprechtPhaseData`, not an auxiliary copy of it. -/
theorem phase_eq_localCriticalFactor
    (V : RamifiedHasseOddStationaryPhase E chi psi) :
    letI := residueFieldFintype E
    V.phase = V.localPhase.criticalFactor := by
  rfl

end RamifiedHasseOddStationaryPhase

/-- Exact pointwise tame normal forms on the common residue field. -/
structure RamifiedHasseTameOddFiniteData
    (k : Type u) [Field k] [Fintype k]
    (ell : ℕ) (epsilon : k) (lower upper : k → ℂ) where
  residueCharacteristic_odd : ringChar k ≠ 2
  psi : FiniteAddChar k
  psi_ne_one : psi ≠ 1
  degree_odd : Odd ell
  degree_scalar_ne_zero : (ell : k) ≠ 0
  c : k
  c_ne_zero : c ≠ 0
  epsilon_eq : epsilon = (ell : k) * c ^ 2
  alpha : k
  quadraticReciprocitySign :
    finiteQuadraticChar k (ell : k) =
      finiteQuadraticChar k (-1) ^ ((ell - 1) / 2)
  lower_pointwise : ∀ x,
    lower x = psi ((1 : k) / 2 * x ^ 2 + alpha * x)
  upper_pointwise : ∀ x,
    upper (c⁻¹ * x) =
      psi ((ell : k) / 2 * x ^ 2 + ((ell : k) * alpha) * x)

namespace RamifiedHasseTameOddFiniteData

theorem comparison
    {k : Type u} [Field k] [Fintype k]
    {ell : ℕ} {epsilon : k} {lower upper : k → ℂ}
    (D : RamifiedHasseTameOddFiniteData k ell epsilon lower upper) :
    ramifiedHasseFunctionPhase upper =
      ramifiedHasseFunctionPhase lower ^ ell := by
  have hlower : ramifiedHasseFunctionPhase lower =
      quadraticPhase D.psi 1 D.alpha := by
    calc
      ramifiedHasseFunctionPhase lower =
          ramifiedHasseFunctionPhase (fun x ↦
            D.psi ((1 : k) / 2 * x ^ 2 + D.alpha * x)) :=
        ramifiedHasseFunctionPhase_congr D.lower_pointwise
      _ = quadraticPhase D.psi 1 D.alpha := rfl
  have hupperReindex : ramifiedHasseFunctionPhase upper =
      ramifiedHasseFunctionPhase (fun x ↦ upper (D.c⁻¹ * x)) := by
    exact ramifiedHasseFunctionPhase_mul_inv upper D.c_ne_zero
  have hupper : ramifiedHasseFunctionPhase upper =
      quadraticPhase D.psi (ell : k) ((ell : k) * D.alpha) := by
    calc
      ramifiedHasseFunctionPhase upper =
          ramifiedHasseFunctionPhase (fun x ↦ upper (D.c⁻¹ * x)) :=
        hupperReindex
      _ = ramifiedHasseFunctionPhase (fun x ↦
          D.psi ((ell : k) / 2 * x ^ 2 +
            ((ell : k) * D.alpha) * x)) :=
        ramifiedHasseFunctionPhase_congr D.upper_pointwise
      _ = quadraticPhase D.psi (ell : k) ((ell : k) * D.alpha) := rfl
  calc
    ramifiedHasseFunctionPhase upper =
        quadraticPhase D.psi (ell : k) ((ell : k) * D.alpha) := hupper
    _ = quadraticPhase D.psi 1 D.alpha ^ ell :=
      ramifiedHasseTameOddFinite D.residueCharacteristic_odd D.psi_ne_one
        D.degree_odd D.degree_scalar_ne_zero D.quadraticReciprocitySign D.alpha
    _ = ramifiedHasseFunctionPhase lower ^ ell :=
      congrArg (fun z : ℂ ↦ z ^ ell) hlower.symm

end RamifiedHasseTameOddFiniteData

structure RamifiedHasseWildOddFiniteData
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    (epsilon : k) (lower upper : k → ℂ) where
  odd_prime : p ≠ 2
  psi : FiniteAddChar k
  psi_ne_one : psi ≠ 1
  alpha : k
  lambda : k
  lambda_ne_zero : lambda ≠ 0
  epsilon_eq : epsilon = -lambda ^ (p - 1)
  lower_pointwise : ∀ x,
    lower x = psi ((1 : k) / 2 * x ^ 2 + alpha * x)
  upper_pointwise : ∀ x,
    upper x = psi (epsilon / 2 * x ^ 2 + 0 * x)

namespace RamifiedHasseWildOddFiniteData

theorem comparison
    {p : ℕ} [Fact p.Prime]
    {k : Type u} [Field k] [Fintype k] [CharP k p]
    {epsilon : k} {lower upper : k → ℂ}
    (D : RamifiedHasseWildOddFiniteData p k epsilon lower upper) :
    ramifiedHasseFunctionPhase upper =
      ramifiedHasseFunctionPhase lower ^ p := by
  have hlower : ramifiedHasseFunctionPhase lower =
      quadraticPhase D.psi 1 D.alpha := by
    calc
      ramifiedHasseFunctionPhase lower =
          ramifiedHasseFunctionPhase (fun x ↦
            D.psi ((1 : k) / 2 * x ^ 2 + D.alpha * x)) :=
        ramifiedHasseFunctionPhase_congr D.lower_pointwise
      _ = quadraticPhase D.psi 1 D.alpha := rfl
  have hupper : ramifiedHasseFunctionPhase upper =
      quadraticPhase D.psi epsilon 0 := by
    calc
      ramifiedHasseFunctionPhase upper =
          ramifiedHasseFunctionPhase (fun x ↦
            D.psi (epsilon / 2 * x ^ 2 + 0 * x)) :=
        ramifiedHasseFunctionPhase_congr D.upper_pointwise
      _ = quadraticPhase D.psi epsilon 0 := rfl
  calc
    ramifiedHasseFunctionPhase upper =
        quadraticPhase D.psi epsilon 0 := hupper
    _ = quadraticPhase D.psi 1 D.alpha ^ p :=
      ramifiedHasseWildOddFinite D.odd_prime D.psi_ne_one D.lambda_ne_zero
        D.epsilon_eq D.alpha
    _ = ramifiedHasseFunctionPhase lower ^ p :=
      congrArg (fun z : ℂ ↦ z ^ p) hlower.symm

end RamifiedHasseWildOddFiniteData

structure RamifiedHasseCharTwoFiniteData
    (k : Type u) [Field k] [Fintype k] [CharP k 2]
    (ell : ℕ) (epsilon : k) (lower upper : k → ℂ) where
  degree_odd : Odd ell
  q : CharTwoRefinement k
  c : k
  c_ne_zero : c ≠ 0
  epsilon_eq : epsilon = (ell : k) * c ^ 2
  coordinateScale : k
  coordinateScale_ne_zero : coordinateScale ≠ 0
  lambda : k
  lower_pointwise : ∀ x,
    lower (coordinateScale⁻¹ * x) = q.affine lambda x
  binaryDegree : ℕ
  card_eq_two_pow : Fintype.card k = 2 ^ binaryDegree
  traceOne : absoluteTraceChar k 1 = (-1 : ℂ) ^ binaryDegree
  difficultParity : ell % 8 = 3 ∨ ell % 8 = 5 →
    Even binaryDegree
  upper_binomial_pointwise : ∀ x,
    upper ((c * coordinateScale)⁻¹ * x) =
      q.affine lambda ((ell : k) * x) *
        absoluteTraceChar k (-((ell.choose 2 : k) * x ^ 2))

namespace RamifiedHasseCharTwoFiniteData

/-- The retained scalar correction has the exact positive pointwise-power
orientation before the modulo-four phase split. -/
theorem binomialPointwise
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    {ell : ℕ} {epsilon : k} {lower upper : k → ℂ}
    (D : RamifiedHasseCharTwoFiniteData k ell epsilon lower upper)
    (x : k) :
    upper ((D.c * D.coordinateScale)⁻¹ * x) =
      D.q.affine D.lambda x ^ ell := by
  rw [D.upper_binomial_pointwise]
  exact ramifiedHasseCharTwo_binomialCorrection D.q D.lambda ell x

/-- The modulo-four `1` row follows from the retained binomial correction;
it is not an additional normal-form hypothesis. -/
theorem upperPointwise_of_mod_four_one
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    {ell : ℕ} {epsilon : k} {lower upper : k → ℂ}
    (D : RamifiedHasseCharTwoFiniteData k ell epsilon lower upper)
    (hmod : ell % 4 = 1) (x : k) :
    upper ((D.c * D.coordinateScale)⁻¹ * x) =
      D.q.affine D.lambda x := by
  rw [D.binomialPointwise]
  exact ramifiedHasseCharTwo_affine_value_pow_of_mod_four_one
    D.q D.lambda x hmod

/-- The modulo-four `3` row, with the exact conjugation orientation, follows
from the same retained binomial correction. -/
theorem upperPointwise_of_mod_four_three
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    {ell : ℕ} {epsilon : k} {lower upper : k → ℂ}
    (D : RamifiedHasseCharTwoFiniteData k ell epsilon lower upper)
    (hmod : ell % 4 = 3) (x : k) :
    upper ((D.c * D.coordinateScale)⁻¹ * x) =
      conj (D.q.affine D.lambda x) := by
  rw [D.binomialPointwise]
  exact ramifiedHasseCharTwo_affine_value_pow_of_mod_four_three
    D.q D.lambda x hmod

theorem comparison
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    {ell : ℕ} {epsilon : k} {lower upper : k → ℂ}
    (D : RamifiedHasseCharTwoFiniteData k ell epsilon lower upper) :
    ramifiedHasseFunctionPhase upper =
      ramifiedHasseFunctionPhase lower ^ ell := by
  have hlower : ramifiedHasseFunctionPhase lower =
      D.q.affinePhase D.lambda := by
    calc
      ramifiedHasseFunctionPhase lower =
          ramifiedHasseFunctionPhase
            (fun x ↦ lower (D.coordinateScale⁻¹ * x)) :=
        ramifiedHasseFunctionPhase_mul_inv lower D.coordinateScale_ne_zero
      _ =
          ramifiedHasseFunctionPhase (fun x ↦ D.q.affine D.lambda x) :=
        ramifiedHasseFunctionPhase_congr D.lower_pointwise
      _ = D.q.affinePhase D.lambda := rfl
  have hupperReindex : ramifiedHasseFunctionPhase upper =
      ramifiedHasseFunctionPhase
        (fun x ↦ upper ((D.c * D.coordinateScale)⁻¹ * x)) := by
    exact ramifiedHasseFunctionPhase_mul_inv upper
      (mul_ne_zero D.c_ne_zero D.coordinateScale_ne_zero)
  have hupperOne : ell % 4 = 1 →
      ramifiedHasseFunctionPhase upper = D.q.affinePhase D.lambda := by
    intro hmod
    calc
      ramifiedHasseFunctionPhase upper =
          ramifiedHasseFunctionPhase
            (fun x ↦ upper ((D.c * D.coordinateScale)⁻¹ * x)) :=
        hupperReindex
      _ = ramifiedHasseFunctionPhase (fun x ↦ D.q.affine D.lambda x) :=
        ramifiedHasseFunctionPhase_congr
          (D.upperPointwise_of_mod_four_one hmod)
      _ = D.q.affinePhase D.lambda := rfl
  have hupperThree : ell % 4 = 3 →
      ramifiedHasseFunctionPhase upper = conj (D.q.affinePhase D.lambda) := by
    intro hmod
    calc
      ramifiedHasseFunctionPhase upper =
          ramifiedHasseFunctionPhase
            (fun x ↦ upper ((D.c * D.coordinateScale)⁻¹ * x)) :=
        hupperReindex
      _ = ramifiedHasseFunctionPhase
          (fun x ↦ conj (D.q.affine D.lambda x)) :=
        ramifiedHasseFunctionPhase_congr
          (D.upperPointwise_of_mod_four_three hmod)
      _ = conj (D.q.affinePhase D.lambda) := by
        unfold ramifiedHasseFunctionPhase CharTwoRefinement.affinePhase
          HasseFunction.sumPhase HasseFunction.sum
        rw [← map_sum, phase_conj]
  calc
    ramifiedHasseFunctionPhase upper = D.q.affinePhase D.lambda ^ ell :=
      ramifiedHasseCharTwoFinite D.q D.lambda D.binaryDegree D.traceOne
        D.degree_odd D.difficultParity hupperOne hupperThree
    _ = ramifiedHasseFunctionPhase lower ^ ell :=
      congrArg (fun z : ℂ ↦ z ^ ell) hlower.symm

end RamifiedHasseCharTwoFiniteData

/-- The three finite calculations for the common residue field.  The
constructors store exact normal forms, not the comparison conclusion. -/
inductive RamifiedHasseFiniteCase
    (k : Type u) [Field k] [Fintype k]
    (ell t : ℕ) (epsilon tameCoordinate wildLambda : k)
    (lower upper : k → ℂ) : Prop
  | tameOdd (break_zero : t = 0)
      (D : RamifiedHasseTameOddFiniteData k ell epsilon lower upper)
      (coordinate_eq : D.c = tameCoordinate)
  | wildOdd [CharP k ell] [Fact ell.Prime] (break_positive : 0 < t)
      (D : RamifiedHasseWildOddFiniteData ell k epsilon lower upper)
      (ramificationCoordinate_eq : D.lambda = wildLambda)
  | charTwo [CharP k 2] (break_zero : t = 0)
      (D : RamifiedHasseCharTwoFiniteData k ell epsilon lower upper)
      (coordinate_eq : D.c = tameCoordinate)

theorem RamifiedHasseFiniteCase.comparison
    {k : Type u} [Field k] [Fintype k]
    {ell t : ℕ} {epsilon tameCoordinate wildLambda : k}
    {lower upper : k → ℂ}
    (C : RamifiedHasseFiniteCase k ell t epsilon tameCoordinate
      wildLambda lower upper) :
    ramifiedHasseFunctionPhase upper =
      ramifiedHasseFunctionPhase lower ^ ell := by
  cases C with
  | tameOdd _ D _ => exact D.comparison
  | wildOdd _ D _ => exact D.comparison
  | charTwo _ D _ => exact D.comparison

def ramifiedHasseCriticalInput
    (F K : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K]
    (piK : Kˣ) (dK : ℕ)
    (residueLift : ResidueField F → ringOfIntegers F)
    (x : ResidueField F) : K :=
  (piK : K) ^ dK * algebraMap F K ((residueLift x : ringOfIntegers F) : F)

/-- Local-to-finite comparison data for the actual odd local phases produced
by `PhaseReduction`.  It retains their ordered denominators and supplied
representatives, the named norm--trace calculations, the canonical residue
transport, and the pointwise finite normal forms proved in the three residue
characteristic cases. -/
structure RamifiedHasseComparisonData
    (F K : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (lower : RamifiedHasseOddStationaryPhase F chiF psiF)
    (upper : RamifiedHasseOddStationaryPhase K chiK psiK)
    (ell t : ℕ) [Fact ell.Prime] where
  odd_prime : ell ≠ 2
  degree_eq : Module.finrank F K = ell
  lowerBreak : PrimeCyclicExtension.IsLowerBreak F K t
  residueDegree_eq_one : residueDegree F K = 1
  multiplicativePullback : chiK.character = chiF.character.compNorm
  additivePullback : psiK.character = psiF.character.compTrace
  conductor_ge_break : t + 1 ≤ chiF.conductor
  stableRange : t = 0 ∨ t + 1 ≤ lower.d
  stationaryDepthRelation :
    2 * upper.d + (ell - 1) * t = 2 * ell * lower.d
  conductorDenominatorRelation :
    (chiK.conductor : ℤ) + psiK.conductor =
      (ell : ℤ) * ((chiF.conductor : ℤ) + psiF.conductor)
  denominator_eq :
    (upper.denominator : Kˣ) =
      Units.map (algebraMap F K) (lower.denominator : Fˣ)
  representative_eq :
    (upper.representative.representative : K) =
      algebraMap F K (lower.representative.representative : F)
  piF : Fˣ
  piK : Kˣ
  piF_uniformizer :
    (ValuativeRel.valuation F).IsUniformizer (piF : F)
  piK_uniformizer :
    (ValuativeRel.valuation K).IsUniformizer (piK : K)
  norm_uniformizer : normUnits F K piK = piF
  lower_delta_eq : lower.delta = piF ^ lower.d
  upper_delta_eq : upper.delta = piK ^ upper.d
  residueEquiv : ResidueField F ≃+* ResidueField K
  residueEquiv_eq_extension : ∀ x,
    residueEquiv x = extensionResidueMap F K x
  residueLift : ResidueField F → ringOfIntegers F
  residueLift_spec : ∀ x, residueMap F (residueLift x) = x
  normTruncation : ∀ x,
    norm F K (1 + ramifiedHasseCriticalInput F K piK upper.d residueLift x) -
        (1 + trace F K (ramifiedHasseCriticalInput F K piK upper.d residueLift x) +
          elementarySymmetric F K 2
            (ramifiedHasseCriticalInput F K piK upper.d residueLift x)) ∈
      lattice F ((2 * lower.d + 1 : ℕ) : ℤ)
  traceDepth : ∀ x,
    trace F K (ramifiedHasseCriticalInput F K piK upper.d residueLift x) ∈
      lattice F (lower.d : ℤ)
  secondSymmetricDepth : ∀ x,
    elementarySymmetric F K 2
        (ramifiedHasseCriticalInput F K piK upper.d residueLift x) ∈
      lattice F ((2 * lower.d : ℕ) : ℤ)
  epsilon : F
  epsilon_order : ord F epsilon = (0 : WithTop ℤ)
  epsilon_mem_lattice_zero : epsilon ∈ lattice F 0
  epsilonResidue : ResidueField F
  epsilonResidue_eq :
    epsilonResidue = reduce F epsilon epsilon_mem_lattice_zero
  tameCoordinate : ResidueField F
  tameCoordinate_origin : t = 0 →
    ∃ cLift : lattice K 0,
      (cLift : K) =
          (piK : K) ^ upper.d /
            algebraMap F K ((piF : F) ^ lower.d) ∧
        residueEquiv tameCoordinate = reduce K (cLift : K) cLift.property
  wildLambda : ResidueField F
  wildLambda_origin : 0 < t →
    ∃ lambdaLift : lattice K 0,
      (lambdaLift : K) =
          (PrimeCyclicExtension.generator F K (piK : K) - (piK : K)) /
            (piK : K) ^ (t + 1) ∧
        residueEquiv wildLambda =
          reduce K (lambdaLift : K) lambdaLift.property
  epsilonTraceSpecialization :
    trace F K ((piK : K) ^ (2 * upper.d)) =
      epsilon * (piF : F) ^ (2 * lower.d)
  finiteComparison :
    letI := residueFieldFintype F
    RamifiedHasseFiniteCase (ResidueField F) ell t epsilonResidue
      tameCoordinate wildLambda
      (fun x ↦ lower.function x)
      (fun x ↦ upper.function (residueEquiv x))

namespace RamifiedHasseComparisonData

theorem traceProductSpecialization
    {F K : Type u}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    {lower : RamifiedHasseOddStationaryPhase F chiF psiF}
    {upper : RamifiedHasseOddStationaryPhase K chiK psiK}
    {ell t : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      lower upper ell t)
    (x y : ResidueField F) :
    trace F K
        (ramifiedHasseCriticalInput F K D.piK upper.d D.residueLift x *
          ramifiedHasseCriticalInput F K D.piK upper.d D.residueLift y) =
      D.epsilon * (D.piF : F) ^ (2 * lower.d) *
        (D.residueLift x : F) * (D.residueLift y : F) := by
  let ax : F := (D.residueLift x : F)
  let ay : F := (D.residueLift y : F)
  have hprod :
      ramifiedHasseCriticalInput F K D.piK upper.d D.residueLift x *
          ramifiedHasseCriticalInput F K D.piK upper.d D.residueLift y =
        algebraMap F K (ax * ay) * (D.piK : K) ^ (2 * upper.d) := by
    unfold ramifiedHasseCriticalInput
    rw [map_mul]
    rw [show (D.piK : K) ^ (2 * upper.d) =
      (D.piK : K) ^ upper.d * (D.piK : K) ^ upper.d by
        rw [← pow_add]
        congr 1
        omega]
    ring
  calc
    trace F K
        (ramifiedHasseCriticalInput F K D.piK upper.d D.residueLift x *
          ramifiedHasseCriticalInput F K D.piK upper.d D.residueLift y) =
        trace F K (algebraMap F K (ax * ay) *
          (D.piK : K) ^ (2 * upper.d)) := congrArg (trace F K) hprod
    _ = (ax * ay) * trace F K ((D.piK : K) ^ (2 * upper.d)) := by
      simpa [Algebra.smul_def] using
        (Algebra.trace F K).map_smul (ax * ay)
          ((D.piK : K) ^ (2 * upper.d))
    _ = D.epsilon * (D.piF : F) ^ (2 * lower.d) *
        (D.residueLift x : F) * (D.residueLift y : F) := by
      rw [D.epsilonTraceSpecialization]
      dsimp [ax, ay]
      ring

end RamifiedHasseComparisonData

private theorem ramifiedHasseComparison_phase
    {F K : Type u}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    {lower : RamifiedHasseOddStationaryPhase F chiF psiF}
    {upper : RamifiedHasseOddStationaryPhase K chiK psiK}
    {ell t : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      lower upper ell t) :
    upper.phase = lower.phase ^ ell := by
  letI := residueFieldFintype F
  letI := residueFieldFintype K
  calc
    upper.phase = ramifiedHasseFunctionPhase
        (fun x : ResidueField K ↦ upper.function x) :=
      upper.phase_eq_functionPhase
    _ = ramifiedHasseFunctionPhase
        (fun x : ResidueField F ↦ upper.function (D.residueEquiv x)) :=
      (ramifiedHasseFunctionPhase_equiv D.residueEquiv.toEquiv
        (fun x : ResidueField K ↦ upper.function x)).symm
    _ = ramifiedHasseFunctionPhase
          (fun x : ResidueField F ↦ lower.function x) ^ ell :=
      D.finiteComparison.comparison
    _ = lower.phase ^ ell :=
      congrArg (fun z : ℂ ↦ z ^ ell) lower.phase_eq_functionPhase.symm

/-- The finite-normal-form core of the upper-to-lower Hasse/refinement
comparison.  The public theorem below specializes it to the compatible pair
constructed by the real stable-high `PhaseReduction` row. -/
theorem ramifiedHasseComparison_of_finiteNormalForms
    {F K : Type u}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    {lower : RamifiedHasseOddStationaryPhase F chiF psiF}
    {upper : RamifiedHasseOddStationaryPhase K chiK psiK}
    {ell t : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      lower upper ell t) :
    upper.localPhase.criticalFactor =
      lower.localPhase.criticalFactor ^ ell := by
  letI := residueFieldFintype F
  letI := residueFieldFintype K
  rw [← upper.phase_eq_localCriticalFactor,
    ← lower.phase_eq_localCriticalFactor]
  exact ramifiedHasseComparison_phase D

namespace HighStableOddParameterData

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
  (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
  {d dK : ℕ}
  (hF : IsStationaryConductorDecomposition chiF.conductor d 1)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK 1)
  (hchi : chiK.character = chiF.character.compNorm)
  (hpsi : psiK.character = psiF.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (hd : t + 1 ≤ d)
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))

/-- The downstairs odd phase of the real stable-high compatible pair, with
the supplied quotient representative and critical coordinate unchanged. -/
def downstairsOddStationaryPhase
    (_H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ)) :
    RamifiedHasseOddStationaryPhase F chiF psiF where
  d := d
  decomposition := hF
  denominator := ⟨gammaF, hgammaF⟩
  representative := R
  delta := deltaF
  delta_order := hdeltaF

/-- The upstairs odd phase supplied by the real stable-high row.  Its
denominator and representative are exactly `H.commonDenominator` and
`H.upstairsRepresentative R`. -/
def upstairsOddStationaryPhase
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ)) :
    RamifiedHasseOddStationaryPhase K chiK psiK where
  d := dK
  decomposition := hK
  denominator :=
    ⟨Units.map (algebraMap F K) gammaF, H.commonDenominator⟩
  representative :=
    upstairsRepresentative F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF H R
  delta := deltaK
  delta_order := hdeltaK

@[simp] theorem downstairsOddStationaryPhase_localPhase
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ)) :
    (downstairsOddStationaryPhase F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R deltaF hdeltaF).localPhase =
      (compatiblePhasePair F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R (.odd deltaF hdeltaF) (.odd deltaK hdeltaK)).downstairs :=
  rfl

@[simp] theorem upstairsOddStationaryPhase_localPhase
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ)) :
    (upstairsOddStationaryPhase F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R deltaK hdeltaK).localPhase =
      (compatiblePhasePair F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R (.odd deltaF hdeltaF) (.odd deltaK hdeltaK)).upstairs :=
  rfl

/-- Compare the actual odd critical factors in the stable-high compatible
pair returned by the real `PhaseReduction` API. -/
theorem ramifiedHasseComparison_compatiblePhasePair
    (H : HighStableOddParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    {ell : ℕ} [Fact ell.Prime]
    (D : RamifiedHasseComparisonData F K chiF psiF chiK psiK
      (downstairsOddStationaryPhase F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R deltaF hdeltaF)
      (upstairsOddStationaryPhase F K ht hres pi hpi hgen
        chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
        H R deltaK hdeltaK)
      ell t) :
    let P := compatiblePhasePair F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R (.odd deltaF hdeltaF) (.odd deltaK hdeltaK)
    P.upstairs.criticalFactor = P.downstairs.criticalFactor ^ ell := by
  change
    (upstairsOddStationaryPhase F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R deltaK hdeltaK).localPhase.criticalFactor =
    (downstairsOddStationaryPhase F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF
      H R deltaF hdeltaF).localPhase.criticalFactor ^ ell
  exact ramifiedHasseComparison_of_finiteNormalForms D

end HighStableOddParameterData

/-- Principal real-API comparison theorem.  Its full dependent type is the
stable-high compatible-pair specialization immediately above. -/
theorem ramifiedHasseComparison :
    type_of% @HighStableOddParameterData.ramifiedHasseComparison_compatiblePhasePair :=
  HighStableOddParameterData.ramifiedHasseComparison_compatiblePhasePair

/-- Explicit old/new denominator pairs together with the representative and
inverse phase translations required to transport a proved comparison. -/
structure RamifiedHasseDenominatorTransport
    (F K : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K]
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (oldLower newLower : RamifiedHasseOddStationaryPhase F chiF psiF)
    (oldUpper newUpper : RamifiedHasseOddStationaryPhase K chiK psiK)
    (ell : ℕ) where
  oldDenominatorPair :
    (oldUpper.denominator : Kˣ) =
      Units.map (algebraMap F K) (oldLower.denominator : Fˣ)
  newDenominatorPair :
    (newUpper.denominator : Kˣ) =
      Units.map (algebraMap F K) (newLower.denominator : Fˣ)
  lowerRepresentativeChange :
    (newLower.representative.representative : F) =
      denominatorChangeRatio F (oldLower.denominator : Fˣ)
        (newLower.denominator : Fˣ) *
          (oldLower.representative.representative : F)
  upperRepresentativeChange :
    (newUpper.representative.representative : K) =
      denominatorChangeRatio K (oldUpper.denominator : Kˣ)
        (newUpper.denominator : Kˣ) *
          (oldUpper.representative.representative : K)
  lowerTranslationValue : ℂ
  upperTranslationValue : ℂ
  translationPower : upperTranslationValue = lowerTranslationValue ^ ell
  lowerPhaseChange :
    newLower.phase = lowerTranslationValue⁻¹ * oldLower.phase
  upperPhaseChange :
    newUpper.phase = upperTranslationValue⁻¹ * oldUpper.phase

theorem ramifiedHasseComparison_changeDenominator
    {F K : Type u}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K]
    {chiF : LocalQuasiCharData F} {psiF : LocalAddCharData F}
    {chiK : LocalQuasiCharData K} {psiK : LocalAddCharData K}
    {oldLower newLower : RamifiedHasseOddStationaryPhase F chiF psiF}
    {oldUpper newUpper : RamifiedHasseOddStationaryPhase K chiK psiK}
    {ell : ℕ}
    (T : RamifiedHasseDenominatorTransport F K chiF psiF chiK psiK
      oldLower newLower oldUpper newUpper ell)
    (hold : oldUpper.localPhase.criticalFactor =
      oldLower.localPhase.criticalFactor ^ ell) :
    newUpper.localPhase.criticalFactor =
      newLower.localPhase.criticalFactor ^ ell := by
  letI := residueFieldFintype F
  letI := residueFieldFintype K
  have holdPhase : oldUpper.phase = oldLower.phase ^ ell := by
    rw [oldUpper.phase_eq_localCriticalFactor,
      oldLower.phase_eq_localCriticalFactor]
    exact hold
  have hnewPhase : newUpper.phase = newLower.phase ^ ell := by
    calc
    newUpper.phase =
        T.upperTranslationValue⁻¹ * oldUpper.phase := T.upperPhaseChange
    _ = (T.lowerTranslationValue ^ ell)⁻¹ *
        oldLower.phase ^ ell := by rw [T.translationPower, holdPhase]
    _ = (T.lowerTranslationValue⁻¹ * oldLower.phase) ^ ell := by
      rw [mul_pow, inv_pow]
    _ = newLower.phase ^ ell :=
      congrArg (fun z : ℂ ↦ z ^ ell) T.lowerPhaseChange.symm
  rw [← newUpper.phase_eq_localCriticalFactor,
    ← newLower.phase_eq_localCriticalFactor]
  exact hnewPhase

end

end LanglandsFirstMainLemma
