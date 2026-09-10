import LanglandsFirstMainLemma.Parameters.PhaseReduction.Odd.Core
import LanglandsFirstMainLemma.Parameters.PhaseReduction.ParameterTablePhases
import LanglandsFirstMainLemma.Parameters.PhaseReduction.FactorSeparation

/-!
# Odd-prime assembly inputs

This module collects the proof-bearing high and low row sources, coherent
polynomial data, separated scalar input, and literal admissible-character
cancellation shapes shared by the odd-prime high and low assemblies.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## One destructured high-table generator witness -/

structure HighOddNormRowSource
    (F K : Type)
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
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d epsilon)
    (htpos : 0 < t)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) where
  a : lattice F ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
  alpha : Fˣ
  alpha1 : Kˣ
  a_coe : (a : F) = (alpha : F)
  alpha_choice : IsSubcriticalNormRepresentative F K
    ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ))
    ((t + 1) / 2) alpha alpha1
  a_class : latticeQuotientMk F
      (sub_le_sub_left
        (highParameter_intermediate_normCharacterDepth
          F K ht hres pi hpi hgen htpos).int_le_conductor
        (chiF.conductor : ℤ)) a =
    stationaryNumeratorClass F
      (quasiCharDataOfIsConductor F
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (1 : ZMod (Module.finrank F K)))).1
        (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _
          (highParameter_intermediate_indexOne_ne_one
            F K ht hres pi hpi hgen)))
      psiF (chiF.conductor : ℤ)
      (highParameter_intermediate_normCharacterDepth
        F K ht hres pi hpi hgen htpos)
      gammaF hgammaF

/-- One `parameters` witness supplies the generator source used for all
nonidentity norm-character rows.  The result is `Nonempty` because the table
is Prop-valued; no representative is extracted canonically. -/
theorem highOddNormRowSource_nonempty
    (F K : Type)
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
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighOddIntermediateParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF) :
    Nonempty (HighOddNormRowSource F K ht hres pi hpi hgen
      chiF psiF hF htpos gammaF hgammaF) := by
  rcases H.parameters with
    ⟨_hmK, _hTwist, precision, a, b, alpha, beta, alpha1, beta1,
      hacoe, hbcoe, halpha1, hbeta1, ha, hb, hconversion, hrest⟩
  exact ⟨
    { a := a
      alpha := alpha
      alpha1 := alpha1
      a_coe := hacoe
      alpha_choice := halpha1
      a_class := ha }⟩

/-- A simultaneous odd high source produced from one destructuring of the
high-parameter theorem.  In particular, the norm rows and the extension/twist
product rows carry literally the same `alpha` and `alpha1`; these equalities
are not postulated between two independently selected existential packages. -/
structure HighOddCoherentPhaseSource
    (F K : Type)
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
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) where
  normRows : HighOddNormRowSource F K ht hres pi hpi hgen
    chiF psiF hF htpos gammaF hgammaF
  productRows : OddIntermediateHighProductData F K ht hres pi hpi hgen
    chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos hlower hupper
      gammaF hgammaF
  alpha_eq : normRows.alpha = productRows.alpha
  alpha1_eq : normRows.alpha1 = productRows.alpha1

section HighOddCoherentPolynomialSection

open Polynomial

/-- Exact Teichmüller factorization used in the simultaneous-source
construction.  It is repeated here because the source theorem's helper is
private; the statement remains an equality of the literal supplied scalars. -/
private theorem highOddCoherent_prod_teichmuller
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpodd : Odd p)
    (hchar : residueCharacteristic F = p)
    (A B : F) (hA : A ≠ 0) :
    (∏ j : ZMod p,
      (B + highIntermediateTeichmullerScalar F p hchar j * A)) =
      B ^ p - B * A ^ (p - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  let lam : ZMod p → F := fun j =>
    highIntermediateTeichmullerScalar F p hchar j
  have hlam_injective : Function.Injective lam := by
    intro j k hjk
    dsimp only [lam, highIntermediateTeichmullerScalar] at hjk
    change
      ((teichmuller F (ZMod.cast j : ResidueField F) :
          ringOfIntegers F) : F) =
        ((teichmuller F (ZMod.cast k : ResidueField F) :
          ringOfIntegers F) : F) at hjk
    have hjkO :
        teichmuller F (ZMod.cast j : ResidueField F) =
          teichmuller F (ZMod.cast k : ResidueField F) := by
      exact_mod_cast hjk
    have hresidue := congrArg (residueMap F) hjkO
    simp only [residueMap_teichmuller] at hresidue
    exact (ZMod.castHom (dvd_refl p) (ResidueField F)).injective hresidue
  let P : F[X] := X ^ p - X
  let Q : F[X] := ∏ j : ZMod p, (X - C (-lam j))
  have hpzero : p ≠ 0 := hp.ne_zero
  have hpone : 1 < p := hp.one_lt
  have hP : P.IsMonicOfDegree p := by
    dsimp only [P]
    exact (isMonicOfDegree_X_pow F p).sub (by simp [hpone])
  have hQmonic : Q.Monic := by
    dsimp only [Q]
    apply monic_prod_of_monic
    intro i hi
    exact monic_X_sub_C _
  have hQdegree : Q.natDegree = p := by
    dsimp only [Q]
    simpa only [Finset.card_univ, ZMod.card] using
      (natDegree_finsetProd_X_sub_C_eq_card
        (Finset.univ : Finset (ZMod p)) (fun j => -lam j))
  have hQ : Q.IsMonicOfDegree p := ⟨hQdegree, hQmonic⟩
  have hPQzero : P - Q = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (P - Q) (f := fun j : ZMod p => -lam j)
    · intro j k h
      exact hlam_injective (neg_inj.mp h)
    · intro j
      have hlam_pow : lam j ^ p = lam j := by
        exact highParameter_intermediate_teichmuller_pow F p hchar j
      have hPzero : P.eval (-lam j) = 0 := by
        dsimp only [P]
        simp only [eval_sub, eval_pow, eval_X]
        rw [hpodd.neg_pow, hlam_pow]
        ring
      have hQzero : Q.eval (-lam j) = 0 := by
        dsimp only [Q]
        rw [eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp
      rw [eval_sub, hPzero, hQzero, sub_zero]
    · simpa only [ZMod.card] using hP.natDegree_sub_lt hpzero hQ
  have hPQ : P = Q := sub_eq_zero.mp hPQzero
  have heval := congrArg (Polynomial.eval (B / A)) hPQ
  have hpow : A ^ p = A ^ (p - 1) * A := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
  have hscaled :
      A ^ p * (∏ j : ZMod p, (B / A + lam j)) =
        B ^ p - B * A ^ (p - 1) := by
    simp only [P, Q, eval_sub, eval_pow, eval_X, eval_prod,
      eval_C, sub_neg_eq_add] at heval
    rw [← heval, mul_sub]
    congr 1
    · rw [div_pow]
      field_simp [hA]
    · rw [div_eq_mul_inv, hpow]
      field_simp [hA]
  calc
    (∏ j : ZMod p,
      (B + highIntermediateTeichmullerScalar F p hchar j * A)) =
        ∏ j : ZMod p, A * (B / A + lam j) := by
          apply Finset.prod_congr rfl
          intro j hj
          dsimp only [lam]
          field_simp [hA]
    _ = A ^ p * ∏ j : ZMod p, (B / A + lam j) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, ZMod.card]
    _ = B ^ p - B * A ^ (p - 1) := hscaled

end HighOddCoherentPolynomialSection

set_option maxHeartbeats 16000000 in
/-- Destructure one `HighOddIntermediateParameterData` proof exactly once
and build both odd high row packages from that same tuple. -/
theorem highOddCoherentPhaseSource_nonempty
    (F K : Type)
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
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighOddIntermediateParameterData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos hlower
        hupper gammaF hgammaF) :
    Nonempty (HighOddCoherentPhaseSource F K ht hres pi hpi hgen chiF chiK
      psiF psiK hF hK hminimal hchi hpsi hodd htpos hlower hupper gammaF
        hgammaF) := by
  letI : NeZero (Module.finrank F K) := ⟨Module.finrank_pos.ne'⟩
  rcases H.parameters with
    ⟨_hconductor, _htwistsConductor, precision, a, b, alpha, beta, alpha1,
      beta1, hacoe, hbcoe, halpha1, hbeta1, ha, hb, _hconversion,
        hcandidatePack⟩
  obtain ⟨hcandidate, hcandidateData⟩ := hcandidatePack
  obtain ⟨_hadjoint, hupstairs, htwists⟩ := hcandidateData
  choose hJ hgammaJ hlinearMem hnormMem hnormLinear hnormClass using htwists
  let p : ℕ := Module.finrank F K
  let T : ℕ := t + 1
  let hchar : residueCharacteristic F = p := by
    simpa only [p] using residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
  let lam : ZMod p → F := fun j ↦
    highIntermediateTeichmullerScalar F p hchar j
  let candidate : K :=
    algebraMap F K (norm F K (beta1 : K)) -
      (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
        (alpha1 : K)
  let linear : ZMod p → F := fun j ↦
    norm F K (beta1 : K) + lam j * norm F K (alpha1 : K)
  let lower : ZMod p → F := fun j ↦
    norm F K ((beta1 : K) + algebraMap F K (lam j) * (alpha1 : K))
  have hlinearClass (j : ZMod p) :
      latticeQuotientMk F (Int.natCast_nonneg d)
          (⟨linear j, by
            simpa only [linear, lam, p, hchar] using (hlinearMem j)⟩ :
              lattice F 0) =
        stationaryCoefficientClass F
          (ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chiF
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd j)))
          psiF (hJ j) gammaF (hgammaJ j) := by
    exact (hnormLinear j).symm.trans (hnormClass j)
  have hlowerClass (j : ZMod p) :
      latticeQuotientMk F (Int.natCast_nonneg d)
          (⟨lower j, by
            simpa only [lower, lam, p, hchar] using (hnormMem j)⟩ :
              lattice F 0) =
        stationaryCoefficientClass F
          (ramifiedNormCharacterOrbitTwistData F K ht hres pi hpi hgen chiF
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd j)))
          psiF (hJ j) gammaF (hgammaJ j) := by
    simpa only [lower, lam, p, hchar] using hnormClass j
  let candidateLattice : lattice K 0 := ⟨candidate, by
    simpa only [candidate] using hcandidate⟩
  have hcandidateClass :
      latticeQuotientMk K (Int.natCast_nonneg dK) candidateLattice =
        stationaryCoefficientClass K chiK psiK hK
          (Units.map (algebraMap F K) gammaF)
          (highParameter_intermediate_commonDenominator
            F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal hchi hpsi
              hlower gammaF hgammaF) := by
    simpa only [candidateLattice, candidate] using hupstairs
  have hcandidateOrd : ord K candidate = 0 := by
    simpa only [candidateLattice] using
      stationaryCoefficientClass_suppliedRepresentative_ord K hcandidateClass
  have hcandidateNe : candidate ≠ 0 := by
    apply (ord_ne_top_iff K).1
    rw [hcandidateOrd]
    simp
  let candidateUnit : Kˣ := Units.mk0 candidate hcandidateNe
  let upstairs : unitFiltration K 0 := ⟨candidateUnit, by
    exact (mem_unitFiltration_zero K candidateUnit).2 (by
      simpa only [candidateUnit, Units.val_mk0] using hcandidateOrd)⟩
  have hlinearOrd (j : ZMod p) : ord F (linear j) = 0 := by
    let linearLattice : lattice F 0 := ⟨linear j, by
      simpa only [linear, lam, p, hchar] using hlinearMem j⟩
    simpa only [linearLattice] using
      stationaryCoefficientClass_suppliedRepresentative_ord F (hlinearClass j)
  have hlinearNe (j : ZMod p) : linear j ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [hlinearOrd j]
    simp
  have hlowerOrd (j : ZMod p) : ord F (lower j) = 0 := by
    let lowerLattice : lattice F 0 := ⟨lower j, by
      simpa only [lower, lam, p, hchar] using hnormMem j⟩
    simpa only [lowerLattice] using
      stationaryCoefficientClass_suppliedRepresentative_ord F (hlowerClass j)
  have hlowerNe (j : ZMod p) : lower j ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [hlowerOrd j]
    simp
  let factorUnit (j : ZMod p) : Fˣ := Units.mk0 (lower j) (hlowerNe j)
  let factors : ZMod p → unitFiltration F 0 := fun j ↦
    ⟨factorUnit j, (mem_unitFiltration_zero F (factorUnit j)).2 (by
      simpa only [factorUnit, Units.val_mk0] using hlowerOrd j)⟩
  let linearUnit (j : ZMod p) : Fˣ := Units.mk0 (linear j) (hlinearNe j)
  let linearFactors : ZMod p → unitFiltration F 0 := fun j ↦
    ⟨linearUnit j, (mem_unitFiltration_zero F (linearUnit j)).2 (by
      simpa only [linearUnit, Units.val_mk0] using hlinearOrd j)⟩
  have hp : p.Prime := by
    simpa only [p] using PrimeCyclicExtension.degree_prime F K
  have hram : ramificationIndex F K = p := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    simpa only [p] using hdegree.symm
  have htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ) := by
    simpa only [p, T] using
      traceIdealLowerBound_of_integralGenerator F K ht hres pi hpi hgen
  have halphaSource : ord K (alpha1 : K) =
      ((((chiF.conductor - T : ℕ) : ℤ) : WithTop ℤ)) := by
    simpa only [T, Int.ofNat_sub hlower] using halpha1.source_order
  have hcandidateEndpoint :=
    highParameter_intermediate_norm_product_congruent F K p T
      chiF.conductor d epsilon hp hodd (by dsimp only [T]; omega)
        hchar rfl hres hram htrace hF (by simpa only [T] using hlower)
        alpha1 beta1 halphaSource hbeta1.source_order
  have halphaNormNe : norm F K (alpha1 : K) ≠ 0 :=
    (Algebra.norm_ne_zero_iff).2 (Units.ne_zero alpha1)
  have hproductExact := highOddCoherent_prod_teichmuller F p hp hodd hchar
    (norm F K (alpha1 : K)) (norm F K (beta1 : K)) halphaNormNe
  have hnormProduct :
      norm F K candidate - ∏ j : ZMod p, linear j ∈ lattice F (d : ℤ) := by
    rw [show (∏ j : ZMod p, linear j) =
        norm F K (beta1 : K) ^ p -
          norm F K (beta1 : K) * norm F K (alpha1 : K) ^ (p - 1) by
      simpa only [linear, lam] using hproductExact]
    simpa only [candidate] using hcandidateEndpoint
  have hcongruentLinear : CongruentAtDepth (d : ℤ)
      ((normUnits F K (upstairs : Kˣ) : Fˣ) : F)
      (((∏ j, linearFactors j : unitFiltration F 0) : Fˣ) : F) := by
    rw [congruentAtDepth_iff_sub_mem_lattice]
    have hlinearFactorsCoe :
        (((∏ j, linearFactors j : unitFiltration F 0) : Fˣ) : F) =
          ∏ j, linear j := by
      change (Units.coeHom F)
        ((unitFiltration F 0).subtype (∏ j, linearFactors j)) = _
      rw [map_prod, map_prod]
      apply Finset.prod_congr rfl
      intro j _
      rfl
    rw [hlinearFactorsCoe]
    simpa only [upstairs, candidateUnit, Units.val_mk0, coe_normUnits] using
      hnormProduct
  have hfactorCongruent (j : ZMod p) :
      CongruentAtDepth (d : ℤ) (lower j) (linear j) := by
    have h := (latticeQuotientMk_eq_mk_iff_congruentAtDepth F
      (Int.natCast_nonneg d)).1 (hnormLinear j)
    simpa only [lower, linear, lam, p, hchar] using h
  have hfactorQuotient (j : ZMod p) :
      unitFiltrationQuotientMk F (Nat.zero_le d) (factors j) =
        unitFiltrationQuotientMk F (Nat.zero_le d) (linearFactors j) := by
    apply (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
      (Nat.zero_le d) _ _).2
    simpa only [factors, factorUnit, linearFactors, linearUnit,
      Units.val_mk0] using hfactorCongruent j
  have hfactorProductQuotient :
      (∏ j, unitFiltrationQuotientMk F (Nat.zero_le d) (factors j)) =
        ∏ j, unitFiltrationQuotientMk F (Nat.zero_le d)
          (linearFactors j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hfactorQuotient j
  have hfactorProductCongruent : CongruentAtDepth (d : ℤ)
      (((∏ j, factors j : unitFiltration F 0) : Fˣ) : F)
      (((∏ j, linearFactors j : unitFiltration F 0) : Fˣ) : F) := by
    apply (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
      (Nat.zero_le d) _ _).1
    rw [map_prod, map_prod]
    exact hfactorProductQuotient
  have hcongruent : CongruentAtDepth (d : ℤ)
      ((normUnits F K (upstairs : Kˣ) : Fˣ) : F)
      (((∏ j, factors j : unitFiltration F 0) : Fˣ) : F) :=
    hcongruentLinear.trans hfactorProductCongruent.symm
  have hclosed : CongruentAtDepth (d : ℤ)
      ((normUnits F K (upstairs : Kˣ) : Fˣ) : F)
      (norm F K (beta1 : K) ^ p -
        norm F K (beta1 : K) * norm F K (alpha1 : K) ^ (p - 1)) := by
    rw [congruentAtDepth_iff_sub_mem_lattice]
    simpa only [upstairs, candidateUnit, Units.val_mk0, coe_normUnits,
      candidate] using hcandidateEndpoint
  have hnormEq :
      normPolynomialStationaryNormClass F K precision
          (unitFiltrationQuotientMk K (Nat.zero_le dK) upstairs) =
        ∏ j, unitFiltrationQuotientMk F (Nat.zero_le d) (factors j) := by
    rw [normPolynomialStationaryNormClass, stationaryNormClass_mk, ← map_prod]
    exact (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
      (Nat.zero_le d) _ _).2 hcongruent
  let product : HighStationaryNormProduct F K precision (ZMod p) :=
    ⟨upstairs, factors, hnormEq⟩
  let Q : OddIntermediateHighProductData F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos hlower
        hupper gammaF hgammaF := by
    refine
      { precision := precision
        alpha := alpha
        beta := beta
        alpha1 := alpha1
        beta1 := beta1
        alpha_choice := halpha1
        beta_choice := hbeta1
        quotientProduct := product
        upstairs_formula := ?_
        upstairs_class := ?_
        factorDecomposition := hJ
        factorDenominator := hgammaJ
        factor_formula := ?_
        factor_linear_congruence := ?_
        factor_class := ?_
        closed_product_congruence := ?_ }
    · rfl
    · simpa only [product, upstairs, candidateUnit, Units.val_mk0,
        candidateLattice, candidate] using hcandidateClass
    · intro j
      rfl
    · intro j
      simpa only [product, factors, factorUnit, Units.val_mk0, lower, lam]
        using hfactorCongruent j
    · intro j
      simpa only [product, factors, factorUnit, Units.val_mk0] using
        hlowerClass j
    · simpa only [product, p] using hclosed
  let S : HighOddNormRowSource F K ht hres pi hpi hgen chiF psiF hF htpos
      gammaF hgammaF :=
    { a := a
      alpha := alpha
      alpha1 := alpha1
      a_coe := hacoe
      alpha_choice := halpha1
      a_class := ha }
  exact ⟨
    { normRows := S
      productRows := Q
      alpha_eq := rfl
      alpha1_eq := rfl }⟩

/-! ## Actual table-built rows in the computational datum -/

/-- The target's exact-norm high-table row, transported only across the
proof-bearing local quasi-character datum.  Its denominator is
`gammaF / N(alpha1)`, its conductor is `t+1`, and its representative is the
proved Teichmüller scalar. -/
def highOddNormPhaseForComputationalData
    (F K : Type)
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
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon)
    (htpos : 0 < t)
    (hlower : t + 1 ≤ (data.twistData 1).conductor)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      ((((data.twistData 1).conductor : ℤ) +
        data.baseAddChar.conductor : ℤ) : WithTop ℤ))
    (S : HighOddNormRowSource F K ht hres pi hpi hgen
      (data.twistData 1) data.baseAddChar hF htpos gammaF hgammaF)
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))))
      data.baseAddChar := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hmu : mu ≠ 1 := by
    apply (ramifiedNormCharacterZModEquiv_ne_one_iff
      F K ht hres pi hpi hgen _).2
    intro h
    exact j.property (by
      have h' := congrArg Multiplicative.toAdd h
      simpa using h')
  let muData := quasiCharDataOfIsConductor F mu.1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen mu hmu)
  have hdata : muData = data.normCharacterData mu := by
    apply LocalQuasiCharData.ext_character F
    rw [quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
  let sourcePhase := highOddNormCharacterPowerPhase F K ht hres pi hpi hgen
    (data.twistData 1) data.baseAddChar htpos hlower gammaF hgammaF
      S.a S.alpha S.a_coe S.alpha1 S.alpha_choice S.a_class
      (j : ZMod (Module.finrank F K)) j.property C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

/-- The low-table power row transported only across the proof-bearing
computational datum.  It keeps the simultaneous pair's representative
`[j]·alpha`, denominator `delta`, and exact conductor/depth. -/
def lowOddNormPhaseForComputationalData
    (F K : Type)
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
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    {d epsilon : ℕ}
    (hF : IsStationaryConductorDecomposition
      (data.twistData 1).conductor d epsilon)
    (delta : Fˣ) (epsilon1 : Kˣ)
    (hdelta : ord F (delta : F) =
      ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
    (hT : 2 ≤ t + 1)
    (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
      ((((data.twistData 1).conductor : ℤ) +
        data.baseAddChar.conductor : ℤ) : WithTop ℤ))
    (P : LowStationaryNormRepresentativePair F K
      (lowCriticalFloorDepth t) d
      (stationaryCoefficientClass F
        (quasiCharDataOfIsConductor F
          (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
          (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
            (lowNormCharacterGenerator F K ht hres pi hpi hgen)
            (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
        data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
          delta hdelta)
      (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
        (lowGammaF F K delta epsilon1) hgammaF))
    (j : OddNormIndex F K)
    (C : LamprechtCriticalCoordinate F
      (lowCriticalFloorDepth t) (lowCriticalParity t)) :
    LocalLamprechtPhaseData F
      (data.normCharacterData
        (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))))
      data.baseAddChar := by
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have hpow : tau ^ (j : ZMod (Module.finrank F K)).val ≠ 1 :=
    lowGeneratorPower_ne_one F K ht hres pi hpi hgen j j.property
  let powerData := quasiCharDataOfIsConductor F
    (tau ^ (j : ZMod (Module.finrank F K)).val).1 (t + 1)
    (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen _ hpow)
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hmuPower : mu = tau ^ (j : ZMod (Module.finrank F K)).val :=
    lowNormCharacterGenerator_pow F K ht hres pi hpi hgen j
  have hdata : powerData = data.normCharacterData mu := by
    apply LocalQuasiCharData.ext_character F
    rw [quasiCharDataOfIsConductor_character,
      data.normCharacterData_character]
    exact congrArg (fun z : NormCharacter F K ↦ z.1) hmuPower.symm
  let sourcePhase := lowNormCharacterPowerPhase F K ht hres pi hpi hgen
    (data.twistData 1) data.baseAddChar hF delta epsilon1 hdelta hT hgammaF P
      (j : ZMod (Module.finrank F K)) j.property C
  exact transportLocalLamprechtPhaseData
    (congrArg LocalQuasiCharData.character hdata) rfl sourcePhase

namespace FirstMainPhaseData

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F}
  {globalPsi : ContinuousAddChar F}
  {data : FirstMainComputationalData F K globalChi globalPsi}
  (D : FirstMainPhaseData F K globalChi globalPsi data)

local instance : Fintype (NormCharacter F K) :=
  Fintype.ofFinite (NormCharacter F K)

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

private theorem identityNorm_elementaryAdditiveFactor_eq_one :
    (D.normCharacter 1).elementaryAdditiveFactor = 1 := by
  rcases identityNormCharacterEndpoint_of_phaseData D with
    ⟨_h, _Gamma, hrow⟩
  rw [hrow]
  rfl

private theorem identityNorm_elementaryMultiplicativeFactor_eq_one :
    (D.normCharacter 1).elementaryMultiplicativeFactor = 1 := by
  rcases identityNormCharacterEndpoint_of_phaseData D with
    ⟨_h, _Gamma, hrow⟩
  rw [hrow]
  rfl

/-- Reindex the positive-additive numerator into the literal extension row
and exactly the nonidentity norm-character rows. -/
theorem oddElementaryAdditiveNumerator_reindex :
    D.elementaryAdditiveNumerator =
      D.extension.elementaryAdditiveFactor *
        ∏ j : OddNormIndex F K,
          (D.normCharacter
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd
                (j : ZMod (Module.finrank F K))))).elementaryAdditiveFactor := by
  rw [elementaryAdditiveNumerator]
  rw [← Equiv.prod_comp (oddNormCharacterIndexing
    F K ht hres pi hpi hgen)
    (fun mu : NormCharacter F K ↦
      (D.normCharacter mu).elementaryAdditiveFactor)]
  rw [Fintype.prod_option,
    oddNormCharacterIndexing_none F K ht hres pi hpi hgen,
    identityNorm_elementaryAdditiveFactor_eq_one D,
    one_mul]
  congr 1

/-- Reindex the inverse-character numerator into the literal extension row
and exactly the nonidentity norm-character rows. -/
theorem oddElementaryMultiplicativeNumerator_reindex :
    D.elementaryMultiplicativeNumerator =
      D.extension.elementaryMultiplicativeFactor *
        ∏ j : OddNormIndex F K,
          (D.normCharacter
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd
                (j : ZMod (Module.finrank F K))))).elementaryMultiplicativeFactor := by
  rw [elementaryMultiplicativeNumerator]
  rw [← Equiv.prod_comp (oddNormCharacterIndexing
    F K ht hres pi hpi hgen)
    (fun mu : NormCharacter F K ↦
      (D.normCharacter mu).elementaryMultiplicativeFactor)]
  rw [Fintype.prod_option,
    oddNormCharacterIndexing_none F K ht hres pi hpi hgen,
    identityNorm_elementaryMultiplicativeFactor_eq_one D,
    one_mul]
  congr 1

/-- Reindex the positive-additive denominator into its identity twist and
the literal nonidentity twist rows. -/
theorem oddElementaryAdditiveDenominator_reindex :
    D.elementaryAdditiveDenominator =
      (D.twist 1).elementaryAdditiveFactor *
        ∏ j : OddNormIndex F K,
          (D.twist
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd
                (j : ZMod (Module.finrank F K))))).elementaryAdditiveFactor := by
  rw [elementaryAdditiveDenominator]
  rw [← Equiv.prod_comp (oddNormCharacterIndexing
    F K ht hres pi hpi hgen)
    (fun mu : NormCharacter F K ↦
      (D.twist mu).elementaryAdditiveFactor)]
  rw [Fintype.prod_option,
    oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
  congr 1

/-- Reindex the inverse-character denominator into its identity twist and
the literal nonidentity twist rows. -/
theorem oddElementaryMultiplicativeDenominator_reindex :
    D.elementaryMultiplicativeDenominator =
      (D.twist 1).elementaryMultiplicativeFactor *
        ∏ j : OddNormIndex F K,
          (D.twist
            (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
              (Multiplicative.ofAdd
                (j : ZMod (Module.finrank F K))))).elementaryMultiplicativeFactor := by
  rw [elementaryMultiplicativeDenominator]
  rw [← Equiv.prod_comp (oddNormCharacterIndexing
    F K ht hres pi hpi hgen)
    (fun mu : NormCharacter F K ↦
      (D.twist mu).elementaryMultiplicativeFactor)]
  rw [Fintype.prod_option,
    oddNormCharacterIndexing_none F K ht hres pi hpi hgen]
  congr 1

end FirstMainPhaseData

/-- A finite product of values of an additive character is its value on the
finite sum of the literal arguments. -/
theorem continuousAddChar_prod_apply_eq_apply_sum
    {E I : Type*} [Field E] [TopologicalSpace E] [Fintype I]
    (psi : ContinuousAddChar E) (f : I → E) :
    (∏ i : I, (psi (f i) : ℂ)) = (psi (∑ i : I, f i) : ℂ) := by
  classical
  let s : Finset I := Finset.univ
  change (∏ i ∈ s, (psi (f i) : ℂ)) = (psi (∑ i ∈ s, f i) : ℂ)
  have hs : ∀ s : Finset I,
      (∏ i ∈ s, (psi (f i) : ℂ)) = (psi (∑ i ∈ s, f i) : ℂ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp [ha, ih, ContinuousAddChar.map_add_eq_mul]
  exact hs s

/-! ## The genuinely global scalar input -/

/-- Legacy lower-level scalar input.  Its aggregate endpoint, admissible, and
whole-elementary equalities are not consequences of the parameter tables.
The documented table-backed entry points below instead use
`OddSeparatedScalarInput` and derive the first two cancellations from actual
rows while keeping the additive and multiplicative scalar calculations
separate. -/
structure OddGlobalScalarInput
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [NeZero (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (globalChi : ContinuousQuasiChar F)
    (globalPsi : ContinuousAddChar F)
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (D : FirstMainPhaseData F K globalChi globalPsi data) where
  A : F
  u : K
  n : F
  norm_u : norm F K u = n
  zZero : Fˣ
  z : OddNormIndex F K → Fˣ
  X : F
  X_eq : X = trace F K u + n * ((zZero : F) - 1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
        ((z j : F) - 1)
  chiLinearization : globalChi zZero =
    globalPsi (A * n * ((zZero : F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1 (z j) =
      globalPsi (A *
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          ((z j : F) - 1))
  endpointCommonFactor : ℂ
  endpointCommonFactor_ne_zero : endpointCommonFactor ≠ 0
  endpointNumerator_eq : D.endpointNumerator = endpointCommonFactor
  endpointDenominator_eq : D.endpointDenominator = endpointCommonFactor
  admissibleCommonFactor : ℂ
  admissibleCommonFactor_ne_zero : admissibleCommonFactor ≠ 0
  admissibleNumerator_eq : D.admissibleNumerator = admissibleCommonFactor
  admissibleDenominator_eq : D.admissibleDenominator = admissibleCommonFactor
  elementaryCommonFactor : ℂ
  elementaryCommonFactor_ne_zero : elementaryCommonFactor ≠ 0
  elementaryNumerator_eq : D.elementaryNumerator = elementaryCommonFactor
  elementaryDenominator_eq : D.elementaryDenominator =
    ((globalPsi (A * trace F K u) : ℂ) *
      (globalChi zZero : ℂ) *
      ∏ j : OddNormIndex F K,
        ((ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))).1 (z j) : ℂ)) *
      elementaryCommonFactor

/-- Global scalar input for exact odd assembly after removing opaque
endpoint, admissible-character, and whole-elementary product assumptions.
Only the correction coordinate, its pointwise linearizations, and the two
separately oriented additive and multiplicative scalar products remain. -/
structure OddSeparatedScalarInput
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [NeZero (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    (globalChi : ContinuousQuasiChar F)
    (globalPsi : ContinuousAddChar F)
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (D : FirstMainPhaseData F K globalChi globalPsi data) where
  A : F
  u : K
  n : F
  norm_u : norm F K u = n
  zZero : Fˣ
  z : OddNormIndex F K → Fˣ
  X : F
  X_eq : X = trace F K u + n * ((zZero : F) - 1) +
    ∑ j : OddNormIndex F K,
      oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
        ((z j : F) - 1)
  chiLinearization : globalChi zZero =
    globalPsi (A * n * ((zZero : F) - 1))
  powerLinearization : ∀ j : OddNormIndex F K,
    (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd
        (j : ZMod (Module.finrank F K)))).1 (z j) =
      globalPsi (A *
        oddNormIndexScalar F K ht hres pi hpi hgen htpos j *
          ((z j : F) - 1))
  additiveDenominator_eq : D.elementaryAdditiveDenominator =
    (globalPsi (A * trace F K u) : ℂ) * D.elementaryAdditiveNumerator
  multiplicativeDenominator_eq : D.elementaryMultiplicativeDenominator =
    ((globalChi zZero : ℂ) *
      ∏ j : OddNormIndex F K,
        ((ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
          (Multiplicative.ofAdd
            (j : ZMod (Module.finrank F K)))).1 (z j) : ℂ)) *
      D.elementaryMultiplicativeNumerator

namespace OddSeparatedScalarInput

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  [NeZero (Module.finrank F K)]
  {t : ℕ} {ht : PrimeCyclicExtension.IsLowerBreak F K t}
  {hres : residueDegree F K = 1}
  {pi : ringOfIntegers K}
  {hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K)}
  {hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤}
  {htpos : 0 < t}
  {globalChi : ContinuousQuasiChar F}
  {globalPsi : ContinuousAddChar F}
  {data : FirstMainComputationalData F K globalChi globalPsi}
  {D : FirstMainPhaseData F K globalChi globalPsi data}

/-- The two separated scalar products reassemble in the manuscript's exact
denominator orientation. -/
theorem elementaryDenominator_eq_bracket_mul
    (R : OddSeparatedScalarInput F K ht hres pi hpi hgen htpos
      globalChi globalPsi data D) :
    D.elementaryDenominator =
      ((globalPsi (R.A * trace F K R.u) : ℂ) *
        (globalChi R.zZero : ℂ) *
        ∏ j : OddNormIndex F K,
          ((ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))).1 (R.z j) : ℂ)) *
        D.elementaryNumerator := by
  rw [D.elementaryDenominator_eq_separated,
    D.elementaryNumerator_eq_separated,
    R.additiveDenominator_eq, R.multiplicativeDenominator_eq]
  ring

end OddSeparatedScalarInput

/-- Fill the exact odd assembly with canonical exhaustive nonidentity
indexing and *actual supplied local phases*.  Unlike the original raw record,
`normCharacterStationary` is derived from `row_eq`; callers cannot insert an
unrelated existential stationary package. -/
def exactOddAssemblyOfActualNormRows
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [NeZero (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (D : FirstMainPhaseData F K globalChi globalPsi data)
    (range : PhaseParameterRange t (data.twistData 1).conductor)
    (row : ∀ j : OddNormIndex F K,
      LocalLamprechtPhaseData F
        (data.normCharacterData
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))))
        data.baseAddChar)
    (row_eq : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary (row j))
    (R : OddGlobalScalarInput F K ht hres pi hpi hgen htpos
      globalChi globalPsi data D) :
    ExactOddPhaseAssembly F K globalChi globalPsi data D
      (t := t) (m := (data.twistData 1).conductor) (OddNormIndex F K) := by
  let indexing := oddNormCharacterIndexing F K ht hres pi hpi hgen
  let mu : OddNormIndex F K → NormCharacter F K := fun j ↦
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  exact
    { baseData := data.twistData 1
      baseData_eq := rfl
      baseCharacter := by
        rw [data.twistData_character]
        ext x
        simp
      baseConductor := rfl
      parameterRange := range
      A := R.A
      u := R.u
      n := R.n
      norm_u := R.norm_u
      zZero := R.zZero
      z := R.z
      indexScalar := oddNormIndexScalar F K ht hres pi hpi hgen htpos
      normCharacterIndex := mu
      normCharacterIndexing := indexing
      normCharacterIndexing_none := by
        exact oddNormCharacterIndexing_none F K ht hres pi hpi hgen
      normCharacterIndexing_some := by
        intro j
        exact oddNormCharacterIndexing_some F K ht hres pi hpi hgen j
      normCharacterStationary := by
        intro j
        exact ⟨row j, row_eq j⟩
      normCharacterPower := fun j ↦ (mu j).1
      normCharacterPower_eq := fun _ ↦ rfl
      X := R.X
      X_eq := R.X_eq
      chiLinearization := R.chiLinearization
      powerLinearization := R.powerLinearization
      endpointCommonFactor := R.endpointCommonFactor
      endpointCommonFactor_ne_zero := R.endpointCommonFactor_ne_zero
      endpointNumerator_eq := R.endpointNumerator_eq
      endpointDenominator_eq := R.endpointDenominator_eq
      admissibleCommonFactor := R.admissibleCommonFactor
      admissibleCommonFactor_ne_zero := R.admissibleCommonFactor_ne_zero
      admissibleNumerator_eq := R.admissibleNumerator_eq
      admissibleDenominator_eq := R.admissibleDenominator_eq
      elementaryCommonFactor := R.elementaryCommonFactor
      elementaryCommonFactor_ne_zero := R.elementaryCommonFactor_ne_zero
      elementaryNumerator_eq := R.elementaryNumerator_eq
      elementaryDenominator_eq := R.elementaryDenominator_eq }

/-- Build the exact odd decomposition from actual stationary rows and the
separated scalar calculation.  Endpoint and admissible cancellation are
proved facts, never fields of the scalar input. -/
def exactOddAssemblyOfActualNormRowsSeparated
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [Finite (NormCharacter F K)]
    [NeZero (Module.finrank F K)]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t)
    {globalChi : ContinuousQuasiChar F}
    {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (D : FirstMainPhaseData F K globalChi globalPsi data)
    (range : PhaseParameterRange t (data.twistData 1).conductor)
    (row : ∀ j : OddNormIndex F K,
      LocalLamprechtPhaseData F
        (data.normCharacterData
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))))
        data.baseAddChar)
    (row_eq : ∀ j : OddNormIndex F K,
      D.normCharacter
          (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
            (Multiplicative.ofAdd
              (j : ZMod (Module.finrank F K)))) =
        LocalPhaseData.stationary (row j))
    (R : OddSeparatedScalarInput F K ht hres pi hpi hgen htpos
      globalChi globalPsi data D)
    (hEndpoint : D.factors.endpoint = 1)
    (hAdmissible : D.factors.admissibleCharacter = 1) :
    ExactOddPhaseAssembly F K globalChi globalPsi data D
      (t := t) (m := (data.twistData 1).conductor)
        (OddNormIndex F K) := by
  let indexing := oddNormCharacterIndexing F K ht hres pi hpi hgen
  let mu : OddNormIndex F K → NormCharacter F K := fun j ↦
    ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  have hEndpointEq : D.endpointNumerator = D.endpointDenominator := by
    apply (div_eq_one_iff_eq D.endpointDenominator_ne_zero).mp
    simpa only [FirstMainPhaseData.factors] using hEndpoint
  have hAdmissibleEq : D.admissibleNumerator =
      D.admissibleDenominator := by
    apply (div_eq_one_iff_eq D.admissibleDenominator_ne_zero).mp
    simpa only [FirstMainPhaseData.factors] using hAdmissible
  exact
    { baseData := data.twistData 1
      baseData_eq := rfl
      baseCharacter := by
        rw [data.twistData_character]
        ext x
        simp
      baseConductor := rfl
      parameterRange := range
      A := R.A
      u := R.u
      n := R.n
      norm_u := R.norm_u
      zZero := R.zZero
      z := R.z
      indexScalar := oddNormIndexScalar F K ht hres pi hpi hgen htpos
      normCharacterIndex := mu
      normCharacterIndexing := indexing
      normCharacterIndexing_none := by
        exact oddNormCharacterIndexing_none F K ht hres pi hpi hgen
      normCharacterIndexing_some := by
        intro j
        exact oddNormCharacterIndexing_some F K ht hres pi hpi hgen j
      normCharacterStationary := by
        intro j
        exact ⟨row j, row_eq j⟩
      normCharacterPower := fun j ↦ (mu j).1
      normCharacterPower_eq := fun _ ↦ rfl
      X := R.X
      X_eq := R.X_eq
      chiLinearization := R.chiLinearization
      powerLinearization := R.powerLinearization
      endpointCommonFactor := D.endpointDenominator
      endpointCommonFactor_ne_zero := D.endpointDenominator_ne_zero
      endpointNumerator_eq := hEndpointEq
      endpointDenominator_eq := rfl
      admissibleCommonFactor := D.admissibleDenominator
      admissibleCommonFactor_ne_zero := D.admissibleDenominator_ne_zero
      admissibleNumerator_eq := hAdmissibleEq
      admissibleDenominator_eq := rfl
      elementaryCommonFactor := D.elementaryNumerator
      elementaryCommonFactor_ne_zero := D.elementaryNumerator_ne_zero
      elementaryNumerator_eq := rfl
      elementaryDenominator_eq :=
        R.elementaryDenominator_eq_bracket_mul }

/-! High-range admissible-character cancellation from the literal table
gammas. -/

/-- The four literal high-row gamma evaluations.  This shape contains no
aggregate numerator or denominator equality. -/
structure HighOddAdmissibleShape
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (gammaF : Fˣ) (alpha1 : Kˣ)
    (D : FirstMainPhaseData F K globalChi globalPsi data) : Prop where
  extension_factor : D.extension.admissibleFactor =
    (data.extensionQuasiChar.character
      (Units.map (algebraMap F K) gammaF) : ℂ)
  identity_norm_factor : (D.normCharacter 1).admissibleFactor = 1
  nonidentity_norm_factor : ∀ mu, mu ≠ 1 →
    (D.normCharacter mu).admissibleFactor =
      (data.normCharacterData mu).character
        (gammaF / normUnits F K alpha1)
  twist_factor : ∀ mu, (D.twist mu).admissibleFactor =
    (data.twistData mu).character gammaF

namespace HighOddAdmissibleShape

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  {t : ℕ}
  (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

local instance : Fintype (NormCharacter F K) :=
  Fintype.ofFinite (NormCharacter F K)

private theorem extension_balance
    (hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm)
    (gammaF : Fˣ) :
    (data.extensionQuasiChar.character
      (Units.map (algebraMap F K) gammaF) : ℂ) =
      ((data.twistData 1).character gammaF : ℂ) ^
        Module.finrank F K := by
  have hnormMap :
      normUnits F K (Units.map (algebraMap F K) gammaF) =
        gammaF ^ Module.finrank F K := by
    ext
    simp
  rw [hchiArg, ContinuousQuasiChar.compNorm_apply, hnormMap, map_pow]
  rfl

theorem numerator_eq_explicit
    {gammaF : Fˣ} {alpha1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (S : HighOddAdmissibleShape data gammaF alpha1 D) :
    D.admissibleNumerator =
      (data.extensionQuasiChar.character
        (Units.map (algebraMap F K) gammaF) : ℂ) *
        ∏ mu : NormCharacter F K, (mu.1 gammaF : ℂ) := by
  rw [FirstMainPhaseData.admissibleNumerator, S.extension_factor]
  congr 1
  apply Finset.prod_congr rfl
  intro mu _hmu
  by_cases hmu : mu = 1
  · subst mu
    rw [S.identity_norm_factor]
    simp
  · rw [S.nonidentity_norm_factor mu hmu,
      data.normCharacterData_character, map_div]
    rw [NormCharacter.eq_one_on_normRange F K mu
      (normUnits F K alpha1) ⟨alpha1, rfl⟩,
      div_one]

theorem denominator_eq_explicit
    {gammaF : Fˣ} {alpha1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (S : HighOddAdmissibleShape data gammaF alpha1 D) :
    D.admissibleDenominator =
      ∏ mu : NormCharacter F K,
        (mu.1 gammaF : ℂ) *
          ((data.twistData 1).character gammaF : ℂ) := by
  rw [FirstMainPhaseData.admissibleDenominator]
  apply Finset.prod_congr rfl
  intro mu _hmu
  rw [S.twist_factor, data.twistData_character,
    data.twistData_character]
  simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
    ContinuousQuasiChar.one_apply, one_mul]
  rfl

include ht hres pi hpi hgen

theorem numerator_eq_denominator
    {gammaF : Fˣ} {alpha1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm)
    (S : HighOddAdmissibleShape data gammaF alpha1 D) :
    D.admissibleNumerator = D.admissibleDenominator := by
  rw [S.numerator_eq_explicit, S.denominator_eq_explicit,
    extension_balance data hchiArg gammaF,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hcard : Fintype.card (NormCharacter F K) = Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card]
    exact ramifiedNormCharacter_card F K ht hres pi hpi hgen
  rw [hcard]
  ring

theorem factor_eq_one
    {gammaF : Fˣ} {alpha1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm)
    (S : HighOddAdmissibleShape data gammaF alpha1 D) :
    D.factors.admissibleCharacter = 1 := by
  rw [FirstMainPhaseData.factors,
    numerator_eq_denominator data ht hres pi hpi hgen hchiArg S]
  exact div_self D.admissibleDenominator_ne_zero

end HighOddAdmissibleShape

/-! Low-range admissible-character cancellation from the literal table
gammas. -/

/-- The five literal low-row gamma evaluations.  Identity and nonidentity
twists are separate because the table gives them different denominators. -/
structure LowOddAdmissibleShape
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (delta : Fˣ) (epsilon1 : Kˣ)
    (D : FirstMainPhaseData F K globalChi globalPsi data) : Prop where
  extension_factor : D.extension.admissibleFactor =
    (data.extensionQuasiChar.character
      (lowGammaK F K delta epsilon1) : ℂ)
  identity_norm_factor : (D.normCharacter 1).admissibleFactor = 1
  nonidentity_norm_factor : ∀ mu, mu ≠ 1 →
    (D.normCharacter mu).admissibleFactor =
      (data.normCharacterData mu).character delta
  identity_twist_factor : (D.twist 1).admissibleFactor =
    (data.twistData 1).character (lowGammaF F K delta epsilon1)
  nonidentity_twist_factor : ∀ mu, mu ≠ 1 →
    (D.twist mu).admissibleFactor = (data.twistData mu).character delta

private theorem low_extension_gamma_character_balance
    {F K : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
    (data : FirstMainComputationalData F K globalChi globalPsi)
    (hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm)
    (delta : Fˣ) (epsilon1 : Kˣ) :
    (data.extensionQuasiChar.character
        (lowGammaK F K delta epsilon1) : ℂ) =
      ((data.twistData 1).character
          (lowGammaF F K delta epsilon1) : ℂ) *
        ((data.twistData 1).character delta : ℂ) ^
          (Module.finrank F K - 1) := by
  have hnormMap :
      normUnits F K (Units.map (algebraMap F K) delta) =
        delta ^ Module.finrank F K := by
    ext
    simp [coe_normUnits, norm_algebraMap]
  have hp : Module.finrank F K - 1 + 1 = Module.finrank F K :=
    Nat.sub_add_cancel Module.finrank_pos
  rw [hchiArg, ContinuousQuasiChar.compNorm_apply, lowGammaK, map_div,
    hnormMap, lowGammaF, lowEpsilon, map_div, map_div, map_pow]
  rw [← hp, pow_add, pow_one]
  push_cast
  ring

private theorem prod_identity_else_mul
    {I : Type*} [Fintype I] [DecidableEq I] [One I]
    (f : I → ℂ) (b c : ℂ) (hf : f 1 = 1) :
    (∏ i : I, if i = 1 then b else f i * c) =
      b * (∏ i : I, f i) * c ^ (Fintype.card I - 1) := by
  let S : Finset I := Finset.univ
  have hone : (1 : I) ∈ S := Finset.mem_univ _
  calc
    (∏ i : I, if i = 1 then b else f i * c) =
        (if (1 : I) = 1 then b else f 1 * c) *
          ∏ i ∈ S.erase 1, if i = 1 then b else f i * c := by
      exact (Finset.mul_prod_erase S
        (fun i ↦ if i = 1 then b else f i * c) hone).symm
    _ = b * ∏ i ∈ S.erase 1, f i * c := by
      rw [if_pos rfl]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1]
    _ = b * ((∏ i ∈ S.erase 1, f i) *
        ∏ _i ∈ S.erase 1, c) := by
      rw [Finset.prod_mul_distrib]
    _ = b * (∏ i : I, f i) * c ^ (Fintype.card I - 1) := by
      have hfprod : ∏ i ∈ S.erase 1, f i = ∏ i : I, f i := by
        rw [← Finset.mul_prod_erase S f hone, hf, one_mul]
      rw [hfprod, Finset.prod_const, Finset.card_erase_of_mem hone]
      simp only [S, Finset.card_univ]
      ring

namespace LowOddAdmissibleShape

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  {t : ℕ}
  (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

local instance : Fintype (NormCharacter F K) :=
  Fintype.ofFinite (NormCharacter F K)

local instance : DecidableEq (NormCharacter F K) := Classical.decEq _

theorem numerator_eq_explicit
    {delta : Fˣ} {epsilon1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (S : LowOddAdmissibleShape data delta epsilon1 D) :
    D.admissibleNumerator =
      (data.extensionQuasiChar.character
        (lowGammaK F K delta epsilon1) : ℂ) *
        ∏ mu : NormCharacter F K, (mu.1 delta : ℂ) := by
  rw [FirstMainPhaseData.admissibleNumerator, S.extension_factor]
  congr 1
  apply Finset.prod_congr rfl
  intro mu _hmu
  by_cases hmu : mu = 1
  · subst mu
    rw [S.identity_norm_factor]
    simp
  · rw [S.nonidentity_norm_factor mu hmu,
      data.normCharacterData_character]

theorem denominator_eq_explicit
    {delta : Fˣ} {epsilon1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (S : LowOddAdmissibleShape data delta epsilon1 D) :
    D.admissibleDenominator =
      ∏ mu : NormCharacter F K,
        if mu = 1 then
          ((data.twistData 1).character
            (lowGammaF F K delta epsilon1) : ℂ)
        else
          (mu.1 delta : ℂ) *
            ((data.twistData 1).character delta : ℂ) := by
  rw [FirstMainPhaseData.admissibleDenominator]
  apply Finset.prod_congr rfl
  intro mu _hmu
  by_cases hmu : mu = 1
  · subst mu
    rw [if_pos rfl, S.identity_twist_factor]
  · rw [if_neg hmu, S.nonidentity_twist_factor mu hmu,
      data.twistData_character, data.twistData_character]
    simp only [ContinuousQuasiChar.mul_apply, NormCharacter.coe_one,
      ContinuousQuasiChar.one_apply, one_mul]
    rfl

include ht hres pi hpi hgen

theorem numerator_eq_denominator
    {delta : Fˣ} {epsilon1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm)
    (S : LowOddAdmissibleShape data delta epsilon1 D) :
    D.admissibleNumerator = D.admissibleDenominator := by
  rw [S.numerator_eq_explicit, S.denominator_eq_explicit]
  let f : NormCharacter F K → ℂ := fun mu ↦ (mu.1 delta : ℂ)
  let b : ℂ := ((data.twistData 1).character
    (lowGammaF F K delta epsilon1) : ℂ)
  let c : ℂ := ((data.twistData 1).character delta : ℂ)
  have hf : f 1 = 1 := by simp [f]
  rw [prod_identity_else_mul f b c hf]
  have hcard : Fintype.card (NormCharacter F K) = Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card]
    exact ramifiedNormCharacter_card F K ht hres pi hpi hgen
  rw [hcard]
  rw [low_extension_gamma_character_balance data hchiArg delta epsilon1]
  dsimp only [f, b, c]
  ring

theorem factor_eq_one
    {delta : Fˣ} {epsilon1 : Kˣ}
    {D : FirstMainPhaseData F K globalChi globalPsi data}
    (hchiArg : data.extensionQuasiChar.character =
      (data.twistData 1).character.compNorm)
    (S : LowOddAdmissibleShape data delta epsilon1 D) :
    D.factors.admissibleCharacter = 1 := by
  rw [FirstMainPhaseData.factors,
    numerator_eq_denominator data ht hres pi hpi hgen hchiArg S]
  exact div_self D.admissibleDenominator_ne_zero

end LowOddAdmissibleShape

end

end LanglandsFirstMainLemma
