import LanglandsFirstMainLemma.Parameters.HighIntermediate
import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Parameters.NormPolynomial

/-!
# High stationary-class norm products

The norm in this file is applied only to an honest unit-filtration quotient.
In particular, an additive stationary-coefficient quotient is first accompanied
by a supplied unit representative; no operation on an arbitrary additive
quotient representative is defined.  The source and target ambiguity depths
are exactly the floor depths `dK` and `dF` in the relevant stationary conductor
decompositions.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

open Polynomial

set_option maxHeartbeats 4000000

/-! ## The representative-free product interface -/

/-- A quotient-level norm product.  The norm map is the one induced by the
`ambiguity_inclusion` field of the supplied `NormPolynomialPrecision`
certificate, hence has exactly source denominator `U_K^dK` and target
denominator `U_F^dF`. -/
structure HighStationaryNormProduct
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (precision : NormPolynomialPrecision F K mK dK epsilonK
      mF dF epsilonF)
    (ι : Type*) [Fintype ι] where
  upstairs : unitFiltration K 0
  factors : ι → unitFiltration F 0
  norm_eq_product :
    normPolynomialStationaryNormClass F K precision
        (unitFiltrationQuotientMk K (Nat.zero_le dK) upstairs) =
      ∏ i, unitFiltrationQuotientMk F (Nat.zero_le dF) (factors i)

namespace HighStationaryNormProduct

variable {F K : Type*}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  {mK dK epsilonK mF dF epsilonF : ℕ}
  {precision : NormPolynomialPrecision F K mK dK epsilonK
    mF dF epsilonF}
  {ι : Type*} [Fintype ι]

/-- Field-level reading of `norm_eq_product`: it is an additive congruence at
exactly depth `dF`, not an equality in `F`. -/
theorem congruentAtTarget
    (P : HighStationaryNormProduct F K precision ι) :
    CongruentAtDepth (dF : ℤ)
      ((normUnits F K (P.upstairs : Kˣ) : Fˣ) : F)
      ((((∏ i, P.factors i : unitFiltration F 0) : Fˣ) : F)) := by
  have h := P.norm_eq_product
  rw [normPolynomialStationaryNormClass, stationaryNormClass_mk] at h
  rw [← map_prod] at h
  exact (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
    (Nat.zero_le dF) _ _).1 h

/-- Changing the upstairs unit representative within its allowed stationary
ambiguity does not change the product class. -/
theorem upstairs_representative_independent
    (P : HighStationaryNormProduct F K precision ι)
    (u : unitFiltration K 0)
    (hu : CongruentAtDepth (dK : ℤ)
      (((u : Kˣ) : K)) (((P.upstairs : Kˣ) : K))) :
    normPolynomialStationaryNormClass F K precision
        (unitFiltrationQuotientMk K (Nat.zero_le dK) u) =
      ∏ i, unitFiltrationQuotientMk F (Nat.zero_le dF) (P.factors i) := by
  have hmk :
      unitFiltrationQuotientMk K (Nat.zero_le dK) u =
        unitFiltrationQuotientMk K (Nat.zero_le dK) P.upstairs :=
    (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth K
      (Nat.zero_le dK) _ _).2 hu
  rw [hmk]
  exact P.norm_eq_product

/-- Every factor may independently be replaced by a representative of the
same depth-`dF` quotient class. -/
theorem factors_representative_independent
    (P : HighStationaryNormProduct F K precision ι)
    (f : ι → unitFiltration F 0)
    (hf : ∀ i, CongruentAtDepth (dF : ℤ)
      ((((f i : unitFiltration F 0) : Fˣ) : F))
      ((((P.factors i : unitFiltration F 0) : Fˣ) : F))) :
    ∏ i, unitFiltrationQuotientMk F (Nat.zero_le dF) (f i) =
      ∏ i, unitFiltrationQuotientMk F (Nat.zero_le dF) (P.factors i) := by
  apply Finset.prod_congr rfl
  intro i _
  exact (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
    (Nat.zero_le dF) _ _).2 (hf i)

end HighStationaryNormProduct

/-- Construct the high-product class from an exact depth-`dF` congruence.
This is the public quotient descent used by both high-conductor branches.
It invokes only the norm map certified by the supplied precision certificate. -/
theorem highStationaryNormProduct_of_congruence
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (precision : NormPolynomialPrecision F K mK dK epsilonK
      mF dF epsilonF)
    (ι : Type*) [Fintype ι]
    (upstairs : unitFiltration K 0)
    (factors : ι → unitFiltration F 0)
    (hproduct : CongruentAtDepth (dF : ℤ)
      ((normUnits F K (upstairs : Kˣ) : Fˣ) : F)
      (((∏ i, factors i : unitFiltration F 0) : Fˣ) : F)) :
    Nonempty (HighStationaryNormProduct F K precision ι) := by
  refine ⟨⟨upstairs, factors, ?_⟩⟩
  rw [normPolynomialStationaryNormClass, stationaryNormClass_mk, ← map_prod]
  exact (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
    (Nat.zero_le dF) _ _).2 hproduct

/-! ## Helpers for supplied stationary representatives -/

/-- A supplied representative of a stationary coefficient quotient has
order zero.  This extracts a property from an already supplied representative
and does not choose a canonical representative. -/
theorem stationaryCoefficientClass_suppliedRepresentative_ord
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {d epsilon : ℕ}
    {h : IsStationaryConductorDecomposition chi.conductor d epsilon}
    {gamma : Eˣ}
    {hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)}
    {c : lattice E 0}
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

/-- The underlying field value of an element of `U_E^0` is integral. -/
private theorem unitFiltrationZero_coe_mem_lattice
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (u : unitFiltration E 0) :
    (((u : unitFiltration E 0) : Eˣ) : E) ∈ lattice E 0 := by
  rw [mem_lattice]
  have hu := (mem_unitFiltration_zero E (u : Eˣ)).1 u.property
  rw [hu]
  simp

/-! ## Odd intermediate branch package -/

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

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

/-- The selected odd-prime representatives together with the actual
stationary additive quotient classes and their norm product in
`U_F^0/U_F^d`.  All representatives are existential fields of this package. -/
structure OddIntermediateHighProductData
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
  precision : NormPolynomialPrecision F K chiK.conductor dK epsilonK
    chiF.conductor d epsilon
  alpha : Fˣ
  beta : Fˣ
  alpha1 : Kˣ
  beta1 : Kˣ
  alpha_choice : IsSubcriticalNormRepresentative F K
    ((chiF.conductor : ℤ) - ((t + 1 : ℕ) : ℤ)) ((t + 1) / 2)
      alpha alpha1
  beta_choice : IsSubcriticalNormRepresentative F K 0 d beta beta1
  quotientProduct : HighStationaryNormProduct F K precision
    (ZMod (Module.finrank F K))
  upstairs_formula :
    (((quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K) =
      algebraMap F K (norm F K (beta1 : K)) -
        (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
          (alpha1 : K)
  upstairs_class : latticeQuotientMk K (Int.natCast_nonneg dK)
      (⟨(((quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K),
        unitFiltrationZero_coe_mem_lattice K quotientProduct.upstairs⟩ :
          lattice K 0) =
    stationaryCoefficientClass K chiK psiK hK
      (Units.map (algebraMap F K) gammaF)
      (highParameter_intermediate_commonDenominator
        F K ht hres pi hpi hgen chiF chiK psiF psiK hminimal hchi hpsi
          hlower gammaF hgammaF)
  factorDecomposition : ∀ j : ZMod (Module.finrank F K),
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    IsStationaryConductorDecomposition twist.conductor d epsilon
  factorDenominator : ∀ j : ZMod (Module.finrank F K),
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    ord F (gammaF : F) =
      (((twist.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)
  factor_formula : ∀ j : ZMod (Module.finrank F K),
    let hchar := residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
    (((quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F) =
      norm F K ((beta1 : K) +
        algebraMap F K
          (highIntermediateTeichmullerScalar F (Module.finrank F K)
            hchar j) * (alpha1 : K))
  factor_linear_congruence : ∀ j : ZMod (Module.finrank F K),
    let hchar := residueCharacteristic_eq_degree_of_positive_break
      F K ht htpos pi hpi hgen
    CongruentAtDepth (d : ℤ)
      (((quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F)
      (norm F K (beta1 : K) +
        highIntermediateTeichmullerScalar F (Module.finrank F K)
          hchar j * norm F K (alpha1 : K))
  factor_class : ∀ j : ZMod (Module.finrank F K),
    let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
      (Multiplicative.ofAdd j)
    let twist := ramifiedNormCharacterOrbitTwistData
      F K ht hres pi hpi hgen chiF mu
    latticeQuotientMk F (Int.natCast_nonneg d)
        (⟨(((quotientProduct.factors j : unitFiltration F 0) : Fˣ) : F),
          unitFiltrationZero_coe_mem_lattice F (quotientProduct.factors j)⟩ :
            lattice F 0) =
      stationaryCoefficientClass F twist psiF (factorDecomposition j)
        gammaF (factorDenominator j)
  closed_product_congruence :
    CongruentAtDepth (d : ℤ)
      ((normUnits F K (quotientProduct.upstairs : Kˣ) : Fˣ) : F)
      (norm F K (beta1 : K) ^ Module.finrank F K -
        norm F K (beta1 : K) *
          norm F K (alpha1 : K) ^ (Module.finrank F K - 1))

/-! ## Odd-prime computations -/

/-- The mixed-characteristic Teichmüller factorization used by the lower
twists.  It is an exact polynomial identity for the supplied Teichmüller
scalars; it does not turn any stationary quotient class into a canonical
field element. -/
private theorem highProduct_prod_teichmuller
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
  let lam : ZMod p → F :=
    fun j => highIntermediateTeichmullerScalar F p hchar j
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

/-- The odd-prime norm computation for the normalized upstairs
representative.  The conclusion is membership in the exact target lattice
`p_F^d`, never an equality in `F`. -/
theorem highParameter_intermediate_norm_product_congruent
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [IsGalois F K]
    (p T m d epsilon : ℕ)
    (hp : p.Prime) (hodd : Odd p) (hT : 2 ≤ T)
    (hchar : residueCharacteristic F = p)
    (hdegree : Module.finrank F K = p)
    (hres : residueDegree F K = 1)
    (hram : ramificationIndex F K = p)
    (htrace : TraceIdealLowerBound F K p
      (((p - 1) * T : ℕ) : ℤ))
    (hF : IsStationaryConductorDecomposition m d epsilon)
    (hlower : T ≤ m)
    (alpha1 beta1 : Kˣ)
    (halpha1 : ord K (alpha1 : K) =
      ((((m - T : ℕ) : ℤ) : WithTop ℤ)))
    (hbeta1 : ord K (beta1 : K) = (0 : WithTop ℤ)) :
    norm F K
          (algebraMap F K (norm F K (beta1 : K)) -
            (beta1 : K) * algebraMap F K (norm F K (alpha1 : K)) /
              (alpha1 : K)) -
        (norm F K (beta1 : K) ^ p -
          norm F K (beta1 : K) * norm F K (alpha1 : K) ^ (p - 1)) ∈
      lattice F (d : ℤ) := by
  let A : F := norm F K (alpha1 : K)
  let B : F := norm F K (beta1 : K)
  let x : K :=
    -(beta1 : K) * algebraMap F K A /
      ((alpha1 : K) * algebraMap F K B)
  have hAord : ord F A =
      ((((m - T : ℕ) : ℤ) : WithTop ℤ)) := by
    dsimp only [A]
    rw [ord_norm, halpha1, hres]
    simp
  have hBord : ord F B = (0 : WithTop ℤ) := by
    dsimp only [B]
    rw [ord_norm, hbeta1]
    simp
  have hA0 : A ≠ 0 := by
    dsimp only [A]
    exact (Algebra.norm_ne_zero_iff).2 (Units.ne_zero alpha1)
  have hB0 : B ≠ 0 := by
    dsimp only [B]
    exact (Algebra.norm_ne_zero_iff).2 (Units.ne_zero beta1)
  have hxord : ord K x =
      (((p - 1) * (m - T) : ℕ) : ℤ) := by
    dsimp only [x]
    rw [ord_div, ord_mul, ord_neg, hbeta1, ord_algebraMap, hAord,
      ord_mul, halpha1, ord_algebraMap, hBord]
    rw [hram]
    simp only [zero_add, nsmul_zero, add_zero]
    rw [← WithTop.coe_nsmul]
    change ((((p : ℤ) * ((m - T : ℕ) : ℤ) : ℤ)) : WithTop ℤ) -
        ((((m - T : ℕ) : ℤ)) : WithTop ℤ) =
      (((((p - 1) * (m - T) : ℕ) : ℤ)) : WithTop ℤ)
    change (((p : ℤ) * ((m - T : ℕ) : ℤ) -
        ((m - T : ℕ) : ℤ) : ℤ) : WithTop ℤ) =
      (((((p - 1) * (m - T) : ℕ) : ℤ)) : WithTop ℤ)
    congr 1
    push_cast
    rw [Nat.cast_sub hp.one_le]
    ring
  have hxordLower :
      ((((p - 1) * (m - T) : ℕ) : ℤ) : WithTop ℤ) ≤ ord K x :=
    hxord.ge
  let mid : F := ∑ k ∈ Finset.range (p - 1),
    elementarySymmetric F K (k + 1) x
  have hcross : ∀ i : ℕ, 1 ≤ i → i < p →
      p * d ≤ i * ((p - 1) * (m - T)) + (p - 1) * T := by
    intro i hi hip
    have hm : m = 2 * d + epsilon := hF.conductor_eq
    have hpTwo : 2 ≤ p := hp.two_le
    have himul : (p - 1) * (m - T) ≤
        i * ((p - 1) * (m - T)) := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right ((p - 1) * (m - T)) hi
    have hbase : p * d ≤
        (p - 1) * (m - T) + (p - 1) * T := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hlower]
      calc
        p * d ≤ (2 * (p - 1)) * d :=
          Nat.mul_le_mul_right d (by omega)
        _ = (p - 1) * (2 * d) := by ring
        _ ≤ (p - 1) * m :=
          Nat.mul_le_mul_left (p - 1) (by rw [hm]; omega)
    omega
  have hmid : mid ∈ lattice F (d : ℤ) := by
    dsimp only [mid]
    apply Submodule.sum_mem
    intro k hk
    have hklt : k < p - 1 := Finset.mem_range.1 hk
    have hkp : k + 1 < p := by omega
    have hbound := wild_elementarySymmetric_bound F K p T
      (((p - 1) * (m - T) : ℕ) : ℤ)
      hp hT hchar hdegree htrace hxordLower
      (j := k + 1) (by omega) hkp
    rw [mem_lattice]
    apply (WithTop.coe_le_coe.mpr ?_).trans hbound
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
    have hnat := hcross (k + 1) (by omega) hkp
    simpa [mul_comm, mul_left_comm, mul_assoc] using (show
      (p * d : ℤ) ≤
        ((k + 1) * ((p - 1) * (m - T)) + (p - 1) * T : ℕ) by
          exact_mod_cast hnat)
  have hBpowMem : B ^ p ∈ lattice F 0 := by
    rw [mem_lattice, ord_pow, hBord]
    simp
  have hscaledMid : B ^ p * mid ∈ lattice F (d : ℤ) := by
    simpa [add_comm] using mul_mem_lattice F hBpowMem hmid
  have hnormNeg (y : K) : norm F K (-y) = -norm F K y := by
    rw [show -y = algebraMap F K (-1 : F) * y by simp,
      map_mul, norm_algebraMap, hdegree, hodd.neg_one_pow, neg_one_mul]
  have hterminal :
      B ^ p * elementarySymmetric F K p x = -B * A ^ (p - 1) := by
    rw [← hdegree, elementarySymmetric_finrank]
    dsimp only [x]
    rw [div_eq_mul_inv, map_mul, map_mul, Algebra.norm_inv,
      hnormNeg, norm_algebraMap, hdegree, map_mul,
      norm_algebraMap, hdegree]
    dsimp only [A, B]
    field_simp [hA0, hB0]
    have hpow : A ^ p = A * A ^ (p - 1) := by
      conv_lhs => rw [show p = (p - 1) + 1 from
        (Nat.sub_add_cancel hp.one_le).symm, pow_succ']
    simpa only [A] using congrArg Neg.neg hpow
  have hfactor :
      algebraMap F K B - (beta1 : K) * algebraMap F K A / (alpha1 : K) =
        algebraMap F K B * (1 + x) := by
    dsimp only [x]
    field_simp [hB0]
    ring
  have hpSucc : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
  have hexpand :
      norm F K
          (algebraMap F K B -
            (beta1 : K) * algebraMap F K A / (alpha1 : K)) -
        (B ^ p - B * A ^ (p - 1)) = B ^ p * mid := by
    rw [hfactor, map_mul, norm_algebraMap, hdegree,
      norm_one_add_eq_one_add_sum_elementarySymmetric]
    rw [hdegree, hpSucc, Finset.sum_range_succ]
    have hlast : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    rw [hlast]
    change B ^ p * (1 + (mid + elementarySymmetric F K p x)) -
        (B ^ p - B * A ^ (p - 1)) = B ^ p * mid
    calc
      _ = B ^ p * mid +
          (B ^ p * elementarySymmetric F K p x +
            B * A ^ (p - 1)) := by ring
      _ = B ^ p * mid := by rw [hterminal]; ring
  change norm F K
        (algebraMap F K B -
          (beta1 : K) * algebraMap F K A / (alpha1 : K)) -
      (B ^ p - B * A ^ (p - 1)) ∈ lattice F (d : ℤ)
  rw [hexpand]
  exact hscaledMid

/-! ## Odd intermediate branch -/

set_option maxHeartbeats 16000000 in
/-- Proposition `prop:high-parameter-table`, part (c), in norm-product form.
The source coefficient is the actual upstairs stationary quotient class, every
factor is the actual stationary class of its indexed lower twist, and norm is
applied only after all of them have been wrapped as depth-zero units. -/
theorem highParameter_product_intermediate
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
    Nonempty (OddIntermediateHighProductData
      F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hminimal
        hchi hpsi hodd htpos hlower hupper gammaF hgammaF) := by
  obtain ⟨_hconductor, _htwistsConductor, hparameters⟩ :=
    highParameter_intermediate F K ht hres pi hpi hgen
      chiF chiK psiF psiK hF hK hminimal hchi hpsi hodd htpos
        hlower hupper gammaF hgammaF
  obtain ⟨precision, hchoices⟩ := hparameters
  dsimp only at hchoices
  obtain ⟨a, b, alpha, beta, alpha1, beta1, hacoe, hbcoe,
    halpha1, hbeta1, ha, hb, _hconversion, hcandidatePack⟩ := hchoices
  obtain ⟨hcandidate, hcandidateData⟩ := hcandidatePack
  obtain ⟨_hadjoint, hupstairs, htwists⟩ := hcandidateData
  choose hJ hgammaJ hlinearMem hnormMem hnormLinear hnormClass using htwists
  let p : ℕ := Module.finrank F K
  let T : ℕ := t + 1
  let v : ℕ := chiF.conductor - T
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
      stationaryCoefficientClass_suppliedRepresentative_ord
        K hcandidateClass
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
  have hproductExact := highProduct_prod_teichmuller F p hp hodd hchar
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
        ∏ j, unitFiltrationQuotientMk F (Nat.zero_le d) (linearFactors j) := by
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
  let P : HighStationaryNormProduct F K precision (ZMod p) :=
    ⟨upstairs, factors, hnormEq⟩
  refine ⟨⟨precision, alpha, beta, alpha1, beta1, halpha1, hbeta1,
    P, ?_, ?_, hJ, hgammaJ, ?_, ?_, ?_, ?_⟩⟩
  · rfl
  · simpa only [P, upstairs, candidateUnit, Units.val_mk0,
      candidateLattice, candidate] using hcandidateClass
  · intro j
    rfl
  · intro j
    simpa only [P, factors, factorUnit, Units.val_mk0, lower, lam] using
      hfactorCongruent j
  · intro j
    simpa only [P, factors, factorUnit, Units.val_mk0] using hlowerClass j
  · simpa only [P, p] using hclosed

/-! ## Wild quadratic branch -/

/-- The two lower factors in the wild quadratic branch, with `true` ordered
before `false`.  The package retains the complete simultaneous choice from
`HighQuadratic`, including its essential break-level unit `delta`. -/
structure WildQuadraticHighProductData
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
  parameters : WildQuadraticHighParameterData
    F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF
  quotientProduct : HighStationaryNormProduct F K parameters.precision Bool
  upstairs_formula :
    (((quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K) =
      parameters.representatives.betaK
  upstairs_class : latticeQuotientMk K (Int.natCast_nonneg dK)
      (⟨(((quotientProduct.upstairs : unitFiltration K 0) : Kˣ) : K),
        unitFiltrationZero_coe_mem_lattice K quotientProduct.upstairs⟩ :
          lattice K 0) =
    stationaryCoefficientClass K chiK psiK hK
      (Units.map (algebraMap F K) gammaF) parameters.commonDenominator
  beta_factor_formula :
    (((quotientProduct.factors true : unitFiltration F 0) : Fˣ) : F) =
      (parameters.representatives.beta : F)
  beta_factor_class : latticeQuotientMk F (Int.natCast_nonneg d)
      (⟨(((quotientProduct.factors true : unitFiltration F 0) : Fˣ) : F),
        unitFiltrationZero_coe_mem_lattice F
          (quotientProduct.factors true)⟩ : lattice F 0) =
    stationaryCoefficientClass F chiF psiF hF gammaF hgammaF
  twist_factor_formula :
    (((quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) =
      parameters.representatives.betaTwist
  twist_factor_class :
    let hTw := wildQuadraticHighTwistDecomposition
      F K ht hres pi hpi hgen chiF hF hminimal hhigh tau htau
    let hgammaTw := highParameter_wildQuadratic_twistDenominator
      F K ht hres pi hpi hgen chiF psiF hminimal hhigh tau htau
        gammaF hgammaF
    latticeQuotientMk F (Int.natCast_nonneg d)
        (⟨(((quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F),
          unitFiltrationZero_coe_mem_lattice F
            (quotientProduct.factors false)⟩ : lattice F 0) =
      stationaryCoefficientClass F
        (wildQuadraticHighTwistData F K ht hres pi hpi hgen chiF tau)
        psiF hTw gammaF hgammaTw
  break_unit_relation : parameters.representatives.beta =
    (parameters.representatives.delta : Fˣ) *
      normUnits F K parameters.representatives.beta1
  correction_unit_retained :
    (((quotientProduct.factors false : unitFiltration F 0) : Fˣ) : F) =
      (parameters.representatives.beta : F) +
        (((normUnits F K parameters.representatives.alpha1) *
          (parameters.representatives.delta : Fˣ) : Fˣ) : F)
  ordered_factor_product :
    ((((∏ b, quotientProduct.factors b : unitFiltration F 0) : Fˣ) : F)) =
      (parameters.representatives.beta : F) *
        parameters.representatives.betaTwist
  product_congruence : CongruentAtDepth (d : ℤ)
    ((normUnits F K (quotientProduct.upstairs : Kˣ) : Fˣ) : F)
    ((parameters.representatives.beta : F) *
      parameters.representatives.betaTwist)

/-- Proposition `prop:high-parameter-table`, wild quadratic norm-product
branch.  The lower factors are ordered as the original coefficient and its
nontrivial twist; the latter is exactly `beta + N(alpha1) * delta`. -/
theorem highParameter_product_wildQuadratic
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
    Nonempty (WildQuadraticHighProductData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
        hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF) := by
  obtain ⟨D⟩ := highParameter_wildQuadratic
    F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
      hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF
  let R := D.representatives
  have hbetaKOrd : ord K R.betaK = 0 := by
    let betaKLattice : lattice K 0 :=
      ⟨R.betaK, R.betaK_integral hdegree⟩
    simpa only [betaKLattice] using
      stationaryCoefficientClass_suppliedRepresentative_ord K D.upstairs_class
  have hbetaKNe : R.betaK ≠ 0 := by
    apply (ord_ne_top_iff K).1
    rw [hbetaKOrd]
    simp
  let betaKUnit : Kˣ := Units.mk0 R.betaK hbetaKNe
  let upstairs : unitFiltration K 0 := ⟨betaKUnit, by
    exact (mem_unitFiltration_zero K betaKUnit).2 (by
      simpa only [betaKUnit, Units.val_mk0] using hbetaKOrd)⟩
  let betaFactor : unitFiltration F 0 := ⟨R.beta, by
    exact (mem_unitFiltration_zero F R.beta).2 R.beta_order⟩
  have htwistOrd : ord F R.betaTwist = 0 := by
    let twistLattice : lattice F 0 := ⟨R.betaTwist, R.betaTwist_integral⟩
    simpa only [twistLattice] using
      stationaryCoefficientClass_suppliedRepresentative_ord F D.twist_class
  have htwistNe : R.betaTwist ≠ 0 := by
    apply (ord_ne_top_iff F).1
    rw [htwistOrd]
    simp
  let twistUnit : Fˣ := Units.mk0 R.betaTwist htwistNe
  let twistFactor : unitFiltration F 0 := ⟨twistUnit, by
    exact (mem_unitFiltration_zero F twistUnit).2 (by
      simpa only [twistUnit, Units.val_mk0] using htwistOrd)⟩
  let factors : Bool → unitFiltration F 0 := fun b ↦
    if b then betaFactor else twistFactor
  have hfactorTrue : factors true = betaFactor := by rfl
  have hfactorFalse : factors false = twistFactor := by rfl
  have hordered :
      ((((∏ b, factors b : unitFiltration F 0) : Fˣ) : F)) =
        (R.beta : F) * R.betaTwist := by
    change (Units.coeHom F)
      ((unitFiltration F 0).subtype (∏ b, factors b)) = _
    rw [map_prod, map_prod, Fintype.prod_bool]
    rfl
  have hcongruent : CongruentAtDepth (d : ℤ)
      ((normUnits F K (upstairs : Kˣ) : Fˣ) : F)
      ((((∏ b, factors b : unitFiltration F 0) : Fˣ) : F)) := by
    rw [congruentAtDepth_iff_sub_mem_lattice, hordered]
    simpa only [upstairs, betaKUnit, Units.val_mk0, coe_normUnits] using
      R.norm_betaK_sub_product_mem hdegree
  have hnormEq :
      normPolynomialStationaryNormClass F K D.precision
          (unitFiltrationQuotientMk K (Nat.zero_le dK) upstairs) =
        ∏ b, unitFiltrationQuotientMk F (Nat.zero_le d) (factors b) := by
    rw [normPolynomialStationaryNormClass, stationaryNormClass_mk, ← map_prod]
    exact (unitFiltrationQuotientMk_eq_mk_iff_congruentAtDepth F
      (Nat.zero_le d) _ _).2 hcongruent
  let P : HighStationaryNormProduct F K D.precision Bool :=
    ⟨upstairs, factors, hnormEq⟩
  refine ⟨⟨D, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rfl
  · simpa only [P, upstairs, betaKUnit, Units.val_mk0, R] using
      D.upstairs_class
  · rfl
  · simpa only [P, factors, if_true, betaFactor, R] using R.beta_class
  · rfl
  · simpa only [P, factors,
      if_neg Bool.false_eq_true_eq_False,
      twistFactor, twistUnit, Units.val_mk0, R] using D.twist_class
  · exact R.beta_factor
  · simp only [P, factors, twistFactor, twistUnit,
      WildQuadraticHighRepresentatives.betaTwist,
      WildQuadraticHighRepresentatives.cF,
      WildQuadraticHighRepresentatives.alpha, R]
    rfl
  · simpa only [P] using hordered
  · rw [← hordered]
    exact hcongruent

/-! ## Principal two-branch interface -/

/-- The high norm-product statement has two genuinely different formulas.
This proposition keeps the odd intermediate and wild quadratic conclusions
as separate universally quantified fields rather than hiding their different
indexing sets or correction terms behind a common field-level equation. -/
structure HighProductBranch : Prop where
  oddIntermediate : ∀
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
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    Nonempty (OddIntermediateHighProductData
      F K ht hres pi hpi hgen chiF chiK psiF psiK hF hK hminimal
        hchi hpsi hodd htpos hlower hupper gammaF hgammaF)
  wildQuadratic : ∀
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
        (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)),
    Nonempty (WildQuadraticHighProductData
      F K ht hres pi hpi hgen hdegree htpos chiF chiK psiF psiK
        hF hK hminimal hhigh hchi hpsi tau htau gammaF hgammaF)

/-- **High stationary-class norm product.**  This is the principal exported
declaration for `mod:parameters-highproduct`; its two fields are proved by
the completed odd-intermediate and wild-quadratic parameter theorems. -/
theorem highParameter_product :
    HighProductBranch F K ht hres pi hpi hgen := by
  refine ⟨?_, ?_⟩
  · exact highParameter_product_intermediate F K ht hres pi hpi hgen
  · exact highParameter_product_wildQuadratic F K ht hres pi hpi hgen

end

end LanglandsFirstMainLemma
