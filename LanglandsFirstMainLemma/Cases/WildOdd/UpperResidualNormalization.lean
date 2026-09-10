import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsFirstMainLemma.Parameters.PhaseReduction

namespace LanglandsFirstMainLemma

noncomputable section

theorem scaledAddChar_eq_of_sub_mem_lattice
    (F : Type*) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (psi : LocalAddCharData F) (A : Fˣ) (T : ℕ)
    (hA : ord F (A : F) =
      (-((T : ℤ) + psi.conductor) : WithTop ℤ))
    {x y : F} (hxy : x - y ∈ lattice F (T : ℤ)) :
    (psi.character ((A : F) * x) : ℂ) =
      (psi.character ((A : F) * y) : ℂ) := by
  have hAmem : (A : F) ∈ lattice F (-((T : ℤ) + psi.conductor)) := by
    rw [mem_lattice, hA]
    simp
  have hscaled : (A : F) * (x - y) ∈ lattice F (-psi.conductor) := by
    have := mul_mem_lattice F hAmem hxy
    convert this using 1
    all_goals ring_nf
  have htriv := psi.isConductor.trivial _ hscaled
  have hadd := ContinuousAddChar.map_add_eq_mul psi.character
    ((A : F) * (x - y)) ((A : F) * y)
  have hsum : (A : F) * (x - y) + (A : F) * y = (A : F) * x := by ring
  rw [hsum, htriv, one_mul] at hadd
  exact congrArg (Units.val : ℂˣ → ℂ) hadd

/-! ## The last break layer and its exact Frobenius direction -/
/-- The denominator which turns the exact norm coefficient into the last
lower residual additive character. -/
def wildOddUpperGammaZero
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (S : PhaseReductionResidualCoordinateSource F K)
    (A : Fˣ) (t : ℕ) : Fˣ :=
  (A * S.lowerUniformizer ^ t)⁻¹
theorem wildOddUpperGammaZero_order
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (S : PhaseReductionResidualCoordinateSource F K)
    (psi : LocalAddCharData F) (A : Fˣ) (t : ℕ)
    (hA : ord F (A : F) =
      (-(((t + 1 : ℕ) : ℤ) + psi.conductor) : WithTop ℤ)) :
    ord F (wildOddUpperGammaZero S A t : F) =
      ((psi.conductor + 1 : ℤ) : WithTop ℤ) := by
  rw [wildOddUpperGammaZero]
  simp only [Units.val_inv_eq_inv_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  change ord F (((A : F) * (S.lowerUniformizer : F) ^ t)⁻¹) = _
  rw [ord_inv, ord_mul, ord_pow, hA, S.lower_order]
  norm_num [nsmul_eq_mul]
  change -(((t : ℤ) : WithTop ℤ)) +
      (((t : ℤ) : WithTop ℤ) + 1 +
        ((psi.conductor : ℤ) : WithTop ℤ)) =
    (((psi.conductor : ℤ) : WithTop ℤ) + 1)
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  change ((-(t : ℤ) + ((t : ℤ) + 1 + psi.conductor) : ℤ) :
      WithTop ℤ) = ((psi.conductor + 1 : ℤ) : WithTop ℤ)
  norm_cast
  omega
/-- The manuscript's `eta_0`, extracted from the actual norm coefficient
and the single lower residual character. -/
noncomputable def wildOddUpperEtaZero
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {p : ℕ}
    (S : PhaseReductionResidualCoordinateSource F K)
    (psi : LocalAddCharData F) (A : Fˣ) (t : ℕ)
    (hA : ord F (A : F) =
      (-(((t + 1 : ℕ) : ℤ) + psi.conductor) : WithTop ℤ))
    (C : FrobeniusResidualAddCharData F p) : ResidueField F := by
  letI := residueFieldFintype F
  exact finiteAddCharCoefficient C.lower C.lower_ne_one
    (residualAddChar F psi (wildOddUpperGammaZero S A t)
      (wildOddUpperGammaZero_order S psi A t hA))
theorem wildOddUpperEtaZero_spec
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {p : ℕ}
    (S : PhaseReductionResidualCoordinateSource F K)
    (psi : LocalAddCharData F) (A : Fˣ) (t : ℕ)
    (hA : ord F (A : F) =
      (-(((t + 1 : ℕ) : ℤ) + psi.conductor) : WithTop ℤ))
    (C : FrobeniusResidualAddCharData F p) (z : ResidueField F) :
    (psi.character
      ((A : F) * (S.lowerUniformizer : F) ^ t *
        (teichmuller F z : F)) : ℂ) =
      C.lower (wildOddUpperEtaZero S psi A t hA C * z) := by
  letI := residueFieldFintype F
  unfold wildOddUpperEtaZero
  rw [finiteAddCharCoefficient_apply]
  change (psi.character
      ((A : F) * (S.lowerUniformizer : F) ^ t *
        (teichmuller F z : F)) : ℂ) =
    (psi.character ((teichmuller F z : F) /
      (wildOddUpperGammaZero S A t : F)) : ℂ)
  congr 2
  unfold wildOddUpperGammaZero
  simp only [Units.val_inv_eq_inv_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  change (A : F) * (S.lowerUniformizer : F) ^ t *
      (teichmuller F z : F) =
    (teichmuller F z : F) /
      (((A : F) * (S.lowerUniformizer : F) ^ t)⁻¹)
  field_simp [Units.ne_zero A, Units.ne_zero S.lowerUniformizer]
theorem wildOddUpperEtaZero_ne_zero
    {F K : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    {p : ℕ}
    (S : PhaseReductionResidualCoordinateSource F K)
    (psi : LocalAddCharData F) (A : Fˣ) (t : ℕ)
    (hA : ord F (A : F) =
      (-(((t + 1 : ℕ) : ℤ) + psi.conductor) : WithTop ℤ))
    (C : FrobeniusResidualAddCharData F p) :
    wildOddUpperEtaZero S psi A t hA C ≠ 0 := by
  letI := residueFieldFintype F
  unfold wildOddUpperEtaZero
  apply finiteAddCharCoefficient_ne_zero
  exact residualAddChar_ne_one F psi (wildOddUpperGammaZero S A t)
    (wildOddUpperGammaZero_order S psi A t hA)
/-- An annihilated critical norm polynomial fixes the inverse-Frobenius
root in the manuscript's direction. -/
theorem wildOddCriticalPolynomial_frobeniusPreimage_eq
    {k : Type*} [Field k]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (psi : FiniteAddChar k) (hpsi : psi ≠ 1)
    (hfrob : ∀ x : k, psi (x ^ p) = psi x)
    {eta betaInv lambda : k}
    (hbetaInv : betaInv ^ p = eta)
    (hann : ∀ z : k,
      psi (eta * (z ^ p - lambda ^ (p - 1) * z)) = 1) :
    betaInv = eta * lambda ^ (p - 1) := by
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (AddChar.IsPrimitive.of_ne_one hpsi)
  ext z
  simp only [AddChar.mulShift_apply]
  rw [← hfrob (betaInv * z), mul_pow, hbetaInv]
  have hz := hann z
  rw [show eta * (z ^ p - lambda ^ (p - 1) * z) =
      eta * z ^ p - (eta * lambda ^ (p - 1)) * z by ring,
    AddChar.map_sub_eq_div] at hz
  exact (div_eq_one_iff_eq (AddChar.val_isUnit psi _).ne_zero).mp hz
theorem wildOddUpperEtaZero_frobeniusPreimage_eq
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {p : ℕ} (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (etaZero lambda : ResidueField F)
    (hann : ∀ z : ResidueField F,
      C.lower (etaZero * (z ^ p - lambda ^ (p - 1) * z)) = 1) :
    (C.frobeniusEquiv hchar).symm etaZero =
      etaZero * lambda ^ (p - 1) := by
  letI : Fact p.Prime := ⟨by
    simpa [hchar] using residueCharacteristic_prime F⟩
  letI : CharP (ResidueField F) p := ringChar.of_eq hchar
  have hpow : ((C.frobeniusEquiv hchar).symm etaZero) ^ p = etaZero := by
    rw [← C.frobeniusEquiv_apply hchar]
    exact (C.frobeniusEquiv hchar).apply_symm_apply etaZero
  exact wildOddCriticalPolynomial_frobeniusPreimage_eq C.lower
    C.lower_ne_one C.frobenius hpow hann
end
end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma

noncomputable section

private theorem compact_reduce_norm_unit_pow
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (v : K) (hvord : ord K v = (0 : WithTop ℤ)) :
    let hv : v ∈ lattice K 0 := by rw [mem_lattice, hvord]; exact le_rfl
    let hn : algebraMap F K (norm F K v) ∈ lattice K 0 := by
      rw [mem_lattice, ord_algebraMap, ord_norm, hres, one_nsmul, hvord,
        nsmul_zero]
      exact le_rfl
    reduce K (algebraMap F K (norm F K v)) hn =
      (reduce K v hv) ^ Module.finrank F K := by
  dsimp only
  classical
  have hv : v ∈ lattice K 0 := by rw [mem_lattice, hvord]; exact le_rfl
  let vO : ringOfIntegers K :=
    ⟨v, (mem_lattice_zero_iff K).1 hv⟩
  let cO : Gal(K/F) → ringOfIntegers K := fun σ ↦
    ⟨σ v, by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_galoisConjugate, hvord]
      exact le_rfl⟩
  let nO : ringOfIntegers K :=
    ⟨algebraMap F K (norm F K v), by
      rw [← mem_lattice_zero_iff, mem_lattice, ord_algebraMap, ord_norm,
        hres, one_nsmul, hvord, nsmul_zero]
      exact le_rfl⟩
  have hnO : nO = ∏ σ : Gal(K/F), cO σ := by
    apply Subtype.ext
    dsimp only [nO, cO]
    change algebraMap F K (norm F K v) =
      algebraMap (ringOfIntegers K) K
        (∏ σ : Gal(K/F), (⟨σ v, _⟩ : ringOfIntegers K))
    rw [map_prod]
    change algebraMap F K (norm F K v) = ∏ σ : Gal(K/F), σ v
    exact Algebra.norm_eq_prod_automorphisms F v
  have hconj (σ : Gal(K/F)) : residueMap K (cO σ) = residueMap K vO := by
    apply (residueMap_eq_residueMap_iff K _ _).2
    have htop : lowerRamificationGroup F K (0 : ℤ) = ⊤ :=
      PrimeCyclicExtension.lowerRamificationGroup_eq_top_of_le_break
        F K ht (by omega)
    have hσ : σ ∈ lowerRamificationGroup F K (0 : ℤ) := by
      rw [htop]
      trivial
    rw [← congruentAtDepth_iff_sub_mem_lattice]
    simpa only [cO, vO, zero_add] using
      (mem_lowerRamificationGroup F K σ (0 : ℤ)).1 hσ
        (⟨v, (mem_lattice_zero_iff K).1 hv⟩ : ringOfIntegers K)
  change residueMap K nO = (residueMap K vO) ^ Module.finrank F K
  rw [hnO, map_prod]
  calc
    ∏ σ : Gal(K/F), residueMap K (cO σ) =
        ∏ _σ : Gal(K/F), residueMap K vO := by
      apply Finset.prod_congr rfl
      intro σ _
      exact hconj σ
    _ = (residueMap K vO) ^ Fintype.card Gal(K/F) := by simp
    _ = (residueMap K vO) ^ Module.finrank F K := by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

end
end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma
noncomputable section
/-! Compact intrinsic break normalization. -/
section Break
variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1) (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
private def wildOddCompactPiF : F :=
  criticalNormLowerUniformizer F K pi
include hres hpi in
private theorem wildOddCompactPiF_uniformizer :
    (ValuativeRel.valuation F).IsUniformizer (wildOddCompactPiF F K pi) :=
  criticalNormLowerUniformizer_isUniformizer F K hres pi hpi
/-- Intrinsic critical ramification root in the PhaseReduction lower residue coordinate. -/
noncomputable def wildOddCompactLambda : ResidueField F :=
  criticalNormRamificationLambda F K ht hres pi hpi
include hgen in
theorem wildOddCompactLambda_ne_zero :
    wildOddCompactLambda F K ht hres pi hpi ≠ 0 :=
  criticalNormRamificationLambda_ne_zero F K ht hres pi hpi hgen
include hpi in
private def wildOddCompactDisp (z : ResidueField F) : lattice K ((s + 1 : ℕ) : ℤ) :=
  criticalNormSourceDisplacement F K (s + 1) pi hpi z
include hpi in
private noncomputable def wildOddCompactUnit
    (z : ResidueField F) : unitFiltration K (s + 1) :=
  criticalNormSourceUnit F K (by omega) pi hpi z
include ht hres hpi hgen in
def wildOddCompactP (z : ResidueField F) : ResidueField F :=
  criticalNormPolynomialValue F K ht (by omega) hres pi hpi hgen z
private theorem wildOddCompactP_raw (z : ResidueField F) :
    wildOddCompactP F K ht hres pi hpi hgen z =
      reduce F ((norm F K (1 + algebraMap F K
        (((teichmuller F z : ringOfIntegers F) : F)) * (pi : K) ^ (s + 1)) - 1) /
        wildOddCompactPiF F K pi ^ (s + 1)) (by
          have hd := (unitFiltrationDisplacement F s
            (normBelowBreakUnitFiltrationHom F K (s + 1) (s + 1)
              (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)
              (wildOddCompactUnit F K pi hpi z))).property
          apply (div_mem_lattice_iff F (wildOddCompactPiF F K pi ^ (s + 1)) _
            (s + 1 : ℤ) 0 (by
              rw [ord_pow, ord_uniformizer F
                (wildOddCompactPiF_uniformizer F K hres pi hpi)]; norm_num)).2
          simpa [wildOddCompactUnit, wildOddCompactDisp,
            coe_criticalNormSourceUnit] using hd) := by
  simpa only [wildOddCompactP, wildOddCompactPiF] using
    (criticalNormPolynomialValue_raw F K ht (by omega) hres pi hpi hgen z)
include ht hres hpi hgen in
noncomputable def wildOddCompactLift (z : ResidueField F) : lattice F 0 :=
  ⟨(norm F K (1 + algebraMap F K (((teichmuller F z : ringOfIntegers F) : F)) *
      (pi : K) ^ (s + 1)) - 1) / wildOddCompactPiF F K pi ^ (s + 1), by
    have hd := (unitFiltrationDisplacement F s
      (normBelowBreakUnitFiltrationHom F K (s + 1) (s + 1)
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)
        (wildOddCompactUnit F K pi hpi z))).property
    apply (div_mem_lattice_iff F (wildOddCompactPiF F K pi ^ (s + 1)) _
      (s + 1 : ℤ) 0 (by
        rw [ord_pow, ord_uniformizer F (wildOddCompactPiF_uniformizer F K hres pi hpi)];
        norm_num)).2
    simpa [wildOddCompactUnit, wildOddCompactDisp,
      coe_criticalNormSourceUnit] using hd⟩
@[simp] theorem wildOddCompactLift_reduce (z : ResidueField F) :
    reduce F (wildOddCompactLift F K ht hres pi hpi hgen z : F)
      (wildOddCompactLift F K ht hres pi hpi hgen z).property =
        wildOddCompactP F K ht hres pi hpi hgen z := by
  rw [wildOddCompactP_raw]; rfl
include ht hres hpi hgen in
private theorem wildOddCompactTrace_mem (x : K)
    (hx : x ∈ lattice K (s + 1 : ℤ)) : trace F K x ∈ lattice F (s + 1 : ℤ) :=
  criticalNormTrace_mem F K ht hres pi hpi hgen x hx
include ht hres hpi hgen in
private theorem wildOddCompactTrace_deep (x : K)
    (hx : x ∈ lattice K ((s + 2 : ℕ) : ℤ)) :
    trace F K x ∈ lattice F ((s + 2 : ℕ) : ℤ) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at h
    exact h.symm
  have h := trace_mem_lattice_floor F K pi hpi hgen ((s + 2 : ℕ) : ℤ) hx
  rw [differentExponent_eq F K ht pi hpi hgen, hram] at h
  convert h using 1
  have hp : 0 < Module.finrank F K := Module.finrank_pos
  congr 1
  have hn : (s + 2) + (Module.finrank F K - 1) * (s + 2) =
      Module.finrank F K * (s + 2) := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    rw [hq]
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  rw [show (((s + 2 : ℕ) : ℤ) +
      (((Module.finrank F K - 1) * (s + 1 + 1) : ℕ) : ℤ)) =
      (Module.finrank F K : ℤ) * (s + 2 : ℤ) by exact_mod_cast hn]
  symm
  apply Int.mul_ediv_cancel_left
  exact_mod_cast hp.ne'
include ht hres hpi hgen in
private def wildOddCompactC : ResidueField F :=
  criticalNormLinearCoefficient F K ht hres pi hpi hgen
/-- Exact critical polynomial `P(z)=z^p-lambda^(p-1)z`. -/
theorem wildOddCompactP_exact (z : ResidueField F) :
    wildOddCompactP F K ht hres pi hpi hgen z = z ^ Module.finrank F K -
      wildOddCompactLambda F K ht hres pi hpi ^ (Module.finrank F K - 1) * z :=
  criticalNormPolynomialValue_exact_of_positiveBreak
    F K ht (by omega) hres pi hpi hgen z
private theorem wildOddCompactC_eq :
    wildOddCompactC F K ht hres pi hpi hgen =
      -wildOddCompactLambda F K ht hres pi hpi ^ (Module.finrank F K - 1) :=
  criticalNormLinearCoefficient_eq_neg_ramificationLambda_pow
    F K ht (by omega) hres pi hpi hgen
include hgen in
theorem wildOddCompactTraceUnit (w : ringOfIntegers K) (z : ResidueField F) :
    trace F K ((w : K) * (pi : K) ^ (s + 1) *
        (teichmuller K
          (PhaseReductionResidualCoordinateSource.residueEquiv hres z) : K)) -
      wildOddCompactPiF F K pi ^ (s + 1) *
        (teichmuller F
          (-wildOddCompactLambda F K ht hres pi hpi ^
              (Module.finrank F K - 1) *
            (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
              (residueMap K w) * z) : F) ∈
        lattice F ((s + 2 : ℕ) : ℤ) := by
  let e := PhaseReductionResidualCoordinateSource.residueEquiv (F := F) (K := K) hres
  let q := e.symm (residueMap K w)
  let aO : ringOfIntegers F := teichmuller F (q * z)
  let aK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) aO
  let bK : ringOfIntegers K := w * teichmuller K (e z)
  have haKres : residueMap K aK = extensionResidueMap F K (residueMap F aO) := by
    exact (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (ValuativeRel.valuation F) (ValuativeRel.valuation K) aO).symm
  have hresidue : residueMap K bK = residueMap K aK := by
    rw [haKres]
    dsimp only [bK]
    rw [map_mul, residueMap_teichmuller]
    have hw : residueMap K w = e q := by
      exact (e.apply_symm_apply (residueMap K w)).symm
    rw [hw, ← e.map_mul]
    rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
    simp only [aO, residueMap_teichmuller]
  have hdiff : (bK : K) - (aK : K) ∈ lattice K 1 :=
    (residueMap_eq_residueMap_iff K bK aK).1 hresidue
  have hpiPow : (pi : K) ^ (s + 1) ∈ lattice K ((s + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_pow, ord_uniformizer K hpi]
    norm_num
  have htraceDiff : trace F K ((pi : K) ^ (s + 1) * ((bK : K) - (aK : K))) ∈
      lattice F ((s + 2 : ℕ) : ℤ) := by
    apply wildOddCompactTrace_deep F K ht hres pi hpi hgen
    have hm := mul_mem_lattice K hpiPow hdiff
    rw [show ((s + 1 : ℕ) : ℤ) + 1 = ((s + 2 : ℕ) : ℤ) by push_cast; ring] at hm
    exact hm
  let piF := wildOddCompactPiF F K pi
  let c : F := trace F K ((pi : K) ^ (s + 1)) / piF ^ (s + 1)
  have hcInt : c ∈ lattice F 0 := by
    dsimp only [c, piF]
    apply (div_mem_lattice_iff F _ _ (s + 1 : ℤ) 0 (by
      rw [ord_pow, ord_uniformizer F
        (wildOddCompactPiF_uniformizer F K hres pi hpi)]; norm_num)).2
    exact wildOddCompactTrace_mem F K ht hres pi hpi hgen _ (by
      rw [mem_lattice, ord_pow, ord_uniformizer K hpi]; norm_num)
  let cO : ringOfIntegers F := ⟨c, (mem_lattice_zero_iff F).1 hcInt⟩
  let targetO : ringOfIntegers F := teichmuller F
    (-wildOddCompactLambda F K ht hres pi hpi ^ (Module.finrank F K - 1) * q * z)
  have hcoefDiff : (cO * aO : F) - (targetO : F) ∈ lattice F 1 := by
    apply (residueMap_eq_residueMap_iff F (cO * aO) targetO).1
    rw [map_mul, residueMap_teichmuller, residueMap_teichmuller]
    change wildOddCompactC F K ht hres pi hpi hgen * (q * z) = _
    rw [wildOddCompactC_eq]
    ring
  have hpiFPow : piF ^ (s + 1) ∈ lattice F ((s + 1 : ℕ) : ℤ) := by
    rw [mem_lattice, ord_pow, ord_uniformizer F
      (wildOddCompactPiF_uniformizer F K hres pi hpi)]
    norm_num
  have hbase := mul_mem_lattice F hpiFPow hcoefDiff
  have hp0 : piF ^ (s + 1) ≠ 0 := pow_ne_zero _
    (wildOddCompactPiF_uniformizer F K hres pi hpi).ne_zero
  have hpiF0 : piF ≠ 0 :=
    (wildOddCompactPiF_uniformizer F K hres pi hpi).ne_zero
  have hactual : trace F K ((w : K) * (pi : K) ^ (s + 1) *
      (teichmuller K (e z) : K)) = trace F K ((pi : K) ^ (s + 1) * (bK : K)) := by
    change trace F K ((w : K) * (pi : K) ^ (s + 1) *
      (teichmuller K (e z) : K)) = trace F K
        ((pi : K) ^ (s + 1) * ((w : K) * (teichmuller K (e z) : K)))
    congr 1
    ring
  have htraceExpand : trace F K ((pi : K) ^ (s + 1) * ((bK : K) - (aK : K))) =
      trace F K ((pi : K) ^ (s + 1) * (bK : K)) -
        trace F K ((pi : K) ^ (s + 1) * (aK : K)) := by
    rw [mul_sub, map_sub]
  convert add_mem_lattice F htraceDiff hbase using 1
  rw [hactual, htraceExpand]
  have hscalar : trace F K
      ((pi : K) ^ (s + 1) * algebraMap F K (aO : F)) =
      (aO : F) * trace F K ((pi : K) ^ (s + 1)) := by
    rw [mul_comm]
    simpa [Algebra.smul_def] using (Algebra.trace F K).map_smul
      (aO : F) ((pi : K) ^ (s + 1))
  rw [show (aK : K) = algebraMap F K (aO : F) by rfl, hscalar]
  change trace F K ((pi : K) ^ (s + 1) * (bK : K)) -
      piF ^ (s + 1) * (targetO : F) =
    (trace F K ((pi : K) ^ (s + 1) * (bK : K)) -
      (aO : F) * trace F K ((pi : K) ^ (s + 1))) +
      piF ^ (s + 1) * (c * (aO : F) - (targetO : F))
  have hcCancel : piF ^ (s + 1) * c = trace F K ((pi : K) ^ (s + 1)) := by
    dsimp only [c]
    field_simp [hp0]
  rw [mul_sub, ← mul_assoc (piF ^ (s + 1)) c (aO : F), hcCancel]
  ring
/-! Exact residual normalization, independent of Lamprecht parity. -/
/-- Arbitrary integral-lift form of `eta₀`, suitable for normalized trace arguments. -/
theorem wildOddCompactEta_integral
    (S : PhaseReductionResidualCoordinateSource F K) (psi : LocalAddCharData F)
    (A : Fˣ) (t : ℕ)
    (hA : ord F (A : F) = (-(((t + 1 : ℕ) : ℤ) + psi.conductor) : WithTop ℤ))
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (x : F) (hx : x ∈ lattice F 0) :
    C.lower (wildOddUpperEtaZero S psi A t hA C * reduce F x hx) =
      (psi.character ((A : F) * (S.lowerUniformizer : F) ^ t * x) : ℂ) := by
  letI := residueFieldFintype F
  unfold wildOddUpperEtaZero
  rw [finiteAddCharCoefficient_apply, residualAddChar_integral_lift]
  congr 2
  unfold wildOddUpperGammaZero
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp [Units.ne_zero A, Units.ne_zero S.lowerUniformizer]
include hgen in
theorem wildOddCompactNormalizedTraceCharacter
    (psi : LocalAddCharData F) (A : Fˣ)
    (hA : ord F (A : F) =
      (-(((((s + 1) + 1 : ℕ) : ℤ) + psi.conductor)) : WithTop ℤ))
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (betaInv initial : ResidueField F)
    (hbeta : betaInv = wildOddUpperEtaZero
      (phaseReductionResidualCoordinateSource F K hres pi hpi)
        psi A (s + 1) hA C *
      wildOddCompactLambda F K ht hres pi hpi ^ (Module.finrank F K - 1))
    (r : ℤ) (dK : ℕ) (y : K) (hy : ord K y = (r : WithTop ℤ))
    (hdepth : r + 2 * (dK : ℤ) = (s + 1 : ℕ))
    (hinitial : ∀ hx :
      y * ((pi : K) ^ dK) ^ 2 / (pi : K) ^ (s + 1) ∈ lattice K 0,
      (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
          (reduce K (y * ((pi : K) ^ dK) ^ 2 / (pi : K) ^ (s + 1)) hx) =
        -initial)
    (z : ResidueField F) :
    (psi.character ((A : F) * trace F K
      (y * ((pi : K) ^ dK) ^ 2 *
        (teichmuller K
          (PhaseReductionResidualCoordinateSource.residueEquiv hres z) : K))) : ℂ) =
      C.lower ((betaInv * initial) * z) := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let e := PhaseReductionResidualCoordinateSource.residueEquiv (F := F) (K := K) hres
  let v : K := y * ((pi : K) ^ dK) ^ 2
  have hvord : ord K v = (((s + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [v]
    rw [ord_mul, ord_pow, ord_pow, hy, ord_uniformizer K hpi]
    change (r : WithTop ℤ) + 2 • (dK • (((1 : ℤ) : WithTop ℤ))) = _
    rw [← WithTop.coe_nsmul, ← WithTop.coe_nsmul]
    norm_cast
    simpa [nsmul_eq_mul] using hdepth
  have hx : v / (pi : K) ^ (s + 1) ∈ lattice K 0 := by
    rw [mem_lattice, ord_div, hvord, ord_pow, ord_uniformizer K hpi]
    norm_num
  let w : ringOfIntegers K :=
    ⟨v / (pi : K) ^ (s + 1), (mem_lattice_zero_iff K).1 hx⟩
  have hq : e.symm (residueMap K w) = -initial := by
    simpa only [w, reduce, v, e] using hinitial (by simpa only [v] using hx)
  have hvEq : (w : K) * (pi : K) ^ (s + 1) = v := by
    dsimp only [w]
    field_simp [pow_ne_zero _ hpi.ne_zero]
  have htrace := wildOddCompactTraceUnit F K ht hres pi hpi hgen w z
  rw [show (PhaseReductionResidualCoordinateSource.residueEquiv hres).symm
      (residueMap K w) = -initial by exact hq] at htrace
  rw [show -wildOddCompactLambda F K ht hres pi hpi ^
      (Module.finrank F K - 1) * -initial * z =
      wildOddCompactLambda F K ht hres pi hpi ^
        (Module.finrank F K - 1) * initial * z by ring] at htrace
  have htrace' : trace F K (v * (teichmuller K (e z) : K)) -
      wildOddCompactPiF F K pi ^ (s + 1) *
        (teichmuller F (wildOddCompactLambda F K ht hres pi hpi ^
          (Module.finrank F K - 1) * initial * z) : F) ∈
      lattice F (((s + 1) + 1 : ℕ) : ℤ) := by
    rw [← hvEq]
    simpa only [e, Nat.add_assoc] using htrace
  have hscaled := scaledAddChar_eq_of_sub_mem_lattice F psi A ((s + 1) + 1) hA htrace'
  have heta := wildOddUpperEtaZero_spec S psi A (s + 1) hA C
    (wildOddCompactLambda F K ht hres pi hpi ^
      (Module.finrank F K - 1) * initial * z)
  change (psi.character ((A : F) * trace F K
      (v * (teichmuller K (e z) : K))) : ℂ) = _
  calc
    _ = (psi.character ((A : F) * (S.lowerUniformizer : F) ^ (s + 1) *
        (teichmuller F (wildOddCompactLambda F K ht hres pi hpi ^
          (Module.finrank F K - 1) * initial * z) : F)) : ℂ) := by
      have hS : (S.lowerUniformizer : F) = wildOddCompactPiF F K pi := by rfl
      rw [hS]
      simpa only [e, mul_assoc] using hscaled
    _ = C.lower (wildOddUpperEtaZero S psi A (s + 1) hA C *
        (wildOddCompactLambda F K ht hres pi hpi ^
          (Module.finrank F K - 1) * initial * z)) := heta
    _ = C.lower ((betaInv * initial) * z) := by
      rw [hbeta]
      congr 1
      ring
/-- A raw-factor identity for the literal normalized norm proves eta annihilation;
this is the common final step for `lowTauRaw_eq_one` and `highOdd_tauRaw_eq_one`. -/
theorem wildOddCompactEta_annihilates
    (psi : LocalAddCharData F) (A : Fˣ)
    (hA : ord F (A : F) =
      (-((((s + 1) + 1 : ℕ) : ℤ) + psi.conductor) : WithTop ℤ))
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (hraw : ∀ z : ResidueField F,
      (psi.character ((A : F) * phaseReductionNormPolynomial F K
        (wildOddCompactDisp (s := s) F K pi hpi z : K)) : ℂ) = 1)
    (z : ResidueField F) :
    C.lower (wildOddUpperEtaZero
      (phaseReductionResidualCoordinateSource F K hres pi hpi)
        psi A (s + 1) hA C *
      wildOddCompactP F K ht hres pi hpi hgen z) = 1 := by
  let S := phaseReductionResidualCoordinateSource F K hres pi hpi
  let L := wildOddCompactLift F K ht hres pi hpi hgen z
  change C.lower (wildOddUpperEtaZero S psi A (s + 1) hA C *
    wildOddCompactP F K ht hres pi hpi hgen z) = 1
  have he := wildOddCompactEta_integral F K S psi A (s + 1) hA C (L : F) L.property
  rw [wildOddCompactLift_reduce] at he
  rw [he, ← hraw z]
  apply congrArg Units.val
  apply congrArg psi.character
  let piF := wildOddCompactPiF F K pi
  have hS : (S.lowerUniformizer : F) = piF := by rfl
  rw [hS]
  dsimp only [L, wildOddCompactLift]
  change (A : F) * piF ^ (s + 1) *
      ((norm F K (1 + (wildOddCompactDisp (s := s) F K pi hpi z : K)) - 1) /
        piF ^ (s + 1)) =
    (A : F) * phaseReductionNormPolynomial F K
      (wildOddCompactDisp (s := s) F K pi hpi z : K)
  unfold phaseReductionNormPolynomial
  have hp0 : piF ^ (s + 1) ≠ 0 := pow_ne_zero _
    (wildOddCompactPiF_uniformizer F K hres pi hpi).ne_zero
  field_simp [hp0]
end Break
end
end LanglandsFirstMainLemma

namespace LanglandsFirstMainLemma

noncomputable section

universe u v

/-! ## Boundary norm in the common lower residual coordinate -/

/-- The literal normalized norm at the boundary.  Both the upstairs unit
and its norm are proved integral before either residue is formed. -/
structure WildOddBoundaryNormNormalization
    (F : Type u) (K : Type v)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (u : K) where
  u_integral : u ∈ lattice K 0
  norm_integral : norm F K u ∈ lattice F 0
  nO : ringOfIntegers F
  nO_coe : (nO : F) = norm F K u
  zeta : ResidueField F
  dZero : ResidueField F
  dZero_eq : dZero = zeta ^ Module.finrank F K
  residueMap_nO : residueMap F nO = dZero
  zeta_ne_zero : zeta ≠ 0
  dZero_ne_zero : dZero ≠ 0

/-- At valuation zero the residue norm is forward Frobenius.  The equality
is stated downstairs, so no extra scalar is introduced when the literal
normalized norm is compared with `d₀ = ζ^p`. -/
noncomputable def WildOddBoundaryNormNormalization.of_order_zero
    (F : Type u) (K : Type v)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (u : K) (hu : ord K u = (0 : WithTop ℤ)) :
    WildOddBoundaryNormNormalization F K u := by
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) hres
  have hu_integral : u ∈ lattice K 0 := by
    rw [mem_lattice, hu]
    exact le_rfl
  have hnorm_order : ord F (norm F K u) = (0 : WithTop ℤ) := by
    rw [ord_norm, hres, one_nsmul, hu]
  have hnorm_integral : norm F K u ∈ lattice F 0 := by
    rw [mem_lattice, hnorm_order]
    exact le_rfl
  let uO : ringOfIntegers K :=
    ⟨u, (mem_lattice_zero_iff K).1 hu_integral⟩
  let nO : ringOfIntegers F :=
    ⟨norm F K u, (mem_lattice_zero_iff F).1 hnorm_integral⟩
  let zeta : ResidueField F := e.symm (residueMap K uO)
  let dZero : ResidueField F := zeta ^ Module.finrank F K
  have hleft : e (residueMap F nO) =
      reduce K (algebraMap F K (norm F K u)) (by
        rw [mem_lattice, ord_algebraMap, ord_norm, hres, one_nsmul, hu,
          nsmul_zero]
        exact le_rfl) := by
    rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
    unfold reduce
    change extensionResidueMap F K (residueMap F nO) =
      residueMap K
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) nO)
    exact
      Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation F) (ValuativeRel.valuation K) nO
  have hnormResidue := compact_reduce_norm_unit_pow F K ht hres u hu
  have hboundary : residueMap F nO = dZero := by
    apply e.injective
    rw [hleft]
    dsimp only [dZero, zeta]
    rw [map_pow, e.apply_symm_apply]
    exact hnormResidue
  have hzeta : zeta ≠ 0 := by
    intro hz
    have hz' := congrArg e hz
    dsimp only [zeta] at hz'
    rw [e.apply_symm_apply, map_zero] at hz'
    rw [residueMap_eq_zero_iff] at hz'
    rw [mem_lattice, hu] at hz'
    exact (by norm_num : ¬ (((1 : ℤ) : WithTop ℤ) ≤ 0)) hz'
  exact
    { u_integral := hu_integral
      norm_integral := hnorm_integral
      nO := nO
      nO_coe := rfl
      zeta := zeta
      dZero := dZero
      dZero_eq := rfl
      residueMap_nO := hboundary
      zeta_ne_zero := hzeta
      dZero_ne_zero := pow_ne_zero _ hzeta }

end
end LanglandsFirstMainLemma
namespace LanglandsFirstMainLemma

noncomputable section

/-! ## Source-tied High and Low specializations -/

section BreakSource

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres hgen in
/-- The literal break displacement has norm polynomial on the exact last
lower layer.  This is the integrality input used by both real source rows. -/
theorem wildOddCompactNormPolynomial_mem
    (z : ResidueField F) :
    phaseReductionNormPolynomial F K
        (wildOddCompactDisp (s := s) F K pi hpi z : K) ∈
      lattice F ((s + 1 : ℕ) : ℤ) := by
  let piF := wildOddCompactPiF F K pi
  let x := wildOddCompactDisp (s := s) F K pi hpi z
  have hdiv := (wildOddCompactLift F K ht hres pi hpi hgen z).property
  have hpiF :
      ord F (piF ^ (s + 1)) =
        (((s + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ord_uniformizer F
      (wildOddCompactPiF_uniformizer F K hres pi hpi)]
    norm_num
  have hmul := (div_mem_lattice_iff F (piF ^ (s + 1))
    (norm F K (1 + (x : K)) - 1) ((s + 1 : ℕ) : ℤ) 0 hpiF).1 hdiv
  simpa only [x, piF, phaseReductionNormPolynomial, add_zero] using hmul

end BreakSource

section HighSource

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (htpos : 0 < s + 1)
  (hstrict : s + 1 + 1 < (data.twistData 1).conductor)
  (hupper : (data.twistData 1).conductor < 2 * (s + 1 + 1))
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF)

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The exact High denominator quotient, retained as a unit so every
division used in the residual normalization carries its nonvanishing proof. -/
noncomputable def wildOddHighNormalizationCoefficient : Fˣ :=
  normUnits F K source.productRows.alpha1 / gammaF

/-- The actual High coefficient has precisely the last-break additive
normalization required by `eta₀`. -/
theorem wildOddHighNormalizationCoefficient_order :
    ord F (wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source : F) =
      (-(((((s + 1) + 1 : ℕ) : ℤ) + data.baseAddChar.conductor)) :
        WithTop ℤ) := by
  rw [wildOddHighNormalizationCoefficient, Units.val_div_eq_div_val,
    ord_div, coe_normUnits, source.productRows.alpha_choice.norm_order,
    hgammaF]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  push_cast
  ring

/-- `hraw` specialized to the real coherent High source and the literal
last-break displacement. -/
theorem wildOddHighNormalization_raw (z : ResidueField F) :
    (data.baseAddChar.character
      ((wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source : F) *
        phaseReductionNormPolynomial F K
          (wildOddCompactDisp (s := s) F K pi hpi z : K)) : ℂ) = 1 := by
  let uU : Kˣ := source.productRows.beta1 / source.productRows.alpha1
  let x : K := (uU⁻¹ : K) *
    (wildOddCompactDisp (s := s) F K pi hpi z : K)
  let upper : Kˣ :=
    (wildOddCompactUnit (s := s) F K pi hpi z : unitFiltration K (s + 1))
  have hu : highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows = (uU : K) := by
    simp [uU, highOddNormalizedRatio, Units.val_div_eq_div_val]
  have hux : highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source.productRows * x =
      (wildOddCompactDisp (s := s) F K pi hpi z : K) := by
    rw [hu]
    dsimp only [x]
    rw [← mul_assoc]
    simp
  have hUpper : (upper : K) =
      1 + highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK
        hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows * x := by
    rw [hux]
    simp only [upper, wildOddCompactUnit, coe_criticalNormSourceUnit,
      wildOddCompactDisp, criticalNormSourceDisplacement]
  have hP : phaseReductionNormPolynomial F K
      (highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
        hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
          source.productRows * x) ∈
      lattice F (((((s + 1) + 2) / 2 : ℕ) : ℤ)) := by
    rw [hux]
    apply lattice_antitone F
      (m := (((s + 1 + 2) / 2 : ℕ) : ℤ))
      (n := ((s + 1 : ℕ) : ℤ))
    · exact_mod_cast (show (s + 1 + 2) / 2 ≤ s + 1 by omega)
    · exact wildOddCompactNormPolynomial_mem F K ht hres pi hpi hgen z
  have hraw := highOdd_tauRaw_eq_one F K ht hres pi hpi hgen data chiK
    psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
      source x upper hUpper hP
  dsimp only at hraw
  let tau := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (1 : ZMod (Module.finrank F K)))
  have htau : (tau.1 (normUnits F K upper) : ℂ) = 1 := by
    exact congrArg (Units.val : ℂˣ → ℂ)
      (NormCharacter.eq_one_on_normRange F K tau _ ⟨upper, rfl⟩)
  have hcoef :
      1 / (((gammaF / normUnits F K source.normRows.alpha1 : Fˣ) : F)) =
        (wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
          chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
            gammaF hgammaF source : F) := by
    rw [wildOddHighNormalizationCoefficient, source.alpha1_eq]
    simp only [Units.val_div_eq_div_val]
    field_simp [Units.ne_zero gammaF,
      Units.ne_zero (normUnits F K source.productRows.alpha1)]
  rw [htau, inv_one, mul_one, hcoef, hux] at hraw
  exact hraw

/-- The real High upstairs representative divided by its unchanged
denominator is exactly `A·(n-u)`. -/
theorem wildOddHighStationaryRatio_eq_normalized :
    ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source.productRows : Kˣ) : K) /
        algebraMap F K (gammaF : F) =
      algebraMap F K
          (wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source : F) *
        (algebraMap F K
            (highOddNormalizedNorm F K ht hres pi hpi hgen data chiK psiK
              hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
                hgammaF source.productRows) -
          highOddNormalizedRatio F K ht hres pi hpi hgen data chiK psiK hF
            hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
              source.productRows) := by
  change ((highOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data
    chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
      hgammaF source.productRows : Kˣ) : K) /
      algebraMap F K (gammaF : F) =
    algebraMap F K (((normUnits F K source.productRows.alpha1 /
      gammaF : Fˣ) : F)) * _
  rw [highOddUpstairsRepresentative_eq_normalized]
  simp only [Units.val_div_eq_div_val, coe_normUnits, map_div₀]
  field_simp [Units.ne_zero gammaF]

/-- `hann` for the real High source, stated with the exact critical
polynomial rather than an abstract transported coordinate. -/
theorem wildOddHighNormalization_annihilator
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (z : ResidueField F) :
    C.lower
      (wildOddUpperEtaZero
          (phaseReductionResidualCoordinateSource F K hres pi hpi)
          data.baseAddChar
          (wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source)
          (s + 1)
          (wildOddHighNormalizationCoefficient_order F K ht hres pi hpi
            hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source) C *
        (z ^ Module.finrank F K -
          wildOddCompactLambda F K ht hres pi hpi ^
              (Module.finrank F K - 1) * z)) = 1 := by
  rw [← wildOddCompactP_exact F K ht hres pi hpi hgen z]
  exact wildOddCompactEta_annihilates F K ht hres pi hpi hgen
    data.baseAddChar
    (wildOddHighNormalizationCoefficient F K ht hres pi hpi hgen data
      chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF source)
    (wildOddHighNormalizationCoefficient_order F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF source) C
    (wildOddHighNormalization_raw F K ht hres pi hpi hgen data chiK psiK
      hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
        source) z

end HighSource

section LowSource

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hLow : (data.twistData 1).conductor ≤ s + 1 + 1)
  (delta : Fˣ) (epsilon1 : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((s + 1 + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) :
      WithTop ℤ))
  (hepsilon1 : ord K (epsilon1 : K) =
    (((s + 1 + 1 - (data.twistData 1).conductor : ℕ) : ℤ) :
      WithTop ℤ))
  (hT : 2 ≤ s + 1 + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth (s + 1)) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (s + 1 + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := s + 1) hT)
        delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF))
  (table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The exact Low denominator quotient from the simultaneous stationary
pair, retained as a unit. -/
noncomputable def wildOddLowNormalizationCoefficient : Fˣ :=
  P.alpha / delta

/-- The actual Low coefficient has the same last-break additive
normalization as the coherent High coefficient. -/
theorem wildOddLowNormalizationCoefficient_order :
    ord F (wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P) : F) =
      (-(((((s + 1) + 1 : ℕ) : ℤ) + data.baseAddChar.conductor)) :
        WithTop ℤ) := by
  rw [wildOddLowNormalizationCoefficient, Units.val_div_eq_div_val,
    ord_div]
  change ord F (norm F K (P.alpha₁ : K)) - ord F (delta : F) = _
  rw [P.alphaRepresentative.norm_order, hdelta]
  simp

include ht hres hgen hminimal hchi hpsi hLow hdelta hepsilon1 hT hgammaF
  hgammaK table in
/-- `hraw` specialized to the real Low table source, its exact stationary
pair, and the literal last-break displacement. -/
theorem wildOddLowNormalization_raw (z : ResidueField F) :
    (data.baseAddChar.character
      ((wildOddLowNormalizationCoefficient
          (F := F) (K := K) (delta := delta) (hT := hT) (P := P) : F) *
        phaseReductionNormPolynomial F K
          (wildOddCompactDisp (s := s) F K pi hpi z : K)) : ℂ) = 1 := by
  let uU : Kˣ := epsilon1 * P.beta₁ / P.alpha₁
  let x : K := (uU⁻¹ : K) *
    (wildOddCompactDisp (s := s) F K pi hpi z : K)
  let upper : Kˣ :=
    (wildOddCompactUnit (s := s) F K pi hpi z : unitFiltration K (s + 1))
  have hu : lowNormalizedRatio F K epsilon1 P = (uU : K) := by
    simp [uU, lowNormalizedRatio, Units.val_div_eq_div_val]
  have hux : lowNormalizedRatio F K epsilon1 P * x =
      (wildOddCompactDisp (s := s) F K pi hpi z : K) := by
    rw [hu]
    dsimp only [x]
    rw [← mul_assoc]
    simp
  have hUpper : (upper : K) =
      1 + lowNormalizedRatio F K epsilon1 P * x := by
    rw [hux]
    simp only [upper, wildOddCompactUnit, coe_criticalNormSourceUnit,
      wildOddCompactDisp, criticalNormSourceDisplacement]
  have hP : phaseReductionNormPolynomial F K
      (lowNormalizedRatio F K epsilon1 P * x) ∈
      lattice F (((lowCriticalFloorDepth (s + 1) +
        lowCriticalParity (s + 1) : ℕ) : ℤ)) := by
    rw [hux]
    apply lattice_antitone F
      (m := ((lowCriticalFloorDepth (s + 1) +
        lowCriticalParity (s + 1) : ℕ) : ℤ))
      (n := ((s + 1 : ℕ) : ℤ))
    · have hc := lowCriticalConductor_eq (t := s + 1)
      have hp := lowCriticalParity_le_one (t := s + 1)
      exact_mod_cast (show lowCriticalFloorDepth (s + 1) +
        lowCriticalParity (s + 1) ≤ s + 1 by omega)
    · exact wildOddCompactNormPolynomial_mem F K ht hres pi hpi hgen z
  have hraw := lowTauRaw_eq_one F K ht hres pi hpi hgen data hF delta
    epsilon1 hdelta hT hgammaF P x upper hUpper hP
  dsimp only at hraw
  let tau := lowNormCharacterGenerator F K ht hres pi hpi hgen
  have htau : (tau.1 (normUnits F K upper) : ℂ) = 1 := by
    exact congrArg (Units.val : ℂˣ → ℂ)
      (NormCharacter.eq_one_on_normRange F K tau _ ⟨upper, rfl⟩)
  have hcoef : (P.alpha : F) / (delta : F) =
      (wildOddLowNormalizationCoefficient
        (F := F) (K := K) (delta := delta) (hT := hT) (P := P) : F) := by
    simp [wildOddLowNormalizationCoefficient, Units.val_div_eq_div_val]
  rw [htau, inv_one, mul_one, hcoef, hux] at hraw
  exact hraw

/-- The explicitly supplied Low upstairs witness has the same exact
stationary ratio `A·(n-u)` used by normalized trace. -/
theorem wildOddLowStationaryRatio_eq_normalized
    (W : LowOddUpstairsWitness F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table) :
    ((lowOddUpstairsRepresentativeUnit F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table W : Kˣ) : K) /
        (lowGammaK F K delta epsilon1 : K) =
      algebraMap F K
          (wildOddLowNormalizationCoefficient
            (F := F) (K := K) (delta := delta) (hT := hT) (P := P) : F) *
        (algebraMap F K
            (lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT)) -
          lowNormalizedRatio F K epsilon1 P) := by
  rw [lowOddUpstairsRepresentative_eq_normalized]
  dsimp only [wildOddLowNormalizationCoefficient, lowOddNormalizedNorm,
    lowGammaK]
  simp only [Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
    map_div₀, map_mul]
  field_simp [Units.ne_zero delta, Units.ne_zero epsilon1,
    Units.ne_zero P.alpha]

include hminimal hchi hpsi hLow hepsilon1 hgammaK table in
/-- `hann` for the actual Low stationary pair and parameter table. -/
theorem wildOddLowNormalization_annihilator
    (C : FrobeniusResidualAddCharData F (Module.finrank F K))
    (z : ResidueField F) :
    C.lower
      (wildOddUpperEtaZero
          (phaseReductionResidualCoordinateSource F K hres pi hpi)
          data.baseAddChar
          (wildOddLowNormalizationCoefficient
            (F := F) (K := K) (delta := delta) (hT := hT) (P := P))
          (s + 1)
          (wildOddLowNormalizationCoefficient_order
            (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
            (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
            (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
            (hT := hT) (hgammaF := hgammaF) (P := P)) C *
        (z ^ Module.finrank F K -
          wildOddCompactLambda F K ht hres pi hpi ^
              (Module.finrank F K - 1) * z)) = 1 := by
  rw [← wildOddCompactP_exact F K ht hres pi hpi hgen z]
  exact wildOddCompactEta_annihilates F K ht hres pi hpi hgen
    data.baseAddChar
    (wildOddLowNormalizationCoefficient
      (F := F) (K := K) (delta := delta) (hT := hT) (P := P))
    (wildOddLowNormalizationCoefficient_order
      (F := F) (K := K) (ht := ht) (hres := hres) (pi := pi)
      (hpi := hpi) (hgen := hgen) (data := data) (hF := hF)
      (delta := delta) (epsilon1 := epsilon1) (hdelta := hdelta)
      (hT := hT) (hgammaF := hgammaF) (P := P)) C
    (wildOddLowNormalization_raw F K ht hres pi hpi hgen data chiK psiK
      hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table) z

include hepsilon1 in
/-- At the noncancelling Low boundary the real normalized ratio has order
zero, and its literal norm has residue `d₀ = ζ^p` in the common lower
coordinate, with the manuscript's forward orientation. -/
noncomputable def wildOddLowBoundaryNormNormalization
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    WildOddBoundaryNormNormalization F K
      (lowNormalizedRatio F K epsilon1 P) := by
  apply WildOddBoundaryNormNormalization.of_order_zero F K ht hres
  simpa [hboundary] using
    (lowNormalizedRatio_order F K epsilon1 hepsilon1 P)

/-- The boundary package identifies its integral lift with the exact Low
normalized norm and records every residue and nonvanishing condition used
downstream. -/
theorem wildOddLowBoundaryNormNormalization_spec
    (hboundary : (data.twistData 1).conductor = s + 1 + 1) :
    let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
      data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
    lowNormalizedRatio F K epsilon1 P ∈ lattice K 0 ∧
      norm F K (lowNormalizedRatio F K epsilon1 P) ∈ lattice F 0 ∧
      ((N.nO : F) = lowOddNormalizedNorm
        (F := F) (K := K) (P := P) (hT := hT)) ∧
      (residueMap F N.nO = N.dZero) ∧
      (N.dZero = N.zeta ^ Module.finrank F K) ∧
      N.zeta ≠ 0 ∧ N.dZero ≠ 0 := by
  let N := wildOddLowBoundaryNormNormalization F K ht hres pi hpi hgen
    data hF delta epsilon1 hdelta hepsilon1 hT hgammaF P hboundary
  have hn : norm F K (lowNormalizedRatio F K epsilon1 P) =
      lowOddNormalizedNorm (F := F) (K := K) (P := P) (hT := hT) := by
    simpa only [lowOddNormalizedNorm] using
      (lowNormalizedRatio_norm F K epsilon1 P)
  exact ⟨N.u_integral, N.norm_integral, N.nO_coe.trans hn,
    N.residueMap_nO, N.dZero_eq, N.zeta_ne_zero, N.dZero_ne_zero⟩

end LowSource

/-- The narrow normalization API consumed by the upper residual coefficient
node.  It contains source specialization, trace normalization, the raw and
annihilator directions, exact Frobenius transport, and the boundary residue;
it contains no coefficient rows or cancellation argument. -/
structure WildOddUpperResidualNormalizationAPI : Prop where
  highCoefficientOrder :
    type_of% @wildOddHighNormalizationCoefficient_order
  lowCoefficientOrder :
    type_of% @wildOddLowNormalizationCoefficient_order
  normalizedTrace : type_of% @wildOddCompactNormalizedTraceCharacter
  highStationaryRatio :
    type_of% @wildOddHighStationaryRatio_eq_normalized
  lowStationaryRatio :
    type_of% @wildOddLowStationaryRatio_eq_normalized
  highRaw : type_of% @wildOddHighNormalization_raw
  lowRaw : type_of% @wildOddLowNormalization_raw
  highAnnihilator : type_of% @wildOddHighNormalization_annihilator
  lowAnnihilator : type_of% @wildOddLowNormalization_annihilator
  criticalPolynomial : type_of% @wildOddCompactP_exact
  criticalRootNonzero : type_of% @wildOddCompactLambda_ne_zero
  etaNonzero : type_of% @wildOddUpperEtaZero_ne_zero.{0, 0}
  inverseFrobeniusRoot :
    type_of% @wildOddUpperEtaZero_frobeniusPreimage_eq.{0}
  boundary : type_of% @wildOddLowBoundaryNormNormalization_spec

/-- The completed High/Low upper residual normalization package. -/
theorem wildOdd_upperResidualNormalization :
    WildOddUpperResidualNormalizationAPI where
  highCoefficientOrder := wildOddHighNormalizationCoefficient_order
  lowCoefficientOrder := wildOddLowNormalizationCoefficient_order
  normalizedTrace := wildOddCompactNormalizedTraceCharacter
  highStationaryRatio := wildOddHighStationaryRatio_eq_normalized
  lowStationaryRatio := wildOddLowStationaryRatio_eq_normalized
  highRaw := wildOddHighNormalization_raw
  lowRaw := wildOddLowNormalization_raw
  highAnnihilator := wildOddHighNormalization_annihilator
  lowAnnihilator := wildOddLowNormalization_annihilator
  criticalPolynomial := wildOddCompactP_exact
  criticalRootNonzero := wildOddCompactLambda_ne_zero
  etaNonzero := wildOddUpperEtaZero_ne_zero
  inverseFrobeniusRoot := wildOddUpperEtaZero_frobeniusPreimage_eq
  boundary := wildOddLowBoundaryNormNormalization_spec

end
end LanglandsFirstMainLemma
