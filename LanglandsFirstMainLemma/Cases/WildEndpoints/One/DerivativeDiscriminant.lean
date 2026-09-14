import LanglandsFirstMainLemma.Cases.WildEndpoints.One.CyclicWilson

/-!
# Derivative, discriminant, and explicit Wilson-product factors
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

section EndpointDerivativeResidue

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

variable (n : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K (n + 1))
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

local instance endpointDegreePrimeFact' :
    Fact (Nat.Prime (Module.finrank F K)) :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

include ht hpi hgen in
noncomputable def endpointNormalizedDerivativeFactor
    (sigma : {sigma : Gal(K/F) // sigma ≠ 1}) : ringOfIntegers K :=
  ⟨((pi : K) - sigma.1 (pi : K)) / (pi : K) ^ (n + 2), by
    have hnum : ord K ((pi : K) - sigma.1 (pi : K)) =
        ((((n + 2 : ℕ) : ℤ)) : WithTop ℤ) := by
      rw [show (pi : K) - sigma.1 (pi : K) =
          -(sigma.1 (pi : K) - (pi : K)) by ring, ord_neg,
        ord_galois_uniformizer_sub_eq_of_isLowerBreak F K ht pi hpi hgen sigma.2]
    have hden : ord K ((pi : K) ^ (n + 2)) =
        ((((n + 2 : ℕ) : ℤ)) : WithTop ℤ) := by
      rw [ord_pow, ord_uniformizer K hpi]
      norm_num
    rw [← mem_lattice_zero_iff]
    rw [mem_lattice, ord_div, hnum, hden]
    norm_num⟩

@[simp] theorem endpointNormalizedDerivativeFactor_coe
    (sigma : {sigma : Gal(K/F) // sigma ≠ 1}) :
    (endpointNormalizedDerivativeFactor F K n ht pi hpi hgen sigma : K) =
      ((pi : K) - sigma.1 (pi : K)) / (pi : K) ^ (n + 2) := rfl

include ht hpi hgen in
noncomputable def endpointNormalizedDerivative : ringOfIntegers K := by
  classical
  exact ∏ sigma : {sigma : Gal(K/F) // sigma ≠ 1},
    endpointNormalizedDerivativeFactor F K n ht pi hpi hgen sigma

theorem endpointNormalizedDerivative_field_eq :
    (endpointNormalizedDerivative F K n ht pi hpi hgen : K) =
      endpointDerivative F K pi /
        (pi : K) ^ ((Module.finrank F K - 1) * (n + 2)) := by
  classical
  rw [endpointNormalizedDerivative]
  change (ringOfIntegers K).subtype
      (∏ sigma : {sigma : Gal(K/F) // sigma ≠ 1},
        endpointNormalizedDerivativeFactor F K n ht pi hpi hgen sigma) = _
  rw [map_prod]
  change (∏ sigma : {sigma : Gal(K/F) // sigma ≠ 1},
      ((pi : K) - sigma.1 (pi : K)) / (pi : K) ^ (n + 2)) = _
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_const]
  have hcard : Fintype.card {sigma : Gal(K/F) // sigma ≠ 1} =
      Module.finrank F K - 1 := by
    rw [← Fintype.card_congr (endpointNonidentityEquivZModUnits F K)]
    rw [ZMod.card_units_eq_totient,
      Nat.totient_prime (PrimeCyclicExtension.degree_prime F K)]
  rw [Finset.card_univ, hcard]
  have hden :
      ((pi : K) ^ (n + 2)) ^ (Module.finrank F K - 1) =
        (pi : K) ^ ((Module.finrank F K - 1) * (n + 2)) := by
    simpa only [Nat.mul_comm] using
      (pow_mul (pi : K) (n + 2) (Module.finrank F K - 1)).symm
  rw [hden]
  rw [endpointDerivative_eq_prod_nonidentity F K pi hgen]
  rw [div_eq_div_iff]
  · congr 1
    symm
    apply Finset.prod_subtype
    intro sigma
    rw [mem_nonidentityGaloisAutomorphisms]
  · exact pow_ne_zero _ hpi.ne_zero
  · exact pow_ne_zero _ hpi.ne_zero

theorem residueMap_endpointNormalizedDerivativeFactor
    (sigma : {sigma : Gal(K/F) // sigma ≠ 1}) :
    residueMap K
        (endpointNormalizedDerivativeFactor F K n ht pi hpi hgen sigma) =
      -lowerRamificationResidueDisplacement F K
        (endpointLowerBreakElement F K n ht sigma.1) (pi : K) hpi := by
  let d := lowerRamificationNormalizedDisplacement F K
    (endpointLowerBreakElement F K n ht sigma.1) (pi : K) hpi
  let dO : ringOfIntegers K :=
    ⟨(d : K), (mem_lattice_zero_iff K).1 d.property⟩
  have hfactor :
      endpointNormalizedDerivativeFactor F K n ht pi hpi hgen sigma = -dO := by
    apply Subtype.ext
    change ((pi : K) - sigma.1 (pi : K)) / (pi : K) ^ (n + 2) = -(d : K)
    rw [show (d : K) =
        (sigma.1 (pi : K) - (pi : K)) /
          (pi : K) ^ ((((n + 1 : ℕ) : ℤ)) + 1) by
      exact coe_lowerRamificationNormalizedDisplacement F K
        (endpointLowerBreakElement F K n ht sigma.1) (pi : K) hpi]
    have hexp : ((((n + 1 : ℕ) : ℤ)) + 1) = ((n + 2 : ℕ) : ℤ) := by
      omega
    rw [hexp, zpow_natCast]
    ring
  rw [hfactor, map_neg]
  rfl

theorem residueMap_endpointNormalizedDerivative :
    residueMap K (endpointNormalizedDerivative F K n ht pi hpi hgen) =
      (-1 : ResidueField K) ^ Module.finrank F K *
        endpointRamificationLambda F K n ht pi hpi hgen ^
          (Module.finrank F K - 1) := by
  classical
  let p := Module.finrank F K
  have hcharF : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K ht (by omega)
      pi hpi hgen
  have hcharK : residueCharacteristic K = p :=
    (residueCharacteristic_extension_eq F K).trans hcharF
  letI : CharP (ResidueField K) p := ringChar.of_eq hcharK
  have hcast (u : (ZMod p)ˣ) :
      (u.val.val : ResidueField K) =
        ZMod.castHom (dvd_refl p) (ResidueField K) (u : ZMod p) := by
    simpa only [ZMod.castHom_apply] using
      (ZMod.natCast_val (R := ResidueField K) (u : ZMod p))
  rw [endpointNormalizedDerivative, map_prod]
  rw [← (endpointNonidentityEquivZModUnits F K).prod_comp
    (fun sigma ↦ residueMap K
      (endpointNormalizedDerivativeFactor F K n ht pi hpi hgen sigma))]
  calc
    (∏ u : (ZMod p)ˣ,
        residueMap K
          (endpointNormalizedDerivativeFactor F K n ht pi hpi hgen
            (endpointNonidentityEquivZModUnits F K u))) =
        ∏ u : (ZMod p)ˣ,
          (-ZMod.castHom (dvd_refl p) (ResidueField K) (u : ZMod p)) *
            endpointRamificationLambda F K n ht pi hpi hgen := by
      apply Finset.prod_congr rfl
      intro u hu
      rw [residueMap_endpointNormalizedDerivativeFactor]
      change -lowerRamificationResidueDisplacement F K
          (endpointLowerBreakElement F K n ht
            (endpointGaloisZModEquiv F K (Multiplicative.ofAdd (u : ZMod p))))
          (pi : K) hpi = _
      rw [endpointResidueDisplacement_zmod F K n ht pi hpi hgen (u : ZMod p)]
      rw [hcast]
      ring
    _ = (-1 : ResidueField K) ^ p *
          endpointRamificationLambda F K n ht pi hpi hgen ^ (p - 1) :=
      endpointWilsonProduct (endpointRamificationLambda F K n ht pi hpi hgen)

theorem endpointNormalizedDerivative_order :
    ord K (endpointNormalizedDerivative F K n ht pi hpi hgen : K) = 0 := by
  rw [endpointNormalizedDerivative_field_eq F K n ht pi hpi hgen, ord_div,
    endpointDerivative_order F K ht pi hpi hgen, ord_pow, ord_uniformizer K hpi]
  have hexp :
      (Module.finrank F K - 1) * ((n + 1) + 1) =
        (Module.finrank F K - 1) * (n + 2) := by
    congr 1
  rw [hexp]
  simp
  norm_cast

end EndpointDerivativeResidue
section EndpointDerivativeNormResidue

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]

variable (n : ℕ) (ht : PrimeCyclicExtension.IsLowerBreak F K (n + 1))
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hpi hgen in
noncomputable def endpointNormalizedDerivativeNorm : ringOfIntegers F :=
  ⟨norm F K (endpointNormalizedDerivative F K n ht pi hpi hgen : K), by
    rw [← mem_lattice_zero_iff, mem_lattice, ord_norm,
      endpointNormalizedDerivative_order F K n ht pi hpi hgen]
    simp⟩

@[simp] theorem endpointNormalizedDerivativeNorm_coe :
    (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen : F) =
      norm F K (endpointNormalizedDerivative F K n ht pi hpi hgen : K) := rfl

theorem residueMap_galois_endpointNormalizedDerivative (sigma : Gal(K/F)) :
    residueMap K
        (galoisIntegerEquiv F K sigma
          (endpointNormalizedDerivative F K n ht pi hpi hgen)) =
      residueMap K (endpointNormalizedDerivative F K n ht pi hpi hgen) := by
  have hsBreak : sigma ∈
      lowerRamificationGroup F K (((n + 1 : ℕ) : ℤ)) := by
    rw [ht.1]
    trivial
  have hsZero : sigma ∈ lowerRamificationGroup F K 0 :=
    (lowerRamificationGroup_antitone F K (show (0 : ℤ) ≤ (n + 1 : ℕ) by omega))
      hsBreak
  rw [lowerRamificationGroup_zero_eq_ker_galoisResidueAction F K,
    MonoidHom.mem_ker] at hsZero
  calc
    residueMap K
        (galoisIntegerEquiv F K sigma
          (endpointNormalizedDerivative F K n ht pi hpi hgen)) =
        galoisResidueAction F K sigma
          (residueMap K (endpointNormalizedDerivative F K n ht pi hpi hgen)) :=
      (galoisResidueAction_residue F K sigma _).symm
    _ = residueMap K (endpointNormalizedDerivative F K n ht pi hpi hgen) := by
      rw [hsZero]
      rfl

theorem endpointResidueEquiv_normalizedDerivativeNorm
    (hres : residueDegree F K = 1) :
    endpointResidueEquiv F K hres
        (residueMap F (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen)) =
      residueMap K (endpointNormalizedDerivative F K n ht pi hpi hgen) ^
        Module.finrank F K := by
  classical
  let D := endpointNormalizedDerivative F K n ht pi hpi hgen
  let DN := endpointNormalizedDerivativeNorm F K n ht pi hpi hgen
  let DNK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) DN
  have hDNKcoe : (DNK : K) = algebraMap F K (DN : F) :=
    Valuation.HasExtension.val_algebraMap DN
  have hprodField :
      (∏ sigma : Gal(K/F), sigma (D : K)) =
        algebraMap F K (norm F K (D : K)) := by
    simpa only [galoisConjugates, galoisConjugate,
      Finset.prod_eq_multiset_prod] using galoisConjugates_prod F K (D : K)
  have hDNK : DNK = ∏ sigma : Gal(K/F), galoisIntegerEquiv F K sigma D := by
    apply Subtype.ext
    rw [hDNKcoe]
    rw [show (DN : F) = norm F K (D : K) by rfl]
    change algebraMap F K (norm F K (D : K)) =
      (ringOfIntegers K).subtype
        (∏ sigma : Gal(K/F), galoisIntegerEquiv F K sigma D)
    rw [map_prod]
    change algebraMap F K (norm F K (D : K)) =
      ∏ sigma : Gal(K/F), sigma (D : K)
    exact hprodField.symm
  rw [endpointResidueEquiv_apply]
  change residueMap K DNK = residueMap K D ^ Module.finrank F K
  rw [hDNK, map_prod]
  calc
    (∏ sigma : Gal(K/F),
        residueMap K (galoisIntegerEquiv F K sigma D)) =
        ∏ _sigma : Gal(K/F), residueMap K D := by
      apply Finset.prod_congr rfl
      intro sigma hsigma
      exact residueMap_galois_endpointNormalizedDerivative
        F K n ht pi hpi hgen sigma
    _ = residueMap K D ^ Module.finrank F K := by
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        PrimeCyclicExtension.galoisCard_eq_degree F K]

theorem residueMap_endpointNormalizedDerivativeNorm
    (hres : residueDegree F K = 1) :
    residueMap F (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen) =
      (-1 : ResidueField F) ^ Module.finrank F K *
        endpointNormalizedDerivativeCriticalLambda F K n ht pi hpi hgen hres ^
          (Module.finrank F K * (Module.finrank F K - 1)) := by
  classical
  let p := Module.finrank F K
  let e := endpointResidueEquiv F K hres
  have hlambda :
      e (endpointNormalizedDerivativeCriticalLambda F K n ht pi hpi hgen hres) =
        endpointRamificationLambda F K n ht pi hpi hgen := by
    exact (endpointResidueEquiv F K hres).apply_symm_apply _
  apply e.injective
  rw [endpointResidueEquiv_normalizedDerivativeNorm F K n ht pi hpi hgen hres]
  rw [residueMap_endpointNormalizedDerivative F K n ht pi hpi hgen]
  simp only [map_mul, map_pow, map_neg, map_one, hlambda]
  change (((-1 : ResidueField K) ^ p *
      endpointRamificationLambda F K n ht pi hpi hgen ^ (p - 1)) ^ p) =
    (-1 : ResidueField K) ^ p *
      endpointRamificationLambda F K n ht pi hpi hgen ^ (p * (p - 1))
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have hsign : (-1 : ResidueField K) ^ (p * p) =
      (-1 : ResidueField K) ^ p := by
    rcases (PrimeCyclicExtension.degree_prime F K).eq_two_or_odd' with hp2 | hpodd
    · rw [show p = 2 from hp2]
      norm_num
    · rw [(hpodd.mul hpodd).neg_one_pow, hpodd.neg_one_pow]
  rw [hsign]
  rw [Nat.mul_comm (p - 1) p]

theorem endpointNormalizedDerivativeNorm_order :
    ord F (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen : F) = 0 := by
  rw [endpointNormalizedDerivativeNorm_coe, ord_norm,
    endpointNormalizedDerivative_order F K n ht pi hpi hgen]
  simp

include ht hpi hgen in
noncomputable def endpointNormalizedDerivativeNormLocalUnit : unitGroup F :=
  ⟨Units.mk0
      (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen : F)
      ((ord_ne_top_iff F).1 (by
        rw [endpointNormalizedDerivativeNorm_order F K n ht pi hpi hgen]
        simp)),
    (mem_unitGroup_iff_ord_eq_zero F _).2
      (endpointNormalizedDerivativeNorm_order F K n ht pi hpi hgen)⟩

@[simp] theorem residueUnits_endpointNormalizedDerivativeNormLocalUnit :
    ((residueUnits F
        (endpointNormalizedDerivativeNormLocalUnit F K n ht pi hpi hgen) :
          (ResidueField F)ˣ) : ResidueField F) =
      residueMap F (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen) := by
  rw [residueUnits_coe]
  congr 1

/-- The norm part of the endpoint discriminant congruence.  The assumption
is precisely the reciprocal-stationary residue power furnished by the
critical annihilator; the conclusion fixes the quotient direction in
`U_F^1`. -/
theorem endpointNormalizedDerivativeNorm_div_stationaryPower_mem_one
    (hres : residueDegree F K = 1)
    (a : unitGroup F)
    (ha : (((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) ^
        (Module.finrank F K - 1)) =
      endpointNormalizedDerivativeCriticalLambda F K n ht pi hpi hgen hres ^
        (Module.finrank F K * (Module.finrank F K - 1))) :
    (((endpointNormalizedDerivativeNormLocalUnit F K n ht pi hpi hgen /
        (endpointNegOneLocalUnit F ^ Module.finrank F K *
          a ^ (Module.finrank F K - 1)) : unitGroup F) : Fˣ)) ∈
      unitFiltration F 1 := by
  let p := Module.finrank F K
  let D0 := endpointNormalizedDerivativeNormLocalUnit F K n ht pi hpi hgen
  let s0 := endpointNegOneLocalUnit F ^ p
  have hresEq : residueUnits F D0 = residueUnits F (s0 * a ^ (p - 1)) := by
    apply Units.ext
    rw [map_mul, map_pow, map_pow]
    change residueMap F
        (endpointNormalizedDerivativeNorm F K n ht pi hpi hgen) =
      (-1 : ResidueField F) ^ p *
        (((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) ^ (p - 1))
    rw [residueMap_endpointNormalizedDerivativeNorm F K n ht pi hpi hgen hres]
    rw [ha]
  have hker : D0 / (s0 * a ^ (p - 1)) ∈ (residueUnits F).ker := by
    rw [MonoidHom.mem_ker, map_div, hresEq]
    simp
  rw [residueUnits_ker] at hker
  have hmem := (mem_unitFiltrationInside F (show (0 : ℕ) ≤ 1 by omega)
    (D0 / (s0 * a ^ (p - 1)))).1 hker
  simpa only [D0, s0, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_pow] using hmem

/-- Algebraic assembly of the intrinsic norm congruence with the reciprocal
stationary quotient.  Here `a = c/A` is the normalized reciprocal and
`upper = A^(p-1) N(D)` is the exact derivative-denominator norm identity. -/
theorem endpointDiscriminantCongruence_from_normalizedDerivative
    (hres : residueDegree F K = 1)
    (A c upper : Fˣ) (a : unitGroup F)
    (haCoe : ((a : unitGroup F) : Fˣ) = c / A)
    (haResidue : (((residueUnits F a : (ResidueField F)ˣ) : ResidueField F) ^
        (Module.finrank F K - 1)) =
      endpointNormalizedDerivativeCriticalLambda F K n ht pi hpi hgen hres ^
        (Module.finrank F K * (Module.finrank F K - 1)))
    (hupper : upper =
      A ^ (Module.finrank F K - 1) *
        ((endpointNormalizedDerivativeNormLocalUnit F K n ht pi hpi hgen :
          unitGroup F) : Fˣ)) :
    upper / (((-1 : Fˣ) ^ Module.finrank F K) *
        c ^ (Module.finrank F K - 1)) ∈ unitFiltration F 1 := by
  have hD := endpointNormalizedDerivativeNorm_div_stationaryPower_mem_one
    F K n ht pi hpi hgen hres a haResidue
  convert hD using 1
  simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_pow,
    endpointNegOneLocalUnit_coe]
  rw [hupper, haCoe]
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
  ac_rfl

end EndpointDerivativeNormResidue
section EndpointDerivativeNormIdentity

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
variable {s : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K (s + 1))
  (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

/-- The exact unit identity behind the endpoint discriminant congruence:
`N(gamma_K)/gamma_F = (pi_F^t gamma_F)^(p-1) N(D)`. -/
theorem endpointDerivativeGamma_norm_identity
    (chi : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (gammaF : AdmissibleGamma F chi psi) :
    normUnits F K
          (endpointDerivativeGammaUnit F K ht piK hpiK hgen chi psi gammaF) /
        (gammaF : Fˣ) =
      ((wildLowerUniformizer F K piK hpiK) ^ (s + 1) * (gammaF : Fˣ)) ^
          (Module.finrank F K - 1) *
        ((endpointNormalizedDerivativeNormLocalUnit
          F K s ht piK hpiK hgen : unitGroup F) : Fˣ) := by
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul, coe_normUnits]
  change norm F K
      (algebraMap F K (((gammaF : Fˣ) : F)) * endpointDerivative F K piK /
        (piK : K) ^ (Module.finrank F K - 1)) /
      (((gammaF : Fˣ) : F)) =
    ((norm F K (piK : K)) ^ (s + 1) * (((gammaF : Fˣ) : F))) ^
        (Module.finrank F K - 1) *
      norm F K (endpointNormalizedDerivative F K s ht piK hpiK hgen : K)
  simp only [div_eq_mul_inv]
  rw [map_mul, map_mul, norm_algebraMap, Algebra.norm_inv, map_pow]
  rw [endpointNormalizedDerivative_field_eq F K s ht piK hpiK hgen]
  simp only [div_eq_mul_inv]
  rw [map_mul, Algebra.norm_inv, map_pow]
  have hp : 0 < Module.finrank F K := Module.finrank_pos
  have hpi : norm F K (piK : K) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hpiK.ne_zero
  have hgamma : (((gammaF : Fˣ) : F)) ≠ 0 := gammaF.coe_ne_zero
  have hder : endpointDerivative F K piK ≠ 0 :=
    endpointDerivative_ne_zero F K ht piK hpiK hgen
  field_simp
  have hgammaPow : (((gammaF : Fˣ) : F)) ^ Module.finrank F K =
      (((gammaF : Fˣ) : F)) ^ (Module.finrank F K - 1) *
        (((gammaF : Fˣ) : F)) := by
    calc
      _ = (((gammaF : Fˣ) : F)) ^ (Module.finrank F K - 1 + 1) := by
        congr 1
        omega
      _ = _ := pow_succ _ _
  have hpiPow : norm F K (piK : K) ^
        ((Module.finrank F K - 1) * (s + 2)) =
      norm F K (piK : K) ^ (Module.finrank F K - 1) *
        norm F K (piK : K) ^ ((s + 1) * (Module.finrank F K - 1)) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hgammaPow, hpiPow]
  ring

end EndpointDerivativeNormIdentity
section EndpointNormCharacterFactors

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (htpos : 0 < t) (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

local notation "p" => Module.finrank F K

local instance endpointFactorDegreeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance endpointFactorDegreeNeZero : NeZero p :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

include ht htpos hres piK hpiK hgen

/-- A representative of the generator stationary class is nonzero, by its
exact order zero. -/
theorem endpointTauRepresentative_ne_zero
    (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hbreak : t + 1 = 2 * d + epsilon)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (cTau : lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (hcTau :
      let thetaTau := endpointTauData F K ht hres piK hpiK hgen
      let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
        (by change t + 1 = 2 * d + epsilon; exact hbreak)
        (by change 1 < t + 1; omega)
      latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)) cTau =
        stationaryNumeratorClass F thetaTau psi ((t + 1 : ℕ) : ℤ)
          hrTau Gamma (by simpa using hGamma)) :
    (cTau : F) ≠ 0 := by
  let thetaTau := endpointTauData F K ht hres piK hpiK hgen
  let hthetaTau : thetaTau.conductor = 2 * d + epsilon := by
    simp only [thetaTau, endpointTauData_conductor]
    omega
  let hlargeTau : 1 < thetaTau.conductor := by
    simp only [thetaTau, endpointTauData_conductor]
    omega
  let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
    hthetaTau hlargeTau
  apply (ord_ne_top_iff F).1
  rw [stationaryNumeratorClass_representative_ord F thetaTau psi
    ((t + 1 : ℕ) : ℤ) hrTau Gamma (by simpa using hGamma) cTau hcTau]
  simp

/-- Reciprocal stationary factor attached to a norm character.  The
identity branch is explicit; every nonidentity branch uses its canonical
cyclic index and the scalar multiple of `b_tau`. -/
noncomputable def endpointNormCharacterReciprocalFactor
    (Gamma : Fˣ) (bTau : F) (hbTau : bTau ≠ 0)
    (mu : NormCharacter F K) : Fˣ := by
  classical
  by_cases hmu : mu = 1
  · exact 1
  · exact Gamma /
      endpointScaledStationaryUnit F bTau hbTau
        (endpointNormCharacterIndex F K ht hres piK hpiK hgen mu)

@[simp] theorem endpointNormCharacterReciprocalFactor_one
    (Gamma : Fˣ) (bTau : F) (hbTau : bTau ≠ 0) :
    endpointNormCharacterReciprocalFactor F K ht hres piK hpiK hgen
      Gamma bTau hbTau 1 = 1 := by
  simp [endpointNormCharacterReciprocalFactor]

theorem endpointNormCharacterReciprocalFactor_ne_one
    (Gamma : Fˣ) (bTau : F) (hbTau : bTau ≠ 0)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    endpointNormCharacterReciprocalFactor F K ht hres piK hpiK hgen
      Gamma bTau hbTau mu =
      Gamma / endpointScaledStationaryUnit F bTau hbTau
        (endpointNormCharacterIndex F K ht hres piK hpiK hgen mu) := by
  simp [endpointNormCharacterReciprocalFactor, hmu]

/-- The complete nontrivial factor product has the Wilson sign and the
single generator reciprocal, with exact quotient direction. -/
theorem endpointNormCharacterReciprocalFactor_product_mod_one
    (Gamma : Fˣ) (bTau : F) (hbTau : bTau ≠ 0) :
    ((endpointNontrivialNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (endpointNormCharacterReciprocalFactor
          F K ht hres piK hpiK hgen Gamma bTau hbTau)) /
      (((-1 : Fˣ) ^ p) *
        (Gamma / Units.mk0 bTau hbTau) ^ (p - 1)) ∈
      unitFiltration F 1 := by
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos piK hpiK hgen
  rw [ramifiedNontrivialProduct_eq_IcoProduct
    F K ht hres piK hpiK hgen]
  have hprod := endpointReciprocalFactorProduct_mod_one F Gamma
    (Units.mk0 bTau hbTau)
    (fun j ↦ endpointScaledStationaryUnit F bTau hbTau j)
    (by
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      exact endpointScaledStationaryUnit_eq_mul F bTau hbTau hj'.1 hj'.2)
  rw [hchar] at hprod
  convert hprod using 1
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  let mu := ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen
    (Multiplicative.ofAdd (j : ZMod p))
  have hmu : mu ≠ 1 :=
    endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hj'.1 hj'.2
  rw [endpointNormCharacterReciprocalFactor_ne_one
    F K ht htpos hres piK hpiK hgen Gamma bTau hbTau mu hmu]
  congr 2
  simp [endpointNormCharacterIndex, mu, ZMod.val_cast_of_lt hj'.2]

end EndpointNormCharacterFactors
section

variable (F K : Type) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
variable {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (htpos : 0 < t) (hres : residueDegree F K = 1)
  (piK : ringOfIntegers K)
  (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
  (hgen : Algebra.adjoin (ringOfIntegers F) ({piK} : Set (ringOfIntegers K)) = ⊤)

local notation "p" => Module.finrank F K

local instance bridgeDegreeFact : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

local instance bridgeDegreeNeZero : NeZero p :=
  ⟨(PrimeCyclicExtension.degree_prime F K).ne_zero⟩

/-- Stable twisting for an actual nontrivial norm character, with its
factor identified with the reciprocal-factor family used in the product. -/
theorem endpointNormCharacter_stableTwistFactor_explicit
    (chi : LocalQuasiCharData F) (hchi : chi.conductor = 1)
    (psi : LocalAddCharData F)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hbreak : t + 1 = 2 * d + epsilon)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (gammaChi : AdmissibleGamma F chi psi)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psi)
    (cTau : lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (hcTau :
      let thetaTau := endpointTauData F K ht hres piK hpiK hgen
      let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
        (by change t + 1 = 2 * d + epsilon; exact hbreak)
        (by change 1 < t + 1; omega)
      latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)) cTau =
        stationaryNumeratorClass F thetaTau psi ((t + 1 : ℕ) : ℤ)
          hrTau Gamma (by simpa using hGamma))
    (hcTau0 : (cTau : F) ≠ 0)
    (mu : NormCharacter F K) (hmu : mu ≠ 1) :
    deltaFinite
        (wildEndpointOneTwistData F K ht htpos hres piK hpiK hgen
          chi hchi mu) psi
        (wildEndpointOneTwistGamma F K ht htpos hres piK hpiK hgen
          chi hchi psi gammaChi gammaNorm mu) =
      (chi.character
        (endpointNormCharacterReciprocalFactor
          F K ht hres piK hpiK hgen Gamma (cTau : F) hcTau0 mu) : ℂ) *
        deltaFinite
          (wildNormCharacterData F K ht hres piK hpiK hgen mu)
          psi (gammaNorm mu) := by
  let j := endpointNormCharacterIndex F K ht hres piK hpiK hgen mu
  have hjpos : 0 < j :=
    endpointNormCharacterIndex_pos F K ht hres piK hpiK hgen mu hmu
  have hjlt : j < p :=
    endpointNormCharacterIndex_lt F K ht hres piK hpiK hgen mu
  let hmuJ := endpoint_enum_nat_ne_one F K ht hres piK hpiK hgen hjpos hjlt
  let thetaJ := endpointIndexedNormData F K ht hres piK hpiK hgen j hmuJ
  let hthetaJ : thetaJ.conductor = 2 * d + epsilon := by
    change t + 1 = 2 * d + epsilon
    exact hbreak
  let hlargeJ : 1 < thetaJ.conductor := by
    change 1 < t + 1
    omega
  let hrJ := stableTwist_stationaryDepth F thetaJ d epsilon hepsilon
    hthetaJ hlargeJ
  let gammaJ : AdmissibleGamma F thetaJ psi := ⟨Gamma, by
    change ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psi.conductor : ℤ) : WithTop ℤ)
    exact hGamma⟩
  let cJ : lattice F
      ((thetaJ.conductor : ℤ) - (thetaJ.conductor : ℤ)) :=
    (j : ℤ) • cTau
  let hcJ : latticeQuotientMk F
        (sub_le_sub_left hrJ.int_le_conductor (thetaJ.conductor : ℤ)) cJ =
      stationaryNumeratorClass F thetaJ psi (thetaJ.conductor : ℤ)
        hrJ gammaJ gammaJ.property := by
    exact endpointIndexed_stationaryRepresentative
      F K ht hres piK hpiK hgen htpos psi d epsilon hepsilon hbreak
        Gamma hGamma cTau hcTau hjpos hjlt
  let hcond : chi.conductor < thetaJ.conductor := by
    change chi.conductor < t + 1
    rw [hchi]
    omega
  have hidx := endpointIndexed_stableTwistFactor
    F K ht hres piK hpiK hgen htpos chi hchi psi d epsilon hepsilon hbreak
      Gamma hGamma cTau hcTau hjpos hjlt
  have hchar : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K ht htpos piK hpiK hgen
  have hunit :
      stableStationaryRepresentativeUnit F thetaJ psi hrJ gammaJ cJ hcJ =
        endpointScaledStationaryUnit F (cTau : F) hcTau0 j := by
    apply Units.ext
    rw [stableStationaryRepresentativeUnit_coe,
      endpointScaledStationaryUnit_coe F (cTau : F) hcTau0 hjpos]
    · dsimp only [cJ]
      change (j : ℤ) • (cTau : F) = (j : F) * (cTau : F)
      rw [zsmul_eq_mul, Int.cast_natCast]
    · simpa [hchar] using hjlt
  have hthetaChar :
      thetaJ.character =
        (wildNormCharacterData F K ht hres piK hpiK hgen mu).character := by
    rw [wildNormCharacterData_character]
    change
      ((ramifiedNormCharacterZModEquiv F K ht hres piK hpiK hgen)
        (Multiplicative.ofAdd (j : ZMod p))).1 = mu.1
    exact congrArg (fun nu : NormCharacter F K => nu.1)
      (endpoint_enum_index F K ht hres piK hpiK hgen mu)
  have hdeltaTheta :
      deltaFinite thetaJ psi gammaJ =
        deltaFinite (wildNormCharacterData F K ht hres piK hpiK hgen mu)
          psi (gammaNorm mu) :=
    endpointDeltaFinite_eq_of_character_eq
      F K ht htpos hres piK hpiK hgen thetaJ
        (wildNormCharacterData F K ht hres piK hpiK hgen mu)
        hthetaChar psi gammaJ (gammaNorm mu)
  have htwistChar :
      (stableTwistData F chi thetaJ hcond).character =
        (wildEndpointOneTwistData F K ht htpos hres piK hpiK hgen
          chi hchi mu).character := by
    rw [stableTwistData_character,
      wildEndpointOneTwistData_character, hthetaChar,
      wildNormCharacterData_character]
    exact mul_comm chi.character mu.1
  have hdeltaTwist :
      deltaFinite (stableTwistData F chi thetaJ hcond) psi
          (stableTwistAdmissibleGamma F chi thetaJ psi hcond gammaJ) =
        deltaFinite
          (wildEndpointOneTwistData F K ht htpos hres piK hpiK hgen
            chi hchi mu) psi
          (wildEndpointOneTwistGamma F K ht htpos hres piK hpiK hgen
            chi hchi psi gammaChi gammaNorm mu) :=
    endpointDeltaFinite_eq_of_character_eq
      F K ht htpos hres piK hpiK hgen
        (stableTwistData F chi thetaJ hcond)
        (wildEndpointOneTwistData F K ht htpos hres piK hpiK hgen
          chi hchi mu) htwistChar psi
        (stableTwistAdmissibleGamma F chi thetaJ psi hcond gammaJ)
        (wildEndpointOneTwistGamma F K ht htpos hres piK hpiK hgen
          chi hchi psi gammaChi gammaNorm mu)
  rw [← hdeltaTwist]
  rw [hidx]
  rw [hdeltaTheta]
  rw [hunit]
  rw [endpointNormCharacterReciprocalFactor_ne_one
    F K ht htpos hres piK hpiK hgen Gamma (cTau : F) hcTau0 mu hmu]

/-- The two public names for the nonidentity norm-character set are the
same erased complete finite group. -/
theorem endpointNontrivialNormCharacterFinset_eq_wild :
    endpointNontrivialNormCharacterFinset F K ht hres piK hpiK hgen =
      wildEndpointOneNontrivialNormCharacterFinset
        F K ht hres piK hpiK hgen := by
  rfl

/-- Cancels the common Wilson-normalized target, preserving the audited
quotient direction from the endpoint discriminant to the factor product. -/
theorem endpointNormCharacterDiscriminantBridge
    (htwild : 0 < t)
    (Gamma : Fˣ) (bTau : F) (hbTau : bTau ≠ 0) (upper : Fˣ)
    (hupper :
      upper /
          (((-1 : Fˣ) ^ p) *
            (Gamma / Units.mk0 bTau hbTau) ^ (p - 1)) ∈
        unitFiltration F 1) :
    upper /
        (wildEndpointOneNontrivialNormCharacterFinset
          F K ht hres piK hpiK hgen).prod
          (endpointNormCharacterReciprocalFactor
            F K ht hres piK hpiK hgen Gamma bTau hbTau) ∈
      unitFiltration F 1 := by
  have hproduct := endpointNormCharacterReciprocalFactor_product_mod_one
    F K ht htwild hres piK hpiK hgen Gamma bTau hbTau
  rw [endpointNontrivialNormCharacterFinset_eq_wild
    F K ht hres piK hpiK hgen] at hproduct
  have hquot := (unitFiltration F 1).div_mem hupper hproduct
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hquot

/-- Final conductor-one product assembly with the explicit reciprocal
factor family.  Thus the only remaining input is the audited discriminant
congruence in the direction `upper / factorProduct ∈ U^1`. -/
theorem wildEndpointOne_productAssembly_explicit
    (chiF : LocalQuasiCharData F) (hchiF : chiF.conductor = 1)
    (chiK : LocalQuasiCharData K) (psiF : LocalAddCharData F)
    (psiK : LocalAddCharData K)
    (gammaF : AdmissibleGamma F chiF psiF)
    (gammaK : AdmissibleGamma K chiK psiK)
    (gammaNorm : ∀ mu : NormCharacter F K,
      AdmissibleGamma F
        (wildNormCharacterData F K ht hres piK hpiK hgen mu) psiF)
    (d epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hbreak : t + 1 = 2 * d + epsilon)
    (Gamma : Fˣ)
    (hGamma : ord F (Gamma : F) =
      ((((t + 1 : ℕ) : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (cTau : lattice F (((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)))
    (hcTau :
      let thetaTau := endpointTauData F K ht hres piK hpiK hgen
      let hrTau := stableTwist_stationaryDepth F thetaTau d epsilon hepsilon
        (by change t + 1 = 2 * d + epsilon; exact hbreak)
        (by change 1 < t + 1; omega)
      latticeQuotientMk F
          (sub_le_sub_left hrTau.int_le_conductor ((t + 1 : ℕ) : ℤ)) cTau =
        stationaryNumeratorClass F thetaTau psiF ((t + 1 : ℕ) : ℤ)
          hrTau Gamma (by simpa using hGamma))
    (hcTau0 : (cTau : F) ≠ 0)
    (hupper :
      deltaFinite chiK psiK gammaK =
        (chiF.character
          (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) : ℂ) *
          deltaFinite chiF psiF gammaF)
    (hdiscriminant :
      (normUnits F K (gammaK : Kˣ) / (gammaF : Fˣ)) /
          (wildEndpointOneNontrivialNormCharacterFinset
            F K ht hres piK hpiK hgen).prod
            (endpointNormCharacterReciprocalFactor
              F K ht hres piK hpiK hgen Gamma (cTau : F) hcTau0) ∈
        unitFiltration F 1) :
    deltaFinite chiK psiK gammaK *
        (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
          (fun mu => deltaFinite
            (wildNormCharacterData F K ht hres piK hpiK hgen mu)
            psiF (gammaNorm mu)) =
      (ramifiedNormCharacterFinset F K ht hres piK hpiK hgen).prod
        (fun mu => deltaFinite
          (wildEndpointOneTwistData F K ht htpos hres piK hpiK hgen
            chiF hchiF mu) psiF
          (wildEndpointOneTwistGamma F K ht htpos hres piK hpiK hgen
            chiF hchiF psiF gammaF gammaNorm mu)) := by
  apply wildEndpointOne_productAssembly
    F K ht htpos hres piK hpiK hgen chiF hchiF chiK psiF psiK
      gammaF gammaK gammaNorm
      (endpointNormCharacterReciprocalFactor
        F K ht hres piK hpiK hgen Gamma (cTau : F) hcTau0)
      hupper hdiscriminant
  intro mu hmu
  exact endpointNormCharacter_stableTwistFactor_explicit
    F K ht htpos hres piK hpiK hgen chiF hchiF psiF d epsilon
      hepsilon hbreak Gamma hGamma gammaF gammaNorm cTau hcTau hcTau0 mu hmu

end

end

end LanglandsFirstMainLemma
