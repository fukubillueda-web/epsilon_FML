import LanglandsFirstMainLemma.Ramification.Different
import LanglandsFirstMainLemma.Ramification.TraceIdeals
import LanglandsFirstMainLemma.Ramification.NormAboveBreak
import LanglandsFirstMainLemma.Ramification.NormBelowBreak

/-!
# The cyclic-prime norm filtration

This file assembles the four independent ramification calculations used in the manuscript's
norm-filtration theorem.  The integral inverse Herbrand function is always read from an upper
target depth to a lower source depth.  Thus the source of the graded norm at upper depth `r` is
`U_K^(Psi(r)) / U_K^(Psi(r)+1)`; above the break its denominator is deliberately not
`U_K^(Psi(r+1))`.

Below the break the full norm image is not the whole target unit layer.  It is described
exactly by its join and intersection with the critical layer.  At the break it is the inverse
image of the range of the critical graded norm, whose kernel and cokernel both have the prime
extension degree.  Strictly above the break the two full norm images are equal to the stated
target layers.
-/

namespace LanglandsFirstMainLemma

noncomputable section

section QuotientGlue

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The two filtration-containment predicates used by the independently proved below- and
above-break modules have the same mathematical content. -/
theorem normMapsUnitFiltration_iff_aboveBreak
    (sourceDepth targetDepth : ℕ) :
    NormMapsUnitFiltration F K sourceDepth targetDepth ↔
      AboveBreakNormMapsUnitFiltration F K sourceDepth targetDepth :=
  Iff.rfl

/-- Norm on quotient layers commutes with the canonical projections obtained by deepening
both denominators.  This is the below-break and critical analogue of the heterogeneous
projection square proved in `NormAboveBreak`. -/
theorem normUnitFiltrationQuotient_projection
    {sourceNumerator sourceDenominator₁ sourceDenominator₂
      targetNumerator targetDenominator₁ targetDenominator₂ : ℕ}
    (hsource₁ : sourceNumerator ≤ sourceDenominator₁)
    (hsource₁₂ : sourceDenominator₁ ≤ sourceDenominator₂)
    (htarget₁ : targetNumerator ≤ targetDenominator₁)
    (htarget₁₂ : targetDenominator₁ ≤ targetDenominator₂)
    (hnum : NormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden₁ : NormMapsUnitFiltration F K sourceDenominator₁ targetDenominator₁)
    (hden₂ : NormMapsUnitFiltration F K sourceDenominator₂ targetDenominator₂) :
    (unitFiltrationQuotientProjection F htarget₁ htarget₁₂).comp
        (normUnitFiltrationQuotient F K
          (hsource₁.trans hsource₁₂) (htarget₁.trans htarget₁₂) hnum hden₂) =
      (normUnitFiltrationQuotient F K hsource₁ htarget₁ hnum hden₁).comp
        (unitFiltrationQuotientProjection K hsource₁ hsource₁₂) := by
  ext z
  rfl

/-- The heterogeneous above-break quotient projection square, re-exported as part of the
assembled norm-filtration API. -/
theorem cyclicPrimeAboveBreakQuotient_projection
    {sourceNumerator sourceDenominator₁ sourceDenominator₂
      targetNumerator targetDenominator₁ targetDenominator₂ : ℕ}
    (hsource₁ : sourceNumerator ≤ sourceDenominator₁)
    (hsource₁₂ : sourceDenominator₁ ≤ sourceDenominator₂)
    (htarget₁ : targetNumerator ≤ targetDenominator₁)
    (htarget₁₂ : targetDenominator₁ ≤ targetDenominator₂)
    (hnum : AboveBreakNormMapsUnitFiltration F K sourceNumerator targetNumerator)
    (hden₁ : AboveBreakNormMapsUnitFiltration F K sourceDenominator₁ targetDenominator₁)
    (hden₂ : AboveBreakNormMapsUnitFiltration F K sourceDenominator₂ targetDenominator₂) :
    (unitFiltrationQuotientProjection F htarget₁ htarget₁₂).comp
        (aboveBreakNormUnitFiltrationQuotient F K
          (hsource₁.trans hsource₁₂) (htarget₁.trans htarget₁₂) hnum hden₂) =
      (aboveBreakNormUnitFiltrationQuotient F K hsource₁ htarget₁ hnum hden₁).comp
        (unitFiltrationQuotientProjection K hsource₁ hsource₁₂) :=
  aboveBreakNormUnitFiltrationQuotient_projection F K
    hsource₁ hsource₁₂ htarget₁ htarget₁₂ hnum hden₁ hden₂

end QuotientGlue

section PrimeCyclicAssembly

variable (F K : Type*) [Field F] [Field K]
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

/-- At every upper depth, norm maps the inverse-Herbrand source layer into the corresponding
target layer.  For `r ≤ t` this is the same-numbered below-break containment; for `t < r` it
is the heterogeneous above-break containment. -/
theorem normMapsUnitFiltration_herbrand (r : ℕ) :
    NormMapsUnitFiltration F K
      (herbrandPsiNat t (Module.finrank F K) r) r := by
  rcases le_or_gt r t with hrt | htr
  · rw [herbrandPsiNat_of_le_break t (Module.finrank F K) hrt]
    exact normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen
  · exact (normMapsUnitFiltration_iff_aboveBreak F K _ _).2
      (by simpa only [aboveBreakSourceDepth] using
        normMapsUnitFiltration_aboveBreakCanonical F K ht htr hres pi hpi hgen)

/-- The adjacent denominator containment is valid at every depth.  The proof has three
disjoint cases: `r < t`, `r = t`, and `t < r`; the middle case is exactly the critical
`t+1` endpoint. -/
theorem normMapsUnitFiltration_herbrand_succ (r : ℕ) :
    NormMapsUnitFiltration F K
      (herbrandPsiNat t (Module.finrank F K) r + 1) (r + 1) := by
  rcases lt_trichotomy r t with hrt | rfl | htr
  · rw [herbrandPsiNat_of_le_break t (Module.finrank F K) hrt.le]
    exact normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen
  · rw [herbrandPsiNat_break]
    exact normMapsUnitFiltration_break_succ F K ht hres pi hpi hgen
  · exact (normMapsUnitFiltration_iff_aboveBreak F K _ _).2
      (by simpa only [aboveBreakSourceDepth] using
        normMapsUnitFiltration_aboveBreakCanonical_succ F K ht htr hres pi hpi hgen)

/-- The norm-induced map on the graded line at every upper depth.  Its source is always the
lower depth `Psi(r)` and its denominator is exactly `Psi(r)+1`. -/
noncomputable def cyclicPrimeGradedNorm (r : ℕ) :
    UnitFiltrationQuotient K
        (herbrandPsiNat t (Module.finrank F K) r)
        (herbrandPsiNat t (Module.finrank F K) r + 1)
        (Nat.le_succ _) →*
      UnitGradedPiece F r :=
  normUnitFiltrationQuotient F K (Nat.le_succ _) (Nat.le_succ r)
    (normMapsUnitFiltration_herbrand F K ht hres pi hpi hgen r)
    (normMapsUnitFiltration_herbrand_succ F K ht hres pi hpi hgen r)

@[simp]
theorem cyclicPrimeGradedNorm_mk (r : ℕ)
    (u : unitFiltration K (herbrandPsiNat t (Module.finrank F K) r)) :
    cyclicPrimeGradedNorm F K ht hres pi hpi hgen r
        (unitFiltrationQuotientMk K (Nat.le_succ _) u) =
      unitGradedMk F r
        (normBelowBreakUnitFiltrationHom F K
          (herbrandPsiNat t (Module.finrank F K) r) r
          (normMapsUnitFiltration_herbrand F K ht hres pi hpi hgen r) u) :=
  rfl

/-- Strictly below the break, the all-depth inverse-Herbrand graded norm is bijective.
The proof is only the dependent transport from `Psi(r) = r`; the graded norm argument itself
is the theorem from `NormBelowBreak`. -/
theorem cyclicPrimeGradedNorm_bijective_belowBreak
    {r : ℕ} (hrt : r < t) :
    Function.Bijective
      (cyclicPrimeGradedNorm F K ht hres pi hpi hgen r) := by
  have hpsi : herbrandPsiNat t (Module.finrank F K) r = r :=
    herbrandPsiNat_of_le_break t (Module.finrank F K) hrt.le
  have hgraded := gradedNorm_bijective_belowBreak F K ht hrt hres pi hpi hgen
  constructor
  · intro x y hxy
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective K (Nat.le_succ _) x
    obtain ⟨v, rfl⟩ := unitFiltrationQuotientMk_surjective K (Nat.le_succ _) y
    let u_r : unitFiltration K r := ⟨u, by simpa only [hpsi] using u.property⟩
    let v_r : unitFiltration K r := ⟨v, by simpa only [hpsi] using v.property⟩
    have hgradedEq :
        normUnitGraded F K r
            (normMapsUnitFiltration_belowBreak F K ht hrt.le hres pi hpi hgen)
            (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)
            (unitGradedMk K r u_r) =
          normUnitGraded F K r
            (normMapsUnitFiltration_belowBreak F K ht hrt.le hres pi hpi hgen)
            (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)
            (unitGradedMk K r v_r) := by
      calc
        _ = cyclicPrimeGradedNorm F K ht hres pi hpi hgen r
              (unitFiltrationQuotientMk K (Nat.le_succ _) u) := by
                rw [normUnitGraded_mk, cyclicPrimeGradedNorm_mk]
                congr 1
        _ = cyclicPrimeGradedNorm F K ht hres pi hpi hgen r
              (unitFiltrationQuotientMk K (Nat.le_succ _) v) := hxy
        _ = normUnitGraded F K r
              (normMapsUnitFiltration_belowBreak F K ht hrt.le hres pi hpi hgen)
              (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen)
              (unitGradedMk K r v_r) := by
                rw [normUnitGraded_mk, cyclicPrimeGradedNorm_mk]
                congr 1
    have hquotient := hgraded.1 hgradedEq
    apply (unitFiltrationQuotientMk_eq_mk_iff K (Nat.le_succ _) u v).2
    have hdeep :=
      (unitFiltrationQuotientMk_eq_mk_iff K (Nat.le_succ r) u_r v_r).1 hquotient
    simpa only [hpsi] using hdeep
  · intro z
    obtain ⟨x, hx⟩ := hgraded.2 z
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective K (Nat.le_succ r) x
    let u_psi : unitFiltration K (herbrandPsiNat t (Module.finrank F K) r) :=
      ⟨u, by simpa only [hpsi] using u.property⟩
    refine ⟨unitFiltrationQuotientMk K (Nat.le_succ _) u_psi, ?_⟩
    rw [cyclicPrimeGradedNorm_mk]
    change unitGradedMk F r
      (normBelowBreakUnitFiltrationHom F K r r
        (normMapsUnitFiltration_belowBreak F K ht hrt.le hres pi hpi hgen) u) = z at hx
    rw [← hx]
    congr 1

/-- At the break, the all-depth graded norm has exactly the canonical critical range. -/
theorem cyclicPrimeGradedNorm_range_atBreak :
    (cyclicPrimeGradedNorm F K ht hres pi hpi hgen t).range =
      (criticalGradedNorm F K ht hres pi hpi hgen).range := by
  have hpsi : herbrandPsiNat t (Module.finrank F K) t = t :=
    herbrandPsiNat_break t (Module.finrank F K)
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨u, rfl⟩ := unitFiltrationQuotientMk_surjective K (Nat.le_succ _) z
    let u_t : unitFiltration K t := ⟨u, by simpa only [hpsi] using u.property⟩
    refine ⟨unitGradedMk K t u_t, ?_⟩
    rw [criticalGradedNorm_mk, cyclicPrimeGradedNorm_mk]
    congr 1
  · rintro _ ⟨z, rfl⟩
    obtain ⟨u, rfl⟩ := unitGradedMk_surjective K t z
    let u_psi : unitFiltration K (herbrandPsiNat t (Module.finrank F K) t) :=
      ⟨u, by simpa only [hpsi] using u.property⟩
    refine ⟨unitFiltrationQuotientMk K (Nat.le_succ _) u_psi, ?_⟩
    rw [criticalGradedNorm_mk, cyclicPrimeGradedNorm_mk]
    congr 1

/-- Strictly above the break, the all-depth inverse-Herbrand graded norm is bijective. -/
theorem cyclicPrimeGradedNorm_bijective_aboveBreak
    {r : ℕ} (htr : t < r) :
    Function.Bijective
      (cyclicPrimeGradedNorm F K ht hres pi hpi hgen r) := by
  change Function.Bijective
    (normGradedAboveBreakCanonical F K ht htr hres pi hpi hgen)
  exact norm_graded_bijective_above_break F K ht htr hres pi hpi hgen

/-- Norm on arbitrary inverse-Herbrand-indexed filtration quotients. -/
noncomputable def cyclicPrimeNormFiltrationQuotient
    {r s : ℕ} (hrs : r ≤ s) :
    UnitFiltrationQuotient K
        (herbrandPsiNat t (Module.finrank F K) r)
        (herbrandPsiNat t (Module.finrank F K) s)
        (herbrandPsiNat_monotone t (Module.finrank F K)
          (PrimeCyclicExtension.degree_prime F K).pos hrs) →*
      UnitFiltrationQuotient F r s hrs :=
  normUnitFiltrationQuotient F K
    (herbrandPsiNat_monotone t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos hrs)
    hrs
    (normMapsUnitFiltration_herbrand F K ht hres pi hpi hgen r)
    (normMapsUnitFiltration_herbrand F K ht hres pi hpi hgen s)

@[simp]
theorem cyclicPrimeNormFiltrationQuotient_mk
    {r s : ℕ} (hrs : r ≤ s)
    (u : unitFiltration K (herbrandPsiNat t (Module.finrank F K) r)) :
    cyclicPrimeNormFiltrationQuotient F K ht hres pi hpi hgen hrs
        (unitFiltrationQuotientMk K
          (herbrandPsiNat_monotone t (Module.finrank F K)
            (PrimeCyclicExtension.degree_prime F K).pos hrs) u) =
      unitFiltrationQuotientMk F hrs
        (normBelowBreakUnitFiltrationHom F K
          (herbrandPsiNat t (Module.finrank F K) r) r
          (normMapsUnitFiltration_herbrand F K ht hres pi hpi hgen r) u) :=
  rfl

/-- The inverse-Herbrand quotient maps commute with deepening the denominator. -/
theorem cyclicPrimeNormFiltrationQuotient_projection
    {r s₁ s₂ : ℕ} (hrs₁ : r ≤ s₁) (hs₁s₂ : s₁ ≤ s₂) :
    (unitFiltrationQuotientProjection F hrs₁ hs₁s₂).comp
        (cyclicPrimeNormFiltrationQuotient F K ht hres pi hpi hgen
          (hrs₁.trans hs₁s₂)) =
      (cyclicPrimeNormFiltrationQuotient F K ht hres pi hpi hgen hrs₁).comp
        (unitFiltrationQuotientProjection K
          (herbrandPsiNat_monotone t (Module.finrank F K)
            (PrimeCyclicExtension.degree_prime F K).pos hrs₁)
          (herbrandPsiNat_monotone t (Module.finrank F K)
            (PrimeCyclicExtension.degree_prime F K).pos hs₁s₂)) := by
  ext z
  rfl

omit ht hres pi hpi hgen in
/-- `Psi(r)+1` is at most the next inverse-Herbrand level.  Above the break the inequality is
strict, which keeps the graded denominator distinct from `Psi(r+1)`. -/
theorem herbrandPsiNat_add_one_le_succ (r : ℕ) :
    herbrandPsiNat t (Module.finrank F K) r + 1 ≤
      herbrandPsiNat t (Module.finrank F K) (r + 1) :=
  Nat.succ_le_of_lt
    (herbrandPsiNat_strictMono t (Module.finrank F K)
      (PrimeCyclicExtension.degree_prime F K).pos (Nat.lt_succ_self r))

/-- The quotient from upper depth `r` to `r+1` is the graded norm after projecting the
source denominator from `Psi(r+1)` to `Psi(r)+1`. -/
theorem cyclicPrimeNormFiltrationQuotient_succ
    (r : ℕ) :
    cyclicPrimeNormFiltrationQuotient F K ht hres pi hpi hgen (Nat.le_succ r) =
      (cyclicPrimeGradedNorm F K ht hres pi hpi hgen r).comp
        (unitFiltrationQuotientProjection K (Nat.le_succ _)
          (herbrandPsiNat_add_one_le_succ F K r)) := by
  ext z
  rfl

/-- The endpoint needed to pass from the critical graded range to the full critical norm
image: every element of `U_F^(t+1)` is the exact norm of an element already in
`U_K^(t+1)`.  The tame (`t=0`) and positive-break constructions are joined only here. -/
theorem norm_unitFiltration_surjective_break_succ :
    ∀ u : Fˣ, u ∈ unitFiltration F (t + 1) →
      ∃ x : Kˣ, x ∈ unitFiltration K (t + 1) ∧ normUnits F K x = u := by
  by_cases ht0 : t = 0
  · subst t
    simpa only [zero_add] using
      tame_norm_unitFiltration_surjective_break_succ F K ht hres pi hpi hgen
  · exact wild_norm_unitFiltration_surjective_break_succ F K ht
      (Nat.pos_of_ne_zero ht0) hres pi hpi hgen

/-- Elementwise exact-image form of the critical successor endpoint. -/
theorem mem_unitFiltration_break_succ_iff_exists_norm (u : Fˣ) :
    u ∈ unitFiltration F (t + 1) ↔
      ∃ x : Kˣ, x ∈ unitFiltration K (t + 1) ∧ normUnits F K x = u := by
  constructor
  · exact norm_unitFiltration_surjective_break_succ F K ht hres pi hpi hgen u
  · rintro ⟨x, hx, rfl⟩
    exact normMapsUnitFiltration_break_succ F K ht hres pi hpi hgen x hx

/-- Exact critical-successor image equality. -/
theorem norm_unitFiltration_map_eq_break_succ :
    Subgroup.map (normUnits F K) (unitFiltration K (t + 1)) =
      unitFiltration F (t + 1) := by
  ext u
  rw [Subgroup.mem_map]
  exact (mem_unitFiltration_break_succ_iff_exists_norm F K ht hres pi hpi hgen u).symm

/-- The full critical image inside `U_F^t`: it is the inverse image of the actual range of
the critical graded norm under `U_F^t → U_F^t/U_F^(t+1)`. -/
noncomputable def criticalNormTargetImage : Subgroup (unitFiltration F t) :=
  (criticalGradedNorm F K ht hres pi hpi hgen).range.comap (unitGradedMk F t)

/-- Exact full critical image in the target unit subgroup.  The reverse inclusion is where
the exact `t+1` lifting theorem is used; a graded-range representative alone would give only
an inclusion modulo `U_F^(t+1)`. -/
theorem norm_unitFiltration_range_eq_criticalNormTargetImage :
    (normBelowBreakUnitFiltrationHom F K t t
      (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)).range =
      criticalNormTargetImage F K ht hres pi hpi hgen := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change unitGradedMk F t
      (normBelowBreakUnitFiltrationHom F K t t
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen) x) ∈
      (criticalGradedNorm F K ht hres pi hpi hgen).range
    exact ⟨unitGradedMk K t x, criticalGradedNorm_mk F K ht hres pi hpi hgen x⟩
  · intro y hy
    change unitGradedMk F t y ∈
      (criticalGradedNorm F K ht hres pi hpi hgen).range at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨x, rfl⟩ := unitGradedMk_surjective K t z
    have heq :
        unitGradedMk F t
            (normBelowBreakUnitFiltrationHom F K t t
              (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen) x) =
          unitGradedMk F t y := by
      simpa only [criticalGradedNorm_mk] using hz
    have hcong := (unitGradedMk_eq_mk_iff F t _ _).1 heq
    have herr : (y : Fˣ) / normUnits F K (x : Kˣ) ∈
        unitFiltration F (t + 1) := by
      apply (div_mem_unitFiltration_iff_congruentAtDepth F (t + 1)
        (y : Fˣ) (normUnits F K (x : Kˣ))
        (unitFiltration_le_unitGroup F t y.property)
        (unitFiltration_le_unitGroup F t
          (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen
            (x : Kˣ) x.property))).2
      exact hcong.symm
    obtain ⟨w, hw, hnw⟩ :=
      norm_unitFiltration_surjective_break_succ F K ht hres pi hpi hgen
        ((y : Fˣ) / normUnits F K (x : Kˣ)) herr
    let xw : unitFiltration K t :=
      ⟨(x : Kˣ) * w, unitFiltration_mul_mem K x.property
        (unitFiltration_antitone K (Nat.le_succ t) hw)⟩
    refine ⟨xw, ?_⟩
    apply Subtype.ext
    change normUnits F K ((x : Kˣ) * w) = (y : Fˣ)
    rw [map_mul, hnw]
    simp [div_eq_mul_inv, mul_left_comm]

/-- The critical full image as a subgroup of `Fˣ`, rather than as a subgroup of the subtype
`U_F^t`. -/
noncomputable def criticalNormImage : Subgroup Fˣ :=
  Subgroup.map (unitFiltration F t).subtype
    (criticalNormTargetImage F K ht hres pi hpi hgen)

/-- Exact full norm image at the critical layer. -/
theorem norm_unitFiltration_map_eq_atBreak :
    Subgroup.map (normUnits F K) (unitFiltration K t) =
      criticalNormImage F K ht hres pi hpi hgen := by
  rw [criticalNormImage, ← norm_unitFiltration_range_eq_criticalNormTargetImage
    F K ht hres pi hpi hgen]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let x0 : unitFiltration K t := ⟨x, hx⟩
    refine ⟨normBelowBreakUnitFiltrationHom F K t t
      (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen) x0, ?_, rfl⟩
    exact ⟨x0, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨(x : Kˣ), x.property, rfl⟩

/-- For every layer at or below the break, its full norm image meets the critical target
layer in exactly the full critical norm image. -/
theorem norm_unitFiltration_map_inf_eq_criticalNormImage
    {r : ℕ} (hrt : r ≤ t) :
    Subgroup.map (normUnits F K) (unitFiltration K r) ⊓ unitFiltration F t =
      criticalNormImage F K ht hres pi hpi hgen := by
  rw [← norm_unitFiltration_map_eq_atBreak F K ht hres pi hpi hgen]
  apply le_antisymm
  · intro u hu
    rcases hu.1 with ⟨x, hx, rfl⟩
    exact ⟨x, mem_unitFiltration_break_of_norm_mem F K ht hres pi hpi hgen x hu.2, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · exact ⟨x, unitFiltration_antitone K hrt hx, rfl⟩
    · exact normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen x hx

/-- For every layer at or below the break, adjoining the critical target layer to its full
norm image gives the entire target layer.  Together with the preceding intersection equality,
this is the exact full-image description below the break; it does not assert false
surjectivity onto `U_F^r`. -/
theorem norm_unitFiltration_map_sup_eq_belowBreak
    {r : ℕ} (hrt : r ≤ t) :
    Subgroup.map (normUnits F K) (unitFiltration K r) ⊔ unitFiltration F t =
      unitFiltration F r := by
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      exact normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen x hx
    · exact unitFiltration_antitone F hrt
  · intro u hu
    obtain ⟨x, hx, herr⟩ :=
      exists_norm_belowBreak_finiteCorrection F K hrt ht hres pi hpi hgen u hu
    have hnorm : normUnits F K x ∈
        Subgroup.map (normUnits F K) (unitFiltration K r) ⊔ unitFiltration F t :=
      (le_sup_left : Subgroup.map (normUnits F K) (unitFiltration K r) ≤ _)
        ⟨x, hx, rfl⟩
    have herr' : u / normUnits F K x ∈
        Subgroup.map (normUnits F K) (unitFiltration K r) ⊔ unitFiltration F t :=
      (le_sup_right : unitFiltration F t ≤ _) herr
    have hmul :=
      (Subgroup.map (normUnits F K) (unitFiltration K r) ⊔ unitFiltration F t).mul_mem
        hnorm herr'
    simpa [div_eq_mul_inv, mul_assoc] using hmul

/-- The global field norm range meets `U_F^t` in exactly the critical full image. -/
theorem norm_range_inf_unitFiltration_atBreak :
    (normUnits F K).range ⊓ unitFiltration F t =
      criticalNormImage F K ht hres pi hpi hgen := by
  rw [← norm_unitFiltration_map_eq_atBreak F K ht hres pi hpi hgen]
  apply le_antisymm
  · intro u hu
    rcases hu.1 with ⟨x, rfl⟩
    exact ⟨x, mem_unitFiltration_break_of_norm_mem F K ht hres pi hpi hgen x hu.2, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen x hx⟩

/-- The global field norm range together with the critical unit layer generates all of
`Fˣ`.  This is the full-field counterpart of the below-break join formula. -/
theorem norm_range_sup_unitFiltration_atBreak :
    (normUnits F K).range ⊔ unitFiltration F t = ⊤ := by
  apply top_unique
  intro u _
  obtain ⟨x, herr⟩ := exists_norm_representative_mod_break F K ht hres pi hpi hgen u
  have hnorm : normUnits F K x ∈ (normUnits F K).range ⊔ unitFiltration F t :=
    (le_sup_left : (normUnits F K).range ≤ _) ⟨x, rfl⟩
  have herr' : u / normUnits F K x ∈ (normUnits F K).range ⊔ unitFiltration F t :=
    (le_sup_right : unitFiltration F t ≤ _) herr
  have hmul := ((normUnits F K).range ⊔ unitFiltration F t).mul_mem hnorm herr'
  simpa [div_eq_mul_inv, mul_assoc] using hmul

/-- The different exponent in the manuscript's prime-degree normalization. -/
theorem cyclicPrime_differentExponent_eq :
    differentExponent F K = (Module.finrank F K - 1) * (t + 1) :=
  differentExponent_eq F K ht pi hpi hgen

/-- Exact trace image with the ramification index replaced by the prime extension degree.
The residue-degree-one hypothesis is what justifies this replacement. -/
theorem cyclicPrime_trace_lattice_image_eq (a : ℤ) :
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) =
      lattice F ((a + ((((Module.finrank F K - 1) * (t + 1) : ℕ)) : ℤ)) /
        (Module.finrank F K : ℤ)) := by
  have hram : ramificationIndex F K = Module.finrank F K := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  rw [trace_lattice_image_eq F K pi hpi hgen a,
    differentExponent_eq F K ht pi hpi hgen, hram]

/-- Splicing the strictly subcritical graded norm isomorphisms gives a bijection on every
finite interval `U_K^r/U_K^t → U_F^r/U_F^t`, including the trivial endpoint `r=t`. -/
theorem normUnitFiltrationInterval_bijective_belowBreak
    {r : ℕ} (hrt : r ≤ t) :
    Function.Bijective
      (normUnitFiltrationInterval F K hrt
        (fun i _ hit ↦
          normMapsUnitFiltration_belowBreak F K ht hit hres pi hpi hgen)) := by
  constructor
  · apply normUnitFiltrationInterval_injective F K hrt
    intro i _ hit
    exact (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen).1
  · apply normUnitFiltrationInterval_surjective F K hrt
    intro i _ hit
    exact (gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen).2

/-- Norm is bijective on the full multiplicative quotients modulo `U^t`; at `t=0` this is
exactly the valuation quotient and does not use the critical residue map. -/
theorem normFieldFiltrationQuotient_bijective_belowBreak :
    Function.Bijective
      (normFieldFiltrationQuotient F K t
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)) := by
  exact (normFieldFiltrationEquiv_belowBreak F K ht hres pi hpi hgen).bijective

/-- Norm from a below-break layer modulo the first layer beyond the critical line.  This is
the quotient that detects the honest full image inside `U_F^r`. -/
noncomputable def normUnitFiltrationToBreakSucc
    {r : ℕ} (hrt : r ≤ t) :
    UnitFiltrationQuotient K r (t + 1) (hrt.trans (Nat.le_succ t)) →*
      UnitFiltrationQuotient F r (t + 1) (hrt.trans (Nat.le_succ t)) :=
  normUnitFiltrationQuotient F K
    (hrt.trans (Nat.le_succ t)) (hrt.trans (Nat.le_succ t))
    (normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen)
    (normMapsUnitFiltration_break_succ F K ht hres pi hpi hgen)

@[simp]
theorem normUnitFiltrationToBreakSucc_mk
    {r : ℕ} (hrt : r ≤ t) (u : unitFiltration K r) :
    normUnitFiltrationToBreakSucc F K ht hres pi hpi hgen hrt
        (unitFiltrationQuotientMk K (hrt.trans (Nat.le_succ t)) u) =
      unitFiltrationQuotientMk F (hrt.trans (Nat.le_succ t))
        (normBelowBreakUnitFiltrationHom F K r r
          (normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen) u) :=
  rfl

/-- The exact target-side description of the full norm image from `U_K^r`, for `r ≤ t`.
It is the inverse image of the range of norm modulo `U_F^(t+1)`. -/
noncomputable def belowBreakNormTargetImage
    {r : ℕ} (hrt : r ≤ t) : Subgroup (unitFiltration F r) :=
  (normUnitFiltrationToBreakSucc F K ht hres pi hpi hgen hrt).range.comap
    (unitFiltrationQuotientMk F (hrt.trans (Nat.le_succ t)))

/-- Exact full-image equality on every below-break or critical unit layer. -/
theorem norm_unitFiltration_range_eq_belowBreakNormTargetImage
    {r : ℕ} (hrt : r ≤ t) :
    (normBelowBreakUnitFiltrationHom F K r r
      (normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen)).range =
      belowBreakNormTargetImage F K ht hres pi hpi hgen hrt := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change unitFiltrationQuotientMk F (hrt.trans (Nat.le_succ t))
        (normBelowBreakUnitFiltrationHom F K r r
          (normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen) x) ∈
      (normUnitFiltrationToBreakSucc F K ht hres pi hpi hgen hrt).range
    exact ⟨unitFiltrationQuotientMk K (hrt.trans (Nat.le_succ t)) x,
      normUnitFiltrationToBreakSucc_mk F K ht hres pi hpi hgen hrt x⟩
  · intro y hy
    change unitFiltrationQuotientMk F (hrt.trans (Nat.le_succ t)) y ∈
      (normUnitFiltrationToBreakSucc F K ht hres pi hpi hgen hrt).range at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨x, rfl⟩ :=
      unitFiltrationQuotientMk_surjective K (hrt.trans (Nat.le_succ t)) z
    have heq :
        unitFiltrationQuotientMk F (hrt.trans (Nat.le_succ t))
            (normBelowBreakUnitFiltrationHom F K r r
              (normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen) x) =
          unitFiltrationQuotientMk F (hrt.trans (Nat.le_succ t)) y := by
      simpa only [normUnitFiltrationToBreakSucc_mk] using hz
    have hquotient :=
      (unitFiltrationQuotientMk_eq_mk_iff F (hrt.trans (Nat.le_succ t)) _ _).1 heq
    have herr : (y : Fˣ) / normUnits F K (x : Kˣ) ∈
        unitFiltration F (t + 1) := by
      have hinv := (unitFiltration F (t + 1)).inv_mem hquotient
      simpa only [inv_div, coe_normBelowBreakUnitFiltrationHom] using hinv
    obtain ⟨w, hw, hnw⟩ :=
      norm_unitFiltration_surjective_break_succ F K ht hres pi hpi hgen
        ((y : Fˣ) / normUnits F K (x : Kˣ)) herr
    let xw : unitFiltration K r :=
      ⟨(x : Kˣ) * w, unitFiltration_mul_mem K x.property
        (unitFiltration_antitone K (hrt.trans (Nat.le_succ t)) hw)⟩
    refine ⟨xw, ?_⟩
    apply Subtype.ext
    change normUnits F K ((x : Kˣ) * w) = (y : Fˣ)
    rw [map_mul, hnw]
    simp [div_eq_mul_inv, mul_left_comm]

/-- Projecting the exact quotient modulo `U^(t+1)` to the below-break quotient modulo `U^t`
recovers the spliced below-break norm. -/
theorem normUnitFiltrationToBreakSucc_projection
    {r : ℕ} (hrt : r ≤ t) :
    (unitFiltrationQuotientProjection F hrt (Nat.le_succ t)).comp
        (normUnitFiltrationToBreakSucc F K ht hres pi hpi hgen hrt) =
      (normUnitFiltrationInterval F K hrt
        (fun i _ hit ↦
          normMapsUnitFiltration_belowBreak F K ht hit hres pi hpi hgen)).comp
        (unitFiltrationQuotientProjection K hrt (Nat.le_succ t)) := by
  ext z
  rfl

/-- At `r=t`, the all-below-layers image description agrees with the critical graded-range
description. -/
theorem belowBreakNormTargetImage_atBreak :
    belowBreakNormTargetImage F K ht hres pi hpi hgen (le_rfl : t ≤ t) =
      criticalNormTargetImage F K ht hres pi hpi hgen := by
  rw [← norm_unitFiltration_range_eq_belowBreakNormTargetImage F K ht hres pi hpi hgen,
    ← norm_unitFiltration_range_eq_criticalNormTargetImage F K ht hres pi hpi hgen]

end PrimeCyclicAssembly

section FinalTheorem

section CriticalAllDepthCardinality

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

/-- The all-depth graded norm has the exact critical cokernel order at `r=t`. -/
theorem cyclicPrimeGradedNorm_cokernel_card_atBreak :
    Nat.card (UnitGradedPiece F t ⧸
      (cyclicPrimeGradedNorm F K ht hres pi hpi hgen t).range) =
      Module.finrank F K := by
  rw [cyclicPrimeGradedNorm_range_atBreak F K ht hres pi hpi hgen]
  exact criticalGradedNorm_cokernel_card F K ht hres pi hpi hgen

/-- The all-depth graded norm has the exact critical kernel order at `r=t`. -/
theorem cyclicPrimeGradedNorm_kernel_card_atBreak :
    Nat.card (cyclicPrimeGradedNorm F K ht hres pi hpi hgen t).ker =
      Module.finrank F K := by
  let f := cyclicPrimeGradedNorm F K ht hres pi hpi hgen t
  have hpsi : herbrandPsiNat t (Module.finrank F K) t = t :=
    herbrandPsiNat_break t (Module.finrank F K)
  have hcard : Nat.card (UnitFiltrationQuotient K
        (herbrandPsiNat t (Module.finrank F K) t)
        (herbrandPsiNat t (Module.finrank F K) t + 1) (Nat.le_succ _)) =
      Nat.card (UnitGradedPiece F t) := by
    calc
      _ = Nat.card (UnitGradedPiece K t) := by simpa only [hpsi]
      _ = Nat.card (UnitGradedPiece F t) :=
        unitGradedPiece_card_eq_of_residueDegree_eq_one F K t hres
  have hcokerEqKernel :
      Nat.card (UnitGradedPiece F t ⧸ f.range) = Nat.card f.ker := by
    have hkernel := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hrange := Subgroup.card_eq_card_quotient_mul_card_subgroup f.range
    have hfirstIso : Nat.card (_ ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have hmul : Nat.card f.range * Nat.card (UnitGradedPiece F t ⧸ f.range) =
        Nat.card f.range * Nat.card f.ker := by
      calc
        _ = Nat.card (UnitGradedPiece F t) := by
          rw [mul_comm]
          exact hrange.symm
        _ = Nat.card (UnitFiltrationQuotient K
            (herbrandPsiNat t (Module.finrank F K) t)
            (herbrandPsiNat t (Module.finrank F K) t + 1)
            (Nat.le_succ _)) := hcard.symm
        _ = Nat.card (_ ⧸ f.ker) * Nat.card f.ker := hkernel
        _ = Nat.card f.range * Nat.card f.ker := by rw [hfirstIso]
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.range)) hmul
  change Nat.card f.ker = Module.finrank F K
  rw [← hcokerEqKernel]
  exact cyclicPrimeGradedNorm_cokernel_card_atBreak F K ht hres pi hpi hgen

end CriticalAllDepthCardinality

/-- Named proposition containing the complete cyclic-prime norm-filtration theorem.  Every
field is a proposition: the canonical quotient maps and equivalences themselves remain the
separate public definitions above and in the four prerequisite modules. -/
structure CyclicPrimeNormFiltration
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) : Prop where
  /-- Every natural target depth is strictly below, equal to, or strictly above the break. -/
  depth_cases : ∀ r : ℕ, r < t ∨ r = t ∨ t < r
  /-- The critical upper depth has the same lower depth. -/
  herbrand_at_break : herbrandPsiNat t (Module.finrank F K) t = t
  /-- The first strict upper depth has lower depth `t + [K:F]`. -/
  herbrand_first_above :
    herbrandPsiNat t (Module.finrank F K) (t + 1) = t + Module.finrank F K
  /-- Piecewise inverse-Herbrand formula in the above-break direction. -/
  herbrand_above : ∀ r : ℕ, t ≤ r →
    herbrandPsiNat t (Module.finrank F K) r =
      t + Module.finrank F K * (r - t)
  /-- The denominator `Psi(r)+1` never overshoots the next Herbrand level. -/
  herbrand_denominator_le_next : ∀ r : ℕ,
    herbrandPsiNat t (Module.finrank F K) r + 1 ≤
      herbrandPsiNat t (Module.finrank F K) (r + 1)
  /-- Above and at the break this separation is strict because the degree is prime. -/
  herbrand_denominator_lt_next : ∀ r : ℕ, t ≤ r →
    herbrandPsiNat t (Module.finrank F K) r + 1 <
      herbrandPsiNat t (Module.finrank F K) (r + 1)
  /-- Numerator containment for the all-depth inverse-Herbrand quotient norm. -/
  herbrand_numerator : ∀ r : ℕ,
    NormMapsUnitFiltration F K
      (herbrandPsiNat t (Module.finrank F K) r) r
  /-- Adjacent-denominator containment, including the `r=t` endpoint. -/
  herbrand_denominator : ∀ r : ℕ,
    NormMapsUnitFiltration F K
      (herbrandPsiNat t (Module.finrank F K) r + 1) (r + 1)
  /-- The all-depth Herbrand graded map is bijective strictly below the break. -/
  all_depth_below_bijective : ∀ (r : ℕ), r < t →
    Function.Bijective (cyclicPrimeGradedNorm F K ht hres pi hpi hgen r)
  /-- At the break, the all-depth map and the canonical critical map have the same range. -/
  all_depth_critical_range :
    (cyclicPrimeGradedNorm F K ht hres pi hpi hgen t).range =
      (criticalGradedNorm F K ht hres pi hpi hgen).range
  /-- The kernel of the all-depth map at the break has order `[K:F]`. -/
  all_depth_critical_kernel_card :
    Nat.card (cyclicPrimeGradedNorm F K ht hres pi hpi hgen t).ker =
      Module.finrank F K
  /-- The cokernel of the all-depth map at the break has order `[K:F]`. -/
  all_depth_critical_cokernel_card :
    Nat.card (UnitGradedPiece F t ⧸
      (cyclicPrimeGradedNorm F K ht hres pi hpi hgen t).range) =
      Module.finrank F K
  /-- The all-depth Herbrand graded map is bijective strictly above the break. -/
  all_depth_above_bijective : ∀ (r : ℕ), t < r →
    Function.Bijective (cyclicPrimeGradedNorm F K ht hres pi hpi hgen r)
  /-- Hilbert's different formula in the prime-degree one-break case. -/
  different : differentExponent F K = (Module.finrank F K - 1) * (t + 1)
  /-- Exact trace image at every integer depth, with floor division by `[K:F]`. -/
  trace_image : ∀ a : ℤ,
    Submodule.map ((trace F K).restrictScalars (ringOfIntegers F))
        ((lattice K a).restrictScalars (ringOfIntegers F)) =
      lattice F ((a + ((((Module.finrank F K - 1) * (t + 1) : ℕ)) : ℤ)) /
        (Module.finrank F K : ℤ))
  /-- Every graded norm strictly below the break is bijective. -/
  below_graded_bijective : ∀ (i : ℕ) (hit : i < t),
    Function.Bijective
      (normUnitGraded F K i
        (normMapsUnitFiltration_belowBreak F K ht hit.le hres pi hpi hgen)
        (normMapsUnitFiltration_belowBreak F K ht (by omega) hres pi hpi hgen))
  /-- Every finite interval through the strict below-break graded lines is bijective. -/
  below_interval_bijective : ∀ (r : ℕ) (hrt : r ≤ t),
    Function.Bijective
      (normUnitFiltrationInterval F K hrt
        (fun _i _ hit ↦
          normMapsUnitFiltration_belowBreak F K ht hit hres pi hpi hgen))
  /-- Full field quotients modulo `U^t` are bijective, including `t=0`. -/
  below_field_bijective :
    Function.Bijective
      (normFieldFiltrationQuotient F K t
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen))
  /-- Exact full norm image on every layer at or below the break. -/
  below_full_image : ∀ (r : ℕ) (hrt : r ≤ t),
    (normBelowBreakUnitFiltrationHom F K r r
      (normMapsUnitFiltration_belowBreak F K ht hrt hres pi hpi hgen)).range =
      belowBreakNormTargetImage F K ht hres pi hpi hgen hrt
  /-- The below-layer image meets `U_F^t` in exactly the critical full image. -/
  below_image_inf : ∀ (r : ℕ) (hrt : r ≤ t),
    Subgroup.map (normUnits F K) (unitFiltration K r) ⊓ unitFiltration F t =
      criticalNormImage F K ht hres pi hpi hgen
  /-- Adjoining `U_F^t` to the below-layer image gives all of `U_F^r`. -/
  below_image_sup : ∀ (r : ℕ) (hrt : r ≤ t),
    Subgroup.map (normUnits F K) (unitFiltration K r) ⊔ unitFiltration F t =
      unitFiltration F r
  /-- Exact kernel of the critical graded norm. -/
  critical_kernel :
    (criticalGradedNorm F K ht hres pi hpi hgen).ker =
      (ramificationUnitGradedHom F K t pi hpi hgen).range
  /-- Exactness of ramification followed by the critical graded norm. -/
  critical_exact :
    Function.MulExact
      (ramificationUnitGradedHom F K t pi hpi hgen)
      (criticalGradedNorm F K ht hres pi hpi hgen)
  /-- The critical kernel has order `[K:F]`. -/
  critical_kernel_card :
    Nat.card (criticalGradedNorm F K ht hres pi hpi hgen).ker =
      Module.finrank F K
  /-- The critical cokernel is the target modulo the actual range and has order `[K:F]`. -/
  critical_cokernel_card :
    Nat.card (UnitGradedPiece F t ⧸
      (criticalGradedNorm F K ht hres pi hpi hgen).range) =
      Module.finrank F K
  /-- The honest critical full image is the inverse image of the critical graded range. -/
  critical_full_image :
    (normBelowBreakUnitFiltrationHom F K t t
      (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)).range =
      criticalNormTargetImage F K ht hres pi hpi hgen
  /-- The first layer after the critical line is an exact norm image. -/
  critical_successor_image :
    Subgroup.map (normUnits F K) (unitFiltration K (t + 1)) =
      unitFiltration F (t + 1)
  /-- Strictly above the break, the Herbrand-indexed graded norm is bijective. -/
  above_graded_bijective : ∀ (r : ℕ) (htr : t < r),
    Function.Bijective
      (normGradedAboveBreakCanonical F K ht htr hres pi hpi hgen)
  /-- Strictly above the break, the graded range is the whole target. -/
  above_graded_range : ∀ (r : ℕ) (htr : t < r),
    (normGradedAboveBreakCanonical F K ht htr hres pi hpi hgen).range = ⊤
  /-- First exact above-break full-image equality. -/
  above_image : ∀ (r : ℕ) (htr : t < r),
    Subgroup.map (normUnits F K)
        (unitFiltration K (herbrandPsiNat t (Module.finrank F K) r)) =
      unitFiltration F r
  /-- Second exact above-break full-image equality; the source is `Psi(r)+1`. -/
  above_successor_image : ∀ (r : ℕ) (htr : t < r),
    Subgroup.map (normUnits F K)
        (unitFiltration K (herbrandPsiNat t (Module.finrank F K) r + 1)) =
      unitFiltration F (r + 1)
  /-- The global norm range meets the critical unit layer in the critical image. -/
  field_image_inf :
    (normUnits F K).range ⊓ unitFiltration F t =
      criticalNormImage F K ht hres pi hpi hgen
  /-- The global norm range and `U_F^t` generate `Fˣ`. -/
  field_image_sup : (normUnits F K).range ⊔ unitFiltration F t = ⊤

/-- **Cyclic-prime norm filtration theorem.**  This is the assembled public theorem: the
different and trace formulas, every below/critical/above filtration case, exact full images,
critical kernel and cokernel, inverse-Herbrand depths, and quotient well-definedness all follow
from the four independent prerequisite modules. -/
theorem cyclicPrimeNormFiltration
    (F K : Type) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤) :
    CyclicPrimeNormFiltration F K ht hres pi hpi hgen := by
  refine
    { depth_cases := fun r ↦ lt_trichotomy r t
      herbrand_at_break := herbrandPsiNat_break t (Module.finrank F K)
      herbrand_first_above := herbrandPsiNat_break_succ t (Module.finrank F K)
      herbrand_above := fun r htr ↦
        herbrandPsiNat_of_break_le t (Module.finrank F K) htr
      herbrand_denominator_le_next := fun r ↦
        herbrandPsiNat_add_one_le_succ F K r
      herbrand_denominator_lt_next := fun r htr ↦
        herbrandPsiNat_add_one_lt_succ t (Module.finrank F K)
          (PrimeCyclicExtension.degree_prime F K) htr
      herbrand_numerator :=
        normMapsUnitFiltration_herbrand F K ht hres pi hpi hgen
      herbrand_denominator :=
        normMapsUnitFiltration_herbrand_succ F K ht hres pi hpi hgen
      all_depth_below_bijective := fun _r hrt ↦
        cyclicPrimeGradedNorm_bijective_belowBreak F K ht hres pi hpi hgen hrt
      all_depth_critical_range :=
        cyclicPrimeGradedNorm_range_atBreak F K ht hres pi hpi hgen
      all_depth_critical_kernel_card :=
        cyclicPrimeGradedNorm_kernel_card_atBreak F K ht hres pi hpi hgen
      all_depth_critical_cokernel_card :=
        cyclicPrimeGradedNorm_cokernel_card_atBreak F K ht hres pi hpi hgen
      all_depth_above_bijective := fun _r htr ↦
        cyclicPrimeGradedNorm_bijective_aboveBreak F K ht hres pi hpi hgen htr
      different := differentExponent_eq F K ht pi hpi hgen
      trace_image := cyclicPrime_trace_lattice_image_eq F K ht hres pi hpi hgen
      below_graded_bijective := fun _i hit ↦
        gradedNorm_bijective_belowBreak F K ht hit hres pi hpi hgen
      below_interval_bijective := fun _r hrt ↦
        normUnitFiltrationInterval_bijective_belowBreak F K ht hres pi hpi hgen hrt
      below_field_bijective :=
        normFieldFiltrationQuotient_bijective_belowBreak F K ht hres pi hpi hgen
      below_full_image := fun _r hrt ↦
        norm_unitFiltration_range_eq_belowBreakNormTargetImage
          F K ht hres pi hpi hgen hrt
      below_image_inf := fun _r hrt ↦
        norm_unitFiltration_map_inf_eq_criticalNormImage
          F K ht hres pi hpi hgen hrt
      below_image_sup := fun _r hrt ↦
        norm_unitFiltration_map_sup_eq_belowBreak F K ht hres pi hpi hgen hrt
      critical_kernel := gradedNorm_kernel F K ht hres pi hpi hgen
      critical_exact := ramification_criticalGradedNorm_mulExact F K ht hres pi hpi hgen
      critical_kernel_card := criticalGradedNorm_kernel_card F K ht hres pi hpi hgen
      critical_cokernel_card := criticalGradedNorm_cokernel_card F K ht hres pi hpi hgen
      critical_full_image :=
        norm_unitFiltration_range_eq_criticalNormTargetImage F K ht hres pi hpi hgen
      critical_successor_image :=
        norm_unitFiltration_map_eq_break_succ F K ht hres pi hpi hgen
      above_graded_bijective := fun r htr ↦
        norm_graded_bijective_above_break F K ht htr hres pi hpi hgen
      above_graded_range := fun r htr ↦
        normGradedAboveBreakCanonical_range_eq_top F K ht htr hres pi hpi hgen
      above_image := fun r htr ↦ by
        simpa only [aboveBreakSourceDepth] using
          norm_unitFiltration_map_eq_aboveBreak F K ht htr hres pi hpi hgen
      above_successor_image := fun r htr ↦ by
        simpa only [aboveBreakSourceDepth] using
          norm_unitFiltration_map_eq_aboveBreak_succ F K ht htr hres pi hpi hgen
      field_image_inf := norm_range_inf_unitFiltration_atBreak F K ht hres pi hpi hgen
      field_image_sup := norm_range_sup_unitFiltration_atBreak F K ht hres pi hpi hgen }

end FinalTheorem

end

end LanglandsFirstMainLemma
