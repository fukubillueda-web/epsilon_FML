import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.Basic.CharacterConductors

/-!
# Conductors under trace and norm pullback

This file proves Corollary `cor:additive-conductor` and Proposition
`prop:pullback-conductor` of the manuscript.  Additive conductors use the
manuscript's sign convention: conductor `n` means triviality on `p^(-n)`.
For a ramified cyclic extension of prime degree, the norm formula is indexed
by the last nontrivial target layer.  Thus the inverse Herbrand function maps
the upper depth `r = m - 1` to the lower source depth.

At the critical layer the result is not merely an upper bound.  We prove both
the exact critical-image criterion and the manuscript's equivalent criterion
in terms of a character of the norm quotient.  The latter character is
constructed here from the full quotient equivalence below the break; no
conductor result from the later `NormCharacters` module is used.
-/

namespace LanglandsFirstMainLemma

noncomputable section

section TopologicalHelpers

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Fractional valuation lattices are open in the local-field topology. -/
private theorem isOpen_lattice_forPullbackConductors (n : ℤ) :
    IsOpen (lattice F n : Set F) := by
  obtain ⟨a, ha⟩ := exists_ord_eq F n
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hopen := (ValuativeRel.valuation F).isOpen_closedBall
    (r := (ValuativeRel.valuation F).restrict a) (by simp [ha0])
  convert hopen using 1
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_lattice]
  rw [← ha, ord_le_ord_iff F a x,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    (ValuativeRel.valuation F).restrict_le_iff]

/-- Every positive unit-filtration layer is an open subgroup of `F×`. -/
private theorem isOpen_unitFiltration_succ_forPullbackConductors (n : ℕ) :
    IsOpen (unitFiltration F (n + 1) : Set Fˣ) := by
  have hcontinuous : Continuous (fun u : Fˣ => (u : F) - 1) :=
    Units.continuous_val.sub continuous_const
  have hopen := (isOpen_lattice_forPullbackConductors F ((n + 1 : ℕ) : ℤ)).preimage
    hcontinuous
  convert hopen using 1
  ext u
  exact mem_unitFiltration_succ_iff_sub_mem_lattice F n u

/-- A homomorphism of `F×` that is trivial on one unit layer is continuous.
It is enough to use the next, positive, layer as an open neighborhood of `1`. -/
private theorem continuous_of_trivialOnUnitFiltration
    (f : Fˣ →* ℂˣ) (m : ℕ)
    (hf : ∀ u : Fˣ, u ∈ unitFiltration F m → f u = 1) :
    Continuous f := by
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one]
  rw [Filter.tendsto_def]
  intro V hV
  have hopen : IsOpen (unitFiltration F (m + 1) : Set Fˣ) :=
    isOpen_unitFiltration_succ_forPullbackConductors F m
  have hone : (1 : Fˣ) ∈ unitFiltration F (m + 1) :=
    (unitFiltration F (m + 1)).one_mem
  refine Filter.mem_of_superset (hopen.mem_nhds hone) ?_
  intro u hu
  have hum : u ∈ unitFiltration F m :=
    unitFiltration_antitone F (Nat.le_succ m) hu
  change f u ∈ V
  rw [hf u hum]
  exact mem_of_mem_nhds hV

end TopologicalHelpers

section GeneralPullbackLemmas

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- Triviality of a norm pullback on a source unit layer is exactly
triviality of the original character on the full image of that layer. -/
theorem quasiCharTrivialOnUnitFiltration_compNorm_iff_image
    (chi : ContinuousQuasiChar F) (a : ℕ) :
    QuasiCharTrivialOnUnitFiltration K chi.compNorm a ↔
      ∀ u : Fˣ, u ∈ Subgroup.map (normUnits F K) (unitFiltration K a) →
        chi u = 1 := by
  constructor
  · intro h u hu
    obtain ⟨x, hx, rfl⟩ := hu
    simpa only [ContinuousQuasiChar.compNorm_apply] using h x hx
  · intro h x hx
    exact h (normUnits F K x) ⟨x, hx, rfl⟩

/-- Exact image equality converts norm-pullback triviality into target-side
triviality. -/
theorem quasiCharTrivialOnUnitFiltration_compNorm_iff_of_image_eq
    (chi : ContinuousQuasiChar F) (a b : ℕ)
    (himage : Subgroup.map (normUnits F K) (unitFiltration K a) =
      unitFiltration F b) :
    QuasiCharTrivialOnUnitFiltration K chi.compNorm a ↔
      QuasiCharTrivialOnUnitFiltration F chi b := by
  rw [quasiCharTrivialOnUnitFiltration_compNorm_iff_image F K chi a, himage]
  rfl

/-- A filtration containment is enough to pull target-side triviality
upstairs. -/
theorem quasiCharTrivialOnUnitFiltration_compNorm_of_maps
    (chi : ContinuousQuasiChar F) {a b : ℕ}
    (hmap : NormMapsUnitFiltration F K a b)
    (hchi : QuasiCharTrivialOnUnitFiltration F chi b) :
    QuasiCharTrivialOnUnitFiltration K chi.compNorm a := by
  intro x hx
  exact hchi (normUnits F K x) (hmap x hx)

end GeneralPullbackLemmas

section AdditiveConductor

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [IsGalois F K]

/-- **Additive conductor under trace pullback.**  With the manuscript's
convention that conductor `n` means triviality on `p_F^(-n)`, trace pullback
has conductor `e n + d`, where `d` is measured with the upstairs valuation. -/
theorem additiveConductor_compTrace
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F) ({pi} : Set (ringOfIntegers K)) = ⊤)
    {psi : ContinuousAddChar F} {n : ℤ}
    (hpsi : IsAdditiveConductor F psi n) :
    IsAdditiveConductor K psi.compTrace
      ((ramificationIndex F K : ℤ) * n +
        (differentExponent F K : ℤ)) :=
  isAdditiveConductor_compTrace F K pi hpi hgen hpsi

end AdditiveConductor

section PrimeCyclicPullback

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

/-- Prime-cyclic specialization of the additive formula:
`n_K = ell n_F + (ell - 1)(t + 1)`. -/
theorem additiveConductor_compTrace_cyclicPrime
    {psi : ContinuousAddChar F} {n : ℤ}
    (hpsi : IsAdditiveConductor F psi n) :
    IsAdditiveConductor K psi.compTrace
      ((Module.finrank F K : ℤ) * n +
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) := by
  have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
  have hram : ramificationIndex F K = Module.finrank F K := by
    rw [hres, mul_one] at hdegree
    exact hdegree.symm
  simpa only [hram, differentExponent_eq F K ht pi hpi hgen] using
    additiveConductor_compTrace F K pi hpi hgen hpsi

/-- Above the break, pullback triviality is transported along the exact
Herbrand-indexed norm image. -/
theorem quasiCharTrivialOnUnitFiltration_compNorm_iff_aboveBreak
    (chi : ContinuousQuasiChar F) {r : ℕ} (htr : t < r) :
    QuasiCharTrivialOnUnitFiltration K chi.compNorm
        (herbrandPsiNat t (Module.finrank F K) r) ↔
      QuasiCharTrivialOnUnitFiltration F chi r :=
  quasiCharTrivialOnUnitFiltration_compNorm_iff_of_image_eq F K chi _ _
    (norm_unitFiltration_map_eq_aboveBreak F K ht htr hres pi hpi hgen)

/-- The adjacent above-break denominator is `Psi(r)+1`, and its exact norm
image is `U_F^(r+1)`. -/
theorem quasiCharTrivialOnUnitFiltration_compNorm_iff_aboveBreak_succ
    (chi : ContinuousQuasiChar F) {r : ℕ} (htr : t < r) :
    QuasiCharTrivialOnUnitFiltration K chi.compNorm
        (herbrandPsiNat t (Module.finrank F K) r + 1) ↔
      QuasiCharTrivialOnUnitFiltration F chi (r + 1) :=
  quasiCharTrivialOnUnitFiltration_compNorm_iff_of_image_eq F K chi _ _
    (norm_unitFiltration_map_eq_aboveBreak_succ F K ht htr hres pi hpi hgen)

/-- At the critical successor, norm has the exact full image
`N(U_K^(t+1)) = U_F^(t+1)`. -/
theorem quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
    (chi : ContinuousQuasiChar F) :
    QuasiCharTrivialOnUnitFiltration K chi.compNorm (t + 1) ↔
      QuasiCharTrivialOnUnitFiltration F chi (t + 1) :=
  quasiCharTrivialOnUnitFiltration_compNorm_iff_of_image_eq F K chi _ _
    (norm_unitFiltration_map_eq_break_succ F K ht hres pi hpi hgen)

/-- Conductor zero remains zero under norm pullback. -/
theorem multiplicativeConductor_compNorm_zero
    {chi : ContinuousQuasiChar F}
    (hchi : IsMultiplicativeConductor F chi 0) :
    IsMultiplicativeConductor K chi.compNorm 0 := by
  apply IsMultiplicativeConductor.of_zero
  exact quasiCharTrivialOnUnitFiltration_compNorm_of_maps F K chi
    (normMapsUnitFiltration_belowBreak F K ht (Nat.zero_le t)
      hres pi hpi hgen) hchi.trivial

/-- At a positive conductor whose last nontrivial layer is strictly below
the break, norm pullback has the same exact conductor. -/
theorem multiplicativeConductor_compNorm_belowBreak_succ
    {chi : ContinuousQuasiChar F} {r : ℕ} (hrt : r < t)
    (hchi : IsMultiplicativeConductor F chi (r + 1)) :
    IsMultiplicativeConductor K chi.compNorm (r + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · exact quasiCharTrivialOnUnitFiltration_compNorm_of_maps F K chi
      (normMapsUnitFiltration_belowBreak F K ht (by omega)
        hres pi hpi hgen) hchi.trivial
  · intro hpull
    apply hchi.not_trivialOnPredecessor
    intro u hu
    have husup : u ∈
        Subgroup.map (normUnits F K) (unitFiltration K r) ⊔
          unitFiltration F t := by
      rw [norm_unitFiltration_map_sup_eq_belowBreak F K ht hres pi hpi hgen hrt.le]
      exact hu
    obtain ⟨x, hx, y, hy, hxy⟩ := (Subgroup.mem_sup.mp husup)
    rw [← hxy, map_mul]
    have hxone : chi x = 1 := by
      obtain ⟨z, hz, rfl⟩ := hx
      exact hpull z hz
    have hyone : chi y = 1 :=
      hchi.trivial y (unitFiltration_antitone F (by omega) hy)
    rw [hxone, hyone, mul_one]

/-- **Below-break conductor formula**, including the separate conductor-zero
endpoint: if `m ≤ t`, then `m_K(chi o N) = m`. -/
theorem multiplicativeConductor_compNorm_belowBreak
    {chi : ContinuousQuasiChar F} {m : ℕ} (hmt : m ≤ t)
    (hchi : IsMultiplicativeConductor F chi m) :
    IsMultiplicativeConductor K chi.compNorm m := by
  cases m with
  | zero => exact multiplicativeConductor_compNorm_zero F K ht hres pi hpi hgen hchi
  | succ r =>
      simpa only [Nat.succ_eq_add_one] using
        multiplicativeConductor_compNorm_belowBreak_succ F K ht hres pi hpi hgen
          (r := r) (by omega) (by simpa only [Nat.succ_eq_add_one] using hchi)

/-- **Strictly above-break conductor formula.**  If the downstairs exact
conductor is `r+1` with `t<r`, then the upstairs exact conductor is
`Psi(r)+1`. -/
theorem multiplicativeConductor_compNorm_aboveBreak
    {chi : ContinuousQuasiChar F} {r : ℕ} (htr : t < r)
    (hchi : IsMultiplicativeConductor F chi (r + 1)) :
    IsMultiplicativeConductor K chi.compNorm
      (herbrandPsiNat t (Module.finrank F K) r + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · exact (quasiCharTrivialOnUnitFiltration_compNorm_iff_aboveBreak_succ
      F K ht hres pi hpi hgen chi htr).2 hchi.trivial
  · intro hpull
    apply hchi.not_trivialOnPredecessor
    exact (quasiCharTrivialOnUnitFiltration_compNorm_iff_aboveBreak
      F K ht hres pi hpi hgen chi htr).1 hpull

/-- Manuscript form of the high-conductor formula:
`m'_K - 1 = Psi(m_F - 1)`. -/
theorem multiplicativeConductor_compNorm_high
    {chi : ContinuousQuasiChar F} {m : ℕ} (hm : t + 1 < m)
    (hchi : IsMultiplicativeConductor F chi m) :
    IsMultiplicativeConductor K chi.compNorm
      (herbrandPsiNat t (Module.finrank F K) (m - 1) + 1) := by
  have hmpos : 0 < m := by omega
  have hmrepr : m - 1 + 1 = m := by omega
  apply multiplicativeConductor_compNorm_aboveBreak F K ht hres pi hpi hgen
    (r := m - 1) (by omega)
  simpa only [hmrepr] using hchi

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K] [Module.Free F K] [PrimeCyclicExtension F K]
    ht hres pi hpi hgen in
/-- Integer form of the high Herbrand depth.  This is the downstream-friendly
identity `m_K = ell*m_F - (ell-1)(t+1)`; the subtraction is written in `ℤ`
so its nonnegativity is not hidden by truncated natural subtraction. -/
theorem highConductor_cast_eq_degree_mul_sub_different
    {m : ℕ} (hm : t + 1 < m) :
    ((herbrandPsiNat t (Module.finrank F K) (m - 1) + 1 : ℕ) : ℤ) =
      (Module.finrank F K : ℤ) * (m : ℤ) -
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  rw [herbrandPsiNat_of_break_le t (Module.finrank F K) (by omega)]
  push_cast [Nat.cast_sub (by omega : t ≤ m - 1),
    Nat.cast_sub (show 1 ≤ Module.finrank F K from Module.finrank_pos),
    Nat.cast_sub (by omega : 1 ≤ m)]
  ring

/-- At the critical conductor `t+1`, norm pullback is always trivial on
`U_K^(t+1)`, hence every exact upstairs conductor is at most `t+1`. -/
theorem multiplicativeConductor_compNorm_critical_le
    {chi : ContinuousQuasiChar F}
    (hchi : IsMultiplicativeConductor F chi (t + 1))
    {m' : ℕ} (hchiK : IsMultiplicativeConductor K chi.compNorm m') :
    m' ≤ t + 1 := by
  apply hchiK.minimal
  exact (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
    F K ht hres pi hpi hgen chi).2 hchi.trivial

omit [PrimeCyclicExtension F K] ht hres pi hpi hgen in
/-- Exact critical cancellation criterion on the source layer: an exact
upstairs conductor drops below `t+1` iff the pullback is already trivial on
`U_K^t`. -/
theorem multiplicativeConductor_compNorm_critical_drop_iff
    {chi : ContinuousQuasiChar F} {m' : ℕ}
    (hchiK : IsMultiplicativeConductor K chi.compNorm m') :
    m' < t + 1 ↔
      QuasiCharTrivialOnUnitFiltration K chi.compNorm t := by
  rw [hchiK.trivialOnUnitFiltration_iff]
  omega

/-- Target-side form of the exact critical cancellation criterion.  The
character must be trivial on the honest critical norm image, not on all of
`U_F^t`. -/
theorem multiplicativeConductor_compNorm_critical_drop_iff_image
    {chi : ContinuousQuasiChar F} {m' : ℕ}
    (hchiK : IsMultiplicativeConductor K chi.compNorm m') :
    m' < t + 1 ↔
      ∀ u : Fˣ, u ∈ criticalNormImage F K ht hres pi hpi hgen →
        chi u = 1 := by
  rw [multiplicativeConductor_compNorm_critical_drop_iff
    F K hchiK,
    quasiCharTrivialOnUnitFiltration_compNorm_iff_image F K chi t,
    norm_unitFiltration_map_eq_atBreak F K ht hres pi hpi hgen]

/-- If critical cancellation does not occur, the critical upper bound is
the exact conductor. -/
theorem multiplicativeConductor_compNorm_critical_of_noCancellation
    {chi : ContinuousQuasiChar F}
    (hchi : IsMultiplicativeConductor F chi (t + 1))
    (hnocancel : ¬ QuasiCharTrivialOnUnitFiltration K chi.compNorm t) :
    IsMultiplicativeConductor K chi.compNorm (t + 1) := by
  apply IsMultiplicativeConductor.of_succ_boundary
  · exact (quasiCharTrivialOnUnitFiltration_compNorm_iff_break_succ
      F K ht hres pi hpi hgen chi).2 hchi.trivial
  · exact hnocancel

omit [PrimeCyclicExtension F K] ht hres pi hpi hgen in
/-- Multiplying downstairs by a character of the norm quotient does not
change the norm pullback. -/
theorem normCharacter_mul_compNorm
    (mu : NormCharacter F K) (chi : ContinuousQuasiChar F) :
    ContinuousQuasiChar.compNorm (R := F) (S := K) (mu.1 * chi) =
      ContinuousQuasiChar.compNorm (R := F) (S := K) chi := by
  apply DFunLike.ext _ _
  intro x
  have hmu : mu.1 (Units.map (Algebra.norm F) x) = 1 := by
    have hx : normQuasiChar F K mu.1 x = 1 := by
      rw [mu.property]
      exact ContinuousQuasiChar.one_apply x
    exact hx
  simp only [ContinuousQuasiChar.compNorm_apply,
    ContinuousQuasiChar.mul_apply, hmu, one_mul]

/-- If a norm-character twist has exact conductor `q ≤ t`, then the
critical pullback has exact conductor `q`.  This computes the cancelled
value, rather than giving only a strict inequality. -/
theorem multiplicativeConductor_compNorm_critical_of_twist
    {chi : ContinuousQuasiChar F} (mu : NormCharacter F K)
    {q : ℕ} (hqt : q ≤ t)
    (htwist : IsMultiplicativeConductor F (mu.1 * chi) q) :
    IsMultiplicativeConductor K chi.compNorm q := by
  have h := multiplicativeConductor_compNorm_belowBreak
    F K ht hres pi hpi hgen hqt htwist
  rw [normCharacter_mul_compNorm F K mu chi] at h
  exact h

/-- **Critical cancellation criterion, in the manuscript's norm-character
form.**  If `chi` has critical conductor `t+1`, then its norm pullback has
smaller exact conductor iff a character `mu` of the norm quotient makes the
twist `mu*chi` have conductor below `t+1`.  The forward implication
constructs `mu` from the exact equivalence
`K×/U_K^t ≃ F×/U_F^t`; it does not assume the later norm-character theorem. -/
theorem multiplicativeConductor_compNorm_critical_drop_iff_exists_twist
    {chi : ContinuousQuasiChar F}
    (_hchi : IsMultiplicativeConductor F chi (t + 1))
    {m' : ℕ} (hchiK : IsMultiplicativeConductor K chi.compNorm m') :
    m' < t + 1 ↔
      ∃ mu : NormCharacter F K, ∃ q : ℕ,
        IsMultiplicativeConductor F (mu.1 * chi) q ∧ q < t + 1 := by
  classical
  constructor
  · intro hdrop
    have hpull : QuasiCharTrivialOnUnitFiltration K chi.compNorm t :=
      (multiplicativeConductor_compNorm_critical_drop_iff
        F K hchiK).1 hdrop
    let chiQuot : (Kˣ ⧸ unitFiltration K t) →* ℂˣ :=
      QuotientGroup.lift (unitFiltration K t) chi.compNorm.toMonoidHom (by
        intro x hx
        rw [MonoidHom.mem_ker]
        exact hpull x hx)
    let normEquiv :
        (Kˣ ⧸ unitFiltration K t) ≃* (Fˣ ⧸ unitFiltration F t) :=
      normFieldFiltrationEquiv_belowBreak F K ht hres pi hpi hgen
    let rhoHom : Fˣ →* ℂˣ :=
      (chiQuot.comp normEquiv.symm.toMonoidHom).comp
        (QuotientGroup.mk' (unitFiltration F t))
    have hrhoTriv : ∀ u : Fˣ, u ∈ unitFiltration F t → rhoHom u = 1 := by
      intro u hu
      change chiQuot
        (normEquiv.symm ((QuotientGroup.mk' (unitFiltration F t)) u)) = 1
      have hmk : (QuotientGroup.mk' (unitFiltration F t)) u = 1 :=
        (QuotientGroup.eq_one_iff u).2 hu
      rw [hmk, map_one, map_one]
    let rho : ContinuousQuasiChar F :=
      ⟨rhoHom, continuous_of_trivialOnUnitFiltration F rhoHom t hrhoTriv⟩
    have hnormEquiv (x : Kˣ) :
        normEquiv ((QuotientGroup.mk' (unitFiltration K t)) x) =
          (QuotientGroup.mk' (unitFiltration F t)) (normUnits F K x) := by
      change normFieldFiltrationQuotient F K t
          (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen)
          ((QuotientGroup.mk' (unitFiltration K t)) x) = _
      exact normFieldFiltrationQuotient_mk F K t
        (normMapsUnitFiltration_atBreak F K ht hres pi hpi hgen) x
    have hrhoComp :
        ContinuousQuasiChar.compNorm (R := F) (S := K) rho =
          ContinuousQuasiChar.compNorm (R := F) (S := K) chi := by
      apply DFunLike.ext _ _
      intro x
      change chiQuot
          (normEquiv.symm
            ((QuotientGroup.mk' (unitFiltration F t)) (normUnits F K x))) =
        chi.compNorm x
      rw [← hnormEquiv x, normEquiv.symm_apply_apply]
      exact QuotientGroup.lift_mk' _ _ x
    have hmuNorm : normQuasiChar F K (rho * chi⁻¹) = 1 := by
      apply DFunLike.ext _ _
      intro x
      have hx := congrArg (fun nu : ContinuousQuasiChar K => nu x) hrhoComp
      change rho (Units.map (Algebra.norm F) x) =
        chi (Units.map (Algebra.norm F) x) at hx
      change rho (Units.map (Algebra.norm F) x) *
        (chi (Units.map (Algebra.norm F) x))⁻¹ = 1
      rw [hx]
      exact mul_inv_cancel _
    let mu : NormCharacter F K := ⟨rho * chi⁻¹, hmuNorm⟩
    have htwist : mu.1 * chi = rho := by
      apply DFunLike.ext _ _
      intro u
      simp only [mu, ContinuousQuasiChar.mul_apply,
        ContinuousQuasiChar.inv_apply]
      simp [mul_assoc]
    have hrhoTriv' : QuasiCharTrivialOnUnitFiltration F rho t := by
      intro u hu
      change rhoHom u = 1
      exact hrhoTriv u hu
    have hexists : ∃ q : ℕ,
        QuasiCharTrivialOnUnitFiltration F rho q := by
      exact ⟨t, hrhoTriv'⟩
    let q : ℕ := Nat.find hexists
    have hqtriv : QuasiCharTrivialOnUnitFiltration F rho q :=
      Nat.find_spec hexists
    have hqmin : ∀ r : ℕ,
        QuasiCharTrivialOnUnitFiltration F rho r → q ≤ r := by
      intro r hr
      exact Nat.find_min' hexists hr
    have hqcond : IsMultiplicativeConductor F rho q := ⟨hqtriv, hqmin⟩
    have hqt : q ≤ t := Nat.find_min' hexists hrhoTriv'
    refine ⟨mu, q, ?_, by omega⟩
    rw [htwist]
    exact hqcond
  · rintro ⟨mu, q, htwist, hq⟩
    have hqK := multiplicativeConductor_compNorm_critical_of_twist
      F K ht hres pi hpi hgen mu (by omega) htwist
    have hm'eq : m' = q := hchiK.unique hqK
    omega

section PackagedConductors

/-- Packaged prime-cyclic additive conductor equality. -/
theorem LocalAddCharData.conductor_compTrace_eq_cyclicPrime
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace) :
    psiK.conductor =
      (Module.finrank F K : ℤ) * psiF.conductor +
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  have hcond := additiveConductor_compTrace_cyclicPrime
    F K ht hres pi hpi hgen psiF.isConductor
  have hcond' : IsAdditiveConductor K psiK.character
      ((Module.finrank F K : ℤ) * psiF.conductor +
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ)) := by
    rw [hpsi]
    exact hcond
  exact psiK.isConductor.unique hcond'

/-- Packaged below-break conductor equality, including conductor zero. -/
theorem LocalQuasiCharData.conductor_compNorm_eq_belowBreak
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hmt : chiF.conductor ≤ t) :
    chiK.conductor = chiF.conductor := by
  have hcond := multiplicativeConductor_compNorm_belowBreak
    F K ht hres pi hpi hgen hmt chiF.isConductor
  have hcond' : IsMultiplicativeConductor K chiK.character chiF.conductor := by
    rw [hcomp]
    exact hcond
  exact chiK.isConductor.unique hcond'

/-- Packaged strictly above-break equality in the manuscript's Herbrand
direction. -/
theorem LocalQuasiCharData.conductor_compNorm_eq_high
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : t + 1 < chiF.conductor) :
    chiK.conductor =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1 := by
  have hcond := multiplicativeConductor_compNorm_high
    F K ht hres pi hpi hgen hm chiF.isConductor
  have hcond' : IsMultiplicativeConductor K chiK.character
      (herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) + 1) := by
    rw [hcomp]
    exact hcond
  exact chiK.isConductor.unique hcond'

/-- Explicit high-conductor equality after casting the natural conductors to
integers: `m_K = ell*m_F - (ell-1)(t+1)`. -/
theorem LocalQuasiCharData.conductor_compNorm_eq_high_explicit
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : t + 1 < chiF.conductor) :
    (chiK.conductor : ℤ) =
      (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) -
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  rw [chiF.conductor_compNorm_eq_high F K ht hres pi hpi hgen chiK hcomp hm]
  exact highConductor_cast_eq_degree_mul_sub_different
    F K hm

/-- In the high range, the downstairs Lamprecht denominator has exactly the
required upstairs valuation: `m_K+n_K = ell*(m_F+n_F)`.  The different shift
from the additive formula cancels the high norm-pullback correction. -/
theorem high_compNorm_add_compTrace_conductor_eq
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : t + 1 < chiF.conductor) :
    (chiK.conductor : ℤ) + psiK.conductor =
      (Module.finrank F K : ℤ) *
        ((chiF.conductor : ℤ) + psiF.conductor) := by
  rw [chiF.conductor_compNorm_eq_high_explicit
      F K ht hres pi hpi hgen chiK hcomp hm,
    psiF.conductor_compTrace_eq_cyclicPrime
      F K ht hres pi hpi hgen psiK hpsi]
  ring

/-- Packaged critical upper bound. -/
theorem LocalQuasiCharData.conductor_compNorm_le_critical
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : chiF.conductor = t + 1) :
    chiK.conductor ≤ t + 1 := by
  have hchiF : IsMultiplicativeConductor F chiF.character (t + 1) := by
    rw [← hm]
    exact chiF.isConductor
  have hchiK : IsMultiplicativeConductor K chiF.character.compNorm
      chiK.conductor := by
    rw [← hcomp]
    exact chiK.isConductor
  exact multiplicativeConductor_compNorm_critical_le
    F K ht hres pi hpi hgen hchiF hchiK

/-- Packaged form of the exact critical norm-character criterion. -/
theorem LocalQuasiCharData.conductor_compNorm_critical_drop_iff_exists_twist
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : chiF.conductor = t + 1) :
    chiK.conductor < chiF.conductor ↔
      ∃ mu : NormCharacter F K, ∃ q : ℕ,
        IsMultiplicativeConductor F (mu.1 * chiF.character) q ∧
          q < chiF.conductor := by
  have hchiF : IsMultiplicativeConductor F chiF.character (t + 1) := by
    rw [← hm]
    exact chiF.isConductor
  have hchiK : IsMultiplicativeConductor K chiF.character.compNorm
      chiK.conductor := by
    rw [← hcomp]
    exact chiK.isConductor
  simpa only [hm] using
    (multiplicativeConductor_compNorm_critical_drop_iff_exists_twist
      F K ht hres pi hpi hgen hchiF hchiK)

/-- A representative minimal in its `S(K/F)`-orbit has unchanged norm
pullback conductor throughout the below and critical ranges.  Critical
equality follows from the exact cancellation criterion above, not from a
separate conductor hypothesis. -/
theorem LocalQuasiCharData.conductor_compNorm_eq_of_minimalOrbit
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : chiF.conductor ≤ t + 1)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q) :
    chiK.conductor = chiF.conductor := by
  by_cases hbelow : chiF.conductor ≤ t
  · exact chiF.conductor_compNorm_eq_belowBreak F K ht hres pi hpi hgen
      chiK hcomp hbelow
  · have hcritical : chiF.conductor = t + 1 := by omega
    have hle := chiF.conductor_compNorm_le_critical
      F K ht hres pi hpi hgen chiK hcomp hcritical
    apply Nat.le_antisymm (by simpa only [hcritical] using hle)
    by_contra hnotle
    have hdrop : chiK.conductor < chiF.conductor := by omega
    obtain ⟨mu, q, hqcond, hq⟩ :=
      (chiF.conductor_compNorm_critical_drop_iff_exists_twist
        F K ht hres pi hpi hgen chiK hcomp hcritical).1 hdrop
    exact (not_lt_of_ge (hminimal mu q hqcond)) hq

/-- For a minimal-orbit representative at or above the critical conductor,
the explicit formula `m_K = ell*m_F - (ell-1)(t+1)` also includes the
critical endpoint.  The endpoint is supplied by the exact no-cancellation
argument, while strict inequality is the above-break formula. -/
theorem LocalQuasiCharData.conductor_compNorm_eq_atOrAboveCritical_of_minimalOrbit
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hm : t + 1 ≤ chiF.conductor)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q) :
    (chiK.conductor : ℤ) =
      (Module.finrank F K : ℤ) * (chiF.conductor : ℤ) -
        (((Module.finrank F K - 1) * (t + 1) : ℕ) : ℤ) := by
  rcases eq_or_lt_of_le hm with hcritical | hhigh
  · have hmEq : chiF.conductor = t + 1 := hcritical.symm
    have hsame := chiF.conductor_compNorm_eq_of_minimalOrbit
      F K ht hres pi hpi hgen chiK hcomp (by omega) hminimal
    rw [hsame, hmEq]
    push_cast [Nat.cast_sub
      (show 1 ≤ Module.finrank F K from Module.finrank_pos)]
    ring
  · exact chiF.conductor_compNorm_eq_high_explicit
      F K ht hres pi hpi hgen chiK hcomp hhigh

/-- Denominator-valuation identity used by the high stationary-parameter and
correction-valuation nodes, including the minimal critical endpoint. -/
theorem compNorm_add_compTrace_conductor_eq_atOrAboveCritical_of_minimalOrbit
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hm : t + 1 ≤ chiF.conductor)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q) :
    (chiK.conductor : ℤ) + psiK.conductor =
      (Module.finrank F K : ℤ) *
        ((chiF.conductor : ℤ) + psiF.conductor) := by
  rw [chiF.conductor_compNorm_eq_atOrAboveCritical_of_minimalOrbit
      F K ht hres pi hpi hgen chiK hcomp hm hminimal,
    psiF.conductor_compTrace_eq_cyclicPrime
      F K ht hres pi hpi hgen psiK hpsi]
  ring

/-- Last-nontrivial-layer form strictly below the break. -/
theorem LocalQuasiCharData.conductor_compNorm_sub_one_eq_belowBreak
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hmpos : 0 < chiF.conductor)
    (hlast : chiF.conductor - 1 < t) :
    chiK.conductor - 1 = chiF.conductor - 1 := by
  have hsame := chiF.conductor_compNorm_eq_belowBreak
    F K ht hres pi hpi hgen chiK hcomp (by omega)
  rw [hsame]

/-- Last-nontrivial-layer form at the critical break for a minimal-orbit
representative. -/
theorem LocalQuasiCharData.conductor_compNorm_sub_one_eq_critical_of_minimalOrbit
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hlast : chiF.conductor - 1 = t)
    (hmpos : 0 < chiF.conductor)
    (hminimal : ∀ (mu : NormCharacter F K) (q : ℕ),
      IsMultiplicativeConductor F (mu.1 * chiF.character) q →
        chiF.conductor ≤ q) :
    chiK.conductor - 1 = t := by
  have hm : chiF.conductor = t + 1 := by omega
  have hsame := chiF.conductor_compNorm_eq_of_minimalOrbit
    F K ht hres pi hpi hgen chiK hcomp (by omega) hminimal
  omega

/-- Last-nontrivial-layer form strictly above the break. -/
theorem LocalQuasiCharData.conductor_compNorm_sub_one_eq_aboveBreak
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (hcomp : chiK.character = chiF.character.compNorm)
    (hlast : t < chiF.conductor - 1) :
    chiK.conductor - 1 =
      herbrandPsiNat t (Module.finrank F K) (chiF.conductor - 1) := by
  have hm : t + 1 < chiF.conductor := by omega
  have heq := chiF.conductor_compNorm_eq_high
    F K ht hres pi hpi hgen chiK hcomp hm
  omega

end PackagedConductors

end PrimeCyclicPullback

end

end LanglandsFirstMainLemma
