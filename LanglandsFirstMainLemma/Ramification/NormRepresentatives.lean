import LanglandsFirstMainLemma.Ramification.NormFiltration
import LanglandsFirstMainLemma.LocalField.Lattices

/-!
# Exact norm representatives below the ramification break

Let `K/F` be a totally ramified cyclic extension of prime degree with lower
break `t`.  The cyclic-prime norm filtration identifies

`Kˣ / U_K^t` with `Fˣ / U_F^t`.

Consequently, if `c` has exact order `h`, then at every precision `s ≤ t`
its class modulo `lattice F (h + s)` has a representative that is an exact
field norm.  The public API below is entirely existential: it never chooses
a distinguished element of `K`.

The predicate `IsSubcriticalNormRepresentative` records both exact source
and target orders and the direction of the additive congruence.  Further
theorems express the same fact in honest lattice quotients, show that a
witness at a finer precision projects to every coarser precision, identify
the permitted ambiguity between choices, and choose heterogeneous finite
families pointwise.

This is Lemma `lem:norm-stationary-representatives` of the manuscript.
-/

namespace LanglandsFirstMainLemma

noncomputable section

/-- Two nonzero elements of the same exact order are additively congruent
at shifted depth `h+s` exactly strongly enough for their quotient to lie in
`U^s`.  This is the valuation bridge between coefficient lattices and the
multiplicative ambiguity of norm representatives. -/
theorem div_mem_unitFiltration_of_exactOrder_congruentAtDepth
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {h : ℤ} {s : ℕ} (a b : Eˣ)
    (ha : ord E (a : E) = (h : WithTop ℤ))
    (hb : ord E (b : E) = (h : WithTop ℤ))
    (hab : CongruentAtDepth (h + (s : ℤ)) (a : E) (b : E)) :
    a / b ∈ unitFiltration E s := by
  have hab' : (a : E) - (b : E) ∈ lattice E (h + (s : ℤ)) := hab
  have hdiv : ((a : E) - (b : E)) / (b : E) ∈ lattice E (s : ℤ) :=
    (div_mem_lattice_iff E (b : E) ((a : E) - (b : E)) h (s : ℤ) hb).2 hab'
  have hratioOrder : ord E ((a / b : Eˣ) : E) = 0 := by
    rw [Units.val_div_eq_div_val, ord_div, ha, hb]
    simp
  have hratio0 : a / b ∈ unitGroup E :=
    (mem_unitGroup_iff_ord_eq_zero E (a / b)).2 hratioOrder
  have hcongruent : CongruentAtDepth (s : ℤ) ((a / b : Eˣ) : E) 1 := by
    change ((s : ℤ) : WithTop ℤ) ≤ ord E (((a / b : Eˣ) : E) - 1)
    rw [Units.val_div_eq_div_val, div_sub_one (Units.ne_zero b)]
    exact hdiv
  have hmem := (div_mem_unitFiltration_iff_congruentAtDepth E s (a / b) 1
    hratio0 (unitGroup E).one_mem).2 hcongruent
  simpa only [div_one] using hmem

/-- `c1` is an exact norm representative of the exact-depth coefficient
`c` modulo `p_F^(h+s)`.  This is a predicate on a supplied element, not a
choice of one. -/
structure IsSubcriticalNormRepresentative
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [Module.Free F K]
    (h : ℤ) (s : ℕ) (c : Fˣ) (c1 : Kˣ) : Prop where
  /-- The stationary coefficient is in the exact target shell of depth `h`. -/
  coefficient_order : ord F (c : F) = (h : WithTop ℤ)
  /-- The chosen upstairs element is in the exact source shell of depth `h`. -/
  source_order : ord K (c1 : K) = (h : WithTop ℤ)
  /-- Its exact norm is in the exact target shell of depth `h`. -/
  norm_order : ord F (norm F K (c1 : K)) = (h : WithTop ℤ)
  /-- The congruence direction is the manuscript's `c - N(c1)`. -/
  norm_congruent : (c : F) - norm F K (c1 : K) ∈ lattice F (h + (s : ℤ))

namespace IsSubcriticalNormRepresentative

variable {F K : Type*} [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [Module.Free F K]
  {h : ℤ} {r s : ℕ} {c : Fˣ} {c1 : Kˣ}

/-- A representative valid at a finer precision is the same representative
at every coarser precision. -/
theorem mono (hrs : r ≤ s)
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    IsSubcriticalNormRepresentative F K h r c c1 where
  coefficient_order := hc1.coefficient_order
  source_order := hc1.source_order
  norm_order := hc1.norm_order
  norm_congruent :=
    lattice_antitone F (by omega) hc1.norm_congruent

/-- The coefficient occupies exactly the numerator lattice shell. -/
theorem coefficient_exactDepth
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    (c : F) ∈ lattice F h ∧ (c : F) ∉ lattice F (h + 1) :=
  (mem_lattice_and_not_mem_succ_iff F).2 hc1.coefficient_order

/-- The chosen source element occupies exactly the requested source shell. -/
theorem source_exactDepth
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    (c1 : K) ∈ lattice K h ∧ (c1 : K) ∉ lattice K (h + 1) :=
  (mem_lattice_and_not_mem_succ_iff K).2 hc1.source_order

/-- The exact norm occupies exactly the requested target shell. -/
theorem norm_exactDepth
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    norm F K (c1 : K) ∈ lattice F h ∧
      norm F K (c1 : K) ∉ lattice F (h + 1) :=
  (mem_lattice_and_not_mem_succ_iff F).2 hc1.norm_order

/-- Additive depth-congruence form of the defining norm congruence. -/
theorem congruentAtDepth
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    CongruentAtDepth (h + (s : ℤ)) (c : F) (norm F K (c1 : K)) :=
  hc1.norm_congruent

/-- Quotient-level form: the coefficient and the exact norm determine the
same class in `p_F^h / p_F^(h+s)`. -/
theorem latticeQuotient_eq
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
        (⟨(c : F), hc1.coefficient_exactDepth.1⟩ : lattice F h) =
      latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
        (⟨norm F K (c1 : K), hc1.norm_exactDepth.1⟩ : lattice F h) := by
  exact (latticeQuotientMk_eq_mk_iff F (by omega)).2 hc1.norm_congruent

/-- If two exact-depth coefficient representatives give the same class,
then the norms of any two valid choices give that same class as well.  This
is independence only modulo the permitted target lattice; it does not assert
that the two source elements are equal. -/
theorem norm_congruent_of_coefficient_congruent
    {d : Fˣ} {d1 : Kˣ}
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1)
    (hd1 : IsSubcriticalNormRepresentative F K h s d d1)
    (hcd : (c : F) - (d : F) ∈ lattice F (h + (s : ℤ))) :
    norm F K (c1 : K) - norm F K (d1 : K) ∈
      lattice F (h + (s : ℤ)) := by
  have hleft := neg_mem_lattice F hc1.norm_congruent
  have hsum := add_mem_lattice F (add_mem_lattice F hleft hcd) hd1.norm_congruent
  convert hsum using 1
  ring

/-- Any two norm choices for one coefficient differ only by the permitted
target ambiguity.  No uniqueness of the elements of `Kˣ` is claimed. -/
theorem norm_independent
    {d1 : Kˣ}
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1)
    (hd1 : IsSubcriticalNormRepresentative F K h s c d1) :
    norm F K (c1 : K) - norm F K (d1 : K) ∈
      lattice F (h + (s : ℤ)) :=
  norm_congruent_of_coefficient_congruent hc1 hd1
    (by simp)

/-- Quotient-level form of independence of the norm choice. -/
theorem norm_latticeQuotient_independent
    {d1 : Kˣ}
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1)
    (hd1 : IsSubcriticalNormRepresentative F K h s c d1) :
    latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
        (⟨norm F K (c1 : K), hc1.norm_exactDepth.1⟩ : lattice F h) =
      latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
        (⟨norm F K (d1 : K), hd1.norm_exactDepth.1⟩ : lattice F h) := by
  exact (latticeQuotientMk_eq_mk_iff F (by omega)).2
    (norm_independent hc1 hd1)

/-- The finer quotient equality projects to the corresponding equality at
every coarser precision.  The same supplied representative is reused. -/
theorem latticeQuotient_projection
    (hrs : r ≤ s)
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1) :
    latticeQuotientProjection F
        (show h ≤ h + (r : ℤ) by omega)
        (show h + (r : ℤ) ≤ h + (s : ℤ) by omega)
        (latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
          (⟨norm F K (c1 : K), hc1.norm_exactDepth.1⟩ : lattice F h)) =
      latticeQuotientMk F (show h ≤ h + (r : ℤ) by omega)
        (⟨(c : F), hc1.coefficient_exactDepth.1⟩ : lattice F h) := by
  rw [latticeQuotientProjection_mk]
  exact (latticeQuotient_eq (hc1.mono hrs)).symm

end IsSubcriticalNormRepresentative

section PrimeCyclic

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
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)

include ht hres pi hpi hgen

/-- **Norm representatives at subcritical precision.**  If `c` has exact
order `h` and `s ≤ t`, there is a nonzero `c1` of exact order `h` whose
field norm represents the class of `c` modulo `p_F^(h+s)`.

The witness is existential.  In particular, this theorem does not define a
canonical representative. -/
theorem normRepresentative_subcritical
    {h : ℤ} {s : ℕ} (hs : s ≤ t) (c : Fˣ)
    (hc : ord F (c : F) = (h : WithTop ℤ)) :
    ∃ c1 : Kˣ, IsSubcriticalNormRepresentative F K h s c c1 := by
  obtain ⟨c1, herr⟩ :=
    exists_norm_representative_mod_break F K ht hres pi hpi hgen c
  let n : Fˣ := normUnits F K c1
  let u : Fˣ := c / n
  have hu : u ∈ unitFiltration F t := by
    simpa only [u, n] using herr
  have hu0 : u ∈ unitGroup F := unitFiltration_le_unitGroup F t hu
  have huOrder : ord F (u : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F u).1 hu0
  have hcFactor : (c : F) = (n : F) * (u : F) := by
    dsimp only [u]
    rw [Units.val_div_eq_div_val]
    exact (mul_div_cancel₀ (c : F) (Units.ne_zero n)).symm
  have hnOrder : ord F (n : F) = (h : WithTop ℤ) := by
    rw [hcFactor, ord_mul, huOrder, add_zero] at hc
    exact hc
  have hc1Order : ord K (c1 : K) = (h : WithTop ℤ) := by
    dsimp only [n] at hnOrder
    rw [coe_normUnits, ord_norm, hres, one_nsmul] at hnOrder
    exact hnOrder
  have huCongruent : CongruentAtDepth (t : ℤ) (u : F) 1 := by
    apply (div_mem_unitFiltration_iff_congruentAtDepth F t u 1 hu0
      (unitGroup F).one_mem).1
    simpa only [div_one] using hu
  have hscaled : CongruentAtDepth (h + (t : ℤ))
      ((n : F) * (u : F)) ((n : F) * 1) :=
    CongruentAtDepth.mul_left_shift (r := h) (s := (t : ℤ))
      (n : F) (by rw [hnOrder]) huCongruent
  have hcongruent := CongruentAtDepth.mono (m := h + (s : ℤ))
    (n := h + (t : ℤ)) (by omega) hscaled
  rw [← hcFactor] at hcongruent
  have hcongruent' : CongruentAtDepth (h + (s : ℤ))
      (c : F) (norm F K (c1 : K)) := by
    simpa only [mul_one, n, coe_normUnits] using hcongruent
  exact ⟨c1, hc, hc1Order, hnOrder, hcongruent'⟩

/-- The source ambiguity is also exactly controlled below the break.  If
two coefficient representatives determine the same target class, then any
corresponding norm representatives differ by an element of `U_K^s`.
This is quotient uniqueness only; it is not equality or a canonical choice. -/
theorem subcriticalNormRepresentatives_source_ratio_mem
    {h : ℤ} {s : ℕ} (hs : s ≤ t)
    {c d : Fˣ} {c1 d1 : Kˣ}
    (hcd : CongruentAtDepth (h + (s : ℤ)) (c : F) (d : F))
    (hc1 : IsSubcriticalNormRepresentative F K h s c c1)
    (hd1 : IsSubcriticalNormRepresentative F K h s d d1) :
    c1 / d1 ∈ unitFiltration K s := by
  have hnormCongruent : CongruentAtDepth (h + (s : ℤ))
      (norm F K (c1 : K)) (norm F K (d1 : K)) :=
    hc1.congruentAtDepth.symm.trans (hcd.trans hd1.congruentAtDepth)
  have hnormRatio : normUnits F K c1 / normUnits F K d1 ∈
      unitFiltration F s :=
    div_mem_unitFiltration_of_exactOrder_congruentAtDepth
      (normUnits F K c1) (normUnits F K d1)
      hc1.norm_order hd1.norm_order
      (by simpa only [coe_normUnits] using hnormCongruent)
  have hsource0 : c1 / d1 ∈ unitFiltration K 0 := by
    rw [mem_unitFiltration_zero, Units.val_div_eq_div_val, ord_div,
      hc1.source_order, hd1.source_order]
    simp
  apply mem_unitFiltration_of_norm_mem_of_graded_injective F K (Nat.zero_le s)
    (fun i _ his ↦ normMapsUnitFiltration_belowBreak F K ht
      (his.trans hs) hres pi hpi hgen)
    (fun i _ his ↦ by
      simpa only using
        (gradedNorm_bijective_belowBreak F K ht (his.trans_le hs)
          hres pi hpi hgen).1)
    (c1 / d1) hsource0
  simpa only [map_div] using hnormRatio

/-- One existential witness may be used at all permitted subcritical
precisions simultaneously.  This is compatibility by reuse of a witness,
not a canonical choice depending on the precision. -/
theorem normRepresentative_all_subcriticalPrecisions
    {h : ℤ} (c : Fˣ) (hc : ord F (c : F) = (h : WithTop ℤ)) :
    ∃ c1 : Kˣ, ∀ s : ℕ, s ≤ t →
      IsSubcriticalNormRepresentative F K h s c c1 := by
  obtain ⟨c1, hc1⟩ :=
    normRepresentative_subcritical F K ht hres pi hpi hgen
      (le_rfl : t ≤ t) c hc
  exact ⟨c1, fun s hs ↦ hc1.mono hs⟩

/-- A heterogeneous finite family of stationary coefficient classes has
pointwise independent, hence simultaneous, exact norm representatives.
The depths and precisions may vary with the index. -/
theorem normRepresentatives_subcritical_finite
    {I : Type*} [Fintype I]
    (h : I → ℤ) (s : I → ℕ) (hs : ∀ i, s i ≤ t)
    (c : I → Fˣ)
    (hc : ∀ i, ord F (c i : F) = (h i : WithTop ℤ)) :
    ∃ c1 : I → Kˣ, ∀ i,
      IsSubcriticalNormRepresentative F K (h i) (s i) (c i) (c1 i) := by
  classical
  have hex : ∀ i, ∃ c1 : Kˣ,
      IsSubcriticalNormRepresentative F K (h i) (s i) (c i) c1 :=
    fun i ↦ normRepresentative_subcritical F K ht hres pi hpi hgen
      (hs i) (c i) (hc i)
  choose c1 hc1 using hex
  exact ⟨c1, hc1⟩

/-- A finite family can be chosen once and reused at every precision below
the break.  The family is obtained pointwise, with no relation imposed
between distinct choices. -/
theorem normRepresentatives_all_subcriticalPrecisions_finite
    {I : Type*} [Fintype I]
    (h : I → ℤ) (c : I → Fˣ)
    (hc : ∀ i, ord F (c i : F) = (h i : WithTop ℤ)) :
    ∃ c1 : I → Kˣ, ∀ i (s : ℕ), s ≤ t →
      IsSubcriticalNormRepresentative F K (h i) s (c i) (c1 i) := by
  classical
  have hex : ∀ i, ∃ c1 : Kˣ, ∀ s : ℕ, s ≤ t →
      IsSubcriticalNormRepresentative F K (h i) s (c i) c1 :=
    fun i ↦ normRepresentative_all_subcriticalPrecisions
      F K ht hres pi hpi hgen (c i) (hc i)
  choose c1 hc1 using hex
  exact ⟨c1, hc1⟩

/-- Quotient-class form of the existence theorem.  The explicit exact-shell
representative hypothesis is essential: an arbitrary quotient element, for
example the zero class, need not have order exactly `h`. -/
theorem normRepresentative_subcritical_latticeQuotient
    {h : ℤ} {s : ℕ} (hs : s ≤ t)
    (z : LatticeQuotient F h (h + (s : ℤ)) (by omega))
    (c : Fˣ) (hc : ord F (c : F) = (h : WithTop ℤ))
    (hz : latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
      (⟨(c : F), by rw [mem_lattice, hc]⟩ : lattice F h) = z) :
    ∃ (c1 : Kˣ) (hc1 : IsSubcriticalNormRepresentative F K h s c c1),
      latticeQuotientMk F (show h ≤ h + (s : ℤ) by omega)
        (⟨norm F K (c1 : K), hc1.norm_exactDepth.1⟩ : lattice F h) = z := by
  obtain ⟨c1, hc1⟩ :=
    normRepresentative_subcritical F K ht hres pi hpi hgen hs c hc
  refine ⟨c1, hc1, ?_⟩
  exact hc1.latticeQuotient_eq.symm.trans hz

/-- Multiplying an exact norm by any supplied target unit gives the
rescaled representative used in the wild quadratic calculation.  The
exact norm itself remains a separate existential witness. -/
theorem normRepresentative_subcritical_mul_unit
    {h : ℤ} {s : ℕ} (hs : s ≤ t)
    (c delta : Fˣ) (hdelta : delta ∈ unitGroup F)
    (hc : ord F (c : F) = (h : WithTop ℤ)) :
    ∃ c1 : Kˣ,
      IsSubcriticalNormRepresentative F K h s (c / delta) c1 ∧
      (c : F) - (delta : F) * norm F K (c1 : K) ∈
        lattice F (h + (s : ℤ)) := by
  have hdeltaOrder : ord F (delta : F) = 0 :=
    (mem_unitGroup_iff_ord_eq_zero F delta).1 hdelta
  have hcdiv : ord F ((c / delta : Fˣ) : F) = (h : WithTop ℤ) := by
    rw [Units.val_div_eq_div_val, ord_div, hc, hdeltaOrder]
    simp
  obtain ⟨c1, hc1⟩ :=
    normRepresentative_subcritical F K ht hres pi hpi hgen hs (c / delta) hcdiv
  refine ⟨c1, hc1, ?_⟩
  have hscaled := CongruentAtDepth.mul_left
    (a := (delta : F)) (by rw [hdeltaOrder]) hc1.congruentAtDepth
  change CongruentAtDepth (h + (s : ℤ))
    ((delta : F) * ((c / delta : Fˣ) : F))
    ((delta : F) * norm F K (c1 : K)) at hscaled
  rw [Units.val_div_eq_div_val,
    mul_div_cancel₀ (c : F) (Units.ne_zero delta)] at hscaled
  exact hscaled

/-- Break-level unit correction used when a requested stationary precision
may exceed `t` (the wild quadratic `beta` case).  A target unit is written
exactly as a depth-`t` correction times a norm of a source unit.  No deeper
norm congruence is asserted. -/
theorem unit_eq_unitFiltration_mul_norm
    (c : Fˣ) (hc : c ∈ unitGroup F) :
    ∃ c1 : Kˣ, c1 ∈ unitGroup K ∧
      ∃ delta : unitFiltration F t,
        c = (delta : Fˣ) * normUnits F K c1 := by
  have hcOrder : ord F (c : F) = ((0 : ℤ) : WithTop ℤ) :=
    (mem_unitGroup_iff_ord_eq_zero F c).1 hc
  obtain ⟨c1, hc1⟩ :=
    normRepresentative_subcritical F K ht hres pi hpi hgen
      (le_rfl : t ≤ t) c hcOrder
  have hratio : c / normUnits F K c1 ∈ unitFiltration F t :=
    div_mem_unitFiltration_of_exactOrder_congruentAtDepth
      c (normUnits F K c1) hc1.coefficient_order hc1.norm_order
      (by simpa only [zero_add, coe_normUnits] using hc1.congruentAtDepth)
  let delta : unitFiltration F t := ⟨c / normUnits F K c1, hratio⟩
  refine ⟨c1, (mem_unitGroup_iff_ord_eq_zero K c1).2 hc1.source_order,
    delta, ?_⟩
  apply Units.ext
  change (c : F) = ((c / normUnits F K c1 : Fˣ) : F) *
    (normUnits F K c1 : F)
  rw [Units.val_div_eq_div_val,
    div_mul_cancel₀ (c : F) (Units.ne_zero (normUnits F K c1))]

end PrimeCyclic

end

end LanglandsFirstMainLemma
