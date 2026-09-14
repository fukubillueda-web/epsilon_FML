import LanglandsFirstMainLemma.Ramification.PrimeCyclicExtension

/-!
# One-break Herbrand functions

For a prime-cyclic extension with unique lower break `t` and degree `ℓ`, the lower-to-upper
Herbrand function has slope one through `t` and slope `1 / ℓ` after `t`.  Its inverse has
slope one through `t` and slope `ℓ` after `t`.

The real functions below are defined directly as continuous broken-linear maps, rather than
by storing their piecewise formulas as assumptions.  The natural-number function
`herbrandPsiNat` records the fact that the inverse Herbrand function carries every integral
upper depth to an integral lower depth.  In particular, it keeps the two source depths
`Ψ(r)` and `Ψ(r) + 1` used by the norm-filtration theorem distinct from the next Herbrand
level `Ψ(r + 1) = Ψ(r) + ℓ`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

/-- The lower-to-upper Herbrand function for one lower break `t` and degree `ℓ`.

The expression uses the length below the break, `min u t`, plus the length above the break
scaled by `1 / ℓ`.  It is a total real function; on the manuscript's domain `u ≥ -1` it is
the integral of the one-break ramification density. -/
def herbrandPhi (t ℓ : ℕ) (u : ℝ) : ℝ :=
  min u (t : ℝ) + max (u - (t : ℝ)) 0 / (ℓ : ℝ)

/-- The upper-to-lower inverse Herbrand function for one lower break `t` and degree `ℓ`.

The part above the break is scaled by `ℓ`. -/
def herbrandPsi (t ℓ : ℕ) (v : ℝ) : ℝ :=
  min v (t : ℝ) + (ℓ : ℝ) * max (v - (t : ℝ)) 0

/-- The integral lower depth corresponding to a natural upper depth in the one-break case. -/
def herbrandPsiNat (t ℓ r : ℕ) : ℕ :=
  min r t + ℓ * (r - t)

@[simp]
theorem herbrandPhi_of_le_break (t ℓ : ℕ) {u : ℝ} (hu : u ≤ (t : ℝ)) :
    herbrandPhi t ℓ u = u := by
  rw [herbrandPhi, min_eq_left hu, max_eq_right (sub_nonpos.mpr hu)]
  simp

@[simp]
theorem herbrandPhi_of_break_le (t ℓ : ℕ) {u : ℝ} (hu : (t : ℝ) ≤ u) :
    herbrandPhi t ℓ u = (t : ℝ) + (u - (t : ℝ)) / (ℓ : ℝ) := by
  rw [herbrandPhi, min_eq_right hu, max_eq_left (sub_nonneg.mpr hu)]

@[simp]
theorem herbrandPsi_of_le_break (t ℓ : ℕ) {v : ℝ} (hv : v ≤ (t : ℝ)) :
    herbrandPsi t ℓ v = v := by
  rw [herbrandPsi, min_eq_left hv, max_eq_right (sub_nonpos.mpr hv)]
  simp

@[simp]
theorem herbrandPsi_of_break_le (t ℓ : ℕ) {v : ℝ} (hv : (t : ℝ) ≤ v) :
    herbrandPsi t ℓ v = (t : ℝ) + (ℓ : ℝ) * (v - (t : ℝ)) := by
  rw [herbrandPsi, min_eq_right hv, max_eq_left (sub_nonneg.mpr hv)]

@[simp]
theorem herbrandPhi_break (t ℓ : ℕ) :
    herbrandPhi t ℓ (t : ℝ) = (t : ℝ) :=
  herbrandPhi_of_le_break t ℓ le_rfl

@[simp]
theorem herbrandPsi_break (t ℓ : ℕ) :
    herbrandPsi t ℓ (t : ℝ) = (t : ℝ) :=
  herbrandPsi_of_le_break t ℓ le_rfl

@[simp]
theorem herbrandPhi_neg_one (t ℓ : ℕ) : herbrandPhi t ℓ (-1) = -1 := by
  apply herbrandPhi_of_le_break
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  linarith

@[simp]
theorem herbrandPsi_neg_one (t ℓ : ℕ) : herbrandPsi t ℓ (-1) = -1 := by
  apply herbrandPsi_of_le_break
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  linarith

/-- The one-break lower-to-upper Herbrand function is monotone. -/
theorem herbrandPhi_monotone (t ℓ : ℕ) : Monotone (herbrandPhi t ℓ) := by
  intro u v huv
  apply add_le_add
  · exact min_le_min huv le_rfl
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg ℓ)
    exact max_le_max (sub_le_sub_right huv _) le_rfl

/-- The one-break upper-to-lower Herbrand function is monotone. -/
theorem herbrandPsi_monotone (t ℓ : ℕ) : Monotone (herbrandPsi t ℓ) := by
  intro u v huv
  apply add_le_add
  · exact min_le_min huv le_rfl
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg ℓ)
    exact max_le_max (sub_le_sub_right huv _) le_rfl

/-- The one-break lower-to-upper Herbrand function is continuous, including at the break. -/
theorem continuous_herbrandPhi (t ℓ : ℕ) : Continuous (herbrandPhi t ℓ) := by
  exact (continuous_id.min continuous_const).add
    (((continuous_id.sub continuous_const).max continuous_const).div_const _)

/-- The one-break upper-to-lower Herbrand function is continuous, including at the break. -/
theorem continuous_herbrandPsi (t ℓ : ℕ) : Continuous (herbrandPsi t ℓ) := by
  exact (continuous_id.min continuous_const).add
    (((continuous_id.sub continuous_const).max continuous_const).const_mul _)

/-- Applying `ψ` after `φ` returns the original lower depth. -/
theorem herbrandPsi_herbrandPhi (t ℓ : ℕ) (hℓ : 0 < ℓ) (u : ℝ) :
    herbrandPsi t ℓ (herbrandPhi t ℓ u) = u := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  by_cases hu : u ≤ (t : ℝ)
  · rw [herbrandPhi_of_le_break t ℓ hu, herbrandPsi_of_le_break t ℓ hu]
  · have htu : (t : ℝ) ≤ u := le_of_not_ge hu
    rw [herbrandPhi_of_break_le t ℓ htu]
    have himage : (t : ℝ) ≤ (t : ℝ) + (u - (t : ℝ)) / (ℓ : ℝ) := by
      exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr htu) hℓR.le)
    rw [herbrandPsi_of_break_le t ℓ himage]
    field_simp
    ring

/-- Applying `φ` after `ψ` returns the original upper depth. -/
theorem herbrandPhi_herbrandPsi (t ℓ : ℕ) (hℓ : 0 < ℓ) (v : ℝ) :
    herbrandPhi t ℓ (herbrandPsi t ℓ v) = v := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  by_cases hv : v ≤ (t : ℝ)
  · rw [herbrandPsi_of_le_break t ℓ hv, herbrandPhi_of_le_break t ℓ hv]
  · have htv : (t : ℝ) ≤ v := le_of_not_ge hv
    rw [herbrandPsi_of_break_le t ℓ htv]
    have himage : (t : ℝ) ≤ (t : ℝ) + (ℓ : ℝ) * (v - (t : ℝ)) := by
      exact le_add_of_nonneg_right (mul_nonneg hℓR.le (sub_nonneg.mpr htv))
    rw [herbrandPhi_of_break_le t ℓ himage]
    field_simp
    ring

/-- `ψ` is a left inverse of `φ`. -/
theorem herbrandPsi_leftInverse_herbrandPhi (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    Function.LeftInverse (herbrandPsi t ℓ) (herbrandPhi t ℓ) :=
  herbrandPsi_herbrandPhi t ℓ hℓ

/-- `ψ` is a right inverse of `φ`. -/
theorem herbrandPsi_rightInverse_herbrandPhi (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    Function.RightInverse (herbrandPsi t ℓ) (herbrandPhi t ℓ) :=
  herbrandPhi_herbrandPsi t ℓ hℓ

/-- Positive degree makes the one-break lower-to-upper Herbrand function strictly increasing. -/
theorem herbrandPhi_strictMono (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    StrictMono (herbrandPhi t ℓ) :=
  (herbrandPhi_monotone t ℓ).strictMono_of_injective
    (herbrandPsi_leftInverse_herbrandPhi t ℓ hℓ).injective

/-- Positive degree makes the one-break upper-to-lower Herbrand function strictly increasing. -/
theorem herbrandPsi_strictMono (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    StrictMono (herbrandPsi t ℓ) :=
  (herbrandPsi_monotone t ℓ).strictMono_of_injective
    (herbrandPsi_rightInverse_herbrandPhi t ℓ hℓ).injective

/-- Lower-to-upper numbering never raises a depth when the degree is positive. -/
theorem herbrandPhi_le_self (t ℓ : ℕ) (hℓ : 0 < ℓ) (u : ℝ) :
    herbrandPhi t ℓ u ≤ u := by
  by_cases hu : u ≤ (t : ℝ)
  · rw [herbrandPhi_of_le_break t ℓ hu]
  · have htu : (t : ℝ) ≤ u := le_of_not_ge hu
    rw [herbrandPhi_of_break_le t ℓ htu]
    have h1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    have hdiv := div_le_self (sub_nonneg.mpr htu) h1
    linarith

/-- Upper-to-lower numbering never lowers a depth when the degree is positive. -/
theorem self_le_herbrandPsi (t ℓ : ℕ) (hℓ : 0 < ℓ) (v : ℝ) :
    v ≤ herbrandPsi t ℓ v := by
  by_cases hv : v ≤ (t : ℝ)
  · rw [herbrandPsi_of_le_break t ℓ hv]
  · have htv : (t : ℝ) ≤ v := le_of_not_ge hv
    rw [herbrandPsi_of_break_le t ℓ htv]
    have h1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    have hmul := mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr htv)
    linarith

@[simp]
theorem herbrandPsiNat_of_le_break (t ℓ : ℕ) {r : ℕ} (hr : r ≤ t) :
    herbrandPsiNat t ℓ r = r := by
  simp [herbrandPsiNat, min_eq_left hr, Nat.sub_eq_zero_of_le hr]

@[simp]
theorem herbrandPsiNat_of_break_le (t ℓ : ℕ) {r : ℕ} (hr : t ≤ r) :
    herbrandPsiNat t ℓ r = t + ℓ * (r - t) := by
  rw [herbrandPsiNat, min_eq_right hr]

@[simp]
theorem herbrandPsiNat_break (t ℓ : ℕ) : herbrandPsiNat t ℓ t = t :=
  herbrandPsiNat_of_le_break t ℓ le_rfl

/-- Natural and real inverse Herbrand depths agree exactly. -/
@[norm_cast]
theorem herbrandPsiNat_cast (t ℓ r : ℕ) :
    (herbrandPsiNat t ℓ r : ℝ) = herbrandPsi t ℓ (r : ℝ) := by
  rcases le_total r t with hrt | htr
  · rw [herbrandPsiNat_of_le_break t ℓ hrt,
      herbrandPsi_of_le_break t ℓ (by exact_mod_cast hrt)]
  · rw [herbrandPsiNat_of_break_le t ℓ htr,
      herbrandPsi_of_break_le t ℓ (by exact_mod_cast htr)]
    push_cast [Nat.cast_sub htr]
    rfl

/-- The real lower-to-upper function sends an integral inverse depth back to its upper depth. -/
@[simp]
theorem herbrandPhi_herbrandPsiNat_cast (t ℓ r : ℕ) (hℓ : 0 < ℓ) :
    herbrandPhi t ℓ (herbrandPsiNat t ℓ r : ℝ) = (r : ℝ) := by
  rw [herbrandPsiNat_cast]
  exact herbrandPhi_herbrandPsi t ℓ hℓ (r : ℝ)

/-- The ceiling of an integral inverse Herbrand depth is the same integral depth. -/
@[simp]
theorem ceil_herbrandPsi_natCast (t ℓ r : ℕ) :
    ⌈herbrandPsi t ℓ (r : ℝ)⌉ = (herbrandPsiNat t ℓ r : ℤ) := by
  rw [← herbrandPsiNat_cast]
  exact Int.ceil_natCast _

/-- The floor of an integral inverse Herbrand depth is the same integral depth. -/
@[simp]
theorem floor_herbrandPsi_natCast (t ℓ r : ℕ) :
    ⌊herbrandPsi t ℓ (r : ℝ)⌋ = (herbrandPsiNat t ℓ r : ℤ) := by
  rw [← herbrandPsiNat_cast]
  exact Int.floor_natCast _

/-- The `+1` source exponent in the norm theorem is an exact natural depth. -/
theorem herbrandPsi_natCast_add_one (t ℓ r : ℕ) :
    herbrandPsi t ℓ (r : ℝ) + 1 = (herbrandPsiNat t ℓ r + 1 : ℕ) := by
  rw [← herbrandPsiNat_cast]
  norm_num

/-- Above the break, increasing the upper depth by `k` increases the lower depth by `ℓ * k`. -/
theorem herbrandPsiNat_add (t ℓ : ℕ) {r : ℕ} (hr : t ≤ r) (k : ℕ) :
    herbrandPsiNat t ℓ (r + k) = herbrandPsiNat t ℓ r + ℓ * k := by
  rw [herbrandPsiNat_of_break_le t ℓ hr,
    herbrandPsiNat_of_break_le t ℓ (hr.trans (Nat.le_add_right r k))]
  have hsub : r + k - t = r - t + k := by omega
  rw [hsub, Nat.mul_add]
  omega

/-- The next integral Herbrand level above the break is `ℓ` lower levels away. -/
theorem herbrandPsiNat_succ (t ℓ : ℕ) {r : ℕ} (hr : t ≤ r) :
    herbrandPsiNat t ℓ (r + 1) = herbrandPsiNat t ℓ r + ℓ := by
  simpa using herbrandPsiNat_add t ℓ hr 1

@[simp]
theorem herbrandPsiNat_break_succ (t ℓ : ℕ) :
    herbrandPsiNat t ℓ (t + 1) = t + ℓ := by
  rw [herbrandPsiNat_succ t ℓ le_rfl, herbrandPsiNat_break]

/-- The natural inverse-depth conversion is strictly increasing for positive degree. -/
theorem herbrandPsiNat_strictMono (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    StrictMono (herbrandPsiNat t ℓ) := by
  intro r s hrs
  have hrsR : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
  have hreal := herbrandPsi_strictMono t ℓ hℓ hrsR
  rw [← herbrandPsiNat_cast, ← herbrandPsiNat_cast] at hreal
  exact_mod_cast hreal

/-- The natural inverse-depth conversion is monotone for positive degree. -/
theorem herbrandPsiNat_monotone (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    Monotone (herbrandPsiNat t ℓ) :=
  (herbrandPsiNat_strictMono t ℓ hℓ).monotone

/-- Natural inverse Herbrand depths tend to infinity, as required for successive lifting. -/
theorem tendsto_herbrandPsiNat_atTop (t ℓ : ℕ) (hℓ : 0 < ℓ) :
    Filter.Tendsto (herbrandPsiNat t ℓ) Filter.atTop Filter.atTop :=
  (herbrandPsiNat_strictMono t ℓ hℓ).tendsto_atTop

/-- Every natural upper depth is at most its corresponding lower depth. -/
theorem self_le_herbrandPsiNat (t ℓ : ℕ) (hℓ : 0 < ℓ) (r : ℕ) :
    r ≤ herbrandPsiNat t ℓ r := by
  have hreal := self_le_herbrandPsi t ℓ hℓ (r : ℝ)
  rw [← herbrandPsiNat_cast] at hreal
  exact_mod_cast hreal

/-- The norm theorem's depth `Ψ(r) + 1` is strictly below the next Herbrand level.

This is the off-by-one distinction between the second norm equality at upper depth `r` and
the first norm equality at upper depth `r + 1`. -/
theorem herbrandPsiNat_add_one_lt_succ (t ℓ : ℕ) (hℓ : ℓ.Prime)
    {r : ℕ} (hr : t ≤ r) :
    herbrandPsiNat t ℓ r + 1 < herbrandPsiNat t ℓ (r + 1) := by
  rw [herbrandPsiNat_succ t ℓ hr]
  exact Nat.add_lt_add_left hℓ.one_lt _

/-- Exact doubled-depth conversion above the break.

The manuscript uses `e = 0` or `e = 1`; the same identity holds for every natural `e`. -/
theorem herbrandPsiNat_two_mul_add (t ℓ : ℕ) (hℓ : 0 < ℓ)
    {s : ℕ} (hs : t ≤ s) (e : ℕ) :
    herbrandPsiNat t ℓ (2 * s + e) =
      2 * herbrandPsiNat t ℓ s + (ℓ - 1) * t + ℓ * e := by
  rw [herbrandPsiNat_of_break_le t ℓ hs,
    herbrandPsiNat_of_break_le t ℓ (by omega : t ≤ 2 * s + e)]
  have hsub : 2 * s + e - t = t + 2 * (s - t) + e := by omega
  rw [hsub]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓ)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-- Taking half of an upper depth and then applying `Ψ` is bounded by half the lower depth.

Natural-number division by two is the floor appearing in the manuscript's stationary-depth
calculation. -/
theorem herbrandPsiNat_half_le_half (t ℓ : ℕ) (hℓ : 0 < ℓ) (r : ℕ) :
    herbrandPsiNat t ℓ (r / 2) ≤ herbrandPsiNat t ℓ r / 2 := by
  by_cases hr : r / 2 ≤ t
  · rw [herbrandPsiNat_of_le_break t ℓ hr]
    exact Nat.div_le_div_right (self_le_herbrandPsiNat t ℓ hℓ r)
  · have htr : t ≤ r / 2 := le_of_not_ge hr
    have hformula := herbrandPsiNat_two_mul_add t ℓ hℓ htr (r % 2)
    rw [Nat.div_add_mod r 2] at hformula
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    rw [hformula]
    omega

/-- The subtraction-free stationary-depth identity used after the high-conductor conversion.

The manuscript only needs parity digits `ε ∈ {0,1}`, but the identity is valid for every
natural `ε`. -/
theorem herbrandPsiNat_stationary_depth (t ℓ : ℕ) (hℓ : 0 < ℓ)
    {d : ℕ} (hd : t + 2 ≤ d) (ε : ℕ) :
    herbrandPsiNat t ℓ (2 * d + ε - 1) + 1 =
      2 * (herbrandPsiNat t ℓ (d - 1) + 1) +
        (ℓ - 1) * (t + 1) + ℓ * ε := by
  have hdlower : t ≤ d - 1 := by omega
  have hupper : t ≤ 2 * d + ε - 1 := by omega
  rw [herbrandPsiNat_of_break_le t ℓ hupper,
    herbrandPsiNat_of_break_le t ℓ hdlower]
  have hsub : 2 * d + ε - 1 - t =
      t + 1 + 2 * (d - 1 - t) + ε := by omega
  rw [hsub]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓ)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-- The complete mutual-inverse statement for an actual one-break prime-cyclic extension.

The lower-break hypothesis supplies the one-break situation; the functions themselves depend
only on its break and on the canonical extension degree, whose positivity follows from
primality. -/
theorem herbrand
    (F K : Type*) [Field F] [Field K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
    {t : ℕ} (_ht : PrimeCyclicExtension.IsLowerBreak F K t) :
    Function.LeftInverse
        (herbrandPsi t (Module.finrank F K))
        (herbrandPhi t (Module.finrank F K)) ∧
      Function.RightInverse
        (herbrandPsi t (Module.finrank F K))
        (herbrandPhi t (Module.finrank F K)) := by
  have hdegree : 0 < Module.finrank F K :=
    (PrimeCyclicExtension.degree_prime F K).pos
  exact ⟨herbrandPsi_leftInverse_herbrandPhi t _ hdegree,
    herbrandPsi_rightInverse_herbrandPhi t _ hdegree⟩

end

end LanglandsFirstMainLemma
