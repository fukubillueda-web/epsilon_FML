import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Ramification.NormBelowBreak
import LanglandsFirstMainLemma.Parameters.High
import LanglandsFirstMainLemma.Parameters.RamifiedHasseComparison
import LanglandsFirstMainLemma.Ramification.NormAboveBreak
import LanglandsFirstMainLemma.Ramification.SymmetricBounds
import LanglandsFirstMainLemma.Ramification.TraceIdeals
import LanglandsFirstMainLemma.Ramification.LowerGroups

/-!
# Local geometry for the ramified Hasse comparison

This file proves the local calculation which is common to the tame and wild
odd prime-degree stable-high cases.  The chosen upper uniformizer is the one
in `PrimeCyclicPreparation`; the lower uniformizer is its norm.  In
particular, none of the residual coordinates below may be independently
rescaled.

The public certificate at the end of the file contains the second-order norm
truncation, the trace and second-symmetric depth statements, the exact unit
order of the normalized trace, and the two residual coordinates.  It does
not contain a finite Hasse-function comparison.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

section Definitions

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- The source-tied upper uniformizer used in the Hasse calculation. -/
def ramifiedHasseUpperUniformizer
    (P : PrimeCyclicPreparation F K) : Kˣ :=
  phaseReductionUpperUniformizer K P.piK P.hpiK

/-- The ordered lower uniformizer: literally the norm of the chosen upper
uniformizer. -/
def ramifiedHasseLowerUniformizer
    (P : PrimeCyclicPreparation F K) : Fˣ :=
  phaseReductionLowerUniformizer F K P.piK P.hpiK

@[simp]
theorem ramifiedHasseUpperUniformizer_coe
    (P : PrimeCyclicPreparation F K) :
    (ramifiedHasseUpperUniformizer F K P : K) = (P.piK : K) :=
  rfl

@[simp]
theorem ramifiedHasseLowerUniformizer_coe
    (P : PrimeCyclicPreparation F K) :
    (ramifiedHasseLowerUniformizer F K P : F) = norm F K (P.piK : K) :=
  rfl

theorem ramifiedHasseUpperUniformizer_order
    (P : PrimeCyclicPreparation F K) :
    ord K (ramifiedHasseUpperUniformizer F K P : K) =
      ((1 : ℤ) : WithTop ℤ) :=
  phaseReductionUpperUniformizer_order K P.piK P.hpiK

theorem ramifiedHasseLowerUniformizer_order
    (P : PrimeCyclicPreparation F K) :
    ord F (ramifiedHasseLowerUniformizer F K P : F) =
      ((1 : ℤ) : WithTop ℤ) :=
  phaseReductionLowerUniformizer_order F K P.hres P.piK P.hpiK

@[simp]
theorem ramifiedHasse_norm_upperUniformizer
    (P : PrimeCyclicPreparation F K) :
    normUnits F K (ramifiedHasseUpperUniformizer F K P) =
      ramifiedHasseLowerUniformizer F K P :=
  rfl

/-- The actual perturbation used in the local norm calculation.  Keeping the
coefficient as a field element lets the depth and lift-independence statements
be stated before specializing to the Teichmuller representative. -/
def ramifiedHasseLocalInput
    (P : PrimeCyclicPreparation F K) (dK : ℕ) (a : F) : K :=
  (ramifiedHasseUpperUniformizer F K P : K) ^ dK * algebraMap F K a

/-- The normalized trace coefficient `epsilon` in the manuscript. -/
def ramifiedHasseNormalizedTrace
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) : F :=
  trace F K ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK)) /
    (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d)

/-- The field-level tame coordinate before taking its quotient class. -/
def ramifiedHasseTameCoordinateValue
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) : K :=
  (ramifiedHasseUpperUniformizer F K P : K) ^ dK /
    algebraMap F K ((ramifiedHasseLowerUniformizer F K P : F) ^ d)

/-- The chosen generator, retained as an element of the exact break group. -/
noncomputable def ramifiedHasseBreakGenerator
    (P : PrimeCyclicPreparation F K) :
    lowerRamificationGroup F K (P.t : ℤ) :=
  ⟨PrimeCyclicExtension.generator F K, by rw [P.ht.1]; trivial⟩

/-- The field-level wild coordinate with the manuscript's displacement
orientation `sigma(pi)-pi`. -/
def ramifiedHasseWildCoordinateValue
    (P : PrimeCyclicPreparation F K) : K :=
  (PrimeCyclicExtension.generator F K
      (ramifiedHasseUpperUniformizer F K P : K) -
      (ramifiedHasseUpperUniformizer F K P : K)) /
    (ramifiedHasseUpperUniformizer F K P : K) ^ (P.t + 1)

theorem ramifiedHasseWildCoordinateValue_eq_normalizedDisplacement
    (P : PrimeCyclicPreparation F K) :
    ramifiedHasseWildCoordinateValue F K P =
      (lowerRamificationNormalizedDisplacement F K
        (ramifiedHasseBreakGenerator F K P) (P.piK : K) P.hpiK : K) := by
  simp only [ramifiedHasseWildCoordinateValue,
    ramifiedHasseUpperUniformizer_coe,
    coe_lowerRamificationNormalizedDisplacement]
  change ((PrimeCyclicExtension.generator F K) (P.piK : K) - (P.piK : K)) /
      (P.piK : K) ^ (P.t + 1) =
    ((PrimeCyclicExtension.generator F K) (P.piK : K) - (P.piK : K)) /
      (P.piK : K) ^ ((P.t : ℤ) + 1)
  rw [show (P.t : ℤ) + 1 = ((P.t + 1 : ℕ) : ℤ) by omega, zpow_natCast]

end Definitions

section DepthArithmetic

private theorem ramifiedHasse_degree_three_le
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have hp2 := hp.two_le
  rcases hodd with ⟨q, hq⟩
  omega

/-- The stable relation puts the upper critical input strictly beyond the
target error depth. -/
private theorem ramifiedHasse_terminal_depth
    {p t d dK : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hd : 0 < d)
    (hstable : t = 0 ∨ t + 1 ≤ d)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    2 * d + 1 ≤ dK := by
  have hp3 : 3 ≤ p := ramifiedHasse_degree_three_le hp hodd
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  rcases hstable with ht0 | hs
  · subst t
    have htwo : 2 * dK = 2 * p * d := by simpa using hdepth
    nlinarith
  · nlinarith

/-- Twice the critical upper depth is exactly the Herbrand source depth of
the lower depth `2d`. -/
private theorem ramifiedHasse_aboveBreak_depth
    {p t d dK : ℕ} (hp : p.Prime)
    (hd : 0 < d)
    (hstable : t = 0 ∨ t + 1 ≤ d)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    aboveBreakSourceDepth t p (2 * d) = 2 * dK := by
  have htle : t ≤ 2 * d := by
    rcases hstable with rfl | hs
    · simp
    · omega
  rw [aboveBreakSourceDepth_eq t p htle]
  have hsub : 2 * d - t + t = 2 * d := Nat.sub_add_cancel htle
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  nlinarith

private theorem ramifiedHasse_trace_floor_ge
    {p t d dK : ℕ} (hp : p.Prime)
    (hd : 0 < d)
    (hstable : t = 0 ∨ t + 1 ≤ d)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    (d : ℤ) ≤
      ((dK : ℤ) + (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hdepthZ :
      2 * (dK : ℤ) + ((p - 1 : ℕ) : ℤ) * (t : ℤ) =
        2 * (p : ℤ) * (d : ℤ) := by exact_mod_cast hdepth
  have hpsubZ : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
    exact_mod_cast hpsub
  push_cast
  nlinarith

private theorem ramifiedHasse_trace_floor_ge_succ_of_pos
    {p t d dK : ℕ} (hp : p.Prime) (hodd : Odd p) (ht : 0 < t)
    (hstable : t = 0 ∨ t + 1 ≤ d)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    ((d + 1 : ℕ) : ℤ) ≤
      ((dK : ℤ) + (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hs : t + 1 ≤ d := hstable.resolve_left (Nat.ne_of_gt ht)
  have hp3 : 3 ≤ p := ramifiedHasse_degree_three_le hp hodd
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hdepthZ :
      2 * (dK : ℤ) + ((p - 1 : ℕ) : ℤ) * (t : ℤ) =
        2 * (p : ℤ) * (d : ℤ) := by exact_mod_cast hdepth
  have hpsubZ : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
    exact_mod_cast hpsub
  push_cast
  nlinarith

private theorem ramifiedHasse_trace_floor_deeper_ge
    {p t d dK : ℕ} (hp : p.Prime)
    (hd : 0 < d)
    (hstable : t = 0 ∨ t + 1 ≤ d)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    ((d + 1 : ℕ) : ℤ) ≤
      (((dK + p : ℕ) : ℤ) +
        (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hbase := ramifiedHasse_trace_floor_ge hp hd hstable hdepth
  have hbase' : (d : ℤ) * (p : ℤ) ≤
      (dK : ℤ) + (((p - 1) * (t + 1) : ℕ) : ℤ) :=
    (Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)).mp hbase
  push_cast
  nlinarith

private theorem ramifiedHasse_tame_ceiling_ge
    {p d dK j : ℕ} (hp : p.Prime)
    (hd : 0 < d) (hdepth : 2 * dK = 2 * p * d)
    (hj : 3 ≤ j) :
    ((2 * d + 1 : ℕ) : ℤ) ≤ integerCeilingDiv ((j : ℤ) * dK) p := by
  have hdK : dK = p * d := by nlinarith
  rw [integerCeilingDiv]
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hjZ : (3 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hdKZ : (dK : ℤ) = (p : ℤ) * (d : ℤ) := by exact_mod_cast hdK
  push_cast
  nlinarith

private theorem ramifiedHasse_tame_second_ceiling_ge
    {p d dK : ℕ} (hp : p.Prime)
    (hdepth : 2 * dK = 2 * p * d) :
    ((2 * d : ℕ) : ℤ) ≤ integerCeilingDiv ((2 : ℤ) * dK) p := by
  rw [integerCeilingDiv,
    Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hdepthZ : 2 * (dK : ℤ) = 2 * (p : ℤ) * (d : ℤ) := by
    exact_mod_cast hdepth
  have hpZ : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.pos
  push_cast
  nlinarith

private theorem ramifiedHasse_tame_second_ceiling_deeper
    {p d dK : ℕ} (hp : p.Prime)
    (hdepth : 2 * dK = 2 * p * d) :
    ((2 * d + 1 : ℕ) : ℤ) ≤
      integerCeilingDiv ((2 : ℤ) * ((dK + p : ℕ) : ℤ)) p := by
  rw [integerCeilingDiv,
    Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hdepthZ : 2 * (dK : ℤ) = 2 * (p : ℤ) * (d : ℤ) := by
    exact_mod_cast hdepth
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  push_cast
  nlinarith

private theorem ramifiedHasse_wild_second_floor
    {p t d dK : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    ((2 * d : ℕ) : ℤ) ≤
      (((2 : ℕ) : ℤ) * (dK : ℤ) +
        (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hdepthZ :
      2 * (dK : ℤ) + ((p - 1 : ℕ) : ℤ) * (t : ℤ) =
        2 * (p : ℤ) * (d : ℤ) := by exact_mod_cast hdepth
  have hpsubZ : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
    exact_mod_cast hpsub
  push_cast
  nlinarith

private theorem ramifiedHasse_wild_higher_floor_ge
    {p t d dK j : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hstable : t + 1 ≤ d)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d)
    (hj : 3 ≤ j) :
    ((2 * d + 1 : ℕ) : ℤ) ≤
      ((j : ℤ) * (dK : ℤ) +
        (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hp2 := hp.two_le
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hdKpos : 0 < dK := by
    by_contra hz
    have : dK = 0 := Nat.eq_zero_of_not_pos hz
    subst dK
    have hpt : (p - 1) * t = 2 * p * d := by simpa using hdepth
    nlinarith
  have hdepthZ :
      2 * (dK : ℤ) + ((p - 1 : ℕ) : ℤ) * (t : ℤ) =
        2 * (p : ℤ) * (d : ℤ) := by exact_mod_cast hdepth
  have hpsubZ : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
    exact_mod_cast hpsub
  have hdKZ : (0 : ℤ) < (dK : ℤ) := by exact_mod_cast hdKpos
  have hjZ : (3 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  push_cast
  nlinarith

private theorem ramifiedHasse_wild_second_floor_deeper
    {p t d dK : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hdepth : 2 * dK + (p - 1) * t = 2 * p * d) :
    ((2 * d + 1 : ℕ) : ℤ) ≤
      (((2 : ℕ) : ℤ) * ((dK + p : ℕ) : ℤ) +
        (((p - 1) * (t + 1) : ℕ) : ℤ)) / (p : ℤ) := by
  rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hp.pos)]
  have hp1 : 1 ≤ p := hp.pos
  have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hdepthZ :
      2 * (dK : ℤ) + ((p - 1 : ℕ) : ℤ) * (t : ℤ) =
        2 * (p : ℤ) * (d : ℤ) := by exact_mod_cast hdepth
  have hpsubZ : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
    exact_mod_cast hpsub
  push_cast
  nlinarith

end DepthArithmetic

section LocalDepths

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

variable (P : PrimeCyclicPreparation F K)

theorem ramifiedHasseLocalInput_order_ge
    (dK r : ℕ) (a : F) (ha : a ∈ lattice F (r : ℤ)) :
    (((dK + Module.finrank F K * r : ℕ) : ℤ) : WithTop ℤ) ≤
      ord K (ramifiedHasseLocalInput F K P dK a) := by
  have ha' : (((r : ℕ) : ℤ) : WithTop ℤ) ≤ ord F a := by
    rw [mem_lattice] at ha
    exact ha
  have hmul : Module.finrank F K •
      ((((r : ℕ) : ℤ) : WithTop ℤ)) ≤
      Module.finrank F K • ord F a :=
    nsmul_le_nsmul_right ha' (Module.finrank F K)
  calc
    (((dK + Module.finrank F K * r : ℕ) : ℤ) : WithTop ℤ) =
        dK • (((1 : ℤ) : WithTop ℤ)) +
          Module.finrank F K • ((((r : ℕ) : ℤ) : WithTop ℤ)) := by
      rw [← WithTop.coe_nsmul]
      norm_num [nsmul_eq_mul]
      push_cast
      calc
        (((Module.finrank F K : ℕ) : ℤ) : WithTop ℤ) *
              (((r : ℕ) : ℤ) : WithTop ℤ) =
            ((((Module.finrank F K : ℕ) : ℤ) * (r : ℤ) : ℤ) :
              WithTop ℤ) :=
          (WithTop.coe_mul ((Module.finrank F K : ℕ) : ℤ) (r : ℤ)).symm
        _ = (((Module.finrank F K • (r : ℤ)) : ℤ) : WithTop ℤ) := by
          rw [nsmul_eq_mul]
        _ = Module.finrank F K • ((((r : ℕ) : ℤ) : WithTop ℤ)) :=
          WithTop.coe_nsmul (r : ℤ) (Module.finrank F K)
    _ ≤ dK • (((1 : ℤ) : WithTop ℤ)) +
        Module.finrank F K • ord F a := add_le_add le_rfl hmul
    _ = ord K (ramifiedHasseLocalInput F K P dK a) := by
      rw [ramifiedHasseLocalInput, ord_mul, ord_pow,
        ramifiedHasseUpperUniformizer_order, ord_algebraMap,
        P.ramificationIndex_eq_degree]

theorem ramifiedHasseLocalInput_order_ge_zero
    (dK : ℕ) (a : F) (ha : a ∈ lattice F 0) :
    (((dK : ℕ) : ℤ) : WithTop ℤ) ≤
      ord K (ramifiedHasseLocalInput F K P dK a) := by
  simpa using ramifiedHasseLocalInput_order_ge F K P dK 0 a ha

theorem ramifiedHasseLocalInput_order_ge_deeper
    (dK : ℕ) (a : F) (ha : a ∈ lattice F 1) :
    (((dK + Module.finrank F K : ℕ) : ℤ) : WithTop ℤ) ≤
      ord K (ramifiedHasseLocalInput F K P dK a) := by
  simpa using ramifiedHasseLocalInput_order_ge F K P dK 1 a ha

private theorem ramifiedHasse_traceFloor
    (q : ℕ) {x : K} (hx : x ∈ lattice K (q : ℤ)) :
    trace F K x ∈ lattice F
      (((q : ℤ) +
        (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)) /
          (Module.finrank F K : ℤ)) := by
  have h := trace_mem_lattice_floor F K P.piK P.hpiK P.hgen (q : ℤ) hx
  rw [differentExponent_eq F K P.ht P.piK P.hpiK P.hgen,
    P.ramificationIndex_eq_degree] at h
  exact h

/-- Exact trace-image floor for the critical input. -/
theorem ramifiedHasse_trace_floor
    (dK : ℕ) (a : F) (ha : a ∈ lattice F 0) :
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F (((dK : ℤ) +
        (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)) /
          (Module.finrank F K : ℤ)) := by
  apply ramifiedHasse_traceFloor F K P dK
  rw [mem_lattice]
  exact ramifiedHasseLocalInput_order_ge_zero F K P dK a ha

/-- The trace lies at lower depth `d`, with the different and lower-break
normalization made explicit in `ramifiedHasse_trace_floor`. -/
theorem ramifiedHasse_trace_depth
    (d dK : ℕ) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 0) :
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈ lattice F (d : ℤ) := by
  apply lattice_antitone F
    (ramifiedHasse_trace_floor_ge
      (PrimeCyclicExtension.degree_prime F K) hd hstable hdepth)
  exact ramifiedHasse_trace_floor F K P dK a ha

/-- At a positive break the same exact floor gives the extra trace depth. -/
theorem ramifiedHasse_trace_depth_of_break_pos
    (d dK : ℕ) (hodd : Odd (Module.finrank F K)) (ht : 0 < P.t)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 0) :
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
  apply lattice_antitone F
    (ramifiedHasse_trace_floor_ge_succ_of_pos
      (PrimeCyclicExtension.degree_prime F K) hodd ht hstable hdepth)
  exact ramifiedHasse_trace_floor F K P dK a ha

/-- Changing a coefficient by one lower-field lattice step changes its trace
by one lower target step.  This is the trace half of lift independence. -/
theorem ramifiedHasse_trace_depth_deeper
    (d dK : ℕ) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 1) :
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
  have hfloor := ramifiedHasse_traceFloor F K P
    (dK + Module.finrank F K) (x := ramifiedHasseLocalInput F K P dK a)
  apply lattice_antitone F
    (ramifiedHasse_trace_floor_deeper_ge
      (PrimeCyclicExtension.degree_prime F K) hd hstable hdepth)
  apply hfloor
  rw [mem_lattice]
  exact ramifiedHasseLocalInput_order_ge_deeper F K P dK a ha

private theorem ramifiedHasse_symmetric_bound_tame
    (d dK j : ℕ)
    (hd : 0 < d)
    (hdepth : 2 * dK = 2 * Module.finrank F K * d)
    (hj : 3 ≤ j) (hjle : j ≤ Module.finrank F K)
    (a : F) (ha : a ∈ lattice F 0) :
    elementarySymmetric F K j (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ) := by
  rw [mem_lattice]
  have hceil : (((2 * d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      (integerCeilingDiv ((j : ℤ) * (dK : ℤ))
        (Module.finrank F K) : WithTop ℤ) := by
    exact_mod_cast ramifiedHasse_tame_ceiling_ge
      (PrimeCyclicExtension.degree_prime F K)
      hd hdepth hj
  exact hceil.trans
    (totallyRamified_elementarySymmetric_bound F K
      (Module.finrank F K) (dK : ℤ)
      (PrimeCyclicExtension.degree_prime F K).pos rfl
      P.ramificationIndex_eq_degree
      (ramifiedHasseLocalInput_order_ge_zero F K P dK a ha) j hjle)

private theorem ramifiedHasse_symmetric_bound_wild
    (d dK j : ℕ) (ht : 0 < P.t) (hstable : P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (hj : 3 ≤ j) (hjlt : j < Module.finrank F K)
    (a : F) (ha : a ∈ lattice F 0) :
    elementarySymmetric F K j (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ) := by
  rw [mem_lattice]
  apply (show (((2 * d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      ((((j : ℤ) * (dK : ℤ) +
        (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)) /
          (Module.finrank F K : ℤ) : ℤ) : WithTop ℤ) by
    exact_mod_cast ramifiedHasse_wild_higher_floor_ge
      (PrimeCyclicExtension.degree_prime F K) ht hstable hdepth hj).trans
  apply wild_elementarySymmetric_bound F K
    (Module.finrank F K) (P.t + 1) (dK : ℤ)
    (PrimeCyclicExtension.degree_prime F K) (by omega)
    (residueCharacteristic_eq_degree_of_positive_isLowerBreak
      F K P.ht ht P.piK P.hpiK P.hgen)
    rfl (traceIdealLowerBound_of_integralGenerator
      F K P.ht P.hres P.piK P.hpiK P.hgen)
    (ramifiedHasseLocalInput_order_ge_zero F K P dK a ha)
    (by omega) hjlt

/-- Every term of degree at least three in the exact norm expansion has the
required error depth.  The terminal term is handled separately by its exact
norm order; no higher term is discarded. -/
theorem ramifiedHasse_higher_symmetric_depth
    (d dK : ℕ) (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 0)
    (j : ℕ) (hj : 3 ≤ j) (hjle : j ≤ Module.finrank F K) :
    elementarySymmetric F K j (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ) := by
  by_cases hjtop : j = Module.finrank F K
  · subst j
    rw [mem_lattice,
      elementarySymmetric_degree_ord F K (Module.finrank F K) rfl
        P.ramificationIndex_eq_degree]
    have hterminal : (((2 * d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (((dK : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast ramifiedHasse_terminal_depth
        (PrimeCyclicExtension.degree_prime F K) hodd hd hstable hdepth
    exact hterminal.trans
      (ramifiedHasseLocalInput_order_ge_zero F K P dK a ha)
  · have hjlt : j < Module.finrank F K := by omega
    by_cases ht0 : P.t = 0
    · apply ramifiedHasse_symmetric_bound_tame F K P d dK j hd
      · simpa [ht0] using hdepth
      · exact hj
      · exact hjle
      · exact ha
    · exact ramifiedHasse_symmetric_bound_wild F K P d dK j
        (Nat.pos_of_ne_zero ht0) (hstable.resolve_left ht0) hdepth
        hj hjlt a ha

/-- The quadratic elementary-symmetric term has exactly the lower target
depth dictated by the stable relation.  Tame and wild bounds are proved by
their respective totally-ramified estimates. -/
theorem ramifiedHasse_second_symmetric_depth
    (d dK : ℕ) (hodd : Odd (Module.finrank F K))
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 0) :
    elementarySymmetric F K 2 (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d : ℕ) : ℤ) := by
  rw [mem_lattice]
  by_cases ht0 : P.t = 0
  · have hdepth0 : 2 * dK = 2 * Module.finrank F K * d := by
      simpa [ht0] using hdepth
    have hceil : (((2 * d : ℕ) : ℤ) : WithTop ℤ) ≤
        (integerCeilingDiv ((2 : ℤ) * (dK : ℤ))
          (Module.finrank F K) : WithTop ℤ) := by
      exact_mod_cast ramifiedHasse_tame_second_ceiling_ge
        (PrimeCyclicExtension.degree_prime F K) hdepth0
    exact hceil.trans
      (totallyRamified_elementarySymmetric_bound F K
        (Module.finrank F K) (dK : ℤ)
        (PrimeCyclicExtension.degree_prime F K).pos rfl
        P.ramificationIndex_eq_degree
        (ramifiedHasseLocalInput_order_ge_zero F K P dK a ha) 2
        (PrimeCyclicExtension.degree_prime F K).two_le)
  · have ht : 0 < P.t := Nat.pos_of_ne_zero ht0
    have hfloor : (((2 * d : ℕ) : ℤ) : WithTop ℤ) ≤
        (((((2 : ℕ) : ℤ) * (dK : ℤ) +
          (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)) /
            (Module.finrank F K : ℤ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast ramifiedHasse_wild_second_floor
        (PrimeCyclicExtension.degree_prime F K) ht hdepth
    exact hfloor.trans
      (wild_elementarySymmetric_bound F K
        (Module.finrank F K) (P.t + 1) (dK : ℤ)
        (PrimeCyclicExtension.degree_prime F K) (by omega)
        (residueCharacteristic_eq_degree_of_positive_isLowerBreak
          F K P.ht ht P.piK P.hpiK P.hgen)
        rfl (traceIdealLowerBound_of_integralGenerator
          F K P.ht P.hres P.piK P.hpiK P.hgen)
        (ramifiedHasseLocalInput_order_ge_zero F K P dK a ha)
        (by omega) (by
          have := ramifiedHasse_degree_three_le
            (PrimeCyclicExtension.degree_prime F K) hodd
          omega))

/-- If the lower coefficient changes by one lattice step, its `E₂` term is
already in the norm-error lattice.  This is the quadratic half of lift
independence. -/
theorem ramifiedHasse_second_symmetric_depth_deeper
    (d dK : ℕ) (hodd : Odd (Module.finrank F K))
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 1) :
    elementarySymmetric F K 2 (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ) := by
  rw [mem_lattice]
  by_cases ht0 : P.t = 0
  · have hdepth0 : 2 * dK = 2 * Module.finrank F K * d := by
      simpa [ht0] using hdepth
    have hceil : (((2 * d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (integerCeilingDiv
          ((2 : ℤ) * ((dK + Module.finrank F K : ℕ) : ℤ))
          (Module.finrank F K) : WithTop ℤ) := by
      exact_mod_cast ramifiedHasse_tame_second_ceiling_deeper
        (PrimeCyclicExtension.degree_prime F K) hdepth0
    exact hceil.trans
      (totallyRamified_elementarySymmetric_bound F K
        (Module.finrank F K) ((dK + Module.finrank F K : ℕ) : ℤ)
        (PrimeCyclicExtension.degree_prime F K).pos rfl
        P.ramificationIndex_eq_degree
        (ramifiedHasseLocalInput_order_ge_deeper F K P dK a ha) 2
        (PrimeCyclicExtension.degree_prime F K).two_le)
  · have ht : 0 < P.t := Nat.pos_of_ne_zero ht0
    have hfloor : (((2 * d + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
        (((((2 : ℕ) : ℤ) *
            ((dK + Module.finrank F K : ℕ) : ℤ) +
          (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)) /
            (Module.finrank F K : ℤ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast ramifiedHasse_wild_second_floor_deeper
        (PrimeCyclicExtension.degree_prime F K) ht hdepth
    exact hfloor.trans
      (wild_elementarySymmetric_bound F K
        (Module.finrank F K) (P.t + 1)
        ((dK + Module.finrank F K : ℕ) : ℤ)
        (PrimeCyclicExtension.degree_prime F K) (by omega)
        (residueCharacteristic_eq_degree_of_positive_isLowerBreak
          F K P.ht ht P.piK P.hpiK P.hgen)
        rfl (traceIdealLowerBound_of_integralGenerator
          F K P.ht P.hres P.piK P.hpiK P.hgen)
        (ramifiedHasseLocalInput_order_ge_deeper F K P dK a ha)
        (by omega) (by
          have := ramifiedHasse_degree_three_le
            (PrimeCyclicExtension.degree_prime F K) hodd
          omega))

/-- Precise second-order norm truncation for the stable-high perturbation.
The proof rewrites the exact elementary-symmetric expansion and sends the
entire interval of degrees `3,...,ell` to the error lattice using
`ramifiedHasse_higher_symmetric_depth`. -/
theorem ramifiedHasse_norm_truncation
    (d dK : ℕ) (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (a : F) (ha : a ∈ lattice F 0) :
    norm F K (1 + ramifiedHasseLocalInput F K P dK a) -
        (1 + trace F K (ramifiedHasseLocalInput F K P dK a) +
          elementarySymmetric F K 2
            (ramifiedHasseLocalInput F K P dK a)) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ) := by
  let y := ramifiedHasseLocalInput F K P dK a
  let f : ℕ → F := fun j ↦ elementarySymmetric F K (j + 1) y
  have hp3 : 3 ≤ Module.finrank F K :=
    ramifiedHasse_degree_three_le
      (PrimeCyclicExtension.degree_prime F K) hodd
  have hsum : ∑ j ∈ Finset.Ico 2 (Module.finrank F K), f j ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ) := by
    rw [mem_lattice]
    apply ord_sum F
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hterm := ramifiedHasse_higher_symmetric_depth F K P d dK
      hodd hd hstable hdepth a ha (j + 1) (by omega) (by omega)
    rw [mem_lattice] at hterm
    exact hterm
  have hsplit := Finset.sum_range_add_sum_Ico f (show 2 ≤ Module.finrank F K by omega)
  have hfirst : ∑ j ∈ Finset.range 2, f j =
      trace F K y + elementarySymmetric F K 2 y := by
    norm_num [Finset.sum_range_succ, f, elementarySymmetric_one]
  rw [hfirst] at hsplit
  have hexp := norm_one_add_sub_one_eq_sum_elementarySymmetric F K y
  have heq :
      norm F K (1 + y) -
          (1 + trace F K y + elementarySymmetric F K 2 y) =
        ∑ j ∈ Finset.Ico 2 (Module.finrank F K), f j := by
    linear_combination hexp - hsplit
  rw [show ramifiedHasseLocalInput F K P dK a = y by rfl, heq]
  exact hsum

end LocalDepths

section ExactNormalizedTrace

/-- The linear part of a finite product of depth-`t` perturbations is exact
modulo depth `2t`.  This is the elementary product estimate used in the
critical normalized-uniformizer calculation. -/
private theorem ramifiedHasse_prod_linear_remainder
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → E) (t : ℕ)
    (ha : ∀ i ∈ s, a i ∈ lattice E (t : ℤ)) :
    (∏ i ∈ s, (1 + a i)) - 1 ∈ lattice E (t : ℤ) ∧
      (∏ i ∈ s, (1 + a i)) - 1 - ∑ i ∈ s, a i ∈
        lattice E ((2 * t : ℕ) : ℤ) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hai : a i ∈ lattice E (t : ℤ) := ha i (by simp)
      have has : ∀ j ∈ s, a j ∈ lattice E (t : ℤ) := by
        intro j hj
        exact ha j (by simp [hj])
      obtain ⟨ih₁, ih₂⟩ := ih has
      have hone : (1 : E) ∈ lattice E 0 := by
        rw [mem_lattice, ord_one]
        simp
      have hold0 : (∏ j ∈ s, (1 + a j)) - 1 ∈ lattice E 0 :=
        lattice_antitone E (by omega) ih₁
      have hprod0 : (∏ j ∈ s, (1 + a j)) ∈ lattice E 0 := by
        rw [show (∏ j ∈ s, (1 + a j)) =
            1 + ((∏ j ∈ s, (1 + a j)) - 1) by ring]
        exact add_mem_lattice E hone hold0
      have haProd : a i * (∏ j ∈ s, (1 + a j)) ∈ lattice E (t : ℤ) := by
        simpa using mul_mem_lattice E hai hprod0
      have haDiff : a i * ((∏ j ∈ s, (1 + a j)) - 1) ∈
          lattice E ((2 * t : ℕ) : ℤ) := by
        convert mul_mem_lattice E hai ih₁ using 1 <;> push_cast <;> ring
      constructor
      · rw [Finset.prod_insert hi]
        rw [show (1 + a i) * (∏ j ∈ s, (1 + a j)) - 1 =
            ((∏ j ∈ s, (1 + a j)) - 1) +
              a i * (∏ j ∈ s, (1 + a j)) by ring]
        exact add_mem_lattice E ih₁ haProd
      · rw [Finset.prod_insert hi, Finset.sum_insert hi]
        rw [show (1 + a i) * (∏ j ∈ s, (1 + a j)) - 1 -
              (a i + ∑ j ∈ s, a j) =
            ((∏ j ∈ s, (1 + a j)) - 1 - ∑ j ∈ s, a j) +
              a i * ((∏ j ∈ s, (1 + a j)) - 1) by ring]
        exact add_mem_lattice E ih₂ haDiff

/-- For an odd prime `p`, the sum of the canonical `ZMod p` coordinates
vanishes. -/
private theorem ramifiedHasse_sum_zmod
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) :
    (∑ u : ZMod p, u) = 0 := by
  have hp3 : 3 ≤ p := by
    have hp2 := (Fact.out : p.Prime).two_le
    rcases hpodd with ⟨q, hq⟩
    omega
  have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1 (by
    rw [ZMod.card]
    omega)
  simpa using h

/-- The preceding cancellation transported to any characteristic-`p`
field, in the representatives used by the critical displacement formula. -/
private theorem ramifiedHasse_sum_zmod_cast
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (k : Type*) [Field k] [CharP k p] :
    (∑ u : ZMod p, (u.val : k)) = 0 := by
  have hcast (u : ZMod p) :
      (u.val : k) = ZMod.castHom (dvd_refl p) k u := by
    simpa only [ZMod.castHom_apply] using ZMod.natCast_val (R := k) u
  simp_rw [hcast]
  rw [← map_sum, ramifiedHasse_sum_zmod p hpodd, map_zero]

/-- Congruence at a fixed depth is preserved by nonnegative powers of
integral elements. -/
private theorem ramifiedHasse_congruentAtDepth_pow
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {n : ℤ} {x y : E} (hx : (0 : WithTop ℤ) ≤ ord E x)
    (hy : (0 : WithTop ℤ) ≤ ord E y)
    (hxy : CongruentAtDepth n x y) (m : ℕ) :
    CongruentAtDepth n (x ^ m) (y ^ m) := by
  induction m with
  | zero => simpa using CongruentAtDepth.refl (1 : E)
  | succ m ih =>
      rw [pow_succ, pow_succ]
      exact CongruentAtDepth.mul
        (a := x ^ m) (b := y ^ m) (x := x) (y := y)
        (by simpa [ord_pow] using nsmul_nonneg hx m) hy ih hxy

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- For a positive break, the chosen norm uniformizer divided by the
`p`-th power of the chosen upper uniformizer is one modulo depth `t+1`.
The proof enumerates the conjugates cyclically, identifies their linear
residues as `j * lambda`, cancels their sum in characteristic `p`, and
controls all nonlinear terms at depth `2t ≥ t+1`. -/
theorem ramifiedHasse_normalized_uniformizer_congr
    (P : PrimeCyclicPreparation F K)
    (hodd : Odd (Module.finrank F K)) (ht : 0 < P.t) :
    CongruentAtDepth (((P.t + 1 : ℕ) : ℤ))
      (algebraMap F K (ramifiedHasseLowerUniformizer F K P : F) /
        (ramifiedHasseUpperUniformizer F K P : K) ^ Module.finrank F K)
      1 := by
  classical
  let p := Module.finrank F K
  let piK : K := (P.piK : K)
  let piF : F := norm F K (P.piK : K)
  letI : Fact p.Prime := ⟨PrimeCyclicExtension.degree_prime F K⟩
  letI : NeZero p := ⟨Module.finrank_pos.ne'⟩
  have hcharF : residueCharacteristic F = p :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K P.ht (by omega)
      P.piK P.hpiK P.hgen
  have hcharK : residueCharacteristic K = p :=
    (residueCharacteristic_extension_eq F K).trans hcharF
  letI : CharP (ResidueField K) p := ringChar.of_eq hcharK
  let sigma : ZMod p → Gal(K/F) := fun u ↦
    criticalNormGaloisZModEquiv F K (Multiplicative.ofAdd u)
  let a : ZMod p → K := fun u ↦ sigma u piK / piK - 1
  have ha_eq (u : ZMod p) :
      a u = (sigma u piK - piK) / piK := by
    dsimp only [a]
    field_simp [show piK ≠ 0 by exact P.hpiK.ne_zero]
  have ha_mem (u : ZMod p) : a u ∈ lattice K (P.t : ℤ) := by
    rw [ha_eq]
    apply (div_mem_lattice_iff K piK (sigma u piK - piK) 1
      (P.t : ℤ) (by
        dsimp only [piK]
        exact ord_uniformizer K P.hpiK)).2
    have hdisp := (lowerRamificationDisplacement F K
      (criticalNormLowerBreakElement F K P.ht (sigma u))
      (P.piK : K) P.hpiK).property
    change sigma u (P.piK : K) - (P.piK : K) ∈
      lattice K ((P.t : ℤ) + 1) at hdisp
    simpa only [piK, add_comm] using hdisp
  have ha_norm_mem (u : ZMod p) :
      a u / piK ^ P.t ∈ lattice K 0 := by
    apply (div_mem_lattice_iff K (piK ^ P.t) (a u)
      (P.t : ℤ) 0 (by
        dsimp only [piK]
        rw [ord_pow, ord_uniformizer K P.hpiK]
        norm_num)).2
    simpa using ha_mem u
  have ha_reduce (u : ZMod p) :
      reduce K (a u / piK ^ P.t) (ha_norm_mem u) =
        (u.val : ResidueField K) *
          criticalNormUpperRamificationLambda F K P.ht P.piK P.hpiK := by
    rw [← criticalNormResidueDisplacement_zmod F K P.ht ht
      P.piK P.hpiK P.hgen u]
    apply (reduce_eq_reduce_iff K _ _).2
    rw [congruentAtDepth_iff_sub_mem_lattice]
    have heq :
        a u / piK ^ P.t =
          (lowerRamificationNormalizedDisplacement F K
            (criticalNormLowerBreakElement F K P.ht (sigma u))
            (P.piK : K) P.hpiK : K) := by
      rw [ha_eq, coe_lowerRamificationNormalizedDisplacement]
      change (((sigma u piK - piK) / piK) / piK ^ P.t) =
        (sigma u piK - piK) / piK ^ ((P.t : ℤ) + 1)
      rw [div_div, zpow_add₀ P.hpiK.ne_zero]
      congr 1
      simp only [zpow_natCast, zpow_one]
      ac_rfl
    rw [heq, sub_self]
    exact (lattice K 1).zero_mem
  have hsum_mem : (∑ u : ZMod p, a u) ∈ lattice K (P.t : ℤ) :=
    sum_mem_lattice K (fun u _ ↦ ha_mem u)
  have hsum_norm_mem :
      (∑ u : ZMod p, a u) / piK ^ P.t ∈ lattice K 0 := by
    apply (div_mem_lattice_iff K (piK ^ P.t) (∑ u : ZMod p, a u)
      (P.t : ℤ) 0 (by
        dsimp only [piK]
        rw [ord_pow, ord_uniformizer K P.hpiK]
        norm_num)).2
    simpa using hsum_mem
  let b : ZMod p → ringOfIntegers K := fun u ↦
    ⟨a u / piK ^ P.t,
      (mem_lattice_zero_iff K).1 (ha_norm_mem u)⟩
  have hsum_integral :
      (⟨(∑ u : ZMod p, a u) / piK ^ P.t,
          (mem_lattice_zero_iff K).1 hsum_norm_mem⟩ : ringOfIntegers K) =
        ∑ u : ZMod p, b u := by
    apply Subtype.ext
    change (∑ u : ZMod p, a u) / piK ^ P.t =
      (ringOfIntegers K).subtype (∑ u : ZMod p, b u)
    rw [map_sum]
    change (∑ u : ZMod p, a u) / piK ^ P.t =
      ∑ u : ZMod p, a u / piK ^ P.t
    rw [Finset.sum_div]
  have hsum_reduce :
      reduce K ((∑ u : ZMod p, a u) / piK ^ P.t) hsum_norm_mem = 0 := by
    change residueMap K
      (⟨(∑ u : ZMod p, a u) / piK ^ P.t,
        (mem_lattice_zero_iff K).1 hsum_norm_mem⟩ : ringOfIntegers K) = 0
    rw [hsum_integral, map_sum]
    change (∑ u : ZMod p,
      reduce K (a u / piK ^ P.t) (ha_norm_mem u)) = 0
    simp_rw [ha_reduce]
    rw [← Finset.sum_mul,
      ramifiedHasse_sum_zmod_cast p hodd (ResidueField K)]
    simp
  have hsum_deep : (∑ u : ZMod p, a u) ∈
      lattice K ((P.t + 1 : ℕ) : ℤ) := by
    have hquot : (∑ u : ZMod p, a u) / piK ^ P.t ∈ lattice K 1 := by
      change residueMap K
        (⟨(∑ u : ZMod p, a u) / piK ^ P.t,
          (mem_lattice_zero_iff K).1 hsum_norm_mem⟩ : ringOfIntegers K) = 0
        at hsum_reduce
      exact (residueMap_eq_zero_iff K _).1 hsum_reduce
    have hraw := (div_mem_lattice_iff K (piK ^ P.t) (∑ u : ZMod p, a u)
      (P.t : ℤ) 1 (by
        dsimp only [piK]
        rw [ord_pow, ord_uniformizer K P.hpiK]
        norm_num)).1 hquot
    simpa only [Nat.cast_add, Nat.cast_one] using hraw
  obtain ⟨_, hremainder⟩ :=
    ramifiedHasse_prod_linear_remainder Finset.univ a P.t
      (fun u _ ↦ ha_mem u)
  have htwice : P.t + 1 ≤ 2 * P.t := by omega
  have hremainder_deep :
      (∏ u : ZMod p, (1 + a u)) - 1 - ∑ u : ZMod p, a u ∈
        lattice K ((P.t + 1 : ℕ) : ℤ) :=
    lattice_antitone K (by exact_mod_cast htwice) hremainder
  have hprod_deep :
      (∏ u : ZMod p, (1 + a u)) - 1 ∈
        lattice K ((P.t + 1 : ℕ) : ℤ) := by
    rw [show (∏ u : ZMod p, (1 + a u)) - 1 =
        ((∏ u : ZMod p, (1 + a u)) - 1 - ∑ u : ZMod p, a u) +
          ∑ u : ZMod p, a u by ring]
    exact add_mem_lattice K hremainder_deep hsum_deep
  have hprod_eq :
      algebraMap F K piF / piK ^ p = ∏ u : ZMod p, (1 + a u) := by
    calc
      algebraMap F K piF / piK ^ p =
          (∏ tau : Gal(K/F), tau piK) / piK ^ p := by
        dsimp only [piF]
        rw [Algebra.norm_eq_prod_automorphisms]
      _ = (∏ u : ZMod p, sigma u piK) / (∏ _u : ZMod p, piK) := by
        rw [show (∏ tau : Gal(K/F), tau piK) =
            ∏ u : ZMod p, sigma u piK by
          calc
            (∏ tau : Gal(K/F), tau piK) =
                ∏ v : Multiplicative (ZMod p),
                  criticalNormGaloisZModEquiv F K v piK :=
              ((criticalNormGaloisZModEquiv F K).toEquiv.prod_comp
                (fun tau : Gal(K/F) ↦ tau piK)).symm
            _ = ∏ u : ZMod p,
                criticalNormGaloisZModEquiv F K (Multiplicative.ofAdd u) piK :=
              ((Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p)).prod_comp
                (fun v ↦ criticalNormGaloisZModEquiv F K v piK)).symm
            _ = ∏ u : ZMod p, sigma u piK := by rfl]
        rw [Finset.prod_const, Finset.card_univ, ZMod.card]
      _ = ∏ u : ZMod p, (sigma u piK / piK) := by
        rw [Finset.prod_div_distrib]
      _ = ∏ u : ZMod p, (1 + a u) := by
        apply Finset.prod_congr rfl
        intro u hu
        dsimp only [a]
        ring
  rw [congruentAtDepth_iff_sub_mem_lattice]
  simpa only [ramifiedHasseLowerUniformizer_coe,
    ramifiedHasseUpperUniformizer_coe, piF, piK, p, hprod_eq] using hprod_deep

/-- The stable stationary-depth relation transports the normalized
uniformizer congruence to the required congruence between upper powers. -/
theorem ramifiedHasse_uniformizer_power_congr
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (hodd : Odd (Module.finrank F K)) (ht : 0 < P.t)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    CongruentAtDepth ((2 * dK + 1 : ℕ) : ℤ)
      ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK))
      (algebraMap F K
          ((ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d - P.t)) *
        (ramifiedHasseUpperUniformizer F K P : K) ^ P.t) := by
  let p := Module.finrank F K
  let piK : K := (ramifiedHasseUpperUniformizer F K P : K)
  let piF : F := (ramifiedHasseLowerUniformizer F K P : F)
  let m := 2 * d - P.t
  have hs : P.t + 1 ≤ d := hstable.resolve_left (Nat.ne_of_gt ht)
  have huniformizer :=
    ramifiedHasse_normalized_uniformizer_congr F K P hodd ht
  have htle : P.t ≤ 2 * d := by omega
  have hsource' : P.t + p * m = 2 * dK := by
    have hp1 : 1 ≤ p := (PrimeCyclicExtension.degree_prime F K).pos
    have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
    have hmt : m + P.t = 2 * d := by
      dsimp only [m]
      exact Nat.sub_add_cancel htle
    dsimp only [p] at hdepth ⊢
    nlinarith
  have hqord : ord K (algebraMap F K piF / piK ^ p) = 0 := by
    dsimp only [piF, piK, p]
    rw [ord_div, ord_algebraMap, ramifiedHasseLowerUniformizer_order,
      P.ramificationIndex_eq_degree, ord_pow,
      ramifiedHasseUpperUniformizer_order]
    norm_num [nsmul_eq_mul]
  have hqinv := CongruentAtDepth.inv hqord (by rw [ord_one])
    (by simpa only [piF, piK, p] using huniformizer)
  have hratio : CongruentAtDepth ((P.t + 1 : ℕ) : ℤ)
      (piK ^ p / algebraMap F K piF) 1 := by
    convert hqinv using 1 <;>
      field_simp [Units.ne_zero (ramifiedHasseUpperUniformizer F K P),
        Units.ne_zero (ramifiedHasseLowerUniformizer F K P)]
  have hratioOrd : ord K (piK ^ p / algebraMap F K piF) = 0 := by
    rw [ord_div, ord_pow]
    dsimp only [piK, piF, p]
    rw [ramifiedHasseUpperUniformizer_order, ord_algebraMap,
      ramifiedHasseLowerUniformizer_order, P.ramificationIndex_eq_degree]
    norm_num [nsmul_eq_mul]
  have hratioPow := ramifiedHasse_congruentAtDepth_pow
    (by rw [hratioOrd]) (by simp) hratio m
  let a : K := algebraMap F K (piF ^ m) * piK ^ P.t
  have haord : ord K a = (((2 * dK : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [a]
    rw [ord_mul, ord_algebraMap, ord_pow, ord_pow]
    dsimp only [piF, piK, p, m]
    rw [ramifiedHasseLowerUniformizer_order,
      ramifiedHasseUpperUniformizer_order, P.ramificationIndex_eq_degree]
    rw [← WithTop.coe_nsmul, ← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
    change ((((p * m + P.t : ℕ) : ℤ)) : WithTop ℤ) =
      ((((2 * dK : ℕ) : ℤ)) : WithTop ℤ)
    rw [show p * m + P.t = 2 * dK by omega]
  have hscaled := CongruentAtDepth.mul_left_shift
    (r := (2 * dK : ℤ)) (s := ((P.t + 1 : ℕ) : ℤ)) a
    (by simpa using le_of_eq haord.symm) hratioPow
  have hscaled' := CongruentAtDepth.mono
    (m := ((2 * dK + 1 : ℕ) : ℤ))
    (n := (2 * dK : ℤ) + ((P.t + 1 : ℕ) : ℤ))
    (by omega) hscaled
  have hleft : a * (piK ^ p / algebraMap F K piF) ^ m =
      piK ^ (2 * dK) := by
    have hpiF : algebraMap F K piF ≠ 0 := by
      exact (map_ne_zero (algebraMap F K)).2
        (Units.ne_zero (ramifiedHasseLowerUniformizer F K P))
    dsimp only [a]
    rw [div_pow, map_pow]
    rw [show (algebraMap F K piF) ^ m * piK ^ P.t *
          ((piK ^ p) ^ m / (algebraMap F K piF) ^ m) =
        piK ^ P.t * (piK ^ p) ^ m by field_simp [hpiF] <;> ring]
    rw [← pow_mul, ← pow_add]
    congr 1
  have hright : a * 1 ^ m = algebraMap F K (piF ^ m) * piK ^ P.t := by
    simp [a]
  rw [hleft, hright] at hscaled'
  simpa only [piF, piK, m] using hscaled'

/-- After applying the trace-ideal bound at the power-congruence precision,
the stable normalized trace is congruent modulo the lower maximal ideal to
the critical normalized trace coefficient. -/
theorem ramifiedHasse_normalizedTrace_congr_critical
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (hodd : Odd (Module.finrank F K)) (ht : 0 < P.t)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    CongruentAtDepth 1
      (ramifiedHasseNormalizedTrace F K P d dK)
      (trace F K ((ramifiedHasseUpperUniformizer F K P : K) ^ P.t) /
        (ramifiedHasseLowerUniformizer F K P : F) ^ P.t) := by
  let p := Module.finrank F K
  let piK : K := (ramifiedHasseUpperUniformizer F K P : K)
  let piF : F := (ramifiedHasseLowerUniformizer F K P : F)
  let m := 2 * d - P.t
  have hs : P.t + 1 ≤ d := hstable.resolve_left (Nat.ne_of_gt ht)
  have htle : P.t ≤ 2 * d := by omega
  have hsource : aboveBreakSourceDepth P.t p (2 * d) = 2 * dK := by
    rw [aboveBreakSourceDepth_eq P.t p htle]
    have hp1 : 1 ≤ p := (PrimeCyclicExtension.degree_prime F K).pos
    have hpsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
    have hmt : m + P.t = 2 * d := by
      dsimp only [m]
      exact Nat.sub_add_cancel htle
    dsimp only [p] at hdepth ⊢
    nlinarith
  have habove : P.t < 2 * d := by omega
  have hfloor :
      ((((2 * dK + 1 : ℕ) : ℤ) +
          (((p - 1) * (P.t + 1) : ℕ) : ℤ)) / (p : ℤ)) =
        ((2 * d + 1 : ℕ) : ℤ) := by
    rw [← hsource]
    exact aboveBreak_trace_floor_succ P.t p
      (PrimeCyclicExtension.degree_prime F K).pos habove
  have hpow := ramifiedHasse_uniformizer_power_congr
    F K P hodd ht hstable hdepth
  rw [congruentAtDepth_iff_sub_mem_lattice] at hpow
  have htrace := trace_mem_lattice_floor F K P.piK P.hpiK P.hgen
    ((2 * dK + 1 : ℕ) : ℤ) hpow
  rw [differentExponent_eq F K P.ht P.piK P.hpiK P.hgen,
    P.ramificationIndex_eq_degree] at htrace
  change trace F K
      (piK ^ (2 * dK) -
        algebraMap F K (piF ^ m) * piK ^ P.t) ∈ _ at htrace
  rw [map_sub] at htrace
  rw [hfloor] at htrace
  have htraceY :
      trace F K (algebraMap F K (piF ^ m) * piK ^ P.t) =
        piF ^ m * trace F K (piK ^ P.t) := by
    simpa [Algebra.smul_def] using
      (Algebra.trace F K).map_smul (piF ^ m) (piK ^ P.t)
  rw [htraceY] at htrace
  have hdenord : ord F (piF ^ (2 * d)) =
      (((2 * d : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [piF]
    rw [ord_pow, ramifiedHasseLowerUniformizer_order]
    rw [← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  have hdiv :
      (trace F K (piK ^ (2 * dK)) -
          piF ^ m * trace F K (piK ^ P.t)) / piF ^ (2 * d) ∈
        lattice F 1 := by
    apply (div_mem_lattice_iff F (piF ^ (2 * d)) _
      (((2 * d : ℕ) : ℤ)) 1 hdenord).2
    simpa only [Nat.cast_add, Nat.cast_one] using htrace
  rw [congruentAtDepth_iff_sub_mem_lattice]
  have hpiF : piF ≠ 0 := Units.ne_zero (ramifiedHasseLowerUniformizer F K P)
  have hmt : m + P.t = 2 * d := by
    dsimp only [m]
    exact Nat.sub_add_cancel htle
  convert hdiv using 1
  dsimp only [ramifiedHasseNormalizedTrace, piK, piF]
  have hpowden :
      (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) =
        (ramifiedHasseLowerUniformizer F K P : F) ^ m *
          (ramifiedHasseLowerUniformizer F K P : F) ^ P.t := by
    rw [← pow_add, hmt]
  have hsecond :
      trace F K ((ramifiedHasseUpperUniformizer F K P : K) ^ P.t) /
          (ramifiedHasseLowerUniformizer F K P : F) ^ P.t =
        ((ramifiedHasseLowerUniformizer F K P : F) ^ m *
            trace F K ((ramifiedHasseUpperUniformizer F K P : K) ^ P.t)) /
          (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) := by
    apply (div_eq_div_iff
      (pow_ne_zero _ (Units.ne_zero (ramifiedHasseLowerUniformizer F K P)))
      (pow_ne_zero _ (Units.ne_zero (ramifiedHasseLowerUniformizer F K P)))).2
    rw [hpowden]
    ring
  rw [hsecond, ← sub_div]

/-- Exact order of the trace numerator.  The lower bound alone comes from
the trace ideal; exactness uses injectivity of the above-break graded norm.
Thus the proof cannot be replaced by an unspecified trace estimate. -/
private theorem ramifiedHasse_trace_uniformizer_exact_order_aux
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ}
    (hodd : Module.finrank F K ≠ 2)
    (hd : 0 < d)
    (habove : P.t < 2 * d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ord F (trace F K ((P.piK : K) ^ (2 * dK))) =
      (((2 * d : ℕ) : ℤ) : WithTop ℤ) := by
  let ell := Module.finrank F K
  let r := 2 * d
  let sourceDepth := aboveBreakSourceDepth P.t ell r
  let x : K := (P.piK : K) ^ (2 * dK)
  have hellPrime : ell.Prime := PrimeCyclicExtension.degree_prime F K
  have hellThree : 3 ≤ ell := by
    have hellTwo := hellPrime.two_le
    dsimp only [ell] at hodd ⊢
    omega
  have hrpos : 0 < r := by dsimp only [r]; omega
  have hpdec : ell = (ell - 1) + 1 := by omega
  have hrdecomp : r = P.t + (r - P.t) := by omega
  have hsource : sourceDepth = 2 * dK := by
    dsimp only [sourceDepth]
    rw [aboveBreakSourceDepth_eq P.t ell
      (by simpa only [r] using habove.le)]
    have hrelation :
        2 * dK + (ell - 1) * P.t = ell * r := by
      dsimp only [ell, r]
      calc
        2 * dK + (Module.finrank F K - 1) * P.t =
            2 * Module.finrank F K * d := hdepth
        _ = Module.finrank F K * (2 * d) := by ring
    have hexpand :
        ell * r = (ell - 1) * P.t +
          (P.t + ell * (r - P.t)) := by
      have hellmul : ell * P.t = (ell - 1) * P.t + P.t := by
        calc
          ell * P.t = ((ell - 1) + 1) * P.t := by rw [← hpdec]
          _ = (ell - 1) * P.t + P.t := by ring
      calc
        ell * r = ell * (P.t + (r - P.t)) :=
          congrArg (ell * ·) hrdecomp
        _ = ell * P.t + ell * (r - P.t) := by rw [Nat.mul_add]
        _ = ((ell - 1) * P.t + P.t) + ell * (r - P.t) := by
          rw [hellmul]
        _ = (ell - 1) * P.t + (P.t + ell * (r - P.t)) := by ring
    have hcancel :
        (ell - 1) * P.t + 2 * dK =
          (ell - 1) * P.t + (P.t + ell * (r - P.t)) := by
      calc
        (ell - 1) * P.t + 2 * dK =
            2 * dK + (ell - 1) * P.t := by ac_rfl
        _ = ell * r := hrelation
        _ = (ell - 1) * P.t + (P.t + ell * (r - P.t)) := hexpand
    exact (Nat.add_left_cancel hcancel).symm
  have hdKpos : 0 < dK := by
    by_contra hdKzero
    have hdKzero' : dK = 0 := Nat.eq_zero_of_not_pos hdKzero
    rw [hdKzero'] at hdepth
    norm_num at hdepth
    have hleft :
        (Module.finrank F K - 1) * P.t <
          (Module.finrank F K - 1) * (2 * d) :=
      Nat.mul_lt_mul_of_pos_left habove (by omega)
    have hright :
        (Module.finrank F K - 1) * (2 * d) <
          Module.finrank F K * (2 * d) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have hlt : (Module.finrank F K - 1) * P.t <
        Module.finrank F K * (2 * d) := hleft.trans hright
    exact (Nat.ne_of_lt hlt) (by
      calc
        (Module.finrank F K - 1) * P.t =
            2 * Module.finrank F K * d := hdepth
        _ = Module.finrank F K * (2 * d) := by ring)
  have hsourcePos : 0 < sourceDepth := by rw [hsource]; omega
  have hxord : ord K x =
      (((sourceDepth : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [x]
    rw [ord_pow, ord_uniformizer K P.hpiK, hsource]
    change (2 * dK) • (((1 : ℤ) : WithTop ℤ)) =
      ((((2 * dK : ℕ) : ℤ)) : WithTop ℤ)
    rw [← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  have hxbound : (sourceDepth : WithTop ℤ) ≤ ord K x := by
    rw [hxord]
    norm_num
  have hxlat : x ∈ lattice K (sourceDepth : ℤ) := by
    rw [mem_lattice]
    exact hxbound
  have hxnotdeep : x ∉ lattice K ((sourceDepth + 1 : ℕ) : ℤ) := by
    intro hdeep
    rw [mem_lattice, hxord] at hdeep
    have hlt : (((sourceDepth : ℕ) : ℤ) : WithTop ℤ) <
        ((((sourceDepth + 1 : ℕ) : ℤ)) : WithTop ℤ) := by
      exact_mod_cast Nat.lt_succ_self sourceDepth
    exact (not_lt_of_ge hdeep) hlt
  have htraceLat : trace F K x ∈ lattice F (r : ℤ) :=
    trace_mem_lattice_aboveBreak F K P.ht
      (by simpa only [r] using habove) P.hres P.piK P.hpiK P.hgen
      (by simpa only [sourceDepth, ell, r] using hxlat)
  have hsourceEq : sourceDepth = (sourceDepth - 1) + 1 := by omega
  let u0 : Kˣ := principalUnitOf K (sourceDepth - 1) x (by
    rw [← hsourceEq]
    exact hxlat)
  have hu0 : u0 ∈ unitFiltration K sourceDepth := by
    rw [hsourceEq]
    exact principalUnitOf_mem K (sourceDepth - 1) x (by
      rw [← hsourceEq]
      exact hxlat)
  let u : unitFiltration K sourceDepth := ⟨u0, hu0⟩
  have hucoe : (((u : unitFiltration K sourceDepth) : Kˣ) : K) =
      1 + x := rfl
  have husource : unitGradedMk K sourceDepth u ≠ 1 := by
    intro hone
    have hudeep : (u : Kˣ) ∈ unitFiltration K (sourceDepth + 1) :=
      (unitGradedMk_eq_one_iff K sourceDepth u).1 hone
    have hsub :=
      (mem_unitFiltration_succ_iff_sub_mem_lattice K sourceDepth
        (u : Kˣ)).1 hudeep
    rw [hucoe, add_sub_cancel_left] at hsub
    exact hxnotdeep hsub
  have hrEq : r = (r - 1) + 1 := by omega
  let v0 : Fˣ := principalUnitOf F (r - 1) (trace F K x) (by
    rw [← hrEq]
    exact htraceLat)
  have hv0 : v0 ∈ unitFiltration F r := by
    rw [hrEq]
    exact principalUnitOf_mem F (r - 1) (trace F K x) (by
      rw [← hrEq]
      exact htraceLat)
  let v : unitFiltration F r := ⟨v0, hv0⟩
  have hvcoe : (((v : unitFiltration F r) : Fˣ) : F) =
      1 + trace F K x := rfl
  have hmap :
      normGradedAboveBreakCanonical F K P.ht
          (by simpa only [r] using habove) P.hres P.piK P.hpiK P.hgen
          (unitGradedMk K sourceDepth u) =
        unitGradedMk F r v := by
    exact normGradedAboveBreakCanonical_mk_eq_trace F K P.ht
      (by simpa only [r] using habove) P.hres P.piK P.hpiK P.hgen
      x (by simpa only [sourceDepth, ell, r] using hxbound) u
      (by simpa only [sourceDepth, ell, r] using hucoe) v
      (by simpa only [r] using hvcoe)
  have hinjective : Function.Injective
      (normGradedAboveBreakCanonical F K P.ht
        (by simpa only [r] using habove) P.hres P.piK P.hpiK P.hgen) :=
    (norm_graded_bijective_above_break F K P.ht
      (by simpa only [r] using habove) P.hres P.piK P.hpiK P.hgen).1
  have hvtarget : unitGradedMk F r v ≠ 1 := by
    intro hone
    apply husource
    apply hinjective
    rw [hmap, hone, map_one]
  have htraceNotDeep : trace F K x ∉ lattice F ((r + 1 : ℕ) : ℤ) := by
    intro hdeep
    apply hvtarget
    apply (unitGradedMk_eq_one_iff F r v).2
    apply (mem_unitFiltration_succ_iff_sub_mem_lattice F r (v : Fˣ)).2
    rw [hvcoe, add_sub_cancel_left]
    exact hdeep
  have htraceOrd : ord F (trace F K x) = ((r : ℤ) : WithTop ℤ) := by
    apply (mem_lattice_and_not_mem_succ_iff F).1
    refine ⟨htraceLat, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using htraceNotDeep
  simpa only [x, r] using htraceOrd

/-- Exact order of the numerator at the stable odd depth. -/
theorem ramifiedHasse_trace_uniformizer_exact_order
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ} (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ord F (trace F K
      ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK))) =
        (((2 * d : ℕ) : ℤ) : WithTop ℤ) := by
  have habove : P.t < 2 * d := by
    rcases hstable with htzero | htstable
    · rw [htzero]
      omega
    · omega
  have hne : Module.finrank F K ≠ 2 := by
    intro heq
    rw [heq] at hodd
    rcases hodd with ⟨q, hq⟩
    omega
  simpa only [ramifiedHasseUpperUniformizer_coe] using
    ramifiedHasse_trace_uniformizer_exact_order_aux F K P hne hd
      habove hdepth

/-- The normalized trace coefficient is an exact unit, not merely integral. -/
theorem ramifiedHasseNormalizedTrace_order
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ} (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ord F (ramifiedHasseNormalizedTrace F K P d dK) =
      (0 : WithTop ℤ) := by
  have hnum := ramifiedHasse_trace_uniformizer_exact_order F K P
    hodd hd hstable hdepth
  have hden : ord F
      ((ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d)) =
        (((2 * d : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ramifiedHasseLowerUniformizer_order,
      ← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [ramifiedHasseNormalizedTrace, ord_div, hnum, hden]
  simp
  exact WithTop.coe_ne_top

/-- The normalized trace retained as an integral representative. -/
def ramifiedHasseNormalizedTraceIntegral
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ} (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) : lattice F 0 :=
  ⟨ramifiedHasseNormalizedTrace F K P d dK, by
    rw [mem_lattice,
      ramifiedHasseNormalizedTrace_order F K P hodd hd hstable hdepth]
    exact le_rfl⟩

/-- The quotient class of the exact normalized-trace unit. -/
def ramifiedHasseNormalizedTraceResidue
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ} (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) : ResidueField F :=
  reduce F (ramifiedHasseNormalizedTrace F K P d dK)
    (ramifiedHasseNormalizedTraceIntegral F K P hodd hd hstable hdepth).property

@[simp]
theorem ramifiedHasseNormalizedTraceResidue_eq
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ} (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ramifiedHasseNormalizedTraceResidue F K P hodd hd hstable hdepth =
      reduce F (ramifiedHasseNormalizedTrace F K P d dK)
        (ramifiedHasseNormalizedTraceIntegral F K P hodd hd hstable hdepth).property :=
  rfl

/-- In the positive-break stable range, the normalized-trace residue is the
linear coefficient of the generic critical norm polynomial. -/
theorem ramifiedHasseNormalizedTraceResidue_eq_criticalNormLinearCoefficient
    (P : PrimeCyclicPreparation F K)
    {d dK : ℕ} (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d)
    (ht : 0 < P.t) :
    ramifiedHasseNormalizedTraceResidue F K P hodd hd hstable hdepth =
      criticalNormLinearCoefficient F K P.ht P.hres P.piK P.hpiK P.hgen := by
  rw [ramifiedHasseNormalizedTraceResidue, criticalNormLinearCoefficient]
  apply (reduce_eq_reduce_iff F _ _).2
  simpa only [criticalNormLowerUniformizer,
    ramifiedHasseUpperUniformizer_coe,
    ramifiedHasseLowerUniformizer_coe] using
      ramifiedHasse_normalizedTrace_congr_critical
        F K P hodd ht hstable hdepth

/-- Exact specialization from the normalized quotient back to the trace
numerator.  The denominator orientation is the ordered lower norm
uniformizer. -/
theorem ramifiedHasse_epsilon_trace_specialization
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) :
    trace F K
        ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK)) =
      ramifiedHasseNormalizedTrace F K P d dK *
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) := by
  rw [ramifiedHasseNormalizedTrace]
  exact (div_mul_cancel₀ _ (pow_ne_zero _
    (Units.ne_zero (ramifiedHasseLowerUniformizer F K P)))).symm

end ExactNormalizedTrace

section ResidualCoordinates

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Total reduction operation used only to give the inactive tame coordinate
a harmless value.  On integral inputs it is definitionally the ordinary
residue quotient. -/
private noncomputable def ramifiedHasseReduceIfIntegral
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (x : E) : ResidueField E := by
  classical
  exact if hx : x ∈ lattice E 0 then reduce E x hx else 0

private theorem ramifiedHasseReduceIfIntegral_of_mem
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (x : E) (hx : x ∈ lattice E 0) :
    ramifiedHasseReduceIfIntegral x = reduce E x hx := by
  classical
  change (if h : x ∈ lattice E 0 then reduce E x h else 0) = reduce E x hx
  rw [dif_pos hx]

/-- The tame residual coordinate in the lower residue field.  Its actual
origin is certified below when the break is zero. -/
def ramifiedHasseTameCoordinate
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) : ResidueField F :=
  (PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) P.hres).symm
      (ramifiedHasseReduceIfIntegral
        (ramifiedHasseTameCoordinateValue F K P d dK))

/-- Exact order-zero normalization of the tame uniformizer-power ratio. -/
theorem ramifiedHasseTameCoordinateValue_order
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (ht : P.t = 0)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ord K (ramifiedHasseTameCoordinateValue F K P d dK) =
      (0 : WithTop ℤ) := by
  have hdK : dK = Module.finrank F K * d := by
    rw [ht] at hdepth
    norm_num at hdepth
    nlinarith
  have hnum : ord K
      ((ramifiedHasseUpperUniformizer F K P : K) ^ dK) =
        (((dK : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_pow, ramifiedHasseUpperUniformizer_order,
      ← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  have hden : ord K (algebraMap F K
      ((ramifiedHasseLowerUniformizer F K P : F) ^ d)) =
        (((dK : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ord_algebraMap, ord_pow, ramifiedHasseLowerUniformizer_order,
      P.ramificationIndex_eq_degree]
    rw [hdK]
    norm_num
    simpa [nsmul_eq_mul] using
      (WithTop.coe_nsmul (d : ℤ) (Module.finrank F K)).symm
  rw [ramifiedHasseTameCoordinateValue, ord_div, hnum, hden]
  simp

/-- Integral tame coordinate lift, available precisely in the tame branch. -/
def ramifiedHasseTameCoordinateIntegral
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (ht : P.t = 0)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) : lattice K 0 :=
  ⟨ramifiedHasseTameCoordinateValue F K P d dK, by
    rw [mem_lattice,
      ramifiedHasseTameCoordinateValue_order F K P ht hdepth]
    exact le_rfl⟩

/-- Exact field-level and residue-level origin of the tame coordinate. -/
theorem ramifiedHasseTameCoordinate_origin
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (ht : P.t = 0)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ∃ cLift : lattice K 0,
      (cLift : K) =
          (ramifiedHasseUpperUniformizer F K P : K) ^ dK /
            algebraMap F K
              ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ∧
        PhaseReductionResidualCoordinateSource.residueEquiv P.hres
            (ramifiedHasseTameCoordinate F K P d dK) =
          reduce K (cLift : K) cLift.property := by
  let cLift := ramifiedHasseTameCoordinateIntegral F K P ht hdepth
  refine ⟨cLift, rfl, ?_⟩
  rw [ramifiedHasseTameCoordinate]
  rw [(PhaseReductionResidualCoordinateSource.residueEquiv P.hres).apply_symm_apply]
  exact ramifiedHasseReduceIfIntegral_of_mem (cLift : K) cLift.property

theorem ramifiedHasseTameCoordinate_ne_zero
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (ht : P.t = 0)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    ramifiedHasseTameCoordinate F K P d dK ≠ 0 := by
  let cLift := ramifiedHasseTameCoordinateIntegral F K P ht hdepth
  have hcOrder : ord K (cLift : K) = 0 :=
    ramifiedHasseTameCoordinateValue_order F K P ht hdepth
  have hreduce : reduce K (cLift : K) cLift.property ≠ 0 := by
    intro hz
    have hcong : CongruentAtDepth 1 (cLift : K) 0 := by
      rw [← reduce_eq_reduce_iff K cLift.property (lattice K 0).zero_mem]
      have hzero : reduce K 0 (lattice K 0).zero_mem = 0 := rfl
      exact hz.trans hzero.symm
    rw [CongruentAtDepth, sub_zero, hcOrder] at hcong
    exact (not_le_of_gt
      (show (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ) by norm_num)) hcong
  intro hz
  apply hreduce
  have hz' := congrArg
    (PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) P.hres) hz
  rw [ramifiedHasseTameCoordinate,
    (PhaseReductionResidualCoordinateSource.residueEquiv P.hres).apply_symm_apply,
    map_zero] at hz'
  change ramifiedHasseReduceIfIntegral (cLift : K) = 0 at hz'
  rw [ramifiedHasseReduceIfIntegral_of_mem (cLift : K) cLift.property] at hz'
  exact hz'

/-- The wild coordinate is always defined by the exact generator
displacement quotient; it is used only when the break is positive. -/
def ramifiedHasseWildLambda
    (P : PrimeCyclicPreparation F K) : ResidueField F :=
  (PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) P.hres).symm
      (lowerRamificationResidueDisplacement F K
        (ramifiedHasseBreakGenerator F K P) (P.piK : K) P.hpiK)

/-- The residue-degree-one coordinate used by local geometry is exactly the
canonical coordinate used by the extracted critical norm polynomial. -/
theorem ramifiedHasse_residueEquiv_eq_criticalNormResidueEquiv
    (hres : residueDegree F K = 1) :
    PhaseReductionResidualCoordinateSource.residueEquiv hres =
      criticalNormResidueEquiv F K hres := by
  ext z
  rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply,
    criticalNormResidueEquiv_apply]

/-- Compatibility of the manuscript's wild local-geometry coordinate with
the generic critical norm ramification coefficient. -/
theorem ramifiedHasseWildLambda_eq_criticalNormRamificationLambda
    (P : PrimeCyclicPreparation F K) :
    ramifiedHasseWildLambda F K P =
      criticalNormRamificationLambda F K P.ht P.hres P.piK P.hpiK := by
  rw [ramifiedHasseWildLambda, criticalNormRamificationLambda,
    ← ramifiedHasse_residueEquiv_eq_criticalNormResidueEquiv F K P.hres]
  congr 1

/-- The chosen generator lies in the exact lower-break shell, with the
correct upper-field displacement direction. -/
theorem ramifiedHasseBreakGenerator_exact_shell
    (P : PrimeCyclicPreparation F K) :
    (PrimeCyclicExtension.generator F K ∈
        lowerRamificationGroup F K (P.t : ℤ) ∧
      PrimeCyclicExtension.generator F K ∉
        lowerRamificationGroup F K ((P.t : ℤ) + 1)) ∧
      ord K (PrimeCyclicExtension.generator F K (P.piK : K) -
        (P.piK : K)) = (((P.t + 1 : ℕ) : ℤ) : WithTop ℤ) := by
  have hshell := PrimeCyclicExtension.generator_mem_break_and_not_mem_succ
    F K P.ht
  refine ⟨hshell, ?_⟩
  exact (lowerRamificationGroup_mem_and_not_mem_succ_iff_ord_sub_eq
    F K P.piK P.hgen).1 hshell

theorem ramifiedHasseWildCoordinateValue_order
    (P : PrimeCyclicPreparation F K) :
    ord K (ramifiedHasseWildCoordinateValue F K P) =
      (0 : WithTop ℤ) := by
  rw [ramifiedHasseWildCoordinateValue_eq_normalizedDisplacement]
  apply ord_lowerRamificationNormalizedDisplacement_eq_zero
    F K (ramifiedHasseBreakGenerator F K P) P.piK P.hpiK P.hgen
  exact (PrimeCyclicExtension.generator_mem_break_and_not_mem_succ
    F K P.ht).2

/-- Exact lift and quotient-class origin of the wild lambda coordinate. -/
theorem ramifiedHasseWildLambda_origin
    (P : PrimeCyclicPreparation F K) :
    ∃ lambdaLift : lattice K 0,
      (lambdaLift : K) =
          (PrimeCyclicExtension.generator F K
              (ramifiedHasseUpperUniformizer F K P : K) -
            (ramifiedHasseUpperUniformizer F K P : K)) /
            (ramifiedHasseUpperUniformizer F K P : K) ^ (P.t + 1) ∧
        PhaseReductionResidualCoordinateSource.residueEquiv P.hres
            (ramifiedHasseWildLambda F K P) =
          reduce K (lambdaLift : K) lambdaLift.property := by
  let lambdaLift := lowerRamificationNormalizedDisplacement F K
    (ramifiedHasseBreakGenerator F K P) (P.piK : K) P.hpiK
  refine ⟨lambdaLift, ?_, ?_⟩
  · symm
    exact ramifiedHasseWildCoordinateValue_eq_normalizedDisplacement F K P
  · rw [ramifiedHasseWildLambda]
    rw [(PhaseReductionResidualCoordinateSource.residueEquiv P.hres).apply_symm_apply]
    rfl

theorem ramifiedHasseWildLambda_ne_zero
    (P : PrimeCyclicPreparation F K) :
    ramifiedHasseWildLambda F K P ≠ 0 := by
  intro hz
  have hz' := congrArg
    (PhaseReductionResidualCoordinateSource.residueEquiv
      (F := F) (K := K) P.hres) hz
  rw [ramifiedHasseWildLambda,
    (PhaseReductionResidualCoordinateSource.residueEquiv P.hres).apply_symm_apply,
    map_zero] at hz'
  exact (lowerRamificationResidueDisplacement_ne_zero F K
    (ramifiedHasseBreakGenerator F K P) P.piK P.hpiK P.hgen
    (PrimeCyclicExtension.generator_mem_break_and_not_mem_succ F K P.ht).2) hz'

/-- Bilinear trace specialization used by the later pointwise phase
constructor.  It retains the actual representatives `a` and `b`. -/
theorem ramifiedHasse_trace_product_specialization
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) (a b : F) :
    trace F K
        (ramifiedHasseLocalInput F K P dK a *
          ramifiedHasseLocalInput F K P dK b) =
      ramifiedHasseNormalizedTrace F K P d dK *
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) * a * b := by
  have hprod :
      ramifiedHasseLocalInput F K P dK a *
          ramifiedHasseLocalInput F K P dK b =
        algebraMap F K (a * b) *
          (ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK) := by
    have hpow : (ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK) =
      (ramifiedHasseUpperUniformizer F K P : K) ^ dK *
        (ramifiedHasseUpperUniformizer F K P : K) ^ dK := by
      rw [← pow_add]
      congr 1
      omega
    simp only [ramifiedHasseLocalInput, map_mul, hpow]
    ring
  calc
    trace F K
        (ramifiedHasseLocalInput F K P dK a *
          ramifiedHasseLocalInput F K P dK b) =
      trace F K (algebraMap F K (a * b) *
        (ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK)) :=
          congrArg (trace F K) hprod
    _ = (a * b) * trace F K
        ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK)) := by
      simpa [Algebra.smul_def] using
        (Algebra.trace F K).map_smul (a * b)
          ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK))
    _ = ramifiedHasseNormalizedTrace F K P d dK *
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) * a * b := by
      rw [ramifiedHasse_epsilon_trace_specialization F K P d dK]
      ring

end ResidualCoordinates

section Certificate

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Cohesive local certificate consumed by `RamifiedHassePreparation`.
It contains no character data and no pointwise finite Hasse comparison. -/
structure RamifiedHasseLocalGeometryData
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) : Prop where
  degree_odd : Odd (Module.finrank F K)
  lowerDepth_pos : 0 < d
  stableRange : P.t = 0 ∨ P.t + 1 ≤ d
  stationaryDepthRelation :
    2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d
  upperUniformizer_order :
    ord K (ramifiedHasseUpperUniformizer F K P : K) =
      ((1 : ℤ) : WithTop ℤ)
  lowerUniformizer_order :
    ord F (ramifiedHasseLowerUniformizer F K P : F) =
      ((1 : ℤ) : WithTop ℤ)
  norm_uniformizer :
    normUnits F K (ramifiedHasseUpperUniformizer F K P) =
      ramifiedHasseLowerUniformizer F K P
  residueEquiv_eq_extension : ∀ x : ResidueField F,
    PhaseReductionResidualCoordinateSource.residueEquiv P.hres x =
      extensionResidueMap F K x
  residueLift_spec : ∀ x : ResidueField F,
    residueMap F (teichmuller F x) = x
  traceFloor : ∀ (a : F), a ∈ lattice F 0 →
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F (((dK : ℤ) +
        (((Module.finrank F K - 1) * (P.t + 1) : ℕ) : ℤ)) /
          (Module.finrank F K : ℤ))
  traceDepth : ∀ (a : F), a ∈ lattice F 0 →
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈ lattice F (d : ℤ)
  traceDepth_of_break_pos : 0 < P.t → ∀ (a : F), a ∈ lattice F 0 →
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((d + 1 : ℕ) : ℤ)
  traceDepth_deeper : ∀ (a : F), a ∈ lattice F 1 →
    trace F K (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((d + 1 : ℕ) : ℤ)
  secondSymmetricDepth : ∀ (a : F), a ∈ lattice F 0 →
    elementarySymmetric F K 2 (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d : ℕ) : ℤ)
  secondSymmetricDepth_deeper : ∀ (a : F), a ∈ lattice F 1 →
    elementarySymmetric F K 2 (ramifiedHasseLocalInput F K P dK a) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ)
  higherSymmetricDepth : ∀ (a : F), a ∈ lattice F 0 →
    ∀ j, 3 ≤ j → j ≤ Module.finrank F K →
      elementarySymmetric F K j (ramifiedHasseLocalInput F K P dK a) ∈
        lattice F ((2 * d + 1 : ℕ) : ℤ)
  normTruncation : ∀ (a : F), a ∈ lattice F 0 →
    norm F K (1 + ramifiedHasseLocalInput F K P dK a) -
        (1 + trace F K (ramifiedHasseLocalInput F K P dK a) +
          elementarySymmetric F K 2
            (ramifiedHasseLocalInput F K P dK a)) ∈
      lattice F ((2 * d + 1 : ℕ) : ℤ)
  epsilon_order :
    ord F (ramifiedHasseNormalizedTrace F K P d dK) = (0 : WithTop ℤ)
  epsilon_mem_lattice_zero :
    ramifiedHasseNormalizedTrace F K P d dK ∈ lattice F 0
  epsilonResidue_eq :
    ramifiedHasseNormalizedTraceResidue F K P degree_odd lowerDepth_pos
        stableRange stationaryDepthRelation =
      reduce F (ramifiedHasseNormalizedTrace F K P d dK)
        epsilon_mem_lattice_zero
  tameCoordinate_order : P.t = 0 →
    ord K (ramifiedHasseTameCoordinateValue F K P d dK) =
      (0 : WithTop ℤ)
  tameCoordinate_origin : P.t = 0 →
    ∃ cLift : lattice K 0,
      (cLift : K) =
          (ramifiedHasseUpperUniformizer F K P : K) ^ dK /
            algebraMap F K
              ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ∧
        PhaseReductionResidualCoordinateSource.residueEquiv P.hres
            (ramifiedHasseTameCoordinate F K P d dK) =
          reduce K (cLift : K) cLift.property
  tameCoordinate_ne_zero : P.t = 0 →
    ramifiedHasseTameCoordinate F K P d dK ≠ 0
  wildGenerator_exact_shell :
    (PrimeCyclicExtension.generator F K ∈
        lowerRamificationGroup F K (P.t : ℤ) ∧
      PrimeCyclicExtension.generator F K ∉
        lowerRamificationGroup F K ((P.t : ℤ) + 1)) ∧
      ord K (PrimeCyclicExtension.generator F K (P.piK : K) -
        (P.piK : K)) = (((P.t + 1 : ℕ) : ℤ) : WithTop ℤ)
  wildCoordinate_order :
    ord K (ramifiedHasseWildCoordinateValue F K P) = (0 : WithTop ℤ)
  wildLambda_origin : 0 < P.t →
    ∃ lambdaLift : lattice K 0,
      (lambdaLift : K) =
          (PrimeCyclicExtension.generator F K
              (ramifiedHasseUpperUniformizer F K P : K) -
            (ramifiedHasseUpperUniformizer F K P : K)) /
            (ramifiedHasseUpperUniformizer F K P : K) ^ (P.t + 1) ∧
        PhaseReductionResidualCoordinateSource.residueEquiv P.hres
            (ramifiedHasseWildLambda F K P) =
          reduce K (lambdaLift : K) lambdaLift.property
  wildLambda_ne_zero : 0 < P.t →
    ramifiedHasseWildLambda F K P ≠ 0
  epsilonTraceSpecialization :
    trace F K
        ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK)) =
      ramifiedHasseNormalizedTrace F K P d dK *
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d)
  traceProductSpecialization : ∀ a b : F,
    trace F K
        (ramifiedHasseLocalInput F K P dK a *
          ramifiedHasseLocalInput F K P dK b) =
      ramifiedHasseNormalizedTrace F K P d dK *
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) * a * b

/-- Principal constructor for the complete local ramified geometry package.
The assumptions are exactly the odd stable-high depth hypotheses. -/
theorem ramifiedHasseLocalGeometry
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (hodd : Odd (Module.finrank F K)) (hd : 0 < d)
    (hstable : P.t = 0 ∨ P.t + 1 ≤ d)
    (hdepth : 2 * dK + (Module.finrank F K - 1) * P.t =
      2 * Module.finrank F K * d) :
    RamifiedHasseLocalGeometryData F K P d dK := by
  let epsilonIntegral :=
    ramifiedHasseNormalizedTraceIntegral F K P hodd hd hstable hdepth
  refine {
    degree_odd := hodd
    lowerDepth_pos := hd
    stableRange := hstable
    stationaryDepthRelation := hdepth
    upperUniformizer_order := ramifiedHasseUpperUniformizer_order F K P
    lowerUniformizer_order := ramifiedHasseLowerUniformizer_order F K P
    norm_uniformizer := ramifiedHasse_norm_upperUniformizer F K P
    residueEquiv_eq_extension :=
      PhaseReductionResidualCoordinateSource.residueEquiv_apply P.hres
    residueLift_spec := residueMap_teichmuller F
    traceFloor := ramifiedHasse_trace_floor F K P dK
    traceDepth := ramifiedHasse_trace_depth F K P d dK hd hstable hdepth
    traceDepth_of_break_pos := fun ht ↦
      ramifiedHasse_trace_depth_of_break_pos F K P d dK hodd ht hstable hdepth
    traceDepth_deeper :=
      ramifiedHasse_trace_depth_deeper F K P d dK hd hstable hdepth
    secondSymmetricDepth :=
      ramifiedHasse_second_symmetric_depth F K P d dK hodd hstable hdepth
    secondSymmetricDepth_deeper :=
      ramifiedHasse_second_symmetric_depth_deeper F K P d dK hodd hstable hdepth
    higherSymmetricDepth := fun a ha j hj hjle ↦
      ramifiedHasse_higher_symmetric_depth F K P d dK hodd hd hstable
        hdepth a ha j hj hjle
    normTruncation :=
      ramifiedHasse_norm_truncation F K P d dK hodd hd hstable hdepth
    epsilon_order :=
      ramifiedHasseNormalizedTrace_order F K P hodd hd hstable hdepth
    epsilon_mem_lattice_zero := epsilonIntegral.property
    epsilonResidue_eq := by
      rfl
    tameCoordinate_order := fun ht ↦
      ramifiedHasseTameCoordinateValue_order F K P ht hdepth
    tameCoordinate_origin := fun ht ↦
      ramifiedHasseTameCoordinate_origin F K P ht hdepth
    tameCoordinate_ne_zero := fun ht ↦
      ramifiedHasseTameCoordinate_ne_zero F K P ht hdepth
    wildGenerator_exact_shell := ramifiedHasseBreakGenerator_exact_shell F K P
    wildCoordinate_order := ramifiedHasseWildCoordinateValue_order F K P
    wildLambda_origin := fun _ ↦ ramifiedHasseWildLambda_origin F K P
    wildLambda_ne_zero := fun _ ↦ ramifiedHasseWildLambda_ne_zero F K P
    epsilonTraceSpecialization :=
      ramifiedHasse_epsilon_trace_specialization F K P d dK
    traceProductSpecialization :=
      ramifiedHasse_trace_product_specialization F K P d dK }

namespace RamifiedHasseLocalGeometryData

/-- In the positive-break branch, the stable normalized-trace residue is
the manuscript's critical coefficient `-lambda^(p-1)`, expressed in the
wild coordinate retained by the local-geometry certificate. -/
theorem wild_epsilonResidue_eq
    {P : PrimeCyclicPreparation F K} {d dK : ℕ}
    (D : RamifiedHasseLocalGeometryData F K P d dK)
    (ht : 0 < P.t) :
    ramifiedHasseNormalizedTraceResidue F K P D.degree_odd
        D.lowerDepth_pos D.stableRange D.stationaryDepthRelation =
      -ramifiedHasseWildLambda F K P ^ (Module.finrank F K - 1) := by
  rw [ramifiedHasseNormalizedTraceResidue_eq_criticalNormLinearCoefficient
    F K P D.degree_odd D.lowerDepth_pos D.stableRange
      D.stationaryDepthRelation ht]
  rw [criticalNormLinearCoefficient_eq_neg_ramificationLambda_pow
    F K P.ht ht P.hres P.piK P.hpiK P.hgen]
  rw [← ramifiedHasseWildLambda_eq_criticalNormRamificationLambda F K P]

end RamifiedHasseLocalGeometryData

end Certificate

end

end LanglandsFirstMainLemma
