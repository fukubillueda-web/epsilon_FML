import LanglandsFirstMainLemma.Parameters.High
import LanglandsFirstMainLemma.Parameters.Low
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary
import LanglandsFirstMainLemma.Lamprecht.Formula
import LanglandsFirstMainLemma.Lamprecht.CriticalPolarCoordinate
import LanglandsFirstMainLemma.Delta.ErrorTerm

/-!
# Exact high/low phase-parameter dispatch

This module contains only the disjoint low/high conductor-range convention
used by the `PhaseReduction` compatibility facade.
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators Polynomial

/-! ## Exact high/low dispatch -/

/-- The assembly convention assigns the overlap `m = t + 1` to the low
range.  Thus the two cases are disjoint even though the public high parameter
table itself is valid at the boundary. -/
inductive PhaseParameterRange (t m : ℕ) : Prop where
  | low (h : m ≤ t + 1)
  | high (h : t + 1 < m)

/-- Every conductor belongs to exactly the manuscript's low or high assembly
range. -/
theorem phaseParameterRange_cases (t m : ℕ) :
    PhaseParameterRange t m := by
  by_cases h : m ≤ t + 1
  · exact .low h
  · exact .high (by omega)

/-- The boundary conductor is routed to the low table. -/
theorem phaseParameterRange_boundary (t : ℕ) :
    PhaseParameterRange t (t + 1) :=
  .low le_rfl

/-- The low and high assembly inequalities cannot overlap. -/
theorem phaseParameterRange_disjoint {t m : ℕ} :
    ¬ (m ≤ t + 1 ∧ t + 1 < m) := by
  omega

end

end LanglandsFirstMainLemma
