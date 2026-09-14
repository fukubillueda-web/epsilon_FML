import LanglandsFirstMainLemma.Ramification.PrimeCyclicExtension

/-!
# Ramification classification in prime degree

For a cyclic Galois extension of prime degree, the identity

`[K : F] = e(K/F) * f(K/F)`

forces the extension to be unramified or totally ramified.  In the ramified case we use the
standard local-field definitions: tame means that the residue characteristic does not divide
the ramification index, and wild means that it does.  Wildness then forces the residue
characteristic to equal the prime extension degree.  Finally, primality splits that degree into
the quadratic and odd-prime cases used by the final dispatch.

All invariants are the canonical invariants supplied by the local-field extension API; none of
the conclusions below is stored in `PrimeCyclicExtension`.
-/

noncomputable section

namespace LanglandsFirstMainLemma

section PrimeDegreeDichotomy

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- A finite local-field extension is tamely ramified when its residue characteristic does not
divide its ramification index.  This convention includes unramified extensions. -/
def IsTamelyRamified : Prop :=
  ¬residueCharacteristic F ∣ ramificationIndex F K

/-- A finite local-field extension is wildly ramified when its residue characteristic divides
its ramification index. -/
def IsWildlyRamified : Prop :=
  residueCharacteristic F ∣ ramificationIndex F K

/-- The prime-degree factorization `[K : F] = e(K/F) f(K/F)` implies that the ramification
index or the residue degree is one.  These are exactly the unramified and totally ramified
alternatives. -/
theorem unramified_or_totallyRamified :
    ramificationIndex F K = 1 ∨ residueDegree F K = 1 := by
  have hprime :
      (ramificationIndex F K * residueDegree F K).Prime := by
    rw [← PrimeCyclicExtension.degree_eq_ramificationIndex_mul_residueDegree F K]
    exact PrimeCyclicExtension.degree_prime F K
  rcases Nat.prime_mul_iff.mp hprime with hram | hres
  · exact Or.inr hram.2
  · exact Or.inl hres.2

/-- A ramified cyclic extension of prime degree is totally ramified. -/
theorem totallyRamified_of_ramified
    (hram : ramificationIndex F K ≠ 1) :
    residueDegree F K = 1 :=
  (unramified_or_totallyRamified F K).resolve_left hram

omit [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K] in
/-- Tame and wild ramification are complementary and exhaustive. -/
theorem isTamelyRamified_or_isWildlyRamified :
    IsTamelyRamified F K ∨ IsWildlyRamified F K := by
  by_cases hwild : residueCharacteristic F ∣ ramificationIndex F K
  · exact Or.inr hwild
  · exact Or.inl hwild

/-- In a wildly ramified cyclic extension of prime degree, the residue characteristic equals
the extension degree. -/
theorem residueCharacteristic_eq_degree_of_isWildlyRamified
    (hwild : IsWildlyRamified F K) :
    residueCharacteristic F = Module.finrank F K := by
  apply (Nat.prime_dvd_prime_iff_eq
    (residueCharacteristic_prime F)
    (PrimeCyclicExtension.degree_prime F K)).mp
  rw [PrimeCyclicExtension.degree_eq_ramificationIndex_mul_residueDegree F K]
  exact dvd_mul_of_dvd_left hwild (residueDegree F K)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K] in
/-- The prime extension degree is either two or odd. -/
theorem degree_eq_two_or_odd :
    Module.finrank F K = 2 ∨ Odd (Module.finrank F K) :=
  (PrimeCyclicExtension.degree_prime F K).eq_two_or_odd'

/-- Complete ramified classification: total ramification, followed by the tame/wild split;
the wild branch records the residue-characteristic equality, and both branches carry the
quadratic/odd-prime split needed by the final case dispatch. -/
theorem ramified_primeDegree_classification
    (hram : ramificationIndex F K ≠ 1) :
    residueDegree F K = 1 ∧
      ((IsTamelyRamified F K ∧
          (Module.finrank F K = 2 ∨ Odd (Module.finrank F K))) ∨
        (IsWildlyRamified F K ∧
          residueCharacteristic F = Module.finrank F K ∧
          (Module.finrank F K = 2 ∨ Odd (Module.finrank F K)))) := by
  refine ⟨totallyRamified_of_ramified F K hram, ?_⟩
  rcases isTamelyRamified_or_isWildlyRamified F K with htame | hwild
  · exact Or.inl ⟨htame, degree_eq_two_or_odd F K⟩
  · exact Or.inr ⟨hwild,
      residueCharacteristic_eq_degree_of_isWildlyRamified F K hwild,
      degree_eq_two_or_odd F K⟩

/-- Exhaustive classification in the form consumed by the final dispatch. -/
theorem primeDegree_ramification_classification :
    ramificationIndex F K = 1 ∨
      (residueDegree F K = 1 ∧
        ((IsTamelyRamified F K ∧
            (Module.finrank F K = 2 ∨ Odd (Module.finrank F K))) ∨
          (IsWildlyRamified F K ∧
            residueCharacteristic F = Module.finrank F K ∧
            (Module.finrank F K = 2 ∨ Odd (Module.finrank F K))))) := by
  by_cases hram : ramificationIndex F K = 1
  · exact Or.inl hram
  · exact Or.inr (ramified_primeDegree_classification F K hram)

end PrimeDegreeDichotomy

end LanglandsFirstMainLemma
