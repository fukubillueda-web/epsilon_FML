import LanglandsFirstMainLemma.FiniteField.QuadraticPhase

namespace LanglandsFirstMainLemma

variable {k : Type*} [Field k] [Fintype k]

/-- The three exact power identities for the basic normalized quadratic phase.
Here the exponent is the residue characteristic, exactly as in the manuscript. -/
theorem quadraticPhase_powers (hchar : ringChar k ≠ 2)
    {psi : FiniteAddChar k} (hpsi : psi ≠ 1) :
    quadraticPhase psi 1 0 ^ 2 = finiteQuadraticChar k (-1) ∧
      quadraticPhase psi 1 0 ^ (ringChar k - 1) = finiteQuadraticChar k (-1) ∧
      quadraticPhase psi 1 0 ^ ringChar k =
        quadraticPhase psi 1 0 * finiteQuadraticChar k (-1) := by
  classical
  let q0 := quadraticPhase psi 1 0
  have hsq : q0 ^ 2 = finiteQuadraticChar k (-1) := by
    simpa [q0] using quadraticPhase_basic_sq hchar hpsi
  have hfour : q0 ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hsq,
      finiteQuadraticChar_sq k (neg_ne_zero.mpr one_ne_zero)]
  have hp : Nat.Prime (ringChar k) := CharP.char_is_prime k (ringChar k)
  have hpodd : ringChar k % 2 = 1 :=
    (hp.mod_two_eq_one_iff_ne_two).2 hchar
  have hpred : q0 ^ (ringChar k - 1) = finiteQuadraticChar k (-1) := by
    rcases Nat.odd_mod_four_iff.mp hpodd with hpone | hpthree
    · obtain ⟨n, _hnprime, hcard⟩ := FiniteField.card k (ringChar k)
      have hpmod : ringChar k ≡ 1 [MOD 4] := by
        simpa [Nat.ModEq] using hpone
      have hcardone : Fintype.card k % 4 = 1 := by
        have hpowmod := hpmod.pow (n : ℕ)
        simp [Nat.ModEq] at hpowmod
        simpa [hcard] using hpowmod
      have hnu : finiteQuadraticChar k (-1) = 1 := by
        change ((quadraticChar k (-1) : ℤ) : ℂ) = 1
        rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_one_mod_four hcardone]
        norm_num
      have hpredmod : (ringChar k - 1) % 4 = 0 := by omega
      rw [pow_eq_pow_mod (ringChar k - 1) hfour, hpredmod, pow_zero, hnu]
    · have hpredmod : (ringChar k - 1) % 4 = 2 := by omega
      calc
        q0 ^ (ringChar k - 1) = q0 ^ ((ringChar k - 1) % 4) :=
          pow_eq_pow_mod (ringChar k - 1) hfour
        _ = q0 ^ 2 := by rw [hpredmod]
        _ = finiteQuadraticChar k (-1) := hsq
  refine ⟨?_, hpred, ?_⟩
  · simpa [q0] using hsq
  · change q0 ^ ringChar k = q0 * finiteQuadraticChar k (-1)
    calc
      q0 ^ ringChar k = q0 ^ ((ringChar k - 1) + 1) := by
        rw [Nat.sub_add_cancel hp.one_le]
      _ = q0 * finiteQuadraticChar k (-1) := by rw [pow_add, hpred, pow_one, mul_comm]

end LanglandsFirstMainLemma
