import LanglandsFirstMainLemma.Prelude

namespace LanglandsFirstMainLemma

/-- In characteristic `p`, the canonical image of `p` is zero. -/
theorem characteristicConvention {E : Type*} [AddMonoidWithOne E]
    (p : ℕ) [CharP E p] :
    (p : E) = 0 :=
  CharP.cast_eq_zero E p

/-- In characteristic two, the canonical image of `2` is zero. -/
theorem characteristicTwoConvention {E : Type*} [AddMonoidWithOne E]
    [CharP E 2] :
    (2 : E) = 0 :=
  characteristicConvention 2

/-- In characteristic zero, a nonzero natural number has nonzero canonical image. -/
theorem natCast_ne_zero_of_charZero {E : Type*} [AddMonoidWithOne E]
    [CharZero E] {n : ℕ} (hn : n ≠ 0) :
    (n : E) ≠ 0 :=
  Nat.cast_ne_zero.mpr hn

/-- In characteristic zero, a nonzero integer has nonzero canonical image. -/
theorem intCast_ne_zero_of_charZero {E : Type*} [AddGroupWithOne E]
    [CharZero E] {z : ℤ} (hz : z ≠ 0) :
    (z : E) ≠ 0 :=
  Int.cast_ne_zero.mpr hz

end LanglandsFirstMainLemma
