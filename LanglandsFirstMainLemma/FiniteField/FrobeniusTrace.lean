import Mathlib.FieldTheory.Finite.Trace

/-!
# Frobenius-minus-identity images and finite-field trace kernels
-/

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

theorem finiteField_frobeniusSub_range_eq_traceKer
    (k : Type*) [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hp : ringChar k = p) :
    Set.range (fun z : k ↦ z ^ p - z) =
      ((Algebra.trace (ZMod p) k).ker : Set k) := by
  subst p
  let p := ringChar k
  let Q : k →+ k :=
    (frobenius k p).toAddMonoidHom - AddMonoidHom.id k
  have hQ (z : k) : Q z = z ^ p - z := rfl
  have hkerQ : Q.ker = (⊥ : Subfield k).toAddSubgroup := by
    ext z
    rw [AddMonoidHom.mem_ker]
    change z ^ p - z = 0 ↔ z ∈ (⊥ : Subfield k)
    rw [sub_eq_zero, Subfield.mem_bot_iff_pow_eq_self]
  have hkerQcard : Nat.card Q.ker = p := by
    rw [hkerQ]
    exact Subfield.card_bot k p
  have hQcard : Nat.card k = Nat.card Q.range * p := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Q.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Q).toEquiv,
      hkerQcard]
  let tr : k →+ ZMod p := (Algebra.trace (ZMod p) k).toAddMonoidHom
  have htrSurj : Function.Surjective tr := by
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate k
      (a := (1 : k)) one_ne_zero
    simp only [one_mul] at hb
    intro y
    refine ⟨(algebraMap (ZMod p) k (y / tr b)) * b, ?_⟩
    change Algebra.trace (ZMod p) k
        (algebraMap (ZMod p) k (y / tr b) * b) = y
    rw [← Algebra.smul_def, map_smul]
    change (y / tr b) * tr b = y
    exact div_mul_cancel₀ y hb
  have htrRange : tr.range = ⊤ := by
    apply top_unique
    intro y _hy
    exact htrSurj y
  have htrRangeCard : Nat.card tr.range = p := by
    rw [htrRange]
    calc
      Nat.card (↥(⊤ : AddSubgroup (ZMod p))) = Nat.card (ZMod p) :=
        Nat.card_congr AddSubgroup.topEquiv.toEquiv
      _ = p := Nat.card_zmod p
  have htrCard : Nat.card k = p * Nat.card tr.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup tr.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange tr).toEquiv,
      htrRangeCard]
  have hcard : Nat.card Q.range = Nat.card tr.ker := by
    apply Nat.mul_right_cancel ((Fact.out : Nat.Prime p).pos)
    calc
      Nat.card Q.range * p = Nat.card k := hQcard.symm
      _ = p * Nat.card tr.ker := htrCard
      _ = Nat.card tr.ker * p := Nat.mul_comm _ _
  have hle : Q.range ≤ tr.ker := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    change Algebra.trace (ZMod p) k (Q z) = 0
    rw [hQ, map_sub]
    let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k
    have hsigma : sigma z = z ^ p := by
      rw [show sigma z = z ^ Fintype.card (ZMod p) by
        exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
          (ZMod p) k) z]
      simp only [ZMod.card]
    rw [← hsigma, Algebra.trace_eq_of_algEquiv sigma, sub_self]
  have hrange : Q.range = tr.ker := by
    apply AddSubgroup.eq_of_le_of_card_ge hle
    exact hcard.symm.le
  ext y
  rw [Set.mem_range]
  change (∃ z : k, z ^ p - z = y) ↔ y ∈ (Algebra.trace (ZMod p) k).ker
  change (∃ z : k, Q z = y) ↔ y ∈ tr.ker
  rw [← hrange]
  rfl

theorem finiteField_scaledFrobeniusSub_range_eq_scaledTraceKer
    (k : Type*) [Field k] [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hp : ringChar k = p) (lambda : k) (hlambda : lambda ≠ 0) :
    Set.range (fun z : k ↦ z ^ p - lambda ^ (p - 1) * z) =
      Set.range (fun y : (Algebra.trace (ZMod p) k).ker ↦
        lambda ^ p * (y : k)) := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpow : lambda ^ (p - 1) * lambda = lambda ^ p := by
    calc
      lambda ^ (p - 1) * lambda = lambda ^ ((p - 1) + 1) :=
        (pow_succ lambda (p - 1)).symm
      _ = lambda ^ p := by congr 1; omega
  have hscale (x : k) :
      (lambda * x) ^ p - lambda ^ (p - 1) * (lambda * x) =
        lambda ^ p * (x ^ p - x) := by
    rw [mul_pow, ← mul_assoc, hpow]
    ring
  have himage := finiteField_frobeniusSub_range_eq_traceKer k p hp
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    let x : k := z / lambda
    have hzx : z = lambda * x := by
      dsimp only [x]
      field_simp
    have hxker : x ^ p - x ∈ (Algebra.trace (ZMod p) k).ker := by
      change x ^ p - x ∈ ((Algebra.trace (ZMod p) k).ker : Set k)
      rw [← himage]
      exact ⟨x, rfl⟩
    refine ⟨⟨x ^ p - x, hxker⟩, ?_⟩
    rw [hzx]
    change lambda ^ p * (x ^ p - x) =
      (lambda * x) ^ p - lambda ^ (p - 1) * (lambda * x)
    exact (hscale x).symm
  · rintro ⟨y, rfl⟩
    have hy : (y : k) ∈ Set.range (fun x : k ↦ x ^ p - x) := by
      rw [himage]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    refine ⟨lambda * x, ?_⟩
    change (lambda * x) ^ p - lambda ^ (p - 1) * (lambda * x) =
      lambda ^ p * (y : k)
    change x ^ p - x = (y : k) at hx
    rw [hscale, hx]

end

end LanglandsFirstMainLemma
