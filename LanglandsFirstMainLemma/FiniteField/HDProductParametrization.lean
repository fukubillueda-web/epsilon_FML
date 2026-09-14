import LanglandsFirstMainLemma.FiniteField.CharacterAPI
import LanglandsFirstMainLemma.Basic.FiniteProducts

/-!
# Product-constrained tuples in the Hasse--Davenport calculation

When a product of `n + 1` Gauss sums is expanded, multiplicative-character
orthogonality leaves tuples whose coordinate product is prescribed.  This
file gives the finite reindexing used for those surviving tuples: the first
`n` coordinates are free and the last coordinate is uniquely determined.
In particular every fiber of the tuple-product map has cardinality
`|G| ^ n`.
-/

open scoped BigOperators

namespace LanglandsFirstMainLemma

/-- Tuples of length `n` in a commutative group whose coordinate product is
the prescribed element `a`. -/
def HDProductTupleFiber (G : Type*) [CommGroup G] (n : ℕ) (a : G) :=
  {x : Fin n → G // ∏ i, x i = a}

/-- An explicit parametrization of a prescribed product fiber: choose the
first `n` entries freely and take the last entry to be
`a * (∏ i, x i)⁻¹`. -/
def hdProductTupleFiberEquiv {G : Type*} [CommGroup G] (n : ℕ) (a : G) :
    HDProductTupleFiber G (n + 1) a ≃ (Fin n → G) where
  toFun x := fun i ↦ x.1 i.castSucc
  invFun x := ⟨Fin.snoc x (a * (∏ i, x i)⁻¹), by
    rw [Fin.prod_univ_castSucc]
    simp⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Fin.snoc_last]
      change a * (∏ j : Fin n, x.1 j.castSucc)⁻¹ = x.1 (Fin.last n)
      have hxprod :
          (∏ j : Fin n, x.1 j.castSucc) * x.1 (Fin.last n) = a := by
        simpa only [Fin.prod_univ_castSucc] using x.2
      calc
        a * (∏ j : Fin n, x.1 j.castSucc)⁻¹ =
            ((∏ j : Fin n, x.1 j.castSucc) * x.1 (Fin.last n)) *
              (∏ j : Fin n, x.1 j.castSucc)⁻¹ :=
          congrArg (· * (∏ j : Fin n, x.1 j.castSucc)⁻¹) hxprod.symm
        _ = x.1 (Fin.last n) := by
          calc
            ((∏ j : Fin n, x.1 j.castSucc) * x.1 (Fin.last n)) *
                (∏ j : Fin n, x.1 j.castSucc)⁻¹ =
                x.1 (Fin.last n) *
                  ((∏ j : Fin n, x.1 j.castSucc) *
                    (∏ j : Fin n, x.1 j.castSucc)⁻¹) := by
              ac_rfl
            _ = x.1 (Fin.last n) := by simp
    · simp
  right_inv x := by
    funext i
    simp

/-- The explicit parametrization really preserves the chosen free
coordinates. -/
@[simp]
theorem hdProductTupleFiberEquiv_apply {G : Type*} [CommGroup G]
    (n : ℕ) (a : G) (x : HDProductTupleFiber G (n + 1) a) (i : Fin n) :
    hdProductTupleFiberEquiv n a x i = x.1 i.castSucc :=
  rfl

/-- The inverse parametrization appends exactly the coordinate forced by the
product constraint. -/
@[simp]
theorem hdProductTupleFiberEquiv_symm_apply {G : Type*} [CommGroup G]
    (n : ℕ) (a : G) (x : Fin n → G) :
    (hdProductTupleFiberEquiv n a).symm x =
      ⟨Fin.snoc x (a * (∏ i, x i)⁻¹), by
        rw [Fin.prod_univ_castSucc]
        simp⟩ :=
  rfl

/-- The finite structure on a surviving product fiber is transported along
the explicit parametrization, so its enumeration is the enumeration of the
free coordinates. -/
noncomputable instance hdProductTupleFiberSuccFintype
    {G : Type*} [CommGroup G] [Fintype G] (n : ℕ) (a : G) :
    Fintype (HDProductTupleFiber G (n + 1) a) :=
  Fintype.ofEquiv (Fin n → G) (hdProductTupleFiberEquiv n a).symm

/-- Reindex a finite sum over surviving tuples by the `n` freely chosen
coordinates.  The appended coordinate is part of the equivalence rather
than an implicit choice. -/
theorem sum_hdProductTupleFiber {G R : Type*} [CommGroup G] [Fintype G]
    [AddCommMonoid R] (n : ℕ) (a : G)
    (f : HDProductTupleFiber G (n + 1) a → R) :
    ∑ x, f x = ∑ y : Fin n → G, f ((hdProductTupleFiberEquiv n a).symm y) := by
  classical
  exact (Equiv.sum_comp (hdProductTupleFiberEquiv n a).symm f).symm

/-- Every prescribed-product fiber of `(n + 1)`-tuples has the same
cardinality, namely `|G| ^ n`.  This is the constant-fiber count for the
surviving tuples in the Hasse--Davenport expansion. -/
theorem hdProduct_survivingTuples {G : Type*} [CommGroup G] [Fintype G]
    (n : ℕ) (a : G) :
    Fintype.card (HDProductTupleFiber G (n + 1) a) = Fintype.card G ^ n := by
  classical
  rw [Fintype.card_congr (hdProductTupleFiberEquiv n a), Fintype.card_fun,
    Fintype.card_fin]

end LanglandsFirstMainLemma
