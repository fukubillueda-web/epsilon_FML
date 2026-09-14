import LanglandsFirstMainLemma.Parameters.Adjoint
import LanglandsFirstMainLemma.Lamprecht.StationaryClass
import LanglandsFirstMainLemma.Lamprecht.Formula

/-!
# Stationary numerator classes under norm pullback

Let `chiK = chiF.compNorm`, with the exact conductors decomposed as
`mK = 2 * dK + epsilonK` and `mF = 2 * dF + epsilonF`.  A
`NormPolynomialPrecision` certificate supplies the three separate norm
filtration inclusions needed by the manuscript.  For an ordered admissible
denominator pair `(gammaF, gammaK)`, this file proves the equality

`St_{gammaK, dK + epsilonK}(chiK) = P^*_{gammaF,gammaK}
  (St_{gammaF, dF + epsilonF}(chiF))`

in `𝒪_K / 𝓅_K^dK`.

The conductors in the theorem are the conductors stored in `chiF` and `chiK`;
in particular the upstairs conductor is not identified with the downstairs
one.  Both are greater than one because that is part of the precision
certificate.  Thus no stationary class is manufactured at conductor zero or
one.  All primary statements concern lattice-quotient classes.  The separate
representative lemmas quantify over supplied representatives and prove their
independence.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-! ## The exact minimal stationary class as an honest coefficient quotient -/

/-- The Lamprecht stationary depth attached to an exact conductor
decomposition. -/
theorem stationaryDepthOfConductorDecomposition
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon) :
    IsLamprechtStationaryDepth chi.conductor (d + epsilon) :=
  lamprechtFormula_stationaryDepth E chi d epsilon h.epsilon_le_one
    h.conductor_eq h.conductor_gt_one

private noncomputable def stationaryCoefficientToLamprechtClass
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon) :
    StationaryCoefficientQuotient E d →+
      LamprechtCoefficientQuotient E (m : ℤ) (m : ℤ)
        ((d + epsilon : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) where
  toFun := latticeQuotientLift E (by omega)
    (fun c ↦ latticeQuotientMk E
      (sub_le_sub_left
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) (m : ℤ))
      ⟨(c : E), by simpa using c.property⟩)
    (fun c c' hcc' ↦ by
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth E _).2
      have hdepth : (m : ℤ) - ((d + epsilon : ℕ) : ℤ) = (d : ℤ) := by
        rw [h.conductor_eq]
        push_cast
        omega
      simpa only [hdepth] using hcc')
  map_zero' := by
    change latticeQuotientLift E (by omega) _ _
      (latticeQuotientMk E (by omega) 0) = 0
    rw [latticeQuotientLift_mk]
    apply (latticeQuotientMk_eq_zero_iff E _).2
    simp
  map_add' := by
    intro a b
    obtain ⟨a, rfl⟩ := latticeQuotientMk_surjective E (by omega) a
    obtain ⟨b, rfl⟩ := latticeQuotientMk_surjective E (by omega) b
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk,
      ← latticeQuotientMk_add]
    rfl

private noncomputable def stationaryCoefficientFromLamprechtClass
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon) :
    LamprechtCoefficientQuotient E (m : ℤ) (m : ℤ)
        ((d + epsilon : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) →+
      StationaryCoefficientQuotient E d where
  toFun := latticeQuotientLift E
    (sub_le_sub_left
      (Int.ofNat_le.mpr h.variableDepth_le_conductor) (m : ℤ))
    (fun c ↦ latticeQuotientMk E (by omega)
      ⟨(c : E), by simpa using c.property⟩)
    (fun c c' hcc' ↦ by
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth E _).2
      have hdepth : (m : ℤ) - ((d + epsilon : ℕ) : ℤ) = (d : ℤ) := by
        rw [h.conductor_eq]
        push_cast
        omega
      simpa only [hdepth] using hcc')
  map_zero' := by
    change latticeQuotientLift E _ _ _ (latticeQuotientMk E _ 0) = 0
    rw [latticeQuotientLift_mk]
    simp
  map_add' := by
    intro a b
    obtain ⟨a, rfl⟩ := latticeQuotientMk_surjective E _ a
    obtain ⟨b, rfl⟩ := latticeQuotientMk_surjective E _ b
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk,
      ← latticeQuotientMk_add]
    rfl

/-- The explicit equivalence between the literal coefficient quotient
`𝒪_E / 𝓅_E^d` and the coefficient quotient used by Lamprecht duality at
`m = 2*d + epsilon`.  It changes neither representatives nor depths. -/
noncomputable def stationaryCoefficientLamprechtEquivAtConductor
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon) :
    StationaryCoefficientQuotient E d ≃+
      LamprechtCoefficientQuotient E (m : ℤ) (m : ℤ)
        ((d + epsilon : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) where
  toFun := stationaryCoefficientToLamprechtClass E h
  invFun := stationaryCoefficientFromLamprechtClass E h
  left_inv z := by
    obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E (by omega) z
    rfl
  right_inv z := by
    obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E _ z
    rfl
  map_add' := map_add (stationaryCoefficientToLamprechtClass E h)

@[simp]
theorem stationaryCoefficientLamprechtEquivAtConductor_mk
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (c : lattice E 0) :
    stationaryCoefficientLamprechtEquivAtConductor E h
        (latticeQuotientMk E (by omega) c) =
      latticeQuotientMk E
        (sub_le_sub_left
          (Int.ofNat_le.mpr h.variableDepth_le_conductor) (m : ℤ))
        ⟨(c : E), by simpa using c.property⟩ :=
  rfl

/-- The exact minimal-depth stationary numerator class, transported from the
Lamprecht quotient to the literal quotient `𝒪_E / 𝓅_E^d`.  No representative
is chosen. -/
noncomputable def stationaryCoefficientClass
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    StationaryCoefficientQuotient E d :=
  (stationaryCoefficientLamprechtEquivAtConductor E h).symm
    (stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
      (stationaryDepthOfConductorDecomposition E chi h) gamma hgamma)

@[simp]
theorem stationaryCoefficientClass_toLamprecht
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryCoefficientLamprechtEquivAtConductor E h
        (stationaryCoefficientClass E chi psi h gamma hgamma) =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (stationaryDepthOfConductorDecomposition E chi h) gamma hgamma :=
  (stationaryCoefficientLamprechtEquivAtConductor E h).apply_symm_apply _

/-- The literal coefficient pairing is the Lamprecht pairing after the
explicit quotient transport. -/
theorem stationaryPairingLeft_eq_lamprechtPairing
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : StationaryCoefficientQuotient E d) :
    stationaryPairingLeft E h psi gamma hgamma c =
      lamprechtPairingLeft E psi
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) gamma hgamma
        (stationaryCoefficientLamprechtEquivAtConductor E h c) := by
  apply AddChar.ext
  intro y
  obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E (by omega) c
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E
    (Int.ofNat_le.mpr h.variableDepth_le_conductor) y
  rw [stationaryCoefficientLamprechtEquivAtConductor_mk,
    stationaryPairingLeft_mk_mk, lamprechtPairingLeft_apply,
    lamprechtPairing_mk_mk]

/-- Quotient-level stationary linearization at the actual conductor and its
minimal stationary depth. -/
def IsStationaryCoefficientClass
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (s : StationaryCoefficientQuotient E d) : Prop :=
  stationaryPairingLeft E h psi gamma hgamma s =
    stationaryLinearizationCharacter E chi
      (stationaryDepthOfConductorDecomposition E chi h)

/-- The transported class satisfies the stationary linearization law. -/
theorem stationaryCoefficientClass_isStationary
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    IsStationaryCoefficientClass E chi psi h gamma hgamma
      (stationaryCoefficientClass E chi psi h gamma hgamma) := by
  rw [IsStationaryCoefficientClass,
    stationaryPairingLeft_eq_lamprechtPairing,
    stationaryCoefficientClass_toLamprecht,
    lamprechtPairingLeft_stationaryNumeratorClass]

private theorem isStationaryCoefficientClass_toLamprecht
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (s : StationaryCoefficientQuotient E d)
    (hs : IsStationaryCoefficientClass E chi psi h gamma hgamma s) :
    IsStationaryNumeratorClass E chi psi (chi.conductor : ℤ)
      (stationaryDepthOfConductorDecomposition E chi h) gamma
      (stationaryCoefficientLamprechtEquivAtConductor E h s) := by
  intro c hc x
  have heval := congrArg
    (fun xi : AddChar
        (LamprechtVariableQuotient E (chi.conductor : ℤ)
          ((d + epsilon : ℕ) : ℤ)
          (stationaryDepthOfConductorDecomposition E chi h).int_le_conductor) ℂ ↦
      xi (latticeQuotientMk E
        (stationaryDepthOfConductorDecomposition E chi h).int_le_conductor x)) hs
  rw [stationaryPairingLeft_eq_lamprechtPairing, ← hc,
    lamprechtPairingLeft_apply, lamprechtPairing_mk_mk,
    stationaryLinearizationCharacter_mk] at heval
  apply Units.ext
  exact heval.symm

/-- Uniqueness of the literal quotient class, obtained by transporting the
existence-and-uniqueness theorem from `Lamprecht.StationaryClass`. -/
theorem stationaryCoefficientClass_unique
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (s : StationaryCoefficientQuotient E d)
    (hs : IsStationaryCoefficientClass E chi psi h gamma hgamma s) :
    s = stationaryCoefficientClass E chi psi h gamma hgamma := by
  apply (stationaryCoefficientLamprechtEquivAtConductor E h).injective
  rw [stationaryCoefficientClass_toLamprecht]
  exact stationaryNumeratorClass_unique E chi psi (chi.conductor : ℤ)
    (stationaryDepthOfConductorDecomposition E chi h) gamma hgamma _
    (isStationaryCoefficientClass_toLamprecht E chi psi h gamma hgamma s hs)

/-- Existence and uniqueness of the stationary class in the literal
coefficient quotient. -/
theorem stationaryCoefficientClass_existsUnique
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    ∃! s : StationaryCoefficientQuotient E d,
      IsStationaryCoefficientClass E chi psi h gamma hgamma s := by
  refine ⟨stationaryCoefficientClass E chi psi h gamma hgamma,
    stationaryCoefficientClass_isStationary E chi psi h gamma hgamma, ?_⟩
  intro s hs
  exact stationaryCoefficientClass_unique E chi psi h gamma hgamma s hs

/-- A supplied integral numerator represents the stationary coefficient class
if and only if it satisfies the stationary linearization on the whole minimal
stationary layer. -/
theorem latticeQuotientMk_eq_stationaryCoefficientClass_iff
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice E 0) :
    latticeQuotientMk E (by omega) c =
        stationaryCoefficientClass E chi psi h gamma hgamma ↔
      ∀ x : lattice E ((d + epsilon : ℕ) : ℤ),
        chi.character
            (positiveUnitOfLattice E h.variableDepth_pos x) =
          psi.character ((c : E) * (x : E) / (gamma : E)) := by
  constructor
  · intro hc x
    have heval := congrArg
      (fun xi : AddChar
          (LamprechtVariableQuotient E (chi.conductor : ℤ)
            ((d + epsilon : ℕ) : ℤ)
            (Int.ofNat_le.mpr h.variableDepth_le_conductor)) ℂ ↦
        xi (latticeQuotientMk E
          (Int.ofNat_le.mpr h.variableDepth_le_conductor) x))
      (stationaryCoefficientClass_isStationary E chi psi h gamma hgamma)
    rw [← hc, stationaryPairingLeft_mk_mk,
      stationaryLinearizationCharacter_mk] at heval
    apply Units.ext
    exact heval.symm
  · intro hlinear
    apply stationaryCoefficientClass_unique E chi psi h gamma hgamma
    rw [IsStationaryCoefficientClass]
    apply AddChar.ext
    intro z
    obtain ⟨x, rfl⟩ := latticeQuotientMk_surjective E
      (Int.ofNat_le.mpr h.variableDepth_le_conductor) z
    rw [stationaryPairingLeft_mk_mk,
      stationaryLinearizationCharacter_mk]
    exact congrArg Units.val (hlinear x).symm

/-- Restricting the minimal stationary class to any deeper admissible
stationary layer agrees with the class constructed at that layer. -/
theorem stationaryCoefficientClass_restrict
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon s : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (hdepth : d + epsilon ≤ s) (hs : s + 1 ≤ chi.conductor)
    (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryClassRestriction E (chi.conductor : ℤ)
        (stationaryDepthOfConductorDecomposition E chi h) hdepth hs
        (stationaryCoefficientLamprechtEquivAtConductor E h
          (stationaryCoefficientClass E chi psi h gamma hgamma)) =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        ((stationaryDepthOfConductorDecomposition E chi h).deeper hdepth hs)
        gamma hgamma := by
  rw [stationaryCoefficientClass_toLamprecht]
  exact stationaryNumeratorClass_restrict E chi psi (chi.conductor : ℤ)
    (stationaryDepthOfConductorDecomposition E chi h) hdepth hs gamma hgamma

/-! ## Pullback of the stationary linearization -/

/-- Pulling the downstairs stationary linearization back along the truncated
norm gives the upstairs stationary linearization for the actual norm-pullback
quasi-character. -/
theorem stationaryLinearizationCharacter_compNorm
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (hchi : chiK.character = chiF.character.compNorm) :
    (stationaryLinearizationCharacter F chiF
        (stationaryDepthOfConductorDecomposition F chiF
          h.targetDecomposition)).compAddMonoidHom
        (normPolynomial F K h) =
      stationaryLinearizationCharacter K chiK
        (stationaryDepthOfConductorDecomposition K chiK
          h.sourceDecomposition) := by
  apply AddChar.ext
  intro z
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective K
    (Int.ofNat_le.mpr
      h.sourceDecomposition.variableDepth_le_conductor) z
  rw [AddChar.compAddMonoidHom_apply, normPolynomial_mk,
    stationaryLinearizationCharacter_mk,
    stationaryLinearizationCharacter_mk, hchi,
    ContinuousQuasiChar.compNorm_apply]
  have hunit :
      (positiveUnitOfLattice F h.targetDecomposition.variableDepth_pos
          (normPolynomialRepresentative F K h y) : Fˣ) =
        Units.map (Algebra.norm F)
          (positiveUnitOfLattice K
            h.sourceDecomposition.variableDepth_pos y : Kˣ) := by
    apply Units.ext
    simp [normPolynomialRepresentative]
  rw [hunit]

/-- The denominator-sensitive adjoint image of the downstairs stationary
class satisfies the upstairs stationary linearization law at the actual
upstairs conductor and depth. -/
theorem normPolynomialAdjoint_stationaryClass_isStationary
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (hchi : chiK.character = chiF.character.compNorm)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)) :
    IsStationaryCoefficientClass K chiK psiK h.sourceDecomposition
      gammaK hgammaK
      (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK
        (stationaryCoefficientClass F chiF psiF h.targetDecomposition
          gammaF hgammaF)) := by
  rw [IsStationaryCoefficientClass,
    normPolynomialAdjoint_character]
  change
    (stationaryPairingLeft F h.targetDecomposition psiF gammaF hgammaF
      (stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF)).compAddMonoidHom (normPolynomial F K h) = _
  rw [stationaryCoefficientClass_isStationary]
  exact stationaryLinearizationCharacter_compNorm F K chiF chiK h hchi

/-! ## The stationary class under norm -/

/-- **Stationary numerator class under norm pullback.**

For the ordered denominator pair `(gammaF, gammaK)`, the stationary numerator
class of the actual upstairs character `chiK = chiF.compNorm` is the image of
the downstairs stationary class under the denominator-sensitive adjoint of
the truncated norm.  This is an equality in `𝒪_K / 𝓅_K^dK`, not an equality
of chosen field representatives.  The additive-character hypothesis records
the manuscript's normalization `psiK = psiF.compTrace`. -/
theorem stationaryClass_compNorm
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (hchi : chiK.character = chiF.character.compNorm)
    (_hpsi : psiK.character = psiF.character.compTrace)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)) :
    stationaryCoefficientClass K chiK psiK h.sourceDecomposition
        gammaK hgammaK =
      normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK
        (stationaryCoefficientClass F chiF psiF h.targetDecomposition
          gammaF hgammaF) := by
  symm
  exact stationaryCoefficientClass_unique K chiK psiK h.sourceDecomposition
    gammaK hgammaK _
    (normPolynomialAdjoint_stationaryClass_isStationary F K chiF chiK
      psiF psiK h hchi gammaF gammaK hgammaF hgammaK)

/-- Every supplied pair of downstairs and upstairs representatives of the
adjoint identity satisfies the upstairs stationary linearization.  The
representatives are hypotheses, not choices made by this theorem. -/
theorem stationaryClass_compNorm_representative_linearization
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : lattice F 0)
    (hc : latticeQuotientMk F (by omega) c =
      stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF)
    (b : lattice K 0)
    (hb : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega) b)
    (y : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    chiK.character
        (positiveUnitOfLattice K
          h.sourceDecomposition.variableDepth_pos y) =
      psiK.character ((b : K) * (y : K) / (gammaK : K)) := by
  have hbclass : latticeQuotientMk K (by omega) b =
      stationaryCoefficientClass K chiK psiK h.sourceDecomposition
        gammaK hgammaK := by
    calc
      _ = normPolynomialAdjoint F K h psiF psiK gammaF gammaK
            hgammaF hgammaK (latticeQuotientMk F (by omega) c) := hb.symm
      _ = normPolynomialAdjoint F K h psiF psiK gammaF gammaK
            hgammaF hgammaK
            (stationaryCoefficientClass F chiF psiF h.targetDecomposition
              gammaF hgammaF) := congrArg _ hc
      _ = stationaryCoefficientClass K chiK psiK h.sourceDecomposition
            gammaK hgammaK :=
        (stationaryClass_compNorm F K chiF chiK psiF psiK h hchi hpsi
          gammaF gammaK hgammaF hgammaK).symm
  exact (latticeQuotientMk_eq_stationaryCoefficientClass_iff K chiK psiK
    h.sourceDecomposition gammaK hgammaK b).1 hbclass y

/-- Changing either supplied coefficient representative leaves the resulting
upstairs class unchanged: any two supplied output representatives are
congruent at exactly the actual upstairs coefficient depth `dK`. -/
theorem stationaryClass_compNorm_representatives_independent
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c c' : lattice F 0)
    (hc : latticeQuotientMk F (by omega) c =
      stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF)
    (hc' : latticeQuotientMk F (by omega) c' =
      stationaryCoefficientClass F chiF psiF h.targetDecomposition
        gammaF hgammaF)
    (b b' : lattice K 0)
    (hb : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega) b)
    (hb' : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c') =
      latticeQuotientMk K (by omega) b') :
    CongruentAtDepth (dK : ℤ) (b : K) (b' : K) := by
  apply normPolynomialAdjoint_representatives_congruent F K h psiF psiK
    gammaF gammaK hgammaF hgammaK c c'
  · apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth F (by omega)).1
    rw [hc, hc']
  · exact hb
  · exact hb'

/-- Changing the variable representative modulo the actual upstairs
conductor changes neither side of the representative adjoint identity. -/
theorem stationaryClass_compNorm_variable_representative_independent
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : lattice F 0) (b : lattice K 0)
    (hb : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega) b)
    (y y' : lattice K ((dK + epsilonK : ℕ) : ℤ))
    (hyy' : CongruentAtDepth (chiK.conductor : ℤ) (y : K) (y' : K)) :
    psiF.character
        ((c : F) * (normPolynomialRepresentative F K h y : F) /
          (gammaF : F)) =
      psiF.character
        ((c : F) * (normPolynomialRepresentative F K h y' : F) /
          (gammaF : F)) ∧
    psiK.character ((b : K) * (y : K) / (gammaK : K)) =
      psiK.character ((b : K) * (y' : K) / (gammaK : K)) :=
  normPolynomialAdjoint_variable_representative_independent F K h psiF psiK
    gammaF gammaK hgammaF hgammaK c b hb y y' hyy'

/-! ## Denominator and endpoint compatibility -/

/-- Changing an admissible denominator scales the stationary coefficient
class by the exact new-to-old denominator ratio. -/
theorem stationaryCoefficientClass_changeDenominator
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    {d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition chi.conductor d epsilon)
    (gamma gamma' : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma' : ord E (gamma' : E) =
      (((chi.conductor : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    stationaryCoefficientClass E chi psi h gamma' hgamma' =
      stationaryCoefficientScale E d
        (denominatorChangeRatio E gamma gamma')
        (denominatorChangeRatio_ord_eq_zero E psi gamma gamma'
          hgamma hgamma')
        (stationaryCoefficientClass E chi psi h gamma hgamma) := by
  symm
  apply stationaryCoefficientClass_unique E chi psi h gamma' hgamma'
  rw [IsStationaryCoefficientClass]
  apply AddChar.ext
  intro y
  calc
    stationaryPairingLeft E h psi gamma' hgamma'
        (stationaryCoefficientScale E d
          (denominatorChangeRatio E gamma gamma')
          (denominatorChangeRatio_ord_eq_zero E psi gamma gamma'
            hgamma hgamma')
          (stationaryCoefficientClass E chi psi h gamma hgamma)) y =
      stationaryPairingLeft E h psi gamma hgamma
        (stationaryCoefficientClass E chi psi h gamma hgamma) y :=
      stationaryPairingLeft_changeDenominator E h psi gamma gamma'
        hgamma hgamma' _ y
    _ = stationaryLinearizationCharacter E chi
        (stationaryDepthOfConductorDecomposition E chi h) y :=
      congrArg (fun xi ↦ xi y)
        (stationaryCoefficientClass_isStationary E chi psi h gamma hgamma)

/-- The stationary pullback equality commutes with simultaneous admissible
changes of the ordered denominator pair. -/
theorem stationaryClass_compNorm_changeDenominator
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF)
    (gammaF gammaF' : Fˣ) (gammaK gammaK' : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaF' : ord F (gammaF' : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hgammaK' : ord K (gammaK' : K) =
      (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)) :
    normPolynomialAdjoint F K h psiF psiK gammaF' gammaK'
        hgammaF' hgammaK'
        (stationaryCoefficientClass F chiF psiF h.targetDecomposition
          gammaF' hgammaF') =
      stationaryCoefficientScale K dK
        (denominatorChangeRatio K gammaK gammaK')
        (denominatorChangeRatio_ord_eq_zero K psiK gammaK gammaK'
          hgammaK hgammaK')
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK
          (stationaryCoefficientClass F chiF psiF h.targetDecomposition
            gammaF hgammaF)) := by
  rw [stationaryCoefficientClass_changeDenominator F chiF psiF
    h.targetDecomposition gammaF gammaF' hgammaF hgammaF']
  exact normPolynomialAdjoint_changeDenominator F K h psiF psiK
    gammaF gammaF' gammaK gammaK' hgammaF hgammaF' hgammaK hgammaK'
    (stationaryCoefficientClass F chiF psiF h.targetDecomposition
      gammaF hgammaF)

omit [ValuativeExtension F K] [Module.Free F K] [Module.Finite F K] in
/-- The precision certificate records that both actual conductors lie outside
the conductor-zero and conductor-one endpoint regimes. -/
theorem stationaryClass_compNorm_conductors_gt_one
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    {dK epsilonK dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K chiK.conductor dK epsilonK
      chiF.conductor dF epsilonF) :
    1 < chiF.conductor ∧ 1 < chiK.conductor :=
  ⟨h.targetDecomposition.conductor_gt_one,
    h.sourceDecomposition.conductor_gt_one⟩

end
end LanglandsFirstMainLemma
