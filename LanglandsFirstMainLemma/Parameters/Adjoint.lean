import LanglandsFirstMainLemma.Parameters.NormPolynomial
import LanglandsFirstMainLemma.Lamprecht.FiniteDuality

/-!
# The denominator-sensitive adjoint of the stationary norm polynomial

For stationary decompositions `m = 2*d + epsilon`, finite duality pairs the
literal coefficient quotient `𝒪/𝓅^d` with the variable quotient
`𝓅^(d+epsilon)/𝓅^m`.  This file pulls a downstairs pairing character
back along `normPolynomial`, then uses the inverse upstairs perfect pairing to
construct the unique adjoint

`StationaryCoefficientQuotient F dF →+ StationaryCoefficientQuotient K dK`.

The construction retains both denominators.  Its representative lemmas only
evaluate quotient maps on supplied numerators.  The trace specialization is an
equality of quotient-valued maps, and the common-denominator conclusion is an
equality of quotient classes rather than a stronger equality in `K`.
-/

namespace LanglandsFirstMainLemma

noncomputable section

variable (F K : Type*)
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- The actual finite stationary coefficient quotient `𝒪_E/𝓅_E^d`. -/
abbrev StationaryCoefficientQuotient (E : Type*)
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (d : ℕ) :=
  LatticeQuotient E 0 (d : ℤ) (by omega)

private noncomputable def stationaryCoefficientToLamprecht
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

private noncomputable def stationaryCoefficientFromLamprecht
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

private noncomputable def stationaryCoefficientLamprechtEquiv
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon) :
    StationaryCoefficientQuotient E d ≃+
      LamprechtCoefficientQuotient E (m : ℤ) (m : ℤ)
        ((d + epsilon : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) where
  toFun := stationaryCoefficientToLamprecht E h
  invFun := stationaryCoefficientFromLamprecht E h
  left_inv z := by
    obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E (by omega) z
    rfl
  right_inv z := by
    obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E _ z
    rfl
  map_add' := map_add (stationaryCoefficientToLamprecht E h)

/-- Perfect finite duality on the literal stationary coefficient quotient.
The private transport uses `m - (d + epsilon) = d` and does not change
representatives or quotient depths silently. -/
noncomputable def stationaryPairingLeftEquiv
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    StationaryCoefficientQuotient E d ≃+
      AddChar
        (LamprechtVariableQuotient E (m : ℤ)
          ((d + epsilon : ℕ) : ℤ)
          (Int.ofNat_le.mpr h.variableDepth_le_conductor)) ℂ := by
  let coefficientEquiv : StationaryCoefficientQuotient E d ≃+
      LamprechtCoefficientQuotient E (m : ℤ) (m : ℤ)
        ((d + epsilon : ℕ) : ℤ)
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) :=
    stationaryCoefficientLamprechtEquiv E h
  exact coefficientEquiv.trans (lamprechtPairingLeftEquiv E psi
    (M := (m : ℤ)) (q := (m : ℤ))
    (r := ((d + epsilon : ℕ) : ℤ))
    (Int.ofNat_le.mpr h.variableDepth_le_conductor) gamma hgamma)

/-- The coefficient-to-character homomorphism underlying stationary perfect duality. -/
noncomputable def stationaryPairingLeft
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    StationaryCoefficientQuotient E d →+
      AddChar
        (LamprechtVariableQuotient E (m : ℤ)
          ((d + epsilon : ℕ) : ℤ)
          (Int.ofNat_le.mpr h.variableDepth_le_conductor)) ℂ :=
  (stationaryPairingLeftEquiv E h psi gamma hgamma).toAddMonoidHom

/-- Evaluation of the stationary pairing on two supplied numerator representatives. -/
@[simp] theorem stationaryPairingLeft_mk_mk
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice E 0) (x : lattice E ((d + epsilon : ℕ) : ℤ)) :
    stationaryPairingLeft E h psi gamma hgamma
        (latticeQuotientMk E (by omega) c)
        (latticeQuotientMk E
          (Int.ofNat_le.mpr h.variableDepth_le_conductor) x) =
      (psi.character ((c : E) * (x : E) / (gamma : E)) : ℂ) := by
  rfl

/-- Pull the downstairs coefficient character back along the truncated norm. -/
noncomputable def normPolynomialPullbackCharacter
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ)) :
    StationaryCoefficientQuotient F dF →+
      AddChar
        (LamprechtVariableQuotient K (mK : ℤ)
          ((dK + epsilonK : ℕ) : ℤ)
          (Int.ofNat_le.mpr
            h.sourceDecomposition.variableDepth_le_conductor)) ℂ where
  toFun c :=
    (stationaryPairingLeft F h.targetDecomposition psiF gammaF hgammaF c).compAddMonoidHom
      (normPolynomial F K h)
  map_zero' := by
    apply AddChar.ext
    intro y
    simp only [AddChar.compAddMonoidHom_apply, map_zero, AddChar.zero_apply]
  map_add' := by
    intro c c'
    apply AddChar.ext
    intro y
    simp only [AddChar.compAddMonoidHom_apply, map_add, AddChar.add_apply]

/-- The denominator-sensitive adjoint of the stationary truncated norm. -/
noncomputable def normPolynomialAdjoint
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)) :
    StationaryCoefficientQuotient F dF →+
      StationaryCoefficientQuotient K dK :=
  (stationaryPairingLeftEquiv K h.sourceDecomposition
      psiK gammaK hgammaK).symm.toAddMonoidHom.comp
    (normPolynomialPullbackCharacter F K h psiF gammaF hgammaF)

/-- Applying perfect duality to the adjoint recovers the pulled-back character. -/
theorem normPolynomialAdjoint_character
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : StationaryCoefficientQuotient F dF) :
    stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK hgammaF hgammaK c) =
      normPolynomialPullbackCharacter F K h psiF gammaF hgammaF c := by
  exact (stationaryPairingLeftEquiv K h.sourceDecomposition
    psiK gammaK hgammaK).apply_symm_apply _

/-- The defining adjoint identity, with coefficient first and variable second. -/
theorem normPolynomialAdjoint_pairing
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : StationaryCoefficientQuotient F dF)
    (y : LamprechtVariableQuotient K (mK : ℤ)
      ((dK + epsilonK : ℕ) : ℤ)
      (Int.ofNat_le.mpr
        h.sourceDecomposition.variableDepth_le_conductor)) :
    stationaryPairingLeft F h.targetDecomposition psiF gammaF hgammaF c
        (normPolynomial F K h y) =
      stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK c) y := by
  have hchar := congrArg
    (fun chi : AddChar
      (LamprechtVariableQuotient K (mK : ℤ)
        ((dK + epsilonK : ℕ) : ℤ)
        (Int.ofNat_le.mpr
          h.sourceDecomposition.variableDepth_le_conductor)) ℂ ↦ chi y)
    (normPolynomialAdjoint_character F K h psiF psiK gammaF gammaK
      hgammaF hgammaK c)
  exact hchar.symm

/-- No other additive map satisfies the denominator-sensitive adjoint identity. -/
theorem normPolynomialAdjoint_unique
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (A : StationaryCoefficientQuotient F dF →+
      StationaryCoefficientQuotient K dK)
    (hA : ∀ c y,
      stationaryPairingLeft F h.targetDecomposition psiF gammaF hgammaF c
          (normPolynomial F K h y) =
        stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
          (A c) y) :
    A = normPolynomialAdjoint F K h psiF psiK gammaF gammaK
      hgammaF hgammaK := by
  apply AddMonoidHom.ext
  intro c
  apply (stationaryPairingLeftEquiv K h.sourceDecomposition
    psiK gammaK hgammaK).injective
  apply AddChar.ext
  intro y
  exact (hA c y).symm.trans
    (normPolynomialAdjoint_pairing F K h psiF psiK gammaF gammaK
      hgammaF hgammaK c y)

/-- Existence and uniqueness of the adjoint, obtained from upstairs perfect duality. -/
theorem normPolynomialAdjoint_existsUnique
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)) :
    ∃! A : StationaryCoefficientQuotient F dF →+
        StationaryCoefficientQuotient K dK,
      ∀ c y,
        stationaryPairingLeft F h.targetDecomposition psiF gammaF hgammaF c
            (normPolynomial F K h y) =
          stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
            (A c) y := by
  refine ⟨normPolynomialAdjoint F K h psiF psiK gammaF gammaK
      hgammaF hgammaK, ?_, ?_⟩
  · exact normPolynomialAdjoint_pairing F K h psiF psiK gammaF gammaK
      hgammaF hgammaK
  · intro A hA
    exact normPolynomialAdjoint_unique F K h psiF psiK gammaF gammaK
      hgammaF hgammaK A hA

/-- The pairing is unchanged when its coefficient numerator changes modulo `𝓅^d`. -/
theorem stationaryPairingLeft_coefficient_representative_independent
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c c' : lattice E 0)
    (hcc' : CongruentAtDepth (d : ℤ) (c : E) (c' : E))
    (y : lattice E ((d + epsilon : ℕ) : ℤ)) :
    psi.character ((c : E) * (y : E) / (gamma : E)) =
      psi.character ((c' : E) * (y : E) / (gamma : E)) := by
  let hd : (0 : ℤ) ≤ (d : ℤ) := by omega
  have hmk : (latticeQuotientMk E hd c :
        StationaryCoefficientQuotient E d) =
      latticeQuotientMk E hd c' :=
    (latticeQuotientMk_eq_mk_iff_congruentAtDepth E hd).2 hcc'
  have heval := congrArg
    (fun z : StationaryCoefficientQuotient E d ↦
      stationaryPairingLeft E h psi gamma hgamma z
        (latticeQuotientMk E
          (Int.ofNat_le.mpr h.variableDepth_le_conductor) y)) hmk
  apply Units.ext
  exact heval

/-- The pairing is unchanged when its variable numerator changes modulo `𝓅^m`. -/
theorem stationaryPairingLeft_variable_representative_independent
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : lattice E 0)
    (y y' : lattice E ((d + epsilon : ℕ) : ℤ))
    (hyy' : CongruentAtDepth (m : ℤ) (y : E) (y' : E)) :
    psi.character ((c : E) * (y : E) / (gamma : E)) =
      psi.character ((c : E) * (y' : E) / (gamma : E)) := by
  have hmk : latticeQuotientMk E
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) y =
      latticeQuotientMk E
        (Int.ofNat_le.mpr h.variableDepth_le_conductor) y' :=
    (latticeQuotientMk_eq_mk_iff_congruentAtDepth E
      (Int.ofNat_le.mpr h.variableDepth_le_conductor)).2 hyy'
  have heval := congrArg
    (fun z : LamprechtVariableQuotient E (m : ℤ)
      ((d + epsilon : ℕ) : ℤ)
      (Int.ofNat_le.mpr h.variableDepth_le_conductor) ↦
        stationaryPairingLeft E h psi gamma hgamma
          (latticeQuotientMk E (by omega) c) z) hmk
  apply Units.ext
  exact heval

/-- Representative form of the adjoint identity, conditional on a supplied
representative of the output class. -/
theorem normPolynomialAdjoint_pairing_mk
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : lattice F 0) (b : lattice K 0)
    (hb : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega) b)
    (y : lattice K ((dK + epsilonK : ℕ) : ℤ)) :
    psiF.character
        ((c : F) * (normPolynomialRepresentative F K h y : F) /
          (gammaF : F)) =
      psiK.character ((b : K) * (y : K) / (gammaK : K)) := by
  have hpair := normPolynomialAdjoint_pairing F K h psiF psiK
    gammaF gammaK hgammaF hgammaK
    (latticeQuotientMk F (by omega) c)
    (latticeQuotientMk K
      (Int.ofNat_le.mpr
        h.sourceDecomposition.variableDepth_le_conductor) y)
  rw [normPolynomial_mk, stationaryPairingLeft_mk_mk, hb,
    stationaryPairingLeft_mk_mk] at hpair
  apply Units.ext
  exact hpair

/-- Congruent downstairs coefficient numerators have the same adjoint class. -/
theorem normPolynomialAdjoint_input_representative_independent
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c c' : lattice F 0)
    (hcc' : CongruentAtDepth (dF : ℤ) (c : F) (c' : F)) :
    normPolynomialAdjoint F K h psiF psiK gammaF gammaK hgammaF hgammaK
        (latticeQuotientMk F (by omega) c) =
      normPolynomialAdjoint F K h psiF psiK gammaF gammaK hgammaF hgammaK
        (latticeQuotientMk F (by omega) c') := by
  apply congrArg (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
    hgammaF hgammaK)
  exact (latticeQuotientMk_eq_mk_iff_congruentAtDepth F (by omega)).2 hcc'

/-- Any supplied representatives of adjoint images of equal downstairs classes
are congruent at exactly the upstairs stationary coefficient depth. -/
theorem normPolynomialAdjoint_representatives_congruent
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c c' : lattice F 0)
    (hcc' : CongruentAtDepth (dF : ℤ) (c : F) (c' : F))
    (b b' : lattice K 0)
    (hb : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega) b)
    (hb' : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c') =
      latticeQuotientMk K (by omega) b') :
    CongruentAtDepth (dK : ℤ) (b : K) (b' : K) := by
  apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth K (by omega)).1
  rw [← hb, ← hb']
  exact normPolynomialAdjoint_input_representative_independent F K h
    psiF psiK gammaF gammaK hgammaF hgammaK c c' hcc'

/-- Both representative-level phases are invariant under changing the upstairs
variable numerator modulo its conductor depth. -/
theorem normPolynomialAdjoint_variable_representative_independent
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : lattice F 0) (b : lattice K 0)
    (hb : normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega) b)
    (y y' : lattice K ((dK + epsilonK : ℕ) : ℤ))
    (hyy' : CongruentAtDepth (mK : ℤ) (y : K) (y' : K)) :
    psiF.character
        ((c : F) * (normPolynomialRepresentative F K h y : F) /
          (gammaF : F)) =
      psiF.character
        ((c : F) * (normPolynomialRepresentative F K h y' : F) /
          (gammaF : F)) ∧
    psiK.character ((b : K) * (y : K) / (gammaK : K)) =
      psiK.character ((b : K) * (y' : K) / (gammaK : K)) := by
  have hright := stationaryPairingLeft_variable_representative_independent
    K h.sourceDecomposition psiK gammaK hgammaK b y y' hyy'
  refine ⟨?_, hright⟩
  exact (normPolynomialAdjoint_pairing_mk F K h psiF psiK gammaF gammaK
    hgammaF hgammaK c b hb y).trans
      (hright.trans (normPolynomialAdjoint_pairing_mk F K h psiF psiK
        gammaF gammaK hgammaF hgammaK c b hb y').symm)

/-! ## Change of denominator -/

/-- Ratio from an old denominator to a new denominator. -/
def denominatorChangeRatio
    (E : Type*) [Field E] (gamma gamma' : Eˣ) : E :=
  (gamma' : E) / (gamma : E)

/-- A change-of-denominator ratio is nonzero. -/
theorem denominatorChangeRatio_ne_zero
    (E : Type*) [Field E] (gamma gamma' : Eˣ) :
    denominatorChangeRatio E gamma gamma' ≠ 0 := by
  exact div_ne_zero (Units.ne_zero gamma') (Units.ne_zero gamma)

/-- Two admissible denominators for the same conductor differ by a depth-zero scalar. -/
theorem denominatorChangeRatio_ord_eq_zero
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m : ℕ} (psi : LocalAddCharData E) (gamma gamma' : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma' : ord E (gamma' : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ)) :
    ord E (denominatorChangeRatio E gamma gamma') = 0 := by
  simpa [denominatorChangeRatio, ord_div, hgamma', hgamma]

/-- Multiplication of a supplied integral coefficient by a depth-zero scalar. -/
noncomputable def stationaryCoefficientScaledRepresentative
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (a : E) (ha : ord E a = 0) (c : lattice E 0) : lattice E 0 := by
  refine ⟨a * (c : E), ?_⟩
  rw [mem_lattice, ord_mul, ha, zero_add]
  exact c.property

/-- Scaling on the honest coefficient quotient; no representative is selected. -/
noncomputable def stationaryCoefficientScale
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (d : ℕ) (a : E) (ha : ord E a = 0) :
    StationaryCoefficientQuotient E d →+
      StationaryCoefficientQuotient E d where
  toFun := latticeQuotientLift E (by omega)
    (fun c ↦ latticeQuotientMk E (by omega)
      (stationaryCoefficientScaledRepresentative E a ha c))
    (fun c c' hcc' ↦ by
      apply (latticeQuotientMk_eq_mk_iff_congruentAtDepth E (by omega)).2
      rw [CongruentAtDepth]
      change (((d : ℕ) : ℤ) : WithTop ℤ) ≤
        ord E (a * (c : E) - a * (c' : E))
      rw [← mul_sub, ord_mul, ha, zero_add]
      exact hcc')
  map_zero' := by
    change latticeQuotientLift E (by omega) _ _
      (latticeQuotientMk E (by omega) 0) = 0
    rw [latticeQuotientLift_mk]
    apply (latticeQuotientMk_eq_zero_iff E (by omega)).2
    simp [stationaryCoefficientScaledRepresentative]
  map_add' := by
    intro c c'
    obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E (by omega) c
    obtain ⟨c', rfl⟩ := latticeQuotientMk_surjective E (by omega) c'
    rw [← latticeQuotientMk_add, latticeQuotientLift_mk,
      latticeQuotientLift_mk, latticeQuotientLift_mk,
      ← latticeQuotientMk_add]
    congr 1
    apply Subtype.ext
    simp [stationaryCoefficientScaledRepresentative, mul_add]

@[simp]
theorem stationaryCoefficientScale_mk
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (d : ℕ) (a : E) (ha : ord E a = 0) (c : lattice E 0) :
    stationaryCoefficientScale E d a ha
        (latticeQuotientMk E (by omega) c) =
      latticeQuotientMk E (by omega)
        (stationaryCoefficientScaledRepresentative E a ha c) :=
  rfl

/-- Depth-zero coefficient scaling respects congruence modulo the coefficient depth. -/
theorem stationaryCoefficientScale_representative_independent
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (d : ℕ) (a : E) (ha : ord E a = 0)
    (c c' : lattice E 0)
    (hcc' : CongruentAtDepth (d : ℤ) (c : E) (c' : E)) :
    CongruentAtDepth (d : ℤ)
      (stationaryCoefficientScaledRepresentative E a ha c : E)
      (stationaryCoefficientScaledRepresentative E a ha c' : E) := by
  rw [CongruentAtDepth]
  change (((d : ℕ) : ℤ) : WithTop ℤ) ≤
    ord E (a * (c : E) - a * (c' : E))
  rw [← mul_sub, ord_mul, ha, zero_add]
  exact hcc'

/-- Scaling a coefficient by `gamma' / gamma` transports the `gamma` pairing
to the `gamma'` pairing. -/
theorem stationaryPairingLeft_changeDenominator
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {m d epsilon : ℕ}
    (h : IsStationaryConductorDecomposition m d epsilon)
    (psi : LocalAddCharData E) (gamma gamma' : Eˣ)
    (hgamma : ord E (gamma : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (hgamma' : ord E (gamma' : E) =
      (((m : ℤ) + psi.conductor : ℤ) : WithTop ℤ))
    (c : StationaryCoefficientQuotient E d)
    (y : LamprechtVariableQuotient E (m : ℤ)
      ((d + epsilon : ℕ) : ℤ)
      (Int.ofNat_le.mpr h.variableDepth_le_conductor)) :
    stationaryPairingLeft E h psi gamma' hgamma'
        (stationaryCoefficientScale E d
          (denominatorChangeRatio E gamma gamma')
          (denominatorChangeRatio_ord_eq_zero E psi gamma gamma'
            hgamma hgamma') c) y =
      stationaryPairingLeft E h psi gamma hgamma c y := by
  obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective E (by omega) c
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective E
    (Int.ofNat_le.mpr h.variableDepth_le_conductor) y
  rw [stationaryCoefficientScale_mk,
    stationaryPairingLeft_mk_mk, stationaryPairingLeft_mk_mk]
  congr 1
  dsimp [stationaryCoefficientScaledRepresentative, denominatorChangeRatio]
  field_simp [Units.ne_zero gamma, Units.ne_zero gamma']

/-- Pointwise compatibility of the adjoint with simultaneous denominator changes. -/
theorem normPolynomialAdjoint_changeDenominator
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF gammaF' : Fˣ) (gammaK gammaK' : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaF' : ord F (gammaF' : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hgammaK' : ord K (gammaK' : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (c : StationaryCoefficientQuotient F dF) :
    normPolynomialAdjoint F K h psiF psiK gammaF' gammaK'
        hgammaF' hgammaK'
        (stationaryCoefficientScale F dF
          (denominatorChangeRatio F gammaF gammaF')
          (denominatorChangeRatio_ord_eq_zero F psiF gammaF gammaF'
            hgammaF hgammaF') c) =
      stationaryCoefficientScale K dK
        (denominatorChangeRatio K gammaK gammaK')
        (denominatorChangeRatio_ord_eq_zero K psiK gammaK gammaK'
          hgammaK hgammaK')
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK c) := by
  apply (stationaryPairingLeftEquiv K h.sourceDecomposition
    psiK gammaK' hgammaK').injective
  apply AddChar.ext
  intro y
  change stationaryPairingLeft K h.sourceDecomposition psiK gammaK' hgammaK'
      (normPolynomialAdjoint F K h psiF psiK gammaF' gammaK'
        hgammaF' hgammaK'
        (stationaryCoefficientScale F dF
          (denominatorChangeRatio F gammaF gammaF')
          (denominatorChangeRatio_ord_eq_zero F psiF gammaF gammaF'
            hgammaF hgammaF') c)) y =
    stationaryPairingLeft K h.sourceDecomposition psiK gammaK' hgammaK'
      (stationaryCoefficientScale K dK
        (denominatorChangeRatio K gammaK gammaK')
        (denominatorChangeRatio_ord_eq_zero K psiK gammaK gammaK'
          hgammaK hgammaK')
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK c)) y
  calc
    _ = stationaryPairingLeft F h.targetDecomposition psiF gammaF' hgammaF'
        (stationaryCoefficientScale F dF
          (denominatorChangeRatio F gammaF gammaF')
          (denominatorChangeRatio_ord_eq_zero F psiF gammaF gammaF'
            hgammaF hgammaF') c) (normPolynomial F K h y) :=
      (normPolynomialAdjoint_pairing F K h psiF psiK gammaF' gammaK'
        hgammaF' hgammaK' _ y).symm
    _ = stationaryPairingLeft F h.targetDecomposition psiF gammaF hgammaF c
        (normPolynomial F K h y) :=
      stationaryPairingLeft_changeDenominator F h.targetDecomposition
        psiF gammaF gammaF' hgammaF hgammaF' c _
    _ = stationaryPairingLeft K h.sourceDecomposition psiK gammaK hgammaK
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK c) y :=
      normPolynomialAdjoint_pairing F K h psiF psiK gammaF gammaK
        hgammaF hgammaK c y
    _ = stationaryPairingLeft K h.sourceDecomposition psiK gammaK' hgammaK'
        (stationaryCoefficientScale K dK
          (denominatorChangeRatio K gammaK gammaK')
          (denominatorChangeRatio_ord_eq_zero K psiK gammaK gammaK'
            hgammaK hgammaK')
          (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
            hgammaF hgammaK c)) y :=
      (stationaryPairingLeft_changeDenominator K h.sourceDecomposition
        psiK gammaK gammaK' hgammaK hgammaK' _ y).symm

/-- Homomorphism-level denominator-change square for the adjoint. -/
theorem normPolynomialAdjoint_changeDenominator_hom
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (gammaF gammaF' : Fˣ) (gammaK gammaK' : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaF' : ord F (gammaF' : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hgammaK' : ord K (gammaK' : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ)) :
    (normPolynomialAdjoint F K h psiF psiK gammaF' gammaK'
        hgammaF' hgammaK').comp
        (stationaryCoefficientScale F dF
          (denominatorChangeRatio F gammaF gammaF')
          (denominatorChangeRatio_ord_eq_zero F psiF gammaF gammaF'
            hgammaF hgammaF')) =
      (stationaryCoefficientScale K dK
        (denominatorChangeRatio K gammaK gammaK')
        (denominatorChangeRatio_ord_eq_zero K psiK gammaK gammaK'
          hgammaK hgammaK')).comp
        (normPolynomialAdjoint F K h psiF psiK gammaF gammaK
          hgammaF hgammaK) := by
  apply AddMonoidHom.ext
  intro c
  exact normPolynomialAdjoint_changeDenominator F K h psiF psiK
    gammaF gammaF' gammaK gammaK' hgammaF hgammaF' hgammaK hgammaK' c

/-! ## Trace specialization -/

/-- If the truncated norm is trace at the required quotient precision and
`psiK = psiF ∘ trace`, its adjoint is multiplication by the exact denominator
ratio followed by base-field inclusion. -/
theorem normPolynomialAdjoint_eq_denominatorScaledAlgebraMap
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K mK mF)
    (htrace : normPolynomial F K h =
      normPolynomialTrace F K h hvariable hconductor)
    (hdepth : dK ≤ ramificationIndex F K * dF)
    (hratio : ord K
      (normPolynomialDenominatorRatio F K gammaF gammaK) = 0) :
    normPolynomialAdjoint F K h psiF psiK gammaF gammaK
        hgammaF hgammaK =
      denominatorScaledAlgebraMap F K dF dK hdepth gammaF gammaK hratio := by
  symm
  apply normPolynomialAdjoint_unique F K h psiF psiK gammaF gammaK
    hgammaF hgammaK
  intro c y
  obtain ⟨c, rfl⟩ := latticeQuotientMk_surjective F (by omega) c
  obtain ⟨y, rfl⟩ := latticeQuotientMk_surjective K
    (Int.ofNat_le.mpr
      h.sourceDecomposition.variableDepth_le_conductor) y
  rw [htrace, normPolynomialTrace_mk, denominatorScaledAlgebraMap_mk,
    stationaryPairingLeft_mk_mk, stationaryPairingLeft_mk_mk]
  rw [hpsi, ContinuousAddChar.compTrace_apply]
  dsimp [denominatorScaledRepresentative]
  rw [trace_denominatorScaled_div]

/-- Quotient-class form of the trace/denominator-ratio specialization on a
supplied downstairs numerator. -/
theorem normPolynomialAdjoint_trace_denominatorRatio_mk
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    (gammaF : Fˣ) (gammaK : Kˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K (gammaK : K) =
      (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K mK mF)
    (htrace : normPolynomial F K h =
      normPolynomialTrace F K h hvariable hconductor)
    (hdepth : dK ≤ ramificationIndex F K * dF)
    (hratio : ord K
      (normPolynomialDenominatorRatio F K gammaF gammaK) = 0)
    (c : lattice F 0) :
    normPolynomialAdjoint F K h psiF psiK gammaF gammaK hgammaF hgammaK
        (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega)
        (denominatorScaledRepresentative F K gammaF gammaK hratio c) := by
  rw [normPolynomialAdjoint_eq_denominatorScaledAlgebraMap F K h psiF psiK
    hpsi gammaF gammaK hgammaF hgammaK hvariable hconductor htrace
    hdepth hratio, denominatorScaledAlgebraMap_mk]

private theorem commonDenominatorRatio_ord_eq_zero
    (gammaF : Fˣ) :
    ord K (normPolynomialDenominatorRatio F K gammaF
      (Units.map (algebraMap F K) gammaF)) = 0 := by
  simp [normPolynomialDenominatorRatio]

set_option maxHeartbeats 800000 in
/-- With a common denominator, every supplied downstairs numerator maps to
the class of its natural image in `K`; no representative equality is asserted. -/
theorem normPolynomialAdjoint_commonDenominator_mk
    {mK dK epsilonK mF dF epsilonF : ℕ}
    (h : NormPolynomialPrecision F K mK dK epsilonK mF dF epsilonF)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    (hpsi : psiK.character = psiF.character.compTrace)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((mF : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (hgammaK : ord K
      ((Units.map (algebraMap F K) gammaF : Kˣ) : K) =
        (((mK : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
    (hvariable :
      TraceLatticeInclusion F K (dK + epsilonK) (dF + epsilonF))
    (hconductor : TraceLatticeInclusion F K mK mF)
    (htrace : normPolynomial F K h =
      normPolynomialTrace F K h hvariable hconductor)
    (hdepth : dK ≤ ramificationIndex F K * dF)
    (c : lattice F 0) :
    normPolynomialAdjoint F K h psiF psiK gammaF
        (Units.map (algebraMap F K) gammaF) hgammaF hgammaK
        (latticeQuotientMk F (by omega) c) =
      latticeQuotientMk K (by omega)
        ⟨algebraMap F K (c : F), by
          rw [mem_lattice, ord_algebraMap]
          have hc := c.property
          rw [mem_lattice] at hc
          simpa using nsmul_le_nsmul_right hc (ramificationIndex F K)⟩ := by
  rw [normPolynomialAdjoint_trace_denominatorRatio_mk F K h psiF psiK
    hpsi gammaF (Units.map (algebraMap F K) gammaF) hgammaF hgammaK
    hvariable hconductor htrace hdepth
    (commonDenominatorRatio_ord_eq_zero F K gammaF)]
  congr 1
  apply Subtype.ext
  simp [denominatorScaledRepresentative, normPolynomialDenominatorRatio]

end
end LanglandsFirstMainLemma
