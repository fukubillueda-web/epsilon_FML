import LanglandsFirstMainLemma.Parameters.PhaseReduction

/-!
# Wild odd lower residual coefficient rows

This file extracts coefficient pairs from the complete source-tied
Lamprecht functions constructed in `Parameters.PhaseReduction`.  It never
chooses a new residual coordinate.  The clean manuscript rows use the
literal natural-multiple representatives; the actual Teichmuller rows are
kept separate and carry their exact representative-translation terms.

The last section records the corrected norm-row/twist-row ratio.  Before a
character is applied the inverse norm factor is present.  The manuscript
`z_j` identity is stated only after applying the indexed norm character.
-/

namespace LanglandsFirstMainLemma

noncomputable section

universe u

/-! ## Coefficient-pair calculus for complete critical functions -/

/-- The positive polar and affine coefficients of one residual critical
function, in that order. -/
structure WildOddCoefficientPair (k : Type*) where
  polar : k
  affine : k
  deriving DecidableEq

@[ext]
theorem WildOddCoefficientPair.ext {k : Type*}
    {P Q : WildOddCoefficientPair k}
    (hpolar : P.polar = Q.polar) (haffine : P.affine = Q.affine) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Extract both coefficients from the same actual Lamprecht package. -/
noncomputable def wildOddCoefficientPair
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    WildOddCoefficientPair (ResidueField E) :=
  ⟨D.polarCoefficient psi0 hpsi0,
    D.affineCoefficient psi0 hpsi0 hchar⟩

@[simp]
theorem wildOddCoefficientPair_polar
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    (wildOddCoefficientPair D psi0 hpsi0 hchar).polar =
      D.polarCoefficient psi0 hpsi0 :=
  rfl

@[simp]
theorem wildOddCoefficientPair_affine
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    (wildOddCoefficientPair D psi0 hpsi0 hchar).affine =
      D.affineCoefficient psi0 hpsi0 hchar :=
  rfl

/-- A complete critical function determines both its polar and affine
coefficients. -/
private theorem criticalFunction_coefficients_eq_of_function_eq
    {k : Type u} [Field k] [Fintype k]
    {psi0 : FiniteAddChar k} (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar k ≠ 2)
    {A₁ A₂ : k}
    (phi₁ : CriticalPolarFunction k psi0 A₁)
    (phi₂ : CriticalPolarFunction k psi0 A₂)
    (hfun : ∀ x, phi₁ x = phi₂ x) :
    A₁ = A₂ ∧
      phi₁.affineCoefficient hchar hpsi0 =
        phi₂.affineCoefficient hchar hpsi0 := by
  have hpolar : A₁ = A₂ := by
    apply AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hpsi0)
    apply AddChar.ext
    intro z
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply]
    have h₁ := phi₁.map_add 1 z
    have h₂ := phi₂.map_add 1 z
    rw [hfun, hfun, hfun] at h₁
    have hcommon : phi₂ 1 * phi₂ z ≠ 0 :=
      mul_ne_zero (phi₂.ne_zero 1) (phi₂.ne_zero z)
    apply mul_left_cancel₀ hcommon
    simpa using h₁.symm.trans h₂
  subst A₂
  refine ⟨rfl, ?_⟩
  have heq : phi₁ = phi₂ := CriticalPolarFunction.ext _ _ hfun
  subst phi₂
  rfl

/-- Raise a complete polar function to a natural power without forgetting
the induced scaling of its polar coefficient. -/
private noncomputable def CriticalPolarFunction.wildOddNatPow
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A : k}
    (phi : CriticalPolarFunction k psi0 A) (q : ℕ) :
    CriticalPolarFunction k psi0 ((q : k) * A) where
  toFun x := phi x ^ q
  ne_zero' x := pow_ne_zero _ (phi.ne_zero x)
  map_add' x y := by
    rw [phi.map_add, mul_pow, mul_pow]
    congr 1
    calc
      psi0 (A * (x * y)) ^ q = psi0 (q • (A * (x * y))) :=
        (AddChar.map_nsmul_eq_pow psi0 q _).symm
      _ = psi0 ((q : k) * A * (x * y)) := by
        congr 1
        simp only [nsmul_eq_mul]
        ring

/-- Multiply complete polar functions without discarding either affine
term. -/
private noncomputable def CriticalPolarFunction.wildOddMul
    {k : Type u} [Field k] {psi0 : FiniteAddChar k} {A₁ A₂ : k}
    (phi₁ : CriticalPolarFunction k psi0 A₁)
    (phi₂ : CriticalPolarFunction k psi0 A₂) :
    CriticalPolarFunction k psi0 (A₁ + A₂) where
  toFun x := phi₁ x * phi₂ x
  ne_zero' x := mul_ne_zero (phi₁.ne_zero x) (phi₂.ne_zero x)
  map_add' x y := by
    rw [phi₁.map_add, phi₂.map_add]
    calc
      phi₁ x * phi₁ y * psi0 (A₁ * (x * y)) *
          (phi₂ x * phi₂ y * psi0 (A₂ * (x * y))) =
        (phi₁ x * phi₂ x) * (phi₁ y * phi₂ y) *
          (psi0 (A₁ * (x * y)) * psi0 (A₂ * (x * y))) := by
            ring
      _ = (phi₁ x * phi₂ x) * (phi₁ y * phi₂ y) *
          psi0 ((A₁ + A₂) * (x * y)) := by
        rw [← psi0.map_add_eq_mul]
        congr 2
        ring

/-- Equality of complete functions gives equality of both extracted
coefficients. -/
theorem wildOddCoefficientPair_eq_of_function_eq
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi₁ chi₂ : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D₁ : LocalLamprechtPhaseData E chi₁ psi)
    (D₂ : LocalLamprechtPhaseData E chi₂ psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (hfun : ∀ x, D₁.criticalFunction x = D₂.criticalFunction x) :
    wildOddCoefficientPair D₁ psi0 hpsi0 hchar =
      wildOddCoefficientPair D₂ psi0 hpsi0 hchar := by
  letI := residueFieldFintype E
  have hpair := criticalFunction_coefficients_eq_of_function_eq hpsi0 hchar
    (D₁.toCriticalPolarFunction psi0 hpsi0)
    (D₂.toCriticalPolarFunction psi0 hpsi0) (by
      intro x
      simpa only [LocalLamprechtPhaseData.toCriticalPolarFunction_apply]
        using hfun x)
  exact WildOddCoefficientPair.ext hpair.1 hpair.2

/-- Pointwise natural powers scale both coefficients by the corresponding
prime-field scalar. -/
theorem wildOddCoefficientPair_eq_nsmul_of_function_eq_pow
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi₁ chi₂ : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D₁ : LocalLamprechtPhaseData E chi₁ psi)
    (D₂ : LocalLamprechtPhaseData E chi₂ psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (q : ℕ)
    (hfun : ∀ x, D₁.criticalFunction x = D₂.criticalFunction x ^ q) :
    wildOddCoefficientPair D₁ psi0 hpsi0 hchar =
      ⟨(q : ResidueField E) * D₂.polarCoefficient psi0 hpsi0,
        (q : ResidueField E) *
          D₂.affineCoefficient psi0 hpsi0 hchar⟩ := by
  letI := residueFieldFintype E
  have hpair := criticalFunction_coefficients_eq_of_function_eq hpsi0 hchar
    (D₁.toCriticalPolarFunction psi0 hpsi0)
    ((D₂.toCriticalPolarFunction psi0 hpsi0).wildOddNatPow q) (by
      intro x
      change (D₁.toCriticalPolarFunction psi0 hpsi0) x =
        (D₂.toCriticalPolarFunction psi0 hpsi0 x) ^ q
      simp only [LocalLamprechtPhaseData.toCriticalPolarFunction_apply]
      exact hfun x)
  apply WildOddCoefficientPair.ext
  · exact hpair.1
  · change (D₁.toCriticalPolarFunction psi0 hpsi0).affineCoefficient
        hchar hpsi0 = _
    rw [hpair.2]
    apply CriticalPolarFunction.affineCoefficient_unique
    intro x
    change (D₂.toCriticalPolarFunction psi0 hpsi0 x) ^ q = _
    rw [(D₂.toCriticalPolarFunction psi0 hpsi0).eq_quadratic hchar hpsi0]
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp only [nsmul_eq_mul]
    unfold LocalLamprechtPhaseData.affineCoefficient
    ring

/-- Pointwise products add both coefficient rows. -/
theorem wildOddCoefficientPair_eq_add_of_function_eq_mul
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chi₁ chi₂ : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (D₁ : LocalLamprechtPhaseData E chi₁ psi)
    (D₂ : LocalLamprechtPhaseData E chi₂ psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (hfun : ∀ x,
      D.criticalFunction x = D₁.criticalFunction x * D₂.criticalFunction x) :
    wildOddCoefficientPair D psi0 hpsi0 hchar =
      ⟨D₁.polarCoefficient psi0 hpsi0 +
          D₂.polarCoefficient psi0 hpsi0,
        D₁.affineCoefficient psi0 hpsi0 hchar +
          D₂.affineCoefficient psi0 hpsi0 hchar⟩ := by
  letI := residueFieldFintype E
  have hpair := criticalFunction_coefficients_eq_of_function_eq hpsi0 hchar
    (D.toCriticalPolarFunction psi0 hpsi0)
    ((D₁.toCriticalPolarFunction psi0 hpsi0).wildOddMul
      (D₂.toCriticalPolarFunction psi0 hpsi0)) (by
        intro x
        change (D.toCriticalPolarFunction psi0 hpsi0) x =
          (D₁.toCriticalPolarFunction psi0 hpsi0) x *
            (D₂.toCriticalPolarFunction psi0 hpsi0) x
        simp only [LocalLamprechtPhaseData.toCriticalPolarFunction_apply]
        exact hfun x)
  apply WildOddCoefficientPair.ext
  · exact hpair.1
  · change (D.toCriticalPolarFunction psi0 hpsi0).affineCoefficient
        hchar hpsi0 = _
    rw [hpair.2]
    apply CriticalPolarFunction.affineCoefficient_unique
    intro x
    change D₁.toCriticalPolarFunction psi0 hpsi0 x *
        D₂.toCriticalPolarFunction psi0 hpsi0 x = _
    rw [(D₁.toCriticalPolarFunction psi0 hpsi0).eq_quadratic hchar hpsi0,
      (D₂.toCriticalPolarFunction psi0 hpsi0).eq_quadratic hchar hpsi0,
      ← psi0.map_add_eq_mul]
    congr 1
    unfold LocalLamprechtPhaseData.affineCoefficient
    ring

/-- A literal constant-one complete function has the even-conductor pair
`(0,0)`. -/
theorem wildOddCoefficientPair_eq_zero_of_function_eq_one
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (hfun : ∀ x, D.criticalFunction x = 1) :
    wildOddCoefficientPair D psi0 hpsi0 hchar = ⟨0, 0⟩ := by
  letI := residueFieldFintype E
  let oneFunction : CriticalPolarFunction (ResidueField E) psi0 0 :=
    { toFun := fun _ ↦ 1
      ne_zero' := fun _ ↦ one_ne_zero
      map_add' := by simp }
  have hpair := criticalFunction_coefficients_eq_of_function_eq hpsi0 hchar
    (D.toCriticalPolarFunction psi0 hpsi0) oneFunction (by
      intro x
      change (D.toCriticalPolarFunction psi0 hpsi0) x = 1
      simp only [LocalLamprechtPhaseData.toCriticalPolarFunction_apply]
      exact hfun x)
  apply WildOddCoefficientPair.ext hpair.1
  change (D.toCriticalPolarFunction psi0 hpsi0).affineCoefficient
      hchar hpsi0 = 0
  rw [hpair.2]
  apply CriticalPolarFunction.affineCoefficient_unique
  intro x
  change (1 : ℂ) = psi0 (0 / 2 * x ^ 2 + 0 * x)
  simp

/-- In the odd branch the polar coefficient is nonzero.  This is proved
before any slope or quotient coefficient is formed. -/
theorem LocalLamprechtPhaseData.polarCoefficient_ne_zero_of_odd
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hodd : Odd chi.conductor) :
    D.polarCoefficient psi0 hpsi0 ≠ 0 := by
  letI := residueFieldFintype E
  cases D with
  | even d hm hlarge Gamma c hc =>
      obtain ⟨e, he⟩ := hodd
      omega
  | odd d hm hlarge Gamma delta hdelta c hc =>
      exact finiteAddCharCoefficient_ne_zero psi0 hpsi0 _
        (lamprechtResidualAddChar_ne_one E chi psi d hm hlarge Gamma delta
          hdelta c hc)

/-! ## Manuscript normalization of a nonzero coefficient pair -/

/-- The manuscript writes a nonzero row `(A,B)` as `(eta,eta*gamma)`.
The nonvanishing proof is a field of the structure, so `gamma` is formed
only after its denominator has been certified. -/
structure WildOddNamedCoefficientPair (k : Type*) [Field k] where
  eta : k
  eta_ne_zero : eta ≠ 0
  gamma : k

namespace WildOddNamedCoefficientPair

/-- Normalize an already extracted pair. -/
noncomputable def ofPair {k : Type*} [Field k]
    (P : WildOddCoefficientPair k) (hpolar : P.polar ≠ 0) :
    WildOddNamedCoefficientPair k where
  eta := P.polar
  eta_ne_zero := hpolar
  gamma := P.affine / P.polar

theorem pair_eq {k : Type*} [Field k]
    (P : WildOddCoefficientPair k) (hpolar : P.polar ≠ 0) :
    P = ⟨(ofPair P hpolar).eta,
      (ofPair P hpolar).eta * (ofPair P hpolar).gamma⟩ := by
  apply WildOddCoefficientPair.ext
  · rfl
  · dsimp only [ofPair]
    field_simp

end WildOddNamedCoefficientPair

/-- The literal `j`th norm-character row in the manuscript normalization. -/
def wildOddTauPowerPair {k : Type*} [Field k]
    (P : WildOddNamedCoefficientPair k) (j : k) :
    WildOddCoefficientPair k :=
  ⟨j * P.eta, j * P.eta * P.gamma⟩

/-- The identity/base row in the manuscript normalization. -/
def wildOddBasePair {k : Type*} [Field k]
    (P : WildOddNamedCoefficientPair k) : WildOddCoefficientPair k :=
  ⟨P.eta, P.eta * P.gamma⟩

/-- At the boundary, `dZero` is the exact ratio of the base polar
coefficient to the norm-generator polar coefficient. -/
noncomputable def wildOddBoundaryDZero {k : Type*} [Field k]
    (tau base : WildOddNamedCoefficientPair k) : k :=
  base.eta / tau.eta

theorem wildOddBoundary_eta_eq {k : Type*} [Field k]
    (tau base : WildOddNamedCoefficientPair k) :
    base.eta = tau.eta * wildOddBoundaryDZero tau base := by
  unfold wildOddBoundaryDZero
  field_simp [tau.eta_ne_zero]

/-- The clean boundary row for the literal natural-multiple representative. -/
noncomputable def wildOddBoundaryPair {k : Type*} [Field k]
    (tau base : WildOddNamedCoefficientPair k) (j : k) :
    WildOddCoefficientPair k :=
  ⟨tau.eta * (j + wildOddBoundaryDZero tau base),
    tau.eta *
      (j * tau.gamma + wildOddBoundaryDZero tau base * base.gamma)⟩

theorem wildOddBoundaryPair_eq_add {k : Type*} [Field k]
    (tau base : WildOddNamedCoefficientPair k) (j : k) :
    wildOddBoundaryPair tau base j =
      ⟨j * tau.eta + base.eta,
        j * tau.eta * tau.gamma + base.eta * base.gamma⟩ := by
  have heta := wildOddBoundary_eta_eq tau base
  apply WildOddCoefficientPair.ext
  · dsimp only [wildOddBoundaryPair]
    rw [mul_add]
    rw [← heta]
    ring
  · dsimp only [wildOddBoundaryPair]
    rw [mul_add]
    calc
      tau.eta * (j * tau.gamma) +
          tau.eta * (wildOddBoundaryDZero tau base * base.gamma) =
        tau.eta * j * tau.gamma +
          (tau.eta * wildOddBoundaryDZero tau base) * base.gamma := by ring
      _ = j * tau.eta * tau.gamma + base.eta * base.gamma := by
        rw [← heta]
        ring

@[simp]
theorem wildOddBoundaryPair_zero {k : Type*} [Field k]
    (tau base : WildOddNamedCoefficientPair k) :
    wildOddBoundaryPair tau base 0 = wildOddBasePair base := by
  rw [wildOddBoundaryPair_eq_add]
  apply WildOddCoefficientPair.ext <;>
    simp only [wildOddBasePair, zero_mul, zero_add]

/-- A literal powered row has exactly the manuscript's scaled pair. -/
theorem wildOddCoefficientPair_eq_tauPowerPair_of_function_eq_pow
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chiPower chiGenerator : LocalQuasiCharData E}
    {psi : LocalAddCharData E}
    (power : LocalLamprechtPhaseData E chiPower psi)
    (generator : LocalLamprechtPhaseData E chiGenerator psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (hoddGenerator : Odd chiGenerator.conductor)
    (q : ℕ)
    (hfun : ∀ x,
      power.criticalFunction x = generator.criticalFunction x ^ q) :
    wildOddCoefficientPair power psi0 hpsi0 hchar =
      wildOddTauPowerPair
        (WildOddNamedCoefficientPair.ofPair
          (wildOddCoefficientPair generator psi0 hpsi0 hchar)
          (generator.polarCoefficient_ne_zero_of_odd psi0 hpsi0
            hoddGenerator))
        (q : ResidueField E) := by
  rw [wildOddCoefficientPair_eq_nsmul_of_function_eq_pow power generator
    psi0 hpsi0 hchar q hfun]
  apply WildOddCoefficientPair.ext
  · rfl
  · unfold wildOddTauPowerPair WildOddNamedCoefficientPair.ofPair
    dsimp only
    simp only [wildOddCoefficientPair_affine]
    field_simp [generator.polarCoefficient_ne_zero_of_odd psi0 hpsi0
      hoddGenerator]

/-- When complete functions multiply, the normalized literal power row and
the base row give the clean manuscript boundary pair. -/
theorem wildOddCoefficientPair_eq_boundaryPair_of_function_eq_mul
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi chiTau chiBase : LocalQuasiCharData E}
    {psi : LocalAddCharData E}
    (row : LocalLamprechtPhaseData E chi psi)
    (tau : LocalLamprechtPhaseData E chiTau psi)
    (base : LocalLamprechtPhaseData E chiBase psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (tauNamed baseNamed :
      WildOddNamedCoefficientPair (ResidueField E))
    (j : ResidueField E)
    (htau : wildOddCoefficientPair tau psi0 hpsi0 hchar =
      wildOddTauPowerPair tauNamed j)
    (hbase : wildOddCoefficientPair base psi0 hpsi0 hchar =
      wildOddBasePair baseNamed)
    (hfun : ∀ x,
      row.criticalFunction x =
        tau.criticalFunction x * base.criticalFunction x) :
    wildOddCoefficientPair row psi0 hpsi0 hchar =
      wildOddBoundaryPair tauNamed baseNamed j := by
  rw [wildOddCoefficientPair_eq_add_of_function_eq_mul row tau base psi0
    hpsi0 hchar hfun]
  have htauPolar := congrArg WildOddCoefficientPair.polar htau
  have htauAffine := congrArg WildOddCoefficientPair.affine htau
  have hbasePolar := congrArg WildOddCoefficientPair.polar hbase
  have hbaseAffine := congrArg WildOddCoefficientPair.affine hbase
  change tau.polarCoefficient psi0 hpsi0 = j * tauNamed.eta at htauPolar
  change tau.affineCoefficient psi0 hpsi0 hchar =
    j * tauNamed.eta * tauNamed.gamma at htauAffine
  change base.polarCoefficient psi0 hpsi0 = baseNamed.eta at hbasePolar
  change base.affineCoefficient psi0 hpsi0 hchar =
    baseNamed.eta * baseNamed.gamma at hbaseAffine
  rw [htauPolar, htauAffine, hbasePolar, hbaseAffine]
  rw [wildOddBoundaryPair_eq_add]

/-- Coefficient transport attached to an exact change of stationary
representative.  The source-to-selected orientation is part of the data. -/
structure WildOddRepresentativeTranslationCertificate
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) : Prop where
  function_transport : ∀ x,
    selected.criticalFunction x = source.criticalFunction x *
      psi0 (R.translationCoefficient psi0 hpsi0 * x)
  polar_transport :
    selected.polarCoefficient psi0 hpsi0 =
      source.polarCoefficient psi0 hpsi0
  affine_transport :
    selected.affineCoefficient psi0 hpsi0 hchar =
      source.affineCoefficient psi0 hpsi0 hchar +
        R.translationCoefficient psi0 hpsi0
  affine_parameter_transport :
    selected.affineCoefficient psi0 hpsi0 hchar =
      source.affineCoefficient psi0 hpsi0 hchar +
        source.polarCoefficient psi0 hpsi0 *
          criticalRepresentativeTranslationParameter E chi psi R.d R.hm
            R.hlarge R.Gamma R.delta R.hdelta R.beta R.beta' R.hbeta
              R.hbeta'

/-- The real PhaseReduction representative-change data gives the complete
function, polar, and both equivalent affine transport formulas. -/
theorem OddRepresentativeChangeData.wildOddTranslationCertificate
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    WildOddRepresentativeTranslationCertificate R psi0 hpsi0 hchar := by
  cases R with
  | mk d hm hlarge Gamma delta hdelta beta beta' hbeta hbeta' hsource
      hselected =>
    subst source
    subst selected
    refine
      { function_transport :=
          OddRepresentativeChangeData.criticalFunction_eq_mul_translation
            _ psi0 hpsi0
        polar_transport := rfl
        affine_transport := ?_
        affine_parameter_transport := ?_ }
    · exact criticalAffineCoefficient_changeRepresentative E chi psi d hm
        hlarge Gamma delta hdelta psi0 hpsi0 hchar beta beta' hbeta hbeta'
    · exact LocalLamprechtPhaseData.odd_affineCoefficient_changeRepresentative
        d hm hlarge Gamma delta hdelta psi0 hpsi0 hchar beta beta' hbeta
          hbeta'

/-! ## Exact affine transport of extracted pairs -/

/-- Add the affine representative-translation term without changing the
polar coefficient. -/
def WildOddCoefficientPair.translateAffine {k : Type*} [Add k]
    (P : WildOddCoefficientPair k) (translation : k) :
    WildOddCoefficientPair k :=
  ⟨P.polar, P.affine + translation⟩

@[simp]
theorem WildOddCoefficientPair.translateAffine_polar
    {k : Type*} [Add k] (P : WildOddCoefficientPair k) (translation : k) :
    (P.translateAffine translation).polar = P.polar :=
  rfl

@[simp]
theorem WildOddCoefficientPair.translateAffine_affine
    {k : Type*} [Add k] (P : WildOddCoefficientPair k) (translation : k) :
    (P.translateAffine translation).affine = P.affine + translation :=
  rfl

/-- Adding a translated powered norm row to a base row gives the clean
boundary row with that same affine translation retained. -/
theorem wildOddBoundaryPair_translateAffine_eq_add
    {k : Type*} [Field k]
    (tau base : WildOddNamedCoefficientPair k) (j translation : k) :
    (wildOddBoundaryPair tau base j).translateAffine translation =
      ⟨(wildOddTauPowerPair tau j).polar +
          (wildOddBasePair base).polar,
        (wildOddTauPowerPair tau j).affine + translation +
          (wildOddBasePair base).affine⟩ := by
  rw [wildOddBoundaryPair_eq_add]
  apply WildOddCoefficientPair.ext <;>
    simp only [WildOddCoefficientPair.translateAffine,
      wildOddTauPowerPair, wildOddBasePair] <;> ring

/-- The exact source-to-selected representative change on coefficient
pairs.  In particular, the translation has the positive direction fixed by
`OddRepresentativeChangeData`. -/
theorem wildOddCoefficientPair_eq_translateAffine
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    wildOddCoefficientPair selected psi0 hpsi0 hchar =
      (wildOddCoefficientPair source psi0 hpsi0 hchar).translateAffine
        (R.translationCoefficient psi0 hpsi0) := by
  have htransport := R.wildOddTranslationCertificate psi0 hpsi0 hchar
  apply WildOddCoefficientPair.ext
  · exact htransport.polar_transport
  · exact htransport.affine_transport

/-- The same transport with the translation written as polar coefficient
times the exact representative parameter. -/
theorem wildOddCoefficientPair_eq_translateAffine_parameter
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    {source selected : LocalLamprechtPhaseData E chi psi}
    (R : OddRepresentativeChangeData source selected)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2) :
    wildOddCoefficientPair selected psi0 hpsi0 hchar =
      (wildOddCoefficientPair source psi0 hpsi0 hchar).translateAffine
        (source.polarCoefficient psi0 hpsi0 *
          criticalRepresentativeTranslationParameter E chi psi R.d R.hm
            R.hlarge R.Gamma R.delta R.hdelta R.beta R.beta' R.hbeta
              R.hbeta') := by
  have htransport := R.wildOddTranslationCertificate psi0 hpsi0 hchar
  apply WildOddCoefficientPair.ext
  · exact htransport.polar_transport
  · exact htransport.affine_parameter_transport

/-- Normalize the pair of one actual odd phase, after its polar
nonvanishing has been proved from the conductor parity. -/
noncomputable def wildOddNamedPairOfPhase
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (hodd : Odd chi.conductor) :
    WildOddNamedCoefficientPair (ResidueField E) :=
  WildOddNamedCoefficientPair.ofPair
    (wildOddCoefficientPair D psi0 hpsi0 hchar)
    (D.polarCoefficient_ne_zero_of_odd psi0 hpsi0 hodd)

/-- The defining `(eta, eta*gamma)` identity for an actual odd phase. -/
theorem wildOddCoefficientPair_eq_namedPairOfPhase
    {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}
    (D : LocalLamprechtPhaseData E chi psi)
    (psi0 : FiniteAddChar (ResidueField E)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField E) ≠ 2)
    (hodd : Odd chi.conductor) :
    wildOddCoefficientPair D psi0 hpsi0 hchar =
      wildOddBasePair
        (wildOddNamedPairOfPhase D psi0 hpsi0 hchar hodd) := by
  exact WildOddNamedCoefficientPair.pair_eq _
    (D.polarCoefficient_ne_zero_of_odd psi0 hpsi0 hodd)

/-! ## Low and boundary rows from the real source-tied phases -/

section LowCoefficientRows

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hLow : (data.twistData 1).conductor ≤ t + 1)
  (delta : Fˣ) (epsilon1 : Kˣ)
  (hdelta : ord F (delta : F) =
    ((((t + 1 : ℕ) : ℤ) + data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hepsilon1 : ord K (epsilon1 : K) =
    (((t + 1 - (data.twistData 1).conductor : ℕ) : ℤ) : WithTop ℤ))
  (hT : 2 ≤ t + 1)
  (hgammaF : ord F (lowGammaF F K delta epsilon1 : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))
  (hgammaK : ord K (lowGammaK F K delta epsilon1 : K) =
    (((chiK.conductor : ℤ) + psiK.conductor : ℤ) : WithTop ℤ))
  (P : LowStationaryNormRepresentativePair F K
    (lowCriticalFloorDepth t) d
    (stationaryCoefficientClass F
      (quasiCharDataOfIsConductor F
        (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
        (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
          (lowNormCharacterGenerator F K ht hres pi hpi hgen)
          (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen)))
      data.baseAddChar (lowCriticalConductorDecomposition (t := t) hT)
        delta hdelta)
    (stationaryCoefficientClass F (data.twistData 1) data.baseAddChar hF
      (lowGammaF F K delta epsilon1) hgammaF))
  (table : LowConductorParameterTableData F K ht hres pi hpi hgen
    (data.twistData 1) chiK data.baseAddChar psiK hminimal hchi hpsi hF hLow
      delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P)

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

include hT

/-- Odd post-drop parity is exactly oddness of the new norm-generator
conductor `t+1`; this is the parity used by every nonzero lower norm row. -/
theorem wildOdd_lowCriticalConductor_odd
    (hparity : lowCriticalParity t = 1) :
    Odd (quasiCharDataOfIsConductor F
      (lowNormCharacterGenerator F K ht hres pi hpi hgen).1 (t + 1)
      (ramifiedNormCharacter_conductor F K ht hres pi hpi hgen
        (lowNormCharacterGenerator F K ht hres pi hpi hgen)
        (lowNormCharacterGenerator_ne_one F K ht hres pi hpi hgen))).conductor := by
  rw [quasiCharDataOfIsConductor_conductor]
  refine ⟨lowCriticalFloorDepth t, ?_⟩
  simpa only [hparity] using
    (lowCriticalConductorDecomposition (t := t) hT).conductor_eq

include hminimal hLow in

/-- The actual nonidentity low twist datum has conductor `t+1`.  This keeps
the direction from the chosen norm-character index to the actual twist. -/
theorem wildOdd_lowActualTwist_conductor
    (j : OddNormIndex F K) :
    (data.twistData
      (ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
        (Multiplicative.ofAdd
          (j : ZMod (Module.finrank F K))))).conductor = t + 1 := by
  let mu := ramifiedNormCharacterZModEquiv F K ht hres pi hpi hgen
    (Multiplicative.ofAdd (j : ZMod (Module.finrank F K)))
  let twist := lowNonzeroTwistDatum F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property
  have hdata : twist = data.twistData mu := by
    rw [show twist = ramifiedNormCharacterOrbitTwistData
        F K ht hres pi hpi hgen (data.twistData 1) mu by
      simpa only [twist, mu] using
        (lowNonzeroTwistDatum_eq_actual F K ht hres pi hpi hgen
          (data.twistData 1) hminimal hLow
            (j : ZMod (Module.finrank F K)) j.property)]
    apply LocalQuasiCharData.ext_character F
    rw [ramifiedNormCharacterOrbitTwistData_character,
      data.twistData_character, data.twistData_character]
    ext z
    simp
  change (data.twistData mu).conductor = t + 1
  rw [← hdata]
  exact lowNonzeroTwistDatum_conductor F K ht hres pi hpi hgen
    (data.twistData 1) hminimal hLow
      (j : ZMod (Module.finrank F K)) j.property

/-- The normalized fixed norm-generator row, written as
`(etaZero, etaZero*gammaZero)`. -/
noncomputable def wildOddLowGeneratorNamedPair
    (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    WildOddNamedCoefficientPair (ResidueField F) := by
  apply wildOddNamedPairOfPhase
    (lowNormalizedNormGeneratorPhase F K ht hres pi hpi hgen data hF
      delta epsilon1 hdelta hT hgammaF P hparity) psi0 hpsi0 hchar
  exact wildOdd_lowCriticalConductor_odd F K ht hres pi hpi hgen hT hparity

/-- The actual identity/base row, written as `(eta,eta*gamma)` only after
its polar coefficient has been proved nonzero. -/
noncomputable def wildOddLowBaseNamedPair
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (hbaseOdd : Odd (data.twistData 1).conductor) :
    WildOddNamedCoefficientPair (ResidueField F) :=
  wildOddNamedPairOfPhase
    (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF hminimal
      hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
        table) psi0 hpsi0 hchar hbaseOdd

/-- The literal nonzero norm row is exactly
`j*(etaZero,etaZero*gammaZero)`. -/
theorem wildOdd_lowLiteralNormCoefficients
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P j hparity)
      psi0 hpsi0 hchar =
      wildOddTauPowerPair
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        ((j : ZMod (Module.finrank F K)).val : ResidueField F) := by
  simpa only [wildOddLowGeneratorNamedPair, wildOddNamedPairOfPhase] using
    wildOddCoefficientPair_eq_tauPowerPair_of_function_eq_pow
      (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P j hparity)
      (lowNormalizedNormGeneratorPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P hparity)
      psi0 hpsi0 hchar
      (wildOdd_lowCriticalConductor_odd F K ht hres pi hpi hgen hT hparity)
      (j : ZMod (Module.finrank F K)).val
      (lowNormalizedLiteralPower_criticalFunction_eq_pow F K ht hres pi
        hpi hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)

/-- The actual Teichmüller norm row retains the exact positive affine
representative translation from the literal-power row. -/
theorem wildOdd_lowActualNormCoefficients
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P j hparity)
      psi0 hpsi0 hchar =
      (wildOddTauPowerPair
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)).translateAffine
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
            psi0 hpsi0) := by
  let R := lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
    hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity
  calc
    _ = (wildOddCoefficientPair
          (lowNormalizedLiteralPowerPhase F K ht hres pi hpi hgen data hF
            delta epsilon1 hdelta hT hgammaF P j hparity)
          psi0 hpsi0 hchar).translateAffine
            (R.translationCoefficient psi0 hpsi0) :=
      wildOddCoefficientPair_eq_translateAffine R psi0 hpsi0 hchar
    _ = _ := by
      rw [wildOdd_lowLiteralNormCoefficients F K ht hres pi hpi hgen data
        hF delta epsilon1 hdelta hT hgammaF P j hparity psi0 hpsi0 hchar]

/-- The named source norm row is the same actual Teichmüller row, so its
pair has the identical retained translation. -/
theorem wildOdd_lowSourceNormCoefficients
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j) psi0 hpsi0 hchar =
      (wildOddTauPowerPair
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)).translateAffine
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
            psi0 hpsi0) := by
  calc
    _ = wildOddCoefficientPair
        (lowActualTeichmullerPowerPhase F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P j hparity)
        psi0 hpsi0 hchar := by
      apply wildOddCoefficientPair_eq_of_function_eq
      intro X
      exact lowSourceNormFunction_eq_actualTeichmuller F K ht hres pi hpi
        hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity X
    _ = _ := wildOdd_lowActualNormCoefficients F K ht hres pi hpi hgen data
      hF delta epsilon1 hdelta hT hgammaF P j hparity psi0 hpsi0 hchar

/-- The actual `j=0` base row has the manuscript pair `(eta,eta*gamma)` in
the very same lower source coordinate. -/
theorem wildOdd_lowBaseCoefficients
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (hbaseOdd : Odd (data.twistData 1).conductor) :
    wildOddCoefficientPair
      (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table) psi0 hpsi0 hchar =
      wildOddBasePair
        (wildOddLowBaseNamedPair F K ht hres pi hpi hgen data chiK psiK hF
          hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
            hgammaK P table psi0 hpsi0 hchar hbaseOdd) := by
  simpa only [wildOddLowBaseNamedPair] using
    wildOddCoefficientPair_eq_namedPairOfPhase
      (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table) psi0 hpsi0 hchar hbaseOdd

/-- In the strict-lower regime, every nonidentity selected twist row is the
actual source norm row, hence has the powered row plus its exact affine
representative translation. -/
theorem wildOdd_lowStrictTwistCoefficients
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hstrict : (data.twistData 1).conductor < t + 1)
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j) psi0 hpsi0 hchar =
      (wildOddTauPowerPair
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)).translateAffine
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
            psi0 hpsi0) := by
  calc
    _ = wildOddCoefficientPair
        (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
          hdelta hT hgammaF P j) psi0 hpsi0 hchar := by
      apply wildOddCoefficientPair_eq_of_function_eq
      intro X
      exact lowSourceTwistFunction_eq_norm_of_strict F K ht hres pi hpi
        hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta
          hepsilon1 hT hgammaF hgammaK P table WTwist hstrict j X
    _ = _ := wildOdd_lowSourceNormCoefficients F K ht hres pi hpi hgen data
      hF delta epsilon1 hdelta hT hgammaF P j hparity psi0 hpsi0 hchar

/-- At the boundary the base conductor is odd whenever the new norm-row
parity is odd. -/
theorem wildOdd_lowBoundaryBase_odd
    (hboundary : (data.twistData 1).conductor = t + 1)
    (hparity : lowCriticalParity t = 1) :
    Odd (data.twistData 1).conductor := by
  refine ⟨lowCriticalFloorDepth t, ?_⟩
  rw [hboundary]
  simpa only [hparity] using
    (lowCriticalConductorDecomposition (t := t) hT).conductor_eq

/-- Boundary notation for the actual base row, with nonvanishing obtained
from the boundary conductor equality rather than postulated. -/
noncomputable def wildOddLowBoundaryBaseNamedPair
    (hboundary : (data.twistData 1).conductor = t + 1)
    (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    WildOddNamedCoefficientPair (ResidueField F) :=
  wildOddLowBaseNamedPair F K ht hres pi hpi hgen data chiK psiK hF
    hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table psi0 hpsi0 hchar
        (wildOdd_lowBoundaryBase_odd (F := F) (K := K) (data := data)
          hT hboundary hparity)

/-- The `j=0` boundary row is exactly the clean specialization
`etaZero*(dZero,dZero*gamma)` and simultaneously the actual base row. -/
theorem wildOdd_lowBoundaryZeroCoefficients
    (hboundary : (data.twistData 1).conductor = t + 1)
    (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table) psi0 hpsi0 hchar =
      wildOddBoundaryPair
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        (wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table hboundary hparity psi0 hpsi0 hchar)
        0 := by
  rw [wildOddBoundaryPair_zero]
  exact wildOdd_lowBaseCoefficients F K ht hres pi hpi hgen data chiK psiK
    hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
      hgammaK P table psi0 hpsi0 hchar
        (wildOdd_lowBoundaryBase_odd (F := F) (K := K) (data := data)
          hT hboundary hparity)

/-- Every nonzero boundary row is the manuscript affine row
`(etaZero*(j+dZero), etaZero*(j*gammaZero+dZero*gamma))`, with the actual
Teichmüller representative translation retained in the affine coordinate. -/
theorem wildOdd_lowBoundaryTwistCoefficients
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hboundary : (data.twistData 1).conductor = t + 1)
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j) psi0 hpsi0 hchar =
      (wildOddBoundaryPair
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        (wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table hboundary hparity psi0 hpsi0 hchar)
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)).translateAffine
          (OddRepresentativeChangeData.translationCoefficient
            (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
            psi0 hpsi0) := by
  calc
    _ = ⟨(wildOddCoefficientPair
          (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
            hdelta hT hgammaF P j) psi0 hpsi0 hchar).polar +
          (wildOddCoefficientPair
            (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
              hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
                hgammaF hgammaK P table) psi0 hpsi0 hchar).polar,
        (wildOddCoefficientPair
          (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
            hdelta hT hgammaF P j) psi0 hpsi0 hchar).affine +
          (wildOddCoefficientPair
            (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
              hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
                hgammaF hgammaK P table) psi0 hpsi0 hchar).affine⟩ := by
      apply wildOddCoefficientPair_eq_add_of_function_eq_mul
      intro X
      exact lowSourceTwistFunction_eq_norm_mul_base_of_boundary F K ht hres
        pi hpi hgen data chiK psiK hF hminimal hchi hpsi hLow delta epsilon1
          hdelta hepsilon1 hT hgammaF hgammaK P table WTwist hboundary j X
    _ = _ := by
      rw [wildOdd_lowSourceNormCoefficients F K ht hres pi hpi hgen data hF
        delta epsilon1 hdelta hT hgammaF P j hparity psi0 hpsi0 hchar]
      rw [wildOdd_lowBaseCoefficients F K ht hres pi hpi hgen data chiK psiK
        hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table psi0 hpsi0 hchar
            (wildOdd_lowBoundaryBase_odd (F := F) (K := K) (data := data)
              hT hboundary hparity)]
      exact (wildOddBoundaryPair_translateAffine_eq_add
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        (wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table hboundary hparity psi0 hpsi0 hchar)
        ((j : ZMod (Module.finrank F K)).val : ResidueField F)
        (OddRepresentativeChangeData.translationCoefficient
          (lowTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
            hgen data hF delta epsilon1 hdelta hT hgammaF P j hparity)
          psi0 hpsi0)).symm

/-- Odd critical parity makes each actual selected nonzero low twist polar
coefficient nonzero. -/
theorem wildOdd_lowSourceTwistPolar_ne_zero
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1) :
    (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table WTwist j).polarCoefficient psi0 hpsi0 ≠ 0 := by
  apply LocalLamprechtPhaseData.polarCoefficient_ne_zero_of_odd
  refine ⟨lowCriticalFloorDepth t, ?_⟩
  rw [wildOdd_lowActualTwist_conductor F K ht hres pi hpi hgen data
    hminimal hLow hT j]
  simpa only [hparity] using
    (lowCriticalConductorDecomposition (t := t) hT).conductor_eq

/-- Consequently every displayed boundary numerator `j+dZero` is nonzero
before it can be used as a denominator in any later phase calculation. -/
theorem wildOdd_lowBoundaryNumerator_ne_zero
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hboundary : (data.twistData 1).conductor = t + 1)
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    ((j : ZMod (Module.finrank F K)).val : ResidueField F) +
      wildOddBoundaryDZero
        (wildOddLowGeneratorNamedPair F K ht hres pi hpi hgen data hF
          delta epsilon1 hdelta hT hgammaF P hparity psi0 hpsi0 hchar)
        (wildOddLowBoundaryBaseNamedPair F K ht hres pi hpi hgen data chiK
          psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
            hgammaF hgammaK P table hboundary hparity psi0 hpsi0 hchar) ≠ 0 := by
  intro hzero
  have hrow := congrArg WildOddCoefficientPair.polar
    (wildOdd_lowBoundaryTwistCoefficients F K ht hres pi hpi hgen data chiK
      psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
        hgammaF hgammaK P table WTwist hboundary j hparity psi0 hpsi0 hchar)
  apply wildOdd_lowSourceTwistPolar_ne_zero F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table WTwist j hparity psi0 hpsi0
  change (wildOddCoefficientPair
    (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
      hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
        hgammaK P table WTwist j) psi0 hpsi0 hchar).polar = 0
  rw [hrow]
  simp only [WildOddCoefficientPair.translateAffine_polar,
    wildOddBoundaryPair]
  rw [hzero, mul_zero]

/-- Even base conductor parity gives the literal zero coefficient pair. -/
theorem wildOdd_lowBaseCoefficients_even
    (hepsilon : epsilon = 0)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceBasePhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table) psi0 hpsi0 hchar = ⟨0, 0⟩ := by
  apply wildOddCoefficientPair_eq_zero_of_function_eq_one
  intro X
  exact lowSourceBaseFunction_eq_one_of_even F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table hepsilon X

/-- Even new norm-row parity gives the literal zero coefficient pair. -/
theorem wildOdd_lowNormCoefficients_even
    (hparity : lowCriticalParity t = 0) (j : OddNormIndex F K)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceNormPhase F K ht hres pi hpi hgen data hF delta epsilon1
        hdelta hT hgammaF P j) psi0 hpsi0 hchar = ⟨0, 0⟩ := by
  apply wildOddCoefficientPair_eq_zero_of_function_eq_one
  intro X
  exact lowSourceNormFunction_eq_one_of_even F K ht hres pi hpi hgen data
    hF delta epsilon1 hdelta hT hgammaF P hparity j X

/-- Even new twist-row parity gives the literal zero coefficient pair. -/
theorem wildOdd_lowTwistCoefficients_even
    (WTwist : ∀ j : OddNormIndex F K,
      LowOddTwistWitness F K ht hres pi hpi hgen data chiK psiK hF hminimal
        hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF hgammaK P
          table j)
    (hparity : lowCriticalParity t = 0) (j : OddNormIndex F K)
    (psi0 : FiniteAddChar (ResidueField F)) (hpsi0 : psi0 ≠ 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
      (lowSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF
        hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT hgammaF
          hgammaK P table WTwist j) psi0 hpsi0 hchar = ⟨0, 0⟩ := by
  apply wildOddCoefficientPair_eq_zero_of_function_eq_one
  intro X
  exact lowSourceTwistFunction_eq_one_of_even F K ht hres pi hpi hgen data
    chiK psiK hF hminimal hchi hpsi hLow delta epsilon1 hdelta hepsilon1 hT
      hgammaF hgammaK P table WTwist hparity j X

end LowCoefficientRows

/-! ## Above-break lower rows from the real high source -/

section HighAboveRows

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
  (hres : residueDegree F K = 1)
  (pi : ringOfIntegers K)
  (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
  (hgen : Algebra.adjoin (ringOfIntegers F)
    ({pi} : Set (ringOfIntegers K)) = ⊤)
  {globalChi : ContinuousQuasiChar F} {globalPsi : ContinuousAddChar F}
  (data : FirstMainComputationalData F K globalChi globalPsi)
  (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
  {d epsilon dK epsilonK : ℕ}
  (hF : IsStationaryConductorDecomposition
    (data.twistData 1).conductor d epsilon)
  (hK : IsStationaryConductorDecomposition chiK.conductor dK epsilonK)
  (hminimal : IsMinimalNormCharacterOrbitRepresentative F K
    (data.twistData 1))
  (hchi : chiK.character = (data.twistData 1).character.compNorm)
  (hpsi : psiK.character = data.baseAddChar.character.compTrace)
  (hodd : Odd (Module.finrank F K))
  (htpos : 0 < t)
  (hstrict : t + 1 < (data.twistData 1).conductor)
  (hupper : (data.twistData 1).conductor < 2 * (t + 1))
  (gammaF : Fˣ)
  (hgammaF : ord F (gammaF : F) =
    ((((data.twistData 1).conductor : ℤ) +
      data.baseAddChar.conductor : ℤ) : WithTop ℤ))

local instance : NeZero (Module.finrank F K) :=
  ⟨Module.finrank_pos.ne'⟩

local instance : Fact (Module.finrank F K).Prime :=
  ⟨PrimeCyclicExtension.degree_prime F K⟩

/-- The clean base row at strict upper conductor, normalized only after its
polar coefficient has been proved nonzero. -/
noncomputable def wildOddHighSourceBaseNamedPair
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    WildOddNamedCoefficientPair (ResidueField F) :=
  WildOddNamedCoefficientPair.ofPair
    (wildOddCoefficientPair
      (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0)
      C.lower C.lower_ne_one hchar)
    (LocalLamprechtPhaseData.polarCoefficient_ne_zero_of_odd
      (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0)
      C.lower C.lower_ne_one (by
        refine ⟨d, ?_⟩
        rw [ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen]
        simpa [hepsilon] using hF.conductor_eq))

/-- Both coefficients of the zero-index/base row are exactly
`(eta, eta*gamma)`. -/
theorem wildOdd_highSourceBaseCoefficients
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source 0)
        C.lower C.lower_ne_one hchar =
      wildOddBasePair
        (wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF p C source hepsilon hchar) := by
  let P := wildOddCoefficientPair
    (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
      hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0)
    C.lower C.lower_ne_one hchar
  have hP : P.polar ≠ 0 :=
    LocalLamprechtPhaseData.polarCoefficient_ne_zero_of_odd
      (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
        hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF source 0)
      C.lower C.lower_ne_one (by
        refine ⟨d, ?_⟩
        rw [ramifiedNormCharacterZModEquiv_zero F K ht hres pi hpi hgen]
        simpa [hepsilon] using hF.conductor_eq)
  simpa only [P, wildOddHighSourceBaseNamedPair, wildOddBasePair] using
    WildOddNamedCoefficientPair.pair_eq P hP

/-- Every above-break odd lower twist row is the same clean base row, for
all indices including zero. -/
theorem wildOdd_highTwistCoefficients_above_odd
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 1)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (j : ZMod (Module.finrank F K)) :
    wildOddCoefficientPair
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j)
        C.lower C.lower_ne_one hchar =
      wildOddBasePair
        (wildOddHighSourceBaseNamedPair F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF p C source hepsilon hchar) := by
  calc
    wildOddCoefficientPair
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j)
        C.lower C.lower_ne_one hchar =
      wildOddCoefficientPair
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source 0)
        C.lower C.lower_ne_one hchar := by
          apply wildOddCoefficientPair_eq_of_function_eq
          intro x
          exact highSourceTwistFunction_eq_base F K ht hres pi hpi hgen
            data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict
              hupper gammaF hgammaF source j x
    _ = _ := wildOdd_highSourceBaseCoefficients F K ht hres pi hpi hgen
      data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
        gammaF hgammaF p C source hepsilon hchar

/-- At even base parity the above-break row is literally constant one and
its polar and affine coefficients are both zero. -/
theorem wildOdd_highTwistCoefficients_above_even
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (hepsilon : epsilon = 0)
    (hchar : ringChar (ResidueField F) ≠ 2)
    (j : ZMod (Module.finrank F K)) :
    wildOddCoefficientPair
        (highSourceTwistPhase F K ht hres pi hpi hgen data chiK psiK hF hK
          hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j)
        C.lower C.lower_ne_one hchar = ⟨0, 0⟩ ∧
      ∀ x : ResidueField F,
        highSourceTwistFunction F K ht hres pi hpi hgen data chiK psiK hF
          hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF hgammaF
            source j x = 1 := by
  have hfun := highSourceTwistFunction_eq_one_of_even F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF source hepsilon j
  refine ⟨wildOddCoefficientPair_eq_zero_of_function_eq_one _ C.lower
    C.lower_ne_one hchar hfun, hfun⟩

/-- The actual high Teichmüller representative is selected and the literal
natural multiple is the source.  Thus the affine correction is added from
literal to actual, never in the reverse direction. -/
theorem wildOdd_highActualTeichmullerTranslation
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    WildOddRepresentativeTranslationCertificate
      (highTeichmullerLiteralRepresentativeChange F K ht hres pi hpi hgen
        data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
          gammaF hgammaF source j hparity)
      C.lower C.lower_ne_one hchar :=
  OddRepresentativeChangeData.wildOddTranslationCertificate _ C.lower
    C.lower_ne_one hchar

/-- Pair-level version of the same source-to-selected transport:
`(A_actual,B_actual)=(A_literal,B_literal+DeltaB)`. -/
theorem wildOdd_highActualTeichmullerCoefficientTranslation
    (p : ℕ) (C : FrobeniusResidualAddCharData F p)
    (source : HighOddSimultaneousSource F K ht hres pi hpi hgen data chiK
      psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
        hgammaF)
    (j : OddNormIndex F K) (hparity : lowCriticalParity t = 1)
    (hchar : ringChar (ResidueField F) ≠ 2) :
    wildOddCoefficientPair
        (highNormActualTeichmullerPhase F K ht hres pi hpi hgen data chiK
          psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source j hparity)
        C.lower C.lower_ne_one hchar =
      ⟨(highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source j hparity).polarCoefficient C.lower
              C.lower_ne_one,
        (highNormLiteralPowerPhase F K ht hres pi hpi hgen data chiK psiK
          hF hK hminimal hchi hpsi hodd htpos hstrict hupper gammaF
            hgammaF source j hparity).affineCoefficient C.lower
              C.lower_ne_one hchar +
          OddRepresentativeChangeData.translationCoefficient
            (highTeichmullerLiteralRepresentativeChange F K ht hres pi hpi
              hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos
                hstrict hupper gammaF hgammaF source j hparity)
            C.lower C.lower_ne_one⟩ := by
  let cert := wildOdd_highActualTeichmullerTranslation F K ht hres pi hpi
    hgen data chiK psiK hF hK hminimal hchi hpsi hodd htpos hstrict hupper
      gammaF hgammaF p C source j hparity hchar
  exact WildOddCoefficientPair.ext cert.polar_transport cert.affine_transport

end HighAboveRows

/-! ## Common-coordinate and corrected representative-ratio API -/

/-- The coordinate facts used above are exactly the source and transport
facts from `PhaseReduction`; this record prevents a downstream assembly from
silently substituting an independently normalized coordinate. -/
structure WildOddLowerCoordinateTransportAPI : Prop where
  lowerSourceCoordinate_eq_norm :
    type_of%
      @PhaseReductionResidualCoordinateSource.lowerSourceCoordinate_eq_norm.{0, 0}
  scaledSourceCoordinate_eq :
    type_of%
      @PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq.{0}
  criticalFunction_transport :
    type_of% @criticalPolarFunction_transportCoordinate_apply.{0}
  polarCoefficient_transport :
    type_of% @criticalPolarCoefficient_transportCoordinate.{0}
  affineCoefficient_transport :
    type_of% @criticalPolarData_transportCoordinate_affine.{0}

/-- The accepted common/source coordinate package, with the source-to-
selected scaling direction fixed simultaneously for functions, polar
coefficients, and affine coefficients. -/
theorem wildOddLowerCoordinateTransportAPI :
    WildOddLowerCoordinateTransportAPI where
  lowerSourceCoordinate_eq_norm :=
    PhaseReductionResidualCoordinateSource.lowerSourceCoordinate_eq_norm
  scaledSourceCoordinate_eq :=
    PhaseReductionResidualCoordinateSource.scaledSourceCoordinate_eq
  criticalFunction_transport :=
    criticalPolarFunction_transportCoordinate_apply
  polarCoefficient_transport :=
    criticalPolarCoefficient_transportCoordinate
  affineCoefficient_transport :=
    criticalPolarData_transportCoordinate_affine

/-- The denominator `[j]` inside `(u+[j])/[j]` is nonzero before the scaled
numerator unit is constructed. -/
theorem wildOddIndexScalar_ne_zero
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [NeZero (Module.finrank F K)]
    [Fact (Module.finrank F K).Prime]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) (j : OddNormIndex F K) :
    oddNormIndexScalar F K ht hres pi hpi hgen htpos j ≠ 0 := by
  rw [← oddNormIndexUnit_coe F K ht hres pi hpi hgen htpos j]
  exact Units.ne_zero _

/-- The scaled numerator unit really is `(u+[j])/[j]`; its denominator was
certified by `wildOddIndexScalar_ne_zero` before this division. -/
@[simp]
theorem wildOddScaledNumeratorUnit_coe
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    [NeZero (Module.finrank F K)]
    [Fact (Module.finrank F K).Prime]
    {t : ℕ} (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (hres : residueDegree F K = 1)
    (pi : ringOfIntegers K)
    (hpi : (ValuativeRel.valuation K).IsUniformizer (pi : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({pi} : Set (ringOfIntegers K)) = ⊤)
    (htpos : 0 < t) {u : Kˣ} {n : Fˣ}
    (C : OddNormCorrectionUnitData F K ht hres pi hpi hgen htpos u n)
    (j : OddNormIndex F K) :
    ((OddNormCorrectionUnitData.scaledNumeratorUnit
      ht hres pi hpi hgen htpos C j : Kˣ) : K) =
      (u + algebraMap F K
        (oddNormIndexScalar F K ht hres pi hpi hgen htpos j)) /
      algebraMap F K
        (oddNormIndexScalar F K ht hres pi hpi hgen htpos j) := by
  unfold OddNormCorrectionUnitData.scaledNumeratorUnit
  simp only [Units.val_div_eq_div_val, Units.val_mk0, Units.coe_map,
    MonoidHom.coe_coe, oddNormIndexUnit_coe]

/-- Correct low raw representative ratio.  Its inverse norm factor is part
of the statement and has deliberately not been cancelled. -/
theorem wildOdd_lowRawRepresentativeRatio :
    type_of% @lowOddSourceTied_rowRatio_eq :=
  lowOddSourceTied_rowRatio_eq

/-- Correct high raw representative ratio.  Besides the scaled numerator it
retains the inverse norm of the high source factor `alpha1`. -/
theorem wildOdd_highRawRepresentativeRatio :
    type_of% @highOddSourceTied_rowRatio_eq :=
  highOddSourceTied_rowRatio_eq

/-- Only after the indexed norm character is applied does the low selected
row ratio become the manuscript value `mu(z_j)`. -/
theorem wildOdd_lowIndexedCharacter_z :
    type_of% @LowOddSourceTiedCorrectionCoordinates.powerCharacterBridge :=
  LowOddSourceTiedCorrectionCoordinates.powerCharacterBridge

/-- Only after the indexed norm character is applied does the high selected
row ratio become the manuscript value `mu(z_j)`. -/
theorem wildOdd_highIndexedCharacter_z :
    type_of% @HighOddSourceTiedCorrectionCoordinates.powerCharacterBridge :=
  HighOddSourceTiedCorrectionCoordinates.powerCharacterBridge

/-- The exceptional low `j=0` correction is tied to the selected rows
separately; it has no indexed-character bridge. -/
theorem wildOdd_lowZeroCorrection_selected :
    type_of% @lowOddSourceTied_zZero_selected_eq :=
  lowOddSourceTied_zZero_selected_eq

/-- The exceptional high `j=0` correction is tied to the selected rows
separately; it has no indexed-character bridge. -/
theorem wildOdd_highZeroCorrection_selected :
    type_of% @highOddSourceTied_zZero_selected_eq :=
  highOddSourceTied_zZero_selected_eq

/-- Proof-bearing facade for every correction-unit division and for the
strict separation between raw representative ratios and character-level
`z_j` identities. -/
structure WildOddLowerRepresentativeRatioAPI : Prop where
  norm_u : type_of% @OddNormCorrectionUnitData.norm_u
  zeroNumerator_ne_zero :
    type_of% @OddNormCorrectionUnitData.zeroNumerator_ne_zero
  zeroDenominator_ne_zero :
    type_of% @OddNormCorrectionUnitData.zeroDenominator_ne_zero
  numerator_ne_zero :
    type_of% @OddNormCorrectionUnitData.numerator_ne_zero
  denominator_ne_zero :
    type_of% @OddNormCorrectionUnitData.denominator_ne_zero
  zZero_formula : type_of% @OddNormCorrectionUnitData.coe_zZero
  z_formula : type_of% @OddNormCorrectionUnitData.coe_z
  identityIndexing : type_of% @oddNormCharacterIndexing_none
  nonidentityIndexing : type_of% @oddNormCharacterIndexing_some
  high_zZero_selected : type_of% @wildOdd_highZeroCorrection_selected
  low_zZero_selected : type_of% @wildOdd_lowZeroCorrection_selected
  high_raw_ratio : type_of% @wildOdd_highRawRepresentativeRatio
  low_raw_ratio : type_of% @wildOdd_lowRawRepresentativeRatio
  high_character_bridge : type_of% @wildOdd_highIndexedCharacter_z
  low_character_bridge : type_of% @wildOdd_lowIndexedCharacter_z

/-- All numerator, denominator, raw-ratio, zero-index, norm-direction, and
character-level correction statements supplied as one lower-table API. -/
theorem wildOddLowerRepresentativeRatioAPI :
    WildOddLowerRepresentativeRatioAPI where
  norm_u := OddNormCorrectionUnitData.norm_u
  zeroNumerator_ne_zero := OddNormCorrectionUnitData.zeroNumerator_ne_zero
  zeroDenominator_ne_zero :=
    OddNormCorrectionUnitData.zeroDenominator_ne_zero
  numerator_ne_zero := OddNormCorrectionUnitData.numerator_ne_zero
  denominator_ne_zero := OddNormCorrectionUnitData.denominator_ne_zero
  zZero_formula := OddNormCorrectionUnitData.coe_zZero
  z_formula := OddNormCorrectionUnitData.coe_z
  identityIndexing := oddNormCharacterIndexing_none
  nonidentityIndexing := oddNormCharacterIndexing_some
  high_zZero_selected := wildOdd_highZeroCorrection_selected
  low_zZero_selected := wildOdd_lowZeroCorrection_selected
  high_raw_ratio := wildOdd_highRawRepresentativeRatio
  low_raw_ratio := wildOdd_lowRawRepresentativeRatio
  high_character_bridge := wildOdd_highIndexedCharacter_z
  low_character_bridge := wildOdd_lowIndexedCharacter_z

/-! ## Cohesive public lower-table package -/

/-- The complete lower residual-coefficient responsibility.  Every field is
an independently usable theorem: strict, boundary, above-break, odd/even,
representative translation, boundary nonvanishing, common-coordinate
transport, and corrected representative ratios. -/
structure WildOddLowerResidualCoefficientAPI : Prop where
  coordinateTransport : WildOddLowerCoordinateTransportAPI
  coefficientPair_extensionality :
    type_of% @wildOddCoefficientPair_eq_of_function_eq.{0}
  representativeTranslation :
    type_of% @wildOddCoefficientPair_eq_translateAffine.{0}
  lowBase : type_of% @wildOdd_lowBaseCoefficients
  lowLiteralNorm : type_of% @wildOdd_lowLiteralNormCoefficients
  lowActualNorm : type_of% @wildOdd_lowActualNormCoefficients
  lowSourceNorm : type_of% @wildOdd_lowSourceNormCoefficients
  lowStrictTwist : type_of% @wildOdd_lowStrictTwistCoefficients
  lowBoundaryZero : type_of% @wildOdd_lowBoundaryZeroCoefficients
  lowBoundaryTwist : type_of% @wildOdd_lowBoundaryTwistCoefficients
  lowBoundaryNumerator_ne_zero :
    type_of% @wildOdd_lowBoundaryNumerator_ne_zero
  lowBaseEven : type_of% @wildOdd_lowBaseCoefficients_even
  lowNormEven : type_of% @wildOdd_lowNormCoefficients_even
  lowTwistEven : type_of% @wildOdd_lowTwistCoefficients_even
  highBase : type_of% @wildOdd_highSourceBaseCoefficients
  highAboveOdd : type_of% @wildOdd_highTwistCoefficients_above_odd
  highAboveEven : type_of% @wildOdd_highTwistCoefficients_above_even
  highRepresentativeTranslation :
    type_of% @wildOdd_highActualTeichmullerCoefficientTranslation
  representativeRatios : WildOddLowerRepresentativeRatioAPI

/-- Principal exported theorem for the lower half of the wild odd
coefficient table. -/
theorem wildOdd_lowerResidualCoefficients :
    WildOddLowerResidualCoefficientAPI where
  coordinateTransport := wildOddLowerCoordinateTransportAPI
  coefficientPair_extensionality := wildOddCoefficientPair_eq_of_function_eq
  representativeTranslation := wildOddCoefficientPair_eq_translateAffine
  lowBase := wildOdd_lowBaseCoefficients
  lowLiteralNorm := wildOdd_lowLiteralNormCoefficients
  lowActualNorm := wildOdd_lowActualNormCoefficients
  lowSourceNorm := wildOdd_lowSourceNormCoefficients
  lowStrictTwist := wildOdd_lowStrictTwistCoefficients
  lowBoundaryZero := wildOdd_lowBoundaryZeroCoefficients
  lowBoundaryTwist := wildOdd_lowBoundaryTwistCoefficients
  lowBoundaryNumerator_ne_zero := wildOdd_lowBoundaryNumerator_ne_zero
  lowBaseEven := wildOdd_lowBaseCoefficients_even
  lowNormEven := wildOdd_lowNormCoefficients_even
  lowTwistEven := wildOdd_lowTwistCoefficients_even
  highBase := wildOdd_highSourceBaseCoefficients
  highAboveOdd := wildOdd_highTwistCoefficients_above_odd
  highAboveEven := wildOdd_highTwistCoefficients_above_even
  highRepresentativeTranslation :=
    wildOdd_highActualTeichmullerCoefficientTranslation
  representativeRatios := wildOddLowerRepresentativeRatioAPI

end

end LanglandsFirstMainLemma
