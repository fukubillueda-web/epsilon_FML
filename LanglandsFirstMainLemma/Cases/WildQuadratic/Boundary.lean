import LanglandsFirstMainLemma.Cases.WildQuadratic.ErrorFormula
import LanglandsFirstMainLemma.Cases.WildQuadratic.QuadraticRefinement
import LanglandsFirstMainLemma.Cases.WildQuadratic.EqualCharacteristicBreak
import LanglandsFirstMainLemma.Parameters.MinimalOrbitStationary

namespace LanglandsFirstMainLemma

noncomputable section

namespace WildQuadraticBoundaryData

variable {k : Type*} [Field k] [Fintype k] [CharP k 2]

/-- The single Artin--Schreier witness which combines the square term and
the final `c + c^2` term in the manuscript's boundary calculation. -/
def artinSchreierWitness (D : WildQuadraticBoundaryData k) : k :=
  D.r ^ 3 / (1 + D.rho ^ 2) + 1 / (1 + D.rho)

/-- The two positively oriented correction classes add to the polar class. -/
theorem B_add_C_eq_A_rho (D : WildQuadraticBoundaryData k) :
    D.B + D.C = D.A_rho := by
  unfold B C A_rho
  field_simp [D.one_add_rho_ne_zero, D.one_add_rho_sq_ne_zero]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  ring_nf
  simp [htwo]

/-- After retaining every affine and correction term from the exact boundary
formula, its residual exponent is the manuscript's plus-sign
Artin--Schreier class. -/
theorem boundary_residual_eq_artinSchreier
    (D : WildQuadraticBoundaryData k) :
    D.aOne + D.A_rho + D.B * D.C =
      D.artinSchreierWitness + D.artinSchreierWitness ^ 2 := by
  rcases D with
    ⟨rho, r, gammaZero, gamma, gammaPrime, hrho, hr, hden, hgammaPrime⟩
  subst rho
  have hdenSq : 1 + (r ^ 2) ^ 2 ≠ 0 := by
    rw [show 1 + (r ^ 2) ^ 2 = (1 + r ^ 2) ^ 2 by
      rw [CharTwo.add_sq, one_pow]]
    exact pow_ne_zero 2 hden
  have hdenFour : 1 + r ^ 4 ≠ 0 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
    exact hdenSq
  have hdenEight : 1 + r ^ 8 ≠ 0 := by
    rw [show 1 + r ^ 8 = (1 + r ^ 4) ^ 2 by
      rw [CharTwo.add_sq, one_pow]
      ring]
    exact pow_ne_zero 2 hdenFour
  unfold aOne gammaOne A_rho B C artinSchreierWitness
  field_simp [hden, hdenSq, hdenFour, hdenEight]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hthree : (3 : k) = 1 := by linear_combination htwo
  have hfour : (4 : k) = 0 := by linear_combination 2 * htwo
  have hseven : (7 : k) = 1 := by linear_combination 3 * htwo
  have height : (8 : k) = 0 := by linear_combination 4 * htwo
  ring_nf
  simp only [htwo, hthree, hfour, hseven, height, mul_zero, mul_one,
    add_zero, zero_add]

/-- The complete finite boundary value, including both positive quadratic
corrections and the elementary phase, is exactly one. -/
theorem value_eq_one
    (q : CharTwoRefinement k) (D : WildQuadraticBoundaryData k) :
    D.value q = 1 := by
  have hBC := D.B_add_C_eq_A_rho
  have hAS := D.boundary_residual_eq_artinSchreier
  unfold value
  calc
    q D.A_rho * q D.B * q D.C * absoluteTraceChar k D.aOne =
        q D.A_rho * q D.A_rho * absoluteTraceChar k (D.B * D.C) *
          absoluteTraceChar k D.aOne := by
      rw [show q D.A_rho * q D.B * q D.C =
          q D.A_rho * (q D.B * q D.C) by ring,
        q.value_mul D.B D.C, hBC]
      ring
    _ = absoluteTraceChar k D.A_rho *
          absoluteTraceChar k (D.B * D.C) *
            absoluteTraceChar k D.aOne := by
      rw [show q D.A_rho * q D.A_rho = q D.A_rho ^ 2 by ring,
        q.value_sq]
    _ = absoluteTraceChar k
          (D.aOne + D.A_rho + D.B * D.C) := by
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
    _ = 1 := by
      rw [hAS, WildQuadraticRefinement.artinSchreier_sign]

end WildQuadraticBoundaryData

section RealBoundary

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]
  [Finite (NormCharacter F K)]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {q : CharTwoRefinement (ResidueField F)} {t m : ℕ}
  {V : WildQuadraticCoefficientView F K q t m}
  {data : FirstMainComputationalData F K V.chiFData.character
    V.psiF.character}
  {D : FirstMainPhaseData F K V.chiFData.character V.psiF.character data}
  {A : ExactQuadraticPhaseAssembly F K V.chiFData.character
    V.psiF.character data D (t := t) (m := m)}
  {DeltaF : LocalConstantFunction F} {DeltaK : LocalConstantFunction K}
  {hDeltaF : IsDeltaFiniteLocalConstant DeltaF}
  {hDeltaK : IsDeltaFiniteLocalConstant DeltaK}
  {rows : WildQuadraticPhaseRowCompatibility V data D A}
  {coordinates : WildQuadraticCoordinateCompatibility V data D A}
  {refinements : WildQuadraticRefinementAssembly V data D A coordinates}
  {formula : WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates
    refinements}
  {boundary : WildQuadraticBoundaryData (ResidueField F)}
  {chiCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
    V.psiF V.chiFData q}
  {tauCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
    V.psiF V.tauData q}
  {compatibility : WildQuadraticBoundaryCompatibility
    (V := V) (A := A) boundary}

namespace WildQuadraticBoundaryFormula

/-- A genuine boundary formula forces precisely `m = t + 1` and odd
`T = t + 1`; equivalently this is the exceptional row `b = t`. -/
theorem exceptionalCondition
    (B : WildQuadraticBoundaryFormula formula boundary chiCorrection
      tauCorrection compatibility) :
    m = t + 1 ∧ Odd (t + 1) := by
  constructor
  · have hmatch := V.boundaryCoordinate
    change WildQuadraticCoefficientData.MatchesCorrection F K V.correction
      V.coefficients.1 at hmatch
    rw [B.coefficientData_eq] at hmatch
    rcases hmatch with ⟨hboundary, _, _⟩
    exact hboundary
  · have hrow : (V.coefficients.1).row = .boundaryOdd := by
      rw [B.coefficientData_eq]
      exact boundary.coefficientData_row
    have hparity :
        WildQuadraticConductorParity.ofConductor (t + 1) = .odd := by
      rw [← WildQuadraticCoefficientRow.ofConductors_TParity (m - 1) t,
        ← V.coefficients.2, hrow]
      rfl
    exact
      (WildQuadraticConductorParity.ofConductor_eq_odd_iff (t + 1)).mp
        hparity

/-- The exceptional row cannot occur in equal characteristic two: the exact
lower-break theorem makes `t` odd, whereas the boundary row makes `t + 1`
odd. -/
theorem equalCharacteristic_elim
    [CharP F 2]
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (B : WildQuadraticBoundaryFormula formula boundary chiCorrection
      tauCorrection compatibility) : False := by
  have htOdd := quadraticBreak_odd_equalCharacteristic F K
    V.correction.degree_eq_two V.correction.residueDegree_eq_one t ht.1 ht.2
  exact (Nat.odd_add_one.mp B.exceptionalCondition.2) htOdd

end WildQuadraticBoundaryFormula

/-- Exceptional wild-quadratic boundary cancellation.  The exact error
formula selects the two actual translated correction records, so their
denominators, numerators, affine coefficients, positive orientations, and
representative transports are retained.  Equal characteristic is excluded
by break parity; in mixed characteristic the remaining residue phase is the
explicit plus-sign Artin--Schreier identity. -/
theorem wildQuadratic_boundary
    (ht : PrimeCyclicExtension.IsLowerBreak F K t)
    (formula : WildQuadraticErrorFormula hDeltaF hDeltaK rows coordinates
      refinements)
    (boundary : WildQuadraticBoundaryData (ResidueField F))
    (chiCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
      V.psiF V.chiFData q)
    (tauCorrection : WildQuadraticRefinementCorrection F (ResidueField F)
      V.psiF V.tauData q)
    (compatibility : WildQuadraticBoundaryCompatibility
      (V := V) (A := A) boundary)
    (hchi : refinements.chiCorrection = some chiCorrection)
    (htau : refinements.tauCorrection = some tauCorrection) :
    errorTerm F K DeltaF DeltaK V.chiFData.character V.psiF.character = 1 := by
  let B := wildQuadratic_errorFormula_boundary formula boundary chiCorrection
    tauCorrection compatibility hchi htau
  by_cases hEqual : (2 : F) = 0
  · letI : CharP F 2 :=
      (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 hEqual
    exact (B.equalCharacteristic_elim ht).elim
  · exact B.exact_formula.trans (boundary.value_eq_one q)

end RealBoundary

end

end LanglandsFirstMainLemma
