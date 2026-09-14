import LanglandsFirstMainLemma.FiniteField.AffinePencil
import LanglandsFirstMainLemma.Cases.WildOdd.ResidualCoefficients

open scoped BigOperators

namespace LanglandsFirstMainLemma

noncomputable section

/-- **Wild odd boundary pencil.**

Specialize `affinePencil` to the certified boundary parameters
`rho = dZero⁻¹`, `sigma = gamma`, and `tau = rho * gammaZero`.  The first
factor is the inverse-Frobenius upper row, the unit-indexed factors are the
nonidentity norm rows, and the right side is the complete boundary twist
pencil. -/
theorem wildOdd_boundaryPencil
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField F) p]
    (hp : p ≠ 2)
    (hchar : residueCharacteristic F = p)
    (C : FrobeniusResidualAddCharData F p)
    (generator base : WildOddNamedCoefficientPair (ResidueField F))
    (hnonzero : ∀ j : {j : ZMod p // j ≠ 0},
      ((j : ZMod p).val : ResidueField F) +
        wildOddBoundaryDZero generator base ≠ 0) :
    letI := residueFieldFintype F
    quadraticPhase C.lower
        (wildOddBoundaryA0 F p hchar C generator base)
        (wildOddBoundaryB0 F p hchar C generator base) *
        (∏ u : (ZMod p)ˣ,
          quadraticPhase C.lower
            ((ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p) *
              wildOddBoundaryRho generator base)
            ((ZMod.castHom (dvd_refl p) (ResidueField F)) (u : ZMod p) *
              wildOddBoundaryTau generator base)) =
      ∏ j : ZMod p,
        quadraticPhase C.lower
          (1 + (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
            wildOddBoundaryRho generator base)
          (wildOddBoundarySigma generator base +
            (ZMod.castHom (dvd_refl p) (ResidueField F)) j *
              wildOddBoundaryTau generator base) := by
  letI := residueFieldFintype F
  let certificate := wildOdd_boundaryAffinePencilCertificate F p hchar C
    generator base hnonzero
  exact affinePencil hp C.lower C.lower_ne_one C.frobenius
    certificate.rho_ne_zero
    certificate.one_add_index_mul_rho_ne_zero
    certificate.a0_pow certificate.b0_pow

end

end LanglandsFirstMainLemma
