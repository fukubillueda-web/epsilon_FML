import LanglandsFirstMainLemma.LocalField.MonogenicUniformizer
import LanglandsFirstMainLemma.Ramification.PrimeCyclicExtension
import LanglandsFirstMainLemma.Ramification.PrimeDegreeDichotomy
import LanglandsFirstMainLemma.Ramification.LowerGroups
import LanglandsFirstMainLemma.Ramification.NormBelowBreak

/-!
# Preparation for ramified cyclic extensions of prime degree

This file assembles the common local-field data used by every ramified
prime-cyclic case. Ramifiedness first forces residue degree one. The
resulting trivial residue extension makes the full Galois group equal to
`G₀`; the prime-order filtration therefore has its canonical unique
nonnegative lower break. The residue-degree-one monogenic-uniformizer
theorem supplies an integral uniformizer which generates the upper valuation
ring over the lower one.

The tame and wild specializations are consequences of this package. At a
positive break the existing faithful positive ramification coordinate forces
the prime degree to equal the residue characteristic. At break zero the
faithful multiplicative coordinate embeds the prime-order graded
ramification group into the units of the residue field, whose order is prime
to the residue characteristic. Thus tame ramification has break zero and
wild ramification has positive break.

No character, conductor, stationary parameter, Hasse comparison, or epsilon
factor data occurs here.
-/

noncomputable section

namespace LanglandsFirstMainLemma

section ResidueDegreeOne

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Finite F K] [IsGalois F K]

/-- If the residue degree is one, the zeroth lower ramification group is the
full Galois group. Indeed, residue degree one makes the canonical residue
field map surjective, while every `F`-automorphism acts trivially on its
image. -/
theorem lowerRamificationGroup_zero_eq_top_of_residueDegree_eq_one
    (hres : residueDegree F K = 1) :
    lowerRamificationGroup F K 0 = ⊤ := by
  rw [lowerRamificationGroup_zero_eq_ker_galoisResidueAction]
  apply eq_top_iff.mpr
  intro σ _
  rw [MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro z
  obtain ⟨xi, rfl⟩ :=
    extensionResidueMap_surjective_of_residueDegree_eq_one F K hres z
  obtain ⟨a, rfl⟩ := residueMap_surjective F xi
  have halg :
      residueMap K
          (algebraMap (ringOfIntegers F) (ringOfIntegers K) a) =
        extensionResidueMap F K (residueMap F a) :=
    (Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (ValuativeRel.valuation F) (ValuativeRel.valuation K) a).symm
  rw [← halg, galoisResidueAction_residue]
  have hfix :
      galoisIntegerEquiv F K σ
          (algebraMap (ringOfIntegers F) (ringOfIntegers K) a) =
        algebraMap (ringOfIntegers F) (ringOfIntegers K) a := by
    ext
    change σ (algebraMap F K (a : F)) = algebraMap F K (a : F)
    exact σ.commutes (a : F)
  rw [hfix]
  rfl

end ResidueDegreeOne

section RamifiedPrimeCyclic

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- The reusable preparation data for a ramified cyclic extension of prime
degree. The break is the canonical index selected from `G₀ = G`; the
uniformizer is integral and retains both its uniformizer proof and its
valuation-ring generation proof. -/
structure PrimeCyclicPreparation where
  /-- The canonical nonnegative lower break. -/
  t : ℕ
  /-- Boundary property `G_t = G` and `G_(t+1) = 1`. -/
  ht : PrimeCyclicExtension.IsLowerBreak F K t
  /-- Ramified prime degree forces residue degree one. -/
  hres : residueDegree F K = 1
  /-- A chosen integral upper uniformizer. -/
  piK : ringOfIntegers K
  /-- The chosen integral element is a uniformizer of `K`. -/
  hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K)
  /-- The chosen uniformizer generates `𝒪_K` over `𝒪_F`. -/
  hgen : Algebra.adjoin (ringOfIntegers F)
    ({piK} : Set (ringOfIntegers K)) = ⊤

namespace PrimeCyclicPreparation

/-- The depth-zero identity retained by every ramified prime-cyclic
preparation package. -/
theorem lowerRamificationGroup_zero_eq_top
    (P : PrimeCyclicPreparation F K) :
    lowerRamificationGroup F K 0 = ⊤ :=
  lowerRamificationGroup_zero_eq_top_of_residueDegree_eq_one F K P.hres

/-- The ramification index of a prepared ramified prime-cyclic extension is
its prime extension degree. -/
theorem ramificationIndex_eq_degree
    (P : PrimeCyclicPreparation F K) :
    ramificationIndex F K = Module.finrank F K := by
  have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
  rw [P.hres, mul_one] at hdegree
  exact hdegree.symm

/-- The packaged break is the canonical break selected from the packaged
depth-zero identity. -/
theorem t_eq_lowerBreakIndex (P : PrimeCyclicPreparation F K) :
    P.t = PrimeCyclicExtension.lowerBreakIndex F K
      P.lowerRamificationGroup_zero_eq_top := by
  symm
  exact PrimeCyclicExtension.lowerBreakIndex_eq F K
    P.lowerRamificationGroup_zero_eq_top P.ht

end PrimeCyclicPreparation

/-- Construct the full reusable preparation package from ramifiedness. The
residue-degree conclusion comes from the prime-degree dichotomy, the break
from the existing canonical lower-break selector, and the integral generator
from `monogenicUniformizer`. -/
noncomputable def primeCyclicPreparation
    (hram : ramificationIndex F K ≠ 1) :
    PrimeCyclicPreparation F K :=
  let hres : residueDegree F K = 1 :=
    totallyRamified_of_ramified F K hram
  let hzero : lowerRamificationGroup F K 0 = ⊤ :=
    lowerRamificationGroup_zero_eq_top_of_residueDegree_eq_one F K hres
  let t : ℕ := PrimeCyclicExtension.lowerBreakIndex F K hzero
  let ht : PrimeCyclicExtension.IsLowerBreak F K t :=
    PrimeCyclicExtension.lowerBreakIndex_isLowerBreak F K hzero
  let hex := monogenicUniformizer F K hres
  let piK : ringOfIntegers K := hex.choose
  {
    t := t
    ht := ht
    hres := hres
    piK := piK
    hpiK := hex.choose_spec.1
    hgen := hex.choose_spec.2 }

section TameBoundary

/-- A ramified prime-cyclic lower break at zero forces tame ramification.
The faithful degree-zero ramification coordinate embeds the prime-order
graded group into the residue-field units. Hence the extension degree
divides `q_K - 1`, while the residue characteristic divides `q_K`; these
consecutive numbers are coprime. -/
theorem isTamelyRamified_of_isLowerBreak_zero
    (hres : residueDegree F K = 1)
    (piK : ringOfIntegers K)
    (hpiK : (ValuativeRel.valuation K).IsUniformizer (piK : K))
    (hgen : Algebra.adjoin (ringOfIntegers F)
      ({piK} : Set (ringOfIntegers K)) = ⊤)
    (ht : PrimeCyclicExtension.IsLowerBreak F K 0) :
    IsTamelyRamified F K := by
  let σ0 : lowerRamificationGroup F K 0 :=
    ⟨PrimeCyclicExtension.generator F K, by
      have htop : lowerRamificationGroup F K 0 = ⊤ := by
        simpa only [Nat.cast_zero] using ht.1
      rw [htop]
      trivial⟩
  let σ0bar : LowerRamificationGraded F K 0 :=
    lowerRamificationGradedMk F K 0 σ0
  let u : UnitGradedPiece K 0 :=
    ramificationUnitGradedHom F K 0 piK hpiK hgen σ0bar

  have hgradedInjective :
      Function.Injective (lowerRamificationGradedMk F K 0) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    change (lowerRamificationQuotientMk F K
      (show (0 : ℤ) ≤ 0 + 1 by omega)).ker = ⊥
    rw [lowerRamificationQuotientMk_ker]
    ext σ
    rw [mem_lowerRamificationGroupInside, Subgroup.mem_bot]
    change ((σ : lowerRamificationGroup F K 0) : Gal(K/F)) ∈
        lowerRamificationGroup F K 1 ↔ σ = 1
    have hbot : lowerRamificationGroup F K 1 = ⊥ := by
      simpa only [Nat.cast_zero, zero_add] using ht.2
    rw [hbot, Subgroup.mem_bot]
    constructor
    · intro hσ
      exact Subtype.ext hσ
    · intro hσ
      exact congrArg Subtype.val hσ

  have hσ0barOrder : orderOf σ0bar = Module.finrank F K := by
    calc
      orderOf σ0bar = orderOf σ0 :=
        orderOf_injective (lowerRamificationGradedMk F K 0)
          hgradedInjective σ0
      _ = orderOf (PrimeCyclicExtension.generator F K) := by
        rw [← orderOf_submonoid σ0]
      _ = Module.finrank F K :=
        PrimeCyclicExtension.orderOf_generator F K

  have huOrder : orderOf u = Module.finrank F K := by
    change orderOf
      (ramificationUnitGradedHom F K 0 piK hpiK hgen σ0bar) = _
    rw [orderOf_injective
      (ramificationUnitGradedHom F K 0 piK hpiK hgen)
      (ramificationUnitGradedHom_injective F K 0 piK hpiK hgen)]
    exact hσ0barOrder

  have hdegreeCard :
      Module.finrank F K ∣ Nat.card (UnitGradedPiece K 0) := by
    rw [← huOrder]
    exact orderOf_dvd_natCard u
  have hgradedCard :
      Nat.card (UnitGradedPiece K 0) = residueCard K - 1 := by
    change Nat.card (UnitFiltrationQuotient K 0 1 (by omega)) =
      residueCard K - 1
    simpa [Nat.one_ne_zero] using
      (unitFiltrationQuotient_card K (show 0 ≤ 1 by omega))
  rw [hgradedCard] at hdegreeCard

  have hramIndex : ramificationIndex F K = Module.finrank F K := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
    rw [hres, mul_one] at hdegree
    exact hdegree.symm

  intro hpRamification
  have hpDegree : residueCharacteristic F ∣ Module.finrank F K := by
    rwa [← hramIndex]
  have hpQsub : residueCharacteristic F ∣ residueCard K - 1 :=
    hpDegree.trans hdegreeCard

  have hpQ : residueCharacteristic F ∣ residueCard K := by
    rw [← residueCharacteristic_extension_eq F K]
    change ringChar (ResidueField K) ∣ residueCard K
    letI : Fintype (ResidueField K) := residueFieldFintype K
    letI : Fact (Nat.Prime (ringChar (ResidueField K))) :=
      ⟨CharP.prime_ringChar (ResidueField K)⟩
    exact (prime_dvd_char_iff_dvd_card
      (R := ResidueField K) (ringChar (ResidueField K))).mp (dvd_refl _)

  have hQpos : 1 ≤ residueCard K := (one_lt_residueCard K).le
  have hconsecutive : Nat.Coprime (residueCard K - 1) (residueCard K) :=
    (Nat.coprime_self_sub_left hQpos).mpr
      (Nat.coprime_one_left (residueCard K))
  have hpCoprime : Nat.Coprime (residueCharacteristic F) (residueCard K) :=
    Nat.Coprime.of_dvd_left hpQsub hconsecutive
  have hpOne : residueCharacteristic F = 1 :=
    Nat.eq_one_of_dvd_coprimes hpCoprime (dvd_refl _) hpQ
  exact (residueCharacteristic_prime F).ne_one hpOne

end TameBoundary

namespace PrimeCyclicPreparation

/-- Tame ramification forces the packaged canonical lower break to be zero. -/
theorem t_eq_zero_of_isTamelyRamified
    (P : PrimeCyclicPreparation F K)
    (htame : IsTamelyRamified F K) :
    P.t = 0 := by
  by_contra htzero
  have htpos : 0 < P.t := Nat.pos_of_ne_zero htzero
  have hchar : residueCharacteristic F = Module.finrank F K :=
    residueCharacteristic_eq_degree_of_positive_isLowerBreak F K
      P.ht htpos P.piK P.hpiK P.hgen
  apply htame
  rw [P.ramificationIndex_eq_degree, ← hchar]

/-- Tame ramification exposes the manuscript boundary `G₀ = G`,
`G₁ = 1` as `IsLowerBreak F K 0`. -/
theorem isLowerBreak_zero_of_isTamelyRamified
    (P : PrimeCyclicPreparation F K)
    (htame : IsTamelyRamified F K) :
    PrimeCyclicExtension.IsLowerBreak F K 0 := by
  simpa only [t_eq_zero_of_isTamelyRamified F K P htame] using P.ht

/-- Wild ramification forces the packaged canonical lower break to be
strictly positive. -/
theorem t_pos_of_isWildlyRamified
    (P : PrimeCyclicPreparation F K)
    (hwild : IsWildlyRamified F K) :
    0 < P.t := by
  by_contra htpos
  have htzero : P.t = 0 := Nat.eq_zero_of_not_pos htpos
  have hbreakZero : PrimeCyclicExtension.IsLowerBreak F K 0 := by
    simpa only [htzero] using P.ht
  have htame : IsTamelyRamified F K :=
    isTamelyRamified_of_isLowerBreak_zero F K
      P.hres P.piK P.hpiK P.hgen hbreakZero
  exact htame hwild

end PrimeCyclicPreparation

/-- The wild specialization retains the complete common package and adds
only positivity of its canonical break. -/
structure WildPrimeCyclicPreparation extends PrimeCyclicPreparation F K where
  /-- Wild ramification has a positive lower break. -/
  htpos : 0 < t

/-- Construct the wild ramified preparation package. Its inherited data
exposes `t`, `IsLowerBreak t`, residue degree one, and the integral monogenic
uniformizer; the additional field records `0 < t`. -/
noncomputable def wildPrimeCyclicPreparation
    (hram : ramificationIndex F K ≠ 1)
    (hwild : IsWildlyRamified F K) :
    WildPrimeCyclicPreparation F K := by
  let P := primeCyclicPreparation F K hram
  exact {
    toPrimeCyclicPreparation := P
    htpos := PrimeCyclicPreparation.t_pos_of_isWildlyRamified F K P hwild }

end RamifiedPrimeCyclic

end LanglandsFirstMainLemma
