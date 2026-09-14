import LanglandsFirstMainLemma.Ramification.PrimeCyclicPreparation
import LanglandsFirstMainLemma.Ramification.NormCharacters
import LanglandsFirstMainLemma.Cases.Unramified
import LanglandsFirstMainLemma.Cases.TameOddPreparation
import LanglandsFirstMainLemma.Cases.TameQuadraticPreparation
import LanglandsFirstMainLemma.Cases.WildStablePreparation
import LanglandsFirstMainLemma.Cases.WildOdd.CorrectionPreparation
import LanglandsFirstMainLemma.Cases.WildQuadratic.RefinementPreparation

namespace LanglandsFirstMainLemma

noncomputable section

/-- **Exhaustive nonarchimedean case dispatch.**

Classify a cyclic extension of prime degree as unramified, tamely ramified
quadratic, tamely ramified of odd degree, wildly ramified quadratic, or
wildly ramified of odd degree.  In the last case, split at the exact stable
conductor boundary and invoke the corresponding completed case theorem.

This theorem contains no stationary-phase calculation: the two nonstable
wild branches only connect their public preparation APIs to their public
First Main identity consumers. -/
theorem firstMainLemma_nonarchimedean
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (DeltaF : LocalConstantFunction F)
    (DeltaK : LocalConstantFunction K)
    (hDeltaF : IsDeltaFiniteLocalConstant DeltaF)
    (hDeltaK : IsDeltaFiniteLocalConstant DeltaK)
    (chiF : LocalQuasiCharData F)
    (psiF : LocalAddCharData F) :
    letI : Finite (NormCharacter F K) :=
      primeCyclicNormCharacter_finite F K
    FirstMainIdentity F K DeltaF DeltaK chiF.character psiF.character := by
  letI : Finite (NormCharacter F K) :=
    primeCyclicNormCharacter_finite F K
  by_cases hunr : ramificationIndex F K = 1
  · obtain ⟨pi0, hpi0⟩ :=
      Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial
        (ValuativeRel.valuation F)
    let pi : Fˣ := Units.mk0 (pi0 : F) hpi0.ne_zero
    have hpi : (ValuativeRel.valuation F).IsUniformizer (pi : F) := by
      change (ValuativeRel.valuation F).IsUniformizer (pi0 : F)
      exact hpi0
    exact firstMain_unramified_dispatchReady F K DeltaF DeltaK
      hDeltaF hDeltaK hunr chiF psiF pi hpi
  · let P : PrimeCyclicPreparation F K :=
      primeCyclicPreparation F K hunr
    rcases (ramified_primeDegree_classification F K hunr).2 with
      (⟨htame, hdegree⟩ | ⟨hwild, hchar, hdegree⟩)
    · rcases hdegree with htwo | hodd
      · exact firstMain_tameQuadratic_of_isDeltaFinite F K P htame htwo
          DeltaF DeltaK hDeltaF hDeltaK chiF psiF
      · exact firstMain_tameOdd_of_isDeltaFinite F K P htame hodd
          DeltaF DeltaK hDeltaF hDeltaK chiF psiF
    · have htpos : 0 < P.t :=
        P.t_pos_of_isWildlyRamified F K hwild
      rcases hdegree with htwo | hodd
      · have hcharTwo : residueCharacteristic F = 2 := hchar.trans htwo
        letI : Fintype (ResidueField F) := residueFieldFintype F
        letI : CharP (ResidueField F) 2 := ringChar.of_eq hcharTwo
        letI : Fintype (ResidueField K) := residueFieldFintype K
        letI : CharP (ResidueField K) 2 := ringChar.of_eq
          ((residueCharacteristic_extension_eq F K).trans hcharTwo)
        apply firstMain_wildQuadratic F K P.ht htpos htwo P.hres P.piK
          P.hpiK P.hgen DeltaF DeltaK hDeltaF hDeltaK chiF psiF
        intro hm
        exact wildQuadraticHigherData P.ht htpos P.hres P.piK P.hpiK
          P.hgen htwo
          (minimalOrbitRepresentative F K P.ht P.hres P.piK P.hpiK
            P.hgen chiF)
          psiF
          (minimalOrbitRepresentative_isMinimal F K P.ht P.hres P.piK
            P.hpiK P.hgen chiF)
          hm
      · have hoddChar : residueCharacteristic F ≠ 2 := by
          intro htwoChar
          have htwoDegree : Module.finrank F K = 2 :=
            hchar.symm.trans htwoChar
          rw [htwoDegree] at hodd
          norm_num at hodd
        by_cases hstable :
            P.t + 1 ≤
              (minimalOrbitRepresentative F K P.ht P.hres P.piK P.hpiK
                P.hgen chiF).conductor / 2
        · exact firstMain_wildStable_of_isDeltaFinite F K P hwild hodd
            DeltaF DeltaK hDeltaF hDeltaK chiF psiF hstable
        · have hnonstable :
              (minimalOrbitRepresentative F K P.ht P.hres P.piK P.hpiK
                P.hgen chiF).conductor / 2 < P.t + 1 :=
            Nat.lt_of_not_ge hstable
          apply firstMain_wildOdd_nonstable F K P.ht htpos hchar.symm
            hoddChar P.hres P.piK P.hpiK P.hgen DeltaF DeltaK hDeltaF
              hDeltaK chiF psiF
          intro hm
          let chiMin := minimalOrbitRepresentative F K P.ht P.hres P.piK
            P.hpiK P.hgen chiF
          letI : CharP (ResidueField F) (Module.finrank F K) :=
            ringChar.of_eq hchar
          exact wildOddNonstableHigherData F K P.t P.ht P.hres P.piK
            P.hpiK P.hgen chiMin psiF
            (wildOddPhasePreparation F K P.t P.ht htpos hoddChar P.hres
              P.piK P.hpiK P.hgen chiMin psiF
              (minimalOrbitRepresentative_isMinimal F K P.ht P.hres P.piK
                P.hpiK P.hgen chiF)
              hm hnonstable)

end

end LanglandsFirstMainLemma
