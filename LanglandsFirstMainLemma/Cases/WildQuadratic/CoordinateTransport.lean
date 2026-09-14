import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.HighQuadratic
import LanglandsFirstMainLemma.Cases.WildQuadratic.CoefficientTable
import LanglandsFirstMainLemma.Cases.WildQuadratic.ErrorFormula

namespace LanglandsFirstMainLemma

noncomputable section

/-!
# Degree-two coordinate transport for the wild quadratic case

This file supplies the q-polymorphic interface between the actual local
Lamprecht rows and the coefficient table.  The low- and high-conductor
producers retain their source representatives separately; the declarations
below contain only their common degree-two and phase-normalization core.
-/

section PublicCertificates

variable (F K : Type)
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

/-- The q-polymorphic upper-coordinate and actual-extension-phase certificate
retained by every positive-polar wild-quadratic preparation branch. -/
structure WildQuadraticPositivePolarCoordinateTransport
    {t m : ℕ}
    (view : WildQuadraticCommonCoefficientView F K t m)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K
      view.chiFData.character view.psiF.character data phaseData
        (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view data phaseData assembly) : Prop where
  matchesCorrection :
    ∀ q : CharTwoRefinement (ResidueField F),
      WildQuadraticCoefficientData.MatchesCorrection F K view.correction
        (view.criticalInputs.toCoefficientData q)
  upperCoordinates :
    ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (view.criticalInputs.toCoefficientData q).affineCoefficient .chiK =
          some lambda →
        Nonempty
          (ActualUpperCoordinateCertificate F K view.correction q
            view.criticalInputs view.stationaryPairs
            view.tauData view.chiFData view.psiF)
  extension_phase :
    ∀ q : CharTwoRefinement (ResidueField F),
      rows.extension.criticalFactor =
        (view.criticalInputs.toCoefficientData q).phaseFactor q .chiK

/-- The complete q-polymorphic continuation retained by phase preparation.
It keeps upper-coordinate transport separate from the lower-product
certificate and retains the four actual row phases needed by the later
refinement consumer.  The computational packages are implicit so this node
does not depend on the later `WildQuadraticCommonHigherData` wrapper. -/
structure WildQuadraticPositivePolarContinuation
    {t m : ℕ}
    (view : WildQuadraticCommonCoefficientView F K t m)
    (source : view.criticalInputs.PositivePolarSource)
    {data : FirstMainComputationalData F K view.chiFData.character
      view.psiF.character}
    {phaseData : FirstMainPhaseData F K view.chiFData.character
      view.psiF.character data}
    {assembly : ExactQuadraticPhaseAssembly F K
      view.chiFData.character view.psiF.character data phaseData
        (t := t) (m := m)}
    (rows : WildQuadraticActualPhaseRows view data phaseData assembly) : Prop where
  coordinate : WildQuadraticPositivePolarCoordinateTransport F K view rows
  lowerProduct :
    ∀ (q : CharTwoRefinement (ResidueField F))
      {lambda : ResidueField F},
      (view.criticalInputs.toCoefficientData q).affineCoefficient .tauChiF =
          some lambda →
        Nonempty
          (ActualProductCoordinateCertificate F K q view.criticalInputs
            view.stationaryPairs view.tauData view.chiFData view.psiF)
  tau_phase :
    ∀ _q : CharTwoRefinement (ResidueField F),
      rows.tau.criticalFactor =
        quotientSourcePhase F view.criticalInputs.tauSource
  base_phase :
    ∀ _q : CharTwoRefinement (ResidueField F),
      rows.base.criticalFactor =
        quotientSourcePhase F view.criticalInputs.chiFSource
  twist_phase :
    ∀ q : CharTwoRefinement (ResidueField F),
      rows.twist.criticalFactor =
        (view.criticalInputs.toCoefficientData q).phaseFactor q .tauChiF

end PublicCertificates

/-! ## Common degree-two norm-polynomial core -/

/-- In degree two the exact phase-reduction norm polynomial is trace plus
norm.  This is only a presentation bridge between the two existing APIs. -/
theorem wildQuadratic_phaseReductionNormPolynomial_eq_trace_add_norm
    (F K : Type*)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    (hdegree : Module.finrank F K = 2) (x : K) :
    phaseReductionNormPolynomial F K x = trace F K x + norm F K x := by
  rw [phaseReductionNormPolynomial_eq_normPolynomialValue,
    wildQuadratic_normPolynomialValue_eq_trace_add_norm F K hdegree]

/-! ## Cross-field normalization -/

/-- In characteristic two, the raw displayed-upstairs polar relation fixes
the relative normalization of the actual upper and lower coordinates.  This
is the algebraic bridge used after the source-tied polar coefficients have
been compared; it makes no additional representative choice. -/
theorem wildQuadratic_cross_normalization_scale
    {kF kK : Type*} [Field kF] [CharP kF 2]
    [Field kK] [CharP kK 2]
    (e : kF ≃+* kK)
    (AUp : kK) (ABase : kF) (aUp : kK) (aBase : kF)
    (hAUp : aUp ^ 2 = AUp⁻¹)
    (hABase : aBase ^ 2 = ABase⁻¹)
    (hpolar : ABase = (e.symm AUp) ^ 2) :
    aBase = (e.symm aUp) ^ 2 := by
  have hsquares : aBase ^ 2 = ((e.symm aUp) ^ 2) ^ 2 := by
    rw [hABase, hpolar, ← inv_pow]
    rw [show (e.symm AUp)⁻¹ = e.symm (AUp⁻¹) by
      exact (map_inv₀ e.symm AUp).symm]
    rw [← hAUp, map_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

/-! ## Common branch matrix -/


section BranchMatrix

variable (F K : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K] [PrimeCyclicExtension F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
  {t m : ℕ}


/-- `MatchesCorrection` is q-independent once the one genuine odd-boundary
source fact has been proved.  Every nonboundary coefficient constructor is
definitionally trivial. -/
theorem wildQuadratic_matchesCorrection_of_boundary_source
    (V : WildQuadraticCommonCoefficientView F K t m)
    (hBoundary : ∀
      (rho : ResidueField F) (hrho : rho ≠ 0) (hden : 1 + rho ≠ 0)
      (tau chiF : QuotientDerivedNormalizedCriticalFunction F),
      V.criticalInputs = .boundaryOdd rho hrho hden tau chiF →
      ∃ hboundary : m = t + 1,
        residueMap K
            (wildQuadraticBoundaryRingUnit F K V.correction hboundary :
              ringOfIntegers K) = extensionResidueMap F K rho ∧
        WildQuadraticCoefficientData.boundaryNResidue F K V.correction
          hboundary = rho ^ 2) :
    ∀ q : CharTwoRefinement (ResidueField F),
      WildQuadraticCoefficientData.MatchesCorrection F K V.correction
        (V.criticalInputs.toCoefficientData q) := by
  intro q
  cases hI : V.criticalInputs with
  | boundaryOdd rho hrho hden tau chiF =>
      simpa only [WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.boundaryOddComputed,
        WildQuadraticCoefficientData.MatchesCorrection, hI] using
          hBoundary rho hrho hden tau chiF hI
  | belowMEvenTEven | belowMEvenTOdd | belowMOddTEven | belowMOddTOdd |
      boundaryEven | aboveMEvenTEven | aboveMEvenTOdd | aboveMOddTEven |
      aboveMOddTOdd =>
      simp only [hI, WildQuadraticCoefficientInputs.toCoefficientData,
        WildQuadraticCoefficientData.belowMOddTEvenComputed,
        WildQuadraticCoefficientData.belowMOddTOddComputed,
        WildQuadraticCoefficientData.aboveMEvenTOddComputed,
        WildQuadraticCoefficientData.aboveMOddTOddComputed,
        WildQuadraticCoefficientData.MatchesCorrection]

end BranchMatrix

/-! ## Normalized critical-source transport -/

section NormalizedCriticalSourceTransport

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Fintype (ResidueField E)] [CharP (ResidueField E) 2]

/-- Scaling the literal stationary ratio by an integral unit scales the
intrinsic polar coefficient by the residue of that same unit.  The two
characters may differ; equality of the additive data and the two displayed
critical depths are the only identifications used in the proof. -/
theorem wildQuadratic_polarCoefficient_of_stationaryRatio_scale
    {chi₁ chi₂ : LocalQuasiCharData E}
    (psi₁ psi₂ : LocalAddCharData E) (hpsi : psi₁ = psi₂)
    (d₁ d₂ : ℕ) (hm₁ : chi₁.conductor = 2 * d₁ + 1)
    (hm₂ : chi₂.conductor = 2 * d₂ + 1)
    (hlarge₁ : 1 < chi₁.conductor) (hlarge₂ : 1 < chi₂.conductor)
    (Gamma₁ : AdmissibleGamma E chi₁ psi₁)
    (Gamma₂ : AdmissibleGamma E chi₂ psi₂) (delta : Eˣ)
    (hdelta₁ : ord E (delta : E) = ((d₁ : ℤ) : WithTop ℤ))
    (hdelta₂ : ord E (delta : E) = ((d₂ : ℤ) : WithTop ℤ))
    (beta₁ : lattice E ((chi₁.conductor : ℤ) - chi₁.conductor))
    (hbeta₁ : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi₁ d₁ hm₁ hlarge₁).int_le_conductor
          chi₁.conductor) beta₁ =
      stationaryNumeratorClass E chi₁ psi₁ chi₁.conductor
        (criticalPolar_stationaryDepth E chi₁ d₁ hm₁ hlarge₁)
          Gamma₁ Gamma₁.property)
    (beta₂ : lattice E ((chi₂.conductor : ℤ) - chi₂.conductor))
    (hbeta₂ : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi₂ d₂ hm₂ hlarge₂).int_le_conductor
          chi₂.conductor) beta₂ =
      stationaryNumeratorClass E chi₂ psi₂ chi₂.conductor
        (criticalPolar_stationaryDepth E chi₂ d₂ hm₂ hlarge₂)
          Gamma₂ Gamma₂.property)
    (u : unitGroup E)
    (hratio : (beta₂ : E) / ((Gamma₂ : Eˣ) : E) =
      ((u : Eˣ) : E) * ((beta₁ : E) / ((Gamma₁ : Eˣ) : E))) :
    criticalPolarCoefficient E chi₂ psi₂ d₂ hm₂ hlarge₂ Gamma₂ delta hdelta₂
        (absoluteTraceChar (ResidueField E))
        (absoluteTraceChar_ne_one (ResidueField E)) =
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) *
        criticalPolarCoefficient E chi₁ psi₁ d₁ hm₁ hlarge₁ Gamma₁ delta
          hdelta₁ (absoluteTraceChar (ResidueField E))
            (absoluteTraceChar_ne_one (ResidueField E)) := by
  subst psi₂
  let psi0 := absoluteTraceChar (ResidueField E)
  let hpsi0 := absoluteTraceChar_ne_one (ResidueField E)
  let phi₁ := criticalPolarAddChar E chi₁ psi₁ d₁ hm₁ hlarge₁ Gamma₁ delta
    hdelta₁
  let phi₂ := criticalPolarAddChar E chi₂ psi₁ d₂ hm₂ hlarge₂ Gamma₂ delta
    hdelta₂
  have hphi : phi₂ = phi₁.mulShift
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) := by
    apply AddChar.ext
    intro x
    rw [AddChar.mulShift_apply]
    let tx : E := (teichmuller E x : E)
    have htx : tx ∈ lattice E 0 :=
      (mem_lattice_zero_iff E).2 (teichmuller E x).property
    let ux : E := ((u : Eˣ) : E) * tx
    have hu : ((u : Eˣ) : E) ∈ lattice E 0 :=
      (mem_lattice_zero_iff E).2
        (((unitGroupMulEquivRingOfIntegers E u : (ringOfIntegers E)ˣ) :
          ringOfIntegers E).property)
    have hux : ux ∈ lattice E 0 := mul_mem_lattice E hu htx
    have hreduce : reduce E ux hux =
        ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) * x := by
      change residueMap E
        (((unitGroupMulEquivRingOfIntegers E u : (ringOfIntegers E)ˣ) :
          ringOfIntegers E) * teichmuller E x) = _
      rw [map_mul, ← residueUnits_coe, residueMap_teichmuller]
    have htwo := criticalPolarAddChar_integral_lift E chi₂ psi₁ d₂ hm₂
      hlarge₂ Gamma₂ delta hdelta₂ beta₂ hbeta₂ tx htx
    have hone := criticalPolarAddChar_integral_lift E chi₁ psi₁ d₁ hm₁
      hlarge₁ Gamma₁ delta hdelta₁ beta₁ hbeta₁ ux hux
    rw [show reduce E tx htx = x from residueMap_teichmuller E x] at htwo
    rw [hreduce] at hone
    dsimp only [phi₁, phi₂] at htwo hone ⊢
    rw [htwo, hone]
    congr 2
    dsimp only [ux]
    calc
      (beta₂ : E) * (delta : E) ^ 2 * tx / ((Gamma₂ : Eˣ) : E) =
          ((beta₂ : E) / ((Gamma₂ : Eˣ) : E)) *
            (delta : E) ^ 2 * tx := by
        field_simp [AdmissibleGamma.coe_ne_zero Gamma₂]
      _ = (((u : Eˣ) : E) *
          ((beta₁ : E) / ((Gamma₁ : Eˣ) : E))) *
            (delta : E) ^ 2 * tx := by rw [hratio]
      _ = (beta₁ : E) * (delta : E) ^ 2 *
          (((u : Eˣ) : E) * tx) / ((Gamma₁ : Eˣ) : E) := by
        field_simp [AdmissibleGamma.coe_ne_zero Gamma₁]
  change finiteAddCharCoefficient psi0 hpsi0 phi₂ =
    ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) *
      finiteAddCharCoefficient psi0 hpsi0 phi₁
  rw [hphi, finiteAddCharCoefficient_mulShift]
  ring

namespace QuotientDerivedNormalizedCriticalFunction

/-- Integral unit carrying the normalized coordinate of `target` to the
normalized coordinate of `source`.  The conductor equality is retained in
the index because it is exactly what makes the delta ratio integral. -/
def normalizedDeltaRatioUnit
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = target.chi.conductor) : unitGroup E := by
  have hd : source.d = target.d := by
    have hs := source.conductor_eq
    have ht := target.conductor_eq
    omega
  let ratio : Eˣ := source.delta / target.delta
  refine ⟨ratio, (mem_unitGroup_iff_ord_eq_zero E ratio).2 ?_⟩
  simp only [ratio, Units.val_div_eq_div_val]
  rw [ord_div, source.delta_order, target.delta_order, hd]
  simp

@[simp]
theorem normalizedDeltaRatioUnit_coe
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = target.chi.conductor) :
    (((normalizedDeltaRatioUnit source target hconductor : unitGroup E) : Eˣ) : E) =
      (source.delta : E) / (target.delta : E) := by
  simp [normalizedDeltaRatioUnit]

/-- The delta ratio really transports the target normalized coordinate to
the source normalized coordinate; no residue-level choice is involved. -/
theorem normalizedDeltaRatioUnit_scale
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = target.chi.conductor) :
    source.delta = criticalPolarScaledCoordinate E
      (normalizedDeltaRatioUnit source target hconductor) target.delta := by
  apply Units.ext
  simp only [criticalPolarScaledCoordinate, Units.val_mul,
    normalizedDeltaRatioUnit_coe]
  exact (div_mul_cancel₀ (source.delta : E)
    (Units.ne_zero target.delta)).symm

/-- Residual scale from the target normalized coordinate to the source
normalized coordinate. -/
def normalizedDeltaRatioResidue
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = target.chi.conductor) :
    ResidueField E :=
  ((residueUnits E (normalizedDeltaRatioUnit source target hconductor) :
    (ResidueField E)ˣ) : ResidueField E)

theorem normalizedDeltaRatioResidue_ne_zero
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = target.chi.conductor) :
    normalizedDeltaRatioResidue source target hconductor ≠ 0 :=
  Units.ne_zero
    (residueUnits E (normalizedDeltaRatioUnit source target hconductor))

/-- If the target stationary ratio is the source ratio multiplied by `u`,
then the square of the residual ratio of their independently normalized
critical coordinates is exactly the residue of `u`. -/
theorem normalizedDeltaRatioResidue_sq_of_stationaryRatio_scale
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hpsi : source.psi = target.psi)
    (hconductor : source.chi.conductor = target.chi.conductor)
    (u : unitGroup E)
    (hratio : (target.beta : E) / ((target.Gamma : Eˣ) : E) =
      ((u : Eˣ) : E) *
        ((source.beta : E) / ((source.Gamma : Eˣ) : E))) :
    normalizedDeltaRatioResidue source target hconductor ^ 2 =
      ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) := by
  have hd : source.d = target.d := by
    have hs := source.conductor_eq
    have ht := target.conductor_eq
    omega
  let rhoLift := normalizedDeltaRatioUnit source target hconductor
  let rho := normalizedDeltaRatioResidue source target hconductor
  have hcoordinate : source.delta =
      criticalPolarScaledCoordinate E rhoLift target.delta := by
    exact normalizedDeltaRatioUnit_scale source target hconductor
  have hdelta : ord E (target.delta : E) =
      ((source.d : ℤ) : WithTop ℤ) := by
    rw [target.delta_order, hd]
  have hcoeff := wildQuadratic_polarCoefficient_of_stationaryRatio_scale
    source.psi target.psi hpsi source.d target.d source.conductor_eq
      target.conductor_eq source.conductor_gt_one target.conductor_gt_one
        source.Gamma target.Gamma target.delta hdelta target.delta_order
          source.beta source.beta_class target.beta target.beta_class u hratio
  let coeff := criticalPolarCoefficient E source.chi source.psi source.d
    source.conductor_eq source.conductor_gt_one source.Gamma target.delta hdelta
      (absoluteTraceChar (ResidueField E))
        (absoluteTraceChar_ne_one (ResidueField E))
  have hu : ((residueUnits E u : (ResidueField E)ˣ) : ResidueField E) *
      coeff = 1 := by
    rw [← target.polar_eq_one]
    simpa only [coeff] using hcoeff.symm
  have hscale := criticalPolarCoefficient_scaleCoordinate E source.chi
    source.psi source.d source.conductor_eq source.conductor_gt_one source.Gamma
      target.delta hdelta (absoluteTraceChar (ResidueField E))
        (absoluteTraceChar_ne_one (ResidueField E)) rhoLift
  have hrho : rho ^ 2 * coeff = 1 := by
    rw [← source.polar_eq_one]
    simpa only [rho, normalizedDeltaRatioResidue, coeff, hcoordinate] using
      hscale.symm
  have hcoeffne : coeff ≠ 0 := criticalPolarCoefficient_ne_zero E source.chi
    source.psi source.d source.conductor_eq source.conductor_gt_one source.Gamma
      target.delta hdelta (absoluteTraceChar (ResidueField E))
        (absoluteTraceChar_ne_one (ResidueField E))
  apply mul_right_cancel₀ hcoeffne
  simpa only [rho] using hrho.trans hu.symm

/-- In characteristic two, equality of the squares of two proposed
normalized delta residues determines the residue itself. -/
theorem normalizedDeltaRatioResidue_eq_of_sq
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = target.chi.conductor)
    (s : ResidueField E)
    (hs : normalizedDeltaRatioResidue source target hconductor ^ 2 = s ^ 2) :
    normalizedDeltaRatioResidue source target hconductor = s := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

/-- An exact stationary-ratio unit scale determines the corresponding
normalized coordinate scale as soon as its residue square is identified. -/
theorem normalizedDeltaRatioResidue_eq_of_scale
    (source target : QuotientDerivedNormalizedCriticalFunction E)
    (hpsi : source.psi = target.psi)
    (hconductor : source.chi.conductor = target.chi.conductor)
    (u : unitGroup E)
    (hratio : (target.beta : E) / ((target.Gamma : Eˣ) : E) =
      ((u : Eˣ) : E) *
        ((source.beta : E) / ((source.Gamma : Eˣ) : E)))
    (s : ResidueField E)
    (hresidue : ((residueUnits E u : (ResidueField E)ˣ) :
      ResidueField E) = s ^ 2) :
    normalizedDeltaRatioResidue source target hconductor = s := by
  apply normalizedDeltaRatioResidue_eq_of_sq
  rw [normalizedDeltaRatioResidue_sq_of_stationaryRatio_scale
    source target hpsi hconductor u hratio, hresidue]

/-- The common product lift is the Teichmüller lift of the displayed
product argument. -/
noncomputable def normalizedCommonProductLift (z : ResidueField E) :
    lattice E 0 :=
  ⟨(teichmuller E z : E),
    (mem_lattice_zero_iff E).2 (teichmuller E z).property⟩

@[simp]
theorem normalizedCommonProductLift_coe (z : ResidueField E) :
    (normalizedCommonProductLift z : E) = (teichmuller E z : E) :=
  rfl

theorem normalizedCommonProductLift_reduce (z : ResidueField E) :
    reduce E (normalizedCommonProductLift z : E)
      (normalizedCommonProductLift z).property = z := by
  exact residueMap_teichmuller E z

/-- Given the product lift, the source lift is obtained by the inverse of
the exact normalized delta ratio.  Hence the two field displacements, not
merely their reductions, are equal. -/
noncomputable def normalizedCommonSourceLift
    (source product : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = product.chi.conductor)
    (z : ResidueField E) : lattice E 0 := by
  let r := normalizedDeltaRatioUnit source product hconductor
  let rinv : unitGroup E := r⁻¹
  have hrinv : ((rinv : Eˣ) : E) ∈ lattice E 0 :=
    (mem_lattice_zero_iff E).2
      (((unitGroupMulEquivRingOfIntegers E rinv : (ringOfIntegers E)ˣ) :
        ringOfIntegers E).property)
  exact ⟨((rinv : Eˣ) : E) * (teichmuller E z : E),
    mul_mem_lattice E hrinv
      ((mem_lattice_zero_iff E).2 (teichmuller E z).property)⟩

@[simp]
theorem normalizedCommonSourceLift_coe
    (source product : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = product.chi.conductor)
    (z : ResidueField E) :
    (normalizedCommonSourceLift source product hconductor z : E) =
      ((((normalizedDeltaRatioUnit source product hconductor)⁻¹ :
        unitGroup E) : Eˣ) : E) * (teichmuller E z : E) := by
  rfl

/-- Reduction of the explicit source lift is multiplication by the inverse
normalized delta residue. -/
theorem normalizedCommonSourceLift_reduce
    (source product : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = product.chi.conductor)
    (z : ResidueField E) :
    reduce E (normalizedCommonSourceLift source product hconductor z : E)
        (normalizedCommonSourceLift source product hconductor z).property =
      (normalizedDeltaRatioResidue source product hconductor)⁻¹ * z := by
  change residueMap E
    (((unitGroupMulEquivRingOfIntegers E
        ((normalizedDeltaRatioUnit source product hconductor)⁻¹) :
          (ringOfIntegers E)ˣ) : ringOfIntegers E) * teichmuller E z) = _
  rw [map_mul, ← residueUnits_coe, residueMap_teichmuller]
  rw [map_inv]
  rw [Units.val_inv_eq_inv_val]
  rfl

/-- The explicit source and product lifts give literally the same critical
principal unit. -/
theorem criticalUnitAtLift_normalizedCommonSourceLift
    (source product : QuotientDerivedNormalizedCriticalFunction E)
    (hconductor : source.chi.conductor = product.chi.conductor)
    (z : ResidueField E) :
    criticalUnitAtLift source
        (normalizedCommonSourceLift source product hconductor z) =
      criticalUnitAtLift product (normalizedCommonProductLift z) := by
  let r := normalizedDeltaRatioUnit source product hconductor
  have hdelta : source.delta = (r : Eˣ) * product.delta := by
    simpa only [r, criticalPolarScaledCoordinate] using
      normalizedDeltaRatioUnit_scale source product hconductor
  have hunit : source.delta * ((r⁻¹ : unitGroup E) : Eˣ) =
      product.delta := by
    rw [hdelta]
    rw [show ((r⁻¹ : unitGroup E) : Eˣ) = (r : Eˣ)⁻¹ by rfl]
    simp [mul_assoc, mul_comm]
  apply Units.ext
  simp only [criticalUnitAtLift_coe, normalizedCommonSourceLift_coe,
    normalizedCommonProductLift_coe]
  change 1 + (source.delta : E) *
      ((((r⁻¹ : unitGroup E) : Eˣ) : E) * (teichmuller E z : E)) = _
  rw [← mul_assoc, ← Units.val_mul, hunit]

end QuotientDerivedNormalizedCriticalFunction

namespace ProductDominantCoordinates

/-- Construct the dominant-range primitive coordinates from the exact
normalized delta ratio.  The argument hypothesis is purely residual; the
constructor supplies all integral lifts and the literal common-unit
identity. -/
noncomputable def ofNormalizedDeltaRatio
    (product dominant : QuotientDerivedNormalizedCriticalFunction E)
    (productArg dominantArg : ResidueField E → ResidueField E)
    (hconductor : dominant.chi.conductor = product.chi.conductor)
    (hargument : ∀ z, productArg z =
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue
        dominant product hconductor * dominantArg z) :
    ProductDominantCoordinates E product dominant productArg dominantArg where
  productLift := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonProductLift
      (productArg z)
  dominantLift := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonSourceLift
      dominant product hconductor (productArg z)
  product_reduce := fun z =>
    QuotientDerivedNormalizedCriticalFunction.normalizedCommonProductLift_reduce
      (productArg z)
  dominant_reduce := by
    intro z
    rw [QuotientDerivedNormalizedCriticalFunction.normalizedCommonSourceLift_reduce]
    rw [hargument z]
    field_simp [
      QuotientDerivedNormalizedCriticalFunction.normalizedDeltaRatioResidue_ne_zero
        dominant product hconductor]
  commonUnit := fun z =>
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_normalizedCommonSourceLift
      dominant product hconductor (productArg z)

end ProductDominantCoordinates


end NormalizedCriticalSourceTransport

/-! ## Common upper lift and unit -/

section CommonUpperPoint

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- The actual principal unit `1 + u * (delta * zLift)` used by both the low
and high upper-coordinate producers.  The producer supplies precisely the
positive-depth estimate; no stronger representative precision is hidden in
this definition. -/
noncomputable def wildQuadraticTwistedCriticalUnit
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (upperLift : lattice K 0)
    (hmem : (C.u : K) * ((upper.delta : K) * (upperLift : K)) ∈
      lattice K 1) : Kˣ :=
  (positiveUnitOfLattice K (by omega : 0 < 1)
    ⟨(C.u : K) * ((upper.delta : K) * (upperLift : K)), hmem⟩ :
      unitFiltration K 1)

@[simp]
theorem wildQuadraticTwistedCriticalUnit_coe
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (upperLift : lattice K 0)
    (hmem : (C.u : K) * ((upper.delta : K) * (upperLift : K)) ∈
      lattice K 1) :
    (wildQuadraticTwistedCriticalUnit C upper upperLift hmem : K) =
      1 + (C.u : K) * ((upper.delta : K) * (upperLift : K)) := by
  exact coe_positiveUnitOfLattice K (by omega : 0 < 1)
    ⟨(C.u : K) * ((upper.delta : K) * (upperLift : K)), hmem⟩

/-- Assemble one primitive upper point from its two proved residual
coordinates.  This constructor fixes the common principal unit once and
prevents the low and high branches from making independent unit choices. -/
noncomputable def ActualUpperCoordinatePoint.ofTwistedCriticalUnit
    {T m : ℕ}
    (C : WildQuadraticCommonCorrectionData F K T m)
    (S : WildQuadraticSelectedStationaryPairs F K)
    (I : WildQuadraticCoefficientInputs F)
    (tauData chiFData : LocalQuasiCharData F)
    (psiF : LocalAddCharData F)
    (upper : QuotientDerivedNormalizedCriticalFunction K)
    (zK : ResidueField K) (p qcoord : ResidueField F)
    (upperLift : lattice K 0)
    (upper_reduce : reduce K (upperLift : K) upperLift.property = zK)
    (hmem : (C.u : K) * ((upper.delta : K) * (upperLift : K)) ∈
      lattice K 1)
    (chiF_coordinate : ActualLowerStationaryCoordinate F I.chiFSource
      chiFData psiF S.chiF p
        (normUnits F K
          (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
            upper upperLift)))
    (tau_coordinate : ActualLowerStationaryCoordinate F I.tauSource
      tauData psiF S.tau qcoord
        (normUnits F K
          (wildQuadraticTwistedCriticalUnit C upper upperLift hmem))) :
    ActualUpperCoordinatePoint F K C S I tauData chiFData psiF upper
      zK p qcoord where
  upperLift := upperLift
  upper_reduce := upper_reduce
  uxUnit := wildQuadraticTwistedCriticalUnit C upper upperLift hmem
  uxUnit_coe := wildQuadraticTwistedCriticalUnit_coe C upper upperLift hmem
  chiF_coordinate := chiF_coordinate
  tau_coordinate := tau_coordinate

end CommonUpperPoint

/-! ## Common primitive lower-coordinate helpers -/

section PrimitiveLowerCoordinates

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]

/-- Build a primitive lower critical coordinate from the actual field
displacement.  The caller supplies only the justified integrality and
reduction of `y / W.delta`; the exact local unit is then forced, with no
replacement of the stationary quotient representative. -/
theorem wildQuadratic_actualLowerCritical_of_displacement
    (W : QuotientDerivedNormalizedCriticalFunction F)
    (data : LocalQuasiCharData F) (psi : LocalAddCharData F)
    (P : WildQuadraticStationaryPair F)
    (hpair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      F W P)
    (hlocal : QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
      F W data psi)
    (z : ResidueField F) (y : F)
    (hy : y / (W.delta : F) ∈ lattice F 0)
    (hreduce : reduce F (y / (W.delta : F)) hy = z)
    (v : Fˣ) (hv : (v : F) = 1 + y) :
    ActualLowerStationaryCoordinate F (some W) data psi P z v := by
  refine .critical W rfl hpair hlocal
    ⟨y / (W.delta : F), hy⟩ hreduce ?_
  apply Units.ext
  rw [QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_coe, hv]
  field_simp [Units.ne_zero W.delta]

/-- The field-valued norm of the actual normalized upper critical unit is
the exact norm polynomial at its retained displacement. -/
theorem wildQuadratic_norm_criticalUnitAtLift_coe
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    (W : QuotientDerivedNormalizedCriticalFunction K)
    (lift : lattice K 0) :
    ((normUnits F K
      (QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift
        W lift) : Fˣ) : F) =
      1 + phaseReductionNormPolynomial F K
        ((W.delta : K) * (lift : K)) := by
  rw [coe_normUnits,
    QuotientDerivedNormalizedCriticalFunction.criticalUnitAtLift_coe]
  simp only [phaseReductionNormPolynomial]
  ring

/-- The same exact norm-polynomial identity for the selected twisted upper
principal unit.  Its positive-depth proof is retained explicitly. -/
theorem wildQuadratic_norm_twistedCriticalUnit_coe
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [Fintype (ResidueField K)] [CharP (ResidueField K) 2]
    {T m : ℕ} (C : WildQuadraticCommonCorrectionData F K T m)
    (W : QuotientDerivedNormalizedCriticalFunction K)
    (lift : lattice K 0)
    (hmem : (C.u : K) * ((W.delta : K) * (lift : K)) ∈ lattice K 1) :
    ((normUnits F K
      (wildQuadraticTwistedCriticalUnit C W lift hmem) : Fˣ) : F) =
      1 + phaseReductionNormPolynomial F K
        ((C.u : K) * ((W.delta : K) * (lift : K))) := by
  rw [coe_normUnits, wildQuadraticTwistedCriticalUnit_coe]
  simp only [phaseReductionNormPolynomial]
  ring

end PrimitiveLowerCoordinates



/-! ## Exact phases from primitive coordinate certificates -/

section DirectCertificatePhases

variable {F K : Type}
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [Fintype (ResidueField F)] [CharP (ResidueField F) 2]
  [Fintype (ResidueField K)] [CharP (ResidueField K) 2]

/-- The primitive lower-product certificate computes the exact table phase
of its retained product source.  This direct form avoids making an unrelated
choice of a derived source. -/
theorem ActualProductCoordinateCertificate.phase_eq_table
    {q : CharTwoRefinement (ResidueField F)}
    {I : WildQuadraticCoefficientInputs F}
    {S : WildQuadraticSelectedStationaryPairs F K}
    {tauData chiFData : LocalQuasiCharData F}
    {psiF : LocalAddCharData F}
    (C : ActualProductCoordinateCertificate F K q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .tauChiF = some lambda) :
    QuotientDerivedNormalizedCriticalFunction.phase F C.product =
      (I.toCoefficientData q).phaseFactor q .tauChiF := by
  have hfun : ∀ z,
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
          F C.product z =
        (I.toCoefficientData q).function q .tauChiF z := by
    intro z
    let D := I.toCoefficientData q
    let s := D.lowerProductScaleValue
    let w : ResidueField F := s⁻¹ * z
    have hscale : D.lowerProductScale w = z := by
      rw [D.lowerProductScale_eq_mul]
      dsimp only [w, s]
      rw [← mul_assoc,
        mul_inv_cancel₀ D.lowerProductScaleValue_ne_zero_from_row, one_mul]
    calc
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
            F C.product z =
          QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
            F C.product (D.lowerProductScale w) := by rw [hscale]
      _ = I.actualTauFunction (D.lowerTauArgument w) *
            I.actualChiFFunction (D.lowerChiArgument w) :=
        ActualProductCoordinateCertificate.transport F K C w
      _ = D.function q .tau (D.lowerTauArgument w) *
            D.function q .chiF (D.lowerChiArgument w) := by
              rw [I.actualTauFunction_eq_table,
                I.actualChiFFunction_eq_table]
      _ = D.function q .tauChiF (D.lowerProductScale w) :=
        D.lowerProduct_exact q w
      _ = D.function q .tauChiF z := by rw [hscale]
  have hcoeff :
      QuotientDerivedNormalizedCriticalFunction.affineCoefficient
        F C.product q = lambda := by
    change normalizedCriticalPolarGamma q C.product.toCriticalPolarFunction =
      lambda
    symm
    apply (WildQuadraticRefinement.existsUnique_criticalFunction q
      C.product.toCriticalPolarFunction.toHasse).choose_spec.2
    apply HasseFunction.ext
    intro z
    change WildQuadraticRefinement.criticalFunction q lambda z =
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
        F C.product z
    rw [hfun z]
    exact ((I.toCoefficientData q).function_eq_critical_of_odd
      q .tauChiF h z).symm
  rw [QuotientDerivedNormalizedCriticalFunction.phase_eq_refinement, hcoeff]
  simp [WildQuadraticCoefficientData.phaseFactor, h]

/-- The primitive upper certificate computes the exact table phase of its
retained upstairs source, including transport along the residue-field
equivalence. -/
theorem ActualUpperCoordinateCertificate.phase_eq_table
    {T m : ℕ}
    {correction : WildQuadraticCommonCorrectionData F K T m}
    {q : CharTwoRefinement (ResidueField F)}
    {I : WildQuadraticCoefficientInputs F}
    {S : WildQuadraticSelectedStationaryPairs F K}
    {tauData chiFData : LocalQuasiCharData F}
    {psiF : LocalAddCharData F}
    (C : ActualUpperCoordinateCertificate F K correction q I S
      tauData chiFData psiF)
    {lambda : ResidueField F}
    (h : (I.toCoefficientData q).affineCoefficient .chiK = some lambda) :
    QuotientDerivedNormalizedCriticalFunction.phase K C.upper =
      (I.toCoefficientData q).phaseFactor q .chiK := by
  have hfun : ∀ z,
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
          K C.upper (wildQuadraticResidueEquiv F K correction z) =
        (I.toCoefficientData q).function q .chiK z := by
    intro z
    let D := I.toCoefficientData q
    let s := D.commonScale .chiK
    let w : ResidueField F := s⁻¹ * z
    have hscale : s * w = z := by
      dsimp only [w, s]
      rw [← mul_assoc,
        mul_inv_cancel₀ (D.commonScale_ne_zero_from_row .chiK), one_mul]
    calc
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
            K C.upper (wildQuadraticResidueEquiv F K correction z) =
          I.actualChiFFunction (D.pTransport (w ^ 2)) *
            I.actualTauFunction (D.qTransport (w ^ 2)) *
              (if D.row.TParity = .odd then
                absoluteTraceChar (ResidueField F) (D.qTransport (w ^ 2))
              else 1) := ActualUpperCoordinateCertificate.transport F K C z
      _ = D.transportedRawUpper q (w ^ 2) := by
            rw [I.actualChiFFunction_eq_table,
              I.actualTauFunction_eq_table]
            rfl
      _ = D.rawUpperFunction q (w ^ 2) :=
        (D.rawUpper_exact_transport q (w ^ 2)).symm
      _ = D.commonFunction q .chiK w := D.rawUpper_frobenius q w
      _ = D.function q .chiK z := by
        rw [WildQuadraticCoefficientData.commonFunction]
        exact congrArg (D.function q .chiK) hscale
  have hsum : C.upper.toCriticalPolarFunction.toHasse.sum =
      (WildQuadraticRefinement.criticalFunction q lambda).sum := by
    rw [HasseFunction.sum, HasseFunction.sum]
    symm
    apply Fintype.sum_equiv (wildQuadraticResidueEquiv F K correction).toEquiv
    intro z
    change WildQuadraticRefinement.criticalFunction q lambda z =
      QuotientDerivedNormalizedCriticalFunction.toCriticalPolarFunction
        K C.upper (wildQuadraticResidueEquiv F K correction z)
    rw [hfun z]
    exact ((I.toCoefficientData q).function_eq_critical_of_odd
      q .chiK h z).symm
  rw [QuotientDerivedNormalizedCriticalFunction.phase,
    WildQuadraticCoefficientData.phaseFactor, h]
  change phase C.upper.toCriticalPolarFunction.toHasse.sum =
    phase (WildQuadraticRefinement.criticalFunction q lambda).sum
  rw [hsum]

end DirectCertificatePhases

/-! ## Normalized actual-phase bridge -/

section NormalizedActualPhase

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Fintype (ResidueField E)] [CharP (ResidueField E) 2]
  {chi : LocalQuasiCharData E} {psi : LocalAddCharData E}

/-- Scaling an actual odd critical coordinate by an integral unit does not
change the phase of its complete finite sum.  The equality is proved by
reindexing the whole function, so no elementary translation or stationary
representative is discarded. -/
theorem criticalPolarFunction_phase_scaleCoordinate
    (d : ℕ) (hm : chi.conductor = 2 * d + 1)
    (hlarge : 1 < chi.conductor)
    (Gamma : AdmissibleGamma E chi psi)
    (delta : Eˣ) (hdelta : ord E (delta : E) = ((d : ℤ) : WithTop ℤ))
    (beta : lattice E ((chi.conductor : ℤ) - (chi.conductor : ℤ)))
    (hbeta : latticeQuotientMk E
        (sub_le_sub_left
          (criticalPolar_stationaryDepth E chi d hm hlarge).int_le_conductor
          (chi.conductor : ℤ)) beta =
      stationaryNumeratorClass E chi psi (chi.conductor : ℤ)
        (criticalPolar_stationaryDepth E chi d hm hlarge)
        Gamma Gamma.property)
    (u : unitGroup E) :
    phase (∑ x : ResidueField E,
        criticalPolarFunction E chi psi d hm hlarge Gamma
          (criticalPolarScaledCoordinate E u delta)
          (criticalPolarScaledCoordinate_ord E d u delta hdelta) beta x) =
      phase (∑ x : ResidueField E,
        criticalPolarFunction E chi psi d hm hlarge Gamma delta hdelta beta x) := by
  apply congrArg phase
  apply Fintype.sum_equiv (residueUnits E u).mulLeft
  intro x
  exact criticalPolarFunction_scaleCoordinate_apply chi psi d hm hlarge
    Gamma delta hdelta beta hbeta u x

/-- Normalize one actual odd Lamprecht row without changing its characters,
denominator, stationary numerator, or finite-sum phase. -/
theorem LocalLamprechtPhaseData.exists_normalizedQuotientDerivedCriticalFunction
    (row : LocalLamprechtPhaseData E chi psi)
    (hodd : Odd chi.conductor) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction E,
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData E W chi psi ∧
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair E W
        row.selectedStationaryPair ∧
      row.criticalFactor =
        QuotientDerivedNormalizedCriticalFunction.phase E W := by
  cases row with
  | even d hm hlarge Gamma beta hbeta =>
      obtain ⟨j, hj⟩ := hodd
      omega
  | odd d hm hlarge Gamma delta hdelta beta hbeta =>
      let W := normalizedQuotientDerivedCriticalFunction E chi psi d hm hlarge
        Gamma delta hdelta beta hbeta
      refine ⟨W, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
      rw [LocalLamprechtPhaseData.criticalFactor_eq_criticalFunctionPhase]
      unfold LocalLamprechtPhaseData.criticalFunctionPhase
        QuotientDerivedNormalizedCriticalFunction.phase HasseFunction.sumPhase
        HasseFunction.sum
      have huniv :
          @Finset.univ (ResidueField E) (residueFieldFintype E) =
            @Finset.univ (ResidueField E) (inferInstance :
              Fintype (ResidueField E)) := by
        ext x
        simp
      rw [huniv]
      change phase (∑ x : ResidueField E,
          criticalPolarFunction E chi psi d hm hlarge Gamma delta hdelta beta x) =
        phase (∑ x : ResidueField E,
          criticalPolarFunction E chi psi d hm hlarge Gamma W.delta
            W.delta_order beta x)
      exact (criticalPolarFunction_phase_scaleCoordinate d hm hlarge Gamma delta
        hdelta beta hbeta
          (criticalPolarNormalizationUnit E chi psi d hm hlarge Gamma delta
            hdelta)).symm

/-- Package an already proved normalized actual-row phase as the exact phase
of an optional quotient source.  The source equality is literal, so this
helper cannot replace the actual stationary numerator by another quotient
representative. -/
theorem LocalLamprechtPhaseData.criticalFactor_eq_quotientSourcePhase_of_eq_some
    (row : LocalLamprechtPhaseData E chi psi)
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (hphase : row.criticalFactor =
      QuotientDerivedNormalizedCriticalFunction.phase E W)
    {source : Option (QuotientDerivedNormalizedCriticalFunction E)}
    (hsource : source = some W) :
    row.criticalFactor = quotientSourcePhase E source := by
  rw [hsource]
  exact hphase

/-- Every actual odd Lamprecht row has a normalized quotient source with the
same characters, literal denominator and numerator, and exact
`quotientSourcePhase`.  This is the source-facing form of the finite-sum
reindexing theorem above. -/
theorem LocalLamprechtPhaseData.exists_normalizedQuotientSource
    (row : LocalLamprechtPhaseData E chi psi)
    (hodd : Odd chi.conductor) :
    ∃ W : QuotientDerivedNormalizedCriticalFunction E,
      QuotientDerivedNormalizedCriticalFunction.MatchesLocalData E W chi psi ∧
      QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair E W
        row.selectedStationaryPair ∧
      row.criticalFactor = quotientSourcePhase E (some W) := by
  obtain ⟨W, hlocal, hpair, hphase⟩ :=
    row.exists_normalizedQuotientDerivedCriticalFunction hodd
  exact ⟨W, hlocal, hpair,
    row.criticalFactor_eq_quotientSourcePhase_of_eq_some W hphase rfl⟩

/-- A normalized quotient source with the same literal local data,
denominator, and stationary numerator as an actual Lamprecht row has exactly
that row's complete finite-sum phase.  The normalized coordinates need not be
definitionally equal: their unit ratio reindexes the entire sum. -/
theorem LocalLamprechtPhaseData.criticalFactor_eq_quotientSourcePhase_of_matches
    (row : LocalLamprechtPhaseData E chi psi)
    (W : QuotientDerivedNormalizedCriticalFunction E)
    (hlocal : QuotientDerivedNormalizedCriticalFunction.MatchesLocalData
      E W chi psi)
    (hpair : QuotientDerivedNormalizedCriticalFunction.MatchesStationaryPair
      E W row.selectedStationaryPair) :
    row.criticalFactor = quotientSourcePhase E (some W) := by
  rcases hlocal with ⟨hchi, hpsi⟩
  cases row with
  | even d hm hlarge Gamma beta hbeta =>
      have hW := W.conductor_eq
      rw [hchi] at hW
      omega
  | odd d hm hlarge Gamma delta hdelta beta hbeta =>
      have hd : W.d = d := by
        have hW := W.conductor_eq
        rw [hchi] at hW
        omega
      let ratio : Eˣ := W.delta / delta
      have hratioOrd : ord E (ratio : E) = (0 : WithTop ℤ) := by
        simp only [ratio, Units.val_div_eq_div_val]
        rw [ord_div, W.delta_order, hdelta, hd]
        simp
      let u : unitGroup E :=
        ⟨ratio, (mem_unitGroup_iff_ord_eq_zero E ratio).2 hratioOrd⟩
      have hscaled : criticalPolarScaledCoordinate E u delta = W.delta := by
        apply Units.ext
        simp only [criticalPolarScaledCoordinate, u, ratio, Units.val_mul,
          Units.val_div_eq_div_val]
        field_simp [Units.ne_zero delta]
      have hGamma : (W.Gamma : Eˣ) = (Gamma : Eˣ) := hpair.1
      have hbetaW : (W.beta : E) = (beta : E) := hpair.2
      rw [LocalLamprechtPhaseData.criticalFactor_eq_criticalFunctionPhase]
      unfold LocalLamprechtPhaseData.criticalFunctionPhase quotientSourcePhase
        QuotientDerivedNormalizedCriticalFunction.phase HasseFunction.sumPhase
        HasseFunction.sum
      have huniv :
          @Finset.univ (ResidueField E) (residueFieldFintype E) =
            @Finset.univ (ResidueField E)
              (inferInstance : Fintype (ResidueField E)) := by
        ext x
        simp
      rw [huniv]
      have hphase := criticalPolarFunction_phase_scaleCoordinate
        d hm hlarge Gamma delta hdelta beta hbeta u
      change phase (∑ x : ResidueField E,
          criticalPolarFunction E chi psi d hm hlarge Gamma delta hdelta beta x) =
        phase (∑ x : ResidueField E,
          criticalPolarFunction E W.chi W.psi W.d W.conductor_eq
            W.conductor_gt_one W.Gamma W.delta W.delta_order W.beta x)
      have hright :
          (∑ x : ResidueField E,
              criticalPolarFunction E W.chi W.psi W.d W.conductor_eq
                W.conductor_gt_one W.Gamma W.delta W.delta_order W.beta x) =
            ∑ x : ResidueField E,
              criticalPolarFunction E chi psi d hm hlarge Gamma W.delta
                (by rw [W.delta_order, hd]) beta x := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [criticalPolarFunction, criticalPolarValue]
        rw [show W.psi.character = psi.character by rw [hpsi],
          hbetaW, hGamma,
          show W.chi.character = chi.character by rw [hchi]]
        congr
      rw [hright]
      simpa only [hscaled] using hphase.symm

end NormalizedActualPhase

end

end LanglandsFirstMainLemma
