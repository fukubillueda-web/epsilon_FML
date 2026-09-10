import LanglandsFirstMainLemma.Parameters.RamifiedHasseLocalGeometry
import LanglandsFirstMainLemma.Parameters.RamifiedHasseComparison
import LanglandsFirstMainLemma.Parameters.PhaseReduction
import LanglandsFirstMainLemma.Parameters.High

namespace LanglandsFirstMainLemma

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

universe u

section Transport

variable (F K : Type u)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]

/-- Transport the genuine Lamprecht value through norm and trace, retaining
the lower residual character and the negative second-symmetric translation. -/
private theorem lamprechtHasseValue_ramified_odd
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (d dK : ℕ)
    (hmF : chiF.conductor = 2 * d + 1)
    (hmK : chiK.conductor = 2 * dK + 1)
    (hlargeF : 1 < chiF.conductor)
    (hlargeK : 1 < chiK.conductor)
    (GammaF : AdmissibleGamma F chiF psiF)
    (GammaK : AdmissibleGamma K chiK psiK)
    (hGamma : (GammaK : Kˣ) =
      Units.map (algebraMap F K) (GammaF : Fˣ))
    (deltaF : Fˣ)
    (hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ))
    (deltaK : Kˣ)
    (hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ))
    (cF : lattice F ((chiF.conductor : ℤ) - (chiF.conductor : ℤ)))
    (hcF : latticeQuotientMk F
        (sub_le_sub_left
          (lamprechtFormula_stationaryDepth F chiF d 1
            (by omega) hmF hlargeF).int_le_conductor
          (chiF.conductor : ℤ)) cF =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF d 1
          (by omega) hmF hlargeF) GammaF GammaF.property)
    (cK : lattice K ((chiK.conductor : ℤ) - (chiK.conductor : ℤ)))
    (hc : (cK : K) = algebraMap F K (cF : F))
    (x : K) (hx : x ∈ lattice K 0)
    (z : F) (hz : z ∈ lattice F 0)
    (e2 : F) (he2 : e2 ∈ lattice F 0)
    (htrace : (deltaF : F) * z =
      trace F K ((deltaK : K) * x))
    (hsecond : (deltaF : F) ^ 2 * e2 =
      elementarySymmetric F K 2 ((deltaK : K) * x))
    (hnorm :
      norm F K (1 + (deltaK : K) * x) -
          (1 + trace F K ((deltaK : K) * x) +
            elementarySymmetric F K 2 ((deltaK : K) * x)) ∈
        lattice F ((2 * d + 1 : ℕ) : ℤ)) :
    lamprechtHasseValue K chiK psiK dK hmK hlargeK GammaK
        deltaK hdeltaK cK x hx =
      lamprechtHasseValue F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF cF z hz *
        lamprechtResidualAddChar F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF (reduce F (-e2) ((lattice F 0).neg_mem he2)) := by
  have hd : 0 < d := lamprechtOdd_d_pos F chiF d hmF hlargeF
  let hrF := lamprechtFormula_stationaryDepth F chiF d 1
    (by omega) hmF hlargeF
  have hdeltaMem : (deltaF : F) ∈ lattice F (d : ℤ) := by
    rw [mem_lattice, hdeltaF]
  have hdeltaSq : (deltaF : F) ^ 2 ∈
      lattice F ((d : ℤ) + (d : ℤ)) := by
    simpa only [pow_two] using mul_mem_lattice F hdeltaMem hdeltaMem
  have hw2 : (deltaF : F) ^ 2 * e2 ∈
      lattice F ((d + 1 : ℕ) : ℤ) := by
    apply lattice_antitone F
      (m := ((d + 1 : ℕ) : ℤ)) (n := (d : ℤ) + (d : ℤ)) (by omega)
    simpa only [add_zero] using
      (mul_mem_lattice (m := (d : ℤ) + (d : ℤ)) (n := 0)
        F hdeltaSq he2)
  let w2 : lattice F ((d + 1 : ℕ) : ℤ) :=
    ⟨(deltaF : F) ^ 2 * e2, hw2⟩
  let uK : unitFiltration K dK :=
    lamprechtHasseUnit K chiK dK hmK hlargeK deltaK hdeltaK x hx
  let u1 : unitFiltration F d :=
    lamprechtHasseUnit F chiF d hmF hlargeF deltaF hdeltaF z hz
  let u2 : unitFiltration F (d + 1) :=
    positiveUnitOfLattice F (by omega) w2
  let v : Fˣ := (u1 : Fˣ) * (u2 : Fˣ)
  have hcross :
      ((deltaF : F) * z) * ((deltaF : F) ^ 2 * e2) ∈
        lattice F ((2 * d + 1 : ℕ) : ℤ) := by
    have hdz : (deltaF : F) * z ∈ lattice F (d : ℤ) := by
      simpa only [add_zero] using mul_mem_lattice F hdeltaMem hz
    have hq : (deltaF : F) ^ 2 * e2 ∈
        lattice F ((d : ℤ) + d) := by
      simpa only [add_zero] using mul_mem_lattice F hdeltaSq he2
    have hp := mul_mem_lattice F hdz hq
    apply lattice_antitone F (n := (d : ℤ) + ((d : ℤ) + d)) (by omega)
    simpa only [add_assoc] using hp
  have hnormCong : CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (normUnits F K (uK : Kˣ) : F) (v : F) := by
    have hfirst : CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
        (norm F K (1 + (deltaK : K) * x))
        (1 + trace F K ((deltaK : K) * x) +
          elementarySymmetric F K 2 ((deltaK : K) * x)) := by
      rw [CongruentAtDepth.iff]
      exact hnorm
    have hsecondCong : CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
        (1 + trace F K ((deltaK : K) * x) +
          elementarySymmetric F K 2 ((deltaK : K) * x))
        ((1 + (deltaF : F) * z) *
          (1 + (deltaF : F) ^ 2 * e2)) := by
      rw [CongruentAtDepth.iff, ← htrace, ← hsecond]
      have halg :
          (1 + (deltaF : F) * z + (deltaF : F) ^ 2 * e2) -
              ((1 + (deltaF : F) * z) *
                (1 + (deltaF : F) ^ 2 * e2)) =
            -(((deltaF : F) * z) * ((deltaF : F) ^ 2 * e2)) := by ring
      rw [halg, ord_neg]
      exact hcross
    have h := hfirst.trans hsecondCong
    have huKcoe : ((uK : Kˣ) : K) = 1 + (deltaK : K) * x := by
      simp only [uK, lamprechtHasseUnit_coe]
    have hu1coe : ((u1 : Fˣ) : F) = 1 + (deltaF : F) * z := by
      simp only [u1, lamprechtHasseUnit_coe]
    have hu2coe : ((u2 : Fˣ) : F) = 1 + (deltaF : F) ^ 2 * e2 := by
      simp only [u2, coe_positiveUnitOfLattice, w2]
    change CongruentAtDepth ((2 * d + 1 : ℕ) : ℤ)
      (norm F K ((uK : Kˣ) : K)) (((u1 : Fˣ) : F) * ((u2 : Fˣ) : F))
    rw [huKcoe, hu1coe, hu2coe]
    exact h
  have huK0 : (uK : Kˣ) ∈ unitGroup K :=
    unitFiltration_antitone K (Nat.zero_le dK) uK.property
  have hnorm0 : normUnits F K (uK : Kˣ) ∈ unitGroup F := by
    rw [mem_unitGroup_iff_ord_eq_zero, coe_normUnits, ord_norm,
      (mem_unitGroup_iff_ord_eq_zero K (uK : Kˣ)).1 huK0, nsmul_zero]
  have hu10 : (u1 : Fˣ) ∈ unitGroup F :=
    unitFiltration_antitone F (Nat.zero_le d) u1.property
  have hu20 : (u2 : Fˣ) ∈ unitGroup F :=
    unitFiltration_antitone F (Nat.zero_le (d + 1)) u2.property
  have hv0 : v ∈ unitGroup F := (unitGroup F).mul_mem hu10 hu20
  have hratio : normUnits F K (uK : Kˣ) / v ∈
      unitFiltration F (2 * d + 1) :=
    (div_mem_unitFiltration_iff_congruentAtDepth F (2 * d + 1)
      (normUnits F K (uK : Kˣ)) v hnorm0 hv0).2 hnormCong
  have hratioChar :
      chiF.character (normUnits F K (uK : Kˣ) / v) = 1 := by
    apply chiF.isConductor.trivial
    simpa only [hmF] using hratio
  have hlinear := stationaryNumeratorClass_linearization
    F chiF psiF (chiF.conductor : ℤ) hrF GammaF GammaF.property
      cF hcF w2
  have hchiNorm :
      chiF.character (normUnits F K (uK : Kˣ)) =
        chiF.character (u1 : Fˣ) *
          psiF.character ((cF : F) * (deltaF : F) ^ 2 * e2 /
            ((GammaF : Fˣ) : F)) := by
    calc
      chiF.character (normUnits F K (uK : Kˣ)) =
          chiF.character ((normUnits F K (uK : Kˣ) / v) * v) := by
        congr 1
        exact (div_mul_cancel _ _).symm
      _ = chiF.character (normUnits F K (uK : Kˣ) / v) *
          chiF.character v := by rw [map_mul]
      _ = chiF.character v := by rw [hratioChar, one_mul]
      _ = chiF.character (u1 : Fˣ) * chiF.character (u2 : Fˣ) := by
        rw [map_mul]
      _ = chiF.character (u1 : Fˣ) *
          psiF.character ((cF : F) * (deltaF : F) ^ 2 * e2 /
            ((GammaF : Fˣ) : F)) := by
        rw [hlinear]
        dsimp only [w2]
        congr 2
        ring
  have hpsiE2 :
      lamprechtResidualAddChar F chiF psiF d hmF hlargeF GammaF
          deltaF hdeltaF (reduce F (-e2) ((lattice F 0).neg_mem he2)) =
        (psiF.character
          (-((cF : F) * (deltaF : F) ^ 2 * e2 /
            ((GammaF : Fˣ) : F))) : ℂ) := by
    rw [lamprechtResidualAddChar_integral_lift F chiF psiF d hmF hlargeF
      GammaF deltaF hdeltaF cF hcF (-e2) ((lattice F 0).neg_mem he2)]
    congr 2
    ring
  have hpsiMain :
      psiK.character
          ((cK : K) * (deltaK : K) * x / ((GammaK : Kˣ) : K)) =
        psiF.character
          ((cF : F) * (deltaF : F) * z / ((GammaF : Fˣ) : F)) := by
    rw [hpsi, ContinuousAddChar.compTrace_apply]
    apply congrArg psiF.character
    have htraceScalar := (Algebra.trace F K).map_smul
      ((cF : F) / ((GammaF : Fˣ) : F)) ((deltaK : K) * x)
    rw [← htrace] at htraceScalar
    have hGammaCoe := congrArg Units.val hGamma
    rw [hc, hGammaCoe]
    simpa [Units.coe_map, Algebra.smul_def, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using htraceScalar
  have hchiMain : chiK.character (uK : Kˣ) =
      chiF.character (normUnits F K (uK : Kˣ)) := by
    rw [hchi, ContinuousQuasiChar.compNorm_apply]
  unfold lamprechtHasseValue
  rw [show lamprechtHasseUnit K chiK dK hmK hlargeK deltaK hdeltaK x hx =
        uK by rfl,
    show lamprechtHasseUnit F chiF d hmF hlargeF deltaF hdeltaF z hz =
        u1 by rfl,
    hpsiMain, hchiMain, hchiNorm, hpsiE2]
  push_cast
  have hq0 :
      (psiF.character
        ((cF : F) * (deltaF : F) ^ 2 * e2 /
          ((GammaF : Fˣ) : F)) : ℂ) ≠ 0 :=
    ContinuousAddChar.apply_ne_zero _ _
  have hpsiNeg :
      (psiF.character
        (-((cF : F) * (deltaF : F) ^ 2 * e2 /
          ((GammaF : Fˣ) : F))) : ℂ) =
        (psiF.character
          ((cF : F) * (deltaF : F) ^ 2 * e2 /
            ((GammaF : Fˣ) : F)) : ℂ)⁻¹ := by
    simpa only [ContinuousAddChar.toAddChar_apply, Units.val_inv_eq_inv_val] using
      congrArg Units.val (AddChar.map_neg_eq_inv psiF.character.toAddChar
        ((cF : F) * (deltaF : F) ^ 2 * e2 /
          ((GammaF : Fˣ) : F)))
  rw [hpsiNeg]
  push_cast
  field_simp [hq0]

end Transport

end

noncomputable section

section SourceCoordinates

variable (F K : Type u)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

set_option linter.unusedSectionVars false in
/-- The actual stationary-phase form of the raw transport calculation. -/
private theorem RamifiedHasseOddStationaryPhase.function_transport
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (lower : RamifiedHasseOddStationaryPhase F chiF psiF)
    (upper : RamifiedHasseOddStationaryPhase K chiK psiK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hGamma : (upper.denominator : Kˣ) =
      Units.map (algebraMap F K) (lower.denominator : Fˣ))
    (hc : (upper.representative.representative : K) =
      algebraMap F K (lower.representative.representative : F))
    (x : K) (hx : x ∈ lattice K 0)
    (z : F) (hz : z ∈ lattice F 0)
    (e2 : F) (he2 : e2 ∈ lattice F 0)
    (htrace : (lower.delta : F) * z =
      trace F K ((upper.delta : K) * x))
    (hsecond : (lower.delta : F) ^ 2 * e2 =
      elementarySymmetric F K 2 ((upper.delta : K) * x))
    (hnorm :
      norm F K (1 + (upper.delta : K) * x) -
          (1 + trace F K ((upper.delta : K) * x) +
            elementarySymmetric F K 2 ((upper.delta : K) * x)) ∈
        lattice F ((2 * lower.d + 1 : ℕ) : ℤ)) :
    upper.function (reduce K x hx) =
      lower.function (reduce F z hz) *
        lamprechtResidualAddChar F chiF psiF lower.d lower.conductor_eq
          lower.conductor_large lower.denominator lower.delta lower.delta_order
          (reduce F (-e2) ((lattice F 0).neg_mem he2)) := by
  have hcF : latticeQuotientMk F
      (sub_le_sub_left
        (lamprechtFormula_stationaryDepth F chiF lower.d 1
          (by omega) lower.conductor_eq lower.conductor_large).int_le_conductor
        (chiF.conductor : ℤ)) lower.representative.toLamprecht =
      stationaryNumeratorClass F chiF psiF (chiF.conductor : ℤ)
        (lamprechtFormula_stationaryDepth F chiF lower.d 1
          (by omega) lower.conductor_eq lower.conductor_large)
        lower.denominator lower.denominator.property := by
    simpa only [stationaryDepthOfConductorDecomposition] using
      lower.representative.toLamprecht_represents
  have hcK : latticeQuotientMk K
      (sub_le_sub_left
        (lamprechtFormula_stationaryDepth K chiK upper.d 1
          (by omega) upper.conductor_eq upper.conductor_large).int_le_conductor
        (chiK.conductor : ℤ)) upper.representative.toLamprecht =
      stationaryNumeratorClass K chiK psiK (chiK.conductor : ℤ)
        (lamprechtFormula_stationaryDepth K chiK upper.d 1
          (by omega) upper.conductor_eq upper.conductor_large)
        upper.denominator upper.denominator.property := by
    simpa only [stationaryDepthOfConductorDecomposition] using
      upper.representative.toLamprecht_represents
  change
    lamprechtHasseFunction K chiK psiK upper.d upper.conductor_eq
        upper.conductor_large upper.denominator upper.delta upper.delta_order
        upper.representative.toLamprecht hcK (reduce K x hx) =
      lamprechtHasseFunction F chiF psiF lower.d lower.conductor_eq
          lower.conductor_large lower.denominator lower.delta lower.delta_order
          lower.representative.toLamprecht hcF (reduce F z hz) * _
  rw [lamprechtHasseFunction_integral_lift K chiK psiK upper.d
      upper.conductor_eq upper.conductor_large upper.denominator upper.delta
      upper.delta_order upper.representative.toLamprecht hcK x hx,
    lamprechtHasseFunction_integral_lift F chiF psiF lower.d
      lower.conductor_eq lower.conductor_large lower.denominator lower.delta
      lower.delta_order lower.representative.toLamprecht hcF z hz]
  exact lamprechtHasseValue_ramified_odd F K chiF psiF chiK psiK hchi
    hpsi lower.d upper.d lower.conductor_eq upper.conductor_eq
    lower.conductor_large upper.conductor_large lower.denominator
    upper.denominator hGamma lower.delta lower.delta_order upper.delta
    upper.delta_order lower.representative.toLamprecht hcF
    upper.representative.toLamprecht hc x hx z hz e2 he2 htrace hsecond hnorm

/-- The source-tied normalized trace coordinate before reduction. -/
private def ramifiedHasseTraceCoordinateValue
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) (a : F) : F :=
  trace F K (ramifiedHasseLocalInput F K P dK a) /
    (ramifiedHasseLowerUniformizer F K P : F) ^ d

/-- The source-tied normalized second-symmetric coordinate before reduction. -/
private def ramifiedHasseSecondCoordinateValue
    (P : PrimeCyclicPreparation F K) (d dK : ℕ) (a : F) : F :=
  elementarySymmetric F K 2 (ramifiedHasseLocalInput F K P dK a) /
    (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d)

private theorem ramifiedHasseTraceCoordinateValue_mem
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (a : F) (ha : a ∈ lattice F 0) :
    ramifiedHasseTraceCoordinateValue F K P d dK a ∈ lattice F 0 := by
  unfold ramifiedHasseTraceCoordinateValue
  apply (div_mem_lattice_iff F
    ((ramifiedHasseLowerUniformizer F K P : F) ^ d)
    (trace F K (ramifiedHasseLocalInput F K P dK a))
    (d : ℤ) 0 (by
      simpa only [phaseReductionSourceCoordinate_coe] using
        phaseReductionSourceCoordinate_order F
          (ramifiedHasseLowerUniformizer F K P)
          G.lowerUniformizer_order d)).2
  simpa only [add_zero] using G.traceDepth a ha

private theorem ramifiedHasseSecondCoordinateValue_mem
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (a : F) (ha : a ∈ lattice F 0) :
    ramifiedHasseSecondCoordinateValue F K P d dK a ∈ lattice F 0 := by
  unfold ramifiedHasseSecondCoordinateValue
  apply (div_mem_lattice_iff F
    ((ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d))
    (elementarySymmetric F K 2 (ramifiedHasseLocalInput F K P dK a))
    (((2 * d : ℕ) : ℤ)) 0 (by
      simpa only [phaseReductionSourceCoordinate_coe] using
        phaseReductionSourceCoordinate_order F
          (ramifiedHasseLowerUniformizer F K P)
          G.lowerUniformizer_order (2 * d))).2
  simpa only [add_zero] using G.secondSymmetricDepth a ha

private noncomputable def ramifiedHasseTraceCoordinate
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (x : ResidueField F) : ResidueField F :=
  let a : F := teichmuller F x
  reduce F (ramifiedHasseTraceCoordinateValue F K P d dK a)
    (ramifiedHasseTraceCoordinateValue_mem F K P G a
      ((mem_lattice_zero_iff F).2 (teichmuller F x).property))

private noncomputable def ramifiedHasseSecondCoordinate
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (x : ResidueField F) : ResidueField F :=
  let a : F := teichmuller F x
  reduce F (ramifiedHasseSecondCoordinateValue F K P d dK a)
    (ramifiedHasseSecondCoordinateValue_mem F K P G a
      ((mem_lattice_zero_iff F).2 (teichmuller F x).property))

/-- LocalGeometry-specialized transport for the two actual stationary Hasse
functions.  This is the point at which the representative translation and
ordered denominator pair enter the finite calculation. -/
private theorem ramifiedHasse_actual_function_transport
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (lower : RamifiedHasseOddStationaryPhase F chiF psiF)
    (upper : RamifiedHasseOddStationaryPhase K chiK psiK)
    (hlowerDepth : lower.d = d) (_hupperDepth : upper.d = dK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hGamma : (upper.denominator : Kˣ) =
      Units.map (algebraMap F K) (lower.denominator : Fˣ))
    (hc : (upper.representative.representative : K) =
      algebraMap F K (lower.representative.representative : F))
    (hlowerDelta : lower.delta =
      phaseReductionSourceCoordinate F
        (ramifiedHasseLowerUniformizer F K P) d)
    (hupperDelta : upper.delta =
      phaseReductionSourceCoordinate K
        (ramifiedHasseUpperUniformizer F K P) dK)
    (x : ResidueField F) :
    upper.function
        (PhaseReductionResidualCoordinateSource.residueEquiv P.hres x) =
      lower.function (ramifiedHasseTraceCoordinate F K P G x) *
        lamprechtResidualAddChar F chiF psiF lower.d lower.conductor_eq
          lower.conductor_large lower.denominator lower.delta lower.delta_order
          (-ramifiedHasseSecondCoordinate F K P G x) := by
  let a : F := teichmuller F x
  have ha : a ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  let xK : K := algebraMap F K a
  have hxK : xK ∈ lattice K 0 := by
    rw [mem_lattice, ord_algebraMap]
    rw [mem_lattice] at ha
    simpa using nsmul_le_nsmul_right ha (ramificationIndex F K)
  let z := ramifiedHasseTraceCoordinateValue F K P d dK a
  have hz : z ∈ lattice F 0 :=
    ramifiedHasseTraceCoordinateValue_mem F K P G a ha
  let e2 := ramifiedHasseSecondCoordinateValue F K P d dK a
  have he2 : e2 ∈ lattice F 0 :=
    ramifiedHasseSecondCoordinateValue_mem F K P G a ha
  have htrace : (lower.delta : F) * z =
      trace F K ((upper.delta : K) * xK) := by
    rw [hlowerDelta, hupperDelta]
    simp only [phaseReductionSourceCoordinate_coe]
    unfold z ramifiedHasseTraceCoordinateValue xK
    unfold ramifiedHasseLocalInput
    have hpi : (ramifiedHasseLowerUniformizer F K P : F) ^ d ≠ 0 :=
      pow_ne_zero _ (Units.ne_zero _)
    field_simp [hpi]
  have hsecond : (lower.delta : F) ^ 2 * e2 =
      elementarySymmetric F K 2 ((upper.delta : K) * xK) := by
    rw [hlowerDelta, hupperDelta]
    simp only [phaseReductionSourceCoordinate_coe]
    unfold e2 ramifiedHasseSecondCoordinateValue xK
    unfold ramifiedHasseLocalInput
    rw [← pow_mul]
    rw [show d * 2 = 2 * d by omega]
    have hpi : (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) ≠ 0 :=
      pow_ne_zero _ (Units.ne_zero _)
    field_simp [hpi]
  have hnorm :
      norm F K (1 + (upper.delta : K) * xK) -
          (1 + trace F K ((upper.delta : K) * xK) +
            elementarySymmetric F K 2 ((upper.delta : K) * xK)) ∈
        lattice F ((2 * lower.d + 1 : ℕ) : ℤ) := by
    rw [hlowerDepth, hupperDelta]
    simpa only [phaseReductionSourceCoordinate_coe, xK,
      ramifiedHasseLocalInput] using G.normTruncation a ha
  have hraw := RamifiedHasseOddStationaryPhase.function_transport F K
    chiF psiF chiK psiK lower upper hchi hpsi hGamma hc xK hxK z hz e2 he2
      htrace hsecond hnorm
  have hredK : reduce K xK hxK =
      PhaseReductionResidualCoordinateSource.residueEquiv P.hres x := by
    rw [G.residueEquiv_eq_extension]
    change residueMap K
        (⟨algebraMap F K a, (mem_lattice_zero_iff K).1 hxK⟩ :
          ringOfIntegers K) = extensionResidueMap F K x
    change extensionResidueMap F K
        (residueMap F
          (⟨a, (mem_lattice_zero_iff F).1 ha⟩ : ringOfIntegers F)) = _
    simp [a]
  rw [hredK] at hraw
  have hredNeg : reduce F (-e2) ((lattice F 0).neg_mem he2) =
      -reduce F e2 he2 := by
    unfold reduce
    have hsub :
        (⟨-e2, (mem_lattice_zero_iff F).1 ((lattice F 0).neg_mem he2)⟩ :
          ringOfIntegers F) =
        -(⟨e2, (mem_lattice_zero_iff F).1 he2⟩ : ringOfIntegers F) := by
      ext
      rfl
    rw [hsub, map_neg]
  rw [hredNeg] at hraw
  simpa only [ramifiedHasseTraceCoordinate,
    ramifiedHasseSecondCoordinate, a, z, e2] using hraw

end SourceCoordinates

end

noncomputable section

section FiniteNormalForms

/-- A Hasse function has polar coefficient one when its own additive
character is retained. -/
private noncomputable def HasseFunction.toSelfCriticalPolar
    {k : Type u} [Field k]
    {theta : FiniteAddChar k} (phi : HasseFunction k theta) :
    CriticalPolarFunction k theta 1 where
  toFun := phi
  ne_zero' := phi.ne_zero
  map_add' x y := by
    rw [phi.map_add]
    simp only [one_mul]

private theorem HasseFunction.exists_self_quadratic_normalForm
    {k : Type u} [Field k] [Fintype k]
    {theta : FiniteAddChar k} (htheta : theta ≠ 1)
    (hchar : ringChar k ≠ 2) (phi : HasseFunction k theta) :
    ∃ alpha : k, ∀ x : k,
      phi x = theta ((1 : k) / 2 * x ^ 2 + alpha * x) := by
  refine ⟨phi.toSelfCriticalPolar.affineCoefficient hchar htheta, ?_⟩
  intro x
  exact phi.toSelfCriticalPolar.eq_quadratic hchar htheta x

/-- Coefficient-one quadratic normal form of the actual lower Lamprecht
function, with its quotient-derived residual additive character. -/
private theorem RamifiedHasseOddStationaryPhase.exists_lower_normalForm
    (E : Type u)
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    (chi : LocalQuasiCharData E) (psi : LocalAddCharData E)
    (V : RamifiedHasseOddStationaryPhase E chi psi)
    (hchar : residueCharacteristic E ≠ 2) :
    letI := residueFieldFintype E
    ∃ alpha : ResidueField E, ∀ x : ResidueField E,
      V.function x =
        (lamprechtResidualAddChar E chi psi V.d V.conductor_eq
          V.conductor_large V.denominator V.delta V.delta_order)
          ((1 : ResidueField E) / 2 * x ^ 2 + alpha * x) := by
  letI : Fintype (ResidueField E) := residueFieldFintype E
  apply HasseFunction.exists_self_quadratic_normalForm
  · exact lamprechtResidualAddChar_ne_one E chi psi V.d V.conductor_eq
      V.conductor_large V.denominator V.delta V.delta_order
      V.representative.toLamprecht (by
        simpa only [stationaryDepthOfConductorDecomposition] using
          V.representative.toLamprecht_represents)
  · exact hchar

private theorem tame_upper_normalForm_of_powerRelation
    {k : Type u} [Field k] [Fintype k]
    {theta : FiniteAddChar k}
    {ell : ℕ} {c alpha : k} {lower upper : k → ℂ}
    (hlower : ∀ x : k,
      lower x = theta ((1 : k) / 2 * x ^ 2 + alpha * x))
    (hpower : ∀ x : k, upper (c⁻¹ * x) = lower x ^ ell) :
    ∀ x : k, upper (c⁻¹ * x) =
      theta ((ell : k) / 2 * x ^ 2 + ((ell : k) * alpha) * x) := by
  intro x
  rw [hpower, hlower, ← AddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul]
  congr 1
  ring

private noncomputable def RamifiedHasseTameOddFiniteData.of_powerRelation
    {k : Type u} [Field k] [Fintype k]
    {ell : ℕ} {epsilon : k} {lower upper : k → ℂ}
    (hchar : ringChar k ≠ 2)
    (theta : FiniteAddChar k) (htheta : theta ≠ 1)
    (hell : Odd ell) (hell0 : (ell : k) ≠ 0)
    (c : k) (hc : c ≠ 0)
    (hepsilon : epsilon = (ell : k) * c ^ 2)
    (alpha : k)
    (hsign : finiteQuadraticChar k (ell : k) =
      finiteQuadraticChar k (-1) ^ ((ell - 1) / 2))
    (hlower : ∀ x : k,
      lower x = theta ((1 : k) / 2 * x ^ 2 + alpha * x))
    (hpower : ∀ x : k, upper (c⁻¹ * x) = lower x ^ ell) :
    RamifiedHasseTameOddFiniteData k ell epsilon lower upper where
  residueCharacteristic_odd := hchar
  psi := theta
  psi_ne_one := htheta
  degree_odd := hell
  degree_scalar_ne_zero := hell0
  c := c
  c_ne_zero := hc
  epsilon_eq := hepsilon
  alpha := alpha
  quadraticReciprocitySign := hsign
  lower_pointwise := hlower
  upper_pointwise := tame_upper_normalForm_of_powerRelation hlower hpower

private theorem wild_upper_normalForm
    {k : Type u} [Field k]
    {theta : FiniteAddChar k}
    {epsilon : k} (lower : HasseFunction k theta) {upper : k → ℂ}
    (trace secondSymmetric : k → k)
    (htransport : ∀ x : k,
      upper x = lower (trace x) * theta (-(secondSymmetric x)))
    (htrace : ∀ x : k, trace x = 0)
    (hsecond : ∀ x : k,
      -(secondSymmetric x) = epsilon / 2 * x ^ 2) :
    ∀ x : k, upper x = theta (epsilon / 2 * x ^ 2 + 0 * x) := by
  intro x
  rw [htransport, htrace, lower.map_zero, hsecond]
  simp

/-- Normalize a characteristic-two Hasse function against the absolute
trace character, retaining the exact scalar precomposition. -/
private theorem exists_charTwo_affine_normalForm
    {k : Type u} [Field k] [Fintype k] [CharP k 2]
    {theta : FiniteAddChar k} (htheta : theta ≠ 1)
    (phi : HasseFunction k theta) :
    ∃ coordinateScale : k, coordinateScale ≠ 0 ∧
      ∃ (q : CharTwoRefinement k) (lambda : k),
        ∀ x : k, phi (coordinateScale⁻¹ * x) = q.affine lambda x := by
  let psi0 := absoluteTraceChar k
  let hpsi0 : psi0 ≠ 1 := absoluteTraceChar_ne_one k
  let A := finiteAddCharCoefficient psi0 hpsi0 theta
  have hA : A ≠ 0 :=
    finiteAddCharCoefficient_ne_zero psi0 hpsi0 theta htheta
  obtain ⟨coordinateScale, hscaleSq, _⟩ := existsUnique_squareRoot k A
  have hscale0 : coordinateScale ≠ 0 := by
    intro hzero
    apply hA
    rw [← hscaleSq, hzero, zero_pow (by omega : 2 ≠ 0)]
  let Phi : CriticalPolarFunction k psi0 A :=
    { toFun := phi
      ne_zero' := phi.ne_zero
      map_add' := by
        intro x y
        rw [phi.map_add]
        congr 1
        exact (finiteAddCharCoefficient_apply psi0 hpsi0 theta (x * y)).symm }
  let normalized : HasseFunction k psi0 :=
    { toFun := fun x ↦ Phi (coordinateScale⁻¹ * x)
      ne_zero' := fun x ↦ Phi.ne_zero _
      map_add' := by
        intro x y
        rw [mul_add, Phi.map_add]
        congr 1
        congr 1
        rw [← hscaleSq]
        field_simp [hscale0] }
  obtain ⟨q, _d, _hq⟩ :=
    CharTwoRefinement.exists_charTwoRefinement_translate normalized
  obtain ⟨lambda, hlambda, _⟩ := q.existsUnique_affine normalized
  refine ⟨coordinateScale, hscale0, q, lambda, ?_⟩
  intro x
  change normalized x = q.affine lambda x
  exact (DFunLike.congr_fun hlambda x).symm

end FiniteNormalForms

end

section TameArithmetic

private theorem tame_quadraticSign
    {k : Type*} [Field k] [Fintype k]
    {ell : ℕ} [Fact ell.Prime]
    (hchar : ringChar k ≠ 2)
    (hellOdd : Odd ell)
    (hellk : (ell : k) ≠ 0)
    (hdiv : ell ∣ Fintype.card k - 1) :
    finiteQuadraticChar k (ell : k) =
      finiteQuadraticChar k (-1) ^ ((ell - 1) / 2) := by
  classical
  have hellChar : ringChar k ≠ ell := by
    intro h
    apply hellk
    rw [CharP.cast_eq_zero_iff k (ringChar k) ell, h]
  have hZchar : ringChar (ZMod ell) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    obtain ⟨r, rfl⟩ := hellOdd
    omega
  have hcardmod : (Fintype.card k : ZMod ell) = 1 := by
    have hm : Fintype.card k ≡ 1 [MOD ell] :=
      ((Nat.modEq_iff_dvd' Fintype.card_pos).2 hdiv).symm
    simpa only [Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (Fintype.card k) 1 ell).2 hm
  have hq := quadraticChar_card_card (F := k) hchar
    (F' := ZMod ell) hZchar (by simpa [ZMod.ringChar_zmod_n] using hellChar.symm)
  simp only [ZMod.card] at hq
  rw [hcardmod, mul_one] at hq
  have hsign := quadraticChar_dichotomy
    (F := k) (a := (-1 : k)) (neg_ne_zero.mpr one_ne_zero)
  change ((quadraticChar k (ell : k) : ℤ) : ℂ) =
    (((quadraticChar k (-1 : k) : ℤ) : ℂ) ^ ((ell - 1) / 2))
  rw [← Int.cast_pow]
  congr 1
  rw [hq]
  rcases hsign with hpos | hneg
  · rw [hpos]
    simp
  · rw [hneg]
    have hcastneg : ((-1 : ℤ) : ZMod ell) = (-1 : ZMod ell) := by norm_num
    rw [hcastneg, quadraticChar_neg_one hZchar, ZMod.card,
      ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hellOdd)]
    congr 1
    obtain ⟨r, hr⟩ := hellOdd
    omega

private theorem tame_degree_scalar_ne_zero
    {k : Type*} [Field k] [Fintype k] {ell : ℕ}
    (hdiv : ell ∣ Fintype.card k - 1) : (ell : k) ≠ 0 := by
  intro hell
  have hchar : ringChar k ∣ ell :=
    (CharP.cast_eq_zero_iff k (ringChar k) ell).mp hell
  letI : Fact (Nat.Prime (ringChar k)) := ⟨CharP.prime_ringChar k⟩
  have hcq : ringChar k ∣ Fintype.card k :=
    (prime_dvd_char_iff_dvd_card (ringChar k)).mp (dvd_refl _)
  have hcop : Nat.Coprime (Fintype.card k - 1) (Fintype.card k) :=
    (Nat.coprime_self_sub_left Fintype.card_pos).mpr
      (Nat.coprime_one_left (Fintype.card k))
  have hellcop : Nat.Coprime ell (Fintype.card k) :=
    Nat.Coprime.of_dvd_left hdiv hcop
  have hone : ringChar k = 1 :=
    Nat.eq_one_of_dvd_coprimes hellcop hchar hcq
  exact (CharP.prime_ringChar k).ne_one hone

variable (F K : Type u) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

/-- Tame inertia embeds the prime cyclic degree into the nonzero residue
scalars. -/
private theorem tame_degree_dvd_residueCard_sub_one
    (P : PrimeCyclicPreparation F K) (ht : P.t = 0) :
    Module.finrank F K ∣ residueCard F - 1 := by
  let σ0 : lowerRamificationGroup F K 0 :=
    ⟨PrimeCyclicExtension.generator F K, by
      rw [P.lowerRamificationGroup_zero_eq_top]
      trivial⟩
  let σ0bar : LowerRamificationGraded F K 0 :=
    lowerRamificationGradedMk F K 0 σ0
  let u : UnitGradedPiece K 0 :=
    ramificationUnitGradedHom F K 0 P.piK P.hpiK P.hgen σ0bar
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
      have hbreak : PrimeCyclicExtension.IsLowerBreak F K 0 := by
        simpa only [ht] using P.ht
      simpa only [Nat.cast_zero, zero_add] using hbreak.2
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
      _ = Module.finrank F K := PrimeCyclicExtension.orderOf_generator F K
  have huOrder : orderOf u = Module.finrank F K := by
    change orderOf
      (ramificationUnitGradedHom F K 0 P.piK P.hpiK P.hgen σ0bar) = _
    rw [orderOf_injective
      (ramificationUnitGradedHom F K 0 P.piK P.hpiK P.hgen)
      (ramificationUnitGradedHom_injective F K 0 P.piK P.hpiK P.hgen)]
    exact hσ0barOrder
  have hdegreeCard : Module.finrank F K ∣ Nat.card (UnitGradedPiece K 0) := by
    rw [← huOrder]
    exact orderOf_dvd_natCard u
  have hgradedCard : Nat.card (UnitGradedPiece K 0) = residueCard K - 1 := by
    change Nat.card (UnitFiltrationQuotient K 0 1 (by omega)) =
      residueCard K - 1
    simpa [Nat.one_ne_zero] using
      (unitFiltrationQuotient_card K (show 0 ≤ 1 by omega))
  rw [hgradedCard, residueCard_eq_of_residueDegree_eq_one F K P.hres]
    at hdegreeCard
  exact hdegreeCard

/-- The exact tame normalized-trace residue supplied by the source
coordinate `piK^dK / piF^d`. -/
private theorem tame_epsilonResidue_eq
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (ht : P.t = 0) :
    ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
        G.lowerDepth_pos G.stableRange G.stationaryDepthRelation =
      (Module.finrank F K : ResidueField F) *
        ramifiedHasseTameCoordinate F K P d dK ^ 2 := by
  classical
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) P.hres
  obtain ⟨cLift, hcLift, hcResidue⟩ := G.tameCoordinate_origin ht
  let cO : ringOfIntegers K :=
    ⟨(cLift : K), (mem_lattice_zero_iff K).1 cLift.property⟩
  have hcOrd : (0 : WithTop ℤ) ≤ ord K (cLift : K) := by
    have hc := cLift.property
    rw [mem_lattice] at hc
    exact hc
  have htraceCLift :
      trace F K ((cLift : K) ^ 2) =
        ramifiedHasseNormalizedTrace F K P d dK := by
    have hscaled := (Algebra.trace F K).map_smul
      ((ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d))
      ((cLift : K) ^ 2)
    have hinside :
        algebraMap F K
              ((ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d)) *
            (cLift : K) ^ 2 =
          (ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK) := by
      rw [hcLift, div_pow, map_pow]
      have hden : algebraMap F K
          ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ≠ 0 :=
        (map_ne_zero (algebraMap F K)).2
          (pow_ne_zero _ (Units.ne_zero
            (ramifiedHasseLowerUniformizer F K P)))
      field_simp
      simp only [map_pow, ← pow_mul]
      ring
    have hmul :
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) *
            trace F K ((cLift : K) ^ 2) =
          trace F K
            ((ramifiedHasseUpperUniformizer F K P : K) ^ (2 * dK)) := by
      rw [← hinside]
      simpa [Algebra.smul_def] using hscaled.symm
    rw [G.epsilonTraceSpecialization] at hmul
    exact mul_left_cancel₀
      (pow_ne_zero _ (Units.ne_zero
        (ramifiedHasseLowerUniformizer F K P))) (by
          simpa [mul_comm] using hmul)
  have hsumEq :
      algebraMap F K (ramifiedHasseNormalizedTrace F K P d dK) =
        ∑ σ : Gal(K/F), σ ((cLift : K) ^ 2) := by
    rw [← htraceCLift]
    exact trace_eq_sum_automorphisms ((cLift : K) ^ 2)
  have hsigma (sigma : Gal(K/F)) :
      CongruentAtDepth 1 (sigma (cLift : K)) (cLift : K) := by
    have hsigmaMem : sigma ∈ lowerRamificationGroup F K 0 := by
      rw [P.lowerRamificationGroup_zero_eq_top]
      trivial
    simpa [cO] using
      (mem_lowerRamificationGroup F K sigma 0).1 hsigmaMem cO
  have hsigmaSq (sigma : Gal(K/F)) :
      CongruentAtDepth 1 (sigma ((cLift : K) ^ 2)) ((cLift : K) ^ 2) := by
    rw [map_pow]
    have hsigmaOrd : (0 : WithTop ℤ) ≤ ord K (sigma (cLift : K)) := by
      rw [ord_galoisConjugate]
      exact hcOrd
    simpa [pow_two] using CongruentAtDepth.mul hsigmaOrd hcOrd
      (hsigma sigma) (hsigma sigma)
  have hsumCong : CongruentAtDepth 1
      (∑ sigma : Gal(K/F), sigma ((cLift : K) ^ 2))
      (∑ _sigma : Gal(K/F), (cLift : K) ^ 2) := by
    rw [congruentAtDepth_iff_sub_mem_lattice, ← Finset.sum_sub_distrib]
    exact sum_mem_lattice K (fun sigma _ ↦
      (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1 (hsigmaSq sigma))
  have hepsilonCong : CongruentAtDepth 1
      (algebraMap F K (ramifiedHasseNormalizedTrace F K P d dK))
      ((Module.finrank F K : K) * (cLift : K) ^ 2) := by
    rw [hsumEq]
    simpa only [Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      nsmul_eq_mul] using hsumCong
  let epsilonO : ringOfIntegers F :=
    ⟨ramifiedHasseNormalizedTrace F K P d dK,
      (mem_lattice_zero_iff F).1 G.epsilon_mem_lattice_zero⟩
  let epsilonKO : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) epsilonO
  let rhsO : ringOfIntegers K :=
    (Module.finrank F K : ringOfIntegers K) * cO ^ 2
  have hresidueEq : residueMap K epsilonKO = residueMap K rhsO := by
    rw [residueMap_eq_residueMap_iff]
    exact (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1 (by
      simpa [epsilonKO, epsilonO, rhsO, cO,
        Valuation.HasExtension.val_algebraMap] using hepsilonCong)
  have hleft : residueMap K epsilonKO = e
      (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
        G.lowerDepth_pos G.stableRange G.stationaryDepthRelation) := by
    rw [G.epsilonResidue_eq]
    change residueMap K epsilonKO = e (residueMap F epsilonO)
    rw [show e (residueMap F epsilonO) =
        extensionResidueMap F K (residueMap F epsilonO) by
      exact PhaseReductionResidualCoordinateSource.residueEquiv_apply
        P.hres (residueMap F epsilonO)]
    rfl
  have hright : residueMap K rhsO =
      (Module.finrank F K : ResidueField K) *
        (e (ramifiedHasseTameCoordinate F K P d dK)) ^ 2 := by
    change residueMap K
      ((Module.finrank F K : ringOfIntegers K) * cO ^ 2) = _
    rw [map_mul, map_natCast, map_pow]
    congr 2
    simpa only [e, cO, reduce] using hcResidue.symm
  apply e.injective
  rw [map_mul, map_natCast, map_pow, ← hleft, hresidueEq, hright]

/-- In tame depth, normalized trace is multiplication by the literal tame
coordinate and by the extension degree. -/
private theorem tame_normalizedTraceResidue
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (ht : P.t = 0) (a : F) (ha : a ∈ lattice F 0) :
    let z := trace F K (ramifiedHasseLocalInput F K P dK a) /
      (ramifiedHasseLowerUniformizer F K P : F) ^ d
    let hz : z ∈ lattice F 0 :=
      (div_mem_lattice_iff F
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d)
        (trace F K (ramifiedHasseLocalInput F K P dK a))
        (d : ℤ) 0 (by
          rw [ord_pow, G.lowerUniformizer_order, ← WithTop.coe_nsmul]
          norm_num [nsmul_eq_mul])).2 (by simpa using G.traceDepth a ha)
    reduce F z hz =
      (Module.finrank F K : ResidueField F) * reduce F a ha *
        ramifiedHasseTameCoordinate F K P d dK := by
  classical
  dsimp only
  let e := PhaseReductionResidualCoordinateSource.residueEquiv
    (F := F) (K := K) P.hres
  obtain ⟨cLift, hcLift, hcResidue⟩ := G.tameCoordinate_origin ht
  let cO : ringOfIntegers K :=
    ⟨(cLift : K), (mem_lattice_zero_iff K).1 cLift.property⟩
  have hpiPowOrder : ord F
      ((ramifiedHasseLowerUniformizer F K P : F) ^ d) =
        ((d : ℤ) : WithTop ℤ) := by
    rw [ord_pow, G.lowerUniformizer_order, ← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  have hinputOne :
      ramifiedHasseLocalInput F K P dK 1 =
        algebraMap F K
            ((ramifiedHasseLowerUniformizer F K P : F) ^ d) *
          (cLift : K) := by
    rw [ramifiedHasseLocalInput, map_one, mul_one, hcLift]
    have hden : algebraMap F K
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ≠ 0 :=
      (map_ne_zero (algebraMap F K)).2
        (pow_ne_zero _ (Units.ne_zero
          (ramifiedHasseLowerUniformizer F K P)))
    field_simp
  have htraceOne :
      trace F K (ramifiedHasseLocalInput F K P dK 1) =
        (ramifiedHasseLowerUniformizer F K P : F) ^ d *
          trace F K (cLift : K) := by
    rw [hinputOne]
    simpa [Algebra.smul_def] using
      (Algebra.trace F K).map_smul
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d) (cLift : K)
  have htraceLiftIntegral : trace F K (cLift : K) ∈ lattice F 0 := by
    have htraceDepth := G.traceDepth (1 : F) (by rw [mem_lattice]; simp)
    have hquotIntegral :=
      (div_mem_lattice_iff F
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d)
        (trace F K (ramifiedHasseLocalInput F K P dK 1))
        (d : ℤ) 0 hpiPowOrder).2 (by simpa using htraceDepth)
    have hquot :
        trace F K (ramifiedHasseLocalInput F K P dK 1) /
            (ramifiedHasseLowerUniformizer F K P : F) ^ d =
          trace F K (cLift : K) := by
      rw [htraceOne]
      exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Units.ne_zero
        (ramifiedHasseLowerUniformizer F K P)))
    rwa [hquot] at hquotIntegral
  have hsumEq : algebraMap F K (trace F K (cLift : K)) =
      ∑ sigma : Gal(K/F), sigma (cLift : K) :=
    trace_eq_sum_automorphisms (cLift : K)
  have hsigma (sigma : Gal(K/F)) :
      CongruentAtDepth 1 (sigma (cLift : K)) (cLift : K) := by
    have hsigmaMem : sigma ∈ lowerRamificationGroup F K 0 := by
      rw [P.lowerRamificationGroup_zero_eq_top]
      trivial
    simpa [cO] using
      (mem_lowerRamificationGroup F K sigma 0).1 hsigmaMem cO
  have hsumCong : CongruentAtDepth 1
      (∑ sigma : Gal(K/F), sigma (cLift : K))
      (∑ _sigma : Gal(K/F), (cLift : K)) := by
    rw [congruentAtDepth_iff_sub_mem_lattice, ← Finset.sum_sub_distrib]
    exact sum_mem_lattice K (fun sigma _ ↦
      (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1 (hsigma sigma))
  have htraceCong : CongruentAtDepth 1
      (algebraMap F K (trace F K (cLift : K)))
      ((Module.finrank F K : K) * (cLift : K)) := by
    rw [hsumEq]
    simpa only [Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      nsmul_eq_mul] using hsumCong
  let traceO : ringOfIntegers F :=
    ⟨trace F K (cLift : K),
      (mem_lattice_zero_iff F).1 htraceLiftIntegral⟩
  let traceKO : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) traceO
  let rhsO : ringOfIntegers K :=
    (Module.finrank F K : ringOfIntegers K) * cO
  have hresidueTraceEq : residueMap K traceKO = residueMap K rhsO := by
    rw [residueMap_eq_residueMap_iff]
    exact (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1 (by
      simpa [traceKO, traceO, rhsO, cO,
        Valuation.HasExtension.val_algebraMap] using htraceCong)
  have hleft : residueMap K traceKO =
      e (reduce F (trace F K (cLift : K)) htraceLiftIntegral) := by
    change residueMap K traceKO = e (residueMap F traceO)
    rw [show e (residueMap F traceO) =
        extensionResidueMap F K (residueMap F traceO) by
      exact PhaseReductionResidualCoordinateSource.residueEquiv_apply
        P.hres (residueMap F traceO)]
    rfl
  have hright : residueMap K rhsO =
      (Module.finrank F K : ResidueField K) *
        e (ramifiedHasseTameCoordinate F K P d dK) := by
    change residueMap K
      ((Module.finrank F K : ringOfIntegers K) * cO) = _
    rw [map_mul, map_natCast]
    rw [show residueMap K cO =
        e (ramifiedHasseTameCoordinate F K P d dK) by
      simpa only [e, cO, reduce] using hcResidue.symm]
  have htraceResidue :
      reduce F (trace F K (cLift : K)) htraceLiftIntegral =
        (Module.finrank F K : ResidueField F) *
          ramifiedHasseTameCoordinate F K P d dK := by
    apply e.injective
    rw [map_mul, map_natCast, ← hleft, hresidueTraceEq, hright]
  have hinputA :
      ramifiedHasseLocalInput F K P dK a =
        algebraMap F K a * ramifiedHasseLocalInput F K P dK 1 := by
    simp only [ramifiedHasseLocalInput, map_one, mul_one]
    ring
  have htraceA :
      trace F K (ramifiedHasseLocalInput F K P dK a) =
        a * trace F K (ramifiedHasseLocalInput F K P dK 1) := by
    rw [hinputA]
    simpa [Algebra.smul_def] using
      (Algebra.trace F K).map_smul a
        (ramifiedHasseLocalInput F K P dK 1)
  have hquotA :
      trace F K (ramifiedHasseLocalInput F K P dK a) /
          (ramifiedHasseLowerUniformizer F K P : F) ^ d =
        a * trace F K (cLift : K) := by
    rw [htraceA, htraceOne]
    calc
      (a * ((ramifiedHasseLowerUniformizer F K P : F) ^ d *
          trace F K (cLift : K))) /
            (ramifiedHasseLowerUniformizer F K P : F) ^ d =
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d *
          (a * trace F K (cLift : K))) /
            (ramifiedHasseLowerUniformizer F K P : F) ^ d := by ring
      _ = a * trace F K (cLift : K) :=
        mul_div_cancel_left₀ _ (pow_ne_zero _ (Units.ne_zero
          (ramifiedHasseLowerUniformizer F K P)))
  have hproductMem : a * trace F K (cLift : K) ∈ lattice F 0 := by
    simpa using mul_mem_lattice F ha htraceLiftIntegral
  let aO : ringOfIntegers F :=
    ⟨a, (mem_lattice_zero_iff F).1 ha⟩
  let productO : ringOfIntegers F := aO * traceO
  have hreduceProduct :
      reduce F (a * trace F K (cLift : K)) hproductMem =
        reduce F a ha *
          reduce F (trace F K (cLift : K)) htraceLiftIntegral := by
    change residueMap F productO = _
    rw [map_mul]
    rfl
  calc
    reduce F
        (trace F K (ramifiedHasseLocalInput F K P dK a) /
          (ramifiedHasseLowerUniformizer F K P : F) ^ d) _ =
      reduce F (a * trace F K (cLift : K)) hproductMem := by
        apply (reduce_eq_reduce_iff F _ _).2
        rw [hquotA]
        exact CongruentAtDepth.refl _
    _ = reduce F a ha *
        reduce F (trace F K (cLift : K)) htraceLiftIntegral := hreduceProduct
    _ = (Module.finrank F K : ResidueField F) * reduce F a ha *
        ramifiedHasseTameCoordinate F K P d dK := by
      rw [htraceResidue]
      ring

/-- Reduction of the second elementary symmetric coefficient of an integral
upper element, using the actual tame Galois conjugates. -/
private theorem ramifiedHasse_localFieldInfinite
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] : Infinite E := by
  let f : ℤ → E := fun n ↦ (exists_ord_eq E n).choose
  have hf : Function.Injective f := by
    intro m n hmn
    have hm : ord E (f m) = (m : WithTop ℤ) :=
      (exists_ord_eq E m).choose_spec
    have hn : ord E (f n) = (n : WithTop ℤ) :=
      (exists_ord_eq E n).choose_spec
    exact WithTop.coe_injective
      (hm.symm.trans ((congrArg (ord E) hmn).trans hn))
  exact Infinite.of_injective f hf

private theorem reduce_elementarySymmetric_two
    (P : PrimeCyclicPreparation F K)
    (u : ringOfIntegers K)
    (hE : elementarySymmetric F K 2 (u : K) ∈ lattice F 0) :
    let e := PhaseReductionResidualCoordinateSource.residueEquiv P.hres
    e (reduce F (elementarySymmetric F K 2 (u : K)) hE) =
      ((Module.finrank F K).choose 2 : ResidueField K) *
        residueMap K u ^ 2 := by
  dsimp only
  letI : Infinite F := ramifiedHasse_localFieldInfinite F
  let e := PhaseReductionResidualCoordinateSource.residueEquiv P.hres
  let eF : ringOfIntegers F :=
    ⟨elementarySymmetric F K 2 (u : K), (mem_lattice_zero_iff F).1 hE⟩
  let eK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) eF
  let cu : Gal(K/F) → ringOfIntegers K :=
    fun σ ↦ galoisIntegerEquiv F K σ u
  let S : ringOfIntegers K :=
    ∑ t ∈ (Finset.univ : Finset Gal(K/F)).powersetCard 2,
      ∏ σ ∈ t, cu σ
  have hfield : (eK : K) = (S : K) := by
    have h := algebraMap_elementarySymmetric_eq_esymm_galois F K 2 (u : K)
    rw [galoisConjugates, Finset.esymm_map_val] at h
    calc
      (eK : K) = algebraMap F K (elementarySymmetric F K 2 (u : K)) := rfl
      _ = ∑ t ∈ (Finset.univ : Finset Gal(K/F)).powersetCard 2,
          ∏ σ ∈ t, σ (u : K) := h
      _ = (S : K) := by
        dsimp only [S, cu]
        push_cast
        rfl
  have heK : eK = S := by
    ext
    exact hfield
  have hconj (σ : Gal(K/F)) : residueMap K (cu σ) = residueMap K u := by
    have hmem : σ ∈ lowerRamificationGroup F K 0 := by
      rw [P.lowerRamificationGroup_zero_eq_top]
      trivial
    have hcong := (mem_lowerRamificationGroup F K σ 0).1 hmem u
    change residueMap K (galoisIntegerEquiv F K σ u) = residueMap K u
    rw [residueMap_eq_residueMap_iff]
    exact (congruentAtDepth_iff_sub_mem_lattice K 1 _ _).1 hcong
  have hS : residueMap K S =
      ((Module.finrank F K).choose 2 : ResidueField K) *
        residueMap K u ^ 2 := by
    calc
      residueMap K S =
          ∑ t ∈ (Finset.univ : Finset Gal(K/F)).powersetCard 2,
            ∏ σ ∈ t, residueMap K (cu σ) := by
              simp only [S, map_sum, map_prod]
      _ = ∑ _t ∈ (Finset.univ : Finset Gal(K/F)).powersetCard 2,
            residueMap K u ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        have htcard : t.card = 2 := (Finset.mem_powersetCard.mp ht).2
        calc
          ∏ σ ∈ t, residueMap K (cu σ) =
              ∏ _σ ∈ t, residueMap K u := by
                apply Finset.prod_congr rfl
                intro σ _
                exact hconj σ
          _ = residueMap K u ^ t.card := by rw [Finset.prod_const]
          _ = residueMap K u ^ 2 := by rw [htcard]
      _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
        simp only [nsmul_eq_mul]
  calc
    e (reduce F (elementarySymmetric F K 2 (u : K)) hE) =
        residueMap K eK := by
      rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
      unfold reduce
      change extensionResidueMap F K (residueMap F eF) = residueMap K eK
      exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation F) (ValuativeRel.valuation K) eF
    _ = residueMap K S := by rw [heK]
    _ = _ := hS

/-- The exact tame second-symmetric coordinate, including the binomial
coefficient needed in residue characteristic two. -/
private theorem tame_secondCoordinate_eq
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (ht0 : P.t = 0) (x : ResidueField F) :
    ramifiedHasseSecondCoordinate F K P G x =
      ((Module.finrank F K).choose 2 : ResidueField F) * x ^ 2 *
        ramifiedHasseTameCoordinate F K P d dK ^ 2 := by
  let e := PhaseReductionResidualCoordinateSource.residueEquiv P.hres
  obtain ⟨cLift, hcLift, hcResidue⟩ := G.tameCoordinate_origin ht0
  let cO : ringOfIntegers K :=
    ⟨(cLift : K), (mem_lattice_zero_iff K).1 cLift.property⟩
  let a : F := teichmuller F x
  have ha : a ∈ lattice F 0 :=
    (mem_lattice_zero_iff F).2 (teichmuller F x).property
  let aO : ringOfIntegers F :=
    ⟨a, (mem_lattice_zero_iff F).1 ha⟩
  let aOK : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) aO
  let uO : ringOfIntegers K := cO * aOK
  have hy : ramifiedHasseLocalInput F K P dK a =
      algebraMap F K ((ramifiedHasseLowerUniformizer F K P : F) ^ d) *
        (uO : K) := by
    unfold ramifiedHasseLocalInput
    change (ramifiedHasseUpperUniformizer F K P : K) ^ dK *
        algebraMap F K a =
      algebraMap F K ((ramifiedHasseLowerUniformizer F K P : F) ^ d) *
        ((cO : K) * algebraMap F K a)
    have hcO : (cO : K) =
        (ramifiedHasseUpperUniformizer F K P : K) ^ dK /
          algebraMap F K ((ramifiedHasseLowerUniformizer F K P : F) ^ d) :=
      hcLift
    rw [hcO]
    have hden : algebraMap F K
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ≠ 0 := by
      simpa only [map_zero] using (algebraMap F K).injective.ne
        (pow_ne_zero _ (Units.ne_zero _))
    field_simp [hden]
  have hvalue : ramifiedHasseSecondCoordinateValue F K P d dK a =
      elementarySymmetric F K 2 (uO : K) := by
    unfold ramifiedHasseSecondCoordinateValue
    rw [hy, low_elementarySymmetric_algebraMap_mul]
    have hpi : (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) ≠ 0 :=
      pow_ne_zero _ (Units.ne_zero _)
    rw [show ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ^ 2 =
        (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d) by
      rw [← pow_mul]
      congr 1
      omega]
    field_simp [hpi]
  have hvalueMem : ramifiedHasseSecondCoordinateValue F K P d dK a ∈
      lattice F 0 := ramifiedHasseSecondCoordinateValue_mem F K P G a ha
  have hEu : elementarySymmetric F K 2 (uO : K) ∈ lattice F 0 := by
    rw [← hvalue]
    exact hvalueMem
  have hcore := reduce_elementarySymmetric_two F K P uO hEu
  have haResidue : residueMap K aOK = e x := by
    rw [PhaseReductionResidualCoordinateSource.residueEquiv_apply]
    change residueMap K
        (algebraMap (ringOfIntegers F) (ringOfIntegers K) aO) =
      extensionResidueMap F K x
    rw [show x = residueMap F aO by simp [aO, a]]
    exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (ValuativeRel.valuation F) (ValuativeRel.valuation K) aO
  have huResidue : residueMap K uO =
      e (ramifiedHasseTameCoordinate F K P d dK * x) := by
    dsimp only [uO]
    rw [map_mul, map_mul, haResidue]
    have hcOResidue : residueMap K cO =
        reduce K (cLift : K) cLift.property := by
      unfold reduce
      congr 1
    rw [hcOResidue, ← hcResidue]
  have hredValue :
      reduce F (ramifiedHasseSecondCoordinateValue F K P d dK a) hvalueMem =
        reduce F (elementarySymmetric F K 2 (uO : K)) hEu := by
    unfold reduce
    congr 1
    apply Subtype.ext
    exact hvalue
  apply e.injective
  rw [map_mul, map_mul, map_pow, map_pow]
  rw [show e (ramifiedHasseSecondCoordinate F K P G x) =
      e (reduce F (elementarySymmetric F K 2 (uO : K)) hEu) by
    unfold ramifiedHasseSecondCoordinate
    dsimp only [a]
    rw [hredValue]]
  rw [hcore, huResidue, map_mul]
  simp only [map_natCast]
  ring

end TameArithmetic

noncomputable section

section CaseAssembly

private theorem tame_powerRelation_of_transport
    {k : Type u} [Field k] [Fintype k]
    {theta : FiniteAddChar k} (lower : HasseFunction k theta)
    {upper : k → ℂ} {ell : ℕ} {c : k} (hc : c ≠ 0)
    (trace second : k → k)
    (htransport : ∀ x,
      upper x = lower (trace x) * theta (-second x))
    (htrace : ∀ x, trace x = (ell : k) * x * c)
    (hsecond : ∀ x,
      second x = (ell.choose 2 : k) * x ^ 2 * c ^ 2) :
    ∀ x, upper (c⁻¹ * x) = lower x ^ ell := by
  intro x
  rw [htransport, htrace, hsecond]
  have harg : (ell : k) * (c⁻¹ * x) * c = ell • x := by
    simp only [nsmul_eq_mul]
    field_simp [hc]
  rw [harg, lower.map_nsmul]
  have hquad :
      (ell.choose 2 : k) * (c⁻¹ * x) ^ 2 * c ^ 2 =
        (ell.choose 2 : k) * x ^ 2 := by
    field_simp [hc]
  rw [hquad, AddChar.map_neg_eq_inv]
  have htheta : (theta ((ell.choose 2 : k) * x ^ 2) : ℂ) ≠ 0 := by
    intro hzero
    have hnorm := finiteAddChar_norm theta ((ell.choose 2 : k) * x ^ 2)
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  field_simp [htheta]

private theorem charTwo_difficultParity
    {ell binaryDegree : ℕ} [Fact ell.Prime]
    (hell2 : ell ≠ 2)
    (hdiv : ell ∣ 2 ^ binaryDegree - 1)
    (hmod : ell % 8 = 3 ∨ ell % 8 = 5) :
    Even binaryDegree := by
  by_contra heven
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp heven
  have hpowPos : 1 ≤ 2 ^ binaryDegree := one_le_pow₀ (by omega)
  obtain ⟨a, ha⟩ := hdiv
  have hpowNat : 2 ^ binaryDegree = 1 + ell * a := by omega
  have hpowZMod : (2 : ZMod ell) ^ binaryDegree = 1 := by
    have hz := congrArg (fun n : ℕ ↦ (n : ZMod ell)) hpowNat
    simpa using hz
  have hsquare : IsSquare (2 : ZMod ell) := by
    rw [isSquare_iff_exists_sq]
    refine ⟨(2 : ZMod ell) ^ (r + 1), ?_⟩
    calc
      (2 : ZMod ell) = (2 : ZMod ell) ^ binaryDegree * 2 := by
        rw [hpowZMod, one_mul]
      _ = (2 : ZMod ell) ^ (2 * r + 1) * 2 := by rw [hr]
      _ = ((2 : ZMod ell) ^ (r + 1)) ^ 2 := by ring
  have hgood : ell % 8 = 1 ∨ ell % 8 = 7 :=
    (ZMod.exists_sq_eq_two_iff hell2).mp hsquare
  omega

variable (F K : Type u)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Free F K] [Module.Finite F K]
  [PrimeCyclicExtension F K]

private theorem ramifiedHasseFiniteComparison
    (P : PrimeCyclicPreparation F K) {d dK : ℕ}
    (G : RamifiedHasseLocalGeometryData F K P d dK)
    (chiF : LocalQuasiCharData F) (psiF : LocalAddCharData F)
    (chiK : LocalQuasiCharData K) (psiK : LocalAddCharData K)
    (lower : RamifiedHasseOddStationaryPhase F chiF psiF)
    (upper : RamifiedHasseOddStationaryPhase K chiK psiK)
    (hlowerDepth : lower.d = d) (hupperDepth : upper.d = dK)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hGamma : (upper.denominator : Kˣ) =
      Units.map (algebraMap F K) (lower.denominator : Fˣ))
    (hc : (upper.representative.representative : K) =
      algebraMap F K (lower.representative.representative : F))
    (hlowerDelta : lower.delta =
      phaseReductionSourceCoordinate F
        (ramifiedHasseLowerUniformizer F K P) d)
    (hupperDelta : upper.delta =
      phaseReductionSourceCoordinate K
        (ramifiedHasseUpperUniformizer F K P) dK)
    [Fact (Module.finrank F K).Prime] :
    letI := residueFieldFintype F
    RamifiedHasseFiniteCase (ResidueField F) (Module.finrank F K) P.t
      (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
        G.lowerDepth_pos G.stableRange G.stationaryDepthRelation)
      (ramifiedHasseTameCoordinate F K P d dK)
      (ramifiedHasseWildLambda F K P)
      (fun x ↦ lower.function x)
      (fun x ↦ upper.function
        (PhaseReductionResidualCoordinateSource.residueEquiv P.hres x)) := by
  letI := residueFieldFintype F
  let theta := lamprechtResidualAddChar F chiF psiF lower.d
    lower.conductor_eq lower.conductor_large lower.denominator lower.delta
      lower.delta_order
  have htheta : theta ≠ 1 :=
    lamprechtResidualAddChar_ne_one F chiF psiF lower.d lower.conductor_eq
      lower.conductor_large lower.denominator lower.delta lower.delta_order
      lower.representative.toLamprecht (by
        simpa only [stationaryDepthOfConductorDecomposition] using
          lower.representative.toLamprecht_represents)
  have htransport := ramifiedHasse_actual_function_transport F K P G
    chiF psiF chiK psiK lower upper hlowerDepth hupperDepth hchi hpsi hGamma
      hc hlowerDelta hupperDelta
  rcases Nat.eq_zero_or_pos P.t with ht0 | htpos
  · have hc0 := G.tameCoordinate_ne_zero ht0
    have htrace (x : ResidueField F) :
        ramifiedHasseTraceCoordinate F K P G x =
          (Module.finrank F K : ResidueField F) * x *
            ramifiedHasseTameCoordinate F K P d dK := by
      let a : F := teichmuller F x
      have ha : a ∈ lattice F 0 :=
        (mem_lattice_zero_iff F).2 (teichmuller F x).property
      simpa [ramifiedHasseTraceCoordinate,
        ramifiedHasseTraceCoordinateValue, a] using
        tame_normalizedTraceResidue F K P G ht0 a ha
    have hsecond := tame_secondCoordinate_eq F K P G ht0
    have hpower := tame_powerRelation_of_transport lower.function hc0
      (ramifiedHasseTraceCoordinate F K P G)
      (ramifiedHasseSecondCoordinate F K P G) htransport htrace hsecond
    have hdiv : Module.finrank F K ∣
        Fintype.card (ResidueField F) - 1 := by
      simpa only [residueCard] using
        tame_degree_dvd_residueCard_sub_one F K P ht0
    have hepsilon := tame_epsilonResidue_eq F K P G ht0
    by_cases hchar2 : residueCharacteristic F = 2
    · letI : CharP (ResidueField F) 2 := ringChar.of_eq hchar2
      obtain ⟨scale, hscale, q, lambda, hlower⟩ :=
        exists_charTwo_affine_normalForm htheta lower.function
      letI : Algebra (ZMod 2) (ResidueField F) :=
        ZMod.algebra (ResidueField F) 2
      let f := Module.finrank (ZMod 2) (ResidueField F)
      have hcard : Fintype.card (ResidueField F) = 2 ^ f := by
        simpa only [ZMod.card] using
          (Module.card_eq_pow_finrank
            (K := ZMod 2) (V := ResidueField F))
      have hparity : Module.finrank F K % 8 = 3 ∨
          Module.finrank F K % 8 = 5 → Even f := by
        intro hmod
        apply charTwo_difficultParity (by
          obtain ⟨r, hr⟩ := G.degree_odd
          omega) (by rwa [← hcard]) hmod
      let D : RamifiedHasseCharTwoFiniteData (ResidueField F)
          (Module.finrank F K)
          (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
            G.lowerDepth_pos G.stableRange G.stationaryDepthRelation)
          (fun x ↦ lower.function x)
          (fun x ↦ upper.function
            (PhaseReductionResidualCoordinateSource.residueEquiv P.hres x)) :=
        { degree_odd := G.degree_odd
          q := q
          c := ramifiedHasseTameCoordinate F K P d dK
          c_ne_zero := hc0
          epsilon_eq := hepsilon
          coordinateScale := scale
          coordinateScale_ne_zero := hscale
          lambda := lambda
          lower_pointwise := hlower
          binaryDegree := f
          card_eq_two_pow := hcard
          traceOne := absoluteTraceChar_one (ResidueField F)
          difficultParity := hparity
          upper_binomial_pointwise := fun x ↦ by
            calc
              upper.function
                  (PhaseReductionResidualCoordinateSource.residueEquiv P.hres
                    ((ramifiedHasseTameCoordinate F K P d dK * scale)⁻¹ * x)) =
                  upper.function
                    (PhaseReductionResidualCoordinateSource.residueEquiv P.hres
                      ((ramifiedHasseTameCoordinate F K P d dK)⁻¹ *
                        (scale⁻¹ * x))) := by
                    apply congrArg (fun y ↦ upper.function
                      (PhaseReductionResidualCoordinateSource.residueEquiv
                        P.hres y))
                    rw [mul_inv_rev]
                    ring
              _ = lower.function (scale⁻¹ * x) ^ Module.finrank F K :=
                hpower (scale⁻¹ * x)
              _ = q.affine lambda x ^ Module.finrank F K := by rw [hlower]
              _ = q.affine lambda ((Module.finrank F K : ResidueField F) * x) *
                  absoluteTraceChar (ResidueField F)
                    (-(((Module.finrank F K).choose 2 : ResidueField F) *
                      x ^ 2)) :=
                (ramifiedHasseCharTwo_binomialCorrection q lambda
                  (Module.finrank F K) x).symm }
      exact .charTwo ht0 D rfl
    · have hscalar := tame_degree_scalar_ne_zero hdiv
      obtain ⟨alpha, hlower⟩ :=
        lower.exists_lower_normalForm F chiF psiF hchar2
      let D := RamifiedHasseTameOddFiniteData.of_powerRelation
        (upper := fun x ↦ upper.function
          (PhaseReductionResidualCoordinateSource.residueEquiv P.hres x))
        hchar2 theta
        htheta G.degree_odd hscalar
        (ramifiedHasseTameCoordinate F K P d dK) hc0 hepsilon alpha
        (tame_quadraticSign hchar2 G.degree_odd hscalar hdiv) hlower hpower
      exact .tameOdd ht0 D rfl
  · have hchar : residueCharacteristic F = Module.finrank F K :=
      residueCharacteristic_eq_degree_of_positive_isLowerBreak F K P.ht htpos
        P.piK P.hpiK P.hgen
    letI : CharP (ResidueField F) (Module.finrank F K) := ringChar.of_eq hchar
    have hp2 : Module.finrank F K ≠ 2 := by
      obtain ⟨r, hr⟩ := G.degree_odd
      omega
    obtain ⟨alpha, hlower⟩ :=
      lower.exists_lower_normalForm F chiF psiF (hchar ▸ hp2)
    have hepsilon :=
      RamifiedHasseLocalGeometryData.wild_epsilonResidue_eq
        (F := F) (K := K) G htpos
    -- Newton's identity and the positive-break trace depth give the exact
    -- wild upper quadratic coefficient.
    have htrace (x : ResidueField F) :
        ramifiedHasseTraceCoordinate F K P G x = 0 := by
      unfold ramifiedHasseTraceCoordinate
      let a : F := teichmuller F x
      have ha : a ∈ lattice F 0 :=
        (mem_lattice_zero_iff F).2 (teichmuller F x).property
      apply (residueMap_eq_zero_iff F _).2
      change ramifiedHasseTraceCoordinateValue F K P d dK a ∈ lattice F 1
      unfold ramifiedHasseTraceCoordinateValue
      apply (div_mem_lattice_iff F
        ((ramifiedHasseLowerUniformizer F K P : F) ^ d)
        (trace F K (ramifiedHasseLocalInput F K P dK a)) (d : ℤ) 1 (by
          simpa only [phaseReductionSourceCoordinate_coe] using
            phaseReductionSourceCoordinate_order F
              (ramifiedHasseLowerUniformizer F K P)
              G.lowerUniformizer_order d)).2
      simpa only [Int.natCast_add, Nat.cast_one] using
        G.traceDepth_of_break_pos htpos a ha
    have hsecond (x : ResidueField F) :
        -ramifiedHasseSecondCoordinate F K P G x =
          (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
            G.lowerDepth_pos G.stableRange G.stationaryDepthRelation) / 2 *
              x ^ 2 := by
      let a : F := teichmuller F x
      have ha : a ∈ lattice F 0 :=
        (mem_lattice_zero_iff F).2 (teichmuller F x).property
      let y := ramifiedHasseLocalInput F K P dK a
      let z := ramifiedHasseTraceCoordinateValue F K P d dK a
      have hz : z ∈ lattice F 0 :=
        ramifiedHasseTraceCoordinateValue_mem F K P G a ha
      let e2 := ramifiedHasseSecondCoordinateValue F K P d dK a
      have he2 : e2 ∈ lattice F 0 :=
        ramifiedHasseSecondCoordinateValue_mem F K P G a ha
      let pi2 : F := (ramifiedHasseLowerUniformizer F K P : F) ^ (2 * d)
      have hpi2 : pi2 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
      have htraceFactor :
          (ramifiedHasseLowerUniformizer F K P : F) ^ d * z =
            trace F K y := by
        unfold z ramifiedHasseTraceCoordinateValue y
        exact mul_div_cancel₀ _ (pow_ne_zero _
          (Units.ne_zero (ramifiedHasseLowerUniformizer F K P)))
      have hsecondFactor : pi2 * e2 = elementarySymmetric F K 2 y := by
        unfold e2 ramifiedHasseSecondCoordinateValue pi2 y
        exact mul_div_cancel₀ _ (pow_ne_zero _
          (Units.ne_zero (ramifiedHasseLowerUniformizer F K P)))
      have hant : Finset.HasAntidiagonal.antidiagonal 1 =
          ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
      have hnewton := elementarySymmetric_newton_identity F K y 2
      simp [hant, galoisPowerSum] at hnewton
      have hnewton' :
          (2 : F) * elementarySymmetric F K 2 y =
            trace F K y ^ 2 - trace F K (y ^ 2) := by
        calc
          _ = (-1 : F) ^ 3 *
              (trace F K (y ^ 2) + -(trace F K y * trace F K y)) :=
            hnewton
          _ = _ := by ring
      have hproduct : trace F K (y ^ 2) =
          ramifiedHasseNormalizedTrace F K P d dK * pi2 * a ^ 2 := by
        calc
          trace F K (y ^ 2) = trace F K (y * y) := by rw [pow_two]
          _ = ramifiedHasseNormalizedTrace F K P d dK * pi2 * a * a := by
            simpa only [y, pi2] using G.traceProductSpecialization a a
          _ = _ := by ring
      have hfield : (2 : F) * e2 =
          z ^ 2 - ramifiedHasseNormalizedTrace F K P d dK * a ^ 2 := by
        apply mul_left_cancel₀ hpi2
        calc
          pi2 * ((2 : F) * e2) =
              (2 : F) * (pi2 * e2) := by ring
          _ = (2 : F) * elementarySymmetric F K 2 y := by rw [hsecondFactor]
          _ = trace F K y ^ 2 - trace F K (y ^ 2) := hnewton'
          _ = pi2 *
              (z ^ 2 - ramifiedHasseNormalizedTrace F K P d dK * a ^ 2) := by
            rw [← htraceFactor, hproduct]
            have hpipow :
                ((ramifiedHasseLowerUniformizer F K P : F) ^ d) ^ 2 =
                  pi2 := by
              unfold pi2
              rw [← pow_mul]
              congr 1
              omega
            rw [mul_pow, hpipow]
            ring
      let zO : ringOfIntegers F :=
        ⟨z, (mem_lattice_zero_iff F).1 hz⟩
      let e2O : ringOfIntegers F :=
        ⟨e2, (mem_lattice_zero_iff F).1 he2⟩
      let epsilonO : ringOfIntegers F :=
        ⟨ramifiedHasseNormalizedTrace F K P d dK,
          (mem_lattice_zero_iff F).1 G.epsilon_mem_lattice_zero⟩
      let aO : ringOfIntegers F :=
        ⟨a, (mem_lattice_zero_iff F).1 ha⟩
      have hfieldO : (2 : ringOfIntegers F) * e2O =
          zO ^ 2 - epsilonO * aO ^ 2 := by
        ext
        exact hfield
      have hres := congrArg (residueMap F) hfieldO
      have hzred : residueMap F zO =
          ramifiedHasseTraceCoordinate F K P G x := by
        unfold ramifiedHasseTraceCoordinate
        rfl
      have he2red : residueMap F e2O =
          ramifiedHasseSecondCoordinate F K P G x := by
        unfold ramifiedHasseSecondCoordinate
        rfl
      have hepsilonred : residueMap F epsilonO =
          ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
            G.lowerDepth_pos G.stableRange G.stationaryDepthRelation := by
        rw [G.epsilonResidue_eq]
        rfl
      have hared : residueMap F aO = x := by simp [aO, a]
      simp only [map_mul, map_sub, map_pow] at hres
      rw [hzred, he2red, hepsilonred, hared, htrace x] at hres
      simp only [zero_pow (by omega : 2 ≠ 0), zero_sub] at hres
      change (2 : ResidueField F) *
          ramifiedHasseSecondCoordinate F K P G x = _ at hres
      have htwo : (2 : ResidueField F) ≠ 0 := by
        intro hzero
        have hdvd := (CharP.cast_eq_zero_iff (ResidueField F)
          (Module.finrank F K) 2).mp hzero
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdvd with hp1 | hp2'
        · exact (PrimeCyclicExtension.degree_prime F K).ne_one hp1
        · exact hp2 hp2'
      rw [show
        (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
            G.lowerDepth_pos G.stableRange G.stationaryDepthRelation) / 2 *
              x ^ 2 =
          ((ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
            G.lowerDepth_pos G.stableRange G.stationaryDepthRelation) *
              x ^ 2) / 2 by ring]
      apply (eq_div_iff htwo).2
      calc
        (-ramifiedHasseSecondCoordinate F K P G x) * 2 =
            -((2 : ResidueField F) *
              ramifiedHasseSecondCoordinate F K P G x) := by ring
        _ = (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
              G.lowerDepth_pos G.stableRange G.stationaryDepthRelation) *
            x ^ 2 := by rw [hres]; ring
    let D : RamifiedHasseWildOddFiniteData (Module.finrank F K)
        (ResidueField F)
        (ramifiedHasseNormalizedTraceResidue F K P G.degree_odd
          G.lowerDepth_pos G.stableRange G.stationaryDepthRelation)
        (fun x ↦ lower.function x)
        (fun x ↦ upper.function
          (PhaseReductionResidualCoordinateSource.residueEquiv P.hres x)) :=
      { odd_prime := hp2
        psi := theta
        psi_ne_one := htheta
        alpha := alpha
        lambda := ramifiedHasseWildLambda F K P
        lambda_ne_zero := G.wildLambda_ne_zero htpos
        epsilon_eq := hepsilon
        lower_pointwise := hlower
        upper_pointwise := wild_upper_normalForm lower.function
          (ramifiedHasseTraceCoordinate F K P G)
          (ramifiedHasseSecondCoordinate F K P G) htransport htrace hsecond }
    exact .wildOdd htpos D rfl

end CaseAssembly

end

noncomputable section

/-- Construct the complete stable-high odd ramified Hasse certificate from
the standard high-row representative.  The lower and upper phases use the
source uniformizer powers, the ordered mapped denominator pair, and the
literal transported stationary representative. -/
noncomputable def ramifiedHassePreparation
    (F K : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Algebra F K] [ValuativeExtension F K]
    [Module.Free F K] [Module.Finite F K]
    [PrimeCyclicExtension F K]
    (P : PrimeCyclicPreparation F K)
    (chiF : LocalQuasiCharData F) (chiK : LocalQuasiCharData K)
    (psiF : LocalAddCharData F) (psiK : LocalAddCharData K)
    {d dK : ℕ}
    (hF : IsStationaryConductorDecomposition chiF.conductor d 1)
    (hK : IsStationaryConductorDecomposition chiK.conductor dK 1)
    (hchi : chiK.character = chiF.character.compNorm)
    (hpsi : psiK.character = psiF.character.compTrace)
    (hodd : Odd (Module.finrank F K))
    (hd : P.t + 1 ≤ d)
    (gammaF : Fˣ)
    (hgammaF : ord F (gammaF : F) =
      (((chiF.conductor : ℤ) + psiF.conductor : ℤ) : WithTop ℤ))
    (H : HighStableOddParameterData F K P.ht P.hres P.piK P.hpiK P.hgen
      chiF chiK psiF psiK hF hK hchi hpsi hodd hd gammaF hgammaF)
    (R : StationaryClassRepresentative F chiF psiF hF gammaF hgammaF)
    [Fact (Module.finrank F K).Prime] :
    let deltaF := phaseReductionSourceCoordinate F
      (ramifiedHasseLowerUniformizer F K P) d
    let deltaK := phaseReductionSourceCoordinate K
      (ramifiedHasseUpperUniformizer F K P) dK
    let hdeltaF := phaseReductionSourceCoordinate_order F
      (ramifiedHasseLowerUniformizer F K P)
      (ramifiedHasseLowerUniformizer_order F K P) d
    let hdeltaK := phaseReductionSourceCoordinate_order K
      (ramifiedHasseUpperUniformizer F K P)
      (ramifiedHasseUpperUniformizer_order F K P) dK
    let lower := HighStableOddParameterData.downstairsOddStationaryPhase
      F K P.ht P.hres P.piK P.hpiK P.hgen chiF chiK psiF psiK
        hF hK hchi hpsi hodd hd gammaF hgammaF H R deltaF hdeltaF
    let upper := HighStableOddParameterData.upstairsOddStationaryPhase
      F K P.ht P.hres P.piK P.hpiK P.hgen chiF chiK psiF psiK
        hF hK hchi hpsi hodd hd gammaF hgammaF H R deltaK hdeltaK
    RamifiedHasseComparisonData F K chiF psiF chiK psiK lower upper
      (Module.finrank F K) P.t := by
  dsimp only
  let deltaF := phaseReductionSourceCoordinate F
    (ramifiedHasseLowerUniformizer F K P) d
  let deltaK := phaseReductionSourceCoordinate K
    (ramifiedHasseUpperUniformizer F K P) dK
  have hdeltaF : ord F (deltaF : F) = ((d : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order F
      (ramifiedHasseLowerUniformizer F K P)
      (ramifiedHasseLowerUniformizer_order F K P) d
  have hdeltaK : ord K (deltaK : K) = ((dK : ℤ) : WithTop ℤ) :=
    phaseReductionSourceCoordinate_order K
      (ramifiedHasseUpperUniformizer F K P)
      (ramifiedHasseUpperUniformizer_order F K P) dK
  let lower := HighStableOddParameterData.downstairsOddStationaryPhase
    F K P.ht P.hres P.piK P.hpiK P.hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R deltaF hdeltaF
  let upper := HighStableOddParameterData.upstairsOddStationaryPhase
    F K P.ht P.hres P.piK P.hpiK P.hgen chiF chiK psiF psiK
      hF hK hchi hpsi hodd hd gammaF hgammaF H R deltaK hdeltaK
  have hdepth :
      2 * dK + (Module.finrank F K - 1) * P.t =
        2 * Module.finrank F K * d := by
    have hm := H.conductorRelation
    rw [hF.conductor_eq, hK.conductor_eq] at hm
    ring_nf at hm ⊢
    have hfinrankpos : 0 < Module.finrank F K := Module.finrank_pos
    omega
  have hdpos : 0 < d := by omega
  let G := ramifiedHasseLocalGeometry F K P hodd hdpos (Or.inr hd) hdepth
  refine {
    odd_prime := by obtain ⟨r, hr⟩ := hodd; omega
    degree_eq := rfl
    lowerBreak := P.ht
    residueDegree_eq_one := P.hres
    multiplicativePullback := hchi
    additivePullback := hpsi
    conductor_ge_break := by rw [hF.conductor_eq]; omega
    stableRange := Or.inr hd
    stationaryDepthRelation := hdepth
    conductorDenominatorRelation :=
      high_compNorm_add_compTrace_conductor_eq F K P.ht P.hres P.piK
        P.hpiK P.hgen chiF chiK psiF psiK hchi hpsi (by
          rw [hF.conductor_eq]
          omega)
    denominator_eq := rfl
    representative_eq := by
      exact HighStableOddParameterData.upstairsRepresentative_coe
        F K P.ht P.hres P.piK P.hpiK P.hgen chiF chiK psiF psiK
          hF hK hchi hpsi hodd hd gammaF hgammaF H R
    piF := ramifiedHasseLowerUniformizer F K P
    piK := ramifiedHasseUpperUniformizer F K P
    piF_uniformizer :=
      (ord_eq_one_iff_isUniformizer F _).1
        (ramifiedHasseLowerUniformizer_order F K P)
    piK_uniformizer :=
      (ord_eq_one_iff_isUniformizer K _).1
        (ramifiedHasseUpperUniformizer_order F K P)
    norm_uniformizer := G.norm_uniformizer
    lower_delta_eq := rfl
    upper_delta_eq := rfl
    residueEquiv := PhaseReductionResidualCoordinateSource.residueEquiv P.hres
    residueEquiv_eq_extension := G.residueEquiv_eq_extension
    residueLift := fun x ↦ teichmuller F x
    residueLift_spec := G.residueLift_spec
    normTruncation := fun x ↦ by
      change norm F K
          (1 + ramifiedHasseCriticalInput F K
            (ramifiedHasseUpperUniformizer F K P) dK
              (fun x ↦ teichmuller F x) x) -
          (1 + trace F K (ramifiedHasseCriticalInput F K
            (ramifiedHasseUpperUniformizer F K P) dK
              (fun x ↦ teichmuller F x) x) +
            elementarySymmetric F K 2 (ramifiedHasseCriticalInput F K
              (ramifiedHasseUpperUniformizer F K P) dK
                (fun x ↦ teichmuller F x) x)) ∈
          lattice F ((2 * d + 1 : ℕ) : ℤ)
      simpa only [ramifiedHasseCriticalInput, ramifiedHasseLocalInput] using
        G.normTruncation (teichmuller F x)
          ((mem_lattice_zero_iff F).2 (teichmuller F x).property)
    traceDepth := fun x ↦ by
      change trace F K (ramifiedHasseCriticalInput F K
        (ramifiedHasseUpperUniformizer F K P) dK
          (fun x ↦ teichmuller F x) x) ∈ lattice F (d : ℤ)
      simpa only [ramifiedHasseCriticalInput, ramifiedHasseLocalInput] using
        G.traceDepth (teichmuller F x)
          ((mem_lattice_zero_iff F).2 (teichmuller F x).property)
    secondSymmetricDepth := fun x ↦ by
      change elementarySymmetric F K 2 (ramifiedHasseCriticalInput F K
        (ramifiedHasseUpperUniformizer F K P) dK
          (fun x ↦ teichmuller F x) x) ∈ lattice F ((2 * d : ℕ) : ℤ)
      simpa only [ramifiedHasseCriticalInput, ramifiedHasseLocalInput] using
        G.secondSymmetricDepth (teichmuller F x)
          ((mem_lattice_zero_iff F).2 (teichmuller F x).property)
    epsilon := ramifiedHasseNormalizedTrace F K P d dK
    epsilon_order := G.epsilon_order
    epsilon_mem_lattice_zero := G.epsilon_mem_lattice_zero
    epsilonResidue := ramifiedHasseNormalizedTraceResidue F K P hodd hdpos
      (Or.inr hd) hdepth
    epsilonResidue_eq := G.epsilonResidue_eq
    tameCoordinate := ramifiedHasseTameCoordinate F K P d dK
    tameCoordinate_origin := G.tameCoordinate_origin
    wildLambda := ramifiedHasseWildLambda F K P
    wildLambda_origin := G.wildLambda_origin
    epsilonTraceSpecialization := G.epsilonTraceSpecialization
    finiteComparison := ramifiedHasseFiniteComparison F K P G chiF psiF
      chiK psiK lower upper rfl rfl hchi hpsi rfl
      (HighStableOddParameterData.upstairsRepresentative_coe
        F K P.ht P.hres P.piK P.hpiK P.hgen chiF chiK psiF psiK
          hF hK hchi hpsi hodd hd gammaF hgammaF H R)
      rfl rfl }

end

end LanglandsFirstMainLemma
