import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDeficitTwoTimeLedger
import Mathlib.Tactic

/-!
# A finite-radius physical envelope for the exact annular deficit slope

This continues the actual two-time kinetic-deficit factorization. For one
fixed finite outer cutoff R, the coefficient multiplying the change of the
actual physical sharp highpass mass is bounded using only (1) the genuine
kinetic Fourier-ball source ceiling, (2) the actual snapshot H3 Fourier
residual, (3) the physical L2 snapshot mass, and (4) the polynomial outer
viscous base. No supremum over annuli and no source-time derivative is
postulated. The bounds are deliberately finite-R; they grow with R.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularUniformSlope244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularUniformSlope244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Monotonicity of the ACTUAL product-Lebesgue Fourier-ball volume for
arbitrary real radial cutoffs, not merely an indexed natural subsequence. -/
theorem thirdFullKinetic_fourierBallVolume_mono_real244
    (rho R : ℝ) (hUpper : rho ≤ R) :
    (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow rho) ≤
      (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow R) := by
  have hSub : h3TerminalRadialFrequencyBelow rho ⊆
      h3TerminalRadialFrequencyBelow R := by
    intro ξ hξ
    change h3FourierGradientMagnitude ξ < rho at hξ
    change h3FourierGradientMagnitude ξ < R
    exact lt_of_lt_of_le hξ hUpper
  have hFinite := h3Critical_lowRadial_fourierBall_finiteVolume R
  rw [Measure.real_def, Measure.real_def]
  exact ENNReal.toReal_mono hFinite.ne (measure_mono hSub)

/-- One real finite-radius kinetic source ceiling bounds every smaller
nonnegative cutoff. The true Fourier-ball measure is retained. -/
theorem thirdFullPhysical_kineticSourceCeiling_mono_real244
    (rho R E : ℝ) (hRho : 0 ≤ rho) (hUpper : rho ≤ R) (hE : 0 ≤ E) :
    thirdFullPhysicalKineticLowBandSourceCeiling244 rho E ≤
      thirdFullPhysicalKineticLowBandSourceCeiling244 R E := by
  let Vrho : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow rho)
  let VR : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow R)
  have hVolume : Vrho ≤ VR :=
    thirdFullKinetic_fourierBallVolume_mono_real244 rho R hUpper
  have hVR : 0 ≤ VR := measureReal_nonneg
  have hSquare : rho ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hRho hUpper 2
  have hCoeff : 18 * (rho * E) ≤ 18 * (R * E) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hUpper hE) (by norm_num)
  have hCoeffNonneg : 0 ≤ 18 * (rho * E) := by positivity
  have hCoeffSq : (18 * (rho * E)) ^ 2 ≤ (18 * (R * E)) ^ 2 :=
    pow_le_pow_left₀ hCoeffNonneg hCoeff 2
  have hInside : Vrho * (18 * (rho * E)) ^ 2 ≤
      VR * (18 * (R * E)) ^ 2 := by
    calc
      Vrho * (18 * (rho * E)) ^ 2 ≤
          VR * (18 * (rho * E)) ^ 2 :=
        mul_le_mul_of_nonneg_right hVolume (sq_nonneg _)
      _ ≤ VR * (18 * (R * E)) ^ 2 :=
        mul_le_mul_of_nonneg_left hCoeffSq hVR
  change rho ^ 2 * Real.sqrt E +
      Real.sqrt (Vrho * (18 * (rho * E)) ^ 2) ≤
    R ^ 2 * Real.sqrt E +
      Real.sqrt (VR * (18 * (R * E)) ^ 2)
  exact add_le_add
    (mul_le_mul_of_nonneg_right hSquare (Real.sqrt_nonneg E))
    (Real.sqrt_le_sqrt hInside)

/-- The genuine zero-viscosity physical outer budget is nonnegative and
monotone in the nonnegative squared annular mean frequency. -/
theorem thirdFullPhysical_outerViscousCapBase_boundedReal244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b a R : ℝ) (ha : 0 ≤ a) (hUpper : a ≤ R ^ 2) :
    0 ≤ thirdFullPhysicalOuterViscousCapBase244 u b a ∧
      thirdFullPhysicalOuterViscousCapBase244 u b a ≤
        thirdFullPhysicalOuterViscousCapBase244 u b (R ^ 2) := by
  have hE : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hPow : a ^ 2 ≤ (R ^ 2) ^ 2 :=
    pow_le_pow_left₀ ha hUpper 2
  constructor
  · unfold thirdFullPhysicalOuterViscousCapBase244
    exact add_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _)) hE)
  · unfold thirdFullPhysicalOuterViscousCapBase244
    have hMul : 2 * a ^ 2 * velocityH3Energy0At u b ≤
        2 * (R ^ 2) ^ 2 * velocityH3Energy0At u b := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPow (by norm_num)) hE
    linarith only [hMul]

/-- A single snapshot H3 spectrum bounds the ORIGINAL nonlinear
Young-gap/width cost for every annulus under radius R. -/
noncomputable def thirdFullPhysicalAnnularSnapshotYoungEnvelope244
    (R : ℝ) (U : H3SpectralVelocityState) : ℝ :=
  2 * (∑ j : Fin 3,
    ((2 * R ^ 3) *
      ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) ^ 2) +
  (2 * R ^ 10) * (∑ _j : Fin 3, (2 * ‖U‖) ^ 2)

/-- The snapshot envelope is nonnegative at each finite nonnegative R. -/
theorem thirdFullPhysical_annularSnapshotYoungEnvelope_nonneg244
    (R : ℝ) (hR : 0 ≤ R) (U : H3SpectralVelocityState) :
    0 ≤ thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R U := by
  unfold thirdFullPhysicalAnnularSnapshotYoungEnvelope244
  have hFirst : 0 ≤ (∑ j : Fin 3,
      ((2 * R ^ 3) *
        ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hSecond : 0 ≤ (∑ _j : Fin 3, (2 * ‖U‖) ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  exact add_nonneg
    (mul_nonneg (by norm_num) hFirst)
    (mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hR 10)) hSecond)

/-- Exact original physical Young-width cost is bounded by one H3 snapshot
quantity, independent of rho and sigma within the common radius R. -/
theorem thirdFullPhysical_actualYoungWidth_le_snapshotEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma R : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (hUpper : sigma ≤ R) :
    thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma ≤
      thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let hSigma : 0 ≤ sigma := hRho.trans hOrder
  let K : ℝ := thirdFullPhysicalAnnularWidthFactor244 rho sigma
  let A : Fin 3 → H3FourierComplexL2 := fun j =>
    thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
      (thirdFullPhysicalAnnularYoungResidualFourierL2244 U j)
  let B : Fin 3 → H3FourierComplexL2 := fun j =>
    thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j
  have hK : 0 ≤ K ∧ K ≤ 2 * R ^ 10 :=
    thirdFullPhysical_annularWidthFactor_bound244
      rho sigma R hRho hOrder hUpper
  have hYoungSum :
      (∑ j : Fin 3, ‖A j‖ ^ 2) ≤
      (∑ j : Fin 3,
        ((2 * R ^ 3) *
          ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (thirdFullKinetic_cubicAnnulusApply_norm_le_uniform244
        rho sigma R hSigma hUpper _) 2
  have hWidthSum :
      (∑ j : Fin 3, ‖B j‖ ^ 2) ≤
      (∑ _j : Fin 3, (2 * ‖U‖) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (thirdFullPhysical_annularRawVelocityBand_norm_le_two244 rho sigma U j) 2
  have hWidthNonneg : 0 ≤ (∑ j : Fin 3, ‖B j‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hWidthCapNonneg : 0 ≤ (∑ _j : Fin 3, (2 * ‖U‖) ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
    hH3 t rho sigma hOrder hSigma]
  change 2 * (∑ j : Fin 3, ‖A j‖ ^ 2) +
      K * (∑ j : Fin 3, ‖B j‖ ^ 2) ≤
    2 * (∑ j : Fin 3,
      ((2 * R ^ 3) *
        ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) ^ 2) +
      (2 * R ^ 10) * (∑ _j : Fin 3, (2 * ‖U‖) ^ 2)
  calc
    2 * (∑ j : Fin 3, ‖A j‖ ^ 2) +
        K * (∑ j : Fin 3, ‖B j‖ ^ 2) ≤
      2 * (∑ j : Fin 3,
        ((2 * R ^ 3) *
          ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) ^ 2) +
        K * (∑ _j : Fin 3, (2 * ‖U‖) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hYoungSum (by norm_num))
        (mul_le_mul_of_nonneg_left hWidthSum hK.1)
    _ ≤ 2 * (∑ j : Fin 3,
        ((2 * R ^ 3) *
          ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) ^ 2) +
        (2 * R ^ 10) * (∑ _j : Fin 3, (2 * ‖U‖) ^ 2) :=
      add_le_add_right (mul_le_mul_of_nonneg_right hK.2 hWidthCapNonneg) _

/-- Nonnegativity of the exact original finite-annulus Young width cost. -/
theorem thirdFullPhysical_actualYoungWidth_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    0 ≤ thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma := by
  have hK := thirdFullPhysical_annularWidthFactor_bound244
    rho sigma sigma hRho hOrder le_rfl
  rw [thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
    hH3 t rho sigma hOrder (hRho.trans hOrder)]
  unfold thirdFullPhysicalAnnularYoungWidthHilbertCost244
  have hYoung : 0 ≤ (∑ j : Fin 3,
      ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma (hRho.trans hOrder)
        (thirdFullPhysicalAnnularYoungResidualBandFourierL2244 rho sigma
          (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hWidth : 0 ≤ (∑ j : Fin 3,
      ‖h3CriticalFourierSharpLowCutoffCLM sigma
          (h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
        h3CriticalFourierSharpLowCutoffCLM rho
          (h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  exact add_nonneg (mul_nonneg (by norm_num) hYoung)
    (mul_nonneg hK.1 hWidth)

/-- A pure scalar form of the exact deficit-slope bound. It is applied
below with frequency weights and the TRUE snapshot physical source. -/
theorem thirdFullKinetic_deficitSlope_bound_of_caps244
    (a w B P Y m n Acap Wcap Bcap Pcap Ycap H : ℝ)
    (ha : 0 ≤ a) (haCap : a ≤ Acap)
    (hw : 0 ≤ w) (hwCap : w ≤ Wcap)
    (hB : 0 ≤ B) (hBcap : B ≤ Bcap)
    (hP : 0 ≤ P) (hPcap : P ≤ Pcap)
    (hY : 0 ≤ Y) (hYcap : Y ≤ Ycap)
    (hm : 0 ≤ m) (hmCap : m ≤ H)
    (hn : 0 ≤ n) (hnCap : n ≤ H) :
    |w * a * (a * (m + n) - 2 * B) - (Y + w * P)| ≤
      (Wcap * Acap) * (Acap * (2 * H) + 2 * Bcap) +
        (Ycap + Wcap * Pcap) := by
  have hAcap : 0 ≤ Acap := ha.trans haCap
  have hWcap : 0 ≤ Wcap := hw.trans hwCap
  have hBcap0 : 0 ≤ Bcap := hB.trans hBcap
  have hPcap0 : 0 ≤ Pcap := hP.trans hPcap
  have hYcap0 : 0 ≤ Ycap := hY.trans hYcap
  have hH : 0 ≤ H := hm.trans hmCap
  have hSum : 0 ≤ m + n ∧ m + n ≤ 2 * H := by
    constructor
    · exact add_nonneg hm hn
    · linarith only [hmCap, hnCap]
  have hASum : 0 ≤ a * (m + n) ∧
      a * (m + n) ≤ Acap * (2 * H) := by
    constructor
    · exact mul_nonneg ha hSum.1
    · calc
        a * (m + n) ≤ Acap * (m + n) :=
          mul_le_mul_of_nonneg_right haCap hSum.1
        _ ≤ Acap * (2 * H) :=
          mul_le_mul_of_nonneg_left hSum.2 hAcap
  have hWA : 0 ≤ w * a ∧ w * a ≤ Wcap * Acap := by
    constructor
    · exact mul_nonneg hw ha
    · calc
        w * a ≤ Wcap * a := mul_le_mul_of_nonneg_right hwCap ha
        _ ≤ Wcap * Acap := mul_le_mul_of_nonneg_left haCap hWcap
  have hInnerAbs : |a * (m + n) - 2 * B| ≤
      a * (m + n) + 2 * B := by
    apply abs_le.mpr
    constructor
    · linarith only [hASum.1]
    · linarith only [hB]
  have hInnerBound : a * (m + n) + 2 * B ≤
      Acap * (2 * H) + 2 * Bcap := by
    exact add_le_add hASum.2 (mul_le_mul_of_nonneg_left hBcap (by norm_num))
  have hInnerNonneg : 0 ≤ Acap * (2 * H) + 2 * Bcap := by
    positivity
  have hMain :
      |w * a * (a * (m + n) - 2 * B)| ≤
      (Wcap * Acap) * (Acap * (2 * H) + 2 * Bcap) := by
    rw [abs_mul, abs_of_nonneg hWA.1]
    calc
      w * a * |a * (m + n) - 2 * B| ≤
          w * a * (a * (m + n) + 2 * B) :=
        mul_le_mul_of_nonneg_left hInnerAbs hWA.1
      _ ≤ w * a * (Acap * (2 * H) + 2 * Bcap) :=
        mul_le_mul_of_nonneg_left hInnerBound hWA.1
      _ ≤ (Wcap * Acap) * (Acap * (2 * H) + 2 * Bcap) :=
        mul_le_mul_of_nonneg_right hWA.2 hInnerNonneg
  have hYP : 0 ≤ Y + w * P :=
    add_nonneg hY (mul_nonneg hw hP)
  have hYPCap : Y + w * P ≤ Ycap + Wcap * Pcap := by
    have hWP : w * P ≤ Wcap * Pcap := by
      calc
        w * P ≤ Wcap * P := mul_le_mul_of_nonneg_right hwCap hP
        _ ≤ Wcap * Pcap := mul_le_mul_of_nonneg_left hPcap hWcap
    exact add_le_add hYcap hWP
  calc
    |w * a * (a * (m + n) - 2 * B) - (Y + w * P)| ≤
        |w * a * (a * (m + n) - 2 * B)| + |Y + w * P| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (w * a * (a * (m + n) - 2 * B)) (0 : ℝ) (Y + w * P))
    _ ≤ (Wcap * Acap) * (Acap * (2 * H) + 2 * Bcap) +
        (Ycap + Wcap * Pcap) := by
      rw [abs_of_nonneg hYP]
      exact add_le_add hMain hYPCap

/-- The explicit one-snapshot finite-radius coefficient.  The variables
U and V are the genuine H3 spectral and real physical L2 states at x. -/
noncomputable def thirdFullPhysicalAnnularDeficitSlopeCeiling244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b R : ℝ) (U : H3SpectralVelocityState)
    (V : H3PhysicalRealFinVectorL2Hilbert) : ℝ :=
  let E : ℝ := velocityH3Energy0At u b
  let H : ℝ := ‖V‖ ^ 2 + 1
  let Bcap : ℝ := Real.sqrt E *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 R E)
  let Pcap : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b (R ^ 2)
  let Ycap : ℝ := thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R U
  let Wcap : ℝ := (R ^ 2) ^ 3
  (Wcap * R ^ 2) * (R ^ 2 * (2 * H) + 2 * Bcap) +
    (Ycap + Wcap * Pcap)

/-- No imaginary signed cancellation occurs in the majorant: its
coefficient is nonnegative at every nonnegative finite radius. -/
theorem thirdFullPhysical_annularDeficitSlopeCeiling_nonneg244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b R : ℝ) (hR : 0 ≤ R)
    (U : H3SpectralVelocityState)
    (V : H3PhysicalRealFinVectorL2Hilbert) :
    0 ≤ thirdFullPhysicalAnnularDeficitSlopeCeiling244 u b R U V := by
  let E : ℝ := velocityH3Energy0At u b
  let H : ℝ := ‖V‖ ^ 2 + 1
  let Bcap : ℝ := Real.sqrt E *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 R E)
  let Pcap : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b (R ^ 2)
  let Ycap : ℝ := thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R U
  let Wcap : ℝ := (R ^ 2) ^ 3
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hB : 0 ≤ Bcap := by
    dsimp only [Bcap]
    exact mul_nonneg (Real.sqrt_nonneg E)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 R E))
  have hP : 0 ≤ Pcap := by
    dsimp only [Pcap]
    exact (thirdFullPhysical_outerViscousCapBase_boundedReal244
      u b (R ^ 2) R (sq_nonneg R) le_rfl).1
  have hY : 0 ≤ Ycap :=
    thirdFullPhysical_annularSnapshotYoungEnvelope_nonneg244 R hR U
  change 0 ≤ (Wcap * R ^ 2) * (R ^ 2 * (2 * H) + 2 * Bcap) +
    (Ycap + Wcap * Pcap)
  have hW : 0 ≤ Wcap := by dsimp only [Wcap]; positivity
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg hW (sq_nonneg R))
      (add_nonneg
        (mul_nonneg (sq_nonneg R) (mul_nonneg (by norm_num) hH))
        (mul_nonneg (by norm_num) hB)))
    (add_nonneg hY (mul_nonneg hW hP))

/-- The exact two-time deficit slope is bounded simultaneously for ALL
annuli below R, provided the physical highpass mass changes by at most one.
There is no annulus-dependent coefficient or abstract source envelope. -/
theorem thirdFullPhysical_actualAnnularDeficitSlope_uniform244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b R x s rho sigma : ℝ)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) (hUpper : sigma ≤ R)
    (hMass :
      |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
       thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤ 1) :
    let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let w : ℝ := (rho ^ 2) ^ 3
    let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b))
    let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ≤
      thirdFullPhysicalAnnularDeficitSlopeCeiling244 u b R
        (h3AuditActualSpectralVelocityTotal hH3 x)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 x) := by
  let E : ℝ := velocityH3Energy0At u b
  let U : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 x
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let H : ℝ := ‖V‖ ^ 2 + 1
  let Bcap : ℝ := Real.sqrt E *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 R E)
  let Pcap : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b (R ^ 2)
  let Ycap : ℝ := thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R U
  let Wcap : ℝ := (R ^ 2) ^ 3
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt E *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 rho E)
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  have hR : 0 ≤ R := hRho.trans (hOrder.trans hUpper)
  have hA : 0 ≤ a ∧ a ≤ R ^ 2 :=
    thirdFullKinetic_annularMeanSquare_bound244 rho sigma R hRho hOrder hUpper
  have hW : 0 ≤ w := by dsimp only [w]; positivity
  have hWcap : w ≤ Wcap := by
    dsimp only [w, Wcap]
    have hSq : rho ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ hRho (hOrder.trans hUpper) 2
    exact pow_le_pow_left₀ (sq_nonneg rho) hSq 3
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.sqrt_nonneg E)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 rho E))
  have hBCap : B ≤ Bcap := by
    dsimp only [B, Bcap]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (thirdFullPhysical_kineticSourceCeiling_mono_real244
          rho R E hRho (hOrder.trans hUpper) hE) (by norm_num))
      (Real.sqrt_nonneg E)
  have hPCap : 0 ≤ P ∧ P ≤ Pcap := by
    simpa only [P, Pcap] using
      thirdFullPhysical_outerViscousCapBase_boundedReal244 u b a R hA.1 hA.2
  have hY0 : 0 ≤ Yx :=
    thirdFullPhysical_actualYoungWidth_nonneg244 hH3 x rho sigma hRho hOrder
  have hYCap : Yx ≤ Ycap :=
    thirdFullPhysical_actualYoungWidth_le_snapshotEnvelope244
      hH3 x rho sigma R hRho hOrder hUpper
  have hMx : 0 ≤ Mx := sq_nonneg _
  have hMs : 0 ≤ Ms := sq_nonneg _
  have hMx0 : Mx ≤ ‖V‖ ^ 2 := by
    change ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 ≤ ‖V‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _)
      (thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V) 2
  have hMxH : Mx ≤ H := by dsimp only [H]; linarith only [hMx0]
  have hMsH : Ms ≤ H := by
    have hAbove := (abs_le.mp hMass).2
    dsimp only [H]
    linarith only [hAbove, hMx0]
  change |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ≤
      (Wcap * R ^ 2) * (R ^ 2 * (2 * H) + 2 * Bcap) +
        (Ycap + Wcap * Pcap)
  exact thirdFullKinetic_deficitSlope_bound_of_caps244
    a w B P Yx Ms Mx (R ^ 2) Wcap Bcap Pcap Ycap H
    hA.1 hA.2 hW hWcap hB0 hBCap
    hPCap.1 hPCap.2 hY0 hYCap hMs hMsH hMx hMxH

/-- One right-hand physical time interval preserves BOTH the strict kinetic
excess and the genuine positive annular deficit floor for every annulus of
a prescribed finite-radius family. The coefficient in the error budget is
proved above from the physical source and Hilbert objects: there is NO
unproved family-supremum or independent continuity premise. -/
theorem thirdFullPhysical_actualAnnularDeficit_uniformFloorRightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b radiusMin R x margin epsilon : ℝ)
    (hRadiusMin : 0 < radiusMin) (hRadiusMax : radiusMin ≤ R)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        2 * epsilon ≤
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        ∀ rho sigma : ℝ, radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              rho (velocityH3Energy0At u b)) + margin ≤
            ((rho ^ 2 + sigma ^ 2) / 2) *
              thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
          epsilon ≤
            thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let H : ℝ := ‖V‖ ^ 2 + 1
  let C : ℝ := thirdFullPhysicalAnnularDeficitSlopeCeiling244 u b R U V
  have hR : 0 ≤ R := hRadiusMin.le.trans hRadiusMax
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hC : 0 ≤ C :=
    thirdFullPhysical_annularDeficitSlopeCeiling_nonneg244 u b R hR U V
  have hCOne : 0 < C + 1 := by linarith only [hC]
  have hHOne : 0 < H + 1 := by linarith only [hH]
  have hROne : 0 < R ^ 2 + 1 := by positivity
  let etaM : ℝ := min (1 : ℝ)
    (min (margin / (R ^ 2 + 1)) (epsilon / (4 * (C + 1))))
  let etaY : ℝ := epsilon / (4 * (H + 1))
  have hFourC : 0 < 4 * (C + 1) := by positivity
  have hFourH : 0 < 4 * (H + 1) := by positivity
  have hEtaM : 0 < etaM := by
    dsimp only [etaM]
    exact lt_min (by norm_num)
      (lt_min (div_pos hMargin hROne) (div_pos hEps hFourC))
  have hEtaY : 0 < etaY := div_pos hEps hFourH
  have hEtaMOne : etaM ≤ 1 := by
    dsimp only [etaM]
    exact min_le_left _ _
  have hEtaMRadius : etaM ≤ margin / (R ^ 2 + 1) := by
    dsimp only [etaM]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hEtaMCoeff : etaM ≤ epsilon / (4 * (C + 1)) := by
    dsimp only [etaM]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hMassMargin : R ^ 2 * etaM ≤ margin := by
    have hScale : R ^ 2 ≤ R ^ 2 + 1 := by linarith
    have hProduct : etaM * (R ^ 2 + 1) ≤ margin :=
      (le_div_iff₀ hROne).mp hEtaMRadius
    calc
      R ^ 2 * etaM ≤ (R ^ 2 + 1) * etaM :=
        mul_le_mul_of_nonneg_right hScale hEtaM.le
      _ = etaM * (R ^ 2 + 1) := by ring
      _ ≤ margin := hProduct
  have hEtaMC : etaM * C ≤ epsilon / 4 := by
    have hProduct : etaM * (4 * (C + 1)) ≤ epsilon :=
      (le_div_iff₀ hFourC).mp hEtaMCoeff
    nlinarith only [hProduct, hEtaM.le]
  have hEtaYProduct : etaY * (4 * (H + 1)) = epsilon := by
    change (epsilon / (4 * (H + 1))) * (4 * (H + 1)) = epsilon
    exact div_mul_cancel₀ epsilon (ne_of_gt hFourH)
  have hHEtaY : H * etaY ≤ epsilon / 4 := by
    nlinarith only [hEtaYProduct, hEtaY.le]
  have hBudget : etaM * C + H * etaY ≤ epsilon := by
    linarith only [hEtaMC, hHEtaY, hEps]
  obtain ⟨delta, hd, hEnd, hJoint⟩ :=
    thirdFullPhysical_actualAnnularCosts_jointRightWindow244
      hH3 R x etaY etaM hR hx hEtaY hEtaM
  refine ⟨delta, hd, hEnd, ?_⟩
  intro s hs rho sigma hRad hOrder hUpper
  have hRho : 0 ≤ rho := hRadiusMin.le.trans hRad
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  have hA : 0 ≤ a ∧ a ≤ R ^ 2 :=
    thirdFullKinetic_annularMeanSquare_bound244 rho sigma R hRho hOrder hUpper
  have hMerr : |Ms - Mx| ≤ etaM :=
    ((hJoint s hs).2 rho).le
  have hYerr : |Ys - Yx| ≤ etaY :=
    ((hJoint s hs).1 rho sigma hRho hOrder hUpper).le
  have hMs : 0 ≤ Ms := sq_nonneg _
  have hMx : 0 ≤ Mx := sq_nonneg _
  have hMx0 : Mx ≤ ‖V‖ ^ 2 := by
    change ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 ≤ ‖V‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _)
      (thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V) 2
  have hMsH : Ms ≤ H := by
    have hUpperMass := (abs_le.mp hMerr).2
    dsimp only [H]
    linarith only [hUpperMass, hEtaMOne, hMx0]
  have hLost : a * (Mx - Ms) ≤ margin := by
    have hMassLoss : Mx - Ms ≤ |Ms - Mx| := by
      have hNeg := neg_abs_le (Ms - Mx)
      linarith only [hNeg]
    calc
      a * (Mx - Ms) ≤ a * |Ms - Mx| :=
        mul_le_mul_of_nonneg_left hMassLoss hA.1
      _ ≤ a * etaM := mul_le_mul_of_nonneg_left hMerr hA.1
      _ ≤ R ^ 2 * etaM :=
        mul_le_mul_of_nonneg_right hA.2 hEtaM.le
      _ ≤ margin := hMassMargin
  have hExcessX := hExcess rho sigma hRad hOrder hUpper
  change B + 2 * margin ≤ a * Mx at hExcessX
  have hExcessS : B + margin ≤ a * Ms := by
    rw [mul_sub] at hLost
    have hFirst : B + margin ≤ a * Mx - margin := by
      linarith only [hExcessX]
    have hSecond : a * Mx - margin ≤ a * Ms := by
      linarith only [hLost]
    exact hFirst.trans hSecond
  have hSlope := thirdFullPhysical_actualAnnularDeficitSlope_uniform244
    hH3 b R x s rho sigma hRho hOrder hUpper
    (hMerr.trans hEtaMOne)
  change |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ≤ C
    at hSlope
  have hPeakX := hPeak rho sigma hRad hOrder hUpper
  change 2 * epsilon ≤ w * (a * Mx - B) ^ 2 - Mx * (Yx + w * P)
    at hPeakX
  have hFloor := thirdFullKinetic_deficitPolynomial_floor_of_errors244
    a B w P Ms Mx Ys Yx C H etaM etaY epsilon
    hC hMs hMsH hMerr hYerr hSlope hEtaY.le hPeakX hBudget
  change epsilon ≤
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma
    at hFloor
  exact ⟨hExcessS, hFloor⟩

/-- The one common finite-radius deficit window pays a true *physical* H3
viscous clock at EVERY time and for EVERY eligible annulus. This is the
self-calibrated, cap-free height from the existing physical PDE theorem. -/
theorem thirdFullPhysical_actualAnnularDeficit_uniformViscousRightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (radiusMin R x margin epsilon : ℝ)
    (hRadiusMin : 0 < radiusMin) (hRadiusMax : radiusMin ≤ R)
    (hx : x ∈ Set.Ioo b T)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        2 * epsilon ≤
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        ∀ rho sigma : ℝ, radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
          epsilon / thirdFullPhysicalAnnularCapClockFactor244
            u b rho epsilon ≤ velocityH3DissipationAt u s := by
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
  obtain ⟨delta, hd, hEnd, hWindow⟩ :=
    thirdFullPhysical_actualAnnularDeficit_uniformFloorRightWindow244
      hH3 b radiusMin R x margin epsilon hRadiusMin hRadiusMax
      hxAbs hMargin hEps hExcess hPeak
  refine ⟨delta, hd, hEnd, ?_⟩
  intro s hs rho sigma hRad hOrder hUpper
  have hRho : 0 ≤ rho := hRadiusMin.le.trans hRad
  have hsTail : s ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  obtain ⟨hExS, hFloor⟩ := hWindow s hs rho sigma hRad hOrder hUpper
  have hEx :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho := by
    linarith only [hExS, hMargin]
  exact thirdFullPhysical_annularDeficit_forces_selfCalibratedClock244
    hH3 hClass b hb rho sigma hRho hOrder s hsTail
    epsilon hEps hEx hFloor

/-- One and the same positive time width now charges the ACTUAL finite
physical H3 dissipation integral for every annulus within R. The result
still assumes uniform strict margins at x: it does not derive such margins
from terminal blowup and does not control the window as R goes to infinity. -/
theorem thirdFullPhysical_actualAnnularDeficit_uniformIntegratedClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (radiusMin R x margin epsilon : ℝ)
    (hRadiusMin : 0 < radiusMin) (hRadiusMax : radiusMin ≤ R)
    (hx : x ∈ Set.Ioo b T)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        2 * epsilon ≤
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ rho sigma : ℝ, radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        delta * (epsilon / thirdFullPhysicalAnnularCapClockFactor244
          u b rho epsilon) ≤
        ∫ r in a..T, velocityH3DissipationAt u r := by
  obtain ⟨delta, hd, hEnd, hHeight⟩ :=
    thirdFullPhysical_actualAnnularDeficit_uniformViscousRightWindow244
      hH3 hClass b hb radiusMin R x margin epsilon hRadiusMin
      hRadiusMax hx hMargin hEps hExcess hPeak
  let D : ℝ → ℝ := velocityH3DissipationAt u
  have hxClass : a < x := lt_trans hb.1 hx.1
  have hDwin : IntervalIntegrable D volume x (x + delta) := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x (x + delta) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hd.le)] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.le.trans hrIcc.1, hrIcc.2.trans hEnd.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hDnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a T)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hFull :
      (∫ r in x..(x + delta), D r) ≤
        ∫ r in a..T, D r :=
    intervalIntegral.integral_mono_interval
      hxClass.le (le_add_of_nonneg_right hd.le) hEnd.le hDnonneg hDInt
  refine ⟨delta, hd, hEnd, ?_⟩
  intro rho sigma hRad hOrder hUpper
  let A : ℝ := epsilon /
    thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon
  have hPoint (s : ℝ) (hs : s ∈ Set.Icc x (x + delta)) :
      A ≤ D s :=
    hHeight s hs rho sigma hRad hOrder hUpper
  have hLocal : delta * A ≤ ∫ r in x..(x + delta), D r := by
    have hCost := h3Path_localPositiveHeight_forces_integratedCost244
      D x (x + delta) A (by linarith only [hd]) hDwin hPoint
    calc
      delta * A = ((x + delta) - x) * A := by ring
      _ ≤ ∫ r in x..(x + delta), D r := hCost
  exact hLocal.trans hFull

end
end PrimeTensor.FirstMonomialTriad
