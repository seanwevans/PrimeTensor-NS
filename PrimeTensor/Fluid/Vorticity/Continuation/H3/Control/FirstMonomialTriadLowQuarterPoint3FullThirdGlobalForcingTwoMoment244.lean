import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalAbsoluteLerayBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption
import Mathlib.Tactic

/-!
# Two-moment control of the actual global absolute Leray transfer

The earlier terminal Fourier forcing program proved the integrability of the
fifth radial velocity mass and cubic weighted Leray-forcing mass at each
strict physical time. This module uses their exact half-power factorization

    q^4 |Re <z,f>| <= q^4 |z| |f|

and the square (q |z| - |f|)^2 >= 0 to prove the concrete bound

    G(t) <= M5(t) + M3(t).

Here G = 2 sum integral q^4 |Re <z,f>| is the *existing* cutoff-independent
absolute transfer. M5 = sum integral q^5 |z|^2 and M3 is the existing cubic
forcing square mass, sum integral q^3 |f|^2.

This is a genuine two-moment estimate, not terminal-uniform control of the
fifth velocity mass, nor an anti-concentration theorem. Crucially, the sign
of the fifth diffusion contribution in the concentration-rate upper bound
prevents simply cancelling M5 against the absolute Leray estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1400000

noncomputable local instance axisFintypeH3GlobalForcingTwoMoment244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The *full* fifth radial velocity square mass, without a spectral cutoff. -/
noncomputable def h3PathTopFourierGlobalFifthMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2

/-- Weighted pointwise Young bound with the exact three/five radial powers. -/
theorem h3_globalForcingTwoMoment_pointwise244
    (q : ℝ) (hq : 0 ≤ q) (z f : ℂ) :
    2 * q ^ 4 * |(inner ℂ z f).re| ≤
      q ^ 5 * ‖z‖ ^ 2 + q ^ 3 * ‖f‖ ^ 2 := by
  have hRe : |(inner ℂ z f).re| ≤ ‖z‖ * ‖f‖ := by
    calc
      |(inner ℂ z f).re| ≤ ‖inner ℂ z f‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖z‖ * ‖f‖ := norm_inner_le_norm z f
  have hWeight : 0 ≤ 2 * q ^ 4 := by positivity
  have hBound := mul_le_mul_of_nonneg_left hRe hWeight
  have hSquare : 0 ≤ q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2 :=
    mul_nonneg (pow_nonneg hq 3) (sq_nonneg _)
  have hIdentity :
      q ^ 5 * ‖z‖ ^ 2 + q ^ 3 * ‖f‖ ^ 2 -
          2 * q ^ 4 * (‖z‖ * ‖f‖) =
        q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2 := by ring
  calc
    2 * q ^ 4 * |(inner ℂ z f).re| ≤
      2 * q ^ 4 * (‖z‖ * ‖f‖) := hBound
    _ ≤ q ^ 5 * ‖z‖ ^ 2 + q ^ 3 * ‖f‖ ^ 2 := by
      linarith only [hSquare, hIdentity]

/-- The concrete absolute Leray profile cannot exceed the sum of the
physical fifth velocity moment and the previously constructed cubic forcing
mass. Both masses are finite at each strict physical time. -/
theorem h3Path_globalAbsoluteLerayTransfer_le_fifth_add_cubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
        hH3 hClass ht ≤
      h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass ht := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let z : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ => h3SpectralScalarRawFourierL2 (U j) ξ
  let f : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ => h3RawFinLerayOuterProductDivergence U U j ξ
  let g : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 4 * (inner ℂ (z j ξ) (f j ξ)).re
  let m5 : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 5 * ‖z j ξ‖ ^ 2
  let m3 : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 3 * ‖f j ξ‖ ^ 2
  have hEach (j : Fin 3) :
      2 * ∫ ξ : H3FourierPoint3, |g j ξ| ≤
        (∫ ξ : H3FourierPoint3, m5 j ξ) +
          (∫ ξ : H3FourierPoint3, m3 j ξ) := by
    have hIntG : Integrable (g j) (volume : Measure H3FourierPoint3) := by
      change Integrable
        (h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j) (volume : Measure H3FourierPoint3)
      exact integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
        hH3 hClass ht j
    have hInt5 : Integrable (m5 j) (volume : Measure H3FourierPoint3) := by
      change Integrable (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 5 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3)
      simpa only [U, htAbs] using
        (integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
          hH3 hClass ht j)
    have hInt3 : Integrable (m3 j) (volume : Measure H3FourierPoint3) := by
      change Integrable
        (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j) (volume : Measure H3FourierPoint3)
      exact integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j
    have hAbsG : Integrable (fun ξ : H3FourierPoint3 => |g j ξ|)
        (volume : Measure H3FourierPoint3) := by
      simpa only [Real.norm_eq_abs] using hIntG.norm
    have hPoint : ∀ ξ : H3FourierPoint3,
        2 * |g j ξ| ≤ m5 j ξ + m3 j ξ := by
      intro ξ
      dsimp only [g, m5, m3, z, f]
      rw [abs_mul, abs_of_nonneg (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ) 4)]
      simpa only [mul_assoc] using
        (h3_globalForcingTwoMoment_pointwise244
          (h3FourierGradientSquare ξ)
          (h3FourierGradientSquare_nonneg ξ)
          (h3SpectralScalarRawFourierL2 (U j) ξ)
          (h3RawFinLerayOuterProductDivergence U U j ξ))
    have hIntegral :
        (∫ ξ : H3FourierPoint3, 2 * |g j ξ|) ≤
          ∫ ξ : H3FourierPoint3, m5 j ξ + m3 j ξ :=
      integral_mono (hAbsG.const_mul 2) (hInt5.add hInt3) hPoint
    calc
      2 * ∫ ξ : H3FourierPoint3, |g j ξ| =
          ∫ ξ : H3FourierPoint3, 2 * |g j ξ| := by
            rw [integral_const_mul]
      _ ≤ ∫ ξ : H3FourierPoint3, m5 j ξ + m3 j ξ := hIntegral
      _ = (∫ ξ : H3FourierPoint3, m5 j ξ) +
          (∫ ξ : H3FourierPoint3, m3 j ξ) :=
            integral_add hInt5 hInt3
  unfold h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
    h3PathTopFourierGlobalFifthMass244
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
  dsimp only
  change (∑ j : Fin 3, 2 * ∫ ξ : H3FourierPoint3, |g j ξ|) ≤
    (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m5 j ξ) +
      (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m3 j ξ)
  calc
    (∑ j : Fin 3, 2 * ∫ ξ : H3FourierPoint3, |g j ξ|) ≤
      ∑ j : Fin 3,
        ((∫ ξ : H3FourierPoint3, m5 j ξ) +
          (∫ ξ : H3FourierPoint3, m3 j ξ)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hEach j
    _ = (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m5 j ξ) +
      (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m3 j ξ) := by
        rw [Finset.sum_add_distrib]

/-- The absolute-transfer normalized rate is controlled by the sum of
physical fifth velocity and cubic forcing masses, divided by actual D3. -/
theorem h3Path_globalAbsoluteTransferNormalizedRate_le_twoMoments244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244
        hH3 hClass t ht ≤
      (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass ht) /
        h3TerminalPhysicalTopDissipation3Path hClass t := by
  have hPos : 0 < h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass ht]
    exact hD
  unfold h3PathTopFourierGlobalAbsoluteTransferNormalizedRate244
  exact (div_le_div_iff_of_pos_right hPos).2
    (h3Path_globalAbsoluteLerayTransfer_le_fifth_add_cubic244
      hH3 hClass ht)

/-- An exact near-Young variance secant forces one of the existing radial
velocity/forcing masses to contribute after the physical gradient and viscous
budgets. This is a necessary two-mass inequality, not a terminal bound. -/
theorem h3Path_nearYoung_forces_fifthPlusCubic_after_budgets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    ∃ r : ℝ, ∃ hr : r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) -
        36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r -
        h3PathTopFourierGlobalViscousCeiling244 hH3 hClass r
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ ≤
      (h3PathTopFourierGlobalFifthMass244 hH3 hClass r
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ +
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩) /
        h3TerminalPhysicalTopDissipation3Path hClass r := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_nearYoung_forces_fullAbsoluteTransfer_after_viscousGradientBudgets244
      hH3 hClass hs ht hst hMass hD hK hNear
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hBound := h3Path_globalAbsoluteTransferNormalizedRate_le_twoMoments244
    hH3 hClass hrClass (hD r ⟨hr.1.le, hr.2.le⟩)
  refine ⟨r, hr, ?_⟩
  exact hRate.trans hBound

end
end PrimeTensor.FirstMonomialTriad
