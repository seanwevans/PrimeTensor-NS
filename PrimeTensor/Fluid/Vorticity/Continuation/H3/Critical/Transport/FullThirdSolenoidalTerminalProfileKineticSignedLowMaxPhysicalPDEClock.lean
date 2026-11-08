import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxLipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticMovingRadialGapPDECost
import Mathlib.Tactic

/-!
# Signed low-maximum sixth flux: genuine physical PDE clock with explicit tails

The new finite-radius Lipschitz theorem estimates the signed sixth-flux
integral by the FULL weighted-H3 spectral distance between Schwartz data.
The physical momentum FTC controls only its sharp LOW-band component.

This module combines the true low/high Fourier decomposition, the actual
projected physical source action, and the signed complex Lipschitz theorem.
The price for replacing the full distance by a low-band PDE clock is explicit:
TWO genuine high-frequency H3 tails and the two Schwartz recovery errors.

In particular, a low-band PDE freezing theorem alone DOES NOT make the
signed flux freeze. The high tails cannot be suppressed using a fixed-radius
argument, and the cutoff in the signed LowMax flux differs from the sharp
projection radius. All estimates are for the literal existing project sets.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev PA3 := PrimeTensor.Axis Depth.three
private abbrev PV3 := H3FourierPoint3

noncomputable local instance axisFintypeKineticSignedPhysicalClock244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Abstract low/high bookkeeping for TWO independent Schwartz recovery
states V,W and TWO actual physical spectral states X,Y. No PDE or regularity
assumption is hidden in the tail correction. -/
private theorem thirdFullKinetic_twoSnapshot_lowHigh_distance244
    (R : ℕ) (V W X Y : H3SpectralVelocityState)
    (B : ℝ)
    (hLow :
      ‖thirdFullSpectralVelocityLowRadialApply244 R X -
        thirdFullSpectralVelocityLowRadialApply244 R Y‖ ≤ B) :
    ‖V - W‖ ≤
      (‖V - X‖ +
        (B + (‖thirdFullSpectralVelocityHighRadialApply244 R X‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R Y‖))) +
        ‖Y - W‖ := by
  have hCore : ‖X - Y‖ ≤
      B + (‖thirdFullSpectralVelocityHighRadialApply244 R X‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 R Y‖) :=
    (thirdFullSpectralVelocity_distance_le_lowDifference_highTails244
      R X Y).trans (add_le_add hLow (le_refl _))
  have hTriangle : ‖V - W‖ ≤
      (‖V - X‖ + ‖X - Y‖) + ‖Y - W‖ := by
    calc
      ‖V - W‖ = ‖(V - X) + (X - Y) + (Y - W)‖ := by
        congr 1
        abel
      _ ≤ ‖(V - X) + (X - Y)‖ + ‖Y - W‖ := norm_add_le _ _
      _ ≤ (‖V - X‖ + ‖X - Y‖) + ‖Y - W‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
  exact hTriangle.trans
    (add_le_add (add_le_add (le_refl _) hCore) (le_refl _))

/-- The actual signed complex LowMax(R) flux is controlled by an
independently supplied LOW-band spectral increment, plus the two physical
high-radial tails and the errors of the two Schwartz representatives.

This works for arbitrary independent complex Schwartz fields: neither
solenoidality nor a fictitious full-H3 time estimate is introduced. -/
theorem thirdFullKinetic_lowMax_twoSnapshot_tailResolved244
    (R : ℕ)
    (v w : PA3 → SchwartzMap PV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : PA3,
      (V (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : PA3,
      (W (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (X Y : H3SpectralVelocityState) (B : ℝ)
    (hLow :
      ‖thirdFullSpectralVelocityLowRadialApply244 R X -
        thirdFullSpectralVelocityLowRadialApply244 R Y‖ ≤ B) :
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
      ((‖V - X‖ +
          (B + (‖thirdFullSpectralVelocityHighRadialApply244 R X‖ +
            ‖thirdFullSpectralVelocityHighRadialApply244 R Y‖))) +
        ‖Y - W‖) *
      (1 + ‖V‖ + ‖W‖) ^ 3 := by
  have hDistance := thirdFullKinetic_twoSnapshot_lowHigh_distance244
    R V W X Y B hLow
  have hFlux := thirdFullKinetic_lowMax_twoSnapshot_signedFlux_lipschitz244
    R v w V W hv hw
  have hC0 : 0 ≤ h3SobolevDeweightingConstant :=
    h3SobolevDeweightingConstant_nonneg
  have hCoeff :
      0 ≤ 243 * (2 * ((R : ℝ) + 1)) ^ 7 *
        h3SobolevDeweightingConstant := by positivity
  have hPower : 0 ≤ (1 + ‖V‖ + ‖W‖) ^ 3 := by positivity
  exact hFlux.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDistance hCoeff) hPower)

/-- Genuine strict-time physical PDE clock for the complex signed sixth flux
of two (possibly unrelated) Schwartz recovery profiles. The source is the
ACTUAL Navier-Stokes projected physical momentum source on [s,t].

The high-radial terms refer to the actual H3 states at the SAME two times,
not to an invented spectral path. No terminal H3 ceiling is assumed. -/
theorem thirdFullPhysical_strictTimes_signedLowMaxSchwartzFlux_PDETail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hst : s ≤ t)
    (v w : PA3 → SchwartzMap PV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : PA3,
      (V (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : PA3,
      (W (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ)) :
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
      ((‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
          (thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in s..t,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
            (‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 t)‖ +
              ‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 s)‖))) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) *
      (1 + ‖V‖ + ‖W‖) ^ 3 := by
  exact thirdFullKinetic_lowMax_twoSnapshot_tailResolved244
    R v w V W hv hw
    (h3AuditActualSpectralVelocityTotal hH3 t)
    (h3AuditActualSpectralVelocityTotal hH3 s)
    (thirdFullFiniteBandH3WeightCeiling244 R *
      ∫ r in s..t, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
    (thirdFullPhysical_strictLowBandPDEModulus244 hH3 R s t hs ht hst)

/-- Uniform clock on an ENTIRE physical strict-time gap. Here s and t
may be chosen in either order. The only time-dependent low-band charge is
the full projected-source action on [x,y], not on a fabricated time window.
This is the interface needed to analyze adverse flux samples in kinetic gaps. -/
theorem thirdFullPhysical_strictGap_signedLowMaxSchwartzFlux_PDETail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hy : y ∈ Set.Ioo (0 : ℝ) T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : PA3 → SchwartzMap PV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : PA3,
      (V (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : PA3,
      (W (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ)) :
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
      ((‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
          (thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
            (‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 t)‖ +
              ‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 s)‖))) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) *
      (1 + ‖V‖ + ‖W‖) ^ 3 := by
  have hBand :
      ‖thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 s)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        (∫ r in x..y,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) := by
    rw [norm_sub_rev]
    exact thirdFullPhysical_strictGap_uniformLowBandPDEModulus244
      hH3 R x y hx hy hxy s t hs ht
  exact thirdFullKinetic_lowMax_twoSnapshot_tailResolved244
    R v w V W hv hw
    (h3AuditActualSpectralVelocityTotal hH3 t)
    (h3AuditActualSpectralVelocityTotal hH3 s)
    (thirdFullFiniteBandH3WeightCeiling244 R *
      ∫ r in x..y, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
    hBand

/-- The genuine signed IMAGINARY part inherits the physical PDE/tail clock.
This is the component entering the established physical sixth-flux
representation; it is not controlled by assuming the complex flux is real. -/
theorem thirdFullPhysical_strictTimes_signedImagLowMaxFlux_PDETail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hst : s ≤ t)
    (v w : PA3 → SchwartzMap PV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : PA3,
      (V (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : PA3,
      (W (h3ClassicalizationFinOfAxis j) : PV3 → ℂ) =ᵐ[volume]
        (fun ξ : PV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ)) :
    |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
      (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im| ≤
      (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
      ((‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
          (thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in s..t,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
            (‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 t)‖ +
              ‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 s)‖))) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) *
      (1 + ‖V‖ + ‖W‖) ^ 3 := by
  have hBound := thirdFullPhysical_strictTimes_signedLowMaxSchwartzFlux_PDETail244
    hH3 R s t hs ht hst v w V W hv hw
  calc
    |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im| =
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
        thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im| := by
          rw [Complex.sub_im]
    _ ≤ ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
          thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ :=
      Complex.abs_im_le_norm _
    _ ≤ _ := hBound

end
end PrimeTensor.FirstMonomialTriad
