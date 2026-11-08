import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxPhysicalPDEClock
import Mathlib.Tactic

/-!
# Adverse signed sixth flux forces actual high-radial H3 escape

The physical PDE clock from the previous module decomposes an exact signed
LowMax(R) complex flux increment into (i) Schwartz recovery errors, (ii) the
actual momentum-source L1 action on a strict gap, and (iii) two actual high-H3
spectral tails at the observation times.

We prove a quantitative converse: if the imaginary-part signed flux increment
is at least η and the first two charges, WITH the exact cubic amplitude factor,
pay at most η/2, then the high tails must pay η/2. Consequently one of the two
actual high tails pays η/4. No terminal H3 norm bound is postulated and the
positive margin does not emerge from a nonpositive or absolute-value ansatz.

The coefficient grows with the fixed radius, and the Schwartz recovery error
premise is explicitly weighted by the actual recovery amplitudes. The result
is not a radius-uniform or unconditional continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev EA3 := PrimeTensor.Axis Depth.three
private abbrev EV3 := H3FourierPoint3

noncomputable local instance axisFintypeKineticAdverseTail244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact local complex-flux Lipschitz coefficient, retaining the cubic
amplitude of the actual Schwartz recovery states. -/
noncomputable def thirdFullKineticSignedLowMaxFluxClockWeight244
    (R : ℕ) (V W : H3SpectralVelocityState) : ℝ :=
  (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
    (1 + ‖V‖ + ‖W‖) ^ 3

/-- An adverse SIGNED imaginary sixth-flux increment that the low-band
clock and the two recovery errors cannot pay forces a positive charge from
the ACTUAL two high-H3 tails. This general interface accepts any proven
low-band clock B, and does not posit a full-H3 time derivative. -/
theorem thirdFullKinetic_signedLowMax_adverseForcesHighTail244
    (R : ℕ)
    (v w : EA3 → SchwartzMap EV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : EA3,
      (V (h3ClassicalizationFinOfAxis j) : EV3 → ℂ) =ᵐ[volume]
        (fun ξ : EV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : EA3,
      (W (h3ClassicalizationFinOfAxis j) : EV3 → ℂ) =ᵐ[volume]
        (fun ξ : EV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (X Y : H3SpectralVelocityState) (B η : ℝ)
    (hLow :
      ‖thirdFullSpectralVelocityLowRadialApply244 R X -
        thirdFullSpectralVelocityLowRadialApply244 R Y‖ ≤ B)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|)
    (hRecoveryClock :
      thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
        (‖V - X‖ + B + ‖Y - W‖) ≤ η / 2) :
    η / 2 ≤ thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖thirdFullSpectralVelocityHighRadialApply244 R X‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 R Y‖) := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  let E : ℝ := ‖V - X‖ + B + ‖Y - W‖
  let H : ℝ :=
    ‖thirdFullSpectralVelocityHighRadialApply244 R X‖ +
      ‖thirdFullSpectralVelocityHighRadialApply244 R Y‖
  have hFlux := thirdFullKinetic_lowMax_twoSnapshot_tailResolved244
    R v w V W hv hw X Y B hLow
  have hImag :
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im| ≤
      ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
        thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ := by
    rw [← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  have hCost : η ≤ A * (E + H) := by
    calc
      η ≤ |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im| := hAdverse
      _ ≤ ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
        thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ := hImag
      _ ≤ (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
        ((‖V - X‖ +
            (B + (‖thirdFullSpectralVelocityHighRadialApply244 R X‖ +
              ‖thirdFullSpectralVelocityHighRadialApply244 R Y‖))) +
          ‖Y - W‖) *
        (1 + ‖V‖ + ‖W‖) ^ 3 := hFlux
      _ = A * (E + H) := by
        dsimp only [A, E, H, thirdFullKineticSignedLowMaxFluxClockWeight244]
        ring
  have hSmall : A * E ≤ η / 2 := hRecoveryClock
  rw [mul_add] at hCost
  change η / 2 ≤ A * H
  linarith only [hCost, hSmall]

/-- On an ACTUAL strict physical time gap, the source L1 clock, the two
Schwartz recovery defects, and the signed imaginary excursion refer to
exactly the same two observation times. If their weighted cost is less than
half the adverse margin, actual spectral tails pay the remainder. -/
theorem thirdFullPhysical_strictGap_signedLowMax_adverseHighTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hy : y ∈ Set.Ioo (0 : ℝ) T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : EA3 → SchwartzMap EV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : EA3,
      (V (h3ClassicalizationFinOfAxis j) : EV3 → ℂ) =ᵐ[volume]
        (fun ξ : EV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : EA3,
      (W (h3ClassicalizationFinOfAxis j) : EV3 → ℂ) =ᵐ[volume]
        (fun ξ : EV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|)
    (hRecoveryClock :
      thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
        (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
          thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
          ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) ≤ η / 2) :
    η / 2 ≤ thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 s)‖) := by
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
  exact thirdFullKinetic_signedLowMax_adverseForcesHighTail244
    R v w V W hv hw
    (h3AuditActualSpectralVelocityTotal hH3 t)
    (h3AuditActualSpectralVelocityTotal hH3 s)
    (thirdFullFiniteBandH3WeightCeiling244 R *
      ∫ r in x..y,
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
    η hBand hAdverse hRecoveryClock

/-- Therefore ONE of the two actual observation-time high-H3 tails must
pay at least one quarter of the unnormalized signed flux excursion, with
the full radius/amplitude coefficient displayed. Neither time can be
silently discarded. -/
theorem thirdFullPhysical_strictGap_signedLowMax_oneHighTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hy : y ∈ Set.Ioo (0 : ℝ) T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : EA3 → SchwartzMap EV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : EA3,
      (V (h3ClassicalizationFinOfAxis j) : EV3 → ℂ) =ᵐ[volume]
        (fun ξ : EV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : EA3,
      (W (h3ClassicalizationFinOfAxis j) : EV3 → ℂ) =ᵐ[volume]
        (fun ξ : EV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|)
    (hRecoveryClock :
      thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
        (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
          thirdFullFiniteBandH3WeightCeiling244 R *
            (∫ r in x..y,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
          ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) ≤ η / 2) :
    η / 4 ≤ thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ∨
    η / 4 ≤ thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 s)‖ := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  let Ht : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R
    (h3AuditActualSpectralVelocityTotal hH3 t)‖
  let Hs : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R
    (h3AuditActualSpectralVelocityTotal hH3 s)‖
  have hTail := thirdFullPhysical_strictGap_signedLowMax_adverseHighTail244
    hH3 R x y hx hy hxy s t hs ht v w V W hv hw η hAdverse hRecoveryClock
  change η / 2 ≤ A * (Ht + Hs) at hTail
  change η / 4 ≤ A * Ht ∨ η / 4 ≤ A * Hs
  by_contra h
  push_neg at h
  rcases h with ⟨hFirst, hSecond⟩
  rw [mul_add] at hTail
  linarith only [hTail, hFirst, hSecond]

end
end PrimeTensor.FirstMonomialTriad
