import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicPhysicalSourcePeak
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopConvolutionCorridor244
import Mathlib.Tactic

/-!
# Critical dyadic physical source peak transfers to actual velocity convolutions

The accepted dyadic source-peak theorem forces, at some physical time r,

  K D3(r) < (2*pi)^6 * sum_j ||F3_j(r)||^2.

This is a statement about the real Leray forcing, not a scalar profile.
The already established order-four convolution corridor estimates EACH
F3_j by the nine actual radial order-four velocity-product convolutions.
Their input moments have order eight. We explicitly assume these raw
moments at all strict physical times: an H3 bound alone is not an
order-eight raw Fourier moment estimate.

The resulting local source-peak obstruction is the genuinely nonlinear
velocity-only condition

  K D3(r) < 3*(2*pi)^6 * A4(r)^2,

where A4 is the exact nine-pair order-four velocity convolution envelope.
Conversely, a bound of this envelope relative to D3 on the dyadic interval
precludes a normalized cubic source peak and forces a large critical anchor.
No bound on A4/D3 is asserted here; obtaining one without an extra
regularity assumption remains the mathematical frontier.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The real nine-pair order-four velocity-product convolution envelope
at a physical time; zero outside the strict energy-class interval. -/
noncomputable def thirdFullPhysicalCriticalOrderFourEnvelopeAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3RawOrderFourVelocityConvolutionEnvelope244 U
      (show ∀ k : Fin 3, H3RawFourierMomentIntegrable (8 : ℝ) (U k) from
        hMom t ht)
  else 0

/-- Each genuine third-radial Leray forcing coordinate is bounded by
exactly the same nine-term velocity-product envelope at that time. -/
theorem thirdFullPhysical_thirdRadialForcing_le_orderFourEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t‖ ≤
      thirdFullPhysicalCriticalOrderFourEnvelopeAt244 hH3 hClass hMom t := by
  have hBound :=
    h3Path_thirdRadialForcing_le_orderFourConvolutionEnvelope244
      hH3 hClass ht j (hMom t ht)
  simpa only [thirdFullPhysicalCriticalOrderFourEnvelopeAt244, dif_pos ht]
    using hBound

/-- The actual third-radial Leray forcing *sum of squares* is controlled
by the square of the nine-pair order-four velocity-product envelope.
The coefficient 3 is the exact number of physical velocity components. -/
theorem thirdFullPhysical_thirdRadialForcingMass_le_orderFourEnvelopeSquare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (ht : t ∈ Set.Ioo a T) :
    (2 * Real.pi) ^ 6 *
      (∑ j : Fin 3,
        (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ) ^ 2) ≤
      (2 * Real.pi) ^ 6 *
        (3 * (thirdFullPhysicalCriticalOrderFourEnvelopeAt244
          hH3 hClass hMom t) ^ 2) := by
  let A : ℝ := thirdFullPhysicalCriticalOrderFourEnvelopeAt244
    hH3 hClass hMom t
  have hEach (j : Fin 3) :
      (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j t‖ : ℝ) ^ 2 ≤ A ^ 2 := by
    have hBound :=
      thirdFullPhysical_thirdRadialForcing_le_orderFourEnvelope244
        hH3 hClass hMom ht j
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [A] using hBound) 2
  have hSum :
      (∑ j : Fin 3,
        (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ) ^ 2) ≤ 3 * A ^ 2 := by
    calc
      (∑ j : Fin 3,
        (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ) ^ 2) ≤
          ∑ _j : Fin 3, A ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            exact hEach j
      _ = 3 * A ^ 2 := by simp <;> ring
  have hC : 0 ≤ (2 * Real.pi) ^ 6 := by positivity
  exact mul_le_mul_of_nonneg_left (by simpa only [A] using hSum) hC

/-- The dyadic source peak therefore forces the genuine order-four
velocity-product convolution envelope to overwhelm the physical top-third
viscous mass at an interior time. No source norm has been postulated. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_orderFourVelocityConvolution244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (hMom : ∀ r (hr : r ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass hr)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K * h3TerminalPhysicalTopDissipation3Path hClass r <
        (2 * Real.pi) ^ 6 *
          (3 * (thirdFullPhysicalCriticalOrderFourEnvelopeAt244
            hH3 hClass hMom r) ^ 2) := by
  obtain ⟨r, hr, hPeak⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_thirdRadialLerayPeak244
      hH3 hClass hs ht hst hD hDouble B hB hRate K hNear
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  refine ⟨r, hr, ?_⟩
  exact lt_of_lt_of_le hPeak
    (thirdFullPhysical_thirdRadialForcingMass_le_orderFourEnvelopeSquare244
      hH3 hClass hMom hrClass)

/-- A uniform velocity-only convolution-to-dissipation ceiling removes
the high-source branch and forces the earlier critical anchor to be large.
Establishing such a ceiling from H3 dynamics is NOT claimed. -/
theorem thirdFullPhysical_dyadicOrderFourConvolutionCeiling_forces_criticalAnchorExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (hMom : ∀ r (hr : r ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass hr)
    (K : ℝ)
    (hConvolutionCeiling : ∀ r, r ∈ Set.Icc s t →
      (2 * Real.pi) ^ 6 *
        (3 * (thirdFullPhysicalCriticalOrderFourEnvelopeAt244
          hH3 hClass hMom r) ^ 2) ≤
        K * h3TerminalPhysicalTopDissipation3Path hClass r) :
    8 * Real.log 2 - 3 * K * (t - s) ≤
      Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) := by
  apply thirdFullPhysical_dyadicCubicCeiling_forces_criticalAnchorExcess244
    hH3 hClass hs ht hst hD hDouble B hB hRate K
  intro r hr
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  rw [h3Path_topCubic_eq_thirdRadialLerayNormSquares244
    hH3 hClass hrClass]
  apply (div_le_iff₀ hDr).mpr
  exact (thirdFullPhysical_thirdRadialForcingMass_le_orderFourEnvelopeSquare244
    hH3 hClass hMom hrClass).trans
      (hConvolutionCeiling r ⟨hr.1.le, hr.2.le⟩)

end
end PrimeTensor.FirstMonomialTriad
