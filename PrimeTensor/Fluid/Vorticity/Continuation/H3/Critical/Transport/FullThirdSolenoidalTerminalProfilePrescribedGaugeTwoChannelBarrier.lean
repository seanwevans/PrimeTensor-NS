import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeEndpointEscape
import Mathlib.Tactic

/-!
# Terminal Fourier carrier versus actual projected-source tail

An arbitrary positive H3 dissipation profile H(n)^8 on genuine minimal
physical windows is paid by the annular eighth moment and the terminal
physical momentum primitive. The endpoint inequality has TWO distinct
channels: the fixed terminal kinetic Fourier tail and the real Bochner-L1
projected Navier--Stokes source tail. This module separates their necessary
quartic contributions, without assuming either dominates.

For each selected window at frequency n with outer radius Q=N(n)+2:

  H(n)^4 < 14 Q^4 ||P_n^+ Fourier(U)||
    OR
  H(n)^4 < 14 Q^4 ||Fourier|| * int_(tau(n))^T ||G(t)|| dt.

The factor 14 is strictly larger than sqrt(4*48), so the alternative follows
from the existing sharp 48 eighth-moment estimate. It exposes an actual
physical-source coercivity requirement whenever terminal highpass alone
cannot pay the chosen scale. No H3 continuation or uniform upper bound on
the selected outer radius is inferred.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A genuine eighth-order Fourier moment paid by two nonnegative amplitudes
forces one amplitude to pay an explicit quartic fraction. Numerically,
48 * 4 = 192 < 196 = 14^2. This is a STRICT dichotomy. -/
theorem thirdFull_eighthMoment_twoChannel_quarticDichotomy244
    (R Q A S : ℝ)
    (hR : 0 < R) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hMoment : R ^ 2 < 48 * Q ^ 2 * (A + S) ^ 2) :
    R < 14 * Q * A ∨ R < 14 * Q * S := by
  by_contra hNot
  push_neg at hNot
  obtain ⟨hLeft, hRight⟩ := hNot
  have hBoth : 7 * Q * (A + S) ≤ R := by
    nlinarith only [hLeft, hRight]
  have hNonneg : 0 ≤ 7 * Q * (A + S) := by positivity
  have hSquared := (sq_le_sq₀ hNonneg hR.le).2 hBoth
  have hSquareNonneg : 0 ≤ (Q * (A + S)) ^ 2 := sq_nonneg _
  nlinarith only [hSquared, hMoment, hSquareNonneg]

/-- Two-channel source-tail alternative in the native eighth-power frequency
coordinates. No square-root or reciprocal of the tail integral is used. -/
theorem thirdFull_eighthMoment_terminalCarrier_or_sourceTail244
    (H Q A S : ℝ)
    (hH : 0 < H) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hMoment : H ^ 8 < 48 * Q ^ 8 * (A + S) ^ 2) :
    H ^ 4 < 14 * Q ^ 4 * A ∨
      H ^ 4 < 14 * Q ^ 4 * S := by
  have hSquared :
      (H ^ 4) ^ 2 < 48 * (Q ^ 4) ^ 2 * (A + S) ^ 2 := by
    convert hMoment using 1 <;> ring
  exact thirdFull_eighthMoment_twoChannel_quarticDichotomy244
    (H ^ 4) (Q ^ 4) A S
    (pow_pos hH 4) (pow_nonneg hQ 4) hA hS hSquared

/-- If terminal kinetic highpass alone is too small, the actual projected
momentum-source L1 tail MUST supply the missing quartic charge. -/
theorem thirdFull_eighthMoment_sourceTail_forced_of_terminalSmall244
    (H Q A S : ℝ)
    (hH : 0 < H) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hMoment : H ^ 8 < 48 * Q ^ 8 * (A + S) ^ 2)
    (hTerminalSmall : 14 * Q ^ 4 * A ≤ H ^ 4) :
    H ^ 4 < 14 * Q ^ 4 * S := by
  rcases thirdFull_eighthMoment_terminalCarrier_or_sourceTail244
      H Q A S hH hQ hA hS hMoment with hCarrier | hSource
  · exact False.elim ((not_lt_of_ge hTerminalSmall) hCarrier)
  · exact hSource

/-- The actual Navier--Stokes minimal profile-window endpoint inequality
splits into terminal Fourier carrier or ACTUAL projected-source action.
Both quantities come from the single terminal physical Bochner primitive,
not from arbitrary source/energy bounds or independent spectral limits. -/
theorem thirdFullPhysical_profileWindow_terminalCarrier_or_sourceTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (H : ℕ → ℝ) (hH : ∀ n : ℕ, 0 < H n)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T)
    (U : H3PhysicalRealFinVectorL2Hilbert)
    (hU : ∀ t : ℝ, t ∈ Set.Ioo b T →
      h3AuditInitialOldPhysicalHilbertTotal hH3 t +
        ∫ r in t..T, h3PathActualProjectedMomentumSource244 hH3 r ∂volume = U)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (n : ℕ)
    (ht : τ n ∈ Set.Ioo b T)
    (hWindow : ThirdFullProfileMinimalAttainedSourceWindow244 hH3
      (fun n : ℕ => (H n) ^ 8) τ N K C δ n)
    (s : ℝ) (hs : s ∈ Set.Icc (τ n) (τ n + δ n)) :
    (H n) ^ 4 < 14 * (((N n : ℝ) + 2) ^ 4) *
      ‖thirdFullSpectralVelocityHighRadialApply244 n
        (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap U)‖ ∨
    (H n) ^ 4 < 14 * (((N n : ℝ) + 2) ^ 4) *
      (‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
        (∫ r in τ n..T,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)) := by
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let A : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 n (F U)‖
  let S : ℝ := ‖F‖ * (∫ r in τ n..T, ‖G r‖ ∂volume)
  have hIntegralNonneg :
      0 ≤ ∫ r in τ n..T, ‖G r‖ ∂volume :=
    intervalIntegral.integral_nonneg ht.2.le (fun r _ => norm_nonneg (G r))
  have hS : 0 ≤ S := mul_nonneg (norm_nonneg F) hIntegralNonneg
  have hMoment :=
    thirdFullPhysical_profile_window_endpointTailMomentBarrier244
      hH3 hClass (fun n : ℕ => (H n) ^ 8) b hb hG U hU
      τ N K C δ n ht hWindow s hs
  change (H n) ^ 8 < 48 * (((N n : ℝ) + 2) ^ 8) * (A + S) ^ 2 at hMoment
  change (H n) ^ 4 < 14 * (((N n : ℝ) + 2) ^ 4) * A ∨
    (H n) ^ 4 < 14 * (((N n : ℝ) + 2) ^ 4) * S
  exact thirdFull_eighthMoment_terminalCarrier_or_sourceTail244
    (H n) ((N n : ℝ) + 2) A S
    (hH n) (by positivity) (norm_nonneg _) hS hMoment

/-- SAME gauge-dependent disjoint physical windows as the established
prescribed-gauge theorem. Every selected crossing must be paid at quartic
order by EITHER the fixed physical terminal Fourier carrier OR the actual
projected-source L1 action. The finite total viscous charge and diverging
outer-to-gauge ratio are kept on precisely these witnesses. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_twoChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (H : ℕ → ℝ) (hH : ∀ n : ℕ, 1 ≤ H n) :
    ∃ (U : H3PhysicalRealFinVectorL2Hilbert)
      (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) τ N K C δ (v k)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ k : ℕ,
        (H (v k)) ^ 4 < 14 * (((N (v k) : ℝ) + 2) ^ 4) *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
            (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap U)‖ ∨
        (H (v k)) ^ 4 < 14 * (((N (v k) : ℝ) + 2) ^ 4) *
          (‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
            (∫ r in τ (v k)..T,
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))) ∧
      Tendsto (fun k : ℕ =>
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap U)‖ +
        ‖h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap‖ *
          (∫ r in τ (v k)..T,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hCharges, hMoment, hAmp, hEscape⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_endpointTailEscape244
      hH3 hClass b hb hNoTrace hDInt H hH
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hSplit (k : ℕ) :
      (H (v k)) ^ 4 < 14 * (((N (v k) : ℝ) + 2) ^ 4) *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (H (v k)) ^ 4 < 14 * (((N (v k) : ℝ) + 2) ^ 4) *
        (‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume)) := by
    have hδ : 0 ≤ δ (v k) := by
      rcases (hWindows k).1.1 with
        ⟨_, _, _, hpos, _, _, _, _, _, _, _, _, _⟩
      exact hpos.le
    have hEnd : τ (v k) < T := by
      rcases (hWindows k).1.1 with
        ⟨_, _, _, _, _, hBefore, _, _, _, _, _, _, _⟩
      linarith only [hδ, hBefore]
    have hStart : τ (v k) ∈
        Set.Icc (τ (v k)) (τ (v k) + δ (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right hδ⟩
    have hEight := hMoment k (τ (v k)) hStart
    have hIntegralNonneg :
        0 ≤ ∫ r in τ (v k)..T, ‖G r‖ ∂volume :=
      intervalIntegral.integral_nonneg hEnd.le
        (fun r _ => norm_nonneg (G r))
    have hS : 0 ≤ ‖F‖ *
        (∫ r in τ (v k)..T, ‖G r‖ ∂volume) :=
      mul_nonneg (norm_nonneg _) hIntegralNonneg
    change (H (v k)) ^ 8 <
        48 * (((N (v k) : ℝ) + 2) ^ 8) *
          (‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ +
            ‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume)) ^ 2 at hEight
    exact thirdFull_eighthMoment_terminalCarrier_or_sourceTail244
      (H (v k)) ((N (v k) : ℝ) + 2)
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖
      (‖F‖ * (∫ r in τ (v k)..T, ‖G r‖ ∂volume))
      (lt_of_lt_of_le zero_lt_one (hH (v k)))
      (by positivity) (norm_nonneg _) hS hEight
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hSplit, hAmp⟩

end
end PrimeTensor.FirstMonomialTriad
