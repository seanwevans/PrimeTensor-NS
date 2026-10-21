import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessSecant244
import PrimeTensor.Fluid.Vorticity.H3.Energy.PDE.Decomposition
import Mathlib.Tactic

/-!
# Actual PDE signed excess forced by terminal-width Fourier concentration

The previous modules derive the physical normalized radial variance
  R = 1 - E₂²/(E₀ D₃)
and its exact derivative R' = -X/(E₀ D₃)². The present module replaces
both lower-order formal energy rates inside X by the *actual* PDE pairings.
The top-dissipation rate remains its proven fourth-radial Hilbert pairing.

An exact physical variance secant and the sharp Young near-saturation bound
then force an interior PDE signed-excess rate of at least
  [R(s) - 256 δ/(27 K⁴ E₀(t))] / (t-s).
If R(s) ≥ η and the near-Young term ≤ η/2, the forced source is at least
  η/[2(T-s)], the critical terminal-width threshold.

This is a NECESSARY PDE mechanism, not a bound on the nonlinear source and
not a Navier--Stokes regularity proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- Signed spectral concentration source with actual Navier--Stokes
momentum pairings at orders zero and two, and actual fourth-radial
Hilbert derivative at the top dissipation order. -/
noncomputable def h3PathTopFourierPDESignedMiddleMomentExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  2 * velocityH3Energy2At u r * velocityH3PDEDerivative2At u p r *
      (velocityH3Energy0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r) -
    velocityH3Energy2At u r ^ 2 *
      (velocityH3PDEDerivative0At u p r *
          h3TerminalPhysicalTopDissipation3Path hClass r +
        velocityH3Energy0At u r *
          h3PathTopFourierFourthRadialPairingRate244 hH3 hClass r)

/-- Normalize the actual PDE signed excess by the physical squared
kinetic/top-dissipation product. -/
noncomputable def h3PathTopFourierPDENormalizedSignedExcessRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  h3PathTopFourierPDESignedMiddleMomentExcess244 p hH3 hClass r /
    (velocityH3Energy0At u r *
      h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2

/-- The physical signed excess is exactly the signed source with PDE
substitution in its zeroth- and second-order temporal moments. -/
theorem h3Path_signedMiddleMomentExcess_eq_PDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T) :
    h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t =
      h3PathTopFourierPDESignedMiddleMomentExcess244 p hH3 hClass t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  unfold h3PathTopFourierSignedMiddleMomentExcess244
    h3PathTopFourierPDESignedMiddleMomentExcess244
  rw [velocityH3FormalDerivative0At_eq_pde hPDE htAbs,
      velocityH3FormalDerivative2At_eq_pde hPDE htAbs]

/-- The normalized signed-excess rate used by the exact physical secant
is the genuine Navier--Stokes PDE signed-excess rate. -/
theorem h3Path_normalizedSignedExcessRate_eq_PDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t =
      h3PathTopFourierPDENormalizedSignedExcessRate244 p hH3 hClass t := by
  unfold h3PathTopFourierNormalizedSignedExcessRate244
    h3PathTopFourierPDENormalizedSignedExcessRate244
  rw [h3Path_signedMiddleMomentExcess_eq_PDE244 hH3 hClass ht hPDE]

/-- Small actual sharp Young gap at t forces a quantitative amount of
PDE signed moment production somewhere between an earlier anchor s and t.
No hypothesis on a sign or a majorant for nonlinear transport is used. -/
theorem h3Path_nearYoung_forces_PDESignedExcessSecant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    ∃ r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) ≤
        h3PathTopFourierPDENormalizedSignedExcessRate244 p hH3 hClass r := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hPDERate :=
    h3Path_normalizedSignedExcessRate_eq_PDE244
      hH3 hClass hrClass hPDE
  rw [hPDERate] at hRate
  have hYoung :=
    h3Path_topFourier_normalizedVariance_nearYoung_upper244
      hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩)
      hK (hD t ⟨hst.le, le_refl t⟩) hNear
  refine ⟨r, hr, ?_⟩
  rw [hRate]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2
  linarith only [hYoung]

/-- If a later near-Young gap is small enough to remove at least half of
a positive anchored spectral variance η, the *genuine PDE source* reaches
the reciprocal terminal-width scale η/[2(T-s)] at an interior time. -/
theorem h3Path_nearYoung_forces_terminalWidthPDESignedExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T a s t K δ η : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hη : 0 < η)
    (hAnchor : η ≤ h3PathTopFourierNormalizedRadialVariance244 u s)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ)
    (hSmall : (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) ≤ η / 2) :
    ∃ r ∈ Set.Ioo s t,
      η / (2 * (T - s)) ≤
        h3PathTopFourierPDENormalizedSignedExcessRate244 p hH3 hClass r := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_nearYoung_forces_PDESignedExcessSecant244
      hH3 hClass hPDE hs ht hst hMass hD hK hNear
  have hNum : η / 2 ≤
      h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) := by
    linarith only [hAnchor, hSmall]
  have hGap : 0 < t - s := sub_pos.mpr hst
  have hTGap : 0 < T - s := sub_pos.mpr hs.2
  have hTimeBound : t - s ≤ T - s :=
    sub_le_sub_right ht.2.le s
  have hEtaBound : η * (t - s) ≤ η * (T - s) :=
    mul_le_mul_of_nonneg_left hTimeBound hη.le
  have hTerminal : η / (2 * (T - s)) ≤ (η / 2) / (t - s) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hTGap) hGap).2
    calc
      η * (t - s) ≤ η * (T - s) := hEtaBound
      _ = (η / 2) * (2 * (T - s)) := by ring
  have hCompare : (η / 2) / (t - s) ≤
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) :=
    (div_le_div_iff_of_pos_right hGap).2 hNum
  exact ⟨r, hr, hTerminal.trans (hCompare.trans hRate)⟩

end
end PrimeTensor.FirstMonomialTriad
