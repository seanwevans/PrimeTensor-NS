import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessComparison244
import Mathlib.Tactic

/-!
# Exact physical normalized Fourier variance secants and signed-excess rate

The earlier physical derivative identity is

  R'(r) = -X(r)/(E₀(r) D₃(r))²,

with the signed excess X built from the actual order-zero and order-two
energy derivatives and the physical fourth-radial Hilbert pairing.

The real mean-value theorem upgrades the qualitative assertion that a
variance drop requires positive excess somewhere to a quantitative identity:

  ∃ r ∈ (s,t),  X(r)/(E₀(r)D₃(r))² = (R(s)-R(t))/(t-s).

Consequently, an interval-wide bound X(r) ≤ M (E₀(r)D₃(r))² implies
R(s)-R(t) ≤ M(t-s), and imposes an explicit floor on the sharp Young
gap at t. No PDE sign estimate or integrable majorant is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- The actual signed middle-moment excess, normalized by the squared
kinetic/top-dissipation product on the physical fourth-radial path. -/
noncomputable def h3PathTopFourierNormalizedSignedExcessRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r /
    (velocityH3Energy0At u r *
      h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2

/-- Exact signed-excess secant from the mean-value theorem applied to the
actual differentiable physical Fourier variance, without time integration. -/
theorem h3Path_normalizedVariance_exists_exactSignedExcessSecant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    ∃ r ∈ Set.Ioo s t,
      h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r =
        (h3PathTopFourierNormalizedRadialVariance244 u s -
          h3PathTopFourierNormalizedRadialVariance244 u t) / (t - s) := by
  let f : ℝ → ℝ := h3PathTopFourierNormalizedVarianceOnClass244 hClass
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDiffAt : ∀ r, r ∈ Set.Icc s t → DifferentiableAt ℝ f r := by
    intro r hr
    exact (h3Path_normalizedVarianceOnClass_hasDerivAt244
      hH3 hClass (hInside r hr) (hMass r hr) (hD r hr)).differentiableAt
  have hContinuous : ContinuousOn f (Set.Icc s t) := by
    intro r hr
    exact (hDiffAt r hr).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ f (Set.Ioo s t) := by
    intro r hr
    exact (hDiffAt r ⟨hr.1.le, hr.2.le⟩).differentiableWithinAt
  obtain ⟨r, hr, hSlope⟩ :=
    exists_deriv_eq_slope f hst hContinuous hDiff
  have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
  have hRate := h3Path_normalizedVariance_deriv_eq_neg_signedExcess244
    hH3 hClass (hInside r hrClosed) (hMass r hrClosed) (hD r hrClosed)
  have hAt : h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r =
      (f s - f t) / (t - s) := by
    unfold h3PathTopFourierNormalizedSignedExcessRate244
    have hDeriv : deriv f r =
        -h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r /
          (velocityH3Energy0At u r *
            h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 := hRate
    rw [hDeriv] at hSlope
    calc
      _ = -(-h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r /
            (velocityH3Energy0At u r *
              h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2) := by ring
      _ = -((f t - f s) / (t - s)) := by rw [hSlope]
      _ = (f s - f t) / (t - s) := by ring
  have hEqS : f s = h3PathTopFourierNormalizedRadialVariance244 u s :=
    h3Path_normalizedVarianceOnClass_eq_physical244 hClass hs
      (hMass s ⟨le_refl s, hst.le⟩)
      (hD s ⟨le_refl s, hst.le⟩)
  have hEqT : f t = h3PathTopFourierNormalizedRadialVariance244 u t :=
    h3Path_normalizedVarianceOnClass_eq_physical244 hClass ht
      (hMass t ⟨hst.le, le_refl t⟩)
      (hD t ⟨hst.le, le_refl t⟩)
  refine ⟨r, hr, ?_⟩
  simpa only [hEqS, hEqT] using hAt

/-- Losing at least `η` units of normalized Fourier variance requires
signed excess of at least `η/(t-s)` at some interior time, after the
exact physical kinetic/top-dissipation normalization. -/
theorem h3Path_normalizedVariance_drop_forces_excessRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t η : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDrop : η ≤ h3PathTopFourierNormalizedRadialVariance244 u s -
      h3PathTopFourierNormalizedRadialVariance244 u t) :
    ∃ r ∈ Set.Ioo s t,
      η / (t - s) ≤
        h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  refine ⟨r, hr, ?_⟩
  rw [hRate]
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2 hDrop

/-- If the genuine normalized signed excess never exceeds a finite rate M
on a positive kinetic/dissipation interval, Fourier variance can decrease
by at most M times the elapsed physical time. -/
theorem h3Path_normalizedVariance_drop_le_of_excessRate_ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hRateCeiling : ∀ r, r ∈ Set.Ioo s t →
      h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r ≤ M) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      h3PathTopFourierNormalizedRadialVariance244 u t ≤ M * (t - s) := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hBound := hRateCeiling r hr
  rw [hRate] at hBound
  exact (div_le_iff₀ (sub_pos.mpr hst)).mp hBound

/-- An interval ceiling on the signed concentration rate forces a
quantitative sharp-Young gap floor at every later near-Young time. It
reduces to the prior monotone-excess gap floor when the rate is zero. -/
theorem h3Path_nearYoung_gap_floor_of_excessRate_ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hRateCeiling : ∀ r, r ∈ Set.Ioo s t →
      h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r ≤ M)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    27 * K ^ 4 * velocityH3Energy0At u t *
      (h3PathTopFourierNormalizedRadialVariance244 u s - M * (t - s)) ≤
      256 * δ := by
  have hDrop := h3Path_normalizedVariance_drop_le_of_excessRate_ceiling244
    hH3 hClass hs ht hst hMass hD hRateCeiling
  have hLower : h3PathTopFourierNormalizedRadialVariance244 u s - M * (t - s) ≤
      h3PathTopFourierNormalizedRadialVariance244 u t := by
    linarith only [hDrop]
  have hUpper := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩) hK
      (hD t ⟨hst.le, le_refl t⟩) hNear
  have hCompare : h3PathTopFourierNormalizedRadialVariance244 u s - M * (t - s) ≤
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) :=
    hLower.trans hUpper
  have hWeight : 0 < 27 * K ^ 4 * velocityH3Energy0At u t :=
    mul_pos (mul_pos (by norm_num : (0 : ℝ) < 27) (pow_pos hK 4))
      (hMass t ⟨hst.le, le_refl t⟩)
  have hScaled := (le_div_iff₀ hWeight).mp hCompare
  calc
    27 * K ^ 4 * velocityH3Energy0At u t *
        (h3PathTopFourierNormalizedRadialVariance244 u s - M * (t - s)) =
      (h3PathTopFourierNormalizedRadialVariance244 u s - M * (t - s)) *
        (27 * K ^ 4 * velocityH3Energy0At u t) := by ring
    _ ≤ 256 * δ := hScaled

end
end PrimeTensor.FirstMonomialTriad
