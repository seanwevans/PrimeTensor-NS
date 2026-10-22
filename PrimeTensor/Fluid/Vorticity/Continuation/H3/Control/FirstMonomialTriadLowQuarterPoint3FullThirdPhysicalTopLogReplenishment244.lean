import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopNegativeLogVariation244
import Mathlib.Tactic

/-!
# Physical top-dissipation logarithmic replenishment versus downward variation

The preceding theorem bounds positive normalized top-phase concentration action
by the *downward* logarithmic variation of the actual physical fourth-radial
mass D3. Downward variation is not determined by endpoints unless D3 is
monotone. This file retains the equally important upward variation:

    integral downward = log D3(s) - log D3(t) + integral upward.

This is an exact identity on compact strict-time intervals, with the
integrability hypotheses explicitly retained. It counts repeated spectral
replenishment cycles rather than hiding them in a net endpoint loss.
Combining the identity with the actual near-Young necessary inequality
forces a definite positive-log-replenishment budget whenever endpoint
loss, kinetic loss, and the gradient action are insufficient.

No bound on upward log variation is asserted and no NS continuation follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual signed logarithmic time derivative of positive D3. -/
noncomputable def h3PathPhysicalTopSignedLogRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  deriv (h3TerminalPhysicalTopDissipation3Path hClass) r /
    h3TerminalPhysicalTopDissipation3Path hClass r

/-- Positive logarithmic growth of D3, zero-extended off the class tail. -/
noncomputable def h3PathPhysicalTopPositiveLogVariationRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if _hr : r ∈ Set.Ioo a T then
    max (deriv (h3TerminalPhysicalTopDissipation3Path hClass) r) 0 /
      h3TerminalPhysicalTopDissipation3Path hClass r
  else 0

/-- Algebraic Jordan decomposition of the logarithmic derivative. -/
theorem h3_scalar_downwardLog_eq_upward_sub_signed244
    (D d : ℝ) (hD : 0 < D) :
    max (-d) 0 / D = max d 0 / D - d / D := by
  have hMax : max (-d) 0 = max d 0 - d := by
    by_cases hd : 0 ≤ d
    · rw [max_eq_right (neg_nonpos.mpr hd), max_eq_left hd]
      ring
    · have hd' : d ≤ 0 := le_of_lt (lt_of_not_ge hd)
      rw [max_eq_left (neg_nonneg.mpr hd'), max_eq_right hd']
      ring
  rw [hMax]
  ring

/-- At every strict physical time, downward log variation equals upward
log variation minus the signed logarithmic derivative of D3. -/
theorem h3Path_topDownwardLog_eq_upward_sub_signed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    h3PathPhysicalTopNegativeLogVariationRate244 hClass r =
      h3PathPhysicalTopPositiveLogVariationRate244 hClass r -
        h3PathPhysicalTopSignedLogRate244 hClass r := by
  have hTop : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  unfold h3PathPhysicalTopNegativeLogVariationRate244
    h3PathPhysicalTopPositiveLogVariationRate244
    h3PathPhysicalTopSignedLogRate244
  simp only [dif_pos hr]
  exact h3_scalar_downwardLog_eq_upward_sub_signed244 _ _ hTop

/-- Derivative of the true top-mass logarithm, obtained from the existing
strong physical fourth-radial Hilbert derivative. -/
theorem h3Path_topLog_hasDerivAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    HasDerivAt
      (fun q : ℝ => Real.log (h3TerminalPhysicalTopDissipation3Path hClass q))
      (h3PathPhysicalTopSignedLogRate244 hClass r) r := by
  have hTop : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  have hDerivative := h3TerminalPhysicalTopDissipation3Path_hasDerivAt
    hH3 hClass hr
  have hLog := hDerivative.log (ne_of_gt hTop)
  -- The logarithmic chain rule returns the established Hilbert pairing.
  -- Rewrite that pairing to the derivative named in our signed-log rate.
  have hRate :
      deriv (h3TerminalPhysicalTopDissipation3Path hClass) r =
        h3PathTopFourierFourthRadialPairingRate244 hH3 hClass r :=
    hDerivative.deriv
  change HasDerivAt
    (fun q : ℝ => Real.log (h3TerminalPhysicalTopDissipation3Path hClass q))
    (deriv (h3TerminalPhysicalTopDissipation3Path hClass) r /
      h3TerminalPhysicalTopDissipation3Path hClass r) r
  rw [hRate]
  exact hLog

/-- Fundamental theorem of calculus for the physical top-mass log rate.
Its integrability is explicit: plain differentiability is insufficient. -/
theorem h3Path_topSignedLog_integral_eq_endpoint244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t) :
    (∫ r in s..t, h3PathPhysicalTopSignedLogRate244 hClass r) =
      Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) := by
  let F : ℝ → ℝ :=
    fun q => Real.log (h3TerminalPhysicalTopDissipation3Path hClass q)
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDerivative (r : ℝ) (hr : r ∈ Set.Icc s t) :
      HasDerivAt F (h3PathPhysicalTopSignedLogRate244 hClass r) r :=
    h3Path_topLog_hasDerivAt244 hH3 hClass (hInside r hr) (hD r hr)
  have hDiff : ∀ r : ℝ, r ∈ Set.uIcc s t → DifferentiableAt ℝ F r := by
    intro r hr
    rw [Set.uIcc_of_le hst] at hr
    exact (hDerivative r hr).differentiableAt
  have hOn : Set.EqOn (h3PathPhysicalTopSignedLogRate244 hClass)
      (deriv F) (Set.uIoc s t) := by
    intro r hr
    rw [Set.uIoc_of_le hst] at hr
    exact (hDerivative r ⟨hr.1.le, hr.2⟩).deriv.symm
  have hIntDeriv : IntervalIntegrable (deriv F) volume s t :=
    hLogIntegrable.congr hOn
  have hFTC := intervalIntegral.integral_deriv_eq_sub hDiff hIntDeriv
  have hEqualIntegral :
      (∫ r in s..t, deriv F r) =
        ∫ r in s..t, h3PathPhysicalTopSignedLogRate244 hClass r := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst
    intro r hr
    exact (hDerivative r ⟨hr.1.le, hr.2.le⟩).deriv
  rw [hEqualIntegral] at hFTC
  exact hFTC

/-- The exact down/up budget: total downward D3 log variation equals
net endpoint logarithmic loss PLUS all positive logarithmic replenishment. -/
theorem h3Path_topDownwardLog_integral_eq_endpoint_add_upward244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDownIntegrable : IntervalIntegrable
      (h3PathPhysicalTopNegativeLogVariationRate244 hClass) volume s t)
    (hUpIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPositiveLogVariationRate244 hClass) volume s t)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t) :
    (∫ r in s..t, h3PathPhysicalTopNegativeLogVariationRate244 hClass r) =
      Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) +
      (∫ r in s..t, h3PathPhysicalTopPositiveLogVariationRate244 hClass r) := by
  have hSplit :
      (∫ r in s..t, h3PathPhysicalTopNegativeLogVariationRate244 hClass r) =
        (∫ r in s..t, h3PathPhysicalTopPositiveLogVariationRate244 hClass r) -
          (∫ r in s..t, h3PathPhysicalTopSignedLogRate244 hClass r) := by
    calc
      _ = ∫ r in s..t,
          h3PathPhysicalTopPositiveLogVariationRate244 hClass r -
            h3PathPhysicalTopSignedLogRate244 hClass r := by
        apply intervalIntegral.integral_congr_Ioo_of_le hst
        intro r hr
        have hrClass : r ∈ Set.Ioo a T :=
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
        exact h3Path_topDownwardLog_eq_upward_sub_signed244
          hClass hrClass (hD r ⟨hr.1.le, hr.2.le⟩)
      _ = _ := intervalIntegral.integral_sub hUpIntegrable hLogIntegrable
  have hLog := h3Path_topSignedLog_integral_eq_endpoint244
    hH3 hClass hs ht hst hD hLogIntegrable
  rw [hSplit, hLog]
  ring

/-- The previous near-Young concentration burden now requires either net
D3 logarithmic loss or positive D3 logarithmic replenishment. This is
an integrated, strictly physical oscillation constraint rather than a
pointwise frequency-rate estimate. -/
theorem h3Path_nearYoung_forces_topLogReplenishment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass)) volume s t)
    (hMiddleIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass) volume s t)
    (hTopIntegrable : IntervalIntegrable
      (h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass) volume s t)
    (hLossIntegrable : IntervalIntegrable
      (h3PathPhysicalKineticLogLossRate244 u) volume s t)
    (hDownIntegrable : IntervalIntegrable
      (h3PathPhysicalTopNegativeLogVariationRate244 hClass) volume s t)
    (hUpIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPositiveLogVariationRate244 hClass) volume s t)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) -
      (Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass t)) ≤
      ∫ r in s..t, h3PathPhysicalTopPositiveLogVariationRate244 hClass r := by
  have hNecessary := h3Path_nearYoung_forces_downwardTopLogVariation244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hMiddleIntegrable hTopIntegrable hLossIntegrable
    hDownIntegrable hK hNear
  have hIdentity := h3Path_topDownwardLog_integral_eq_endpoint_add_upward244
    hH3 hClass hs ht hst.le hD hDownIntegrable hUpIntegrable hLogIntegrable
  rw [hIdentity] at hNecessary
  linarith only [hNecessary]

end
end PrimeTensor.FirstMonomialTriad
