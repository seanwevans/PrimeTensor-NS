import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedVarianceEvolution244
import Mathlib.Tactic

/-!
# Signed middle-moment excess controls monotonicity of physical H³ Fourier variance

The previous derivative closure provides the actual, class-local identity

  R'(t) = - X(t) / (E₀(t) D₃(t))²,

where R = 1 - E₂²/(E₀ D₃) and

  X = 2 E₂ E₂' (E₀ D₃) - E₂² (E₀' D₃ + E₀ D₃').

The top-dissipation rate D₃' here is the physical fourth-radial Hilbert
pairing, not an independently assumed scalar derivative. This file proves:

* X ≤ 0 throughout a strict energy-class interval forces R to be monotone
  nondecreasing and its middle-moment Cauchy ratio to be nonincreasing;
* near-sharp Young absorption on such an interval must pay a gap at least
  proportional to the earlier positive variance;
* if R actually falls from an earlier time to a later time, X > 0 at
  SOME time between them (a closed time interval), by contraposition of
  a calculus monotonicity theorem.

No sign of X is asserted for Navier–Stokes solutions. This isolates the
specific dynamical inequality an anti-concentration proof would require.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- Actual signed production of normalized middle-moment concentration.
A positive value makes physical normalized radial variance decrease. -/
noncomputable def h3PathTopFourierSignedMiddleMomentExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) : ℝ :=
  2 * velocityH3Energy2At u t * velocityH3FormalDerivative2At u t *
      (velocityH3Energy0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t) -
    velocityH3Energy2At u t ^ 2 *
      (velocityH3FormalDerivative0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t +
        velocityH3Energy0At u t *
          h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t)

/-- The exact physical derivative has the OPPOSITE sign of the named
signed middle-moment concentration excess. -/
theorem h3Path_normalizedVariance_deriv_eq_neg_signedExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass) t =
      -(h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 := by
  rw [h3Path_normalizedVarianceOnClass_deriv_eq244
    hH3 hClass ht hMass hD]
  unfold h3PathTopFourierSignedMiddleMomentExcess244
  ring

/-- Nonpositive signed excess prevents instantaneous spectral narrowing. -/
theorem h3Path_normalizedVariance_deriv_nonneg_of_excess_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hExcess : h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t ≤ 0) :
    0 ≤ deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass) t := by
  rw [h3Path_normalizedVariance_deriv_eq_neg_signedExcess244
    hH3 hClass ht hMass hD]
  exact div_nonneg (neg_nonneg.mpr hExcess) (sq_nonneg _)

/-- On a strict physical class interval, nonpositive actual signed moment
excess makes the normalized Fourier variance monotone nondecreasing.
This is a CONDITIONAL anti-concentration criterion, not a PDE sign theorem. -/
theorem h3Path_normalizedVariance_monotoneOn_of_excess_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : ∀ t, t ∈ Set.Ioo a T → 0 < velocityH3Energy0At u t)
    (hD : ∀ t, t ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u t)
    (hExcess : ∀ t, t ∈ Set.Ioo a T →
      h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t ≤ 0) :
    MonotoneOn (h3PathTopFourierNormalizedVarianceOnClass244 hClass)
      (Set.Ioo a T) := by
  have hDiff : DifferentiableOn ℝ
      (h3PathTopFourierNormalizedVarianceOnClass244 hClass)
      (Set.Ioo a T) := by
    intro t ht
    exact (h3Path_normalizedVarianceOnClass_hasDerivAt244
      hH3 hClass ht (hMass t ht) (hD t ht)).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Ioo a T)
    hDiff.continuousOn (hDiff.mono interior_subset) ?_
  intro t htInterior
  have ht : t ∈ Set.Ioo a T := interior_subset htInterior
  exact h3Path_normalizedVariance_deriv_nonneg_of_excess_nonpos244
    hH3 hClass ht (hMass t ht) (hD t ht) (hExcess t ht)

/-- On any nonconcentrating signed-excess interval, the actual normalized
Cauchy variance cannot fall below its value at an earlier anchor. -/
theorem h3Path_normalizedVariance_later_floor_of_excess_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hExcess : ∀ r, r ∈ Set.Ioo a T →
      h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r ≤ 0)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T) (hst : s ≤ t) :
    h3PathTopFourierNormalizedRadialVariance244 u s ≤
      h3PathTopFourierNormalizedRadialVariance244 u t := by
  have hMon := h3Path_normalizedVariance_monotoneOn_of_excess_nonpos244
    hH3 hClass hMass hD hExcess
  have hBound := hMon hs ht hst
  rw [h3Path_normalizedVarianceOnClass_eq_physical244
    hClass hs (hMass s hs) (hD s hs)] at hBound
  rw [h3Path_normalizedVarianceOnClass_eq_physical244
    hClass ht (hMass t ht) (hD t ht)] at hBound
  exact hBound

/-- The normalized physical middle-moment saturation ratio cannot increase
on an interval with nonpositive signed spectral concentration source. -/
theorem h3Path_normalizedMiddle_later_ceiling_of_excess_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hExcess : ∀ r, r ∈ Set.Ioo a T →
      h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r ≤ 0)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T) (hst : s ≤ t) :
    h3PathTopFourierNormalizedMiddleMoment244 u t ≤
      h3PathTopFourierNormalizedMiddleMoment244 u s := by
  have hBound := h3Path_normalizedVariance_later_floor_of_excess_nonpos244
    hH3 hClass hMass hD hExcess hs ht hst
  have hSumS := h3Path_topFourier_normalizedVariance_add_middle_eq_one244
    (hMass s hs) (hD s hs)
  have hSumT := h3Path_topFourier_normalizedVariance_add_middle_eq_one244
    (hMass t ht) (hD t ht)
  linarith only [hBound, hSumS, hSumT]

/-- A near-sharp Young gap at a later time must pay for the strictly positive
normalized variance retained at an earlier anchor whenever signed moment
excess has remained nonpositive on the entire interval. -/
theorem h3Path_nearYoung_gap_floor_of_excess_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hExcess : ∀ r, r ∈ Set.Ioo a T →
      h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r ≤ 0)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T) (hst : s ≤ t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    27 * K ^ 4 * velocityH3Energy0At u t *
      h3PathTopFourierNormalizedRadialVariance244 u s ≤ 256 * δ := by
  have hFloor := h3Path_normalizedVariance_later_floor_of_excess_nonpos244
    hH3 hClass hMass hD hExcess hs ht hst
  have hUpper := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ht) hK (hD t ht) hNear
  have hCompare : h3PathTopFourierNormalizedRadialVariance244 u s ≤
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) :=
    hFloor.trans hUpper
  have hWeight : 0 < 27 * K ^ 4 * velocityH3Energy0At u t := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 27) (pow_pos hK 4))
      (hMass t ht)
  have hScaled := (le_div_iff₀ hWeight).mp hCompare
  calc
    27 * K ^ 4 * velocityH3Energy0At u t *
        h3PathTopFourierNormalizedRadialVariance244 u s =
      h3PathTopFourierNormalizedRadialVariance244 u s *
        (27 * K ^ 4 * velocityH3Energy0At u t) := by ring
    _ ≤ 256 * δ := hScaled

/-- Strict decrease over a nontrivial closed physical time interval forces
positive actual signed middle-moment excess SOMEWHERE in that interval.
No prior global sign or continuity assumption on the excess is introduced:
the required differentiability follows from existing physical Hilbert paths. -/
theorem h3Path_normalizedVariance_drop_forces_positiveExcess_somewhere244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T) (hst : s < t)
    (hDrop : h3PathTopFourierNormalizedRadialVariance244 u t <
      h3PathTopFourierNormalizedRadialVariance244 u s) :
    ∃ r ∈ Set.Icc s t,
      0 < h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r := by
  classical
  by_contra hNo
  have hNonpos : ∀ r, r ∈ Set.Icc s t →
      h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r ≤ 0 := by
    intro r hr
    exact le_of_not_gt (fun hPos => hNo ⟨r, hr, hPos⟩)
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDiff : DifferentiableOn ℝ
      (h3PathTopFourierNormalizedVarianceOnClass244 hClass)
      (Set.Icc s t) := by
    intro r hr
    have hrClass := hInside r hr
    exact (h3Path_normalizedVarianceOnClass_hasDerivAt244
      hH3 hClass hrClass (hMass r hr) (hD r hr)).differentiableAt.differentiableWithinAt
  have hMon : MonotoneOn
      (h3PathTopFourierNormalizedVarianceOnClass244 hClass)
      (Set.Icc s t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc s t)
      hDiff.continuousOn (hDiff.mono interior_subset) ?_
    intro r hrInterior
    have hr : r ∈ Set.Icc s t := interior_subset hrInterior
    exact h3Path_normalizedVariance_deriv_nonneg_of_excess_nonpos244
      hH3 hClass (hInside r hr) (hMass r hr) (hD r hr) (hNonpos r hr)
  have hLower : h3PathTopFourierNormalizedVarianceOnClass244 hClass s ≤
      h3PathTopFourierNormalizedVarianceOnClass244 hClass t :=
    hMon ⟨le_refl s, hst.le⟩ ⟨hst.le, le_refl t⟩ hst.le
  rw [h3Path_normalizedVarianceOnClass_eq_physical244
    hClass hs (hMass s ⟨le_refl s, hst.le⟩)
    (hD s ⟨le_refl s, hst.le⟩)] at hLower
  rw [h3Path_normalizedVarianceOnClass_eq_physical244
    hClass ht (hMass t ⟨hst.le, le_refl t⟩)
    (hD t ⟨hst.le, le_refl t⟩)] at hLower
  exact (not_lt_of_ge hLower) hDrop

end
end PrimeTensor.FirstMonomialTriad
