import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalIntrinsicClockBridge

/-!
# Exact canonical Riccati defect and high-energy coefficient refinement

The intrinsic Riccati lower bound already follows from the autonomous
H3 inequality `E' ≤ K sqrt(E) E`, with `K = 4422 (C1 + 1)`. Its growth
*defect* has an exact, nonnegative, three-channel decomposition:

  K sqrt(E) - E'/E
    = 4422 (sqrt(E)-1) + Delta + 2 D/E.

Here Delta is the signed-transport cancellation gap, D is H3 dissipation,
and the first channel is the overhead from bounding the baseline `4422`
by `4422 sqrt(E)`. This proves the original constant K is not an
asymptotically sharp *pointwise upper growth coefficient* when E is large:
for any eta>0, E' ≤ (4422 C1+eta) sqrt(E) E wherever
`4422 ≤ eta sqrt(E)`.

The *already proved intrinsic Riccati floor*, conditional on hypothetical
nonextension, enforces that high-energy premise uniformly on some terminal
tail. Thus the improved coefficient is eventually available on the entire
tail, without any sample-index restriction. None of these estimates
establishes the strengthened inverse-root terminal comparison, a new
coercive estimate, unconditional continuation, or blowup existence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Difference between the original autonomous Riccati growth envelope
and the exact normalized derivative of the canonical H3 energy. -/
noncomputable def h3PathCanonicalRiccatiGrowthDefect
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => h3PathSqrtEnergyRiccatiCoefficient *
      Real.sqrt (velocityH3EnergyAt u t) -
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t

/-- Exact three-channel decomposition of the autonomous Riccati deficit:
the square-root normalization baseline, commutator cancellation, and
full viscous dissipation. This uses the *signed* exact H3 PDE balance. -/
theorem h3PathCanonical_riccatiDefect_eq_baseline_add_cancellation_add_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalRiccatiGrowthDefect u t =
      4422 * (Real.sqrt (velocityH3EnergyAt u t) - 1) +
      h3PathCanonicalTransportCancellationGap u t +
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hProd : 0 ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hDerivative : deriv (velocityH3EnergyAt u) t =
      - velocityH3TransportDerivativeAt u t -
        2 * velocityH3DissipationAt u t := by
    linarith only [hBalance]
  unfold h3PathCanonicalRiccatiGrowthDefect
    h3PathCanonicalTransportCancellationGap
    h3PathSqrtEnergyRiccatiCoefficient
  rw [hDerivative]
  simp only [h3PathCanonicalKineticTransportCoefficient,
    h3PathCanonicalSqrtEnergyGradientEnvelope, abs_of_nonneg hProd]
  field_simp [ne_of_gt hEPos]
  <;> ring

/-- Every channel in the exact Riccati deficit is nonnegative on an H3
energy-class tail. In particular no positivity of the signed transport
itself is assumed. -/
theorem h3PathCanonical_riccatiDefect_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3PathCanonicalRiccatiGrowthDefect u t := by
  have hOne : 1 ≤ Real.sqrt (velocityH3EnergyAt u t) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (one_le_velocityH3EnergyAt u t)
  have hCancel := h3PathCanonicalTransportCancellationGap_nonneg
    hH3 hClass ht
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hDNorm : 0 ≤
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t :=
    div_nonneg (mul_nonneg (by norm_num) hD) hE
  rw [h3PathCanonical_riccatiDefect_eq_baseline_add_cancellation_add_dissipation
    hH3 hClass ht]
  have hBase : 0 ≤ (4422 : ℝ) *
      (Real.sqrt (velocityH3EnergyAt u t) - 1) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hOne)
  exact add_nonneg (add_nonneg hBase hCancel) hDNorm

/-- Even if transport cancellation and viscous dissipation both vanish,
the constant baseline sacrificed in `1 ≤ sqrt(E)` remains in the defect. -/
theorem h3PathCanonical_riccatiDefect_ge_sqrtEnergy_baseline
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    4422 * (Real.sqrt (velocityH3EnergyAt u t) - 1) ≤
      h3PathCanonicalRiccatiGrowthDefect u t := by
  have hCancel := h3PathCanonicalTransportCancellationGap_nonneg
    hH3 hClass ht
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hDNorm : 0 ≤
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t :=
    div_nonneg (mul_nonneg (by norm_num) hD) hE
  rw [h3PathCanonical_riccatiDefect_eq_baseline_add_cancellation_add_dissipation
    hH3 hClass ht]
  linarith only [hCancel, hDNorm]

/-- A high-energy pointwise bound improves the growth coefficient from
`4422(C1+1)` to `4422*C1+eta`, without dropping or replacing any
assumption of the underlying exact H3 energy-class inequality. -/
theorem h3PathCanonical_highEnergy_refinedRiccatiGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t η : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hOver : 4422 ≤ η * Real.sqrt (velocityH3EnergyAt u t)) :
    deriv (velocityH3EnergyAt u) t ≤
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
        Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hProd : 0 ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hGrowth := deriv_velocityH3EnergyAt_le_sqrtEnergyGrowth
    hH3 hClass ht
  rw [abs_of_nonneg hProd] at hGrowth
  have hCoeff :
      4422 * (1 +
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) ≤
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
        Real.sqrt (velocityH3EnergyAt u t) := by
    nlinarith only [hOver]
  exact le_trans hGrowth (mul_le_mul_of_nonneg_right hCoeff hE)

/-- The intrinsic pointwise Riccati floor forces the high-energy premise
uniformly whenever the actual terminal width is below its explicit cutoff.
This is not a witness-index statement. -/
theorem h3PathCanonical_intrinsic_highEnergy_on_short_width
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t η : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hη : 0 < η)
    (hWidth : T - t <
      (2 * η) / (h3PathSqrtEnergyRiccatiCoefficient * 4422)) :
    4422 ≤ η * Real.sqrt (velocityH3EnergyAt u t) := by
  have hK : 0 < h3PathSqrtEnergyRiccatiCoefficient :=
    h3PathSqrtEnergyRiccatiCoefficient_pos
  have hDist : 0 < T - t := sub_pos.mpr ht.2
  have hDen : 0 < h3PathSqrtEnergyRiccatiCoefficient * (4422 : ℝ) :=
    mul_pos hK (by norm_num)
  have hScaledWidth :
      h3PathSqrtEnergyRiccatiCoefficient * (T - t) * 4422 <
        2 * η := by
    have hRaw := (lt_div_iff₀ hDen).1 hWidth
    nlinarith only [hRaw]
  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass ht
  by_contra hNot
  have hSmall : η * Real.sqrt (velocityH3EnergyAt u t) < 4422 :=
    lt_of_not_ge hNot
  have hRateScaled : 2 * η ≤
      h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
        (η * Real.sqrt (velocityH3EnergyAt u t)) := by
    have hScaled := mul_le_mul_of_nonneg_right hRate hη.le
    nlinarith only [hScaled]
  have hContradiction :
      h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
        (η * Real.sqrt (velocityH3EnergyAt u t)) < 2 * η :=
    lt_trans
      (mul_lt_mul_of_pos_left hSmall (mul_pos hK hDist))
      hScaledWidth
  exact (not_lt_of_ge hRateScaled) hContradiction

/-- On a hypothetical nonextension path the coefficient can be refined to
`4422*C1+eta` on an *entire strict terminal tail*, for every eta>0.
The premise of hypothetical nonextension remains explicit. -/
theorem h3PathCanonical_eventual_refinedRiccatiGrowth_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a η : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hη : 0 < η) :
    ∃ d : ℝ, d ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo d T →
        deriv (velocityH3EnergyAt u) t ≤
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
            Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
  let δ : ℝ :=
    (2 * η) / (h3PathSqrtEnergyRiccatiCoefficient * 4422)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (mul_pos (by norm_num) hη)
      (mul_pos h3PathSqrtEnergyRiccatiCoefficient_pos (by norm_num))
  let m : ℝ := h3BKMKineticTailMidpoint a T
  have hm : m ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  let d : ℝ := max m (T - δ)
  have hd : d ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hm.1 (le_max_left _ _),
      max_lt hm.2 (sub_lt_self T hδ)⟩
  refine ⟨d, hd, ?_⟩
  intro t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hWidth : T - t < δ := by
    have hLower : T - δ ≤ d := le_max_right m (T - δ)
    linarith only [hLower, ht.1]
  have hOver : 4422 ≤ η * Real.sqrt (velocityH3EnergyAt u t) :=
    h3PathCanonical_intrinsic_highEnergy_on_short_width
      hH3 hNoExtension hClass htClass hη (by simpa only [δ] using hWidth)
  exact h3PathCanonical_highEnergy_refinedRiccatiGrowth
    hH3 hClass htClass hOver

/-- Neutral alternative: either the path extends, or for every positive
coefficient tolerance its growth on a complete final tail obeys the improved
high-energy Riccati upper estimate. This is not by itself a contradiction. -/
theorem h3PathCanonical_extension_or_eventual_refinedRiccatiGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ η : ℝ, 0 < η →
      ∃ d : ℝ, d ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo d T →
          deriv (velocityH3EnergyAt u) t ≤
            (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
              Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro η hη
    exact h3PathCanonical_eventual_refinedRiccatiGrowth_of_noExtension
      hH3 hExt hClass hη

end Euclidean
end Bridge
end PrimeTensor
