import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation

/-!
# Strong derivative after bounded `q²` truncation

The raw selected Fourier coordinate now has a genuine strong `L²` derivative,
and the preceding checkpoint packages the bounded operator

    T_R f = 1_{|D|<R} q² f.

For every fixed nonnegative cutoff `R`, ordinary continuous-linear calculus
therefore gives

    d/dt [T_R û_j(t)] = T_R [RHS_j(t)]

at every strict elapsed restart time.

No limit in `R` is taken here.  This checkpoint isolates the exact bounded
approximation to the desired global weighted derivative.  The remaining step
is cutoff removal using the already-constructed global `q² û_j` state and
continuous weighted PDE RHS.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedTruncatedDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/--
For every fixed nonnegative radial cutoff `R`, the bounded truncated intrinsic
`q²` multiplier transports the strong selected raw-Fourier derivative.

The derivative value is the same truncation applied to the exact selected
unit-viscosity projected Fourier RHS.
-/
theorem h3SelectedRestartVelocityRawFourierL2_truncatedQSq_hasDerivAt_unit
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ tau q R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (hR : 0 ≤ R)
    (i : Fin 3) :
    HasDerivAt
      (fun r : ℝ =>
        h3TopTailTruncatedQSqL2
          R hR
          (
            h3SpectralScalarRawFourierL2
              (
                (
                  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    r
                ) i
              )
          ))
      (
        h3TopTailTruncatedQSqL2
          R hR
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail
              (
                h3PreterminalElapsedToSelectedUnitRadius
                  htauR
                  ⟨q, hq.1.le, hq.2.le⟩
              )
              i
          )
      )
      q := by

  have hRaw :=
    h3SelectedRestartVelocityRawFourierL2_hasDerivAt_unit
      hNS ht₀ htau hE hTail htauR hq i

  have h :=
    (
      h3TopTailTruncatedQSqRealCLM
        R hR
    ).hasFDerivAt.comp_hasDerivAt
      q
      hRaw

  simpa only [
    Function.comp_def,
    h3TopTailTruncatedQSqRealCLM_apply
  ] using h

end

end Euclidean
end Bridge
end PrimeTensor
