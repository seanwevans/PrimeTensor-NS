import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdMildMass

/-!
# Fifth Fréchet endpoint: cubic convolution frequency split

The fourth endpoint now closes a quantitative full third raw Fourier moment for
the selected positive-time mild state.

The next derivative layer feeds that cubic state regularity back through the
quadratic forcing.  Since the Leray-divergence symbol contributes one frequency
power, a forcing second-moment estimate begins with a cubic weighted convolution
bound.

This file isolates the only new frequency algebra:

    ξ = η + (ξ - η),

hence

    ‖ξ‖³ ≤ 4 (‖η‖³ + ‖ξ - η‖³).

The coefficient `4` is the standard convexity constant for the cubic power and
is not optimized further.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointThirdFrequencySplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Harmless coefficient in the cubic convolution frequency split. -/
noncomputable def h3FourierThirdSplitCoefficient : ℝ := 4

/-- The output cubic Fourier weight splits between the two convolution
frequencies. -/
theorem h3FourierThirdWeight_le_split
    (ξ η : H3FourierPoint3) :
    ‖ξ‖ ^ 3
      ≤
    h3FourierThirdSplitCoefficient *
      (‖η‖ ^ 3 + ‖ξ - η‖ ^ 3) := by
  have hη0 : 0 ≤ ‖η‖ :=
    norm_nonneg _

  have hshift0 : 0 ≤ ‖ξ - η‖ :=
    norm_nonneg _

  have htri :
      ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    calc
      ‖ξ‖ = ‖η + (ξ - η)‖ := by
        congr 1
        abel
      _ ≤ ‖η‖ + ‖ξ - η‖ :=
        norm_add_le _ _

  have hFirst :
      ‖ξ‖ ^ 3 ≤ (‖η‖ + ‖ξ - η‖) ^ 3 := by
    gcongr

  have hSquare :
      0 ≤ (‖η‖ - ‖ξ - η‖) ^ 2 :=
    sq_nonneg _

  have hFactor :
      0 ≤
        (‖η‖ + ‖ξ - η‖) *
          (‖η‖ - ‖ξ - η‖) ^ 2 :=
    mul_nonneg
      (add_nonneg hη0 hshift0)
      hSquare

  unfold h3FourierThirdSplitCoefficient

  calc
    ‖ξ‖ ^ 3
        ≤
      (‖η‖ + ‖ξ - η‖) ^ 3 :=
      hFirst
    _ ≤
      4 * (‖η‖ ^ 3 + ‖ξ - η‖ ^ 3) := by
      nlinarith

end
end Euclidean
end Bridge
end PrimeTensor
