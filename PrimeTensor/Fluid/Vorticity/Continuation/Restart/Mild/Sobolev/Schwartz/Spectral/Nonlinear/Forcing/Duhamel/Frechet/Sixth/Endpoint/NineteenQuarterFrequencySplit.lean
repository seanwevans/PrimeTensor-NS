import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterMildMass

/-!
# Sixth Fréchet endpoint: nineteen-quarter convolution frequency split

The selected positive-time mild state now has a quantitative `19/4` raw
Fourier moment.

To feed that gain back through the quadratic convolution, isolate the
frequency split

    ξ = η + (ξ - η).

For the fractional exponent `19/4`, a case split on the larger convolution
frequency avoids any polynomial expansion or convexity theorem. If

    ‖η‖ ≤ ‖ξ - η‖,

then

    ‖ξ‖ ≤ 2 ‖ξ - η‖,

and symmetrically in the opposite case. Hence

    ‖ξ‖^(19/4)
      ≤
    2^(19/4)
      (‖η‖^(19/4) + ‖ξ - η‖^(19/4)).

The coefficient is deliberately left in exact real-power form.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNineteenQuarterFrequencySplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Harmless coefficient in the `19/4` convolution frequency split. -/
noncomputable def h3FourierNineteenQuarterSplitCoefficient : ℝ :=
  (2 : ℝ) ^ ((19 : ℝ) / 4)

/-- The `19/4` split coefficient is nonnegative. -/
theorem h3FourierNineteenQuarterSplitCoefficient_nonneg :
    0 ≤ h3FourierNineteenQuarterSplitCoefficient := by
  unfold h3FourierNineteenQuarterSplitCoefficient
  exact Real.rpow_nonneg (by norm_num) _

/-- The output `19/4` Fourier weight splits between the two convolution
frequencies. -/
theorem h3FourierNineteenQuarterWeight_le_split
    (ξ η : H3FourierPoint3) :
    h3FourierNineteenQuarterWeight ξ
      ≤
    h3FourierNineteenQuarterSplitCoefficient *
      (h3FourierNineteenQuarterWeight η +
        h3FourierNineteenQuarterWeight (ξ - η)) := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg _

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

  have hcoeff0 :
      0 ≤ (2 : ℝ) ^ ((19 : ℝ) / 4) :=
    Real.rpow_nonneg (by norm_num) _

  have hηw0 :
      0 ≤ ‖η‖ ^ ((19 : ℝ) / 4) :=
    Real.rpow_nonneg hη0 _

  have hshiftw0 :
      0 ≤ ‖ξ - η‖ ^ ((19 : ℝ) / 4) :=
    Real.rpow_nonneg hshift0 _

  unfold
    h3FourierNineteenQuarterWeight
    h3FourierNineteenQuarterSplitCoefficient

  by_cases hηshift : ‖η‖ ≤ ‖ξ - η‖
  · have htwo :
        ‖ξ‖ ≤ 2 * ‖ξ - η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ ((19 : ℝ) / 4)
          ≤
        (2 * ‖ξ - η‖) ^ ((19 : ℝ) / 4) :=
      Real.rpow_le_rpow
        hξ0 htwo (by norm_num)

    have hmul :
        (2 * ‖ξ - η‖) ^ ((19 : ℝ) / 4)
          =
        (2 : ℝ) ^ ((19 : ℝ) / 4) *
          ‖ξ - η‖ ^ ((19 : ℝ) / 4) := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hshift0
      ]

    calc
      ‖ξ‖ ^ ((19 : ℝ) / 4)
          ≤
        (2 * ‖ξ - η‖) ^ ((19 : ℝ) / 4) :=
        hrpow
      _ =
        (2 : ℝ) ^ ((19 : ℝ) / 4) *
          ‖ξ - η‖ ^ ((19 : ℝ) / 4) :=
        hmul
      _ ≤
        (2 : ℝ) ^ ((19 : ℝ) / 4) *
          (‖η‖ ^ ((19 : ℝ) / 4) +
            ‖ξ - η‖ ^ ((19 : ℝ) / 4)) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

  · have hshiftη :
        ‖ξ - η‖ ≤ ‖η‖ := by
      exact le_of_lt (lt_of_not_ge hηshift)

    have htwo :
        ‖ξ‖ ≤ 2 * ‖η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ ((19 : ℝ) / 4)
          ≤
        (2 * ‖η‖) ^ ((19 : ℝ) / 4) :=
      Real.rpow_le_rpow
        hξ0 htwo (by norm_num)

    have hmul :
        (2 * ‖η‖) ^ ((19 : ℝ) / 4)
          =
        (2 : ℝ) ^ ((19 : ℝ) / 4) *
          ‖η‖ ^ ((19 : ℝ) / 4) := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hη0
      ]

    calc
      ‖ξ‖ ^ ((19 : ℝ) / 4)
          ≤
        (2 * ‖η‖) ^ ((19 : ℝ) / 4) :=
        hrpow
      _ =
        (2 : ℝ) ^ ((19 : ℝ) / 4) *
          ‖η‖ ^ ((19 : ℝ) / 4) :=
        hmul
      _ ≤
        (2 : ℝ) ^ ((19 : ℝ) / 4) *
          (‖η‖ ^ ((19 : ℝ) / 4) +
            ‖ξ - η‖ ^ ((19 : ℝ) / 4)) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

end
end Euclidean
end Bridge
end PrimeTensor
