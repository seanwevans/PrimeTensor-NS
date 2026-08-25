import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingHeatIntertwining

/-!
# Endpoint first-moment bound for the nonlinear heat kernel

The fixed positive-lag nonlinear heat--Leray kernel is already known to have a
classical spatial `C³` representative, and `SchwartzSpectralNonlinearForcingHeatIntertwining`
identifies that representative with the actual spectral kernel used by the
Duhamel term.

For the short-time tail, however, the relevant estimate is not a uniform
three-derivative bound: higher heat moments blow up too strongly as the lag
`τ → 0`.  The first Fourier moment has the sharp integrable singularity

    (sqrt (ν (τ / 3)))⁻¹.

This file extracts that estimate explicitly, both pointwise in frequency and
after integration.  The right-hand side is the Fourier `L¹` mass of the
*unheated* nonlinear forcing, already available at the endpoint.

This is the quantitative input for the first genuine near-endpoint Duhamel
bootstrap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingHeatEndpointBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The scalar coefficient in the first-moment heat estimate.  For fixed
positive viscosity this has the expected `τ⁻¹/²` endpoint singularity. -/
noncomputable def h3NonlinearForcingHeatFirstMomentCoefficient
    (ν τ : ℝ) : ℝ :=
  (Real.sqrt (ν * (τ / 3)))⁻¹

/-- The first-moment coefficient is nonnegative. -/
theorem h3NonlinearForcingHeatFirstMomentCoefficient_nonneg
    (ν τ : ℝ) :
    0 ≤ h3NonlinearForcingHeatFirstMomentCoefficient ν τ := by
  unfold h3NonlinearForcingHeatFirstMomentCoefficient
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- Pointwise first-Fourier-moment bound for the positive-lag nonlinear
heat--Leray forcing. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ *
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖
      ≤
    h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
  have hMoment :=
    h3HeatFourierMomentMultiplier_le_three
      hν hτ 1 (by norm_num) ξ
  simp only [pow_one] at hMoment

  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [norm_mul]
  unfold h3NonlinearForcingHeatFirstMomentCoefficient
  calc
    ‖ξ‖ *
        (‖h3HeatFourierSymbol ν τ ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        =
      (‖ξ‖ * ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
          ring
    _ ≤
      (Real.sqrt (ν * (τ / 3)))⁻¹ *
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
      mul_le_mul_of_nonneg_right hMoment (norm_nonneg _)

/-- Fourier `L¹` mass of one unheated nonlinear forcing coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceL1Mass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- The unheated forcing mass is nonnegative. -/
theorem h3RawFinLerayOuterProductDivergenceL1Mass_nonneg
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    0 ≤ h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
  unfold h3RawFinLerayOuterProductDivergenceL1Mass
  exact integral_nonneg (fun ξ => norm_nonneg _)

/-- Integrated first-moment bound.  This exposes exactly the time-singular
coefficient that must be integrated in the near-endpoint Duhamel tail. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_integral_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖)
      ≤
    h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
      h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i 1 (by norm_num))

  have hRawInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawInt.const_mul
      (h3NonlinearForcingHeatFirstMomentCoefficient ν τ)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
      refine integral_mono_ae hTargetInt hMajorantInt ?_
      filter_upwards with ξ
      exact
        h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_le
          hν hτ U V i ξ
    _ =
      h3NonlinearForcingHeatFirstMomentCoefficient ν τ *
        h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
      unfold h3RawFinLerayOuterProductDivergenceL1Mass
      rw [integral_const_mul]

end

end Euclidean
end Bridge
end PrimeTensor
