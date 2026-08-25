import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingHeatEndpointBound

/-!
# Time integration of the nonlinear endpoint first-moment coefficient

`SchwartzSpectralNonlinearForcingHeatEndpointBound` isolates the fixed-lag
first-moment estimate

    ∫ ‖ξ‖ ‖H_τ F(ξ)‖ dξ
      ≤ (sqrt (ν (τ / 3)))⁻¹ ∫ ‖F(ξ)‖ dξ.

For the Duhamel tail, the remaining scalar issue is the retarded time
coefficient with `τ = t - s`.  This file identifies that coefficient exactly
with the square-root kernel already developed for the H³ Duhamel theory, but
with effective viscosity `ν / 3`.

Consequently we inherit genuine interval integrability and the exact formula

    ∫₀ᵗ (sqrt (ν ((t-s)/3)))⁻¹ ds
      = 2 (sqrt (ν/3))⁻¹ sqrt t.

This closes the scalar improper-integral part of the first-moment tail
bootstrap.  The following layer can combine this time majorant with the
frequency estimate without reopening any square-root integration argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped Interval

noncomputable section

/-- Retarded form of the first-moment heat coefficient. -/
noncomputable def h3NonlinearForcingHeatFirstMomentRetardedCoefficient
    (ν t s : ℝ) : ℝ :=
  h3NonlinearForcingHeatFirstMomentCoefficient ν (t - s)

/-- The endpoint first-moment coefficient is exactly the previously developed
viscous reciprocal-square-root kernel with viscosity `ν / 3`. -/
theorem h3NonlinearForcingHeatFirstMomentRetardedCoefficient_eq_viscousKernel
    (ν t s : ℝ) :
    h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s
      = h3ViscousTimeSingularKernel (ν / 3) t s := by
  unfold h3NonlinearForcingHeatFirstMomentRetardedCoefficient
  unfold h3NonlinearForcingHeatFirstMomentCoefficient
  unfold h3ViscousTimeSingularKernel
  rw [show ν * ((t - s) / 3) = (ν / 3) * (t - s) by ring]

/-- The retarded first-moment coefficient is nonnegative. -/
theorem h3NonlinearForcingHeatFirstMomentRetardedCoefficient_nonneg
    (ν t s : ℝ) :
    0 ≤ h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s := by
  unfold h3NonlinearForcingHeatFirstMomentRetardedCoefficient
  exact h3NonlinearForcingHeatFirstMomentCoefficient_nonneg ν (t - s)

/-- The retarded first-moment coefficient is genuinely interval integrable on
`[0,t]` for positive viscosity and nonnegative terminal time. -/
theorem h3NonlinearForcingHeatFirstMomentRetardedCoefficient_intervalIntegrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t)
      volume
      0
      t := by
  have hk :=
    h3ViscousTimeSingularKernel_intervalIntegrable
      (ν := ν / 3)
      (t := t)
      (by positivity)
      ht
  refine hk.congr ?_
  intro s _hs
  exact
    (h3NonlinearForcingHeatFirstMomentRetardedCoefficient_eq_viscousKernel
      ν t s).symm

/-- Exact integral of the retarded first-moment coefficient. -/
theorem h3NonlinearForcingHeatFirstMomentRetardedCoefficient_integral
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s)
      =
    2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t := by
  calc
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s)
        =
      ∫ s in (0 : ℝ)..t,
        h3ViscousTimeSingularKernel (ν / 3) t s := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact
            h3NonlinearForcingHeatFirstMomentRetardedCoefficient_eq_viscousKernel
              ν t s
    _ =
      2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t := by
        unfold h3ViscousTimeSingularKernel
        exact
          h3_viscousTimeSingularKernel_integral
            (ν := ν / 3)
            (t := t)
            (by positivity)
            ht

/-- Scalar time majorant obtained after imposing a uniform bound `M` on the
unheated forcing's Fourier `L¹` mass. -/
noncomputable def h3NonlinearForcingHeatFirstMomentTimeMajorant
    (ν t M s : ℝ) : ℝ :=
  h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s * M

/-- The bounded-mass first-moment time majorant is interval integrable. -/
theorem h3NonlinearForcingHeatFirstMomentTimeMajorant_intervalIntegrable
    {ν t M : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3NonlinearForcingHeatFirstMomentTimeMajorant ν t M)
      volume
      0
      t := by
  have hk :=
    h3NonlinearForcingHeatFirstMomentRetardedCoefficient_intervalIntegrable
      hν ht
  change IntervalIntegrable
    (fun s : ℝ =>
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s * M)
    volume
    0
    t
  exact hk.mul_const M

/-- Exact integral of the bounded-mass first-moment time majorant. -/
theorem h3NonlinearForcingHeatFirstMomentTimeMajorant_integral
    {ν t M : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstMomentTimeMajorant ν t M s)
      =
    2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t * M := by
  unfold h3NonlinearForcingHeatFirstMomentTimeMajorant
  calc
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s * M)
        =
      (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s) * M := by
          rw [intervalIntegral.integral_mul_const]
    _ =
      (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t) * M := by
        rw [h3NonlinearForcingHeatFirstMomentRetardedCoefficient_integral hν ht]
    _ =
      2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t * M := by
        rfl

end

end Euclidean
end Bridge
end PrimeTensor
