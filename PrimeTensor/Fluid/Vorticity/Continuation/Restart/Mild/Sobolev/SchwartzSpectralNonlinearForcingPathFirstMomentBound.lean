import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingL1Bound

/-!
# Pathwise first-moment bound for the nonlinear Duhamel kernel

The endpoint heat estimate already gives, at every positive lag `τ`,

    ∫ ‖ξ‖ ‖H_τ F(ξ)‖ dξ
      ≤ k_ν(τ) ∫ ‖F(ξ)‖ dξ,

where `k_ν(τ) = (sqrt (ν (τ / 3)))⁻¹`.  The previous quantitative `L¹`
module bounds the unheated finite-index Leray--divergence forcing by

    ∫ ‖F(U,V)(ξ)‖ dξ
      ≤ C_force ‖U‖ ‖V‖.

This file combines those two estimates along a time-dependent spectral path.
For `s < t`, the first Fourier moment of the retarded nonlinear heat kernel is
bounded by the already-integrable scalar majorant

    k_ν(t-s) C_force MU MV

whenever `‖U(s)‖ ≤ MU` and `‖V(s)‖ ≤ MV`.

Thus the frequency-side and time-side endpoint estimates are now joined in one
reusable pathwise statement.  The next layer may use this majorant to justify
the first spatial derivative of the near-endpoint Duhamel tail without
reopening either the Fourier `L¹` estimate or the reciprocal-square-root time
integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathFirstMomentBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quantitative retarded first-moment estimate before imposing uniform path
bounds. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_retarded_firstMoment_integral_le
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (U s) (V s) i ξ‖)
      ≤
    h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
      h3NonlinearForcingL1Coefficient * ‖U s‖ * ‖V s‖ := by
  have hτ : 0 < t - s := sub_pos.mpr hs

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (U s) (V s) i ξ‖)
        ≤
      h3NonlinearForcingHeatFirstMomentCoefficient ν (t - s) *
        h3RawFinLerayOuterProductDivergenceL1Mass (U s) (V s) i :=
          h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_integral_le
            hν hτ (U s) (V s) i
    _ ≤
      h3NonlinearForcingHeatFirstMomentCoefficient ν (t - s) *
        (h3NonlinearForcingL1Coefficient * ‖U s‖ * ‖V s‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (h3RawFinLerayOuterProductDivergenceL1Mass_le
                (U s) (V s) i)
              (h3NonlinearForcingHeatFirstMomentCoefficient_nonneg
                ν (t - s))
    _ =
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
        h3NonlinearForcingL1Coefficient * ‖U s‖ * ‖V s‖ := by
          unfold h3NonlinearForcingHeatFirstMomentRetardedCoefficient
          ring

/-- Scalar majorant for the first Fourier moment of a retarded nonlinear heat
kernel under uniform spectral path bounds. -/
noncomputable def h3NonlinearForcingHeatFirstMomentPathMajorant
    (ν t MU MV s : ℝ) : ℝ :=
  h3NonlinearForcingHeatFirstMomentTimeMajorant
    ν t (h3NonlinearForcingL1Coefficient * MU * MV) s

/-- The pathwise first-moment majorant is interval integrable on `[0,t]`. -/
theorem h3NonlinearForcingHeatFirstMomentPathMajorant_intervalIntegrable
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    IntervalIntegrable
      (h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV)
      volume
      0
      t := by
  unfold h3NonlinearForcingHeatFirstMomentPathMajorant
  exact
    h3NonlinearForcingHeatFirstMomentTimeMajorant_intervalIntegrable
      (M := h3NonlinearForcingL1Coefficient * MU * MV)
      hν ht

/-- Exact integral of the pathwise first-moment majorant. -/
theorem h3NonlinearForcingHeatFirstMomentPathMajorant_integral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV s)
      =
    2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t *
      h3NonlinearForcingL1Coefficient * MU * MV := by
  unfold h3NonlinearForcingHeatFirstMomentPathMajorant
  rw [
    h3NonlinearForcingHeatFirstMomentTimeMajorant_integral
      (M := h3NonlinearForcingL1Coefficient * MU * MV)
      hν ht
  ]
  ring

/-- Pointwise pathwise first-moment estimate under uniform bounds on the two
input paths.  The endpoint `s = t` is intentionally excluded: the retarded
heat lag must be positive for the fixed-lag Fourier estimate, while the scalar
majorant is nevertheless integrable all the way to `t`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_firstMoment_le_pathMajorant
    {ν t MU MV s : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hU : ‖U s‖ ≤ MU)
    (hV : ‖V s‖ ≤ MV)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (U s) (V s) i ξ‖)
      ≤
    h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV s := by
  have hBase :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_retarded_firstMoment_integral_le
      hν hs.2 U V i

  have hRetNonneg :
      0 ≤ h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s :=
    h3NonlinearForcingHeatFirstMomentRetardedCoefficient_nonneg ν t s

  have hForceNonneg : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  have hPrefactorNonneg :
      0 ≤
        h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
          h3NonlinearForcingL1Coefficient :=
    mul_nonneg hRetNonneg hForceNonneg

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (U s) (V s) i ξ‖)
        ≤
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
        h3NonlinearForcingL1Coefficient * ‖U s‖ * ‖V s‖ := hBase
    _ ≤
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
        h3NonlinearForcingL1Coefficient * MU * ‖V s‖ := by
          exact
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hU hPrefactorNonneg)
              (norm_nonneg (V s))
    _ ≤
      h3NonlinearForcingHeatFirstMomentRetardedCoefficient ν t s *
        h3NonlinearForcingL1Coefficient * MU * MV := by
          exact
            mul_le_mul_of_nonneg_left
              hV
              (mul_nonneg hPrefactorNonneg hMU)
    _ = h3NonlinearForcingHeatFirstMomentPathMajorant ν t MU MV s := by
          unfold h3NonlinearForcingHeatFirstMomentPathMajorant
          unfold h3NonlinearForcingHeatFirstMomentTimeMajorant
          ring

end

end Euclidean
end Bridge
end PrimeTensor
