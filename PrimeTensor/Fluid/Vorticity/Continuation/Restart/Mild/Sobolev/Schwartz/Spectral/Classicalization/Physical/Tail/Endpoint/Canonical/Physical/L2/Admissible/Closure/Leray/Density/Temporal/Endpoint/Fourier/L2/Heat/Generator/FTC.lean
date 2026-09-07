import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Generator.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Generator.Integral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Physical L² temporal admissibility: integrated heat-generator identity

The scalar raw-Fourier heat orbit now has the quotient-safe right derivative at
every nonnegative elapsed time.  This file packages the three velocity
coordinates and applies the right-derivative form of FTC-2.

For a weighted H³ velocity state `U`, define the real-time raw Fourier heat
orbit

    D(s) = S(toNNReal s) raw(U).

On every positive interior point of `[0,t]`, the preceding scalar derivative
theorem gives coordinatewise

    D'(s) = ν S(s) Δ̂_L² U.

The right-hand side is exactly the already-packaged continuous Bochner
integrand `h3RawFourierL2HeatGeneratorRHSReal`.  Hence

    ∫₀ᵗ ν S(s) Δ̂_L² U ds = D(t) - D(0),

and therefore, for nonnegative time,

    S(t) raw(U) - raw(U)
      = h3RawFourierL2HeatGeneratorIntegral ν hν U t.

Everything remains in the quotient-safe raw Fourier `L²` space.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three-component real-time raw Fourier heat orbit. -/
noncomputable def h3RawFourierL2HeatRealVectorPath
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (s : ℝ) :
    H3RawFourierL2FinVectorState :=
  h3RawFourierL2HeatApplyNN
    ν hν (Real.toNNReal s)
    (h3SpectralFinVectorRawFourierL2 U)

@[simp]
theorem h3RawFourierL2HeatRealVectorPath_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (s : ℝ)
    (i : Fin 3) :
    h3RawFourierL2HeatRealVectorPath
        ν hν U s i
      =
    h3RawFourierL2HeatRealPath
      ν hν (U i) s :=
  rfl

/-- The vector raw Fourier heat orbit is strongly continuous on real time after
the canonical nonnegative-time clamp. -/
theorem continuous_h3RawFourierL2HeatRealVectorPath
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState) :
    Continuous
      (h3RawFourierL2HeatRealVectorPath
        ν hν U) := by
  unfold h3RawFourierL2HeatRealVectorPath
  exact
    (continuous_h3RawFourierL2HeatApplyNN
      ν hν
      (h3SpectralFinVectorRawFourierL2 U)).comp
      continuous_real_toNNReal

/-- At elapsed zero the vector heat orbit is exactly the deweighted initial
state. -/
@[simp]
theorem h3RawFourierL2HeatRealVectorPath_zero
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatRealVectorPath
        ν hν U 0
      =
    h3SpectralFinVectorRawFourierL2 U := by
  funext i
  rw [h3RawFourierL2HeatRealVectorPath_apply]
  exact
    h3RawFourierL2HeatRealPath_zero
      ν hν (U i)

/-- On nonnegative real time the clamped vector path is exactly the original
nonnegative-time raw Fourier heat semigroup. -/
theorem h3RawFourierL2HeatRealVectorPath_of_nonneg
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatRealVectorPath
        ν hν U s
      =
    h3RawFourierL2HeatApplyNN
      ν hν (NNReal.mk s hs)
      (h3SpectralFinVectorRawFourierL2 U) := by
  unfold h3RawFourierL2HeatRealVectorPath
  rw [Real.toNNReal_of_nonneg hs]

/-- Coordinate form of the quotient-safe generator integrand on a nonnegative
elapsed slice. -/
theorem h3RawFourierL2HeatGeneratorRHSReal_apply_of_nonneg
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFourierL2HeatGeneratorRHSReal
        ν hν U s i
      =
    h3RawFourierL2HeatGeneratorState
      ν
      (h3SpectralScalarHeatApplyNN
        ν hν (Real.toNNReal s) (U i)) := by
  rw [
    h3RawFourierL2HeatGeneratorRHSReal_of_nonneg
      hν hs U
  ]
  rw [
    h3RawFourierL2HeatGeneratorOrbitNN_eq_laplacian_heat
      ν hν U (NNReal.mk s hs)
  ]
  unfold h3RawFourierL2HeatGeneratorState
  simp only [
    Pi.smul_apply,
    h3SpectralFinVectorLaplacianRawFourierL2_apply,
    h3SpectralVelocityHeatApplyNN_apply
  ]
  rw [Real.toNNReal_of_nonneg hs]

/-- The three-component raw Fourier heat orbit has the packaged quotient-safe
generator as its right derivative at every nonnegative elapsed time. -/
theorem h3RawFourierL2HeatRealVectorPath_hasDerivWithinAt_right
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (U : H3SpectralFinVectorState) :
    HasDerivWithinAt
      (h3RawFourierL2HeatRealVectorPath
        ν hν U)
      (h3RawFourierL2HeatGeneratorRHSReal
        ν hν U s)
      (Set.Ioi s)
      s := by
  apply (hasDerivWithinAt_pi).2
  intro i

  rw [
    h3RawFourierL2HeatGeneratorRHSReal_apply_of_nonneg
      hν hs U i
  ]

  change
    HasDerivWithinAt
      (h3RawFourierL2HeatRealPath
        ν hν (U i))
      (h3RawFourierL2HeatGeneratorState
        ν
        (h3SpectralScalarHeatApplyNN
          ν hν (Real.toNNReal s) (U i)))
      (Set.Ioi s)
      s

  exact
    h3RawFourierL2HeatRealPath_hasDerivWithinAt_right
      hν hs (U i)

/-- FTC-2 for the quotient-safe vector heat orbit on every nonnegative real
elapsed interval. -/
theorem h3RawFourierL2HeatGeneratorIntegral_eq_sub_realVectorPath
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatGeneratorIntegral
        ν hν U t
      =
    h3RawFourierL2HeatRealVectorPath
        ν hν U t
      -
    h3RawFourierL2HeatRealVectorPath
        ν hν U 0 := by
  unfold h3RawFourierL2HeatGeneratorIntegral

  have hPathContinuous :
      ContinuousOn
        (h3RawFourierL2HeatRealVectorPath
          ν hν U)
        (Set.Icc (0 : ℝ) t) :=
    (continuous_h3RawFourierL2HeatRealVectorPath
      ν hν U).continuousOn

  have hRight :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        HasDerivWithinAt
          (h3RawFourierL2HeatRealVectorPath
            ν hν U)
          (h3RawFourierL2HeatGeneratorRHSReal
            ν hν U s)
          (Set.Ioi s)
          s := by
    intro s hs
    exact
      h3RawFourierL2HeatRealVectorPath_hasDerivWithinAt_right
        hν hs.1.le U

  have hIntegrable :
      IntervalIntegrable
        (h3RawFourierL2HeatGeneratorRHSReal
          ν hν U)
        volume
        (0 : ℝ)
        t :=
    h3RawFourierL2HeatGeneratorRHSReal_intervalIntegrable
      ν hν U 0 t

  exact
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      ht
      hPathContinuous
      hRight
      hIntegrable

/-- Integrated quotient-safe heat-generator identity. -/
theorem h3RawFourierL2HeatApplyNN_sub_raw_eq_generatorIntegral
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (t : ℝ≥0) :
    h3RawFourierL2HeatApplyNN
          ν hν t
          (h3SpectralFinVectorRawFourierL2 U)
        -
      h3SpectralFinVectorRawFourierL2 U
      =
    h3RawFourierL2HeatGeneratorIntegral
      ν hν U (t : ℝ) := by
  have hFTC :=
    h3RawFourierL2HeatGeneratorIntegral_eq_sub_realVectorPath
      hν t.property U

  rw [
    h3RawFourierL2HeatRealVectorPath_of_nonneg
      hν t.property U,
    h3RawFourierL2HeatRealVectorPath_zero
  ] at hFTC

  exact hFTC.symm

end

end Euclidean
end Bridge
end PrimeTensor
