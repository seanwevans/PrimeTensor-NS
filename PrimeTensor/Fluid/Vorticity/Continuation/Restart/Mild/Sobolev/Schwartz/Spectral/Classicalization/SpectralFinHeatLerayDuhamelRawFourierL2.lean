import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayVariationOfConstants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.RawL2Shift
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Intertwining
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Path
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Classicalization: raw Fourier L² form of the heat-Leray Duhamel state

The all-frequency variation-of-constants theorem now writes the nonlinear term
as the explicit retarded scalar integral

    ∫₀ᵗ H_{t-s}(ξ) N(W(s),W(s))(ξ) ds.

The existing spectral mild solver stores the same nonlinear contribution as the
Banach-valued Duhamel state

    h3SpectralFinHeatLerayDuhamel ν t hν U V.

This file connects those two representations at the quotient-safe Fourier
`L²` level.  Coordinate projection and exact H³ deweighting are bounded linear
maps, so they commute with the genuinely integrable Duhamel Bochner integral.
The positive-lag intertwining theorem then identifies every source-time kernel
with the packaged raw heat-forcing Fourier `L²` state.

No fixed-frequency evaluation of an `L²` class is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Endpoint-safe raw Fourier `L²` kernel corresponding exactly to one
coordinate of the spectral heat-Leray Duhamel integrand. -/
noncomputable def h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  if hs : 0 < t - s then
    h3RawFinLerayOuterProductDivergenceHeatFourierL2
      ν (t - s) hν hs (U s) (V s) i
  else
    0

/-- Exact H³ deweighting of one coordinate of the actual spectral Duhamel state
is the Fourier `L²`-valued interval integral of the raw retarded heat-forcing
kernels. -/
theorem h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          ν t hν U V i)
      =
    ∫ s in (0 : ℝ)..t,
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s := by
  let P : H3SpectralFinVectorState →L[ℂ] H3SpectralScalarState :=
    ContinuousLinearMap.proj (R := ℂ) i

  let E : H3SpectralFinVectorState →L[ℂ] H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2CLM.comp P

  have hUint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU := by
    intro s hs
    exact hU s

  have hVint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV := by
    intro s hs
    exact hV s

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht hMU hMV U V
      hUcont hVcont hUint hVint

  have hComm :
      E
          (∫ s in (0 : ℝ)..t,
            h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s)
        =
      ∫ s in (0 : ℝ)..t,
        E
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s) := by
    symm
    exact E.intervalIntegral_comp_comm hInt

  change
    E
        (h3SpectralFinHeatLerayDuhamel
          ν t hν U V)
      =
    ∫ s in (0 : ℝ)..t,
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s

  unfold h3SpectralFinHeatLerayDuhamel

  rw [hComm]

  apply intervalIntegral.integral_congr

  intro s hs

  by_cases hlag : 0 < t - s

  · simp only [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_pos hlag,
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
      dif_pos hlag
    ]

    change
      h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayVelocityApply
            ν (t - s) hν hlag (U s) (V s) i)
        =
      h3RawFinLerayOuterProductDivergenceHeatFourierL2
        ν (t - s) hν hlag (U s) (V s) i

    exact
      h3SpectralFinHeatLerayVelocityApply_rawFourierL2_eq_rawHeatForcingL2
        hν hlag (U s) (V s) i

  · simp only [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_neg hlag,
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
      dif_neg hlag
    ]

    exact E.map_zero

end

end Euclidean
end Bridge
end PrimeTensor
