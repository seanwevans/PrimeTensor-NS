import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Generator.Quotient

/-!
# Physical L² temporal admissibility: packaged heat-generator quotient state

The scalar raw Fourier quotient estimate is now available frequencywise.  This
file lifts that quotient into the actual raw Fourier `L²` quotient and records
the exact a.e. representatives needed for dominated convergence.

For real increment `h`, define

    Q_L²(h)
      = h⁻¹ • (S(toNNReal h) raw(G) - raw(G)).

On positive increments this has the raw representative from
`FourierL2HeatGeneratorQuotient`.  The target generator is packaged as

    ν • Δ̂_L² G,

and its a.e. representative is exactly the zero-time heat-generator amplitude.

No fixed frequency is selected.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorQuotientState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw Fourier `L²` heat difference quotient, using the canonical
nonnegative-time clamp. -/
noncomputable def h3RawFourierL2HeatQuotientState
    (ν h : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  h⁻¹ •
    (h3HeatFrequencyApplyNN
        ν hν (Real.toNNReal h)
        (h3SpectralScalarRawFourierL2 G)
      -
    h3SpectralScalarRawFourierL2 G)

/-- On a positive increment, the packaged `L²` quotient has exactly the raw
frequency quotient from the preceding file as an a.e. representative. -/
theorem h3RawFourierL2HeatQuotientState_ae_of_pos
    {ν h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 < h)
    (G : H3SpectralScalarState) :
    ((h3RawFourierL2HeatQuotientState
        ν h hν G :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawFourierL2HeatQuotientRawAmplitude
      ν h G := by
  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      h⁻¹
      (h3HeatFrequencyApplyNN
          ν hν (Real.toNNReal h)
          (h3SpectralScalarRawFourierL2 G)
        -
       h3SpectralScalarRawFourierL2 G)

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3HeatFrequencyApplyNN
        ν hν (Real.toNNReal h)
        (h3SpectralScalarRawFourierL2 G))
      (h3SpectralScalarRawFourierL2 G)

  have hHeat :=
    h3HeatFrequencyApplyNN_coeFn
      ν hν (Real.toNNReal h)
      (h3SpectralScalarRawFourierL2 G)

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae G

  unfold h3RawFourierL2HeatQuotientState

  filter_upwards [hSmul, hSub, hHeat, hRaw] with
      ξ hSmulξ hSubξ hHeatξ hRawξ

  simp only [Pi.smul_apply, Pi.sub_apply] at hSmulξ hSubξ

  rw [hSmulξ, hSubξ, hHeatξ, hRawξ]

  have hTime :
      ((Real.toNNReal h : ℝ≥0) : ℝ) = h := by
    simp [Real.toNNReal_of_nonneg hh.le]

  rw [hTime]

  unfold h3RawFourierL2HeatQuotientRawAmplitude
  rfl

/-- Quotient-safe raw Fourier `L²` heat generator state. -/
noncomputable def h3RawFourierL2HeatGeneratorState
    (ν : ℝ)
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  ν • h3SpectralScalarLaplacianRawFourierL2 G

/-- The packaged generator state has exactly the zero-time generator amplitude
as an a.e. representative. -/
theorem h3RawFourierL2HeatGeneratorState_ae
    (ν : ℝ)
    (G : H3SpectralScalarState) :
    ((h3RawFourierL2HeatGeneratorState
        ν G :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawFourierL2HeatGeneratorRawAmplitude
      ν G := by
  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      ν
      (h3SpectralScalarLaplacianRawFourierL2 G)

  have hLap :=
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
      G

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae G

  unfold h3RawFourierL2HeatGeneratorState

  filter_upwards [hSmul, hLap, hRaw] with
      ξ hSmulξ hLapξ hRawξ

  simp only [Pi.smul_apply] at hSmulξ

  rw [hSmulξ, hLapξ, hRawξ]
  unfold h3RawFourierL2HeatGeneratorRawAmplitude
  rw [Complex.real_smul]
  push_cast
  ring

end

end Euclidean
end Bridge
end PrimeTensor
