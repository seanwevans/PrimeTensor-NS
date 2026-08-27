import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Pairing

/-!
# Selected terminal-tail raw Fourier `L²` representative

`StateL2` and `Pairing` now identify the selected terminal tail at the
quotient-safe Fourier `L²` level and show that every Hilbert pairing commutes
through the terminal-half source-time integral.

This file records the fixed-source-time representative theorem that is latent
in the existing `MemLp.toLp` package:

for every `s < t`, the `L²` source-time kernel used in the selected tail has
the explicit raw heat--Leray forcing

    ξ ↦ H_{t-s}(ξ) N(W(s),W(s))(ξ)

as an almost-everywhere representative.

This is the precise pointwise bridge needed by the subsequent scalar Fubini
argument.  No fixed-frequency evaluation of an `L²` equivalence class is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailRawFourierL2Representative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strictly preterminal source time, the quotient-safe selected
tail `L²` kernel has the explicit raw retarded heat--Leray forcing as its
almost-everywhere Fourier representative. -/
theorem h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_lt
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s < t) :
    ((h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)) := by
  have hτ : 0 < t - s := sub_pos.mpr hs

  unfold h3SelectedDuhamelTailRawFourierL2Integrand
  rw [dif_pos hs]

  have hRaw :=
    MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
        hν hτ
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i)

  change
    _ =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν (t - s)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i

  exact hRaw

/-- Terminal-half specialization of the fixed-source-time representative
theorem. -/
theorem h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_mem_Ioo
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (t / 2) t) :
    ((h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)) :=
  h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_lt
    hν U₀ hA hU₀ i hs.2

/-- On the terminal half, the explicit raw kernel is Fourier `L²`
coordinatewise in source time. -/
theorem h3SelectedDuhamelTailComplexKernel_memLp2_of_mem_Ioo
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (t / 2) t) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      2
      (volume : Measure H3FourierPoint3) := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2

  change
    MemLp
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν (t - s)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i)
      2
      (volume : Measure H3FourierPoint3)

  exact
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
      hν hτ
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      i

end
end Euclidean
end Bridge
end PrimeTensor
