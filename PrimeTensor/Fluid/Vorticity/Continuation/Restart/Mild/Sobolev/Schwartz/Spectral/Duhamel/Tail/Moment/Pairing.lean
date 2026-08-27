import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.StateL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Selected terminal-tail raw Fourier `L²` pairing

`StateL2` identifies the deweighted actual selected spectral tail with the
Bochner interval integral of the packaged raw heat-forcing `L²` states.

This file records the Hilbert-space dual form of that identity.

The key points are:

* the quotient-safe raw Fourier `L²` source-time kernel is itself genuinely
  interval-integrable on the terminal half;
* for every Fourier `L²` test state `φ`, the complex inner product with the
  actual selected tail commutes through the source-time interval integral.

This is the correct bridge toward the pointwise raw Fourier amplitude.  The
next checkpoint can prove a scalar Fubini theorem for the pairing kernel

    (s, ξ) ↦ ⟪φ(ξ), K(s,ξ)⟫,

compare it with the explicit amplitude, and then use Hilbert-space
nondegeneracy.  No point evaluation on an `L²` equivalence class is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailRawFourierL2Pairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The quotient-safe raw Fourier `L²` selected-tail source kernel is genuinely
interval-integrable on the terminal half. -/
theorem h3SelectedDuhamelTailRawFourierL2Integrand_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    IntervalIntegrable
      (h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i)
      volume
      (t / 2)
      t := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν W W

  have hD :
      IntervalIntegrable
        D
        volume
        (t / 2)
        t := by
    dsimp only [D, W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_halfTail_intervalIntegrable
        hν U₀ hA hU₀ ht

  have hMapped :
      IntervalIntegrable
        (fun s : ℝ =>
          h3SpectralFinCoordinateRawFourierL2CLM i (D s))
        volume
        (t / 2)
        t := by
    constructor
    · exact
        (h3SpectralFinCoordinateRawFourierL2CLM i).integrable_comp
          hD.1
    · exact
        (h3SpectralFinCoordinateRawFourierL2CLM i).integrable_comp
          hD.2

  refine hMapped.congr ?_
  intro s hs

  dsimp only [
    D,
    W,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ]

  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_rawFourierL2_eq
      hν U₀ hA hU₀ i

/-- Every fixed Fourier `L²` test state gives a genuinely interval-integrable
scalar pairing with the selected raw tail kernel. -/
theorem h3SelectedDuhamelTailRawFourierL2Integrand_inner_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (φ : H3FourierComplexL2) :
    IntervalIntegrable
      (fun s : ℝ =>
        inner ℂ φ
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s))
      volume
      (t / 2)
      t := by
  have hG :=
    h3SelectedDuhamelTailRawFourierL2Integrand_intervalIntegrable
      hν U₀ hA hU₀ ht i

  let L :
      H3FourierComplexL2 →L[ℂ] ℂ :=
    innerSL ℂ φ

  have hMapped :
      IntervalIntegrable
        (fun s : ℝ =>
          L
            (h3SelectedDuhamelTailRawFourierL2Integrand
              ν A t hν U₀ hA hU₀ i s))
        volume
        (t / 2)
        t := by
    constructor
    · exact L.integrable_comp hG.1
    · exact L.integrable_comp hG.2

  simpa only [L, innerSL_apply_apply] using hMapped

/-- Hilbert-space dual form of the selected terminal-tail raw Fourier `L²`
state identity.  Pairing with any Fourier `L²` test state commutes through the
terminal-half source-time integral. -/
theorem inner_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_intervalIntegral
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (φ : H3FourierComplexL2) :
    inner ℂ φ
        (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i)
      =
    ∫ s in (t / 2)..t,
      inner ℂ φ
        (h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s) := by
  rw [
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_intervalIntegral
      hν U₀ hA hU₀ ht i
  ]

  have hG :=
    h3SelectedDuhamelTailRawFourierL2Integrand_intervalIntegrable
      hν U₀ hA hU₀ ht i

  let L :
      H3FourierComplexL2 →L[ℂ] ℂ :=
    innerSL ℂ φ

  have hComm :
      (∫ s in (t / 2)..t,
        L
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s))
        =
      L
        (∫ s in (t / 2)..t,
          h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s) :=
    L.intervalIntegral_comp_comm hG

  simpa only [L, innerSL_apply_apply] using hComm.symm

end
end Euclidean
end Bridge
end PrimeTensor
