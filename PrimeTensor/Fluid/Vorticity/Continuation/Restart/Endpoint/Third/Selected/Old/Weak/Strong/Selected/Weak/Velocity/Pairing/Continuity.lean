import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Elapsed.Local.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Raw.L2.Shift

/-!
# Closed-interval continuity of the selected weak velocity pairing

The selected weak local evolution is now available at every strict positive
elapsed time.  To pass the lower FTC endpoint to restart time zero, the weak
velocity pairing itself must be continuous on the complete closed elapsed
interval.

There is no need to prove continuity of the physical decoder directly.

For each scalar coordinate, Plancherel identifies

    <phi, V_sel(q)>_R

with the real part of the complex Fourier pairing

    <Fourier(phi), raw(W(q))>_C.

The selected weighted H³ path `W` is globally continuous, and deweighting to
raw Fourier `L²` is already bundled as the contractive continuous linear map
`h3SpectralScalarRawFourierL2CLM`.  Hence the Fourier pairing is continuous,
including at `q = 0`.

Summing the three coordinates gives the vector weak pairing continuity.  The
same result for the selected velocity increment follows by subtracting the
constant initial pairing.

No endpoint regularity of the old branch, time derivative, or new analytic
estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakVelocityPairingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One scalar compact-test pairing with the selected physical velocity is
continuous on the complete closed elapsed interval. -/
theorem continuous_inner_h3WeakTestFunctionPhysicalL2_selectedVelocityOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) i)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let Ψ : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3WeakTestFunctionPhysicalL2 ψ)

  let R :
      Set.Icc (0 : ℝ) tau →
        H3FourierComplexL2 :=
    fun q =>
      h3SpectralScalarRawFourierL2
        (W (q : ℝ) i)

  have hW :
      Continuous W := by
    dsimp only [W]
    unfold h3PreterminalTailCanonicalSelectedRestart
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)

  have hCoord :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          W (q : ℝ) i) := by
    exact
      (continuous_apply i).comp
        (hW.comp continuous_subtype_val)

  have hR :
      Continuous R := by
    dsimp only [R]
    exact
      h3SpectralScalarRawFourierL2CLM.continuous.comp
        hCoord

  have hFourierPairing :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          (inner ℂ Ψ (R q)).re) := by
    exact
      Complex.continuous_re.comp
        (continuous_const.inner hR)

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) i))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ Ψ (R q)).re) := by
    funext q

    let qR :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      h3PreterminalElapsedToSelectedUnitRadius
        htauR q

    have hFourier :=
      h3ScalarFourierL2_h3PreterminalSelectedUnitVelocityPhysicalL2OnRadius
        hNS ht hE hTail qR i

    have hFourier' :
        h3ScalarFourierL2
            ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail (q : ℝ)) i)
          =
        R q := by
      dsimp only [R, W]

      simpa only [
        qR,
        h3PreterminalElapsedToSelectedUnitRadius_coe,
        h3PreterminalSelectedUnitSpectralStateOnRadius,
        h3PreterminalTailCanonicalSelectedRestart,
        h3PreterminalSelectedDecoderAnchorState,
        h3PreterminalTailCanonicalAnchorSpectralState
      ] using hFourier

    calc
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) i)
          =
        (inner ℂ
          Ψ
          (h3ScalarFourierL2
            ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail (q : ℝ)) i))).re := by
            symm
            exact
              re_inner_h3ScalarFourierL2_eq_inner
                (h3WeakTestFunctionPhysicalL2 ψ)
                ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
                  (one_pos : (0 : ℝ) < 1)
                  hNS ht hE hTail (q : ℝ)) i)
      _ =
        (inner ℂ Ψ (R q)).re := by
          rw [hFourier']

  rw [hEq]
  exact hFourierPairing

/-- The complete three-component selected weak velocity pairing is continuous
on `[0,tau]`. -/
theorem continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocityOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ))) := by
  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        ∑ i : Fin 3,
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail (q : ℝ)) i)) := by
    funext q

    unfold h3WeakTestVectorPhysicalL2Hilbert
    rw [PiLp.inner_apply]

  rw [hEq]

  apply continuous_finset_sum
  intro i hi

  exact
    continuous_inner_h3WeakTestFunctionPhysicalL2_selectedVelocityOnElapsed
      hNS ht htau hE hTail htauR (φ i) i

/-- Pairing with the selected physical velocity increment from restart time zero
is continuous on the complete closed elapsed interval.  This is the lower
endpoint continuity needed by the selected weak FTC. -/
theorem continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocityIncrementOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
            hNS ht htau hE hTail q)) := by
  unfold
    h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed

  have hSelected :=
    continuous_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocityOnElapsed
      hNS ht htau hE hTail htauR φ

  have hPairingSub :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail (q : ℝ)
            -
           h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail 0))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ))
        -
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail 0)) := by
    funext q
    exact inner_sub_right _ _ _

  rw [hPairingSub]

  exact hSelected.sub continuous_const

end

end Euclidean
end Bridge
end PrimeTensor
