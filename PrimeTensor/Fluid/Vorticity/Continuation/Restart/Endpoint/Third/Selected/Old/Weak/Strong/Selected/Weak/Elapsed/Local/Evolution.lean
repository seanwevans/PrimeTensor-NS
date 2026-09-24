import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Diffusion.Physical.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Reduction

/-!
# Selected weak local evolution in elapsed-time coordinates

The selected strict-positive weak temporal equation is now completely physical:

    weak temporal pairing = <Phi, R_sel(q)>.

The weak FTC frontier, however, is written on a fixed elapsed interval
`[0,tau]` with an ambient-real RHS extension.  This file performs exactly that
coordinate conversion.

For every strict interior elapsed time

    0 < r < tau <= R,

the elapsed subtype maps canonically into the selected restart-radius subtype,
and the ambient-real RHS reduces to the genuine selected physical RHS at that
same time.  Hence the already-closed strict-positive weak temporal equation
becomes

    weak temporal pairing at r
      =
    <Phi, R_sel^elapsed(r)>.

No integration, endpoint limit, or new analytic estimate occurs here.  The
next layer can work entirely with ordinary real elapsed time when proving the
selected weak FTC.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakElapsedLocalEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On every strict interior elapsed time, the selected weak temporal pairing
is exactly the Hilbert pairing with the ambient-real elapsed projected RHS. -/
theorem h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_projectedRHSRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun s : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W s i) x)
            r)
        ∂volume)
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR r) := by
  dsimp only

  have hrClosed : r ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hr.1.le, hr.2.le⟩

  let qR :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    h3PreterminalElapsedToSelectedUnitRadius
      htauR
      ⟨r, hrClosed⟩

  have hq0 : 0 < (qR : ℝ) := by
    simpa only [
      qR,
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using hr.1

  have hqR :
      (qR : ℝ) <
        h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hrt :
        r <
          h3FinHeatLerayRestartRadius (1 : ℝ) E :=
      lt_of_lt_of_le hr.2 htauR

    simpa only [
      qR,
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using hrt

  have hLocal :=
    h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_inner_projectedRHS
      hNS ht hE hTail qR hq0 hqR φ

  have hReal :=
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
      hNS ht hE hTail htauR hrClosed

  rw [hReal]

  simpa only [
    qR,
    h3PreterminalElapsedToSelectedUnitRadius_coe
  ] using hLocal

/-- Symmetric form: the scalar elapsed projected-RHS pairing is the strict
positive weak temporal derivative pairing.  This is the orientation consumed
most naturally by an interval-integral FTC proof. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_projectedRHSRealOnElapsed_eq_weakTemporalPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR r)
      =
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun s : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W s i) x)
            r)
        ∂volume := by
  symm

  exact
    h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_projectedRHSRealOnElapsed
      hNS ht htau hE hTail htauR hr φ

end

end Euclidean
end Bridge
end PrimeTensor
