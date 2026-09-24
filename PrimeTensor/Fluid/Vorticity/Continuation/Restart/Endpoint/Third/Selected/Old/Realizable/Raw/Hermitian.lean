import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.RHS.Decomposition
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Realizable.Decoder.Injective
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge

/-!
# Realizability implies raw Hermitian symmetry

The existing realizability bridge proves

    raw-Hermitian -> realizable.

For the selected/old weak--strong comparison we also need the reverse direction.
A realizable spectral state has inverse Fourier decoder equal to the
complexification of a real `L²` field.  Applying the forward Fourier isometry
therefore identifies its raw deweighted Fourier state with the Fourier transform
of a complexified real field, which is Hermitian by the existing real-Fourier
symmetry theorem.

Thus realizability and raw-Hermitian symmetry are equivalent for the weighted
spectral states used here.

The final theorem applies this converse to the canonical selected restart.
Because the restart is launched from a genuine encoded real H³ anchor, its
existing realizability theorem immediately yields raw Hermitian symmetry at
every closed canonical-radius time.

No endpoint continuity or old/selected agreement is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal Interval Topology ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldRealizableRawHermitian
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Physical realizability of one weighted scalar spectral state forces exact
Hermitian symmetry of its deweighted Fourier `L²` state. -/
theorem h3SpectralScalarRealizable_rawHermitian
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRealizable G) :
    H3SpectralScalarRawHermitian G := by
  unfold H3SpectralScalarRawHermitian

  have hFourier :=
    congrArg
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      hG

  rw [h3Fourier_h3SpectralScalarDecodeComplexL2] at hFourier

  rw [hFourier]

  exact
    h3FourierL2_complexify_real_hermitian
      (h3SpectralScalarDecodeRealL2 G)

/-- Coordinatewise velocity version of realizable implies raw-Hermitian. -/
theorem h3SpectralVelocityRealizable_rawHermitian
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRealizable U) :
    H3SpectralVelocityRawHermitian U := by
  intro j
  exact
    h3SpectralScalarRealizable_rawHermitian
      (hU j)

/-- The canonical selected restart is raw-Hermitian at every closed time in
its restart radius.

This is obtained from the already-proved realizability of the selected mild
solution launched from the genuine encoded old H³ anchor. -/
theorem h3PreterminalSelectedPhysicalExtension_rawHermitian
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E)) :
    H3SpectralVelocityRawHermitian
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)
        (q : ℝ)) := by
  apply h3SpectralVelocityRealizable_rawHermitian

  let hInt : VelocityH3IntegrableAt u t :=
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  have hBound :
      ‖velocityH3SpectralStateAt
          u t hInt hMeas hFourier‖
        ≤ E := by
    change
      ‖h3PreterminalSelectedDecoderAnchorState
          hNS ht hTail‖
        ≤ E

    exact
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht hE hTail

  have hRealizable :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_encoded_realizable
      hν
      hFourier
      (lt_of_lt_of_le zero_lt_one hE)
      hBound
      q

  unfold h3PreterminalSelectedDecoderAnchorState
  unfold h3PreterminalCanonicalAnchorSpectralState
  dsimp only

  exact hRealizable

end

end Euclidean
end Bridge
end PrimeTensor
