import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Diffusion.Sign
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Selected.Incompressibility

/-!
# Selected--old weak--strong difference is Leray-fixed

The transport estimate is now expressed in the physical `L²` norm of the
concrete selected-minus-old velocity difference.  To remove the Leray
projection from the nonlinear forcing pairing, the difference itself must be
recognized as solenoidal in the quotient-safe physical Hilbert space.

This file closes that structural step.

For the selected branch:

* the canonical restart spectral state is Fourier divergence-free;
* therefore the weighted finite Leray multiplier fixes it;
* exact deweighting commutes with the Leray multiplier;
* scalar Plancherel identifies the deweighted state with the concrete selected
  physical `L²` velocity.

Hence the selected physical velocity is Leray-fixed.  The old physical slice
is already known to be Leray-fixed.  Linearity then gives the same property for

    D = U_selected - U_old.

No transport estimate or nonlinear pairing is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongDifferenceLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The unit-viscosity selected weighted spectral state is Fourier
divergence-free on the whole closed canonical restart radius. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_divergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3SpectralFinDivergenceFree
      (h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail q) := by
  have hAnchor :
      H3SpectralFinDivergenceFree
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht hTail) := by
    unfold h3PreterminalSelectedDecoderAnchorState
    unfold h3PreterminalCanonicalAnchorSpectralState

    exact
      velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
        hNS
        ht
        (canonicalH3TailDataFrom_at_anchor ht hTail).1

  unfold h3PreterminalSelectedUnitSpectralStateOnRadius

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_divergenceFree
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht hE hTail)
      hAnchor
      q.property.1
      q.property.2

/-- Consequently the weighted selected state itself is fixed by the finite
Leray multiplier. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3SpectralFinLerayApply
        (h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail q)
      =
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (h3PreterminalSelectedUnitSpectralStateOnRadius_divergenceFree
        hNS ht hE hTail q)

/-- Deweighted raw Fourier vector of the selected unit-viscosity state. -/
noncomputable def h3PreterminalSelectedUnitRawFourierVectorOnRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3SpectralScalarRawFourierL2
      ((h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail q) i)

/-- Exact deweighting transports selected weighted Leray-fixedness to the raw
Fourier vector. -/
theorem h3PreterminalSelectedUnitRawFourierVectorOnRadius_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3SpectralFinLerayApply
        (h3PreterminalSelectedUnitRawFourierVectorOnRadius
          hNS ht hE hTail q)
      =
    h3PreterminalSelectedUnitRawFourierVectorOnRadius
      hNS ht hE hTail q := by
  let G : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  have hG :
      h3SpectralFinLerayApply G = G := by
    dsimp only [G]
    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_lerayFixed
        hNS ht hE hTail q

  funext i

  change
    h3SpectralFinLerayApply
        (fun j : Fin 3 =>
          h3SpectralScalarRawFourierL2 (G j))
        i
      =
    h3SpectralScalarRawFourierL2 (G i)

  rw [
    ← h3SpectralFinLerayApply_rawFourierL2_apply G i,
    hG
  ]

/-- The canonical physical raw Fourier vector of the concrete selected
velocity is exactly the deweighted selected spectral state. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitVelocityOnRadius_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
      =
    h3PreterminalSelectedUnitRawFourierVectorOnRadius
      hNS ht hE hTail q := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalSelectedUnitRawFourierVectorOnRadius

  exact
    h3ScalarFourierL2_h3PreterminalSelectedUnitVelocityPhysicalL2OnRadius
      hNS ht hE hTail q i

/-- The concrete selected physical velocity is Leray-fixed at every closed
restart-radius time. -/
theorem h3PreterminalSelectedUnitVelocityPhysicalL2HilbertOnRadius_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitVelocityOnRadius_eq
      hNS ht hE hTail q
  ]

  exact
    h3PreterminalSelectedUnitRawFourierVectorOnRadius_lerayFixed
      hNS ht hE hTail q

/-- The canonical raw Fourier map on physical three-component `L²` is linear
under subtraction. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_sub
    (V W : H3PhysicalRealFinVectorL2Hilbert) :
    h3PhysicalRealFinVectorL2HilbertRawFourier (V - W)
      =
    h3PhysicalRealFinVectorL2HilbertRawFourier V
      -
    h3PhysicalRealFinVectorL2HilbertRawFourier W := by
  funext i

  unfold h3PhysicalRealFinVectorL2HilbertRawFourier
  simp only [PiLp.sub_apply, Pi.sub_apply]

  exact h3ScalarFourierL2_sub (V i) (W i)

/-- Physical Leray-fixed states are closed under subtraction. -/
theorem H3PhysicalRealFinVectorL2HilbertLerayFixed.sub
    {V W : H3PhysicalRealFinVectorL2Hilbert}
    (hV : H3PhysicalRealFinVectorL2HilbertLerayFixed V)
    (hW : H3PhysicalRealFinVectorL2HilbertLerayFixed W) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed (V - W) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed at hV hW ⊢

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_sub,
    h3SpectralFinLerayApply_sub,
    hV,
    hW
  ]

/-- The actual unit-viscosity selected-minus-old physical `L²` velocity
difference is Leray-fixed on every closed strict elapsed interval. -/
theorem h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q) := by
  unfold h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed

  apply H3PhysicalRealFinVectorL2HilbertLerayFixed.sub

  · have hSelected :=
      h3PreterminalSelectedUnitVelocityPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)

    simpa only [
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using hSelected

  · exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail q

end

end Euclidean
end Bridge
end PrimeTensor
