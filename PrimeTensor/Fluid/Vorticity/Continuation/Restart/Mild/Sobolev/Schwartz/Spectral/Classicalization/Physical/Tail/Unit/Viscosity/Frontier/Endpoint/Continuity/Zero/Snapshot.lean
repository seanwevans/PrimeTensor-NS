import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.WeakMomentum
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Pointwise.Velocity

/-!
# Zeroth-order endpoint continuity: endpoint-independent old spectral snapshots

The pressure-free old weak momentum identity is now available without any
endpoint-continuity hypothesis.  To connect it to the bounded Fourier `L²`
projected RHS, we next isolate the exact spectral state carried by one old
preterminal slice.

For every elapsed `q ∈ [0,tau]`, the canonical weighted H³ state is literally
the Fourier encoding of the old velocity at absolute time `t+q`.  Therefore:

* its canonical real `C¹` representative equals the old logged velocity
  pointwise, not merely almost everywhere;
* it is a genuinely realizable spectral velocity state;
* preterminal incompressibility makes it raw-Fourier divergence-free.

All three facts are snapshot statements.  No time continuity, endpoint path,
selected restart, mild equation, or endpoint hypothesis is used.

These are exactly the hypotheses needed by the generic raw-outer-divergence
bridge in the next increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldSnapshot
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical real `C¹` representative of one old preterminal H³ spectral
snapshot agrees pointwise with the original logged velocity component. -/
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_component_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        i
      =
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 i) := by
  let hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  let hIq :
      VelocityH3IntegrableAt u (t + (q : ℝ)) :=
    h3PreterminalTailIntegrableOnElapsed
      hEnd hTail q

  let hMeas :
      VelocityH3MeasurableAt u (t + (q : ℝ)) :=
    h3PreterminalTailMeasurableOnElapsed
      hNS ht hEnd hTail q

  let hFourier :
      VelocityH3FourierCompatibleAt
        u (t + (q : ℝ)) hIq hMeas :=
    h3PreterminalTailFourierCompatibleOnElapsed
      hNS ht hEnd hTail q

  have hAE :
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q)
          i
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    change
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (velocityH3SpectralStateAt
            u
            (t + (q : ℝ))
            hIq
            hMeas
            hFourier)
          i
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i)

    exact
      h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
        hFourier i

  have hLeft :
      Continuous
        (h3SpectralVelocityRealC1RepresentativeOnPoint3
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q)
          i) := by
    change
      Continuous
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          ((h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q) i))

    exact
      (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        ((h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) i)).continuous

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hOldContinuous :
      Continuous
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent

    exact
      (hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hs
        (h3AxisOfFin3 i)).continuous

  exact
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hLeft
      hOldContinuous

/-- Every canonical old-tail spectral snapshot is physically realizable. -/
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_realizable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralVelocityRealizable
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) := by
  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

  exact
    velocityH3SpectralStateAt_realizable
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)

/-- Preterminal incompressibility makes every canonical old-tail spectral
snapshot raw-Fourier divergence-free. -/
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_rawDivergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinRawDivergenceFree
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) := by
  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

  apply h3SpectralFinRawDivergenceFree_of_divergenceFree

  exact
    velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
      hNS
      (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
      (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)

end

end Euclidean
end Bridge
end PrimeTensor
