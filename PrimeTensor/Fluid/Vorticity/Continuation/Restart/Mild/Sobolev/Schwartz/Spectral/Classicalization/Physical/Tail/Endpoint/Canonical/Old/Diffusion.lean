import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Pressure.Force
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Diffusion
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalIncompressibility

/-!
# Classicalization: endpoint diffusion is the old physical Laplacian

The quotient-safe endpoint diffusion package is a Fourier `L²` sum of the
three diagonal second-order H³ jet slots.  Those Fourier slots came from the
concrete physical `L²` jet by the scalar Plancherel bridge.

This file closes that representation loop.

For one velocity coordinate at elapsed time `q`, define the physical `L²`
Laplacian as the sum

    ∂₁∂₁ uⱼ + ∂₂∂₂ uⱼ + ∂₃∂₃ uⱼ

of the three concrete old-solution jet slots.  Then:

* its scalar Plancherel transform is exactly the already-defined quotient-safe
  Fourier `L²` diffusion state;
* its `L²` representative is almost everywhere the old logged velocity
  Laplacian;
* on the genuine endpoint interval, the pointwise Laplacian of the canonical
  reconstructed velocity is exactly the same old logged velocity Laplacian;
* hence the physical `L²` diffusion state represents the endpoint path's
  reconstructed Laplacian almost everywhere.

No time derivative, old-pressure Fourier transform, pressure uniqueness, or
mild equation is used.  This isolates the complete spatial diffusion side
before the remaining time-evolution bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalOldDiffusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalOldDiffusion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical `L²` Laplacian of one old-solution velocity coordinate at an
elapsed preterminal time, packaged directly from the three diagonal
second-order H³ jet slots. -/
noncomputable def h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    H3ScalarL2 :=
  h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 0 0) q
    +
  h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 1 1) q
    +
  h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 2 2) q

/-- The scalar Plancherel transform of the physical `L²` Laplacian is exactly
the quotient-safe Fourier `L²` diffusion package already used by the endpoint
path. -/
theorem h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
          hNS ht hEnd hTail q j)
      =
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
      hNS ht hEnd hTail q j := by
  unfold
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
  rw [h3ScalarFourierL2_add, h3ScalarFourierL2_add]
  rfl

/-- The physical `L²` Laplacian represents the old logged velocity Laplacian
almost everywhere. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed_ae_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    ((h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q j : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))
          x) := by
  let A0 : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 0 0) q
  let A1 : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 1 1) q
  let A2 : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot2 j 2 2) q

  have h0 :
      ((A0 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u
        (t + (q : ℝ))
        (h3JetSlot2 j 0 0) := by
    dsimp only [A0, h3PreterminalCanonicalL2JetOnElapsed]
    exact
      velocityH3L2JetAt_ae_eq_jetField
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        (h3JetSlot2 j 0 0)

  have h1 :
      ((A1 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u
        (t + (q : ℝ))
        (h3JetSlot2 j 1 1) := by
    dsimp only [A1, h3PreterminalCanonicalL2JetOnElapsed]
    exact
      velocityH3L2JetAt_ae_eq_jetField
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        (h3JetSlot2 j 1 1)

  have h2 :
      ((A2 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u
        (t + (q : ℝ))
        (h3JetSlot2 j 2 2) := by
    dsimp only [A2, h3PreterminalCanonicalL2JetOnElapsed]
    exact
      velocityH3L2JetAt_ae_eq_jetField
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        (h3JetSlot2 j 2 2)

  change
    (((A0 + A1) + A2 : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))
          x)

  filter_upwards [
    MeasureTheory.Lp.coeFn_add A0 A1,
    MeasureTheory.Lp.coeFn_add (A0 + A1) A2,
    h0,
    h1,
    h2
  ] with x h01 h012 h0x h1x h2x

  rw [h012]
  simp only [Pi.add_apply]
  rw [h01]
  simp only [Pi.add_apply]
  rw [h0x, h1x, h2x]

  simp only [
    Fin.sum_univ_three,
    velocityH3JetFieldAt,
    h3JetSlot2,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

/-- On the genuine endpoint interval, the spatial Laplacian of the canonical
reconstructed velocity is pointwise exactly the old logged velocity
Laplacian. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_laplacian_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    (∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i)))
        x)
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (loggedVelocityComponent
            u
            (t + s)
            (h3AxisOfFin3 i)))
        x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hi :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component
          (h3AxisOfFin3 i))
        =
      loggedVelocityComponent
        u
        (t + s)
        (h3AxisOfFin3 i) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint s hs i

  change
    (∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i)))
        x)
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (loggedVelocityComponent
            u
            (t + s)
            (h3AxisOfFin3 i)))
        x

  apply Finset.sum_congr rfl
  intro k hk
  exact
    congrArg
      (fun f : ScalarField3 =>
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            f)
          x)
      hi

/-- Therefore the physical `L²` Laplacian package represents the endpoint
path's reconstructed spatial Laplacian almost everywhere on every genuine
physical slice. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed_ae_eq_normalizedRealPath
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    ((h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail ⟨s, hs⟩ i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hOld :=
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed_ae_eq_old
      hNS ht hEnd hTail ⟨s, hs⟩ i

  filter_upwards [hOld] with x hx

  calc
    ((h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail ⟨s, hs⟩ i : H3ScalarL2) :
        Point3 → ℝ) x
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (loggedVelocityComponent
              u
              (t + s)
              (h3AxisOfFin3 i)))
          x := by
      simpa only using hx
    _ =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x := by
      symm
      simpa only [W] using
        h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_laplacian_eq_old
          hNS ht htau hEnd hE hTail hEndpoint s hs i x

end

end Euclidean
end Bridge
end PrimeTensor
