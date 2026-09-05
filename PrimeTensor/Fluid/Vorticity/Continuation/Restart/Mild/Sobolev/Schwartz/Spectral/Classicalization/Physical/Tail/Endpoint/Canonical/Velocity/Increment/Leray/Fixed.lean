import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Leray.Physical.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Identification

/-!
# Classicalization: the physical endpoint velocity increment is Leray-fixed

The admissible-closure reduction isolates two physical `L²` membership facts.
This file closes the first one at the natural Fourier/Leray level.

For a three-component real physical `L²` Hilbert state `V`, define its canonical
raw Fourier vector coordinatewise by the scalar Plancherel bridge

    Vᵢ ↦ h3ScalarFourierL2 Vᵢ.

Call `V` Leray-fixed when the existing finite Leray multiplier fixes that raw
Fourier vector exactly.

Every old preterminal velocity slice has this property:

* physical incompressibility makes the canonical weighted H³ encoder
  divergence-free;
* the finite Leray multiplier fixes that weighted encoder;
* exact H³ deweighting commutes with the Leray matrix;
* the deweighted encoder is exactly the old zeroth-order/base Fourier `L²`
  state;
* that base Fourier state is exactly the scalar Plancherel transform of the
  physical zeroth-order `L²` jet.

Hence both endpoint velocity states at elapsed times `0` and `τ` are
Leray-fixed.  Linearity of the scalar Fourier bridge and of Leray then shows
that their difference, the physical endpoint velocity increment, is
Leray-fixed as well.

This is a quotient-safe solenoidal statement.  No pointwise frequency
evaluation and no new density theorem are used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalVelocityIncrementLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalVelocityIncrementLerayFixed :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Raw Fourier vector of a physical Hilbert state -/

/-- Canonical raw Fourier vector of a three-component real physical `L²`
Hilbert state. -/
noncomputable def h3PhysicalRealFinVectorL2HilbertRawFourier
    (V : H3PhysicalRealFinVectorL2Hilbert) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3ScalarFourierL2 (V i)

/-- A real physical `L²` Hilbert vector is solenoidal at the quotient-safe
Fourier level when the existing finite Leray multiplier fixes its canonical
raw Fourier vector. -/
def H3PhysicalRealFinVectorL2HilbertLerayFixed
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  h3SpectralFinLerayApply
      (h3PhysicalRealFinVectorL2HilbertRawFourier V)
    =
  h3PhysicalRealFinVectorL2HilbertRawFourier V

/-- Physical zeroth-order velocity state at one elapsed time, bundled in the
finite `PiLp 2` Hilbert product. -/
noncomputable def h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 i) q)

/-- The raw Fourier vector of the physical zeroth-order state is exactly the
coordinatewise deweighting of the canonical H³ spectral encoder. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_velocityOnElapsed_eq_deweightedSpectral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) i) := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed

  simp only [PiLp.toLp_apply]

  calc
    h3ScalarFourierL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 i) q)
        =
      velocityH3BaseFourierAt
        u
        (t + (q : ℝ))
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        i := by
          rfl
    _ =
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) i) := by
          symm

          unfold h3PreterminalTailCanonicalSpectralStateOnElapsed
          unfold velocityH3SpectralStateAt

          exact
            h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
              (h3PreterminalTailFourierCompatibleOnElapsed
                hNS ht hEnd hTail q)
              i

/-- Every physical zeroth-order old-solution slice on the closed elapsed
interval is exactly Leray-fixed in raw Fourier `L²`. -/
theorem h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q) := by
  let G : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hGFixed :
      h3SpectralFinLerayApply G = G := by
    dsimp only [G]

    unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

    exact
      h3SpectralFinLerayApply_velocityH3SpectralStateAt_eq_of_loggedPreterminalNavierStokes
        hNS
        (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)

  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_velocityOnElapsed_eq_deweightedSpectral
      hNS ht hEnd hTail q
  ]

  funext i

  rw [
    ← h3SpectralFinLerayApply_rawFourierL2_apply G i,
    hGFixed
  ]

/-! ## Endpoint difference -/

/-- The raw Fourier vector of the physical endpoint velocity increment is the
difference of the two endpoint raw Fourier vectors. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_velocityIncrement_eq_sub
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
          hNS ht htau hEnd hTail)
      =
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail
          ⟨tau, ⟨htau.le, le_rfl⟩⟩)
      -
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail
          ⟨0, ⟨le_rfl, htau.le⟩⟩) := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed

  simp only [PiLp.toLp_apply, Pi.sub_apply]

  exact
    h3ScalarFourierL2_sub
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail
        (h3JetSlot0 i)
        ⟨tau, ⟨htau.le, le_rfl⟩⟩)
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail
        (h3JetSlot0 i)
        ⟨0, ⟨le_rfl, htau.le⟩⟩)

/-- The genuine physical endpoint velocity increment is Leray-fixed in raw
Fourier `L²`.  This closes the velocity side of the solenoidal membership
frontier. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail) := by
  let Vτ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail
      ⟨tau, ⟨htau.le, le_rfl⟩⟩

  let V0 : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail
      ⟨0, ⟨le_rfl, htau.le⟩⟩

  have hτ :
      h3SpectralFinLerayApply
          (h3PhysicalRealFinVectorL2HilbertRawFourier Vτ)
        =
      h3PhysicalRealFinVectorL2HilbertRawFourier Vτ := by
    dsimp only [Vτ]
    exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail
        ⟨tau, ⟨htau.le, le_rfl⟩⟩

  have h0 :
      h3SpectralFinLerayApply
          (h3PhysicalRealFinVectorL2HilbertRawFourier V0)
        =
      h3PhysicalRealFinVectorL2HilbertRawFourier V0 := by
    dsimp only [V0]
    exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail
        ⟨0, ⟨le_rfl, htau.le⟩⟩

  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_velocityIncrement_eq_sub
      hNS ht htau hEnd hTail
  ]

  change
    h3SpectralFinLerayApply
        (h3PhysicalRealFinVectorL2HilbertRawFourier Vτ -
          h3PhysicalRealFinVectorL2HilbertRawFourier V0)
      =
    h3PhysicalRealFinVectorL2HilbertRawFourier Vτ -
      h3PhysicalRealFinVectorL2HilbertRawFourier V0

  rw [h3SpectralFinLerayApply_sub, hτ, h0]

end

end Euclidean
end Bridge
end PrimeTensor
