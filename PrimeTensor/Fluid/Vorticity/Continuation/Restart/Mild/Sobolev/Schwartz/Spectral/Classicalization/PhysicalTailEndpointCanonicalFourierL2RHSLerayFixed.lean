import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalVelocityIncrementLerayFixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalFourierL2ForcingContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.ProjectionIncompressibility

/-!
# Classicalization: endpoint Fourier `L²` projected RHS is Leray-fixed

`PhysicalTailEndpointCanonicalVelocityIncrementLerayFixed` closes the velocity
side of the quotient-safe solenoidal frontier.  This file closes the matching
pointwise-in-time statement for the projected RHS, still entirely in genuine
Fourier `L²`.

For one elapsed slice `q ∈ [0,τ]`, define the finite Fourier vector

    R̂(q) = Δ̂W(q) - LerayForcinĝ(W(q),W(q)).

Both pieces are divergence-free.

* The endpoint spectral velocity is an encoded old preterminal Navier--Stokes
  slice, hence is Fourier divergence-free.
* The raw Laplacian is multiplication of every velocity component by the same
  scalar Fourier multiplier, so it preserves divergence-freeness.
* The nonlinear forcing is literally the range of the finite Leray projector,
  and the existing projection-incompressibility theorem says every such range
  value is divergence-free.

The difference is therefore divergence-free, and the existing Leray fixed-point
theorem makes the complete endpoint Fourier `L²` RHS exactly Leray-fixed.

This file deliberately stops before transporting the result through the real
physical reconstruction and the Bochner interval integral.  No pointwise
frequency evaluation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalFourierL2RHSLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Elementary closure of Fourier divergence-free states -/

/-- Fourier divergence-free finite `L²` vectors are closed under subtraction. -/
theorem H3SpectralFinDivergenceFree.sub
    {F G : H3SpectralFinVectorState}
    (hF : H3SpectralFinDivergenceFree F)
    (hG : H3SpectralFinDivergenceFree G) :
    H3SpectralFinDivergenceFree (F - G) := by
  have hSub0 :=
    MeasureTheory.Lp.coeFn_sub (F 0) (G 0)
  have hSub1 :=
    MeasureTheory.Lp.coeFn_sub (F 1) (G 1)
  have hSub2 :=
    MeasureTheory.Lp.coeFn_sub (F 2) (G 2)

  filter_upwards [hF, hG, hSub0, hSub1, hSub2] with
      ξ hFξ hGξ hSub0ξ hSub1ξ hSub2ξ

  simp only [Fin.sum_univ_three] at hFξ hGξ ⊢
  simp only [Pi.sub_apply]

  rw [hSub0ξ, hSub1ξ, hSub2ξ]

  calc
    h3FourierDerivativeSymbol 0 ξ *
          ((F 0 : H3FourierPoint3 → ℂ) ξ -
            (G 0 : H3FourierPoint3 → ℂ) ξ)
        +
      h3FourierDerivativeSymbol 1 ξ *
          ((F 1 : H3FourierPoint3 → ℂ) ξ -
            (G 1 : H3FourierPoint3 → ℂ) ξ)
        +
      h3FourierDerivativeSymbol 2 ξ *
          ((F 2 : H3FourierPoint3 → ℂ) ξ -
            (G 2 : H3FourierPoint3 → ℂ) ξ)
        =
      (h3FourierDerivativeSymbol 0 ξ *
          (F 0 : H3FourierPoint3 → ℂ) ξ
        +
       h3FourierDerivativeSymbol 1 ξ *
          (F 1 : H3FourierPoint3 → ℂ) ξ
        +
       h3FourierDerivativeSymbol 2 ξ *
          (F 2 : H3FourierPoint3 → ℂ) ξ)
        -
      (h3FourierDerivativeSymbol 0 ξ *
          (G 0 : H3FourierPoint3 → ℂ) ξ
        +
       h3FourierDerivativeSymbol 1 ξ *
          (G 1 : H3FourierPoint3 → ℂ) ξ
        +
       h3FourierDerivativeSymbol 2 ξ *
          (G 2 : H3FourierPoint3 → ℂ) ξ) := by
          ring
    _ = 0 := by
      rw [hFξ, hGξ]
      ring

/-! ## Endpoint spectral slice incompressibility -/

/-- Every endpoint-canonical bounded physical spectral slice is divergence-free,
because it is exactly the old encoded preterminal Navier--Stokes slice. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_divergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinDivergenceFree
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q) := by
  rw [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
  ]

  unfold h3PreterminalCanonicalSpectralStateOnElapsed

  exact
    velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
      hNS
      (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
      (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)

/-! ## Diffusion remains divergence-free -/

/-- Applying the common raw-Laplacian multiplier to every coordinate of a
divergence-free weighted spectral state preserves divergence-freeness. -/
theorem h3SpectralFinLaplacianRawFourierL2_divergenceFree
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralFinDivergenceFree G) :
    H3SpectralFinDivergenceFree
      (fun i : Fin 3 =>
        h3SpectralScalarLaplacianRawFourierL2 (G i)) := by
  have hLap :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ i : Fin 3,
          ((h3SpectralScalarLaplacianRawFourierL2 (G i) :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ
            =
          h3SpectralScalarLaplacianRawMultiplier ξ *
            (G i : H3FourierPoint3 → ℂ) ξ := by
    exact ae_all_iff.2 (fun i =>
      h3SpectralScalarLaplacianRawFourierL2_ae (G i))

  filter_upwards [hG, hLap] with ξ hGξ hLapξ

  calc
    (∑ i : Fin 3,
      h3FourierDerivativeSymbol i ξ *
        ((h3SpectralScalarLaplacianRawFourierL2 (G i) :
            H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
        =
      h3SpectralScalarLaplacianRawMultiplier ξ *
        (∑ i : Fin 3,
          h3FourierDerivativeSymbol i ξ *
            (G i : H3FourierPoint3 → ℂ) ξ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hLapξ i]
          ring
    _ = 0 := by
      rw [hGξ, mul_zero]

/-- The endpoint Fourier `L²` Laplacian vector is divergence-free at every
closed elapsed time. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_divergenceFree
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinDivergenceFree
      (fun i : Fin 3 =>
        h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
          hNS ht hEnd hTail q i) := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hRecover : W (q : ℝ) = P q := by
    dsimp only [W]
    unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    exact
      h3PathPhysicalRealExtension_normalizedPhysical_apply
        htau P q

  have hPDiv :
      H3SpectralFinDivergenceFree (P q) := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_divergenceFree
        hNS ht hEnd hE hTail hEndpoint q

  have hLapDiv :
      H3SpectralFinDivergenceFree
        (fun i : Fin 3 =>
          h3SpectralScalarLaplacianRawFourierL2 ((P q) i)) :=
    h3SpectralFinLaplacianRawFourierL2_divergenceFree hPDiv

  have hEq :
      (fun i : Fin 3 =>
        h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
          hNS ht hEnd hTail q i)
        =
      (fun i : Fin 3 =>
        h3SpectralScalarLaplacianRawFourierL2 ((P q) i)) := by
    funext i

    rw [
      h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_spectralLaplacian
        hNS ht htau hEnd hE hTail hEndpoint q i
    ]

    exact congrArg
      (fun G : H3SpectralFinVectorState =>
        h3SpectralScalarLaplacianRawFourierL2 (G i))
      hRecover

  rw [hEq]
  exact hLapDiv

/-! ## Leray forcing is in the divergence-free range -/

/-- The packaged raw Fourier nonlinear forcing vector is always divergence-free:
it is exactly the range of the existing finite Leray projector. -/
theorem h3RawFinLerayOuterProductDivergenceFourierL2_divergenceFree
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinDivergenceFree
      (fun i : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceFourierL2 U V i) := by
  have hEq :
      (fun i : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceFourierL2 U V i)
        =
      h3SpectralFinUnheatedLerayForcingApply U V := by
    funext i
    exact
      (h3SpectralFinUnheatedLerayForcingApply_eq_rawFourierL2
        U V i).symm

  rw [hEq]

  unfold h3SpectralFinUnheatedLerayForcingApply

  exact
    h3SpectralFinLerayApply_divergenceFree
      (h3SpectralFinUnheatedDivergenceApply U V)

/-- The endpoint quotient-safe Fourier `L²` forcing vector is divergence-free
at every closed elapsed time. -/
theorem h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed_divergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinDivergenceFree
      (fun i : Fin 3 =>
        h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
          hNS ht hEnd hE hTail hEndpoint q i) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint q

  have hDiv :=
    h3RawFinLerayOuterProductDivergenceFourierL2_divergenceFree U U

  have hEq :
      (fun i : Fin 3 =>
        h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
          hNS ht hEnd hE hTail hEndpoint q i)
        =
      (fun i : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceFourierL2 U U i) := by
    funext i
    rfl

  rw [hEq]
  exact hDiv

/-! ## Pointwise projected Fourier RHS -/

/-- Complete quotient-safe Fourier `L²` projected RHS vector at one closed
elapsed time. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q i
      -
    h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
        hNS ht hEnd hE hTail hEndpoint q i

/-- The complete endpoint Fourier `L²` projected RHS is divergence-free at
every elapsed time. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed_divergenceFree
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinDivergenceFree
      (h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint q) := by
  have hLap :=
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_divergenceFree
      hNS ht htau hEnd hE hTail hEndpoint q

  have hForce :=
    h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed_divergenceFree
      hNS ht hEnd hE hTail hEndpoint q

  unfold h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed

  exact hLap.sub hForce

/-- Therefore the complete endpoint Fourier `L²` projected RHS is fixed
exactly by the finite Leray projector at every elapsed time. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed_lerayFixed
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
    (q : Set.Icc (0 : ℝ) tau) :
    h3SpectralFinLerayApply
        (h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
          hNS ht htau hEnd hE hTail hEndpoint q)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint q := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed_divergenceFree
        hNS ht htau hEnd hE hTail hEndpoint q)

end

end Euclidean
end Bridge
end PrimeTensor
