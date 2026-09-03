import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedRawOuterDivergenceAdvection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealSpatialPDEForm

/-!
# Selected H³ pressure momentum identity

The three ingredients of the physical momentum balance are now all available on
the canonical selected restart:

* the selected real temporal PDE
      ∂ₜ uᵢ = ν Δuᵢ - Re(PFᵢ);
* the unprojected raw forcing reconstruction
      Re(Fᵢ) = (u · ∇)uᵢ;
* the physical pressure-force identity
      -∂ᵢp = Re(Fᵢ) - Re(PFᵢ).

This file combines them without any new estimate.  For each `Fin 3`
coordinate, on every strict positive interior restart time,

    ∂ₜ uᵢ + (u · ∇)uᵢ
      =
    -∂ᵢ p + ν Δuᵢ.

The pressure is the canonical pressure reconstructed pointwise from the selected
spectral path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureMomentum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinatewise physical momentum equation for the canonical selected H³
restart, with the Laplacian left in the exact finite-coordinate form already
used by the selected real PDE theorem. -/
theorem h3PreterminalTailCanonicalSelectedRestart_pressure_momentum_fin
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs0 : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν E)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail
    temporal.d
        (fun τ : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W τ i) x)
        s
      +
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3RawFinPressureRealC1OfPath W)
        s x
        (h3AxisOfFin3 i)
      +
    ν *
      (∑ j : Fin 3,
        spatial3.d
          (h3AxisOfFin3 j)
          (spatial3.d
            (h3AxisOfFin3 j)
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s i)))
          x) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      hν hNS ht hE hTail

  have hPDE :
      temporal.d
          (fun τ : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W τ i) x)
          s
        =
      ν *
          (∑ j : Fin 3,
            spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W s i)))
              x)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re := by
    have h :=
      temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_spatialLaplacian_sub_forcing
        hν U₀ hA hU₀ hs0 hsR i x

    simpa only [
      U₀,
      W,
      h3PreterminalTailCanonicalSelectedRestart
    ] using h

  have hAdv :
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence
          (W s) (W s) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        s x).component
          (h3AxisOfFin3 i) := by
    simpa only [W] using
      h3PreterminalTailCanonicalSelectedRestart_rawOuterDivergence_fourierInv_re_eq_advection
        hν hNS ht hE hTail hs0.le hsR.le i x

  have hPressure :
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x
          (h3AxisOfFin3 i)
        =
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence
          (W s) (W s) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W s) (W s) i x).re := by
    exact
      h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
        W s i x

  rw [hPDE, ← hAdv, hPressure]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
