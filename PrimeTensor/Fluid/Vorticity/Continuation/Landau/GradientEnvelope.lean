import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.VelocityEnvelope
import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure

/-!
# Canonical H³ control produces the velocity-gradient envelope

The remaining public Landau continuation frontier after the top-flux closure is

    EnergyClassProducesGradientEnvelope.

At one strict H³ energy-class time, `TopFlux.VelocityEnvelope` already builds
the canonical weighted spectral state and identifies its real `C¹`
representative pointwise with the old logged velocity.

The same spectral representative has an existing first-coordinate derivative
evaluation estimate

    ‖∂ᵢ uⱼ(x)‖ ≤ C₁ ‖Uⱼ‖.

The canonical spectral-state norm is bounded by the normalized physical H³
energy.  Hence

    ‖∂ᵢ uⱼ(x)‖
      ≤ C₁ · velocityH3EnergyAt u t.

Choosing the right-hand side itself as the time-dependent envelope closes
`EnergyClassProducesGradientEnvelope` from canonical H³ data.

No logarithmic BKM endpoint estimate is used here; this is only the ordinary
H³ → W¹,∞ pointwise control needed inside the differentiated energy estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeLandauGradientEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
At every strict time in an H³ energy-class tail, every first spatial derivative
of every logged velocity component is bounded pointwise by the canonical
first-derivative spectral evaluation coefficient times the normalized H³
energy.
-/
theorem norm_loggedVelocityComponent_spatial_d_le_h3Energy
    {
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (i j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖spatial3.d
        i
        (loggedVelocityComponent u t j)
        x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      *
    velocityH3EnergyAt u t := by

  rcases hClass.pressure_witness with
    ⟨p, hPDE, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  let hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T :=
    ⟨p, hPDE⟩

  let hMeas :
      VelocityH3MeasurableAt
        u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS htNS

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hH3 hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS htNS hH3

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hH3 hMeas hFourier

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let r : Fin 3 :=
    h3ClassicalizationFinOfAxis i

  have hAE0 :=
    h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
      hFourier k

  have hAE :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u t j := by

    dsimp only [U, k] at hAE0 ⊢

    simpa only [
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hAE0

  have hSpectralContinuous :
      Continuous
        (
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k)
        ) :=
    (
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        (U k)
    ).continuous

  have hOldContinuous :
      Continuous
        (
          loggedVelocityComponent
            u t j
        ) := by

    unfold loggedVelocityComponent

    exact
      (
        hPDE.regularity.velocity_spatial_three
          t htNS j
      ).continuous

  have hPointwise :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k)
        =
      loggedVelocityComponent
        u t j :=
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hSpectralContinuous
      hOldContinuous

  have hDerivativeEq :
      spatial3.d
          i
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (U k)
          )
          x
        =
      spatial3.d
          i
          (loggedVelocityComponent u t j)
          x :=
    congrArg
      (
        fun f : Point3 → ℝ =>
          spatial3.d i f x
      )
      hPointwise

  have hEvaluation :
      ‖spatial3.d
          i
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (U k)
          )
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      ‖U k‖ := by

    have h :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
        (U k)
        r
        x

    dsimp only [r] at h

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis i
    ] at h

    exact h

  have hCoordinate :
      ‖U k‖ ≤ ‖U‖ :=
    h3SpectralFinVector_coordinate_norm_le
      U k

  have hState :
      ‖U‖
        ≤
      velocityH3EnergyAt u t := by

    dsimp only [U]

    exact
      norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier
        (one_le_velocityH3EnergyAt u t)
        le_rfl

  have hScalar :
      ‖U k‖
        ≤
      velocityH3EnergyAt u t :=
    hCoordinate.trans hState

  have hBound :
      ‖spatial3.d
          i
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (U k)
          )
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      velocityH3EnergyAt u t :=
    hEvaluation.trans
      (
        mul_le_mul_of_nonneg_left
          hScalar
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      )

  rw [← hDerivativeEq]

  exact hBound

/--
Canonical H³ data automatically produce the finite velocity-gradient envelope
required by the Landau differentiated-energy argument.
-/
theorem energyClassProducesGradientEnvelope_of_canonical
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    ) :
    EnergyClassProducesGradientEnvelope := by

  intro
    u a T
    hClass

  have hData :
      CanonicalH3EnergyDataOnTail
        u a T :=
    hCanonical
      u a T hClass

  let h : ℝ → ℝ :=
    fun t =>
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      velocityH3EnergyAt u t

  refine
    ⟨
      h,
      ?_
    ⟩

  intro t ht

  have htIco :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  have hH3 :
      VelocityH3IntegrableAt
        u t :=
    hData.1 t htIco

  intro i j x

  have hBound :=
    norm_loggedVelocityComponent_spatial_d_le_h3Energy
      hClass
      ht
      hH3
      i j x

  have hComponentEq :
      loggedVelocityComponent u t j
        =
      (
        fun y : Point3 =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u t y
          ).component j
      ) := by
    rfl

  dsimp only [h]

  rw [← hComponentEq]

  simpa only [
    Real.norm_eq_abs
  ] using
    hBound

end

end Euclidean
end Bridge
end PrimeTensor
