import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathVorticityAprioriFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.GradientEnvelope

/-!
# Canonical H³ energy envelope for preterminal vorticity

The remaining H³-path frontier is temporal: finite `L¹_t L∞_x` vorticity.
The spatial part follows directly from the already-built weighted H³ spectral
encoder.

The exact spectral identity

    1 + ∑ j, ‖U_j(t)‖² = E_H3(t)

gives the sharp state estimate

    ‖U(t)‖ ≤ sqrt (E_H3(t)).

The existing inverse-Fourier first-derivative evaluation estimate therefore
gives

    |∂ᵢ uⱼ(t,x)| ≤ C₁ sqrt (E_H3(t)).

Each vorticity component is a difference of two first derivatives, hence

    |ω_m(t,x)| ≤ 2 C₁ sqrt (E_H3(t)).

Thus the spatial `L∞_x` part of the BKM control is automatic on every strict
H³-path slice.  What remains is the genuinely temporal question of integrability
of this (or a sharper) envelope up to the terminal time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathVorticityEnergyEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical weighted spectral velocity state is bounded by the square
root of the exact normalized physical H³ energy. -/
theorem norm_velocityH3SpectralStateAt_le_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas) :
    ‖velocityH3SpectralStateAt
        u t hInt hMeas hFourier‖
      ≤
    Real.sqrt (velocityH3EnergyAt u t) := by

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier

  have hExact :
      1 + h3SpectralVelocitySquareEnergy U
        =
      velocityH3EnergyAt u t := by
    simpa only [U] using
      one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
        hFourier

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t :=
    le_trans
      zero_le_one
      (one_le_velocityH3EnergyAt u t)

  change
    ‖U‖ ≤ Real.sqrt (velocityH3EnergyAt u t)

  apply
    (pi_norm_le_iff_of_nonneg
      (Real.sqrt_nonneg
        (velocityH3EnergyAt u t))).2

  intro j

  have hCoordinateSquare :
      ‖U j‖ ^ 2
        ≤
      h3SpectralVelocitySquareEnergy U := by
    unfold h3SpectralVelocitySquareEnergy
    exact
      Finset.single_le_sum
        (fun i _ => sq_nonneg ‖U i‖)
        (Finset.mem_univ j)

  have hSquare :
      ‖U j‖ ^ 2
        ≤
      velocityH3EnergyAt u t := by
    linarith

  have hSqrtSquare :
      (Real.sqrt (velocityH3EnergyAt u t)) ^ 2
        =
      velocityH3EnergyAt u t := by
    simpa using
      Real.sq_sqrt hEnergyNonneg

  rw [← hSqrtSquare] at hSquare

  exact
    le_of_sq_le_sq
      hSquare
      (Real.sqrt_nonneg _)

/-- On every strict H³-path slice, every first spatial derivative of every
logged velocity component is bounded by the sharp square-root H³ energy
envelope. -/
theorem norm_loggedVelocityComponent_spatial_d_le_sqrt_h3Energy_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (i j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖spatial3.d
        i
        (loggedVelocityComponent u t j)
        x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      *
    Real.sqrt (velocityH3EnergyAt u t) := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible u T :=
    hH3.navier_stokes

  let hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht

  let hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier

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
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k)) :=
    (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
      (U k)).continuous

  have hOldContinuous :
      Continuous
        (loggedVelocityComponent u t j) := by

    let p :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
      Classical.choose hNS

    have hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          p T := by
      dsimp only [p, hNS]
      exact Classical.choose_spec hH3.navier_stokes

    unfold loggedVelocityComponent

    exact
      (hPDE.regularity.velocity_spatial_three
        t ht j).continuous

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
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k))
          x
        =
      spatial3.d
          i
          (loggedVelocityComponent u t j)
          x :=
    congrArg
      (fun f : Point3 → ℝ =>
        spatial3.d i f x)
      hPointwise

  have hEvaluation :
      ‖spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k))
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
      Real.sqrt (velocityH3EnergyAt u t) := by
    dsimp only [U]
    exact
      norm_velocityH3SpectralStateAt_le_sqrt_energy
        hFourier

  have hScalar :
      ‖U k‖
        ≤
      Real.sqrt (velocityH3EnergyAt u t) :=
    hCoordinate.trans hState

  have hBound :
      ‖spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k))
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) :=
    hEvaluation.trans
      (mul_le_mul_of_nonneg_left
        hScalar
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg)

  rw [← hDerivativeEq]

  exact hBound

/-- Any common pointwise envelope for all first velocity derivatives gives a
common vorticity envelope with twice the size. -/
theorem vorticityEnvelope_two_mul_of_velocityGradientEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {h : ℝ → ℝ}
    {t : ℝ}
    (hGradient : VelocityGradientEnvelope u h t) :
    VorticityEnvelope
      u
      (fun s : ℝ => 2 * h s)
      t := by

  intro x

  have hyz :=
    hGradient yAxis zAxis x

  have hzy :=
    hGradient zAxis yAxis x

  have hzx :=
    hGradient zAxis xAxis x

  have hxz :=
    hGradient xAxis zAxis x

  have hxy :=
    hGradient xAxis yAxis x

  have hyx :=
    hGradient yAxis xAxis x

  refine
    ⟨
      ?_,
      ?_,
      ?_
    ⟩

  · unfold realVorticityX

    calc
      |spatial3.d
          yAxis
          (fun y =>
            (logSpaceTimeVectorField u t y).component zAxis)
          x
        -
        spatial3.d
          zAxis
          (fun y =>
            (logSpaceTimeVectorField u t y).component yAxis)
          x|
          ≤
        |spatial3.d
            yAxis
            (fun y =>
              (logSpaceTimeVectorField u t y).component zAxis)
            x|
          +
        |spatial3.d
            zAxis
            (fun y =>
              (logSpaceTimeVectorField u t y).component yAxis)
            x| :=
        abs_sub _ _
      _ ≤ h t + h t :=
        add_le_add hyz hzy
      _ = 2 * h t := by ring

  · unfold realVorticityY

    calc
      |spatial3.d
          zAxis
          (fun y =>
            (logSpaceTimeVectorField u t y).component xAxis)
          x
        -
        spatial3.d
          xAxis
          (fun y =>
            (logSpaceTimeVectorField u t y).component zAxis)
          x|
          ≤
        |spatial3.d
            zAxis
            (fun y =>
              (logSpaceTimeVectorField u t y).component xAxis)
            x|
          +
        |spatial3.d
            xAxis
            (fun y =>
              (logSpaceTimeVectorField u t y).component zAxis)
            x| :=
        abs_sub _ _
      _ ≤ h t + h t :=
        add_le_add hzx hxz
      _ = 2 * h t := by ring

  · unfold realVorticityZ

    calc
      |spatial3.d
          xAxis
          (fun y =>
            (logSpaceTimeVectorField u t y).component yAxis)
          x
        -
        spatial3.d
          yAxis
          (fun y =>
            (logSpaceTimeVectorField u t y).component xAxis)
          x|
          ≤
        |spatial3.d
            xAxis
            (fun y =>
              (logSpaceTimeVectorField u t y).component yAxis)
            x|
          +
        |spatial3.d
            yAxis
            (fun y =>
              (logSpaceTimeVectorField u t y).component xAxis)
            x| :=
        abs_sub _ _
      _ ≤ h t + h t :=
        add_le_add hxy hyx
      _ = 2 * h t := by ring

/-- The canonical spatial vorticity envelope obtained directly from H³ energy. -/
noncomputable def h3PathCanonicalVorticitySqrtEnergyEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    2 *
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
      )

/-- Every strict slice of an admissible H³ path satisfies the canonical
square-root-energy vorticity envelope. -/
theorem h3PathCanonicalVorticitySqrtEnergyEnvelope_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    VorticityEnvelope
      u
      (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
      t := by

  let h : ℝ → ℝ :=
    fun s =>
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u s)

  have hGradient :
      VelocityGradientEnvelope u h t := by

    intro i j x

    have hBound :=
      norm_loggedVelocityComponent_spatial_d_le_sqrt_h3Energy_of_h3Path
        hH3 ht i j x

    change
      abs
        (spatial3.d
          i
          (loggedVelocityComponent u t j)
          x)
        ≤
      h t

    dsimp only [h]

    simpa only [Real.norm_eq_abs] using hBound

  have hVorticity :=
    vorticityEnvelope_two_mul_of_velocityGradientEnvelope
      hGradient

  change
    VorticityEnvelope
      u
      (fun s : ℝ =>
        2 *
          (
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u s)
          ))
      t

  exact hVorticity

/-- Global proposition packaging the now-closed spatial half of the H³-path
vorticity frontier. -/
def H3PathCanonicalVorticitySqrtEnergyEnvelopeOnPreterminal : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ t : ℝ,
        t ∈ Set.Ioo (0 : ℝ) T →
        VorticityEnvelope
          u
          (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
          t

/-- The canonical square-root H³ energy envelope controls vorticity pointwise
throughout every strict preterminal H³ path. -/
theorem h3PathCanonicalVorticitySqrtEnergyEnvelopeOnPreterminal_closed :
    H3PathCanonicalVorticitySqrtEnergyEnvelopeOnPreterminal := by

  intro u T hH3 t ht

  exact
    h3PathCanonicalVorticitySqrtEnergyEnvelope_at
      hH3 ht

end

end Euclidean
end Bridge
end PrimeTensor
