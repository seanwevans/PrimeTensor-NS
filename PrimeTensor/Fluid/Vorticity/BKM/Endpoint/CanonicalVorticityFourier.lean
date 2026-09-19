import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicGradientReconstruction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity

/-!
# BKM endpoint: physical vorticity is the canonical Fourier curl

The localized Biot--Savart identities are written in terms of the canonical
pairwise Fourier curl amplitudes

    C01 = d₁ û₀ - d₀ û₁,
    C02 = d₂ û₀ - d₀ û₂,
    C12 = d₂ û₁ - d₁ û₂.

The physical BKM estimate, however, is written in terms of the classical
vorticity components

    ωₓ = ∂y u_z - ∂z u_y,
    ωᵧ = ∂z u_x - ∂x u_z,
    ω_z = ∂x u_y - ∂y u_x.

The H³ jet already contains every first derivative as a genuine real `L²`
class.  Package the three physical vorticity components as exact differences
of those first-derivative slots.  Their scalar Plancherel transforms are then
the corresponding differences of Fourier first-jet slots.

Under `VelocityH3FourierCompatibleAt`, this gives the exact sign convention

    Fourier(ωₓ) = -C12,
    Fourier(ωᵧ) =  C02,
    Fourier(ω_z) = -C01

almost everywhere.

The same packages are also shown to represent the literal classical physical
vorticity fields almost everywhere.  This is the precise bridge needed before
transporting each localized multiplier product to physical convolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointCanonicalVorticityFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointCanonicalVorticityFourier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical x-vorticity as the exact difference of two first-jet `L²` slots. -/
noncomputable def h3BKMPhysicalVorticityXL2
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    H3ScalarL2 :=
  velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (2 : Fin 3) (1 : Fin 3))
    -
  velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (1 : Fin 3) (2 : Fin 3))

/-- Physical y-vorticity as the exact difference of two first-jet `L²` slots. -/
noncomputable def h3BKMPhysicalVorticityYL2
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    H3ScalarL2 :=
  velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (0 : Fin 3) (2 : Fin 3))
    -
  velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (2 : Fin 3) (0 : Fin 3))

/-- Physical z-vorticity as the exact difference of two first-jet `L²` slots. -/
noncomputable def h3BKMPhysicalVorticityZL2
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    H3ScalarL2 :=
  velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (1 : Fin 3) (0 : Fin 3))
    -
  velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (0 : Fin 3) (1 : Fin 3))

/-- The x-vorticity `L²` package represents the literal classical field a.e. -/
theorem h3BKMPhysicalVorticityXL2_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ((h3BKMPhysicalVorticityXL2 u t hInt hMeas :
        H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    fun x : Point3 =>
      realVorticityX
        (logSpaceTimeVectorField u)
        t
        x := by

  let A :=
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (2 : Fin 3) (1 : Fin 3))

  let B :=
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (1 : Fin 3) (2 : Fin 3))

  have hSub :=
    MeasureTheory.Lp.coeFn_sub A B

  have hA :
      ((A : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u t (h3JetSlot1 (2 : Fin 3) (1 : Fin 3)) := by
    simpa only [A] using
      (velocityH3L2JetAt_ae_eq_jetField
        hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (1 : Fin 3)))

  have hB :
      ((B : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u t (h3JetSlot1 (1 : Fin 3) (2 : Fin 3)) := by
    simpa only [B] using
      (velocityH3L2JetAt_ae_eq_jetField
        hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (2 : Fin 3)))

  unfold h3BKMPhysicalVorticityXL2
  change ((A - B : H3ScalarL2) : Point3 → ℝ) =ᵐ[volume] _

  filter_upwards [hSub, hA, hB] with x hSubx hAx hBx

  rw [hSubx, Pi.sub_apply, hAx, hBx]

  simp only [
    velocityH3JetFieldAt,
    h3JetSlot1,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rfl

/-- The y-vorticity `L²` package represents the literal classical field a.e. -/
theorem h3BKMPhysicalVorticityYL2_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ((h3BKMPhysicalVorticityYL2 u t hInt hMeas :
        H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    fun x : Point3 =>
      realVorticityY
        (logSpaceTimeVectorField u)
        t
        x := by

  let A :=
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (0 : Fin 3) (2 : Fin 3))

  let B :=
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (2 : Fin 3) (0 : Fin 3))

  have hSub :=
    MeasureTheory.Lp.coeFn_sub A B

  have hA :
      ((A : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u t (h3JetSlot1 (0 : Fin 3) (2 : Fin 3)) := by
    simpa only [A] using
      (velocityH3L2JetAt_ae_eq_jetField
        hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (2 : Fin 3)))

  have hB :
      ((B : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u t (h3JetSlot1 (2 : Fin 3) (0 : Fin 3)) := by
    simpa only [B] using
      (velocityH3L2JetAt_ae_eq_jetField
        hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (0 : Fin 3)))

  unfold h3BKMPhysicalVorticityYL2
  change ((A - B : H3ScalarL2) : Point3 → ℝ) =ᵐ[volume] _

  filter_upwards [hSub, hA, hB] with x hSubx hAx hBx

  rw [hSubx, Pi.sub_apply, hAx, hBx]

  simp only [
    velocityH3JetFieldAt,
    h3JetSlot1,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rfl

/-- The z-vorticity `L²` package represents the literal classical field a.e. -/
theorem h3BKMPhysicalVorticityZL2_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ((h3BKMPhysicalVorticityZL2 u t hInt hMeas :
        H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    fun x : Point3 =>
      realVorticityZ
        (logSpaceTimeVectorField u)
        t
        x := by

  let A :=
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (1 : Fin 3) (0 : Fin 3))

  let B :=
    velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot1 (0 : Fin 3) (1 : Fin 3))

  have hSub :=
    MeasureTheory.Lp.coeFn_sub A B

  have hA :
      ((A : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u t (h3JetSlot1 (1 : Fin 3) (0 : Fin 3)) := by
    simpa only [A] using
      (velocityH3L2JetAt_ae_eq_jetField
        hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (0 : Fin 3)))

  have hB :
      ((B : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      velocityH3JetFieldAt
        u t (h3JetSlot1 (0 : Fin 3) (1 : Fin 3)) := by
    simpa only [B] using
      (velocityH3L2JetAt_ae_eq_jetField
        hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (1 : Fin 3)))

  unfold h3BKMPhysicalVorticityZL2
  change ((A - B : H3ScalarL2) : Point3 → ℝ) =ᵐ[volume] _

  filter_upwards [hSub, hA, hB] with x hSubx hAx hBx

  rw [hSubx, Pi.sub_apply, hAx, hBx]

  simp only [
    velocityH3JetFieldAt,
    h3JetSlot1,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rfl

/-- Exact Plancherel image of the physical x-vorticity `L²` package. -/
theorem h3ScalarFourierL2_h3BKMPhysicalVorticityXL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    h3ScalarFourierL2
        (h3BKMPhysicalVorticityXL2 u t hInt hMeas)
      =
    velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (1 : Fin 3))
      -
    velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (2 : Fin 3)) := by

  unfold h3BKMPhysicalVorticityXL2

  simpa [
    velocityH3FourierJetAt,
    h3L2JetFourierApply
  ] using
    h3ScalarFourierL2_sub
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (1 : Fin 3)))
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (2 : Fin 3)))

/-- Exact Plancherel image of the physical y-vorticity `L²` package. -/
theorem h3ScalarFourierL2_h3BKMPhysicalVorticityYL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    h3ScalarFourierL2
        (h3BKMPhysicalVorticityYL2 u t hInt hMeas)
      =
    velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (2 : Fin 3))
      -
    velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (0 : Fin 3)) := by

  unfold h3BKMPhysicalVorticityYL2

  simpa [
    velocityH3FourierJetAt,
    h3L2JetFourierApply
  ] using
    h3ScalarFourierL2_sub
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (2 : Fin 3)))
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (0 : Fin 3)))

/-- Exact Plancherel image of the physical z-vorticity `L²` package. -/
theorem h3ScalarFourierL2_h3BKMPhysicalVorticityZL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    h3ScalarFourierL2
        (h3BKMPhysicalVorticityZL2 u t hInt hMeas)
      =
    velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (0 : Fin 3))
      -
    velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (1 : Fin 3)) := by

  unfold h3BKMPhysicalVorticityZL2

  simpa [
    velocityH3FourierJetAt,
    h3L2JetFourierApply
  ] using
    h3ScalarFourierL2_sub
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (0 : Fin 3)))
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (1 : Fin 3)))

/--
The Fourier transform of physical x-vorticity is `-C12` almost everywhere.
-/
theorem h3BKMPhysicalVorticityXL2_fourier_ae_eq_neg_curl12
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (h3ScalarFourierL2
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun ξ : H3FourierPoint3 =>
      - h3BKMCanonicalCurl12Amplitude
          hInt hMeas ξ := by

  rw [
    h3ScalarFourierL2_h3BKMPhysicalVorticityXL2
      hInt hMeas
  ]

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (1 : Fin 3)))
      (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (2 : Fin 3)))

  have h21 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier
      (2 : Fin 3)
      (1 : Fin 3)

  have h12 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier
      (1 : Fin 3)
      (2 : Fin 3)

  filter_upwards [hSub, h21, h12] with ξ hSubξ h21ξ h12ξ

  rw [hSubξ, Pi.sub_apply, h21ξ, h12ξ]

  unfold
    h3BKMCanonicalCurl12Amplitude
    h3BKMCurl12Amplitude

  ring

/--
The Fourier transform of physical y-vorticity is `C02` almost everywhere.
-/
theorem h3BKMPhysicalVorticityYL2_fourier_ae_eq_curl02
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (h3ScalarFourierL2
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun ξ : H3FourierPoint3 =>
      h3BKMCanonicalCurl02Amplitude
        hInt hMeas ξ := by

  rw [
    h3ScalarFourierL2_h3BKMPhysicalVorticityYL2
      hInt hMeas
  ]

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (2 : Fin 3)))
      (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (0 : Fin 3)))

  have h02 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier
      (0 : Fin 3)
      (2 : Fin 3)

  have h20 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier
      (2 : Fin 3)
      (0 : Fin 3)

  filter_upwards [hSub, h02, h20] with ξ hSubξ h02ξ h20ξ

  rw [hSubξ, Pi.sub_apply, h02ξ, h20ξ]

  unfold
    h3BKMCanonicalCurl02Amplitude
    h3BKMCurl02Amplitude

  ring

/--
The Fourier transform of physical z-vorticity is `-C01` almost everywhere.
-/
theorem h3BKMPhysicalVorticityZL2_fourier_ae_eq_neg_curl01
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (h3ScalarFourierL2
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun ξ : H3FourierPoint3 =>
      - h3BKMCanonicalCurl01Amplitude
          hInt hMeas ξ := by

  rw [
    h3ScalarFourierL2_h3BKMPhysicalVorticityZL2
      hInt hMeas
  ]

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (0 : Fin 3)))
      (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (1 : Fin 3)))

  have h10 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier
      (1 : Fin 3)
      (0 : Fin 3)

  have h01 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier
      (0 : Fin 3)
      (1 : Fin 3)

  filter_upwards [hSub, h10, h01] with ξ hSubξ h10ξ h01ξ

  rw [hSubξ, Pi.sub_apply, h10ξ, h01ξ]

  unfold
    h3BKMCanonicalCurl01Amplitude
    h3BKMCurl01Amplitude

  ring

end

end Euclidean
end Bridge
end PrimeTensor
