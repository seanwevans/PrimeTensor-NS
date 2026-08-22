import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FourierDerivativeAE
import PrimeTensor.Fluid.Vorticity.Jet.Third.Continuity

/-!
# Classical H³ regularity implies Fourier jet compatibility

`Sobolev.FourierDerivativeAE` proves the exact first-order a.e. multiplier
identity for one classical PrimeTensor spatial derivative.

This file iterates that theorem through the concrete H³ jet:

* slot `1 (j,i)` is `∂ᵢ uⱼ`;
* slot `2 (j,i,k)` is `∂ᵢ ∂ₖ uⱼ`;
* slot `3 (j,i,k,l)` is `∂ᵢ ∂ₖ ∂ₗ uⱼ`.

The only regularity used to repeat the first-order theorem is spatial `C³` of
the logged velocity component.  The existing H³ integrability/measurability
package supplies the `L²` hypotheses for all concrete jet slots.

Consequently `VelocityH3FourierCompatibleAt` is no longer an independent
analytic assumption under `VelocityLogSpatialC3`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3FourierCompatibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Concrete Fourier jet slots -/

/--
Expose one Fourier jet coordinate directly as the scalar Fourier transform of
its concrete spatial jet field.
-/
@[simp]
theorem velocityH3FourierJetAt_eq_scalarJetField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    velocityH3FourierJetAt u t hInt hMeas a
      =
    h3ScalarFourierL2
      ((velocityH3JetFieldAt_memLp2 hInt hMeas a).toLp
        (velocityH3JetFieldAt u t a)) :=
  rfl


/--
`MemLp.toLp` does not depend on which proof of the same `MemLp` proposition
was supplied.  Keeping this as an explicit bridge prevents proof terms from
leaking into the Fourier-jet identities.
-/
theorem h3ScalarFourierL2_toLp_proof_irrel
    {f : ScalarField3}
    (hf hg : MemLp f 2 volume) :
    h3ScalarFourierL2 (hf.toLp f)
      =
    h3ScalarFourierL2 (hg.toLp f) := by
  have hp : hf = hg := Subsingleton.elim _ _
  subst hg
  rfl

/-! ## Regularity downgrades needed by repeated first derivatives -/

/-- Spatial `C³` is enough for the first-order multiplier theorem. -/
theorem SpatialC3.toSpatialC1
    {f : ScalarField3}
    (hf : SpatialC3 f) :
    SpatialC1 f := by
  unfold SpatialC3 at hf
  unfold SpatialC1
  exact hf.of_le (by norm_num)

/-- A first coordinate derivative of a spatially `C³` field is spatially `C¹`. -/
theorem SpatialC3.firstPartial_spatialC1
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (k : PrimeTensor.Axis Depth.three) :
    SpatialC1 (spatial3.d k f) := by
  have hk2 :
      SpatialC2
        (fun y => partialDeriv k f y) :=
    SpatialC3.partialDeriv_contDiff_two hf k
  change SpatialC1 (fun y => partialDeriv k f y)
  unfold SpatialC1
  unfold SpatialC2 at hk2
  exact hk2.of_le (by norm_num)

/-- An ordered second derivative of a spatially `C³` field is spatially `C¹`. -/
theorem SpatialC3.secondPartial_spatialC1
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (k l : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d k (spatial3.d l f)) := by
  have hl2 :
      SpatialC2
        (fun y => partialDeriv l f y) :=
    SpatialC3.partialDeriv_contDiff_two hf l
  change
    SpatialC1
      (fun y =>
        partialDeriv k
          (fun q => partialDeriv l f q)
          y)
  exact
    SpatialC2.partialDeriv_contDiff_one
      hl2 k

/-! ## Order one -/

/--
The first-derivative Fourier jet slot is the expected single coordinate
multiplier of the base Fourier field.
-/
theorem velocityH3FourierJetAt_orderOne_of_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j i : Fin 3)
    (hfC3 :
      SpatialC3
        (loggedVelocityComponent u t (h3AxisOfFin3 j))) :
    (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 j i) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ =>
      h3FourierDerivativeSymbol i ξ *
        velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot0 j) ξ) := by
  let f : ScalarField3 :=
    loggedVelocityComponent u t (h3AxisOfFin3 j)

  have hfC1 : SpatialC1 f := by
    exact SpatialC3.toSpatialC1 hfC3

  have hf : MemLp f 2 volume := by
    simpa [f, velocityH3JetFieldAt, h3JetSlot0] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot0 j))

  have hdi :
      MemLp
        (spatial3.d (h3AxisOfFin3 i) f)
        2 volume := by
    simpa [f, velocityH3JetFieldAt, h3JetSlot1] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot1 j i))

  have hAE :=
    h3ScalarFourierL2_spatialDerivative_fin_ae
      hfC1 i hf hdi

  have hOut :
      h3ScalarFourierL2
          (hdi.toLp
            (spatial3.d (h3AxisOfFin3 i) f))
        =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 j i) := by
    rw [velocityH3FourierJetAt_eq_scalarJetField]
    simpa [
      f,
      velocityH3JetFieldAt,
      h3JetSlot1
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hdi
        (by
          simpa [
            f,
            velocityH3JetFieldAt,
            h3JetSlot1
          ] using
            (velocityH3JetFieldAt_memLp2
              hInt hMeas (h3JetSlot1 j i))))

  have hBase :
      h3ScalarFourierL2 (hf.toLp f)
        =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot0 j) := by
    rw [velocityH3FourierJetAt_eq_scalarJetField]
    simpa [
      f,
      velocityH3JetFieldAt,
      h3JetSlot0
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hf
        (by
          simpa [
            f,
            velocityH3JetFieldAt,
            h3JetSlot0
          ] using
            (velocityH3JetFieldAt_memLp2
              hInt hMeas (h3JetSlot0 j))))

  rw [← hOut, ← hBase]
  exact hAE

/-! ## Order two -/

/--
The ordered second-derivative Fourier jet slot is the product of the two
coordinate symbols times the base Fourier field.
-/
theorem velocityH3FourierJetAt_orderTwo_of_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j i k : Fin 3)
    (hfC3 :
      SpatialC3
        (loggedVelocityComponent u t (h3AxisOfFin3 j))) :
    (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot2 j i k) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ =>
      h3FourierDerivativeSymbol2 i k ξ *
        velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot0 j) ξ) := by
  let f : ScalarField3 :=
    loggedVelocityComponent u t (h3AxisOfFin3 j)

  have hkC1 :
      SpatialC1
        (spatial3.d (h3AxisOfFin3 k) f) := by
    exact
      SpatialC3.firstPartial_spatialC1
        hfC3 (h3AxisOfFin3 k)

  have hk :
      MemLp
        (spatial3.d (h3AxisOfFin3 k) f)
        2 volume := by
    simpa [f, velocityH3JetFieldAt, h3JetSlot1] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot1 j k))

  have hik :
      MemLp
        (spatial3.d
          (h3AxisOfFin3 i)
          (spatial3.d (h3AxisOfFin3 k) f))
        2 volume := by
    simpa [f, velocityH3JetFieldAt, h3JetSlot2] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot2 j i k))

  have hStepRaw :=
    h3ScalarFourierL2_spatialDerivative_fin_ae
      hkC1 i hk hik

  have hStepOut :
      h3ScalarFourierL2
          (hik.toLp
            (spatial3.d
              (h3AxisOfFin3 i)
              (spatial3.d (h3AxisOfFin3 k) f)))
        =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot2 j i k) := by
    rw [velocityH3FourierJetAt_eq_scalarJetField]
    simpa [
      f,
      velocityH3JetFieldAt,
      h3JetSlot2
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hik
        (by
          simpa [
            f,
            velocityH3JetFieldAt,
            h3JetSlot2
          ] using
            (velocityH3JetFieldAt_memLp2
              hInt hMeas (h3JetSlot2 j i k))))

  have hStepBase :
      h3ScalarFourierL2
          (hk.toLp
            (spatial3.d (h3AxisOfFin3 k) f))
        =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 j k) := by
    rw [velocityH3FourierJetAt_eq_scalarJetField]
    simpa [
      f,
      velocityH3JetFieldAt,
      h3JetSlot1
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hk
        (by
          simpa [
            f,
            velocityH3JetFieldAt,
            h3JetSlot1
          ] using
            (velocityH3JetFieldAt_memLp2
              hInt hMeas (h3JetSlot1 j k))))

  have hStep :
      (velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot2 j i k) : H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      (fun ξ =>
        h3FourierDerivativeSymbol i ξ *
          velocityH3FourierJetAt u t hInt hMeas
            (h3JetSlot1 j k) ξ) := by
    rw [← hStepOut, ← hStepBase]
    exact hStepRaw

  have hFirst :=
    velocityH3FourierJetAt_orderOne_of_spatialC3
      hInt hMeas j k hfC3

  filter_upwards [hStep, hFirst] with ξ hStepξ hFirstξ
  rw [hStepξ, hFirstξ]
  simp [h3FourierDerivativeSymbol2, mul_assoc]

/-! ## Order three -/

/--
The ordered third-derivative Fourier jet slot is the product of the three
coordinate symbols times the base Fourier field.
-/
theorem velocityH3FourierJetAt_orderThree_of_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j i k l : Fin 3)
    (hfC3 :
      SpatialC3
        (loggedVelocityComponent u t (h3AxisOfFin3 j))) :
    (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot3 j i k l) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ =>
      h3FourierDerivativeSymbol3 i k l ξ *
        velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot0 j) ξ) := by
  let f : ScalarField3 :=
    loggedVelocityComponent u t (h3AxisOfFin3 j)

  have hklC1 :
      SpatialC1
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d (h3AxisOfFin3 l) f)) := by
    exact
      SpatialC3.secondPartial_spatialC1
        hfC3
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 l)

  have hkl :
      MemLp
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d (h3AxisOfFin3 l) f))
        2 volume := by
    simpa [f, velocityH3JetFieldAt, h3JetSlot2] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot2 j k l))

  have hikl :
      MemLp
        (spatial3.d
          (h3AxisOfFin3 i)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d (h3AxisOfFin3 l) f)))
        2 volume := by
    simpa [f, velocityH3JetFieldAt, h3JetSlot3] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas (h3JetSlot3 j i k l))

  have hStepRaw :=
    h3ScalarFourierL2_spatialDerivative_fin_ae
      hklC1 i hkl hikl

  have hStepOut :
      h3ScalarFourierL2
          (hikl.toLp
            (spatial3.d
              (h3AxisOfFin3 i)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d (h3AxisOfFin3 l) f))))
        =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot3 j i k l) := by
    rw [velocityH3FourierJetAt_eq_scalarJetField]
    simpa [
      f,
      velocityH3JetFieldAt,
      h3JetSlot3
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hikl
        (by
          simpa [
            f,
            velocityH3JetFieldAt,
            h3JetSlot3
          ] using
            (velocityH3JetFieldAt_memLp2
              hInt hMeas (h3JetSlot3 j i k l))))

  have hStepBase :
      h3ScalarFourierL2
          (hkl.toLp
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d (h3AxisOfFin3 l) f)))
        =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot2 j k l) := by
    rw [velocityH3FourierJetAt_eq_scalarJetField]
    simpa [
      f,
      velocityH3JetFieldAt,
      h3JetSlot2
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hkl
        (by
          simpa [
            f,
            velocityH3JetFieldAt,
            h3JetSlot2
          ] using
            (velocityH3JetFieldAt_memLp2
              hInt hMeas (h3JetSlot2 j k l))))

  have hStep :
      (velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot3 j i k l) : H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      (fun ξ =>
        h3FourierDerivativeSymbol i ξ *
          velocityH3FourierJetAt u t hInt hMeas
            (h3JetSlot2 j k l) ξ) := by
    rw [← hStepOut, ← hStepBase]
    exact hStepRaw

  have hSecond :=
    velocityH3FourierJetAt_orderTwo_of_spatialC3
      hInt hMeas j k l hfC3

  filter_upwards [hStep, hSecond] with ξ hStepξ hSecondξ
  rw [hStepξ, hSecondξ]
  simp [
    h3FourierDerivativeSymbol2,
    h3FourierDerivativeSymbol3,
    mul_assoc
  ]

/-! ## Full compatibility -/

/--
Per-snapshot spatial `C³` regularity of every logged component implies the
complete first/second/third-order Fourier compatibility predicate.
-/
theorem velocityH3FourierCompatibleAt_of_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hSpatial :
      ∀ j : PrimeTensor.Axis Depth.three,
        SpatialC3 (loggedVelocityComponent u t j))
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    VelocityH3FourierCompatibleAt u t hInt hMeas := by
  intro j

  have hjC3 :
      SpatialC3
        (loggedVelocityComponent u t (h3AxisOfFin3 j)) :=
    hSpatial (h3AxisOfFin3 j)

  constructor
  · intro i
    exact
      velocityH3FourierJetAt_orderOne_of_spatialC3
        hInt hMeas j i hjC3
  constructor
  · intro i k
    exact
      velocityH3FourierJetAt_orderTwo_of_spatialC3
        hInt hMeas j i k hjC3
  · intro i k l
    exact
      velocityH3FourierJetAt_orderThree_of_spatialC3
        hInt hMeas j i k l hjC3

/--
The project-level spatial `C³` predicate for the logged velocity implies
`VelocityH3FourierCompatibleAt` at every H³-integrable measurable snapshot.
-/
theorem velocityH3FourierCompatibleAt_of_velocityLogSpatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hSpatial : VelocityLogSpatialC3 u)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    VelocityH3FourierCompatibleAt u t hInt hMeas := by
  apply
    velocityH3FourierCompatibleAt_of_spatialC3
      (u := u) (t := t)
      (hInt := hInt) (hMeas := hMeas)

  intro j
  change
    SpatialC3
      (fun y =>
        (logSpaceTimeVectorField u t y).component j)
  exact hSpatial t j

end

end Euclidean
end Bridge
end PrimeTensor
