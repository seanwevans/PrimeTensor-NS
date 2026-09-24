import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSqrtEnergyGrowth

/-!
# Exact H³ diffusion magnitude

The H³ path diffusion closure already proves more than nonpositivity.
Every scalar whole-space diffusion pairing satisfies the exact identity

    ⟨f, Δf⟩ = -2 * ∑ᵣ ‖∂ᵣ f‖²₂.

This file packages the positive quantity discarded by the previous
`velocityH3DiffusionDerivativeAt_nonpos` step.

For the four H³ derivative blocks define the corresponding derivative-square
masses, and let `velocityH3DissipationAt` be their sum.  Then the already-closed
whole-space integration-by-parts theorem gives exactly

    velocityH3DiffusionDerivativeAt u t
      = -2 * velocityH3DissipationAt u t.

The highest block is a physical fourth-derivative square mass, so this is the
canonical H⁴-type dissipation magnitude needed for any attempt to absorb the
Riccati-scale transport growth.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PathDiffusionDissipation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Positive dissipation blocks -/

noncomputable def velocityH3Dissipation0At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ r : PrimeTensor.Axis Depth.three,
      spatialSquareEnergy
        (spatial3.d r
          (loggedVelocityComponent u t j))

noncomputable def velocityH3Dissipation1At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ r : PrimeTensor.Axis Depth.three,
        spatialSquareEnergy
          (spatial3.d r
            (spatial3.d i
              (loggedVelocityComponent u t j)))

noncomputable def velocityH3Dissipation2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (spatial3.d r
              (spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j))))

noncomputable def velocityH3Dissipation3At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          ∑ r : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (spatial3.d r
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (loggedVelocityComponent u t j)))))

/-- Full positive H³ viscous dissipation. -/
noncomputable def velocityH3DissipationAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  velocityH3Dissipation0At u t
    + velocityH3Dissipation1At u t
    + velocityH3Dissipation2At u t
    + velocityH3Dissipation3At u t

/-! ## Nonnegativity -/

theorem velocityH3Dissipation0At_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ velocityH3Dissipation0At u t := by
  unfold velocityH3Dissipation0At
  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun r _ =>
            spatialSquareEnergy_nonneg
              (spatial3.d r
                (loggedVelocityComponent u t j))))

theorem velocityH3Dissipation1At_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ velocityH3Dissipation1At u t := by
  unfold velocityH3Dissipation1At
  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun i _ =>
            Finset.sum_nonneg
              (fun r _ =>
                spatialSquareEnergy_nonneg
                  (spatial3.d r
                    (spatial3.d i
                      (loggedVelocityComponent u t j))))))

theorem velocityH3Dissipation2At_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ velocityH3Dissipation2At u t := by
  unfold velocityH3Dissipation2At
  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun i _ =>
            Finset.sum_nonneg
              (fun k _ =>
                Finset.sum_nonneg
                  (fun r _ =>
                    spatialSquareEnergy_nonneg
                      (spatial3.d r
                        (spatial3.d i
                          (spatial3.d k
                            (loggedVelocityComponent u t j))))))))

theorem velocityH3Dissipation3At_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ velocityH3Dissipation3At u t := by
  unfold velocityH3Dissipation3At
  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun i _ =>
            Finset.sum_nonneg
              (fun k _ =>
                Finset.sum_nonneg
                  (fun l _ =>
                    Finset.sum_nonneg
                      (fun r _ =>
                        spatialSquareEnergy_nonneg
                          (spatial3.d r
                            (spatial3.d i
                              (spatial3.d k
                                (spatial3.d l
                                  (loggedVelocityComponent u t j))))))))))

theorem velocityH3DissipationAt_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ velocityH3DissipationAt u t := by
  unfold velocityH3DissipationAt
  have h0 := velocityH3Dissipation0At_nonneg u t
  have h1 := velocityH3Dissipation1At_nonneg u t
  have h2 := velocityH3Dissipation2At_nonneg u t
  have h3 := velocityH3Dissipation3At_nonneg u t
  linarith

/-! ## Exact orderwise diffusion identities -/

theorem velocityH3DiffusionDerivative0At_eq_neg_two_mul_dissipation0
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hIBP : H3DiffusionIntegrationByPartsAt u t) :
    velocityH3DiffusionDerivative0At u t
      =
    -2 * velocityH3Dissipation0At u t := by

  unfold
    velocityH3DiffusionDerivative0At
    velocityH3Dissipation0At

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  exact hIBP.1 j

theorem velocityH3DiffusionDerivative1At_eq_neg_two_mul_dissipation1
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hIBP : H3DiffusionIntegrationByPartsAt u t) :
    velocityH3DiffusionDerivative1At u t
      =
    -2 * velocityH3Dissipation1At u t := by

  unfold
    velocityH3DiffusionDerivative1At
    velocityH3Dissipation1At

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro i hi

  exact hIBP.2.1 i j

theorem velocityH3DiffusionDerivative2At_eq_neg_two_mul_dissipation2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hIBP : H3DiffusionIntegrationByPartsAt u t) :
    velocityH3DiffusionDerivative2At u t
      =
    -2 * velocityH3Dissipation2At u t := by

  unfold
    velocityH3DiffusionDerivative2At
    velocityH3Dissipation2At

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro i hi

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro k hk

  exact hIBP.2.2.1 i k j

theorem velocityH3DiffusionDerivative3At_eq_neg_two_mul_dissipation3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hIBP : H3DiffusionIntegrationByPartsAt u t) :
    velocityH3DiffusionDerivative3At u t
      =
    -2 * velocityH3Dissipation3At u t := by

  unfold
    velocityH3DiffusionDerivative3At
    velocityH3Dissipation3At

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro i hi

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro k hk

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro l hl

  exact hIBP.2.2.2 i k l j

/-- Exact total diffusion identity: no viscous magnitude is discarded. -/
theorem velocityH3DiffusionDerivativeAt_eq_neg_two_mul_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hIBP : H3DiffusionIntegrationByPartsAt u t) :
    velocityH3DiffusionDerivativeAt u t
      =
    -2 * velocityH3DissipationAt u t := by

  have h0 :=
    velocityH3DiffusionDerivative0At_eq_neg_two_mul_dissipation0
      hIBP

  have h1 :=
    velocityH3DiffusionDerivative1At_eq_neg_two_mul_dissipation1
      hIBP

  have h2 :=
    velocityH3DiffusionDerivative2At_eq_neg_two_mul_dissipation2
      hIBP

  have h3 :=
    velocityH3DiffusionDerivative3At_eq_neg_two_mul_dissipation3
      hIBP

  unfold
    velocityH3DiffusionDerivativeAt
    velocityH3DissipationAt

  rw [h0, h1, h2, h3]

  ring

/-! ## Closed H³-path form -/

/-- On every strict H³ energy-class slice, the full diffusion contribution is
exactly minus twice the positive H⁴-type dissipation. -/
theorem h3Path_velocityH3DiffusionDerivativeAt_eq_neg_two_mul_dissipation_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3DiffusionDerivativeAt u t
      =
    -2 * velocityH3DissipationAt u t := by

  exact
    velocityH3DiffusionDerivativeAt_eq_neg_two_mul_dissipation
      (h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
        u T hH3 a hClass t ht)

end

end Euclidean
end Bridge
end PrimeTensor
