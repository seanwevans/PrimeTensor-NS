import PrimeTensor.Fluid.VorticityH3EnergyRegularity

/-!
# The canonical componentwise H³ energy

This file replaces the abstract scalar `E(t)` on the energy side of the BKM
frontier by a concrete finite sum.

For a logged velocity field `v = log u`, define

    E₀(t) = Σ_j       ∫ |v_j|²
    E₁(t) = Σ_{j,i}   ∫ |∂ᵢ v_j|²
    E₂(t) = Σ_{j,i,k} ∫ |∂ᵢ∂ₖ v_j|²
    E₃(t) = Σ_{j,i,k,l} ∫ |∂ᵢ∂ₖ∂ₗ v_j|²

and normalize by

    E_H3(t) = 1 + E₀(t) + E₁(t) + E₂(t) + E₃(t).

The normalization gives `E_H3 ≥ 1`, matching `H3EnergyProfileFrom`.

The main bookkeeping theorem in this file is not an analytic estimate:
assuming only integrability of every squared derivative appearing above,
the total finite sum bounds every individual term.  Hence

    VelocityH3BoundAt u t (velocityH3EnergyAt u t).

This gives the later differentiated PDE estimate one canonical scalar energy
function rather than an existentially chosen envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyFunctional
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- The squared L² energy of one scalar spatial field. -/
noncomputable def spatialSquareEnergy
    (f : ScalarField3) : ℝ :=
  ∫ x : Point3, (f x) ^ 2

theorem spatialSquareEnergy_nonneg
    (f : ScalarField3) :
    0 ≤ spatialSquareEnergy f := by

  unfold spatialSquareEnergy

  exact
    integral_nonneg
      (fun x =>
        sq_nonneg (f x))

/-- Zeroth-order logged-velocity energy. -/
noncomputable def velocityH3Energy0At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    spatialSquareEnergy
      (loggedVelocityComponent u t j)

/-- First-order logged-velocity energy. -/
noncomputable def velocityH3Energy1At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      spatialSquareEnergy
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )

/-- Second-order logged-velocity energy. -/
noncomputable def velocityH3Energy2At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
          )

/-- Third-order logged-velocity energy. -/
noncomputable def velocityH3Energy3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
            )

/--
Canonical normalized componentwise H³ energy.
-/
noncomputable def velocityH3EnergyAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  1
    + velocityH3Energy0At u t
    + velocityH3Energy1At u t
    + velocityH3Energy2At u t
    + velocityH3Energy3At u t

theorem velocityH3Energy0At_nonneg
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    0 ≤ velocityH3Energy0At u t := by

  unfold velocityH3Energy0At

  exact
    Finset.sum_nonneg
      (fun j _ =>
        spatialSquareEnergy_nonneg
          (loggedVelocityComponent u t j))

theorem velocityH3Energy1At_nonneg
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    0 ≤ velocityH3Energy1At u t := by

  unfold velocityH3Energy1At

  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun i _ =>
            spatialSquareEnergy_nonneg
              (
                spatial3.d
                  i
                  (loggedVelocityComponent u t j)
              )))

theorem velocityH3Energy2At_nonneg
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    0 ≤ velocityH3Energy2At u t := by

  unfold velocityH3Energy2At

  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun i _ =>
            Finset.sum_nonneg
              (fun k _ =>
                spatialSquareEnergy_nonneg
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          k
                          (loggedVelocityComponent u t j)
                      )
                  ))))

theorem velocityH3Energy3At_nonneg
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    0 ≤ velocityH3Energy3At u t := by

  unfold velocityH3Energy3At

  exact
    Finset.sum_nonneg
      (fun j _ =>
        Finset.sum_nonneg
          (fun i _ =>
            Finset.sum_nonneg
              (fun k _ =>
                Finset.sum_nonneg
                  (fun l _ =>
                    spatialSquareEnergy_nonneg
                      (
                        spatial3.d
                          i
                          (
                            spatial3.d
                              k
                              (
                                spatial3.d
                                  l
                                  (loggedVelocityComponent u t j)
                              )
                          )
                      )))))

theorem one_le_velocityH3EnergyAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    1 ≤ velocityH3EnergyAt u t := by

  have h0 :=
    velocityH3Energy0At_nonneg u t

  have h1 :=
    velocityH3Energy1At_nonneg u t

  have h2 :=
    velocityH3Energy2At_nonneg u t

  have h3 :=
    velocityH3Energy3At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

/--
Integrability-only version of `SpatialL2SquareBound`.
-/
def SpatialL2SquareIntegrable
    (f : ScalarField3) : Prop :=
  MeasureTheory.Integrable
    (fun x : Point3 => (f x) ^ 2)

/--
Every scalar field entering the componentwise H³ energy is square-integrable.
-/
def VelocityH3IntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ j : PrimeTensor.Axis Depth.three,
    let f :=
      loggedVelocityComponent u t j
    SpatialL2SquareIntegrable f
      ∧
    (
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialL2SquareIntegrable
          (spatial3.d i f)
    )
      ∧
    (
      ∀
        i k : PrimeTensor.Axis Depth.three,
        SpatialL2SquareIntegrable
          (
            spatial3.d
              i
              (spatial3.d k f)
          )
    )
      ∧
    (
      ∀
        i k l : PrimeTensor.Axis Depth.three,
        SpatialL2SquareIntegrable
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (spatial3.d l f)
              )
          )
    )

private theorem order0_le_total
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    spatialSquareEnergy
        (loggedVelocityComponent u t j)
      ≤
    velocityH3EnergyAt u t := by

  have hTerm :
      spatialSquareEnergy
          (loggedVelocityComponent u t j)
        ≤
      velocityH3Energy0At u t := by

    unfold velocityH3Energy0At

    apply
      Finset.single_le_sum
        (fun k _ =>
          spatialSquareEnergy_nonneg
            (loggedVelocityComponent u t k))

    simp

  have h1 :=
    velocityH3Energy1At_nonneg u t

  have h2 :=
    velocityH3Energy2At_nonneg u t

  have h3 :=
    velocityH3Energy3At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

private theorem order1_le_total
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (j i : PrimeTensor.Axis Depth.three) :
    spatialSquareEnergy
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
      ≤
    velocityH3EnergyAt u t := by

  have hInner :
      spatialSquareEnergy
          (
            spatial3.d
              i
              (loggedVelocityComponent u t j)
          )
        ≤
      ∑ k : PrimeTensor.Axis Depth.three,
        spatialSquareEnergy
          (
            spatial3.d
              k
              (loggedVelocityComponent u t j)
          ) := by

    apply
      Finset.single_le_sum
        (fun k _ =>
          spatialSquareEnergy_nonneg
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            ))

    simp

  have hOuter :
      (
        ∑ k : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
      )
        ≤
      velocityH3Energy1At u t := by

    unfold velocityH3Energy1At

    apply
      Finset.single_le_sum
        (fun q _ =>
          Finset.sum_nonneg
            (fun k _ =>
              spatialSquareEnergy_nonneg
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t q)
                )))

    simp

  have h0 :=
    velocityH3Energy0At_nonneg u t

  have h2 :=
    velocityH3Energy2At_nonneg u t

  have h3 :=
    velocityH3Energy3At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

private theorem order2_le_total
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (j i k : PrimeTensor.Axis Depth.three) :
    spatialSquareEnergy
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        )
      ≤
    velocityH3EnergyAt u t := by

  have hK :
      spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
          )
        ≤
      ∑ q : PrimeTensor.Axis Depth.three,
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  q
                  (loggedVelocityComponent u t j)
              )
          ) := by

    apply
      Finset.single_le_sum
        (fun q _ =>
          spatialSquareEnergy_nonneg
            (
              spatial3.d
                i
                (
                  spatial3.d
                    q
                    (loggedVelocityComponent u t j)
                )
            ))

    simp

  have hI :
      (
        ∑ q : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    q
                    (loggedVelocityComponent u t j)
                )
            )
      )
        ≤
      ∑ p : PrimeTensor.Axis Depth.three,
        ∑ q : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                p
                (
                  spatial3.d
                    q
                    (loggedVelocityComponent u t j)
                )
            ) := by

    apply
      Finset.single_le_sum
        (fun p _ =>
          Finset.sum_nonneg
            (fun q _ =>
              spatialSquareEnergy_nonneg
                (
                  spatial3.d
                    p
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )))

    simp

  have hJ :
      (
        ∑ p : PrimeTensor.Axis Depth.three,
          ∑ q : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d
                  p
                  (
                    spatial3.d
                      q
                      (loggedVelocityComponent u t j)
                  )
              )
      )
        ≤
      velocityH3Energy2At u t := by

    unfold velocityH3Energy2At

    apply
      Finset.single_le_sum
        (fun r _ =>
          Finset.sum_nonneg
            (fun p _ =>
              Finset.sum_nonneg
                (fun q _ =>
                  spatialSquareEnergy_nonneg
                    (
                      spatial3.d
                        p
                        (
                          spatial3.d
                            q
                            (loggedVelocityComponent u t r)
                        )
                    ))))

    simp

  have h0 :=
    velocityH3Energy0At_nonneg u t

  have h1 :=
    velocityH3Energy1At_nonneg u t

  have h3 :=
    velocityH3Energy3At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

private theorem order3_le_total
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (
      j i k l :
        PrimeTensor.Axis Depth.three
    ) :
    spatialSquareEnergy
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  spatial3.d
                    l
                    (loggedVelocityComponent u t j)
                )
            )
        )
      ≤
    velocityH3EnergyAt u t := by

  have hL :
      spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      l
                      (loggedVelocityComponent u t j)
                  )
              )
          )
        ≤
      ∑ q : PrimeTensor.Axis Depth.three,
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      q
                      (loggedVelocityComponent u t j)
                  )
              )
          ) := by

    apply
      Finset.single_le_sum
        (fun q _ =>
          spatialSquareEnergy_nonneg
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )
            ))

    simp

  have hK :
      (
        ∑ q : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )
            )
      )
        ≤
      ∑ p : PrimeTensor.Axis Depth.three,
        ∑ q : PrimeTensor.Axis Depth.three,
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    p
                    (
                      spatial3.d
                        q
                        (loggedVelocityComponent u t j)
                    )
                )
            ) := by

    apply
      Finset.single_le_sum
        (fun p _ =>
          Finset.sum_nonneg
            (fun q _ =>
              spatialSquareEnergy_nonneg
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        p
                        (
                          spatial3.d
                            q
                            (loggedVelocityComponent u t j)
                        )
                    )
                )))

    simp

  have hI :
      (
        ∑ p : PrimeTensor.Axis Depth.three,
          ∑ q : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      p
                      (
                        spatial3.d
                          q
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
      )
        ≤
      ∑ r : PrimeTensor.Axis Depth.three,
        ∑ p : PrimeTensor.Axis Depth.three,
          ∑ q : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (
                spatial3.d
                  r
                  (
                    spatial3.d
                      p
                      (
                        spatial3.d
                          q
                          (loggedVelocityComponent u t j)
                      )
                  )
              ) := by

    apply
      Finset.single_le_sum
        (fun r _ =>
          Finset.sum_nonneg
            (fun p _ =>
              Finset.sum_nonneg
                (fun q _ =>
                  spatialSquareEnergy_nonneg
                    (
                      spatial3.d
                        r
                        (
                          spatial3.d
                            p
                            (
                              spatial3.d
                                q
                                (loggedVelocityComponent u t j)
                            )
                        )
                    ))))

    simp

  have hJ :
      (
        ∑ r : PrimeTensor.Axis Depth.three,
          ∑ p : PrimeTensor.Axis Depth.three,
            ∑ q : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (
                  spatial3.d
                    r
                    (
                      spatial3.d
                        p
                        (
                          spatial3.d
                            q
                            (loggedVelocityComponent u t j)
                        )
                    )
                )
      )
        ≤
      velocityH3Energy3At u t := by

    unfold velocityH3Energy3At

    apply
      Finset.single_le_sum
        (fun s _ =>
          Finset.sum_nonneg
            (fun r _ =>
              Finset.sum_nonneg
                (fun p _ =>
                  Finset.sum_nonneg
                    (fun q _ =>
                      spatialSquareEnergy_nonneg
                        (
                          spatial3.d
                            r
                            (
                              spatial3.d
                                p
                                (
                                  spatial3.d
                                    q
                                    (loggedVelocityComponent u t s)
                                )
                            )
                        )))))

    simp

  have h0 :=
    velocityH3Energy0At_nonneg u t

  have h1 :=
    velocityH3Energy1At_nonneg u t

  have h2 :=
    velocityH3Energy2At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

/--
The canonical finite-sum energy bounds every derivative appearing in
`VelocityH3BoundAt`, provided those squared derivatives are integrable.
-/
theorem velocityH3BoundAt_canonical
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (
      hIntegrable :
        VelocityH3IntegrableAt
          u t
    ) :
    VelocityH3BoundAt
      u t
      (velocityH3EnergyAt u t) := by

  unfold VelocityH3BoundAt

  intro j

  dsimp only

  have hInt :=
    hIntegrable j

  rcases hInt with
    ⟨
      h0,
      h1,
      h2,
      h3
    ⟩

  refine
    ⟨
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        h0,
        order0_le_total
          u t j
      ⟩

  · intro i

    exact
      ⟨
        h1 i,
        order1_le_total
          u t j i
      ⟩

  · intro i k

    exact
      ⟨
        h2 i k,
        order2_le_total
          u t j i k
      ⟩

  · intro i k l

    exact
      ⟨
        h3 i k l,
        order3_le_total
          u t j i k l
      ⟩

end Euclidean
end Bridge
end PrimeTensor
