import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationReduction

/-!
# Third-order H³ transport: interpolation monomials

The remaining `D²u · D²u` interpolation block is reduced here to its three
individual monomials for each velocity axis.

For fixed `(i,k,l,j,r)` the axis block is

    (D_k D_l u_r)(D_i D_r u_j)
  + (D_i D_l u_r)(D_k D_r u_j)
  + (D_i D_k u_r)(D_r D_l u_j).

Pairing against `D_i D_k D_l u_j` therefore produces three scalar triple
products.  Across the three velocity axes there are nine such products for a
fixed `(i,k,l,j)` tuple.

This file performs only the exact splitting, integrability bookkeeping, and
finite triangle estimates.  The analytic estimate for one triple product is
left as the next frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeInterpolationMonomials
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- First `D²u · D²u` monomial in one velocity-axis block. -/
noncomputable def thirdOrderInterpolationMonomial1
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    spatial3.d k
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        x
      *
    spatial3.d i
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        x

/-- Second `D²u · D²u` monomial in one velocity-axis block. -/
noncomputable def thirdOrderInterpolationMonomial2
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    spatial3.d i
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        )
        x
      *
    spatial3.d k
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        )
        x

/-- Third `D²u · D²u` monomial in one velocity-axis block. -/
noncomputable def thirdOrderInterpolationMonomial3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    spatial3.d i
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        )
        x
      *
    spatial3.d r
        (
          spatial3.d l
            (loggedVelocityComponent u t j)
        )
        x

/--
The logged interpolation axis block is exactly the sum of the three named
monomials.
-/
theorem thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    thirdTransportCommutatorAxisInterpolationBlock
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            u
        )
        t i k l j r
      =
    fun x : Point3 =>
      thirdOrderInterpolationMonomial1
          u t i k l j r x
        +
      (
        thirdOrderInterpolationMonomial2
            u t i k l j r x
          +
        thirdOrderInterpolationMonomial3
            u t i k l j r x
      ) := by

  funext x

  unfold
    thirdTransportCommutatorAxisInterpolationBlock
    thirdOrderInterpolationMonomial1
    thirdOrderInterpolationMonomial2
    thirdOrderInterpolationMonomial3
    loggedVelocityComponent

  ring

/--
Integrability of every individual triple-product pairing appearing in the hard
third-order interpolation block.
-/
def H3OrderThreeInterpolationMonomialPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ i k l j r : PrimeTensor.Axis Depth.three,
    let f :=
      spatial3.d i
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        )
    MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            thirdOrderInterpolationMonomial1
              u t i k l j r x
        )
      ∧
    MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            thirdOrderInterpolationMonomial2
              u t i k l j r x
        )
      ∧
    MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            thirdOrderInterpolationMonomial3
              u t i k l j r x
        )

/--
A bound for each individual hard triple product.

The constant `K` is the analytic constant for one monomial.  The remainder of
this file shows that the nine monomials in one `(i,k,l,j)` tuple cost at most
`9*K`.
-/
def H3OrderThreeInterpolationMonomialEstimateAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (t K : ℝ) : Prop :=
  0 ≤ K
    ∧
  ∀ i k l j r : PrimeTensor.Axis Depth.three,
    let f :=
      spatial3.d i
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        )
    abs
        (
          spatialEnergyPairing
            f
            (thirdOrderInterpolationMonomial1 u t i k l j r)
        )
      ≤
    K * h t * velocityH3Energy3At u t
      ∧
    abs
        (
          spatialEnergyPairing
            f
            (thirdOrderInterpolationMonomial2 u t i k l j r)
        )
      ≤
    K * h t * velocityH3Energy3At u t
      ∧
    abs
        (
          spatialEnergyPairing
            f
            (thirdOrderInterpolationMonomial3 u t i k l j r)
        )
      ≤
    K * h t * velocityH3Energy3At u t

/--
The monomial integrability package implies integrability of the already-defined
full nine-term interpolation pairing.
-/
theorem h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hInt :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    ) :
    H3OrderThreeInterpolationPairingIntegrableAt
      u t := by

  intro i k l j

  let f : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )

  have axisInt :
      ∀ r : PrimeTensor.Axis Depth.three,
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              f x
                *
              thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j r x
          ) := by

    intro r

    have hr := hInt i k l j r
    dsimp only at hr

    have h1 := hr.1
    have h2 := hr.2.1
    have h3 := hr.2.2

    have h23 :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              f x
                *
              (
                thirdOrderInterpolationMonomial2
                    u t i k l j r x
                  +
                thirdOrderInterpolationMonomial3
                    u t i k l j r x
              )
          ) := by

      simp only [mul_add]

      change
        MeasureTheory.Integrable
          (
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial2
                u t i k l j r x)
              +
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial3
                u t i k l j r x)
          )

      exact h2.add h3

    have h123 :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              f x
                *
              (
                thirdOrderInterpolationMonomial1
                    u t i k l j r x
                  +
                (
                  thirdOrderInterpolationMonomial2
                      u t i k l j r x
                    +
                  thirdOrderInterpolationMonomial3
                      u t i k l j r x
                )
              )
          ) := by

      have hSum := h1.add h23

      have hFun :
          (
            fun x : Point3 =>
              f x
                *
              (
                thirdOrderInterpolationMonomial1
                    u t i k l j r x
                  +
                (
                  thirdOrderInterpolationMonomial2
                      u t i k l j r x
                    +
                  thirdOrderInterpolationMonomial3
                      u t i k l j r x
                )
              )
          )
            =
          (
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial1
                u t i k l j r x)
              +
            (fun x : Point3 =>
              f x
                *
              (
                thirdOrderInterpolationMonomial2
                    u t i k l j r x
                  +
                thirdOrderInterpolationMonomial3
                    u t i k l j r x
              ))
          ) := by

        funext x
        simp only [Pi.add_apply, f, mul_add]

      rw [hFun]

      exact hSum

    rw [
      thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
        u t i k l j r
    ]

    exact h123

  have hX := axisInt xAxis
  have hY := axisInt yAxis
  have hZ := axisInt zAxis

  unfold thirdTransportCommutatorInterpolationBlock

  have hYZ :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
            )
        ) := by

    have hFun :
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
            )
        )
          =
        (
          (fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j yAxis x)
            +
          (fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j zAxis x)
        ) := by

      funext x
      simp only [Pi.add_apply, mul_add]

    rw [hFun]

    exact hY.add hZ

  have hFun :
      (
        fun x : Point3 =>
          spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
            *
          (
            thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j xAxis x
              +
            (
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
            )
          )
      )
        =
      (
        (fun x : Point3 =>
          f x
            *
          thirdTransportCommutatorAxisInterpolationBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j xAxis x)
          +
        (fun x : Point3 =>
          f x
            *
          (
            thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j yAxis x
              +
            thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j zAxis x
          ))
      ) := by

    funext x
    change
      f x
          *
        (
          thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j xAxis x
            +
          (
            thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j yAxis x
              +
            thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j zAxis x
          )
        )
        =
      f x
          *
        thirdTransportCommutatorAxisInterpolationBlock
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i k l j xAxis x
        +
      f x
          *
        (
          thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j yAxis x
            +
          thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j zAxis x
        )

    exact mul_add _ _ _

  rw [hFun]

  exact hX.add hYZ

/--
One velocity-axis interpolation block costs at most three copies of the
single-monomial constant.
-/
theorem thirdOrderInterpolationAxisPairing_le_of_monomialEstimate
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hInt :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    )
    (
      hMono :
        H3OrderThreeInterpolationMonomialEstimateAt
          u h t K
    )
    (i k l j r : PrimeTensor.Axis Depth.three) :
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            (
              thirdTransportCommutatorAxisInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j r
            )
        )
      ≤
    (3 * K) * h t * velocityH3Energy3At u t := by

  let f : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )

  let m1 :=
    thirdOrderInterpolationMonomial1
      u t i k l j r

  let m2 :=
    thirdOrderInterpolationMonomial2
      u t i k l j r

  let m3 :=
    thirdOrderInterpolationMonomial3
      u t i k l j r

  have hIntR := hInt i k l j r
  dsimp only at hIntR

  have h1Int : MeasureTheory.Integrable (fun x : Point3 => f x * m1 x) := by
    simpa only [f, m1] using hIntR.1

  have h2Int : MeasureTheory.Integrable (fun x : Point3 => f x * m2 x) := by
    simpa only [f, m2] using hIntR.2.1

  have h3Int : MeasureTheory.Integrable (fun x : Point3 => f x * m3 x) := by
    simpa only [f, m3] using hIntR.2.2

  have h23Int :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x * (m2 x + m3 x)
        ) := by

    have hFun :
        (fun x : Point3 =>
          f x * (m2 x + m3 x))
          =
        (
          (fun x : Point3 => f x * m2 x)
            +
          (fun x : Point3 => f x * m3 x)
        ) := by

      funext x
      simp only [Pi.add_apply, mul_add]

    rw [hFun]

    exact h2Int.add h3Int

  have hPairSplit23 :
      spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              m2 x + m3 x
          )
        =
      spatialEnergyPairing f m2
        +
      spatialEnergyPairing f m3 := by

    exact
      spatialEnergyPairing_add_of_integrable
        h2Int
        h3Int

  have hPairSplit123 :
      spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              m1 x + (m2 x + m3 x)
          )
        =
      spatialEnergyPairing f m1
        +
      (
        spatialEnergyPairing f m2
          +
        spatialEnergyPairing f m3
      ) := by

    calc
      spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              m1 x + (m2 x + m3 x)
          )
          =
        spatialEnergyPairing f m1
          +
        spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              m2 x + m3 x
          ) := by
            exact
              spatialEnergyPairing_add_of_integrable
                h1Int
                h23Int
      _ =
        spatialEnergyPairing f m1
          +
        (
          spatialEnergyPairing f m2
            +
          spatialEnergyPairing f m3
        ) := by
          rw [hPairSplit23]

  have hMonoR := hMono.2 i k l j r
  dsimp only at hMonoR

  have hb1 := hMonoR.1
  have hb2 := hMonoR.2.1
  have hb3 := hMonoR.2.2

  rw [
    thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
      u t i k l j r
  ]

  change
    abs
        (
          spatialEnergyPairing
            f
            (
              fun x : Point3 =>
                m1 x + (m2 x + m3 x)
            )
        )
      ≤
    (3 * K) * h t * velocityH3Energy3At u t

  rw [hPairSplit123]

  have hTri :
      abs
          (
            spatialEnergyPairing f m1
              +
            (
              spatialEnergyPairing f m2
                +
              spatialEnergyPairing f m3
            )
          )
        ≤
      abs (spatialEnergyPairing f m1)
        +
      (
        abs (spatialEnergyPairing f m2)
          +
        abs (spatialEnergyPairing f m3)
      ) := by

    exact
      le_trans
        (
          abs_add_le
            (spatialEnergyPairing f m1)
            (
              spatialEnergyPairing f m2
                +
              spatialEnergyPairing f m3
            )
        )
        (
          add_le_add_right
            (
              abs_add_le
                (spatialEnergyPairing f m2)
                (spatialEnergyPairing f m3)
            )
            _
        )

  calc
    abs
        (
          spatialEnergyPairing f m1
            +
          (
            spatialEnergyPairing f m2
              +
            spatialEnergyPairing f m3
          )
        )
        ≤
      abs (spatialEnergyPairing f m1)
        +
      (
        abs (spatialEnergyPairing f m2)
          +
        abs (spatialEnergyPairing f m3)
      ) :=
      hTri
    _ ≤
      K * h t * velocityH3Energy3At u t
        +
      (
        K * h t * velocityH3Energy3At u t
          +
        K * h t * velocityH3Energy3At u t
      ) := by
        exact
          add_le_add
            hb1
            (
              add_le_add
                hb2
                hb3
            )
    _ =
      (3 * K) * h t * velocityH3Energy3At u t := by
        ring

/--
The three velocity axes give nine hard monomials for one fixed
`(i,k,l,j)` tuple.
-/
theorem h3OrderThreeInterpolationTupleEstimateAt_of_monomials
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hInt :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    )
    (
      hMono :
        H3OrderThreeInterpolationMonomialEstimateAt
          u h t K
    ) :
    H3OrderThreeInterpolationTupleEstimateAt
      u h t (9 * K) := by

  refine
    ⟨
      mul_nonneg (by norm_num) hMono.1,
      ?_
    ⟩

  intro i k l j

  let f : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )

  let ax : PrimeTensor.Axis Depth.three → ℝ :=
    fun r =>
      spatialEnergyPairing
        f
        (
          thirdTransportCommutatorAxisInterpolationBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j r
        )

  have hX :
      abs (ax xAxis)
        ≤
      (3 * K) * h t * velocityH3Energy3At u t := by
    unfold ax f
    exact
      thirdOrderInterpolationAxisPairing_le_of_monomialEstimate
        hInt hMono i k l j xAxis

  have hY :
      abs (ax yAxis)
        ≤
      (3 * K) * h t * velocityH3Energy3At u t := by
    unfold ax f
    exact
      thirdOrderInterpolationAxisPairing_le_of_monomialEstimate
        hInt hMono i k l j yAxis

  have hZ :
      abs (ax zAxis)
        ≤
      (3 * K) * h t * velocityH3Energy3At u t := by
    unfold ax f
    exact
      thirdOrderInterpolationAxisPairing_le_of_monomialEstimate
        hInt hMono i k l j zAxis

  have hFullInt :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hInt

  have hAxisXInt :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j xAxis x
        ) := by

    have hx := hInt i k l j xAxis
    dsimp only at hx

    rw [
      thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
        u t i k l j xAxis
    ]

    have h23 := hx.2.1.add hx.2.2

    have hFun :
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdOrderInterpolationMonomial1
                  u t i k l j xAxis x
                +
              (
                thirdOrderInterpolationMonomial2
                    u t i k l j xAxis x
                  +
                thirdOrderInterpolationMonomial3
                    u t i k l j xAxis x
              )
            )
        )
          =
        (
          (fun x : Point3 =>
            spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdOrderInterpolationMonomial1
              u t i k l j xAxis x)
            +
          (
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial2
                u t i k l j xAxis x)
              +
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial3
                u t i k l j xAxis x)
          )
        ) := by

      funext x
      simp only [Pi.add_apply, f, mul_add]

    rw [hFun]

    exact hx.1.add h23

  have hAxisYInt :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j yAxis x
        ) := by

    have hy := hInt i k l j yAxis
    dsimp only at hy

    rw [
      thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
        u t i k l j yAxis
    ]

    have h23 := hy.2.1.add hy.2.2

    have hFun :
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdOrderInterpolationMonomial1
                  u t i k l j yAxis x
                +
              (
                thirdOrderInterpolationMonomial2
                    u t i k l j yAxis x
                  +
                thirdOrderInterpolationMonomial3
                    u t i k l j yAxis x
              )
            )
        )
          =
        (
          (fun x : Point3 =>
            spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdOrderInterpolationMonomial1
              u t i k l j yAxis x)
            +
          (
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial2
                u t i k l j yAxis x)
              +
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial3
                u t i k l j yAxis x)
          )
        ) := by

      funext x
      simp only [Pi.add_apply, f, mul_add]

    rw [hFun]

    exact hy.1.add h23

  have hAxisZInt :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j zAxis x
        ) := by

    have hz := hInt i k l j zAxis
    dsimp only at hz

    rw [
      thirdTransportCommutatorAxisInterpolationBlock_logged_eq_monomials
        u t i k l j zAxis
    ]

    have h23 := hz.2.1.add hz.2.2

    have hFun :
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdOrderInterpolationMonomial1
                  u t i k l j zAxis x
                +
              (
                thirdOrderInterpolationMonomial2
                    u t i k l j zAxis x
                  +
                thirdOrderInterpolationMonomial3
                    u t i k l j zAxis x
              )
            )
        )
          =
        (
          (fun x : Point3 =>
            spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdOrderInterpolationMonomial1
              u t i k l j zAxis x)
            +
          (
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial2
                u t i k l j zAxis x)
              +
            (fun x : Point3 =>
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdOrderInterpolationMonomial3
                u t i k l j zAxis x)
          )
        ) := by

      funext x
      simp only [Pi.add_apply, f, mul_add]

    rw [hFun]

    exact hz.1.add h23

  have hYZInt :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
            )
        ) := by

    have hFun :
        (
          fun x : Point3 =>
            f x
              *
            (
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
            )
        )
          =
        (
          (fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j yAxis x)
            +
          (fun x : Point3 =>
            f x
              *
            thirdTransportCommutatorAxisInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j zAxis x)
        ) := by

      funext x
      simp only [Pi.add_apply, mul_add]

    rw [hFun]

    exact hAxisYInt.add hAxisZInt

  have hPairYZ :
      spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
          )
        =
      ax yAxis + ax zAxis := by

    unfold ax

    exact
      spatialEnergyPairing_add_of_integrable
        hAxisYInt
        hAxisZInt

  have hPairXYZ :
      spatialEnergyPairing
          f
          (
            thirdTransportCommutatorInterpolationBlock
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j
          )
        =
      ax xAxis + (ax yAxis + ax zAxis) := by

    unfold thirdTransportCommutatorInterpolationBlock

    calc
      spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j xAxis x
                +
              (
                thirdTransportCommutatorAxisInterpolationBlock
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u
                    )
                    t i k l j yAxis x
                  +
                thirdTransportCommutatorAxisInterpolationBlock
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u
                    )
                    t i k l j zAxis x
              )
          )
          =
        ax xAxis
          +
        spatialEnergyPairing
          f
          (
            fun x : Point3 =>
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j yAxis x
                +
              thirdTransportCommutatorAxisInterpolationBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j zAxis x
          ) := by

            unfold ax

            exact
              spatialEnergyPairing_add_of_integrable
                hAxisXInt
                hYZInt
      _ =
        ax xAxis + (ax yAxis + ax zAxis) := by
          rw [hPairYZ]

  change
    abs
        (
          spatialEnergyPairing
            f
            (
              thirdTransportCommutatorInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )
        )
      ≤
    (9 * K) * h t * velocityH3Energy3At u t

  rw [hPairXYZ]

  have hTri :
      abs
          (
            ax xAxis + (ax yAxis + ax zAxis)
          )
        ≤
      abs (ax xAxis)
        +
      (
        abs (ax yAxis) + abs (ax zAxis)
      ) := by

    exact
      le_trans
        (
          abs_add_le
            (ax xAxis)
            (ax yAxis + ax zAxis)
        )
        (
          add_le_add_right
            (
              abs_add_le
                (ax yAxis)
                (ax zAxis)
            )
            _
        )

  calc
    abs
        (
          ax xAxis + (ax yAxis + ax zAxis)
        )
        ≤
      abs (ax xAxis)
        +
      (
        abs (ax yAxis) + abs (ax zAxis)
      ) :=
      hTri
    _ ≤
      (3 * K) * h t * velocityH3Energy3At u t
        +
      (
        (3 * K) * h t * velocityH3Energy3At u t
          +
        (3 * K) * h t * velocityH3Energy3At u t
      ) := by
        exact
          add_le_add
            hX
            (
              add_le_add
                hY
                hZ
            )
    _ =
      (9 * K) * h t * velocityH3Energy3At u t := by
        ring

/--
The monomial estimate closes the global interpolation frontier with the
explicit, deliberately coarse constant `729*K = 81*9*K`.
-/
theorem h3OrderThreeInterpolationEstimateAt_of_monomials
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hInt :
        H3OrderThreeInterpolationMonomialPairingIntegrableAt
          u t
    )
    (
      hMono :
        H3OrderThreeInterpolationMonomialEstimateAt
          u h t K
    ) :
    H3OrderThreeInterpolationEstimateAt
      u h t (729 * K) := by

  have hTuple :
      H3OrderThreeInterpolationTupleEstimateAt
        u h t (9 * K) :=
    h3OrderThreeInterpolationTupleEstimateAt_of_monomials
      hInt
      hMono

  have hGlobal :=
    h3OrderThreeInterpolationEstimateAt_of_tupleEstimate
      hTuple

  have hCoeff :
      (81 : ℝ) * (9 * K) = 729 * K := by
    ring

  rw [← hCoeff]

  exact hGlobal

end Euclidean
end Bridge
end PrimeTensor
