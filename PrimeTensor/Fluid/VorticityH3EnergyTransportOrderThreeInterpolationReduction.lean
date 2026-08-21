import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationClosure

/-!
# Third-order H³ transport: interpolation reduction

The global interpolation frontier

    |I₃(t)| ≤ C h(t) E₃(t)

is reduced here to a single local analytic obligation for each fixed derivative
tuple `(i,k,l,j)`.

The local block contains exactly the nine `D²u · D²u` commutator monomials
(the three hard terms for each of the three velocity axes).  No transport
algebra remains inside the hypothesis.

For a deliberately simple first interface, each fixed tuple is allowed one
copy of the complete third-order energy:

    |⟨D_i D_k D_l u_j, I₃(i,k,l,j)⟩|
      ≤ K h(t) E₃(t).

There are `3^4 = 81` derivative tuples.  The finite-coordinate bookkeeping
therefore gives the global frontier with constant `81 K`.

This constant is intentionally not optimized.  A later concrete
Gagliardo--Nirenberg proof can sharpen the local majorant without changing the
closure architecture.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeInterpolationReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The local analytic target for one fixed third-derivative coordinate tuple.

The interpolation block here is the exact nine-term hard block already
extracted from the third-order commutator.
-/
def H3OrderThreeInterpolationTupleEstimateAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (t K : ℝ) : Prop :=
  0 ≤ K
    ∧
  ∀ i k l j : PrimeTensor.Axis Depth.three,
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
              thirdTransportCommutatorInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )
        )
      ≤
    K * h t * velocityH3Energy3At u t

/--
The local tuple estimate implies the global interpolation frontier with the
explicit coordinate-count constant `81 * K`.
-/
theorem h3OrderThreeInterpolationEstimateAt_of_tupleEstimate
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t K : ℝ}
    (
      hTuple :
        H3OrderThreeInterpolationTupleEstimateAt
          u h t K
    ) :
    H3OrderThreeInterpolationEstimateAt
      u h t (81 * K) := by

  classical

  refine
    ⟨
      by
        exact mul_nonneg (by norm_num) hTuple.1,
      ?_
    ⟩

  let pairing :
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      ℝ :=
    fun j i k l =>
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
          thirdTransportCommutatorInterpolationBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j
        )

  unfold thirdOrderInterpolationTransportSum

  change
    abs
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  pairing j i k l
        )
      ≤
    (81 * K) * h t * velocityH3Energy3At u t

  have hL :
      ∀ j i k : PrimeTensor.Axis Depth.three,
        abs
            (
              ∑ l : PrimeTensor.Axis Depth.three,
                pairing j i k l
            )
          ≤
        ∑ l : PrimeTensor.Axis Depth.three,
          abs (pairing j i k l) := by

    intro j i k

    simpa only [Real.norm_eq_abs] using
      (
        norm_sum_le
          (Finset.univ :
            Finset (PrimeTensor.Axis Depth.three))
          (fun l => pairing j i k l)
      )

  have hK :
      ∀ j i : PrimeTensor.Axis Depth.three,
        abs
            (
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  pairing j i k l
            )
          ≤
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            abs (pairing j i k l) := by

    intro j i

    have hOuter :
        abs
            (
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  pairing j i k l
            )
          ≤
        ∑ k : PrimeTensor.Axis Depth.three,
          abs
            (
              ∑ l : PrimeTensor.Axis Depth.three,
                pairing j i k l
            ) := by

      simpa only [Real.norm_eq_abs] using
        (
          norm_sum_le
            (Finset.univ :
              Finset (PrimeTensor.Axis Depth.three))
            (
              fun k =>
                ∑ l : PrimeTensor.Axis Depth.three,
                  pairing j i k l
            )
        )

    exact
      le_trans
        hOuter
        (
          Finset.sum_le_sum
            (fun k _ =>
              hL j i k)
        )

  have hI :
      ∀ j : PrimeTensor.Axis Depth.three,
        abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three,
                    pairing j i k l
            )
          ≤
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              abs (pairing j i k l) := by

    intro j

    have hOuter :
        abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three,
                    pairing j i k l
            )
          ≤
        ∑ i : PrimeTensor.Axis Depth.three,
          abs
            (
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  pairing j i k l
            ) := by

      simpa only [Real.norm_eq_abs] using
        (
          norm_sum_le
            (Finset.univ :
              Finset (PrimeTensor.Axis Depth.three))
            (
              fun i =>
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three,
                    pairing j i k l
            )
        )

    exact
      le_trans
        hOuter
        (
          Finset.sum_le_sum
            (fun i _ =>
              hK j i)
        )

  have hTriangle :
      abs
          (
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three,
                    pairing j i k l
          )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              abs (pairing j i k l) := by

    have hOuter :
        abs
            (
              ∑ j : PrimeTensor.Axis Depth.three,
                ∑ i : PrimeTensor.Axis Depth.three,
                  ∑ k : PrimeTensor.Axis Depth.three,
                    ∑ l : PrimeTensor.Axis Depth.three,
                      pairing j i k l
            )
          ≤
        ∑ j : PrimeTensor.Axis Depth.three,
          abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three,
                    pairing j i k l
            ) := by

      simpa only [Real.norm_eq_abs] using
        (
          norm_sum_le
            (Finset.univ :
              Finset (PrimeTensor.Axis Depth.three))
            (
              fun j =>
                ∑ i : PrimeTensor.Axis Depth.three,
                  ∑ k : PrimeTensor.Axis Depth.three,
                    ∑ l : PrimeTensor.Axis Depth.three,
                      pairing j i k l
            )
        )

    exact
      le_trans
        hOuter
        (
          Finset.sum_le_sum
            (fun j _ =>
              hI j)
        )

  have hPairBound :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                abs (pairing j i k l)
      )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              K * h t * velocityH3Energy3At u t := by

    apply Finset.sum_le_sum
    intro j hj

    apply Finset.sum_le_sum
    intro i hi

    apply Finset.sum_le_sum
    intro k hk

    apply Finset.sum_le_sum
    intro l hl

    unfold pairing

    exact
      hTuple.2
        i k l j

  have hCount :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                K * h t * velocityH3Energy3At u t
      )
        =
      (81 * K) * h t * velocityH3Energy3At u t := by

    simp only [axis_sum_three]

    ring

  exact
    le_trans
      hTriangle
      (
        le_trans
          hPairBound
          (
            le_of_eq
              hCount
          )
      )

end Euclidean
end Bridge
end PrimeTensor
