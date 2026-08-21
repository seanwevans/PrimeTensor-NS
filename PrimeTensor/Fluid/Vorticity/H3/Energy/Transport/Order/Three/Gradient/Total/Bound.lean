import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Integral

/-!
# Third-order H³ transport: summed gradient-block bound

The twelve `D³u · Du` terms in the third-order commutator have now been
controlled pointwise and integrated for each fixed coordinate tuple.  The
corresponding four-index square-energy majorant sums exactly to `24 * E₃`.

This file combines those two facts:

    |Σ⟨D³u, G₃⟩| ≤ 24 h(t) E₃(t).

The interpolation block is not touched here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeGradientTotalBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The complete four-index sum of the easy third-order gradient-block pairings is
bounded by twenty-four copies of the third-order H³ energy.
-/
theorem thirdOrderGradientTransportSum_le_gradientEnvelope
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hGradPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    ) :
    abs
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
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
                      thirdTransportCommutatorGradientBlock
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u
                        )
                        t i k l j
                    )
        )
      ≤
    24 * h t * velocityH3Energy3At u t := by

  classical

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
          thirdTransportCommutatorGradientBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j
        )

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
    24 * h t * velocityH3Energy3At u t

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

  have hJ :
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
              h t
                *
              thirdOrderGradientMajorantEnergy
                u t i k l j := by

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
      spatialEnergyPairing_thirdTransportCommutatorGradientBlock_le_majorantEnergy
        hGradient
        hH3
        hGradPairing
        i k l j

  have hScaleSum :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                h t
                  *
                thirdOrderGradientMajorantEnergy
                  u t i k l j
      )
        =
      h t
        *
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                thirdOrderGradientMajorantEnergy
                  u t i k l j
      ) := by

    simp only [axis_sum_three]

    ring

  calc
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
              abs (pairing j i k l) :=
      hJ
    _ ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              h t
                *
              thirdOrderGradientMajorantEnergy
                u t i k l j :=
      hPairBound
    _ =
      h t
        *
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                thirdOrderGradientMajorantEnergy
                  u t i k l j
      ) :=
      hScaleSum
    _ =
      h t
        *
      (
        24 * velocityH3Energy3At u t
      ) := by
        rw [
          sum_thirdOrderGradientMajorantEnergy_eq
            u t
        ]
    _ =
      24 * h t * velocityH3Energy3At u t := by
        ring

end Euclidean
end Bridge
end PrimeTensor
