import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Cocycle

/-!
# Classicalization: third-Fréchet Duhamel right-quotient split

The selected Duhamel cocycle has now been differentiated three times in space:

    D³D(t+h)[e_a,e_b,e_c]
      =
    D³H_hD(t)[e_a,e_b,e_c]
      +
    D³Dfresh(t,h)[e_a,e_b,e_c].

This file performs only the quotient algebra.  Subtract the base third
Fréchet coordinate, scale by `h⁻¹`, and split the scalar action:

    h⁻¹ • (D³D(t+h) - D³D(t))
      =
    h⁻¹ • (D³H_hD(t) - D³D(t))
      +
    h⁻¹ • D³Dfresh(t,h).

The first term is the old-history quotient already identified with the
viscous fifth-derivative trace.  The second is the remaining fresh endpoint.

No limit or new analytic estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetRightQuotientSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Exact positive-increment right-quotient decomposition for one ordered
canonical coordinate of the selected Duhamel third spatial Fréchet
derivative. -/
theorem inv_smul_sub_h3SelectedDuhamel_thirdFrechet_coordinate_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (hthR : t + h ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    let m : Fin 3 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]
    h⁻¹ •
        (iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν (t + h) hν W W i))
            x m
          -
        iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν t hν W W i))
            x m)
      =
    h⁻¹ •
        (iteratedFDeriv ℝ 3
            (h3SelectedDuhamelHistoryHeatRepresentative
              ν A t h hν U₀ hA hU₀ ht i)
            x m
          -
        iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν t hν W W i))
            x m)
      +
    h⁻¹ •
        iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative Dfresh)
          x m := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν
      (fun r => W (r + t))
      (fun r => W (r + t))
      i

  let m : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c)
    ]

  let Dplus : ℂ :=
    iteratedFDeriv ℝ 3
      (h3SpectralScalarC1Representative
        (h3SpectralFinHeatLerayDuhamel
          ν (t + h) hν W W i))
      x m

  let Dbase : ℂ :=
    iteratedFDeriv ℝ 3
      (h3SpectralScalarC1Representative
        (h3SpectralFinHeatLerayDuhamel
          ν t hν W W i))
      x m

  let Hplus : ℂ :=
    iteratedFDeriv ℝ 3
      (h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i)
      x m

  let Ffresh : ℂ :=
    iteratedFDeriv ℝ 3
      (h3SpectralScalarC1Representative Dfresh)
      x m

  have hCocycle :
      Dplus = Hplus + Ffresh := by
    dsimp only [Dplus, Hplus, Ffresh, m, Dfresh, W]
    exact
      h3SelectedDuhamelC1Representative_add_time_thirdFrechet_coordinate_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh hthR i a b c x

  change
    h⁻¹ • (Dplus - Dbase)
      =
    h⁻¹ • (Hplus - Dbase)
      +
    h⁻¹ • Ffresh

  rw [hCocycle]
  simp only [sub_eq_add_neg, smul_add]
  abel

end

end Euclidean
end Bridge
end PrimeTensor
