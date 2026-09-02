import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetCocycle

/-!
# Classicalization: first-Fréchet Duhamel right-quotient split

The preceding file differentiated the exact selected Duhamel cocycle once in
space.  For `h > 0` and one fixed coordinate direction `eₐ` it gives

    DₓD(t+h)[eₐ]
      =
    DₓH_hD(t)[eₐ] + DₓDfresh(t,h)[eₐ].

This file performs only the remaining quotient algebra.  Subtract the base
value `DₓD(t)[eₐ]`, multiply by `h⁻¹`, and split the scalar action across the
sum.  The result is

    h⁻¹ • (DₓD(t+h)[eₐ] - DₓD(t)[eₐ])
      =
    h⁻¹ • (DₓH_hD(t)[eₐ] - DₓD(t)[eₐ])
      +
    h⁻¹ • DₓDfresh(t,h)[eₐ].

This is the exact decomposition needed for the genuinely analytic step:

* the first term is the positive-lag heat quotient of the already-existing
  Duhamel spatial derivative;
* the second is the moving-endpoint fresh remainder.

No limit or new estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetRightQuotientSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Exact positive-increment right-quotient decomposition for one canonical
coordinate evaluation of the selected Duhamel first spatial Fréchet
derivative. -/
theorem inv_smul_sub_h3SelectedDuhamel_firstFrechet_coordinate_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a : Fin 3)
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
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    h⁻¹ •
        ((fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν (t + h) hν W W i))
            x) ea
          -
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν t hν W W i))
            x) ea)
      =
    h⁻¹ •
        ((fderiv ℝ
            (h3SelectedDuhamelHistoryHeatRepresentative
              ν A t h hν U₀ hA hU₀ ht i)
            x) ea
          -
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν t hν W W i))
            x) ea)
      +
    h⁻¹ •
        ((fderiv ℝ
            (h3SpectralScalarC1Representative Dfresh)
            x) ea) := by
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

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let Dplus : ℂ :=
    (fderiv ℝ
      (h3SpectralScalarC1Representative
        (h3SpectralFinHeatLerayDuhamel
          ν (t + h) hν W W i))
      x) ea

  let Dbase : ℂ :=
    (fderiv ℝ
      (h3SpectralScalarC1Representative
        (h3SpectralFinHeatLerayDuhamel
          ν t hν W W i))
      x) ea

  let Hplus : ℂ :=
    (fderiv ℝ
      (h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i)
      x) ea

  let Ffresh : ℂ :=
    (fderiv ℝ
      (h3SpectralScalarC1Representative Dfresh)
      x) ea

  have hCocycle :
      Dplus = Hplus + Ffresh := by
    dsimp only [Dplus, Hplus, Ffresh, ea, Dfresh, W]
    exact
      h3SelectedDuhamelC1Representative_add_time_fderiv_coordinate_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh i a x

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
