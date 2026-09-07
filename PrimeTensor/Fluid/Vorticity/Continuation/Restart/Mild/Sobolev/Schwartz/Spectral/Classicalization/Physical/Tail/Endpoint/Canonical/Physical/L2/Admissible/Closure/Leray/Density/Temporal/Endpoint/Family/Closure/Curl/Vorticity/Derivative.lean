import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Pairing
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Pressure-free pointwise temporal derivatives of the preterminal vorticity

The previous increment identified the three compact curl-test velocity pairings
with the classical vorticity pairings.

This file records the corresponding time-side pointwise fact in the strongest
form useful for the forthcoming measurability/Fubini argument.

For each fixed spatial point, each classical vorticity component has a genuine
`HasDerivAt` witness on the open preterminal interval, and its derivative is
the pressure-free vorticity RHS:

    ∂ₜ ω_x = stretch_x + Δω_x - transport_x
    ∂ₜ ω_y = stretch_y + Δω_y - transport_y
    ∂ₜ ω_z = stretch_z + Δω_z - transport_z.

The proof does not recover a derivative from the total `deriv` operator.  It
subtracts the two existing mixed spatial/time `HasDerivAt` witnesses and then
uses the already-proved preterminal vorticity equation to identify the
coefficient.

We also expose measurability in time of the actual scalar vorticity derivative.
Mathlib's `measurable_deriv` applies because, at a fixed spatial point, this is
an ordinary real derivative.  This is one half of the Carathéodory route toward
joint spacetime measurability; the other half will be spatial continuity from
the pressure-free RHS.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Pressure-free x-vorticity RHS for the logged old solution. -/
noncomputable def h3LoggedPreterminalVorticityRHSX
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (x : Point3) : ℝ :=
  realVortexStretchComponent
      (logSpaceTimeVectorField u) s x xAxis
    +
  PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (fun y : Point3 =>
        realVorticityX
          (logSpaceTimeVectorField u) s y)
      x
    -
  realVorticityTransportX
    (logSpaceTimeVectorField u) s x

/-- Pressure-free y-vorticity RHS for the logged old solution. -/
noncomputable def h3LoggedPreterminalVorticityRHSY
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (x : Point3) : ℝ :=
  realVortexStretchComponent
      (logSpaceTimeVectorField u) s x yAxis
    +
  PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (fun y : Point3 =>
        realVorticityY
          (logSpaceTimeVectorField u) s y)
      x
    -
  realVorticityTransportY
    (logSpaceTimeVectorField u) s x

/-- Pressure-free z-vorticity RHS for the logged old solution. -/
noncomputable def h3LoggedPreterminalVorticityRHSZ
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (x : Point3) : ℝ :=
  realVortexStretchComponent
      (logSpaceTimeVectorField u) s x zAxis
    +
  PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (fun y : Point3 =>
        realVorticityZ
          (logSpaceTimeVectorField u) s y)
      x
    -
  realVorticityTransportZ
    (logSpaceTimeVectorField u) s x

/-- At every strict preterminal time, the x-vorticity trajectory at a fixed
spatial point has the pressure-free vorticity RHS as its genuine derivative. -/
theorem h3LoggedPreterminalVorticityX_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        realVorticityX
          (logSpaceTimeVectorField u) r x)
      (h3LoggedPreterminalVorticityRHSX u s x)
      s := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hy :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x yAxis zAxis

  have hz :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x zAxis yAxis

  have hCross := hy.sub hz

  have hVorticity :
      HasDerivAt
        (fun r : ℝ =>
          realVorticityX
            (logSpaceTimeVectorField u) r x)
        (spatial3.d
            yAxis
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component zAxis)
                s)
            x
          -
         spatial3.d
            zAxis
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component yAxis)
                s)
            x)
        s := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hSlope := hCross.tendsto_slope_zero
    simpa only [
      realVorticityX,
      Pi.sub_apply,
      smul_eq_mul
    ] using hSlope

  have hTemporal :=
    hPDE.temporal_realVorticityX hs x

  rw [← hTemporal] at hVorticity

  have hEquation :=
    hPDE.vorticityEquationX hs x

  have hRHS :
      temporal.d
          (fun r : ℝ =>
            realVorticityX
              (logSpaceTimeVectorField u) r x)
          s
        =
      h3LoggedPreterminalVorticityRHSX u s x := by
    unfold h3LoggedPreterminalVorticityRHSX
    linarith

  rw [hRHS] at hVorticity
  exact hVorticity

/-- The y-vorticity trajectory has the pressure-free vorticity RHS as its
genuine derivative. -/
theorem h3LoggedPreterminalVorticityY_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        realVorticityY
          (logSpaceTimeVectorField u) r x)
      (h3LoggedPreterminalVorticityRHSY u s x)
      s := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hz :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x zAxis xAxis

  have hx :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x xAxis zAxis

  have hCross := hz.sub hx

  have hVorticity :
      HasDerivAt
        (fun r : ℝ =>
          realVorticityY
            (logSpaceTimeVectorField u) r x)
        (spatial3.d
            zAxis
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component xAxis)
                s)
            x
          -
         spatial3.d
            xAxis
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component zAxis)
                s)
            x)
        s := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hSlope := hCross.tendsto_slope_zero
    simpa only [
      realVorticityY,
      Pi.sub_apply,
      smul_eq_mul
    ] using hSlope

  have hTemporal :=
    hPDE.temporal_realVorticityY hs x

  rw [← hTemporal] at hVorticity

  have hEquation :=
    hPDE.vorticityEquationY hs x

  have hRHS :
      temporal.d
          (fun r : ℝ =>
            realVorticityY
              (logSpaceTimeVectorField u) r x)
          s
        =
      h3LoggedPreterminalVorticityRHSY u s x := by
    unfold h3LoggedPreterminalVorticityRHSY
    linarith

  rw [hRHS] at hVorticity
  exact hVorticity

/-- The z-vorticity trajectory has the pressure-free vorticity RHS as its
genuine derivative. -/
theorem h3LoggedPreterminalVorticityZ_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        realVorticityZ
          (logSpaceTimeVectorField u) r x)
      (h3LoggedPreterminalVorticityRHSZ u s x)
      s := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hx :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x xAxis yAxis

  have hy :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x yAxis xAxis

  have hCross := hx.sub hy

  have hVorticity :
      HasDerivAt
        (fun r : ℝ =>
          realVorticityZ
            (logSpaceTimeVectorField u) r x)
        (spatial3.d
            xAxis
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component yAxis)
                s)
            x
          -
         spatial3.d
            yAxis
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component xAxis)
                s)
            x)
        s := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hSlope := hCross.tendsto_slope_zero
    simpa only [
      realVorticityZ,
      Pi.sub_apply,
      smul_eq_mul
    ] using hSlope

  have hTemporal :=
    hPDE.temporal_realVorticityZ hs x

  rw [← hTemporal] at hVorticity

  have hEquation :=
    hPDE.vorticityEquationZ hs x

  have hRHS :
      temporal.d
          (fun r : ℝ =>
            realVorticityZ
              (logSpaceTimeVectorField u) r x)
          s
        =
      h3LoggedPreterminalVorticityRHSZ u s x := by
    unfold h3LoggedPreterminalVorticityRHSZ
    linarith

  rw [hRHS] at hVorticity
  exact hVorticity

/-- Elapsed-time form of the x-vorticity derivative. -/
theorem h3LoggedPreterminalVorticityX_elapsed_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        realVorticityX
          (logSpaceTimeVectorField u) (t + r) x)
      (h3LoggedPreterminalVorticityRHSX u (t + s) x)
      s := by
  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd
      ⟨s, ⟨hs.1.le, hs.2.le⟩⟩

  have hBase :=
    h3LoggedPreterminalVorticityX_hasDerivAt
      hNS hAbs x

  have hShift :
      HasDerivAt
        (fun r : ℝ => t + r)
        1
        s := by
    simpa only [id_eq] using
      (hasDerivAt_id s).const_add t

  have hComp := hBase.comp s hShift
  simpa only [Function.comp_def, mul_one] using hComp

/-- Elapsed-time form of the y-vorticity derivative. -/
theorem h3LoggedPreterminalVorticityY_elapsed_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        realVorticityY
          (logSpaceTimeVectorField u) (t + r) x)
      (h3LoggedPreterminalVorticityRHSY u (t + s) x)
      s := by
  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd
      ⟨s, ⟨hs.1.le, hs.2.le⟩⟩

  have hBase :=
    h3LoggedPreterminalVorticityY_hasDerivAt
      hNS hAbs x

  have hShift :
      HasDerivAt
        (fun r : ℝ => t + r)
        1
        s := by
    simpa only [id_eq] using
      (hasDerivAt_id s).const_add t

  have hComp := hBase.comp s hShift
  simpa only [Function.comp_def, mul_one] using hComp

/-- Elapsed-time form of the z-vorticity derivative. -/
theorem h3LoggedPreterminalVorticityZ_elapsed_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        realVorticityZ
          (logSpaceTimeVectorField u) (t + r) x)
      (h3LoggedPreterminalVorticityRHSZ u (t + s) x)
      s := by
  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd
      ⟨s, ⟨hs.1.le, hs.2.le⟩⟩

  have hBase :=
    h3LoggedPreterminalVorticityZ_hasDerivAt
      hNS hAbs x

  have hShift :
      HasDerivAt
        (fun r : ℝ => t + r)
        1
        s := by
    simpa only [id_eq] using
      (hasDerivAt_id s).const_add t

  have hComp := hBase.comp s hShift
  simpa only [Function.comp_def, mul_one] using hComp

/-- At a fixed spatial point, the actual x-vorticity temporal derivative is a
measurable scalar function of absolute time. -/
theorem measurable_h3LoggedPreterminalVorticityX_temporalDerivative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (x : Point3) :
    Measurable
      (fun s : ℝ =>
        temporal.d
          (fun r : ℝ =>
            realVorticityX
              (logSpaceTimeVectorField u) r x)
          s) := by
  simpa only [temporal_d] using
    measurable_deriv
      (fun r : ℝ =>
        realVorticityX
          (logSpaceTimeVectorField u) r x)

/-- At a fixed spatial point, the actual y-vorticity temporal derivative is
measurable in absolute time. -/
theorem measurable_h3LoggedPreterminalVorticityY_temporalDerivative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (x : Point3) :
    Measurable
      (fun s : ℝ =>
        temporal.d
          (fun r : ℝ =>
            realVorticityY
              (logSpaceTimeVectorField u) r x)
          s) := by
  simpa only [temporal_d] using
    measurable_deriv
      (fun r : ℝ =>
        realVorticityY
          (logSpaceTimeVectorField u) r x)

/-- At a fixed spatial point, the actual z-vorticity temporal derivative is
measurable in absolute time. -/
theorem measurable_h3LoggedPreterminalVorticityZ_temporalDerivative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (x : Point3) :
    Measurable
      (fun s : ℝ =>
        temporal.d
          (fun r : ℝ =>
            realVorticityZ
              (logSpaceTimeVectorField u) r x)
          s) := by
  simpa only [temporal_d] using
    measurable_deriv
      (fun r : ℝ =>
        realVorticityZ
          (logSpaceTimeVectorField u) r x)

end

end Euclidean
end Bridge
end PrimeTensor
