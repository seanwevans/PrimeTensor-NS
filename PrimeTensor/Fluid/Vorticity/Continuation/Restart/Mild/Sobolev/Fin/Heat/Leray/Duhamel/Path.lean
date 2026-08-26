import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Continuity

/-!
# Normalized H³ path packaging for the Fin-indexed heat--Leray Duhamel map

The physical-time Duhamel map is now known to be continuous on `ℝ≥0`.
For a physical lifespan `τ ≥ 0`, normalized time `s ∈ [0,1]` is sent to
physical time `τ s` by `h3PhysicalTimeNN`.

This file packages

    s ↦ D(τ s)

as an actual `H3SpectralVelocityPath`.

The pointwise Duhamel estimate gives a uniform path bound of order `sqrt τ`.
We use the absolute value of the scalar coefficient at this interface, making
nonnegativity immediate and avoiding any extra positivity bookkeeping for the
Sobolev deweighting constant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Manifestly nonnegative path coefficient -/

/--
A manifestly nonnegative version of the heat--Leray Duhamel coefficient.
-/
def h3HeatLerayDuhamelPathCoefficient
    (ν : ℝ) : ℝ :=
  |h3HeatLerayDuhamelCoefficient ν|

theorem h3HeatLerayDuhamelPathCoefficient_nonneg
    (ν : ℝ) :
    0 ≤ h3HeatLerayDuhamelPathCoefficient ν := by
  exact abs_nonneg _

/-! ## Pointwise physical-time bound -/

/--
For globally continuous bounded real-time inputs, the Duhamel value at any
nonnegative physical time obeys the usual square-root estimate with a
manifestly nonnegative coefficient.
-/
theorem norm_h3SpectralFinHeatLerayDuhamel_le_pathCoefficient
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    ‖h3SpectralFinHeatLerayDuhamel
        ν t hν U V‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt t * MU * MV := by
  have hUint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU := by
    intro s _hs
    exact hU s

  have hVint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV := by
    intro s _hs
    exact hV s

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht hMU hMV U V
      hUcont hVcont hUint hVint

  have hBase :=
    norm_h3SpectralFinHeatLerayDuhamel_le
      hν ht hMU hMV U V
      hInt hUint hVint

  calc
    ‖h3SpectralFinHeatLerayDuhamel
        ν t hν U V‖
        ≤
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt t * MU * MV :=
      hBase
    _ ≤
      |h3HeatLerayDuhamelCoefficient ν| *
        Real.sqrt t * MU * MV := by
          have h0 :
              0 ≤ Real.sqrt t :=
            Real.sqrt_nonneg t
          have h1 :
              h3HeatLerayDuhamelCoefficient ν *
                  Real.sqrt t
                ≤
              |h3HeatLerayDuhamelCoefficient ν| *
                  Real.sqrt t :=
            mul_le_mul_of_nonneg_right
              (le_abs_self
                (h3HeatLerayDuhamelCoefficient ν))
              h0
          have h2 :
              (h3HeatLerayDuhamelCoefficient ν *
                  Real.sqrt t) * MU
                ≤
              (|h3HeatLerayDuhamelCoefficient ν| *
                  Real.sqrt t) * MU :=
            mul_le_mul_of_nonneg_right h1 hMU
          exact
            mul_le_mul_of_nonneg_right h2 hMV
    _ =
      h3HeatLerayDuhamelPathCoefficient ν *
        Real.sqrt t * MU * MV := by
          rfl


/-! ## Uniform bound along normalized physical time -/

/--
At normalized time `s ∈ [0,1]`, physical time is at most `τ`, so the
pointwise Duhamel estimate is uniformly controlled by `sqrt τ`.
-/
theorem norm_h3SpectralFinHeatLerayDuhamel_physicalTime_le
    {ν τ MU MV : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (s : H3UnitTime) :
    ‖h3SpectralFinHeatLerayDuhamel
        ν
        (h3PhysicalTimeNN τ hτ s : ℝ)
        hν U V‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * MU * MV := by
  have ht :
      0 ≤ (h3PhysicalTimeNN τ hτ s : ℝ) :=
    (h3PhysicalTimeNN τ hτ s).property

  have ht_le :
      (h3PhysicalTimeNN τ hτ s : ℝ) ≤ τ := by
    exact
      (h3PhysicalTime_mem_Icc hτ s).2

  have hpoint :=
    norm_h3SpectralFinHeatLerayDuhamel_le_pathCoefficient
      hν ht hMU hMV U V
      hUcont hVcont hU hV

  have hsqrt :
      Real.sqrt
          (h3PhysicalTimeNN τ hτ s : ℝ)
        ≤
      Real.sqrt τ :=
    Real.sqrt_le_sqrt ht_le

  have h1 :
      h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt
            (h3PhysicalTimeNN τ hτ s : ℝ)
        ≤
      h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt τ :=
    mul_le_mul_of_nonneg_left
      hsqrt
      (h3HeatLerayDuhamelPathCoefficient_nonneg ν)

  have h2 :
      (h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt
            (h3PhysicalTimeNN τ hτ s : ℝ)) * MU
        ≤
      (h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt τ) * MU :=
    mul_le_mul_of_nonneg_right h1 hMU

  have h3 :
      ((h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt
            (h3PhysicalTimeNN τ hτ s : ℝ)) * MU) * MV
        ≤
      ((h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt τ) * MU) * MV :=
    mul_le_mul_of_nonneg_right h2 hMV

  exact le_trans hpoint h3

/-! ## Normalized path constructor -/

/--
The physical-time heat--Leray Duhamel map restricted to the normalized
interval `s ∈ [0,1]`, with physical target time `τ s`.
-/
noncomputable def h3SpectralFinHeatLerayDuhamelPath
    {ν τ MU MV : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    H3SpectralVelocityPath :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : H3UnitTime =>
      h3SpectralFinHeatLerayDuhamel
        ν
        (h3PhysicalTimeNN τ hτ s : ℝ)
        hν U V)
    ((continuous_h3SpectralFinHeatLerayDuhamel_nnreal
        hν hMU hMV U V
        hUcont hVcont hU hV).comp
      (continuous_h3PhysicalTimeNN τ hτ))
    (h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * MU * MV)
    (fun s =>
      norm_h3SpectralFinHeatLerayDuhamel_physicalTime_le
        hν hτ hMU hMV U V
        hUcont hVcont hU hV s)

@[simp]
theorem h3SpectralFinHeatLerayDuhamelPath_apply
    {ν τ MU MV : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (s : H3UnitTime) :
    h3SpectralFinHeatLerayDuhamelPath
        hν hτ hMU hMV U V
        hUcont hVcont hU hV s
      =
    h3SpectralFinHeatLerayDuhamel
      ν
      (h3PhysicalTimeNN τ hτ s : ℝ)
      hν U V :=
  rfl

/--
Uniform normalized-path estimate.  The nonlinear path has the expected
`sqrt τ` gain.
-/
theorem norm_h3SpectralFinHeatLerayDuhamelPath_le
    {ν τ MU MV : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    ‖h3SpectralFinHeatLerayDuhamelPath
        hν hτ hMU hMV U V
        hUcont hVcont hU hV‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * MU * MV := by
  apply
    (BoundedContinuousFunction.norm_le
      (f :=
        h3SpectralFinHeatLerayDuhamelPath
          hν hτ hMU hMV U V
          hUcont hVcont hU hV)
      (by
        exact
          mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (h3HeatLerayDuhamelPathCoefficient_nonneg ν)
                (Real.sqrt_nonneg τ))
              hMU)
            hMV)).2
  intro s
  change
    ‖h3SpectralFinHeatLerayDuhamel
        ν
        (h3PhysicalTimeNN τ hτ s : ℝ)
        hν U V‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * MU * MV
  exact
    norm_h3SpectralFinHeatLerayDuhamel_physicalTime_le
      hν hτ hMU hMV U V
      hUcont hVcont hU hV s

end

end Euclidean
end Bridge
end PrimeTensor
