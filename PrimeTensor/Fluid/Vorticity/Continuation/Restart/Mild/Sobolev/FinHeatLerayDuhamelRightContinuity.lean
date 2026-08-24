import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayDuhamelTail

/-!
# Right continuity of the Fin-indexed H³ Duhamel map

The previous two rungs established

* the exact restart identity
    `D(a+b) = H_b D(a) + tail(a,b)`;
* the quantitative estimate
    `‖tail(a,b)‖ ≤ Cν sqrt(b) MU MV`.

For globally continuous bounded real-time input paths, all integrability
hypotheses in the restart theorem are automatic.  This file packages that
fact and proves continuity in the nonnegative restart increment

    b ↦ D(t+b),    b : ℝ≥0,

at `b = 0`.

The proof has no moving-singularity dominated convergence:

1. the heat term is strongly continuous in `b`;
2. the restart tail tends to zero by `squeeze_zero_norm'`;
3. the `b = 0` restart identity identifies `H_0 D(t)` with `D(t)`.

This is the one-sided topological input for the full positive-time Volterra
continuity theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Automatic restart on the continuous bounded path class -/

/--
For continuous globally bounded real-time paths, the Duhamel restart identity
requires no explicit interval-integrability hypotheses.
-/
theorem h3SpectralFinHeatLerayDuhamel_add_time_of_continuous
    {ν a b MU MV : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    h3SpectralFinHeatLerayDuhamel
        ν (a + b) hν U V
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinHeatLerayDuhamel
          ν a hν U V)
      +
    ∫ s in a..(a + b),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν U V s := by
  have hab : 0 ≤ a + b :=
    add_nonneg ha hb

  have hULong :
      ∀ s ∈ Set.Ioc (0 : ℝ) (a + b),
        ‖U s‖ ≤ MU := by
    intro s _hs
    exact hU s

  have hVLong :
      ∀ s ∈ Set.Ioc (0 : ℝ) (a + b),
        ‖V s‖ ≤ MV := by
    intro s _hs
    exact hV s

  have hUShort :
      ∀ s ∈ Set.Ioc (0 : ℝ) a,
        ‖U s‖ ≤ MU := by
    intro s _hs
    exact hU s

  have hVShort :
      ∀ s ∈ Set.Ioc (0 : ℝ) a,
        ‖V s‖ ≤ MV := by
    intro s _hs
    exact hV s

  have hIntLong :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν U V)
        volume
        0
        (a + b) :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν hab hMU hMV U V
      hUcont hVcont hULong hVLong

  have hIntShort :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν a hν U V)
        volume
        0
        a :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ha hMU hMV U V
      hUcont hVcont hUShort hVShort

  exact
    h3SpectralFinHeatLerayDuhamel_add_time
      hν ha hb U V hIntLong hIntShort

/-! ## NNReal restart form -/

/--
The same restart identity with the increment already packaged as a
nonnegative real.  This is the form used by the continuity theorem.
-/
theorem h3SpectralFinHeatLerayDuhamel_add_time_nnreal
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (b : ℝ≥0) :
    h3SpectralFinHeatLerayDuhamel
        ν (a + (b : ℝ)) hν U V
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        b
        (h3SpectralFinHeatLerayDuhamel
          ν a hν U V)
      +
    ∫ s in a..(a + (b : ℝ)),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + (b : ℝ)) hν U V s := by
  rcases b with ⟨b, hb⟩
  exact
    h3SpectralFinHeatLerayDuhamel_add_time_of_continuous
      hν ha hb hMU hMV U V
      hUcont hVcont hU hV

/-! ## Tail vanishing at zero increment -/

/--
For a fixed restart time `a`, the translated restart tail tends to zero as
the new elapsed time tends to zero through `ℝ≥0`.
-/
theorem tendsto_h3SpectralFinHeatLerayDuhamel_tail_zero
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    Tendsto
      (fun b : ℝ≥0 =>
        ∫ s in a..(a + (b : ℝ)),
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν (a + (b : ℝ)) hν U V s)
      (𝓝 0)
      (𝓝 0) := by
  let tail : ℝ≥0 → H3SpectralFinVectorState :=
    fun b =>
      ∫ s in a..(a + (b : ℝ)),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + (b : ℝ)) hν U V s

  let B : ℝ≥0 → ℝ :=
    fun b =>
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt (b : ℝ) * MU * MV

  have hUpper :
      ∀ᶠ b : ℝ≥0 in 𝓝 0,
        ‖tail b‖ ≤ B b := by
    exact
      Eventually.of_forall fun b => by
        dsimp [tail, B]
        exact
          norm_h3SpectralFinHeatLerayDuhamel_tail_le
            hν b.property hMU hMV U V
            hUcont hVcont hU hV

  have hBCont : Continuous B := by
    dsimp [B]
    exact
      (((continuous_const.mul
          (Real.continuous_sqrt.comp NNReal.continuous_coe)).mul
        continuous_const).mul
      continuous_const)

  have hBZero :
      Tendsto B (𝓝 0) (𝓝 0) := by
    have hB0 : B (0 : ℝ≥0) = 0 := by
      simp [B]
    have h :=
      hBCont.continuousAt (x := (0 : ℝ≥0))
    change
      Tendsto B
        (𝓝 (0 : ℝ≥0))
        (𝓝 (B (0 : ℝ≥0))) at h
    rw [hB0] at h
    exact h

  change Tendsto tail (𝓝 0) (𝓝 0)
  exact
    squeeze_zero_norm' hUpper hBZero

/-! ## Right continuity of the variable-target Duhamel map -/

/--
At every nonnegative base time `t`, the Duhamel map is continuous under a
nonnegative increment:

    b ↦ D(t+b)

is continuous at `b = 0`.
-/
theorem tendsto_h3SpectralFinHeatLerayDuhamel_add_zero
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
    Tendsto
      (fun b : ℝ≥0 =>
        h3SpectralFinHeatLerayDuhamel
          ν (t + (b : ℝ)) hν U V)
      (𝓝 0)
      (𝓝
        (h3SpectralFinHeatLerayDuhamel
          ν t hν U V)) := by
  let D0 : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamel
      ν t hν U V

  let heatPart : ℝ≥0 → H3SpectralFinVectorState :=
    fun b =>
      h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν) b D0

  let tail : ℝ≥0 → H3SpectralFinVectorState :=
    fun b =>
      ∫ s in t..(t + (b : ℝ)),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (t + (b : ℝ)) hν U V s

  have hRestart :
      (fun b : ℝ≥0 =>
        h3SpectralFinHeatLerayDuhamel
          ν (t + (b : ℝ)) hν U V)
        =
      fun b : ℝ≥0 =>
        heatPart b + tail b := by
    funext b
    dsimp [heatPart, tail, D0]
    exact
      h3SpectralFinHeatLerayDuhamel_add_time_nnreal
        hν ht hMU hMV U V
        hUcont hVcont hU hV b

  have hAtZero :
      D0 = heatPart 0 := by
    have h :=
      congrFun hRestart (0 : ℝ≥0)
    dsimp [D0, heatPart, tail] at h
    simpa using h

  have hHeat :
      Tendsto heatPart
        (𝓝 0)
        (𝓝 D0) := by
    have h :=
      (continuous_h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν) D0).continuousAt
          (x := (0 : ℝ≥0))
    change
      Tendsto
        (fun b : ℝ≥0 =>
          h3SpectralVelocityHeatApplyNN
            ν (le_of_lt hν) b D0)
        (𝓝 (0 : ℝ≥0))
        (𝓝
          (h3SpectralVelocityHeatApplyNN
            ν (le_of_lt hν) 0 D0)) at h
    dsimp [heatPart] at hAtZero ⊢
    rw [← hAtZero] at h
    exact h

  have hTail :
      Tendsto tail
        (𝓝 0)
        (𝓝 0) := by
    dsimp [tail]
    exact
      tendsto_h3SpectralFinHeatLerayDuhamel_tail_zero
        hν hMU hMV U V
        hUcont hVcont hU hV

  rw [hRestart]
  simpa using hHeat.add hTail

end

end Euclidean
end Bridge
end PrimeTensor
