import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Anchor

/-!
# Continuity of the Fin-indexed H³ Duhamel map

For globally continuous bounded real-time inputs, define

    D(t) = ∫₀ᵗ K_{t-s}(U(s),V(s)) ds.

The difficult analytic work has already been isolated:

* `D(t+b)` satisfies the exact heat-semigroup restart identity;
* the restart tail is `O(sqrt b)`;
* hence `D` is right-continuous at every nonnegative time;
* for a fixed anchor `a ≤ t`,
    `D(t)` is within `O(sqrt (t-a))` of the fixed heat orbit
    `H_{t-a} D(a)`.

This file closes the topological loop by proving ordinary continuity of

    t : ℝ≥0 ↦ D(t).

At zero, the previously proved right-continuity theorem is exactly the
required topology on `ℝ≥0`.  At a positive target `t₀`, choose a fixed
anchor `a < t₀` sufficiently close to `t₀`.  Both `D(t₀)` and nearby `D(t)`
are then close to one fixed strongly-continuous heat orbit, giving the
standard three-term epsilon argument.

No dominated-convergence argument with a moving singularity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Scalar restart-error profile -/

/--
The scalar error profile controlling a restart tail of nonnegative length.
-/
def h3HeatLerayRestartError
    (ν MU MV : ℝ)
    (r : ℝ≥0) : ℝ :=
  h3HeatLerayDuhamelCoefficient ν *
    Real.sqrt (r : ℝ) * MU * MV

theorem continuous_h3HeatLerayRestartError
    (ν MU MV : ℝ) :
    Continuous (h3HeatLerayRestartError ν MU MV) := by
  unfold h3HeatLerayRestartError
  exact
    (((continuous_const.mul
        (Real.continuous_sqrt.comp NNReal.continuous_coe)).mul
      continuous_const).mul
    continuous_const)

@[simp]
theorem h3HeatLerayRestartError_zero
    (ν MU MV : ℝ) :
    h3HeatLerayRestartError ν MU MV 0 = 0 := by
  simp [h3HeatLerayRestartError]

/-! ## Fixed-anchor heat orbit -/

/--
Nonnegative elapsed time from a real anchor, truncated to zero before the
anchor.  Near any target strictly after the anchor this is just `t-a`.
-/
def h3RestartLagNN
    (a : ℝ)
    (t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((t : ℝ) - a)

theorem continuous_h3RestartLagNN
    (a : ℝ) :
    Continuous (h3RestartLagNN a) := by
  unfold h3RestartLagNN
  exact
    continuous_real_toNNReal.comp
      (NNReal.continuous_coe.sub continuous_const)

/--
The fixed heat orbit launched from the Duhamel value at anchor `a`.
-/
def h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
    (ν a : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (t : ℝ≥0) :
    H3SpectralFinVectorState :=
  h3SpectralVelocityHeatApplyNN
    ν (le_of_lt hν)
    (h3RestartLagNN a t)
    (h3SpectralFinHeatLerayDuhamel
      ν a hν U V)

theorem continuous_h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
    (ν a : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    Continuous
      (h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
        ν a hν U V) := by
  unfold h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
  exact
    (continuous_h3SpectralVelocityHeatApplyNN
      ν (le_of_lt hν)
      (h3SpectralFinHeatLerayDuhamel
        ν a hν U V)).comp
      (continuous_h3RestartLagNN a)

/--
After the anchor, the fixed heat-orbit lag is exactly the ordinary elapsed
time packaged as a nonnegative real.
-/
theorem h3RestartLagNN_eq_mk
    {a : ℝ}
    {t : ℝ≥0}
    (hat : a ≤ (t : ℝ)) :
    h3RestartLagNN a t
      =
    NNReal.mk ((t : ℝ) - a) (sub_nonneg.mpr hat) := by
  apply NNReal.eq
  simp [h3RestartLagNN, Real.toNNReal, sub_nonneg.mpr hat]

/-! ## Anchor approximation in NNReal time -/

/--
The fixed-anchor approximation rewritten for an `ℝ≥0` target and the globally
defined fixed heat orbit.
-/
theorem dist_h3SpectralFinHeatLerayDuhamel_anchorHeatOrbit_le
    {ν a MU MV : ℝ}
    {t : ℝ≥0}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hat : a ≤ (t : ℝ))
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    dist
      (h3SpectralFinHeatLerayDuhamel
        ν (t : ℝ) hν U V)
      (h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
        ν a hν U V t)
      ≤
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt ((t : ℝ) - a) * MU * MV := by
  have h :=
    dist_h3SpectralFinHeatLerayDuhamel_heat_restart_le
      (ν := ν)
      (a := a)
      (t := (t : ℝ))
      (MU := MU)
      (MV := MV)
      hν ha hat hMU hMV U V
      hUcont hVcont hU hV
  unfold h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
  rw [h3RestartLagNN_eq_mk hat]
  exact h

/-! ## Continuity at positive time -/

/--
The Duhamel map is continuous at every strictly positive nonnegative time.
-/
theorem continuousAt_h3SpectralFinHeatLerayDuhamel_nnreal_of_pos
    {ν MU MV : ℝ}
    {t₀ : ℝ≥0}
    (hν : 0 < ν)
    (ht₀ : 0 < t₀)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    ContinuousAt
      (fun t : ℝ≥0 =>
        h3SpectralFinHeatLerayDuhamel
          ν (t : ℝ) hν U V)
      t₀ := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε

  let E : ℝ≥0 → ℝ :=
    h3HeatLerayRestartError ν MU MV

  have hEcont : Continuous E :=
    continuous_h3HeatLerayRestartError ν MU MV

  have hE0 : E 0 = 0 := by
    simp [E]

  have hε6 : 0 < ε / 6 := by
    linarith

  obtain ⟨δE, hδE, hδEprop⟩ :=
    (Metric.continuousAt_iff.mp
      (hEcont.continuousAt (x := (0 : ℝ≥0)))
      (ε / 6) hε6)

  let r : ℝ :=
    min (δE / 2) ((t₀ : ℝ) / 2)

  have ht₀real : 0 < (t₀ : ℝ) := by
    exact_mod_cast ht₀

  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hδE) (half_pos ht₀real)

  have hr_le_t₀ : r ≤ (t₀ : ℝ) := by
    dsimp [r]
    exact
      (min_le_right _ _).trans
        (by linarith)

  let rNN : ℝ≥0 :=
    NNReal.mk r hr.le

  have hrNN_dist :
      dist rNN (0 : ℝ≥0) < δE := by
    rw [NNReal.dist_eq]
    dsimp [rNN]
    simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero]
    rw [abs_of_nonneg hr.le]
    dsimp [r]
    exact
      lt_of_le_of_lt
        (min_le_left _ _)
        (half_lt_self hδE)

  have hEr_dist :
      dist (E rNN) (E 0) < ε / 6 :=
    hδEprop hrNN_dist

  have hEr :
      E rNN < ε / 6 := by
    rw [hE0, Real.dist_eq, sub_zero] at hEr_dist
    have hle :
        E rNN ≤ |E rNN| :=
      le_abs_self _
    linarith

  let a : ℝ :=
    (t₀ : ℝ) - r

  have ha : 0 ≤ a := by
    dsimp [a]
    linarith

  have hat₀ : a ≤ (t₀ : ℝ) := by
    dsimp [a]
    linarith

  have hat₀_strict : a < (t₀ : ℝ) := by
    dsimp [a]
    linarith

  have ht₀_sub_a :
      (t₀ : ℝ) - a = r := by
    dsimp [a]
    ring

  let H :
      ℝ≥0 → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
      ν a hν U V

  have hHcont : Continuous H :=
    continuous_h3SpectralFinHeatLerayDuhamelAnchorHeatOrbit
      ν a hν U V

  obtain ⟨δH, hδH, hδHprop⟩ :=
    (Metric.continuousAt_iff.mp
      (hHcont.continuousAt (x := t₀))
      (ε / 3) (by linarith))

  let A : ℝ≥0 → ℝ :=
    fun t =>
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt ((t : ℝ) - a) * MU * MV

  have hAcont : Continuous A := by
    dsimp [A]
    exact
      (((continuous_const.mul
          (Real.continuous_sqrt.comp
            (NNReal.continuous_coe.sub continuous_const))).mul
        continuous_const).mul
      continuous_const)

  have hAt₀ :
      A t₀ = E rNN := by
    dsimp [A, E, h3HeatLerayRestartError, rNN]
    rw [ht₀_sub_a]

  obtain ⟨δA, hδA, hδAprop⟩ :=
    (Metric.continuousAt_iff.mp
      (hAcont.continuousAt (x := t₀))
      (ε / 6) hε6)

  let δpos : ℝ :=
    r / 2

  have hδpos : 0 < δpos := by
    dsimp [δpos]
    linarith

  let δ : ℝ :=
    min δpos (min δA δH)

  have hδ : 0 < δ := by
    dsimp [δ]
    exact
      lt_min hδpos
        (lt_min hδA hδH)

  refine ⟨δ, hδ, ?_⟩
  intro t ht

  have htpos :
      dist t t₀ < δpos := by
    exact
      lt_of_lt_of_le ht
        (by
          dsimp [δ]
          exact min_le_left _ _)

  have htA :
      dist t t₀ < δA := by
    exact
      lt_of_lt_of_le ht
        (by
          dsimp [δ]
          exact
            (min_le_right _ _).trans
              (min_le_left _ _))

  have htH :
      dist t t₀ < δH := by
    exact
      lt_of_lt_of_le ht
        (by
          dsimp [δ]
          exact
            (min_le_right _ _).trans
              (min_le_right _ _))

  have ht_lower :
      a ≤ (t : ℝ) := by
    have habs :
        |(t : ℝ) - (t₀ : ℝ)| < r / 2 := by
      simpa [NNReal.dist_eq, δpos] using htpos
    have hleft :=
      (abs_lt.mp habs).1
    dsimp [a]
    linarith

  have hDx :
      dist
        (h3SpectralFinHeatLerayDuhamel
          ν (t : ℝ) hν U V)
        (H t)
        ≤
      A t := by
    dsimp [H, A]
    exact
      dist_h3SpectralFinHeatLerayDuhamel_anchorHeatOrbit_le
        hν ha ht_lower hMU hMV U V
        hUcont hVcont hU hV

  have hD0 :
      dist
        (h3SpectralFinHeatLerayDuhamel
          ν (t₀ : ℝ) hν U V)
        (H t₀)
        ≤
      A t₀ := by
    dsimp [H, A]
    exact
      dist_h3SpectralFinHeatLerayDuhamel_anchorHeatOrbit_le
        hν ha hat₀ hMU hMV U V
        hUcont hVcont hU hV

  have hAnear :
      dist (A t) (A t₀) < ε / 6 :=
    hδAprop htA

  have hAt₀small :
      A t₀ < ε / 6 := by
    rw [hAt₀]
    exact hEr

  have hAt :
      A t < ε / 3 := by
    have hdiff :
        |A t - A t₀| < ε / 6 := by
      simpa [Real.dist_eq] using hAnear
    have hsuble :
        A t - A t₀ ≤ |A t - A t₀| :=
      le_abs_self _
    linarith

  have hH :
      dist (H t) (H t₀) < ε / 3 :=
    hδHprop htH

  calc
    dist
        (h3SpectralFinHeatLerayDuhamel
          ν (t : ℝ) hν U V)
        (h3SpectralFinHeatLerayDuhamel
          ν (t₀ : ℝ) hν U V)
        ≤
      dist
          (h3SpectralFinHeatLerayDuhamel
            ν (t : ℝ) hν U V)
          (H t)
        +
      dist (H t) (H t₀)
        +
      dist
          (H t₀)
          (h3SpectralFinHeatLerayDuhamel
            ν (t₀ : ℝ) hν U V) := by
              exact dist_triangle4 _ _ _ _
    _ < ε := by
      rw [dist_comm (H t₀)]
      linarith

/-! ## Global continuity on nonnegative physical time -/

/--
For globally continuous bounded real-time inputs, the full Fin-indexed
heat--Leray Duhamel map is continuous on physical nonnegative time.
-/
theorem continuous_h3SpectralFinHeatLerayDuhamel_nnreal
    {ν MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    Continuous
      (fun t : ℝ≥0 =>
        h3SpectralFinHeatLerayDuhamel
          ν (t : ℝ) hν U V) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  by_cases ht₀zero : t₀ = 0
  · subst t₀
    change
      Tendsto
        (fun t : ℝ≥0 =>
          h3SpectralFinHeatLerayDuhamel
            ν (t : ℝ) hν U V)
        (𝓝 0)
        (𝓝
          (h3SpectralFinHeatLerayDuhamel
            ν 0 hν U V))
    have h :=
      tendsto_h3SpectralFinHeatLerayDuhamel_add_zero
        (t := (0 : ℝ))
        hν le_rfl hMU hMV U V
        hUcont hVcont hU hV
    simpa only [zero_add] using h
  · have ht₀ : 0 < t₀ :=
      (pos_iff_ne_zero).2 ht₀zero
    exact
      continuousAt_h3SpectralFinHeatLerayDuhamel_nnreal_of_pos
        hν ht₀ hMU hMV U V
        hUcont hVcont hU hV

end

end Euclidean
end Bridge
end PrimeTensor
