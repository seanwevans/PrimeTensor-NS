import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralDuhamelPhysicalCocycleThreeStep

/-!
# Finite physical Duhamel restart cocycle

The two-step and three-step cocycles compile the local restart algebra.  This
file closes the finite iteration step.

A finite list of positive `NNReal` durations is folded from left to right.  At
each new leg the already accumulated nonlinear remainder is advanced by the
heat semigroup and the fresh translated Duhamel remainder is added.  The
existing two-step cocycle proves inductively that this fold is exactly the
single Duhamel remainder over the total elapsed time.

Consequently the total decoded remainder is still in the Schwartz physical
realization set for the total elapsed time.  The final theorem specializes the
construction to the Banach-selected globally clamped mild path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Finite restart fold of spectral Duhamel remainders.  The singleton case is
one ordinary translated Duhamel remainder; each additional leg advances the
previous remainder by the heat semigroup and appends the recursively folded
tail. -/
def h3SpectralFinHeatLerayDuhamelRestartFold
    (ν a : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    List NNReal → H3SpectralFinVectorState
  | [] => 0
  | [b] =>
      h3SpectralFinHeatLerayDuhamel
        ν (b : ℝ) hν
        (fun q => U (q + a))
        (fun q => V (q + a))
  | b :: c :: ds =>
      h3SpectralVelocityHeatApplyNN
          ν hν.le ((c :: ds).sum)
          (h3SpectralFinHeatLerayDuhamel
            ν (b : ℝ) hν
            (fun q => U (q + a))
            (fun q => V (q + a)))
        +
      h3SpectralFinHeatLerayDuhamelRestartFold
        ν ((b : ℝ) + a) hν U V (c :: ds)

/-- A nonempty finite list of strictly positive `NNReal` durations has
strictly positive total duration. -/
theorem h3NNRealList_sum_pos_of_nonempty_of_forall_mem_pos
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d) :
    0 < ds.sum := by
  induction ds with
  | nil => exact (hne rfl).elim
  | cons d ds ih =>
      have hd : 0 < d := hpos d (by simp)
      simp only [List.sum_cons]
      positivity

/-- The finite restart fold is exactly the single Duhamel remainder over the
sum of all elapsed times. -/
theorem h3SpectralFinHeatLerayDuhamel_shifted_eq_restartFold_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d) :
    h3SpectralFinHeatLerayDuhamel
        ν ((ds.sum : NNReal) : ℝ) hν
        (fun q => U (q + a))
        (fun q => V (q + a))
      =
    h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds := by
  induction ds generalizing a with
  | nil => exact (hne rfl).elim
  | cons b ds ih =>
      cases ds with
      | nil =>
          simp [h3SpectralFinHeatLerayDuhamelRestartFold]
      | cons c rest =>
          have hbNN : 0 < b := hpos b (by simp)
          have hposTail : ∀ d ∈ c :: rest, 0 < d := by
            intro d hd
            exact hpos d (List.mem_cons_of_mem b hd)
          have htailNN : 0 < (c :: rest).sum :=
            h3NNRealList_sum_pos_of_nonempty_of_forall_mem_pos
              (c :: rest) (by simp) hposTail
          have hb : 0 < (b : ℝ) := by
            exact_mod_cast hbNN
          have htail : 0 < (((c :: rest).sum : NNReal) : ℝ) := by
            exact_mod_cast htailNN

          have hsplit :=
            h3SpectralFinHeatLerayDuhamel_shifted_add_time_of_continuous
              (a := a)
              hν hb htail hMU hMV U V hUcont hVcont hU hV

          have hih :=
            ih
              (a := (b : ℝ) + a)
              (by simp)
              hposTail

          have hmk :
              NNReal.mk (((c :: rest).sum : NNReal) : ℝ) htail.le
                = (c :: rest).sum := by
            apply Subtype.ext
            simp

          have hih' :
              h3SpectralFinHeatLerayDuhamel
                  ν (((c :: rest).sum : NNReal) : ℝ) hν
                  (fun r => U ((r + (b : ℝ)) + a))
                  (fun r => V ((r + (b : ℝ)) + a))
                =
              h3SpectralFinHeatLerayDuhamelRestartFold
                ν ((b : ℝ) + a) hν U V (c :: rest) := by
            simpa only [add_assoc] using hih

          rw [hmk] at hsplit
          rw [hih'] at hsplit
          simpa only [
            h3SpectralFinHeatLerayDuhamelRestartFold,
            List.sum_cons,
            NNReal.coe_add,
            add_assoc
          ] using hsplit

/-- Finite restart collapse together with Schwartz physical realization of the
single total nonlinear remainder. -/
theorem h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_finite_cocycle_of_continuous
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d) :
    let T : ℝ := ((ds.sum : NNReal) : ℝ)
    let RtotalS :=
      h3SpectralFinHeatLerayDuhamel
        ν T hν
        (fun q => U (q + a))
        (fun q => V (q + a))
    h3SpectralFinVectorDecodeComplexL2 RtotalS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν T hν
      ∧
    RtotalS =
      h3SpectralFinHeatLerayDuhamelRestartFold ν a hν U V ds := by
  dsimp only
  have hsumNN : 0 < ds.sum :=
    h3NNRealList_sum_pos_of_nonempty_of_forall_mem_pos ds hne hpos
  have hsum : 0 < ((ds.sum : NNReal) : ℝ) := by
    exact_mod_cast hsumNN

  let Ua : ℝ → H3SpectralFinVectorState := fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState := fun q => V (q + a)

  have hUaCont : Continuous Ua := by
    dsimp [Ua]
    exact hUcont.comp (continuous_id.add continuous_const)
  have hVaCont : Continuous Va := by
    dsimp [Va]
    exact hVcont.comp (continuous_id.add continuous_const)
  have hUa : ∀ q : ℝ, ‖Ua q‖ ≤ MU := by
    intro q
    exact hU (q + a)
  have hVa : ∀ q : ℝ, ‖Va q‖ ≤ MV := by
    intro q
    exact hV (q + a)

  have hmem :=
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
      hν hsum hMU hMV Ua Va hUaCont hVaCont hUa hVa

  have heq :=
    h3SpectralFinHeatLerayDuhamel_shifted_eq_restartFold_of_continuous
      (a := a)
      hν hMU hMV U V hUcont hVcont hU hV ds hne hpos

  exact ⟨by simpa only [Ua, Va] using hmem, heq⟩

/-- The Banach-selected globally clamped mild path inherits the arbitrary
finite realized restart cocycle at every interior origin. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_realized_finite_remainder_cocycle
    {ν τ A a : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (ds : List NNReal)
    (hne : ds ≠ [])
    (hpos : ∀ d ∈ ds, 0 < d) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall
    let T : ℝ := ((ds.sum : NNReal) : ℝ)
    let RtotalS :=
      h3SpectralFinHeatLerayDuhamel
        ν T hν
        (fun q => W (q + a))
        (fun q => W (q + a))
    h3SpectralFinVectorDecodeComplexL2 RtotalS
        ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization ν T hν
      ∧
    RtotalS =
      h3SpectralFinHeatLerayDuhamelRestartFold ν a hν W W ds := by
  dsimp only
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hWcont : Continuous W := by
    simpa only [W] using hWb.1
  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [W] using hWb.2 s
  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le

  simpa only [W] using
    (h3SpectralFinHeatLerayDuhamel_shifted_decodeComplexL2_realized_finite_cocycle_of_continuous
      (a := a)
      hν htwoA htwoA W W hWcont hWcont hWbound hWbound
      ds hne hpos)

end

end Euclidean
end Bridge
end PrimeTensor
