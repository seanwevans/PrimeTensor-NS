import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Envelope.Clock.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Tail.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Duhamel.Bound

/-!
# Tail-wide vorticity-envelope square-clock obstruction

A tail-wide bound

`(T - t) * g t ^ 2 ≤ B`

is much stronger than the corresponding bound only on a selected sequence.
For a measurable common vorticity envelope it implies

`g t ≲ 1 / sqrt (T - t)`,

and the reciprocal-square-root singularity is integrable at the terminal
endpoint.  Hence the envelope is integrable on the terminal H³ energy-class
tail, and the already-closed tail-local BKM theorem produces smooth
continuation through `T`.

Consequently hypothetical nonextension rules out every measurable common
vorticity envelope with a bounded tail-wide physical square clock.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A measurable common vorticity envelope with bounded tail-wide square clock
is integrable on the H³ energy-class tail. -/
theorem integrableOn_vorticityEnvelope_of_boundedTailSquareClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {g : ℝ → ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hEnvelope :
      ∀ t : ℝ, t ∈ Set.Ioo a T → VorticityEnvelope u g t)
    (hMeas :
      AEStronglyMeasurable
        g
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T)))
    (hSquareClock : ∃ B : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * (g t) ^ 2 ≤ B) :
    MeasureTheory.IntegrableOn g (Set.Ioo a T) := by
  obtain ⟨B, hClock⟩ := hSquareClock

  let t₀ : ℝ := (a + T) / 2
  have ht₀ : t₀ ∈ Set.Ioo a T := by
    dsimp [t₀]
    constructor <;> linarith [hClass.terminal_start.2]

  have hGap₀ : 0 ≤ T - t₀ :=
    sub_nonneg.mpr ht₀.2.le
  have hB : 0 ≤ B := by
    exact
      (mul_nonneg hGap₀ (sq_nonneg (g t₀))).trans
        (hClock t₀ ht₀)

  have hTNonneg : 0 ≤ T := by
    linarith [hClass.terminal_start.1, hClass.terminal_start.2]

  have hKernelInterval :
      IntervalIntegrable
        (h3ViscousTimeSingularKernel (1 : ℝ) T)
        volume
        0 T :=
    h3ViscousTimeSingularKernel_intervalIntegrable
      (ν := (1 : ℝ)) (t := T) zero_lt_one hTNonneg

  have hKernelWhole :
      MeasureTheory.IntegrableOn
        (h3ViscousTimeSingularKernel (1 : ℝ) T)
        (Set.Ioo (0 : ℝ) T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hTNonneg).1
      hKernelInterval

  have hKernelTail :
      MeasureTheory.IntegrableOn
        (h3ViscousTimeSingularKernel (1 : ℝ) T)
        (Set.Ioo a T) := by
    apply hKernelWhole.mono_set
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hMajorant :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt B * h3ViscousTimeSingularKernel (1 : ℝ) T t)
        (Set.Ioo a T) := by
    change
      MeasureTheory.Integrable
        (fun t : ℝ =>
          Real.sqrt B * h3ViscousTimeSingularKernel (1 : ℝ) T t)
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T))
    exact hKernelTail.const_mul (Real.sqrt B)

  change
    MeasureTheory.Integrable
      g
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T))

  apply Integrable.mono' hMajorant hMeas

  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht

  have hGap : 0 < T - t :=
    sub_pos.mpr ht.2
  have hGapNonneg : 0 ≤ T - t :=
    hGap.le
  have hg : 0 ≤ g t :=
    h3BKM_vorticityEnvelope_nonneg (hEnvelope t ht)
  have hRootPos : 0 < Real.sqrt (T - t) :=
    Real.sqrt_pos.2 hGap

  have hSquare :
      (g t * Real.sqrt (T - t)) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hGapNonneg, Real.sq_sqrt hB]
    nlinarith [hClock t ht]

  have hScaled :
      g t * Real.sqrt (T - t) ≤ Real.sqrt B := by
    exact
      (sq_le_sq₀
        (mul_nonneg hg (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg B)).1 hSquare

  have hPoint :
      g t ≤ Real.sqrt B / Real.sqrt (T - t) :=
    (le_div_iff₀ hRootPos).2 hScaled

  have hPoint' :
      g t ≤
        Real.sqrt B * h3ViscousTimeSingularKernel (1 : ℝ) T t := by
    simpa [h3ViscousTimeSingularKernel, div_eq_mul_inv] using hPoint

  have hMajorNonneg :
      0 ≤ Real.sqrt B * h3ViscousTimeSingularKernel (1 : ℝ) T t := by
    unfold h3ViscousTimeSingularKernel
    exact
      mul_nonneg
        (Real.sqrt_nonneg B)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))

  simpa only [Real.norm_eq_abs, abs_of_nonneg hg,
    abs_of_nonneg hMajorNonneg] using hPoint'

/-- A measurable common vorticity envelope satisfying a tail-wide bounded
physical square clock forces smooth continuation through the terminal time. -/
theorem h3PathExtension_of_boundedVorticityEnvelopeTailSquareClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEnvelope :
      ∀ t : ℝ, t ∈ Set.Ioo a T → VorticityEnvelope u g t)
    (hMeas :
      AEStronglyMeasurable
        g
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T)))
    (hSquareClock : ∃ B : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * (g t) ^ 2 ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hIntegrable :
      MeasureTheory.IntegrableOn g (Set.Ioo a T) :=
    integrableOn_vorticityEnvelope_of_boundedTailSquareClock
      hClass hEnvelope hMeas hSquareClock
  exact
    h3PathExtension_of_integrableVorticityEnvelopeOnEnergyClassTail
      hH3 hClass hIntegrable hEnvelope

/-- On a hypothetical nonextension branch, no measurable common vorticity
envelope can have bounded physical square clock on the entire energy-class
tail. -/
theorem no_boundedVorticityEnvelopeTailSquareClock_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEnvelope :
      ∀ t : ℝ, t ∈ Set.Ioo a T → VorticityEnvelope u g t)
    (hMeas :
      AEStronglyMeasurable
        g
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T))) :
    ¬ ∃ B : ℝ,
      ∀ t : ℝ, t ∈ Set.Ioo a T →
        (T - t) * (g t) ^ 2 ≤ B := by
  intro hSquareClock
  exact
    hNoExtension
      (h3PathExtension_of_boundedVorticityEnvelopeTailSquareClock
        hH3 hClass hEnvelope hMeas hSquareClock)

end

end Euclidean
end Bridge
end PrimeTensor
