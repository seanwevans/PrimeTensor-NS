import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.CompactOpen

/-!
# Joint measurability of the preterminal vorticity temporal derivatives

The previous two increments established the exact sectionwise hypotheses:

* for each fixed spatial point, the actual temporal derivative of each
  vorticity component is measurable in time;
* at every strict preterminal time, that same derivative is continuous in
  space.

This file combines those facts into joint measurability without making the
false inference from separate continuity to joint continuity.

The mechanism is Mathlib's Carathéodory-style strong-measurability theorem.
Given a function

    f : ℝ → Point3 → ℝ

whose point evaluations are measurable in time and whose spatial slices are
continuous on `(0,T)`, package each spatial slice as a continuous map and
extend by the zero continuous map outside `(0,T)`.  After swapping the
arguments, `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable`
combines continuity in space with strong measurability in time to give joint
measurability on `Point3 × ℝ`; composing with the coordinate swap gives the
required statement on `ℝ × Point3`.

This is exactly the product-space measurability input needed for the upcoming
vorticity Fubini argument.  No joint spacetime continuity is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Topology

noncomputable section

/-- Extend a family of continuous spatial slices by the zero continuous map
outside the strict preterminal time interval. -/
noncomputable def h3PreterminalContinuousSliceExtension
    (T : ℝ)
    (f : ℝ → Point3 → ℝ)
    (hSpace :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) T →
        Continuous (f s))
    (s : ℝ) :
    C(Point3, ℝ) :=
  if hs : s ∈ Set.Ioo (0 : ℝ) T then
    ⟨f s, hSpace s hs⟩
  else
    ⟨fun _ : Point3 => (0 : ℝ), continuous_const⟩

@[simp]
theorem h3PreterminalContinuousSliceExtension_apply_of_mem
    (T : ℝ)
    (f : ℝ → Point3 → ℝ)
    (hSpace :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) T →
        Continuous (f s))
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3PreterminalContinuousSliceExtension
        T f hSpace s x
      =
    f s x := by
  simp [h3PreterminalContinuousSliceExtension, hs]

@[simp]
theorem h3PreterminalContinuousSliceExtension_apply_of_not_mem
    (T : ℝ)
    (f : ℝ → Point3 → ℝ)
    (hSpace :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) T →
        Continuous (f s))
    {s : ℝ}
    (hs : s ∉ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3PreterminalContinuousSliceExtension
        T f hSpace s x
      =
    0 := by
  simp [h3PreterminalContinuousSliceExtension, hs]

/-- The zero-extended scalar evaluation is jointly measurable in time and
space.  This is a Carathéodory-style measurable consequence, not a continuity
statement. -/
theorem measurable_h3PreterminalContinuousSliceExtension_joint
    (T : ℝ)
    (f : ℝ → Point3 → ℝ)
    (hTime :
      ∀ x : Point3,
        Measurable (fun s : ℝ => f s x))
    (hSpace :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) T →
        Continuous (f s)) :
    Measurable
      (fun p : ℝ × Point3 =>
        h3PreterminalContinuousSliceExtension
          T f hSpace p.1 p.2) := by
  let g : Point3 → ℝ → ℝ :=
    fun x s =>
      h3PreterminalContinuousSliceExtension
        T f hSpace s x

  have hSpaceAll :
      ∀ s : ℝ,
        Continuous (fun x : Point3 => g x s) := by
    intro s
    change Continuous
      (h3PreterminalContinuousSliceExtension
        T f hSpace s)
    exact
      (h3PreterminalContinuousSliceExtension
        T f hSpace s).continuous

  have hTimeAll :
      ∀ x : Point3,
        StronglyMeasurable (g x) := by
    intro x

    have hEq :
        g x
          =
        Set.piecewise
          (Set.Ioo (0 : ℝ) T)
          (fun s : ℝ => f s x)
          (fun _ : ℝ => (0 : ℝ)) := by
      funext s
      by_cases hs : s ∈ Set.Ioo (0 : ℝ) T
      · change
          h3PreterminalContinuousSliceExtension
              T f hSpace s x
            =
          Set.piecewise
              (Set.Ioo (0 : ℝ) T)
              (fun r : ℝ => f r x)
              (fun _ : ℝ => (0 : ℝ))
              s
        rw [Set.piecewise_eq_of_mem _ _ _ hs]
        exact
          h3PreterminalContinuousSliceExtension_apply_of_mem
            T f hSpace hs x
      · change
          h3PreterminalContinuousSliceExtension
              T f hSpace s x
            =
          Set.piecewise
              (Set.Ioo (0 : ℝ) T)
              (fun r : ℝ => f r x)
              (fun _ : ℝ => (0 : ℝ))
              s
        rw [Set.piecewise_eq_of_notMem _ _ _ hs]
        exact
          h3PreterminalContinuousSliceExtension_apply_of_not_mem
            T f hSpace hs x

    have hMeas : Measurable (g x) := by
      rw [hEq]
      exact
        Measurable.piecewise
          measurableSet_Ioo
          (hTime x)
          measurable_const

    exact hMeas.stronglyMeasurable

  have hJointSwap :
      StronglyMeasurable (Function.uncurry g) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      hSpaceAll hTimeAll

  have hJointSwapMeas :
      Measurable (Function.uncurry g) :=
    hJointSwap.measurable

  have hSwap :
      Measurable
        (fun p : ℝ × Point3 => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst

  have hComp := hJointSwapMeas.comp hSwap

  change Measurable (fun p : ℝ × Point3 => g p.2 p.1)
  change
    Measurable
      ((Function.uncurry g) ∘
        (fun p : ℝ × Point3 => (p.2, p.1)))
  exact hComp

/-- Continuous-map-valued zero extension of the actual x-vorticity temporal
derivative. -/
noncomputable def h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (s : ℝ) :
    C(Point3, ℝ) :=
  h3PreterminalContinuousSliceExtension
    T
    (fun r : ℝ =>
      fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            realVorticityX
              (logSpaceTimeVectorField u) q x)
          r)
    (fun r hr =>
      h3LoggedPreterminalVorticityX_temporalDerivative_continuous_space
        hNS hr)
    s

/-- Continuous-map-valued zero extension of the actual y-vorticity temporal
derivative. -/
noncomputable def h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (s : ℝ) :
    C(Point3, ℝ) :=
  h3PreterminalContinuousSliceExtension
    T
    (fun r : ℝ =>
      fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            realVorticityY
              (logSpaceTimeVectorField u) q x)
          r)
    (fun r hr =>
      h3LoggedPreterminalVorticityY_temporalDerivative_continuous_space
        hNS hr)
    s

/-- Continuous-map-valued zero extension of the actual z-vorticity temporal
derivative. -/
noncomputable def h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (s : ℝ) :
    C(Point3, ℝ) :=
  h3PreterminalContinuousSliceExtension
    T
    (fun r : ℝ =>
      fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            realVorticityZ
              (logSpaceTimeVectorField u) q x)
          r)
    (fun r hr =>
      h3LoggedPreterminalVorticityZ_temporalDerivative_continuous_space
        hNS hr)
    s

@[simp]
theorem h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
        hNS s x
      =
    temporal.d
      (fun q : ℝ =>
        realVorticityX
          (logSpaceTimeVectorField u) q x)
      s := by
  unfold
    h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
  exact
    h3PreterminalContinuousSliceExtension_apply_of_mem
      T
      (fun r : ℝ =>
        fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              realVorticityX
                (logSpaceTimeVectorField u) q y)
            r)
      _
      hs x

@[simp]
theorem h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
        hNS s x
      =
    temporal.d
      (fun q : ℝ =>
        realVorticityY
          (logSpaceTimeVectorField u) q x)
      s := by
  unfold
    h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
  exact
    h3PreterminalContinuousSliceExtension_apply_of_mem
      T
      (fun r : ℝ =>
        fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              realVorticityY
                (logSpaceTimeVectorField u) q y)
            r)
      _
      hs x

@[simp]
theorem h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_of_mem
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
        hNS s x
      =
    temporal.d
      (fun q : ℝ =>
        realVorticityZ
          (logSpaceTimeVectorField u) q x)
      s := by
  unfold
    h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
  exact
    h3PreterminalContinuousSliceExtension_apply_of_mem
      T
      (fun r : ℝ =>
        fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              realVorticityZ
                (logSpaceTimeVectorField u) q y)
            r)
      _
      hs x

/-- The zero-extended x-vorticity temporal derivative is jointly measurable. -/
theorem measurable_h3LoggedPreterminalVorticityX_temporalDerivative_joint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) :
    Measurable
      (fun p : ℝ × Point3 =>
        h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
          hNS p.1 p.2) := by
  unfold
    h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension

  exact
    measurable_h3PreterminalContinuousSliceExtension_joint
      T
      (fun r : ℝ =>
        fun x : Point3 =>
          temporal.d
            (fun q : ℝ =>
              realVorticityX
                (logSpaceTimeVectorField u) q x)
            r)
      (fun x =>
        measurable_h3LoggedPreterminalVorticityX_temporalDerivative
          u x)
      (fun r hr =>
        h3LoggedPreterminalVorticityX_temporalDerivative_continuous_space
          hNS hr)

/-- The zero-extended y-vorticity temporal derivative is jointly measurable. -/
theorem measurable_h3LoggedPreterminalVorticityY_temporalDerivative_joint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) :
    Measurable
      (fun p : ℝ × Point3 =>
        h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
          hNS p.1 p.2) := by
  unfold
    h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension

  exact
    measurable_h3PreterminalContinuousSliceExtension_joint
      T
      (fun r : ℝ =>
        fun x : Point3 =>
          temporal.d
            (fun q : ℝ =>
              realVorticityY
                (logSpaceTimeVectorField u) q x)
            r)
      (fun x =>
        measurable_h3LoggedPreterminalVorticityY_temporalDerivative
          u x)
      (fun r hr =>
        h3LoggedPreterminalVorticityY_temporalDerivative_continuous_space
          hNS hr)

/-- The zero-extended z-vorticity temporal derivative is jointly measurable. -/
theorem measurable_h3LoggedPreterminalVorticityZ_temporalDerivative_joint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) :
    Measurable
      (fun p : ℝ × Point3 =>
        h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
          hNS p.1 p.2) := by
  unfold
    h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension

  exact
    measurable_h3PreterminalContinuousSliceExtension_joint
      T
      (fun r : ℝ =>
        fun x : Point3 =>
          temporal.d
            (fun q : ℝ =>
              realVorticityZ
                (logSpaceTimeVectorField u) q x)
            r)
      (fun x =>
        measurable_h3LoggedPreterminalVorticityZ_temporalDerivative
          u x)
      (fun r hr =>
        h3LoggedPreterminalVorticityZ_temporalDerivative_continuous_space
          hNS hr)

end

end Euclidean
end Bridge
end PrimeTensor
