import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Integral.Integrable
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cutoff-uniform derivative majorants for canonical top-order radial tails

The preceding checkpoint reduced terminal radial-tail compactness to a single
cutoff-independent `L¹((a,T))` scalar majorant for all temporal increments of

    Tail₃(t,n+1).

This file moves the remaining frontier one step closer to the PDE.

For each natural cutoff `n`, package the canonical tail as an ordinary scalar
path on `ℝ` (zero outside the strict energy-class interval).  Assume that on
the strict terminal interval:

* every such tail path is differentiable;
* the absolute derivative of every cutoff tail is bounded by the same scalar
  profile `g`;
* `g ∈ L¹((a,T))`.

Measurability of the ordinary derivative is automatic in Mathlib.  Domination
by `g` therefore gives integrability of every cutoff derivative.  The
fundamental theorem of calculus then yields

    |Tail₃(s,n+1) - Tail₃(t,n+1)|
      ≤
    |∫_s^t g(r) dr|,

uniformly in `n`.

Thus the remaining Navier--Stokes target is now a pointwise temporal one:
differentiate the sharp top-order Fourier tail and dominate its derivative by
one cutoff-independent integrable time profile.  No claim is made here that
such a profile has already been obtained from the PDE.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Canonical scalar tail paths -/

/--
The natural-cutoff top-order radial tail, viewed as an ordinary real-valued
path.  Outside the strict energy-class interval it is set to zero; all
derivative statements below are made only at strict interior times.
-/
noncomputable def h3TerminalPhysicalTopDissipationNaturalRadialTailPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationRadialTailMassAt
      hH3 hClass t ht ((n : ℝ) + 1)
  else
    0

/--
On every strict energy-class time, the scalar path is exactly the canonical
natural-cutoff radial-tail mass.
-/
@[simp]
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n t
      =
    h3TerminalPhysicalTopDissipationRadialTailMassAt
      hH3 hClass t ht ((n : ℝ) + 1) := by

  unfold
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath

  simp only [dif_pos ht]

/-! ## One integrable derivative majorant for every cutoff -/

/--
There is one scalar `L¹((a,T))` profile which dominates the absolute temporal
derivative of every canonical natural-cutoff top-order radial-tail path.

Differentiability is required only at strict energy-class times.  Integrability
of the individual derivatives is not included as a separate hypothesis:
Mathlib's measurability theorem for `deriv`, together with domination by `g`,
supplies it automatically.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ g : ℝ → ℝ,
    IntegrableOn g (Set.Ioo a T) volume
      ∧
    ∀ n : ℕ,
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo a T
            →
          DifferentiableAt ℝ
            (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
              hH3 hClass n)
            t
      )
        ∧
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo a T
            →
          abs
              (deriv
                (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
                  hH3 hClass n)
                t)
            ≤
          g t
      )

/-! ## Derivative domination gives the increment majorant -/

/--
A common integrable derivative majorant gives the common integrable increment
majorant from the preceding checkpoint.
-/
theorem naturalTopDissipationRadialTailUniformIntegrableIncrementMajorantAtEndpoint_of_uniformIntegrableDerivativeMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDerivative :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      g,
      hg,
      hCutoff
    ⟩ :=
    hDerivative

  refine
    ⟨
      g,
      hg,
      ?_
    ⟩

  intro s hs t ht n

  let F : ℝ → ℝ :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath
      hH3 hClass n

  have hDiff :
      ∀ r : ℝ,
        r ∈ Set.Ioo a T
          →
        DifferentiableAt ℝ F r := by

    intro r hr

    dsimp only [F]

    exact
      (hCutoff n).1
        r
        hr

  have hBound :
      ∀ r : ℝ,
        r ∈ Set.Ioo a T
          →
        abs (deriv F r)
          ≤
        g r := by

    intro r hr

    dsimp only [F]

    exact
      (hCutoff n).2
        r
        hr

  have hUIccSubset :
      Set.uIcc s t
        ⊆
      Set.Ioo a T := by

    intro r hr

    rcases le_total s t with hst | hts

    · rw [uIcc_of_le hst] at hr
      exact
        ⟨
          lt_of_lt_of_le
            hs.1
            hr.1,
          lt_of_le_of_lt
            hr.2
            ht.2
        ⟩

    · rw [uIcc_of_ge hts] at hr
      exact
        ⟨
          lt_of_lt_of_le
            ht.1
            hr.1,
          lt_of_le_of_lt
            hr.2
            hs.2
        ⟩

  have hDerivIntegrable :
      IntegrableOn
        (deriv F)
        (Set.Ioo a T)
        volume := by

    apply
      hg.mono'

    · exact
        aestronglyMeasurable_deriv
          F
          (volume.restrict (Set.Ioo a T))

    · rw [
        ae_restrict_iff'
          measurableSet_Ioo
      ]

      filter_upwards with r

      intro hr

      simpa only [Real.norm_eq_abs] using
        hBound r hr

  have hDerivInterval :
      IntervalIntegrable
        (deriv F)
        volume
        s
        t := by

    exact
      (
        hDerivIntegrable.mono_set
          hUIccSubset
      ).intervalIntegrable

  have hgInterval :
      IntervalIntegrable
        g
        volume
        s
        t := by

    exact
      (
        hg.mono_set
          hUIccSubset
      ).intervalIntegrable

  have hFT :
      (∫ r in s..t, deriv F r)
        =
      F t - F s := by

    exact
      intervalIntegral.integral_deriv_eq_sub
        (fun r hr =>
          hDiff
            r
            (hUIccSubset hr))
        hDerivInterval

  have hBoundInterval :
      ∀ᵐ r ∂(volume.restrict (Ι s t)),
        ‖deriv F r‖
          ≤
        g r := by

    rw [
      ae_restrict_iff'
        measurableSet_uIoc
    ]

    filter_upwards with r

    intro hr

    have hrUIcc :
        r ∈ Set.uIcc s t :=
      uIoc_subset_uIcc
        hr

    simpa only [Real.norm_eq_abs] using
      hBound
        r
        (hUIccSubset hrUIcc)

  have hIntegralBound :
      ‖∫ r in s..t, deriv F r‖
        ≤
      abs (∫ r in s..t, g r) :=
    intervalIntegral.norm_integral_le_abs_of_norm_le
      hBoundInterval
      hgInterval

  have hFs :
      F s
        =
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass s hs ((n : ℝ) + 1) := by

    dsimp only [F]

    exact
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq
        hH3 hClass n hs

  have hFt :
      F t
        =
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht ((n : ℝ) + 1) := by

    dsimp only [F]

    exact
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq
        hH3 hClass n ht

  calc
    abs
        (
          h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass s hs ((n : ℝ) + 1)
            -
          h3TerminalPhysicalTopDissipationRadialTailMassAt
            hH3 hClass t ht ((n : ℝ) + 1)
        )
        =
      ‖∫ r in s..t, deriv F r‖ := by

        rw [hFT]
        rw [Real.norm_eq_abs]
        rw [hFs, hFt]
        exact
          abs_sub_comm
            (h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass s hs ((n : ℝ) + 1))
            (h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass t ht ((n : ℝ) + 1))

    _ ≤
      abs (∫ r in s..t, g r) :=
        hIntegralBound

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, one cutoff-independent integrable
majorant of all canonical radial-tail derivatives is sufficient for smooth
continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hDerivative :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableIncrementMajorant_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalTopDissipationRadialTailUniformIntegrableIncrementMajorantAtEndpoint_of_uniformIntegrableDerivativeMajorant
        hH3
        hClass
        hDerivative)

/-! ## Nonextension obstruction -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out
one common `L¹` majorant for the derivatives of all natural-cutoff top-order
radial-tail paths.
-/
theorem not_naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
        hH3 hClass := by

  intro hDerivative

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hDerivative)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through
`T`, or the family of canonical natural-cutoff top-order radial-tail paths has
no cutoff-independent integrable derivative majorant on `(a,T)`.

This is a strictly temporal formulation of the remaining radial compactness
frontier.
-/
theorem smoothContinuationExtension_or_not_naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
        hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (not_naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
