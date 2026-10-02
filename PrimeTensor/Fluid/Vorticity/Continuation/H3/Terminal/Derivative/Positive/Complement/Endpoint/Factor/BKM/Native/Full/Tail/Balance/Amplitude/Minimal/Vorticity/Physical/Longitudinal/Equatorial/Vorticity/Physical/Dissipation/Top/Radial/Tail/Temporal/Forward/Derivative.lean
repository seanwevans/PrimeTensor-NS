import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.Integrable
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Derivative.Majorant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-sided derivative control of canonical top-order radial tails

The preceding one-sided checkpoint showed that terminal radial compactness only
needs a common integrable bound on *forward increases* of the natural sharp
tails.

This file reduces that condition to the differential form suited to the
localized Navier--Stokes energy identity.

For every natural cutoff `n`, let

    Fₙ(t) = Tail₃(t,n+1).

Assume:

* `Fₙ` is differentiable at every strict preterminal time;
* `deriv Fₙ` is interval-integrable on every compact strict interval
  `[s,t] ⊂ (a,T)`;
* one common `g ∈ L¹((a,T))` satisfies

      deriv Fₙ(t) ≤ g(t)

  for every cutoff and strict time.

The derivative itself is **not** required to belong to `L¹((a,T))`.  Only
local interval integrability is used for the fundamental theorem of calculus.
This distinction is essential for the PDE application: the localized viscous
part may contribute a large negative derivative near `T`, but that favorable
negative contribution need not be globally absolutely integrable.

The fundamental theorem gives

    Tail₃(t,n+1) - Tail₃(s,n+1)
      =
    ∫_s^t deriv Fₙ(r) dr
      ≤
    ∫_s^t g(r) dr

for `s ≤ t`.  The preceding one-sided criterion then yields terminal radial
compactness and continuation under the retained endpoint hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Common upper derivative majorant -/

/--
There is one globally integrable scalar profile which bounds every natural
sharp-tail derivative from above.

The derivatives themselves are required to be integrable only on each compact
strict subinterval, not globally on `(a,T)`.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
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
        ∀ s : ℝ,
          ∀ hs : s ∈ Set.Ioo a T,
            ∀ t : ℝ,
              ∀ ht : t ∈ Set.Ioo a T,
                s ≤ t
                  →
                IntervalIntegrable
                  (deriv
                    (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
                      hH3 hClass n))
                  volume
                  s
                  t
      )
        ∧
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo a T
            →
          deriv
              (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
                hH3 hClass n)
              t
            ≤
          g t
      )

/-! ## Upper derivative control gives forward increment control -/

/--
A common integrable upper derivative majorant gives the one-sided forward
increment majorant from the preceding checkpoint.
-/
theorem naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint_of_uniformIntegrableUpperDerivativeMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDerivative :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
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

  intro s hs t ht hst n

  let F : ℝ → ℝ :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath
      hH3 hClass n

  have hUIccSubset :
      Set.uIcc s t
        ⊆
      Set.Ioo a T := by

    intro r hr

    rw [uIcc_of_le hst] at hr

    exact
      ⟨
        lt_of_lt_of_le
          hs.1
          hr.1,
        lt_of_le_of_lt
          hr.2
          ht.2
      ⟩

  have hDiff :
      ∀ r : ℝ,
        r ∈ Set.uIcc s t
          →
        DifferentiableAt ℝ F r := by

    intro r hr

    dsimp only [F]

    exact
      (hCutoff n).1
        r
        (hUIccSubset hr)

  have hDerivInterval :
      IntervalIntegrable
        (deriv F)
        volume
        s
        t := by

    dsimp only [F]

    exact
      (hCutoff n).2.1
        s
        hs
        t
        ht
        hst

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
        hDiff
        hDerivInterval

  have hIntegralUpper :
      (∫ r in s..t, deriv F r)
        ≤
      ∫ r in s..t, g r := by

    apply
      intervalIntegral.integral_mono_on
        hst
        hDerivInterval
        hgInterval

    intro r hr

    dsimp only [F]

    exact
      (hCutoff n).2.2
        r
        ⟨
          lt_of_lt_of_le
            hs.1
            hr.1,
          lt_of_le_of_lt
            hr.2
            ht.2
        ⟩

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

  rw [hFT] at hIntegralUpper
  rw [hFs, hFt] at hIntegralUpper

  exact
    hIntegralUpper

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, a cutoff-independent integrable upper
bound on every natural sharp-tail derivative is sufficient for smooth
continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
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
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorant_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint_of_uniformIntegrableUpperDerivativeMajorant
        hH3
        hClass
        hDerivative)

/-! ## Nonextension obstruction -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out one
common terminal-`L¹` upper bound for all natural sharp-tail derivatives, even
though each derivative may remain locally interval-integrable on every strict
compact time interval.
-/
theorem not_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
        hH3 hClass := by

  intro hDerivative

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hDerivative)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or there is no cutoff-independent terminal-`L¹` profile bounding all natural
sharp-tail derivatives from above.
-/
theorem smoothContinuationExtension_or_not_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
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
        (not_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
