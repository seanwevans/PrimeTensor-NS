import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Integral.Integrable

/-!
# One-sided temporal control of canonical top-order radial tails

The symmetric temporal-Cauchy route controls

    |Tail₃(t,n+1) - Tail₃(s,n+1)|.

For the Navier--Stokes evolution this is stronger than necessary.  The
localized viscous contribution has the favorable sign, so forcing an absolute
derivative estimate would spend regularity merely to control a term which can
instead be discarded.

To obtain terminal uniform tail decay, choose one fixed late anchor time `s`.
It is enough to control only later *increases*:

    Tail₃(t,n+1) - Tail₃(s,n+1)
      ≤
    ∫_s^t g(r) dr

for `s ≤ t`, uniformly in `n`, with one `g ∈ L¹((a,T))`.

The fixed-time tail at the anchor is small for all sufficiently large natural
cutoffs.  Integrability of `g` makes its terminal interval integrals small, and
a smaller terminal neighborhood guarantees that every target time lies after
the anchor.  Therefore the one-sided estimate alone yields terminal uniform
radial-tail vanishing.

This is the appropriate interface for the localized PDE energy identity:
negative diffusion need not enter the eventual majorant at all.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## One-sided common increment majorant -/

/--
One scalar profile controls every *forward increase* of every canonical
natural-cutoff top-order radial tail.

No absolute value is imposed, and the estimate is required only when `s ≤ t`.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformForwardIncrementMajorizedBy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (g : ℝ → ℝ) : Prop :=
  ∀ s : ℝ,
    ∀ hs : s ∈ Set.Ioo a T,
      ∀ t : ℝ,
        ∀ ht : t ∈ Set.Ioo a T,
          s ≤ t
            →
          ∀ n : ℕ,
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass t ht ((n : ℝ) + 1)
              -
            h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass s hs ((n : ℝ) + 1)
              ≤
            ∫ r in s..t, g r

/--
There is one `L¹((a,T))` scalar profile controlling every forward natural-tail
increase uniformly in the cutoff.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ g : ℝ → ℝ,
    IntegrableOn g (Set.Ioo a T) volume
      ∧
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformForwardIncrementMajorizedBy
      hH3 hClass g

/-! ## One-sided control already gives terminal uniform tail decay -/

/--
A single integrable common majorant for forward tail increases upgrades the
fixed-time tail decay to terminal uniform tail decay.

The proof chooses one late anchor `s = T-r`.  The final neighborhood is made
strictly smaller than `r`, so every target time in that neighborhood satisfies
`s ≤ t`; no backward increment estimate is needed.
-/
theorem naturalRadialTailUniformVanishingAtEndpoint_of_integrableForwardIncrementMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      g,
      hg,
      hForward
    ⟩ :=
    hMajorant

  intro δ hδ

  have hIntegralVanishing :
      H3TerminalScalarIntervalIntegralVanishingAtEndpoint
        a T g :=
    scalarIntervalIntegralVanishingAtEndpoint_of_integrableOn
      hClass.terminal_start.2
      hg

  obtain
    ⟨
      η₀,
      hη₀,
      hIntegralSmall
    ⟩ :=
    hIntegralVanishing
      (δ / 2)
      (by positivity)

  let r : ℝ :=
    min
      (η₀ / 2)
      ((T - a) / 2)

  have hTa :
      0 < T - a :=
    sub_pos.mpr
      hClass.terminal_start.2

  have hr :
      0 < r := by

    dsimp only [r]

    exact
      lt_min
        (by positivity)
        (by positivity)

  have hrη :
      r ≤ η₀ / 2 := by

    dsimp only [r]

    exact
      min_le_left
        (η₀ / 2)
        ((T - a) / 2)

  have hrTa :
      r ≤ (T - a) / 2 := by

    dsimp only [r]

    exact
      min_le_right
        (η₀ / 2)
        ((T - a) / 2)

  let s : ℝ :=
    T - r

  have hs :
      s ∈ Set.Ioo a T := by

    constructor

    · dsimp only [s]
      linarith

    · dsimp only [s]
      linarith

  have hsNear :
      dist s T < η₀ := by

    have hrη' :
        r < η₀ := by
      linarith

    calc
      dist s T = r := by
        rw [Real.dist_eq]
        dsimp only [s]
        have hSub :
            T - r - T = -r := by
          ring
        rw [
          hSub,
          abs_neg,
          abs_of_nonneg (le_of_lt hr)
        ]

      _ < η₀ := hrη'

  have hFixed :=
    h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
      hH3
      hClass
      hs

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalPhysicalTopDissipationRadialTailMassAt
            hH3 hClass s hs ((n : ℝ) + 1)
          <
        δ / 2 :=
    hFixed.eventually
      (Iio_mem_nhds
        (by positivity))

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    eventually_atTop.1
      hEventually

  let η : ℝ :=
    min
      (r / 2)
      (η₀ / 2)

  have hη :
      0 < η := by

    dsimp only [η]

    exact
      lt_min
        (by positivity)
        (by positivity)

  have hηr :
      η ≤ r / 2 := by

    dsimp only [η]

    exact
      min_le_left
        (r / 2)
        (η₀ / 2)

  have hηη₀ :
      η ≤ η₀ / 2 := by

    dsimp only [η]

    exact
      min_le_right
        (r / 2)
        (η₀ / 2)

  refine
    ⟨
      N,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear n hn

  have htNear₀ :
      dist t T < η₀ := by

    have hηη₀' :
        η < η₀ := by
      linarith

    exact
      lt_trans
        htNear
        hηη₀'

  have htDistance :
      dist t T = T - t := by

    rw [Real.dist_eq]

    have hNonpos :
        t - T ≤ 0 := by
      linarith [ht.2]

    rw [
      abs_of_nonpos hNonpos
    ]

    ring

  have hst :
      s ≤ t := by

    have hNearR :
        T - t < r / 2 := by

      rw [← htDistance]

      exact
        lt_of_lt_of_le
          htNear
          hηr

    dsimp only [s]

    linarith

  have hAnchor :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass s hs ((n : ℝ) + 1)
        <
      δ / 2 :=
    hN
      n
      hn

  have hIntegral :
      abs (∫ r in s..t, g r)
        <
      δ / 2 :=
    hIntegralSmall
      s
      hs
      t
      ht
      hsNear
      htNear₀

  have hIntegralUpper :
      (∫ r in s..t, g r)
        <
      δ / 2 := by

    exact
      lt_of_le_of_lt
        (le_abs_self
          (∫ r in s..t, g r))
        hIntegral

  have hIncrease :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass t ht ((n : ℝ) + 1)
        -
      h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass s hs ((n : ℝ) + 1)
        ≤
      ∫ r in s..t, g r :=
    hForward
      s
      hs
      t
      ht
      hst
      n

  linarith

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, one integrable common upper control on
forward top-tail increments is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorant_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformVanishing_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalRadialTailUniformVanishingAtEndpoint_of_integrableForwardIncrementMajorant
        hH3
        hClass
        hMajorant)

/-! ## Nonextension obstruction -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out a
single integrable common upper control of all forward natural-tail increments.
-/
theorem not_naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
        hH3 hClass := by

  intro hMajorant

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorant_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hMajorant)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or there is no cutoff-independent `L¹((a,T))` profile controlling every
forward increase of the canonical natural top-order radial tails.
-/
theorem smoothContinuationExtension_or_not_naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableForwardIncrementMajorantAtEndpoint
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
        (not_naturalTopDissipationRadialTailUniformIntegrableForwardIncrementMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
