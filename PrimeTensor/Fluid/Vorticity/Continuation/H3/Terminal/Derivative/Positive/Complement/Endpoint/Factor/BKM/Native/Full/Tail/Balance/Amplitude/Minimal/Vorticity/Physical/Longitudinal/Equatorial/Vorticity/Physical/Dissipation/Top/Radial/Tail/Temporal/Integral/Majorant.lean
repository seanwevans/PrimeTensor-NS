import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Cauchy

/-!
# Scalar integral majorants for terminal top-order radial-tail increments

The preceding checkpoint reduced terminal top-order radial compactness to
uniform temporal Cauchy control of the canonical natural radial tails

    Tail₃(t,n+1).

This file removes the cutoff index from the temporal estimate.

Suppose there is one scalar time profile `g` such that every cutoff-tail
increment obeys

    |Tail₃(s,n+1) - Tail₃(t,n+1)|
      ≤
    |∫_s^t g(r) dr|

for every natural cutoff `n`.

If the interval integrals of `g` vanish uniformly as both endpoints approach
the terminal time, then the entire family of radial tails is uniformly Cauchy
in time.  The previous checkpoint then yields terminal uniform radial-tail
decay and smooth continuation under the retained endpoint hypotheses.

Thus the remaining dynamic target can be stated without any frequency cutoff:

* construct one scalar majorant `g` from the Navier--Stokes top-order
  tail/flux evolution;
* prove that its terminal interval integrals vanish.

A later checkpoint may discharge the second item from an `L¹`-type
integrability statement for `g`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Scalar terminal interval-integral vanishing -/

/--
A scalar time profile has vanishing terminal interval integrals when, for every
positive tolerance, the integral between any two sufficiently late strict
preterminal times is smaller than that tolerance in absolute value.
-/
def H3TerminalScalarIntervalIntegralVanishingAtEndpoint
    (a T : ℝ)
    (g : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ s : ℝ,
        s ∈ Set.Ioo a T
          →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T
            →
          dist s T < η
            →
          dist t T < η
            →
          abs (∫ r in s..t, g r) < δ

/-! ## One common scalar majorant for every natural cutoff -/

/--
One scalar time profile majorizes the temporal increment of every canonical
natural top-order radial tail, uniformly in the cutoff index.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIncrementMajorizedBy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (g : ℝ → ℝ) : Prop :=
  ∀ s : ℝ,
    ∀ hs : s ∈ Set.Ioo a T,
      ∀ t : ℝ,
        ∀ ht : t ∈ Set.Ioo a T,
          ∀ n : ℕ,
            abs
                (
                  h3TerminalPhysicalTopDissipationRadialTailMassAt
                      hH3 hClass s hs ((n : ℝ) + 1)
                    -
                  h3TerminalPhysicalTopDissipationRadialTailMassAt
                    hH3 hClass t ht ((n : ℝ) + 1)
                )
              ≤
            abs (∫ r in s..t, g r)

/--
There exists one scalar time profile whose terminal interval integrals vanish
and which simultaneously majorizes all natural radial-tail increments.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegralMajorantAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ g : ℝ → ℝ,
    H3TerminalScalarIntervalIntegralVanishingAtEndpoint a T g
      ∧
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIncrementMajorizedBy
      hH3 hClass g

/-! ## The scalar majorant implies uniform temporal Cauchy control -/

/--
A common scalar increment majorant with vanishing terminal interval integrals
forces the canonical natural top-order radial tails to be terminal Cauchy in
time uniformly over every natural cutoff.
-/
theorem naturalTopDissipationRadialTailUniformTemporalCauchy_of_scalarIntegralMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {g : ℝ → ℝ}
    (hVanishing :
      H3TerminalScalarIntervalIntegralVanishingAtEndpoint a T g)
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIncrementMajorizedBy
        hH3 hClass g) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
      hH3 hClass := by

  intro δ hδ

  obtain
    ⟨
      η,
      hη,
      hSmall
    ⟩ :=
    hVanishing
      δ
      hδ

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro s hs t ht hsNear htNear n

  exact
    lt_of_le_of_lt
      (hMajorant
        s
        hs
        t
        ht
        n)
      (hSmall
        s
        hs
        t
        ht
        hsNear
        htNear)

/--
Existential packaged form of the scalar-majorant reduction.
-/
theorem naturalTopDissipationRadialTailUniformTemporalCauchy_of_uniformIntegralMajorantAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegralMajorantAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      g,
      hVanishing,
      hIncrement
    ⟩ :=
    hMajorant

  exact
    naturalTopDissipationRadialTailUniformTemporalCauchy_of_scalarIntegralMajorant
      hH3
      hClass
      hVanishing
      hIncrement

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, one common scalar terminal-integral
majorant for every canonical top-order radial-tail increment is sufficient for
smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegralMajorant_of_actualVorticityStrongH3EndpointPath
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
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegralMajorantAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformTemporalCauchy_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalTopDissipationRadialTailUniformTemporalCauchy_of_uniformIntegralMajorantAtEndpoint
        hH3
        hClass
        hMajorant)

/-! ## Nonextension obstruction -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out
every common scalar terminal-integral majorant of the canonical natural
top-order radial-tail increments.
-/
theorem not_naturalTopDissipationRadialTailUniformIntegralMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegralMajorantAtEndpoint
        hH3 hClass := by

  intro hMajorant

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegralMajorant_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hMajorant)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or no single scalar time profile with vanishing terminal interval integrals can
majorize every canonical natural top-order radial-tail increment.

This exposes a cutoff-free dynamic frontier for the Navier--Stokes evolution.
-/
theorem smoothContinuationExtension_or_not_naturalTopDissipationRadialTailUniformIntegralMajorantAtEndpoint
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegralMajorantAtEndpoint
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
        (not_naturalTopDissipationRadialTailUniformIntegralMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
