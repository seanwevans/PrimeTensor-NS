import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Integral.Majorant

/-!
# Integrable scalar majorants close the terminal radial-tail Cauchy condition

The preceding checkpoint reduced uniform temporal Cauchy control of every
canonical natural top-order radial tail to one scalar time profile `g` whose
interval integrals vanish at the terminal time and which majorizes all radial
cutoff increments.

This file discharges the scalar terminal-vanishing condition from ordinary
Lebesgue integrability:

    g ∈ L¹((a,T))

implies that

    |∫_s^t g(r) dr| → 0

uniformly as both strict times `s,t → T`.

The proof uses continuity of the indefinite interval integral on `[a,T]`.
Consequently, the remaining dynamic frontier is reduced to one statement:
construct a cutoff-independent `L¹` time majorant for every canonical
radial-tail increment directly from the Navier--Stokes evolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Integrability gives terminal interval-integral vanishing -/

/--
An `L¹` scalar profile on the strict terminal interval has vanishing interval
integrals when both endpoints approach `T` from inside `(a,T)`.
-/
theorem scalarIntervalIntegralVanishingAtEndpoint_of_integrableOn
    {a T : ℝ}
    {g : ℝ → ℝ}
    (haT : a < T)
    (hg : IntegrableOn g (Set.Ioo a T) volume) :
    H3TerminalScalarIntervalIntegralVanishingAtEndpoint a T g := by

  intro δ hδ

  have hInterval :
      IntervalIntegrable g volume a T := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le haT.le]
    exact hg

  let P : ℝ → ℝ :=
    fun x => ∫ r in a..x, g r

  have hPContinuous :
      ContinuousOn P (Set.uIcc a T) := by
    dsimp only [P]
    exact
      intervalIntegral.continuousOn_primitive_interval'
        hInterval
        left_mem_uIcc

  have hTmem :
      T ∈ Set.uIcc a T :=
    right_mem_uIcc

  have hPContinuousAtT :
      ContinuousWithinAt P (Set.uIcc a T) T :=
    hPContinuous T hTmem

  obtain
    ⟨
      η,
      hη,
      hNear
    ⟩ :=
    (Metric.continuousWithinAt_iff.mp hPContinuousAtT)
      (δ / 2)
      (by positivity)

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro s hs t ht hsNear htNear

  have hsU :
      s ∈ Set.uIcc a T := by
    rw [uIcc_of_le haT.le]
    exact
      ⟨
        hs.1.le,
        hs.2.le
      ⟩

  have htU :
      t ∈ Set.uIcc a T := by
    rw [uIcc_of_le haT.le]
    exact
      ⟨
        ht.1.le,
        ht.2.le
      ⟩

  have hsP :
      dist (P s) (P T) < δ / 2 :=
    hNear
      hsU
      hsNear

  have htP :
      dist (P t) (P T) < δ / 2 :=
    hNear
      htU
      htNear

  have hAs :
      IntervalIntegrable g volume a s := by
    apply
      hInterval.mono_set
    rw [
      uIcc_of_le haT.le,
      uIcc_of_le hs.1.le
    ]
    exact
      Icc_subset_Icc
        le_rfl
        hs.2.le

  have hAt :
      IntervalIntegrable g volume a t := by
    apply
      hInterval.mono_set
    rw [
      uIcc_of_le haT.le,
      uIcc_of_le ht.1.le
    ]
    exact
      Icc_subset_Icc
        le_rfl
        ht.2.le

  have hIncrement :
      P t - P s
        =
      ∫ r in s..t, g r := by
    dsimp only [P]
    exact
      intervalIntegral.integral_interval_sub_left
        hAt
        hAs

  rw [← hIncrement]
  rw [← Real.dist_eq]

  calc
    dist (P t) (P s)
        ≤
      dist (P t) (P T) + dist (P T) (P s) :=
        dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by
      exact
        add_lt_add
          htP
          (by
            simpa only [dist_comm] using
              hsP)
    _ = δ := by
      ring

/-! ## Integrable common majorants -/

/--
There exists one `L¹((a,T))` scalar profile which majorizes the temporal
increment of every canonical natural top-order radial tail uniformly in the
cutoff index.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ g : ℝ → ℝ,
    IntegrableOn g (Set.Ioo a T) volume
      ∧
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIncrementMajorizedBy
      hH3 hClass g

/--
An integrable common increment majorant automatically supplies the scalar
terminal-integral majorant from the preceding checkpoint.
-/
theorem naturalTopDissipationRadialTailUniformIntegralMajorantAtEndpoint_of_integrableIncrementMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegralMajorantAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      g,
      hg,
      hIncrement
    ⟩ :=
    hMajorant

  refine
    ⟨
      g,
      ?_,
      hIncrement
    ⟩

  exact
    scalarIntervalIntegralVanishingAtEndpoint_of_integrableOn
      hClass.terminal_start.2
      hg

/--
An integrable common increment majorant forces uniform temporal Cauchy control
of every canonical natural top-order radial tail.
-/
theorem naturalTopDissipationRadialTailUniformTemporalCauchy_of_integrableIncrementMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
      hH3 hClass := by

  exact
    naturalTopDissipationRadialTailUniformTemporalCauchy_of_uniformIntegralMajorantAtEndpoint
      hH3
      hClass
      (naturalTopDissipationRadialTailUniformIntegralMajorantAtEndpoint_of_integrableIncrementMajorant
        hH3
        hClass
        hMajorant)

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, a single cutoff-independent integrable
scalar majorant for all canonical natural radial-tail increments is sufficient
for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableIncrementMajorant_of_actualVorticityStrongH3EndpointPath
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
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegralMajorant_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalTopDissipationRadialTailUniformIntegralMajorantAtEndpoint_of_integrableIncrementMajorant
        hH3
        hClass
        hMajorant)

/-! ## Nonextension obstruction -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out a
single cutoff-independent `L¹` majorant of all canonical natural radial-tail
increments.
-/
theorem not_naturalTopDissipationRadialTailUniformIntegrableIncrementMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
        hH3 hClass := by

  intro hMajorant

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableIncrementMajorant_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hMajorant)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or no single `L¹((a,T))` scalar time profile can majorize every canonical
natural top-order radial-tail increment uniformly in the cutoff index.
-/
theorem smoothContinuationExtension_or_not_naturalTopDissipationRadialTailUniformIntegrableIncrementMajorantAtEndpoint
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
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
        (not_naturalTopDissipationRadialTailUniformIntegrableIncrementMajorant_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
