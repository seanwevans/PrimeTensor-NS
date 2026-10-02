import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Derivative.Majorant

/-!
# Spectral transfer density for canonical top-order radial-tail evolution

The preceding checkpoint reduced terminal radial compactness to one
cutoff-independent `L¹_t` majorant for the time derivatives of the natural
top-order radial tails.

This file removes the cutoff from that majorant in the natural spectral way.

Let `Φ(t,ξ)` be a real spectral transfer density.  Assume that for every
natural radial cutoff `n` and every strict preterminal time `t`,

    d/dt Tail₃(t,n+1)
      =
    ∫_{|D(ξ)| ≥ n+1} Φ(t,ξ) dξ.

Then

    |d/dt Tail₃(t,n+1)|
      ≤
    ∫ |Φ(t,ξ)| dξ,

and the right-hand side no longer depends on `n`.

Consequently, if

    t ↦ ∫ |Φ(t,ξ)| dξ

belongs to `L¹((a,T))`, the derivative-majorant criterion from the preceding
checkpoint applies and yields terminal radial compactness and continuation
under the retained endpoint hypotheses.

This is still a reduction.  The remaining Navier--Stokes task is to identify
the concrete transfer density `Φ` from the sharp Fourier-localized top-order
energy evolution and prove the stated spacetime `L¹` bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailTransfer
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalTopTailTransfer :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Abstract spectral transfer representation -/

/--
A spectral transfer density represents every natural radial-tail derivative
when integrating it over the corresponding sharp radial tail gives the
ordinary time derivative of the canonical tail path.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeRepresentedBy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (Φ : ℝ → H3FourierPoint3 → ℝ) : Prop :=
  ∀ n : ℕ,
    ∀ t : ℝ,
      ∀ ht : t ∈ Set.Ioo a T,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
            hH3 hClass n)
          (∫ ξ in
              (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
              Φ t ξ
            ∂volume)
          t

/--
Full-space absolute spectral transfer mass at one time.
-/
noncomputable def h3TerminalPhysicalTopDissipationTransferL1At
    (Φ : ℝ → H3FourierPoint3 → ℝ)
    (t : ℝ) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    abs (Φ t ξ)
    ∂volume

/--
Spacetime `L¹` control needed by the sharp-tail argument:

* each spatial transfer slice is integrable;
* its full absolute spatial mass is integrable in time on `(a,T)`.
-/
def H3TerminalPhysicalTopDissipationTransferSpacetimeL1
    (a T : ℝ)
    (Φ : ℝ → H3FourierPoint3 → ℝ) : Prop :=
  (
    ∀ t : ℝ,
      t ∈ Set.Ioo a T →
        Integrable
          (Φ t)
          volume
  )
    ∧
  IntegrableOn
    (h3TerminalPhysicalTopDissipationTransferL1At Φ)
    (Set.Ioo a T)
    volume

/-! ## Full spectral L¹ mass dominates every sharp cutoff derivative -/

/--
If `Φ` represents the sharp-tail derivatives and has the stated spacetime
`L¹` control, then its full spatial `L¹` mass is a common integrable derivative
majorant for every natural cutoff.
-/
theorem naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorantAtEndpoint_of_transferDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {Φ : ℝ → H3FourierPoint3 → ℝ}
    (hRep :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeRepresentedBy
        hH3 hClass Φ)
    (hL1 :
      H3TerminalPhysicalTopDissipationTransferSpacetimeL1
        a T Φ) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableDerivativeMajorantAtEndpoint
      hH3 hClass := by

  refine
    ⟨
      h3TerminalPhysicalTopDissipationTransferL1At Φ,
      hL1.2,
      ?_
    ⟩

  intro n

  constructor

  · intro t ht

    exact
      (hRep n t ht).differentiableAt

  · intro t ht

    let S : Set H3FourierPoint3 :=
      (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ

    have hDerivative :
        deriv
            (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
              hH3 hClass n)
            t
          =
        ∫ ξ in S,
          Φ t ξ
          ∂volume := by

      dsimp only [S]

      exact
        (hRep n t ht).deriv

    have hSpatialInt :
        Integrable
          (Φ t)
          volume :=
      hL1.1
        t
        ht

    have hNormBound :
        ‖∫ ξ in S,
            Φ t ξ
            ∂volume‖
          ≤
        ∫ ξ in S,
          ‖Φ t ξ‖
          ∂volume := by

      exact
        norm_integral_le_integral_norm
          (fun ξ : H3FourierPoint3 =>
            Φ t ξ)

    have hSetLeFullSet :
        (∫ ξ in S,
          ‖Φ t ξ‖
          ∂volume)
          ≤
        ∫ ξ in Set.univ,
          ‖Φ t ξ‖
          ∂volume := by

      apply
        setIntegral_mono_set

      · exact
          hSpatialInt.norm.integrableOn

      · exact
          Eventually.of_forall
            (fun ξ =>
              norm_nonneg
                (Φ t ξ))

      · exact
          Filter.Eventually.of_forall
            (fun ξ hξ =>
              Set.mem_univ ξ)

    have hSetLeFull :
        (∫ ξ in S,
          ‖Φ t ξ‖
          ∂volume)
          ≤
        ∫ ξ : H3FourierPoint3,
          ‖Φ t ξ‖
          ∂volume := by

      simpa only [setIntegral_univ] using
        hSetLeFullSet

    have hFull :
        (∫ ξ : H3FourierPoint3,
          ‖Φ t ξ‖
          ∂volume)
          =
        h3TerminalPhysicalTopDissipationTransferL1At
          Φ t := by

      unfold
        h3TerminalPhysicalTopDissipationTransferL1At

      apply integral_congr_ae

      filter_upwards with ξ

      exact
        Real.norm_eq_abs
          (Φ t ξ)

    rw [hDerivative]
    rw [← Real.norm_eq_abs]

    calc
      ‖∫ ξ in S,
          Φ t ξ
          ∂volume‖
          ≤
        ∫ ξ in S,
          ‖Φ t ξ‖
          ∂volume :=
            hNormBound

      _ ≤
        ∫ ξ : H3FourierPoint3,
          ‖Φ t ξ‖
          ∂volume :=
            hSetLeFull

      _ =
        h3TerminalPhysicalTopDissipationTransferL1At
          Φ t :=
            hFull

/-! ## Increment and continuation consequences -/

/--
A represented spacetime-integrable spectral transfer density gives the common
integrable increment majorant for all natural radial tails.
-/
theorem naturalTopDissipationRadialTailUniformIntegrableIncrementMajorantAtEndpoint_of_transferDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {Φ : ℝ → H3FourierPoint3 → ℝ}
    (hRep :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeRepresentedBy
        hH3 hClass Φ)
    (hL1 :
      H3TerminalPhysicalTopDissipationTransferSpacetimeL1
        a T Φ) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableIncrementMajorantAtEndpoint
      hH3 hClass := by

  exact
    naturalTopDissipationRadialTailUniformIntegrableIncrementMajorantAtEndpoint_of_uniformIntegrableDerivativeMajorant
      hH3
      hClass
      (naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorantAtEndpoint_of_transferDensity
        hH3
        hClass
        hRep
        hL1)

/--
Under the retained endpoint hypotheses, a represented spectral transfer
density with finite spacetime `L¹` mass forces smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_topDissipationTransferDensity_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {Φ : ℝ → H3FourierPoint3 → ℝ}
    (hRep :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeRepresentedBy
        hH3 hClass Φ)
    (hL1 :
      H3TerminalPhysicalTopDissipationTransferSpacetimeL1
        a T Φ) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalTopDissipationRadialTailUniformIntegrableDerivativeMajorantAtEndpoint_of_transferDensity
        hH3
        hClass
        hRep
        hL1)

/-! ## Nonextension obstruction and neutral formulation -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension rules out
every represented transfer density whose full absolute spectral mass is
integrable in time.
-/
theorem not_transferSpacetimeL1_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {Φ : ℝ → H3FourierPoint3 → ℝ}
    (hRep :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeRepresentedBy
        hH3 hClass Φ) :
    ¬ H3TerminalPhysicalTopDissipationTransferSpacetimeL1
        a T Φ := by

  intro hL1

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_topDissipationTransferDensity_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hRep
        hL1)

/--
Neutral endpoint alternative for any concrete represented spectral transfer
density `Φ`: either the path extends smoothly through `T`, or `Φ` fails the
required spacetime `L¹` control.
-/
theorem smoothContinuationExtension_or_not_topDissipationTransferSpacetimeL1
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {Φ : ℝ → H3FourierPoint3 → ℝ}
    (hRep :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeRepresentedBy
        hH3 hClass Φ) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    ¬ H3TerminalPhysicalTopDissipationTransferSpacetimeL1
        a T Φ := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (not_transferSpacetimeL1_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy
          hRep)

end

end Euclidean
end Bridge
end PrimeTensor
