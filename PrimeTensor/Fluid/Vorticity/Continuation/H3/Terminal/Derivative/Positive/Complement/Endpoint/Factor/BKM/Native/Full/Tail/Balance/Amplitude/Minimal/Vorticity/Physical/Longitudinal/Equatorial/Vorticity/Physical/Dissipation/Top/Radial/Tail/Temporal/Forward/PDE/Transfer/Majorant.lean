import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Split
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Regularity

/-!
# Cutoff-independent full-space nonlinear-transfer majorant

The exact localized top-tail PDE balance and local derivative integrability are
now closed.  The remaining PDE-facing continuation condition asks for one
terminal-`L¹` scalar profile which bounds every sharp-tail nonlinear transfer
from above, uniformly in the natural cutoff.

This file removes the cutoff from that problem completely.

At a strict time, for coordinate `j`, define the signed nonlinear density

    q(ξ)^4 Re ⟪û_j(ξ), F_j(U,U)(ξ)⟫.

The previous split theorem proves this density is integrable on the whole
Fourier space.  Hence every restricted tail integral is bounded by the
full-space integral of its absolute value.  Summing the three coordinates gives
the explicit cutoff-independent profile

    G(t)
      =
    2 Σ_j ∫ q^4
      |Re ⟪û_j, F_j(U,U)⟫|.

For every radius `R`,

    nonlinearTransfer(t,R) ≤ G(t).

Thus no cutoff-dependent estimate remains.  Smooth continuation follows if
this single concrete full-space profile belongs to `L¹((a,T))`.

This file does not assert that terminal time-integrability.  It isolates it as
the remaining scalar analytic obstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailTransferMajorant
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Full-space signed and absolute nonlinear densities -/

/--
One coordinate of the strict-time signed top-order nonlinear Fourier density.
-/
noncomputable def h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3FourierGradientSquare ξ ^ 4
    *
  (
    inner ℂ
      (h3SpectralScalarRawFourierL2
        (U j) ξ)
      (h3RawFinLerayOuterProductDivergence
        U U j ξ)
  ).re

/--
The strict-time coordinate nonlinear density is integrable on the whole
Fourier space.
-/
theorem integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    Integrable
      (h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
        hH3 hClass ht j)
      (volume : Measure H3FourierPoint3) := by

  unfold
    h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt

  simpa using
    (
      integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
        hH3 hClass ht j
    )

/--
One coordinate of the full-space absolute nonlinear-transfer majorant.
-/
noncomputable def h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  2
    *
  ∫ ξ : H3FourierPoint3,
    abs
      (
        h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j ξ
      )
    ∂(volume : Measure H3FourierPoint3)

/--
The complete full-space absolute nonlinear-transfer majorant at one strict
time.
-/
noncomputable def h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) : ℝ :=
  ∑ j : Fin 3,
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
      hH3 hClass ht j

/--
Global scalar extension of the strict-time full-space absolute nonlinear
transfer.  It is zero outside the physical interval.
-/
noncomputable def h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht
  else
    0

theorem h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
        hH3 hClass t
      =
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht := by

  unfold
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile

  rw [dif_pos ht]

/-! ## Every sharp tail is bounded by the full-space absolute profile -/

/--
For one coordinate, every sharp radial-tail nonlinear transfer is bounded above
by the corresponding full-space absolute transfer.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt_le_fullAbsolute
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
        hH3 hClass ht R j
      ≤
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
      hH3 hClass ht j := by

  let f : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
      hH3 hClass ht j

  let μR : Measure H3FourierPoint3 :=
    (volume : Measure H3FourierPoint3).restrict
      (h3TerminalRadialFrequencyBelow R)ᶜ

  have hFull :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
        hH3 hClass ht j

  have hAbsFull :
      Integrable
        (fun ξ : H3FourierPoint3 => abs (f ξ))
        (volume : Measure H3FourierPoint3) := by
    simpa only [Real.norm_eq_abs] using
      hFull.norm

  have hAbsIntegral :
      abs
          (
            ∫ ξ : H3FourierPoint3,
              f ξ
              ∂μR
          )
        ≤
      ∫ ξ : H3FourierPoint3,
        abs (f ξ)
        ∂μR := by

    simpa only [Real.norm_eq_abs] using
      (
        abs_integral_le_integral_abs
          (μ := μR)
          (f := f)
      )

  have hTailAbs_le_fullAbs :
      (
        ∫ ξ : H3FourierPoint3,
          abs (f ξ)
          ∂μR
      )
        ≤
      ∫ ξ : H3FourierPoint3,
        abs (f ξ)
        ∂(volume : Measure H3FourierPoint3) := by

    exact
      integral_mono_measure
        Measure.restrict_le_self
        (Filter.Eventually.of_forall
          (fun ξ : H3FourierPoint3 =>
            abs_nonneg (f ξ)))
        hAbsFull

  have hRateEq :
      h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
          hH3 hClass ht R j
        =
      (-2 : ℝ)
        *
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂μR := by

    unfold
      h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt

    dsimp only [f, μR]

    rfl

  have hMajorEq :
      h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
          hH3 hClass ht j
        =
      2
        *
      ∫ ξ : H3FourierPoint3,
        abs (f ξ)
        ∂(volume : Measure H3FourierPoint3) := by

    unfold
      h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt

    dsimp only [f]

  rw [hRateEq, hMajorEq]

  calc
    (-2 : ℝ)
        *
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂μR
        =
      2
        *
      (
        -
        ∫ ξ : H3FourierPoint3,
          f ξ
          ∂μR
      ) := by
        ring

    _ ≤
      2
        *
      abs
        (
          ∫ ξ : H3FourierPoint3,
            f ξ
            ∂μR
        ) := by

      gcongr

      exact
        neg_le_abs
          (
            ∫ ξ : H3FourierPoint3,
              f ξ
              ∂μR
          )

    _ ≤
      2
        *
      ∫ ξ : H3FourierPoint3,
        abs (f ξ)
        ∂μR := by

      gcongr

    _ ≤
      2
        *
      ∫ ξ : H3FourierPoint3,
        abs (f ξ)
        ∂(volume : Measure H3FourierPoint3) := by

      gcongr

/--
The complete sharp-tail nonlinear transfer is bounded above by the same
full-space absolute profile for every radial cutoff.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt_le_fullAbsolute
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht R
      ≤
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
      hH3 hClass ht := by

  unfold
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt

  apply
    Finset.sum_le_sum

  intro j hj

  exact
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt_le_fullAbsolute
      hH3 hClass ht j

/--
At a strict time, every natural sharp-tail transfer is bounded by the global
profile value, independently of the cutoff index.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt_le_fullAbsoluteProfile
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (n : ℕ) :
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht ((n : ℝ) + 1)
      ≤
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
      hH3 hClass t := by

  rw [
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile_eq
      hH3 hClass ht
  ]

  exact
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt_le_fullAbsolute
      hH3 hClass ht

/-! ## Reduce the remaining continuation frontier to one explicit scalar L¹ fact -/

/--
Terminal integrability of the concrete full-space absolute transfer profile
implies the previously isolated cutoff-uniform nonlinear-transfer upper-bound
condition.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint_of_fullAbsoluteProfile
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hProfile :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint
      hH3 hClass := by

  refine
    ⟨
      h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
        hH3 hClass,
      hProfile,
      ?_
    ⟩

  intro n t ht

  exact
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt_le_fullAbsoluteProfile
      hH3 hClass ht n

/--
With the exact localized PDE balance and local derivative integrability already
closed, terminal `L¹` integrability of the explicit full-space absolute
nonlinear-transfer profile is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fullAbsoluteTopTailNonlinearTransferProfileIntegrable_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hProfile :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_localizedTopTailPDEBalance_of_nonlinearTransferUpperBound_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (
        h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed
          hH3 hClass
      )
      (
        h3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable_closed
          hH3 hClass
      )
      (
        h3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint_of_fullAbsoluteProfile
          hH3 hClass hProfile
      )

/--
Neutral final reduction: under the retained endpoint hypotheses, either the
path extends smoothly or the explicit full-space absolute nonlinear-transfer
profile is not terminal-integrable.
-/
theorem smoothContinuationExtension_or_not_integrableOn_fullAbsoluteTopTailNonlinearTransferProfile
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
    ¬
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume := by

  classical

  by_cases hProfile :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume

  · exact
      Or.inl
        (
          smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fullAbsoluteTopTailNonlinearTransferProfileIntegrable_of_actualVorticityStrongH3EndpointPath
            hH3
            hClass
            hPhysical
            hCauchy
            hProfile
        )

  · exact
      Or.inr hProfile

end

end Euclidean
end Bridge
end PrimeTensor
