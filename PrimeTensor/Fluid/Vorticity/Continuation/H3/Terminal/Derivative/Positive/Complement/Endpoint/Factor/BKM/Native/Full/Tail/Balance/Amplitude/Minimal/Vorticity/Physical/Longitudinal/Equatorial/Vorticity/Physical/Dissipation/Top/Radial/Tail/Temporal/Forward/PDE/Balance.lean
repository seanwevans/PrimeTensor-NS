import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.State
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fifth.Radial.Moment.Criterion

/-!
# One-sided sharp-tail PDE balance

The preceding checkpoints reduced terminal top-radial compactness to one
cutoff-independent integrable *upper* bound for the derivatives of the sharp
natural tails.

This file isolates the exact PDE quantities which enter that upper bound.

For a strict preterminal slice, write

    q(ξ) = h3FourierGradientSquare ξ

and let `U(t)` be the canonical weighted H³ spectral state.  The normalized
raw-Fourier Navier--Stokes equation already has the sign convention

    raw(U)' = Δ̂ raw(U) - F(U,U).

Consequently the formal derivative of

    Tail₃(t,R) = ∫_{|D| ≥ R} q⁴ |raw(U)|²

splits as

    diffusion + nonlinear transfer,

where

    diffusion
      = -2 ∫_{|D| ≥ R} q⁵ |raw(U)|²
      ≤ 0

and

    nonlinear transfer
      = -2 Σⱼ ∫_{|D| ≥ R}
          q⁴ Re ⟪raw(Uⱼ), Fⱼ(U,U)⟫.

The diffusion sign is proved here directly from pointwise nonnegativity of
`q` and the Fourier mass density.  No absolute value of the diffusion term is
taken, and no terminal fifth-moment bound is assumed.

We then package the exact localized derivative identity as a visible frontier.
Once that identity and local interval-integrability of the derivatives are
available, a single `L¹((a,T))` upper bound for the concrete nonlinear transfer
rates implies the one-sided derivative criterion from the previous file, hence
terminal radial compactness.

Thus after this checkpoint the PDE-facing frontier is exactly:

1. prove the localized sharp-tail derivative identity;
2. dominate the concrete nonlinear transfer from above by one terminal
   integrable scalar profile.

The favorable diffusion term has disappeared from the majorant problem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForwardPDEBalance
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Concrete localized diffusion rate -/

/--
The fifth-radial mass restricted to the sharp radial tail.

Writing this as an ordinary integral against the restricted measure avoids
putting any terminal fifth-moment integrability into the definition.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailFifthMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3TerminalPhysicalFifthRadialDensityAt
      hH3 hClass t ht ξ
    ∂(volume.restrict
      (h3TerminalRadialFrequencyBelow R)ᶜ)

/--
The unit-viscosity contribution to the derivative of the canonical top-order
radial tail.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) : ℝ :=
  (-2 : ℝ)
    *
  h3TerminalPhysicalTopDissipationRadialTailFifthMassAt
    hH3 hClass ht R

/--
The localized unit-viscosity top-tail diffusion rate is always nonpositive.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt_nonpos
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) :
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
        hH3 hClass ht R
      ≤
    0 := by

  have hTailFifthNonneg :
      0
        ≤
      h3TerminalPhysicalTopDissipationRadialTailFifthMassAt
        hH3 hClass ht R := by

    unfold
      h3TerminalPhysicalTopDissipationRadialTailFifthMassAt

    exact
      integral_nonneg
        (fun ξ =>
          h3TerminalPhysicalFifthRadialDensityAt_nonneg
            hH3 hClass t ht ξ)

  unfold
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt

  exact
    mul_nonpos_of_nonpos_of_nonneg
      (by norm_num)
      hTailFifthNonneg

/-! ## Concrete localized nonlinear transfer -/

/--
One coordinate of the nonlinear contribution to the sharp top-tail derivative,
with the sign inherited from

    raw(U)' = Δ̂ raw(U) - F(U,U).
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ)
    (j : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs
  (-2 : ℝ)
    *
  ∫ ξ : H3FourierPoint3,
    h3FourierGradientSquare ξ ^ 4
      *
    (
      inner ℂ
        (h3SpectralScalarRawFourierL2
          (U j) ξ)
        (h3RawFinLerayOuterProductDivergence
          U U j ξ)
    ).re
    ∂(volume.restrict
      (h3TerminalRadialFrequencyBelow R)ᶜ)

/--
The complete nonlinear sharp-tail transfer is the sum of the three coordinate
transfer rates.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) : ℝ :=
  ∑ j : Fin 3,
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
      hH3 hClass ht R j

/-! ## Exact localized balance frontier -/

/--
The canonical natural-cutoff tails satisfy the exact localized
Navier--Stokes energy balance.

Differentiability is included explicitly because equality involving `deriv`
alone would not certify that the ordinary derivative actually exists.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ n : ℕ,
    ∀ t : ℝ,
      ∀ ht : t ∈ Set.Ioo a T,
        DifferentiableAt ℝ
          (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
            hH3 hClass n)
          t
          ∧
        deriv
            (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
              hH3 hClass n)
            t
          =
        h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
            hH3 hClass ht ((n : ℝ) + 1)
          +
        h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
          hH3 hClass ht ((n : ℝ) + 1)

/--
Local strict-time interval integrability of every canonical tail derivative.

This is deliberately only local on compact strict subintervals; no global
`L¹((a,T))` assumption is imposed on the derivative itself.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ n : ℕ,
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

/--
One terminal-integrable scalar profile bounds every concrete nonlinear
sharp-tail transfer rate from above, uniformly in the natural cutoff.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ g : ℝ → ℝ,
    IntegrableOn g (Set.Ioo a T) volume
      ∧
    ∀ n : ℕ,
      ∀ t : ℝ,
        ∀ ht : t ∈ Set.Ioo a T,
          h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
              hH3 hClass ht ((n : ℝ) + 1)
            ≤
          g t

/-! ## Diffusion is discarded in the upper derivative estimate -/

/--
The exact localized PDE balance bounds every sharp-tail derivative from above
by its nonlinear transfer contribution alone.
-/
theorem deriv_naturalTopDissipationRadialTail_le_nonlinearTransfer_of_localizedPDEBalance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hBalance :
      H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
        hH3 hClass)
    (n : ℕ)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T) :
    deriv
        (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
          hH3 hClass n)
        t
      ≤
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
      hH3 hClass ht ((n : ℝ) + 1) := by

  have hExact :=
    (hBalance n t ht).2

  have hDiffusion :=
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt_nonpos
      hH3 hClass ht ((n : ℝ) + 1)

  rw [hExact]

  linarith

/-! ## Concrete nonlinear-transfer criterion implies continuation -/

/--
The exact localized PDE balance, local strict-time derivative integrability,
and one common terminal-`L¹` upper bound for the concrete nonlinear transfer
produce the abstract upper-derivative majorant from the preceding checkpoint.
-/
theorem naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint_of_localizedPDEBalance_of_nonlinearTransferUpperBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hBalance :
      H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
        hH3 hClass)
    (hLocal :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable
        hH3 hClass)
    (hTransfer :
      H3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
      hH3 hClass := by

  obtain
    ⟨
      g,
      hg,
      hUpper
    ⟩ :=
    hTransfer

  refine
    ⟨
      g,
      hg,
      ?_
    ⟩

  intro n

  refine
    ⟨
      ?_,
      ?_,
      ?_
    ⟩

  · intro t ht

    exact
      (hBalance n t ht).1

  · intro s hs t ht hst

    exact
      hLocal
        n
        s
        hs
        t
        ht
        hst

  · intro t ht

    exact
      (
        deriv_naturalTopDissipationRadialTail_le_nonlinearTransfer_of_localizedPDEBalance
          hH3
          hClass
          hBalance
          n
          t
          ht
      ).trans
        (hUpper n t ht)

/--
Under the retained endpoint hypotheses, closing the concrete localized PDE
balance and bounding only its nonlinear transfer by one terminal-integrable
profile is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_localizedTopTailPDEBalance_of_nonlinearTransferUpperBound_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hBalance :
      H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
        hH3 hClass)
    (hLocal :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable
        hH3 hClass)
    (hTransfer :
      H3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint_of_localizedPDEBalance_of_nonlinearTransferUpperBound
        hH3
        hClass
        hBalance
        hLocal
        hTransfer)

/-! ## Neutral formulation -/

/--
Neutral localized-PDE formulation of the remaining endpoint frontier.

If the exact localized balance and local derivative integrability are closed,
then either the path extends smoothly or the concrete nonlinear sharp-tail
transfer has no cutoff-independent terminal-`L¹` upper majorant.
-/
theorem smoothContinuationExtension_or_not_nonlinearTopTailTransferUniformIntegrableUpperBound_of_localizedPDEBalance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hBalance :
      H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
        hH3 hClass)
    (hLocal :
      H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable
        hH3 hClass) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    ¬
      H3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint
        hH3 hClass := by

  classical

  by_cases hTransfer :
      H3TerminalPhysicalTopDissipationNaturalRadialTailNonlinearTransferUniformIntegrableUpperBoundAtEndpoint
        hH3 hClass

  · exact
      Or.inl
        (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_localizedTopTailPDEBalance_of_nonlinearTransferUpperBound_of_actualVorticityStrongH3EndpointPath
          hH3
          hClass
          hPhysical
          hCauchy
          hBalance
          hLocal
          hTransfer)

  · exact
      Or.inr
        hTransfer

end

end Euclidean
end Bridge
end PrimeTensor
