import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption

/-!
# Integrate the cubic-forcing absorption

The preceding checkpoint proved the pointwise weighted-Young estimate

    diffusion density + nonlinear density
      ≤
    q³ |F|²

and showed that the cubic forcing density is globally integrable at every
strict time.

Here we integrate that inequality on an arbitrary sharp radial tail, enlarge
the nonnegative cubic forcing integral to the whole Fourier space, and sum the
three velocity coordinates.  The result is the cutoff-independent estimate

    diffusionRate(t,R) + nonlinearTransferRate(t,R)
      ≤
    fullForcingCubicMass(t).

Combining this with the already-closed exact localized PDE balance gives

    deriv Tail₃(t,n+1)
      ≤
    fullForcingCubicMass(t)

for every natural cutoff `n`.

Thus the cutoff family disappears completely from the upper-derivative
problem.  What remains after this file is only terminal-time integrability of
one explicit scalar forcing mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailTransferAbsorptionIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Coordinatewise integrated absorption -/

/--
For one coordinate, the exact localized diffusion-plus-transfer contribution
is bounded above by the corresponding full-space cubic forcing mass.
-/
theorem h3TerminalPhysicalTopDissipationDiffusionPlusNonlinearCoordinateRateAt_le_fullForcingCubic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (-2 : ℝ)
          *
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
      +
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
      hH3 hClass ht R j
      ≤
    ∫ ξ : H3FourierPoint3,
      h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j ξ
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let μR : Measure H3FourierPoint3 :=
    (volume : Measure H3FourierPoint3).restrict
      (h3TerminalRadialFrequencyBelow R)ᶜ

  let diffusionDensity : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 5
        *
      ‖h3SpectralScalarRawFourierL2
          (U j) ξ‖ ^ 2

  let nonlinearDensity : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 4
        *
      (
        inner ℂ
          (h3SpectralScalarRawFourierL2
            (U j) ξ)
          (h3RawFinLerayOuterProductDivergence
            U U j ξ)
      ).re

  let cubicDensity : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
      hH3 hClass ht j

  have hDiffFull :
      Integrable
        diffusionDensity
        (volume : Measure H3FourierPoint3) := by

    dsimp only [diffusionDensity]

    simpa only [htAbs, U] using
      (
        integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
          hH3 hClass ht j
      )

  have hNonlinearFull :
      Integrable
        nonlinearDensity
        (volume : Measure H3FourierPoint3) := by

    dsimp only [nonlinearDensity]

    simpa only [htAbs, U] using
      (
        integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j
      )

  have hCubicFull :
      Integrable
        cubicDensity
        (volume : Measure H3FourierPoint3) := by

    dsimp only [cubicDensity]

    exact
      integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j

  have hDiff :
      Integrable
        diffusionDensity
        μR :=
    hDiffFull.mono_measure
      Measure.restrict_le_self

  have hNonlinear :
      Integrable
        nonlinearDensity
        μR :=
    hNonlinearFull.mono_measure
      Measure.restrict_le_self

  have hCubic :
      Integrable
        cubicDensity
        μR :=
    hCubicFull.mono_measure
      Measure.restrict_le_self

  have hDiffSigned :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (-2 : ℝ) * diffusionDensity ξ)
        μR :=
    hDiff.const_mul (-2 : ℝ)

  have hNonlinearSigned :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (-2 : ℝ) * nonlinearDensity ξ)
        μR :=
    hNonlinear.const_mul (-2 : ℝ)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        (-2 : ℝ) * diffusionDensity ξ
            +
          (-2 : ℝ) * nonlinearDensity ξ
          ≤
        cubicDensity ξ := by

    intro ξ

    dsimp only [
      diffusionDensity,
      nonlinearDensity,
      cubicDensity
    ]

    simpa only [htAbs, U] using
      (
        h3TerminalPhysicalTopDissipationPDECoordinateDensity_le_forcingCubic
          hH3 hClass ht j ξ
      )

  have hTail :
      (
        ∫ ξ : H3FourierPoint3,
          (
            (-2 : ℝ) * diffusionDensity ξ
              +
            (-2 : ℝ) * nonlinearDensity ξ
          )
          ∂μR
      )
        ≤
      ∫ ξ : H3FourierPoint3,
        cubicDensity ξ
        ∂μR := by

    exact
      integral_mono_ae
        (hDiffSigned.add hNonlinearSigned)
        hCubic
        (Filter.Eventually.of_forall hPoint)

  have hCubicNonneg :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        0 ≤ cubicDensity ξ := by

    filter_upwards with ξ

    dsimp only [cubicDensity]

    unfold
      h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt

    exact
      mul_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          3)
        (sq_nonneg _)

  have hTailFull :
      (
        ∫ ξ : H3FourierPoint3,
          cubicDensity ξ
          ∂μR
      )
        ≤
      ∫ ξ : H3FourierPoint3,
        cubicDensity ξ
        ∂(volume : Measure H3FourierPoint3) := by

    exact
      integral_mono_measure
        Measure.restrict_le_self
        hCubicNonneg
        hCubicFull

  have hLeftEq :
      (-2 : ℝ)
            *
          ∫ ξ : H3FourierPoint3,
            diffusionDensity ξ
            ∂μR
        +
      (-2 : ℝ)
            *
          ∫ ξ : H3FourierPoint3,
            nonlinearDensity ξ
            ∂μR
        =
      ∫ ξ : H3FourierPoint3,
        (
          (-2 : ℝ) * diffusionDensity ξ
            +
          (-2 : ℝ) * nonlinearDensity ξ
        )
        ∂μR := by

    rw [
      integral_add
        hDiffSigned
        hNonlinearSigned,
      integral_const_mul,
      integral_const_mul
    ]

  unfold
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt

  dsimp only [htAbs, U, μR, diffusionDensity, nonlinearDensity] at hLeftEq ⊢

  calc
    (-2 : ℝ)
          *
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
      +
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
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
        =
      ∫ ξ : H3FourierPoint3,
        (
          (-2 : ℝ) * diffusionDensity ξ
            +
          (-2 : ℝ) * nonlinearDensity ξ
        )
        ∂μR := by

      exact hLeftEq

    _ ≤
      ∫ ξ : H3FourierPoint3,
        cubicDensity ξ
        ∂μR :=
      hTail

    _ ≤
      ∫ ξ : H3FourierPoint3,
        cubicDensity ξ
        ∂(volume : Measure H3FourierPoint3) :=
      hTailFull

    _ =
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j ξ
        ∂(volume : Measure H3FourierPoint3) := by

      rfl

/-! ## Sum the three coordinates -/

/--
At every strict time and every sharp cutoff, the complete localized
diffusion-plus-nonlinear PDE rate is bounded above by the full-space cubic
forcing mass, independently of the cutoff.
-/
theorem h3TerminalPhysicalTopDissipationDiffusionPlusNonlinearTransferRateAt_le_fullForcingCubicMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
        hH3 hClass ht R
      +
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht R
      ≤
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hDiff :=
    sum_h3TerminalPhysicalTopDissipationDiffusionCoordinateIntegrals_eq_diffusionRateAt
      (R := R)
      hH3 hClass ht

  have hDiff' :
      (
        ∑ j : Fin 3,
          (-2 : ℝ)
            *
          ∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
            ∂(
              (volume : Measure H3FourierPoint3).restrict
                (h3TerminalRadialFrequencyBelow R)ᶜ
            )
      )
        =
      h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
        hH3 hClass ht R := by

    simpa only [htAbs, U] using hDiff

  rw [← hDiff']

  unfold
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt

  rw [← Finset.sum_add_distrib]

  apply
    Finset.sum_le_sum

  intro j hj

  exact
    h3TerminalPhysicalTopDissipationDiffusionPlusNonlinearCoordinateRateAt_le_fullForcingCubic
      hH3 hClass ht j

/-! ## The actual natural-tail derivative has the same cutoff-free bound -/

/--
Every natural sharp-tail derivative is bounded above by the same full-space
cubic forcing mass at the same strict time.
-/
theorem deriv_h3TerminalPhysicalTopDissipationNaturalRadialTailPath_le_fullForcingCubicMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (ht : t ∈ Set.Ioo a T) :
    deriv
        (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
          hH3 hClass n)
        t
      ≤
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht := by

  have hBalance :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed
      hH3 hClass

  rw [
    (hBalance n t ht).2
  ]

  exact
    h3TerminalPhysicalTopDissipationDiffusionPlusNonlinearTransferRateAt_le_fullForcingCubicMass
      hH3 hClass ht

end

end Euclidean
end Bridge
end PrimeTensor
