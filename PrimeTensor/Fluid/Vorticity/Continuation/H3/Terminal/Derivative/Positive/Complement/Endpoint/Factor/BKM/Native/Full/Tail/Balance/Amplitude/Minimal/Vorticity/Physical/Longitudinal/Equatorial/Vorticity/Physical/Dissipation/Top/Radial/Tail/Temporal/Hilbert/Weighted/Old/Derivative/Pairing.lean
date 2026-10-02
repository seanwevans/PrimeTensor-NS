import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Pairing.Integral

/-!
# Physical Hilbert pairing for the terminal fourth-radial derivative

The terminal physical fourth-radial path now has its literal Fourier PDE
representative. The static restricted-pairing algebra is also already
available.

This file joins those two facts.

For every strict physical time, every component, every radial cutoff, and every
strong derivative value `W`, the real Hilbert pairing

    2 ⟪q² û_j, W⟫_ℝ

on the sharp radial tail is exactly the integral of the combined unit-viscosity
PDE density

    -2 q⁵ |û_j|²
    -2 q⁴ Re ⟪û_j, F_j(U,U)⟫_ℂ.

The result is then summed over the three velocity coordinates.

Importantly, this checkpoint does not split the integral of the combined
density into two separate integrals. That split requires separate
integrability of the strict-time sixth-radial velocity and fourth-radial
forcing terms and is left visible for the next layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedOldDerivativePairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
Any strong derivative value of one terminal physical fourth-radial coordinate
has the exact restricted Hilbert pairing with its canonical Fourier
Navier--Stokes representative.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_two_mul_inner_derivativeValue_eq_unitPDE_integral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (W : H3FourierComplexL2)
    (hW :
      HasDerivAt
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        W
        t) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    2 *
      inner ℝ
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass R j t
        )
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
            R W
        )
      =
    ∫ ξ : H3FourierPoint3,
      (
        (-2 : ℝ)
          *
        h3FourierGradientSquare ξ ^ 5
          *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
      )
        +
      (
        (-2 : ℝ)
          *
        h3FourierGradientSquare ξ ^ 4
          *
        (
          inner ℂ
            (h3SpectralScalarRawFourierL2 (U j) ξ)
            (h3RawFinLerayOuterProductDivergence
              U U j ξ)
        ).re
      )
      ∂(
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  change
    2 *
      inner ℝ
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass R j t
        )
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
            R W
        )
      =
    ∫ ξ : H3FourierPoint3,
      (
        (-2 : ℝ)
          *
        h3FourierGradientSquare ξ ^ 5
          *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
      )
        +
      (
        (-2 : ℝ)
          *
        h3FourierGradientSquare ξ ^ 4
          *
        (
          inner ℂ
            (h3SpectralScalarRawFourierL2 (U j) ξ)
            (h3RawFinLerayOuterProductDivergence
              U U j ξ)
        ).re
      )
      ∂(
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      )

  let hNS :
      LoggedPreterminalNavierStokesAdmissible u T :=
    hH3.navier_stokes

  let hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS htAbs hInt

  have hRawEq :
      h3SpectralScalarRawFourierL2 (U j)
        =
      velocityH3BaseFourierAt
        u t hInt hMeas j := by

    dsimp only [U]

    unfold
      h3TerminalVelocitySpectralStateAt
      velocityH3SpectralStateAt

    rw [
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j
    ]

  have hAtAE :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae
      hH3 hClass ht j

  have hX :
      (
        (
          h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j t :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3SpectralScalarRawFourierL2
          (U j) ξ) := by

    rw [
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
        hH3 hClass ht j
    ]

    filter_upwards [hAtAE] with ξ hξ

    rw [hξ]

    unfold
      h3TerminalPhysicalTopDissipationFourthRadialComponent

    change
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ
        =
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          h3SpectralScalarRawFourierL2
            (U j) ξ

    rw [hRawEq]

  let Fraw : H3FourierComplexL2 :=
    (
      h3RawFinLerayOuterProductDivergence_memLp2
        U U j
    ).toLp
      (
        h3RawFinLerayOuterProductDivergence
          U U j
      )

  have hFrawAE :
      ((Fraw : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergence
        U U j := by

    dsimp only [Fraw]

    exact
      MeasureTheory.MemLp.coeFn_toLp
        (
          h3RawFinLerayOuterProductDivergence_memLp2
            U U j
        )

  have hY0 :
      ((W : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          h3SpectralScalarRawFourierL2
            (U j) ξ
          -
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          h3RawFinLerayOuterProductDivergence
            U U j ξ) := by

    simpa only [htAbs, U] using
      (
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_derivativeValue_ae_unitPDE
          hH3 hClass ht j W hW
      )

  have hY :
      ((W : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          h3SpectralScalarRawFourierL2
            (U j) ξ
          -
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          Fraw ξ) := by

    filter_upwards [hY0, hFrawAE] with ξ hYξ hFξ

    rw [hYξ, hFξ]

  have hPair :=
    two_mul_inner_restrict_eq_weightedPDE_integral
      R
      (
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t
      )
      W
      (h3SpectralScalarRawFourierL2 (U j))
      Fraw
      hX
      hY

  unfold
    h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path

  calc
    2 *
        inner ℝ
          (
            h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
              R
              (
                h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j t
              )
          )
          (
            h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
              R W
          )
        =
      ∫ ξ : H3FourierPoint3,
        (
          (-2 : ℝ)
            *
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
        )
          +
        (
          (-2 : ℝ)
            *
          h3FourierGradientSquare ξ ^ 4
            *
          (
            inner ℂ
              (h3SpectralScalarRawFourierL2 (U j) ξ)
              (Fraw ξ)
          ).re
        )
        ∂(
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) := hPair

    _ =
      ∫ ξ : H3FourierPoint3,
        (
          (-2 : ℝ)
            *
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
        )
          +
        (
          (-2 : ℝ)
            *
          h3FourierGradientSquare ξ ^ 4
            *
          (
            inner ℂ
              (h3SpectralScalarRawFourierL2 (U j) ξ)
              (h3RawFinLerayOuterProductDivergence
                U U j ξ)
          ).re
        )
        ∂(
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) := by

      apply integral_congr_ae

      have hFrawRestrict :=
        ae_restrict_of_ae
          (s := (h3TerminalRadialFrequencyBelow R)ᶜ)
          hFrawAE

      filter_upwards [hFrawRestrict] with ξ hFξ

      rw [hFξ]

/--
Summing the componentwise physical pairing identities gives the exact
three-component combined PDE integral sum.

No exchange between the finite coordinate sum and the Fourier integral, and no
splitting of the diffusion and transfer integrals, is used here.
-/
theorem h3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertPairing_eq_unitPDE_integral_sum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (W : Fin 3 → H3FourierComplexL2)
    (hW :
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          (W j)
          t) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (
      ∑ j : Fin 3,
        2 *
          inner ℝ
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j t
            )
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                R (W j)
            )
    )
      =
    ∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        (
          (-2 : ℝ)
            *
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
        )
          +
        (
          (-2 : ℝ)
            *
          h3FourierGradientSquare ξ ^ 4
            *
          (
            inner ℂ
              (h3SpectralScalarRawFourierL2 (U j) ξ)
              (h3RawFinLerayOuterProductDivergence
                U U j ξ)
          ).re
        )
        ∂(
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) := by

  dsimp only

  apply Finset.sum_congr rfl

  intro j hj

  simpa only using
    (
      h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_two_mul_inner_derivativeValue_eq_unitPDE_integral
        hH3 hClass ht j (W j) (hW j)
    )

end

end Euclidean
end Bridge
end PrimeTensor
