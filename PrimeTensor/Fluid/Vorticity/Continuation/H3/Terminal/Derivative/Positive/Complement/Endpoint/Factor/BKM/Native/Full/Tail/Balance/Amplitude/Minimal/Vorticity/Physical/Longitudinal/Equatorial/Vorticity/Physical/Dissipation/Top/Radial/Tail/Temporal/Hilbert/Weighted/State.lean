import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.RHS.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Fourth.Radial.L2.Continuity

/-!
# Intrinsic q²-weighted selected velocity state

The top-tail Hilbert path is intrinsically

    q(ξ)² û_j(t,ξ),

where

    q(ξ) = h3FourierGradientSquare ξ = (2π)² |ξ|².

The selected high-frequency library already supplies the quotient-safe
fourth-radial Fourier `L²` path

    |ξ|⁴ û_j(t,ξ),

strongly continuously on the strict restart interval.  Multiplication by the
constant `(2π)^4` therefore gives the exact intrinsic `q²`-weighted state.

This file packages that normalization and removes the last radial-coordinate
bookkeeping from the temporal problem.  The preceding RHS checkpoint already
packages the corresponding continuous derivative candidate

    -q³ û_j - q² F_j.

After this file the remaining temporal theorem can be stated directly as

    d/dt [q² û_j] = -q³ û_j - q² F_j

in `H3FourierComplexL2`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Intrinsic q²-weighted selected state -/

/--
The selected `q² û_j` state on the strict restart interval.

This is only the existing fourth-radial selected velocity state multiplied by
the exact conversion constant `(2π)^4`.
-/
noncomputable def h3PreterminalSelectedTopTailWeightedVelocityFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3FourierComplexL2 :=
  ((2 * Real.pi) ^ 4 : ℝ) •
    h3PreterminalSelectedVelocityFourthRadialFourierL2
      hNS ht₀ hE hTail q j

/--
Almost-everywhere intrinsic representative of the selected top-tail weighted
velocity state.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    (
      (
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2
          hNS ht₀ hE hTail j q :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) *
        h3SpectralScalarRawFourier (W (q : ℝ) j) ξ) := by

  dsimp only

  let F4 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2
      hNS ht₀ hE hTail q j

  have hF4 :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2_ae
      hNS ht₀ hE hTail q j

  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      ((2 * Real.pi) ^ 4 : ℝ)
      F4

  unfold
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2

  filter_upwards [hF4, hSmul] with ξ hF4ξ hSmulξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hF4ξ]

  unfold
    h3SelectedRawFourierFourthRadialWeight

  rw [
    h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four
      ξ
  ]

  simp only [
    Complex.ofReal_mul,
    Complex.ofReal_pow,
    Complex.ofReal_ofNat
  ]

  ring

/--
The intrinsic selected `q² û_j` state is strongly continuous throughout the
strict restart interval.
-/
theorem continuous_h3PreterminalSelectedTopTailWeightedVelocityFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3) :
    Continuous
      (h3PreterminalSelectedTopTailWeightedVelocityFourierL2
        hNS ht₀ hE hTail j) := by

  have hF4 :
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedVelocityFourthRadialFourierL2
            hNS ht₀ hE hTail q j) :=
    continuous_h3PreterminalSelectedVelocityFourthRadialFourierL2OnRestartRadius
      hNS ht₀ hE hTail j

  unfold
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2

  exact
    Continuous.smul
      (continuous_const :
        Continuous
          (fun _ :
            Set.Ioo
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            ((2 * Real.pi) ^ 4 : ℝ)))
      hF4

/-! ## Restriction to one terminal-half slab -/

/--
The intrinsic `q² û_j` state restricted to the same terminal-half slab used by
the weighted RHS package.
-/
noncomputable def h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedTopTailWeightedVelocityFourierL2
    hNS ht₀ hE hTail j
    ⟨
      (s : ℝ),
      lt_of_lt_of_le (by positivity : 0 < q / 2) s.property.1,
      lt_of_le_of_lt s.property.2 hqR
    ⟩

/--
The slab restriction of the intrinsic weighted state is strongly continuous.
-/
theorem continuous_h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3) :
    Continuous
      (h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
        hNS ht₀ hE hTail hq hqR j) := by

  let toOpen :
      Set.Icc (q / 2) q →
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    fun s =>
      ⟨
        (s : ℝ),
        lt_of_lt_of_le
          (by positivity : 0 < q / 2)
          s.property.1,
        lt_of_le_of_lt s.property.2 hqR
      ⟩

  have hToOpen :
      Continuous toOpen := by
    exact
      Continuous.subtype_mk
        continuous_subtype_val
        _

  have hBase :=
    continuous_h3PreterminalSelectedTopTailWeightedVelocityFourierL2
      hNS ht₀ hE hTail j

  change
    Continuous
      (fun s : Set.Icc (q / 2) q =>
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2
          hNS ht₀ hE hTail j
          (toOpen s))

  exact
    hBase.comp hToOpen

/--
On the terminal-half slab, the weighted state has the intrinsic `q² û`
representative with the selected mild raw Fourier coordinate.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (q / 2) q) :
    (
      (
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hq hqR j s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) *
        h3SpectralScalarRawFourier
          (
            (
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                (s : ℝ)
            ) j
          )
          ξ) := by

  unfold
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab

  exact
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2_ae
      hNS ht₀ hE hTail j
      ⟨
        (s : ℝ),
        lt_of_lt_of_le
          (by positivity : 0 < q / 2)
          s.property.1,
        lt_of_le_of_lt s.property.2 hqR
      ⟩


end

end Euclidean
end Bridge
end PrimeTensor
