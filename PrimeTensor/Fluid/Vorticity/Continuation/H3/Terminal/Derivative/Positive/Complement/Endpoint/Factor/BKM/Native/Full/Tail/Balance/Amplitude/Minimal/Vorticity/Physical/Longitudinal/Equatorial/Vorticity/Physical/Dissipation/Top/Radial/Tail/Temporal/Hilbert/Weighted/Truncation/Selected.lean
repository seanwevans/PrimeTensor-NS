import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation.Convergence

/-!
# Selected-state specialization of top-tail truncation convergence

The generic cutoff-removal theorem says that whenever

    G = q² F

almost everywhere, the natural bounded truncations of `F` converge strongly
to `G` in Fourier `L²`.

This file instantiates that result for the two selected objects needed in the
temporal top-tail argument:

1. the selected velocity coordinate:
       raw Fourier velocity  ->  q²-weighted velocity;

2. the selected projected PDE RHS:
       `-q û - F`  ->  `-q³ û - q² F`.

The second specialization first exposes the selected quotient-safe projected
RHS coordinate in its literal unit-viscosity Fourier representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedTruncationSelected
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1600000

/-! ## Literal selected projected-RHS representative -/

/--
The selected unit-viscosity projected Fourier RHS coordinate has the literal
a.e. representative

    `-q(ξ) * û_i(ξ) - F_i(U,U)(ξ)`.

Here the velocity term uses the canonical raw Fourier `L²` representative.
-/
theorem h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_ae_eq_unitPDE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail q
    (
      (
        h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht₀ hE hTail q i :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      -(h3FourierGradientSquare ξ : ℂ)
          *
        (
          (
            h3SpectralScalarRawFourierL2 (U i) :
            H3FourierComplexL2
          ) ξ
        )
        -
      h3RawFinLerayOuterProductDivergence
        U U i ξ) := by

  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail q

  let L : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
      hNS ht₀ hE hTail q i

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
      hNS ht₀ hE hTail q i

  have hLap :
      ((L : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
          *
        (
          (
            h3SpectralScalarRawFourierL2 (U i) :
            H3FourierComplexL2
          ) ξ
        )) := by
    dsimp only [L, U]
    unfold
      h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
    exact
      h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
        (
          (
            h3PreterminalSelectedUnitSpectralStateOnRadius
              hNS ht₀ hE hTail q
          ) i
        )

  have hForce :
      ((F : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergence
        U U i := by
    dsimp only [F, U]
    unfold
      h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
      h3RawFinLerayOuterProductDivergenceFourierL2
    exact
      MemLp.coeFn_toLp
        (
          h3RawFinLerayOuterProductDivergence_memLp2
            (
              h3PreterminalSelectedUnitSpectralStateOnRadius
                hNS ht₀ hE hTail q
            )
            (
              h3PreterminalSelectedUnitSpectralStateOnRadius
                hNS ht₀ hE hTail q
            )
            i
        )

  have hSub :=
    MeasureTheory.Lp.coeFn_sub L F

  unfold
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius

  filter_upwards [
    hLap,
    hForce,
    hSub
  ] with ξ hLapξ hForceξ hSubξ

  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hLapξ, hForceξ]

/-! ## Velocity specialization -/

/--
At every time in a positive terminal-half restart slab, the natural bounded
`q²` truncations of the raw selected Fourier velocity converge strongly to the
intrinsic selected `q² û_i` Hilbert state.
-/
theorem tendsto_h3TopTailTruncatedQSqL2_selectedVelocityOnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    Tendsto
      (fun n : ℕ =>
        h3TopTailTruncatedQSqL2
          ((n : ℝ) + 1)
          (by positivity)
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (s : ℝ)
              i
          ))
      atTop
      (
        𝓝
          (
            h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
              hNS ht₀ hE hTail hq hqR i s
          )
      ) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let F : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2
      (W (s : ℝ) i)

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
      hNS ht₀ hE hTail hq hqR i s

  have hG :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_ae
      hNS ht₀ hE hTail hq hqR i s

  have hF :=
    h3SpectralScalarRawFourierL2_ae
      (W (s : ℝ) i)

  have hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        F ξ) := by

    filter_upwards [hG, hF] with ξ hGξ hFξ

    rw [hGξ, hFξ]

  have h :=
    tendsto_h3TopTailTruncatedQSqL2_of_ae_eq
      F G hFG

  dsimp only [F, G, W, U₀, hA, hU₀] at h ⊢

  simpa only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ] using h

/-! ## Projected-RHS specialization -/

/--
At every time in a positive terminal-half restart slab, the natural bounded
`q²` truncations of the selected unweighted projected Fourier RHS converge
strongly to the exact weighted PDE RHS

    `-q³ û_i - q² F_i`.
-/
theorem tendsto_h3TopTailTruncatedQSqL2_selectedProjectedRHSOnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    let qRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨
        (s : ℝ),
        (
          lt_of_lt_of_le
            (by positivity : 0 < q / 2)
            s.property.1
        ).le,
        (
          lt_of_le_of_lt
            s.property.2
            hqR
        ).le
      ⟩
    Tendsto
      (fun n : ℕ =>
        h3TopTailTruncatedQSqL2
          ((n : ℝ) + 1)
          (by positivity)
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail qRadius i
          ))
      atTop
      (
        𝓝
          (
            h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
              hNS ht₀ hE hTail hq hqR i s
          )
      ) := by

  dsimp only

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (s : ℝ),
      (
        lt_of_lt_of_le
          (by positivity : 0 < q / 2)
          s.property.1
      ).le,
      (
        lt_of_le_of_lt
          s.property.2
          hqR
      ).le
    ⟩

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail qRadius

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNS ht₀ hE hTail hq hqR i s

  have hProjected :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_ae_eq_unitPDE
      hNS ht₀ hE hTail qRadius i

  have hWeighted :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_gradientSquare
      hNS ht₀ hE hTail hq hqR i s

  have hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        F ξ) := by

    filter_upwards [hProjected, hWeighted]
      with ξ hProjectedξ hWeightedξ

    dsimp only [F, G] at hProjectedξ hWeightedξ ⊢

    rw [hWeightedξ, hProjectedξ]

    dsimp only [U, qRadius] at *

    unfold
      h3PreterminalSelectedUnitSpectralStateOnRadius
      at *

    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2,
      h3SpectralFinCoordinateRawFourierL2CLM_apply,
      Complex.ofReal_neg,
      Complex.ofReal_mul,
      Complex.ofReal_pow
    ] at *

    ring

  have h :=
    tendsto_h3TopTailTruncatedQSqL2_of_ae_eq
      F G hFG

  dsimp only [F, G, qRadius] at h ⊢

  exact h

end

end Euclidean
end Bridge
end PrimeTensor
