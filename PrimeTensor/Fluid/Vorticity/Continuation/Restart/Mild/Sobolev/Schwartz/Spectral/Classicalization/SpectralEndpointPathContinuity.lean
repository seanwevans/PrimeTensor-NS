import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalL2EndpointContinuity

/-!
# Classicalization: weighted spectral path continuity from endpoint jets

The integrated endpoint estimate proves, for one velocity component,

    ‖G(q) - G(q₀)‖²
      ≤
    3 * (
      ‖F⁰(q) - F⁰(q₀)‖²
        +
      Σᵢₖₗ ‖F³ᵢₖₗ(q) - F³ᵢₖₗ(q₀)‖²).

Thus strong continuity of only the zeroth and ordered third Fourier jets is
enough to force strong continuity of the complete weighted H³ spectral state.

`PhysicalL2EndpointContinuity` already transports the corresponding physical
`L²` endpoint continuity through Plancherel.  This file therefore removes
first- and second-order jet continuity as independent hypotheses from the
spectral path construction.

No Navier--Stokes evolution identity is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralEndpointPathContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Continuity of the reduced zeroth-plus-third Fourier difference square sum
at one fixed base elapsed time. -/
theorem continuous_h3PreterminalFourierEndpointDifferenceSquareSum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalFourierEndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (j : Fin 3)
    (q₀ : Set.Icc (0 : ℝ) τ) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) τ =>
        ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q₀‖ ^ 2
          +
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j i k l) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j i k l) q₀‖ ^ 2) := by
  rcases hEndpoint j with ⟨h0, h3⟩

  have h0Diff :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot0 j) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot0 j) q₀‖ ^ 2) :=
    ((h0.sub continuous_const).norm.pow 2)

  have h3Diff :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot3 j i k l) q
                -
              h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot3 j i k l) q₀‖ ^ 2) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro k hk
    apply continuous_finset_sum
    intro l hl
    exact
      (((h3 i k l).sub continuous_const).norm.pow 2)

  exact h0Diff.add h3Diff

/-- Reduced Fourier endpoint continuity forces continuity of the complete
tail-canonical weighted spectral state. -/
theorem continuous_h3PreterminalTailCanonicalSpectralStateOnElapsed_of_fourierEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalFourierEndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail) := by
  apply continuous_pi
  intro j

  rw [continuous_iff_continuousAt]
  intro q₀

  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]

  let D : Set.Icc (0 : ℝ) τ → ℝ :=
    fun q =>
      ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 j) q₀‖ ^ 2
        +
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot3 j i k l) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot3 j i k l) q₀‖ ^ 2

  have hDContinuous :
      Continuous D := by
    exact
      continuous_h3PreterminalFourierEndpointDifferenceSquareSum
        hNS ht hEnd hTail hEndpoint j q₀

  have hDZero :
      D q₀ = 0 := by
    dsimp [D]
    simp

  have hDTendstoRaw :
      Tendsto D
        (𝓝 q₀)
        (𝓝 (D q₀)) :=
    hDContinuous.continuousAt

  have hDTendsto :
      Tendsto D
        (𝓝 q₀)
        (𝓝 0) := by
    rw [hDZero] at hDTendstoRaw
    exact hDTendstoRaw

  have hThreeDTendsto :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) τ => 3 * D q)
        (𝓝 q₀)
        (𝓝 0) := by
    have h :=
      (tendsto_const_nhds.mul hDTendsto :
        Tendsto
          (fun q : Set.Icc (0 : ℝ) τ => (3 : ℝ) * D q)
          (𝓝 q₀)
          (𝓝 ((3 : ℝ) * 0)))
    simpa using h

  have hSqLe :
      ∀ q : Set.Icc (0 : ℝ) τ,
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j
            -
          h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q₀ j‖ ^ 2
          ≤
        3 * D q := by
    intro q

    have h :=
      norm_velocityH3SpectralScalarAt_sub_sq_le_three_base_third
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q₀)
        j

    simpa only [
      D,
      h3PreterminalTailCanonicalSpectralStateOnElapsed,
      velocityH3SpectralStateAt,
      h3PreterminalCanonicalFourierJetOnElapsed
    ] using h

  have hSqTendsto :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) τ =>
          ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q j
              -
            h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q₀ j‖ ^ 2)
        (𝓝 q₀)
        (𝓝 0) := by
    exact
      squeeze_zero
        (fun q =>
          sq_nonneg
            ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q j
                -
              h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q₀ j‖)
        hSqLe
        hThreeDTendsto

  have hSqrtAt :
      Tendsto
        Real.sqrt
        (𝓝 (0 : ℝ))
        (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt

  have hSqrtComp :=
    hSqrtAt.comp hSqTendsto

  have hSqrtTendsto :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) τ =>
          Real.sqrt
            (‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q j
                -
              h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q₀ j‖ ^ 2))
        (𝓝 q₀)
        (𝓝 0) := by
    rw [Real.sqrt_zero] at hSqrtComp
    change
      Tendsto
        (Real.sqrt ∘
          fun q : Set.Icc (0 : ℝ) τ =>
            ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q j
                -
              h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q₀ j‖ ^ 2)
        (𝓝 q₀)
        (𝓝 0)
    exact hSqrtComp

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg
  ] using hSqrtTendsto

/-- Final reduced physical endpoint continuity bridge in the exact canonical
spectral representation used by the overlap path. -/
theorem continuous_h3PreterminalCanonicalSpectralStateOnElapsed_of_l2Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3PreterminalCanonicalSpectralStateOnElapsed
          hNS ht hEnd
          (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
          q) := by
  have hFourierEndpoint :
      H3PreterminalCanonicalFourierEndpointContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalFourierEndpointContinuousOnElapsed_of_l2Endpoint
      hNS ht hEnd hTail hEndpoint

  have hTailContinuous :
      Continuous
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail) :=
    continuous_h3PreterminalTailCanonicalSpectralStateOnElapsed_of_fourierEndpoint
      hNS ht hEnd hTail hFourierEndpoint

  have hEq :
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3PreterminalCanonicalSpectralStateOnElapsed
          hNS ht hEnd
          (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
          q)
        =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail := by
    funext q
    symm
    exact
      h3PreterminalTailCanonicalSpectralStateOnElapsed_eq
        hNS ht hEnd hTail q

  rw [hEq]
  exact hTailContinuous

end

end Euclidean
end Bridge
end PrimeTensor
