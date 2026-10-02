import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Evolution

/-!
# Strong derivative of the full selected top-tail weighted state

The previous checkpoint proved the exact cutoff-free Hilbert evolution on every
positive compact restart slab:

    q² û_i(t) - q² û_i(s)
      =
    ∫_s^t (-q³ û_i(r) - q² F_i(r)) dr.

The weighted RHS is already strongly continuous in Fourier `L²`.  Therefore
the standard Banach-valued fundamental theorem of calculus immediately yields
the genuine strong derivative of the full weighted state.

No truncation, cutoff limit, or weak derivative remains in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/--
On every positive selected compact restart slab, the full intrinsic
`q² û_i` Hilbert state has strong Fourier `L²` derivative equal to the exact
weighted PDE RHS

    `-q³ û_i - q² F_i`

at every strict interior slab time.

Both paths are extended from the closed slab by `Set.IccExtend`; on the slab
these extensions agree exactly with the previously constructed selected
weighted states.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    HasDerivAt
      (
        Set.IccExtend
          (by linarith : Q / 2 ≤ Q)
          (
            h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR i
          )
      )
      (
        h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  have hHalfLe :
      Q / 2 ≤ Q := by
    linarith

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i

  let Gclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Vclosed

  let G : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Gclosed

  have hGClosedContinuous :
      Continuous Gclosed := by
    dsimp only [Gclosed]
    exact
      continuous_h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR i

  have hGContinuous :
      Continuous G := by
    dsimp only [G]
    exact
      hGClosedContinuous.Icc_extend'

  have hGAt :
      ∀ y ∈ Set.Ioo (Q / 2) Q,
        ContinuousAt G y := by
    intro y hy
    exact hGContinuous.continuousAt

  have hGIntegrable :
      IntervalIntegrable G volume (Q / 2) x := by
    exact
      hGContinuous.intervalIntegrable
        (Q / 2)
        x

  have hGMeasurable :
      StronglyMeasurableAtFilter
        G
        (𝓝 x)
        (volume : Measure ℝ) := by
    exact
      ContinuousAt.stronglyMeasurableAtFilter
        (μ := (volume : Measure ℝ))
        isOpen_Ioo
        hGAt
        x
        hx

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ r in (Q / 2)..y, G r)
        (G x)
        x :=
    intervalIntegral.integral_hasDerivAt_right
      hGIntegrable
      hGMeasurable
      hGContinuous.continuousAt

  let left :
      Set.Icc (Q / 2) Q :=
    ⟨Q / 2, le_rfl, hHalfLe⟩

  let J : ℝ → H3FourierComplexL2 :=
    fun y =>
      V (Q / 2)
        +
      ∫ r in (Q / 2)..y, G r

  have hJDerivative :
      HasDerivAt J (G x) x := by
    dsimp only [J]
    exact
      hIntegralDerivative.const_add
        (V (Q / 2))

  have hJEq :
      ∀ y ∈ Set.Icc (Q / 2) Q,
        J y = V y := by

    intro y hy

    let yClosed :
        Set.Icc (Q / 2) Q :=
      ⟨y, hy⟩

    have hEvolution :=
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_intervalEvolution
        hNS ht₀ hE hTail
        hQ hQR i
        left yClosed

    have hVLeft :
        V (Q / 2)
          =
        Vclosed left := by
      dsimp only [V]
      rw [
        Set.IccExtend_of_mem
          hHalfLe
          Vclosed
          ⟨le_rfl, hHalfLe⟩
      ]

    have hVy :
        V y
          =
        Vclosed yClosed := by
      dsimp only [V]
      rw [
        Set.IccExtend_of_mem
          hHalfLe
          Vclosed
          hy
      ]

    dsimp only [J]

    rw [hVLeft, hVy]

    dsimp only [G, Gclosed, Vclosed, left, yClosed] at hEvolution ⊢

    rw [← hEvolution]

    abel

  have hNeighborhood :
      Set.Icc (Q / 2) Q ∈ 𝓝 x :=
    Icc_mem_nhds
      hx.1
      hx.2

  have hEventuallyEq :
      V =ᶠ[𝓝 x] J := by
    filter_upwards [hNeighborhood] with y hy
    exact
      (hJEq y hy).symm

  have hVDerivative :
      HasDerivAt V (G x) x :=
    hJDerivative.congr_of_eventuallyEq
      hEventuallyEq

  let xClosed :
      Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  have hGx :
      G x = Gclosed xClosed := by
    dsimp only [G]
    rw [
      Set.IccExtend_of_mem
        hHalfLe
        Gclosed
        ⟨hx.1.le, hx.2.le⟩
    ]

  dsimp only [V, Gclosed, xClosed] at hVDerivative ⊢

  exact
    hVDerivative.congr_deriv
      hGx

end

end Euclidean
end Bridge
end PrimeTensor
