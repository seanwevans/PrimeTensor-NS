import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatInteractionSlope

/-!
# Physical L² temporal admissibility: endpoint interaction derivative

The quotient-safe interaction slope has already been factored exactly.  This
file now takes the right limit on an endpoint canonical trajectory.

For fixed final elapsed time `q`, define

    I_q(r) = S₁(q-r) raw(W(r)).

At a strict interior source time `s`, the endpoint evolution derivative gives

    slope raw(W)(s,y) → A₁(W(s)) - F(s),

while the vector heat quotient gives

    Q₁(y-s,W(s)) → A₁(W(s)).

Their difference therefore converges to `-F(s)`.  Joint strong continuity of
the heat action in both time and state transports that cancellation through
`S₁(q-y)`, yielding

    I_q'(s) = S₁(q-s)(-F(s))

from the right.

The result remains conditional on the explicit family
`H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed`; no physical
evolution hypothesis is hidden or discharged here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2EndpointInteractionDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed-final-time unit-heat interaction picture of the quotient-safe
endpoint raw Fourier `L²` velocity path. -/
noncomputable def h3PreterminalTailCanonicalRawFourierL2InteractionReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q r : ℝ) :
    H3RawFourierL2FinVectorState :=
  h3RawFourierL2HeatApplyNN
    1 zero_le_one
    (Real.toNNReal (q - r))
    (h3PreterminalTailCanonicalRawFourierL2VelocityReal
      hNS ht htau hEnd hE hTail hEndpoint r)

/-- On the strict source-time interior `0 < s < q < tau`, the interaction
picture has right derivative equal to the heat-evolved negative endpoint
forcing. -/
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_of_integralEvolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (hs : s ∈ Set.Ioo (0 : ℝ) q) :
    HasDerivWithinAt
      (h3PreterminalTailCanonicalRawFourierL2InteractionReal
        hNS ht htau.le hEnd hE hTail hEndpoint q)
      (h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal (q - s))
        (- h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
          hNS ht htau.le hEnd hE hTail hEndpoint s))
      (Set.Ioi s)
      s := by
  let D : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
      hNS ht htau.le hEnd hE hTail hEndpoint

  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint s

  let A : H3RawFourierL2FinVectorState :=
    h3RawFourierL2UnitGeneratorStateVector U

  let F : H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint s

  have hsTau : s ∈ Set.Ioo (0 : ℝ) tau :=
    ⟨hs.1, hs.2.trans hq.2⟩

  have hDRight :
      HasDerivWithinAt
        D
        (A - F)
        (Set.Ioi s)
        s := by
    dsimp only [D, A, F, U]
    exact
      h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivWithinAt_right_unitGenerator_sub_forcing
        hNS ht htau hEnd hE hTail hEndpoint hEvolution hsTau

  have hSlopeD :
      Tendsto
        (slope D s)
        (𝓝[Set.Ioi s] s)
        (𝓝 (A - F)) := by
    exact
      (hasDerivWithinAt_iff_tendsto_slope'
        (f := D)
        (f' := A - F)
        (s := Set.Ioi s)
        (x := s)
        (by simp)).1
        hDRight

  have hShift :
      Tendsto
        (fun y : ℝ => y - s)
        (𝓝[Set.Ioi s] s)
        (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hBase :
          Tendsto
            (fun y : ℝ => y - s)
            (𝓝 s)
            (𝓝 (0 : ℝ)) := by
        simpa using
          (tendsto_id.sub_const s :
            Tendsto
              (fun y : ℝ => y - s)
              (𝓝 s)
              (𝓝 (s - s)))
      exact
        hBase.mono_left
          (show
            (𝓝[Set.Ioi s] s) ≤ (𝓝 s) by
              exact inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.mpr (Set.mem_Ioi.mp hy)

  have hQuotient :
      Tendsto
        (fun y : ℝ =>
          h3RawFourierL2UnitHeatVectorQuotientState
            (y - s) U)
        (𝓝[Set.Ioi s] s)
        (𝓝 A) := by
    dsimp only [A]
    exact
      (tendsto_h3RawFourierL2UnitHeatVectorQuotientState_zero_right
        U).comp hShift

  have hBracket :
      Tendsto
        (fun y : ℝ =>
          slope D s y -
            h3RawFourierL2UnitHeatVectorQuotientState
              (y - s) U)
        (𝓝[Set.Ioi s] s)
        (𝓝 (-F)) := by
    have hSub := hSlopeD.sub hQuotient
    have hCancel :
        (A - F) - A = -F := by
      abel
    rw [hCancel] at hSub
    exact hSub

  have hSubTime :
      Tendsto
        (fun y : ℝ => q - y)
        (𝓝 s)
        (𝓝 (q - s)) := by
    simpa using
      (tendsto_const_nhds.sub tendsto_id :
        Tendsto
          (fun y : ℝ => q - y)
          (𝓝 s)
          (𝓝 (q - s)))

  have hToNN :
      Tendsto
        Real.toNNReal
        (𝓝 (q - s))
        (𝓝 (Real.toNNReal (q - s))) :=
    continuous_real_toNNReal.continuousAt

  have hHeatTimeFull :
      Tendsto
        (fun y : ℝ => Real.toNNReal (q - y))
        (𝓝 s)
        (𝓝 (Real.toNNReal (q - s))) :=
    hToNN.comp hSubTime

  have hHeatTime :
      Tendsto
        (fun y : ℝ => Real.toNNReal (q - y))
        (𝓝[Set.Ioi s] s)
        (𝓝 (Real.toNNReal (q - s))) :=
    hHeatTimeFull.mono_left
      (show
        (𝓝[Set.Ioi s] s) ≤ (𝓝 s) by
          exact inf_le_left)

  have hMoved :
      Tendsto
        (fun y : ℝ =>
          h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (q - y))
            (slope D s y -
              h3RawFourierL2UnitHeatVectorQuotientState
                (y - s) U))
        (𝓝[Set.Ioi s] s)
        (𝓝
          (h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (q - s))
            (-F))) :=
    tendsto_h3RawFourierL2HeatApplyNN_moving
      1 zero_le_one hHeatTime hBracket

  have hYltQ :
      Set.Iio q ∈ (𝓝[Set.Ioi s] s) :=
    mem_inf_of_left
      (Iio_mem_nhds hs.2)

  have hSlopeEq :
      (fun y : ℝ =>
        h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal (q - y))
          (slope D s y -
            h3RawFourierL2UnitHeatVectorQuotientState
              (y - s) U))
        =ᶠ[(𝓝[Set.Ioi s] s)]
      slope
        (h3PreterminalTailCanonicalRawFourierL2InteractionReal
          hNS ht htau.le hEnd hE hTail hEndpoint q)
        s := by
    filter_upwards [self_mem_nhdsWithin, hYltQ] with y hsy hyq
    have hDs :
        D s =
          h3SpectralFinVectorRawFourierL2 U := by
      rfl
    exact
      (h3RawFourierL2UnitHeatInteractionSlope_eq
        hs.2
        (Set.mem_Ioi.mp hsy)
        (Set.mem_Iio.mp hyq)
        U D hDs).symm

  have hInteractionSlope :
      Tendsto
        (slope
          (h3PreterminalTailCanonicalRawFourierL2InteractionReal
            hNS ht htau.le hEnd hE hTail hEndpoint q)
          s)
        (𝓝[Set.Ioi s] s)
        (𝓝
          (h3RawFourierL2HeatApplyNN
            1 zero_le_one
            (Real.toNNReal (q - s))
            (-F))) :=
    Tendsto.congr'
      hSlopeEq
      hMoved

  refine
    (hasDerivWithinAt_iff_tendsto_slope'
      (f :=
        h3PreterminalTailCanonicalRawFourierL2InteractionReal
          hNS ht htau.le hEnd hE hTail hEndpoint q)
      (f' :=
        h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal (q - s))
          (- h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
            hNS ht htau.le hEnd hE hTail hEndpoint s))
      (s := Set.Ioi s)
      (x := s)
      (by simp)).2 ?_

  dsimp only [F] at hInteractionSlope
  exact hInteractionSlope

end

end Euclidean
end Bridge
end PrimeTensor
