import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Time.Integrability

/-!
# Dynamic upper-endpoint continuity of the retarded nonlinear forcing path

The fixed-state zero-lag theorem identifies the positive-lag nonlinear heat
reconstruction with the unheated continuous Leray--divergence forcing as the
lag tends to zero.

The existing retarded-path theory already controls variation in both spectral
inputs uniformly in the positive heat lag.  Combining these facts shows that,
for continuous spectral paths `U,V`,

    H_{t-s} F(U(s),V(s))  →  F(U(t),V(t))

pointwise in physical space as `s ↑ t`.

No new endpoint-filled path is introduced.  The original retarded path is
already defined at `s = t`, and the zero-lag identity proves that its value
there is exactly the unheated physical forcing.  This is the endpoint
continuity input needed to turn a short Duhamel tail into an ordinary
continuous primitive.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathC0EndpointContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The existing retarded path already has the correct instantaneous nonlinear
forcing value at its upper endpoint. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_endpoint
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x t
      =
    h3RawFinLerayOuterProductDivergenceC0Representative
        (U t) (V t) i x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
  simpa using
    congrFun
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero
        ν (U t) (V t) i)
      x

/-- The lag `t-s` tends to zero through nonnegative values when `s` tends to
`t` from the left. -/
theorem tendsto_sub_self_zero_right_of_left
    (t : ℝ) :
    Tendsto
      (fun s : ℝ => t - s)
      (𝓝[Set.Iio t] t)
      (𝓝[Set.Ici (0 : ℝ)] 0) := by
  have hLagNhds :
      Tendsto
        (fun s : ℝ => t - s)
        (𝓝[Set.Iio t] t)
        (𝓝 (0 : ℝ)) := by
    have hLagCont :
        ContinuousAt
          (fun s : ℝ => t - s)
          t := by
      fun_prop

    have hFull :
        Tendsto
          (fun s : ℝ => t - s)
          (𝓝 t)
          (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using hLagCont.tendsto
    exact hFull.mono_left nhdsWithin_le_nhds

  have hMaps :
      MapsTo
        (fun s : ℝ => t - s)
        (Set.Iio t)
        (Set.Ici (0 : ℝ)) := by
    intro s hs
    change s < t at hs
    exact sub_nonneg.mpr hs.le

  exact
    tendsto_inf.2
      ⟨hLagNhds,
        tendsto_principal.2 <|
          mem_inf_of_right <|
            mem_principal.2 hMaps⟩

/-- For continuous spectral input paths, the classical retarded nonlinear
forcing converges from the left to the instantaneous unheated forcing at the
upper source-time endpoint. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_endpoint
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x)
      (𝓝[Set.Iio t] t)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (U t) (V t) i x)) := by
  let c : ℝ := h3NonlinearForcingL1Coefficient

  let E : ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      (U t) (V t) i x

  let T : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s) (U t) (V t) i x

  let g : ℝ → ℝ :=
    fun s =>
      c * ‖U s - U t‖ * ‖V s‖
        +
      c * ‖U t‖ * ‖V s - V t‖
        +
      ‖T s - E‖

  have hLag :=
    tendsto_sub_self_zero_right_of_left t

  have hFrozen :
      Tendsto
        T
        (𝓝[Set.Iio t] t)
        (𝓝 E) := by
    have h0 :=
      (tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero_right
        hν (U t) (V t) i x).comp hLag
    change
      Tendsto
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U t) (V t) i x)
        (𝓝[Set.Iio t] t)
        (𝓝
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (U t) (V t) i x))
      at h0
    dsimp only [T, E]
    exact h0

  have hUWithin :
      Tendsto U (𝓝[Set.Iio t] t) (𝓝 (U t)) :=
    hU.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

  have hVWithin :
      Tendsto V (𝓝[Set.Iio t] t) (𝓝 (V t)) :=
    hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

  have hUdiff :
      Tendsto
        (fun s : ℝ => ‖U s - U t‖)
        (𝓝[Set.Iio t] t)
        (𝓝 0) := by
    have hUConst :
        Tendsto
          (fun _s : ℝ => U t)
          (𝓝[Set.Iio t] t)
          (𝓝 (U t)) :=
      tendsto_const_nhds
    simpa using
      (hUWithin.sub hUConst).norm

  have hVdiff :
      Tendsto
        (fun s : ℝ => ‖V s - V t‖)
        (𝓝[Set.Iio t] t)
        (𝓝 0) := by
    have hVConst :
        Tendsto
          (fun _s : ℝ => V t)
          (𝓝[Set.Iio t] t)
          (𝓝 (V t)) :=
      tendsto_const_nhds
    simpa using
      (hVWithin.sub hVConst).norm

  have hVnorm :
      Tendsto
        (fun s : ℝ => ‖V s‖)
        (𝓝[Set.Iio t] t)
        (𝓝 ‖V t‖) :=
    hVWithin.norm

  have hc :
      Tendsto
        (fun _s : ℝ => c)
        (𝓝[Set.Iio t] t)
        (𝓝 c) :=
    tendsto_const_nhds

  have hUnorm :
      Tendsto
        (fun _s : ℝ => ‖U t‖)
        (𝓝[Set.Iio t] t)
        (𝓝 ‖U t‖) :=
    tendsto_const_nhds

  have hTdiff :
      Tendsto
        (fun s : ℝ => ‖T s - E‖)
        (𝓝[Set.Iio t] t)
        (𝓝 0) := by
    have hEConst :
        Tendsto
          (fun _s : ℝ => E)
          (𝓝[Set.Iio t] t)
          (𝓝 E) :=
      tendsto_const_nhds
    simpa using
      (hFrozen.sub hEConst).norm

  have hA :
      Tendsto
        (fun s : ℝ =>
          c * ‖U s - U t‖ * ‖V s‖)
        (𝓝[Set.Iio t] t)
        (𝓝 0) := by
    simpa using
      ((hc.mul hUdiff).mul hVnorm)

  have hB :
      Tendsto
        (fun s : ℝ =>
          c * ‖U t‖ * ‖V s - V t‖)
        (𝓝[Set.Iio t] t)
        (𝓝 0) := by
    simpa using
      ((hc.mul hUnorm).mul hVdiff)

  have hgZero :
      Tendsto g (𝓝[Set.Iio t] t) (𝓝 0) := by
    simpa only [g, zero_add] using
      ((hA.add hB).add hTdiff)

  have hUpper :
      ∀ᶠ s : ℝ in (𝓝[Set.Iio t] t),
        ‖h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν t U V i x s
            -
          E‖
          ≤
        g s := by
    filter_upwards [self_mem_nhdsWithin] with s hs

    have hlag : 0 < t - s :=
      sub_pos.mpr hs

    have hDiff :
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν t U V i x s
            -
          E
          =
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U t) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U t) (V s - V t) i x
          +
        (T s - E) := by
      unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      dsimp only [T]

      have hLeft :=
        h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left
          hν hlag (U s) (U t) (V s) i x

      have hRight :=
        h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right
          hν hlag (U t) (V s) (V t) i x

      rw [hLeft, hRight]
      abel

    rw [hDiff]

    have hAbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U s - U t) (V s) i x‖
          ≤
        c * ‖U s - U t‖ * ‖V s‖ := by
      dsimp only [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left_le
          hν hlag (U s) (U t) (V s) i x

    have hBbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U t) (V s - V t) i x‖
          ≤
        c * ‖U t‖ * ‖V s - V t‖ := by
      dsimp only [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right_le
          hν hlag (U t) (V s) (V t) i x

    change
      ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U s - U t) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U t) (V s - V t) i x
          +
        (T s - E)‖
        ≤
      g s

    calc
      ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U t) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U t) (V s - V t) i x
          +
        (T s - E)‖
          ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U t) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U t) (V s - V t) i x‖
          +
        ‖T s - E‖ :=
        norm_add_le _ _
      _ ≤
        (‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U t) (V s) i x‖
          +
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U t) (V s - V t) i x‖)
          +
        ‖T s - E‖ := by
        exact
          add_le_add
            (norm_add_le _ _)
            (le_refl _)
      _ ≤
        (c * ‖U s - U t‖ * ‖V s‖
          +
        c * ‖U t‖ * ‖V s - V t‖)
          +
        ‖T s - E‖ := by
        exact
          add_le_add
            (add_le_add hAbound hBbound)
            (le_refl _)
      _ = g s := by
        rfl

  have hNonneg :
      ∀ᶠ s : ℝ in (𝓝[Set.Iio t] t),
        0 ≤
          ‖h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν t U V i x s
            -
          E‖ :=
    Eventually.of_forall fun s => norm_nonneg _

  have hToE :
      Tendsto
        (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i x)
        (𝓝[Set.Iio t] t)
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  simpa only [E] using hToE

end

end Euclidean
end Bridge
end PrimeTensor
