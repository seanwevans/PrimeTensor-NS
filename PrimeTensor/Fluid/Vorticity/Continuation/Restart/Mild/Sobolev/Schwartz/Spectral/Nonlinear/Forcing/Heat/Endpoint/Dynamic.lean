import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Time.Integrability

/-!
# Dynamic zero-lag stability of the physical nonlinear heat forcing

The fixed-input endpoint theorem proves

    H_τ F(U₀,V₀) → F(U₀,V₀)

pointwise in physical space as `τ → 0⁺`.

For the shrinking Duhamel tail we need the same statement while the two
spectral inputs move at the same time.  The lag-uniform bilinear estimates
already proved for the positive-lag physical reconstruction make this a direct
three-term decomposition:

    H_τ F(U,V) - F(U₀,V₀)
      =
    H_τ F(U-U₀,V)
      + H_τ F(U₀,V-V₀)
      + (H_τ F(U₀,V₀) - F(U₀,V₀)).

Thus convergence of `U` and `V`, positivity of the lags, and the fixed-input
zero-lag theorem imply convergence of the full moving reconstruction.

This theorem is deliberately filter-generic.  The next Duhamel increment can
specialize it to

    τ(h) = h - h r,
    U(h) = U(a + h r),
    V(h) = V(a + h r),

for each fixed `r < 1`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingHeatEndpointDynamic
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Dynamic zero-lag stability: a positive heat lag may collapse to zero while
both spectral inputs move continuously toward limiting states. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_dynamic_zero_right
    {ι : Type*}
    {l : Filter ι}
    {ν : ℝ}
    (hν : 0 < ν)
    (τ : ι → ℝ)
    (U V : ι → H3SpectralFinVectorState)
    (U₀ V₀ : H3SpectralFinVectorState)
    (hτ :
      Tendsto
        τ
        l
        (𝓝[Set.Ici (0 : ℝ)] 0))
    (hτpos : ∀ᶠ n in l, 0 < τ n)
    (hU : Tendsto U l (𝓝 U₀))
    (hV : Tendsto V l (𝓝 V₀))
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun n : ι =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν (τ n) (U n) (V n) i x)
      l
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          U₀ V₀ i x)) := by
  let c : ℝ := h3NonlinearForcingL1Coefficient

  let E : ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      U₀ V₀ i x

  let T : ι → ℂ :=
    fun n =>
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (τ n) U₀ V₀ i x

  let g : ι → ℝ :=
    fun n =>
      c * ‖U n - U₀‖ * ‖V n‖
        +
      c * ‖U₀‖ * ‖V n - V₀‖
        +
      ‖T n - E‖

  have hFrozen :
      Tendsto
        T
        l
        (𝓝 E) := by
    have h0 :=
      (tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero_right
        hν U₀ V₀ i x).comp hτ
    change
      Tendsto
        (fun n : ι =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (τ n) U₀ V₀ i x)
        l
        (𝓝
          (h3RawFinLerayOuterProductDivergenceC0Representative
            U₀ V₀ i x))
      at h0
    dsimp only [T, E]
    exact h0

  have hUConst :
      Tendsto
        (fun _n : ι => U₀)
        l
        (𝓝 U₀) :=
    tendsto_const_nhds

  have hVConst :
      Tendsto
        (fun _n : ι => V₀)
        l
        (𝓝 V₀) :=
    tendsto_const_nhds

  have hEConst :
      Tendsto
        (fun _n : ι => E)
        l
        (𝓝 E) :=
    tendsto_const_nhds

  have hUdiff :
      Tendsto
        (fun n : ι => ‖U n - U₀‖)
        l
        (𝓝 0) := by
    simpa using
      (hU.sub hUConst).norm

  have hVdiff :
      Tendsto
        (fun n : ι => ‖V n - V₀‖)
        l
        (𝓝 0) := by
    simpa using
      (hV.sub hVConst).norm

  have hVnorm :
      Tendsto
        (fun n : ι => ‖V n‖)
        l
        (𝓝 ‖V₀‖) :=
    hV.norm

  have hc :
      Tendsto
        (fun _n : ι => c)
        l
        (𝓝 c) :=
    tendsto_const_nhds

  have hUnorm :
      Tendsto
        (fun _n : ι => ‖U₀‖)
        l
        (𝓝 ‖U₀‖) :=
    tendsto_const_nhds

  have hTdiff :
      Tendsto
        (fun n : ι => ‖T n - E‖)
        l
        (𝓝 0) := by
    simpa using
      (hFrozen.sub hEConst).norm

  have hA :
      Tendsto
        (fun n : ι =>
          c * ‖U n - U₀‖ * ‖V n‖)
        l
        (𝓝 0) := by
    simpa using
      ((hc.mul hUdiff).mul hVnorm)

  have hB :
      Tendsto
        (fun n : ι =>
          c * ‖U₀‖ * ‖V n - V₀‖)
        l
        (𝓝 0) := by
    simpa using
      ((hc.mul hUnorm).mul hVdiff)

  have hgZero :
      Tendsto g l (𝓝 0) := by
    simpa only [g, zero_add] using
      ((hA.add hB).add hTdiff)

  have hUpper :
      ∀ᶠ n : ι in l,
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n) (V n) i x
            -
          E‖
          ≤
        g n := by
    filter_upwards [hτpos] with n hn

    have hDiff :
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n) (V n) i x
            -
          E
          =
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n - U₀) (V n) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) U₀ (V n - V₀) i x
          +
        (T n - E) := by
      dsimp only [T]

      have hLeft :=
        h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left
          hν hn (U n) U₀ (V n) i x

      have hRight :=
        h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right
          hν hn U₀ (V n) V₀ i x

      rw [hLeft, hRight]
      abel

    rw [hDiff]

    have hAbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (τ n) (U n - U₀) (V n) i x‖
          ≤
        c * ‖U n - U₀‖ * ‖V n‖ := by
      dsimp only [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left_le
          hν hn (U n) U₀ (V n) i x

    have hBbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (τ n) U₀ (V n - V₀) i x‖
          ≤
        c * ‖U₀‖ * ‖V n - V₀‖ := by
      dsimp only [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right_le
          hν hn U₀ (V n) V₀ i x

    change
      ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (τ n) (U n - U₀) (V n) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (τ n) U₀ (V n - V₀) i x
          +
        (T n - E)‖
        ≤
      g n

    calc
      ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n - U₀) (V n) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) U₀ (V n - V₀) i x
          +
        (T n - E)‖
          ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n - U₀) (V n) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) U₀ (V n - V₀) i x‖
          +
        ‖T n - E‖ :=
        norm_add_le _ _
      _ ≤
        (‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n - U₀) (V n) i x‖
          +
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) U₀ (V n - V₀) i x‖)
          +
        ‖T n - E‖ := by
        exact
          add_le_add
            (norm_add_le _ _)
            (le_refl _)
      _ ≤
        (c * ‖U n - U₀‖ * ‖V n‖
          +
        c * ‖U₀‖ * ‖V n - V₀‖)
          +
        ‖T n - E‖ := by
        exact
          add_le_add
            (add_le_add hAbound hBbound)
            (le_refl _)
      _ = g n := by
        rfl

  have hNonneg :
      ∀ᶠ n : ι in l,
        0 ≤
          ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (τ n) (U n) (V n) i x
            -
          E‖ :=
    Eventually.of_forall fun n => norm_nonneg _

  have hToE :
      Tendsto
        (fun n : ι =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (τ n) (U n) (V n) i x)
        l
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
