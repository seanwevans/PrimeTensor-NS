import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.Derivative.L2

/-!
# Classicalization: W¹,² cutoff graph convergence

The scalar cutoff itself converges in `L²`, and the previous checkpoint proved
that the derivative-of-cutoff remainder tends to zero in `L²`.

Using

    ∂ₐ(χₙ φ)
      =
    χₙ ∂ₐφ
      +
    Rₙ,ₐ,

the complete coordinate derivative therefore converges in `L²`.  Since there
are only three coordinate directions, the zeroth-order convergence and the
three first-derivative convergences assemble into convergence of the concrete
`W¹,²` graph introduced in `Schwartz.Sobolev`.

Every cutoff graph is literally in the range of a transported compact weak
test, so graph convergence immediately proves the exact density frontier

    H3TransportedWeakTestsDenseInRealW12Schwartz.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoffGraph
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## `toLp` respects the cutoff derivative decomposition -/

/-- Applying the continuous Schwartz-to-`L²` map to the product-rule
decomposition preserves the sum exactly. -/
theorem h3W12CutoffSchwartz_lineDeriv_toLp_eq_main_add_remainder
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    (∂_{h3FourierAxisDirection a}
        (h3W12CutoffSchwartz n φ) :
      𝓢(H3FourierPoint3, ℝ)).toLp
        2
        (volume : Measure H3FourierPoint3)
      =
    (h3W12CutoffSchwartz n
        (∂_{h3FourierAxisDirection a} φ)).toLp
          2
          (volume : Measure H3FourierPoint3)
      +
    (h3W12CutoffDerivativeRemainder n φ a).toLp
      2
      (volume : Measure H3FourierPoint3) := by
  rw [
    h3W12CutoffSchwartz_lineDeriv_eq_main_add_remainder
  ]

  change
    SchwartzMap.toLpCLM ℝ ℝ
        2
        (volume : Measure H3FourierPoint3)
        (h3W12CutoffSchwartz n
            (∂_{h3FourierAxisDirection a} φ)
          +
        h3W12CutoffDerivativeRemainder n φ a)
      =
    SchwartzMap.toLpCLM ℝ ℝ
        2
        (volume : Measure H3FourierPoint3)
        (h3W12CutoffSchwartz n
          (∂_{h3FourierAxisDirection a} φ))
      +
    SchwartzMap.toLpCLM ℝ ℝ
        2
        (volume : Measure H3FourierPoint3)
        (h3W12CutoffDerivativeRemainder n φ a)

  exact
    map_add
      (SchwartzMap.toLpCLM ℝ ℝ
        2
        (volume : Measure H3FourierPoint3))
      _
      _

/-! ## Coordinate derivative convergence -/

/-- Every coordinate derivative of the cutoff sequence converges in real
`L²` to the corresponding derivative of the original Schwartz function. -/
theorem h3W12CutoffSchwartz_lineDeriv_toLp_tendsto
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    Tendsto
      (fun n : ℕ =>
        (∂_{h3FourierAxisDirection a}
            (h3W12CutoffSchwartz n φ) :
          𝓢(H3FourierPoint3, ℝ)).toLp
            2
            (volume : Measure H3FourierPoint3))
      atTop
      (𝓝
        ((∂_{h3FourierAxisDirection a} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp
            2
            (volume : Measure H3FourierPoint3))) := by
  have hMain :=
    h3W12CutoffSchwartz_lineDeriv_main_toLp_tendsto
      φ a

  have hRemainder :=
    h3W12CutoffDerivativeRemainder_toLp_tendsto_zero
      φ a

  have hSum :=
    hMain.add hRemainder

  have hPointwise :
      (fun n : ℕ =>
        (∂_{h3FourierAxisDirection a}
            (h3W12CutoffSchwartz n φ) :
          𝓢(H3FourierPoint3, ℝ)).toLp
            2
            (volume : Measure H3FourierPoint3))
        =
      (fun n : ℕ =>
        (h3W12CutoffSchwartz n
            (∂_{h3FourierAxisDirection a} φ)).toLp
              2
              (volume : Measure H3FourierPoint3)
          +
        (h3W12CutoffDerivativeRemainder n φ a).toLp
          2
          (volume : Measure H3FourierPoint3)) := by
    funext n

    exact
      h3W12CutoffSchwartz_lineDeriv_toLp_eq_main_add_remainder
        n φ a

  rw [hPointwise]

  simpa using hSum

/-! ## Full first-derivative graph convergence -/

/-- The cutoff sequence converges to the original Schwartz function in the
concrete real `W¹,²` graph topology. -/
theorem h3W12CutoffSchwartz_firstDerivativeGraph_tendsto
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    Tendsto
      (fun n : ℕ =>
        h3FourierRealSchwartzFirstDerivativeGraph
          (h3W12CutoffSchwartz n φ))
      atTop
      (𝓝
        (h3FourierRealSchwartzFirstDerivativeGraph φ)) := by
  have hZero :
      Tendsto
        (fun n : ℕ =>
          (h3FourierRealSchwartzFirstDerivativeGraph
            (h3W12CutoffSchwartz n φ)).1)
        atTop
        (𝓝
          (h3FourierRealSchwartzFirstDerivativeGraph φ).1) := by
    simpa only [
      h3FourierRealSchwartzFirstDerivativeGraph_zero
    ] using
      h3W12CutoffSchwartz_toLp_tendsto φ

  have hDerivative :
      Tendsto
        (fun n : ℕ =>
          (h3FourierRealSchwartzFirstDerivativeGraph
            (h3W12CutoffSchwartz n φ)).2)
        atTop
        (𝓝
          (h3FourierRealSchwartzFirstDerivativeGraph φ).2) := by
    rw [tendsto_pi_nhds]

    intro i

    simpa only [
      h3FourierRealSchwartzFirstDerivativeGraph_derivative
    ] using
      h3W12CutoffSchwartz_lineDeriv_toLp_tendsto
        φ
        (h3AxisOfFin3 i)

  exact
    Filter.Tendsto.prodMk_nhds
      hZero
      hDerivative

/-! ## Close the exact W¹,² density frontier -/

/-- Transported compact weak tests are dense among real Schwartz tests in the
first-derivative `L²` graph topology. -/
theorem H3TransportedWeakTestsDenseInRealW12Schwartz_proved :
    H3TransportedWeakTestsDenseInRealW12Schwartz := by
  intro φ

  exact
    mem_closure_of_tendsto
      (h3W12CutoffSchwartz_firstDerivativeGraph_tendsto φ)
      (Eventually.of_forall
        (fun n =>
          h3W12CutoffSchwartz_firstDerivativeGraph_mem_range
            n φ))

end

end Euclidean
end Bridge
end PrimeTensor
