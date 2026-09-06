import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Derivative

/-!
# Classicalization: isolate the exact W¹,² density frontier

`Schwartz.Derivative` proved that weak physical curl-freeness already gives the
three tempered curl identities on every transported compact weak test.

For the specific tempered distributions occurring here, full density in the
Schwartz topology is stronger than necessary.  A first distributional
derivative of an `L²` field acts continuously on the first-derivative `L²`
graph norm.  Thus the exact analytic statement needed is only:

    compact smooth tests are dense among Schwartz tests
    in the real W¹,² graph topology.

This file packages that graph topology concretely and proves the generic
closed-hyperplane extension lemma.  No cutoff construction is used yet; the
next analytic checkpoint can focus solely on proving membership in the closure
of the compact-test graph.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzSobolev
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The real first-derivative L² graph -/

/-- Zeroth-order real `L²` data together with the three coordinate first
derivatives in real `L²`. -/
abbrev H3FourierRealFirstDerivativeGraphSpace : Type :=
  H3FourierRealL2 × (Fin 3 → H3FourierRealL2)

/-- The `W¹,²` graph of a real Schwartz function on the Euclidean carrier. -/
noncomputable def h3FourierRealSchwartzFirstDerivativeGraph
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    H3FourierRealFirstDerivativeGraphSpace :=
  ⟨
    φ.toLp 2 volume,
    fun i : Fin 3 =>
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
        𝓢(H3FourierPoint3, ℝ)).toLp 2 volume
  ⟩

@[simp]
theorem h3FourierRealSchwartzFirstDerivativeGraph_zero
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    (h3FourierRealSchwartzFirstDerivativeGraph φ).1
      =
    φ.toLp 2 volume := by
  rfl

@[simp]
theorem h3FourierRealSchwartzFirstDerivativeGraph_derivative
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (i : Fin 3) :
    (h3FourierRealSchwartzFirstDerivativeGraph φ).2 i
      =
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
      𝓢(H3FourierPoint3, ℝ)).toLp 2 volume := by
  rfl

/-- The same graph for a transported compact physical weak test. -/
noncomputable def h3WeakTestFourierRealFirstDerivativeGraph
    (ψ : H3WeakTestFunction) :
    H3FourierRealFirstDerivativeGraphSpace :=
  h3FourierRealSchwartzFirstDerivativeGraph
    (h3WeakTestToFourierRealSchwartz ψ)

@[simp]
theorem h3WeakTestFourierRealFirstDerivativeGraph_zero
    (ψ : H3WeakTestFunction) :
    (h3WeakTestFourierRealFirstDerivativeGraph ψ).1
      =
    (h3WeakTestToFourierRealSchwartz ψ).toLp 2 volume := by
  rfl

/-- The derivative coordinate of the weak-test graph is exactly the transported
weak derivative already identified in `Schwartz.Derivative`. -/
theorem h3WeakTestFourierRealFirstDerivativeGraph_derivative
    (ψ : H3WeakTestFunction)
    (i : Fin 3) :
    (h3WeakTestFourierRealFirstDerivativeGraph ψ).2 i
      =
    (h3WeakTestToFourierRealSchwartz
      (h3WeakTestFunctionSpatialDerivative
        (h3AxisOfFin3 i) ψ)).toLp 2 volume := by
  unfold h3WeakTestFourierRealFirstDerivativeGraph
  rw [h3FourierRealSchwartzFirstDerivativeGraph_derivative]
  rw [h3WeakTestToFourierRealSchwartz_lineDeriv]

/-! ## Exact W¹,² density frontier -/

/-- Every real Schwartz first-derivative graph lies in the closure of the
graphs of transported compact weak tests.

This is precisely the compact-cutoff approximation statement needed by the
curl argument.  It is deliberately weaker than density of compact tests in the
full Schwartz topology. -/
def H3TransportedWeakTestsDenseInRealW12Schwartz : Prop :=
  ∀ φ : 𝓢(H3FourierPoint3, ℝ),
    h3FourierRealSchwartzFirstDerivativeGraph φ
      ∈
    closure
      (Set.range h3WeakTestFourierRealFirstDerivativeGraph)

/-! ## Closed-hyperplane extension -/

/-- Equality of two first-derivative `L²` pairings on every compact weak-test
graph extends to every real Schwartz graph under the exact `W¹,²` density
frontier.

This is the functional-analytic mechanism needed for each of the three curl
identities. -/
theorem h3FourierReal_firstDerivative_pairing_eq_of_transportW12Dense
    (hDense :
      H3TransportedWeakTestsDenseInRealW12Schwartz)
    (F G : H3FourierRealL2)
    (a b : Fin 3)
    (hWeak :
      ∀ ψ : H3WeakTestFunction,
        inner ℝ
            F
            ((h3WeakTestFourierRealFirstDerivativeGraph ψ).2 a)
          =
        inner ℝ
            G
            ((h3WeakTestFourierRealFirstDerivativeGraph ψ).2 b))
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    inner ℝ
        F
        ((h3FourierRealSchwartzFirstDerivativeGraph φ).2 a)
      =
    inner ℝ
        G
        ((h3FourierRealSchwartzFirstDerivativeGraph φ).2 b) := by
  let K : Set H3FourierRealFirstDerivativeGraphSpace :=
    {z |
      inner ℝ F (z.2 a)
        =
      inner ℝ G (z.2 b)}

  have hLeft :
      Continuous
        (fun z : H3FourierRealFirstDerivativeGraphSpace =>
          inner ℝ F (z.2 a)) := by
    exact
      continuous_const.inner
        ((continuous_apply a).comp continuous_snd)

  have hRight :
      Continuous
        (fun z : H3FourierRealFirstDerivativeGraphSpace =>
          inner ℝ G (z.2 b)) := by
    exact
      continuous_const.inner
        ((continuous_apply b).comp continuous_snd)

  have hKClosed : IsClosed K := by
    exact isClosed_eq hLeft hRight

  have hRange :
      Set.range h3WeakTestFourierRealFirstDerivativeGraph
        ⊆
      K := by
    rintro z ⟨ψ, rfl⟩
    exact hWeak ψ

  exact
    (closure_minimal hRange hKClosed)
      (hDense φ)

/-- Expanded coordinate-derivative form of the preceding closed-hyperplane
extension theorem. -/
theorem h3FourierReal_lineDeriv_pairing_eq_of_transportW12Dense
    (hDense :
      H3TransportedWeakTestsDenseInRealW12Schwartz)
    (F G : H3FourierRealL2)
    (a b : Fin 3)
    (hWeak :
      ∀ ψ : H3WeakTestFunction,
        inner ℝ
            F
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 a)}
                (h3WeakTestToFourierRealSchwartz ψ) :
              𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
          =
        inner ℝ
            G
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 b)}
                (h3WeakTestToFourierRealSchwartz ψ) :
              𝓢(H3FourierPoint3, ℝ)).toLp 2 volume))
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    inner ℝ
        F
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 a)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        G
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 b)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume) := by
  have hWeakGraph :
      ∀ ψ : H3WeakTestFunction,
        inner ℝ
            F
            ((h3WeakTestFourierRealFirstDerivativeGraph ψ).2 a)
          =
        inner ℝ
            G
            ((h3WeakTestFourierRealFirstDerivativeGraph ψ).2 b) := by
    intro ψ
    simpa only [
      h3WeakTestFourierRealFirstDerivativeGraph,
      h3FourierRealSchwartzFirstDerivativeGraph_derivative
    ] using hWeak ψ

  simpa only [
    h3FourierRealSchwartzFirstDerivativeGraph_derivative
  ] using
    h3FourierReal_firstDerivative_pairing_eq_of_transportW12Dense
      hDense F G a b hWeakGraph φ

end

end Euclidean
end Bridge
end PrimeTensor
