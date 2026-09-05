import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Bochner
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Classicalization: physical `L²` evolution defect orthogonality

`PhysicalTailEndpointCanonicalPhysicalL2RHSBochner` produces two genuine
coordinatewise physical `L²(Point3)` vectors over the full elapsed interval:

* the endpoint velocity increment `U(τ) - U(0)`;
* the Bochner integral `∫₀^τ R(s) ds` of the strongly continuous projected RHS.

The preceding weak FTC theorem says that every compactly supported smooth
**divergence-free** test vector satisfying the isolated temporal-local-
domination hypothesis has the same Hilbert pairing with those two vectors.

This file packages that statement in the correct finite-product Hilbert space.
The ordinary function type `Fin 3 → H3ScalarL2` carries the sup norm, so it is
not the Hilbert product we want.  We therefore use the finite `PiLp 2` wrapper

    PiLp 2 (fun _ : Fin 3 => H3ScalarL2),

whose inner product is the sum of the three coordinate `L²` inner products.

We then define the physical evolution defect

    D := (U(τ) - U(0)) - ∫₀^τ R(s) ds

and prove

    ⟪Φ, D⟫ = 0

for every admissible compact smooth solenoidal test vector `Φ`.

This deliberately stops before claiming `D = 0`.  Divergence-free compact
smooth tests are not dense in the whole vector `L²` space; the next step must
identify the relevant closed solenoidal Hilbert subspace and show that both
terms of `D` lie in it.  Only then can density/nondegeneracy legitimately turn
orthogonality into a vector equality.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPhysicalL2DefectOrthogonality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalPhysicalL2DefectOrthogonality :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Three-component physical real `L²` Hilbert product. -/
abbrev H3PhysicalRealFinVectorL2Hilbert : Type :=
  PiLp 2 (fun _ : Fin 3 => H3ScalarL2)

/-- Compact smooth test vector embedded coordinatewise in the finite physical
`L²` Hilbert product. -/
noncomputable def h3WeakTestVectorPhysicalL2Hilbert
    (φ : H3WeakTestVector) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3WeakTestFunctionPhysicalL2 (φ i))

/-- Endpoint velocity increment bundled in the finite physical `L²` Hilbert
product. -/
noncomputable def h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
        hNS ht htau hEnd hTail i)

/-- Bochner-integrated projected RHS bundled in the finite physical `L²`
Hilbert product. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
        hNS ht htau hEnd hE hTail hEndpoint i)

/-- Physical `L²` evolution defect in the finite Hilbert product. -/
noncomputable def h3PreterminalTailCanonicalPhysicalL2EvolutionDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
      hNS ht htau hEnd hTail
    -
  h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint

/-- Hilbert pairing with the bundled endpoint velocity increment is exactly the
finite sum of coordinatewise physical `L²` pairings used in the weak FTC. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
          hNS ht htau hEnd hTail)
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
          hNS ht htau hEnd hTail i) := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
  rw [PiLp.inner_apply]

/-- Hilbert pairing with the bundled Bochner RHS integral is exactly the finite
sum of coordinatewise physical `L²` pairings. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_bochnerProjectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
          hNS ht htau hEnd hE hTail hEndpoint)
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
          hNS ht htau hEnd hE hTail hEndpoint i) := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
  rw [PiLp.inner_apply]

/-- Every divergence-free compact smooth test vector satisfying the isolated
temporal local-domination hypothesis annihilates the physical `L²` evolution
defect. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefect_eq_zero_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalPhysicalL2EvolutionDefect
          hNS ht htau hEnd hE hTail hEndpoint)
      =
    0 := by
  unfold h3PreterminalTailCanonicalPhysicalL2EvolutionDefect
  rw [inner_sub_right]
  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrement
      hNS ht htau hEnd hTail φ,
    inner_h3WeakTestVectorPhysicalL2Hilbert_bochnerProjectedRHS
      hNS ht htau hEnd hE hTail hEndpoint φ
  ]

  exact
    sub_eq_zero.mpr
      (h3PreterminalTailCanonicalWeakPhysicalL2VelocityIncrement_eq_BochnerProjectedRHS_of_localDomination
        hNS ht htau hEnd hE hTail hEndpoint
        φ hφ hDom)

/-! ## Exact admissible test set at the remaining frontier -/

/-- Physical Hilbert test states currently justified by the old temporal FTC:
compact smooth, divergence-free, and satisfying the explicit local-domination
frontier. -/
noncomputable def h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    Set H3PhysicalRealFinVectorL2Hilbert :=
  { Φ |
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ ∧
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ ∧
      Φ = h3WeakTestVectorPhysicalL2Hilbert φ }

/-- The entire currently admissible physical test set is contained in the
zero-pairing set of the physical evolution defect. -/
theorem h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set_subset_evolutionDefect_zeroPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set
        hNS ht htau hEnd hE hTail hEndpoint
      ⊆
    { Φ : H3PhysicalRealFinVectorL2Hilbert |
      inner ℝ Φ
        (h3PreterminalTailCanonicalPhysicalL2EvolutionDefect
          hNS ht htau hEnd hE hTail hEndpoint) = 0 } := by
  intro Φ hΦ

  change
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ ∧
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ ∧
      Φ = h3WeakTestVectorPhysicalL2Hilbert φ
    at hΦ

  rcases hΦ with ⟨φ, hφ, hDom, rfl⟩

  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefect_eq_zero_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hDom

end

end Euclidean
end Bridge
end PrimeTensor
