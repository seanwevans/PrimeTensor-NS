import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralEndpointThirdJetL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalL2JetContinuity

/-!
# Classicalization: reduced physical L² endpoint continuity

The integrated endpoint estimate shows that the complete weighted H³ spectral
distance only needs continuity of

* the zeroth-order velocity Fourier slot, and
* the ordered third-order velocity Fourier slots.

The first- and second-order jet coordinates are therefore not independent
time-topology hypotheses.

This file states the reduced continuity requirement directly in the physical
`H3ScalarL2` jet and transports it through the already-compiled scalar
Plancherel map.

No Navier--Stokes evolution identity is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalL2EndpointContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Strong continuity of only the physical zeroth and ordered third H³ `L²`
jet coordinates on the elapsed overlap interval. -/
def H3PreterminalCanonicalL2EndpointContinuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j : Fin 3,
    Continuous
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j))
      ∧
    ∀ i k l : Fin 3,
      Continuous
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l))

/-- Fourier-side version of the reduced zeroth/third endpoint continuity
predicate. -/
def H3PreterminalCanonicalFourierEndpointContinuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j : Fin 3,
    Continuous
      (h3PreterminalCanonicalFourierJetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j))
      ∧
    ∀ i k l : Fin 3,
      Continuous
        (h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l))

/-- The previous all-jet continuity hypothesis immediately implies the reduced
endpoint continuity hypothesis. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_l2Jet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j
  constructor
  · exact hL2 (h3JetSlot0 j)
  · intro i k l
    exact hL2 (h3JetSlot3 j i k l)

/-- Continuity of one physical elapsed `L²` jet coordinate transports through
the scalar Plancherel map to continuity of the matching Fourier jet
coordinate. -/
theorem continuous_h3PreterminalCanonicalFourierJetOnElapsed_of_l2Coordinate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (a : H3JetIndex)
    (hPhysical :
      Continuous
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a)) :
    Continuous
      (h3PreterminalCanonicalFourierJetOnElapsed
        hNS ht hEnd hTail a) := by
  have hFourier :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3ScalarFourierL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q)) :=
    continuous_h3ScalarFourierL2.comp
      hPhysical

  have hEq :
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail a
        =
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3ScalarFourierL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a q)) := by
    funext q
    exact
      h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
        hNS ht hEnd hTail a q

  rw [hEq]
  exact hFourier

/-- Reduced physical endpoint continuity transports coordinatewise through
Plancherel to reduced Fourier endpoint continuity. -/
theorem h3PreterminalCanonicalFourierEndpointContinuousOnElapsed_of_l2Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalFourierEndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j
  rcases hEndpoint j with ⟨h0, h3⟩
  constructor
  · exact
      continuous_h3PreterminalCanonicalFourierJetOnElapsed_of_l2Coordinate
        hNS ht hEnd hTail (h3JetSlot0 j) h0
  · intro i k l
    exact
      continuous_h3PreterminalCanonicalFourierJetOnElapsed_of_l2Coordinate
        hNS ht hEnd hTail (h3JetSlot3 j i k l) (h3 i k l)

end

end Euclidean
end Bridge
end PrimeTensor
