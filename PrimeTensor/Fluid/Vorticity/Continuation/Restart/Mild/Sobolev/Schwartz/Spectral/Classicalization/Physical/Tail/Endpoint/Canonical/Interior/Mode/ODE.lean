import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Closed.Mode.ODE

/-!
# Classicalization: endpoint canonical interior mode ODE reduction

`PhysicalTailEndpointCanonicalClosedModeODE` showed that a concrete heat--Leray
mode ODE on the entire closed elapsed interval is sufficient to discharge raw
Fourier mode continuity.

That implication is correct, but it is stronger than the PDE-side statement we
should try to prove.  The globally indexed physical path is obtained by
clamping outside `[0,τ]`.  At `0` and `τ`, a two-sided `HasDerivAt` statement
for that clamped extension would impose an artificial endpoint compatibility
condition.

The correct interface is weaker:

* the concrete mode ODE holds only on the genuine open physical interval
  `(0,τ)`;
* each raw Fourier coordinate is continuous *within* `[0,τ]` at the two
  endpoints.

Interior differentiability supplies all remaining continuity automatically.
Thus every positive subinterval `[0,q]`, `q ≤ τ`, has the continuity required
by variation of constants.

This file is purely topological/calculus bookkeeping.  It introduces no new
Fourier representative theorem and no PDE identity.  In particular, the
endpoint within-continuity hypotheses remain explicit; they must eventually be
handled in a quotient-safe way rather than inferred from Banach `L²`
continuity by point evaluation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalInteriorModeODE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Interior concrete mode differentiability plus endpoint within-continuity
gives raw Fourier continuity on every positive closed subinterval. -/
theorem h3FinHeatLerayModeODEAt_open_gives_rawFourier_continuousOn_of_endpoints
    {nu tau : ℝ}
    (W : ℝ → H3SpectralFinVectorState)
    (hZero :
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousWithinAt
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) xi)
          (Set.Icc (0 : ℝ) tau)
          0)
    (hTau :
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousWithinAt
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) xi)
          (Set.Icc (0 : ℝ) tau)
          tau)
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt nu xi W s) :
    ∀ q : ℝ,
      0 < q →
      q ≤ tau →
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) xi)
          (Set.Icc (0 : ℝ) q) := by
  intro q hq hqTau xi i s hs

  have hSubset :
      Set.Icc (0 : ℝ) q ⊆ Set.Icc (0 : ℝ) tau := by
    intro r hr
    exact
      ⟨
        hr.1,
        le_trans hr.2 hqTau
      ⟩

  by_cases hs0 : s = 0
  · subst s
    exact
      (hZero xi i).mono hSubset

  by_cases hsq : s = q
  · subst s

    by_cases hqtau : q = tau
    · subst q
      simpa using hTau xi i

    · have hqLtTau : q < tau := by
        exact lt_of_le_of_ne hqTau hqtau

      have hMode :=
        hODE xi q ⟨hq, hqLtTau⟩

      unfold H3FinHeatLerayModeODEAt at hMode
      unfold H3FinHeatModeODEAt at hMode

      exact
        (hMode i).continuousAt.continuousWithinAt

  · have hsPos : 0 < s := by
      exact
        lt_of_le_of_ne hs.1 (Ne.symm hs0)

    have hsLtQ : s < q := by
      exact
        lt_of_le_of_ne hs.2 hsq

    have hsLtTau : s < tau := by
      exact
        lt_of_lt_of_le hsLtQ hqTau

    have hMode :=
      hODE xi s ⟨hsPos, hsLtTau⟩

    unfold H3FinHeatLerayModeODEAt at hMode
    unfold H3FinHeatModeODEAt at hMode

    exact
      (hMode i).continuousAt.continuousWithinAt

/-- Endpoint physical evolution from the genuine interior mode ODE and
endpoint within-continuity of the raw Fourier coordinates.

This supersedes the closed-mode-ODE frontier as the useful PDE-facing
reduction: no two-sided derivative is requested at a clamp endpoint. -/
theorem h3PreterminalTailPhysicalEvolutionAt_of_endpoint_interior_mode_ODE
    {nu E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hnu : 0 < nu)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hZero :
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousWithinAt
          (fun s : ℝ =>
            h3SpectralScalarRawFourier
              ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                hNS ht htau.le hEnd hE hTail hEndpoint) s i)
              xi)
          (Set.Icc (0 : ℝ) tau)
          0)
    (hTau :
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousWithinAt
          (fun s : ℝ =>
            h3SpectralScalarRawFourier
              ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                hNS ht htau.le hEnd hE hTail hEndpoint) s i)
              xi)
          (Set.Icc (0 : ℝ) tau)
          tau)
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt
            nu xi
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            s) :
    H3PreterminalTailPhysicalEvolutionAt
      hnu
      hNS
      ht
      htau.le
      hEnd
      hE
      hTail := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  apply
    h3PreterminalTailPhysicalEvolutionAt_of_endpoint_mode_continuity_and_ODE
      hnu
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      hEndpoint

  · intro q hq hqTau xi i

    have hContinuous :=
      h3FinHeatLerayModeODEAt_open_gives_rawFourier_continuousOn_of_endpoints
        (nu := nu)
        (tau := tau)
        W
        (by
          intro xi' i'
          dsimp only [W]
          exact hZero xi' i')
        (by
          intro xi' i'
          dsimp only [W]
          exact hTau xi' i')
        (by
          intro xi' s hs
          dsimp only [W]
          exact hODE xi' s hs)
        q
        hq
        hqTau
        xi
        i

    simpa only [W] using hContinuous

  · intro xi s hs
    exact hODE xi s hs

end

end Euclidean
end Bridge
end PrimeTensor
