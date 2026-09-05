import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Variation.Of.Constants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.State
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Evolution

/-!
# Classicalization: endpoint canonical restarted mild equation

`PhysicalTailEndpointCanonicalVariationOfConstants` proves the retarded H³
variation-of-constants identity for one positive physical target time.

The overlap API, however, consumes the restarted mild equation at every
normalized time `s ∈ [0,1]`.  This file packages the positive-target theorem
into that exact interface.

For `q = τ s > 0`, the previous variation-of-constants theorem applies and the
normalized-real extension is identified back with the physical endpoint path.

For `q = 0`, the heat operator is the identity, the Duhamel integral vanishes,
and the endpoint physical path is exactly the retained spectral anchor.

Thus no new PDE or Fourier analysis is introduced.  The only remaining inputs
are the same three positive-time mode hypotheses:

* raw Fourier mode continuity;
* the finite heat--Leray mode ODE;
* weighted forcing interval integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The complete restarted mild identity for the endpoint-only canonical
preterminal path, reduced to the three positive-time Fourier-mode inputs. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_mild_of_mode_data
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
    (hFContinuous :
      ∀ q : ℝ,
        0 < q →
        q ≤ tau →
        ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
          ContinuousOn
            (fun s : ℝ =>
              h3SpectralScalarRawFourier
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s i)
                xi)
            (Set.Icc (0 : ℝ) q))
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt
            nu xi
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            s)
    (hWeightedForcing :
      ∀ q : ℝ,
        0 < q →
        q ≤ tau →
        ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
          IntervalIntegrable
            (fun s : ℝ =>
              Real.exp
                  (nu * h3FourierGradientSquare xi * s)
                •
              h3RawFinLerayOuterProductDivergence
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s)
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s)
                i xi)
            volume
            0
            q) :
    ∀ s : H3UnitTime,
      h3SpectralVelocityHeatApplyNN
          nu hnu.le
          (h3PhysicalTimeNN tau htau.le s)
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        -
      h3SpectralFinHeatLerayDuhamel
          nu
          (h3PhysicalTime tau s)
          hnu
          (h3PathPhysicalRealExtension
            tau
            (h3SpectralNormalizedPathOfPhysical
              htau.le
              (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                hNS ht hEnd hE hTail hEndpoint)))
          (h3PathPhysicalRealExtension
            tau
            (h3SpectralNormalizedPathOfPhysical
              htau.le
              (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                hNS ht hEnd hE hTail hEndpoint)))
        =
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint
        (h3PhysicalTimeMap tau htau.le s) := by
  intro s

  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let W : ℝ → H3SpectralVelocityState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let q : ℝ :=
    h3PhysicalTime tau s

  have hqMem :
      q ∈ Set.Icc (0 : ℝ) tau := by
    dsimp only [q]
    exact h3PhysicalTime_mem_Icc htau.le s

  by_cases hq0 : q = 0

  · have hqNN :
        h3PhysicalTimeNN tau htau.le s = 0 := by
      apply Subtype.ext
      exact hq0

    let q0 : Set.Icc (0 : ℝ) tau :=
      ⟨0, le_rfl, htau.le⟩

    have hMapZero :
        h3PhysicalTimeMap tau htau.le s = q0 := by
      apply Subtype.ext
      exact hq0

    have hPzero :
        P q0
          =
        h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1 := by
      dsimp only [P, q0]
      exact
        h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_zero
          hNS ht htau.le hEnd hE hTail hEndpoint

    rw [hqNN]
    rw [h3SpectralVelocityHeatApplyNN_zero]
    rw [show h3PhysicalTime tau s = 0 by exact hq0]
    rw [h3SpectralFinHeatLerayDuhamel_zero]
    simp only [sub_zero]
    rw [hMapZero]

    exact hPzero.symm

  · have hqPos : 0 < q := by
      exact
        lt_of_le_of_ne
          hqMem.1
          (Ne.symm hq0)

    have hqTau : q ≤ tau :=
      hqMem.2

    have hODEq :
        ∀ xi : H3FourierPoint3,
          ∀ r ∈ Set.Ioo (0 : ℝ) q,
            H3FinHeatLerayModeODEAt
              nu xi W r := by
      intro xi r hr
      dsimp only [W]
      exact
        hODE xi r
          ⟨hr.1, lt_of_lt_of_le hr.2 hqTau⟩

    have hVoC :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_variationOfConstants
        (nu := nu)
        (E := E)
        (u := u)
        (T := T)
        (t := t)
        (tau := tau)
        (q := q)
        hnu
        hNS
        ht
        htau
        hEnd
        hE
        hTail
        hEndpoint
        hqPos
        hqTau
        (hFContinuous q hqPos hqTau)
        hODEq
        (hWeightedForcing q hqPos hqTau)

    have hqNN :
        NNReal.mk q hqPos.le
          =
        h3PhysicalTimeNN tau htau.le s := by
      apply Subtype.ext
      rfl

    have hRecover :
        W q
          =
        P (h3PhysicalTimeMap tau htau.le s) := by
      dsimp only [W, q, P]
      exact
        h3PathPhysicalRealExtension_normalizedPhysical_apply
          htau
          (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint)
          (h3PhysicalTimeMap tau htau.le s)

    have hVoC' :
        W q
          =
        h3SpectralVelocityHeatApplyNN
            nu hnu.le
            (h3PhysicalTimeNN tau htau.le s)
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1)
          -
        h3SpectralFinHeatLerayDuhamel
          nu q hnu W W := by
      simpa only [hqNN] using hVoC

    have hMild :=
      hVoC'.symm.trans hRecover

    simpa only [
      W,
      q,
      P,
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    ] using hMild

/-- A local endpoint physical-evolution package follows from endpoint `L²`
continuity plus the three Fourier-mode inputs. -/
theorem h3PreterminalTailPhysicalEvolutionAt_of_endpoint_mode_data
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
    (hFContinuous :
      ∀ q : ℝ,
        0 < q →
        q ≤ tau →
        ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
          ContinuousOn
            (fun s : ℝ =>
              h3SpectralScalarRawFourier
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s i)
                xi)
            (Set.Icc (0 : ℝ) q))
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt
            nu xi
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            s)
    (hWeightedForcing :
      ∀ q : ℝ,
        0 < q →
        q ≤ tau →
        ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
          IntervalIntegrable
            (fun s : ℝ =>
              Real.exp
                  (nu * h3FourierGradientSquare xi * s)
                •
              h3RawFinLerayOuterProductDivergence
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s)
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s)
                i xi)
            volume
            0
            q) :
    H3PreterminalTailPhysicalEvolutionAt
      hnu
      hNS
      ht
      htau.le
      hEnd
      hE
      hTail := by
  refine
    ⟨
      hEndpoint,
      ?_
    ⟩

  exact
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_mild_of_mode_data
      hnu
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      hEndpoint
      hFContinuous
      hODE
      hWeightedForcing

end

end Euclidean
end Bridge
end PrimeTensor
