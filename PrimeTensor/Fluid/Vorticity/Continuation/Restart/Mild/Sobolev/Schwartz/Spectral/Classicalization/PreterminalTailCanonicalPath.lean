import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalCanonicalPath
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.TailFrontier

/-!
# Classicalization: preterminal canonical path from tail H³ data

The corrected tail-aware frontier retains

    CanonicalH3TailDataFrom u t T E,

so the old preterminal solution is already known to be H³-integrable with
canonical energy at most `E` throughout `[t,T)`.

`PreterminalCanonicalPath` previously asked separately for

* H³ integrability at every elapsed slice in `[0,τ]`;
* the canonical energy bound `≤ 2E` there.

For an overlap interval satisfying `t + τ < T`, both statements are immediate
from the retained tail datum.

This file performs exactly that reduction.  The final theorem instantiates
`h3PreterminalSpectralOverlapWitnessAt_of_canonicalPath` directly from the tail
H³ data.

After this file, the local overlap witness has only two substantive analytic
inputs left:

1. continuity of the canonical weighted spectral H³ state as a function of
   elapsed time;
2. the restarted heat--Leray mild identity for that path.

The Fourier encoding, H³ persistence, energy control, path bound, endpoint
decoder, and Banach uniqueness bookkeeping are no longer separate hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

/-- Every elapsed slice in `[0,τ]` belongs to the retained old H³ tail when
`t + τ < T`. -/
theorem canonicalH3TailDataFrom_integrableOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    VelocityH3IntegrableAt
      u
      (t + (q : ℝ)) := by
  exact
    (hTail
      (t + (q : ℝ))
      ⟨
        by linarith [q.property.1],
        by linarith [hEnd, q.property.2]
      ⟩).1

/-- The retained canonical energy bound `≤ E` is automatically strong enough
for the `≤ 2E` Picard-ball estimate used by the spectral overlap path. -/
theorem canonicalH3TailDataFrom_energyOnElapsed_le_twoE
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hE : 1 ≤ E)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    velocityH3EnergyAt
        u
        (t + (q : ℝ))
      ≤
    2 * E := by
  have hAt :=
    hTail
      (t + (q : ℝ))
      ⟨
        by linarith [q.property.1],
        by linarith [hEnd, q.property.2]
      ⟩

  exact
    le_trans
      hAt.2
      (by linarith)

/-- Tail H³ data remove the persistence and energy hypotheses from the
canonical preterminal overlap-witness construction.

Only continuity of the canonical spectral state and its restarted mild identity
remain explicit. -/
theorem h3PreterminalSpectralOverlapWitnessAt_of_tailCanonicalPath
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 ≤ τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS
            ht
            hEnd
            (canonicalH3TailDataFrom_integrableOnElapsed
              hEnd hTail)
            q))
    (hMild :
      ∀ s : H3UnitTime,
        h3SpectralVelocityHeatApplyNN
            ν hν.le
            (h3PhysicalTimeNN τ hτ s)
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor
                ht hTail).1)
          +
        h3SpectralFinHeatLerayDuhamel
            ν
            (h3PhysicalTime τ s)
            hν
            (h3PathPhysicalRealExtension
              τ
              (h3SpectralNormalizedPathOfPhysical
                hτ
                (h3PreterminalCanonicalSpectralPhysicalPath
                  hNS
                  ht
                  hEnd
                  hE
                  (canonicalH3TailDataFrom_integrableOnElapsed
                    hEnd hTail)
                  (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
                    hE hEnd hTail)
                  hCont)))
            (h3PathPhysicalRealExtension
              τ
              (h3SpectralNormalizedPathOfPhysical
                hτ
                (h3PreterminalCanonicalSpectralPhysicalPath
                  hNS
                  ht
                  hEnd
                  hE
                  (canonicalH3TailDataFrom_integrableOnElapsed
                    hEnd hTail)
                  (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
                    hE hEnd hTail)
                  hCont)))
          =
        h3PreterminalCanonicalSpectralPhysicalPath
          hNS
          ht
          hEnd
          hE
          (canonicalH3TailDataFrom_integrableOnElapsed
            hEnd hTail)
          (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
            hE hEnd hTail)
          hCont
          (h3PhysicalTimeMap τ hτ s)) :
    H3PreterminalSpectralOverlapWitnessAt
      ν
      E
      hν
      (h3PreterminalCanonicalAnchorSpectralState
        hNS
        ht
        (canonicalH3TailDataFrom_at_anchor
          ht hTail).1)
      u
      t
      τ
      hτ := by
  exact
    h3PreterminalSpectralOverlapWitnessAt_of_canonicalPath
      hν
      hNS
      ht
      hτ
      hEnd
      hE
      (canonicalH3TailDataFrom_at_anchor
        ht hTail).1
      (canonicalH3TailDataFrom_integrableOnElapsed
        hEnd hTail)
      (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
        hE hEnd hTail)
      hCont
      hMild

end
end Euclidean
end Bridge
end PrimeTensor
