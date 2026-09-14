import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureOldFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.L2.Jet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity

/-!
# Ordered-third endpoint continuity from weighted H³ spectral continuity

The remaining ordered-third physical `L²` frontier does not need to be treated
as 81 unrelated coordinate-continuity statements.

For two old H³ snapshots, `Spectral.Difference.Energy` already proves the exact
identity

    ‖G(q) - G(r)‖²
      =
    ‖F₀(q)-F₀(r)‖²
      + Σ ‖F₁(q)-F₁(r)‖²
      + Σ ‖F₂(q)-F₂(r)‖²
      + Σ ‖F₃(q)-F₃(r)‖².

Therefore every single ordered third Fourier jet satisfies

    ‖F₃ᵢₖₗ(q)-F₃ᵢₖₗ(r)‖
      ≤
    ‖G(q)-G(r)‖.

Plancherel is an exact isometry, so the same estimate holds for the physical
`L²` third jet.  Consequently continuity of the weighted H³ spectral state on
the closed elapsed interval closes the complete ordered-third physical `L²`
continuity target.

This file introduces no new PDE estimate.  It turns the third branch into one
Banach-valued continuity frontier.  Combined with the previous zeroth-order
work, the current continuation theorem is reduced to:

* the old preterminal pressure-gradient mass frontier; and
* weighted H³ spectral-state continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdSpectralContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One ordered third Fourier-jet difference is bounded by the complete
weighted H³ spectral difference of the same velocity component. -/
theorem norm_h3PreterminalCanonicalFourierJetOnElapsed_slot3_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (j i k l : Fin 3)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) q
        -
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r j‖ := by
  have hEnergy :
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2
        =
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) r‖ ^ 2
        +
      (∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) r‖ ^ 2) := by
    exact
      norm_velocityH3SpectralScalarAt_sub_sq
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail r)
        j

  have hL :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖ ^ 2
        ≤
      ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k c) r‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun c _ =>
          sq_nonneg
            ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j i k c) q
              -
             h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j i k c) r‖)
        (Finset.mem_univ l)

  have hK :
      (∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k c) r‖ ^ 2)
        ≤
      ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i b c) r‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun b _ =>
          Finset.sum_nonneg
            (fun c _ =>
              sq_nonneg
                ‖h3PreterminalCanonicalFourierJetOnElapsed
                    hNS ht hEnd hTail (h3JetSlot3 j i b c) q
                  -
                 h3PreterminalCanonicalFourierJetOnElapsed
                    hNS ht hEnd hTail (h3JetSlot3 j i b c) r‖))
        (Finset.mem_univ k)

  have hI :
      (∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i b c) r‖ ^ 2)
        ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun a _ =>
          Finset.sum_nonneg
            (fun b _ =>
              Finset.sum_nonneg
                (fun c _ =>
                  sq_nonneg
                    ‖h3PreterminalCanonicalFourierJetOnElapsed
                        hNS ht hEnd hTail (h3JetSlot3 j a b c) q
                      -
                     h3PreterminalCanonicalFourierJetOnElapsed
                        hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖)))
        (Finset.mem_univ i)

  have hThird :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖ ^ 2
        ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2 :=
    hL.trans (hK.trans hI)

  have h0 :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2 :=
    sq_nonneg _

  have h1 :
      0 ≤
      ∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ => sq_nonneg _)

  have h2 :
      0 ≤
      ∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ => sq_nonneg _))

  have hSq :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖ ^ 2
        ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2 := by
    calc
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖ ^ 2
          ≤
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2 :=
        hThird
      _ ≤
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2)
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2)
          +
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2) := by
        nlinarith
      _ =
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j
            -
          h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail r j‖ ^ 2 :=
        hEnergy.symm

  have hLeftNonneg :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖ :=
    norm_nonneg _

  have hRightNonneg :
      0 ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ :=
    norm_nonneg _

  nlinarith

/-- The same difference estimate in the physical `L²(Point3)` third-jet
coordinate, by exact scalar Plancherel isometry. -/
theorem norm_h3PreterminalCanonicalL2JetOnElapsed_slot3_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (j i k l : Fin 3)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) q
        -
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r j‖ := by
  have hFourier :=
    norm_h3PreterminalCanonicalFourierJetOnElapsed_slot3_sub_le_spectralCoordinate
      hNS ht hEnd hTail j i k l q r

  calc
    ‖h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) q
        -
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖
        =
      ‖h3ScalarFourierL2
        (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
         h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r)‖ := by
      symm
      exact
        norm_h3ScalarFourierL2
          (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) q
            -
           h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) r)
    _ =
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r‖ := by
      rw [
        h3ScalarFourierL2_sub,
        ← h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
            hNS ht hEnd hTail (h3JetSlot3 j i k l) q,
        ← h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
            hNS ht hEnd hTail (h3JetSlot3 j i k l) r
      ]
    _ ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ :=
      hFourier

/-- Local Banach-valued replacement for the 81-coordinate third continuity
target. -/
def H3PreterminalCanonicalSpectralStateContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  Continuous
    (h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail)

/-- Weighted H³ spectral-state continuity closes every ordered third physical
`L²` jet coordinate. -/
theorem h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_spectralState
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSpectral :
      H3PreterminalCanonicalSpectralStateContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2ThirdContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j i k l

  rw [continuous_iff_continuousAt]
  intro q₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hCoord :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j) :=
    (continuous_apply j).comp hSpectral

  have hSpectralNorm :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q j
              -
            h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q₀ j‖)
        (𝓝 q₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hCoord.continuousAt

  exact
    squeeze_zero
      (fun q =>
        norm_nonneg
          (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) q
            -
           h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j i k l) q₀))
      (fun q =>
        norm_h3PreterminalCanonicalL2JetOnElapsed_slot3_sub_le_spectralCoordinate
          hNS ht hEnd hTail j i k l q q₀)
      hSpectralNorm

/-- Restart-radius weighted H³ spectral-state continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalSpectralStateContinuousOnElapsed
          hNS ht hEnd hTail

/-- Radius-wide spectral continuity closes the existing radius-wide ordered
third physical `L²` frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius_of_spectral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSpectral :
      H3PreterminalTailUnitViscositySpectralContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_spectralState
      hNS ht hEnd hTail
      (hSpectral q hqPos hEnd)

/-- Global weighted H³ spectral-state continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySpectralContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global spectral-state frontier implies the existing global ordered-third
physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_spectral
    (hSpectral :
      H3PreterminalTailUnitViscositySpectralContinuityFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius_of_spectral
      hNS ht hE hTail
      (hSpectral E hE u T t hNS ht hTail)

/-- Current continuation theorem with the two remaining fronts stated as
old-pressure mass and weighted H³ spectral-state continuity. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralContinuityClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hSpectral :
      H3PreterminalTailUnitViscositySpectralContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureThirdContinuityClosed
      hOld
      (h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_spectral
        hSpectral)

end

end Euclidean
end Bridge
end PrimeTensor
