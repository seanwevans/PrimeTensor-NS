import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.DuhamelIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Semigroup

/-!
# Incompressibility of finite H³ heat--Leray mild paths

The previous two incompressibility rungs prove:

* every state in the range of the finite Leray projector is Fourier
  divergence-free;
* the genuine heat--Leray Duhamel integral is Leray-fixed, hence
  divergence-free.

The linear heat term requires no new Fourier-symbol calculation.  The existing
semigroup layer proves

    H_t (P G) = P (H_t G).

Thus a divergence-free initial state, equivalently a Leray-fixed state, stays
Leray-fixed under heat.

Since the lifted Leray projector is additive, the sum of the heat term and
Duhamel term is again fixed by Leray.  Therefore every path satisfying the
origin-based mild identity

    H_t U₀ + D_t(W,W) = W(t)

is divergence-free at that time, provided the initial state is
divergence-free and the already-required Duhamel integrability holds.

This file is deliberately independent of the selected Picard construction.
The result applies to any finite H³ heat--Leray mild path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3FinLerayMildIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Ordinary spectral heat evolution preserves the finite Fourier
divergence-free subspace. -/
theorem h3SpectralVelocityHeatApplyNN_divergenceFree
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralFinDivergenceFree G) :
    H3SpectralFinDivergenceFree
      (h3SpectralVelocityHeatApplyNN ν hν t G) := by
  apply h3SpectralFinDivergenceFree_of_lerayFixed

  calc
    h3SpectralFinLerayApply
        (h3SpectralVelocityHeatApplyNN ν hν t G)
        =
      h3SpectralVelocityHeatApplyNN
        ν hν t
        (h3SpectralFinLerayApply G) := by
          exact
            (h3SpectralVelocityHeatApplyNN_finLeray_commute
              ν hν t G).symm
    _ =
      h3SpectralVelocityHeatApplyNN ν hν t G := by
        rw [h3SpectralFinLerayApply_eq_of_divergenceFree hG]

/-- The finite Fourier divergence-free subspace is closed under addition. -/
theorem h3SpectralFinDivergenceFree_add
    {G H : H3SpectralFinVectorState}
    (hG : H3SpectralFinDivergenceFree G)
    (hH : H3SpectralFinDivergenceFree H) :
    H3SpectralFinDivergenceFree (G + H) := by
  apply h3SpectralFinDivergenceFree_of_lerayFixed

  calc
    h3SpectralFinLerayApply (G + H)
        =
      h3SpectralFinLerayApply G
        +
      h3SpectralFinLerayApply H := by
          exact h3SpectralFinLerayApply_add G H
    _ = G + H := by
      rw [
        h3SpectralFinLerayApply_eq_of_divergenceFree hG,
        h3SpectralFinLerayApply_eq_of_divergenceFree hH
      ]

/-- One origin-based finite heat--Leray mild identity propagates
incompressibility from the initial state to time `t`. -/
theorem h3SpectralFinHeatLerayMild_divergenceFree
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (Uinit : H3SpectralFinVectorState)
    (W : ℝ → H3SpectralFinVectorState)
    (hInit : H3SpectralFinDivergenceFree Uinit)
    (hMild :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t ht) Uinit
        +
      h3SpectralFinHeatLerayDuhamel
          ν t hν W W
        =
      W t)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν W W)
        volume
        0
        t) :
    H3SpectralFinDivergenceFree (W t) := by
  have hHeat :
      H3SpectralFinDivergenceFree
        (h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t ht) Uinit) :=
    h3SpectralVelocityHeatApplyNN_divergenceFree
      ν hν.le (NNReal.mk t ht) hInit

  have hDuhamel :
      H3SpectralFinDivergenceFree
        (h3SpectralFinHeatLerayDuhamel
          ν t hν W W) :=
    h3SpectralFinHeatLerayDuhamel_divergenceFree
      hν ht W W hInt

  have hSum :
      H3SpectralFinDivergenceFree
        (
          h3SpectralVelocityHeatApplyNN
              ν hν.le (NNReal.mk t ht) Uinit
            +
          h3SpectralFinHeatLerayDuhamel
              ν t hν W W
        ) :=
    h3SpectralFinDivergenceFree_add
      hHeat hDuhamel

  rw [hMild] at hSum

  exact hSum

/-- Uniform version: an origin-based mild path with integrable Duhamel kernel
at every nonnegative time remains divergence-free for all nonnegative time. -/
theorem h3SpectralFinHeatLerayMild_divergenceFree_of_forall
    {ν : ℝ}
    (hν : 0 < ν)
    (Uinit : H3SpectralFinVectorState)
    (W : ℝ → H3SpectralFinVectorState)
    (hInit : H3SpectralFinDivergenceFree Uinit)
    (hMild :
      ∀ (t : ℝ) (ht : 0 ≤ t),
        h3SpectralVelocityHeatApplyNN
            ν hν.le (NNReal.mk t ht) Uinit
          +
        h3SpectralFinHeatLerayDuhamel
            ν t hν W W
          =
        W t)
    (hInt :
      ∀ (t : ℝ) (ht : 0 ≤ t),
        IntervalIntegrable
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν W W)
          volume
          0
          t) :
    ∀ (t : ℝ), 0 ≤ t →
      H3SpectralFinDivergenceFree (W t) := by
  intro t ht

  exact
    h3SpectralFinHeatLerayMild_divergenceFree
      hν ht Uinit W hInit
      (hMild t ht)
      (hInt t ht)

end
end Euclidean
end Bridge
end PrimeTensor
