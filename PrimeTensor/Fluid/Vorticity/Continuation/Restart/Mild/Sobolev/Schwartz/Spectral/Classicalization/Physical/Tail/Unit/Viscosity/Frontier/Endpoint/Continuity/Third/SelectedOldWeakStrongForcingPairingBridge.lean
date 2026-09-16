import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongPhysicalForcingAdvectionPairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongDifferenceLerayFixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Snapshot

/-!
# Selected--old Leray forcing pairing equals unprojected advection pairing

The generic physical forcing/advection bridge now accepts every Leray-fixed
physical `L²` test state.  This file specializes it to the concrete
selected-minus-old difference

    D(q) = U_selected(q) - U_old(q).

The nonlinear vector already used by the relative-energy reduction is

    NΔ = N_selected - N_old,

where each `N` is the real physical reconstruction of the Leray-projected
outer-product divergence.

For both selected and old spectral slices, the generic physical forcing package
from `SelectedOldWeakStrongPhysicalForcingAdvectionPairing` is definitionally
the same package already used in `NΔ`.  The selected slice is realizable and
raw-divergence-free; the old snapshot has the same two properties.  The
preceding Leray-fixed increment supplies the solenoidal test property of `D`.

Therefore

    ⟪D, NΔ⟫
      =
    ⟪D, A_selected - A_old⟫,

where `A_selected` and `A_old` are the quotient-safe physical `L²`
reconstructions of the *unprojected* nonlinear advection terms.

This is the exact Hilbert-space seam needed before converting the right-hand
side to the classical weak--strong interaction and applying transport
cancellation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongForcingPairingBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The generic physical Leray-forcing Hilbert vector is exactly the selected
unit-viscosity Leray-forcing package already used by the RHS difference. -/
theorem h3WeakStrongLerayForcingPhysicalL2Hilbert_selectedUnit_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3WeakStrongLerayForcingPhysicalL2Hilbert
        (h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail q)
      =
    h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
      hNS ht hE hTail q := by
  apply PiLp.ext
  intro i
  rfl

/-- The generic physical Leray-forcing Hilbert vector is exactly the old
snapshot Leray-forcing package already used by the RHS difference. -/
theorem h3WeakStrongLerayForcingPhysicalL2Hilbert_oldElapsed_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3WeakStrongLerayForcingPhysicalL2Hilbert
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
      =
    h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q := by
  apply PiLp.ext
  intro i
  rfl

/-- The selected unit-viscosity restart slice is physically realizable. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_realizable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3SpectralVelocityRealizable
      (h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail q) := by
  exact
    h3SpectralVelocityRawHermitian_realizable
      (h3PreterminalSelectedUnitSpectralStateOnRadius_rawHermitian
        hNS ht hE hTail q)

/-- The selected unit-viscosity restart slice is raw-Fourier divergence-free. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_rawDivergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3SpectralFinRawDivergenceFree
      (h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail q) := by
  exact
    h3SpectralFinRawDivergenceFree_of_divergenceFree
      (h3PreterminalSelectedUnitSpectralStateOnRadius_divergenceFree
        hNS ht hE hTail q)

/-- Pairing the concrete selected-minus-old difference with the selected
Leray forcing is the same as pairing it with the selected unprojected physical
advection vector. -/
theorem inner_selectedOldDifference_selectedUnitLerayForcing_eq_advection
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    let qR :=
      h3PreterminalElapsedToSelectedUnitRadius htauR q
    let USel :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail qR
    let D :=
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
    inner ℝ
        D
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
          hNS ht hE hTail qR)
      =
    inner ℝ
        D
        (h3WeakStrongAdvectionPhysicalL2Hilbert USel) := by
  dsimp only

  let qR :=
    h3PreterminalElapsedToSelectedUnitRadius htauR q

  let USel :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail qR

  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  have hD :
      H3PhysicalRealFinVectorL2HilbertLerayFixed D := by
    dsimp only [D]
    exact
      h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_lerayFixed
        hNS ht hEnd hE hTail htauR q

  have hPair :
      inner ℝ
          D
          (h3WeakStrongLerayForcingPhysicalL2Hilbert USel)
        =
      inner ℝ
          D
          (h3WeakStrongAdvectionPhysicalL2Hilbert USel) := by
    exact
      inner_weakStrongLerayForcing_eq_advection_of_lerayFixed
        USel
        (by
          dsimp only [USel]
          exact
            h3PreterminalSelectedUnitSpectralStateOnRadius_realizable
              hNS ht hE hTail qR)
        (by
          dsimp only [USel]
          exact
            h3PreterminalSelectedUnitSpectralStateOnRadius_rawDivergenceFree
              hNS ht hE hTail qR)
        D
        hD

  rw [
    h3WeakStrongLerayForcingPhysicalL2Hilbert_selectedUnit_eq
      hNS ht hE hTail qR
  ] at hPair

  exact hPair

/-- Pairing the concrete selected-minus-old difference with the old Leray
forcing is the same as pairing it with the old unprojected physical advection
vector. -/
theorem inner_selectedOldDifference_oldLerayForcing_eq_advection
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    let UOld :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q
    let D :=
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
    inner ℝ
        D
        (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    inner ℝ
        D
        (h3WeakStrongAdvectionPhysicalL2Hilbert UOld) := by
  dsimp only

  let UOld :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  have hD :
      H3PhysicalRealFinVectorL2HilbertLerayFixed D := by
    dsimp only [D]
    exact
      h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_lerayFixed
        hNS ht hEnd hE hTail htauR q

  have hPair :
      inner ℝ
          D
          (h3WeakStrongLerayForcingPhysicalL2Hilbert UOld)
        =
      inner ℝ
          D
          (h3WeakStrongAdvectionPhysicalL2Hilbert UOld) := by
    exact
      inner_weakStrongLerayForcing_eq_advection_of_lerayFixed
        UOld
        (by
          dsimp only [UOld]
          exact
            h3PreterminalTailCanonicalSpectralStateOnElapsed_realizable
              hNS ht hEnd hTail q)
        (by
          dsimp only [UOld]
          exact
            h3PreterminalTailCanonicalSpectralStateOnElapsed_rawDivergenceFree
              hNS ht hEnd hTail q)
        D
        hD

  rw [
    h3WeakStrongLerayForcingPhysicalL2Hilbert_oldElapsed_eq
      hNS ht hEnd hTail q
  ] at hPair

  exact hPair

/-- The concrete Leray-forcing difference pairing is exactly the difference of
the two unprojected physical advection pairings. -/
theorem inner_selectedOldUnitLerayForcingDifference_eq_advectionDifference
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    let qR :=
      h3PreterminalElapsedToSelectedUnitRadius htauR q
    let USel :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail qR
    let UOld :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q
    let D :=
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
    inner ℝ
        D
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      =
    inner ℝ
        D
        (h3WeakStrongAdvectionPhysicalL2Hilbert USel
          -
         h3WeakStrongAdvectionPhysicalL2Hilbert UOld) := by
  dsimp only

  let qR :=
    h3PreterminalElapsedToSelectedUnitRadius htauR q

  let USel :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail qR

  let UOld :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  unfold
    h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed

  rw [inner_sub_right, inner_sub_right]

  rw [
    inner_selectedOldDifference_selectedUnitLerayForcing_eq_advection
      hNS ht hEnd hE hTail htauR q,
    inner_selectedOldDifference_oldLerayForcing_eq_advection
      hNS ht hEnd hE hTail htauR q
  ]

end

end Euclidean
end Bridge
end PrimeTensor
