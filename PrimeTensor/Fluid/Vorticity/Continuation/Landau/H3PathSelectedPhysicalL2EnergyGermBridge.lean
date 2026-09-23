import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2EnergyAxisBridge

/-!
# Selected physical L² energy: local transport to the old zeroth-order energy

The representation layer is now completely closed:
under selected/old physical agreement,

    ‖S(q)‖² = velocityH3Energy0At u (t + q).

On a strict elapsed interval `[0, tau]` inside the canonical restart radius,
radius-wide selected/old agreement therefore identifies these two scalar
energy paths on an open neighborhood of every interior elapsed time.

The selected physical `L²` energy derivative can consequently be transported
verbatim to the shifted old canonical zeroth-order energy with
`HasDerivAt.congr_of_eventuallyEq`.

No dominated-convergence argument and no differentiation under the spatial
integral is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPhysicalL2EnergyGermBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On every strict elapsed interior point, the selected physical Hilbert
energy and the shifted old canonical zeroth-order energy are the same germ. -/
theorem h3PreterminalSelectedUnitPhysicalL2Energy_eventuallyEq_velocityH3Energy0At_shift
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    (fun r : ℝ =>
      ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail r‖ ^ 2)
      =ᶠ[𝓝 q]
    (fun r : ℝ =>
      velocityH3Energy0At u (t + r)) := by
  have hNeighborhood :
      Set.Ioo (0 : ℝ) tau ∈ 𝓝 q :=
    Ioo_mem_nhds hq.1 hq.2

  filter_upwards [hNeighborhood] with r hr

  let qr :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      r,
      hr.1,
      le_trans hr.2.le htauR
    ⟩

  have hEndr :
      t + (qr : ℝ) < T := by
    dsimp only [qr]
    calc
      t + r < t + tau := by
        simpa only [add_comm] using
          (add_lt_add_left hr.2 t)
      _ < T := hEnd

  exact
    norm_sq_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_velocityH3Energy0At_of_restartRadiusAgreement
      hNS ht hE hTail hPhysical qr hEndr

/-- The strong selected physical `L²` energy derivative transports directly to
the shifted old canonical zeroth-order energy on every strict overlap point. -/
theorem h3PreterminalVelocityH3Energy0At_shift_hasDerivAt_selectedPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivAt
      (fun r : ℝ =>
        velocityH3Energy0At u (t + r))
      (2 * inner ℝ
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR q))
      q := by
  have hSelected :=
    h3PreterminalSelectedUnitPhysicalL2Energy_hasDerivAt
      hNS ht htau hE hTail htauR hq

  exact
    hSelected.congr_of_eventuallyEq
      (h3PreterminalSelectedUnitPhysicalL2Energy_eventuallyEq_velocityH3Energy0At_shift
        hNS ht htau hEnd hE hTail htauR hPhysical hq).symm

/-- Ordinary `deriv` form of the transported shifted zeroth-order energy
identity. -/
theorem deriv_h3PreterminalVelocityH3Energy0At_shift_eq_selectedPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    deriv
        (fun r : ℝ =>
          velocityH3Energy0At u (t + r))
        q
      =
    2 * inner ℝ
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR q) := by
  exact
    (h3PreterminalVelocityH3Energy0At_shift_hasDerivAt_selectedPairing
      hNS ht htau hEnd hE hTail htauR hPhysical hq).deriv

end

end Euclidean
end Bridge
end PrimeTensor
