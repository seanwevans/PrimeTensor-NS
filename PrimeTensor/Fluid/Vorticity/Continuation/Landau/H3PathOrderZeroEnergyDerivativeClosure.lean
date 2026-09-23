import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedOrderZeroCoefficientBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.H3PathAdmissible
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongCurlWeakFTCGlobalClosure
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Close the canonical zeroth-order H³ energy derivative identity

The remaining order-zero differentiation seam is now purely a translation
issue.

At an arbitrary strict energy-class time `s`, H³-path continuity supplies a
local canonical restart anchor `t₀ < s`.  Choose a slightly longer elapsed
window `tau` that remains simultaneously

* inside the shortened old preterminal interval, and
* inside the unit-viscosity canonical restart radius.

The selected physical energy theorem gives

    d/dr E₀(t₀+r)|_{r=q}
      = 2 ⟪S(q), R_selected(q)⟫,

where `q = s - t₀`.  The selected coefficient bridge identifies the right-hand
side with `velocityH3FormalDerivative0At u s`.

Finally compose with the affine inverse translation

    τ ↦ τ - t₀,

whose derivative is one.  Since `t₀ + (τ - t₀) = τ`, this yields the absolute
canonical identity

    HasDerivAt
      (velocityH3Energy0At u)
      (velocityH3FormalDerivative0At u s)
      s.

No differentiation under the spatial integral is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3PathOrderZeroEnergyDerivativeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical zeroth-order kinetic energy has its exact formal derivative
at every strict time of every H³ energy class. -/
theorem h3PathEnergyClassProducesOrder0EnergyDerivativeIdentity_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy0At u)
      (velocityH3FormalDerivative0At u s)
      s := by
  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans hClass.terminal_start.1 hs.1,
        hs.2
      ⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt hsAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hq0,
      hqR,
      hts,
      hsS
    ⟩

  have hS :
      0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes
      hS
      (le_of_lt hST)

  let q : ℝ :=
    s - t₀

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hqPos :
      0 < q := by
    dsimp only [q]
    exact hq0

  have hqRestart :
      q < R := by
    dsimp only [q, R]
    exact hqR

  have hqTerminal :
      q < S - t₀ := by
    dsimp only [q]
    linarith [hsS]

  let upper : ℝ :=
    min R (S - t₀)

  have hqUpper :
      q < upper := by
    dsimp only [upper]
    exact lt_min hqRestart hqTerminal

  let tau : ℝ :=
    (q + upper) / 2

  have hqTau :
      q < tau := by
    dsimp only [tau]
    linarith [hqUpper]

  have htauUpper :
      tau < upper := by
    dsimp only [tau]
    linarith [hqUpper]

  have htauPos :
      0 < tau :=
    lt_trans hqPos hqTau

  have htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hUpperR :
        upper ≤ R := by
      dsimp only [upper]
      exact min_le_left _ _
    dsimp only [R] at hUpperR
    exact le_trans (le_of_lt htauUpper) hUpperR

  have hEnd :
      t₀ + tau < S := by
    have hUpperTerminal :
        upper ≤ S - t₀ := by
      dsimp only [upper]
      exact min_le_right _ _
    linarith [htauUpper, hUpperTerminal]

  have hqMem :
      q ∈ Set.Ioo (0 : ℝ) tau :=
    ⟨hqPos, hqTau⟩

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₀ hNSShort ht₀ hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₀ hNSShort ht₀ hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u S t₀ hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort
      ht₀
      hE
      hTail
      hWeakFTC

  have hsClassShift :
      t₀ + q ∈ Set.Ioo a T := by
    dsimp only [q]
    simpa only [hts] using hs

  have hShifted :
      HasDerivAt
        (fun r : ℝ =>
          velocityH3Energy0At u (t₀ + r))
        (2 * inner ℝ
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNSShort ht₀ hE hTail q)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNSShort ht₀ hE hTail htauR q))
        q :=
    h3PreterminalVelocityH3Energy0At_shift_hasDerivAt_selectedPairing
      hNSShort ht₀ htauPos hEnd hE hTail
      htauR hPhysical hqMem

  have hCoefficient :
      2 * inner ℝ
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNSShort ht₀ hE hTail q)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNSShort ht₀ hE hTail htauR q)
        =
      velocityH3FormalDerivative0At u (t₀ + q) :=
    two_inner_h3PreterminalSelectedVelocity_selectedProjectedRHS_eq_velocityH3FormalDerivative0At
      hNSShort ht₀ htauPos hEnd hE hTail
      htauR hPhysical hqMem
      hH3 hClass hsClassShift

  have hShiftedFormal :
      HasDerivAt
        (fun r : ℝ =>
          velocityH3Energy0At u (t₀ + r))
        (velocityH3FormalDerivative0At u (t₀ + q))
        q :=
    hShifted.congr_deriv hCoefficient

  have hShiftedAtS :
      HasDerivAt
        (fun r : ℝ =>
          velocityH3Energy0At u (t₀ + r))
        (velocityH3FormalDerivative0At u s)
        q := by
    rw [show t₀ + q = s by
      dsimp only [q]
      exact hts] at hShiftedFormal
    exact hShiftedFormal

  have hBack :
      HasDerivAt
        (fun τ : ℝ => τ - t₀)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t₀

  have hAbsoluteRaw :
      HasDerivAt
        (fun τ : ℝ =>
          velocityH3Energy0At u
            (t₀ + (τ - t₀)))
        (velocityH3FormalDerivative0At u s)
        s := by
    have hComp :=
      hShiftedAtS.comp s hBack

    simpa only [
      Function.comp_def,
      mul_one
    ] using hComp

  have hFunction :
      (fun τ : ℝ =>
        velocityH3Energy0At u
          (t₀ + (τ - t₀)))
        =
      velocityH3Energy0At u := by
    funext τ
    have hTime :
        t₀ + (τ - t₀) = τ := by
      ring
    rw [hTime]

  rw [hFunction] at hAbsoluteRaw
  exact hAbsoluteRaw

end

end Euclidean
end Bridge
end PrimeTensor
