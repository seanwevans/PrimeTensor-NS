import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Separate.Derivatives
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall

/-!
# Selected/old physical L² energy Grönwall closure

The previously packaged Hilbert-valued bound

    ‖D'(s)‖ ≤ K ‖D(s)‖

is stronger than the standard Navier--Stokes uniqueness estimate: the
diffusion term naturally contributes a favorable gradient-energy term rather
than an `L² → L²` Lipschitz bound for the vector field itself.

The correct quantity is the scalar difference energy

    E(s) = ‖D(s)‖².

For a differentiable Hilbert-valued path Mathlib gives

    E'(s) = 2 ⟪D(s), D'(s)⟫_ℝ.

Hence the standard one-sided estimate

    2 ⟪D(s), D'(s)⟫_ℝ ≤ K ‖D(s)‖²

is exactly enough.  `le_gronwallBound_of_liminf_deriv_right_le` then forces
`E = 0` from the already-closed zero initial value.

This is the natural uniqueness frontier for the Navier--Stokes energy
calculation: diffusion may be discarded with its favorable sign, pressure is
removed by solenoidality, and only the transport pairing must be estimated.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2EnergyGronwall
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar-energy Grönwall closure for a real Hilbert-valued difference path.

Unlike `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`, this requires
only the one-sided energy inequality and therefore matches the standard
Navier--Stokes uniqueness calculation. -/
theorem h3PhysicalRealFinVectorL2Difference_eq_zero_of_energy_gronwall
    {D D' : ℝ → H3PhysicalRealFinVectorL2Hilbert}
    {K a b : ℝ}
    (hD : ContinuousOn D (Set.Icc a b))
    (hD' :
      ∀ s ∈ Set.Ico a b,
        HasDerivWithinAt
          D (D' s) (Set.Ici s) s)
    (hZero : D a = 0)
    (hEnergy :
      ∀ s ∈ Set.Ico a b,
        2 * inner ℝ (D s) (D' s)
          ≤
        K * ‖D s‖ ^ 2)
    (s : ℝ)
    (hs : s ∈ Set.Icc a b) :
    D s = 0 := by
  let e : ℝ → ℝ :=
    fun r => ‖D r‖ ^ 2

  let e' : ℝ → ℝ :=
    fun r => 2 * inner ℝ (D r) (D' r)

  have heContinuous :
      ContinuousOn e (Set.Icc a b) := by
    dsimp only [e]
    exact
      (continuous_norm.comp_continuousOn hD).pow 2

  have heDeriv :
      ∀ r ∈ Set.Ico a b,
        HasDerivWithinAt
          e (e' r) (Set.Ici r) r := by
    intro r hr
    dsimp only [e, e']
    exact
      (hD' r hr).norm_sq

  have heInitial :
      e a ≤ 0 := by
    simp only [e, hZero, norm_zero, zero_pow]
    norm_num

  have heBound :
      ∀ r ∈ Set.Ico a b,
        e' r ≤ K * e r + 0 := by
    intro r hr
    dsimp only [e, e']
    simpa only [add_zero] using hEnergy r hr

  have heUpper :
      e s
        ≤
      gronwallBound 0 K 0 (s - a) := by
    exact
      le_gronwallBound_of_liminf_deriv_right_le
        heContinuous
        (fun r hr z hz =>
          (heDeriv r hr).liminf_right_slope_le hz)
        heInitial
        heBound
        s
        hs

  have heNonpos :
      e s ≤ 0 := by
    simpa only [gronwallBound_ε0_δ0] using heUpper

  have hNormSq :
      ‖D s‖ ^ 2 ≤ 0 := by
    simpa only [e] using heNonpos

  have hNorm :
      ‖D s‖ = 0 := by
    nlinarith [sq_nonneg ‖D s‖]

  exact norm_eq_zero.mp hNorm

/-- The branch-local uniqueness data with the mathematically natural
Navier--Stokes energy estimate.

`S` and `O` are ordinary real-time liftings of the selected and old physical
`L²` velocity paths.  Their strong derivatives remain branch-local inputs; the
cross-branch estimate is only the scalar energy pairing inequality. -/
def H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∃
    (S O S' O' : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ),
      (∀ q : Set.Icc (0 : ℝ) tau,
        S (q : ℝ)
          =
        h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          hν hNS ht hE hTail (q : ℝ))
      ∧
      (∀ q : Set.Icc (0 : ℝ) tau,
        O (q : ℝ)
          =
        h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      ∧
      ContinuousOn S (Set.Icc (0 : ℝ) tau)
      ∧
      ContinuousOn O (Set.Icc (0 : ℝ) tau)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          S (S' s) (Set.Ici s) s)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          O (O' s) (Set.Ici s) s)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        2 * inner ℝ
              (S s - O s)
              (S' s - O' s)
          ≤
        K * ‖S s - O s‖ ^ 2)

/-- The scalar energy data forces the concrete selected-minus-old physical
`L²` difference to vanish at every point of the closed elapsed interval. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_energyData
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData :
      H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q
      =
    0 := by
  rcases hData with
    ⟨S, O, S', O', K,
      hSConcrete, hOConcrete,
      hSCont, hOCont,
      hSDeriv, hODeriv,
      hEnergy⟩

  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun s => S s - O s

  let D' : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun s => S' s - O' s

  have hDCont :
      ContinuousOn D (Set.Icc (0 : ℝ) tau) := by
    dsimp only [D]
    exact hSCont.sub hOCont

  have hDDeriv :
      ∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          D (D' s) (Set.Ici s) s := by
    intro s hs
    dsimp only [D, D']
    exact
      (hSDeriv s hs).sub
        (hODeriv s hs)

  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, le_rfl, htau.le⟩

  have hDZero :
      D 0 = 0 := by
    calc
      D 0
          =
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail q0 := by
            dsimp only [
              D,
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            ]
            rw [hSConcrete q0, hOConcrete q0]
      _ = 0 :=
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_zero
          hν hNS ht htau hEnd hE hTail

  have hDEnergy :
      ∀ s ∈ Set.Ico (0 : ℝ) tau,
        2 * inner ℝ (D s) (D' s)
          ≤
        K * ‖D s‖ ^ 2 := by
    intro s hs
    dsimp only [D, D']
    exact hEnergy s hs

  have hDq :
      D (q : ℝ) = 0 :=
    h3PhysicalRealFinVectorL2Difference_eq_zero_of_energy_gronwall
      hDCont
      hDDeriv
      hDZero
      hDEnergy
      (q : ℝ)
      q.property

  calc
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q
        =
      D (q : ℝ) := by
        dsimp only [
          D,
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        ]
        rw [hSConcrete q, hOConcrete q]
    _ = 0 := hDq

/-- The natural scalar-energy uniqueness data closes pointwise selected/old
physical agreement at every strict positive elapsed time. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2EnergyDerivatives
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hData :
      H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  let qClosed : Set.Icc (0 : ℝ) tau :=
    ⟨(q : ℝ), q.property.1.le, q.property.2⟩

  have hZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail qClosed
        =
      0 :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_energyData
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      hData
      qClosed

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero
      hν
      hNS
      ht
      hEnd
      hE
      hTail
      qClosed
      q.property.1
      (le_trans q.property.2 htauR)
      hZero

end

end Euclidean
end Bridge
end PrimeTensor
