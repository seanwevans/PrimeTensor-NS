import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldVelocityCompactTest
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Zeroth endpoint continuity: pressure-free old velocity weak pairings

`OldVelocityCompactTest` supplied the two inputs needed for dominated
convergence on every retained closed elapsed interval:

* for each fixed spatial point, the old logged velocity is continuous in
  elapsed time;
* uniformly over elapsed time and space, each velocity component is bounded by
  the retained H³ spectral envelope.

For a fixed compact smooth scalar test `ψ`, define

    q ↦ ∫ ψ(x) u_i(t+q,x) dx.

The test is integrable, the old velocity is spatially continuous at each
snapshot, and the product is dominated uniformly by

    C(E) ‖ψ(x)‖.

Dominated convergence therefore proves continuity of this scalar pairing in
`q`.  Summing over the three coordinates gives continuity of the complete weak
velocity pairing against any `H3WeakTestVector`.

No pressure, temporal derivative, endpoint continuity, mild equation, or
selected restart is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldVelocityWeakPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldVelocityWeakPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One old preterminal velocity component paired with one compact smooth
scalar test at elapsed time `q`. -/
noncomputable def h3PreterminalOldVelocityWeakScalarPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i)
        x)
    ∂volume

/-- The scalar weak velocity integrand is integrable at every retained elapsed
time. -/
theorem h3PreterminalOldVelocityWeakScalarPairing_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 i)
            x))
      (volume : Measure Point3) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hSpatial :
      Continuous
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hAbs
        (h3AxisOfFin3 i)).continuous

  exact
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hSpatial.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- The retained H³ ceiling gives an integrable dominating function for the
scalar weak pairing, uniformly over the closed elapsed interval. -/
theorem h3PreterminalOldVelocityWeakScalarPairing_bound_integrable
    {E : ℝ}
    (hE : 1 ≤ E)
    (ψ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (h3RawFourierL1DeweightingCoefficient * (2 * E))
          * ‖ψ x‖)
      (volume : Measure Point3) := by
  exact
    (h3WeakTestFunction_integrable ψ).norm.const_mul
      (h3RawFourierL1DeweightingCoefficient * (2 * E))

/-- Pointwise domination of the old velocity weak integrand by a fixed
integrable compact-test envelope. -/
theorem norm_h3PreterminalOldVelocityWeakScalarPairing_integrand_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3) :
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x)‖
      ≤
    (h3RawFourierL1DeweightingCoefficient * (2 * E))
      * ‖ψ x‖ := by
  have hVelocity :=
    norm_loggedVelocityComponent_le_oldCanonicalSnapshotEnvelope
      hNS ht hEnd hE hTail q i x

  change
    ‖(ψ x) *
        loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x‖
      ≤
    (h3RawFourierL1DeweightingCoefficient * (2 * E))
      * ‖ψ x‖

  rw [norm_mul]

  calc
    ‖ψ x‖ *
        ‖loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 i)
            x‖
        ≤
      ‖ψ x‖ *
        (h3RawFourierL1DeweightingCoefficient * (2 * E)) :=
      mul_le_mul_of_nonneg_left
        hVelocity
        (norm_nonneg _)
    _ =
      (h3RawFourierL1DeweightingCoefficient * (2 * E))
        * ‖ψ x‖ := by
      ring

/-- For each fixed physical point, the scalar weak integrand is continuous in
elapsed time. -/
theorem continuous_h3PreterminalOldVelocityWeakScalarPairing_integrand_at_point
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3)
    (x : Point3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 i)
            x)) := by
  change
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        (ψ x) *
          loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 i)
            x)

  exact
    continuous_const.mul
      (continuous_loggedVelocityComponent_onElapsed_at_point
        hNS ht hEnd hTail i x)

/-- Pressure-free continuity of one old velocity component paired against one
compact smooth scalar test. -/
theorem continuous_h3PreterminalOldVelocityWeakScalarPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3) :
    Continuous
      (h3PreterminalOldVelocityWeakScalarPairingOnElapsed
        hNS ht hEnd hTail ψ i) := by
  rw [continuous_iff_continuousAt]
  intro q₀

  let F :
      Set.Icc (0 : ℝ) tau → Point3 → ℝ :=
    fun q x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x)

  let bound : Point3 → ℝ :=
    fun x =>
      (h3RawFourierL1DeweightingCoefficient * (2 * E))
        * ‖ψ x‖

  have hMeas :
      ∀ᶠ q in 𝓝 q₀,
        AEStronglyMeasurable
          (F q)
          (volume : Measure Point3) := by
    exact
      Filter.Eventually.of_forall
        (fun q =>
          (h3PreterminalOldVelocityWeakScalarPairing_integrable
            hNS ht hEnd hTail ψ i q).aestronglyMeasurable)

  have hDom :
      ∀ᶠ q in 𝓝 q₀,
        ∀ᵐ x : Point3 ∂volume,
          ‖F q x‖ ≤ bound x := by
    exact
      Filter.Eventually.of_forall
        (fun q =>
          Filter.Eventually.of_forall
            (fun x =>
              norm_h3PreterminalOldVelocityWeakScalarPairing_integrand_le
                hNS ht hEnd hE hTail ψ i q x))

  have hBoundInt :
      Integrable bound
        (volume : Measure Point3) := by
    dsimp only [bound]
    exact
      h3PreterminalOldVelocityWeakScalarPairing_bound_integrable
        hE ψ

  have hPoint :
      ∀ᵐ x : Point3 ∂volume,
        Tendsto
          (fun q : Set.Icc (0 : ℝ) tau =>
            F q x)
          (𝓝 q₀)
          (𝓝 (F q₀ x)) := by
    exact
      Filter.Eventually.of_forall
        (fun x =>
          (continuous_h3PreterminalOldVelocityWeakScalarPairing_integrand_at_point
            hNS ht hEnd hTail ψ i x).continuousAt)

  have hDCT :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          ∫ x : Point3, F q x ∂volume)
        (𝓝 q₀)
        (𝓝 (∫ x : Point3, F q₀ x ∂volume)) := by
    exact
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 q₀)
        (F := F)
        (f := F q₀)
        (bound := bound)
        hMeas
        hDom
        hBoundInt
        hPoint

  change
    Tendsto
      (fun q : Set.Icc (0 : ℝ) tau =>
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 i)
              x)
          ∂volume)
      (𝓝 q₀)
      (𝓝
        (∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (loggedVelocityComponent
              u
              (t + (q₀ : ℝ))
              (h3AxisOfFin3 i)
              x)
          ∂volume))

  simpa only [F] using hDCT

/-- Complete three-coordinate old velocity weak pairing against a compact
smooth test vector. -/
noncomputable def h3PreterminalOldVelocityWeakPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  ∑ i : Fin 3,
    h3PreterminalOldVelocityWeakScalarPairingOnElapsed
      hNS ht hEnd hTail (φ i) i q

/-- The complete old velocity weak pairing is continuous in elapsed time,
without any pressure or endpoint-continuity hypothesis. -/
theorem continuous_h3PreterminalOldVelocityWeakPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) :
    Continuous
      (h3PreterminalOldVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ) := by
  unfold h3PreterminalOldVelocityWeakPairingOnElapsed

  exact
    continuous_finset_sum
      Finset.univ
      (fun i _ =>
        continuous_h3PreterminalOldVelocityWeakScalarPairingOnElapsed
          hNS ht hEnd hE hTail (φ i) i)

end

end Euclidean
end Bridge
end PrimeTensor
