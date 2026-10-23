import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopLocalTemporalDomination244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Local.Domination
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation
import Mathlib.Tactic

/-!
# Compact momentum-term bounds imply physical eighth moments

The old compact-test temporal-domination frontier may be checked on the
three genuine terms of the preterminal momentum equation:

  ∂ₜ u_j = Δu_j - (u · ∇)u_j - ∂_j p.

Uniform bounds on each term over a small elapsed-time neighborhood and the
compact spatial support of a test yield the integrable majorant

  3 C ‖φ_j(x)‖.

This proves the local temporal domination theorem already used by the
selected/old Grönwall uniqueness and raw eighth Fourier-moment arguments.

The compact momentum-term bounds are an explicit analytic hypothesis. They
are not derived here from separate continuity or the H³ energy ceiling:
separate continuity need not give a uniform bound on a product compactum.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3CompactMomentumTerms244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3CompactMomentumTerms244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A compactly supported test probes only bounded physical momentum terms.
The constant and elapsed-time neighborhood may depend on the test, component,
and observation time, but are uniform on the entire spatial test support. -/
def h3PreterminalMomentumTermsCompactBoundOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ tau : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) tau →
    ∀ i : Fin 3,
      ∃ S : Set ℝ,
        S ∈ 𝓝 s ∧
        (∀ r : ℝ, r ∈ S → t₀ + r ∈ Set.Ioo (0 : ℝ) T) ∧
        ∃ C : ℝ,
          0 ≤ C ∧
          ∀ r : ℝ, r ∈ S →
          ∀ x : Point3, x ∈ tsupport (φ i : Point3 → ℝ) →
            ‖PrimeTensor.Bridge.RealFluid.laplacian
                spatial3
                (fun y : Point3 =>
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u (t₀ + r) y).component
                    (h3AxisOfFin3 i)) x‖ ≤ C ∧
            ‖realAdvectionComponent
                (PrimeTensor.Bridge.logSpaceTimeVectorField u) (t₀ + r) x
                  (h3AxisOfFin3 i)‖ ≤ C ∧
            ‖spatial3.d (h3AxisOfFin3 i)
                ((Classical.choose hNS :
                  SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t₀ + r)) x‖ ≤ C

/-- The physical PDE converts compact bounds on diffusion, advection, and
pressure into the locally integrable majorants needed for compact-test weak
momentum differentiation. -/
theorem h3Preterminal_compactTemporalDomination_of_momentumTermsBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ tau : ℝ)
    (hBound : h3PreterminalMomentumTermsCompactBoundOnElapsed244
      hNS t₀ tau) :
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
        hNS t₀ tau φ := by
  intro φ hφ s hs i
  obtain ⟨S, hS, hSAbs, C, _hC0, hTerms⟩ :=
    hBound φ hφ s hs i

  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  have hPDE :
      PreterminalNavierStokes3
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T :=
    Classical.choose_spec hNS

  let bound : Point3 → ℝ := fun x => (3 * C) * ‖φ i x‖
  have hNormInt : Integrable
      (fun x : Point3 => ‖φ i x‖)
      (volume : Measure Point3) :=
    (φ i).continuous.norm.integrable_of_hasCompactSupport
      (φ i).hasCompactSupport.norm
  have hBoundInt : Integrable bound
      (volume : Measure Point3) := by
    dsimp only [bound]
    exact Integrable.const_mul hNormInt (3 * C)

  refine ⟨S, hS, hSAbs, bound, hBoundInt, ?_⟩
  filter_upwards with x
  intro r hr
  by_cases hx : φ i x = 0
  · change
      ‖(φ i x) *
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent u a (h3AxisOfFin3 i) x)
          (t₀ + r)‖ ≤ bound x
    simp [bound, hx]
  · have hxSupport :
        x ∈ tsupport (φ i : Point3 → ℝ) :=
      subset_tsupport _ hx
    obtain ⟨hLap, hAdv, hPressure⟩ :=
      hTerms r hr x hxSupport

    let A : ℝ :=
      PrimeTensor.Bridge.RealFluid.laplacian spatial3
        (fun y : Point3 =>
          (PrimeTensor.Bridge.logSpaceTimeVectorField u (t₀ + r) y).component
            (h3AxisOfFin3 i)) x
    let B : ℝ :=
      realAdvectionComponent (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        (t₀ + r) x (h3AxisOfFin3 i)
    let P : ℝ :=
      spatial3.d (h3AxisOfFin3 i) (p (t₀ + r)) x

    have hEq :
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent u a (h3AxisOfFin3 i) x)
          (t₀ + r) = A - B - P := by
      dsimp only [A, B, P, p]
      exact
        hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
          (hSAbs r hr) x (h3AxisOfFin3 i)

    have hA : ‖A‖ ≤ C := hLap
    have hB : ‖B‖ ≤ C := hAdv
    have hP : ‖P‖ ≤ C := hPressure

    have hDerivative :
        ‖temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent u a (h3AxisOfFin3 i) x)
          (t₀ + r)‖ ≤ 3 * C := by
      rw [hEq]
      calc
        ‖A - B - P‖ ≤ ‖A - B‖ + ‖P‖ := norm_sub_le _ _
        _ ≤ (‖A‖ + ‖B‖) + ‖P‖ := by
          exact add_le_add_left (norm_sub_le A B) _
        _ ≤ (C + C) + C :=
          add_le_add (add_le_add hA hB) hP
        _ = 3 * C := by ring

    change
      ‖(φ i x) *
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent u a (h3AxisOfFin3 i) x)
          (t₀ + r)‖ ≤ bound x
    dsimp only [bound]
    calc
      ‖(φ i x) *
          temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent u a (h3AxisOfFin3 i) x)
            (t₀ + r)‖ =
        ‖φ i x‖ *
          ‖temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent u a (h3AxisOfFin3 i) x)
            (t₀ + r)‖ := norm_mul _ _
      _ ≤ ‖φ i x‖ * (3 * C) :=
        mul_le_mul_of_nonneg_left hDerivative (norm_nonneg _)
      _ = (3 * C) * ‖φ i x‖ := by ring

/-- A shortened physical restart with compact bounds on the genuine
momentum terms, rather than on the temporal derivative itself. -/
def h3PathVelocityShortWindowMomentumTermsBoundAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : Prop :=
  ∃ (t₀ S E : ℝ)
    (_ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (_hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hq : 0 < t - t₀)
    (_hqR : t - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (_hEnd : t₀ + (t - t₀) < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
    h3PreterminalMomentumTermsCompactBoundOnElapsed244
      hNSShort t₀ (t - t₀)

/-- The compact momentum-term estimate constructs the *actual* local
compact-test temporal domination predicate; no weak-FTC or mild agreement is
assumed. -/
theorem h3Path_shortWindowTemporalDomination_of_momentumTermsBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hMomentum : h3PathVelocityShortWindowMomentumTermsBoundAt244
      hH3 t) :
    h3PathVelocityShortWindowTemporalDominationAt244 hH3 t := by
  rcases hMomentum with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, hEnd,
      hNSShort, hBounds⟩
  refine ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR,
    hEnd, hNSShort, ?_⟩
  exact
    h3Preterminal_compactTemporalDomination_of_momentumTermsBound244
      hNSShort t₀ (t - t₀) hBounds

/-- Compact bounds on the old physical momentum terms suffice for raw
velocity eighth-order moments at the actual strict time. -/
theorem h3Path_physicalEighthMoments_of_momentumTermsBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMomentum : h3PathVelocityShortWindowMomentumTermsBoundAt244
      hH3 t) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  exact h3Path_physicalEighthMoments_of_localTemporalDomination244
    hH3 hClass ht
    (h3Path_shortWindowTemporalDomination_of_momentumTermsBound244
      hH3 hMomentum)

/-- The top physical dissipation alternative can be supplied entirely from
compact local bounds on the *spatial* Navier--Stokes momentum terms. -/
theorem h3Path_unboundedPhysicalTop_forces_lower_or_eight_of_momentumTermsBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMomentum : ∀ t (_ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowMomentumTermsBoundAt244 hH3 t) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply
    h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localTemporalDomination244
      hH3 hClass hs hEscape
  intro t ht
  exact h3Path_shortWindowTemporalDomination_of_momentumTermsBound244
    hH3 (hMomentum t ht)

/-- An unconditional necessary trichotomy: either one physical escape
channel is present, or the time-uniform compact momentum estimate fails at
an interior time. This does not exclude the third branch. -/
theorem h3Path_unboundedPhysicalTop_forces_lower_or_eight_or_momentumCompactFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) ∨
    (∃ t, t ∈ Set.Ioo a T ∧
      ¬ h3PathVelocityShortWindowMomentumTermsBoundAt244 hH3 t) := by
  classical
  by_cases hAll : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowMomentumTermsBoundAt244 hH3 t
  · rcases
      h3Path_unboundedPhysicalTop_forces_lower_or_eight_of_momentumTermsBound244
        hH3 hClass hs hEscape hAll with hLow | hEight
    · exact Or.inl hLow
    · exact Or.inr (Or.inl hEight)
  · right
    right
    by_contra hNo
    apply hAll
    intro t ht
    by_contra hNot
    exact hNo ⟨t, ht, hNot⟩

end
end PrimeTensor.FirstMonomialTriad
