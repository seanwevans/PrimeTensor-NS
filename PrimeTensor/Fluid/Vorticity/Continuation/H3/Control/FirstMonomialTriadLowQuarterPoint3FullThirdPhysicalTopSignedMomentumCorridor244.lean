import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCompactMomentumTerms244
import PrimeTensor.Fluid.Vorticity.Preterminal.Temporal.Separate
import Mathlib.Tactic

/-!
# Signed physical momentum corridor and its compact-test domination

The previous interface separately bounds diffusion, advection, and the pressure
force on a compact spatial support and a temporal neighborhood. That is stronger
than what is required for compact-test differentiation: the actual temporal
velocity derivative equals their **signed sum**.

This module retains the Navier--Stokes cancellation before taking absolute
values. A local bound on the signed momentum residual suffices for the physical
weak FTC, selected/old uniqueness, and raw eighth moments. It also proves that
the signed residual is bounded on each fixed compact spatial snapshot from the
already-known separate *spatial* continuity of the temporal derivative.

The latter fixed-time bound is not asserted uniform on a time neighborhood:
separate continuity does not justify that step. No unconditional terminal
regularity or H3-to-Linfty second-derivative bound is assumed or derived.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SignedMomentum244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SignedMomentum244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On a fixed strict physical time slice, the genuine temporal derivative
is bounded on any compact weak-test support. Unlike the interval predicate
below, this follows from the already-proved spatial continuity. -/
theorem h3Preterminal_temporalDerivative_bounded_on_compactTestAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : H3WeakTestVector) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Point3, x ∈ tsupport (φ i : Point3 → ℝ) →
        ‖temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q (h3AxisOfFin3 i) x)
          t‖ ≤ C := by
  have hCont : Continuous
      (fun x : Point3 =>
        temporal.d
          (fun q : ℝ => loggedVelocityComponent u q (h3AxisOfFin3 i) x)
          t) :=
    loggedPreterminalTemporalDerivative_continuous_space
      hNS ht (h3AxisOfFin3 i)
  have hCompact : IsCompact (tsupport (φ i : Point3 → ℝ)) :=
    (φ i).hasCompactSupport
  obtain ⟨C, hC⟩ :=
    hCompact.exists_bound_of_continuousOn hCont.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left C 0)

/-- The cancellation-sensitive compact momentum condition: on a small time
neighborhood, the **signed complete** physical momentum right-hand side is
bounded over a compact weak-test support. The bound is not required termwise. -/
def h3PreterminalSignedMomentumCompactBoundOnElapsed244
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
                  (PrimeTensor.Bridge.logSpaceTimeVectorField
                    u (t₀ + r) y).component (h3AxisOfFin3 i)) x
              - realAdvectionComponent
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (t₀ + r) x (h3AxisOfFin3 i)
              - spatial3.d (h3AxisOfFin3 i)
                  ((Classical.choose hNS :
                    SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t₀ + r)) x‖ ≤ C

/-- Signed physical momentum control gives the compact-test majorant
`C * ‖φ_i(x)‖`, retaining diffusion/advection/pressure cancellation. -/
theorem h3Preterminal_compactTemporalDomination_of_signedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ tau : ℝ)
    (hSigned : h3PreterminalSignedMomentumCompactBoundOnElapsed244
      hNS t₀ tau) :
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
        hNS t₀ tau φ := by
  intro φ hφ s hs i
  obtain ⟨S, hS, hSAbs, C, _hC0, hSignedBound⟩ :=
    hSigned φ hφ s hs i
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  have hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T :=
    Classical.choose_spec hNS
  let bound : Point3 → ℝ := fun x => C * ‖φ i x‖
  have hNormInt : Integrable
      (fun x : Point3 => ‖φ i x‖)
      (volume : Measure Point3) :=
    (φ i).continuous.norm.integrable_of_hasCompactSupport
      (φ i).hasCompactSupport.norm
  have hBoundInt : Integrable bound
      (volume : Measure Point3) := by
    dsimp only [bound]
    exact Integrable.const_mul hNormInt C
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
    have hRHS := hSignedBound r hr x hxSupport
    have hEq :
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent u a (h3AxisOfFin3 i) x)
          (t₀ + r) =
        PrimeTensor.Bridge.RealFluid.laplacian spatial3
          (fun y : Point3 =>
            (PrimeTensor.Bridge.logSpaceTimeVectorField
              u (t₀ + r) y).component (h3AxisOfFin3 i)) x
          - realAdvectionComponent
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (t₀ + r) x (h3AxisOfFin3 i)
          - spatial3.d (h3AxisOfFin3 i) (p (t₀ + r)) x := by
      dsimp only [p]
      exact hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
        (hSAbs r hr) x (h3AxisOfFin3 i)
    change
      ‖(φ i x) *
        temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent u a (h3AxisOfFin3 i) x)
          (t₀ + r)‖ ≤ bound x
    rw [hEq, norm_mul]
    dsimp only [bound]
    calc
      ‖φ i x‖ *
          ‖PrimeTensor.Bridge.RealFluid.laplacian spatial3
              (fun y : Point3 =>
                (PrimeTensor.Bridge.logSpaceTimeVectorField
                  u (t₀ + r) y).component (h3AxisOfFin3 i)) x
            - realAdvectionComponent
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (t₀ + r) x (h3AxisOfFin3 i)
            - spatial3.d (h3AxisOfFin3 i) (p (t₀ + r)) x‖
          ≤ ‖φ i x‖ * C :=
        mul_le_mul_of_nonneg_left hRHS (norm_nonneg _)
      _ = C * ‖φ i x‖ := by ring

/-- The previous term-by-term condition implies the weaker signed condition;
this loses a factor of three because it discards PDE cancellations. -/
theorem h3Preterminal_signedMomentumBound_of_termwiseBounds244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ tau : ℝ)
    (hTerms : h3PreterminalMomentumTermsCompactBoundOnElapsed244
      hNS t₀ tau) :
    h3PreterminalSignedMomentumCompactBoundOnElapsed244 hNS t₀ tau := by
  intro φ hφ s hs i
  obtain ⟨S, hS, hSAbs, C, hC, hTermBounds⟩ :=
    hTerms φ hφ s hs i
  refine ⟨S, hS, hSAbs, 3 * C, by positivity, ?_⟩
  intro r hr x hx
  obtain ⟨hLap, hAdv, hPressure⟩ := hTermBounds r hr x hx
  let A : ℝ := PrimeTensor.Bridge.RealFluid.laplacian spatial3
    (fun y : Point3 =>
      (PrimeTensor.Bridge.logSpaceTimeVectorField
        u (t₀ + r) y).component (h3AxisOfFin3 i)) x
  let B : ℝ := realAdvectionComponent
    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
    (t₀ + r) x (h3AxisOfFin3 i)
  let P : ℝ := spatial3.d (h3AxisOfFin3 i)
    ((Classical.choose hNS : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
      (t₀ + r)) x
  have hA : ‖A‖ ≤ C := hLap
  have hB : ‖B‖ ≤ C := hAdv
  have hP : ‖P‖ ≤ C := hPressure
  change ‖A - B - P‖ ≤ 3 * C
  calc
    ‖A - B - P‖ ≤ ‖A - B‖ + ‖P‖ := norm_sub_le _ _
    _ ≤ (‖A‖ + ‖B‖) + ‖P‖ :=
      add_le_add_left (norm_sub_le A B) _
    _ ≤ (C + C) + C := add_le_add (add_le_add hA hB) hP
    _ = 3 * C := by ring

/-- The signed physical momentum right-hand side is bounded on each
*fixed* compact spatial support, without any spacetime joint-continuity
hypothesis. This uses the spatially continuous temporal derivative and the
pointwise physical momentum equation. -/
theorem h3Preterminal_signedMomentum_bounded_on_compactTestAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : H3WeakTestVector) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Point3, x ∈ tsupport (φ i : Point3 → ℝ) →
        ‖PrimeTensor.Bridge.RealFluid.laplacian spatial3
            (fun y : Point3 =>
              (PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y).component (h3AxisOfFin3 i)) x
          - realAdvectionComponent
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x (h3AxisOfFin3 i)
          - spatial3.d (h3AxisOfFin3 i)
              ((Classical.choose hNS :
                SpaceTimeScalarField ℝ ℝ ℝ Depth.three) t) x‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ :=
    h3Preterminal_temporalDerivative_bounded_on_compactTestAt244
      hNS ht φ i
  refine ⟨C, hC, ?_⟩
  intro x hx
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  have hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T :=
    Classical.choose_spec hNS
  have hEq :=
    hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
      ht x (h3AxisOfFin3 i)
  change
    ‖PrimeTensor.Bridge.RealFluid.laplacian spatial3
        (fun y : Point3 =>
          (PrimeTensor.Bridge.logSpaceTimeVectorField
            u t y).component (h3AxisOfFin3 i)) x
      - realAdvectionComponent
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x (h3AxisOfFin3 i)
      - spatial3.d (h3AxisOfFin3 i) (p t) x‖ ≤ C
  rw [← hEq]
  exact hBound x hx

/-- A shortened physical restart on which the signed actual physical
momentum right-hand side is locally bounded on compact test supports. -/
def h3PathVelocityShortWindowSignedMomentumBoundAt244
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
    h3PreterminalSignedMomentumCompactBoundOnElapsed244
      hNSShort t₀ (t - t₀)

/-- Signed compact momentum control suffices for local temporal domination. -/
theorem h3Path_shortWindowTemporalDomination_of_signedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hSigned : h3PathVelocityShortWindowSignedMomentumBoundAt244 hH3 t) :
    h3PathVelocityShortWindowTemporalDominationAt244 hH3 t := by
  rcases hSigned with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, hEnd,
      hNSShort, hBounds⟩
  refine ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR,
    hEnd, hNSShort, ?_⟩
  exact h3Preterminal_compactTemporalDomination_of_signedMomentumBound244
    hNSShort t₀ (t - t₀) hBounds

/-- Pointwise raw eighth Fourier moments follow from bounded *signed*
physical momentum, without separately bounding its PDE contributions. -/
theorem h3Path_physicalEighthMoments_of_signedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSigned : h3PathVelocityShortWindowSignedMomentumBoundAt244 hH3 t) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  exact h3Path_physicalEighthMoments_of_localTemporalDomination244
    hH3 hClass ht
    (h3Path_shortWindowTemporalDomination_of_signedMomentumBound244
      hH3 hSigned)

/-- The physical top escape alternative uses only the cancellation-preserving
signed momentum bound on compact supports on each positive short window. -/
theorem h3Path_unboundedPhysicalTop_forces_lower_or_eight_of_signedMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hSigned : ∀ t (_ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowSignedMomentumBoundAt244 hH3 t) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply
    h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localTemporalDomination244
      hH3 hClass hs hEscape
  intro t ht
  exact h3Path_shortWindowTemporalDomination_of_signedMomentumBound244
    hH3 (hSigned t ht)

/-- Necessary three-way corridor if compact signed-momentum control is not
known everywhere: lower dissipation, eighth-moment escape, or failure of the
signed momentum bound at some strict time. -/
theorem h3Path_unboundedPhysicalTop_forces_lower_or_eight_or_signedMomentumFailure244
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
      ¬ h3PathVelocityShortWindowSignedMomentumBoundAt244 hH3 t) := by
  classical
  by_cases hAll : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowSignedMomentumBoundAt244 hH3 t
  · rcases
      h3Path_unboundedPhysicalTop_forces_lower_or_eight_of_signedMomentum244
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
