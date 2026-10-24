import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionSpatialEquicontinuityCriterion244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionInteriorSignedPDE244
import Mathlib.Tactic

/-!
# Physical momentum distributions from a local spatial L² envelope

The compact-test differentiation argument does not require signed PDE
momentum to be bounded uniformly over a compact spatial test support.
It is sufficient to have a *single spatial L² envelope* on a neighborhood
of each elapsed time. A compact smooth test coordinate is in spatial L²;
Hölder 2-2-1 makes their product an integrable spatial majorant.

The signed expression is kept whole, preserving the cancellation of
Laplacian, advection and pressure. The envelope is allowed to depend on
the compact test, elapsed time and coordinate. It is uniform in the
nearby times and only required at spatial points where the test is nonzero.

A family of merely uniformly bounded L² norms is NOT asserted to supply
a pointwise L² envelope. Nor is this additional condition inferred from
bare H³ admissibility; those are separate outstanding analytic questions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3PhysicalLocalL2Envelope244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalLocalL2Envelope244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The integrability calculation needed to use a physical spatial L²
majorant for a compact Schwartz test. This uses Hölder, not a pointwise
spatial bound or any assertion of a uniform time modulus. -/
theorem h3Path_compactTestL2Envelope_productIntegrable244
    (φ : H3WeakTestVector) (i : Fin 3)
    (g : Point3 → ℝ)
    (hg : MemLp g 2 (volume : Measure Point3)) :
    Integrable (fun x : Point3 => ‖φ i x‖ * ‖g x‖)
      (volume : Measure Point3) := by
  have hφ : MemLp (fun x : Point3 => φ i x) 2
      (volume : Measure Point3) :=
    (φ i).continuous.memLp_of_hasCompactSupport (φ i).hasCompactSupport
  exact hφ.norm.integrable_mul hg.norm

/-- The signed physical Navier--Stokes momentum has a locally uniform
*spatial L² envelope*, after restriction to each tested coordinate.
The exceptional spatial set is independent of nearby elapsed times.
No pointwise supremum over the compact support is required. -/
def h3PreterminalSignedMomentumLocalL2EnvelopeOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ τ : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) τ →
    ∀ i : Fin 3,
      ∃ S : Set ℝ, S ∈ 𝓝 s ∧
        (∀ r : ℝ, r ∈ S → t₀ + r ∈ Set.Ioo (0 : ℝ) T) ∧
        ∃ g : Point3 → ℝ,
          MemLp g 2 (volume : Measure Point3) ∧
          ∀ᵐ x : Point3 ∂volume,
            ∀ r : ℝ, r ∈ S →
              φ i x = 0 ∨
                ‖h3PreterminalSignedPhysicalMomentumAt244
                    hNS (t₀ + r) x i‖ ≤ ‖g x‖

/-- A local L² spatial envelope dominates the actual tested temporal
derivative by an integrable function, using the classical signed PDE
identity and Hölder's inequality. -/
theorem h3Preterminal_compactTemporalDomination_of_signedL2Envelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ τ : ℝ)
    (hEnvelope : h3PreterminalSignedMomentumLocalL2EnvelopeOnElapsed244
      hNS t₀ τ) :
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
        hNS t₀ τ φ := by
  intro φ hφ s hs i
  obtain ⟨S, hS, hSAbs, g, hg, hBound⟩ :=
    hEnvelope φ hφ s hs i
  let bound : Point3 → ℝ := fun x => ‖φ i x‖ * ‖g x‖
  have hBoundInt : Integrable bound (volume : Measure Point3) :=
    h3Path_compactTestL2Envelope_productIntegrable244 φ i g hg
  refine ⟨S, hS, hSAbs, bound, hBoundInt, ?_⟩
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three := Classical.choose hNS
  have hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T :=
    Classical.choose_spec hNS
  filter_upwards [hBound] with x hx
  intro r hr
  change ‖(φ i x) *
      temporal.d
        (fun q : ℝ => loggedVelocityComponent u q (h3AxisOfFin3 i) x)
        (t₀ + r)‖ ≤ bound x
  rcases hx r hr with hZero | hSigned
  · simp [bound, hZero]
  · have hPDEat :
        temporal.d
          (fun q : ℝ => loggedVelocityComponent u q (h3AxisOfFin3 i) x)
          (t₀ + r) =
        h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i := by
      unfold h3PreterminalSignedPhysicalMomentumAt244
      exact hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
        (hSAbs r hr) x (h3AxisOfFin3 i)
    rw [hPDEat, norm_mul]
    change ‖φ i x‖ *
      ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i‖ ≤
      ‖φ i x‖ * ‖g x‖
    exact mul_le_mul_of_nonneg_left hSigned (norm_nonneg _)

/-- A canonical restart *straddling* one physical time on which the signed
old momentum possesses a spatial L² envelope on each compact test.
This is weaker in spatial regularity than a uniform pointwise Lipschitz
condition but is not deduced from a mere uniform-in-time L² norm bound. -/
def h3PathInteriorTimeSignedL2EnvelopeAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) : Prop :=
  ∃ (t₀ S E τ : ℝ)
    (_ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (_hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hτ : 0 < τ)
    (_hEnd : t₀ + τ < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
      s ∈ Set.Ioo t₀ (t₀ + τ) ∧
      h3PreterminalSignedMomentumLocalL2EnvelopeOnElapsed244 hNSShort t₀ τ

/-- The L² envelope constructs genuine compact-test domination on the same
interior physical restart, without spatial Lipschitz or equicontinuity. -/
theorem h3Path_interiorTemporalDomination_of_signedL2Envelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hEnvelope : h3PathInteriorTimeSignedL2EnvelopeAt244 hH3 s) :
    h3PathInteriorTimeTemporalDominationAt244 hH3 s := by
  rcases hEnvelope with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hL2⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_compactTemporalDomination_of_signedL2Envelope244
    hNSShort t₀ τ hL2

/-- Spatial L² envelopes for the signed old momentum suffice for the
actual physical Hilbert L² time derivative at the observation time. -/
theorem h3Path_physicalHilbertHasDerivAt_of_signedL2Envelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hEnvelope : h3PathInteriorTimeSignedL2EnvelopeAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_interiorTemporalDomination244
    hH3 (h3Path_interiorTemporalDomination_of_signedL2Envelope244
      hH3 hEnvelope)

/-- A genuine physical momentum time distribution on every strict interval
covered by local spatial L² envelopes for the signed classical PDE source. -/
theorem h3Path_distributionalMomentum_of_signedL2Envelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hEnvelope : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedL2EnvelopeAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_interiorTemporalDomination244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorTemporalDomination_of_signedL2Envelope244
    hH3 (hEnvelope s hs)

/-- If a strict physical interval has a nonzero Hilbert momentum FTC defect,
its signed PDE cannot possess these local spatial L² envelopes at every
interior time. This is an obstruction, not an assertion of nonregularity. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_signedL2EnvelopeFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeSignedL2EnvelopeAt244 hH3 s := by
  classical
  by_contra hNo
  have hAll : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedL2EnvelopeAt244 hH3 s := by
    intro s hs
    by_contra hFail
    exact hNo ⟨s, hs, hFail⟩
  have hScalar : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
    intro φ _hφ s hs
    let ψ : H3PhysicalRealFinVectorL2Hilbert :=
      h3WeakTestVectorPhysicalL2Hilbert φ
    exact (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s
      (h3Path_physicalHilbertHasDerivAt_of_signedL2Envelope244
        hH3 (hAll s hs))
  have hWeak := h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
    hH3 ha hab hb hScalar
  have hZero := (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2 hWeak
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
