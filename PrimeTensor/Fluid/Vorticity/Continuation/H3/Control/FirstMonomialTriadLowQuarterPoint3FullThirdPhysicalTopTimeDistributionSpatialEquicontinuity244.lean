import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionSignedOscillation244
import PrimeTensor.Fluid.Vorticity.Preterminal.Temporal.Separate
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# Spatial equicontinuity turns separate PDE continuity into uniform temporal oscillation

The old physical Navier--Stokes equation supplies separate continuity of the
signed momentum RHS F_j(t,x) = temporal derivative of velocity. In particular
for every fixed x, t ↦ F_j(t,x) is continuous. Separate continuity alone does
not give a uniform time modulus on compact spatial test supports.

A *locally time-uniform spatial Lipschitz constant* on each compact test
support is sufficient. Compactness gives finitely many spatial centers;
pointwise time continuity at these centers and the Lipschitz estimate produce
uniform temporal oscillation on the entire support. This supplies the previous
signed oscillation criterion and then genuine physical distributional momentum.

The spatial Lipschitz bound is an explicit extra analytic hypothesis. H3 path
admissibility proves spatial C1 at each time but not a time-uniform spatial
C1 ceiling. This module does not infer the latter incorrectly.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

-- The physical coordinates are a finite product of real Hilbert coordinates.
-- Pin the same norm topology as the existing old-time domination proofs.
noncomputable local instance axisFintypeH3SpatialEquicontinuity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SpatialEquicontinuity244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance point3NormTopologicalSpaceH3SpatialEquicontinuity244 :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Uniform-in-space time convergence from pointwise time continuity and a
locally uniform spatial Lipschitz estimate, on an *arbitrary compact set*.
The argument uses a finite cover, not an assumed product-space continuity. -/
theorem h3Path_compactUniformTimeOscillation_of_spatialLipschitz244
    {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (hK : IsCompact K)
    (f : ℝ → X → ℝ) (s : ℝ)
    (hPointwise : ∀ x ∈ K, ContinuousAt (fun r : ℝ => f r x) s)
    (hSpatial : ∃ S : Set ℝ, S ∈ 𝓝 s ∧
      ∃ L : ℝ, 0 ≤ L ∧
        ∀ r ∈ S, ∀ x ∈ K, ∀ y ∈ K,
          ‖f r x - f r y‖ ≤ L * dist x y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Set ℝ, S ∈ 𝓝 s ∧
      ∀ r ∈ S, ∀ x ∈ K, ‖f r x - f s x‖ ≤ ε := by
  classical
  obtain ⟨S, hS, L, hL, hLip⟩ := hSpatial
  have hLp : 0 < L + 1 := by linarith
  let δ : ℝ := ε / (8 * (L + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδEq : (L + 1) * δ = ε / 8 := by
    dsimp [δ]
    field_simp [ne_of_gt hLp]
    <;> ring
  have hLδ : L * δ ≤ ε / 8 := by
    nlinarith only [hδEq, hδ]
  have hCoverAll : K ⊆ ⋃ z : K, Metric.ball (z : X) δ := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hδ⟩
  obtain ⟨centers, hCover⟩ :=
    hK.elim_finite_subcover
      (fun z : K => Metric.ball (z : X) δ)
      (fun _ => Metric.isOpen_ball) hCoverAll
  have hCenterTime : ∀ z : K,
      ∀ᶠ r in 𝓝 s, ‖f r (z : X) - f s (z : X)‖ < ε / 2 := by
    intro z
    have hAt : ContinuousAt
        (fun r : ℝ => ‖f r (z : X) - f s (z : X)‖) s :=
      ((hPointwise (z : X) z.property).sub continuousAt_const).norm
    have hOpen : Set.Iio (ε / 2) ∈
        𝓝 ((fun r : ℝ => ‖f r (z : X) - f s (z : X)‖) s) := by
      simpa only [sub_self, norm_zero] using
        (isOpen_Iio.mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
    simpa only [Set.mem_Iio] using hAt.eventually hOpen
  have hFiniteTime :
      ∀ᶠ r in 𝓝 s, ∀ z ∈ centers,
        ‖f r (z : X) - f s (z : X)‖ < ε / 2 := by
    have hAux : ∀ zs : Finset K,
        ∀ᶠ r in 𝓝 s, ∀ z ∈ zs,
          ‖f r (z : X) - f s (z : X)‖ < ε / 2 := by
      intro zs
      induction zs using Finset.induction_on with
      | empty =>
          simp
      | @insert z zs hz ih =>
          filter_upwards [ih, hCenterTime z] with r hr hzr
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact hzr
          · exact hr y hy'
    exact hAux centers
  have hSN : S ∩ {r : ℝ | ∀ z ∈ centers,
        ‖f r (z : X) - f s (z : X)‖ < ε / 2} ∈ 𝓝 s :=
    inter_mem hS hFiniteTime
  refine ⟨_, hSN, ?_⟩
  intro r hr x hx
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hCover hx)
  obtain ⟨hzFin, hxBall⟩ := Set.mem_iUnion.mp hz
  have hdist : dist x (z : X) ≤ δ :=
    (Metric.mem_ball.mp hxBall).le
  have hFirst : ‖f r x - f r (z : X)‖ ≤ ε / 8 := by
    calc
      _ ≤ L * dist x (z : X) := hLip r hr.1 x hx (z : X) z.property
      _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist hL
      _ ≤ ε / 8 := hLδ
  have hThird : ‖f s (z : X) - f s x‖ ≤ ε / 8 := by
    calc
      _ ≤ L * dist (z : X) x :=
        hLip s (mem_of_mem_nhds hS) (z : X) z.property x hx
      _ = L * dist x (z : X) := by rw [dist_comm]
      _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist hL
      _ ≤ ε / 8 := hLδ
  have hMiddle : ‖f r (z : X) - f s (z : X)‖ < ε / 2 :=
    hr.2 z hzFin
  calc
    ‖f r x - f s x‖ =
        ‖(f r x - f r (z : X)) +
          (f r (z : X) - f s (z : X)) +
          (f s (z : X) - f s x)‖ := by
      congr 1
      ring
    _ ≤ (‖f r x - f r (z : X)‖ +
          ‖f r (z : X) - f s (z : X)‖) +
          ‖f s (z : X) - f s x‖ := by
      calc
        ‖(f r x - f r (z : X)) +
            (f r (z : X) - f s (z : X)) +
            (f s (z : X) - f s x)‖ ≤
            ‖(f r x - f r (z : X)) +
              (f r (z : X) - f s (z : X))‖ +
              ‖f s (z : X) - f s x‖ := norm_add_le _ _
        _ ≤ (‖f r x - f r (z : X)‖ +
              ‖f r (z : X) - f s (z : X)‖) +
              ‖f s (z : X) - f s x‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ε := by linarith only [hFirst, hMiddle, hThird, hε]

/-- The signed physical momentum PDE has an actual continuous temporal
section at each fixed physical spatial point. The key input is the *existing*
C1-in-time regularity of the old velocity and the classical PDE identity. -/
theorem h3Preterminal_signedPhysicalMomentum_continuousAt_time244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) (i : Fin 3) :
    ContinuousAt
      (fun r : ℝ => h3PreterminalSignedPhysicalMomentumAt244 hNS r x i) t := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three := Classical.choose hNS
  have hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T :=
    Classical.choose_spec hNS
  have hTime : ContinuousAt
      (fun r : ℝ => temporal.d
        (fun q : ℝ => loggedVelocityComponent u q (h3AxisOfFin3 i) x) r) t :=
    loggedPreterminalTemporalDerivative_continuousAt_time
      hNS ht x (h3AxisOfFin3 i)
  have hEq (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
      h3PreterminalSignedPhysicalMomentumAt244 hNS r x i =
        temporal.d
          (fun q : ℝ => loggedVelocityComponent u q (h3AxisOfFin3 i) x) r := by
    unfold h3PreterminalSignedPhysicalMomentumAt244
    exact (hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
      hr x (h3AxisOfFin3 i)).symm
  apply hTime.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  exact hEq r hr

/-- Local spatial Lipschitz constants for the signed PDE expression on
compact spatial test supports, uniformly for time close to the anchor.
This is weaker than assuming full joint spacetime continuity, but stronger
than the fixed-time C1 estimates already provided by preterminal regularity. -/
def h3PreterminalSignedMomentumLocalSpatialLipschitzOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ τ : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) τ →
    ∀ i : Fin 3,
      ∃ S : Set ℝ, S ∈ 𝓝 s ∧
        (∀ r ∈ S, t₀ + r ∈ Set.Ioo (0 : ℝ) T) ∧
        ∃ L : ℝ, 0 ≤ L ∧
          ∀ r ∈ S,
            ∀ x ∈ tsupport (φ i : Point3 → ℝ),
            ∀ y ∈ tsupport (φ i : Point3 → ℝ),
              ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i -
                h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) y i‖ ≤
                  L * dist x y

/-- Compact spatial Lipschitz control plus the ALREADY PROVED pointwise
time continuity yields uniform temporal oscillation on each compact test.
Only a spatial equicontinuity estimate, not full joint continuity, remains. -/
theorem h3Preterminal_signedOscillation_of_localSpatialLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : 0 < t₀) (hEnd : t₀ + τ < T)
    (hLip : h3PreterminalSignedMomentumLocalSpatialLipschitzOnElapsed244
      hNS t₀ τ) :
    h3PreterminalSignedMomentumUniformTimeOscillationOnElapsed244
      hNS t₀ τ := by
  intro φ hφ s hs i ε hε
  obtain ⟨S, hS, hSAbs, L, hL, hSpatial⟩ := hLip φ hφ s hs i
  have hTime : t₀ + s ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith only [ht₀, hs.1]
    · linarith only [hEnd, hs.2]
  let K : Set Point3 := tsupport (φ i : Point3 → ℝ)
  have hK : IsCompact K := by
    unfold point3NormTopologicalSpaceH3SpatialEquicontinuity244
    exact (φ i).hasCompactSupport
  have hPointwise : ∀ x ∈ K,
      ContinuousAt
        (fun r : ℝ => h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i) s := by
    intro x _hx
    exact (h3Preterminal_signedPhysicalMomentum_continuousAt_time244
      hNS hTime x i).comp (continuousAt_const.add continuousAt_id)
  obtain ⟨V, hV, hOsc⟩ :=
    h3Path_compactUniformTimeOscillation_of_spatialLipschitz244
      K hK
      (fun r x => h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i)
      s hPointwise
      ⟨S, hS, L, hL, hSpatial⟩ ε hε
  refine ⟨V ∩ S, inter_mem hV hS, ?_, ?_⟩
  · intro r hr
    exact hSAbs r hr.2
  · intro r hr x hx
    exact hOsc r hr.1 x hx

/-- A straddling canonical physical restart carrying the weaker local
spatial Lipschitz hypothesis, not an assumed temporal oscillation modulus. -/
def h3PathInteriorTimeSignedSpatialLipschitzAt244
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
      h3PreterminalSignedMomentumLocalSpatialLipschitzOnElapsed244
        hNSShort t₀ τ

/-- Turn local spatial Lipschitz bounds on a straddling physical restart
into the previously established signed temporal-oscillation criterion. -/
theorem h3Path_interiorSignedOscillation_of_spatialLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hLip : h3PathInteriorTimeSignedSpatialLipschitzAt244 hH3 s) :
    h3PathInteriorTimeSignedOscillationAt244 hH3 s := by
  rcases hLip with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hLip⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_signedOscillation_of_localSpatialLipschitz244
    hNSShort ht₀.1 hEnd hLip

/-- The genuine old physical Navier--Stokes momentum time-distribution
identity follows from local spatial equicontinuity of its signed RHS,
with no assumed spacetime joint continuity or temporal oscillation. -/
theorem h3Path_distributionalMomentum_of_spatialLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hLip : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedSpatialLipschitzAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_signedOscillation244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorSignedOscillation_of_spatialLipschitz244
    hH3 (hLip s hs)

/-- A nonzero physical Hilbert momentum FTC defect forces failure of the
local uniform spatial-Lipschitz condition somewhere in the interval. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_spatialLipschitzFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeSignedSpatialLipschitzAt244 hH3 s := by
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_signedOscillationFailure244
      hH3 ha hab hb hNonzero
  refine ⟨s, hs, ?_⟩
  intro hLip
  exact hFail (h3Path_interiorSignedOscillation_of_spatialLipschitz244
    hH3 hLip)

end
end PrimeTensor.FirstMonomialTriad
