import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionSpatialEquicontinuity244
import Mathlib.Tactic

/-!
# Spatial equicontinuity on compact supports suffices for physical momentum distributions

The preceding spatial Lipschitz criterion gives uniform-in-time control of
spatial increments. The argument requires less: for every epsilon one may
choose a spatial radius and a time neighborhood on which ALL temporal slices
are equicontinuous on the compact spatial test support. This criterion does
not require a finite global Lipschitz constant, nor any joint continuity of
the signed Navier--Stokes momentum expression.

The classical PDE gives the needed pointwise-in-space time continuity.
Finite compact covers then turn it into UNIFORM temporal oscillation. This
closes the physical momentum distribution equation conditional on the new
spatial equicontinuity premise. Bare H3 admissibility is not claimed to
imply equicontinuity in time at this spatial derivative order.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SpatialEquiCriterion244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SpatialEquiCriterion244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance point3NormTopologicalSpaceH3SpatialEquiCriterion244 :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Pointwise time continuity and locally uniform spatial equicontinuity
on a compact set imply uniform-in-space temporal oscillation.
This requires neither spatial Lipschitz estimates nor joint continuity. -/
theorem h3Path_compactUniformTimeOscillation_of_spatialEquicontinuity244
    {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (hK : IsCompact K)
    (f : ℝ → X → ℝ) (s : ℝ)
    (hPointwise : ∀ x ∈ K, ContinuousAt (fun r : ℝ => f r x) s)
    (hEqui : ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ S : Set ℝ, S ∈ 𝓝 s ∧
          ∀ r ∈ S, ∀ x ∈ K, ∀ y ∈ K,
            dist x y < δ → ‖f r x - f r y‖ ≤ η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Set ℝ, S ∈ 𝓝 s ∧
      ∀ r ∈ S, ∀ x ∈ K, ‖f r x - f s x‖ ≤ ε := by
  classical
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  obtain ⟨δ, hδ, S, hS, hSpatial⟩ := hEqui (ε / 8) hε8
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
      | empty => simp
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
  have hdist : dist x (z : X) < δ := Metric.mem_ball.mp hxBall
  have hFirst : ‖f r x - f r (z : X)‖ ≤ ε / 8 :=
    hSpatial r hr.1 x hx (z : X) z.property hdist
  have hThird : ‖f s (z : X) - f s x‖ ≤ ε / 8 :=
    hSpatial s (mem_of_mem_nhds hS) (z : X) z.property x hx
      (by simpa only [dist_comm] using hdist)
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

/-- The exact PDE-side hypothesis: uniform equicontinuity in space on each
compact weak-test support, *locally* in elapsed time. Its spatial modulus
is not required to be linear in distance. -/
def h3PreterminalSignedMomentumLocalSpatialEquicontinuityOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ τ : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) τ →
    ∀ i : Fin 3, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ S : Set ℝ, S ∈ 𝓝 s ∧
          (∀ r ∈ S, t₀ + r ∈ Set.Ioo (0 : ℝ) T) ∧
          ∀ r ∈ S,
            ∀ x ∈ tsupport (φ i : Point3 → ℝ),
            ∀ y ∈ tsupport (φ i : Point3 → ℝ),
              dist x y < δ →
                ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i -
                  h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) y i‖ ≤ η

/-- Local spatial equicontinuity gives actual uniform-in-space temporal
oscillation, since pointwise time continuity comes from the old PDE. -/
theorem h3Preterminal_signedOscillation_of_localSpatialEquicontinuity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : 0 < t₀) (hEnd : t₀ + τ < T)
    (hEqui : h3PreterminalSignedMomentumLocalSpatialEquicontinuityOnElapsed244
      hNS t₀ τ) :
    h3PreterminalSignedMomentumUniformTimeOscillationOnElapsed244
      hNS t₀ τ := by
  intro φ hφ s hs i ε hε
  have hTime : t₀ + s ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith only [ht₀, hs.1]
    · linarith only [hEnd, hs.2]
  let K : Set Point3 := tsupport (φ i : Point3 → ℝ)
  have hK : IsCompact K := by
    unfold point3NormTopologicalSpaceH3SpatialEquiCriterion244
    exact (φ i).hasCompactSupport
  have hPointwise : ∀ x ∈ K,
      ContinuousAt
        (fun r : ℝ => h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i) s := by
    intro x _hx
    exact (h3Preterminal_signedPhysicalMomentum_continuousAt_time244
      hNS hTime x i).comp (continuousAt_const.add continuousAt_id)
  have hSpatial : ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ S : Set ℝ, S ∈ 𝓝 s ∧
          ∀ r ∈ S, ∀ x ∈ K, ∀ y ∈ K,
            dist x y < δ →
              ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i -
                h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) y i‖ ≤ η := by
    intro η hη
    obtain ⟨δ, hδ, S, hS, _hSAbs, hBound⟩ := hEqui φ hφ s hs i η hη
    exact ⟨δ, hδ, S, hS, hBound⟩
  obtain ⟨V, hV, hOsc⟩ :=
    h3Path_compactUniformTimeOscillation_of_spatialEquicontinuity244
      K hK
      (fun r x => h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i)
      s hPointwise hSpatial ε hε
  have hSInside : {r : ℝ | t₀ + r ∈ Set.Ioo (0 : ℝ) T} ∈ 𝓝 s := by
    have hContinuous : ContinuousAt (fun r : ℝ => t₀ + r) s :=
      continuousAt_const.add continuousAt_id
    exact hContinuous (isOpen_Ioo.mem_nhds hTime)
  refine ⟨V ∩ {r : ℝ | t₀ + r ∈ Set.Ioo (0 : ℝ) T},
    inter_mem hV hSInside, ?_, ?_⟩
  · intro r hr
    exact hr.2
  · intro r hr x hx
    exact hOsc r hr.1 x hx

/-- In the local physical restart geometry, spatial equicontinuity is the
only extra PDE-side premise; the temporal modulus follows from compactness. -/
def h3PathInteriorTimeSignedSpatialEquicontinuityAt244
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
      h3PreterminalSignedMomentumLocalSpatialEquicontinuityOnElapsed244
        hNSShort t₀ τ

/-- Equicontinuity gives the signed oscillation criterion on the same
straddling physical restart; no artificial endpoint extrapolation. -/
theorem h3Path_interiorSignedOscillation_of_spatialEquicontinuity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hEqui : h3PathInteriorTimeSignedSpatialEquicontinuityAt244 hH3 s) :
    h3PathInteriorTimeSignedOscillationAt244 hH3 s := by
  rcases hEqui with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hEqui⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_signedOscillation_of_localSpatialEquicontinuity244
    hNSShort ht₀.1 hEnd hEqui

/-- The new weaker spatial equicontinuity condition supplies the genuine
physical Navier--Stokes momentum identity as a time distribution. -/
theorem h3Path_distributionalMomentum_of_spatialEquicontinuity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hEqui : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedSpatialEquicontinuityAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_signedOscillation244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorSignedOscillation_of_spatialEquicontinuity244
    hH3 (hEqui s hs)

/-- A failure of physical Hilbert FTC forces spatial equicontinuity to
fail somewhere on any strictly preterminal interval containing the defect. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_spatialEquicontinuityFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeSignedSpatialEquicontinuityAt244 hH3 s := by
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_signedOscillationFailure244
      hH3 ha hab hb hNonzero
  refine ⟨s, hs, ?_⟩
  intro hEqui
  exact hFail (h3Path_interiorSignedOscillation_of_spatialEquicontinuity244
    hH3 hEqui)

/-- The previously established fixed spatial Lipschitz bound implies the
strictly weaker equicontinuity premise. This gives a checkable relation
between the two PDE-facing regularity corridors. -/
theorem h3Preterminal_spatialEquicontinuity_of_spatialLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hLip : h3PreterminalSignedMomentumLocalSpatialLipschitzOnElapsed244
      hNS t₀ τ) :
    h3PreterminalSignedMomentumLocalSpatialEquicontinuityOnElapsed244
      hNS t₀ τ := by
  intro φ hφ s hs i η hη
  obtain ⟨S, hS, hSAbs, L, hL, hBound⟩ := hLip φ hφ s hs i
  have hLp : 0 < L + 1 := by linarith only [hL]
  let δ : ℝ := η / (L + 1)
  have hδ : 0 < δ := div_pos hη hLp
  have hδEq : (L + 1) * δ = η := by
    dsimp only [δ]
    field_simp [ne_of_gt hLp]
    <;> ring
  refine ⟨δ, hδ, S, hS, hSAbs, ?_⟩
  intro r hr x hx y hy hxy
  have hBoundXY := hBound r hr x hx y hy
  have hProduct : L * dist x y ≤ L * δ :=
    mul_le_mul_of_nonneg_left hxy.le hL
  have hLδ : L * δ ≤ η := by
    nlinarith only [hδEq, hδ]
  exact hBoundXY.trans (hProduct.trans hLδ)

end
end PrimeTensor.FirstMonomialTriad
