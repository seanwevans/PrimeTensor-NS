import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionProductFubini244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Temporal.Mass.Reduction
import Mathlib.Tactic

/-!
# Old temporal L¹(time;L²(space)) norm closes physical momentum Fubini

The previous checkpoint needed space-time product integrability of the
compact-tested old temporal velocity derivative. It is enough for the *actual*
old derivative to have a spatial L² slice at every interior elapsed time and
an integrable-in-time spatial L² norm. This does not require a common
pointwise spatial envelope, spatial equicontinuity, or joint continuity.

The proof uses the repository's existing joint measurability of the old
Carathéodory temporal derivative, sharp L²--L² Hölder on each spatial slice,
and its proven spatial-norm-mass-to-Fubini bridge. The L¹L² bound remains an
explicit premise; it is not inferred merely from the continuity of the
projected Leray source (the raw temporal derivative can carry a pressure part).
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3OldTemporalL1L2Fubini244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3OldTemporalL1L2Fubini244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Spatial Cauchy--Schwarz plus known joint measurability converts
integrability of the old derivative's spatial L² norm in time into the
integrability of one compact-tested old temporal spatial norm mass in time. -/
theorem h3Preterminal_oldTemporalMassIntegrable_of_L1TimeL2Space244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ) (φ : H3WeakTestVector) (i : Fin 3)
    (hSlice : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) q →
      MemLp
        (fun x : Point3 =>
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        2 (volume : Measure Point3))
    (hTime : Integrable
      (fun r : ℝ =>
        (∫ x : Point3,
          ‖h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))) :
    Integrable
      (h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
        hNS t i (φ i))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) := by
  let μq : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)
  let F : ℝ → Point3 → ℝ := fun r x =>
    h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
      hNS i (t + r) x
  let C : ℝ :=
    (∫ x : Point3, ‖φ i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
  let G : ℝ → ℝ := fun r =>
    (∫ x : Point3, ‖F r x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
  let M : ℝ → ℝ :=
    h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
      hNS t i (φ i)
  have hφ : MemLp (fun x : Point3 => φ i x) 2
      (volume : Measure Point3) :=
    (φ i).continuous.memLp_of_hasCompactSupport (φ i).hasCompactSupport
  have hTwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
    norm_num
  have hφHolder : MemLp (fun x : Point3 => φ i x)
      (ENNReal.ofReal (2 : ℝ)) (volume : Measure Point3) := by
    simpa only [hTwo] using hφ
  have hG : Integrable G μq := by
    simpa only [G, F, μq] using hTime
  have hMMeas : AEStronglyMeasurable M μq := by
    exact
      (h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
        hNS i (φ i)).mono_measure (Measure.restrict_le_self)
  have hDom : ∀ᵐ r ∂μq, ‖M r‖ ≤ C * G r := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with r hr
    have hFr : MemLp (F r) 2 (volume : Measure Point3) :=
      hSlice r hr
    have hFrHolder : MemLp (F r)
        (ENNReal.ofReal (2 : ℝ)) (volume : Measure Point3) := by
      simpa only [hTwo] using hFr
    have hHolder : M r ≤ C * G r := by
      simpa only [M, C, G, F,
        h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul] using
        (MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
          (f := fun x : Point3 => φ i x) (g := F r)
          Real.HolderConjugate.two_two hφHolder hFrHolder)
    have hNonneg : 0 ≤ M r :=
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_nonneg
        hNS i (φ i) r
    calc
      ‖M r‖ = M r := Real.norm_of_nonneg hNonneg
      _ ≤ C * G r := hHolder
  have hMajor : Integrable (fun r => C * G r) μq := hG.const_mul C
  exact Integrable.mono' hMajor hMMeas hDom

/-- Genuine L¹ in elapsed time of the physical old temporal derivative's
spatial L² norm, on every shortened prefix of a physical restart. The
slice L² membership is requested on the strict open time window only. -/
def h3PreterminalOldTemporalL1TimeL2SpaceOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t τ : ℝ) : Prop :=
  ∀ (i : Fin 3) (q : Set.Icc (0 : ℝ) τ),
    (∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) (q : ℝ) →
      MemLp
        (fun x : Point3 =>
          h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        2 (volume : Measure Point3)) ∧
    Integrable
      (fun r : ℝ =>
        (∫ x : Point3,
          ‖h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (q : ℝ)))

/-- L¹(time;L²(space)) of the OLD physical temporal derivative is sufficient
for every compact-solenoidal Fubini hypothesis on a shortened restart. -/
theorem h3Preterminal_oldTemporalProductFubini_of_L1TimeL2Space244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL1L2 : h3PreterminalOldTemporalL1TimeL2SpaceOnElapsed244
      hNS t τ) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
      hNS ht hEnd hTail := by
  intro φ _hφ q
  apply H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
    hNS t (q : ℝ) φ
  intro i
  obtain ⟨hSlice, hTime⟩ := hL1L2 i q
  exact h3Preterminal_oldTemporalMassIntegrable_of_L1TimeL2Space244
    hNS t (q : ℝ) φ i hSlice hTime

/-- A genuine physical restart strictly containing the observation time,
with raw old temporal L¹L² control (as opposed to projected-source control). -/
def h3PathInteriorTimeOldTemporalL1L2At244
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
      h3PreterminalOldTemporalL1TimeL2SpaceOnElapsed244
        hNSShort t₀ τ

/-- The L¹L² data turn into the already formalized interior Fubini corridor,
with the same restart geometry and without a pointwise spatial envelope. -/
theorem h3Path_interiorOldTemporalProductFubini_of_L1TimeL2Space244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hL1L2 : h3PathInteriorTimeOldTemporalL1L2At244 hH3 s) :
    h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s := by
  rcases hL1L2 with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hL1L2⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_oldTemporalProductFubini_of_L1TimeL2Space244
    hNSShort ht₀ hEnd hTail hL1L2

/-- Physical strong Hilbert differentiation from raw old temporal L¹L². -/
theorem h3Path_physicalHilbertHasDerivAt_of_oldTemporalL1L2Fubini244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hL1L2 : h3PathInteriorTimeOldTemporalL1L2At244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_oldTemporalProductFubini244
    hH3 (h3Path_interiorOldTemporalProductFubini_of_L1TimeL2Space244
      hH3 hL1L2)

/-- The full physical distributional momentum equation on any strict
interval whose interior times possess raw old temporal L¹L² restarts. -/
theorem h3Path_distributionalMomentum_of_oldTemporalL1L2Fubini244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hL1L2 : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeOldTemporalL1L2At244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_oldTemporalProductFubini244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorOldTemporalProductFubini_of_L1TimeL2Space244
    hH3 (hL1L2 s hs)

/-- A nonzero physical Hilbert FTC defect witnesses an interior failure of
the full old temporal L¹L² criterion on every straddling restart. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_oldTemporalL1L2Failure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeOldTemporalL1L2At244 hH3 s := by
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_oldTemporalProductFubiniFailure244
      hH3 ha hab hb hNonzero
  refine ⟨s, hs, ?_⟩
  intro hL1L2
  exact hFail (h3Path_interiorOldTemporalProductFubini_of_L1TimeL2Space244
    hH3 hL1L2)

end
end PrimeTensor.FirstMonomialTriad
