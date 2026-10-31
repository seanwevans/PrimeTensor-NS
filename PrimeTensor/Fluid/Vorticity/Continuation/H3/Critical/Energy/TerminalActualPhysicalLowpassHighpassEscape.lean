import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLaplacianTimeL1
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedComponentResidualEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceIdentification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.RHS.Hilbert
import Mathlib.Tactic

/-!
# Real physical sharp cutoff and the actual high-frequency source obstruction

The physical cutoff is the genuine Fourier-conjugated operator

  Pρ f = real-inverse-Fourier (1_{2π|ξ|<ρ} Fourier f).

A real physical source is embedded into the complex Fourier carrier before
multiplying by the radial indicator.  The real inverse-Fourier decoder is
needed only for reconstruction; Hermitian reality of each physical source
ensures the exact complex Fourier round trip, rather than an unsupported
commutation of a complex cutoff with the real-part projection.

On every strict tail of an H³ energy-class path, this physical cutoff of the
ACTUAL projected momentum RHS is Bochner-L¹.  If the physical L² velocity
has no strong terminal trace, one fixed coordinate of the complementary
high-pass actual source is non-L¹ and has cofinal L² norm spikes, for EVERY
fixed nonnegative Fourier radius.  This is a necessary alternative under
failure of a terminal trace, not a proof of finite-time singularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1600000

noncomputable local instance axisFintypeH3ActualPhysicalCutoff
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ActualPhysicalCutoff :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual physical-space sharp low-pass operator, defined using the
real physical Fourier bridge and its true inverse Fourier decoder. -/
noncomputable def h3CriticalPhysicalSharpLowCutoffApply
    (ρ : ℝ) (f : H3ScalarL2) : H3ScalarL2 :=
  h3Path_physicalRawFourierDecoder244
    (h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 f))

/-- The physical sharp cutoff is a contraction on actual real spatial L². -/
theorem h3Critical_physicalSharpLowCutoff_norm_le
    (ρ : ℝ) (f : H3ScalarL2) :
    ‖h3CriticalPhysicalSharpLowCutoffApply ρ f‖ ≤ ‖f‖ := by
  calc
    ‖h3CriticalPhysicalSharpLowCutoffApply ρ f‖ ≤
      ‖h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 f)‖ :=
        h3Path_physicalRawFourierDecoder_norm_le244 _
    _ ≤ ‖h3ScalarFourierL2 f‖ :=
      h3Critical_fourierSharpLowCutoffApply_norm_le ρ _
    _ = ‖f‖ := norm_h3ScalarFourierL2 f

/-- The real physical cutoff respects subtraction. -/
theorem h3Critical_physicalSharpLowCutoff_sub
    (ρ : ℝ) (f g : H3ScalarL2) :
    h3CriticalPhysicalSharpLowCutoffApply ρ (f - g) =
      h3CriticalPhysicalSharpLowCutoffApply ρ f -
        h3CriticalPhysicalSharpLowCutoffApply ρ g := by
  unfold h3CriticalPhysicalSharpLowCutoffApply
  rw [h3ScalarFourierL2_sub, map_sub,
    h3Path_physicalRawFourierDecoder_sub244]

/-- The physical sharp cutoff is 1-Lipschitz. -/
theorem h3Critical_physicalSharpLowCutoff_norm_sub_le
    (ρ : ℝ) (f g : H3ScalarL2) :
    ‖h3CriticalPhysicalSharpLowCutoffApply ρ f -
      h3CriticalPhysicalSharpLowCutoffApply ρ g‖ ≤ ‖f - g‖ := by
  rw [← h3Critical_physicalSharpLowCutoff_sub]
  exact h3Critical_physicalSharpLowCutoff_norm_le ρ (f - g)

/-- Strong continuity of the real physical sharp Fourier cutoff. -/
theorem h3Critical_physicalSharpLowCutoff_continuous (ρ : ℝ) :
    Continuous (h3CriticalPhysicalSharpLowCutoffApply ρ) := by
  have hLip : LipschitzWith 1 (h3CriticalPhysicalSharpLowCutoffApply ρ) :=
    LipschitzWith.of_dist_le_mul (fun f g => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
        h3Critical_physicalSharpLowCutoff_norm_sub_le ρ f g)
  exact hLip.continuous

/-- Hermitian Fourier data commute with the physical cutoff exactly: no
assumed complex/real commutation is involved. -/
theorem h3Critical_physicalSharpLowCutoff_decode_hermitian
    (ρ : ℝ) (F : H3FourierComplexL2)
    (hF : H3FourierL2Hermitian F) :
    h3CriticalPhysicalSharpLowCutoffApply ρ
      (h3Path_physicalRawFourierDecoder244 F) =
      h3Path_physicalRawFourierDecoder244
        (h3CriticalFourierSharpLowCutoffCLM ρ F) := by
  unfold h3CriticalPhysicalSharpLowCutoffApply
  have hRound : h3ScalarFourierL2
      (h3Path_physicalRawFourierDecoder244 F) = F :=
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian F hF
  rw [hRound]

/-- The genuine actual strict-time spectral state is raw-Hermitian. This
uses its existing exact identification with a real canonical restart state. -/
theorem h3Critical_actualSpectralVelocity_rawHermitian
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    H3SpectralVelocityRawHermitian
      (h3AuditActualSpectralVelocityTotal hH3 s) := by
  obtain ⟨t, S, E, ht, hST, _hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := s - t
  have hτ : 0 ≤ τ := by
    dsimp only [τ]
    exact hElapsed.le
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos (le_of_lt hST)
  let q : Set.Icc (0 : ℝ) τ := ⟨τ, hτ, le_rfl⟩
  have hTime : t + (q : ℝ) = s := by
    dsimp only [q, τ]
    ring
  have hEq := h3Audit_actualSpectralVelocityTotal_eq_canonicalElapsed
    hH3 hShort (le_of_lt hST) ht hEnd hTail q
  rw [hTime] at hEq
  rw [hEq]
  exact h3PreterminalTailCanonicalSpectralStateOnElapsed_rawHermitian
    hShort.navier_stokes ht hEnd hTail q

/-- At every genuine strict physical time, the cutoff of the ACTUAL
projected physical source equals the kinetic low-band reconstruction. -/
theorem h3Critical_actualPhysicalSharpLowCutoff_source_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (ρ : ℝ) (i : Fin 3) :
    h3CriticalPhysicalSharpLowCutoffApply ρ
      ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i) =
      h3CriticalLowRadialLaplacianPhysicalL2 ρ
        ((h3AuditActualSpectralVelocityTotal hH3 t) i) -
      h3CriticalLowRadialLerayPhysicalL2 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) i := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let D : H3FourierComplexL2 :=
    h3SpectralScalarLaplacianRawFourierL2 (U i)
  let N : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2 U U i
  have hHermU : H3SpectralVelocityRawHermitian U :=
    h3Critical_actualSpectralVelocity_rawHermitian hH3 t ht
  have hHermD : H3FourierL2Hermitian D :=
    h3SpectralScalarLaplacianRawFourierL2_preserves_hermitian (hHermU i)
  have hHermN : H3FourierL2Hermitian N :=
    h3RawFinLerayOuterProductDivergenceFourierL2_preserves_hermitian
      hHermU hHermU i
  have hSource :
      (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i =
        h3Path_physicalRawFourierDecoder244 D -
        h3Path_physicalRawFourierDecoder244 N := by
    change (h3AuditInitialActualSpectralLaplacianTotal hH3 t -
      h3AuditInitialActualSpectralLerayTotal hH3 t).ofLp i = _
    rw [PiLp.sub_apply]
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left ht]
    rfl
  rw [hSource, h3Critical_physicalSharpLowCutoff_sub]
  rw [h3Critical_physicalSharpLowCutoff_decode_hermitian ρ D hHermD,
    h3Critical_physicalSharpLowCutoff_decode_hermitian ρ N hHermN]
  have hLeray : h3CriticalLowRadialLerayFourierL2 ρ U i =
      h3CriticalFourierSharpLowCutoffCLM ρ N :=
    h3Critical_lowRadialLerayFourierL2_eq_sharpCutoffCLM ρ U i
  -- Expose the two local Fourier states on the right first: simplifying
  -- only the global definitions does not unfold the local `let` bindings.
  change
    h3Path_physicalRawFourierDecoder244
        (h3CriticalFourierSharpLowCutoffCLM ρ D) -
      h3Path_physicalRawFourierDecoder244
        (h3CriticalFourierSharpLowCutoffCLM ρ N) =
    h3Path_physicalRawFourierDecoder244
        (h3CriticalFourierSharpLowCutoffCLM ρ D) -
      h3Path_physicalRawFourierDecoder244
        (h3CriticalLowRadialLerayFourierL2 ρ U i)
  rw [hLeray]

/-- The actual physical sharp cutoff of the projected RHS is Bochner-L¹ on
any later strict kinetic-anchored tail, without a terminal H³ ceiling. -/
theorem h3Critical_actualPhysicalSharpLowCutoff_source_intervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (i : Fin 3) :
    IntervalIntegrable (fun t : ℝ =>
      h3CriticalPhysicalSharpLowCutoffApply ρ
        ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i))
      volume b T := by
  let B : ℝ → H3ScalarL2 := fun t =>
    h3CriticalLowRadialLaplacianPhysicalL2 ρ
        ((h3AuditActualSpectralVelocityTotal hH3 t) i) -
      h3CriticalLowRadialLerayPhysicalL2 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) i
  have hBInt : IntervalIntegrable B volume b T :=
    h3Critical_actual_lowRadialProjectedPhysicalL2_intervalIntegrable
      hH3 hClass b hb ρ hρ i
  have hSub : Set.Ioo b T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hEq : (fun t : ℝ =>
      h3CriticalPhysicalSharpLowCutoffApply ρ
        ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i))
      =ᵐ[((volume : Measure ℝ).restrict (Set.Ioo b T))] B :=
    ae_restrict_of_forall_mem measurableSet_Ioo (by
      intro t ht
      exact h3Critical_actualPhysicalSharpLowCutoff_source_eq
        hH3 t (hSub ht) ρ i)
  have hOn : IntegrableOn B (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hBInt
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2
  exact hOn.congr hEq.symm

/-- On a single bounded terminal tail, a continuous non-L¹ scalar physical
source necessarily has arbitrarily large L² norm. -/
theorem h3Critical_nonintegrable_tail_forces_spikes
    (R : ℝ → H3ScalarL2)
    {T c : ℝ} (hc : c < T)
    (hCont : ContinuousOn R (Set.Ioo c T))
    (hNonInt : ¬ IntervalIntegrable R volume c T) :
    ∀ M : ℝ, ∃ t : ℝ, t ∈ Set.Ioo c T ∧ M < ‖R t‖ := by
  intro M
  by_contra hNone
  have hBound : ∀ t : ℝ, t ∈ Set.Ioo c T → ‖R t‖ ≤ M := by
    intro t ht
    exact le_of_not_gt (fun hLarge => hNone ⟨t, ht, hLarge⟩)
  have hConst : IntervalIntegrable (fun _ : ℝ => M) volume c T :=
    intervalIntegrable_const
  have hMajor : IntegrableOn (fun _ : ℝ => M) (Set.Ioo c T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).1 hConst
  have hMeas : AEStronglyMeasurable R
      ((volume : Measure ℝ).restrict (Set.Ioo c T)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo
  have hDom : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo c T)),
      ‖R t‖ ≤ M :=
    ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hBound t ht)
  have hInt : IntegrableOn R (Set.Ioo c T) volume :=
    Integrable.mono' hMajor hMeas hDom
  exact hNonInt ((intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).2 hInt)

/-- If the actual physical L² velocity has no strong terminal trace,
ONE fixed spatial coordinate of the genuine Fourier high-pass projected
momentum source remains non-L¹ and has cofinal L² spikes at EVERY fixed
nonnegative radius. The reference anchor b is fixed before choosing radius. -/
theorem h3Critical_noL2Trace_actualPhysicalHighpass_escape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ i : Fin 3,
      ∀ (ρ : ℝ), 0 ≤ ρ →
        ∀ (c : ℝ), c ∈ Set.Ioo b T →
          (¬ IntervalIntegrable (fun t : ℝ =>
              (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i -
                h3CriticalPhysicalSharpLowCutoffApply ρ
                  ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i))
              volume c T) ∧
          (∀ M : ℝ, ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < ‖(h3PathActualProjectedMomentumSource244 hH3 t).ofLp i -
                h3CriticalPhysicalSharpLowCutoffApply ρ
                  ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)‖) := by
  obtain ⟨i, hi, _⟩ :=
    h3Critical_noL2Trace_fixed_projected_coordinate_nonintegrable_and_spikes
      hH3 hNoTrace
  refine ⟨i, ?_⟩
  intro ρ hρ c hc
  let F : ℝ → H3ScalarL2 :=
    fun t => (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i
  let B : ℝ → H3ScalarL2 :=
    fun t => h3CriticalPhysicalSharpLowCutoffApply ρ (F t)
  let R : ℝ → H3ScalarL2 := fun t => F t - B t
  have hcClass : c ∈ Set.Ioo a T := ⟨lt_trans hb.1 hc.1, hc.2⟩
  have hBInt : IntervalIntegrable B volume c T :=
    h3Critical_actualPhysicalSharpLowCutoff_source_intervalIntegrable
      hH3 hClass c hcClass ρ hρ i
  have hFNonInt : ¬ IntervalIntegrable F volume c T :=
    hi c ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 hc.1), hc.2⟩
  have hRNonInt : ¬ IntervalIntegrable R volume c T := by
    intro hRInt
    have hFInt : IntervalIntegrable F volume c T := by
      simpa only [R, sub_add_cancel] using hRInt.add hBInt
    exact hFNonInt hFInt
  have hSourceCont : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Ioo (0 : ℝ) T) := by
    change ContinuousOn
      (fun t : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t)
      (Set.Ioo (0 : ℝ) T)
    exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
  have hEval : Continuous
      (fun V : H3PhysicalRealFinVectorL2Hilbert => V.ofLp i) :=
    PiLp.continuous_apply
      (2 : ENNReal) (fun _ : Fin 3 => H3ScalarL2) i
  have hFCont : ContinuousOn F (Set.Ioo (0 : ℝ) T) :=
    hEval.comp_continuousOn hSourceCont
  have hSub : Set.Ioo c T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 (lt_trans hc.1 ht.1)), ht.2⟩
  have hRCont : ContinuousOn R (Set.Ioo c T) :=
    (hFCont.mono hSub).sub
      ((h3Critical_physicalSharpLowCutoff_continuous ρ).comp_continuousOn
        (hFCont.mono hSub))
  exact ⟨hRNonInt,
    h3Critical_nonintegrable_tail_forces_spikes R hc.2 hRCont hRNonInt⟩

end
end PrimeTensor.Bridge.Euclidean
