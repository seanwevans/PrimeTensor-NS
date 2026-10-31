import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualPhysicalLowpassHighpassEscape
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Reality.L2.Closure
import Mathlib.Tactic

/-!
# Exact Fourier localization of the actual terminal high-pass obstruction

The preceding physical-space theorem isolates a single coordinate of the
projected momentum source whose complement to every fixed low-frequency
cutoff is non-L¹ in terminal time and has cofinal physical L² spikes, under
failure of a strong terminal physical L² velocity trace.

Here the sharp Fourier cutoff is proved to preserve Hermitian symmetry.
This closes the real/complex round trip for *cutoff* Fourier states, not only
for the uncut physical PDE source. It identifies the Fourier transform of the
actual physical high-pass remainder with the sharp complementary multiplier
applied to the genuine physical source Fourier transform.

The exact high-band norm-square identity converts the physical spikes into
unbounded integrated Fourier mass outside every fixed radial frequency ball.
There is no assertion that the no-trace hypothesis occurs, nor that the
spectral source mass measures the H³ velocity dissipation itself.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ComplexConjugate

noncomputable section
set_option maxHeartbeats 1600000

noncomputable local instance axisFintypeH3ActualHighpassFourierMass
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ActualHighpassFourierMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The gradient-frequency ball is invariant under reflection. -/
theorem h3Critical_radialFrequencyBelow_neg_iff
    (ρ : ℝ) (ξ : H3FourierPoint3) :
    -ξ ∈ h3TerminalRadialFrequencyBelow ρ ↔
      ξ ∈ h3TerminalRadialFrequencyBelow ρ := by
  change h3FourierGradientMagnitude (-ξ) < ρ ↔
    h3FourierGradientMagnitude ξ < ρ
  unfold h3FourierGradientMagnitude
  simp only [norm_neg]

/-- A real even radial indicator preserves Hermitian Fourier reality. -/
theorem h3Critical_fourierSharpLowCutoff_preserves_hermitian
    (ρ : ℝ) {F : H3FourierComplexL2}
    (hF : H3FourierL2Hermitian F) :
    H3FourierL2Hermitian (h3CriticalFourierSharpLowCutoffCLM ρ F) := by
  change H3FourierL2Hermitian (h3CriticalFourierSharpLowCutoffApply ρ F)
  unfold H3FourierL2Hermitian at hF ⊢
  have hAt := h3Critical_fourierSharpLowCutoffApply_ae ρ F
  have hNeg := h3Fourier_ae_neg hAt
  filter_upwards [hAt, hNeg, hF] with ξ hAtξ hNegξ hHerm
  rw [hNegξ, hAtξ]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · have hξNeg : -ξ ∈ h3TerminalRadialFrequencyBelow ρ :=
      (h3Critical_radialFrequencyBelow_neg_iff ρ ξ).mpr hξ
    rw [Set.indicator_of_mem hξNeg, Set.indicator_of_mem hξ, hHerm]
  · have hξNeg : -ξ ∉ h3TerminalRadialFrequencyBelow ρ := by
      intro hNegMem
      exact hξ ((h3Critical_radialFrequencyBelow_neg_iff ρ ξ).mp hNegMem)
    rw [Set.indicator_of_notMem hξNeg, Set.indicator_of_notMem hξ]
    simp

/-- Genuine scalar physical Fourier transform commutes with the actual
sharp low-pass operator, including real-part reconstruction. -/
theorem h3Critical_scalarFourier_physicalSharpLowCutoff_eq
    (ρ : ℝ) (f : H3ScalarL2) :
    h3ScalarFourierL2 (h3CriticalPhysicalSharpLowCutoffApply ρ f) =
      h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 f) := by
  unfold h3CriticalPhysicalSharpLowCutoffApply
  have hHerm : H3FourierL2Hermitian (h3ScalarFourierL2 f) := by
    unfold h3ScalarFourierL2
    exact h3FourierL2_complexify_real_hermitian (h3ToFourierRealL2 f)
  exact h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian _
    (h3Critical_fourierSharpLowCutoff_preserves_hermitian ρ hHerm)

/-- The physical high-pass remainder has exactly the complementary Fourier
indicator as its scalar Plancherel transform. -/
theorem h3Critical_scalarFourier_physicalHighpass_eq
    (ρ : ℝ) (f : H3ScalarL2) :
    h3ScalarFourierL2 (f - h3CriticalPhysicalSharpLowCutoffApply ρ f) =
      h3ScalarFourierL2 f -
        h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 f) := by
  rw [h3ScalarFourierL2_sub,
    h3Critical_scalarFourier_physicalSharpLowCutoff_eq]

/-- The Fourier high-pass difference is precisely the indicator of the
complement of the fixed radial ball, almost everywhere. -/
theorem h3Critical_fourierSharpHighpass_ae
    (ρ : ℝ) (F : H3FourierComplexL2) :
    ((F - h3CriticalFourierSharpLowCutoffCLM ρ F : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
      (h3TerminalRadialFrequencyBelow ρ)ᶜ.indicator F := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub F (h3CriticalFourierSharpLowCutoffCLM ρ F),
    h3Critical_fourierSharpLowCutoffApply_ae ρ F
  ] with ξ hDiff hCut
  rw [hDiff]
  -- `hDiff` leaves a subtraction of functions. Evaluate at the frequency
  -- before rewriting the cutoff's pointwise Fourier representative.
  simp only [Pi.sub_apply]
  change (F : H3FourierPoint3 → ℂ) ξ -
      (h3CriticalFourierSharpLowCutoffApply ρ F :
        H3FourierPoint3 → ℂ) ξ =
    (h3TerminalRadialFrequencyBelow ρ)ᶜ.indicator F ξ
  rw [hCut]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · have hξC : ξ ∉ (h3TerminalRadialFrequencyBelow ρ)ᶜ := by
      simpa only [Set.mem_compl_iff, not_not] using hξ
    rw [Set.indicator_of_mem hξ, Set.indicator_of_notMem hξC]
    simp
  · have hξC : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ := by
      simpa only [Set.mem_compl_iff] using hξ
    rw [Set.indicator_of_notMem hξ, Set.indicator_of_mem hξC]
    simp

/-- The high-pass Fourier norm is EXACTLY the squared mass on the
complementary radial band, not just bounded by it. -/
theorem h3Critical_fourierSharpHighpass_norm_sq_eq_integral
    (ρ : ℝ) (F : H3FourierComplexL2) :
    ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖F ξ‖ ^ 2 ∂volume := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  rw [← integral_indicator (measurableSet_h3TerminalRadialFrequencyBelow ρ).compl]
  apply integral_congr_ae
  filter_upwards [h3Critical_fourierSharpHighpass_ae ρ F] with ξ hξ
  rw [hξ]
  by_cases hS : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS]
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS]
    simp

/-- The actual projected physical scalar momentum source, transported by
the *real* Plancherel Fourier isometry. -/
noncomputable def h3CriticalActualProjectedFourierSource
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3) (t : ℝ) : H3FourierComplexL2 :=
  h3ScalarFourierL2 ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)

/-- Fourier counterpart of the actual projected physical high-pass remainder. -/
noncomputable def h3CriticalActualProjectedHighpassFourierSource
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (i : Fin 3) (t : ℝ) : H3FourierComplexL2 :=
  h3CriticalActualProjectedFourierSource hH3 i t -
    h3CriticalFourierSharpLowCutoffCLM ρ
      (h3CriticalActualProjectedFourierSource hH3 i t)

/-- There is no disparity between the high-pass Fourier state and the
Fourier transform of the actual physical residual. -/
theorem h3Critical_actualProjectedHighpassFourier_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (i : Fin 3) (t : ℝ) :
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t =
      h3ScalarFourierL2
        ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i -
          h3CriticalPhysicalSharpLowCutoffApply ρ
            ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)) := by
  exact (h3Critical_scalarFourier_physicalHighpass_eq ρ _).symm

/-- At genuine positive time the canonical real source has the exact
raw Fourier Laplacian-minus-Leray representative. -/
theorem h3Critical_actualProjectedFourierSource_eq_rawRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (i : Fin 3) :
    h3CriticalActualProjectedFourierSource hH3 i t =
      h3SpectralScalarLaplacianRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) i) -
        h3RawFinLerayOuterProductDivergenceFourierL2
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) i := by
  let U : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  let D : H3FourierComplexL2 := h3SpectralScalarLaplacianRawFourierL2 (U i)
  let N : H3FourierComplexL2 := h3RawFinLerayOuterProductDivergenceFourierL2 U U i
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
  change h3ScalarFourierL2
      ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i) = D - N
  rw [hSource, h3ScalarFourierL2_sub]
  -- The round-trip theorem is stated for the expanded real physical decoder.
  -- Expose exactly that wrapper, without unfolding the Fourier transform.
  dsimp only [h3Path_physicalRawFourierDecoder244]
  rw [h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian D hHermD,
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian N hHermN]

/-- Exact scalar-L² norm equality for the physical and Fourier high-pass
projected source at EVERY time (no PDE assumptions beyond its definition). -/
theorem h3Critical_actualProjectedHighpassFourier_norm_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (i : Fin 3) (t : ℝ) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ =
      ‖(h3PathActualProjectedMomentumSource244 hH3 t).ofLp i -
        h3CriticalPhysicalSharpLowCutoffApply ρ
          ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)‖ := by
  rw [h3Critical_actualProjectedHighpassFourier_eq_physical,
    norm_h3ScalarFourierL2]

/-- If a scalar time path is continuous and its Fourier image is terminal
Bochner L¹, the original physical path is terminal Bochner L¹ as well.
This uses exact norm preservation and strong measurability, not an
unsupported continuity of a complex-to-real inverse on arbitrary data. -/
theorem h3Critical_intervalIntegrable_of_scalarFourier_intervalIntegrable
    (R : ℝ → H3ScalarL2)
    {c T : ℝ} (hc : c < T)
    (hCont : ContinuousOn R (Set.Ioo c T))
    (hFourier : IntervalIntegrable
      (fun t : ℝ => h3ScalarFourierL2 (R t)) volume c T) :
    IntervalIntegrable R volume c T := by
  have hFourierOn : IntegrableOn
      (fun t : ℝ => h3ScalarFourierL2 (R t)) (Set.Ioo c T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).1 hFourier
  have hFourierNorm : IntegrableOn
      (fun t : ℝ => ‖h3ScalarFourierL2 (R t)‖)
      (Set.Ioo c T) volume := hFourierOn.norm
  have hNorm : IntegrableOn (fun t : ℝ => ‖R t‖)
      (Set.Ioo c T) volume := by
    simpa only [norm_h3ScalarFourierL2] using hFourierNorm
  have hMeas : AEStronglyMeasurable R
      ((volume : Measure ℝ).restrict (Set.Ioo c T)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo
  have hInt : IntegrableOn R (Set.Ioo c T) volume :=
    Integrable.mono' hNorm hMeas (Filter.Eventually.of_forall fun t => le_refl _)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le).2 hInt

/-- Under the explicit missing-terminal-trace hypothesis, ONE fixed
coordinate has a genuine high-pass Fourier source which is non-L¹ on
EVERY terminal tail and unbounded in Fourier L² on every such tail,
for EVERY fixed finite nonnegative cutoff radius. -/
theorem h3Critical_noL2Trace_actualHighpassFourier_escape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ i : Fin 3, ∀ (ρ : ℝ), 0 ≤ ρ →
      ∀ (c : ℝ), c ∈ Set.Ioo b T →
        (¬ IntervalIntegrable
          (h3CriticalActualProjectedHighpassFourierSource hH3 ρ i)
          volume c T) ∧
        (∀ M : ℝ, ∃ t : ℝ, t ∈ Set.Ioo c T ∧
          M < ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) := by
  obtain ⟨i, hi⟩ :=
    h3Critical_noL2Trace_actualPhysicalHighpass_escape
      hH3 hClass b hb hNoTrace
  refine ⟨i, ?_⟩
  intro ρ hρ c hc
  let R : ℝ → H3ScalarL2 := fun t =>
    (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i -
      h3CriticalPhysicalSharpLowCutoffApply ρ
        ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)
  obtain ⟨hNonInt, hSpikes⟩ := hi ρ hρ c hc
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
  have hFCont : ContinuousOn
      (fun t : ℝ => (h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)
      (Set.Ioo (0 : ℝ) T) :=
    hEval.comp_continuousOn hSourceCont
  have hSub : Set.Ioo c T ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 (lt_trans hc.1 ht.1)), ht.2⟩
  have hRCont : ContinuousOn R (Set.Ioo c T) :=
    (hFCont.mono hSub).sub
      ((h3Critical_physicalSharpLowCutoff_continuous ρ).comp_continuousOn
        (hFCont.mono hSub))
  constructor
  · intro hFourierInt
    have hEq :
        (fun t : ℝ => h3ScalarFourierL2 (R t)) =
          h3CriticalActualProjectedHighpassFourierSource hH3 ρ i := by
      funext t
      exact (h3Critical_actualProjectedHighpassFourier_eq_physical
        hH3 ρ i t).symm
    have hFourierOn : IntervalIntegrable
        (fun t : ℝ => h3ScalarFourierL2 (R t)) volume c T := by
      rw [hEq]
      exact hFourierInt
    have hRInt :=
      h3Critical_intervalIntegrable_of_scalarFourier_intervalIntegrable
        R hc.2 hRCont hFourierOn
    exact hNonInt hRInt
  · intro M
    obtain ⟨t, ht, hLarge⟩ := hSpikes M
    refine ⟨t, ht, ?_⟩
    rw [h3Critical_actualProjectedHighpassFourier_norm_eq_physical]
    exact hLarge

/-- The high-frequency radial Fourier square mass of a SINGLE actual
projected-source coordinate escapes every finite threshold, for every
fixed cutoff and every strict terminal subtail, if the physical velocity
fails to have a strong terminal L² trace. -/
theorem h3Critical_noL2Trace_actualHighpassFourierMass_escape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ i : Fin 3, ∀ (ρ : ℝ), 0 ≤ ρ →
      ∀ (c : ℝ), c ∈ Set.Ioo b T → ∀ K : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo c T ∧
          K < ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume := by
  obtain ⟨i, hi⟩ :=
    h3Critical_noL2Trace_actualHighpassFourier_escape
      hH3 hClass b hb hNoTrace
  refine ⟨i, ?_⟩
  intro ρ hρ c hc K
  let A : ℝ := max K 0 + 1
  obtain ⟨t, ht, hLarge⟩ := (hi ρ hρ c hc).2 A
  refine ⟨t, ht, ?_⟩
  have hAOne : 1 ≤ A := by
    dsimp only [A]
    linarith [le_max_right K (0 : ℝ)]
  have hKA : K ≤ A := by
    dsimp only [A]
    linarith [le_max_left K (0 : ℝ)]
  let H : H3FourierComplexL2 :=
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t
  have hM : 1 < ‖H‖ := lt_of_le_of_lt hAOne hLarge
  have hPower : ‖H‖ ≤ ‖H‖ ^ 2 := by nlinarith
  have hSquare : K < ‖H‖ ^ 2 :=
    (lt_of_le_of_lt hKA hLarge).trans_le hPower
  have hMass : ‖H‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume := by
    exact h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ
      (h3CriticalActualProjectedFourierSource hH3 i t)
  simpa only [hMass] using hSquare

end
end PrimeTensor.Bridge.Euclidean
