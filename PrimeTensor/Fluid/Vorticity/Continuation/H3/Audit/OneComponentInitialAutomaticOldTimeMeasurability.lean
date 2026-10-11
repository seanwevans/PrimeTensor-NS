import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightEnergyCeilingReduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentGlobalTimeMeasurability

/-!
# Automatic positive-time measurability of the actual old physical L² path

The initial right-energy/relative-energy comparison previously required
`AEStronglyMeasurable` of the old physical velocity as an extra hypothesis.
The existing path class already yields *stronger* information at every
strictly positive time. On a local H³ restart window the actual old spectral
velocity is continuous by the pressure-free weak-plus-norm theorem, and the
real physical L² decoder is a continuous Hilbert-valued map.

This module glues those local statements on `(0,T)`, giving continuous
physical L² velocity there and hence time measurability on every initial
`(0,b)`. It does not presume continuity or integrability at zero, an initial
H³ energy bound, or any vanishing-residual Navier–Stokes comparison.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The genuine positive-time physical `L²` Hilbert velocity is the decoded
actual three-component weighted H³ spectral state. -/
theorem h3Audit_initialOldPhysicalHilbertTotal_eq_actualSpectralDecode
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 s =
      (WithLp.toLp (2 : ℝ≥0∞)
        (fun j : Fin 3 =>
          h3FromFourierRealL2
            (h3SpectralScalarDecodeRealL2
              ((h3AuditActualSpectralVelocityTotal hH3 s) j))) :
        H3PhysicalRealFinVectorL2Hilbert) := by
  apply PiLp.ext
  intro j
  simpa only [h3AuditInitialOldPhysicalHilbertTotal,
    PiLp.toLp_apply] using
    (h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode
      hH3 s hs j).symm

/-- The original actual state agrees with the local canonical state, on a
strict-time elapsed window. Fourier and integrability witnesses are proofs,
not additional data stored by the spectral encoder. -/
theorem h3Audit_actualSpectralVelocityTotal_eq_canonicalElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) τ) :
    h3AuditActualSpectralVelocityTotal hH3 (t + (q : ℝ)) =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hShort.navier_stokes ht hEnd hTail q := by
  have hs := h3PreterminalElapsedTime_mem_Ioo ht hEnd q
  have hsT : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_of_lt_of_le hs.2 hST⟩
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 _ hsT]
  rfl

/-- The actual OLD physical Hilbert velocity (not only an auxiliary selected
path) is strongly continuous on every local strict elapsed-time window. -/
theorem h3Audit_initialOldPhysicalHilbert_continuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E) :
    Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      h3AuditInitialOldPhysicalHilbertTotal hH3 (t + (q : ℝ))) := by
  have hSpectral : Continuous
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hShort.navier_stokes ht hEnd hTail) :=
    h3Audit_preterminalSpectral_continuousOnElapsed_of_h3Path
      hShort ht hτ hEnd hE hTail
  have hDecoded : Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      (WithLp.toLp (2 : ℝ≥0∞)
        (fun j : Fin 3 =>
          h3FromFourierRealL2
            (h3SpectralScalarDecodeRealL2
              ((h3PreterminalTailCanonicalSpectralStateOnElapsed
                hShort.navier_stokes ht hEnd hTail q) j))) :
        H3PhysicalRealFinVectorL2Hilbert)) :=
    continuous_h3SelectedPhysicalL2HilbertDecode.comp hSpectral
  have hEq :
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3AuditInitialOldPhysicalHilbertTotal hH3 (t + (q : ℝ))) =
      (fun q : Set.Icc (0 : ℝ) τ =>
        (WithLp.toLp (2 : ℝ≥0∞)
          (fun j : Fin 3 =>
            h3FromFourierRealL2
              (h3SpectralScalarDecodeRealL2
                ((h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hShort.navier_stokes ht hEnd hTail q) j))) :
          H3PhysicalRealFinVectorL2Hilbert)) := by
    funext q
    have hs := h3PreterminalElapsedTime_mem_Ioo ht hEnd q
    have hsT : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hs.1, lt_of_lt_of_le hs.2 hST⟩
    rw [h3Audit_initialOldPhysicalHilbertTotal_eq_actualSpectralDecode
      hH3 (t + (q : ℝ)) hsT]
    rw [h3Audit_actualSpectralVelocityTotal_eq_canonicalElapsed
      hH3 hShort hST ht hEnd hTail q]
  rw [hEq]
  exact hDecoded

/-- Transfer local elapsed-parameter continuity back to ambient real time
at an interior physical time. -/
private theorem h3Audit_initialHilbert_continuousAt_of_elapsedWindow
    (f : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    {t τ s : ℝ}
    (hts : t < s)
    (hsEnd : s < t + τ)
    (hf : Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      f (t + (q : ℝ)))) :
    ContinuousAt f s := by
  have hMaps : ∀ x : Set.Icc t (t + τ),
      (x : ℝ) - t ∈ Set.Icc (0 : ℝ) τ := by
    intro x
    rcases x.property with ⟨hl, hu⟩
    change 0 ≤ (x : ℝ) - t ∧ (x : ℝ) - t ≤ τ
    constructor <;> linarith
  have hCoordinate : Continuous (fun x : Set.Icc t (t + τ) =>
      (⟨(x : ℝ) - t, hMaps x⟩ : Set.Icc (0 : ℝ) τ)) :=
    (continuous_subtype_val.sub continuous_const).subtype_mk hMaps
  have hTransfer : Continuous (fun x : Set.Icc t (t + τ) =>
      f (t + ((x : ℝ) - t))) := hf.comp hCoordinate
  have hOn : ContinuousOn f (Set.Icc t (t + τ)) := by
    apply (continuousOn_iff_continuous_domRestrict).2
    have hEq :
        (fun x : Set.Icc t (t + τ) => f (t + ((x : ℝ) - t))) =
        (Set.Icc t (t + τ)).domRestrict f := by
      funext x
      simp only [Set.domRestrict_apply]
      congr 1
      ring
    rw [← hEq]
    exact hTransfer
  have hNear : Set.Icc t (t + τ) ∈ 𝓝 s := by
    refine Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo t (t + τ)
        from ⟨hts, hsEnd⟩)) ?_
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  exact hOn.continuousAt hNear

/-- No right endpoint trace is needed for continuity of the actual old
physical `L²` Hilbert state at any strict positive preterminal time. -/
theorem h3Audit_initialOldPhysicalHilbert_continuousAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt (h3AuditInitialOldPhysicalHilbertTotal hH3) s := by
  obtain ⟨t, S, E, ht, hST, hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := (s + S) / 2 - t
  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith only [hElapsed, hsS]
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hsWithin : s < t + τ := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos
      (le_of_lt hST)
  exact h3Audit_initialHilbert_continuousAt_of_elapsedWindow
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (sub_pos.mp hElapsed) hsWithin
    (h3Audit_initialOldPhysicalHilbert_continuousOnElapsed
      hH3 hShort (le_of_lt hST) ht hτ hEnd hE hTail)

/-- Local windows cover the entire open preterminal interval. -/
theorem h3Audit_initialOldPhysicalHilbert_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
  apply continuousOn_of_forall_continuousAt
  intro s hs
  exact h3Audit_initialOldPhysicalHilbert_continuousAt hH3 hs

/-- The OLD physical velocity is automatically strongly measurable on every
strict initial time interval inside `(0,T)`. -/
theorem h3Audit_initialOldPhysicalHilbert_aestronglyMeasurableOnInitial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hbT : b ≤ T) :
    AEStronglyMeasurable
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) := by
  have hSub : Set.Ioo (0 : ℝ) b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_lt_of_le hs.2 hbT⟩
  have hCont : ContinuousOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (Set.Ioo (0 : ℝ) b) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hSub
  exact hCont.aestronglyMeasurable measurableSet_Ioo

/-- The right-energy-trace comparison no longer needs an independent
measurability assertion about the actual old physical Hilbert path. -/
def H3AuditInitialCanonicalRightEnergyTraceNoMeasurabilityData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b₀ : ℝ),
    0 < b₀ ∧ b₀ < T ∧
    b₀ ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (L K : ℝ),
      Tendsto (velocityH3EnergyAt u) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b₀) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b₀ → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b₀ ∧
          (∫ s in (0 : ℝ)..b₀, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b₀ →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Supply the formerly assumed old-velocity measurability directly from
strict-time H³ path admissibility, without using initial uniqueness. -/
theorem h3Audit_initialRightEnergyTraceNoMeasurability_implies_data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightEnergyTraceNoMeasurabilityData hH3) :
    H3AuditInitialCanonicalRightEnergyTraceRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b₀, hb₀, hb₀T, hb₀R, L, K, hRight, hEpsilon⟩ := hData
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b₀, hb₀, hb₀T, hb₀R, L, K, hRight,
    h3Audit_initialOldPhysicalHilbert_aestronglyMeasurableOnInitial
      hH3 b₀ hb₀T.le, hEpsilon⟩

/-- Actual compact weak-test uniqueness under right energy trace and
vanishing PDE comparison residuals, with NO old time-measurability premise. -/
theorem h3Audit_initialRightEnergyTraceNoMeasurability_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightEnergyTraceNoMeasurabilityData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialRightEnergyTrace_implies_compactWeakComparisonData
    hH3 (h3Audit_initialRightEnergyTraceNoMeasurability_implies_data hH3 hData)

/-- The physical initial `L²`/upper `H³` trace also needs no separate
measurability hypothesis on the positive-time old Hilbert velocity. -/
theorem h3Audit_initialRightEnergyTraceNoMeasurability_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightEnergyTraceNoMeasurabilityData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialRightEnergyTrace_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialRightEnergyTraceNoMeasurability_implies_data hH3 hData)

/-- The conditional terminal one-component estimate remains independent. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightEnergyTraceNoMeasurability
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalRightEnergyTraceNoMeasurabilityData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightEnergyTrace
    hH3 hClass i hPhysical
    (h3Audit_initialRightEnergyTraceNoMeasurability_implies_data hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
