import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSpectralExcursionEndpointViscousGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusIntegratedWindows244
import Mathlib.Tactic

/-!
# Attained endpoint H³ viscous spikes have genuine finite-band integrated costs

Full H³ dissipation need not be continuous in time merely because the
weighted H³ spectral state is. Nevertheless, at each strict physical time,
the high-radial dissipation tail tends to zero as its cutoff tends to infinity.
A strict full-H³ dissipation spike therefore has a finite Fourier cutoff whose
low-radial dissipation already exceeds any prescribed lower height. This
bounded-frequency physical quantity is continuous in time and thus persists
on a positive right-hand interval. Its floor is charged to the actual full
physical H³ dissipation integral using the existing partition.

Applying this to the cofinal fivefold spectral-source witnesses converts the
attained-maximizer endpoint-spike branch into a genuinely integrated positive
physical cost. New right-hand windows need not belong to the original short
quartic windows and are not asserted to be pairwise disjoint. No continuity
hypothesis on full H³ dissipation or terminal-uniform rate is introduced.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- At a single strict time, any height below the ACTUAL full H³ viscous
dissipation is exceeded already by a finite radial low-dissipation cutoff.
This is the essential compact-frequency capture lemma. -/
theorem h3Critical_fullViscousSpike_has_finiteRadialCapture
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s H : ℝ) (hs : s ∈ Set.Ioo a T)
    (hSpike : H < velocityH3DissipationAt u s) :
    ∃ N : ℕ, H < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s) := by
  have hGap : 0 < velocityH3DissipationAt u s - H :=
    sub_pos.mpr hSpike
  have hTail := h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    hH3 hClass s hs
  have hEventually : ∀ᶠ n : ℕ in atTop,
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) <
          velocityH3DissipationAt u s - H :=
    hTail.eventually (eventually_lt_nhds hGap)
  rw [Filter.eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  have hSmall := hN N le_rfl
  have hPartition := h3Path_actualRadialDissipation_partition244
    hH3 hClass s hs ((N : ℝ) + 1)
  refine ⟨N, ?_⟩
  linarith only [hSmall, hPartition]

/-- A strict full-H³ viscous spike persists through a finite-band physical
quantity on a genuine positive interval, producing a lower bound for the
actual EXTENDED full-H³ dissipation cost. No time continuity of the
unbounded full dissipation operator is used. -/
theorem h3Critical_fullViscousSpike_has_finiteBandIntegratedRightWindow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s H : ℝ) (hs : s ∈ Set.Ioo a T)
    (hSpike : H < velocityH3DissipationAt u s) :
    ∃ (N : ℕ) (η : ℝ), 0 < η ∧ s + η < T ∧
      (∀ r : ℝ, r ∈ Set.Icc s (s + η) →
        H < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        H < velocityH3DissipationAt u r) ∧
      ENNReal.ofReal H * ENNReal.ofReal η ≤
        ∫⁻ r in Set.Ioc s (s + η),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
  obtain ⟨N, hCapture⟩ :=
    h3Critical_fullViscousSpike_has_finiteRadialCapture
      hH3 hClass s H hs hSpike
  let B : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r)
  have hBCont : ContinuousOn B (Set.Ioo a T) := by
    dsimp only [B]
    exact h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
      hH3 hClass ((N : ℝ) + 1) (by positivity)
  have hAt : H < B s := hCapture
  have hContinuous : ContinuousAt (fun r : ℝ => H - B r) s :=
    continuousAt_const.sub (hBCont.continuousAt (isOpen_Ioo.mem_nhds hs))
  have hNegative : H - B s < 0 := by linarith only [hAt]
  obtain ⟨η₀, hη₀, hNear⟩ :=
    h3Path_continuousStrictInequality_localWindow244
      hContinuous hNegative
  let η : ℝ := min (η₀ / 2) ((T - s) / 2)
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (by linarith only [hη₀]) (by linarith only [hs.2])
  have hηNear : η ≤ η₀ / 2 := min_le_left _ _
  have hηEnd : η ≤ (T - s) / 2 := min_le_right _ _
  have hEnd : s + η < T := by linarith only [hηEnd, hs.2]
  have hInside : Set.Icc s (s + η) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
  have hLowFloor (r : ℝ) (hr : r ∈ Set.Icc s (s + η)) : H < B r := by
    have hDist : dist r s < η₀ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
      linarith only [hr.2, hηNear, hη₀]
    have hNear' := hNear r hDist
    linarith only [hNear']
  have hFloor (r : ℝ) (hr : r ∈ Set.Icc s (s + η)) :
      H < B r ∧ H < velocityH3DissipationAt u r := by
    have hLow := hLowFloor r hr
    have hPartition := h3Path_actualRadialDissipation_partition244
      hH3 hClass r (hInside hr) ((N : ℝ) + 1)
    have hHigh : 0 ≤ h3PathActualHighRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) := by
      unfold h3PathActualHighRadialDissipation244
      apply integral_nonneg
      intro ξ
      exact h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3AuditActualSpectralVelocityTotal hH3 r) ξ
    dsimp only [B] at hLow ⊢
    exact ⟨hLow, by linarith only [hLow, hPartition, hHigh]⟩
  refine ⟨N, η, hη, hEnd, hFloor, ?_⟩
  have hIntegral :
      (∫⁻ _r in Set.Ioc s (s + η), ENNReal.ofReal H ∂volume) ≤
        ∫⁻ r in Set.Ioc s (s + η),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
    apply h3Critical_extendedWindowCost_of_pointwiseFloor
    intro r hr
    exact (hFloor r hr).2.le
  calc
    ENNReal.ofReal H * ENNReal.ofReal η =
        (∫⁻ _r in Set.Ioc s (s + η), ENNReal.ofReal H ∂volume) :=
      (h3Critical_extendedConstantWindow_eq_heightWidth s η H hη.le).symm
    _ ≤ ∫⁻ r in Set.Ioc s (s + η),
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := hIntegral

/-- A strictly positive Fourier cutoff converts an endpoint viscous spike
into a strictly positive source-threshold floor and hence a certified
finite-band integrated physical cost at the endpoint maximum. -/
theorem h3Critical_endpointViscousSpike_atMax_has_integratedCost
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s R ε : ℝ) (hs : s ∈ Set.Ioo a T)
    (hR : 0 < R) (hε : 0 < ε)
    (hSpike : R ^ 2 * ε ^ 2 < 8 * velocityH3DissipationAt u s) :
    ∃ (N : ℕ) (η : ℝ), 0 < R ^ 2 * ε ^ 2 / 8 ∧
      0 < η ∧ s + η < T ∧
      (∀ r : ℝ, r ∈ Set.Icc s (s + η) →
        R ^ 2 * ε ^ 2 / 8 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        R ^ 2 * ε ^ 2 / 8 < velocityH3DissipationAt u r) ∧
      ENNReal.ofReal (R ^ 2 * ε ^ 2 / 8) * ENNReal.ofReal η ≤
        ∫⁻ r in Set.Ioc s (s + η),
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
  have hHeight : R ^ 2 * ε ^ 2 / 8 < velocityH3DissipationAt u s := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    nlinarith only [hSpike]
  obtain ⟨N, η, hη, hEnd, hFloor, hCost⟩ :=
    h3Critical_fullViscousSpike_has_finiteBandIntegratedRightWindow
      hH3 hClass s (R ^ 2 * ε ^ 2 / 8) hs hHeight
  have hHeightPos : 0 < R ^ 2 * ε ^ 2 / 8 := by positivity
  exact ⟨N, η, hHeightPos, hη, hEnd, hFloor, hCost⟩

/-- The SAME accepted fivefold source witnesses and full integrated
calibrated costs now also carry a second, independent physical integrated
cost whenever the attained spectral maximum must pay the viscous branch.
For each selected index and threshold, Riccati/compression/cutoff/source
alternatives, the finite-band PDE clock, and the anchor spike remain explicit.
The new right-hand interval starts at the attained spectral maximum and is
not asserted disjoint from the original calibrated intervals or from other
newly selected intervals. -/
theorem h3Critical_noL2Trace_cofinalFivefold_endpointMaxIntegratedCostGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n) :
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState A B δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        sSource k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        A k = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        B k = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 +
          2 * (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s)) ∧
      (∀ k : ℕ, ∀ R ε : ℝ, 0 < R → 0 < ε →
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R ^ 2 * ε ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (∃ (N : ℕ) (η : ℝ), 0 < R ^ 2 * ε ^ 2 / 8 ∧
          0 < η ∧ sState k + η < T ∧
          (∀ r : ℝ, r ∈ Set.Icc (sState k) (sState k + η) →
            R ^ 2 * ε ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R ^ 2 * ε ^ 2 / 8 < velocityH3DissipationAt u r) ∧
          ENNReal.ofReal (R ^ 2 * ε ^ 2 / 8) * ENNReal.ofReal η ≤
            ∫⁻ r in Set.Ioc (sState k) (sState k + η),
              ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume)) := by
  obtain ⟨t, w, v, sSource, sState, A, B, δ,
      hv, hLimit, hSep, hCosts, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_spectralExcursionEndpointViscousGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, sSource, sState, A, B, δ,
    hv, hLimit, hSep, hCosts, hWindows, ?_⟩
  intro k R ε hR hε hThreshold
  rcases hGate k R ε hR hε hThreshold with hOld | hClock | hAtPeak | hAtMax
  · exact Or.inl hOld
  · exact Or.inr (Or.inl hClock)
  · exact Or.inr (Or.inr (Or.inl hAtPeak))
  · obtain ⟨ht, _hw, hEnd, _hsSource, hsState, _hMax,
        _hA, _hB, _hδ, _hδw, _hWidth, _hFloor⟩ := hWindows k
    have htClass : t (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1), ht.2⟩
    have hsClass : sState k ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le htClass.1 hsState.1,
        lt_of_le_of_lt hsState.2 hEnd⟩
    exact Or.inr (Or.inr (Or.inr
      (h3Critical_endpointViscousSpike_atMax_has_integratedCost
        hH3 hClass (sState k) R ε hsClass hR hε hAtMax)))

end
end PrimeTensor.Bridge.Euclidean
