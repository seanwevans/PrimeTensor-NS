import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSpectralExcursionPDEClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropEndpointDissipationTransport
import Mathlib.Tactic

/-!
# Actual endpoint H³ dissipation price for cofinal spectral excursions

The accepted fivefold source clock forces either finite-band physical PDE
motion or a high-radial Fourier square displacement between the source peak
and the attained spectral maximum. The already proved two-endpoint coercivity
converts that displacement into a *genuine full physical H³ dissipation*
demand at one of the two endpoints, at every strictly positive cutoff.

The maximizing time is on the original source window, not necessarily inside
the shorter dissipation-charging window. This theorem does not compare
instantaneous dissipation with its time integral or assume a terminal-uniform
rate for the full weighted spectral state.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A positive Fourier radius turns high temporal mass into an exact
strict two-endpoint dissipation demand. The strictness genuinely requires
R>0; at radius zero multiplication would lose the strict inequality. -/
theorem h3Critical_scalar_highTemporalMass_to_endpointDissipation
    (R ε X Dt Ds : ℝ) (hR : 0 < R)
    (hMass : ε ^ 2 < 2 * X)
    (hEndpoint : R ^ 2 * X ≤ 2 * (Dt + Ds)) :
    R ^ 2 * ε ^ 2 < 4 * (Dt + Ds) := by
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  calc
    R ^ 2 * ε ^ 2 < R ^ 2 * (2 * X) :=
      mul_lt_mul_of_pos_left hMass hR2
    _ = 2 * (R ^ 2 * X) := by ring
    _ ≤ 2 * (2 * (Dt + Ds)) :=
      mul_le_mul_of_nonneg_left hEndpoint (by norm_num)
    _ = 4 * (Dt + Ds) := by ring

/-- A strict two-endpoint sum cannot be paid by two individually
subthreshold endpoint values. No positivity of the endpoint values is
needed to perform this exact algebraic allocation. -/
theorem h3Critical_scalar_endpointDissipation_forces_oneSpike
    (Q Dt Ds : ℝ)
    (hSum : Q < 4 * (Dt + Ds)) :
    Q < 8 * Dt ∨ Q < 8 * Ds := by
  by_cases hFirst : Q < 8 * Dt
  · exact Or.inl hFirst
  · right
    have hSmall : 8 * Dt ≤ Q := le_of_not_gt hFirst
    linarith only [hSum, hSmall]

/-- Actual high-frequency temporal Fourier motion is paid by actual full
physical H³ dissipation at BOTH strict-time observations. The peak and
maximizing observation can be arbitrarily close to terminal time, but
both must belong to the physical energy class. -/
theorem h3Critical_highTemporalMass_forces_fullEndpointDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s R ε : ℝ)
    (ht : t ∈ Set.Ioo a T) (hs : s ∈ Set.Ioo a T)
    (hR : 0 < R)
    (hMass : ε ^ 2 < 2 * h3Path_spectralTemporalHighRadialIntegral244 R
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 s)) :
    R ^ 2 * ε ^ 2 <
      4 * (velocityH3DissipationAt u t + velocityH3DissipationAt u s) := by
  have hRadial := h3Critical_highTemporalMass_radiusSq_le_endpointDissipation
    hH3 hClass t s ht hs R hR.le
  have htFull := h3Critical_actualHighRadialDissipation_le_full
    hH3 hClass t ht R
  have hsFull := h3Critical_actualHighRadialDissipation_le_full
    hH3 hClass s hs R
  have hSum := add_le_add htFull hsFull
  have hFull : R ^ 2 * h3Path_spectralTemporalHighRadialIntegral244 R
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤
      2 * (velocityH3DissipationAt u t + velocityH3DissipationAt u s) := by
    exact hRadial.trans
      (mul_le_mul_of_nonneg_left hSum (by norm_num))
  exact h3Critical_scalar_highTemporalMass_to_endpointDissipation
    R ε _ (velocityH3DissipationAt u t) (velocityH3DissipationAt u s)
    hR hMass hFull

/-- Pointwise physical H³ endpoint concentration produced by actual high
spectral-temporal motion, without a fictitious global H³ time derivative. -/
theorem h3Critical_highTemporalMass_forces_onePhysicalDissipationSpike
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s R ε : ℝ)
    (ht : t ∈ Set.Ioo a T) (hs : s ∈ Set.Ioo a T)
    (hR : 0 < R)
    (hMass : ε ^ 2 < 2 * h3Path_spectralTemporalHighRadialIntegral244 R
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 s)) :
    R ^ 2 * ε ^ 2 < 8 * velocityH3DissipationAt u t ∨
    R ^ 2 * ε ^ 2 < 8 * velocityH3DissipationAt u s := by
  exact h3Critical_scalar_endpointDissipation_forces_oneSpike
    (R ^ 2 * ε ^ 2)
    (velocityH3DissipationAt u t) (velocityH3DissipationAt u s)
    (h3Critical_highTemporalMass_forces_fullEndpointDissipation
      hH3 hClass t s R ε ht hs hR hMass)

/-- Preserve exactly the accepted cofinal windows, attained maxima,
calibrated widths and disjoint full-H³ integral charges. For every positive
Fourier cutoff R and attempted spectral threshold ε, an unexcluded spectral
excursion is paid either by the finite-band physical PDE clock, by the
actual viscous dissipation at the source anchor, or by actual viscous
dissipation at its attained spectral maximizing time. -/
theorem h3Critical_noL2Trace_cofinalFivefold_spectralExcursionEndpointViscousGate
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
        R ^ 2 * ε ^ 2 < 8 * velocityH3DissipationAt u (sState k)) := by
  obtain ⟨t, w, v, sSource, sState, A, B, δ,
      hv, hLimit, hSep, hCosts, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_spectralExcursionPDEClockGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, sSource, sState, A, B, δ,
    hv, hLimit, hSep, hCosts, hWindows, ?_⟩
  intro k R ε hR hε hThreshold
  rcases hGate k R ε hR.le hε hThreshold with hOld | hClock | hMass
  · exact Or.inl hOld
  · exact Or.inr (Or.inl hClock)
  · obtain ⟨ht, _hw, hEnd, _hsSource, hsState, _hMax,
        _hA, _hB, _hδ, _hδw, _hWidth, _hFloor⟩ := hWindows k
    have htClass : t (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1), ht.2⟩
    have hsClass : sState k ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le htClass.1 hsState.1,
        lt_of_le_of_lt hsState.2 hEnd⟩
    rcases h3Critical_highTemporalMass_forces_onePhysicalDissipationSpike
      hH3 hClass (t (v k)) (sState k) R ε htClass hsClass hR hMass with
      hAtPeak | hAtMax
    · exact Or.inr (Or.inr (Or.inl hAtPeak))
    · exact Or.inr (Or.inr (Or.inr hAtMax))

end
end PrimeTensor.Bridge.Euclidean
