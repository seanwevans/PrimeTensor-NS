import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessQuinticCofinalCostSplit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact
import Mathlib.Tactic

/-!
# Physical source-excess windows: exact signed H³ transport and energy competition

The source-driven windows from the existing quintic three-way theorem have
strict physical H³ dissipation floors at every time. Retaining the exact
energy equation, E' + 2D = -Transport, gives a signed drain/transport
alternative, without assuming that E' is positive. The actual dissipative
Riccati estimate E' + 2D <= K sqrt(E) E further forces a genuine H³
energy-amplitude cost whenever the signed H³ energy is not decreasing.

The last theorem attaches both signed conclusions to the EXACT existing
cofinal quintic windows and reuses their geometric/cutoff/PDE gate and
physical dissipation costs. No terminal-uniform estimate is inserted.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A genuine physical viscous floor forces a signed transport expenditure
in the EXACT H³ energy identity. This does not discard a time derivative. -/
theorem h3Critical_fullDissipationFloor_forces_signedH3Transport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (H : ℝ) (hFloor : H < velocityH3DissipationAt u t) :
    deriv (velocityH3EnergyAt u) t + 2 * H <
      -velocityH3TransportDerivativeAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  linarith only [hFloor, hBalance]

/-- The signed energy derivative and the viscous source-driven floor must
be paid together by the ALREADY PROVED physical H³ Riccati nonlinearity. -/
theorem h3Critical_fullDissipationFloor_forces_signedH3Riccati
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (H : ℝ) (hFloor : H < velocityH3DissipationAt u t) :
    deriv (velocityH3EnergyAt u) t + 2 * H <
      h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
  have hGrowth :=
    deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergy_mul_energy
      hH3 hClass ht
  linarith only [hFloor, hGrowth]

/-- At every source-driven viscous spike, either the true signed H³
energy derivative is sufficiently negative, or the Riccati nonlinearity
must itself pay at least one copy of the enhanced dissipation floor. -/
theorem h3Critical_fullDissipationFloor_signedDrainOrRiccati
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (H : ℝ) (hFloor : H < velocityH3DissipationAt u t) :
    deriv (velocityH3EnergyAt u) t ≤ -H ∨
      H < h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
  have hSigned := h3Critical_fullDissipationFloor_forces_signedH3Riccati
    hH3 hClass ht H hFloor
  by_cases hDrain : deriv (velocityH3EnergyAt u) t ≤ -H
  · exact Or.inl hDrain
  · right
    have hNotDrain : -H < deriv (velocityH3EnergyAt u) t :=
      lt_of_not_ge hDrain
    linarith only [hSigned, hNotDrain]

/-- If a strong physical viscous source spike occurs on a slice where H³
energy is nondecreasing, the current energy itself must pay a CUBIC
Riccati-scale charge. No endpoint regularity or local time ceiling needed. -/
theorem h3Critical_fullDissipationFloor_nondecreasing_forces_cubicH3Energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (H : ℝ) (hH : 0 ≤ H)
    (hFloor : H < velocityH3DissipationAt u t)
    (hSlope : 0 ≤ deriv (velocityH3EnergyAt u) t) :
    4 * H ^ 2 ≤
      h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3EnergyAt u t) ^ 3 := by
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  let E : ℝ := velocityH3EnergyAt u t
  have hSigned := h3Critical_fullDissipationFloor_forces_signedH3Riccati
    hH3 hClass ht H hFloor
  have hCompare : 2 * H ≤ K * Real.sqrt E * E := by
    dsimp only [K, E]
    linarith only [hSigned, hSlope]
  have hHpos : 0 ≤ 2 * H := mul_nonneg (by norm_num) hH
  have hSquare : (2 * H) ^ 2 ≤ (K * Real.sqrt E * E) ^ 2 :=
    pow_le_pow_left₀ hHpos hCompare 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_velocityH3EnergyAt u t)
  have hSqrt : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  calc
    4 * H ^ 2 = (2 * H) ^ 2 := by ring
    _ ≤ (K * Real.sqrt E * E) ^ 2 := hSquare
    _ = K ^ 2 * E ^ 3 := by
      calc
        (K * Real.sqrt E * E) ^ 2 = K ^ 2 * (Real.sqrt E) ^ 2 * E ^ 2 := by ring
        _ = K ^ 2 * E ^ 3 := by rw [hSqrt]; ring
    _ = h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3EnergyAt u t) ^ 3 := rfl

/-- Actual highpass Fourier-source excess, rather than an abstract D floor,
forces the signed H³ energy/transport and energy/viscosity constraints. -/
theorem h3Critical_actualSourceExcess_forces_signedH3Competition
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (M Q : ℝ)
    (hPeak :
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M + Q <
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖) :
    let H := h3CriticalSourceExcessEnhancedFloor M Q
    (deriv (velocityH3EnergyAt u) t + 2 * H <
       -velocityH3TransportDerivativeAt u t) ∧
    (deriv (velocityH3EnergyAt u) t + 2 * H <
       h3PathSqrtEnergyRiccatiCoefficient *
         Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t) ∧
    (deriv (velocityH3EnergyAt u) t ≤ -H ∨
       H < h3PathSqrtEnergyRiccatiCoefficient *
         Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t) := by
  let H : ℝ := h3CriticalSourceExcessEnhancedFloor M Q
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hHigh := h3Critical_strictSourceExcess_forces_quantitativeHighRadialSurplus
    hH3 hClass b hb ρ σ hσ i t ht M Q hPeak
  have hFull : H < velocityH3DissipationAt u t := by
    exact lt_of_lt_of_le hHigh
      (h3Critical_actualHighRadialDissipation_le_full
        hH3 hClass t htClass σ)
  exact ⟨h3Critical_fullDissipationFloor_forces_signedH3Transport
      hH3 hClass htClass H hFull,
    h3Critical_fullDissipationFloor_forces_signedH3Riccati
      hH3 hClass htClass H hFull,
    h3Critical_fullDissipationFloor_signedDrainOrRiccati
      hH3 hClass htClass H hFull⟩

/-- The EXACT cofinal quintic source-peak physical windows now carry an
unconditional signed H³ transport/energy competition. The old disjointness,
full physical dissipation costs and three-way quintic gate are unchanged.
Nondecreasing H³ slices on these windows incur a cubic physical energy cost.
No new peak/window selection and no assumed energy-slope sign are involved. -/
theorem h3Critical_noL2Trace_cofinalQuintic_signedH3EnergyCompetition
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
    ∃ A B R δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        1 ≤ R k ∧ 0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          let H := h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))
          H < velocityH3DissipationAt u s ∧
          (deriv (velocityH3EnergyAt u) s + 2 * H <
             -velocityH3TransportDerivativeAt u s) ∧
          (deriv (velocityH3EnergyAt u) s + 2 * H <
             h3PathSqrtEnergyRiccatiCoefficient *
               Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∧
          (deriv (velocityH3EnergyAt u) s ≤ -H ∨
             H < h3PathSqrtEnergyRiccatiCoefficient *
               Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∧
          (0 ≤ deriv (velocityH3EnergyAt u) s →
             4 * H ^ 2 ≤
               h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
                 (velocityH3EnergyAt u s) ^ 3)) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ, ∀ J : ℝ, 0 < J →
        (∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
            ENNReal.ofReal J →
        w (v k) ≤ J / h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k)) ∨
        (q (v k) ≤
            16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              (max 1 (σ (v k)) + 1) ^ 4 ∨
          16 * (q (v k)) ^ 5 ≤
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              ((A k) ^ 2 * (B k)) ^ 2)) := by
  obtain ⟨_i, t, w, v, A, B, R, δ, hv, hLimit,
      hWindows, hSeparated, hCosts, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefoldSource_quinticThreeWayCostGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, A, B, R, δ, hv, hLimit, ?_, hSeparated, hCosts, hGate⟩
  intro k
  obtain ⟨hStart, hw, hEnd, hR, hδ, hδw, hWidth, hFloor⟩ := hWindows k
  refine ⟨hStart, hw, hEnd, hR, hδ, hδw, hWidth, ?_⟩
  intro s hs
  let H : ℝ := h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))
  have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
    add_le_add_right hδw (t (v k))
  have hsClass : s ∈ Set.Ioo a T := by
    have hStartA : a < t (v k) :=
      lt_trans hb.1 (lt_trans (hc (v k)).1 hStart.1)
    exact ⟨lt_of_lt_of_le hStartA hs.1,
      lt_of_le_of_lt (le_trans hs.2 hShort) hEnd⟩
  have hFull : H < velocityH3DissipationAt u s := hFloor s hs
  have hSigned := h3Critical_fullDissipationFloor_forces_signedH3Transport
    hH3 hClass hsClass H hFull
  have hRiccati := h3Critical_fullDissipationFloor_forces_signedH3Riccati
    hH3 hClass hsClass H hFull
  have hAlternative := h3Critical_fullDissipationFloor_signedDrainOrRiccati
    hH3 hClass hsClass H hFull
  have hHnonneg : 0 ≤ H := by
    dsimp only [H, h3CriticalSourceExcessEnhancedFloor]
    have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
      have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
      positivity
    exact add_nonneg (hM (v k))
      (div_nonneg (hq (v k)).le hκ.le)
  refine ⟨hFull, hSigned, hRiccati, hAlternative, ?_⟩
  intro hSlope
  exact h3Critical_fullDissipationFloor_nondecreasing_forces_cubicH3Energy
    hH3 hClass hsClass H hHnonneg hFull hSlope

end
end PrimeTensor.Bridge.Euclidean
