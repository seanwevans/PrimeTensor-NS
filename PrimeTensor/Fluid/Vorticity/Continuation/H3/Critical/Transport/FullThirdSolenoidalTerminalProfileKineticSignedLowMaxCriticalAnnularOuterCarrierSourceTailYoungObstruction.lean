import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierForcedTemporalExcursion
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeDelayedViscousTail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUnconditionalHilbertFTCKinetic244
import Mathlib.Tactic

/-!
# The selected outer carrier must pay actual physical source action or lose its nonlinear Young deficit

The preceding cofinal theorem forces a real physical L² velocity excursion or
an exact annular Young-width deficit loss before the midpoint of the terminal
interval. A velocity excursion cannot be left as an abstract alternative:
the unconditional physical Navier--Stokes Hilbert FTC charges it to the exact
projected source L¹ action, and the physical kinetic anchor plus H³ dissipation
bound that source action on the terminal tail.

For a selected snapshot x, set
    S(x) = ∫_x^T ‖projected momentum source‖,
    V(x) = ∫_x^T D_H3,
    H(x) = (3 + C_L) * ((1 + 6 E0(b)) * (T-x) + 3 V(x)).
The actual physical PDE gives S(x) ≤ H(x). If a selected highpass excursion
occurs before T, then
    margin < (rho² + sigma²) * S(x) * (2‖U(x)‖ + S(x)).
Consequently a cofinal selected carrier with noncollapsing sixth-power
terminal scale must pay that true physical source budget, or exhibit a
strictly positive fall in the *exact nonlinear annular deficit* on the
right half-tail. The source action itself tends to zero cofinally.

No claim is made that frequency-weighted source cost must vanish, or that the
remaining nonlinear-deficit branch is impossible. Neither H³ continuation
nor a contradiction with finite dissipation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The actual physical momentum FTC, together with integrability of the
projected source, controls every interior physical L² velocity increment
by the full terminal source L¹ action. -/
theorem thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ≤
      ∫ r in x..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hx0 : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
  have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hx0.1 hxs, hsT⟩
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hGTail : IntervalIntegrable G volume x T := by
    apply hG.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc x T := by
      simpa only [Set.uIcc_of_le hx.2.le] using hr
    have hr'' : r ∈ Set.Icc b T :=
      ⟨hx.1.le.trans hr'.1, hr'.2⟩
    simpa only [Set.uIcc_of_le hb.2.le] using hr''
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244
    hH3 x s hx0 hs0
  have hNorm :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
          h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ≤
        ∫ r in x..s, ‖G r‖ := by
    rw [hFTC]
    exact intervalIntegral.norm_integral_le_integral_norm hxs
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x T)] (fun r => ‖G r‖) := by
    filter_upwards [] with r
    exact norm_nonneg (G r)
  have hTail : (∫ r in x..s, ‖G r‖) ≤ ∫ r in x..T, ‖G r‖ :=
    intervalIntegral.integral_mono_interval
      (le_refl x) hxs hsT.le hNonneg hGTail.norm
  exact hNorm.trans hTail

/-- The kinetic-mass excursion is charged to a QUADRATIC physical source
budget, with the actual physical velocity at the selected snapshot as the
sole state-size coefficient. No cutoff-dependent temporal derivative enters. -/
theorem thirdFullPhysical_outerMassExcursion_forcesSourceTailCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma margin : ℝ) (hRho : 0 < rho)
    (hAspect : 2 * rho ≤ sigma)
    (hDrop : margin < (rho ^ 2 + sigma ^ 2) *
      (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
          h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ *
       (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ +
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖))) :
    let S : ℝ := ∫ r in x..T,
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖
    margin < (rho ^ 2 + sigma ^ 2) *
      (S * (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ + S)) := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let S : ℝ := ∫ r in x..T,
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖
  have hIncrement : ‖U s - U x‖ ≤ S :=
    thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
      hH3 hClass hDInt b hb x hx s hxs hsT
  have hTriangle : ‖U s‖ ≤ ‖U s - U x‖ + ‖U x‖ := by
    calc
      ‖U s‖ = ‖(U s - U x) + U x‖ := by rw [sub_add_cancel]
      _ ≤ ‖U s - U x‖ + ‖U x‖ := norm_add_le _ _
  have hSum : ‖U s‖ + ‖U x‖ ≤ 2 * ‖U x‖ + S := by
    linarith only [hTriangle, hIncrement]
  have hProduct :
      ‖U s - U x‖ * (‖U s‖ + ‖U x‖) ≤
        S * (2 * ‖U x‖ + S) := by
    calc
      _ ≤ S * (‖U s‖ + ‖U x‖) :=
        mul_le_mul_of_nonneg_right hIncrement (by positivity)
      _ ≤ S * (2 * ‖U x‖ + S) :=
        mul_le_mul_of_nonneg_left hSum
          (le_trans (norm_nonneg (U s - U x)) hIncrement)
  have hCoeff : 0 ≤ rho ^ 2 + sigma ^ 2 := by positivity
  change margin < (rho ^ 2 + sigma ^ 2) *
    (S * (2 * ‖U x‖ + S))
  exact lt_of_lt_of_le hDrop (mul_le_mul_of_nonneg_left hProduct hCoeff)

/-- A scalar bridge: enlarging the genuine nonnegative source tail to its
physical kinetic-plus-viscous bound enlarges the source excursion price. -/
theorem thirdFullKinetic_sourceTail_quadraticMonotonicity244
    (margin B N S H : ℝ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hS : 0 ≤ S) (hSH : S ≤ H)
    (hMargin : margin < B * (S * (2 * N + S))) :
    margin < B * (H * (2 * N + H)) := by
  have hWidth : 2 * N + S ≤ 2 * N + H := by linarith only [hSH]
  have hProduct : S * (2 * N + S) ≤ H * (2 * N + H) := by
    calc
      _ ≤ H * (2 * N + S) :=
        mul_le_mul_of_nonneg_right hSH (by positivity)
      _ ≤ H * (2 * N + H) :=
        mul_le_mul_of_nonneg_left hWidth (hS.trans hSH)
  exact lt_of_lt_of_le hMargin
    (mul_le_mul_of_nonneg_left hProduct hB)

/-- The ORIGINAL projected physical momentum source has a fully explicit
terminal-tail L¹ ceiling, involving only the fixed kinetic anchor, elapsed
time and the TRUE physical H³ dissipation. -/
theorem thirdFullPhysical_outerSourceTail_le_kineticViscousBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T) :
    (∫ r in x..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖) ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        ((1 + 6 * velocityH3Energy0At u b) * (T - x) +
          3 * (∫ r in x..T, velocityH3DissipationAt u r)) := by
  have hG : IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
      volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  exact thirdFullPhysical_delayedSource_le_kineticClock_add_viscosity244
    hH3 hClass hDInt b hb hG x hx

/-- Low terminal physical viscosity now forces either a quantitative action
of the ACTUAL projected momentum source, or loss of the original nonlinear
Young-width annular deficit before the middle of the remaining time. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_forcesSourceOrDeficit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hSmall :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        119 * margin * sigma ^ 6 * (T - x) / 320) :
    let S : ℝ := ∫ r in x..T,
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖
    (margin < (rho ^ 2 + sigma ^ 2) *
      (S * (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ + S))) ∨
    (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma >
          epsilon) := by
  obtain ⟨s, hs, hAlternative⟩ :=
    thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesVelocityOrDeficit244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  have hMid : (x + T) / 2 < T := by linarith only [hx.2]
  have hsT : s < T := lt_of_le_of_lt hs.2 hMid
  dsimp only
  rcases hAlternative with hMotion | hDeficit
  · left
    exact thirdFullPhysical_outerMassExcursion_forcesSourceTailCost244
      hH3 hClass hDInt b hb x hx s hs.1.le hsT
      rho sigma margin hRho hAspect hMotion
  · exact Or.inr ⟨s, hs, hDeficit⟩

/-- The principal PDE gate: replace the abstract physical L² motion arm by
an explicit kinetic elapsed-time plus physical H³ viscous terminal budget. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hSmall :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        119 * margin * sigma ^ 6 * (T - x) / 320) :
    let H : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
      ((1 + 6 * velocityH3Energy0At u b) * (T - x) +
        3 * (∫ r in x..T, velocityH3DissipationAt u r))
    (margin < (rho ^ 2 + sigma ^ 2) *
      (H * (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ + H))) ∨
    (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma >
          epsilon) := by
  let S : ℝ := ∫ r in x..T,
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖
  let H : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
    ((1 + 6 * velocityH3Energy0At u b) * (T - x) +
      3 * (∫ r in x..T, velocityH3DissipationAt u r))
  have hSH : S ≤ H :=
    thirdFullPhysical_outerSourceTail_le_kineticViscousBudget244
      hH3 hClass hDInt b hb x hx
  have hS : 0 ≤ S := by
    have hZero := thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
      hH3 hClass hDInt b hb x hx x (le_refl x) hx.2
    simpa only [sub_self, norm_zero] using hZero
  have hB : 0 ≤ rho ^ 2 + sigma ^ 2 := by positivity
  obtain hMass | hYoung :=
    thirdFullPhysical_selectedOuter_lowHalfTail_forcesSourceOrDeficit244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  · exact Or.inl (thirdFullKinetic_sourceTail_quadraticMonotonicity244
      margin (rho ^ 2 + sigma ^ 2)
      (‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖) S H
      hB (norm_nonneg _) hS hSH hMass)
  · exact Or.inr hYoung

/-- The genuine projected-source action itself vanishes along ANY cofinal
sequence inside the strict physical time interval, without a temporal rate
assumption or a moving cutoff. -/
theorem thirdFullPhysical_cofinalOuterSourceTail_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T)) :
    Tendsto (fun k : ℕ =>
      ∫ r in x k..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖)
        atTop (𝓝 (0 : ℝ)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  exact thirdFull_scalarTerminalTail_integral_tendsto_zero244
    (fun r : ℝ => ‖G r‖) b T hb.2 hG.norm x hCofinal
    (Filter.Eventually.of_forall (fun k =>
      ⟨(hx k).1.le, (hx k).2.le⟩))

/-- On noncollapsing selected sixth-power terminal scales, finite physical
H³ dissipation forces a PDE SOURCE PAYMENT or a strict loss in the exact
nonlinear annular Young-width deficit. The unweighted source action tends
to zero, but its outer-frequency multiplier is not automatically small. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_forceSourceOrYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hAspect : ∀ k : ℕ, 2 * rho k ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
    (hPeak : ∀ k : ℕ, 2 * epsilon k ≤
      thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) (rho k) (sigma k))
    (c : ℝ) (hc : 0 < c)
    (hTerminalScale : ∀ᶠ k : ℕ in atTop,
      c ≤ margin k * sigma k ^ 6 * (T - x k)) :
    (∀ᶠ k : ℕ in atTop,
      let H : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
        ((1 + 6 * velocityH3Energy0At u b) * (T - x k) +
          3 * (∫ r in x k..T, velocityH3DissipationAt u r))
      (margin k < (rho k ^ 2 + sigma k ^ 2) *
        (H * (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)‖ + H))) ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b (x k) (rho k) (sigma k) -
          thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b s (rho k) (sigma k) > epsilon k)) ∧
    Tendsto (fun k : ℕ =>
      ∫ r in x k..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖)
        atTop (𝓝 (0 : ℝ)) := by
  let V : ℕ → ℝ := fun k =>
    ∫ r in x k..T, velocityH3DissipationAt u r
  have hTail : Tendsto V atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨le_of_lt (lt_trans hb.1 (hx k).1), (hx k).2.le⟩))
  have hSmall : ∀ᶠ k : ℕ in atTop, V k < 119 * c / 320 :=
    hTail.eventually
      (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 119 * c / 320))
  have hChoice : ∀ᶠ k : ℕ in atTop,
      let H : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
        ((1 + 6 * velocityH3Energy0At u b) * (T - x k) +
          3 * (∫ r in x k..T, velocityH3DissipationAt u r))
      (margin k < (rho k ^ 2 + sigma k ^ 2) *
        (H * (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)‖ + H))) ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b (x k) (rho k) (sigma k) -
          thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b s (rho k) (sigma k) > epsilon k) := by
    filter_upwards [hTerminalScale, hSmall] with k hFloor hkSmall
    have hScaled : (119 / 320 : ℝ) * c ≤
        (119 / 320 : ℝ) * (margin k * sigma k ^ 6 * (T - x k)) :=
      mul_le_mul_of_nonneg_left hFloor (by norm_num)
    have hShort : V k <
        119 * margin k * sigma k ^ 6 * (T - x k) / 320 := by
      calc
        V k < (119 / 320 : ℝ) * c := by
          convert hkSmall using 1 <;> ring
        _ ≤ (119 / 320 : ℝ) *
          (margin k * sigma k ^ 6 * (T - x k)) := hScaled
        _ = 119 * margin k * sigma k ^ 6 * (T - x k) / 320 := by ring
    exact thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
      hH3 hClass hDInt b hb (x k) (hx k)
      (rho k) (sigma k) (margin k) (epsilon k)
      (hRho k) (hAspect k) (hMargin k) (hEps k)
      (hExcess k) (hPeak k) hShort
  exact ⟨hChoice, thirdFullPhysical_cofinalOuterSourceTail_tendsto_zero244
    hH3 hClass hDInt b hb x hx hCofinal⟩

end
end PrimeTensor.FirstMonomialTriad
