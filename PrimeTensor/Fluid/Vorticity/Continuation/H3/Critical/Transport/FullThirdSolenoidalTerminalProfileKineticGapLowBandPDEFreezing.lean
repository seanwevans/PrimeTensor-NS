import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticArbitraryRadialFluxTradeoff
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalKineticLowBandCauchy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.Tactic

/-!
# Quantitative low-band PDE freezing on the genuine kinetic Fourier-flux gaps

The last theorem locates an adverse signed sixth-power Fourier transfer in a
low-maximum sector or an actual weighted-H3 high-frequency tail at ANY radius.
Here we supply the missing temporal input for that low-frequency channel.

The exact, unconditional physical Hilbert momentum FTC and the finite-band
W3 Fourier multiplier show that the ACTUAL H3 low-radial spectral increment
on [s,t] is bounded by C_R times the absolute L1 action of the ACTUAL
projected physical Navier--Stokes source. No independent physical-H3 time
derivative, upper Fourier cutoff cap, or temporal joint-continuity premise
is introduced.

On the ORIGINAL gaps between the already selected kinetic annular PDE windows,
finite full H3 dissipation makes those source actions vanish. Thus every
fixed weighted H3 Fourier low band freezes across the SAME cofinal gaps,
including the endpoints used to account for signed sixth-power transport.
This is a temporal low-band estimate; it does NOT claim continuity of the
cubic sixth-power flux in raw kinetic L2 or a terminal-uniform H3 tail bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeKineticGapLowBandPDEFreezing244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An ACTUAL physical low-H3 Fourier band can move no faster than the
projected momentum source action multiplied by the exact radial W3 ceiling.
The underlying momentum FTC is unconditional on the strict old H3 path. -/
theorem thirdFullPhysical_strictLowBandPDEModulus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 s)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ∫ r in s..t,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume := by
  have hLow :=
    thirdFullPhysicalStrictTimes_lowRadial_distance_le_kinetic244
      hH3 R t s ht hs
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244
    hH3 s t hs ht
  have hAction :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤
        ∫ r in s..t,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume := by
    rw [hFTC]
    exact intervalIntegral.norm_integral_le_integral_norm hst
  exact hLow.trans
    (mul_le_mul_of_nonneg_left hAction
      (thirdFullFiniteBandH3WeightCeiling_nonneg244 R))

/-- Source L1 on a terminal tail vanishes on the exact INTER-WINDOW gaps,
not only on the kinetic annular persistence intervals themselves.
The next-window times and the current-window endpoints both converge to T. -/
theorem thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k))) :
    Tendsto (fun k : ℕ =>
      ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hPositive (k : ℕ) :
      0 < δ (v k) ∧ τ (v k) + δ (v k) < T := by
    rcases (hWindows k).2 with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨hδ, hEnd⟩
  have hRemaining : Tendsto (fun k : ℕ => T - τ (v k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (T : ℝ))
        atTop (𝓝 T)).sub hLimit
  have hWidth : Tendsto (fun k : ℕ => δ (v k)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun k => (hPositive k).1.le))
      (Filter.Eventually.of_forall (fun k => by
        have h := (hPositive k).2
        linarith only [h]))
      hRemaining
  have hStartT : Tendsto (fun k : ℕ => τ (v k) + δ (v k))
      atTop (𝓝 T) := by
    simpa only [add_zero] using hLimit.add hWidth
  have hEndT : Tendsto (fun k : ℕ => τ (v (k + 1)))
      atTop (𝓝 T) := by
    simpa only [Function.comp_def] using
      hLimit.comp (tendsto_add_atTop_nat 1)
  have hIntervals : ∀ᶠ k : ℕ in atTop,
      b ≤ τ (v k) + δ (v k) ∧
      τ (v k) + δ (v k) ≤ τ (v (k + 1)) ∧
      τ (v (k + 1)) ≤ T := by
    exact Filter.Eventually.of_forall (fun k =>
      ⟨by linarith only [(hWindows k).1.1, (hPositive k).1],
       (hSeparated k (k + 1) (Nat.lt_succ_self k)).le,
       (hWindows (k + 1)).1.2.le⟩)
  exact thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244
    G b T hb.2 hG
    (fun k => τ (v k) + δ (v k))
    (fun k => τ (v (k + 1)))
    hStartT hEndT hIntervals

/-- The genuine physical weighted H3 LOW band freezes across every one of
the original kinetic gaps at each fixed Fourier radius R. This is an
actual two-time PDE consequence, not a bound on the nonlinear signed flux. -/
theorem thirdFullPhysical_kineticGaps_lowBandPDEFreeze244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (R : ℕ) :
    Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v (k + 1)))) -
        thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3
            (τ (v k) + δ (v k)))‖)
      atTop (𝓝 (0 : ℝ)) := by
  have hSource := thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244
    hH3 hClass hDInt b hb M τ N δ v hLimit hSeparated hWindows
  let C : ℝ := thirdFullFiniteBandH3WeightCeiling244 R
  have hBound (k : ℕ) :
      ‖thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v (k + 1)))) -
        thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3
            (τ (v k) + δ (v k)))‖ ≤
      C * (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) := by
    have hStart : τ (v k) + δ (v k) ∈ Set.Ioo (0 : ℝ) T := by
      obtain ⟨ht, hw⟩ := hWindows k
      rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
      exact ⟨by linarith only [hClass.terminal_start.1, hb.1, ht.1, hδ], hEnd⟩
    have hEnd : τ (v (k + 1)) ∈ Set.Ioo (0 : ℝ) T := by
      have h := (hWindows (k + 1)).1
      exact ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1) h.1, h.2⟩
    exact thirdFullPhysical_strictLowBandPDEModulus244
      hH3 R _ _ hStart hEnd
      (hSeparated k (k + 1) (Nat.lt_succ_self k)).le
  have hUpper : Tendsto (fun k : ℕ =>
      C * (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hSource)
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun k => norm_nonneg _))
    (Filter.Eventually.of_forall (fun k => hBound k))
    hUpper

/-- Stronger than endpoint freezing: for each FIXED radius, the whole
physical low-H3 Fourier band is asymptotically constant on EVERY pair of
instants within the original intervening kinetic gap. The common modulus is
its full absolute projected-source action, with no dependence on the selected
pair of times. This includes any adverse third-transport sample in the gap. -/
theorem thirdFullPhysical_kineticGaps_uniformLowBandPDEFreeze244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ s t : ℝ,
        s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
        t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
        ‖thirdFullSpectralVelocityLowRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          thirdFullSpectralVelocityLowRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ < ε := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let C : ℝ := thirdFullFiniteBandH3WeightCeiling244 R
  have hC : 0 ≤ C := thirdFullFiniteBandH3WeightCeiling_nonneg244 R
  have hOneC : 0 < 1 + C := by linarith only [hC]
  have hSmall : 0 < ε / (1 + C) := div_pos hε hOneC
  have hScalar : C * (ε / (1 + C)) < ε := by
    calc
      C * (ε / (1 + C)) < (1 + C) * (ε / (1 + C)) :=
        mul_lt_mul_of_pos_right (by linarith only [hC]) hSmall
      _ = ε := by
        rw [mul_comm (1 + C)]
        exact div_mul_cancel₀ ε hOneC.ne'
  have hSource := thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244
    hH3 hClass hDInt b hb M τ N δ v hLimit hSeparated hWindows
  have hEventually : ∀ᶠ k : ℕ in atTop,
      (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)), ‖G r‖ ∂volume) <
        ε / (1 + C) := by
    exact hSource.eventually (eventually_lt_nhds hSmall)
  filter_upwards [hEventually] with k hk
  let x : ℝ := τ (v k) + δ (v k)
  let y : ℝ := τ (v (k + 1))
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hx : x ∈ Set.Ioo (0 : ℝ) T := by
    obtain ⟨ht, hw⟩ := hWindows k
    rcases hw with ⟨_, hd, _, he, _, _⟩
    exact ⟨by linarith only [hClass.terminal_start.1, hb.1, ht.1, hd], he⟩
  have hy : y ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
       (hWindows (k + 1)).1.1, (hWindows (k + 1)).1.2⟩
  have hGInt : IntervalIntegrable G volume x y :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 hx.1 hxy hy.2
  have hIntegralBound (s t : ℝ) (hs : s ∈ Set.Icc x y)
      (ht : t ∈ Set.Icc x y) (hst : s ≤ t) :
      (∫ r in s..t, ‖G r‖ ∂volume) ≤
        ∫ r in x..y, ‖G r‖ ∂volume := by
    exact intervalIntegral.integral_mono_interval
      hs.1 hst ht.2
      (Filter.Eventually.of_forall (fun r => norm_nonneg (G r))) hGInt.norm
  have hEstimate (s t : ℝ) (hs : s ∈ Set.Icc x y)
      (ht : t ∈ Set.Icc x y) (hst : s ≤ t) :
      ‖thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 s)‖ < ε := by
    have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
    have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hModulus := thirdFullPhysical_strictLowBandPDEModulus244
      hH3 R s t hs0 ht0 hst
    have hLower := hIntegralBound s t hs ht hst
    have hUpper :
        C * (∫ r in x..y, ‖G r‖ ∂volume) < ε := by
      have h := mul_le_mul_of_nonneg_left hk.le hC
      exact lt_of_le_of_lt h hScalar
    exact lt_of_le_of_lt
      (hModulus.trans (mul_le_mul_of_nonneg_left hLower hC)) hUpper
  intro s t hs ht
  by_cases hst : s ≤ t
  · rw [norm_sub_rev]
    exact hEstimate s t hs ht hst
  · have hts : t ≤ s := le_of_not_ge hst
    exact hEstimate t s ht hs hts

/-- On the EXACT cofinal kinetic witness family, both the absolute source
L1 action AND every fixed weighted H3 low-band difference vanish on the
gaps. The universal-in-radius signed sixth-flux/high-tail alternative from
the previous module remains attached to the very same witnesses. -/
theorem thirdFullPhysical_noH3Trace_kineticGapLowBandPDEFreezing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) *
            ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) < ε) ∧
      (∀ k : ℕ, ThirdFullKineticGapArbitraryRadialTradeoff244
        u T hH3 (τ (v k) + δ (v k)) (τ (v (k + 1)))) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ R : ℕ,
        Tendsto (fun k : ℕ =>
          ‖thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v (k + 1)))) -
            thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3
                (τ (v k) + δ (v k)))‖)
          atTop (𝓝 (0 : ℝ))) ∧
      (∀ R : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s t : ℝ,
          s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
          t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
          ‖thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ < ε) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, hTradeoff⟩ :=
    thirdFullPhysical_noH3Trace_kineticArbitraryRadialGapTradeoff244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hWindows (k : ℕ) :
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)) :=
    ⟨(hTimes k).2.1, (hTimes k).2.2⟩
  have hGapSource := thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244
    hH3 hClass hDInt b hb M τ N δ v hCofinal hSeparated hWindows
  have hLow (R : ℕ) := thirdFullPhysical_kineticGaps_lowBandPDEFreeze244
    hH3 hClass hDInt b hb M τ N δ v hCofinal hSeparated hWindows R
  have hAll (R : ℕ) (ε : ℝ) (hε : 0 < ε) :=
    thirdFullPhysical_kineticGaps_uniformLowBandPDEFreeze244
      hH3 hClass hDInt b hb M τ N δ v hCofinal hSeparated hWindows
      R ε hε
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, hTradeoff, hGapSource,
    hLow, hAll⟩

end
end PrimeTensor.FirstMonomialTriad
