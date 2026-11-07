import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticDisjointRawEighthTightness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthWindowRawTransport
import Mathlib.Tactic

/-!
# Transported raw Fourier tightness throughout the actual kinetic PDE windows

The existing kinetic-only annular clock has positive H3 dissipation on its
entire physical interval, but the preceding raw-eighth theorem controls raw
kinetic mass only at the start. The actual projected Navier--Stokes source
is Bochner-L1 on a terminal interval when full H3 dissipation is integrable.
Combining the physical Hilbert FTC, raw Fourier Plancherel, and highpass
contraction gives UNIFORM moving-annular kinetic tightness on every instant
of those very same disjoint kinetic-selected windows. The H3 annular floor
and the eighth-power raw carrier bound also hold at every such instant.

This is a transport/energy separation result, not a terminal H3 trace:
the positive H3 dissipation is supported on vanishing raw kinetic mass at
an unconstrained moving outer radius. No rate bound on that radius follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

-- The imported physical Fourier lemmas use the canonical product measure.
-- Their local instances are intentionally not exported between modules.
noncomputable local instance axisFintypeKineticDynamicRaw244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceKineticDynamicRaw244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Absolute physical projected-source action vanishes on the SAME cofinal
kinetic-selected PDE intervals. A peak times its width is not substituted
for this actual Bochner-L1 norm integral. -/
theorem thirdFullPhysical_kineticWindows_sourceL1_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T))
    (hWindows : ∀ k : ℕ, τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k))) :
    Tendsto (fun k : ℕ =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hPos (k : ℕ) : 0 < δ (v k) ∧
      τ (v k) + δ (v k) < T := by
    rcases (hWindows k).2 with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨hδ, hEnd⟩
  have hGap : Tendsto (fun k : ℕ => T - τ (v k))
      atTop (𝓝 (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => (T : ℝ)) atTop (𝓝 T) :=
      tendsto_const_nhds
    simpa only [sub_self] using hConst.sub hLimit
  have hδZero : Tendsto (fun k : ℕ => δ (v k))
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun k => (hPos k).1.le))
      (Filter.Eventually.of_forall (fun k => by
        have hk := (hPos k).2
        linarith only [hk]))
      hGap
  have hEndT : Tendsto (fun k : ℕ => τ (v k) + δ (v k))
      atTop (𝓝 T) := by
    simpa only [add_zero] using hLimit.add hδZero
  have hWindow : ∀ᶠ k : ℕ in atTop,
      b ≤ τ (v k) ∧ τ (v k) ≤ τ (v k) + δ (v k) ∧
        τ (v k) + δ (v k) ≤ T :=
    Filter.Eventually.of_forall (fun k =>
      ⟨(hWindows k).1.1.le, by linarith only [(hPos k).1],
        (hPos k).2.le⟩)
  exact thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244
    G b T hb.2 hG (fun k => τ (v k))
    (fun k => τ (v k) + δ (v k)) hLimit hEndT hWindow

/-- At EVERY instant in the original exact kinetic PDE persistence window,
the same positive H3 annular floor is paid by raw kinetic mass in that
annulus, not by the total kinetic energy. No source maximum is involved. -/
theorem thirdFullPhysical_kineticWindow_rawEighthThroughout244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (n N : ℕ) (M δ : ℝ)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ)
    (s : ℝ) (hs : s ∈ Set.Icc x (x + δ)) :
    M / 4 < 4 * (((N : ℝ) + 2) ^ 8) *
      h3PathActualBandRawKineticMass244 ((n : ℝ) + 1)
        ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
  rcases hWindow with ⟨hnN, _hδ, _hEq, hEnd, hFloor, _hCost⟩
  have hCast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hRadial : ((n : ℝ) + 1) ≤ ((N : ℝ) + 1) := by
    linarith only [hCast]
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le (lt_trans hb.1 hx.1) hs.1,
      lt_of_le_of_lt hs.2 hEnd⟩
  have hFourier := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass s hsClass ((n : ℝ) + 1) ((N : ℝ) + 1)
    hRadial (by positivity)
  simpa only [show ((N : ℝ) + 1) + 1 = (N : ℝ) + 2 by ring] using
    (lt_of_lt_of_le (hFloor s hs).1 hFourier)

/-- The real projected momentum FTC bounds the SAME moving raw annulus at
all physical times on the kinetic-selected windows, uniformly in time.
Neither outer Fourier radius nor source-peak height is bounded. -/
theorem thirdFullPhysical_kineticWindows_uniformMovingRawMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hMono : StrictMono v)
    (hLimit : Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T))
    (hWindows : ∀ k : ℕ, τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) < ε := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hLimitLeft : Tendsto (fun k : ℕ => τ (v k))
      atTop (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hLimit, Filter.Eventually.of_forall (fun k => (hWindows k).1.2)⟩
  obtain ⟨L, hTrace⟩ :=
    h3Critical_physicalL2_terminal_trace_of_finite_dissipation
      hH3 hClass hDInt
  have hPhysical : Tendsto (fun k : ℕ => X (τ (v k)))
      atTop (𝓝 L) := hTrace.comp hLimitLeft
  have hHigh : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (v k)
        (F (X (τ (v k))))‖) atTop (𝓝 (0 : ℝ)) :=
    thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244
      (fun k : ℕ => X (τ (v k))) L v
      hPhysical hMono.tendsto_atTop
  have hL1 : Tendsto (fun k : ℕ =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)), ‖G r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFullPhysical_kineticWindows_sourceL1_tendsto_zero244
      hH3 hClass hDInt b hb M τ N δ v hLimit hWindows
  have hBound : Tendsto (fun k : ℕ =>
      3 * (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (F (X (τ (v k))))‖ +
        ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖G r‖ ∂volume)) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hCombined := hHigh.add (hL1.const_mul ‖F‖)
    have hSquared := hCombined.pow 2
    have hScaled := hSquared.const_mul 3
    simpa using hScaled
  intro ε hε
  have hSmall : ∀ᶠ k : ℕ in atTop,
      3 * (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
          (F (X (τ (v k))))‖ +
        ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖G r‖ ∂volume)) ^ 2 < ε :=
    hBound.eventually (eventually_lt_nhds hε)
  filter_upwards [hSmall] with k hkSmall
  intro s hs
  have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
        (lt_trans hb.1 (hWindows k).1.1), (hWindows k).1.2⟩
  have hPos : 0 < δ (v k) ∧ τ (v k) + δ (v k) < T := by
    rcases (hWindows k).2 with ⟨_, hp, _, hend, _, _⟩
    exact ⟨hp, hend⟩
  have hσ : τ (v k) + δ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ht.1 (by linarith only [hPos.1]), hPos.2⟩
  have hsTime : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hPos.2⟩
  have hMassBound := thirdFullPhysical_rawBandMass_window_le_sourceL1244
    hH3 (v k) ((N (v k) : ℝ) + 1)
    (τ (v k)) (τ (v k) + δ (v k)) s
    ht hσ hsTime hs.1 hs.2
  exact hMassBound.trans_lt (by
    change 3 * (‖thirdFullSpectralVelocityHighRadialApply244 (v k)
        (F (X (τ (v k))))‖ +
      ‖F‖ * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
        ‖G r‖ ∂volume)) ^ 2 < ε at hkSmall
    exact hkSmall)

/-- Critical-eighth separation now holds uniformly across each WHOLE
kinetic-selected window, not merely at its start: M/(N+2)^8 is bounded by
the sup raw annular mass, and that mass tends to zero. -/
theorem thirdFullPhysical_kineticWindows_uniformNormalizedHeight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hMono : StrictMono v)
    (hLimit : Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T))
    (hWindows : ∀ k : ℕ, τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        M (v k) / (((N (v k) : ℝ) + 2) ^ 8) < ε ∧
        M (v k) / 4 < 4 * (((N (v k) : ℝ) + 2) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
  intro ε hε
  have hSmall := thirdFullPhysical_kineticWindows_uniformMovingRawMass244
    hH3 hClass hDInt b hb M τ N δ v hMono hLimit hWindows
    (ε / 16) (by positivity)
  filter_upwards [hSmall] with k hk
  intro s hs
  let Q : ℝ := (N (v k) : ℝ) + 2
  let μ : ℝ := h3PathActualBandRawKineticMass244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s)
  have hQ : 0 < Q ^ 8 := by
    dsimp only [Q]
    positivity
  have hAt := thirdFullPhysical_kineticWindow_rawEighthThroughout244
    hH3 hClass b hb (τ (v k)) (hWindows k).1
    (v k) (N (v k)) (M (v k)) (δ (v k)) (hWindows k).2 s hs
  have hAt' : M (v k) / 4 < 4 * Q ^ 8 * μ := by
    simpa only [Q, μ] using hAt
  have hDiv : M (v k) / Q ^ 8 < 16 * μ := by
    apply (div_lt_iff₀ hQ).2
    nlinarith only [hAt']
  have hSmall' : μ < ε / 16 := hk s hs
  have hRatio : M (v k) / Q ^ 8 < ε := by
    have hScaled := mul_lt_mul_of_pos_left hSmall' (by norm_num : (0 : ℝ) < 16)
    have hEq : 16 * (ε / 16) = ε := by ring
    rw [hEq] at hScaled
    exact lt_trans hDiv hScaled
  exact ⟨by simpa only [Q] using hRatio, hAt⟩

/-- SAME-WITNESS physical terminal consequence: failure of the weighted
terminal H3 trace plus finite ordinary physical H3 dissipation retains the
original disjoint kinetic PDE windows, their global ENNReal viscous cost,
and absolute source-L1 decay. Every instant of every sufficiently late
window simultaneously carries its positive H3 annular floor in a vanishing
raw Fourier mass. The carrier height is uniformly little-o of (N+2)^8.
No bound on the actual outer frequency or on full H3 amplitude is inferred. -/
theorem thirdFullPhysical_noH3Trace_kineticDynamicRawWindowConcentration244
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
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          M (v k) / (((N (v k) : ℝ) + 2) ^ 8) < ε ∧
          M (v k) / 4 < 4 * (((N (v k) : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  -- Select the original cofinal windows WITH their strict-time membership.
  -- The global-budget wrapper intentionally discards this membership, so
  -- reconstruct its packing estimate on precisely these original witnesses.
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hTimes⟩ :=
    thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244
      hH3 hClass b hb hNoTrace M hM
  let p : ℕ → ℝ := fun k => τ (v k)
  let w : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => M (v k) / 4
  have hStart (k : ℕ) : a < p k :=
    lt_trans hb.1 (hTimes k).1.1
  have hWidth (k : ℕ) : 0 ≤ w k := by
    rcases (hTimes k).2 with ⟨_, hp, _, _, _, _⟩
    exact hp.le
  have hEnd (k : ℕ) : p k + w k < T := by
    rcases (hTimes k).2 with ⟨_, _, _, hEnd, _, _⟩
    exact hEnd
  have hFloor (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + w k)) :
      H k ≤ velocityH3DissipationAt u r := by
    rcases (hTimes k).2 with ⟨_, _, _, _, hWindowFloor, _⟩
    exact ((hWindowFloor r hr).1.le).trans (hWindowFloor r hr).2
  have hSep : ∀ k l : ℕ, k < l → p k + w k < p l :=
    hSeparated
  have hCharges (m : ℕ) :
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (M (v k) / 4) *
          ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume := by
    exact thirdFull_scalar_disjointWindows_le_globalExtendedBudget244
      (velocityH3DissipationAt u) a T p w H
      hStart hWidth hEnd hSep hFloor m
  have hL1 := thirdFullPhysical_kineticWindows_sourceL1_tendsto_zero244
    hH3 hClass hDInt b hb M τ N δ v hCofinal hTimes
  have hUniform := thirdFullPhysical_kineticWindows_uniformMovingRawMass244
    hH3 hClass hDInt b hb M τ N δ v hv hCofinal hTimes
  have hHeight := thirdFullPhysical_kineticWindows_uniformNormalizedHeight244
    hH3 hClass hDInt b hb M τ N δ v hv hCofinal hTimes
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    (fun k => ⟨hIndex k, (hTimes k).1, (hTimes k).2⟩),
    hCharges, hL1, hUniform, hHeight⟩

end
end PrimeTensor.FirstMonomialTriad
