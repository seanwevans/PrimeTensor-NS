import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticFourierCubicGapFlux
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalOffshellPersistence
import Mathlib.Tactic

/-!
# Exact kinetic gap overdraw forces a solenoidal off-shell top-order flux

This module separates the genuine lower-order H³ physical transport from the
signed full-third Fourier commutator on the ORIGINAL kinetic annular PDE gaps.
For every positive margin η, if the cumulative physical viscous charges
cannot be paid by initial energy and the integrated lower-order budget plus η,
then one of the intervening gaps contains an actual snapshot with
η < -Transport₃, and necessarily η below the native sixth-power Fourier
cubic energy bound. The previous exact real-solenoidal Schwartz recovery then
carries this adverse top-order rate on the COMPLEMENT of any bounded moving
common squared-radius shell of vanishing width, while the shell contribution
tends to zero in norm. No joint-in-time Schwartz recovery, endpoint cutoff,
or universal terminal H³ ceiling is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private abbrev FluxAxisGap244 := PrimeTensor.Axis Depth.three
private abbrev FluxVGap244 := H3FourierPoint3
private abbrev FluxPairGap244 := FluxVGap244 × FluxVGap244

noncomputable local instance axisFintypeKineticOffshellGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The verified lower-order 0/1/2 physical H³ transport bound, with an
arbitrary positive margin; it does not already include the top-order cubic. -/
noncomputable def thirdFullKineticLowOrderMargin244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (η t : ℝ) : ℝ :=
  24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t + η

noncomputable def thirdFullKineticGapSignedSurplus244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (x y : ℝ) : ℝ :=
  ∫ t in x..y,
    max 0 (-velocityH3TransportDerivativeAt u t -
      2 * velocityH3DissipationAt u t)

noncomputable def thirdFullKineticGapLowOrderMargin244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (η x y : ℝ) : ℝ :=
  ∫ t in x..y, thirdFullKineticLowOrderMargin244 u η t

/-- If the actual positive signed gap expenditure exceeds the integrated
LOW-order commutator plus η, the exact physical PDE requires an adverse
THIRD-order signed transport snapshot. This proves existence by integral
comparison; no temporal integrability of the top-order flux is presumed. -/
theorem thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y η : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) (hη : 0 < η)
    (hExcess : thirdFullKineticGapLowOrderMargin244 u η x y <
      thirdFullKineticGapSignedSurplus244 u x y) :
    ∃ s : ℝ, s ∈ Set.Icc x y ∧
      η < -velocityH3TransportDerivative3At u s := by
  let E : ℝ → ℝ := velocityH3EnergyAt u
  let A : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let F : ℝ → ℝ := fun s => 24 * (A * Real.sqrt (E s)) * E s + η
  have hSubset : Set.Icc x y ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  have hECont : ContinuousOn E (Set.Icc x y) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono hSubset
  have hSqrt : ContinuousOn (fun s => Real.sqrt (E s)) (Set.Icc x y) :=
    Real.continuous_sqrt.comp_continuousOn hECont
  have hFCont : ContinuousOn F (Set.Icc x y) := by
    dsimp only [F]
    exact ((continuousOn_const.mul (continuousOn_const.mul hSqrt)).mul hECont).add
      continuousOn_const
  have hFInt : IntervalIntegrable F volume x y :=
    hFCont.intervalIntegrable_of_Icc hxy.le
  have hGInt : IntervalIntegrable
      (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)) volume x y :=
    (h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic
      hH3 hClass x y hx hy hxy).2
  by_contra hNone
  have hTop (s : ℝ) (hs : s ∈ Set.Icc x y) :
      -velocityH3TransportDerivative3At u s ≤ η := by
    exact le_of_not_gt (fun hgt => hNone ⟨s, hs, hgt⟩)
  have hPoint (s : ℝ) (hs : s ∈ Set.Icc x y) :
      max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s) ≤ F s := by
    have hsClass := hSubset hs
    have hBase := h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
      hH3 hClass hsClass
    have hExact := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
    have hD := velocityH3DissipationAt_nonneg u s
    have hLow : 0 ≤ 24 *
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u s)) * velocityH3EnergyAt u s := by
      have hE : 0 ≤ velocityH3EnergyAt u s :=
        (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_velocityH3EnergyAt u s)
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
            (Real.sqrt_nonneg _))) hE
    have hZero : 0 ≤ F s := by
      dsimp only [F, A, E]
      exact add_nonneg hLow hη.le
    have hUpper :
        -velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s ≤ F s := by
      dsimp only [F, A, E]
      linarith only [hBase, hExact, hD, hTop s hs]
    exact max_le hZero hUpper
  have hIntegral := intervalIntegral.integral_mono_on
    hxy.le hGInt hFInt hPoint
  have hEx : (∫ s in x..y, F s) <
      ∫ s in x..y,
        max 0 (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s) := by
    simpa only [F, A, E, thirdFullKineticGapLowOrderMargin244,
      thirdFullKineticGapSignedSurplus244,
      thirdFullKineticLowOrderMargin244] using hExcess
  exact (not_lt_of_ge hIntegral) hEx

/-- A certified adverse third-order sample also forces a quantified native
sixth-power Fourier energy amplitude. This is an upper constraint, not a
claim that the amplitude is bounded near the terminal time. -/
theorem thirdFullPhysical_adverseThird_forces_sixthFluxEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (η : ℝ)
    (hAdverse : η < -velocityH3TransportDerivative3At u s) :
    η < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u s + 1) ^ 3) := by
  have hFourier := thirdFullPhysical_topThird_sixthFlux_le_energyCubic244
    hH3 hClass hs
  exact lt_of_lt_of_le hAdverse
    ((neg_le_abs (velocityH3TransportDerivative3At u s)).trans hFourier)

/-- At a genuinely adverse physical top-order snapshot, every bounded
vanishing-width common-radius annular Fourier sector can be removed from
ONE physical solenoidal Schwartz recovery. Its off-shell signed sixth flux
must eventually retain the entire adverse η-margin. The recovery may depend
on the snapshot; no joint-time measurability is claimed. -/
theorem thirdFullPhysical_adverseThird_forces_offshellSixthFlux244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (η : ℝ)
    (hAdverse : η < -velocityH3TransportDerivative3At u t)
    (lo hi : ℕ → ℝ) (H : ℝ)
    (hlo : ∀ n, 0 ≤ lo n) (hlohi : ∀ n, lo n ≤ hi n)
    (hhi : ∀ n, hi n ≤ H)
    (σ : ℕ → Set FluxPairGap244) (hσ : ∀ n, MeasurableSet (σ n))
    (hShell : ∀ n z, z ∈ σ n →
      thirdFullTriadWithinSquareAnnulus244 (lo n) (hi n) z)
    (hWidth : Tendsto (fun n => hi n - lo n) atTop (𝓝 (0 : ℝ))) :
    ∃ (Ψ : ℕ → Fin 3 → SchwartzMap FluxVGap244 ℝ),
      (∀ (n : ℕ) (x : FluxVGap244), ∑ j : FluxAxisGap244,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
          (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n : ℕ =>
        ‖∫ z in σ n, thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : FluxAxisGap244 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume‖) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z in (σ n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : FluxAxisGap244 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) ∧
      (∀ᶠ n : ℕ in atTop,
        η < -(((2 * Real.pi) ^ 7 / 3) *
          (∫ z in (σ n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : FluxAxisGap244 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im)) := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  obtain ⟨_V, Ψ, _K, _hK, _hV, hDiv, _hMoments, hNear, hOff⟩ :=
    exists_thirdFullPhysicalSnapshot_offshellTransportPersistence244
      hH3.navier_stokes htNS hH3 hClass ht hFourier
      lo hi H hlo hlohi hhi σ hσ hShell hWidth
  have hThreshold : velocityH3TransportDerivative3At u t < -η := by
    linarith only [hAdverse]
  have hEventually : ∀ᶠ n : ℕ in atTop,
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z in (σ n)ᶜ, thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : FluxAxisGap244 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im < -η :=
    hOff.eventually (Iio_mem_nhds hThreshold)
  refine ⟨Ψ, hDiv, hNear, hOff, ?_⟩
  filter_upwards [hEventually] with n hn
  linarith only [hn]

/-- Finite scalar extraction: if an aggregate exceeds the sum of proposed
gap budgets but is bounded by the true gap expenditure, at least one original
gap strictly exceeds its own proposal. No nonnegativity assumptions needed. -/
theorem thirdFull_scalar_gapAggregateOverdraft244
    (g ℓ : ℕ → ℝ) (m : ℕ) (Q E : ℝ)
    (hPhysical : Q ≤ E + ∑ k ∈ Finset.range m, g k)
    (hOverdraw : E + ∑ k ∈ Finset.range m, ℓ k < Q) :
    ∃ k : ℕ, k < m ∧ ℓ k < g k := by
  by_contra hNone
  have hEach (k : ℕ) (hk : k ∈ Finset.range m) : g k ≤ ℓ k :=
    le_of_not_gt (fun hgt => hNone ⟨k, Finset.mem_range.mp hk, hgt⟩)
  have hSum : (∑ k ∈ Finset.range m, g k) ≤
      ∑ k ∈ Finset.range m, ℓ k :=
    Finset.sum_le_sum hEach
  linarith only [hPhysical, hOverdraw, hSum]

/-- Exact three-way kinetic-gap obstruction. Either an ORIGINAL PDE window
reaches the cubic Riccati scale, or the ORIGINAL physical viscous charges fit
in initial energy plus the lower-order integrated commutator with margin η,
or an ORIGINAL intervening gap contains an adverse top-third physical sample
whose amplitude is certified by the exact solenoidal sixth Fourier flux.
The preceding off-shell theorem applies to that very sample. -/
theorem thirdFullPhysical_kineticCumulativeMarginOrAdverseThird244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (η : ℝ) (hη : 0 < η) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧
        ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
          M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      ((∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
        velocityH3EnergyAt u (τ (v 0)) +
        ∑ k ∈ Finset.range m,
          thirdFullKineticGapLowOrderMargin244 u η
            (τ (v k) + δ (v k)) (τ (v (k + 1)))) ∨
      (∃ k : ℕ, k < m ∧
        ∃ s : ℝ, s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
          η < -velocityH3TransportDerivative3At u s ∧
          η < ((2 * Real.pi) ^ 7 / 3) *
            (1944 * h3SobolevFirstMomentDeweightingConstant *
              (velocityH3EnergyAt u s + 1) ^ 3)) := by
  have hBase := thirdFullPhysical_kineticDisjoint_cumulativeSignedGapBudget244
    hH3 hClass b hb M τ N δ v hSeparated hWindows
  have hGapStart (k : ℕ) :
      τ (v k) + δ (v k) ∈ Set.Ioo a T := by
    obtain ⟨ht, hw⟩ := hWindows k
    rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, ht.1, hδ], hEnd⟩
  have hGapFinish (k : ℕ) :
      τ (v (k + 1)) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  intro m
  rcases hBase m with hRiccati | hBudget
  · exact Or.inl hRiccati
  · let Q : ℝ :=
      (∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1
    let E : ℝ := velocityH3EnergyAt u (τ (v 0))
    let g : ℕ → ℝ := fun k =>
      thirdFullKineticGapSignedSurplus244 u
        (τ (v k) + δ (v k)) (τ (v (k + 1)))
    let ℓ : ℕ → ℝ := fun k =>
      thirdFullKineticGapLowOrderMargin244 u η
        (τ (v k) + δ (v k)) (τ (v (k + 1)))
    have hPhysical : Q ≤ E + ∑ k ∈ Finset.range m, g k := by
      simpa only [Q, E, g, thirdFullKineticGapSignedSurplus244] using hBudget
    by_cases hLow : Q ≤ E + ∑ k ∈ Finset.range m, ℓ k
    · exact Or.inr (Or.inl (by simpa only [Q, E, ℓ] using hLow))
    · have hOver : E + ∑ k ∈ Finset.range m, ℓ k < Q :=
        lt_of_not_ge hLow
      obtain ⟨k, hk, hExcess⟩ :=
        thirdFull_scalar_gapAggregateOverdraft244 g ℓ m Q E hPhysical hOver
      have hTime : τ (v k) + δ (v k) < τ (v (k + 1)) :=
        hSeparated k (k + 1) (Nat.lt_succ_self k)
      have hStrict :
          thirdFullKineticGapLowOrderMargin244 u η
            (τ (v k) + δ (v k)) (τ (v (k + 1))) <
          thirdFullKineticGapSignedSurplus244 u
            (τ (v k) + δ (v k)) (τ (v (k + 1))) := by
        simpa only [ℓ, g] using hExcess
      obtain ⟨s, hs, hTop⟩ :=
        thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
          hH3 hClass _ _ η (hGapStart k) (hGapFinish k)
          hTime hη hStrict
      have hsClass : s ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hGapStart k).1 hs.1,
          lt_of_le_of_lt hs.2 (hGapFinish k).2⟩
      have hAmplitude :=
        thirdFullPhysical_adverseThird_forces_sixthFluxEnergy244
          hH3 hClass hsClass η hTop
      exact Or.inr (Or.inr ⟨k, hk, s, hs, hTop, hAmplitude⟩)

/-- Same-window no-terminal-H³-trace consequence. The earlier genuine
kinetic-selected windows still have exact cutoffs, strict separation,
cofinality, global viscous packing, absolute source-L¹ decay, and uniform
raw kinetic mass decay. For ANY η>0 their gap account has the sharper
low-order-budget / off-shell-top-flux / Riccati three-way alternative. -/
theorem thirdFullPhysical_noH3Trace_kineticOffshellGapObstruction244
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
      (∀ η : ℝ, 0 < η → ∀ m : ℕ,
        (∃ k : ℕ, k ≤ m ∧
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        ((∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
          velocityH3EnergyAt u (τ (v 0)) +
          ∑ k ∈ Finset.range m,
            thirdFullKineticGapLowOrderMargin244 u η
              (τ (v k) + δ (v k)) (τ (v (k + 1)))) ∨
        (∃ k : ℕ, k < m ∧
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
            η < -velocityH3TransportDerivative3At u s ∧
            η < ((2 * Real.pi) ^ 7 / 3) *
              (1944 * h3SobolevFirstMomentDeweightingConstant *
                (velocityH3EnergyAt u s + 1) ^ 3))) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, _hAccount⟩ :=
    thirdFullPhysical_noH3Trace_kineticCumulativeSignedGapObstruction244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hWindows (k : ℕ) :
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)) :=
    ⟨(hTimes k).2.1, (hTimes k).2.2⟩
  have hAlternative := thirdFullPhysical_kineticCumulativeMarginOrAdverseThird244
    hH3 hClass b hb M τ N δ v hSeparated hWindows
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform,
    fun η hη m => hAlternative η hη m⟩

end
end PrimeTensor.FirstMonomialTriad
