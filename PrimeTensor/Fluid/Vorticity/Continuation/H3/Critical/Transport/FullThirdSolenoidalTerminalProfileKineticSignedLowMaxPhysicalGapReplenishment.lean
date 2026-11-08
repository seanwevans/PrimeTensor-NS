import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxAdversePhysicalRecovery
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticCompactGapLowMaxFlux
import Mathlib.Tactic

/-!
# Physical signed replenishment: automatic two-snapshot Fourier recovery

An actual positive signed physical gap-surplus produces an adverse third-order
transport observation. The preceding theorem recovers its negative LowMax
Schwartz flux or the physical high-radial tail, but needed an independently
provided earlier reference Schwartz state.

Here the same genuine solenoidal physical snapshot recovery automatically
constructs that reference at the ORIGINAL left gap endpoint, with arbitrarily
small H3 error and exact a.e. Fourier representation. No new two-snapshot
adverse flux hypothesis or a time-dependent Schwartz selection is introduced.

The integrated gap-surplus theorem and the original cumulative kinetic
replenishment trichotomy are then lifted to this full physical outcome,
retaining the actual gap, its common LowMax cutoff, and the physical cubic
energy ceiling. The baseline/clock/viscous arms remain honest alternatives.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private abbrev AA3 := PrimeTensor.Axis Depth.three
private abbrev AV3 := H3FourierPoint3

noncomputable local instance axisFintypeSignedReplenishment244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At EVERY actual strict physical time there is a real-solenoidal Schwartz
reference with the genuine weighted Fourier state, arbitrarily close in H3.
This is obtained from the existing physical Schwartz recovery rather than
postulating an independent reference state. -/
theorem thirdFullPhysical_snapshot_signedLowMax_referenceRecovery244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (sigma : ℝ) (hSigma : 0 < sigma) :
    ∃ (q : AA3 → SchwartzMap AV3 ℂ) (W : H3SpectralVelocityState),
      (∀ j : AA3,
        (W (h3ClassicalizationFinOfAxis j) : AV3 → ℂ) =ᵐ[volume]
          (fun ξ : AV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ)) ∧
      (∀ ξ : AV3, ∑ j : AA3,
        fderiv ℝ (q j) ξ (h3FourierAxisDirection j) = 0) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖ < sigma := by
  have hsNS : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  let hInt : VelocityH3IntegrableAt u s :=
    hH3.velocity_h3_integrable s hsNS
  let hMeas : VelocityH3MeasurableAt u s :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes hsNS
  let hFourier : VelocityH3FourierCompatibleAt u s hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes hsNS hInt
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 s
  have hUeq : U = velocityH3SpectralStateAt u s hInt hMeas hFourier := by
    dsimp only [U]
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 s hsNS]
    rfl
  obtain ⟨V, Psi, hVraw, hAE, hDiv, _hDefect, _hE₂, _hE₃, _hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hH3.navier_stokes hsNS hH3 hClass hs hFourier
  have hV : Tendsto V atTop (𝓝 U) := by
    rw [hUeq]
    exact hVraw
  have hDiff : Tendsto (fun n : ℕ => ‖V n - U‖)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hV
  obtain ⟨n, hn⟩ :=
    (hDiff.eventually (eventually_lt_nhds hSigma)).exists
  let q : AA3 → SchwartzMap AV3 ℂ :=
    fun j => h3SchwartzComplexify (Psi n (h3ClassicalizationFinOfAxis j))
  have hRep : ∀ j : AA3,
      (V n (h3ClassicalizationFinOfAxis j) : AV3 → ℂ) =ᵐ[volume]
        (fun ξ : AV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ) := by
    intro j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hSol : ∀ ξ : AV3, ∑ j : AA3,
      fderiv ℝ (q j) ξ (h3FourierAxisDirection j) = 0 := by
    intro ξ
    exact hDiv n ξ
  have hReverse : ‖U - V n‖ < sigma := by
    rw [norm_sub_rev]
    exact hn
  exact ⟨q, V n, hRep, hSol, by simpa only [U] using hReverse⟩

/-- Fully explicit physical signed-replenishment outcome on the SAME kinetic
gap. The earlier Schwartz reference is now an actual physical recovery at
its left endpoint. The adverse later time is selected by physical transport,
not assumed to have a two-snapshot flux excursion. -/
def ThirdFullKineticSignedLowMaxPhysicalGapOutcome244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (x y eta gamma epsilon sigma : ℝ) : Prop :=
  ∃ t : ℝ, t ∈ Set.Icc x y ∧
    eta < -velocityH3TransportDerivative3At u t ∧
    eta < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) ^ 3) ∧
    ∃ (q : AA3 → SchwartzMap AV3 ℂ) (W : H3SpectralVelocityState),
      (∀ j : AA3,
        (W (h3ClassicalizationFinOfAxis j) : AV3 → ℂ) =ᵐ[volume]
          (fun ξ : AV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ)) ∧
      (∀ ξ : AV3, ∑ j : AA3,
        fderiv ℝ (q j) ξ (h3FourierAxisDirection j) = 0) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 x - W‖ < sigma ∧
      ((eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
        (1944 * h3SobolevFirstMomentDeweightingConstant *
          (velocityH3EnergyAt u t + 1) *
          (‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
       ∃ (p : AA3 → SchwartzMap AV3 ℂ) (V : H3SpectralVelocityState),
         (∀ j : AA3,
           (V (h3ClassicalizationFinOfAxis j) : AV3 → ℂ) =ᵐ[volume]
             (fun ξ : AV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (p j)) ξ)) ∧
         (∀ ξ : AV3, ∑ j : AA3,
           fderiv ℝ (p j) ξ (h3FourierAxisDirection j) = 0) ∧
         ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ < epsilon ∧
         ((thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2 ≤
           |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im|) ∨
          (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 4 <
            thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
              (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
                thirdFullFiniteBandH3WeightCeiling244 R *
                  (∫ r in x..y,
                    ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
                ‖h3AuditActualSpectralVelocityTotal hH3 x - W‖)) ∨
          (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
            ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
            width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
              R V W (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2) / 4) ≤
              ∫ r in x..y, velocityH3DissipationAt u r ∂volume)))

/-- An ACTUAL adverse physical third-order time on a strict gap is enough to
construct both Schwartz profiles and their exact Fourier states. There is no
reference-recovery hypothesis; both errors can be prescribed independently. -/
theorem thirdFullPhysical_gapAdverseThird_twoPhysicalSignedRecoveries244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (ht : t ∈ Set.Icc x y)
    (eta gamma epsilon sigma : ℝ)
    (hEta : 0 < eta) (hGamma : 0 < gamma)
    (hEpsilon : 0 < epsilon) (hSigma : 0 < sigma)
    (hAdverse : eta < -velocityH3TransportDerivative3At u t) :
    ThirdFullKineticSignedLowMaxPhysicalGapOutcome244
      hH3 R x y eta gamma epsilon sigma := by
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hxClass.1 ht.1,
      lt_of_le_of_lt ht.2 hy.2⟩
  have hAmplitude :=
    thirdFullPhysical_adverseThird_forces_sixthFluxEnergy244
      hH3 hClass htClass eta hAdverse
  obtain ⟨q, W, hq, hSolQ, hNearQ⟩ :=
    thirdFullPhysical_snapshot_signedLowMax_referenceRecovery244
      hH3 hClass hxClass sigma hSigma
  have hAlt :=
    thirdFullPhysical_strictGap_adverseThird_tailOrBaselineClockCost244
      hH3 hClass hDInt b hb R x y hx hy hxy
      x t ⟨le_rfl, hxy.le⟩ ht q W hq
      eta gamma epsilon hEta hGamma hEpsilon hAdverse
  exact ⟨t, ht, hAdverse, hAmplitude, q, W, hq, hSolQ, hNearQ, hAlt⟩

/-- The ORIGINAL signed integrated surplus, not an externally specified
adverse snapshot, now forces this genuine two-physical-recovery alternative.
No cofinal adverse-margin or uniform cutoff assumption is introduced. -/
theorem thirdFullPhysical_gapSignedSurplus_twoPhysicalSignedRecoveries244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (eta gamma epsilon sigma : ℝ)
    (hEta : 0 < eta) (hGamma : 0 < gamma)
    (hEpsilon : 0 < epsilon) (hSigma : 0 < sigma)
    (hExcess : thirdFullKineticGapLowOrderMargin244 u eta x y <
      thirdFullKineticGapSignedSurplus244 u x y) :
    ThirdFullKineticSignedLowMaxPhysicalGapOutcome244
      hH3 R x y eta gamma epsilon sigma := by
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hy.1, hy.2⟩
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
      hH3 hClass x y eta hxClass hyClass hxy hEta hExcess
  exact thirdFullPhysical_gapAdverseThird_twoPhysicalSignedRecoveries244
    hH3 hClass hDInt b hb R x y t hx hy hxy ht
    eta gamma epsilon sigma hEta hGamma hEpsilon hSigma hAdverse

/-- Full cumulative physical H3 ledger on the ORIGINAL annular kinetic
windows. A Riccati-scale window or the previous aggregate low-order budget
still discharges the first two arms. In the remaining arm, the earlier
accepted proof selects an actual offending original gap, a common LowMax
radius before the adverse time, and an adverse physical third-order snapshot.
We now automatically construct BOTH exact Schwartz Fourier recoveries there,
with independent arbitrarily small H3 errors, and keep every physical
high-tail/baseline/PDE clock/viscous-charge alternative. -/
theorem thirdFullPhysical_kineticCumulativeMarginOrTwoPhysicalSignedRecoveries244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta gamma epsilon sigma : ℝ)
    (hEta : 0 < eta) (hGamma : 0 < gamma)
    (hEpsilon : 0 < epsilon) (hSigma : 0 < sigma) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧
        ∃ s : ℝ, s ∈ Set.Icc (tau (v k)) (tau (v k) + delta (v k)) ∧
          M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      ((∑ k ∈ Finset.range (m + 1), delta (v k) * (M (v k) / 4)) + 1 ≤
        velocityH3EnergyAt u (tau (v 0)) +
        ∑ k ∈ Finset.range m,
          thirdFullKineticGapLowOrderMargin244 u eta
            (tau (v k) + delta (v k)) (tau (v (k + 1)))) ∨
      (∃ k : ℕ, k < m ∧
        ∃ R : ℕ,
          ThirdFullKineticSignedLowMaxPhysicalGapOutcome244
            hH3 R (tau (v k) + delta (v k)) (tau (v (k + 1)))
            eta gamma epsilon sigma) := by
  intro m
  have hOld := thirdFullPhysical_kineticCumulativeMarginOrGapLowMax244
    hH3 hClass b hb M tau N delta v hSeparated hWindows eta hEta m
  rcases hOld with hRiccati | hBudget | ⟨k, hk, hCarrier, t, ht, hAdverse, _hAmplitude⟩
  · exact Or.inl hRiccati
  · exact Or.inr (Or.inl hBudget)
  · right; right
    obtain ⟨R, _hUniform⟩ := hCarrier
    have hStart : tau (v k) + delta (v k) ∈ Set.Ioo b T := by
      have hWin := (hWindows k).2
      rcases hWin with ⟨_, hDelta, _, hEnd, _, _⟩
      exact ⟨by linarith only [(hWindows k).1.1, hDelta], hEnd⟩
    have hFinish : tau (v (k + 1)) ∈ Set.Ioo b T :=
      (hWindows (k + 1)).1
    have hGap : tau (v k) + delta (v k) < tau (v (k + 1)) :=
      hSeparated k (k + 1) (Nat.lt_succ_self k)
    have hOutcome := thirdFullPhysical_gapAdverseThird_twoPhysicalSignedRecoveries244
      hH3 hClass hDInt b hb R
      (tau (v k) + delta (v k)) (tau (v (k + 1))) t
      hStart hFinish hGap ht
      eta gamma epsilon sigma hEta hGamma hEpsilon hSigma hAdverse
    exact ⟨k, hk, R, hOutcome⟩

end
end PrimeTensor.FirstMonomialTriad
