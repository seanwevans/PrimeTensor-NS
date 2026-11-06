import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthKineticGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUnconditionalHilbertFTCKinetic244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Same-witness critical-eighth raw kinetic carrier and physical source action

The selected outer cutoff is the least crossing of M/2. The corresponding
physical Fourier annular mass pays its dissipative cost at the critical
eighth frequency scale. For every fixed relative-frequency cap D, the
critical-height assumption forces a positive raw mass floor or a genuine
superlinear escape of the minimal first crossing.

The canonical source ceiling is an attained physical L2 maximum. The actual
positive-time physical Hilbert FTC converts this ceiling into an explicit
momentum-transport bound over the SAME disjoint persistence windows.

Finite full H3 dissipation provides a physical L2 terminal trace. A separate
moving-frequency tightness transfer is still required to infer that raw
mass in the selected rapidly moving annuli tends to zero. We retain this
last implication as an explicit conditional theorem, without inserting any
new axiom or hypothesizing an unproved uniform H3 cutoff bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- True physical momentum transport, not merely a formal PDE rate:
the projected Navier--Stokes source norm on a strict window controls
its old physical L2 Hilbert velocity difference by the elapsed time. -/
theorem thirdFullPhysical_projectedSourceAction_controls_kineticIncrement244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t δ s C : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hδ : 0 < δ) (hEnd : t + δ < T)
    (hs : s ∈ Set.Icc t (t + δ))
    (hSource : ∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ C * (s - t) := by
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244
    hH3 t s ht hsAbs
  have hts : t ≤ s := hs.1
  have hNorm :
      ‖∫ r in t..s, h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        C * |s - t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    have hrIoc : r ∈ Set.Ioc t s := by
      simpa only [Set.uIoc_of_le hts] using hr
    exact hSource r ⟨hrIoc.1.le, hrIoc.2.trans hs.2⟩
  calc
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ =
        ‖∫ r in t..s, h3PathActualProjectedMomentumSource244 hH3 r‖ := by
          rw [hFTC]
    _ ≤ C * |s - t| := hNorm
    _ = C * (s - t) := by rw [abs_of_nonneg (sub_nonneg.mpr hts)]

/-- On the original disjoint, minimal-carrier physical H3 windows, a
critical-eighth profile demands either outer-frequency escape or a fixed
positive raw kinetic-mass floor. The source maxima simultaneously bound
actual physical L2 momentum transport. The last, conditional implication
isolates the exact missing moving-band tightness-to-frequency step.

The previous genuine physical source-peak / quintic / eighth-order PDE
alternatives are preserved on these SAME witnesses. -/
theorem thirdFullPhysical_noH3Trace_criticalEighthCarrierMassOrTransport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (hMTop : Tendsto M atTop atTop)
    (η : ℝ) (hη : 0 < η)
    (hCritical : ∀ᶠ n : ℕ in atTop,
      η * (((n : ℝ) + 1) ^ 8) ≤ M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244
        hH3 M τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (M (v k) / 4)) ∧
      (∃ U : H3PhysicalRealFinVectorL2Hilbert,
        Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
          (𝓝[<] T) (𝓝 U)) ∧
      (∀ᶠ k : ℕ in atTop,
        M (v k) < 8 * (((N (v k) : ℝ) + 2) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ᶠ k : ℕ in atTop,
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3
              (τ (v k) + δ (v k)) -
          h3AuditInitialOldPhysicalHilbertTotal hH3 (τ (v k))‖ ≤
          C (v k) * δ (v k)) ∧
      (∀ D : ℝ, 0 ≤ D → ∀ᶠ k : ℕ in atTop,
        D * ((v k : ℝ) + 1) < ((N (v k) : ℝ) + 2) ∨
        η < 8 * D ^ 8 *
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (Tendsto (fun k : ℕ =>
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
          atTop (𝓝 (0 : ℝ)) →
        Tendsto (fun k : ℕ =>
          ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop) ∧
      (∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        M (v k) ^ 2 < 384 * K (v k) * C (v k) *
          (((N (v k) : ℝ) + 2) ^ 5 + ((v k : ℝ) + 2) ^ 5) + 8 ∨
        M (v k) ^ 2 < 576 * C (v k) ^ 2 *
          (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 8) ∧
      (∀ S : ℝ, 0 ≤ S → ∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        (∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          S < ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖) ∨
        M (v k) ^ 2 < 8 *
          (S * h3PathFiniteAnnulusPDELinearGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
           S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
      hWindows, hSummable, _hLast, _hAveraged, hRates, hSourceAlt⟩ :=
    thirdFullPhysical_noH3Trace_minimalCarrier_sourceClock_or_physicalRates244
      hH3 hClass b hb hNoTrace hDInt M hM hMTop
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hMassCost : ∀ᶠ k : ℕ in atTop,
      M (v k) < 8 * (((N (v k) : ℝ) + 2) ^ 8) *
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    filter_upwards [hAfter] with k hkAfter
    rcases (hWindows k).1.1 with
      ⟨hnN, _, _, hδ, _, hEnd, _, _, hCross, _, _, _, _⟩
    have ht : τ (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hkAfter, by linarith only [hδ, hEnd]⟩
    exact thirdFullPhysical_profileAnnulus_rawEighthKineticCost244
      hH3 hClass (τ (v k)) ht (v k) (N (v k)) hnN (M (v k)) hCross
  have hAction : ∀ᶠ k : ℕ in atTop,
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3
            (τ (v k) + δ (v k)) -
        h3AuditInitialOldPhysicalHilbertTotal hH3 (τ (v k))‖ ≤
        C (v k) * δ (v k) := by
    filter_upwards [hAfter] with k hkAfter
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hδ, _, hEnd, _, hSource, _, _, _, _, _⟩
    have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hkAfter),
        by linarith only [hδ, hEnd]⟩
    have hRight : τ (v k) + δ (v k) ∈
        Set.Icc (τ (v k)) (τ (v k) + δ (v k)) :=
      ⟨by linarith only [hδ], le_rfl⟩
    have hAction' := thirdFullPhysical_projectedSourceAction_controls_kineticIncrement244
      hH3 (τ (v k)) (δ (v k))
      (τ (v k) + δ (v k)) (C (v k))
      ht hδ hEnd hRight hSource
    convert hAction' using 1 <;> ring
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let Q : ℕ → ℝ := fun k => (N (v k) : ℝ) + 1
  let H : ℕ → ℝ := fun k => M (v k)
  let μ : ℕ → ℝ := fun k =>
    h3PathActualBandRawKineticMass244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
  have hR (k : ℕ) : 1 ≤ R k := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hQ (k : ℕ) : 0 ≤ Q k := by
    dsimp only [Q]
    positivity
  have hμ (k : ℕ) : 0 ≤ μ k :=
    thirdFull_bandRawKineticMass_nonneg244 _ _ _
  have hCriticalK : ∀ᶠ k : ℕ in atTop, η * R k ^ 8 ≤ H k := by
    have hEv := hMono.tendsto_atTop.eventually hCritical
    simpa only [R, H] using hEv
  have hCostK : ∀ᶠ k : ℕ in atTop,
      H k < 8 * (Q k + 1) ^ 8 * μ k := by
    filter_upwards [hMassCost] with k hk
    change M (v k) < 8 * (((N (v k) : ℝ) + 1) + 1) ^ 8 *
      h3PathActualBandRawKineticMass244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
    convert hk using 1 <;> ring
  have hBarrier (D : ℝ) (hD : 0 ≤ D) :
      ∀ᶠ k : ℕ in atTop,
        D * ((v k : ℝ) + 1) < (N (v k) : ℝ) + 2 ∨
        η < 8 * D ^ 8 *
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    filter_upwards [hCriticalK, hCostK] with k hCriticalAt hCostAt
    have hAlt := thirdFull_criticalEighthHeight_forces_farCarrier_or_kineticMass244
      (R k) (Q k) (H k) (μ k) D η
      (hR k) (hQ k) (hμ k) hD hη hCriticalAt hCostAt
    rcases hAlt with hFar | hMass
    · left
      dsimp only [R, Q] at hFar
      linarith only [hFar]
    · exact Or.inr hMass
  have hVanishing :
      Tendsto (fun k : ℕ => μ k) atTop (𝓝 (0 : ℝ)) →
      Tendsto (fun k : ℕ => ((N (v k) : ℝ) + 2) /
        ((v k : ℝ) + 1)) atTop atTop := by
    intro hZero
    have hOuter := thirdFull_criticalEighthHeight_vanishingBand_forces_escape244
      R Q H μ η hR hQ hμ hη hCriticalK hCostK hZero
    have hOuterFn :
        (fun k : ℕ => (Q k + 1) / R k) =
        (fun k : ℕ => ((N (v k) : ℝ) + 2) /
          ((v k : ℝ) + 1)) := by
      funext k
      dsimp only [Q, R]
      ring
    rw [hOuterFn] at hOuter
    exact hOuter
  have hTrace := h3Critical_physicalL2_terminal_trace_of_finite_dissipation
    hH3 hClass hDInt
  exact ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSummable, hTrace, hMassCost, hAction, hBarrier,
    (by simpa only [μ] using hVanishing), hRates, hSourceAlt⟩

end
end PrimeTensor.FirstMonomialTriad
