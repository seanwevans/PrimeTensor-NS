import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMovingRawFourierTightness
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Close the critical-eighth minimal-carrier frequency escape implication

The earlier same-witness critical-eighth theorem established an exact band
kinetic mass cost and a conditional outer-frequency escape. The physical L²
terminal trace is already obtained under finite full H³ dissipation. The
moving raw Fourier tightness theorem supplies the missing mass vanishing,
so the escape is now unconditional relative to the stated physical H³-path,
finite-dissipation and critical-height assumptions. The cutoff remains the
LEAST actual first crossing, and the windows retain the actual PDE source.

No uniform H³ terminal energy estimate or Navier--Stokes regularity theorem
is claimed. In particular, the critical-height profile is an input here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- The physical terminal L² trace makes the actual kinetic mass on the
moving minimal-crossing annuli vanish. At critical-eighth height, the SAME
minimal outer radii therefore diverge relative to the inner radii. -/
theorem thirdFullPhysical_noH3Trace_criticalEighthMinimalCarrier_outerEscape244
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
      Tendsto (fun k : ℕ =>
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3
            (τ (v k) + δ (v k)) -
          h3AuditInitialOldPhysicalHilbertTotal hH3 (τ (v k))‖ ≤
        C (v k) * δ (v k)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
      hWindows, hSummable, hTrace, _hMassCost, hAction, _hBarrier,
      hEscapeIfVanishing, _hRates, _hSourceAlt⟩ :=
    thirdFullPhysical_noH3Trace_criticalEighthCarrierMassOrTransport244
      hH3 hClass b hb hNoTrace hDInt M hM hMTop η hη hCritical
  have hBefore (k : ℕ) : τ (v k) < T := by
    rcases (hWindows k).1.1 with
      ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
    linarith only [hδ, hEnd]
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hStrict : ∀ᶠ k : ℕ in atTop,
      τ (v k) ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [hAfter] with k hk
    exact ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hk),
      hBefore k⟩
  have hBeforeEventually : ∀ᶠ k : ℕ in atTop,
      τ (v k) ∈ Set.Iio T :=
    Filter.Eventually.of_forall (fun k => hBefore k)
  have hLimitLeft : Tendsto (fun k : ℕ => τ (v k))
      atTop (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hLimit, hBeforeEventually⟩
  have hIndex : Tendsto v atTop atTop := hMono.tendsto_atTop
  have hVanishing :=
    thirdFullPhysical_movingBandRawMass_tendsto_zero_of_L2Trace244
      hH3 (fun k => τ (v k)) v
      (fun k => (N (v k) : ℝ) + 1)
      hLimitLeft hStrict hIndex hTrace
  exact ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSummable, hVanishing, hEscapeIfVanishing hVanishing,
    hAction⟩

end
end PrimeTensor.FirstMonomialTriad
