import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthTightEscape
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Construct the critical-eighth height profile from the no-trace branch

The previous critical-eighth Fourier tightness result required a chosen height
profile `M` together with `η (n+1)^8 ≤ M n`. Here the profile is fixed
explicitly, with no auxiliary sequence selected by the caller:

  M_η(n) = η (n+1)^8 + (n+1),     η > 0.

The linear term gives a direct at-top proof; the eighth-power term enforces
the sharp critical lower height. The existing no-H³-trace selection theorem
then supplies genuinely attained minimal crossing windows for THIS profile.
On those same physical windows, raw L² Fourier tightness forces the actual
annular kinetic mass to zero and therefore drives the *minimal* outer carrier
radius beyond every fixed multiple of the inner radius.

The disjoint dissipation charges, actual Hilbert momentum-transport bound,
and source/viscosity PDE alternatives remain on these witnesses. This is a
conditional necessary consequence of the no-trace branch, NOT a proof of
regularity or an assertion that the no-trace branch is nonempty.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- An explicit critical-eighth height sequence. The additional linear term
makes at-top divergence independent of any power-limit lemma. -/
def thirdFullConstructiveCriticalEighthProfile244 (η : ℝ) (n : ℕ) : ℝ :=
  η * (((n : ℝ) + 1) ^ 8) + ((n : ℝ) + 1)

theorem thirdFullConstructiveCriticalEighthProfile_pos244
    (η : ℝ) (hη : 0 < η) (n : ℕ) :
    0 < thirdFullConstructiveCriticalEighthProfile244 η n := by
  unfold thirdFullConstructiveCriticalEighthProfile244
  positivity

theorem thirdFullConstructiveCriticalEighthProfile_atTop244
    (η : ℝ) (hη : 0 < η) :
    Tendsto (thirdFullConstructiveCriticalEighthProfile244 η) atTop atTop := by
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop.2
  intro B
  filter_upwards [hNat.eventually (eventually_ge_atTop B)] with n hn
  change B ≤ η * (((n : ℝ) + 1) ^ 8) + ((n : ℝ) + 1)
  have hNonneg : 0 ≤ η * (((n : ℝ) + 1) ^ 8) := by positivity
  linarith only [hn, hNonneg]

theorem thirdFullConstructiveCriticalEighthProfile_lower244
    (η : ℝ) (n : ℕ) :
    η * (((n : ℝ) + 1) ^ 8) ≤
      thirdFullConstructiveCriticalEighthProfile244 η n := by
  unfold thirdFullConstructiveCriticalEighthProfile244
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  linarith only [hn]

/-- No prescribed height sequence or eighth-power growth condition is
necessary. For every positive scale η, lack of the strong terminal H³ trace
with finite full H³ dissipation constructs one explicit critical-eighth
profile and SAME-WITNESS minimal physical source windows, where raw kinetic
band mass vanishes while the minimal outer/inner radius ratio escapes.
The original disjoint charges and actual physical PDE alternatives are kept. -/
theorem thirdFullPhysical_noH3Trace_constructiveCriticalEighthSourceEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (η : ℝ) (hη : 0 < η) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244
        hH3 (thirdFullConstructiveCriticalEighthProfile244 η)
        τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) *
        (thirdFullConstructiveCriticalEighthProfile244 η (v k) / 4)) ∧
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
        C (v k) * δ (v k)) ∧
      (∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * thirdFullConstructiveCriticalEighthProfile244 η (v k) < 4 ∨
        (thirdFullConstructiveCriticalEighthProfile244 η (v k)) ^ 2 <
          384 * K (v k) * C (v k) *
            (((N (v k) : ℝ) + 2) ^ 5 + ((v k : ℝ) + 2) ^ 5) + 8 ∨
        (thirdFullConstructiveCriticalEighthProfile244 η (v k)) ^ 2 <
          576 * C (v k) ^ 2 *
            (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 8) ∧
      (∀ S : ℝ, 0 ≤ S → ∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * thirdFullConstructiveCriticalEighthProfile244 η (v k) < 4 ∨
        (∃ sSource : ℝ,
          sSource ∈ Set.Icc (τ (v k)) ((τ (v k) + T) / 2) ∧
          S < ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖) ∨
        (thirdFullConstructiveCriticalEighthProfile244 η (v k)) ^ 2 < 8 *
          (S * h3PathFiniteAnnulusPDELinearGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
           S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1)) := by
  let M : ℕ → ℝ := thirdFullConstructiveCriticalEighthProfile244 η
  have hM : ∀ n : ℕ, 0 < M n :=
    thirdFullConstructiveCriticalEighthProfile_pos244 η hη
  have hMTop : Tendsto M atTop atTop :=
    thirdFullConstructiveCriticalEighthProfile_atTop244 η hη
  have hCritical : ∀ᶠ n : ℕ in atTop,
      η * (((n : ℝ) + 1) ^ 8) ≤ M n :=
    Filter.Eventually.of_forall
      (thirdFullConstructiveCriticalEighthProfile_lower244 η)
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
      hWindows, hSummable, hTrace, _hMassCost, hAction, _hBarrier,
      hEscapeIfVanishing, hRates, hSourceAlt⟩ :=
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
    hAction, hRates, hSourceAlt⟩

end
end PrimeTensor.FirstMonomialTriad
