import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePhysicalRatePolynomial
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Actual H3 terminal nontrace: physical source, quintic and eighth-power alternatives

The committed anchored PDE-clock theorem produces one disjoint family of actual
Navier--Stokes finite-annulus windows with summable viscous charges. On that
SAME family, terminal clock compression is now opposed to explicit fifth/eighth
frequency costs, not merely an anonymous large PDE coefficient. For each fixed
candidate projected-source ceiling S, one has the additional trichotomy:
terminal clock compression, failure of the selected source ceiling S, or a
large S-limited spectral state/frequency gain.

No upper bound on the outer cutoff N(k), starting weighted H3 amplitude K(k),
or local projected source ceiling C(k) is asserted. The source ceiling C is
selected from the real physical source on an actual time interval; C>S by
itself is NOT a lower bound on the source at any single time.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalProfilePhysicalRate244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the exact SAME disjoint, summably charged terminal windows from
absence of a strong H3 trace, the late-time endpoint rate obstruction is
an actual projected-source / high-frequency geometric alternative.
Neither physical kinetic L2 nontrace nor positive terminal kinetic mass
is needed. This is not an unconditional H3 terminal trace. -/
theorem thirdFullPhysical_noH3Trace_profileClock_or_physicalQuinticEighth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (hMTop : Tendsto M atTop atTop) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileAnchoredPDEWindow244 hH3 M τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (M (v k) / 4)) ∧
      (∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        M (v k) ^ 2 < 384 * K (v k) * C (v k) *
            (((N (v k) : ℝ) + 2) ^ 5 + ((v k : ℝ) + 2) ^ 5) + 8 ∨
        M (v k) ^ 2 < 576 * C (v k) ^ 2 *
            (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 8) ∧
      (∀ S : ℝ, 0 ≤ S → ∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        S < C (v k) ∨
        M (v k) ^ 2 < 8 *
          (S * h3PathFiniteAnnulusPDELinearGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) +
           S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSummable, hBarrier⟩ :=
    thirdFullPhysical_noH3Trace_profileTerminalClock_or_quadraticPDERate244
      hH3 hClass b hb hNoTrace hDInt M hM hMTop
  have hKC (k : ℕ) : 0 ≤ K (v k) ∧ 0 ≤ C (v k) := by
    rcases hWindows k with
      ⟨_, hK, hC, _, _, _, _, _, _, _, _, _, _⟩
    exact ⟨hK, hC⟩
  refine ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    hWindows, hSummable, ?_, ?_⟩
  · filter_upwards [hBarrier] with k hk
    rcases hk with hClock | hRate
    · exact Or.inl hClock
    · have hR : (1 : ℝ) ≤ (v k : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
        linarith only [hn]
      have hQ : (1 : ℝ) ≤ (N (v k) : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (N (v k) : ℝ) := Nat.cast_nonneg _
        linarith only [hn]
      have hSplit := thirdFull_quadraticPDESum_forces_quinticOrEighth244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
        (K (v k)) (C (v k)) (M (v k))
        hR hQ (hKC k).1 (hKC k).2 hRate
      have hRewriteR : (((v k : ℝ) + 1) + 1) = (v k : ℝ) + 2 := by ring
      have hRewriteQ : (((N (v k) : ℝ) + 1) + 1) =
          (N (v k) : ℝ) + 2 := by ring
      exact Or.inr (by
        simpa only [hRewriteR, hRewriteQ] using hSplit)
  · intro S hS
    filter_upwards [hBarrier] with k hk
    rcases hk with hClock | hRate
    · exact Or.inl hClock
    · exact Or.inr
        (thirdFull_quadraticPDESum_forces_sourceOrSpectralGains244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (K (v k)) (C (v k)) S (M (v k))
          (hKC k).1 (hKC k).2 hS hRate)

end
end PrimeTensor.FirstMonomialTriad
