import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnchoredPDEClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Arbitrary-height actual PDE clocks and disjoint viscous charges

No-H³-trace produces a cofinal diagonal of genuine finite-annulus H³ viscous
persistence windows. Unlike continuity-only windows, each selected width is
EXACTLY the minimum of the half-terminal clock and the linear/quadratic
physical source-rate gap. Under the additional full-H³-dissipation L¹
assumption, a separated subsequence has summable physical height-width cost.
The actual PDE coefficient and clock information are retained on this same
subsequence, so rate/clock rigidity can be analyzed without changing witnesses.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeProfileAnchoredSum244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact PDE-anchored witness data at the natural n+1 Fourier radius. -/
def ThirdFullProfileAnchoredPDEWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (K C δ : ℕ → ℝ) (n : ℕ) : Prop :=
  n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧ 0 < δ n ∧ δ n ≤ 1 ∧
  τ n + δ n < T ∧
  (∀ j : Fin 3,
    ‖(h3AuditActualSpectralVelocityTotal hH3 (τ n)) j‖ ≤ K n) ∧
  (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
    ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C n) ∧
  (M n / 2 < h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
    (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
  δ n = thirdFullProfileAnchoredPDEWidth244 hH3
    (τ n) n (N n) (K n) (C n) (M n) ∧
  (h3PathFiniteAnnulusPDEVariationCoefficient244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) * δ n +
    h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n) * (δ n) ^ 2 <
    (h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n))) - M n / 4) ∧
  (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
    M n / 4 < h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
  (δ n * (M n / 4) ≤ ∫ s in τ n..(τ n + δ n),
    h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s))

/-- No strong H³ endpoint trace requires genuine polynomial PDE windows at
any prescribed POSITIVE height profile. Their exact clock formula and both
actual physical PDE rate coefficients survive the selection of witnesses. -/
theorem thirdFullPhysical_noH3Trace_profileAnchoredPDEWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo b T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, ThirdFullProfileAnchoredPDEWindow244 hH3
        M τ N K C δ n) := by
  obtain ⟨τ, hτ, _hDist, hLimit, hHigh, _hFull⟩ :=
    thirdFullPhysical_noH3Trace_arbitraryViscousHeightDiagonal244
      hH3 hClass b hb hNoTrace M
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ τ n + δ < T ∧
      (∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 (τ n)) j‖ ≤ K) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C) ∧
      (M n / 2 < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (δ = thirdFullProfileAnchoredPDEWidth244 hH3
        (τ n) n N K C (M n)) ∧
      (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C * δ +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C * δ ^ 2 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) - M n / 4) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        M n / 4 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (δ * (M n / 4) ≤ ∫ s in τ n..(τ n + δ),
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
    exact thirdFullPhysical_highRadialSnapshot_profileAnchoredPDEClock244
      hH3 hClass (τ n) ht n (M n) (hM n) (hHigh n)
  choose N K C δ hData using hChoice
  refine ⟨τ, N, K, C, δ, hτ, hLimit, ?_⟩
  intro n
  exact hData n

/-- Preserve exactly the same anchored PDE clocks when extracting disjoint
terminal windows. Under finite physical H³ dissipation their real viscous
charges are bounded by the total endpoint dissipation integral. -/
theorem thirdFullPhysical_noH3Trace_disjointProfileAnchoredPDECharges244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullProfileAnchoredPDEWindow244 hH3 M τ N K C δ (v k)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * (M (v k) / 4)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hWindows⟩ :=
    thirdFullPhysical_noH3Trace_profileAnchoredPDEWindows244
      hH3 hClass b hb hNoTrace M hM
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hWindows n with ⟨_, _, _, hpos, _, _, _, _, _, _, _, _, _⟩
    exact hpos
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hWindows n with ⟨_, _, _, _, _, hend, _, _, _, _, _, _, _⟩
    exact hend
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  have hFloorFull (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      M (v k) / 4 ≤ velocityH3DissipationAt u r := by
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le (lt_trans hb.1 (hTime (v k)).1) hr.1,
        lt_of_le_of_lt hr.2 (hEnd (v k))⟩
    have hData := hWindows (v k)
    rcases hData with ⟨_, _, _, _, _, _, _, _, _, _, _, hFloor, _⟩
    exact (hFloor r hr).le.trans
      (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r hrClass ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1))
  have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
    (velocityH3DissipationAt u) a T
    (fun k => τ (v k)) (fun k => δ (v k))
    (fun k => M (v k) / 4)
    hClass.terminal_start.2.le
    (fun r => velocityH3DissipationAt_nonneg u r)
    hDInt
    (fun k => (lt_trans hb.1 (hTime (v k)).1).le)
    (fun k => (hδ (v k)).le)
    (fun k => (hEnd (v k)).le)
    (fun k => (hSeparated k (k + 1) (Nat.lt_succ_self k)).le)
    hFloorFull
  exact ⟨τ, N, K, C, δ, v, hMono, hCofinal, hSeparated,
    (fun k => ⟨hTime (v k), hWindows (v k)⟩), hSum⟩

end
end PrimeTensor.FirstMonomialTriad
