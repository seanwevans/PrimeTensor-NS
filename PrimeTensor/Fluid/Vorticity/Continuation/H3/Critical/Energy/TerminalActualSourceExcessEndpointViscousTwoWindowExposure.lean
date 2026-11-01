import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousSummability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorPhysicalExposure244
import Mathlib.Tactic

/-!
# Actual physical H³ mass exposure on the two synchronized terminal window families

The same cofinal fivefold observations carry the exact physical PDE alternatives
and two distinct types of strictly separated source / internal endpoint windows.
Under an explicit finite terminal physical H³ dissipation integral, we now
charge the FULL physical dissipation integrals on both families, not merely
height times width. Each full-mass series is summable and tends to zero.

The two families can overlap for the same index; they each cost at most the
whole terminal integral, but their costs must NOT be added as if disjoint.
The internal interval may have zero width when no endpoint spike occurs.
The optional vanishing *normalized exposure time* requires the endpoint
threshold heights to diverge and is not used to claim uniform continuity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The ENTIRE mass of a nonnegative integrable physical time density over
pairwise separated, possibly degenerate, subintervals is summable. The
integral of each interval therefore vanishes as the index grows, and every
finite collection has the same enclosing real-integral bound. -/
theorem h3Critical_disjointPhysicalWindow_fullMassCollapse
    (f : ℝ → ℝ) (a T : ℝ) (p η : ℕ → ℝ)
    (haT : a ≤ T)
    (hf : ∀ r : ℝ, 0 ≤ f r)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k : ℕ, a ≤ p k)
    (hWidth : ∀ k : ℕ, 0 ≤ η k)
    (hEnd : ∀ k : ℕ, p k + η k ≤ T)
    (hSeparate : ∀ k : ℕ, p k + η k ≤ p (k + 1)) :
    Summable (fun k : ℕ => ∫ r in p k..(p k + η k), f r) ∧
    Tendsto (fun k : ℕ => ∫ r in p k..(p k + η k), f r)
      atTop (𝓝 (0 : ℝ)) ∧
    (∀ m : ℕ,
      (∑ k ∈ Finset.range m, ∫ r in p k..(p k + η k), f r) ≤
        ∫ r in a..T, f r) := by
  have hSum : Summable (fun k : ℕ =>
      ∫ r in p k..(p k + η k), f r) :=
    h3Path_disjointNonnegativeWindows_fullIntegral_summable244
      f a T p η haT hf hInt hStart hWidth hEnd hSeparate
  have hBound := h3Path_disjointNonnegativeWindows_finiteIntegralSum_le244
    f a T p η haT hf hInt hStart hWidth hEnd hSeparate
  exact ⟨hSum, hSum.tendsto_atTop_zero, hBound⟩

/-- A genuine physical dissipation integral mass, normalized by a diverging
positive comparison height, has vanishing exposure time. No persistence
comparison of full dissipation against its value at a maximizing time is
used in this calculation. -/
theorem h3Critical_disjointPhysicalWindow_divergingHeight_exposureCollapse
    (f : ℝ → ℝ) (a T : ℝ) (p η H : ℕ → ℝ)
    (haT : a ≤ T)
    (hf : ∀ r : ℝ, 0 ≤ f r)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k : ℕ, a ≤ p k)
    (hWidth : ∀ k : ℕ, 0 ≤ η k)
    (hEnd : ∀ k : ℕ, p k + η k ≤ T)
    (hSeparate : ∀ k : ℕ, p k + η k ≤ p (k + 1))
    (hTall : Tendsto H atTop atTop) :
    Tendsto (fun k : ℕ =>
      (∫ r in p k..(p k + η k), f r) / H k)
        atTop (𝓝 (0 : ℝ)) := by
  have hSum := h3Path_disjointNonnegativeWindows_fullIntegral_summable244
    f a T p η haT hf hInt hStart hWidth hEnd hSeparate
  have hNonneg (k : ℕ) :
      0 ≤ ∫ r in p k..(p k + η k), f r :=
    intervalIntegral.integral_nonneg
      (le_add_of_nonneg_right (hWidth k)) (fun r _ => hf r)
  exact h3Path_scalar_summableMass_divergingHeight_exposureCollapse244
    (fun k => ∫ r in p k..(p k + η k), f r)
    H hSum hNonneg hTall

/-- For the SAME selected fivefold highpass-source peaks and attained source
and spectral maxima, the actual full physical H³ dissipation has TWO
summable series of window integrals. The original fivefold windows and the
internally persisted endpoint-spike windows are each disjoint across indices,
but can overlap one another within an index. Thus their two separate real
bounds are NOT combined into a single double-budget claim.

The original exact synchronized PDE-clock alternatives remain attached to
these same witnesses. An optional diverging endpoint threshold additionally
forces the ratio of the endpoint internal integral to that height to vanish.
No global regularity or terminal trace is inferred. -/
theorem h3Critical_noL2Trace_cofinalFivefold_fullPhysicalTwoWindowExposureCollapse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n)
    (R ε : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hε : ∀ k, 0 < ε k)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + w (v k) < t (v l)) ∧
      (∀ k l : ℕ, k < l → p k + η k < p l) ∧
      Summable (fun k : ℕ =>
        ∫ r in t (v k)..(t (v k) + w (v k)), velocityH3DissipationAt u r) ∧
      Summable (fun k : ℕ =>
        ∫ r in p k..(p k + η k), velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in t (v k)..(t (v k) + w (v k)), velocityH3DissipationAt u r)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in p k..(p k + η k), velocityH3DissipationAt u r)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ∫ r in t (v k)..(t (v k) + w (v k)),
            velocityH3DissipationAt u r) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ∫ r in p k..(p k + η k), velocityH3DissipationAt u r) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (Tendsto (fun k : ℕ => R k ^ 2 * ε k ^ 2 / 8) atTop atTop →
        Tendsto (fun k : ℕ =>
          (∫ r in p k..(p k + η k), velocityH3DissipationAt u r) /
            (R k ^ 2 * ε k ^ 2 / 8)) atTop (𝓝 (0 : ℝ))) ∧
      (∀ k : ℕ,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, A, B, δ, p, η, N,
      hv, hLimit, hSourceSep, _hShortSep, hInternalSep,
      _hOldHeightCosts, _hEndpointHeightCosts, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε
  have hGeometry (k : ℕ) :
      a ≤ t (v k) ∧ 0 ≤ w (v k) ∧ t (v k) + w (v k) ≤ T ∧
      a ≤ p k ∧ 0 ≤ η k ∧ p k + η k ≤ T := by
    obtain ⟨ht, hw, hEnd, _hPeaks, _hsSource, _hsState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      hp, hη, hpEnd, _hSpike, _hZero⟩ := hWindows k
    have hta : a ≤ t (v k) :=
      le_of_lt (lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1))
    exact ⟨hta, hw.le, hEnd.le, hta.trans hp, hη,
      hpEnd.trans hEnd.le⟩
  have hNonneg (r : ℝ) : 0 ≤ velocityH3DissipationAt u r :=
    velocityH3DissipationAt_nonneg u r
  obtain ⟨hSourceSum, hSourceZero, hSourceBudget⟩ :=
    h3Critical_disjointPhysicalWindow_fullMassCollapse
      (velocityH3DissipationAt u) a T
      (fun k => t (v k)) (fun k => w (v k))
      hClass.terminal_start.2.le hNonneg hDInt
      (fun k => (hGeometry k).1)
      (fun k => (hGeometry k).2.1)
      (fun k => (hGeometry k).2.2.1)
      (fun k => (hSourceSep k (k + 1) (Nat.lt_succ_self k)).le)
  obtain ⟨hInternalSum, hInternalZero, hInternalBudget⟩ :=
    h3Critical_disjointPhysicalWindow_fullMassCollapse
      (velocityH3DissipationAt u) a T p η
      hClass.terminal_start.2.le hNonneg hDInt
      (fun k => (hGeometry k).2.2.2.1)
      (fun k => (hGeometry k).2.2.2.2.1)
      (fun k => (hGeometry k).2.2.2.2.2)
      (fun k => (hInternalSep k (k + 1) (Nat.lt_succ_self k)).le)
  have hNormalized
      (hTall : Tendsto (fun k : ℕ => R k ^ 2 * ε k ^ 2 / 8) atTop atTop) :
      Tendsto (fun k : ℕ =>
        (∫ r in p k..(p k + η k), velocityH3DissipationAt u r) /
          (R k ^ 2 * ε k ^ 2 / 8)) atTop (𝓝 (0 : ℝ)) := by
    exact h3Critical_disjointPhysicalWindow_divergingHeight_exposureCollapse
      (velocityH3DissipationAt u) a T p η
      (fun k => R k ^ 2 * ε k ^ 2 / 8)
      hClass.terminal_start.2.le hNonneg hDInt
      (fun k => (hGeometry k).2.2.2.1)
      (fun k => (hGeometry k).2.2.2.2.1)
      (fun k => (hGeometry k).2.2.2.2.2)
      (fun k => (hInternalSep k (k + 1) (Nat.lt_succ_self k)).le)
      hTall
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hSourceSep, hInternalSep,
    hSourceSum, hInternalSum, hSourceZero, hInternalZero,
    hSourceBudget, hInternalBudget, hNormalized, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
