import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorUnconditionalInnerHigherEscape244
import Mathlib.Tactic

/-!
# Canonical H³ inner-cutoff higher radial escape on full PDE persistence windows

On every point of the ORIGINAL canonical interval, the proven annular low-Q
physical PDE persistence supplies a half-cubic real dissipation floor outside
the inner radius R=v(k)+1. The physical full-to-top comparison and the
existing extended higher-radial coercivity theorem transfer that floor to
EVERY physical q^(4+m) extended moment, without time regularity of such
moments and WITHOUT a noncollapsing delta_k D_k assumption.

The resulting escape is uniform across each entire original window in the
order-theoretic sense: for each fixed m and real B, all sufficiently late
windows have moment >= ofReal B at EVERY time in the window.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Annular persistence at a genuine physical time transfers to the
existing extended top-order q^(4+m) moment above the inner cutoff.
There is no extra assumption that this extended moment is finite. -/
theorem h3Path_physicalHalfAnnulus_forces_windowTopHigherMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s : ℝ) (hs : s ∈ Set.Ioo a T)
    (m : ℕ) (R Q : ℝ) (hR : 1 ≤ R)
    (hAnnulus : R ^ 3 / 2 <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 s)) :
    ENNReal.ofReal ((R ^ 2) ^ m * (R ^ 3 / 8)) ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass m s hs := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 s
  have hRPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass s hs R
  have hQPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass s hs Q
  have hQNonneg : 0 ≤ h3PathActualHighRadialDissipation244 Q G := by
    unfold h3PathActualHighRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  have hInner := h3Path_scalar_annulus_le_innerHighTail244
    (h3PathActualLowRadialDissipation244 R G)
    (h3PathActualLowRadialDissipation244 Q G)
    (h3PathActualHighRadialDissipation244 R G)
    (h3PathActualHighRadialDissipation244 Q G)
    (velocityH3DissipationAt u s) hRPart hQPart hQNonneg
  have hTail : R ^ 3 / 2 ≤ h3PathActualHighRadialDissipation244 R G :=
    (lt_of_lt_of_le hAnnulus hInner).le
  have hQuarter : R ^ 3 / 8 ≤
      h3PathActualHighRadialDissipation244 R G / 4 := by
    linarith only [hTail]
  have hScaled := mul_le_mul_of_nonneg_left hQuarter
    (pow_nonneg (sq_nonneg R) m)
  have hMoment := h3Path_physicalHighTail_forces_topHigherRadialMoment244
    hH3 hClass s hs m R hR
  exact (ENNReal.ofReal_le_ofReal hScaled).trans hMoment

/-- A growing cubic radial floor forces every additional nonnegative
polynomial frequency weight past any prescribed real threshold. -/
theorem h3Path_scalar_cubicWindowMoment_eventually_above244
    (R : ℕ → ℝ) (hR : ∀ k, 1 ≤ R k)
    (hRadius : Tendsto (fun k => R k ^ 3) atTop atTop)
    (m : ℕ) (B : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      B ≤ ((R k) ^ 2) ^ m * ((R k) ^ 3 / 8) := by
  have hScaled : Tendsto (fun k => R k ^ 3 / 8) atTop atTop := by
    have h := hRadius.const_mul_atTop
      (show (0 : ℝ) < 1 / 8 by norm_num)
    convert h using 1
    funext k
    ring
  have hEventually : ∀ᶠ k : ℕ in atTop, B ≤ R k ^ 3 / 8 :=
    hScaled.eventually (eventually_ge_atTop B)
  filter_upwards [hEventually] with k hk
  have hSquare : (1 : ℝ) ≤ (R k) ^ 2 := by
    have h := pow_le_pow_left₀
      (by norm_num : (0 : ℝ) ≤ 1) (hR k) 2
    simpa only [one_pow] using h
  have hPower : (1 : ℝ) ≤ ((R k) ^ 2) ^ m := by
    have h := pow_le_pow_left₀
      (by norm_num : (0 : ℝ) ≤ 1) hSquare m
    simpa only [one_pow] using h
  have hCubic : 0 ≤ (R k) ^ 3 / 8 := by
    have hNonneg : 0 ≤ R k := le_trans (by norm_num) (hR k)
    exact div_nonneg (pow_nonneg hNonneg 3) (by norm_num)
  have hMultiply : (R k) ^ 3 / 8 ≤
      ((R k) ^ 2) ^ m * ((R k) ^ 3 / 8) := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hPower hCubic)
  exact hk.trans hMultiply

/-- The SAME canonical first-crossing annular PDE clocks force the
physical extended top-order higher-radial moments to grow uniformly over
EVERY point of EVERY sufficiently late original window. This is strictly
stronger than the previous anchor-only escape: the time inside each
window may be chosen arbitrarily, and no continuity of higher moments or
persistent anchor-height charge is introduced. -/
theorem h3Path_noL2Trace_exactAnchor_uniformWindowTopHigherEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ m k : ℕ, ∀ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
        ∃ hs : s ∈ Set.Ioo a T,
          ENNReal.ofReal (((((v k : ℝ) + 1) ^ 2) ^ m) *
            (((v k : ℝ) + 1) ^ 3 / 8)) ≤
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs) ∧
      (∀ m : ℕ, ∀ B : ℝ,
        ∀ᶠ k : ℕ in atTop,
          ∀ s : ℝ,
            s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
            ∃ hs : s ∈ Set.Ioo a T,
              ENNReal.ofReal B ≤
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass m s hs) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, _hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hK (k : ℕ) :
      K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ :=
    (hAll k).1
  have hC (k : ℕ) : C (v k) = h3PathActualProjectedSourceWindowEnvelope244
      hH3 (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) := by
    rcases hAll k with ⟨_, _, _, _, hc, _, _, _, _, _, _, _⟩
    exact hc
  have hWidth (k : ℕ) : 0 < δ (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, hp, _, _, _, _, _⟩
    exact hp
  have hEnd (k : ℕ) : τ (v k) + δ (v k) < T := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, he, _, _, _, _⟩
    exact he
  have hWindow (m k : ℕ) (s : ℝ)
      (hsWindow : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      ∃ hs : s ∈ Set.Ioo a T,
        ENNReal.ofReal (((((v k : ℝ) + 1) ^ 2) ^ m) *
          (((v k : ℝ) + 1) ^ 3 / 8)) ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass m s hs := by
    have hsTime : s ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le (hTime (v k)).1 hsWindow.1,
        lt_of_le_of_lt hsWindow.2 (hEnd k)⟩
    have hAnn : (((v k : ℝ) + 1) ^ 3) / 2 <
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
      rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, hp, _, _⟩
      exact hp s hsWindow
    have hR : (1 : ℝ) ≤ (v k : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    exact ⟨hsTime,
      h3Path_physicalHalfAnnulus_forces_windowTopHigherMoment244
        hH3 hClass s hsTime m ((v k : ℝ) + 1)
          ((N (v k) : ℝ) + 1) hR hAnn⟩
  have hRadius : Tendsto
      (fun k => ((v k : ℝ) + 1) ^ 3) atTop atTop :=
    h3Path_strictMono_canonicalRadiusCube_escape244 v hv
  refine ⟨τ, N, K, C, δ, v, hTime, hv, hCofinal,
    hSeparate, ?_, hWindow, ?_⟩
  · intro k
    exact ⟨hK k, hC k, hWidth k⟩
  · intro m B
    have hR : ∀ k, (1 : ℝ) ≤ (v k : ℝ) + 1 := by
      intro k
      have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hLate := h3Path_scalar_cubicWindowMoment_eventually_above244
      (fun k => (v k : ℝ) + 1) hR hRadius m B
    filter_upwards [hLate] with k hk
    intro s hsWindow
    obtain ⟨hs, hsBound⟩ := hWindow m k s hsWindow
    exact ⟨hs, (ENNReal.ofReal_le_ofReal hk).trans hsBound⟩

end
end PrimeTensor.FirstMonomialTriad
