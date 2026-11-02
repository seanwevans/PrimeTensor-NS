import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousCutoffEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropQuarticPhysicalClock
import Mathlib.Tactic

/-!
# Explicit eighth-power frequency cost of a captured terminal H³ viscous spike

The physical kinetic ceiling for the low radial viscous dissipation at cutoff
Q is Q² W₃(Q) E₀, where W₃(Q)=1+Q²+Q⁴+Q⁶. The existing quartic-clock
polynomial inequality gives W₃(Q) ≤ 4 Q⁶ when Q ≥ 1. Therefore a strictly
positive finite-band endpoint spike of height H captured at Q=N+1 obeys

  H ≤ 4 E₀ (N+1)^8.

This yields a pointwise lower requirement on its capturing frequency: an
active spike exceeding the kinetic polynomial ceiling at a proposed cutoff
L cannot be captured by any N≤L. It is more quantitative than an eventual
escape statement and needs no terminal full-H³ integrability.

The eighth power concerns the amplitude of H³ *dissipation* at a fixed
frequency. It is NOT the quartic PDE temporal clock, and it gives no lower
bound on a physical persistence interval. Thus this result does not close
terminal regularity or replace the other physical PDE alternatives.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact fixed-radius H³ kinetic ceiling, converted into an eighth-power
frequency bound with the already-proved radial polynomial inequality. -/
theorem h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower
    (Q E H : ℝ) (hQ : 1 ≤ Q) (hE : 0 ≤ E)
    (hCeiling :
      H ≤ Q ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling Q * E)) :
    H ≤ 4 * E * Q ^ 8 := by
  have hWeight := h3Critical_quarticClock_radialWeight_le_fourSixth Q hQ
  have hMul := mul_le_mul_of_nonneg_right hWeight hE
  have hBound := mul_le_mul_of_nonneg_left hMul (sq_nonneg Q)
  calc
    H ≤ Q ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling Q * E) := hCeiling
    _ ≤ Q ^ 2 * ((4 * Q ^ 6) * E) := hBound
    _ = 4 * E * Q ^ 8 := by ring

/-- The actual physical low-frequency dissipation captured at N+1 cannot
exceed the eighth-power kinetic ceiling at the same cutoff. -/
theorem h3Critical_physicalActiveCutoff_eighthPowerCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (N : ℕ → ℕ) (η H : ℕ → ℝ)
    (hs : ∀ k : ℕ, s k ∈ Set.Ioo b T)
    (hActiveFloor : ∀ k : ℕ, η k ≠ 0 →
      H k ≤ h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (s k))) :
    ∀ k : ℕ, η k ≠ 0 →
      H k ≤ 4 * velocityH3Energy0At u b * ((N k : ℝ) + 1) ^ 8 := by
  intro k hActive
  have hKinetic := h3Path_actualLowRadialDissipation_le_kineticAnchor244
    hH3 hClass b hb ((N k : ℝ) + 1) (by positivity) (s k) (hs k)
  have hFloor := (hActiveFloor k hActive).trans hKinetic
  exact h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower
    ((N k : ℝ) + 1) (velocityH3Energy0At u b) (H k)
    (by
      have hn : (0 : ℝ) ≤ (N k : ℝ) := Nat.cast_nonneg _
      linarith only [hn])
    (velocityH3Energy0At_nonneg u b) hFloor

/-- If a captured spike is taller than the kinetic ceiling at proposed
cutoff L, either its interval is inactive or its actual capturing cutoff
must be strictly larger than L. This works at EACH selected index. -/
theorem h3Critical_scalar_eighthPowerBarrier_forcesHigherCutoff
    (N L : ℕ → ℕ) (η H : ℕ → ℝ) (E : ℝ)
    (hE : 0 ≤ E)
    (hCaptured : ∀ k : ℕ, η k ≠ 0 →
      H k ≤ 4 * E * ((N k : ℝ) + 1) ^ 8) :
    ∀ k : ℕ, 4 * E * ((L k : ℝ) + 1) ^ 8 < H k →
      η k = 0 ∨ L k < N k := by
  intro k hTall
  by_cases hZero : η k = 0
  · exact Or.inl hZero
  · right
    by_contra hNot
    have hNk : N k ≤ L k := Nat.le_of_not_gt hNot
    have hCast : (N k : ℝ) ≤ (L k : ℝ) := by exact_mod_cast hNk
    have hRadius : (N k : ℝ) + 1 ≤ (L k : ℝ) + 1 := by
      linarith only [hCast]
    have hPow : ((N k : ℝ) + 1) ^ 8 ≤ ((L k : ℝ) + 1) ^ 8 :=
      pow_le_pow_left₀ (by positivity) hRadius 8
    have hFactor : 0 ≤ 4 * E := mul_nonneg (by norm_num) hE
    have hCompare := mul_le_mul_of_nonneg_left hPow hFactor
    have hCapture := hCaptured k hZero
    linarith only [hTall, hCapture, hCompare]

/-- Pointwise frequency-height obstruction on the SAME cofinal source
windows, source maxima, spectral maxima and physical PDE four-way gate.
No new selection is made. A proposed cutoff profile L is excluded for
active internal persistence precisely when its eighth-power kinetic
ceiling falls below the physical spike threshold. -/
theorem h3Critical_noL2Trace_cofinalFivefold_polynomialCutoffBarrier
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
    (L : ℕ → ℕ) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ, η k ≠ 0 →
        R k ^ 2 * ε k ^ 2 / 8 ≤
          4 * velocityH3Energy0At u b * ((N k : ℝ) + 1) ^ 8) ∧
      (∀ k : ℕ,
        4 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
          R k ^ 2 * ε k ^ 2 / 8 →
        η k = 0 ∨ L k < N k) ∧
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
      hv, hLimit, _hSep, _hShortSep, _hInternalSep,
      _hSourceCost, _hInternalCost, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε
  have hpTail (k : ℕ) : p k ∈ Set.Ioo b T := by
    obtain ⟨ht, _hw, hEnd, _hPeak, _hS, _hState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      hp, hη, hpEnd, _hSpike, _hZero⟩ := hWindows k
    have htb : b < t (v k) := lt_trans (hc (v k)).1 ht.1
    exact ⟨lt_of_lt_of_le htb hp,
      lt_of_le_of_lt
        (le_trans (le_add_of_nonneg_right hη) hpEnd) hEnd⟩
  have hActiveFloor (k : ℕ) (hActive : η k ≠ 0) :
      R k ^ 2 * ε k ^ 2 / 8 ≤
        h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (p k)) := by
    obtain ⟨_ht, _hw, _hEnd, _hPeak, _hS, _hState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      _hp, hη, _hpEnd, hSpike, hZero⟩ := hWindows k
    have hAtMax : R k ^ 2 * ε k ^ 2 <
        8 * velocityH3DissipationAt u (sState k) := by
      by_contra hNot
      exact hActive (hZero hNot)
    have hMem : p k ∈ Set.Icc (p k) (p k + η k) :=
      ⟨le_rfl, le_add_of_nonneg_right hη⟩
    exact ((hSpike hAtMax).2 (p k) hMem).1.le
  have hCeiling := h3Critical_physicalActiveCutoff_eighthPowerCeiling
    hH3 hClass b hb p N η
      (fun k => R k ^ 2 * ε k ^ 2 / 8) hpTail hActiveFloor
  have hBarrier := h3Critical_scalar_eighthPowerBarrier_forcesHigherCutoff
    N L η (fun k => R k ^ 2 * ε k ^ 2 / 8)
    (velocityH3Energy0At u b) (velocityH3Energy0At_nonneg u b) hCeiling
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hCeiling, hBarrier, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
