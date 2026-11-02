import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAdaptiveBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousSynchronizedGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFixedFrequencyDissipationEvacuation244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralKineticAnchoredLowDissipationBudget244
import Mathlib.Tactic

/-!
# Physical kinetic-anchor ceilings force the active endpoint cutoff to escape

The previous finite H³-budget results constrain how long endpoint high-dissipation
spikes persist. They do not force a lower persistence width. This module takes a
DIFFERENT, genuinely spectral consequence from the *existing physical kinetic
energy ceiling*: for every FIXED finite radial frequency, the low-band H³
viscous dissipation is uniformly bounded over the strict physical tail.

If the selected endpoint threshold R(k)^2 ε(k)^2 / 8 grows without bound,
a nonzero internal persistence window requires its own finite-band cutoff N(k)
to eventually exceed EVERY fixed integer bound. No continuity of full H³
dissipation, terminal-uniform temporal modulus, or integrability of terminal
full H³ dissipation is used here.

An active cutoff may diverge arbitrarily rapidly; this does not settle the
non-spectral, physical PDE-clock, or anchor-dissipation alternatives.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A height diverging to +∞ cannot be met by infinitely late active
indices whose cutoff stays below a fixed threshold with finite ceiling. -/
theorem h3Critical_scalar_activeCutoff_escape_of_divergingHeight
    (N : ℕ → ℕ) (η H : ℕ → ℝ) (C : ℕ → ℝ)
    (hTall : Tendsto H atTop atTop)
    (hFixedCeiling : ∀ (m k : ℕ), N k ≤ m → η k ≠ 0 → H k ≤ C m) :
    ∀ m : ℕ, ∀ᶠ k : ℕ in atTop, η k = 0 ∨ m < N k := by
  intro m
  have hLarge : ∀ᶠ k : ℕ in atTop, C m < H k := by
    have hAbove := (tendsto_atTop.1 hTall) (C m + 1)
    filter_upwards [hAbove] with k hk
    linarith only [hk]
  filter_upwards [hLarge] with k hk
  by_cases hZero : η k = 0
  · exact Or.inl hZero
  · right
    by_contra hNot
    have hBound : N k ≤ m := Nat.le_of_not_gt hNot
    have hCeil := hFixedCeiling m k hBound hZero
    linarith only [hk, hCeil]

/-- The kinetic-energy anchor bounds every fixed low-radial dissipation band.
Consequently, if a moving finite band must pay a diverging physical
viscous height at an active time, its cutoff escapes all fixed radii.
Inactive slots remain allowed, exactly as in the synchronized gate. -/
theorem h3Critical_physicalActiveFiniteBandCutoff_escape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (N : ℕ → ℕ) (η H : ℕ → ℝ)
    (hs : ∀ k : ℕ, s k ∈ Set.Ioo b T)
    (hTall : Tendsto H atTop atTop)
    (hActiveFloor : ∀ k : ℕ, η k ≠ 0 →
      H k ≤ h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (s k))) :
    ∀ m : ℕ, ∀ᶠ k : ℕ in atTop, η k = 0 ∨ m < N k := by
  let C : ℕ → ℝ := fun m =>
    ((m : ℝ) + 1) ^ 2 *
      (h3TerminalRadialSobolevWeightSquareCeiling ((m : ℝ) + 1) *
        velocityH3Energy0At u b)
  have hFixedCeiling (m k : ℕ) (hBound : N k ≤ m)
      (hActive : η k ≠ 0) : H k ≤ C m := by
    have hCast : (N k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hBound
    have hRadius : (N k : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      linarith only [hCast]
    have hsClass : s k ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hs k).1, (hs k).2⟩
    have hMono := h3Path_actualLowRadialDissipation_mono_radius244
      hH3 hClass (s k) hsClass hRadius
    have hKinetic := h3Path_actualLowRadialDissipation_le_kineticAnchor244
      hH3 hClass b hb ((m : ℝ) + 1) (by positivity) (s k) (hs k)
    exact (hActiveFloor k hActive).trans (hMono.trans hKinetic)
  exact h3Critical_scalar_activeCutoff_escape_of_divergingHeight
    N η H C hTall hFixedCeiling

/-- A uniformly bounded finite-band cutoff makes the active endpoint-spike
slots eventually disappear whenever the physical threshold diverges. -/
theorem h3Critical_scalar_activeCutoff_eventuallyZero_of_boundedCutoffs
    (N : ℕ → ℕ) (η : ℕ → ℝ)
    (hEscape : ∀ m : ℕ,
      ∀ᶠ k : ℕ in atTop, η k = 0 ∨ m < N k)
    (M : ℕ) (hBound : ∀ᶠ k : ℕ in atTop, N k ≤ M) :
    ∀ᶠ k : ℕ in atTop, η k = 0 := by
  filter_upwards [hEscape M, hBound] with k hk hNk
  rcases hk with hZero | hLarge
  · exact hZero
  · omega

/-- The EXACT cofinal source windows and attained spectral maxima from the
synchronized gate are retained. If the selected height R(k)^2 ε(k)^2/8
diverges, every active positive-width finite-band endpoint spike forces the
capturing cutoff N(k) beyond every fixed Fourier cutoff. An eventually
bounded capture cutoff therefore removes this spike-persistence branch.

No assumption of terminal full H³-integrability is required; the bound is
instead the existing physical low-band kinetic-energy ceiling. -/
theorem h3Critical_noL2Trace_cofinalFivefold_activeEndpointCutoffEscape
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
    (hTall : Tendsto (fun k : ℕ => R k ^ 2 * ε k ^ 2 / 8) atTop atTop) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ m : ℕ, ∀ᶠ k : ℕ in atTop, η k = 0 ∨ m < N k) ∧
      (∀ K : ℕ, (∀ᶠ k : ℕ in atTop, N k ≤ K) →
        ∀ᶠ k : ℕ in atTop, η k = 0) ∧
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
      _hSourceCosts, _hInternalCosts, hWindows, hGate⟩ :=
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
  have hEscape := h3Critical_physicalActiveFiniteBandCutoff_escape
    hH3 hClass b hb p N η (fun k => R k ^ 2 * ε k ^ 2 / 8)
    hpTail hTall hActiveFloor
  have hBounded (K : ℕ) (hNK : ∀ᶠ k : ℕ in atTop, N k ≤ K) :
      ∀ᶠ k : ℕ in atTop, η k = 0 :=
    h3Critical_scalar_activeCutoff_eventuallyZero_of_boundedCutoffs
      N η hEscape K hNK
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hEscape, hBounded, hGate⟩

end
end PrimeTensor.Bridge.Euclidean
