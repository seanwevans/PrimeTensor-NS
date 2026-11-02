import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousPolynomialCutoffBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Tactic

/-!
# Physical H³ endpoint spikes force genuine annular spectral dissipation

The active finite-band endpoint witness controls the LOW radial physical
H³ dissipation on its entire internal time window. Its already-established
kinetic anchor also gives a uniform bound on every smaller fixed band.

If the endpoint threshold H exceeds twice the eighth-power kinetic ceiling
of a proposed lower cutoff L, then MORE THAN HALF the threshold must lie
in the actual radial annulus between L and the capturing cutoff N+1.
This annular quantity is bounded by the actual full physical dissipation.

The result is pointwise throughout the SAME selected internal windows,
not merely at the maximizing time, and retains the four-way PDE alternatives.
It needs no integrability of the full terminal H³ dissipation, and it does
not assert a uniform temporal persistence modulus or terminal continuation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A strict high-band floor and a lower-band ceiling force an actual
half-height gap in the difference of the two bands. -/
theorem h3Critical_scalar_twiceLowerBandCeiling_forces_halfAnnularGap
    (low high H C : ℝ)
    (hHigh : H < high)
    (hLow : low ≤ C)
    (hExcess : 2 * C < H) :
    H / 2 < high - low := by
  linarith only [hHigh, hLow, hExcess]

/-- A finite-band physical spike above twice the kinetic ceiling at a
smaller cutoff forces more than half the height into a genuine radial
Fourier annulus. The annular dissipation is paid by actual full H³
viscous dissipation at the same strict physical time. -/
theorem h3Critical_physicalLowRadialSpike_forces_halfHeightAnnulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (hs : s ∈ Set.Ioo b T)
    (L Q H : ℝ) (hL : 1 ≤ L)
    (hSpike : H < h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 s))
    (hThreshold : 8 * velocityH3Energy0At u b * L ^ 8 < H) :
    H / 2 <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 L
        (h3AuditActualSpectralVelocityTotal hH3 s) ∧
    h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 L
        (h3AuditActualSpectralVelocityTotal hH3 s) ≤
      velocityH3DissipationAt u s := by
  have hLowKinetic := h3Path_actualLowRadialDissipation_le_kineticAnchor244
    hH3 hClass b hb L (by linarith only [hL]) s hs
  have hLowCeiling := h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower
    L (velocityH3Energy0At u b)
    (h3PathActualLowRadialDissipation244 L
      (h3AuditActualSpectralVelocityTotal hH3 s))
    hL (velocityH3Energy0At_nonneg u b) hLowKinetic
  have hDouble : 2 * (4 * velocityH3Energy0At u b * L ^ 8) < H := by
    linarith only [hThreshold]
  have hGap := h3Critical_scalar_twiceLowerBandCeiling_forces_halfAnnularGap
    (h3PathActualLowRadialDissipation244 L
      (h3AuditActualSpectralVelocityTotal hH3 s))
    (h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 s))
    H (4 * velocityH3Energy0At u b * L ^ 8)
    hSpike hLowCeiling hDouble
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  exact ⟨hGap,
    h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass s hsClass L Q⟩

/-- Same cofinal fivefold source observations, same attained source and
spectral maxima, same disjoint internal physical windows. If the selected
height is larger than twice the kinetic budget below a proposed cutoff
profile, either the internal window is inactive, or throughout the entire
active interval a genuine positive radial annulus accounts for more than
half the physical H³ spike threshold. Its capturing cutoff must exceed the
proposed cutoff. The four-way source/PDE/spectral alternative is unchanged.
-/
theorem h3Critical_noL2Trace_cofinalFivefold_activeAnnularLocalization
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
      (∀ k : ℕ,
        8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
          R k ^ 2 * ε k ^ 2 / 8 →
        η k = 0 ∨
          (L k < N k ∧
            ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
              R k ^ 2 * ε k ^ 2 / 16 <
                h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 r) -
                h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 r) ∧
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 r) -
                h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 r) ≤
                velocityH3DissipationAt u r)) ∧
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
  have hActiveFloor (k : ℕ) (hActive : η k ≠ 0) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + η k)) :
      R k ^ 2 * ε k ^ 2 / 8 <
        h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
    obtain ⟨_ht, _hw, _hEnd, _hPeak, _hS, _hState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      _hp, _hη, _hpEnd, hSpike, hZero⟩ := hWindows k
    have hAtMax : R k ^ 2 * ε k ^ 2 <
        8 * velocityH3DissipationAt u (sState k) := by
      by_contra hNot
      exact hActive (hZero hNot)
    exact ((hSpike hAtMax).2 r hr).1
  have hTail (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + η k)) :
      r ∈ Set.Ioo b T := by
    obtain ⟨ht, _hw, hEnd, _hPeak, _hS, _hState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      hp, _hη, hpEnd, _hSpike, _hZero⟩ := hWindows k
    have htb : b < t (v k) := lt_trans (hc (v k)).1 ht.1
    exact ⟨lt_of_lt_of_le htb (le_trans hp hr.1),
      lt_of_le_of_lt (le_trans hr.2 hpEnd) hEnd⟩
  have hRadius (k : ℕ) :
      (1 : ℝ) ≤ (L k : ℝ) + 1 := by
    have hNat : (0 : ℝ) ≤ (L k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hAnnulus (k : ℕ) (hActive : η k ≠ 0)
      (hHeight : 8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
        R k ^ 2 * ε k ^ 2 / 8)
      (r : ℝ) (hr : r ∈ Set.Icc (p k) (p k + η k)) :
      R k ^ 2 * ε k ^ 2 / 16 <
        h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) ∧
      h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) ≤
        velocityH3DissipationAt u r := by
    have h := h3Critical_physicalLowRadialSpike_forces_halfHeightAnnulus
      hH3 hClass b hb r (hTail k r hr)
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      (R k ^ 2 * ε k ^ 2 / 8) (hRadius k)
      (hActiveFloor k hActive r hr) hHeight
    constructor
    · have hHalf : (R k ^ 2 * ε k ^ 2 / 8) / 2 =
          R k ^ 2 * ε k ^ 2 / 16 := by ring
      simpa only [hHalf] using h.1
    · exact h.2
  have hEscape (k : ℕ) (hActive : η k ≠ 0)
      (hHeight : 8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
        R k ^ 2 * ε k ^ 2 / 8) : L k < N k := by
    by_contra hNot
    have hNL : N k ≤ L k := Nat.le_of_not_gt hNot
    have hOrder : (N k : ℝ) + 1 ≤ (L k : ℝ) + 1 := by
      have hc : (N k : ℝ) ≤ (L k : ℝ) := by exact_mod_cast hNL
      linarith only [hc]
    obtain ⟨_ht, _hw, _hEnd, _hPeak, _hS, _hState, _hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
      _hp, hη, _hpEnd, _hSpike, _hZero⟩ := hWindows k
    have hpMem : p k ∈ Set.Icc (p k) (p k + η k) :=
      ⟨le_rfl, le_add_of_nonneg_right hη⟩
    have hMono := h3Path_actualLowRadialDissipation_mono_radius244
      hH3 hClass (p k)
      ⟨lt_trans hb.1 (hTail k (p k) hpMem).1,
        (hTail k (p k) hpMem).2⟩ hOrder
    have hGap := (hAnnulus k hActive hHeight (p k) hpMem).1
    have hPos : 0 < R k ^ 2 * ε k ^ 2 / 16 := by
      have hr := hR k
      have he := hε k
      positivity
    linarith only [hMono, hGap, hPos]
  refine ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, ?_, hGate⟩
  intro k hHeight
  by_cases hZero : η k = 0
  · exact Or.inl hZero
  · exact Or.inr ⟨hEscape k hZero hHeight,
      fun r hr => hAnnulus k hZero hHeight r hr⟩

end
end PrimeTensor.Bridge.Euclidean
