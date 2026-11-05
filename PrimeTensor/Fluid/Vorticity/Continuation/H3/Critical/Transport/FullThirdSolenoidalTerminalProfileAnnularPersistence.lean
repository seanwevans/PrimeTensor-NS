import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalArbitraryViscousDiagonal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusIntegratedWindows244
import Mathlib.Tactic

/-!
# Arbitrary-height finite-annulus viscous persistence at the physical endpoint

The previous cubic persistence theorem works with the specific height
`(n+1)^3`.  Here the height is an arbitrary STRICTLY POSITIVE real number.
At a genuine physical H³-viscous high-radial snapshot of height greater than
`A`, the dissipation at that fixed time can be localized to a FINITE annulus
with more than three quarters of the requested height.  Continuity of that
finite annular functional yields a positive-width interval on which at least
half of `A` persists.  The real time integral of the same finite annulus pays
its actual positive height-width charge.

Combined with the physical no-H³-terminal-trace arbitrary-height diagonal,
this produces a full family of actual terminal windows at ANY prescribed
positive height profile.  Their widths depend on the profile and the actual
solution; no uniform width estimate or regularity assertion is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalProfileAnnular244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every high-radial dissipation snapshot above a positive *arbitrary*
height admits a finite outer Fourier radius, a strictly positive physical
time width, half-height persistence, and the exact Bochner real-integral
charge. Neither a terminal trace nor a common time-width bound is used. -/
theorem thirdFullPhysical_highRadialSnapshot_profileAnnularWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (A : ℝ) (hA : 0 < A)
    (hHigh : A < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (δ : ℝ), n ≤ N ∧ 0 < δ ∧ t + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        A / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        A / 2 < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * (A / 2) ≤
        (∫ s in t..(t + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hQuarter : 0 < A / 4 := by linarith only [hA]
  have hTail := h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    hH3 hClass t ht
  have hEvent : ∀ᶠ m : ℕ in atTop,
      h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) < A / 4 :=
    hTail.eventually (eventually_lt_nhds hQuarter)
  rw [Filter.eventually_atTop] at hEvent
  obtain ⟨N₀, hN₀⟩ := hEvent
  let N : ℕ := max N₀ n
  have hnN : n ≤ N := le_max_right N₀ n
  have hN₀N : N₀ ≤ N := le_max_left N₀ n
  let Q : ℝ := (N : ℝ) + 1
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hOuter : h3PathActualHighRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 t) < A / 4 := by
    exact hN₀ N hN₀N
  let B : ℝ → ℝ := fun s =>
    h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 s) -
    h3PathActualLowRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s)
  have hPartR := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht R
  have hPartQ := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht Q
  have hAt : 3 * A / 4 < B t := by
    dsimp only [B, R, Q] at hHigh hOuter hPartR hPartQ ⊢
    linarith only [hHigh, hOuter, hPartR, hPartQ]
  have hB : ContinuousOn B (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass R Q hR.le hQ.le
  have hCont : ContinuousAt B t :=
    hB.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hDiffCont : ContinuousAt (fun s => A / 2 - B s) t :=
    continuousAt_const.sub hCont
  have hNegative : A / 2 - B t < 0 := by
    linarith only [hAt, hA]
  obtain ⟨η, hη, hNear⟩ :=
    h3Path_continuousStrictInequality_localWindow244 hDiffCont hNegative
  let δ : ℝ := min (η / 2) ((T - t) / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by linarith only [hη]) (by linarith only [ht.2])
  have hδη : δ ≤ η / 2 := min_le_left _ _
  have hδT : δ ≤ (T - t) / 2 := min_le_right _ _
  have hEnd : t + δ < T := by linarith only [hδT, ht.2]
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → A / 2 < B s := by
    intro s hs
    have hDist : dist s t < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith only [hs.2, hδη, hη]
    have h := hNear s hDist
    linarith only [h]
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hIntegrable : IntervalIntegrable B volume t (t + δ) :=
    (hB.mono hSub).intervalIntegrable_of_Icc (by linarith only [hδ])
  have hCost : ((t + δ) - t) * (A / 2) ≤
      ∫ s in t..(t + δ), B s :=
    h3Path_localPositiveHeight_forces_integratedCost244
      B t (t + δ) (A / 2) (by linarith only [hδ]) hIntegrable
      (fun s hs => (hFloor s hs).le)
  refine ⟨N, δ, hnN, hδ, hEnd, ?_, ?_⟩
  · intro s hs
    have hsClass : s ∈ Set.Ioo a T := hSub hs
    have hPartR := h3Path_actualRadialDissipation_partition244
      hH3 hClass s hsClass R
    have hPartQ := h3Path_actualRadialDissipation_partition244
      hH3 hClass s hsClass Q
    have hHighQ : 0 ≤ h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
      unfold h3PathActualHighRadialDissipation244
      apply integral_nonneg
      intro ξ
      exact h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3AuditActualSpectralVelocityTotal hH3 s) ξ
    have hFloorAt : A / 2 < B s := hFloor s hs
    constructor
    · simpa only [B, R, Q] using hFloorAt
    · dsimp only [B] at hFloorAt
      dsimp only [R, Q] at hFloorAt hPartR hPartQ ⊢
      linarith only [hFloorAt, hPartR, hPartQ, hHighQ]
  · change δ * (A / 2) ≤ ∫ s in t..(t + δ), B s
    calc
      δ * (A / 2) = ((t + δ) - t) * (A / 2) := by ring
      _ ≤ ∫ s in t..(t + δ), B s := hCost

/-- No strong H³ endpoint trace forces positive finite-annulus physical
viscous persistence windows at EVERY positive prescribed height profile.
The same terminal sequence is used for all of the selected windows; each
index is allowed its own finite outer Fourier radius and time width. -/
theorem thirdFullPhysical_noH3Trace_profileFiniteAnnularWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo b T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, n ≤ N n ∧ 0 < δ n ∧ τ n + δ n < T) ∧
      (∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
        M n / 2 <
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        M n / 2 < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ n : ℕ, δ n * (M n / 2) ≤
        ∫ s in τ n..(τ n + δ n),
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨τ, hτ, _hDist, hLimit, hHigh, _hFull⟩ :=
    thirdFullPhysical_noH3Trace_arbitraryViscousHeightDiagonal244
      hH3 hClass b hb hNoTrace M
  have hWindow (n : ℕ) :
      ∃ (N : ℕ) (δ : ℝ), n ≤ N ∧ 0 < δ ∧ τ n + δ < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
          M n / 2 <
            h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) ∧
          M n / 2 < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ * (M n / 2) ≤
          ∫ s in τ n..(τ n + δ),
            h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) := by
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
    exact thirdFullPhysical_highRadialSnapshot_profileAnnularWindow244
      hH3 hClass (τ n) ht n (M n) (hM n) (hHigh n)
  choose N δ hInfo using hWindow
  exact ⟨τ, N, δ, hτ, hLimit,
    (fun n => ⟨(hInfo n).1, (hInfo n).2.1, (hInfo n).2.2.1⟩),
    (fun n s hs => (hInfo n).2.2.2.1 s hs),
    (fun n => (hInfo n).2.2.2.2)⟩

end
end PrimeTensor.FirstMonomialTriad
