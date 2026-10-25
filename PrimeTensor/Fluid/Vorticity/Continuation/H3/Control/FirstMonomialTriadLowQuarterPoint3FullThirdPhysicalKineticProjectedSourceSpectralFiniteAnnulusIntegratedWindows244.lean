import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralLowRadialTemporalContinuity244
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Unconditional finite-annulus temporal persistence of cubic H³ dissipation

At each strict physical time, the exact full spectral H³ dissipation density
is integrable. Therefore its high-radial tail decreases to zero as the outer
cutoff tends to infinity. A cubic high-radial snapshot can consequently be
captured inside a finite annulus (n+1, N+1) without losing more than a
quarter of its height.

The low-cutoff physical H³ dissipation is already known to be continuous
at every positive time. The finite-annulus dissipation is the *difference*
of two such low-cutoff functionals, hence continuous. A positive-width time
window therefore retains half the cubic height throughout the annulus.

This produces a genuine finite-band time integral, without assuming time
continuity or local integrability of the *unbounded* full H³ dissipation.
The latter is still needed to compare the ordinary real high-frequency
interval integral with this finite-band cost.

Under the prior conditional no-strong-physical-L²-trace branch, one and the
same terminal sequence carries all the cubic finite-band windows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3FiniteAnnulus244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3FiniteAnnulus244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At every fixed strict time the FULL actual H³ spectral dissipation
outside natural radial balls tends to zero. This is not uniform in time. -/
theorem h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) :
    Tendsto (fun n : ℕ =>
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) atTop (𝓝 0) := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  let G : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let f : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity G
  let S : ℕ → Set H3FourierPoint3 := fun n =>
    (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ
  have hf : Integrable f volume := by
    dsimp only [f, G]
    exact h3TerminalSpectralDissipationSingleDensity_integrable hH3 hClass ht
  have hSMeas : ∀ n : ℕ, MeasurableSet (S n) := by
    intro n
    dsimp only [S]
    exact (measurableSet_h3TerminalRadialFrequencyBelow ((n : ℝ) + 1)).compl
  have hSAnti : Antitone S := by
    intro m n hmn ξ hξ
    dsimp only [S] at hξ ⊢
    change ¬ h3FourierGradientMagnitude ξ < (n : ℝ) + 1 at hξ
    change ¬ h3FourierGradientMagnitude ξ < (m : ℝ) + 1
    intro hBelow
    apply hξ
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    exact lt_of_lt_of_le hBelow (by linarith only [hmn'])
  have hInter : (⋂ n : ℕ, S n) = (∅ : Set H3FourierPoint3) := by
    ext ξ
    constructor
    · intro hξ
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (h3FourierGradientMagnitude ξ)
      have hAt := Set.mem_iInter.1 hξ N
      dsimp only [S] at hAt
      change ¬ h3FourierGradientMagnitude ξ < (N : ℝ) + 1 at hAt
      exact False.elim (hAt (by linarith only [hN]))
    · intro hξ
      exact False.elim (by simpa using hξ)
  have hConverges :
      Tendsto (fun n : ℕ => ∫ ξ in S n, f ξ ∂volume)
        atTop (𝓝 (∫ ξ in ⋂ n : ℕ, S n, f ξ ∂volume)) :=
    Antitone.tendsto_setIntegral hSMeas hSAnti hf.integrableOn
  rw [hInter] at hConverges
  simpa only [h3PathActualHighRadialDissipation244, S, f, G,
    Measure.restrict_empty, integral_zero_measure] using hConverges

/-- Every cubic actual high-radial witness has a FINITE outer Fourier radius
with at least three-quarters of the cubic height inside the annulus. -/
theorem h3Path_cubicHighSnapshot_has_finiteAnnularHeight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ N : ℕ, n ≤ N ∧
      (3 * (((n : ℝ) + 1) ^ 3)) / 4 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let R : ℝ := (n : ℝ) + 1
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hR : 0 < R := by dsimp only [R]; positivity
  have hQuarter : 0 < R ^ 3 / 4 := by positivity
  have hTail := h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244
    hH3 hClass t ht
  have hEvent : ∀ᶠ m : ℕ in atTop,
      h3PathActualHighRadialDissipation244 ((m : ℝ) + 1) G < R ^ 3 / 4 := by
    exact hTail.eventually (eventually_lt_nhds hQuarter)
  rw [Filter.eventually_atTop] at hEvent
  obtain ⟨N₀, hN₀⟩ := hEvent
  let N : ℕ := max N₀ n
  have hnN : n ≤ N := le_max_right N₀ n
  have hN₀N : N₀ ≤ N := le_max_left N₀ n
  have hOuter : h3PathActualHighRadialDissipation244 ((N : ℝ) + 1) G <
      R ^ 3 / 4 := hN₀ N hN₀N
  have hPartR := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht R
  have hPartN := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht ((N : ℝ) + 1)
  refine ⟨N, hnN, ?_⟩
  dsimp only [R, G] at hOuter hPartR hPartN ⊢
  linarith only [hCube, hOuter, hPartR, hPartN]

/-- A finite annulus is continuous in time from the already-established
low-cutoff multiplier theorem. No unbounded dissipation continuity is used. -/
theorem h3Path_finiteAnnularDissipation_continuousOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R Q : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q) :
    ContinuousOn (fun s : ℝ =>
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T) := by
  exact (h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
    hH3 hClass Q hQ).sub
      (h3Path_actualLowRadialDissipation_continuousOn_positiveTime244
        hH3 hClass R hR)

/-- A high-radial cubic snapshot forces a positive STRICT physical time
window of finite-annulus dissipation, with an automatically integrable
annular function. Both the annular and high-radial pointwise floors hold.
No full H³ dissipation continuity or high-tail time integrability is assumed. -/
theorem h3Path_cubicHighSnapshot_has_integratedFiniteAnnulusWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (δ : ℝ), n ≤ N ∧ 0 < δ ∧ t + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        (∫ s in t..(t + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨N, hnN, hHeight⟩ :=
    h3Path_cubicHighSnapshot_has_finiteAnnularHeight244
      hH3 hClass t ht n hCube
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let B : ℝ → ℝ := fun s =>
    h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 s) -
    h3PathActualLowRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hB : ContinuousOn B (Set.Ioo a T) := by
    exact h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass R Q hR.le hQ.le
  have hAt : 3 * R ^ 3 / 4 < B t := by
    simpa only [B, R, Q] using hHeight
  have hCont : ContinuousAt B t :=
    hB.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hDiffCont : ContinuousAt (fun s => R ^ 3 / 2 - B s) t :=
    continuousAt_const.sub hCont
  have hNegative : R ^ 3 / 2 - B t < 0 := by
    have hCubePos : 0 < R ^ 3 := pow_pos hR 3
    linarith only [hAt, hCubePos]
  obtain ⟨η, hη, hNear⟩ :=
    h3Path_continuousStrictInequality_localWindow244 hDiffCont hNegative
  let δ : ℝ := min (η / 2) ((T - t) / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by linarith only [hη]) (by linarith only [ht.2])
  have hδη : δ ≤ η / 2 := min_le_left _ _
  have hδT : δ ≤ (T - t) / 2 := min_le_right _ _
  have hEnd : t + δ < T := by linarith only [hδT, ht.2]
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → R ^ 3 / 2 < B s := by
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
  have hCost : ((t + δ) - t) * (R ^ 3 / 2) ≤
      ∫ s in t..(t + δ), B s :=
    h3Path_localPositiveHeight_forces_integratedCost244
      B t (t + δ) (R ^ 3 / 2) (by linarith only [hδ]) hIntegrable
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
    have hFloorAt : R ^ 3 / 2 < B s := hFloor s hs
    constructor
    · simpa only [B, R, Q] using hFloorAt
    · dsimp only [B] at hFloorAt
      dsimp only [R, Q] at hFloorAt hPartR hPartQ ⊢
      linarith only [hFloorAt, hPartR, hPartQ, hHighQ]
  · change δ * (R ^ 3 / 2) ≤ ∫ s in t..(t + δ), B s
    calc
      δ * (R ^ 3 / 2) = ((t + δ) - t) * (R ^ 3 / 2) := by ring
      _ ≤ ∫ s in t..(t + δ), B s := hCost

/-- The no-strong-physical-kinetic-L²-trace cubic witness admits physical
finite-frequency ANNULAR integrated windows, with no separate temporal
continuity premise for full H³ dissipation. The outer radius and the window
length are selected for each n, and need not obey a uniform scale. -/
theorem h3Path_noL2Trace_forces_cubicFiniteAnnulusIntegratedWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, n ≤ N n ∧ 0 < δ n ∧ τ n + δ n < T) ∧
      (∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ n : ℕ,
        δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
          (∫ s in τ n..(τ n + δ n),
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (δ : ℝ),
      n ≤ N ∧ 0 < δ ∧ τ n + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        (∫ s in τ n..(τ n + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    exact h3Path_cubicHighSnapshot_has_integratedFiniteAnnulusWindow244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N δ hδ using hChoice
  exact ⟨τ, N, δ, hτ, hLimit,
    (fun n => ⟨(hδ n).1, (hδ n).2.1, (hδ n).2.2.1⟩),
    (fun n s hs => (hδ n).2.2.2.1 s hs),
    (fun n => (hδ n).2.2.2.2)⟩

end
end PrimeTensor.FirstMonomialTriad
