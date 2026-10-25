import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralIntegratedHighRadialAverage244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralQuantitativeTemporalDissipationWindow244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# From a cubic high-radial dissipation snapshot to a positive integrated cost

The physical no-kinetic-L²-trace branch has a SINGLE terminal sequence τ(n) on
which the actual high-radial H³ dissipation above R_n=n+1 exceeds R_n³.
The previous persistence result additionally recorded positive-width windows
under continuity of the low and total scalar dissipation functions.

We prove the exact compatibility missing from that interval argument:
  * the actual high-radial dissipation is continuous on a strict physical
    time tail if its low-radial and full counterparts are continuous there;
  * such continuity turns each cubic snapshot into a compact strict-time
    interval of positive length with high dissipation above R_n³/2;
  * continuity automatically gives interval integrability there, hence
    ∫ high D ≥ (R_n³/2) × window length;
  * one sequence of snapshots and one sequence of intervals carry ALL these
    facts under the previously retained no-kinetic-L²-trace condition.

The widths are not bounded below by a known scale. In particular the cubic
heights do NOT imply divergence of the sum of integrated costs. Continuity
of FULL H³ dissipation is still an explicit hypothesis, not a deduction
from strong continuity of the weighted H³ spectral state.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact spectral partition transports continuity from low-radial plus full
physical H³ dissipation to high-radial dissipation. There is no independent
regularity assumption on the high-radial integral. -/
theorem h3Path_actualHighRadialDissipation_continuousOn_of_parts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ)
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T))
    (hLowCont : ContinuousOn (fun s : ℝ =>
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T)) :
    ContinuousOn (fun s : ℝ =>
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T) := by
  have hDiff : ContinuousOn (fun s : ℝ =>
      velocityH3DissipationAt u s -
        h3PathActualLowRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T) :=
    hDCont.sub hLowCont
  apply hDiff.congr
  intro s hs
  have hPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass s hs ρ
  linarith only [hPart]

/-- A cubic high-frequency snapshot has a positive, physical, right-hand
window on which the high-frequency dissipation remains above half that cubic
height. Its integral has a corresponding length-times-height lower bound.
No separate time-integrability hypothesis is needed beyond continuity. -/
theorem h3Path_highRadialCubicSnapshot_integratedWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hHighCont : ContinuousOn (fun s : ℝ =>
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T)) :
    ∃ δ : ℝ, 0 < δ ∧ t + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        (∫ s in t..(t + δ),
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let R : ℝ := (n : ℝ) + 1
  let H : ℝ → ℝ := fun s =>
    h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hCube' : R ^ 3 < H t := by simpa only [R, H] using hCube
  have hHalf : 0 < R ^ 3 / 2 := by positivity
  have hContinuous : ContinuousAt H t := by
    exact hHighCont.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hDifferenceCont : ContinuousAt (fun s => R ^ 3 / 2 - H s) t :=
    continuousAt_const.sub hContinuous
  have hAt : R ^ 3 / 2 - H t < 0 := by
    linarith only [hCube', hHalf]
  obtain ⟨η, hη, hNeighborhood⟩ :=
    h3Path_continuousStrictInequality_localWindow244
      hDifferenceCont hAt
  let δ : ℝ := min (η / 2) ((T - t) / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by linarith only [hη]) (by linarith only [ht.2])
  have hδη : δ ≤ η / 2 := by
    dsimp only [δ]
    exact min_le_left _ _
  have hδT : δ ≤ (T - t) / 2 := by
    dsimp only [δ]
    exact min_le_right _ _
  have hEnd : t + δ < T := by linarith only [hδT, ht.2]
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      R ^ 3 / 2 < H s := by
    intro s hs
    have hDist : dist s t < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith only [hs.2, hδη, hη]
    have hWindow := hNeighborhood s hDist
    linarith only [hWindow]
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hInt : IntervalIntegrable H volume t (t + δ) := by
    exact (hHighCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hδ])
  have hCost : ((t + δ) - t) * (R ^ 3 / 2) ≤
      ∫ s in t..(t + δ), H s :=
    h3Path_localPositiveHeight_forces_integratedCost244
      H t (t + δ) (R ^ 3 / 2) (by linarith only [hδ]) hInt
      (fun s hs => (hFloor s hs).le)
  refine ⟨δ, hδ, hEnd, ?_, ?_⟩
  · intro s hs
    simpa only [H, R] using hFloor s hs
  · change δ * (R ^ 3 / 2) ≤ ∫ s in t..(t + δ), H s
    calc
      δ * (R ^ 3 / 2) = ((t + δ) - t) * (R ^ 3 / 2) := by ring
      _ ≤ ∫ s in t..(t + δ), H s := hCost

/-- The no-strong-kinetic-L²-trace cubic radial witness can be given its OWN
positive right-hand integration windows. This does not combine two unrelated
terminal witness sequences, and assumes continuity only where it is used. -/
theorem h3Path_noL2Trace_forces_cubicHighDissipationIntegralWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T))
    (hLowCont : ∀ n : ℕ, ContinuousOn (fun s : ℝ =>
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T)) :
    ∃ (τ δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 0 < δ n ∧ τ n + δ n < T) ∧
      (∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ n : ℕ, δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
        (∫ s in τ n..(τ n + δ n),
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCubic⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ τ n + δ < T ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        (∫ s in τ n..(τ n + δ),
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    exact h3Path_highRadialCubicSnapshot_integratedWindow244
      hH3 hClass (τ n) (hτ n) n (hCubic n)
      (h3Path_actualHighRadialDissipation_continuousOn_of_parts244
        hH3 hClass ((n : ℝ) + 1) hDCont (hLowCont n))
  choose δ hδ using hChoice
  exact ⟨τ, δ, hτ, hLimit, (fun n => ⟨(hδ n).1, (hδ n).2.1⟩),
    (fun n s hs => (hδ n).2.2.1 s hs),
    (fun n => (hδ n).2.2.2)⟩

end
end PrimeTensor.FirstMonomialTriad
