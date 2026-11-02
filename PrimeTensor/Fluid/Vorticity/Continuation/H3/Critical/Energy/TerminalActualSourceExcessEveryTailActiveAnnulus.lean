import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedRadialHighDissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorSource244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Tactic

/-!
# All-active finite Fourier annuli on every physical terminal subtail

Previous synchronized fivefold gates offered only conditional active annular
windows. The already-proved fixed-radius high-H3 dissipation spike theorem
provides an actual cubic spike beyond ANY prescribed integer inner cutoff,
on EVERY preterminal subtail, without assuming terminal dissipation is L1.
The canonical exact-anchor first-crossing theorem then supplies a finite outer
cutoff, a physical projected-source maximum, an exact PDE persistence clock,
and a positive annular dissipation floor. We also charge its integral on its
OWN strictly preterminal interval; there is no global summability premise.

The absence of a physical L2 terminal trace is a hypothesis, not a conclusion.
This is not a Navier--Stokes continuation theorem.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- On every terminal subtail, at every specified inner integer frequency,
there is a genuinely ACTIVE finite physical Fourier annulus. Its exact
PDE-controlled width is selected using the physical projected-source
maximum, and its annular cost is a real positive-time integral. Neither a
full terminal H3 dissipation budget nor a positive terminal kinetic limit
is assumed. -/
theorem h3Critical_noL2Trace_everyTail_activeCubicPhysicalAnnulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (n : ℕ) :
    ∃ t : ℝ, t ∈ Set.Ioo b T ∧
      ∃ N : ℕ, ∃ C δ : ℝ,
        n ≤ N ∧ 0 ≤ C ∧
        C = h3PathActualProjectedSourceWindowEnvelope244 hH3
          t (t + (T - t) / 2) ∧
        0 < δ ∧ t + δ < T ∧
        δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
          ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t)) -
            ((n : ℝ) + 1) ^ 3 / 2)
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((n : ℝ) + 1) ((N : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 t‖ C)
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((n : ℝ) + 1) ((N : ℝ) + 1) C) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
          velocityH3EnergyAt u t ∧
        (∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ∧
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ≤
            velocityH3DissipationAt u r) ∧
        δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in t..(t + δ),
            h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) := by
  obtain ⟨t, ht, hSpike⟩ :=
    h3Critical_noL2Trace_highRadialDissipation_spikes_everyFixedRadius
      hH3 hClass hNoTrace b hb ((n : ℝ) + 1)
      (by positivity) (((n : ℝ) + 1) ^ 3)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨N, C, δ, hnN, hC, hCEq, _hAttained,
      hδ, hEnd, hδEq, hFloor, hKinetic, _hProduct,
      _hQuarter, _hMinimal⟩ :=
    h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244
      hH3 hClass t htClass n hSpike
  let B : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r)
  have hR : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hQ : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le htClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
  have hContinuous : ContinuousOn B (Set.Ioo a T) := by
    exact h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((n : ℝ) + 1) ((N : ℝ) + 1) hR hQ
  have hIntegrable : IntervalIntegrable B volume t (t + δ) :=
    (hContinuous.mono hSub).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right hδ.le)
  have hCost : δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
      ∫ r in t..(t + δ), B r := by
    have hFromFloor := h3Path_localPositiveHeight_forces_integratedCost244
      B t (t + δ) (((n : ℝ) + 1) ^ 3 / 2)
      (by linarith only [hδ]) hIntegrable
      (fun r hr => (hFloor r hr).le)
    calc
      δ * (((n : ℝ) + 1) ^ 3 / 2) =
          ((t + δ) - t) * (((n : ℝ) + 1) ^ 3 / 2) := by ring
      _ ≤ ∫ r in t..(t + δ), B r := hFromFloor
  have hFull (r : ℝ) (hr : r ∈ Set.Icc t (t + δ)) :
      B r ≤ velocityH3DissipationAt u r := by
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r (hSub hr) ((n : ℝ) + 1) ((N : ℝ) + 1)
  refine ⟨t, ht, N, C, δ, hnN, hC, hCEq,
    hδ, hEnd, hδEq, hKinetic, ?_, ?_⟩
  · intro r hr
    exact ⟨hFloor r hr, hFull r hr⟩
  · exact hCost

/-- Every terminal subtail carries a strictly positive finite-annulus
physical H3 integral cost, regardless of the integrability of the FULL
terminal dissipation. The positive integral occurs on its own compact
strict-time interval, and is not asserted to have a uniform lower bound. -/
theorem h3Critical_noL2Trace_everyTail_positiveCubicAnnularIntegral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (n : ℕ) :
    ∃ t : ℝ, t ∈ Set.Ioo b T ∧
      ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ t + δ < T ∧
        0 < ∫ r in t..(t + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) := by
  obtain ⟨t, ht, N, C, δ, _hnN, _hC, _hCEq,
      hδ, hEnd, _hδEq, _hEnergy, _hFloor, hCost⟩ :=
    h3Critical_noL2Trace_everyTail_activeCubicPhysicalAnnulus
      hH3 hClass hNoTrace b hb n
  have hHeight : 0 < ((n : ℝ) + 1) ^ 3 / 2 := by positivity
  have hPositive := lt_of_lt_of_le (mul_pos hδ hHeight) hCost
  exact ⟨t, ht, N, δ, hδ, hEnd, hPositive⟩

end
end PrimeTensor.Bridge.Euclidean
