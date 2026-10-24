import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticLongitudinalTail244
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Physical terminal L² trace from transverse action: the exact missing channel

For an H³-admissible path on a strict energy-class tail (a,T), its kinetic energy
E₀(t) tends to a finite nonnegative limit L. The committed kinetic/transverse
source decomposition bounds any ordered physical displacement by the integrated
transverse-source norm and the scalar remainder (E₀(s)-L)/(2√L) when L>0.

This module closes the corresponding sufficient endpoint criterion rigorously:
  * if L=0, the physical velocity tends strongly to zero, with no source assumption;
  * if L>0 and the integrated transverse variation vanishes uniformly over
    later strict times, the physical velocity has a strong terminal Hilbert trace;
  * in either case the trace has exactly the canonical terminal kinetic mass L.

This is an L² trace criterion, not a smooth Navier--Stokes continuation theorem.
The positive-limit transverse hypothesis is not discharged here. In particular,
scalar kinetic spending alone cannot control transverse velocity rotation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Uniform vanishing of transverse L² source variation on later strict
terminal intervals; this is an analytic hypothesis, not a consequence of the
kinetic energy budget. -/
def H3PhysicalTransverseTerminalTailVanishing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ s : ℝ in 𝓝[<] T,
      s ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
          (∫ r in s..t, ‖h3PathPhysicalTransverseSource244 hH3 r‖) < ε

/-- In the positive terminal kinetic-mass branch, vanishing transverse
variation implies a uniform Cauchy estimate for later physical velocities. -/
theorem h3Path_physicalVelocity_uniformTerminalIncrementSmall_of_transverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[<] T,
      s ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
          ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
            h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ < ε := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  have hRoot : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hDen : 0 < 2 * Real.sqrt L := mul_pos (by norm_num) hRoot
  have hLimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L) :=
    h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass
  have hProdPos : 0 < ε * Real.sqrt L := mul_pos hε hRoot
  have hBoundPos : L < L + ε * Real.sqrt L := by
    linarith only [hProdPos]
  have hKSmall : ∀ᶠ s : ℝ in 𝓝[<] T,
      velocityH3Energy0At u s < L + ε * Real.sqrt L :=
    (tendsto_order.1 hLimit).2 _ hBoundPos
  have hHalf : 0 < ε / 2 := by linarith only [hε]
  have hQSmall := hQ (ε / 2) hHalf
  filter_upwards [hKSmall, hQSmall] with s hsK hsQ
  refine ⟨hsQ.1, ?_⟩
  intro t ht hst
  have hInc :=
    h3Path_physicalHilbert_increment_le_transverse_and_remainingKinetic244
      hH3 hClass hL s t hsQ.1 ht hst
  have hRemainder :
      (velocityH3Energy0At u s - L) / (2 * Real.sqrt L) < ε / 2 := by
    apply (div_lt_iff₀ hDen).2
    have hMul : (ε / 2) * (2 * Real.sqrt L) = ε * Real.sqrt L := by ring
    rw [hMul]
    linarith only [hsK]
  have hQBound := hsQ.2 t ht hst
  dsimp only [L] at hRemainder
  linarith only [hInc, hQBound, hRemainder]

/-- Completeness of physical L² upgrades the uniform terminal Cauchy
estimate to an actual strong Hilbert-space endpoint trace. -/
theorem h3Path_physicalVelocity_existsTerminalL2Trace_of_transverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3) :
    ∃ V : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 V) := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hCauchy : Cauchy (Filter.map U (𝓝[<] T)) := by
    apply Metric.cauchy_iff.mpr
    constructor
    · infer_instance
    · intro ε hε
      have hSmall :=
        h3Path_physicalVelocity_uniformTerminalIncrementSmall_of_transverse244
          hH3 hClass hL hQ ε hε
      let A : Set ℝ :=
        {s | s ∈ Set.Ioo a T ∧
          ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
            ‖U t - U s‖ < ε}
      have hAMem : A ∈ 𝓝[<] T := hSmall
      refine ⟨U '' A, ?_, ?_⟩
      · change U ⁻¹' (U '' A) ∈ 𝓝[<] T
        exact Filter.mem_of_superset hAMem (fun s hs => ⟨s, hs, rfl⟩)
      · intro x hx y hy
        obtain ⟨s, hs, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hy
        change dist (U s) (U t) < ε
        change s ∈ Set.Ioo a T ∧
          (∀ z : ℝ, z ∈ Set.Ioo a T → s ≤ z → ‖U z - U s‖ < ε) at hs
        change t ∈ Set.Ioo a T ∧
          (∀ z : ℝ, z ∈ Set.Ioo a T → t ≤ z → ‖U z - U t‖ < ε) at ht
        by_cases hst : s ≤ t
        · rw [dist_eq_norm, norm_sub_rev]
          exact hs.2 t ht.1 hst
        · have hts : t ≤ s := le_of_not_ge hst
          rw [dist_eq_norm]
          exact ht.2 s hs.1 hts
  obtain ⟨V, hV⟩ := (cauchy_map_iff_exists_tendsto).mp hCauchy
  exact ⟨V, hV⟩

/-- Vanishing terminal kinetic mass alone gives strong physical L² convergence
to zero; transverse source integrability is unnecessary in this branch. -/
theorem h3Path_physicalVelocity_tendsto_zero_of_zeroTerminalKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hZero : h3PathCanonicalTerminalKineticEnergyAt u a T = 0) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[<] T) (𝓝 (0 : H3PhysicalRealFinVectorL2Hilbert)) := by
  have hKinetic :=
    h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass
  have hSqrt : Tendsto
      (fun t : ℝ => Real.sqrt (velocityH3Energy0At u t))
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, hZero, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto _).comp hKinetic
  have hTpos : 0 < T :=
    lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  have hNear : ∀ᶠ t : ℝ in 𝓝[<] T, t ∈ Set.Ioo (0 : ℝ) T := by
    have hAfter : ∀ᶠ t : ℝ in 𝓝 T, (0 : ℝ) < t := Ioi_mem_nhds hTpos
    filter_upwards [hAfter.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hpos hlt
    exact ⟨hpos, hlt⟩
  have hNorm : Tendsto
      (fun t : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖)
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    apply hSqrt.congr'
    filter_upwards [hNear] with t ht
    exact (h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy
      hH3 t ht).symm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hNorm

/-- The transverse terminal-tail criterion suffices for the full nonnegative
terminal kinetic-mass range: zero mass is automatic, positive mass uses Q. -/
theorem h3Path_physicalVelocity_existsTerminalL2Trace_of_transverseAllCases244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3) :
    ∃ V : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 V) := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  by_cases hZero : L = 0
  · exact ⟨0, h3Path_physicalVelocity_tendsto_zero_of_zeroTerminalKinetic244
      hH3 hClass hZero⟩
  · have hNonneg : 0 ≤ L :=
      h3PathCanonical_terminalKineticEnergy_nonneg hClass
    have hPos : 0 < L := lt_of_le_of_ne hNonneg (Ne.symm hZero)
    exact h3Path_physicalVelocity_existsTerminalL2Trace_of_transverse244
      hH3 hClass hPos hQ

/-- Any strong terminal physical velocity trace has squared L² norm exactly
the existing canonical terminal kinetic mass. The result does not assume Q. -/
theorem h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (hV : Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[<] T) (𝓝 V)) :
    ‖V‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  have hCont : Continuous
      (fun W : H3PhysicalRealFinVectorL2Hilbert => ‖W‖ ^ 2) :=
    continuous_norm.pow 2
  have hNormSq : Tendsto
      (fun t : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2)
      (𝓝[<] T) (𝓝 (‖V‖ ^ 2)) :=
    (hCont.tendsto V).comp hV
  have hTpos : 0 < T :=
    lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  have hNear : ∀ᶠ t : ℝ in 𝓝[<] T, t ∈ Set.Ioo (0 : ℝ) T := by
    have hAfter : ∀ᶠ t : ℝ in 𝓝 T, (0 : ℝ) < t := Ioi_mem_nhds hTpos
    filter_upwards [hAfter.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hpos hlt
    exact ⟨hpos, hlt⟩
  have hEq : ∀ᶠ t : ℝ in 𝓝[<] T,
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 =
        velocityH3Energy0At u t := by
    filter_upwards [hNear] with t ht
    exact h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t ht
  have hPhysicalLimit : Tendsto (velocityH3Energy0At u)
      (𝓝[<] T) (𝓝 (‖V‖ ^ 2)) := hNormSq.congr' hEq
  exact tendsto_nhds_unique hPhysicalLimit
    (h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass)


/-- The sufficient transverse-action criterion produces a genuine physical
terminal L² vector whose norm square is the canonical terminal kinetic mass. -/
theorem h3Path_physicalVelocity_terminalL2Trace_and_exactKineticMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3) :
    ∃ V : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 V) ∧
        ‖V‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  obtain ⟨V, hV⟩ :=
    h3Path_physicalVelocity_existsTerminalL2Trace_of_transverseAllCases244
      hH3 hClass hQ
  exact ⟨V, hV,
    h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
      hH3 hClass V hV⟩

end
end PrimeTensor.FirstMonomialTriad
