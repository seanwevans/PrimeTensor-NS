import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropPhysicalGradientAlternative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenWindows
import Mathlib.Tactic

/-!
# Actual source-drop signed energy and gradient gate, with cofinal physical peaks

The previous endpoint alternative used an auxiliary *uniform* H³ energy
ceiling and a fixed gradient threshold small relative to that ceiling.
Here the physical H³ transport commutator is applied at each endpoint with
its OWN observed energy and its OWN actual velocity-gradient cap. Thus the
source-drop inequality becomes an exact two-endpoint energy-drain budget,
without any artificial terminal-uniform energy bound.

We then synchronize the gate with the already constructed cofinal separated
source-driven windows. Selecting the Fourier-source threshold to be the
SQUARE of the actual kinetic-anchored source barrier makes the physical
highpass peak hypothesis automatic on every selected window, by Plancherel.
A drop after such a window remains a CONDITION; no drop or terminal-uniform
source bound is inferred.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCofinalEnergyGate
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCofinalEnergyGate :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact H³ energy identity plus the one-time *physical* gradient
commutator charges a drop of the actual Fourier source to negative endpoint
energy slopes and to the actual endpoint energies, separately. No global
H³ ceiling, no full-H³ temporal derivative, and no new spectral assumption. -/
theorem h3Critical_sourceDrop_gradientCaps_signedEnergySlopeBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C Ht Hs : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M)
    (hGradientT : VelocityGradientEnvelope u (fun _ : ℝ => Ht) t)
    (hGradientS : VelocityGradientEnvelope u (fun _ : ℝ => Hs) s) :
    R ^ 2 *
      (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) -
          deriv (velocityH3EnergyAt u) t -
          deriv (velocityH3EnergyAt u) s +
          (4422 * (1 + |Ht|)) * velocityH3EnergyAt u t +
          (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s) := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hSigned :=
    h3Critical_sourceDrop_forces_signedEndpointRateBudget
      hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C
      hCeil hPeak hDrop
  have hTrT := h3Critical_oneTimeGradientEnvelope_negTransport_le
    hH3 hClass htClass hGradientT
  have hTrS := h3Critical_oneTimeGradientEnvelope_negTransport_le
    hH3 hClass hsClass hGradientS
  have hRates :
      -(deriv (velocityH3EnergyAt u) t +
          velocityH3TransportDerivativeAt u t) -
        (deriv (velocityH3EnergyAt u) s +
          velocityH3TransportDerivativeAt u s) ≤
      -deriv (velocityH3EnergyAt u) t -
        deriv (velocityH3EnergyAt u) s +
        (4422 * (1 + |Ht|)) * velocityH3EnergyAt u t +
        (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s := by
    linarith only [hTrT, hTrS]
  have hA : 0 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 := sq_nonneg _
  calc
    R ^ 2 *
      (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) -
          (deriv (velocityH3EnergyAt u) t +
            velocityH3TransportDerivativeAt u t) -
          (deriv (velocityH3EnergyAt u) s +
            velocityH3TransportDerivativeAt u s)) := hSigned
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      linarith only [hRates]

/-- Under ACTUAL endpoint spatial-gradient caps, if a source drop consumes
more than the finite-band motion, capped nonlinear transport, and two allowed
energy-slope expenditures, one endpoint must have a rapid negative slope.
Crucially there is no common H³ energy ceiling and no `K/2` gradient budget. -/
theorem h3Critical_sourceDrop_gradientCaps_force_endpointEnergyDrain
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C K Ht Hs : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M)
    (hGradientT : VelocityGradientEnvelope u (fun _ : ℝ => Ht) t)
    (hGradientS : VelocityGradientEnvelope u (fun _ : ℝ => Hs) s)
    (hGap :
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) + 2 * K +
          (4422 * (1 + |Ht|)) * velocityH3EnergyAt u t +
          (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s) <
      R ^ 2 *
        (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) σ M) ^ 2) :
    deriv (velocityH3EnergyAt u) t < -K ∨
      deriv (velocityH3EnergyAt u) s < -K := by
  have hBound := h3Critical_sourceDrop_gradientCaps_signedEnergySlopeBudget
    hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C Ht Hs
    hCeil hPeak hDrop hGradientT hGradientS
  by_contra hNot
  have hSlopeT : -K ≤ deriv (velocityH3EnergyAt u) t :=
    le_of_not_gt (fun h => hNot (Or.inl h))
  have hSlopeS : -K ≤ deriv (velocityH3EnergyAt u) s :=
    le_of_not_gt (fun h => hNot (Or.inr h))
  have hSum :
      -deriv (velocityH3EnergyAt u) t -
          deriv (velocityH3EnergyAt u) s ≤ 2 * K := by
    linarith only [hSlopeT, hSlopeS]
  have hNonneg : 0 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 := sq_nonneg _
  have hUpper := mul_le_mul_of_nonneg_left
    (show R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
            (C * (s - t)) ^ 2) -
          deriv (velocityH3EnergyAt u) t -
          deriv (velocityH3EnergyAt u) s +
          (4422 * (1 + |Ht|)) * velocityH3EnergyAt u t +
          (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s ≤
        R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
            (C * (s - t)) ^ 2) + 2 * K +
          (4422 * (1 + |Ht|)) * velocityH3EnergyAt u t +
          (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s from by
        linarith only [hSum]) hNonneg
  exact (not_lt_of_ge (hBound.trans hUpper)) hGap

/-- The direct two-endpoint physical alternative, without a terminal-uniform
energy ceiling. Actual gradients may have DIFFERENT caps Ht and Hs.
The gap prices their ACTUAL endpoint H³ energies rather than a surrogate. -/
theorem h3Critical_sourceDrop_noDrain_forces_actualEndpointGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C K Ht Hs : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M)
    (hSlopeT : -K ≤ deriv (velocityH3EnergyAt u) t)
    (hSlopeS : -K ≤ deriv (velocityH3EnergyAt u) s)
    (hGap :
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) + 2 * K +
          (4422 * (1 + |Ht|)) * velocityH3EnergyAt u t +
          (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s) <
      R ^ 2 *
        (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) σ M) ^ 2) :
    (∃ j k : Axis Depth.three, ∃ x : Point3,
      Ht < abs (spatial3.d j (loggedVelocityComponent u t k) x)) ∨
    (∃ j k : Axis Depth.three, ∃ x : Point3,
      Hs < abs (spatial3.d j (loggedVelocityComponent u s k) x)) := by
  by_contra hNot
  have hAtT : VelocityGradientEnvelope u (fun _ : ℝ => Ht) t := by
    intro j k x
    apply le_of_not_gt
    intro hHigher
    exact hNot (Or.inl ⟨j, k, x, hHigher⟩)
  have hAtS : VelocityGradientEnvelope u (fun _ : ℝ => Hs) s := by
    intro j k x
    apply le_of_not_gt
    intro hHigher
    exact hNot (Or.inr ⟨j, k, x, hHigher⟩)
  rcases h3Critical_sourceDrop_gradientCaps_force_endpointEnergyDrain
    hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C K Ht Hs
    hCeil hPeak hDrop hAtT hAtS hGap with hDrainT | hDrainS
  · exact (not_lt_of_ge hSlopeT) hDrainT
  · exact (not_lt_of_ge hSlopeS) hDrainS

/-- The source-driven diagonal makes the peak *automatic* at one fixed
physical Fourier coordinate on an actual disjoint cofinal family. For EACH
later physical time with a genuine dissipation drop, the new no-drain gate
can then be invoked with the cutoff and constants at that same index.

The after-window drop, source ceiling, and strict numerical gap are local
conditions, not silently derived from terminal cofinality. -/
theorem h3Critical_noL2Trace_cofinalSourceWindows_postDropGradientGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) <
            ‖h3CriticalActualProjectedHighpassFourierSource hH3
              (ρ (v k)) i (t (v k))‖ ∧
        (∀ r : ℝ, r ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 r))) ∧
      (∀ k : ℕ, ∀ s : ℝ,
        t (v k) + δ (v k) ≤ s → s < T →
        h3PathActualHighRadialDissipation244 (σ (v k))
          (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M (v k) →
        ∀ R C K Ht Hs : ℝ, 0 ≤ R →
        (∀ r : ℝ, r ∈ Set.Icc (t (v k)) s →
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) →
        (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
          (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
            (C * (s - t (v k))) ^ 2) + 2 * K +
            (4422 * (1 + |Ht|)) * velocityH3EnergyAt u (t (v k)) +
            (4422 * (1 + |Hs|)) * velocityH3EnergyAt u s) <
          R ^ 2 *
            (‖h3CriticalActualProjectedHighpassFourierSource hH3
                (ρ (v k)) i (t (v k))‖ -
              h3CriticalSourceDrivenHighDissipationBarrier
                (velocityH3Energy0At u b) (σ (v k)) (M (v k))) ^ 2 →
        -K ≤ deriv (velocityH3EnergyAt u) (t (v k)) →
        -K ≤ deriv (velocityH3EnergyAt u) s →
        (∃ j l : Axis Depth.three, ∃ x : Point3,
          Ht < abs (spatial3.d j (loggedVelocityComponent u (t (v k)) l) x)) ∨
        (∃ j l : Axis Depth.three, ∃ x : Point3,
          Hs < abs (spatial3.d j (loggedVelocityComponent u s l) x))) := by
  let B : ℕ → ℝ := fun n =>
    h3CriticalSourceDrivenHighDissipationBarrier
      (velocityH3Energy0At u b) (σ n) (M n)
  let Ksource : ℕ → ℝ := fun n => (B n) ^ 2
  obtain ⟨i, t, δ, v, hv, hCofinal, hDisjoint, hWindows, _, _⟩ :=
    h3Critical_noL2Trace_sourceDriven_profileDisjointWindows
      hH3 hClass b hb hNoTrace c ρ σ Ksource M hc hcLimit hρ hσ
  have hPeakNorm (k : ℕ) :
      B (v k) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i (t (v k))‖ := by
    let F : H3FourierComplexL2 :=
      h3CriticalActualProjectedHighpassFourierSource hH3
        (ρ (v k)) i (t (v k))
    have hB : 0 ≤ B (v k) := by
      dsimp only [B, h3CriticalSourceDrivenHighDissipationBarrier]
      exact le_max_right _ _
    have hAtStart : t (v k) ∈ Set.Icc
        (t (v k)) (t (v k) + δ (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right ((hWindows k).2.1).le⟩
    have hMass := ((hWindows k).2.2.2.1 (t (v k)) hAtStart).1
    have hNormMass : ‖F‖ ^ 2 =
        ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ (v k)))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i (t (v k)) ξ‖ ^ 2
          ∂volume := by
      dsimp only [F, h3CriticalActualProjectedHighpassFourierSource]
      exact h3Critical_fourierSharpHighpass_norm_sq_eq_integral
        (ρ (v k)) (h3CriticalActualProjectedFourierSource hH3 i (t (v k)))
    have hSq : (B (v k)) ^ 2 < ‖F‖ ^ 2 := by
      rw [hNormMass]
      exact hMass
    have hNorm : 0 ≤ ‖F‖ := norm_nonneg _
    have hStrict : B (v k) < ‖F‖ := by
      nlinarith only [hSq, hB, hNorm]
    exact hStrict
  refine ⟨i, t, δ, v, hv, hCofinal, hDisjoint, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hPeakNorm k,
      fun r hr => ((hWindows k).2.2.2.1 r hr).2⟩
  · intro k s hsAfter hsBefore hDrop R C K Ht Hs hR hCeil hGap
      hSlopeT hSlopeS
    have ht : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 (hWindows k).1.1, (hWindows k).1.2⟩
    have hs : s ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le ht.1 (le_trans
        (le_add_of_nonneg_right ((hWindows k).2.1).le) hsAfter), hsBefore⟩
    have hts : t (v k) ≤ s :=
      le_trans (le_add_of_nonneg_right ((hWindows k).2.1).le) hsAfter
    exact h3Critical_sourceDrop_noDrain_forces_actualEndpointGradient
      hH3 hClass b hb (ρ (v k)) (σ (v k)) R (hσ (v k)) hR i
      (t (v k)) s ht hs hts (M (v k)) C K Ht Hs
      hCeil (hPeakNorm k).le hDrop hSlopeT hSlopeS hGap

end
end PrimeTensor.Bridge.Euclidean
