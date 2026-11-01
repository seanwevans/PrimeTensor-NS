import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropSignedEndpointRates
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.PhysicalGradient.ActualSpike
import Mathlib.Tactic

/-!
# Source-driven highpass collapse: physical gradient spike or H³ energy drain

The source-drop signed endpoint theorem forces a fast negative H³ energy slope
or adverse physical nonlinear transport at one of two actual strict-time
endpoints. The exact one-time H³ transport commutator, with an *arbitrary
actual spatial-gradient cap* spliced into the already-proved physical energy
class envelope at that particular time, now converts adverse transport into a
lower bound on an actual spatial first derivative of velocity.

The resulting alternatives are phrased using the true old physical velocity
and exact Navier--Stokes energy slope. Neither a terminal-uniform H³ energy
ceiling nor a uniform source margin is derived. This closes the translation
from high-band spectral temporal transport to a physical gradient-or-drain
condition; it does not eliminate the gradient spike branch.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSourceDropGradient
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSourceDropGradient :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The genuine one-time physical velocity-gradient envelope bounds the
adverse full H³ transport commutator. No global or temporal gradient bound
is assumed: outside the selected time we use the already established
canonical H³ gradient envelope, which is only an intermediate proof device. -/
theorem h3Critical_oneTimeGradientEnvelope_negTransport_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s H : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hAt : VelocityGradientEnvelope u (fun _ : ℝ => H) s) :
    -velocityH3TransportDerivativeAt u s ≤
      (4422 * (1 + |H|)) * velocityH3EnergyAt u s := by
  let h : ℝ → ℝ := fun q =>
    if q = s then H else h3PathCanonicalSqrtEnergyGradientEnvelope u q
  have hTail : ∀ q : ℝ, q ∈ Set.Ioo a T →
      VelocityGradientEnvelope u h q := by
    intro q hq i j x
    by_cases heq : q = s
    · subst q
      have hLocal := hAt i j x
      change abs (spatial3.d i (fun y =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u s y).component j) x) ≤ h s
      have hEval : h s = H := by
        simp only [h, if_pos rfl]
      rw [hEval]
      exact hLocal
    · have hCanonical :=
        (h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hq) i j x
      change abs (spatial3.d i (fun y =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u q y).component j) x) ≤ h q
      have hEval : h q = h3PathCanonicalSqrtEnergyGradientEnvelope u q := by
        simp only [h, if_neg heq]
      rw [hEval]
      exact hCanonical
  have hComm : H3TransportCommutatorBoundAt u h 4422 s :=
    (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass hTail s hs).2
  have hTransport := neg_transport_le_of_commutatorBound hComm
  simpa only [h, if_pos rfl] using hTransport

/-- If an adverse signed physical transport exceeds the entire budget of an
actual spatial-gradient cap H, at least one genuine velocity derivative at
that exact time must exceed H. The conclusion is about a spatial derivative,
not about a chosen canonical upper envelope. -/
theorem h3Critical_adverseTransport_forces_actualGradientAbove
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (H K : ℝ) (hH : 0 ≤ H)
    (hBudget : (4422 * (1 + H)) * velocityH3EnergyAt u s ≤ K / 2)
    (hAdverse : K / 2 < -velocityH3TransportDerivativeAt u s) :
    ∃ i j : Axis Depth.three, ∃ x : Point3,
      H < abs (spatial3.d i (loggedVelocityComponent u s j) x) := by
  by_contra hNo
  have hAt : VelocityGradientEnvelope u (fun _ : ℝ => H) s := by
    intro i j x
    apply le_of_not_gt
    intro hGreater
    exact hNo ⟨i, j, x, hGreater⟩
  have hPDE := h3Critical_oneTimeGradientEnvelope_negTransport_le
    hH3 hClass hs hAt
  have hPDE' : -velocityH3TransportDerivativeAt u s ≤
      (4422 * (1 + H)) * velocityH3EnergyAt u s := by
    simpa only [abs_of_nonneg hH] using hPDE
  linarith only [hBudget, hPDE', hAdverse]

/-- A source peak followed by a high-radial H³ dissipation drop necessarily
produces, at one of its two actual endpoint times, either a fast negative H³
energy slope or an actual first spatial velocity derivative above H.

The energy ceilings and the selected numerical source-gap condition remain
explicit premises. There is NO premise that the physical derivatives are
continuous or bounded on the intervening window, and no independent Fourier
high-band temporal-displacement assumption. -/
theorem h3Critical_sourceDrop_endpointEnergyDrain_or_actualGradientSpike
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C K Emax H : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M)
    (hGap :
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) + 2 * K) <
      R ^ 2 *
        (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) σ M) ^ 2)
    (hEmaxT : velocityH3EnergyAt u t ≤ Emax)
    (hEmaxS : velocityH3EnergyAt u s ≤ Emax)
    (hH : 0 ≤ H)
    (hThreshold : (4422 * (1 + H)) * Emax ≤ K / 2) :
    (deriv (velocityH3EnergyAt u) t < -K / 2 ∨
      deriv (velocityH3EnergyAt u) s < -K / 2) ∨
    (∃ j k : Axis Depth.three, ∃ x : Point3,
      H < abs (spatial3.d j (loggedVelocityComponent u t k) x)) ∨
    (∃ j k : Axis Depth.three, ∃ x : Point3,
      H < abs (spatial3.d j (loggedVelocityComponent u s k) x)) := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hCoeff : 0 ≤ (4422 : ℝ) * (1 + H) := by positivity
  have hBt : (4422 * (1 + H)) * velocityH3EnergyAt u t ≤ K / 2 :=
    (mul_le_mul_of_nonneg_left hEmaxT hCoeff).trans hThreshold
  have hBs : (4422 * (1 + H)) * velocityH3EnergyAt u s ≤ K / 2 :=
    (mul_le_mul_of_nonneg_left hEmaxS hCoeff).trans hThreshold
  have hOld := h3Critical_sourceDrop_forces_endpointEnergyDrain_or_transport
    hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C K
    hCeil hPeak hDrop hGap
  rcases hOld with hAtT | hAtS
  · rcases hAtT with hDrain | hTransport
    · exact Or.inl (Or.inl hDrain)
    · right
      left
      have hAdverse : K / 2 < -velocityH3TransportDerivativeAt u t := by
        linarith only [hTransport]
      exact h3Critical_adverseTransport_forces_actualGradientAbove
        hH3 hClass htClass H K hH hBt hAdverse
  · rcases hAtS with hDrain | hTransport
    · exact Or.inl (Or.inr hDrain)
    · right
      right
      have hAdverse : K / 2 < -velocityH3TransportDerivativeAt u s := by
        linarith only [hTransport]
      exact h3Critical_adverseTransport_forces_actualGradientAbove
        hH3 hClass hsClass H K hH hBs hAdverse

/-- Contrapositive in purely physical terms. If both exact endpoint H³
energy slopes avoid the large-negative branch, and both ACTUAL endpoint
velocity gradients obey the cap H, then a source margin above the computed
PDE budget cannot lose high-radial dissipation by the second time. -/
theorem h3Critical_sourceDrop_gradientAndSlopeCaps_preclude_drop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C K Emax H : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hGap :
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) + 2 * K) <
      R ^ 2 *
        (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) σ M) ^ 2)
    (hEmaxT : velocityH3EnergyAt u t ≤ Emax)
    (hEmaxS : velocityH3EnergyAt u s ≤ Emax)
    (hH : 0 ≤ H)
    (hThreshold : (4422 * (1 + H)) * Emax ≤ K / 2)
    (hSlopeT : -K / 2 ≤ deriv (velocityH3EnergyAt u) t)
    (hSlopeS : -K / 2 ≤ deriv (velocityH3EnergyAt u) s)
    (hGradientT : VelocityGradientEnvelope u (fun _ : ℝ => H) t)
    (hGradientS : VelocityGradientEnvelope u (fun _ : ℝ => H) s) :
    M < h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) := by
  by_contra hNot
  have hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M :=
    le_of_not_gt hNot
  have hAlt := h3Critical_sourceDrop_endpointEnergyDrain_or_actualGradientSpike
    hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts
    M C K Emax H hCeil hPeak hDrop hGap hEmaxT hEmaxS hH hThreshold
  rcases hAlt with hDrain | hAtT | hAtS
  · rcases hDrain with htDrain | hsDrain
    · exact (not_lt_of_ge hSlopeT) htDrain
    · exact (not_lt_of_ge hSlopeS) hsDrain
  · obtain ⟨j, k, x, hSpike⟩ := hAtT
    exact (not_lt_of_ge (hGradientT j k x)) hSpike
  · obtain ⟨j, k, x, hSpike⟩ := hAtS
    exact (not_lt_of_ge (hGradientS j k x)) hSpike

end
end PrimeTensor.Bridge.Euclidean
