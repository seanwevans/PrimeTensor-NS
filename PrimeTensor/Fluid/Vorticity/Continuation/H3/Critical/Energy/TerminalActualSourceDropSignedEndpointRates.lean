import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropEndpointDissipationTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact
import Mathlib.Tactic

/-!
# Actual source-drop endpoint dissipation as signed physical H³ energy rates

The existing physical PDE source-drop estimate charges a highpass source margin
first to finite-radial temporal Fourier motion, then to actual high-radial H³
viscous dissipation at both endpoints. The exact physical Navier--Stokes
energy identity is E' + 2D = -Transport. Here the high-radial endpoint costs
are bounded by full physical dissipation and replaced by this exact signed
identity, with no terminal dissipation ceiling or fictitious H³ Lipschitz rate.

If the source excess overwhelms the low-frequency PDE clock and a specified
signed-rate threshold at both endpoints, a dissipation drop is impossible.
Equivalently, a sufficiently expensive source drop forces either a fast
negative H³ energy derivative or an adverse signed nonlinear transport at
one of the two exact physical endpoint times. These are necessary conditions,
not upper estimates for the transport or claims of global regularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSignedEndpoint
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSignedEndpoint :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The unpriced high-radial spectral temporal term has already been charged
to endpoint physical dissipation. The exact *signed* Navier--Stokes H³
energy balance now converts that cost into the physical derivative and
transport values at those very same endpoints. The velocity and projected
source are the actual PDE representatives, not auxiliary scalar profiles. -/
theorem h3Critical_sourceDrop_forces_signedEndpointRateBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
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
            velocityH3TransportDerivativeAt u s)) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let V : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 s
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖)
  let P : ℝ :=
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M
  let L : ℝ := R ^ 2 *
    ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
      (C * (s - t)) ^ 2)
  let Dt : ℝ := h3PathActualHighRadialDissipation244 R U
  let Ds : ℝ := h3PathActualHighRadialDissipation244 R V
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hOriginal : R ^ 2 * P ^ 2 ≤ A ^ 2 * (L + 2 * (Dt + Ds)) := by
    dsimp only [P, A, L, Dt, Ds, U, V]
    exact h3Critical_sourceDrop_forces_endpointPhysicalDissipationBudget
      hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C
      hCeil hPeak hDrop
  have hDt : Dt ≤ velocityH3DissipationAt u t :=
    h3Critical_actualHighRadialDissipation_le_full
      hH3 hClass t htClass R
  have hDs : Ds ≤ velocityH3DissipationAt u s :=
    h3Critical_actualHighRadialDissipation_le_full
      hH3 hClass s hsClass R
  have hBalanceT :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass htClass
  have hBalanceS :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
  have hRates :
      2 * (Dt + Ds) ≤
        - (deriv (velocityH3EnergyAt u) t +
          velocityH3TransportDerivativeAt u t) -
        (deriv (velocityH3EnergyAt u) s +
          velocityH3TransportDerivativeAt u s) := by
    have hAdd := add_le_add hDt hDs
    have hTwice := mul_le_mul_of_nonneg_left hAdd
      (by norm_num : 0 ≤ (2 : ℝ))
    linarith only [hTwice, hBalanceT, hBalanceS]
  change R ^ 2 * P ^ 2 ≤ A ^ 2 *
    (L - (deriv (velocityH3EnergyAt u) t +
      velocityH3TransportDerivativeAt u t) -
      (deriv (velocityH3EnergyAt u) s +
        velocityH3TransportDerivativeAt u s))
  calc
    R ^ 2 * P ^ 2 ≤ A ^ 2 * (L + 2 * (Dt + Ds)) := hOriginal
    _ ≤ A ^ 2 *
        (L - (deriv (velocityH3EnergyAt u) t +
          velocityH3TransportDerivativeAt u t) -
          (deriv (velocityH3EnergyAt u) s +
            velocityH3TransportDerivativeAt u s)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      linarith only [hRates]

/-- A source margin too large for the finite-band PDE clock and a prescribed
signed-rate budget K cannot coexist with a drop of high-H³ dissipation unless
at least one of the actual physical endpoint signed viscous rates exceeds K.
The signed rate -E'-Transport equals exactly 2D, but its decomposition keeps
the nonlinear and energy-loss channels visible. -/
theorem h3Critical_sourceDrop_forces_oneLargeSignedEndpointRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C K : ℝ)
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
            (velocityH3Energy0At u b) σ M) ^ 2) :
    K < - (deriv (velocityH3EnergyAt u) t +
      velocityH3TransportDerivativeAt u t) ∨
    K < - (deriv (velocityH3EnergyAt u) s +
      velocityH3TransportDerivativeAt u s) := by
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient *
    (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
  let L : ℝ := R ^ 2 *
    ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
      (C * (s - t)) ^ 2)
  let P : ℝ :=
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M
  have hSigned : R ^ 2 * P ^ 2 ≤ A ^ 2 *
      (L - (deriv (velocityH3EnergyAt u) t +
        velocityH3TransportDerivativeAt u t) -
        (deriv (velocityH3EnergyAt u) s +
          velocityH3TransportDerivativeAt u s)) := by
    dsimp only [P, A, L]
    exact h3Critical_sourceDrop_forces_signedEndpointRateBudget
      hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C
      hCeil hPeak hDrop
  by_contra hNot
  have hnT : ¬ K < - (deriv (velocityH3EnergyAt u) t +
      velocityH3TransportDerivativeAt u t) :=
    fun h => hNot (Or.inl h)
  have hnS : ¬ K < - (deriv (velocityH3EnergyAt u) s +
      velocityH3TransportDerivativeAt u s) :=
    fun h => hNot (Or.inr h)
  have hTBound := le_of_not_gt hnT
  have hSBound := le_of_not_gt hnS
  have hRates :
      - (deriv (velocityH3EnergyAt u) t +
          velocityH3TransportDerivativeAt u t) -
        (deriv (velocityH3EnergyAt u) s +
          velocityH3TransportDerivativeAt u s) ≤ 2 * K := by
    linarith only [hTBound, hSBound]
  have hUpper : R ^ 2 * P ^ 2 ≤ A ^ 2 * (L + 2 * K) := by
    calc
      R ^ 2 * P ^ 2 ≤ A ^ 2 *
          (L - (deriv (velocityH3EnergyAt u) t +
            velocityH3TransportDerivativeAt u t) -
            (deriv (velocityH3EnergyAt u) s +
              velocityH3TransportDerivativeAt u s)) := hSigned
      _ ≤ A ^ 2 * (L + 2 * K) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
        linarith only [hRates]
  exact (not_lt_of_ge hUpper) hGap

/-- Large signed viscous rate means either fast negative energy slope or
an adverse nonlinear transport at the same physical instant. This is exact
algebra and makes no one-sided transport assumption. -/
theorem h3Critical_largeSignedViscousRate_energyDrain_or_transport
    (e transport K : ℝ) (hRate : K < - (e + transport)) :
    e < - K / 2 ∨ transport < - K / 2 := by
  by_cases he : e < - K / 2
  · exact Or.inl he
  · right
    have heBound : - K / 2 ≤ e := le_of_not_gt he
    linarith only [heBound, hRate]

/-- Exact physical source-drop signed endpoint alternative, with no additional high-band
spectral displacement hypothesis: the same two physical endpoint times must
exhibit rapid H³ energy loss or adverse signed nonlinear transport if the
source peak exceeds the finite-frequency PDE and endpoint signed-rate budget.
This is NOT a proof that the signed transport is bounded by the dissipation. -/
theorem h3Critical_sourceDrop_forces_endpointEnergyDrain_or_transport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C K : ℝ)
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
            (velocityH3Energy0At u b) σ M) ^ 2) :
    (deriv (velocityH3EnergyAt u) t < - K / 2 ∨
      velocityH3TransportDerivativeAt u t < - K / 2) ∨
    (deriv (velocityH3EnergyAt u) s < - K / 2 ∨
      velocityH3TransportDerivativeAt u s < - K / 2) := by
  rcases h3Critical_sourceDrop_forces_oneLargeSignedEndpointRate
      hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C K
      hCeil hPeak hDrop hGap with hAtT | hAtS
  · exact Or.inl (h3Critical_largeSignedViscousRate_energyDrain_or_transport
      (deriv (velocityH3EnergyAt u) t)
      (velocityH3TransportDerivativeAt u t) K hAtT)
  · exact Or.inr (h3Critical_largeSignedViscousRate_energyDrain_or_transport
      (deriv (velocityH3EnergyAt u) s)
      (velocityH3TransportDerivativeAt u s) K hAtS)

end
end PrimeTensor.Bridge.Euclidean
