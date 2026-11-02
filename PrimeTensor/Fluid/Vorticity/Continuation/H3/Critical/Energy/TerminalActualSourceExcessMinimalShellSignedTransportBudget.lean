import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellNormalizedEnergyWidthBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSignedEnergyCompetition
import Mathlib.Tactic

/-!
# Minimal first-crossing H³ annular floor and exact signed physical transport

On the SAME actual physical first-crossing PDE window as the minimal-shell
kinetic, source, energy, and sixth/ninth-rate certificates, the finite-annulus
floor is inherited by the full physical H³ dissipation. The exact signed
Navier--Stokes H³ balance consequently requires a transport contribution of
one entire inner cubic height, together with a signed drain / cubic Riccati
energy alternative at every strict physical time in that window.

This is unconditional pointwise information on each sufficiently late selected
window. It does not assert that energy is nondecreasing or that transport
absorption closes near the terminal time. No terminal full-H³ integrability.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact signed physical expenditure throughout the same first-crossing
annular PDE window. The alternative does not assume the sign of E'. -/
def h3CriticalMinimalShellSignedTransportBudgetAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
    (deriv (velocityH3EnergyAt u) s + ((n : ℝ) + 1) ^ 3 <
      -velocityH3TransportDerivativeAt u s) ∧
    (deriv (velocityH3EnergyAt u) s ≤ -(((n : ℝ) + 1) ^ 3 / 2) ∨
      ((n : ℝ) + 1) ^ 3 / 2 <
        h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∧
    (0 ≤ deriv (velocityH3EnergyAt u) s →
      ((n : ℝ) + 1) ^ 6 ≤
        h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3EnergyAt u s) ^ 3)

/-- The original minimal first-crossing certificate already provides a
strict full-physical-H³ dissipation floor on every point in its PDE window.
Exact H³ balance turns that floor into signed transport, drain/Riccati, and
nondecreasing-energy cubic amplitude costs, without new PDE assumptions. -/
theorem h3Critical_minimalShellExactWindow_forces_signedTransportBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N m : ℕ) (C δ : ℝ)
    (hWindow : h3CriticalMinimalShellEnergyWindow hH3 t n N m C δ) :
    h3CriticalMinimalShellSignedTransportBudgetAt hH3 t n δ := by
  rcases hWindow with ⟨_, _, _, _, _, hEnd, _, _, _, _, hBandFloor, _, _, _, _⟩
  intro s hs
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let H : ℝ := R ^ 3 / 2
  have hFullBand :
      h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 s) ≤
      velocityH3DissipationAt u s :=
    h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass s hsClass R Q
  have hAnnular : H <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
    simpa only [H, R, Q] using hBandFloor s hs
  have hFloor : H < velocityH3DissipationAt u s :=
    lt_of_lt_of_le hAnnular hFullBand
  have hSigned := h3Critical_fullDissipationFloor_forces_signedH3Transport
    hH3 hClass hsClass H hFloor
  have hAlternative := h3Critical_fullDissipationFloor_signedDrainOrRiccati
    hH3 hClass hsClass H hFloor
  have hHnonneg : 0 ≤ H := by dsimp only [H, R]; positivity
  have hCubic (hSlope : 0 ≤ deriv (velocityH3EnergyAt u) s) :
      R ^ 6 ≤ h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3EnergyAt u s) ^ 3 := by
    have hCost := h3Critical_fullDissipationFloor_nondecreasing_forces_cubicH3Energy
      hH3 hClass hsClass H hHnonneg hFloor hSlope
    have hPower : R ^ 6 = 4 * H ^ 2 := by dsimp only [H]; ring
    rw [hPower]
    exact hCost
  have hSigned' :
      deriv (velocityH3EnergyAt u) s + R ^ 3 <
        -velocityH3TransportDerivativeAt u s := by
    have hTwo : 2 * H = R ^ 3 := by dsimp only [H]; ring
    rw [hTwo] at hSigned
    exact hSigned
  refine ⟨?_, ?_, ?_⟩
  · simpa only [R] using hSigned'
  · simpa only [H, R] using hAlternative
  · intro hSlope
    exact (by simpa only [R] using hCubic hSlope)

/-- The previous unconditional normalized energy/width inequality and the
sixth/ninth physical rate gate now live on the EXACT SAME strictly disjoint
minimal-shell windows as a signed transport expenditure of at least R³.
At nondecreasing-energy slices a cubic physical energy cost is mandatory;
negative-energy-derivative slices remain a separate, legitimate channel. -/
theorem h3Critical_noL2Trace_disjointMinimalShell_energyWidth_signedTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      (∀ q : ℕ,
        (∑ k ∈ Finset.range q,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range q,
          (∫ s in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (∀ k : ℕ,
        1 < 4 * (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1)) *
          (((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) ^ 2 ∧
        ∀ D : ℝ,
          D * ((v k : ℝ) + 1) < ((N (v k) - v k : ℕ) : ℝ) ∨
          1 < 4 * (D + 2) ^ 2 *
            (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1))) ∧
      (∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellSignedTransportBudgetAt
          hH3 (t (v k)) (v k) (δ (v k))) := by
  obtain ⟨t, N, m, C, δ, v, j, hv, hCofinal, hSeparated,
      hWindows, hSum, hRates, hShell, hEnergyWidth⟩ :=
    h3Critical_noL2Trace_disjointMinimalShell_energyWidthUncertainty
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hNhds : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hCofinal.eventually hNhds
  have hSigned : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellSignedTransportBudgetAt
        hH3 (t (v k)) (v k) (δ (v k)) := by
    filter_upwards [hTailTime] with k hta
    have hData := hWindows k
    have hEnd : t (v k) + δ (v k) < T := by
      rcases hData with ⟨_, _, _, _, _, hEnd, _⟩
      exact hEnd
    have hPositive : 0 < δ (v k) := by
      rcases hData with ⟨_, _, _, _, hδ, _⟩
      exact hδ
    have ht : t (v k) ∈ Set.Ioo a T := by
      constructor
      · exact hta
      · linarith only [hPositive, hEnd]
    exact h3Critical_minimalShellExactWindow_forces_signedTransportBudget
      hH3 hClass (t (v k)) ht (v k) (N (v k)) (m (v k))
      (C (v k)) (δ (v k)) (hWindows k)
  exact ⟨t, N, m, C, δ, v, j, hv, hCofinal, hSeparated,
    hWindows, hSum, hRates, hShell, hEnergyWidth, hSigned⟩

end
end PrimeTensor.Bridge.Euclidean
