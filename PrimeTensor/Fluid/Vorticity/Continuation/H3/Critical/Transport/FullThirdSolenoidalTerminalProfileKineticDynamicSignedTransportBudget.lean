import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticDynamicRawWindowTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSignedEnergyCompetition
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakAutomaticIntegratedTransport244
import Mathlib.Tactic

/-!
# Exact signed H³ transport accounting on the dynamically tight kinetic windows

The accepted actual kinetic H³ annular clocks carry a strictly positive
physical fourth-order dissipation floor at EVERY time. Their raw Fourier
kinetic carriers and their absolute physical projected-source actions vanish
under finite ordinary full H³ dissipation. Neither of these L² observations
controls the signed, differentiated cubic H³ transport by itself.

This file uses instead the exact physical H³ balance and the previously
verified automatic compact-time transport integrability. On EACH ORIGINAL
kinetic window the physical viscous charge is paid by genuine H³ energy drain
or by the signed negative transport integral. Both possibilities remain;
no sign is assigned to the physical derivative or to the nonlinear flux.

The final no-terminal-H³-trace theorem retains the SAME kinetic-selected
radii, strictly disjoint intervals, extended global dissipation packing,
vanishing projected-source L¹ action and uniform dynamic raw Fourier
concentration as the earlier accepted theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Two viscous copies in the exact signed energy identity force either one
full charge of physical energy drain or one full charge of adverse signed
transport. The disjunction is exhaustive even if the signed flux oscillates. -/
theorem thirdFull_scalar_doubleViscousCharge_signedDrainOrFlux244
    (A B F q : ℝ)
    (hBudget : 2 * q ≤ A - B - F) :
    q ≤ A - B ∨ q ≤ -F := by
  by_cases hDrain : q ≤ A - B
  · exact Or.inl hDrain
  · right
    have hNotDrain : A - B < q := lt_of_not_ge hDrain
    linarith only [hBudget, hNotDrain]

/-- Integrated exact physical H³ expenditure on one of the existing
kinetic-selected PDE windows. Every actual viscous annular floor contributes
twice to the energy identity. If the weighted H³ energy does not lose one
full window charge, the SIGNED nonlinear transport integral is negative by
at least that charge. At every point the same window also pays the stronger
pointwise physical signed transport/Riccati alternative.

The finite-dissipation premise is used for the already proved compact-time
signed transport integral identity, not as a hidden endpoint H³ ceiling. -/
theorem thirdFullPhysical_kineticWindow_signedIntegratedBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (n N : ℕ) (M δ : ℝ)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ) :
    δ * (M / 4) ≤
      ∫ s in x..(x + δ), velocityH3DissipationAt u s ∂volume ∧
    2 * (δ * (M / 4)) ≤
      velocityH3EnergyAt u x - velocityH3EnergyAt u (x + δ) -
      (∫ s in x..(x + δ), velocityH3TransportDerivativeAt u s ∂volume) ∧
    (δ * (M / 4) ≤
        velocityH3EnergyAt u x - velocityH3EnergyAt u (x + δ) ∨
      δ * (M / 4) ≤
        -(∫ s in x..(x + δ), velocityH3TransportDerivativeAt u s ∂volume)) ∧
    (∀ s : ℝ, s ∈ Set.Icc x (x + δ) →
      (deriv (velocityH3EnergyAt u) s + M / 2 <
        -velocityH3TransportDerivativeAt u s) ∧
      (deriv (velocityH3EnergyAt u) s ≤ -(M / 4) ∨
        M / 4 < h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s)) := by
  obtain ⟨_hnN, hδ, _hExact, hEnd, hFloor, _hCost⟩ := hWindow
  have hStart : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hFinish : x + δ ∈ Set.Ioo a T := by
    exact ⟨by linarith only [hStart.1, hδ], hEnd⟩
  have hDLocal : IntervalIntegrable
      (velocityH3DissipationAt u) volume x (x + δ) := by
    apply hDInt.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hδ.le),
      Set.uIcc_of_le hClass.terminal_start.2.le]
    exact Set.Icc_subset_Icc hStart.1.le hEnd.le
  have hFullFloor (s : ℝ) (hs : s ∈ Set.Icc x (x + δ)) :
      M / 4 < velocityH3DissipationAt u s :=
    lt_of_lt_of_le (hFloor s hs).1 (hFloor s hs).2
  have hCharge :
      δ * (M / 4) ≤
        ∫ s in x..(x + δ), velocityH3DissipationAt u s ∂volume := by
    have hIntegral := h3Path_localPositiveHeight_forces_integratedCost244
      (velocityH3DissipationAt u) x (x + δ) (M / 4)
      (le_add_of_nonneg_right hδ.le) hDLocal
      (fun s hs => (hFullFloor s hs).le)
    calc
      δ * (M / 4) = ((x + δ) - x) * (M / 4) := by ring
      _ ≤ ∫ s in x..(x + δ), velocityH3DissipationAt u s ∂volume :=
        hIntegral
  have hSigned :=
    h3Path_canonicalSignedTransportResidual_eq_integral_automatic244
      hH3 hClass hDInt x (x + δ) hStart hFinish
      (by linarith only [hδ])
  have hDouble :
      2 * (δ * (M / 4)) ≤
        velocityH3EnergyAt u x - velocityH3EnergyAt u (x + δ) -
        (∫ s in x..(x + δ), velocityH3TransportDerivativeAt u s ∂volume) := by
    calc
      2 * (δ * (M / 4)) ≤
          2 * (∫ s in x..(x + δ), velocityH3DissipationAt u s ∂volume) :=
        mul_le_mul_of_nonneg_left hCharge (by norm_num)
      _ = velocityH3EnergyAt u x - velocityH3EnergyAt u (x + δ) -
          (∫ s in x..(x + δ), velocityH3TransportDerivativeAt u s ∂volume) := by
        linarith only [hSigned]
  have hFork := thirdFull_scalar_doubleViscousCharge_signedDrainOrFlux244
    (velocityH3EnergyAt u x) (velocityH3EnergyAt u (x + δ))
    (∫ s in x..(x + δ), velocityH3TransportDerivativeAt u s ∂volume)
    (δ * (M / 4)) hDouble
  refine ⟨hCharge, hDouble, hFork, ?_⟩
  intro s hs
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hStart.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hSignedPoint := h3Critical_fullDissipationFloor_forces_signedH3Transport
    hH3 hClass hsClass (M / 4) (hFullFloor s hs)
  have hRiccati := h3Critical_fullDissipationFloor_signedDrainOrRiccati
    hH3 hClass hsClass (M / 4) (hFullFloor s hs)
  have hHalf : 2 * (M / 4) = M / 2 := by ring
  rw [hHalf] at hSignedPoint
  exact ⟨hSignedPoint, hRiccati⟩

/-- The signed expenditure is synchronized with the previously proved
uniform raw kinetic tightness and vanishing projected-source L¹ action on
EXACTLY the same cofinal kinetic windows. Finite ordinary H³ dissipation
and failure of the strong weighted terminal H³ trace remain explicit.

This is a genuine signed-energy dichotomy: it does not assert that the
energy-drain arm is impossible or that the negative signed flux is bounded
by the vanishing unweighted physical source action. -/
theorem thirdFullPhysical_noH3Trace_kineticDynamicSignedWindowObstruction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) *
            ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          M (v k) / (((N (v k) : ℝ) + 2) ^ 8) < ε ∧
          M (v k) / 4 < 4 * (((N (v k) : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ k : ℕ,
        2 * (δ (v k) * (M (v k) / 4)) ≤
          velocityH3EnergyAt u (τ (v k)) -
          velocityH3EnergyAt u (τ (v k) + δ (v k)) -
          (∫ s in τ (v k)..(τ (v k) + δ (v k)),
            velocityH3TransportDerivativeAt u s ∂volume) ∧
        (δ (v k) * (M (v k) / 4) ≤
            velocityH3EnergyAt u (τ (v k)) -
              velocityH3EnergyAt u (τ (v k) + δ (v k)) ∨
          δ (v k) * (M (v k) / 4) ≤
            -(∫ s in τ (v k)..(τ (v k) + δ (v k)),
              velocityH3TransportDerivativeAt u s ∂volume)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          (deriv (velocityH3EnergyAt u) s + M (v k) / 2 <
            -velocityH3TransportDerivativeAt u s) ∧
          (deriv (velocityH3EnergyAt u) s ≤ -(M (v k) / 4) ∨
            M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s))) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hWindows, hCharges, hL1, hUniform, hHeight⟩ :=
    thirdFullPhysical_noH3Trace_kineticDynamicRawWindowConcentration244
      hH3 hClass b hb hNoTrace hDInt M hM
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hWindows, hCharges, hL1, hUniform, hHeight, ?_⟩
  intro k
  obtain ⟨_hCharge, hDouble, hFork, hPointwise⟩ :=
    thirdFullPhysical_kineticWindow_signedIntegratedBudget244
      hH3 hClass hDInt b hb (τ (v k)) (hWindows k).2.1
      (v k) (N (v k)) (M (v k)) (δ (v k)) (hWindows k).2.2
  exact ⟨hDouble, hFork, hPointwise⟩

end
end PrimeTensor.FirstMonomialTriad
