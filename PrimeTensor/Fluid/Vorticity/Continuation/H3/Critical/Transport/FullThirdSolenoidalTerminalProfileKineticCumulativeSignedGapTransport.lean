import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticDynamicSignedTransportBudget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAutomaticIntegratedGapTransport
import Mathlib.Tactic

/-!
# Cumulative signed H3 replenishment on the exact kinetic annular PDE clocks

The previous physical kinetic windows carry a persistent full-H3 dissipation
floor and a rigorous signed energy/transport identity. It is not legitimate
to eliminate either the energy-drain arm or the nonlinear replenishment arm
at a single window using merely raw Fourier L2 tightness.

Here the original windows are linked by their actual intervening time gaps.
On each kinetic window either the physical H3 Riccati energy scale is attained,
or the actual energy decreases by the certified annular viscous charge. The
exact physical signed PDE identity on each inter-window gap bounds any
subsequent replenishment by its integrated *positive signed transport surplus*

  max 0 (-velocityH3TransportDerivativeAt - 2*velocityH3DissipationAt).

Consequently at every finite stage either an actual Riccati-scale H3 state
occurs on an ORIGINAL kinetic window, or all certified physical viscous costs
are paid by initial H3 energy and the signed positive surplus on ORIGINAL
intervening gaps. No outer cutoff cap, terminal H3 trace, global signed-flux
integrability, or assumed monotonicity of H3 energy is introduced.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A kinetic PDE persistence window incurs a whole physical H3 energy drain
unless at some time its genuine cubic Riccati nonlinearity is at least the
annular dissipation floor. The physical mean-value theorem is applied to the
actual differentiable H3 energy, not to the unweighted momentum source. -/
theorem thirdFullPhysical_kineticWindow_riccatiOrSecantDrain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (n N : ℕ) (M δ : ℝ)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ) :
    (∃ s : ℝ, s ∈ Set.Icc x (x + δ) ∧
      M / 4 < h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      δ * (M / 4) + velocityH3EnergyAt u (x + δ) ≤
        velocityH3EnergyAt u x := by
  obtain ⟨_hnN, hδ, _hExact, hEnd, hFloor, _hCost⟩ := hWindow
  have hStart : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hFinish : x + δ ∈ Set.Ioo a T :=
    ⟨by linarith only [hStart.1, hδ], hEnd⟩
  have hDiff (s : ℝ) (hs : s ∈ Set.Icc x (x + δ)) :
      DifferentiableAt ℝ (velocityH3EnergyAt u) s := by
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hStart.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
    exact h3Critical_actualH3Energy_differentiableAt_onStrict
      hH3 hClass hsClass
  obtain ⟨s, hs, hSecant⟩ :=
    h3Critical_scalar_gapEnergy_exactMeanValueSecant
      (velocityH3EnergyAt u) x (x + δ)
      (by linarith only [hδ]) hDiff
  have hsClosed : s ∈ Set.Icc x (x + δ) := ⟨hs.1.le, hs.2.le⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hStart.1 hsClosed.1,
      lt_of_le_of_lt hsClosed.2 hEnd⟩
  have hFullFloor : M / 4 < velocityH3DissipationAt u s :=
    lt_of_lt_of_le (hFloor s hsClosed).1 (hFloor s hsClosed).2
  rcases h3Critical_fullDissipationFloor_signedDrainOrRiccati
      hH3 hClass hsClass (M / 4) hFullFloor with hDrain | hRiccati
  · right
    have hScaled := mul_le_mul_of_nonneg_left hDrain hδ.le
    have hSecant' :
        velocityH3EnergyAt u (x + δ) - velocityH3EnergyAt u x =
          δ * deriv (velocityH3EnergyAt u) s := by
      convert hSecant using 1 <;> ring
    linarith only [hScaled, hSecant']
  · exact Or.inl ⟨s, hsClosed, hRiccati⟩

/-- Finite cumulative account on the ORIGINAL kinetic-selected windows.
The physical signed H3 transport surplus on each actual inter-window gap
pays any H3 energy restored after the preceding certified viscous drain.
The required gap integrability and FTC are already established for compact
strict preterminal times, without global signed transport integrability. -/
theorem thirdFullPhysical_kineticDisjoint_cumulativeSignedGapBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k))) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧
        ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
          M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      (∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
        velocityH3EnergyAt u (τ (v 0)) +
        ∑ k ∈ Finset.range m,
          ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
            max 0 (-velocityH3TransportDerivativeAt u s -
              2 * velocityH3DissipationAt u s) := by
  let x : ℕ → ℝ := fun k => velocityH3EnergyAt u (τ (v k))
  let y : ℕ → ℝ := fun k => velocityH3EnergyAt u (τ (v k) + δ (v k))
  let c : ℕ → ℝ := fun k => δ (v k) * (M (v k) / 4)
  let g : ℕ → ℝ := fun k =>
    ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
      max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)
  let P : ℕ → Prop := fun k =>
    ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
      M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s
  have hStep (k : ℕ) : P k ∨ c k + y k ≤ x k := by
    obtain ⟨hStart, hWindow⟩ := hWindows k
    have hAlternative := thirdFullPhysical_kineticWindow_riccatiOrSecantDrain244
      hH3 hClass b hb (τ (v k)) hStart
      (v k) (N (v k)) (M (v k)) (δ (v k)) hWindow
    simpa only [P, c, x, y] using hAlternative
  have hGapStart (k : ℕ) :
      τ (v k) + δ (v k) ∈ Set.Ioo a T := by
    obtain ⟨ht, hWitness⟩ := hWindows k
    rcases hWitness with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, ht.1, hδ], hEnd⟩
  have hGapFinish (k : ℕ) :
      τ (v (k + 1)) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hGap (k : ℕ) : x (k + 1) - y k ≤ g k := by
    dsimp only [x, y, g]
    exact h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
      hH3 hClass _ _ (hGapStart k) (hGapFinish k)
      (hSeparated k (k + 1) (Nat.lt_succ_self k))
  intro m
  have hAccount := h3Critical_scalar_finiteDrainOrReplenishmentAccounting
    x y c g P hStep hGap m
  rcases hAccount with ⟨k, hk, hp⟩ | hBound
  · exact Or.inl ⟨k, hk, by simpa only [P] using hp⟩
  · right
    have hLast : 1 ≤ y m := by
      dsimp only [y]
      exact one_le_velocityH3EnergyAt u (τ (v m) + δ (v m))
    have hBudget :
        (∑ k ∈ Finset.range (m + 1), c k) + 1 ≤
          x 0 + ∑ k ∈ Finset.range m, g k := by
      calc
        (∑ k ∈ Finset.range (m + 1), c k) + 1 ≤
            (∑ k ∈ Finset.range (m + 1), c k) + y m :=
          (by simpa only [add_comm] using
            (add_le_add_left hLast (∑ k ∈ Finset.range (m + 1), c k)))
        _ ≤ x 0 + ∑ k ∈ Finset.range m, g k := hBound
    simpa only [c, x, g] using hBudget

/-- Combine the cumulative signed transport-gap account with the SAME
physical kinetic annular witnesses already carrying uniform moving raw
Fourier tightness, source L1 decay, and integrated signed window costs.
There is no new choice of frequency cutoff, time or persistence width. -/
theorem thirdFullPhysical_noH3Trace_kineticCumulativeSignedGapObstruction244
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
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
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
      (∀ m : ℕ,
        (∃ k : ℕ, k ≤ m ∧
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            M (v k) / 4 < h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (∑ k ∈ Finset.range (m + 1), δ (v k) * (M (v k) / 4)) + 1 ≤
          velocityH3EnergyAt u (τ (v 0)) +
          ∑ k ∈ Finset.range m,
            ∫ s in (τ (v k) + δ (v k))..τ (v (k + 1)),
              max 0 (-velocityH3TransportDerivativeAt u s -
                2 * velocityH3DissipationAt u s)) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, _hHeight, _hSigned⟩ :=
    thirdFullPhysical_noH3Trace_kineticDynamicSignedWindowObstruction244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hWindows (k : ℕ) :
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)) :=
    ⟨(hTimes k).2.1, (hTimes k).2.2⟩
  have hAccount := thirdFullPhysical_kineticDisjoint_cumulativeSignedGapBudget244
    hH3 hClass b hb M τ N δ v hSeparated hWindows
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, hAccount⟩

end
end PrimeTensor.FirstMonomialTriad
