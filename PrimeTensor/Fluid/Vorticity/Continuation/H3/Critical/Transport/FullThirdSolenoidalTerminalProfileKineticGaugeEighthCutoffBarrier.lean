import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticDisjointGlobalExtendedBudget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousPolynomialCutoffBarrier
import Mathlib.Tactic

/-!
# Kinetic eighth-power frequency barrier for the actual disjoint annular clocks

An actual finite-annulus H3-dissipation spike cannot be realized in an
arbitrarily small Fourier band while the physical kinetic anchor is fixed.
The existing radial kinetic estimate and the physical finite-annulus floor
show that every exact kinetic PDE-selected annular window of height M has

    M <= 16 E (N+1)^8,   E = velocityH3Energy0At u b.

This constraint is independent of the terminal time and any global H3
viscous-integrability hypothesis. It supplies the missing non-temporal
frequency-growth mechanism for our disjoint kinetic annular witnesses.

A preassigned natural-frequency gauge G(n) can be beaten unconditionally
on the no-terminal-H3-trace branch: choose the allowed height profile
M(n)=16 E (G(n)+1)^8 + 1. The previously constructed cofinal physical
windows, their EXACT PDE-selected widths, their strict separation, and
their global extended full-dissipation cost inequality remain unchanged.
Their capturing outer cutoff N(v(k)) must exceed G(v(k)) at every retained
index. This is an unconditional spectral escape statement, not a claim
that the height-width costs diverge.

With a separate finite GLOBAL extended dissipation bound C, any given
local kinetic window must satisfy either clock compression or an outer
cutoff above any gauge whose finite kinetic PDE-rate ceiling is too small.
This latter dichotomy explains why unconditional gauge escape alone does
not close the Navier--Stokes continuation problem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The actual PDE-selected natural annulus must have enough outer
Fourier bandwidth to carry its positive physical H3 dissipation floor.
This is an instantaneous kinetic-only inequality: no viscous time integral
or full-H3 state/source ceiling is used. -/
theorem thirdFullPhysical_kineticLocalWitness_eighthPowerHeightBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (n N : ℕ) (M δ : ℝ)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ) :
    M ≤ 16 * velocityH3Energy0At u b * ((N : ℝ) + 1) ^ 8 := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let E : ℝ := velocityH3Energy0At u b
  let Q : ℝ := (N : ℝ) + 1
  obtain ⟨_hnN, hδ, _hδEq, _hEnd, hFloor, _hCost⟩ := hWindow
  have hxWindow : x ∈ Set.Icc x (x + δ) :=
    ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩
  have hPeak : M / 4 <
      h3PathActualLowRadialDissipation244 Q U -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) U := by
    simpa only [Q, U] using (hFloor x hxWindow).1
  have hInner : 0 ≤
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) U := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg U ξ
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith only [hN]
  have hQNonneg : 0 ≤ Q := by linarith only [hQ]
  have hKinetic :
      h3PathActualLowRadialDissipation244 Q U ≤
        Q ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling Q * E) :=
    h3Path_actualLowRadialDissipation_le_kineticAnchor244
      hH3 hClass b hb Q hQNonneg x hx
  have hHeight : M / 4 ≤
      Q ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling Q * E) := by
    linarith only [hPeak, hInner, hKinetic]
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hEighth := h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower
    Q E (M / 4) hQ hE hHeight
  change M ≤ 16 * E * Q ^ 8
  nlinarith only [hEighth]

/-- A proposed Fourier cutoff below the kinetic eighth-power cost of a
captured height cannot be the actual outer radius. -/
theorem thirdFull_scalar_kineticEighthPower_forcesOuterCutoff244
    (E M : ℝ) (N G : ℕ) (hE : 0 ≤ E)
    (hCaptured : M ≤ 16 * E * ((N : ℝ) + 1) ^ 8)
    (hTall : 16 * E * ((G : ℝ) + 1) ^ 8 < M) :
    G < N := by
  by_contra hNot
  have hNG : N ≤ G := Nat.le_of_not_gt hNot
  have hCast : (N : ℝ) ≤ (G : ℝ) := by exact_mod_cast hNG
  have hRadius : (N : ℝ) + 1 ≤ (G : ℝ) + 1 := by
    linarith only [hCast]
  have hPow : ((N : ℝ) + 1) ^ 8 ≤ ((G : ℝ) + 1) ^ 8 :=
    pow_le_pow_left₀ (by positivity) hRadius 8
  have hFactor : 0 ≤ 16 * E := mul_nonneg (by norm_num) hE
  have hComparison := mul_le_mul_of_nonneg_left hPow hFactor
  linarith only [hCaptured, hTall, hComparison]

/-- A canonical positive height profile that necessarily forces a
capturing Fourier radius above the arbitrarily prescribed gauge G. -/
noncomputable def thirdFullPhysicalKineticGaugeHeight244
    (E : ℝ) (G : ℕ → ℕ) (n : ℕ) : ℝ :=
  16 * E * ((G n : ℝ) + 1) ^ 8 + 1

theorem thirdFullPhysicalKineticGaugeHeight_pos244
    (E : ℝ) (hE : 0 ≤ E) (G : ℕ → ℕ) (n : ℕ) :
    0 < thirdFullPhysicalKineticGaugeHeight244 E G n := by
  unfold thirdFullPhysicalKineticGaugeHeight244
  positivity

/-- An upper bound on the GLOBAL extended full-physical H3 dissipation
transfers to one locally certified kinetic clock, without a global L1
hypothesis. Either the actual terminal time compresses its large height,
or the outer frequency exceeds the proposed cutoff once the corresponding
finite kinetic-rate budget is too small. -/
theorem thirdFullPhysical_kineticGlobalBudget_clockOrOuterCutoff244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b x : ℝ) (n N G : ℕ) (M δ C : ℝ)
    (hax : a < x) (hM : 0 < M) (hC : 0 ≤ C)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ)
    (hGlobal :
      (∫⁻ r in Set.Ioo a T,
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
        ENNReal.ofReal C)
    (hRateSmall : 8 *
      ((∑ j ∈ Finset.range (G + 1),
          thirdFullPhysicalKineticLowBandDissipationRate244 j
            (velocityH3Energy0At u b)) +
        thirdFullPhysicalKineticLowBandDissipationRate244 n
          (velocityH3Energy0At u b) + 1) * C < (M / 2) ^ 2) :
    (T - x) * (M / 2) ≤ 16 * C ∨ G < N := by
  have hEnd : x + δ < T := by
    rcases hWindow with ⟨_, _, _, hEnd, _, _⟩
    exact hEnd
  have hSubset : Set.Ioc x (x + δ) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_trans hax hr.1, lt_of_le_of_lt hr.2 hEnd⟩
  have hLocal :
      (∫⁻ r in Set.Ioc x (x + δ),
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
        ENNReal.ofReal C :=
    (lintegral_mono_set hSubset).trans hGlobal
  have hFork := thirdFullPhysical_kineticAnnularExtendedBudget_clockOrRate244
    hH3 b x n N M δ C hM hC hWindow hLocal
  rcases hFork with hClock | hRate
  · exact Or.inl hClock
  · right
    let L : ℕ → ℝ := fun j =>
      thirdFullPhysicalKineticLowBandDissipationRate244 j
        (velocityH3Energy0At u b)
    have hL (j : ℕ) : 0 ≤ L j :=
      thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j _
    exact thirdFull_scalar_kineticAnnularRate_forces_outerCutoffEscape244
      L n N G (M / 2) C hL hC
      (by simpa only [L] using hRate)
      (by simpa only [L] using hRateSmall)

/-- HARD COFINAL CONSEQUENCE: for EVERY preassigned natural outer-frequency
gauge G, select the permitted height profile just above its eighth-power
kinetic ceiling. The original no-H3-trace arbitrary-height diagonal then
produces genuinely separated physical PDE annular windows whose capturing
outer cutoff N(v(k)) beats G(v(k)) at every retained index. Simultaneously
the same exact windows pay the ONE global extended full-H3 dissipation
budget, without assuming that budget is finite.

The output is an arbitrary-gauge concentration necessity, NOT a contradiction:
the outer cutoff can always move faster and the kinetic widths can shrink.
-/
theorem thirdFullPhysical_noH3Trace_kineticArbitraryGaugeEscapeGlobalCharges244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (G : ℕ → ℕ) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ G (v k) < N (v k)) ∧
      (∀ k : ℕ,
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (thirdFullPhysicalKineticGaugeHeight244
            (velocityH3Energy0At u b) G (v k)) (δ (v k))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal
            (thirdFullPhysicalKineticGaugeHeight244
              (velocityH3Energy0At u b) G (v k) / 4) *
            ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) := by
  let E : ℝ := velocityH3Energy0At u b
  let M : ℕ → ℝ := thirdFullPhysicalKineticGaugeHeight244 E G
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hM (n : ℕ) : 0 < M n :=
    thirdFullPhysicalKineticGaugeHeight_pos244 E hE G n
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hTimes⟩ :=
    thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244
      hH3 hClass b hb hNoTrace M hM
  have hGauge (k : ℕ) : G (v k) < N (v k) := by
    have hCeiling := thirdFullPhysical_kineticLocalWitness_eighthPowerHeightBound244
      hH3 hClass b hb (τ (v k)) (hTimes k).1
      (v k) (N (v k)) (M (v k)) (δ (v k)) (hTimes k).2
    have hTall : 16 * E * ((G (v k) : ℝ) + 1) ^ 8 < M (v k) := by
      dsimp only [M, thirdFullPhysicalKineticGaugeHeight244]
      linarith
    exact thirdFull_scalar_kineticEighthPower_forcesOuterCutoff244
      E (M (v k)) (N (v k)) (G (v k)) hE
      (by simpa only [E] using hCeiling) hTall
  let p : ℕ → ℝ := fun k => τ (v k)
  let w : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => M (v k) / 4
  have hStart (k : ℕ) : a < p k :=
    lt_trans hb.1 (hTimes k).1.1
  have hWidth (k : ℕ) : 0 ≤ w k := by
    rcases (hTimes k).2 with ⟨_, hp, _, _, _, _⟩
    exact hp.le
  have hEnd (k : ℕ) : p k + w k < T := by
    rcases (hTimes k).2 with ⟨_, _, _, hEnd, _, _⟩
    exact hEnd
  have hFloor (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (p k) (p k + w k)) :
      H k ≤ velocityH3DissipationAt u r := by
    rcases (hTimes k).2 with ⟨_, _, _, _, hWindowFloor, _⟩
    exact ((hWindowFloor r hr).1.le).trans (hWindowFloor r hr).2
  have hSep : ∀ k l : ℕ, k < l → p k + w k < p l :=
    hSeparated
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    (fun k => ⟨hIndex k, hGauge k⟩), (fun k => (hTimes k).2), ?_⟩
  intro m
  exact thirdFull_scalar_disjointWindows_le_globalExtendedBudget244
    (velocityH3DissipationAt u) a T p w H
    hStart hWidth hEnd hSep hFloor m

end
end PrimeTensor.FirstMonomialTriad
