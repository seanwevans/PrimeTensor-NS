import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralMovingRadialDissipation244
import Mathlib.Tactic

/-!
# Moving spectral cutoff with asymptotically dominant high-frequency H³ mass

The committed moving-radial construction retains a positive quantity of
weighted H³ mass outside the increasing cutoff |D(ξ)| ≥ n+1. We sharpen
its diagonal selection: the high-radial mass can be selected to exceed
(n+1) times the WHOLE low-radial mass, without any new dynamical assumption.

The substantive bridge is the established physical kinetic anchor:

  LowMass_ρ(S(t)) ≤ (1+ρ²+ρ⁴+ρ⁶) E₀(b),  b<t<T.

The cofinal high-radial escape theorem allows the requested threshold to
depend on n and on this explicit kinetic ceiling. Choosing that threshold
before selecting t_n gives

  (n+1) LowMass_(n+1)(S(t_n)) < HighMass_(n+1)(S(t_n)),
  (n+2) HighMass_(n+1)(S(t_n))
    > (n+1) SpectralSquareEnergy(S(t_n)),
  (n+1)^3 < velocityH3DissipationAt u t_n,
  dist t_n T < 1/(n+1).

Equivalently, the high-radial region carries more than (n+1)/(n+2)
OF THE TOTAL weighted H³ spectral square energy at the selected times.
No physical L² terminal-trace failure is inferred from H³ nonextension.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- If the high-radial mass exceeds (N+1) times a strict low-radial ceiling,
then its contribution to the total square energy is strictly greater than
(N+1)/(N+2). Written without division to avoid requiring a separate
positivity hypothesis for the total energy. -/
theorem h3Path_highRadialDominates_total_of_lowCeiling244
    (G : H3SpectralVelocityState)
    (ρ C N : ℝ)
    (hN : 0 ≤ N)
    (hLow : h3PathActualSpectralLowRadialSquareMass244 ρ G ≤ C)
    (hHigh : (N + 1) * (C + 1) <
      h3PathActualSpectralHighRadialRemainder244 ρ G) :
    (N + 2) * h3PathActualSpectralHighRadialRemainder244 ρ G >
      (N + 1) * h3SpectralVelocitySquareEnergy G := by
  have hScale : 0 ≤ N + 1 := by linarith
  have hScaled :
      (N + 1) * h3PathActualSpectralLowRadialSquareMass244 ρ G ≤
        (N + 1) * C :=
    mul_le_mul_of_nonneg_left hLow hScale
  have hMargin : (N + 1) * C < (N + 1) * (C + 1) := by
    nlinarith only [hScale, hN]
  have hDom :
      (N + 1) * h3PathActualSpectralLowRadialSquareMass244 ρ G <
        h3PathActualSpectralHighRadialRemainder244 ρ G :=
    lt_trans (lt_of_le_of_lt hScaled hMargin) hHigh
  unfold h3PathActualSpectralHighRadialRemainder244 at hDom ⊢
  nlinarith only [hDom]

/-- Failure of the terminal physical L² trace admits ONE moving-cutoff
sequence for which high-radial weighted H³ mass asymptotically dominates
the entire weighted H³ spectrum, while physical dissipation grows at least
cubically in the selected radial cutoff. -/
theorem h3Path_physicalNoL2Trace_forces_movingRadialHighDominanceSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ,
        dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 2) *
            h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
          ((n : ℝ) + 1) *
            h3SpectralVelocitySquareEnergy
              (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 < velocityH3DissipationAt u (τ n)) := by
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hClass.terminal_start.2]
  have hEnergy0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hChoice (n : ℕ) :
      ∃ t : ℝ,
        t ∈ Set.Ioo a T ∧
        dist t T < (1 : ℝ) / ((n : ℝ) + 1) ∧
        ((n : ℝ) + 2) *
            h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t) >
          ((n : ℝ) + 1) *
            h3SpectralVelocitySquareEnergy
              (h3AuditActualSpectralVelocityTotal hH3 t) ∧
        ((n : ℝ) + 1) ^ 3 < velocityH3DissipationAt u t := by
    let ρ : ℝ := (n : ℝ) + 1
    let ε : ℝ := 1 / ρ
    let C : ℝ :=
      h3TerminalRadialSobolevWeightSquareCeiling ρ * velocityH3Energy0At u b
    let c : ℝ := max b (T - ε)
    have hρ : 0 < ρ := by dsimp only [ρ]; positivity
    have hε : 0 < ε := by dsimp only [ε]; positivity
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact mul_nonneg
        (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le hEnergy0
    have hc : c ∈ Set.Ioo a T := by
      dsimp only [c]
      exact ⟨lt_of_lt_of_le hb.1 (le_max_left _ _),
        (max_lt_iff).2 ⟨hb.2, by linarith only [hε]⟩⟩
    obtain ⟨t, ht, hMass⟩ :=
      h3Path_physicalNoL2Trace_forces_highRadialFourierIntegralEscape244
        hH3 hClass hL hNoTrace ρ hρ.le c hc (ρ * (C + 1))
    have htTail : t ∈ Set.Ioo a T :=
      ⟨lt_trans hc.1 ht.1, ht.2⟩
    have htB : t ∈ Set.Ioo b T :=
      ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, ht.2⟩
    have hNear : T - ε < t :=
      lt_of_le_of_lt (le_max_right _ _) ht.1
    have hDist : dist t T < (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
      dsimp only [ε, ρ] at hNear
      linarith only [hNear]
    let G : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    have hHigh : ρ * (C + 1) <
        h3PathActualSpectralHighRadialRemainder244 ρ G := by
      rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
      exact hMass
    have hLow : h3PathActualSpectralLowRadialSquareMass244 ρ G ≤ C := by
      dsimp only [G, C]
      exact h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
        hH3 hClass b hb ρ hρ.le t htB
    have hDominance : (ρ + 1) *
        h3PathActualSpectralHighRadialRemainder244 ρ G >
          ρ * h3SpectralVelocitySquareEnergy G := by
      have h := h3Path_highRadialDominates_total_of_lowCeiling244
        G ρ C (n : ℝ) (Nat.cast_nonneg n) hLow (by
          simpa only [ρ] using hHigh)
      simpa only [ρ, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using h
    have hHighSimple : ρ < h3PathActualSpectralHighRadialRemainder244 ρ G := by
      have hLower : ρ ≤ ρ * (C + 1) := by
        nlinarith only [mul_nonneg hρ.le hC]
      exact lt_of_le_of_lt hLower hHigh
    have hD : ρ ^ 2 * h3PathActualSpectralHighRadialRemainder244 ρ G ≤
        velocityH3DissipationAt u t := by
      rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
      exact h3Path_physicalDissipation_ge_highRadialSpectralMass244
        hH3 hClass t htTail ρ hρ.le
    have hCubic : ρ ^ 3 < velocityH3DissipationAt u t := by
      calc
        ρ ^ 3 = ρ ^ 2 * ρ := by ring
        _ < ρ ^ 2 * h3PathActualSpectralHighRadialRemainder244 ρ G :=
          mul_lt_mul_of_pos_left hHighSimple (pow_pos hρ 2)
        _ ≤ velocityH3DissipationAt u t := hD
    refine ⟨t, htTail, hDist, ?_, ?_⟩
    · simpa only [G, ρ, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
        using hDominance
    · simpa only [ρ] using hCubic
  choose τ hτ using hChoice
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hNormBound : ∀ n : ℕ,
      ‖τ n - T‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    simpa only [Real.norm_eq_abs, Real.dist_eq] using
      (le_of_lt (hτ n).2.1)
  have hTendsto : Tendsto τ atTop (𝓝 T) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (τ n - T)))
        (Filter.Eventually.of_forall hNormBound)
        hInv)
  exact ⟨τ, (fun n => (hτ n).1), (fun n => (hτ n).2.1),
    hTendsto, (fun n => (hτ n).2.2.1), (fun n => (hτ n).2.2.2)⟩

end
end PrimeTensor.FirstMonomialTriad
