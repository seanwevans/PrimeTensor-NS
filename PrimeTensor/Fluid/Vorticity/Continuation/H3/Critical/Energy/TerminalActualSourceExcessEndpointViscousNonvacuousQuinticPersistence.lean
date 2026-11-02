import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularQuinticRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularPDEPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.Tactic

/-!
# Nonvacuous physical H³ annular persistence and a finite-dissipation guard

The existing PDE persistence gate does NOT assume terminal H³ dissipation
integrability. Using its actual source/state envelopes and the already proved
fifth-order cutoff bound, we obtain a concrete LOWER bound on its persistence
width without a terminal integrability premise.

In contrast, previous terminal summability/clock-rate/quintic-rate results
assumed no physical L² terminal trace AND finite terminal H³ dissipation.
Those two assumptions were already formally proved incompatible in
FiniteDissipationTerminalTrace. The third theorem states the incompatibility
explicitly to prevent further inferences from that empty conjunction.

No Navier--Stokes regularity or continuation is concluded by this module.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- An upper bound on a nonnegative PDE variation coefficient yields a lower
bound on its exact min-selected persistence radius. No temporal integral is
used. -/
theorem h3Critical_scalar_quinticRate_lowerPersistence
    (d H Λ P θ : ℝ)
    (hH : 0 ≤ H) (hΛ : 0 ≤ Λ) (hP : Λ ≤ P)
    (hθ : θ = min (d / 2) ((H / 4) / (2 * (Λ + 1)))) :
    min (d / 2) ((H / 4) / (2 * (P + 1))) ≤ θ := by
  have hΛPlus : 0 < Λ + 1 := by linarith only [hΛ]
  have hPPlus : 0 < P + 1 := by linarith only [hΛ, hP]
  have hDen : 2 * (Λ + 1) ≤ 2 * (P + 1) := by
    linarith only [hP]
  have hDiv : (H / 4) / (2 * (P + 1)) ≤
      (H / 4) / (2 * (Λ + 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (P + 1))
      (by positivity : 0 < 2 * (Λ + 1))).2
    exact mul_le_mul_of_nonneg_left hDen (by positivity : 0 ≤ H / 4)
  calc
    min (d / 2) ((H / 4) / (2 * (P + 1))) ≤
        min (d / 2) ((H / 4) / (2 * (Λ + 1))) :=
      min_le_min le_rfl hDiv
    _ = θ := hθ.symm

/-- Same cofinal fivefold witnesses, actual projected-momentum source maximum,
actual spectral-state maximum and physical four-way gate. An ACTIVE spike
above twice the lower-band kinetic ceiling carries a NEW positive annular
persistence interval with an explicit minimum width. The denominator is now
the fifth-order polynomial physical-source/state frequency bound rather
than the opaque exact annular PDE variation coefficient. This result needs
NO finite terminal H³ dissipation assumption. -/
theorem h3Critical_noL2Trace_cofinalFivefold_nonvacuousQuinticPersistence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n)
    (R ε : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hε : ∀ k, 0 < ε k)
    (L : ℕ → ℕ) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + w (v k) < t (v l)) ∧
      (∀ k : ℕ,
        8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
          R k ^ 2 * ε k ^ 2 / 8 →
        η k = 0 ∨
        ∃ θ : ℝ, 0 < θ ∧
          min ((t (v k) + w (v k) - p k) / 2)
            (((R k ^ 2 * ε k ^ 2 / 8) / 4) /
              (2 * (24 *
                ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖ *
                ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
                (((N k : ℝ) + 2) ^ 5 + ((L k : ℝ) + 2) ^ 5) + 1))) ≤ θ ∧
          p k + θ < T ∧
          (∀ r : ℝ, r ∈ Set.Icc (p k) (p k + θ) →
            (R k ^ 2 * ε k ^ 2 / 8) / 4 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) -
              h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) -
              h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ≤
              velocityH3DissipationAt u r) ∧
          θ * ((R k ^ 2 * ε k ^ 2 / 8) / 4) ≤
            ∫ r in p k..(p k + θ),
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) -
              h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      (∀ k : ℕ,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, δ, p, η, N,
      hv, hLimit, hSep, hActive, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_PDEAnnularPersistenceGate
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε L
  refine ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hSep, ?_, hGate⟩
  intro k hThreshold
  rcases hActive k hThreshold with hInactive | hWitness
  · exact Or.inl hInactive
  · right
    obtain ⟨θ, hθPos, _hθHalf, hθEq, hθEnd, hθFloor, hθCost⟩ := hWitness
    let K : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
    let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
    let Lo : ℝ := (L k : ℝ) + 1
    let Hi : ℝ := (N k : ℝ) + 1
    let rate : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 Lo Hi K C
    let poly : ℝ := 24 * K * C * ((Hi + 1) ^ 5 + (Lo + 1) ^ 5)
    have hLo : 1 ≤ Lo := by
      dsimp only [Lo]
      have hn : (0 : ℝ) ≤ (L k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hHi : 1 ≤ Hi := by
      dsimp only [Hi]
      have hn : (0 : ℝ) ≤ (N k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hRateNonneg : 0 ≤ rate :=
      h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 Lo Hi K C
        (norm_nonneg _) (norm_nonneg _)
    have hRatePoly : rate ≤ poly :=
      h3Critical_annularPDE_variationRate_le_quinticPhysicalProduct
        Lo Hi K C hLo hHi (norm_nonneg _) (norm_nonneg _)
    have hHeight : 0 ≤ R k ^ 2 * ε k ^ 2 / 8 := by positivity
    have hWidthEq : θ = min ((t (v k) + w (v k) - p k) / 2)
        (((R k ^ 2 * ε k ^ 2 / 8) / 4) / (2 * (rate + 1))) := by
      simpa only [rate, Lo, Hi, K, C] using hθEq
    have hLower := h3Critical_scalar_quinticRate_lowerPersistence
      (t (v k) + w (v k) - p k) (R k ^ 2 * ε k ^ 2 / 8)
      rate poly θ hHeight hRateNonneg hRatePoly hWidthEq
    have hLower' :
        min ((t (v k) + w (v k) - p k) / 2)
          (((R k ^ 2 * ε k ^ 2 / 8) / 4) /
            (2 * (24 * K * C *
              (((N k : ℝ) + 2) ^ 5 + ((L k : ℝ) + 2) ^ 5) + 1))) ≤ θ := by
      simpa only [poly, Hi, Lo, show (N k : ℝ) + 1 + 1 = (N k : ℝ) + 2 by ring,
        show (L k : ℝ) + 1 + 1 = (L k : ℝ) + 2 by ring] using hLower
    exact ⟨θ, hθPos, hLower', hθEnd, hθFloor, hθCost⟩

/-- The earlier finite-terminal-dissipation + no-physical-L²-trace premise
is inconsistent under the same H³ energy class. Therefore summability
results built under both hypotheses must not be used as a new restriction
on the no-trace branch. -/
theorem h3Critical_noL2Trace_finiteDissipation_quinticBranch_inconsistent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    False :=
  h3Critical_noL2Trace_incompatible_with_finite_dissipation
    hH3 hClass hDInt hNoTrace

end
end PrimeTensor.Bridge.Euclidean
