import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakTransportSpike244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFastDecayRadialSynchronization244
import Mathlib.Tactic

/-!
# Canonical transport spike: the physical Landau ceiling forces H³ overshoot or slow clock

The canonical half-loss theorem forces a *positive* signed transport spike
    H A² < 8 (B+1) Tr(q).
The preexisting, genuine physical Landau commutator estimate bounds
    Tr(q) ≤ 4422 (1+C₁ sqrt(E₃(q))) E₃(q).

Crucially A is the product SUP norm of the three spectral velocity components:
the exact energy identity is E₃(s) = 1 + Σⱼ ‖Gⱼ(s)‖², NOT 1+A².
The proven three-component comparison gives E₃(s) ≤ 1+3A².
If E₃(q) ≤ E₃(s) and A≥2, it follows that E₃(q) ≤ 4A² and
sqrt(E₃(q)) ≤ 2A. Hence the transport spike is only possible if
    H < 32 (B+1) 4422 (1+2 C₁ A).
Thus the fast-clock arm forces an actual energy overshoot E₃(q)>E₃(s),
while the transport spike and root-free fourteen-power constraint remain true.

This is an exact necessary physical dichotomy; no new peak times are selected.
It does not alone bound the overshoot or establish terminal regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A positive transport spike with Landau's E^(3/2) ceiling cannot occur
at an energy no larger than 1+3A² when the optimized clock outruns the
explicit linear-in-A threshold. -/
theorem h3Path_scalarLandauSpike_energyOvershoot_or_slowClock244
    (A B H C E Tr : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hSpike : H * A ^ 2 < 8 * (B + 1) * Tr)
    (hLandau : Tr ≤ 4422 * (1 + C * Real.sqrt E) * E) :
    1 + 3 * A ^ 2 < E ∨
      H < 32 * (B + 1) * 4422 * (1 + 2 * C * A) := by
  by_cases hOvershoot : 1 + 3 * A ^ 2 < E
  · exact Or.inl hOvershoot
  · right
    have hCap : E ≤ 1 + 3 * A ^ 2 := le_of_not_gt hOvershoot
    have hAOne : 1 ≤ A ^ 2 := by
      nlinarith only [hA, sq_nonneg (A - 1)]
    have hFour : E ≤ 4 * A ^ 2 := by linarith only [hCap, hAOne]
    have hRoot : Real.sqrt E ≤ 2 * A := by
      have hRootSq := Real.sq_sqrt hE
      have hRootNN := Real.sqrt_nonneg E
      nlinarith only [hRootSq, hRootNN, hFour, hA]
    have hCoeff : 1 + C * Real.sqrt E ≤ 1 + 2 * C * A := by
      have hScaled := mul_le_mul_of_nonneg_left hRoot hC
      nlinarith only [hScaled]
    have hFactor : 0 ≤ 4422 * (1 + C * Real.sqrt E) := by positivity
    have hCoeffScaled :
        4422 * (1 + C * Real.sqrt E) ≤ 4422 * (1 + 2 * C * A) := by
      nlinarith only [hCoeff]
    have hTransportUpper :
        Tr ≤ 4422 * (1 + 2 * C * A) * (4 * A ^ 2) := by
      calc
        Tr ≤ 4422 * (1 + C * Real.sqrt E) * E := hLandau
        _ ≤ 4422 * (1 + C * Real.sqrt E) * (4 * A ^ 2) :=
          mul_le_mul_of_nonneg_left hFour hFactor
        _ ≤ 4422 * (1 + 2 * C * A) * (4 * A ^ 2) :=
          mul_le_mul_of_nonneg_right hCoeffScaled (by positivity)
    have hBudgetFactor : 0 ≤ 8 * (B + 1) := by positivity
    have hSpUpper :
        H * A ^ 2 < 8 * (B + 1) *
          (4422 * (1 + 2 * C * A) * (4 * A ^ 2)) :=
      lt_of_lt_of_le hSpike
        (mul_le_mul_of_nonneg_left hTransportUpper hBudgetFactor)
    have hFactored :
        H * A ^ 2 <
          (32 * (B + 1) * 4422 * (1 + 2 * C * A)) * A ^ 2 := by
      calc
        _ < 8 * (B + 1) *
          (4422 * (1 + 2 * C * A) * (4 * A ^ 2)) := hSpUpper
        _ = _ := by ring
    have hApos : 0 < A ^ 2 := by
      have ha : 0 < A := by linarith only [hA]
      exact pow_pos ha _
    by_contra hNot
    have hSlow :
        32 * (B + 1) * 4422 * (1 + 2 * C * A) ≤ H :=
      le_of_not_gt hNot
    have hScaled := mul_le_mul_of_nonneg_right hSlow hApos.le
    exact (not_lt_of_ge hScaled) hFactored

/-- The *actual* transport-spike witness either exceeds the physical H³
energy at its source-maximizing starting time or the optimized clock is
at most linear in the starting spectral SUP norm. -/
theorem h3Path_physicalTransportSpike_energyOvershoot_or_slowClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s q A B H : ℝ)
    (hs : s ∈ Set.Ioo a T) (hq : q ∈ Set.Ioo a T)
    (hA : A = ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hTwo : 2 ≤ A) (hB : 0 ≤ B)
    (hSpike : H * A ^ 2 <
      8 * (B + 1) * velocityH3TransportDerivativeAt u q) :
    velocityH3EnergyAt u s < velocityH3EnergyAt u q ∨
      H < 32 * (B + 1) * 4422 *
        (1 + 2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * A) := by
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hEs := h3AuditActualSpectralVelocityTotal_energy_exact hH3 s hsAbs
  have hSup := h3Path_spectralSquareEnergy_le_threeSupSquare244
    (h3AuditActualSpectralVelocityTotal hH3 s)
  have hEStartBound : velocityH3EnergyAt u s ≤ 1 + 3 * A ^ 2 := by
    rw [hA]
    linarith only [hEs, hSup]
  have hPhysicalLandau := h3Path_physicalFullTransport_abs_le_sqrtEnergy244
    hH3 hClass hq
  have hLandau : velocityH3TransportDerivativeAt u q ≤
      4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u q)) * velocityH3EnergyAt u q :=
    (le_abs_self _).trans hPhysicalLandau
  have hENonneg : 0 ≤ velocityH3EnergyAt u q :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u q)
  have hCNonneg : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  by_cases hOvershoot : velocityH3EnergyAt u s < velocityH3EnergyAt u q
  · exact Or.inl hOvershoot
  · right
    have hCap : velocityH3EnergyAt u q ≤ 1 + 3 * A ^ 2 := by
      have hNo := le_of_not_gt hOvershoot
      linarith only [hNo, hEStartBound]
    have hScalar := h3Path_scalarLandauSpike_energyOvershoot_or_slowClock244
      A B H h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      (velocityH3EnergyAt u q) (velocityH3TransportDerivativeAt u q)
      hTwo hB hCNonneg hENonneg hSpike hLandau
    exact hScalar.elim (fun h => False.elim ((not_lt_of_ge hCap) h)) id

/-- Sufficiently fast clock makes the energy overshoot compulsory at the
same actual physical transport-spike time. -/
theorem h3Path_physicalTransportSpike_forces_energyOvershoot_of_fastClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s q A B H : ℝ)
    (hs : s ∈ Set.Ioo a T) (hq : q ∈ Set.Ioo a T)
    (hA : A = ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hTwo : 2 ≤ A) (hB : 0 ≤ B)
    (hSpike : H * A ^ 2 <
      8 * (B + 1) * velocityH3TransportDerivativeAt u q)
    (hFast : 32 * (B + 1) * 4422 *
      (1 + 2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * A) ≤ H) :
    velocityH3EnergyAt u s < velocityH3EnergyAt u q := by
  rcases h3Path_physicalTransportSpike_energyOvershoot_or_slowClock244
    hH3 hClass s q A B H hs hq hA hTwo hB hSpike with hOvershoot | hSlow
  · exact hOvershoot
  · exact False.elim ((not_lt_of_ge hFast) hSlow)

/-- Preserve the original optimized canonical source peak and exact rate
witness: terminal compression, or half-loss with the signed transport spike
and an explicit physical energy-overshoot-versus-slow-clock alternative. -/
theorem h3Path_optimizedPeak_terminalCompression_or_transportLandauOvershoot244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hLarge : 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2)
    (hThreshold : 16 * (∫ t in a..T, velocityH3DissipationAt u t) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ∃ H : ℝ, 0 < H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      let B := ∫ t in a..T, velocityH3DissipationAt u t
      T - s ≤ (B + 1) / H ∨
        ∃ r q : ℝ,
          r ∈ Set.Icc s (s + (B + 1) / H) ∧
          q ∈ Set.Icc s r ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
          H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
            8 * (B + 1) * velocityH3TransportDerivativeAt u q ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 14 <
            8388608 * (velocityH3Energy0At u b + 1) *
              (B + 1) ^ 3 * velocityH3TransportDerivativeAt u q ^ 3 ∧
          (velocityH3EnergyAt u s < velocityH3EnergyAt u q ∨
            H < 32 * (B + 1) * 4422 *
              (1 + 2 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) := by
  obtain ⟨H, hH, hIdentity, hAlternative⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_transportSpike244
      hH3 hClass hDInt b hb s hs hTwo hLarge hThreshold
  let B : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ (B + 1) / H ∨
    ∃ r q : ℝ,
      r ∈ Set.Icc s (s + (B + 1) / H) ∧
      q ∈ Set.Icc s r ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
      H * ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 <
        8 * (B + 1) * velocityH3TransportDerivativeAt u q ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 14 <
        8388608 * (velocityH3Energy0At u b + 1) *
          (B + 1) ^ 3 * velocityH3TransportDerivativeAt u q ^ 3 at hAlternative
  rcases hAlternative with hCompression | ⟨r, q, hr, hq, hHalf, hSpike, hPoly⟩
  · exact Or.inl hCompression
  · by_cases hCompressed : T - s ≤ (B + 1) / H
    · exact Or.inl hCompressed
    · right
      have hEnd : s + (B + 1) / H < T := by
        have hShort := lt_of_not_ge hCompressed
        linarith only [hShort]
      have hsClass : s ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 hs.1, hs.2⟩
      have hqClass : q ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hsClass.1 hq.1,
          lt_of_le_of_lt (le_trans hq.2 hr.2) hEnd⟩
      have hB : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg hClass.terminal_start.2.le
          (fun t _ => velocityH3DissipationAt_nonneg u t)
      have hDichotomy := h3Path_physicalTransportSpike_energyOvershoot_or_slowClock244
        hH3 hClass s q ‖h3AuditActualSpectralVelocityTotal hH3 s‖ B H
        hsClass hqClass rfl hTwo hB hSpike
      exact ⟨r, q, hr, hq, hHalf, hSpike, hPoly, hDichotomy⟩

end
end PrimeTensor.FirstMonomialTriad
