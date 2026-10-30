import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetSpectralEnergyGate244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Excess.Full
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Seed.Tail.Control
import Mathlib.Tactic

/-!
# Higher radial spectral escape forces signed physical H3 growth nonintegrability

The canonical higher-budget spectral-energy theorem already proves energy
escape on the original cofinal exact-anchor windows under its explicit
higher-moment, attained-source, cutoff and noncompressed-time hypotheses.

An integrable positive logarithmic H3 growth rate on the SAME energy-class
tail gives canonical uniform H3 control via the established Gronwall theorem
and finite-coordinate bridge. The escaping cofinal energy contradicts that
uniform ceiling. The exact physical signed balance then identifies this
nonintegrable positive growth rate with the positive normalized transport
excess after paying BOTH copies of physical H3 dissipation.

No transport estimate, source ceiling, cutoff cap, or higher-moment
integrability is inferred from the Navier--Stokes energy balance.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Cofinal divergence of the genuine physical H3 energy is incompatible
with an integrable positive logarithmic H3 growth rate on the same tail.
This uses the established scalar Gronwall and coordinate-budget theorems. -/
theorem h3Path_cofinalPhysicalEnergyEscape_excludes_integrablePositiveLog244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hTendsto : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ¬ MeasureTheory.IntegrableOn
      (h3PathPositiveLogEnergyGrowthRate u) (Set.Ioo a T) := by
  intro hInt
  have hControl : TerminalTailH3Control u T :=
    terminalTailH3Control_of_integrablePositiveLogEnergyGrowthRateOnTail
      hH3 hClass hInt
  obtain ⟨b, M, hb, _hM, hTail⟩ :=
    canonicalH3Tail_of_terminalTailH3Control hControl
  have hLate : ∀ᶠ k : ℕ in atTop, b < t k :=
    hTendsto.eventually (Ioi_mem_nhds hb.2)
  have hBound : ∀ᶠ k : ℕ in atTop,
      velocityH3EnergyAt u (t k) ≤ M := by
    filter_upwards [hLate] with k hk
    exact (hTail (t k) ⟨hk.le, (ht k).2⟩).2
  have hLarge : ∀ᶠ k : ℕ in atTop,
      M + 1 ≤ velocityH3EnergyAt u (t k) :=
    hEscape.eventually (eventually_ge_atTop (M + 1))
  obtain ⟨k, hkLarge, hkBound⟩ := (hLarge.and hBound).exists
  linarith only [hkLarge, hkBound]

/-- The positive normalized energy derivative shares the same obstruction,
by the exact logarithmic chain rule already proved for an H3 path. -/
theorem h3Path_cofinalPhysicalEnergyEscape_excludes_integrableNormalizedGrowth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hTendsto : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ¬ MeasureTheory.IntegrableOn
      (h3PathPositiveEnergyGrowthRate u) (Set.Ioo a T) := by
  intro hInt
  have hLog : MeasureTheory.IntegrableOn
      (h3PathPositiveLogEnergyGrowthRate u) (Set.Ioo a T) :=
    IntegrableOn.congr_fun hInt
      (fun s hs =>
        (h3PathPositiveLogEnergyGrowthRate_eq_positiveEnergyGrowthRate
          hH3 hClass hs).symm)
      measurableSet_Ioo
  exact (h3Path_cofinalPhysicalEnergyEscape_excludes_integrablePositiveLog244
    hH3 hClass t ht hTendsto hEscape) hLog

/-- The exact signed H3 PDE balance E' + 2D = -Transport identifies
normalized positive energy growth with positive full-dissipation transport
excess. Hence its time integral cannot be finite on the same tail. -/
theorem h3Path_cofinalPhysicalEnergyEscape_excludes_integrableFullTransport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hTendsto : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ¬ MeasureTheory.IntegrableOn
      (h3PathFullDissipationTransportExcessRate u) (Set.Ioo a T) := by
  intro hInt
  have hLog : MeasureTheory.IntegrableOn
      (h3PathPositiveLogEnergyGrowthRate u) (Set.Ioo a T) :=
    IntegrableOn.congr_fun hInt
      (fun s hs =>
        h3PathFullDissipationTransportExcessRate_eq_positiveLogEnergyGrowthRate
          hH3 hClass hs)
      measurableSet_Ioo
  exact (h3Path_cofinalPhysicalEnergyEscape_excludes_integrablePositiveLog244
    hH3 hClass t ht hTendsto hEscape) hLog

/-- The ORIGINAL canonical first-crossing anchors inherit the signed
energy-growth obstruction under precisely the conditional higher-radial
premises of the previous all-orders spectral-energy gate. This theorem does
not insert a nonextension hypothesis or reselect any canonical windows. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_signedGrowthGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S D η ε : ℝ,
          0 ≤ S → 0 ≤ D → 0 < η → 0 < ε → ε < η →
          16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1 →
          (∀ᶠ k : ℕ in atTop, C (v k) ≤ S) →
          (∀ᶠ k : ℕ in atTop,
            ((N (v k) : ℝ) + 2) ^ 8 ≤ D * ((v k : ℝ) + 1) ^ 9) →
          (∀ᶠ k : ℕ in atTop,
            η ≤ ((v k : ℝ) + 1) ^ (2 * m + 3) * ((T - τ (v k)) / 4)) →
          ¬ MeasureTheory.IntegrableOn
            (h3PathPositiveLogEnergyGrowthRate u) (Set.Ioo a T) ∧
          ¬ MeasureTheory.IntegrableOn
            (h3PathPositiveEnergyGrowthRate u) (Set.Ioo a T) ∧
          ¬ MeasureTheory.IntegrableOn
            (h3PathFullDissipationTransportExcessRate u) (Set.Ioo a T)) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hτ,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom
  obtain ⟨_hQuantitative, hEnergyEscape, _hSpectralEscape⟩ :=
    hHigher m F hF hFInt hUpper S D η ε hS hD hη hε
      hεη hSmall hCeil hCap hGeom
  have hLog :=
    h3Path_cofinalPhysicalEnergyEscape_excludes_integrablePositiveLog244
      hH3 hClass (fun k => τ (v k))
      (fun k => hτ (v k)) hCofinal hEnergyEscape
  have hNorm :=
    h3Path_cofinalPhysicalEnergyEscape_excludes_integrableNormalizedGrowth244
      hH3 hClass (fun k => τ (v k))
      (fun k => hτ (v k)) hCofinal hEnergyEscape
  have hSigned :=
    h3Path_cofinalPhysicalEnergyEscape_excludes_integrableFullTransport244
      hH3 hClass (fun k => τ (v k))
      (fun k => hτ (v k)) hCofinal hEnergyEscape
  exact ⟨hLog, hNorm, hSigned⟩

end
end PrimeTensor.FirstMonomialTriad
