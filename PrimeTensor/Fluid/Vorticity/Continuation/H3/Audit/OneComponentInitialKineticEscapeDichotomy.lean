import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCofinalKineticAnchorsRelativeEnergy

/-!
# Initial kinetic escape versus old/selected relative-energy uniqueness

The existing PDE argument proves that the actual order-zero kinetic energy is
antitone on the WHOLE strictly positive interval. Its initial weak--strong
comparison therefore needs just one number `B` for which arbitrarily early
positive kinetic-energy samples are at most `B`.

Here we remove the *a priori choice* of those samples by proving a sharp
initial-filter dichotomy, valid for any real scalar function:

* some finite nonnegative `B` bounds arbitrarily early samples, or
* the scalar function tends to `+∞` as time decreases to zero.

For the actual kinetic energy, the first branch yields the previously proved
old-velocity `L²` ceiling and, conditionally on the epsilon-accurate physical
relative-energy estimates, initial uniqueness. The second branch exposes the
remaining kinetic obstruction rather than silently assuming it is absent.

This does NOT prove that a genuine Navier--Stokes initial-value solution has
nondivergent right kinetic energy, nor derive the vanishing-residual relative-
energy estimate. In particular neither strong initial H³ convergence nor the
independent terminal actual-vorticity strong-H³ hypothesis is smuggled in.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- For any real function on a right neighborhood of zero, failure to find
one uniformly bounded, cofinal family of samples is precisely escape to the
top filter. No monotonicity is needed for this purely filter-theoretic step. -/
theorem h3Audit_initialScalar_cofinalBoundedSamples_or_tendstoAtTop
    (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b) :
    (∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ f s ≤ B) ∨
      Tendsto f (𝓝[>] (0 : ℝ)) atTop := by
  by_cases hBound : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ f s ≤ B
  · exact Or.inl hBound
  · right
    apply tendsto_atTop.2
    intro M
    let B : ℝ := max M 0
    have hB : 0 ≤ B := le_max_right M 0
    have hNoBound : ¬ ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ f s ≤ B := by
      intro hSamples
      exact hBound ⟨B, hB, hSamples⟩
    push_neg at hNoBound
    obtain ⟨t, ht, hLower⟩ := hNoBound
    have hNear : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
        s ∈ Set.Ioo (0 : ℝ) t := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ht.1)] with s hs0 hst
      exact ⟨hs0, hst⟩
    filter_upwards [hNear] with s hs
    exact (le_max_left M 0).trans (hLower s hs).le

/-- A nonescaping initial scalar has a common finite bound on a cofinal
family of its right-time samples. This uses no continuity at time zero. -/
theorem h3Audit_initialScalar_cofinalBoundedSamples_of_noEscape
    (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hNoEscape : ¬ Tendsto f (𝓝[>] (0 : ℝ)) atTop) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ f s ≤ B := by
  rcases h3Audit_initialScalar_cofinalBoundedSamples_or_tendstoAtTop
      f b hb with hBound | hEscape
  · exact hBound
  · exact False.elim (hNoEscape hEscape)

/-- A strictly positive-time Navier--Stokes H³ path has a sharp kinetic
alternative: a global finite kinetic ceiling on `(0,b)` or initial kinetic
escape to `+∞`. The actual kinetic antitonicity is used only here. -/
theorem h3Audit_initialKineticEnergy_uniformCeiling_or_initialEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T) :
    (∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        velocityH3Energy0At u t ≤ B) ∨
      Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop := by
  rcases h3Audit_initialScalar_cofinalBoundedSamples_or_tendstoAtTop
      (velocityH3Energy0At u) b hb with hSample | hEscape
  · obtain ⟨B, hB, hSamples⟩ := hSample
    exact Or.inl ⟨B, hB,
      h3Audit_initialKineticEnergy_le_of_cofinalAnchors
        hH3 b B hbT hSamples⟩
  · exact Or.inr hEscape

/-- A nondivergent initial kinetic energy suffices for a uniform actual
positive-time physical `L²` bound, with no kinetic trace or defect budget. -/
theorem h3Audit_initialOldPhysicalHilbert_uniformBound_of_noKineticEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (hNoEscape :
      ¬ Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ Real.sqrt B := by
  obtain ⟨B, hB, hSamples⟩ :=
    h3Audit_initialScalar_cofinalBoundedSamples_of_noEscape
      (velocityH3Energy0At u) b hb hNoEscape
  exact ⟨B, hB,
    h3Audit_initialOldPhysicalHilbert_norm_le_of_cofinalKineticAnchors
      hH3 b B hbT hSamples⟩

/-- PDE-facing data with NO kinetic ceiling, cofinal-anchor assertion,
kinetic right limit, or kinetic integral budget. Only the real initial datum
and epsilon-vanishing old/selected comparison are stipulated.

The kinetic-escape branch is deliberately not excluded by this definition. -/
def H3AuditInitialCanonicalKineticEscapeDichotomyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ K : ℝ,
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- When the kinetic energy does not escape, the bare physical comparison
data supplies exactly the cofinal-anchor condition used by the existing
initial uniqueness theorem. -/
theorem h3Audit_initialKineticNoEscape_implies_cofinalComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalKineticEscapeDichotomyData hH3)
    (hNoEscape :
      ¬ Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop) :
    H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hEpsilon⟩ := hData
  obtain ⟨B, hB, hSamples⟩ :=
    h3Audit_initialScalar_cofinalBoundedSamples_of_noEscape
      (velocityH3Energy0At u) b hb hNoEscape
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, B, K, hB, hSamples, hEpsilon⟩

/-- Nondivergent initial kinetic energy plus the still-explicit physical
relative-energy comparison gives compact weak-test initial uniqueness. -/
theorem h3Audit_initialKineticNoEscape_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalKineticEscapeDichotomyData hH3)
    (hNoEscape :
      ¬ Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_compactWeakComparisonData
    hH3 (h3Audit_initialKineticNoEscape_implies_cofinalComparisonData
      hH3 hData hNoEscape)

/-- Without any initial kinetic hypothesis, physical approximate comparison
implies the precise dichotomy: compact initial weak uniqueness, OR genuine
kinetic escape at zero. This does NOT eliminate the second branch. -/
theorem h3Audit_initialComparison_compactWeakUniqueness_or_kineticEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalKineticEscapeDichotomyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 ∨
      Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop := by
  by_cases hEscape :
      Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop
  · exact Or.inr hEscape
  · exact Or.inl
      (h3Audit_initialKineticNoEscape_implies_compactWeakComparisonData
        hH3 hData hEscape)

/-- Initial physical `L²` and upper `H³` traces follow in the nonescaping
branch; they are not used as hypotheses in this alternative. -/
theorem h3Audit_initialKineticNoEscape_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalKineticEscapeDichotomyData hH3)
    (hNoEscape :
      ¬ Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialKineticNoEscape_implies_cofinalComparisonData
      hH3 hData hNoEscape)

/-- Full-time complementary intrinsic `Ḣ^(3/2)` estimates, or initial
kinetic escape, under the independent terminal actual-vorticity hypothesis. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_or_initialKineticEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalKineticEscapeDichotomyData hH3) :
    (MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T))) ∨
    Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop := by
  by_cases hEscape :
      Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop
  · exact Or.inr hEscape
  · exact Or.inl
      (h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCofinalKineticAnchors
        hH3 hClass i hPhysical
        (h3Audit_initialKineticNoEscape_implies_cofinalComparisonData
          hH3 hData hEscape))

end
end Euclidean
end Bridge
end PrimeTensor
