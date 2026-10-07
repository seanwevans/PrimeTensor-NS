import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt.Package

/-!
# Critical square-root-width normalization

The exact bound `C / sqrt gap ≤ M`, interpreted in `ENNReal`, gives
`ofReal C ≤ ofReal (sqrt gap) * M` whenever the width is positive.
Each selected radial branch therefore has a strictly positive normalized
lower bound and cannot converge to zero at this scale.

If both radial families have vanishing normalized moments on the parent
sequence, the canonical forcing alternative selects H3 energy escape.
These vanishing assumptions are conditional; this file does not establish
them from the PDE or exclude the retained energy branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Clear a positive real scale in an extended-nonnegative lower bound. -/
theorem h3Terminal_ofReal_le_scaled_of_inverseScale_le
    {C x : ℝ} {M : ℝ≥0∞}
    (hx : 0 < x)
    (hBound : ENNReal.ofReal (C / x) ≤ M) :
    ENNReal.ofReal C ≤ ENNReal.ofReal x * M := by
  have hCancel : x * (C / x) = C := by
    field_simp [ne_of_gt hx] <;> ring
  calc
    ENNReal.ofReal C =
        ENNReal.ofReal x * ENNReal.ofReal (C / x) := by
      rw [← ENNReal.ofReal_mul hx.le, hCancel]
    _ ≤ ENNReal.ofReal x * M := by
      gcongr <;> exact hBound

/-- A fixed positive normalized floor rules out convergence to zero. -/
theorem h3Terminal_not_tendsto_zero_of_eventually_ofReal_pos_le
    {C : ℝ} {F : ℕ → ℝ≥0∞}
    (hC : 0 < C)
    (hLower : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal C ≤ F n) :
    ¬ Tendsto F atTop (𝓝 0) := by
  intro hZero
  have hLe : ENNReal.ofReal C ≤ 0 := ge_of_tendsto hZero hLower
  have hPos : (0 : ℝ≥0∞) < ENNReal.ofReal C :=
    ENNReal.ofReal_pos.mpr hC
  exact (not_le_of_gt hPos) hLe

/-- A selected higher moment stays above its positive critical-width floor. -/
def H3TerminalHigherRadialSqrtWidthPositiveFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (gap : ℕ → ℝ)
    (radialOrder : ℕ)
    (C : ℝ) : Prop :=
  0 < C ∧
  ∃ v : ℕ → ℕ,
    StrictMono v ∧
    Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
    (∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal C ≤
        ENNReal.ofReal (Real.sqrt (gap (v n))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n))) ∧
    (¬ Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt (gap (v n))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n)))
      atTop (𝓝 0)) ∧
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass radialOrder (τ (v n)) (hτ (v n)))
      atTop (𝓝 ∞)

/-- The energy branch or one of the two canonical positive normalized floors. -/
theorem resolvedCanonicalForcing_energy_or_sqrtWidthPositiveFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ) (gap : ℕ → ℝ)
    (hδ : 0 < δ)
    (hGap : ∀ n : ℕ, 0 < gap n)
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
        hH3 hClass τ hτ δ gap) :
    (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSqrtWidthPositiveFloor
        hH3 hClass τ hτ gap
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSqrtWidthPositiveFloor
        hH3 hClass τ hτ gap
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial)) := by
  rcases hBranch with hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy

  · obtain ⟨_j, qRadial, v, hMono, hTau, _hRate, _hScale,
      _hOfReal, hDirect, hHigher⟩ := hSecond
    have hC :
        0 < h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial :=
      h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient_pos hδ qRadial
    have hLower :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial) ≤
            ENNReal.ofReal (Real.sqrt (gap (v n))) *
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass (h3TerminalForcingThirdQHigherRadialShift qRadial)
                (τ (v n)) (hτ (v n)) := by
      filter_upwards [hDirect] with n hn
      exact h3Terminal_ofReal_le_scaled_of_inverseScale_le
        (Real.sqrt_pos.2 (hGap (v n))) hn
    have hNonzero :=
      h3Terminal_not_tendsto_zero_of_eventually_ofReal_pos_le hC hLower
    exact Or.inr (Or.inl
      ⟨qRadial, hC, v, hMono, hTau, hLower, hNonzero, hHigher⟩)

  · obtain ⟨_j, qRadial, v, hMono, hTau, _hRate, _hScale,
      _hOfReal, hDirect, hHigher⟩ := hFourth
    have hC :
        0 < h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial :=
      h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient_pos hδ qRadial
    have hLower :
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal
              (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial) ≤
            ENNReal.ofReal (Real.sqrt (gap (v n))) *
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass (h3TerminalForcingFourthQHigherRadialShift qRadial)
                (τ (v n)) (hτ (v n)) := by
      filter_upwards [hDirect] with n hn
      exact h3Terminal_ofReal_le_scaled_of_inverseScale_le
        (Real.sqrt_pos.2 (hGap (v n))) hn
    have hNonzero :=
      h3Terminal_not_tendsto_zero_of_eventually_ofReal_pos_le hC hLower
    exact Or.inr (Or.inr
      ⟨qRadial, hC, v, hMono, hTau, hLower, hNonzero, hHigher⟩)

/-- Vanishing normalized moments exclude both radial branches, leaving energy escape. -/
theorem resolvedCanonicalForcing_energyEscape_of_sqrtWidthMoments_tendsto_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ) (gap : ℕ → ℝ)
    (hδ : 0 < δ)
    (hGap : ∀ n : ℕ, 0 < gap n)
    (hBranch :
      H3TerminalResolvedCanonicalForcingDivergentInverseSqrtWidthHigherScaleBranch
        hH3 hClass τ hτ δ gap)
    (hSecondZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (gap n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingThirdQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0))
    (hFourthZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (gap n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingFourthQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)) :
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop := by
  rcases resolvedCanonicalForcing_energy_or_sqrtWidthPositiveFloor
      hH3 hClass τ hτ δ gap hδ hGap hBranch with
    hEnergy | hSecond | hFourth
  · exact hEnergy
  · obtain ⟨qRadial, _hC, v, hMono, _hTau, _hLower, hNonzero, _hHigher⟩ := hSecond
    exact False.elim (hNonzero ((hSecondZero qRadial).comp hMono.tendsto_atTop))
  · obtain ⟨qRadial, _hC, v, hMono, _hTau, _hLower, hNonzero, _hHigher⟩ := hFourth
    exact False.elim (hNonzero ((hFourthZero qRadial).comp hMono.tendsto_atTop))

end

end Euclidean
end Bridge
end PrimeTensor
