import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationSingleTimeConcentration

/-!
# Global physical dissipation lower bound from the localized angular branch

The preceding checkpoint extracts one strict-time sequence carrying a fixed
amount of localized full H³ dissipation on shrinking equatorial cones.

This file records the immediate physical consequence without discarding the
localization data.  Since the one-time dissipation density is nonnegative, its
mass on any measurable frequency region is bounded by its whole-space mass.
The latter is exactly `velocityH3DissipationAt`.

Hence the same selected sequence satisfies the real scalar lower bound

    ρ² (ε² / 64) < 16 * velocityH3DissipationAt u (τ n).

This does **not** replace the angular concentration statement: a global lower
bound alone contains no information about concentration.  The final package
therefore retains both the shrinking-cone localized lower bound and its global
physical consequence on the same sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationScalarLowerBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationScalarLowerBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Localized mass is bounded by total physical dissipation -/

/-- The real localized high-radial bad-cone dissipation mass is bounded by the
whole-space physical H³ dissipation at the same strict time. -/
theorem h3TerminalPhysicalDissipationBadConeHighRadialRealMass_le_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (κ ρ : ℝ) :
    h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3 i κ ρ t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      ≤
    velocityH3DissipationAt u t := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      \
    h3TerminalRadialFrequencyBelow ρ

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ

  have hInt : Integrable f volume := by
    dsimp only [f, htAbs]
    simpa only using
      (h3TerminalSpectralDissipationSingleDensity_integrable
        hH3 hClass ht)

  have hNonneg :
      0 ≤ᵐ[volume] f := by
    filter_upwards with ξ
    dsimp only [f]
    exact
      h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
        ξ

  have hLocalLeFull :
      (∫ ξ in S, f ξ ∂volume)
        ≤
      ∫ ξ : H3FourierPoint3, f ξ ∂volume := by
    exact
      integral_mono_measure
        Measure.restrict_le_self
        hNonneg
        hInt

  have hFull :
      (∫ ξ : H3FourierPoint3, f ξ ∂volume)
        =
      velocityH3DissipationAt u t := by
    dsimp only [f, htAbs]
    exact
      integral_h3TerminalSpectralDissipationSingleDensity_eq_dissipation
        hH3 hClass ht

  unfold h3TerminalPhysicalDissipationBadConeHighRadialRealMass

  change
    (∫ ξ in S, f ξ ∂volume)
      ≤
    velocityH3DissipationAt u t

  exact
    hLocalLeFull.trans_eq hFull

/-- Extended localized mass is bounded by the `ENNReal.ofReal` lift of the
whole physical H³ dissipation. -/
theorem h3TerminalPhysicalDissipationBadConeHighRadialMass_le_ofReal_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (κ ρ : ℝ) :
    h3TerminalPhysicalDissipationBadConeHighRadialMass
        hH3 i κ ρ t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      ≤
    ENNReal.ofReal (velocityH3DissipationAt u t) := by

  have hReal :=
    h3TerminalPhysicalDissipationBadConeHighRadialRealMass_le_dissipation
      hH3 hClass ht i κ ρ

  have hBridge :=
    ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
      hH3 hClass ht i κ ρ

  calc
    h3TerminalPhysicalDissipationBadConeHighRadialMass
        hH3 i κ ρ t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
        =
      ENNReal.ofReal
        (h3TerminalPhysicalDissipationBadConeHighRadialRealMass
          hH3 i κ ρ t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) := by
      exact hBridge.symm

    _ ≤
      ENNReal.ofReal (velocityH3DissipationAt u t) :=
        ENNReal.ofReal_le_ofReal hReal

/-! ## Same-sequence global physical lower bound -/

/-- Package the shrinking-cone single-time concentration together with the
resulting ordinary real lower bound for total physical H³ dissipation, on the
same sequence. -/
def H3TerminalPhysicalDissipationSingleTimeAngularConcentrationWithScalarLowerBoundAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (ε ρ : ℝ) : Prop :=
  ∃ τ κ : ℕ → ℝ,
    ∃ hτ : ∀ n, τ n ∈ Set.Ioo a T,
      (∀ n, 0 < κ n)
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto κ atTop (𝓝 0)
        ∧
      (∀ n,
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3 i (κ n) ρ (τ n)
            ⟨lt_trans hClass.terminal_start.1 (hτ n).1,
              (hτ n).2⟩)
        ∧
      ∀ n,
        ρ ^ 2 * (ε ^ 2 / 64)
          <
        16 * velocityH3DissipationAt u (τ n)

/-- Every positive-cutoff single-time angular concentration branch yields, on
exactly the same sequence, a uniform ordinary real lower bound for total
physical H³ dissipation. -/
theorem physicalDissipationSingleTimeAngularConcentrationWithScalarLowerBoundAtCutoff_of_branch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hε : 0 < ε)
    (hρ : 0 < ρ)
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
        hH3 hClass i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeAngularConcentrationWithScalarLowerBoundAtCutoff
      hH3 hClass i ε ρ := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
      at hBranch

  obtain
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hLocal⟩ :=
    hBranch

  refine
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hLocal,
      ?_⟩

  intro n

  let htAbs : τ n ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (hτ n).1,
      (hτ n).2⟩

  have hMassLe :
      h3TerminalPhysicalDissipationBadConeHighRadialMass
          hH3 i (κ n) ρ (τ n) htAbs
        ≤
      ENNReal.ofReal (velocityH3DissipationAt u (τ n)) := by
    exact
      h3TerminalPhysicalDissipationBadConeHighRadialMass_le_ofReal_dissipation
        hH3 hClass (hτ n) i (κ n) ρ

  have hENN :
      ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
        <
      16 * ENNReal.ofReal (velocityH3DissipationAt u (τ n)) := by
    exact
      (hLocal n).trans_le
        (mul_le_mul_of_nonneg_left
          hMassLe
          (by positivity))

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u (τ n) :=
    velocityH3DissipationAt_nonneg u (τ n)

  have hDPos :
      0 < velocityH3DissipationAt u (τ n) := by
    by_contra hNotPos
    have hDLe :
        velocityH3DissipationAt u (τ n) ≤ 0 :=
      le_of_not_gt hNotPos
    have hDZero :
        velocityH3DissipationAt u (τ n) = 0 :=
      le_antisymm hDLe hDNonneg
    rw [hDZero] at hENN
    norm_num at hENN

  have hScaled :
      ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
        <
      ENNReal.ofReal
        (16 * velocityH3DissipationAt u (τ n)) := by
    calc
      ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
          <
        16 * ENNReal.ofReal (velocityH3DissipationAt u (τ n)) :=
        hENN
      _ =
        ENNReal.ofReal
          (16 * velocityH3DissipationAt u (τ n)) := by
        rw [
          ENNReal.ofReal_mul
            (by norm_num : (0 : ℝ) ≤ 16)
        ]
        norm_num

  exact
    (
      ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (by norm_num : (0 : ℝ) < 16) hDPos)
    ).1
      hScaled

/-! ## Necessary scalar lower bound under hypothetical nonextension -/

/-- Under the retained raw-Fourier L² Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity endpoint force a
single-time shrinking-cone dissipation concentration sequence whose total
physical H³ dissipation is uniformly bounded below by the same quantitative
threshold. -/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationAngularConcentrationWithScalarLowerBound_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬ H3TerminalActualVorticityStrongH3EndpointPath hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ
          ∧
        H3TerminalPhysicalDissipationSingleTimeAngularConcentrationWithScalarLowerBoundAtCutoff
          hH3 hClass i ε ρ := by

  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hSingle⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationAngularConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeAngularConcentrationWithScalarLowerBoundAtCutoff_of_branch
      hH3
      hClass
      i
      hε
      hρ
      hSingle

end

end Euclidean
end Bridge
end PrimeTensor
