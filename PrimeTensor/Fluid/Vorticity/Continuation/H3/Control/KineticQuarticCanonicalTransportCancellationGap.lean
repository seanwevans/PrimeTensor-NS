import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalActualSpectralSynchronization

/-!
# Exact cancellation budget between the commutator envelope and signed H3 transport

The existing canonical commutator bound supplies a nonnegative cancellation
slack `Delta = B + transport / E`, where `B = 4422 (1 + C1 sqrt E)`.
This is the difference between the spectral upper bound `B E` and the
actual signed adverse transport `-transport`, divided by the H3 energy.

The zero-margin exact raw excess and this slack add to the complete spectral
margin `4422 + S`, where `S = 4422 C1 sqrt E - 2D/E`. On the positive actual
excess branch, the raw excess is exactly the canonical normalized positive
excess. Thus a simultaneous blowup sequence gives a pointwise budget: the
nonnegative cancellation slack leaves at least `n` of spectral shortfall
for the true dissipative transport excess.

A quantitative lower bound for this cancellation slack that compensates the
spectral margin modulo an integrable coefficient forces continuation. Such a
bound is an *additional analytic hypothesis*, not supplied by the present
commutator estimate. None of these results asserts or excludes blowup.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Nonnegative slack between the canonical spectral commutator upper bound
and actual signed adverse H3 transport, normalized by the positive energy. -/
noncomputable def h3PathCanonicalTransportCancellationGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => h3PathCanonicalKineticTransportCoefficient u t +
    velocityH3TransportDerivativeAt u t / velocityH3EnergyAt u t

/-- The established commutator estimate makes the normalized cancellation
slack nonnegative on every H3 energy-class time. -/
theorem h3PathCanonicalTransportCancellationGap_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3PathCanonicalTransportCancellationGap u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hTransport :=
    h3PathCanonical_neg_transport_le_kineticCoefficient_mul_energy
      hH3 hClass ht
  have hNumerator :
      0 ≤ h3PathCanonicalKineticTransportCoefficient u t *
          velocityH3EnergyAt u t + velocityH3TransportDerivativeAt u t := by
    linarith only [hTransport]
  have hDiv := div_nonneg hNumerator (le_of_lt hEPos)
  have hIdentity :
      h3PathCanonicalTransportCancellationGap u t =
        (h3PathCanonicalKineticTransportCoefficient u t *
            velocityH3EnergyAt u t + velocityH3TransportDerivativeAt u t) /
          velocityH3EnergyAt u t := by
    unfold h3PathCanonicalTransportCancellationGap
    field_simp [ne_of_gt hEPos]
    <;> ring
  rw [hIdentity]
  exact hDiv

/-- Exact algebraic cancellation budget. This identity is valid without a
PDE admissibility premise because the canonical H3 energy is always positive. -/
theorem h3PathCanonical_cancellationGap_add_rawExcess_eq_spectralBudget
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    h3PathCanonicalTransportCancellationGap u t +
      (- velocityH3TransportDerivativeAt u t -
        2 * velocityH3DissipationAt u t) / velocityH3EnergyAt u t =
      4422 + h3PathCanonicalNonlinearDissipationShortfall u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hProd : 0 ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  calc
    _ = h3PathCanonicalKineticTransportCoefficient u t -
          2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
      unfold h3PathCanonicalTransportCancellationGap
      field_simp [ne_of_gt hEPos]
      <;> ring
    _ = 4422 + h3PathCanonicalNonlinearDissipationShortfall u t := by
      unfold h3PathCanonicalNonlinearDissipationShortfall
      simp only [h3PathCanonicalKineticTransportCoefficient,
        h3PathCanonicalSqrtEnergyGradientEnvelope, abs_of_nonneg hProd]
      ring

/-- Whenever the actual zero-margin normalized excess is positive, its max
is inactive and the exact cancellation budget uses that positive excess. -/
theorem h3PathCanonical_cancellationGap_add_actualExcess_eq_spectralBudget_of_pos
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hPositive : 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t =
      4422 + h3PathCanonicalNonlinearDissipationShortfall u t := by
  let x : ℝ :=
    (- velocityH3TransportDerivativeAt u t -
        2 * velocityH3DissipationAt u t) / velocityH3EnergyAt u t
  have hRate : h3PathCanonicalMarginExcessRate u 0 t = max 0 x := by
    dsimp only [x, h3PathCanonicalMarginExcessRate]
    simp only [sub_zero]
  have hx : 0 ≤ x := by
    by_contra hNot
    have hNonpos : x ≤ 0 := le_of_lt (lt_of_not_ge hNot)
    have hZero : h3PathCanonicalMarginExcessRate u 0 t = 0 := by
      rw [hRate, max_eq_left hNonpos]
    linarith only [hPositive, hZero]
  have hActual : h3PathCanonicalMarginExcessRate u 0 t = x := by
    rw [hRate, max_eq_right hx]
  rw [hActual]
  exact h3PathCanonical_cancellationGap_add_rawExcess_eq_spectralBudget u t

/-- A lower bound for cancellation slack compensating the commutator envelope
up to a scalar remainder implies an actual signed transport estimate. -/
theorem h3PathCanonical_transport_le_of_cancellationCompensation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (ε r t : ℝ)
    (hCompensation :
      h3PathCanonicalKineticTransportCoefficient u t -
        (2 - ε) * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t - r ≤
        h3PathCanonicalTransportCancellationGap u t) :
    - velocityH3TransportDerivativeAt u t ≤
      (2 - ε) * velocityH3DissipationAt u t +
        r * velocityH3EnergyAt u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hRatio :
      - velocityH3TransportDerivativeAt u t /
          velocityH3EnergyAt u t ≤
        (2 - ε) * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t + r := by
    unfold h3PathCanonicalTransportCancellationGap at hCompensation
    -- `linarith` treats `(-T) / E` and `T / E` as separate atoms.
    -- First cancel the shared scalar terms with an explicit outer negation,
    -- then normalize that negation across division.
    have hLinear :
        -(velocityH3TransportDerivativeAt u t /
            velocityH3EnergyAt u t) ≤
          (2 - ε) * velocityH3DissipationAt u t /
            velocityH3EnergyAt u t + r := by
      linarith only [hCompensation]
    simpa only [neg_div] using hLinear
  have hProduct := (div_le_iff₀ hEPos).1 hRatio
  calc
    - velocityH3TransportDerivativeAt u t ≤
        ((2 - ε) * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t + r) *
          velocityH3EnergyAt u t := hProduct
    _ = (2 - ε) * velocityH3DissipationAt u t +
          r * velocityH3EnergyAt u t := by
      field_simp [ne_of_gt hEPos]
      <;> ring

/-- An integrable cancellation-compensation remainder at any nonnegative
retained dissipation margin is a sufficient, anchor-free continuation test. -/
theorem h3PathCanonical_extension_of_integrable_cancellationCompensation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ} {r : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε)
    (hr : IntegrableOn r (Set.Ioo a T))
    (hCompensation : ∀ t : ℝ, t ∈ Set.Ioo a T →
      h3PathCanonicalKineticTransportCoefficient u t -
        (2 - ε) * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t - r t ≤
        h3PathCanonicalTransportCancellationGap u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hr
  intro t ht
  exact h3PathCanonical_energyGrowth_le_of_dissipationMargin
    hH3 hClass ht hε
    (h3PathCanonical_transport_le_of_cancellationCompensation
      u ε (r t) t (hCompensation t ht))

/-- Under hypothetical nonextension, no integrable remainder can compensate
the canonical spectral envelope by cancellation on an entire terminal tail. -/
theorem h3PathCanonical_cancellationCompensation_fails_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d ε : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hε : 0 ≤ ε)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3PathCanonicalTransportCancellationGap u t <
        h3PathCanonicalKineticTransportCoefficient u t -
          (2 - ε) * velocityH3DissipationAt u t /
            velocityH3EnergyAt u t - r t := by
  by_contra hNoWitness
  have hCompensation : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3PathCanonicalKineticTransportCoefficient u t -
        (2 - ε) * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t - r t ≤
        h3PathCanonicalTransportCancellationGap u t := by
    intro t ht
    by_contra hNot
    exact hNoWitness ⟨t, ht, lt_of_not_ge hNot⟩
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_cancellationCompensation
      hH3 hClassD hε hr hCompensation)

/-- On the synchronized terminal clock the nonnegative cancellation slack
leaves a strictly positive, quantitatively divergent actual transport share. -/
theorem h3PathCanonical_exists_direct_cancellationBudget_sequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ,
      (∀ n : ℕ,
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0 ∧
        (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 (σ n) ∧
        (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u (σ n) ∧
        0 ≤ h3PathCanonicalTransportCancellationGap u (σ n) ∧
        h3PathCanonicalTransportCancellationGap u (σ n) + (n : ℝ) <
          4422 + h3PathCanonicalNonlinearDissipationShortfall u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => h3PathCanonicalMarginExcessRate u 0 (σ n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
  obtain ⟨σ, hσ, hClock, hActualTends, hSpectralTends⟩ :=
    h3PathCanonical_exists_direct_actualAndSpectralExcess_blowupSequence
      hH3 hNoExtension hClass hMass
  refine ⟨σ, ?_, hClock, hActualTends, hSpectralTends⟩
  intro n
  obtain ⟨hAt, hNear, hDirect, hAbsorbed, hActual, hSpectral⟩ := hσ n
  have hCancel := h3PathCanonicalTransportCancellationGap_nonneg
    hH3 hClass hAt
  have hNNonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hPositive : 0 < h3PathCanonicalMarginExcessRate u 0 (σ n) :=
    lt_of_le_of_lt hNNonneg hActual
  have hBudget :=
    h3PathCanonical_cancellationGap_add_actualExcess_eq_spectralBudget_of_pos
      u (σ n) hPositive
  have hStrict :
      h3PathCanonicalTransportCancellationGap u (σ n) + (n : ℝ) <
        4422 + h3PathCanonicalNonlinearDissipationShortfall u (σ n) := by
    linarith only [hBudget, hActual]
  exact ⟨hAt, hNear, hDirect, hAbsorbed, hActual, hSpectral, hCancel, hStrict⟩

/-- Neutral alternative with a quantitative cancellation budget on a single
physical terminal clock, without presuming boundedness or saturation of slack. -/
theorem h3PathCanonical_extension_or_direct_cancellationBudget_sequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∃ σ : ℕ → ℝ,
        (∀ n : ℕ,
          σ n ∈ Set.Ioo a T ∧
          σ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
          (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 (σ n) ∧
          0 ≤ h3PathCanonicalTransportCancellationGap u (σ n) ∧
          h3PathCanonicalTransportCancellationGap u (σ n) + (n : ℝ) <
            4422 + h3PathCanonicalNonlinearDissipationShortfall u (σ n)) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, hσ, _hClock, _hActual, _hSpectral⟩ :=
      h3PathCanonical_exists_direct_cancellationBudget_sequence
        hH3 hExt hClass hMass
    refine ⟨σ, ?_⟩
    intro n
    obtain ⟨hAt, hNear, _hDirect, _hAbsorbed, hActual, _hSpectral,
      hCancel, hBudget⟩ := hσ n
    exact ⟨hAt, hNear, hActual, hCancel, hBudget⟩

end Euclidean
end Bridge
end PrimeTensor
