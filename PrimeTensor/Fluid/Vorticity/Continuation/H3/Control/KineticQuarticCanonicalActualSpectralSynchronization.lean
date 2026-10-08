import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSpectralShortfall

/-!
# Synchronize actual H3 transport excess and spectral shortfall on the physical clock

The previous terminal physical-clock sequence made the *commutator envelope*
shortfall S(t)=4422*C1*sqrt(E(t))-2*D(t)/E(t) unbounded. This alone did not
ensure large *actual* transport excess: the commutator inequality can lose
cancellations.

The exact direct-regime dissipation-margin obstruction already gives stronger
witnesses: at any positive kinetic anchor and any arbitrarily late interval,

  2*D(t) + R*E(t) < -transport(t)

for every fixed R. Taking R=4422+max(M,0) and using the previously proved
comparison between actual minimal margin excess and the spectral gap yields
one and the same time with

  M < max(0,(-transport(t)-2*D(t))/E(t)),
  M < 4422*C1*sqrt(E(t))-2*D(t)/E(t).

These witnesses can be selected along the explicit terminal physical clock,
with exact direct selection and zero selected absorption at every sample.
This is still conditional on hypothetical nonextension and does not assert
that commutator bounds saturate or that blowup exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- A strict actual transport surplus over both copies of H3 dissipation
forces the normalized zero-margin *actual* positive excess above the same
scalar threshold. This pointwise implication does not require energy-class
hypotheses: the canonical H3 energy is positive everywhere. -/
theorem h3PathCanonical_actualMarginExcess_gt_of_strictTransportSurplus
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (M t : ℝ)
    (hSurplus :
      2 * velocityH3DissipationAt u t + M * velocityH3EnergyAt u t <
        - velocityH3TransportDerivativeAt u t) :
    M < h3PathCanonicalMarginExcessRate u 0 t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hNumerator :
      M * velocityH3EnergyAt u t <
        - velocityH3TransportDerivativeAt u t -
          2 * velocityH3DissipationAt u t := by
    linarith only [hSurplus]
  have hRatio : M <
      (- velocityH3TransportDerivativeAt u t -
          2 * velocityH3DissipationAt u t) /
        velocityH3EnergyAt u t :=
    (lt_div_iff₀ hEPos).2 hNumerator
  unfold h3PathCanonicalMarginExcessRate
  simpa only [sub_zero] using
    (lt_of_lt_of_le hRatio (le_max_right (0 : ℝ) _))

/-- The actual normalized excess is below the spectral envelope, so exceeding
`4422 + max M 0` in the *actual* quantity forces the baseline-free spectral
shortfall above `M` at the same time. -/
theorem h3PathCanonical_spectralShortfall_gt_of_actualMarginExcess_gt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hActual : 4422 + max M 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  have hUpper :=
    h3PathCanonicalMarginExcessRate_le_spectralDissipationGap
      (0 : ℝ) hH3 hClass ht
  have hGap : 4422 + max M 0 <
      h3PathCanonicalSpectralDissipationGap u 0 t :=
    lt_of_lt_of_le hActual hUpper
  exact h3PathCanonical_shortfall_gt_of_spectralGap_large u M t hGap

/-- Under hypothetical nonextension there are arbitrarily late *simultaneous*
large actual transport-excess and spectral-shortfall witnesses. Each lies on
the exact direct regime at a fixed positive-mass kinetic anchor. -/
theorem h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hd : d ∈ Set.Ioo a T) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      M < h3PathCanonicalMarginExcessRate u 0 t ∧
      M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  let R : ℝ := 4422 + max M 0
  obtain ⟨t, ht, hDirect, hSurplus⟩ :=
    h3PathCanonical_direct_margin_exceeds_every_constant_energy_rate
      R hH3 hNoExtension hClass hMass hd (le_refl (0 : ℝ))
  have hSelectedCondition :
      velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) *
          (h3PathCanonicalKineticTransportCoefficient u t) ^ 3) *
            velocityH3Energy0At u b := by
    by_contra hNot
    have hZero :
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
      simp only [h3ExactAdaptiveSelectedDirectCoefficient, if_neg hNot]
    have hPositive := h3PathCanonicalKineticTransportCoefficient_pos u t
    rw [hZero] at hDirect
    linarith only [hDirect, hPositive]
  have hAbsorbed :
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
    unfold h3ExactAdaptiveSelectedAbsorbedCoefficient
    exact if_pos hSelectedCondition
  have hActualR : R < h3PathCanonicalMarginExcessRate u 0 t :=
    h3PathCanonical_actualMarginExcess_gt_of_strictTransportSurplus
      u R t (by simpa only [sub_zero] using hSurplus)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hSpectral : M < h3PathCanonicalNonlinearDissipationShortfall u t :=
    h3PathCanonical_spectralShortfall_gt_of_actualMarginExcess_gt
      M hH3 hClass htClass (by simpa only [R] using hActualR)
  have hMMax : M ≤ max M 0 := le_max_left _ _
  have hActualM : M < h3PathCanonicalMarginExcessRate u 0 t := by
    dsimp only [R] at hActualR
    linarith only [hActualR, hMMax]
  exact ⟨t, ht, hDirect, hAbsorbed, hActualM, hSpectral⟩

/-- One explicit physical-clock sequence simultaneously has divergent
*actual* normalized H3 transport excess and divergent normalized spectral
shortfall, while exact direct selection holds at each sample. -/
theorem h3PathCanonical_exists_direct_actualAndSpectralExcess_blowupSequence
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
        (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => h3PathCanonicalMarginExcessRate u 0 (σ n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
  classical
  let m : ℝ := h3BKMKineticTailMidpoint a T
  have hm : m ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hChoice : ∀ n : ℕ, ∃ t : ℝ,
      t ∈ Set.Ioo a T ∧
      t ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      (n : ℝ) < h3PathCanonicalMarginExcessRate u 0 t ∧
      (n : ℝ) < h3PathCanonicalNonlinearDissipationShortfall u t := by
    intro n
    let δ : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    let d : ℝ := max m (T - δ)
    have hd : d ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hm.1 (le_max_left _ _),
        max_lt hm.2 (sub_lt_self T hδ)⟩
    obtain ⟨t, ht, hDirect, hAbsorbed, hActual, hSpectral⟩ :=
      h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
        (n : ℝ) hH3 hNoExtension hClass hMass hd
    have htOld : t ∈ Set.Ioo a T :=
      ⟨lt_trans hd.1 ht.1, ht.2⟩
    have htNear : t ∈ Set.Ioo (T - δ) T :=
      ⟨lt_of_le_of_lt (le_max_right m (T - δ)) ht.1, ht.2⟩
    exact ⟨t, htOld, htNear, hDirect, hAbsorbed, hActual, hSpectral⟩
  choose σ hσ using hChoice
  have hClock : Tendsto σ atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hDenN : 0 < (N : ℝ) + 1 := by positivity
    have hInvN : (1 : ℝ) / ((n : ℝ) + 1) ≤
        1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hDenN (by linarith)
    have hSmallN : 1 / ((N : ℝ) + 1) < ε := by
      have hInvEps : 1 / ε < (N : ℝ) := hN
      have hNPlus : 1 / ε < (N : ℝ) + 1 := by linarith
      have hMulRaw : 1 < ((N : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε).1 hNPlus
      have hMul : 1 < ε * ((N : ℝ) + 1) := by
        simpa only [mul_comm] using hMulRaw
      exact (div_lt_iff₀ hDenN).2 (by simpa only [one_mul] using hMul)
    have hSmall : (1 : ℝ) / ((n : ℝ) + 1) < ε :=
      lt_of_le_of_lt hInvN hSmallN
    have hLower := (hσ n).2.1.1
    have hUpper := (hσ n).2.1.2
    rw [Real.dist_eq]
    have hDiffNonpos : σ n - T ≤ 0 := by linarith [hUpper]
    rw [abs_of_nonpos hDiffNonpos]
    linarith
  have hActualDiverges : Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (σ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_of_lt (lt_of_lt_of_le hN
      (le_trans hCast (le_of_lt (hσ n).2.2.2.2.1)))
  have hSpectralDiverges : Tendsto (fun n : ℕ =>
      h3PathCanonicalNonlinearDissipationShortfall u (σ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_of_lt (lt_of_lt_of_le hN
      (le_trans hCast (le_of_lt (hσ n).2.2.2.2.2)))
  exact ⟨σ, hσ, hClock, hActualDiverges, hSpectralDiverges⟩

/-- Neutral alternative with a *single simultaneous* witness for the actual
PDE transport excess and the spectral envelope shortfall. -/
theorem h3PathCanonical_extension_or_simultaneously_unbounded_actualAndSpectralExcess
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∀ d : ℝ, d ∈ Set.Ioo a T →
        ∀ M : ℝ, ∃ t : ℝ, t ∈ Set.Ioo d T ∧
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t =
              h3PathCanonicalKineticTransportCoefficient u t ∧
          h3ExactAdaptiveSelectedAbsorbedCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
          M < h3PathCanonicalMarginExcessRate u 0 t ∧
          M < h3PathCanonicalNonlinearDissipationShortfall u t := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass d hd M
    exact h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
      M hH3 hExt hClass hMass hd

end Euclidean
end Bridge
end PrimeTensor
