import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Primitive

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQPrimitiveClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQPrimitiveClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2600000

noncomputable def h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U := h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U i)

theorem h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt_le_rawL1_add_moment10
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3) :
    h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
        hH3 hClass ht i
      ≤
    h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass ht i
      +
    h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
        hH3 hClass ht i := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hRaw :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier (U i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have h :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 (U i))
    exact h.norm

  have hM10 :
      H3RawFourierMomentIntegrable (10 : ℝ) (U i) := by
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 10 (by norm_num) i

  have hMoment10 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (10 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (U i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact hM10

  have hM6 :
      H3RawFourierMomentIntegrable (6 : ℝ) (U i) := by
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 6 (by norm_num) i

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (6 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (U i) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hM6

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3SpectralScalarRawFourier (U i) ξ‖
        +
      h3FourierMomentWeight (10 : ℝ) ξ *
        ‖h3SpectralScalarRawFourier (U i) ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact hRaw.add hMoment10

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (6 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (U i) ξ‖
          ≤
        major ξ := by

    intro ξ

    have hNorm0 :
        0 ≤ ‖h3SpectralScalarRawFourier (U i) ξ‖ :=
      norm_nonneg _

    have hPow :=
      mul_le_mul_of_nonneg_right
        (norm_pow_six_le_one_add_pow_ten ξ)
        hNorm0

    dsimp only [major]

    have hWeight6 :
        h3FourierMomentWeight (6 : ℝ) ξ = ‖ξ‖ ^ 6 := by
      have h := h3FourierMomentWeight_natCast 6 ξ
      norm_num at h ⊢
      exact h

    have hWeight10 :
        h3FourierMomentWeight (10 : ℝ) ξ = ‖ξ‖ ^ 10 := by
      have h := h3FourierMomentWeight_natCast 10 ξ
      norm_num at h ⊢
      exact h

    rw [hWeight6, hWeight10]

    calc
      ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier (U i) ξ‖
          ≤
        (1 + ‖ξ‖ ^ 10) * ‖h3SpectralScalarRawFourier (U i) ξ‖ :=
        hPow
      _ =
        ‖h3SpectralScalarRawFourier (U i) ξ‖
          +
        ‖ξ‖ ^ 10 * ‖h3SpectralScalarRawFourier (U i) ξ‖ := by
        ring

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (6 : ℝ) ξ *
          ‖h3SpectralScalarRawFourier (U i) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono_ae hLeft hMajor
    filter_upwards with ξ
    exact hPoint ξ

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      h3SpectralScalarRawFourierL1Mass (U i)
        +
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U i) := by
    dsimp only [major]
    rw [integral_add hRaw hMoment10]
    rfl

  rw [hMajorIntegral] at hIntegral

  unfold
    h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
    h3TerminalForcingThirdQRawL1MassAt
    h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt

  dsimp only [U, htAbs]

  exact hIntegral

noncomputable def h3TerminalSecondQVelocityMoment6ResolverAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalForcingThirdQRawL1MassAt hH3 hClass ht i
  else
    h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
      hH3 hClass ht i

theorem exists_fixed_h3TerminalSecondQVelocityMoment6Resolver_subsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
            hH3 hClass (hτ n) i)
        atTop atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQVelocityMoment6ResolverAt
              hH3 hClass (hτ (s n)) i q)
          atTop atTop := by

  have hMaxTop :
      Tendsto
        (fun n : ℕ =>
          max
            (h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) i)
            (h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
              hH3 hClass (hτ n) i))
        atTop atTop := by

    refine tendsto_atTop.2 ?_
    intro M

    let R : ℝ := max M 0

    have hMLe : M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          2 * R + 1
            <
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
            hH3 hClass (hτ n) i :=
      hMomentTop.eventually
        (eventually_gt_atTop (2 * R + 1))

    filter_upwards [hLarge] with n hn

    let A : ℝ :=
      h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass (hτ n) i
    let B : ℝ :=
      h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
        hH3 hClass (hτ n) i
    let H : ℝ := max A B

    have hAH : A ≤ H := by
      dsimp only [H]
      exact le_max_left A B

    have hBH : B ≤ H := by
      dsimp only [H]
      exact le_max_right A B

    have hBound :=
      h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt_le_rawL1_add_moment10
        hH3 hClass (hτ n) i

    have hRLtH : R < H := by
      by_contra hNot
      have hHLe : H ≤ R := le_of_not_gt hNot
      have hALe : A ≤ R := hAH.trans hHLe
      have hBLe : B ≤ R := hBH.trans hHLe
      have hSum : A + B ≤ 2 * R := by linarith
      have hMomentLe :
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
              hH3 hClass (hτ n) i
            ≤
          2 * R := by
        dsimp only [A, B] at hBound hSum
        exact hBound.trans hSum
      linarith

    exact hMLe.trans (le_of_lt hRLtH)

  classical

  let q : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
          ≤
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i
      then 0 else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ n) i (q n)
          =
        max
          (h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass (hτ n) i)
          (h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i) := by
    intro n
    dsimp only [q]
    by_cases h :
        h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
          ≤
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i
    · simp only [if_pos h]
      unfold h3TerminalSecondQVelocityMoment6ResolverAt
      simp only [if_pos]
      exact (max_eq_left h).symm
    · simp only [if_neg h]
      have hReverse :
          h3TerminalForcingThirdQRawL1MassAt hH3 hClass (hτ n) i
            ≤
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i :=
        le_of_lt (lt_of_not_ge h)
      unfold h3TerminalSecondQVelocityMoment6ResolverAt
      simp only [if_neg, one_ne_zero]
      exact (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ n) i (q n))
        atTop atTop := by
    simpa only [hChosen] using hMaxTop

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop, ∃ q0 : Fin 2, q n = q0 :=
    Frequently.of_forall (fun n => ⟨q n, rfl⟩)

  obtain ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySome

  obtain ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop hFrequently

  have hs : ∀ n : ℕ, n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop : Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ (s n)) i (q (s n)))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQVelocityMoment6ResolverAt
            hH3 hClass (hτ (s n)) i q0)
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauTendsto.comp hsTop, hTop⟩

theorem h3TerminalSecondQVelocityMoment6_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
            hH3 hClass (hτ n) i)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (s n))) atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m (τ (s n)) (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  obtain ⟨q, s, hs, hsTop, hTauSub, hResolverTop⟩ :=
    exists_fixed_h3TerminalSecondQVelocityMoment6Resolver_subsequence
      hH3 hClass i τ hτ hTauTendsto hMomentTop

  fin_cases q

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ (s n)) i)
          atTop atTop := by
      simpa [h3TerminalSecondQVelocityMoment6ResolverAt] using hResolverTop

    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hL1Top

    exact Or.inl ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

  · have hM10Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
              hH3 hClass (hτ (s n)) i)
          atTop atTop := by
      simpa [h3TerminalSecondQVelocityMoment6ResolverAt] using hResolverTop

    rcases
      h3TerminalFourthQForcingDerivativeVelocityMoment10_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub hM10Top
    with hEnergy | hHigher

    · rcases hEnergy with ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩
      exact Or.inl
        ⟨
          (fun n => s (v n)),
          (fun n => le_trans (hv n) (hs (v n))),
          hsTop.comp hvTop,
          hTauFinal,
          hEnergyTop
        ⟩

    · rcases hHigher with
        ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩
      exact Or.inr
        ⟨
          m, hm,
          (fun n => s (v n)),
          (fun n => le_trans (hv n) (hs (v n))),
          hsTop.comp hvTop,
          hTauFinal,
          hHigherTop
        ⟩

theorem h3TerminalSecondQForcingDerivativePrimitiveFactor_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 6)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hPrimitiveTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativePrimitiveFactorAt
            hH3 hClass (hτ n) j o k l q)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (s n))) atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m (τ (s n)) (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  fin_cases q <;> fin_cases o

  · have hRawTop :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
              hH3 hClass (hτ n) j k)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeFirstStateAt,
        h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt,
        norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2
      ] using hPrimitiveTop
    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt_tendstoAtTop
        hH3 hClass j k τ hτ hRawTop
    exact Or.inl
      ⟨id, fun n => le_rfl, tendsto_id, hTauTendsto, by simpa using hEnergyTop⟩

  · have hOldTop :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL2FactorAt
              hH3 hClass (hτ n) k l 0)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeFirstStateAt,
        h3TerminalForcingThirdQRawL2FactorAt,
        h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity,
        norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2
      ] using hPrimitiveTop
    have hNot :=
      not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
        hH3 hClass k l 0 τ hτ hTauTendsto
    exact False.elim (hNot hOldTop)

  · have hOldTop :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL2FactorAt
              hH3 hClass (hτ n) k l 1)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeSecondStateAt,
        h3TerminalForcingThirdQRawL2FactorAt,
        h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
      ] using hPrimitiveTop
    have hNot :=
      not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
        hH3 hClass k l 1 τ hτ hTauTendsto
    exact False.elim (hNot hOldTop)

  · have hRawTop :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
              hH3 hClass (hτ n) j l)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeSecondStateAt,
        h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
      ] using hPrimitiveTop
    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt_tendstoAtTop
        hH3 hClass j l τ hτ hRawTop
    exact Or.inl
      ⟨id, fun n => le_rfl, tendsto_id, hTauTendsto, by simpa using hEnergyTop⟩

  · have hM6Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
              hH3 hClass (hτ n) j k)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeFirstStateAt,
        h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
      ] using hPrimitiveTop
    exact
      h3TerminalSecondQProjectedRHSMoment6_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j k τ hτ hTauTendsto hM6Top

  · have hM6Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
              hH3 hClass (hτ n) k)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeFirstStateAt,
        h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt,
        h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
      ] using hPrimitiveTop
    exact
      h3TerminalSecondQVelocityMoment6_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass k τ hτ hTauTendsto hM6Top

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) l)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeSecondStateAt,
        h3TerminalForcingThirdQRawL1MassAt,
        h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
      ] using hPrimitiveTop
    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass l τ hτ hL1Top
    exact Or.inl
      ⟨id, fun n => le_rfl, tendsto_id, hTauTendsto, by simpa using hEnergyTop⟩

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
              hH3 hClass (hτ n) j l)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeSecondStateAt,
        h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
      ] using hPrimitiveTop
    exact
      h3TerminalSecondQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j l τ hτ hTauTendsto hL1Top

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
              hH3 hClass (hτ n) j k)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeFirstStateAt,
        h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
      ] using hPrimitiveTop
    exact
      h3TerminalSecondQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j k τ hτ hTauTendsto hL1Top

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) k)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeFirstStateAt,
        h3TerminalForcingThirdQRawL1MassAt,
        h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
      ] using hPrimitiveTop
    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass k τ hτ hL1Top
    exact Or.inl
      ⟨id, fun n => le_rfl, tendsto_id, hTauTendsto, by simpa using hEnergyTop⟩

  · have hM6Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
              hH3 hClass (hτ n) l)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeSecondStateAt,
        h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt,
        h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
      ] using hPrimitiveTop
    exact
      h3TerminalSecondQVelocityMoment6_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass l τ hτ hTauTendsto hM6Top

  · have hM6Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
              hH3 hClass (hτ n) j l)
          atTop atTop := by
      simpa [
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeSecondStateAt,
        h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
      ] using hPrimitiveTop
    exact
      h3TerminalSecondQProjectedRHSMoment6_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j l τ hτ hTauTendsto hM6Top

end

end Euclidean
end Bridge
end PrimeTensor
