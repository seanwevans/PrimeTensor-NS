import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationAngularConcentration

/-!
# Single-time physical H³ dissipation concentration

The preceding checkpoint produces a two-snapshot physical dissipation
concentration majorant on shrinking equatorial cones.  This file removes the
remaining two-time pairing.

On the genuine H³ energy-class tail the one-state dissipation densities are
integrable.  Hence the extended localized mass is the `ENNReal.ofReal` lift of
the corresponding real localized integral.  The pair majorant is therefore
exactly the `ENNReal.ofReal` lift of

    8 * (M_s + M_t).

At each index choose whichever of `M_s` and `M_t` is larger.  Then

    8 * (M_s + M_t) ≤ 16 * max(M_s,M_t),

so the same fixed positive lower threshold survives on one selected physical
time slice.  Since both candidate time sequences converge to `T`, an
indexwise choice between them also converges to `T`.

Thus hypothetical nonextension, under the already retained hypotheses, forces
a genuine single-time sequence carrying localized full H³ dissipation mass in
shrinking equatorial cones.  This remains a necessary-condition theorem only.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationSingleTimeConcentration
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationSingleTimeConcentration :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Real localized dissipation mass -/

/-- Real localized one-time H³ dissipation mass on the bad-cone high-radial
region.  On the energy-class tail this is finite and its `ENNReal.ofReal` lift
is exactly `h3TerminalPhysicalDissipationBadConeHighRadialMass`. -/
noncomputable def h3TerminalPhysicalDissipationBadConeHighRadialRealMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (κ ρ t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) : ℝ :=
  ∫ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        \
      h3TerminalRadialFrequencyBelow ρ,
    h3TerminalSpectralDissipationSingleDensity
      (h3TerminalVelocitySpectralStateAt hH3 t ht) ξ

/-- The real localized one-time dissipation mass is nonnegative. -/
theorem h3TerminalPhysicalDissipationBadConeHighRadialRealMass_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (κ ρ t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    0 ≤
      h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3 i κ ρ t ht := by
  unfold h3TerminalPhysicalDissipationBadConeHighRadialRealMass
  exact
    integral_nonneg_of_ae
      (Eventually.of_forall
        (fun ξ =>
          h3TerminalSpectralDissipationSingleDensity_nonneg
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            ξ))

/-- On the genuine H³ energy-class tail, the extended localized dissipation
mass is exactly the `ENNReal.ofReal` lift of the real localized integral. -/
theorem ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (κ ρ : ℝ) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    ENNReal.ofReal
        (h3TerminalPhysicalDissipationBadConeHighRadialRealMass
          hH3 i κ ρ t htAbs)
      =
    h3TerminalPhysicalDissipationBadConeHighRadialMass
      hH3 i κ ρ t htAbs := by
  dsimp only

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

  have hFInt : IntegrableOn f S volume := by
    have hGlobal : Integrable f volume := by
      dsimp only [f, htAbs]
      simpa only using
        (h3TerminalSpectralDissipationSingleDensity_integrable
          hH3 hClass ht)
    exact hGlobal.integrableOn

  have hFNonneg :
      0 ≤ᵐ[volume.restrict S] f := by
    filter_upwards with ξ
    exact
      h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
        ξ

  unfold
    h3TerminalPhysicalDissipationBadConeHighRadialRealMass
    h3TerminalPhysicalDissipationBadConeHighRadialMass

  change
    ENNReal.ofReal
        (∫ ξ in S, f ξ ∂volume)
      =
    ∫⁻ ξ in S,
      ENNReal.ofReal (f ξ)
      ∂volume

  exact
    ofReal_integral_eq_lintegral_ofReal
      hFInt
      hFNonneg

/-! ## Exact pair-majorant decomposition on the energy-class tail -/

/-- On two genuine energy-class slices, the physical pair majorant is exactly
the `ENNReal.ofReal` lift of eight times the sum of the two real localized
single-time masses. -/
theorem physicalDissipationPairBadConeHighRadialMajorantMass_eq_ofReal_eight_mul_realMass_add
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (κ ρ : ℝ) :
    let hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
        hH3 i κ ρ s t hsAbs htAbs
      =
    ENNReal.ofReal
      (8 *
        (h3TerminalPhysicalDissipationBadConeHighRadialRealMass
            hH3 i κ ρ s hsAbs
          +
         h3TerminalPhysicalDissipationBadConeHighRadialRealMass
            hH3 i κ ρ t htAbs)) := by
  dsimp only

  let hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      \
    h3TerminalRadialFrequencyBelow ρ

  let fs : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 s hsAbs) ξ

  let ft : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs) ξ

  have hFs : IntegrableOn fs S volume := by
    have hGlobal : Integrable fs volume := by
      dsimp only [fs, hsAbs]
      simpa only using
        (h3TerminalSpectralDissipationSingleDensity_integrable
          hH3 hClass hs)
    exact hGlobal.integrableOn

  have hFt : IntegrableOn ft S volume := by
    have hGlobal : Integrable ft volume := by
      dsimp only [ft, htAbs]
      simpa only using
        (h3TerminalSpectralDissipationSingleDensity_integrable
          hH3 hClass ht)
    exact hGlobal.integrableOn

  have hPairInt :
      IntegrableOn
        (fun ξ : H3FourierPoint3 =>
          8 * (fs ξ + ft ξ))
        S volume := by
    exact
      (hFs.add hFt).const_mul 8

  have hPairNonneg :
      0 ≤ᵐ[volume.restrict S]
        (fun ξ : H3FourierPoint3 =>
          8 * (fs ξ + ft ξ)) := by
    filter_upwards with ξ
    have hfs0 : 0 ≤ fs ξ := by
      dsimp only [fs]
      exact
        h3TerminalSpectralDissipationSingleDensity_nonneg
          (h3TerminalVelocitySpectralStateAt hH3 s hsAbs)
          ξ
    have hft0 : 0 ≤ ft ξ := by
      dsimp only [ft]
      exact
        h3TerminalSpectralDissipationSingleDensity_nonneg
          (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
          ξ
    positivity

  have hIntegral :
      (∫ ξ in S,
        8 * (fs ξ + ft ξ)
        ∂volume)
        =
      8 *
        ((∫ ξ in S, fs ξ ∂volume)
          +
         (∫ ξ in S, ft ξ ∂volume)) := by
    calc
      (∫ ξ in S,
        8 * (fs ξ + ft ξ)
        ∂volume)
          =
        8 *
          (∫ ξ in S,
            fs ξ + ft ξ
            ∂volume) := by
        rw [integral_const_mul]
      _ =
        8 *
          ((∫ ξ in S, fs ξ ∂volume)
            +
           (∫ ξ in S, ft ξ ∂volume)) := by
        rw [integral_add hFs hFt]

  have hBridge :
      ENNReal.ofReal
        (∫ ξ in S,
          8 * (fs ξ + ft ξ)
          ∂volume)
        =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (8 * (fs ξ + ft ξ))
        ∂volume := by
    exact
      ofReal_integral_eq_lintegral_ofReal
        hPairInt
        hPairNonneg

  unfold
    h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
    h3TerminalPhysicalDissipationBadConeHighRadialRealMass

  change
    (∫⁻ ξ in S,
      ENNReal.ofReal
        (8 * (fs ξ + ft ξ))
      ∂volume)
      =
    ENNReal.ofReal
      (8 *
        ((∫ ξ in S, fs ξ ∂volume)
          +
         (∫ ξ in S, ft ξ ∂volume)))

  calc
    (∫⁻ ξ in S,
      ENNReal.ofReal
        (8 * (fs ξ + ft ξ))
      ∂volume)
        =
      ENNReal.ofReal
        (∫ ξ in S,
          8 * (fs ξ + ft ξ)
          ∂volume) :=
      hBridge.symm

    _ =
      ENNReal.ofReal
        (8 *
          ((∫ ξ in S, fs ξ ∂volume)
            +
           (∫ ξ in S, ft ξ ∂volume))) := by
      rw [hIntegral]

/-! ## Single-time concentration branch -/

/-- A single strict-time sequence carries a fixed localized full-H³
dissipation lower bound while the equatorial aperture collapses to zero. -/
def H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
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
      ∀ n,
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3 i (κ n) ρ (τ n)
            ⟨lt_trans hClass.terminal_start.1 (hτ n).1,
              (hτ n).2⟩

/-- The two-time physical dissipation concentration branch always contains a
single-time concentration sequence, with only the sharp factor-two loss from
choosing the larger of the two snapshot masses. -/
theorem physicalDissipationSingleTimeAngularConcentrationBranchAtCutoff_of_pairBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationAngularConcentrationBranchAtCutoff
        hH3 i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
      hH3 hClass i ε ρ := by
  classical

  unfold H3TerminalPhysicalDissipationAngularConcentrationBranchAtCutoff at hBranch

  obtain
    ⟨s, t, hs, ht, p,
      hPMono,
      hSTendsto,
      hTTendsto,
      hKappaTendsto,
      hMass⟩ :=
    hBranch

  have hSPast :
      ∀ᶠ n : ℕ in atTop,
        a < s (p n) :=
    hSTendsto.eventually
      (Ioi_mem_nhds hClass.terminal_start.2)

  have hTPast :
      ∀ᶠ n : ℕ in atTop,
        a < t (p n) :=
    hTTendsto.eventually
      (Ioi_mem_nhds hClass.terminal_start.2)

  obtain ⟨N, hN⟩ :=
    eventually_atTop.1
      (hSPast.and hTPast)

  let m : ℕ → ℕ :=
    fun n => max n N

  have hm :
      ∀ n : ℕ, n ≤ m n :=
    fun n => le_max_left n N

  have hmTop :
      Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with n hn
    exact hn.trans (hm n)

  let σ : ℕ → ℝ :=
    fun n => s (p (m n))

  let θ : ℕ → ℝ :=
    fun n => t (p (m n))

  let κ : ℕ → ℝ :=
    fun n =>
      (1 : ℝ) / (((p (m n) : ℕ) : ℝ) + 2)

  have hσ :
      ∀ n, σ n ∈ Set.Ioo a T := by
    intro n
    have hPast :=
      (hN (m n) (le_max_right n N)).1
    exact
      ⟨hPast, (hs (p (m n))).2⟩

  have hθ :
      ∀ n, θ n ∈ Set.Ioo a T := by
    intro n
    have hPast :=
      (hN (m n) (le_max_right n N)).2
    exact
      ⟨hPast, (ht (p (m n))).2⟩

  have hσTendsto :
      Tendsto σ atTop (𝓝 T) := by
    exact
      hSTendsto.comp hmTop

  have hθTendsto :
      Tendsto θ atTop (𝓝 T) := by
    exact
      hTTendsto.comp hmTop

  have hκTendsto :
      Tendsto κ atTop (𝓝 0) := by
    exact
      hKappaTendsto.comp hmTop

  have hκPos :
      ∀ n, 0 < κ n := by
    intro n
    dsimp only [κ]
    positivity

  let hσAbs :
      ∀ n, σ n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨lt_trans hClass.terminal_start.1 (hσ n).1,
        (hσ n).2⟩

  let hθAbs :
      ∀ n, θ n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨lt_trans hClass.terminal_start.1 (hθ n).1,
        (hθ n).2⟩

  let Mσ : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3 i (κ n) ρ (σ n) (hσAbs n)

  let Mθ : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3 i (κ n) ρ (θ n) (hθAbs n)

  let τ : ℕ → ℝ :=
    fun n =>
      if Mσ n ≤ Mθ n then θ n else σ n

  have hτ :
      ∀ n, τ n ∈ Set.Ioo a T := by
    intro n
    dsimp only [τ]
    by_cases hComp : Mσ n ≤ Mθ n
    · simp only [if_pos hComp]
      exact hθ n
    · simp only [if_neg hComp]
      exact hσ n

  have hτTendsto :
      Tendsto τ atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop]
    rw [Metric.tendsto_atTop] at hσTendsto
    rw [Metric.tendsto_atTop] at hθTendsto
    intro δ hδ
    obtain ⟨Nσ, hNσ⟩ := hσTendsto δ hδ
    obtain ⟨Nθ, hNθ⟩ := hθTendsto δ hδ
    refine ⟨max Nσ Nθ, ?_⟩
    intro n hn
    dsimp only [τ]
    by_cases hComp : Mσ n ≤ Mθ n
    · simp only [if_pos hComp]
      exact
        hNθ n
          ((le_max_right Nσ Nθ).trans hn)
    · simp only [if_neg hComp]
      exact
        hNσ n
          ((le_max_left Nσ Nθ).trans hn)

  refine
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      ?_⟩

  intro n

  have hPairLower :=
    hMass (m n)

  have hPairEq :=
    physicalDissipationPairBadConeHighRadialMajorantMass_eq_ofReal_eight_mul_realMass_add
      hH3
      hClass
      (hσ n)
      (hθ n)
      i
      (κ n)
      ρ

  have hPairLowerReal :
      ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
        <
      ENNReal.ofReal
        (8 * (Mσ n + Mθ n)) := by
    dsimp only [σ, θ, κ, Mσ, Mθ, hσAbs, hθAbs] at hPairEq ⊢
    exact
      hPairLower.trans_eq
        hPairEq

  by_cases hComp : Mσ n ≤ Mθ n

  · have hMθNonneg : 0 ≤ Mθ n := by
      dsimp only [Mθ]
      exact
        h3TerminalPhysicalDissipationBadConeHighRadialRealMass_nonneg
          hH3 i (κ n) ρ (θ n) (hθAbs n)

    have hRealLe :
        8 * (Mσ n + Mθ n)
          ≤
        16 * Mθ n := by
      nlinarith

    have hOfRealLe :
        ENNReal.ofReal
            (8 * (Mσ n + Mθ n))
          ≤
        ENNReal.ofReal
            (16 * Mθ n) :=
      ENNReal.ofReal_le_ofReal hRealLe

    have hBridge :=
      ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
        hH3
        hClass
        (hθ n)
        i
        (κ n)
        ρ

    have hFinal :
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3 i (κ n) ρ (θ n) (hθAbs n) := by
      calc
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
            <
          ENNReal.ofReal
            (8 * (Mσ n + Mθ n)) :=
          hPairLowerReal
        _ ≤
          ENNReal.ofReal
            (16 * Mθ n) :=
          hOfRealLe
        _ =
          16 *
            h3TerminalPhysicalDissipationBadConeHighRadialMass
              hH3 i (κ n) ρ (θ n) (hθAbs n) := by
          rw [
            ENNReal.ofReal_mul
              (by norm_num : (0 : ℝ) ≤ 16)
          ]
          norm_num
          dsimp only [Mθ] at hBridge
          rw [hBridge]

    simpa only [τ, if_pos hComp] using hFinal

  · have hMσNonneg : 0 ≤ Mσ n := by
      dsimp only [Mσ]
      exact
        h3TerminalPhysicalDissipationBadConeHighRadialRealMass_nonneg
          hH3 i (κ n) ρ (σ n) (hσAbs n)

    have hReverse : Mθ n ≤ Mσ n :=
      le_of_not_ge hComp

    have hRealLe :
        8 * (Mσ n + Mθ n)
          ≤
        16 * Mσ n := by
      nlinarith

    have hOfRealLe :
        ENNReal.ofReal
            (8 * (Mσ n + Mθ n))
          ≤
        ENNReal.ofReal
            (16 * Mσ n) :=
      ENNReal.ofReal_le_ofReal hRealLe

    have hBridge :=
      ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
        hH3
        hClass
        (hσ n)
        i
        (κ n)
        ρ

    have hFinal :
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3 i (κ n) ρ (σ n) (hσAbs n) := by
      calc
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
            <
          ENNReal.ofReal
            (8 * (Mσ n + Mθ n)) :=
          hPairLowerReal
        _ ≤
          ENNReal.ofReal
            (16 * Mσ n) :=
          hOfRealLe
        _ =
          16 *
            h3TerminalPhysicalDissipationBadConeHighRadialMass
              hH3 i (κ n) ρ (σ n) (hσAbs n) := by
          rw [
            ENNReal.ofReal_mul
              (by norm_num : (0 : ℝ) ≤ 16)
          ]
          norm_num
          dsimp only [Mσ] at hBridge
          rw [hBridge]

    simpa only [τ, if_neg hComp] using hFinal

/-! ## Necessary single-time concentration under hypothetical nonextension -/

/-- Under the retained raw-Fourier L² Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity endpoint force a
single-time localized full-H³ dissipation concentration sequence at one fixed
positive radial cutoff. -/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationAngularConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
          hH3 hClass i ε ρ := by
  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hPairBranch⟩ :=
    exists_failing_complementary_vorticityComponent_physicalDissipationAngularConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeAngularConcentrationBranchAtCutoff_of_pairBranch
      hH3
      hClass
      i
      hPairBranch

end

end Euclidean
end Bridge
end PrimeTensor
