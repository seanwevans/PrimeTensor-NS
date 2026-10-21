import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdActualLowerOrderSlack244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalAllLowerOrderAbsorption
import Mathlib.Tactic

/-!
# Kinetic-anchored genuinely negative spectral H³ channel

The previous normalized signed-channel obstruction could be produced by the
positive `24 C₁ sqrt(E)` allowance: it did not show that either cubic was
negative.  The *physical* kinetic-anchored absorption theorem is stronger.
After freezing a kinetic anchor b, hypothetical nonextension forces

  M E(t) + D(t) < - T₃(t)

at arbitrarily late times, for every M >= 0.  The already-proved exact
physical/spectral bridge identifies T₃ with G₃ + 3 M₃, with no spatial
approximation or choice of Schwartz witness remaining.

Splitting the energy cost and the **actual dissipation** evenly, a genuinely
negative gradient or interpolation channel must occur.  Finite cofinal
selection makes the choice of signed channel independent of the tail and
threshold.  In particular the selected cubic overwhelms arbitrarily large
multiples of *the entire actual H³ energy*, even after being charged half
of the physical H³ viscous dissipation.

This is conditional on nonextension.  The static Schwartz concentration
counterexamples prohibit concluding an unrestricted signed coercivity bound
from this necessary condition.  No unconditional Navier--Stokes regularity or
finite-time singularity is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- The kinetic anchor removes the artificial positive sqrt-energy allowance
from a *genuine* physical obstruction.  One of the two canonical signed
spectral blocks must pay M times the full physical H³ energy and one half of
its full viscous dissipation on every sufficiently late terminal tail. -/
theorem h3Path_weightedThird_kineticAnchored_negativeSplit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) +
          M * velocityH3EnergyAt u t +
          velocityH3DissipationAt u t / 2 < 0 ∨
       3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t) +
          M * velocityH3EnergyAt u t +
          velocityH3DissipationAt u t / 2 < 0) := by
  have hTwoM : 0 ≤ 2 * M := by linarith only [hM]
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hTwoM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hIdent := h3Path_weightedFullThird_eq_physical244
    hH3 hClass htClass
  rw [hIdent] at hAdverse
  unfold weightedH3CanonicalFullThirdCommutator244 at hAdverse
  refine ⟨t, ht, ?_⟩
  by_contra hNone
  push Not at hNone
  nlinarith only [hAdverse, hNone.1, hNone.2]

/-- The genuinely adverse signed block is FIXED for every later subtail and
for every arbitrarily large energy-multiple threshold.  This avoids the
positive allowance in the original signed-channel cofinality theorem. -/
theorem h3Path_weightedThird_fixedKineticNegativeChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ M : ℝ, 0 ≤ M →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        weightedH3CanonicalGradientTransport244
            (h3PathWeightedSpectralState244 u T hH3 t) +
          M * velocityH3EnergyAt u t +
          velocityH3DissipationAt u t / 2 < 0) ∨
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ M : ℝ, 0 ≤ M →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        3 * weightedH3CanonicalSignedFirstMonomial244
            (h3PathWeightedSpectralState244 u T hH3 t) +
          M * velocityH3EnergyAt u t +
          velocityH3DissipationAt u t / 2 < 0) := by
  apply h3_twoChannel_cofinal_threshold_selection244
    (P := fun t M =>
      weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) +
        M * velocityH3EnergyAt u t +
        velocityH3DissipationAt u t / 2 < 0)
    (Q := fun t M =>
      3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t) +
        M * velocityH3EnergyAt u t +
        velocityH3DissipationAt u t / 2 < 0)
  · intro t M N hMN hHigh
    have hE : 0 ≤ velocityH3EnergyAt u t :=
      le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
    have hGap : 0 ≤ (N - M) * velocityH3EnergyAt u t :=
      mul_nonneg (sub_nonneg.mpr hMN) hE
    nlinarith only [hHigh, hGap]
  · intro t M N hMN hHigh
    have hE : 0 ≤ velocityH3EnergyAt u t :=
      le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
    have hGap : 0 ≤ (N - M) * velocityH3EnergyAt u t :=
      mul_nonneg (sub_nonneg.mpr hMN) hE
    nlinarith only [hHigh, hGap]
  · intro d hd M hM
    exact h3Path_weightedThird_kineticAnchored_negativeSplit244
      hH3 hNoExtension hClass hb hd hM

/-- Normalized form of the kinetic-anchored obstruction.  The chosen
signed canonical cubic, with *half the actual dissipation*, has arbitrarily
negative ratio to full H³ energy on all terminal subtails. -/
theorem h3Path_weightedThird_fixedNegativeNormalizedCofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ M : ℝ, 0 ≤ M →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        (weightedH3CanonicalGradientTransport244
            (h3PathWeightedSpectralState244 u T hH3 t) +
            velocityH3DissipationAt u t / 2) /
          velocityH3EnergyAt u t < -M) ∨
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ M : ℝ, 0 ≤ M →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        (3 * weightedH3CanonicalSignedFirstMonomial244
            (h3PathWeightedSpectralState244 u T hH3 t) +
            velocityH3DissipationAt u t / 2) /
          velocityH3EnergyAt u t < -M) := by
  rcases h3Path_weightedThird_fixedKineticNegativeChannel244
      hH3 hNoExtension hClass hb with hG | hI
  · left
    intro d hd M hM
    obtain ⟨t, ht, hBad⟩ := hG d hd M hM
    refine ⟨t, ht, ?_⟩
    have hE : 0 < velocityH3EnergyAt u t :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
    apply (div_lt_iff₀ hE).2
    nlinarith only [hBad]
  · right
    intro d hd M hM
    obtain ⟨t, ht, hBad⟩ := hI d hd M hM
    refine ⟨t, ht, ?_⟩
    have hE : 0 < velocityH3EnergyAt u t :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
    apply (div_lt_iff₀ hE).2
    nlinarith only [hBad]

/-- A sufficient path-dependent signed-coercivity condition: if *both*
canonical third-order blocks offset half the physical dissipation up to a
finite energy multiple on one post-kinetic-anchor tail, smooth continuation
follows.  The fixed negative-channel theorem shows why these hypotheses
cannot hold under nonextension; they are not universal spatial estimates. -/
theorem h3Path_extension_of_kineticAnchored_signedChannelFloors244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo d T →
      -(K * velocityH3EnergyAt u t) ≤
        weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) +
          velocityH3DissipationAt u t / 2)
    (hInterpolation : ∀ t : ℝ, t ∈ Set.Ioo d T →
      -(K * velocityH3EnergyAt u t) ≤
        3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t) +
          velocityH3DissipationAt u t / 2) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  let M : ℝ := max 0 K + 1
  have hM : 0 ≤ M := by
    dsimp only [M]
    have hBase : (0 : ℝ) ≤ max 0 K := le_max_left 0 K
    linarith only [hBase]
  have hKM : K < M := by
    dsimp only [M]
    have hBase : K ≤ max 0 K := le_max_right 0 K
    linarith only [hBase]
  obtain ⟨t, ht, hBad⟩ :=
    h3Path_weightedThird_kineticAnchored_negativeSplit244
      hH3 hNoExtension hClass hb hd hM
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hGap : 0 < (M - K) * velocityH3EnergyAt u t :=
    mul_pos (sub_pos.mpr hKM) hEPos
  rcases hBad with hBad | hBad
  · have hFloor := hGradient t ht
    nlinarith only [hBad, hFloor, hGap]
  · have hFloor := hInterpolation t ht
    nlinarith only [hBad, hFloor, hGap]

end
end PrimeTensor.FirstMonomialTriad
