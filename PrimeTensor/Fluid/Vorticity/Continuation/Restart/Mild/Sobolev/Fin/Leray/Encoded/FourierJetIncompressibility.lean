import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Incompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Compatibility

/-!
# Fourier-jet incompressibility implies spectral H³ incompressibility

The encoded Leray layer isolates the PDE-facing obligation as the raw
frequency identity

    Σⱼ dⱼ(ξ) ûⱼ(ξ) = 0.

The classical H³ Fourier-compatibility layer already identifies each
multiplier `dⱼ ûⱼ` with the Fourier transform of the concrete diagonal first
jet `∂ⱼ uⱼ`.

This file packages the exact intermediate statement which remains to be
derived from physical incompressibility:

    Σⱼ Fourier(∂ⱼ uⱼ) = 0    a.e.

Once that diagonal first-jet identity is available, all remaining frequency
algebra is automatic:

* Fourier compatibility rewrites the diagonal first jets to derivative-symbol
  multiples of the base Fourier velocity;
* hence the raw base Fourier velocity is divergence-free;
* the common H³ weight preserves that identity;
* therefore the encoded H³ state is divergence-free and is fixed by Leray.

The next analytic increment only has to prove the diagonal Fourier-jet identity
from the physical equation `div u = 0`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3LerayFourierJetIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The Fourier transforms of the three concrete diagonal first derivatives
sum to zero almost everywhere.  This is the exact Plancherel-side image of the
physical incompressibility equation. -/
def VelocityH3FourierDiagonalDivergenceFreeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : Prop :=
  ∀ᵐ ξ ∂volume,
    (∑ j : Fin 3,
      (velocityH3FourierJetAt
        u t hInt hMeas
        (h3JetSlot1 j j) :
          H3FourierPoint3 → ℂ) ξ)
      =
    0

/-- Fourier compatibility converts vanishing of the diagonal first-jet
Fourier sum into the raw base-frequency divergence identity. -/
theorem velocityH3BaseFourierDivergenceFreeAt_of_fourierDiagonal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas)
    (hDiagonal :
      VelocityH3FourierDiagonalDivergenceFreeAt
        u t hInt hMeas) :
    VelocityH3BaseFourierDivergenceFreeAt
      u t hInt hMeas := by
  have h0 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier 0 0
  have h1 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier 1 1
  have h2 :=
    velocityH3FourierCompatibleAt_orderOne
      hFourier 2 2

  filter_upwards [hDiagonal, h0, h1, h2] with
    ξ hDiagonalξ h0ξ h1ξ h2ξ

  simp only [Fin.sum_univ_three] at hDiagonalξ ⊢

  rw [← h0ξ, ← h1ξ, ← h2ξ]

  exact hDiagonalξ

/-- Consequently the weighted H³ spectral encoder is divergence-free whenever
the concrete diagonal first-jet Fourier sum vanishes. -/
theorem velocityH3SpectralStateAt_divergenceFree_of_fourierDiagonal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas)
    (hDiagonal :
      VelocityH3FourierDiagonalDivergenceFreeAt
        u t hInt hMeas) :
    H3SpectralFinDivergenceFree
      (velocityH3SpectralStateAt
        u t hInt hMeas hFourier) := by
  exact
    velocityH3SpectralStateAt_divergenceFree_of_base
      hFourier
      (velocityH3BaseFourierDivergenceFreeAt_of_fourierDiagonal
        hFourier hDiagonal)

/-- In the same hypotheses, the finite Leray projector fixes the encoded H³
restart state exactly. -/
theorem h3SpectralFinLerayApply_velocityH3SpectralStateAt_eq_of_fourierDiagonal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas)
    (hDiagonal :
      VelocityH3FourierDiagonalDivergenceFreeAt
        u t hInt hMeas) :
    h3SpectralFinLerayApply
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
      =
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (velocityH3SpectralStateAt_divergenceFree_of_fourierDiagonal
        hFourier hDiagonal)

end
end Euclidean
end Bridge
end PrimeTensor
