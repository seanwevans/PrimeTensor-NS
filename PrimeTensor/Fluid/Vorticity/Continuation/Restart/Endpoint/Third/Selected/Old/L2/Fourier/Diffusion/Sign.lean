import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Plancherel.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Diffusion.Continuity

/-!
# Fourier-side diffusion sign for the selected/old L² difference

The scalar Plancherel pairing identity from
`SelectedOldL2PlancherelPairing` lets us prove diffusion dissipation entirely
on the Fourier side.

For a weighted H³ scalar state `G`, write

    raw(G) = W₃⁻¹ G

and let `lap(G)` be the already-packaged raw Fourier Laplacian.  Its existing
a.e. representative theorem is

    lap(G)(ξ) = -q(ξ) raw(G)(ξ),

with `q(ξ) = h3FourierGradientSquare ξ ≥ 0`.

Therefore

    Re ⟪raw(G), lap(G)⟫
      = ∫ -q(ξ) |raw(G)(ξ)|² dξ
      ≤ 0.

This avoids any separate decay-at-infinity or spatial integration-by-parts
hypothesis for the selected/old difference.

The second theorem transports this sign back to physical real `L²`: if a
physical pair `F,L` Fourier-transforms exactly to `raw(G),lap(G)`, then

    ⟪F,L⟫_ℝ ≤ 0.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2FourierDiffusionSign
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The raw Fourier field of a weighted H³ scalar state pairs nonpositively
with its quotient-safe Fourier Laplacian. -/
theorem re_inner_h3SpectralScalarRawFourierL2_laplacian_nonpos
    (G : H3SpectralScalarState) :
    (inner ℂ
        (h3SpectralScalarRawFourierL2 G)
        (h3SpectralScalarLaplacianRawFourierL2 G)).re
      ≤
    0 := by
  calc
    (inner ℂ
        (h3SpectralScalarRawFourierL2 G)
        (h3SpectralScalarLaplacianRawFourierL2 G)).re
        =
      Complex.re
        (∫ ξ : H3FourierPoint3,
          inner ℂ
            (h3SpectralScalarRawFourierL2 G ξ)
            (h3SpectralScalarLaplacianRawFourierL2 G ξ)) := by
          rw [MeasureTheory.L2.inner_def]
    _ =
      ∫ ξ : H3FourierPoint3,
        Complex.re
          (inner ℂ
            (h3SpectralScalarRawFourierL2 G ξ)
            (h3SpectralScalarLaplacianRawFourierL2 G ξ)) := by
          symm
          exact
            Complex.reCLM.integral_comp_comm
              (MeasureTheory.L2.integrable_inner
                (h3SpectralScalarRawFourierL2 G)
                (h3SpectralScalarLaplacianRawFourierL2 G))
    _ ≤ 0 := by
      apply MeasureTheory.integral_nonpos_of_ae

      have hLap :=
        h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
          G

      filter_upwards [hLap] with ξ hLapξ

      rw [hLapξ]

      let z : ℂ :=
        h3SpectralScalarRawFourierL2 G ξ

      let q : ℝ :=
        h3FourierGradientSquare ξ

      have hq : 0 ≤ q := by
        dsimp only [q]
        exact h3FourierGradientSquare_nonneg ξ

      change
        Complex.re
            (inner ℂ z
              ((-(q : ℂ)) • z))
          ≤
        0

      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]

      have hComplex :
          (-(q : ℂ)) * ((‖z‖ : ℂ) ^ 2)
            =
          ((-q * ‖z‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring

      have hRe :
          Complex.re
              ((-(q : ℂ)) * ((‖z‖ : ℂ) ^ 2))
            =
          -q * ‖z‖ ^ 2 := by
        have h :=
          congrArg Complex.re hComplex
        simpa only [Complex.ofReal_re] using h

      calc
        Complex.re
            ((-(q : ℂ)) * ((‖z‖ : ℂ) ^ 2))
            =
          -q * ‖z‖ ^ 2 := hRe
        _ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr hq)
            (sq_nonneg ‖z‖)

/-- Physical scalar `L²` diffusion is nonpositive whenever Plancherel
identifies the physical state with the raw Fourier field of one weighted H³
state and identifies the physical linear term with that state's Fourier
Laplacian. -/
theorem h3ScalarL2_inner_nonpos_of_fourier_eq_raw_laplacian
    (F L : H3ScalarL2)
    (G : H3SpectralScalarState)
    (hF :
      h3ScalarFourierL2 F
        =
      h3SpectralScalarRawFourierL2 G)
    (hL :
      h3ScalarFourierL2 L
        =
      h3SpectralScalarLaplacianRawFourierL2 G) :
    inner ℝ F L ≤ 0 := by
  apply
    h3ScalarL2_inner_nonpos_of_fourier_re_inner_nonpos
      F L

  rw [hF, hL]

  exact
    re_inner_h3SpectralScalarRawFourierL2_laplacian_nonpos G

/-- Minimal spectral realization datum for one physical scalar diffusion
pairing. -/
def H3ScalarL2FourierLaplacianPairingData
    (F L : H3ScalarL2) : Prop :=
  ∃ G : H3SpectralScalarState,
    h3ScalarFourierL2 F
        =
      h3SpectralScalarRawFourierL2 G
      ∧
    h3ScalarFourierL2 L
        =
      h3SpectralScalarLaplacianRawFourierL2 G

/-- Spectral realization of a physical scalar state and its Laplacian gives
diffusion nonpositivity with no spatial IBP assumption. -/
theorem h3ScalarL2_inner_nonpos_of_fourierLaplacianPairingData
    (F L : H3ScalarL2)
    (hData :
      H3ScalarL2FourierLaplacianPairingData F L) :
    inner ℝ F L ≤ 0 := by
  rcases hData with ⟨G, hF, hL⟩

  exact
    h3ScalarL2_inner_nonpos_of_fourier_eq_raw_laplacian
      F L G hF hL

end

end Euclidean
end Bridge
end PrimeTensor
