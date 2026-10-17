import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralVelocityDensity244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Raw.Fourier.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Decoder

/-!
# Weighted H³ Schwartz-vector density descends to genuine complex physical L²

The preceding full spectral velocity-density theorem supplies actual
three-component Schwartz approximants of an arbitrary weighted H³ state.
This module transports the SAME approximating sequence, without replacing
it by unrelated density witnesses, through the project's exact contractive
Fourier deweighting and its inverse-L² Fourier isometry.

Consequently the raw Fourier L² velocity and the decoded complex physical
L² velocity converge strongly, componentwise and simultaneously, with the
weighted H³ state. An explicit scalar contraction estimate records the
physical norm loss (at most one) along this map.

These complex spectral Schwartz approximants are not yet asserted to be
Fourier transforms of REAL, divergence-free PHYSICAL Schwartz fields.
In particular this module does not assert E₂/E₃ physical Schwartz graph
convergence or identification of the completed signed transport pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section

noncomputable local instance axisFintypeSpectralDecodeDensity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact inverse Fourier reconstruction is contractive on differences
of weighted H³ scalar states; no reality hypothesis is needed. -/
theorem norm_h3SpectralScalarDecodeComplexL2_sub_le244
    (F G : H3SpectralScalarState) :
    ‖h3SpectralScalarDecodeComplexL2 F -
        h3SpectralScalarDecodeComplexL2 G‖ ≤ ‖F - G‖ := by
  let T := (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
  change ‖T (h3SpectralScalarRawFourierL2 F) -
      T (h3SpectralScalarRawFourierL2 G)‖ ≤ ‖F - G‖
  rw [← map_sub]
  calc
    ‖T (h3SpectralScalarRawFourierL2 F -
        h3SpectralScalarRawFourierL2 G)‖ =
        ‖h3SpectralScalarRawFourierL2 F -
          h3SpectralScalarRawFourierL2 G‖ := T.norm_map _
    _ ≤ ‖F - G‖ := norm_h3SpectralScalarRawFourierL2_sub_le F G

/-- The exact weighted-to-raw Fourier map is continuous on the whole
spectral Hilbert state, not just along one Navier–Stokes trajectory. -/
theorem continuous_h3SpectralScalarRawFourierL2_244 :
    Continuous (fun F : H3SpectralScalarState =>
      h3SpectralScalarRawFourierL2 F) := by
  exact continuous_h3SpectralScalarRawFourierL2_comp
    (fun F : H3SpectralScalarState => F) continuous_id

/-- Inverse Fourier decoding of arbitrary weighted H³ scalar data into
complex physical L² is continuous. It is not a Schwartz-to-Schwartz claim. -/
theorem continuous_h3SpectralScalarDecodeComplexL2_244 :
    Continuous (fun F : H3SpectralScalarState =>
      h3SpectralScalarDecodeComplexL2 F) := by
  change Continuous (fun F : H3SpectralScalarState =>
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
      (h3SpectralScalarRawFourierL2 F))
  exact (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.continuous.comp
    continuous_h3SpectralScalarRawFourierL2_244

/-- A convergent THREE-component weighted spectral sequence remains
convergent as a complete raw Fourier L² velocity sequence. -/
theorem h3SpectralVelocityRawFourierL2_tendsto_of_weighted244
    {F : ℕ → H3SpectralVelocityState} {U : H3SpectralVelocityState}
    (hF : Tendsto F atTop (𝓝 U)) :
    Tendsto (fun n : ℕ => fun j : Fin 3 =>
        h3SpectralScalarRawFourierL2 (F n j)) atTop
      (𝓝 (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U j))) := by
  rw [tendsto_pi_nhds]
  intro j
  have hCoord : Tendsto (fun n : ℕ => F n j) atTop (𝓝 (U j)) :=
    (continuous_apply j).continuousAt.tendsto.comp hF
  exact continuous_h3SpectralScalarRawFourierL2_244.continuousAt.tendsto.comp
    hCoord

/-- The same convergence is preserved by the genuine unitary complex
inverse Fourier decoder, in all three physical L² components. -/
theorem h3SpectralVelocityDecodeComplexL2_tendsto_of_weighted244
    {F : ℕ → H3SpectralVelocityState} {U : H3SpectralVelocityState}
    (hF : Tendsto F atTop (𝓝 U)) :
    Tendsto (fun n : ℕ => h3SpectralVelocityDecodeComplexL2 (F n))
      atTop (𝓝 (h3SpectralVelocityDecodeComplexL2 U)) := by
  rw [tendsto_pi_nhds]
  intro j
  have hCoord : Tendsto (fun n : ℕ => F n j) atTop (𝓝 (U j)) :=
    (continuous_apply j).continuousAt.tendsto.comp hF
  exact continuous_h3SpectralScalarDecodeComplexL2_244.continuousAt.tendsto.comp
    hCoord

/-- One genuinely constructed spectral Schwartz-vector sequence approximates
all three interpretations of the SAME H³ state: weighted, deweighted raw
Fourier L², and decoded complex physical L². The latter is also Cauchy. -/
theorem exists_h3SchwartzSpectralVelocityApprox_decodedSequence244
    (U : H3SpectralVelocityState) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      Tendsto (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 U) ∧
      Tendsto (fun n => fun j : Fin 3 =>
        h3SpectralScalarRawFourierL2
          (h3SchwartzSpectralVelocityRealization244 (Φ n) j))
        atTop (𝓝 (fun j : Fin 3 =>
          h3SpectralScalarRawFourierL2 (U j))) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeComplexL2
        (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (h3SpectralVelocityDecodeComplexL2 U)) ∧
      CauchySeq (fun n => h3SpectralVelocityDecodeComplexL2
        (h3SchwartzSpectralVelocityRealization244 (Φ n))) := by
  obtain ⟨Φ, hWeighted, _⟩ :=
    exists_h3SchwartzSpectralVelocityApprox_sequence244 U
  have hRaw := h3SpectralVelocityRawFourierL2_tendsto_of_weighted244
    hWeighted
  have hDecoded := h3SpectralVelocityDecodeComplexL2_tendsto_of_weighted244
    hWeighted
  exact ⟨Φ, hWeighted, hRaw, hDecoded, hDecoded.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad
