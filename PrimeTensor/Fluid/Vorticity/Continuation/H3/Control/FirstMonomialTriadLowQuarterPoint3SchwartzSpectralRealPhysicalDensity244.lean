import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralDecodeDensity244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Strong real physical L² approximation of actual H³ velocity snapshots

The previous checkpoint transported simultaneous three-component Schwartz
weighted-spectral approximations through inverse Fourier to complex physical
L². Here we pass through the actual real-part projection, which is
contractive and continuous on real Banach L². As a consequence, the SAME
spectral Schwartz sequence converges to the real physical decoder.

For a genuine compatible H³ snapshot the repository already proves that
its real decoder equals the actual zeroth-order physical velocity jet.
We specialize the new approximation theorem to this genuine physical L²
state, removing a decoder-identification hypothesis rather than assuming it.

The Schwartz property here belongs to the WEIGHTED SPECTRAL approximants.
Their real-decoded physical L² representatives are not asserted to be
physical Schwartz, solenoidal, or convergent in physical E₂/E₃ energies.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section
set_option maxHeartbeats 800000

noncomputable local instance axisFintypeSpectralRealPhysicalDensity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine real inverse-Fourier decoder is a contraction on weighted
H³ *differences*, not only on individual states. -/
theorem norm_h3SpectralScalarDecodeRealL2_sub_le244
    (F G : H3SpectralScalarState) :
    ‖h3SpectralScalarDecodeRealL2 F -
        h3SpectralScalarDecodeRealL2 G‖ ≤ ‖F - G‖ := by
  rw [← h3SpectralScalarDecodeRealL2_sub]
  exact norm_h3SpectralScalarDecodeRealL2_le (F - G)

/-- Real inverse-Fourier decoding is strongly continuous, derived from
continuity of the complex decoder and real-part projection. -/
theorem continuous_h3SpectralScalarDecodeRealL2_244 :
    Continuous (fun F : H3SpectralScalarState =>
      h3SpectralScalarDecodeRealL2 F) := by
  change Continuous (fun F : H3SpectralScalarState =>
    h3RealPartFourierL2 (h3SpectralScalarDecodeComplexL2 F))
  exact continuous_h3RealPartFourierL2.comp
    continuous_h3SpectralScalarDecodeComplexL2_244

/-- Every strongly convergent full spectral velocity sequence converges
in the actual three-component REAL physical L² decoder. -/
theorem h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244
    {F : ℕ → H3SpectralVelocityState} {U : H3SpectralVelocityState}
    (hF : Tendsto F atTop (𝓝 U)) :
    Tendsto (fun n : ℕ => h3SpectralVelocityDecodeRealL2 (F n))
      atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) := by
  rw [tendsto_pi_nhds]
  intro j
  have hCoord : Tendsto (fun n : ℕ => F n j) atTop (𝓝 (U j)) :=
    (continuous_apply j).continuousAt.tendsto.comp hF
  exact continuous_h3SpectralScalarDecodeRealL2_244.continuousAt.tendsto.comp
    hCoord

/-- The previously constructed, same spectral Schwartz sequence converges
both in weighted spectral H³ and as a REAL physical L² velocity sequence. -/
theorem exists_h3SchwartzSpectralVelocityApprox_realDecodedSequence244
    (U : H3SpectralVelocityState) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      Tendsto (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 U) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
        (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) ∧
      CauchySeq (fun n => h3SpectralVelocityDecodeRealL2
        (h3SchwartzSpectralVelocityRealization244 (Φ n))) := by
  obtain ⟨Φ, hWeighted, _, _, _⟩ :=
    exists_h3SchwartzSpectralVelocityApprox_decodedSequence244 U
  have hReal := h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244
    hWeighted
  exact ⟨Φ, hWeighted, hReal, hReal.cauchySeq⟩

/-- At a genuine compatible H³ physical time slice, a constructed sequence
of three-component weighted spectral Schwartz representatives has real
inverse-Fourier decoders converging to the ACTUAL physical zeroth-order
velocity components, transported to the project's Euclidean carrier.

This is an explicit physical L² approximation theorem, NOT an E₂/E₃
Schwartz graph-density theorem. -/
theorem exists_h3SchwartzSpectralApprox_actualPhysicalZeroJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      Tendsto (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
        (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨Φ, hWeighted, hReal, _⟩ :=
    exists_h3SchwartzSpectralVelocityApprox_realDecodedSequence244 U
  have hEq :
      h3SpectralVelocityDecodeRealL2 U =
        (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j))) := by
    funext j
    exact h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
      hFourier j
  refine ⟨Φ, hWeighted, ?_⟩
  rw [← hEq]
  exact hReal

end
end PrimeTensor.FirstMonomialTriad
