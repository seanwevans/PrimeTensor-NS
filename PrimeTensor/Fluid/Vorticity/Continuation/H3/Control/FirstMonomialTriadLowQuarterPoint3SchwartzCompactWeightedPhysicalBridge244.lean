import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzActualThirdJetIdentification244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Compact.Density
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Raw.Approximation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPhysicalRealDensity244

/-!
# Synchronize weighted H³ approximants with genuine real physical Schwartz maps

Earlier results used two different approximating families: weighted spectral
Schwartz representatives for all 81 cubic jets, and independently chosen raw
Fourier Schwartz representatives for the real physical zero jet. This file
constructs a SINGLE family whose members simultaneously satisfy both needs.

Smooth compact density in the exact weighted spectral Hilbert carrier supplies
F close to any weighted H³ scalar G. Deweighting the compact smooth representative
of F produces an actual complex Schwartz Fourier spectrum S. Its Schwartz
inverse Fourier transform has a real Schwartz part ψ. Plancherel shows the
stronger EXACT equality

    ψ.toLp = h3SpectralScalarDecodeRealL2 F,

and the norm ‖G - F‖ is small in the ORIGINAL weighted H³ state. Unlike
raw-Fourier L² density alone, this construction retains the full weighted norm.

Coordinatewise diagonal selection yields one entire three-component sequence of
weighted approximants Fₙ AND matched genuine real physical Schwartz maps ψₙ.
In parallel, all 81 canonical cubic physical jet reconstructions of Fₙ converge.
At a genuine compatible physical H³ slice, the limits are exactly the actual
old zeroth- and third-order derivative L² jets.

We do not yet assert that the *literal* third derivatives of ψₙ agree with the
cubic multiplier reconstructions of Fₙ. That is the remaining Schwartz Fourier
derivative intertwinement, before identifying the E₂/E₃ difference energies.
Solenoidality of the approximants remains a separate issue.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology FourierTransform
open scoped ENNReal SchwartzMap FourierTransform

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeCompactWeightedPhysicalBridge244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine smooth-compact weighted approximation synchronized with a real
physical Schwartz inverse Fourier field. The *exact same* weighted F is used
on both sides of the decoding equality. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzExact244
    (G : H3SpectralScalarState)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H3SpectralScalarState,
      ∃ ψ : SchwartzMap H3FourierPoint3 ℝ,
        ‖G - F‖ < ε ∧
        h3SpectralScalarDecodeRealL2 F =
          ψ.toLp 2 (volume : Measure H3FourierPoint3) := by
  obtain ⟨F, ⟨g, hg, hcompact, hsmooth⟩, hClose⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm G hε
  let S : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hcompact hsmooth
  have hRaw :
      h3SpectralScalarRawFourierL2 F =
        S.toLp 2 (volume : Measure H3FourierPoint3) := by
    simpa only [S] using
      (h3SpectralScalarRawFourierL2_eq_deweightedSchwartz_toLp
        F g hg hcompact hsmooth)
  have hInv :
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
          (S.toLp 2 (volume : Measure H3FourierPoint3)) =
        (𝓕⁻ S).toLp 2 (volume : Measure H3FourierPoint3) := by
    change 𝓕⁻ (S.toLp 2 (volume : Measure H3FourierPoint3)) =
      (𝓕⁻ S).toLp 2 (volume : Measure H3FourierPoint3)
    exact SchwartzMap.toLp_fourierInv_eq S
  refine ⟨F, h3RawSchwartzPhysicalRealInverse244 S, hClose, ?_⟩
  change
    h3RealPartFourierL2
        ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
          (h3SpectralScalarRawFourierL2 F)) =
      (h3RawSchwartzPhysicalRealInverse244 S).toLp
        2 (volume : Measure H3FourierPoint3)
  rw [hRaw, hInv]
  exact h3RealPartFourierL2_schwartz_toLp244 (𝓕⁻ S)

/-- A SINGLE sequence of weighted H³ states and three genuine real physical
Schwartz maps. Every real Schwartz L² class is EXACTLY the decoded state of
its own weighted H³ approximant; simultaneously all cubic reconstructed jets
converge in the complete 81-coordinate product space. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzAndThirdSequence244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n : ℕ, ∀ j : Fin 3,
        h3SpectralVelocityDecodeRealL2 (V n) j =
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3)) ∧
      Tendsto (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) ∧
      Tendsto (fun n : ℕ =>
          h3SpectralVelocityThirdPhysicalJetFamily244 (V n))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 U)) := by
  classical
  have hRadiusPos (n : ℕ) :
      0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hApprox (n : ℕ) (j : Fin 3) :
      ∃ F : H3SpectralScalarState,
      ∃ ψ : SchwartzMap H3FourierPoint3 ℝ,
        ‖U j - F‖ < (1 : ℝ) / ((n : ℝ) + 1) ∧
        h3SpectralScalarDecodeRealL2 F =
          ψ.toLp 2 (volume : Measure H3FourierPoint3) := by
    exact exists_h3SmoothCompactWeighted_realSchwartzExact244
      (U j) (hRadiusPos n)
  choose F Ψ hF hΨ using hApprox
  let V : ℕ → H3SpectralVelocityState := fun n j => F n j
  have hRadiusTendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hWeighted : Tendsto V atTop (𝓝 U) := by
    rw [tendsto_pi_nhds]
    intro j
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRadiusTendsto) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hSmall : (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      have h := hN n hn
      simpa only [Real.dist_eq, sub_zero,
        abs_of_pos (hRadiusPos n)] using h
    calc
      dist (V n j) (U j) = dist (U j) (V n j) := dist_comm _ _
      _ = ‖U j - F n j‖ := by simp only [V, dist_eq_norm]
      _ < (1 : ℝ) / ((n : ℝ) + 1) := hF n j
      _ < ε := hSmall
  have hExact (n : ℕ) (j : Fin 3) :
      h3SpectralVelocityDecodeRealL2 (V n) j =
        (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3) := by
    change h3SpectralScalarDecodeRealL2 (F n j) = _
    exact hΨ n j
  have hPsiFun :
      (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3)) =
      (fun n : ℕ => h3SpectralVelocityDecodeRealL2 (V n)) := by
    funext n j
    exact (hExact n j).symm
  have hPhysical :
      Tendsto (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) := by
    rw [hPsiFun]
    exact h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244 hWeighted
  have hThird :=
    h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244
      hWeighted
  exact ⟨V, Ψ, hWeighted, hExact, hPhysical, hThird⟩

/-- On the actual encoded H³ velocity slice, the synchronized REAL Schwartz
approximants tend to the genuine physical velocity, while the cubic physical
jet reconstructions of their MATCHED weighted states tend to the 81 actual
old physical third derivatives. No separate approximation families remain. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzActualZeroThird244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℝ,
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ n : ℕ, ∀ j : Fin 3,
        h3SpectralVelocityDecodeRealL2 (V n) j =
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3)) ∧
      Tendsto (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
        atTop (𝓝 (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))) ∧
      Tendsto (fun n : ℕ =>
          h3SpectralVelocityThirdPhysicalJetFamily244 (V n))
        atTop (𝓝 (fun j : Fin 3 => fun a b c : A3 =>
          velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)
              (h3ClassicalizationFinOfAxis c)))) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨V, Ψ, hWeighted, hExact, hPhysical, hThird⟩ :=
    exists_h3SmoothCompactWeighted_realSchwartzAndThirdSequence244 U
  have hZeroEq :
      h3SpectralVelocityDecodeRealL2 U =
        (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j))) := by
    funext j
    exact h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
      hFourier j
  have hThirdEq :=
    h3SpectralVelocityThirdPhysicalJetFamily_actualJet244 hFourier
  refine ⟨V, Ψ, hWeighted, hExact, ?_, ?_⟩
  · rw [← hZeroEq]
    exact hPhysical
  · rw [← hThirdEq]
    exact hThird

end
end PrimeTensor.FirstMonomialTriad
