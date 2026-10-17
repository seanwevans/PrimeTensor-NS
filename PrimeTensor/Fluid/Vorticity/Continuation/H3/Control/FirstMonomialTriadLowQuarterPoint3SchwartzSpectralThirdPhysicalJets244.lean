import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPhysicalRealDensity244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Cubic.Velocity.Physical.L2.Continuity

/-!
# All 81 ordered third physical L² jets from actual spectral H³ convergence

The previous checkpoint constructed real physical Schwartz approximations in
zeroth-order L². The old spectral cubic multiplier theorems already control
EACH ordered third derivative component by the actual weighted H³ state.

This file assembles the 3 velocity components × 3³ ordered derivatives into
one continuous 81-coordinate physical L² state. Consequently, a SINGLE
sequence of genuinely weighted-spectral Schwartz approximants simultaneously
converges in weighted spectral H³, real-decoded velocity L², and the ENTIRE
canonical real third-order derivative L² jet family.

The cubic jets here are the project's existing inverse-Fourier / real-part /
physical-carrier reconstructions. Identification with the literal derivatives
of real physical Schwartz approximants and the actual E₂/E₃ integrals is a
separate obligation, as is preservation of incompressibility. No such
identification or unconditional Navier–Stokes regularity is claimed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeSpectralThirdPhysicalJets244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine inverse-Fourier-real-point3 reconstruction of all 81 cubic
velocity jets, indexed by velocity component and three ordered directions. -/
noncomputable def h3SpectralVelocityThirdPhysicalJetFamily244
    (U : H3SpectralVelocityState) :
    Fin 3 → A3 → A3 → A3 → H3ScalarL2 :=
  fun j a b c => h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c (U j)

@[simp]
theorem h3SpectralVelocityThirdPhysicalJetFamily_apply244
    (U : H3SpectralVelocityState) (j : Fin 3) (a b c : A3) :
    h3SpectralVelocityThirdPhysicalJetFamily244 U j a b c =
      h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c (U j) := rfl

/-- Every real physical cubic jet is quantitatively bounded by the
native weighted spectral H³ norm with the actual Fourier constant. -/
theorem norm_h3SpectralScalarRawThirdCoordinatePhysicalL2_le244
    (a b c : A3) (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c G‖ ≤
      (2 * Real.pi) ^ 3 * ‖G‖ := by
  unfold h3SpectralScalarRawThirdCoordinatePhysicalL2
  let T := (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
  change ‖h3FromFourierRealL2
      (h3RealPartFourierL2
        (T (h3SpectralScalarRawThirdCoordinateFourierL2 a b c G)))‖ ≤ _
  calc
    ‖h3FromFourierRealL2
      (h3RealPartFourierL2
        (T (h3SpectralScalarRawThirdCoordinateFourierL2 a b c G)))‖ =
        ‖h3RealPartFourierL2
          (T (h3SpectralScalarRawThirdCoordinateFourierL2 a b c G))‖ :=
      norm_h3FromFourierRealL2 _
    _ ≤ ‖T (h3SpectralScalarRawThirdCoordinateFourierL2 a b c G)‖ :=
      norm_h3RealPartFourierL2_le _
    _ = ‖h3SpectralScalarRawThirdCoordinateFourierL2 a b c G‖ :=
      T.norm_map _
    _ ≤ (2 * Real.pi) ^ 3 * ‖G‖ :=
      norm_h3SpectralScalarRawThirdCoordinateFourierL2_le a b c G

/-- The full 81-jet physical L² state is continuous in the weighted
spectral H³ topology, not only coordinatewise along a selected solution. -/
theorem continuous_h3SpectralVelocityThirdPhysicalJetFamily244 :
    Continuous h3SpectralVelocityThirdPhysicalJetFamily244 := by
  unfold h3SpectralVelocityThirdPhysicalJetFamily244
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  apply continuous_pi
  intro c
  exact
    (continuous_h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c).comp
      (continuous_apply j)

/-- Strong spectral H³ convergence implies strong convergence of all
81 real physical third jets as ONE product-Hilbert state. -/
theorem h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244
    {F : ℕ → H3SpectralVelocityState} {U : H3SpectralVelocityState}
    (hF : Tendsto F atTop (𝓝 U)) :
    Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244 (F n))
      atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 U)) := by
  exact
    continuous_h3SpectralVelocityThirdPhysicalJetFamily244.continuousAt.tendsto.comp hF

/-- ONE Schwartz-weighted approximation sequence simultaneously controls:
weighted spectral H³, all three real physical zero jets, and all 81 real
physical third jets. The complete cubic jet family is also Cauchy. -/
theorem exists_h3SchwartzSpectralApprox_realZeroAndAllThird244
    (U : H3SpectralVelocityState) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      Tendsto (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 U) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) ∧
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 U)) ∧
      CauchySeq (fun n => h3SpectralVelocityThirdPhysicalJetFamily244
        (h3SchwartzSpectralVelocityRealization244 (Φ n))) := by
  obtain ⟨Φ, hWeighted, hReal, _⟩ :=
    exists_h3SchwartzSpectralVelocityApprox_realDecodedSequence244 U
  have hThird :
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 U)) :=
    h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244 hWeighted
  exact ⟨Φ, hWeighted, hReal, hThird, hThird.cauchySeq⟩

/-- On an ACTUAL Fourier-compatible H³ physical time slice, the constructed
same spectral Schwartz sequence converges to the old physical zero-order
jet and to the complete canonical real cubic spectral-derivative jet family. -/
theorem exists_h3SchwartzSpectralApprox_actualZeroAndAllThird244
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
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))) ∧
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨Φ, hWeighted, hReal, hThird, _⟩ :=
    exists_h3SchwartzSpectralApprox_realZeroAndAllThird244 U
  have hZeroEq :
      h3SpectralVelocityDecodeRealL2 U =
        (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j))) := by
    funext j
    exact h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
      hFourier j
  refine ⟨Φ, hWeighted, ?_, hThird⟩
  rw [← hZeroEq]
  exact hReal

end
end PrimeTensor.FirstMonomialTriad
