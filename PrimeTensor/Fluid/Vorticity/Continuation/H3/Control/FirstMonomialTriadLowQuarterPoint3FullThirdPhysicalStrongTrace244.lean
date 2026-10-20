import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalPhysicalBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzActualThirdJetIdentification244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedSecondFamily244
import Mathlib.Tactic

/-!
# Strong physical H³ jet traces for every canonical full-third Schwartz completion

The canonical 3–3–1 gradient and signed 3–2–2 completions were constructed
from synchronized real Schwartz fields and proved independent of their chosen
matched families. Their resulting full-third commutator was *not* yet equated
to the independently defined physical Navier–Stokes transport pairing.

Here the original physical Fourier-compatibility theorems are used to close a
strong, rather than merely pointwise, portion of the physical trace bridge.
For EVERY admissible matched Schwartz completion of a genuine H³ snapshot:

* all 27 literal real Schwartz second derivatives, pushed to physical Point3
  L² by the actual volume-preserving carrier isometry, converge jointly to
  the ORIGINAL 27 old physical second-order H³ jet classes;
* all 81 literal real Schwartz third derivatives converge jointly in the
  same physical Hilbert topology to the ORIGINAL 81 third-order H³ jets;
* the real Schwartz first derivatives have a uniform spatial error gauge
  bounded by C₁ times the native weighted H³ spectral difference;
* the full 972+243 signed commutator converges to the already constructed
  choice-independent canonical full-third scalar.

This is actual physical L² jet identification. Identifying the canonical
second-jet L⁴ classes with the literal physical L⁴ derivatives, and passing
the L²×L⁴×L⁴ and L²×L²×L∞ products to the old physical integral, are still
separate analytical tasks. No such nonlinear pairing identification is
assumed or asserted below.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

-- The Euclidean carrier is a finite product.  Its normed, volume and
-- Schwartz-map instances require a concrete finite axis index type.
noncomputable local instance axisFintypePhysicalStrongTrace244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- All 27 *literal* second-order Schwartz derivatives as physical L²
states, using the actual Point3/Fourier-carrier measure-preserving map. -/
noncomputable def h3MatchedSchwartzPhysicalSecondJetState244
    {U : H3SpectralVelocityState}
    (F : H3MatchedSchwartzGradientCompletion244 U) (n : ℕ) :
    Fin 3 → A3 → A3 → H3ScalarL2 :=
  fun j a b => h3FromFourierRealL2
    ((∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (F.family.approximants n (h3AxisOfFin3 j)))).toLp
          2 (volume : Measure V3))

/-- All 81 *literal* third-order Schwartz derivatives in the original
physical H³ jet Hilbert carrier, with no third-jet L⁴ premise. -/
noncomputable def h3MatchedSchwartzPhysicalThirdJetState244
    {U : H3SpectralVelocityState}
    (F : H3MatchedSchwartzGradientCompletion244 U) (n : ℕ) :
    Fin 3 → A3 → A3 → A3 → H3ScalarL2 :=
  fun j a b c => h3FromFourierRealL2
    ((∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c}
          (F.family.approximants n (h3AxisOfFin3 j))))).toLp
            2 (volume : Measure V3))

/-- The actual 27-coordinate old physical second-jet family is the strong
limit of the LITERAL derivatives of ANY fully matched Schwartz completion. -/
theorem h3MatchedSchwartzPhysicalSecondJetState_tendsto_actual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    Tendsto (fun n => h3MatchedSchwartzPhysicalSecondJetState244 F n)
      atTop (𝓝 (fun j : Fin 3 => fun a b : A3 =>
        velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)))) := by
  have hExact (n : ℕ) :
      h3MatchedSchwartzPhysicalSecondJetState244 F n =
        h3SpectralVelocitySecondPhysicalJetFamily244 (F.spectral n) := by
    funext j a b
    have hEq := congrArg h3FromFourierRealL2
      (F.second_exact n (h3AxisOfFin3 j) a b)
    simpa only [h3MatchedSchwartzPhysicalSecondJetState244,
      matchedSpectralSecondFourierJets244,
      h3ClassicalizationFinOfAxis_h3AxisOfFin3,
      h3FromFourierRealL2_h3ToFourierRealL2] using hEq
  have hSequence :
      (fun n => h3MatchedSchwartzPhysicalSecondJetState244 F n) =
        (fun n => h3SpectralVelocitySecondPhysicalJetFamily244 (F.spectral n)) := by
    funext n
    exact hExact n
  rw [hSequence]
  rw [← h3SpectralVelocitySecondPhysicalJetFamily_actualJet244 hFourier]
  exact h3SpectralVelocitySecondPhysicalJetFamily_tendsto_of_weighted244
    F.spectral_tendsto

/-- The actual 81-coordinate old physical third-jet family is the strong
limit of the LITERAL derivatives of ANY fully matched Schwartz completion. -/
theorem h3MatchedSchwartzPhysicalThirdJetState_tendsto_actual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    Tendsto (fun n => h3MatchedSchwartzPhysicalThirdJetState244 F n)
      atTop (𝓝 (fun j : Fin 3 => fun a b c : A3 =>
        velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)
            (h3ClassicalizationFinOfAxis c)))) := by
  have hExact (n : ℕ) :
      h3MatchedSchwartzPhysicalThirdJetState244 F n =
        h3SpectralVelocityThirdPhysicalJetFamily244 (F.spectral n) := by
    funext j a b c
    have hEq := congrArg h3FromFourierRealL2
      (F.third_exact n (h3AxisOfFin3 j) a b c)
    simpa only [h3MatchedSchwartzPhysicalThirdJetState244,
      matchedSpectralThirdFourierJets244,
      h3ClassicalizationFinOfAxis_h3AxisOfFin3,
      h3FromFourierRealL2_h3ToFourierRealL2] using hEq
  have hSequence :
      (fun n => h3MatchedSchwartzPhysicalThirdJetState244 F n) =
        (fun n => h3SpectralVelocityThirdPhysicalJetFamily244 (F.spectral n)) := by
    funext n
    exact hExact n
  rw [hSequence]
  rw [← h3SpectralVelocityThirdPhysicalJetFamily_actualJet244 hFourier]
  exact h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244
    F.spectral_tendsto

/-- For any matched gradient completion of an actual preterminal slice,
its actual first Schwartz derivatives differ from the physical velocity
gradient by a single uniformly spatial H³ error gauge tending to zero. -/
theorem h3MatchedSchwartz_physicalFirstJetGauge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    (∀ j : Fin 3,
      Tendsto (fun n =>
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖F.spectral n j -
            velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖)
        atTop (𝓝 0)) ∧
    (∀ n : ℕ, ∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
      |(∂_{h3FourierAxisDirection i}
          (F.family.approximants n (h3AxisOfFin3 j))) x -
        spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
          ((WithLp.ofLp : V3 → Point3) x)| ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖F.spectral n j -
            velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖) := by
  constructor
  · intro j
    have hCoord := (tendsto_pi_nhds.mp F.spectral_tendsto) j
    have hNorm : Tendsto (fun n =>
        ‖F.spectral n j -
          velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖)
        atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hCoord
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient)
          atTop (𝓝 h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient)).mul
        hNorm
  · intro n j i x
    have hMatch (q : Fin 3) :
        h3SchwartzPoint3Scalar
          (F.family.approximants n (h3AxisOfFin3 q)) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (F.spectral n q) := by
      simpa only [h3ClassicalizationFinOfAxis_h3AxisOfFin3] using
        F.zero_exact n (h3AxisOfFin3 q)
    exact thirdFullSchwartz_physicalFirstJetError_le_spectral244
      hNS ht hFourier (F.spectral n)
      (fun q => F.family.approximants n (h3AxisOfFin3 q))
      hMatch j i x

/-- ONE matched family has the complete physical 27+81 strong L² traces,
a vanishing uniform physical first-jet gauge, and the canonical full
signed top commutator limit. All limits are attached to the SAME family. -/
theorem h3MatchedSchwartz_physicalStrongTraceAndFullThird244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    Tendsto (fun n => h3MatchedSchwartzPhysicalSecondJetState244 F n)
      atTop (𝓝 (fun j : Fin 3 => fun a b : A3 =>
        velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)))) ∧
    Tendsto (fun n => h3MatchedSchwartzPhysicalThirdJetState244 F n)
      atTop (𝓝 (fun j : Fin 3 => fun a b c : A3 =>
        velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)
            (h3ClassicalizationFinOfAxis c)))) ∧
    (∀ j : Fin 3,
      Tendsto (fun n =>
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖F.spectral n j -
            velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖)
        atTop (𝓝 0)) ∧
    (∀ n : ℕ, ∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
      |(∂_{h3FourierAxisDirection i}
          (F.family.approximants n (h3AxisOfFin3 j))) x -
        spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
          ((WithLp.ofLp : V3 → Point3) x)| ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖F.spectral n j -
            velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖) ∧
    Tendsto (fun n => fullSchwartzThirdCommutator244 (F.family.approximants n))
      atTop (𝓝 (h3PhysicalSnapshotCanonicalFullThird244 u t hFourier)) := by
  obtain ⟨hFirstGauge, hFirstBound⟩ :=
    h3MatchedSchwartz_physicalFirstJetGauge244 hNS ht hFourier F
  exact ⟨h3MatchedSchwartzPhysicalSecondJetState_tendsto_actual244 hFourier F,
    h3MatchedSchwartzPhysicalThirdJetState_tendsto_actual244 hFourier F,
    hFirstGauge, hFirstBound,
    h3MatchedSchwartzGradientCompletion_fullThird_tendsto244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) F⟩

/-- The full physical strong-jet trace and full-third completion are
simultaneously realized for every admissible Fourier-compatible H³ slice,
without postulating the nonlinear physical trilinear limit. -/
theorem exists_physicalSnapshot_matchedFullThirdAndStrongJets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ F : H3MatchedSchwartzGradientCompletion244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier),
      Tendsto (fun n => h3MatchedSchwartzPhysicalSecondJetState244 F n)
        atTop (𝓝 (fun j : Fin 3 => fun a b : A3 =>
          velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)))) ∧
      Tendsto (fun n => h3MatchedSchwartzPhysicalThirdJetState244 F n)
        atTop (𝓝 (fun j : Fin 3 => fun a b c : A3 =>
          velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)
              (h3ClassicalizationFinOfAxis c)))) ∧
      (∀ j : Fin 3, Tendsto (fun n =>
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖F.spectral n j -
            velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖)
          atTop (𝓝 0)) ∧
      (∀ n : ℕ, ∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
        |(∂_{h3FourierAxisDirection i}
            (F.family.approximants n (h3AxisOfFin3 j))) x -
          spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
            ((WithLp.ofLp : V3 → Point3) x)| ≤
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            ‖F.spectral n j -
              velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖) ∧
      Tendsto (fun n => fullSchwartzThirdCommutator244 (F.family.approximants n))
        atTop (𝓝 (h3PhysicalSnapshotCanonicalFullThird244 u t hFourier)) := by
  let F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) :=
    Classical.choice (exists_h3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
  exact ⟨F, h3MatchedSchwartz_physicalStrongTraceAndFullThird244
    hNS ht hFourier F⟩

end
end PrimeTensor.FirstMonomialTriad
