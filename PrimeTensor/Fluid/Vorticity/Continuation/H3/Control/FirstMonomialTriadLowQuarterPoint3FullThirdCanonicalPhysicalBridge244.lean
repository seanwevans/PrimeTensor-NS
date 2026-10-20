import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientReferenceIndependence244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzPhysicalFirstJet244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientIntegrability244
import Mathlib.Tactic

/-!
# Canonical complete H³ transport and its physical decomposition

The previous checkpoints constructed two choice-independent real-valued
functionals on the *same* weighted spectral H³ Hilbert space:
* the full 972-term third-order 3–3–1 gradient completion;
* the signed 243-slot 3–2–2 interpolation completion.

The physical third transport splits, with its proven exact cyclic factor THREE,
into their two original Schwartz expressions. We construct the complete
canonical third-order commutator G₃ + 3M, prove its convergence for EVERY
fully matched Schwartz completion (without a new nonlinear limit premise),
and give a quantitative TWO-PROFILE modulus combining the 972 gradient and
243 interpolation errors, retaining both physical factors 2 and 3.

At an actual Fourier-compatible admissible preterminal slice, a single matched
family realizes this canonical full commutator and converges to the true
physical FIRST derivative at every spatial point. Finally we identify the
EXACT remaining physical transport discrepancy in terms of its gradient and
signed interpolation discrepancies. We do not assume either discrepancy is
zero: this is the remaining physical L² product identification problem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Slots5 := SchwartzStrongJetSlots244

noncomputable local instance axisFintypeCanonicalFullThird244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact complete signed 3rd-order commutator at arbitrary weighted H³
spectral velocity data. Both summands are already independent of the choice
of matching Schwartz approximants; the factor three is the proved cyclic
multiplicity in the physical interpolation sum. -/
noncomputable def weightedH3CanonicalFullThirdCommutator244
    (U : H3SpectralVelocityState) : ℝ :=
  weightedH3CanonicalGradientTransport244 U +
    3 * weightedH3CanonicalSignedFirstMonomial244 U

/-- The original matched gradient record has exactly the second/third-order
matching data demanded by the previously constructed signed completion. -/
noncomputable def h3MatchedGradientCompletion_toSignedCompletion244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U) :
    WeightedH3MatchedSchwartzCompletion244 U := {
  spectral := F.spectral
  family := F.family
  spectral_tendsto := F.spectral_tendsto
  second_exact := F.second_exact
  third_exact := F.third_exact
}

/-- Every derivative- and decoder-matched Schwartz completion has the SAME
full 3rd-order transport limit. No third-derivative L⁴ premise, separate
gradient convergence assumption, or physical nonlinear identity is added. -/
theorem h3MatchedSchwartzGradientCompletion_fullThird_tendsto244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U) :
    Tendsto
      (fun n => fullSchwartzThirdCommutator244 (F.family.approximants n))
      atTop (𝓝 (weightedH3CanonicalFullThirdCommutator244 U)) := by
  have hGradient := weightedH3CanonicalGradientTransport_tendsto244 U F
  have hSigned := weightedH3CanonicalSignedFirstMonomial_tendsto244 U
    (h3MatchedGradientCompletion_toSignedCompletion244 U F)
  -- The adapter retains the original family definitionally.  Expose this
  -- projection equality before multiplying its scalar limit by three.
  change Tendsto
    (fun n => lowNormalRealSchwartzPoint3Monomial (F.family.approximants n))
    atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U)) at hSigned
  have hThree :
      Tendsto (fun n => 3 * lowNormalRealSchwartzPoint3Monomial
        (F.family.approximants n)) atTop
        (𝓝 (3 * weightedH3CanonicalSignedFirstMonomial244 U)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ))
        atTop (𝓝 (3 : ℝ))).mul hSigned
  simpa only [fullSchwartzThirdCommutator244,
    weightedH3CanonicalFullThirdCommutator244] using hGradient.add hThree

/-- The complete third-order limit is independent of either Schwartz
reference family; this is a nonlinear statement about the entire physical
G₃ + 3M combination, not a definition of the limit through one family. -/
theorem h3MatchedSchwartzGradientCompletion_fullThird_unique244
    (U : H3SpectralVelocityState)
    (F G : H3MatchedSchwartzGradientCompletion244 U)
    (LF LG : ℝ)
    (hF : Tendsto (fun n => fullSchwartzThirdCommutator244
      (F.family.approximants n)) atTop (𝓝 LF))
    (hG : Tendsto (fun n => fullSchwartzThirdCommutator244
      (G.family.approximants n)) atTop (𝓝 LG)) :
    LF = LG := by
  have hFEq : LF = weightedH3CanonicalFullThirdCommutator244 U :=
    tendsto_nhds_unique hF
      (h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U F)
  have hGEq : LG = weightedH3CanonicalFullThirdCommutator244 U :=
    tendsto_nhds_unique hG
      (h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U G)
  exact hFEq.trans hGEq.symm

/-- An explicit TWO-PROFILE quantitative perturbation envelope for the FULL
third-order signed transport. Its first summand contains the 972 genuine
3–3–1 errors; its second contains all 243 signed 3–2–2 errors, with the exact
physical multiplier 3 * 2 = 6. -/
noncomputable def fullSchwartzThirdSpectralPairEnvelope244
    (f g : A3 → SchwartzMap V3 ℝ)
    (U W : H3SpectralVelocityState) : ℝ :=
  fullSchwartzGradientSpectralPairEnvelope244 f g U W +
    6 * (∑ p : Slots5, schwartzPhysicalSlotPerturbation244 f g p)

/-- Nonlinear two-profile stability of the FULL physical-order third
commutator, including the signed 243-slot interpolation, on any TWO exact
pointwise decoder-matched real Schwartz velocities. -/
theorem fullSchwartzThirdCommutator_spectralPair_modulus244
    (f g : A3 → SchwartzMap V3 ℝ)
    (U W : H3SpectralVelocityState)
    (hf : ∀ j : A3,
      h3SchwartzPoint3Scalar (f j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (U (h3ClassicalizationFinOfAxis j)))
    (hg : ∀ j : A3,
      h3SchwartzPoint3Scalar (g j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W (h3ClassicalizationFinOfAxis j))) :
    |fullSchwartzThirdCommutator244 f -
        fullSchwartzThirdCommutator244 g| ≤
      fullSchwartzThirdSpectralPairEnvelope244 f g U W := by
  have hG := fullSchwartzGradientTransport_spectralPair_modulus244
    f g U W hf hg
  have hM := lowNormalRealSchwartz_fullMonomial_integratedStability244 f g
  have hThree :
      3 * |lowNormalRealSchwartzPoint3Monomial f -
          lowNormalRealSchwartzPoint3Monomial g| ≤
      6 * (∑ p : Slots5, schwartzPhysicalSlotPerturbation244 f g p) := by
    dsimp only [Slots5] at hM ⊢
    linarith only [hM]
  have hRewrite :
      fullSchwartzThirdCommutator244 f -
        fullSchwartzThirdCommutator244 g =
      (fullSchwartzGradientTransport244 f -
        fullSchwartzGradientTransport244 g) +
      3 * (lowNormalRealSchwartzPoint3Monomial f -
        lowNormalRealSchwartzPoint3Monomial g) := by
    unfold fullSchwartzThirdCommutator244
    ring
  rw [hRewrite]
  calc
    |(fullSchwartzGradientTransport244 f -
        fullSchwartzGradientTransport244 g) +
      3 * (lowNormalRealSchwartzPoint3Monomial f -
        lowNormalRealSchwartzPoint3Monomial g)| ≤
      |fullSchwartzGradientTransport244 f -
        fullSchwartzGradientTransport244 g| +
      |3 * (lowNormalRealSchwartzPoint3Monomial f -
        lowNormalRealSchwartzPoint3Monomial g)| := abs_add_le _ _
    _ = |fullSchwartzGradientTransport244 f -
        fullSchwartzGradientTransport244 g| +
      3 * |lowNormalRealSchwartzPoint3Monomial f -
        lowNormalRealSchwartzPoint3Monomial g| := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
    _ ≤ fullSchwartzGradientSpectralPairEnvelope244 f g U W +
        6 * (∑ p : Slots5, schwartzPhysicalSlotPerturbation244 f g p) :=
      add_le_add hG hThree
    _ = fullSchwartzThirdSpectralPairEnvelope244 f g U W := rfl

/-- One genuine real Schwartz family simultaneously approximates weighted
H³ spectral data and the complete choice-independent top commutator. -/
theorem exists_weightedH3Matched_fullThirdApproximation244
    (U : H3SpectralVelocityState) :
    ∃ F : H3MatchedSchwartzGradientCompletion244 U,
      Tendsto (fun n => fullSchwartzThirdCommutator244
        (F.family.approximants n)) atTop
        (𝓝 (weightedH3CanonicalFullThirdCommutator244 U)) := by
  let F : H3MatchedSchwartzGradientCompletion244 U :=
    Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U)
  exact ⟨F, h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U F⟩

/-- The completed full top commutator at a genuine physical Fourier-compatible
H³ velocity snapshot. This is a CANONICAL SPECTRAL observable and is not yet
claimed equal to the preexisting physical PDE pairing. -/
noncomputable def h3PhysicalSnapshotCanonicalFullThird244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) : ℝ :=
  weightedH3CanonicalFullThirdCommutator244
    (velocityH3SpectralStateAt u t hInt hMeas hFourier)

/-- At an ACTUAL admissible Fourier-compatible Navier–Stokes slice, ONE
fully matched Schwartz family (a) converges to the canonical complete top
commutator, (b) converges in spectral weighted H³, and (c) has literal
first-coordinate derivatives converging to the OLD physical gradient at
EVERY spatial point. No equality with the physical cubic is presumed. -/
theorem exists_physicalSnapshot_matchedFullThirdAndFirstJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      Tendsto (fun n => fullSchwartzThirdCommutator244 (f n)) atTop
        (𝓝 (h3PhysicalSnapshotCanonicalFullThird244 u t hFourier)) ∧
      (∀ j i : A3, ∀ x : V3,
        Tendsto (fun n => (∂_{h3FourierAxisDirection i} (f n j)) x)
          atTop (𝓝 (spatial3.d i
            (loggedVelocityComponent u t j)
            ((WithLp.ofLp : V3 → Point3) x)))) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  let F : H3MatchedSchwartzGradientCompletion244 U :=
    Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U)
  have hFull :
      Tendsto (fun n => fullSchwartzThirdCommutator244
        (F.family.approximants n)) atTop
        (𝓝 (h3PhysicalSnapshotCanonicalFullThird244 u t hFourier)) := by
    simpa only [h3PhysicalSnapshotCanonicalFullThird244, U] using
      h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U F
  refine ⟨F.spectral, F.family.approximants,
    F.spectral_tendsto, hFull, ?_⟩
  intro j i x
  let jj : Fin 3 := h3ClassicalizationFinOfAxis j
  have hCoord : Tendsto (fun n => F.spectral n jj) atTop (𝓝 (U jj)) :=
    (tendsto_pi_nhds.mp F.spectral_tendsto) jj
  have hNorm : Tendsto (fun n => ‖F.spectral n jj - U jj‖)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hCoord
  have hMatch (n : ℕ) :
      h3SchwartzPoint3Scalar (F.family.approximants n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (F.spectral n jj) := by
    exact F.zero_exact n j
  have hPhysical :
      h3SpectralScalarRealC1RepresentativeOnPoint3 (U jj) =
        loggedVelocityComponent u t j := by
    have h :=
      h3SpectralScalarRealC1RepresentativeOnPoint3_velocityH3SpectralScalarAt_eq_loggedVelocityComponent
        hNS ht hFourier jj
    simpa only [U, velocityH3SpectralStateAt, jj,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis] using h
  have hJet := thirdFullSchwartz_matchedFirstJet_tendsto_canonical244
    (fun n => F.spectral n jj) (U jj)
    (fun n => F.family.approximants n j)
    hMatch hNorm i x
  rw [hPhysical] at hJet
  exact hJet

/-- The PRECISE physical pairing discrepancy is the sum of two analytic
identification gaps: the 3–3–1 gradient gap and THREE times the signed 3–2–2
interpolation gap. This identity is unconditional under the existing H³
physical decomposition; it exposes rather than assumes the two missing
nonlinear trace identifications. -/
theorem physicalFullThird_minus_canonical_eq_gradient_and_signed_gaps244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3TransportDerivative3At u t -
        h3PhysicalSnapshotCanonicalFullThird244 u t hFourier =
      (thirdOrderGradientTransportSum u t -
        weightedH3CanonicalGradientTransport244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)) +
      3 * (h3PathCanonicalFirstMonomialAggregateAt u t -
        weightedH3CanonicalSignedFirstMonomial244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)) := by
  rw [h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht]
  rw [h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
    hH3 hClass ht]
  unfold h3PhysicalSnapshotCanonicalFullThird244
    weightedH3CanonicalFullThirdCommutator244
  ring

/-- An immediate *quantitative* physical-trace error bound. The completed
third-order transport matches the old PDE pairing once BOTH explicit
component discrepancies vanish, with no new hidden multiplier. -/
theorem physicalFullThird_canonical_error_le_component_errors244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    |velocityH3TransportDerivative3At u t -
        h3PhysicalSnapshotCanonicalFullThird244 u t hFourier| ≤
      |thirdOrderGradientTransportSum u t -
        weightedH3CanonicalGradientTransport244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)| +
      3 * |h3PathCanonicalFirstMonomialAggregateAt u t -
        weightedH3CanonicalSignedFirstMonomial244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)| := by
  rw [physicalFullThird_minus_canonical_eq_gradient_and_signed_gaps244
    hH3 hClass ht hFourier]
  calc
    |(thirdOrderGradientTransportSum u t -
        weightedH3CanonicalGradientTransport244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)) +
      3 * (h3PathCanonicalFirstMonomialAggregateAt u t -
        weightedH3CanonicalSignedFirstMonomial244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))| ≤
      |thirdOrderGradientTransportSum u t -
        weightedH3CanonicalGradientTransport244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)| +
      |3 * (h3PathCanonicalFirstMonomialAggregateAt u t -
        weightedH3CanonicalSignedFirstMonomial244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))| :=
      abs_add_le _ _
    _ = _ := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]

end
end PrimeTensor.FirstMonomialTriad
