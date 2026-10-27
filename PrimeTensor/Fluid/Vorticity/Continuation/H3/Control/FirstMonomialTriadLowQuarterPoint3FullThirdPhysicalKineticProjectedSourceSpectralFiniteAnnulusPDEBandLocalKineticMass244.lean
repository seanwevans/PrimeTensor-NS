import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalKineticBandwidth244
import Mathlib.Tactic

/-!
# Actual annular H³ dissipation versus Fourier-local kinetic mass

The old kinetic bandwidth argument bounded a first-crossing annulus using
*global* kinetic energy. Here the raw Fourier square density is restricted to
exactly the same measurable annulus as the dissipative density, and the
pointwise H³ Sobolev reweighting estimate is integrated *on that band*.
No artificial nonzero lower bound for Fourier L² mass is imposed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeBandKinetic244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBandKinetic244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Raw (unweighted) kinetic Fourier square mass on the literal annular band.
It is a physical Fourier object for actual strict-time velocity states. -/
noncomputable def h3PathActualBandRawKineticMass244
    (R Q : ℝ) (G : H3SpectralVelocityState) : ℝ :=
  ∫ ξ in (h3TerminalRadialFrequencyBelow Q \
      h3TerminalRadialFrequencyBelow R),
    h3TerminalRawVelocityFourierTotalSquareDensity G 0 ξ ∂volume

/-- Exact annular identity for the physical H³ dissipation. It is essential
that the inner Fourier ball is included in the outer one. -/
theorem h3Path_actualAnnularDissipation_eq_bandIntegral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (R Q : ℝ) (hRQ : R ≤ Q) :
    h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) =
      ∫ ξ in (h3TerminalRadialFrequencyBelow Q \
          h3TerminalRadialFrequencyBelow R),
        h3TerminalSpectralDissipationSingleDensity
          (h3AuditActualSpectralVelocityTotal hH3 t) ξ ∂volume := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow Q
  let V : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow R
  have hVS : V ⊆ S := by
    intro ξ hξ
    change h3FourierGradientMagnitude ξ < R at hξ
    change h3FourierGradientMagnitude ξ < Q
    exact lt_of_lt_of_le hξ hRQ
  have hVMeas : MeasurableSet V :=
    measurableSet_h3TerminalRadialFrequencyBelow R
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hDInt : Integrable (h3TerminalSpectralDissipationSingleDensity G)
      volume := by
    dsimp only [G]
    rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
    exact h3TerminalSpectralDissipationSingleDensity_integrable
      hH3 hClass ht
  have hSub := setIntegral_sdiff hVMeas
    (hDInt.mono_measure Measure.restrict_le_self) hVS
  dsimp only [h3PathActualLowRadialDissipation244, G, S, V] at hSub ⊢
  exact hSub.symm

/-- The band-local quadratic Fourier multiplier costs no more than the
actual outer radius squared times its Sobolev weight ceiling. The RHS
integrates *raw kinetic density on the same annulus*, not over all ξ. -/
theorem h3Path_actualBandDissipation_le_bandRawKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (R Q : ℝ) (hQ : 0 ≤ Q) :
    (∫ ξ in (h3TerminalRadialFrequencyBelow Q \
        h3TerminalRadialFrequencyBelow R),
      h3TerminalSpectralDissipationSingleDensity
        (h3AuditActualSpectralVelocityTotal hH3 t) ξ ∂volume) ≤
      (Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q) *
        h3PathActualBandRawKineticMass244 R Q
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow Q
  let V : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow R
  let A : Set H3FourierPoint3 := S \ V
  let d : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity G
  let f : H3FourierPoint3 → ℝ :=
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G 0
  let g : H3FourierPoint3 → ℝ :=
    h3TerminalRawVelocityFourierTotalSquareDensity G 0
  let W : ℝ := h3TerminalRadialSobolevWeightSquareCeiling Q
  have hSMeas : MeasurableSet S :=
    measurableSet_h3TerminalRadialFrequencyBelow Q
  have hAMeas : MeasurableSet A :=
    MeasurableSet.diff hSMeas
      (measurableSet_h3TerminalRadialFrequencyBelow R)
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hdInt : Integrable d volume := by
    dsimp only [d, G]
    rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
    exact h3TerminalSpectralDissipationSingleDensity_integrable
      hH3 hClass ht
  have hgInt : Integrable g volume := by
    dsimp only [g]
    exact rawVelocityFourierTotalSquareDensity_integrable G 0
  have hWPoint : ∀ᵐ ξ : H3FourierPoint3 ∂volume,
      ξ ∈ S → f ξ ≤ W * g ξ := by
    rw [← ae_restrict_iff' hSMeas]
    dsimp only [S, f, g, W]
    exact weightedSpectralVelocityTotalSquareDifferenceDensity_le_radialCeiling_mul_raw_ae
      hQ G 0
  have hPoint : ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict A),
      d ξ ≤ (Q ^ 2 * W) * g ξ := by
    rw [ae_restrict_iff' hAMeas]
    filter_upwards [hWPoint] with ξ hξ
    intro hx
    have hD : d ξ ≤ Q ^ 2 *
        h3TerminalSpectralStateSquareAmplitude G ξ := by
      dsimp only [d]
      exact h3Path_lowRadialDissipationDensity_le_squareEnergy244
        G hQ hx.1
    have hEq : h3TerminalSpectralStateSquareAmplitude G ξ = f ξ := by
      exact (h3Path_actualSpectralDifferenceFromZero_density_eq244 G ξ).symm
    have hW : f ξ ≤ W * g ξ := hξ hx.1
    have hMul := mul_le_mul_of_nonneg_left hW (sq_nonneg Q)
    rw [hEq] at hD
    dsimp only [W, f, g] at *
    nlinarith only [hD, hMul]
  have hScaledInt : Integrable (fun ξ => (Q ^ 2 * W) * g ξ)
      volume := hgInt.const_mul _
  have hMono := integral_mono_ae
    (hdInt.mono_measure Measure.restrict_le_self)
    (hScaledInt.mono_measure Measure.restrict_le_self)
    hPoint
  change (∫ ξ in A, d ξ ∂volume) ≤
    ∫ ξ in A, (Q ^ 2 * W) * g ξ ∂volume at hMono
  rw [integral_const_mul] at hMono
  simpa only [A, S, V, d, G, W, g,
    h3PathActualBandRawKineticMass244] using hMono

/-- The genuine finite physical annulus is paid for by its own raw Fourier
L² mass, rather than just a uniform global kinetic-energy ceiling. -/
theorem h3Path_actualAnnularDissipation_le_bandRawKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (R Q : ℝ) (hRQ : R ≤ Q) (hQ : 0 ≤ Q) :
    h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      (Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q) *
        h3PathActualBandRawKineticMass244 R Q
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  rw [h3Path_actualAnnularDissipation_eq_bandIntegral244
    hH3 hClass t ht R Q hRQ]
  exact h3Path_actualBandDissipation_le_bandRawKinetic244
    hH3 hClass t ht R Q hQ

/-- A genuine first crossing requires an explicitly positive amount of raw
kinetic Fourier mass *within that very first-crossing annulus*. -/
theorem h3Path_firstCrossing_forces_bandKineticMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N : ℕ) (hnN : n ≤ N)
    (hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    3 * (((n : ℝ) + 1) ^ 3) <
      16 * (((N : ℝ) + 2) ^ 8) *
        h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hRQ : R ≤ Q := by
    have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    dsimp only [R, Q]
    linarith only [hnR]
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hBand : 0 ≤ h3PathActualBandRawKineticMass244 R Q G := by
    unfold h3PathActualBandRawKineticMass244
    apply integral_nonneg
    intro ξ
    unfold h3TerminalRawVelocityFourierTotalSquareDensity
    positivity
  have hRBound := h3Path_actualAnnularDissipation_le_bandRawKinetic244
    hH3 hClass t ht R Q hRQ hQ
  have hProduct : Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q ≤
      4 * (Q + 1) ^ 8 := by
    have hQ2 : Q ^ 2 ≤ (Q + 1) ^ 2 := by
      nlinarith only [hQ]
    have hW := h3Path_radialSobolevCeiling_le_fourShiftSixth244 Q hQ
    have hPos := (h3TerminalRadialSobolevWeightSquareCeiling_pos Q).le
    calc
      _ ≤ (Q + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q :=
        mul_le_mul_of_nonneg_right hQ2 hPos
      _ ≤ (Q + 1) ^ 2 * (4 * (Q + 1) ^ 6) :=
        mul_le_mul_of_nonneg_left hW (sq_nonneg _)
      _ = 4 * (Q + 1) ^ 8 := by ring
  have hScaled :
      (Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q) *
          h3PathActualBandRawKineticMass244 R Q G ≤
      (4 * (Q + 1) ^ 8) * h3PathActualBandRawKineticMass244 R Q G :=
    mul_le_mul_of_nonneg_right hProduct hBand
  have hCross' : 3 * R ^ 3 / 4 <
      h3PathActualLowRadialDissipation244 Q G -
        h3PathActualLowRadialDissipation244 R G := by
    simpa only [R, Q, G] using hCross
  have hLower : 3 * R ^ 3 / 4 <
      4 * (Q + 1) ^ 8 * h3PathActualBandRawKineticMass244 R Q G := by
    linarith only [hCross', hRBound, hScaled]
  dsimp only [R, Q, G] at hLower ⊢
  nlinarith only [hLower]

/-- Physical no-strong-terminal-L²-trace first-crossing witnesses have
band-local kinetic mass cost, without replacing it by the total energy. -/
theorem h3Path_noL2Trace_minimalFirstCrossing_bandKineticCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ),
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, n ≤ N n ∧
        ∀ m : ℕ, n ≤ m → m < N n →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
              3 * (((n : ℝ) + 1) ^ 3) / 4) ∧
      (∀ n : ℕ,
        3 * (((n : ℝ) + 1) ^ 3) <
          16 * (((N n : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n))) := by
  obtain ⟨τ, N, K, C, δ, hτ, hLimit, hAll⟩ :=
    h3Path_noL2Trace_minimalQuadraticSharpClocks_retain_quarterHighTail244
      hH3 hClass hMass hNoTrace
  refine ⟨τ, N, hLimit, ?_, ?_⟩
  · intro n
    rcases hAll n with ⟨hnN, _, _, _, _, _, _, _, hMinimal, _⟩
    exact ⟨hnN, hMinimal⟩
  · intro n
    rcases hAll n with ⟨hnN, _, _, _, _, _, _, hGap, _, _⟩
    have hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
        h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) := by
      dsimp only [h3PathCubicAnnulusActualGap244] at hGap
      linarith only [hGap]
    exact h3Path_firstCrossing_forces_bandKineticMass244
      hH3 hClass (τ n) (hτ n) n (N n) hnN hCross

end
end PrimeTensor.FirstMonomialTriad
