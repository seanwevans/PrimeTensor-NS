import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceSpectralTemporalGap244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure
import Mathlib.Tactic

/-!
# Physical inverse-Fourier source differences from actual weighted H³ state differences

The preceding source module proves an exact diagonal difference formula and a
576 π C₃ Lipschitz bound for the raw Leray Fourier L² class. This module
transports the difference itself through the genuine inverse Fourier
transform, real-part projection and volume-preserving physical L² carrier.
It also transports the linear raw spectral Laplacian difference. The resulting
physical estimate, with precisely the previously calibrated C_L, is

  ‖(D(U)-L(U))-(D(V)-L(V))‖ ≤
    (3+C_L*(‖U‖+‖V‖))*‖U-V‖.

No time-regularity assumption is introduced. A final theorem applies it to
canonical source-maximizers and their actual quadratic-sharp PDE anchors,
retaining the same disjoint finite-dissipation window sequence and the
conditional critical-width spectral-displacement alternative. In particular,
this does NOT bound the spectral increments using finite H³ dissipation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCanonicalSourcePhysicalDifference244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCanonicalSourcePhysicalDifference244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The physical inverse-Fourier real carrier is a linear transport; unlike
an estimate for individual norms, subtraction is preserved exactly. -/
theorem h3Path_fromFourierRealL2_sub244
    (f g : H3FourierRealL2) :
    h3FromFourierRealL2 (f - g) =
      h3FromFourierRealL2 f - h3FromFourierRealL2 g := by
  unfold h3FromFourierRealL2
  exact
    (MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three))).map_sub f g

/-- Real-part projection on the genuine Fourier L² class is real-linear. -/
theorem h3Path_realPartFourierL2_sub244
    (f g : H3FourierComplexL2) :
    h3RealPartFourierL2 (f - g) =
      h3RealPartFourierL2 f - h3RealPartFourierL2 g := by
  simpa only [sub_eq_add_neg, h3RealPartFourierL2_add,
    h3RealPartFourierL2_neg]

/-- The exact physical inverse-Fourier decoder, once and for all. -/
noncomputable def h3Path_physicalRawFourierDecoder244
    (f : H3FourierComplexL2) : H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f))

/-- Decode the *difference*, not the two individual norms independently. -/
theorem h3Path_physicalRawFourierDecoder_sub244
    (f g : H3FourierComplexL2) :
    h3Path_physicalRawFourierDecoder244 (f - g) =
      h3Path_physicalRawFourierDecoder244 f -
        h3Path_physicalRawFourierDecoder244 g := by
  unfold h3Path_physicalRawFourierDecoder244
  rw [(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.map_sub]
  rw [h3Path_realPartFourierL2_sub244]
  exact h3Path_fromFourierRealL2_sub244 _ _

/-- Plancherel plus real-part contraction makes the decoded physical L²
norm at most the original complex Fourier L² norm. -/
theorem h3Path_physicalRawFourierDecoder_norm_le244
    (f : H3FourierComplexL2) :
    ‖h3Path_physicalRawFourierDecoder244 f‖ ≤ ‖f‖ := by
  unfold h3Path_physicalRawFourierDecoder244
  calc
    ‖h3FromFourierRealL2
      (h3RealPartFourierL2
        ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f))‖ =
        ‖h3RealPartFourierL2
          ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f)‖ :=
        norm_h3FromFourierRealL2 _
    _ ≤ ‖(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f‖ :=
      norm_h3RealPartFourierL2_le _
    _ = ‖f‖ := norm_fourierInv_h3FourierComplexL2 _

/-- The same old physical inverse-Fourier Leray forcing has a quantitative
locally Lipschitz difference bound. Unlike a bound on its individual norms,
this tends to zero with ‖U-V‖ for bounded spectral amplitudes. -/
theorem h3Path_physicalLeray_spectralSub_norm_le244
    (U V : H3SpectralVelocityState) :
    ‖h3AuditSpectralPhysicalLerayForcing U -
        h3AuditSpectralPhysicalLerayForcing V‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        (‖U‖ + ‖V‖) * ‖U - V‖ := by
  let C : ℝ := 576 * Real.pi * h3SobolevDeweightingConstant
  let A : ℝ := C * (‖U‖ + ‖V‖) * ‖U - V‖
  have hA : 0 ≤ A := by
    dsimp only [A, C]
    positivity [h3SobolevDeweightingConstant_nonneg]
  have hCoordinate (i : Fin 3) :
      ‖(h3AuditSpectralPhysicalLerayForcing U -
          h3AuditSpectralPhysicalLerayForcing V) i‖ ≤ A := by
    change ‖h3Path_physicalRawFourierDecoder244
        (h3RawFinLerayOuterProductDivergenceFourierL2 U U i) -
      h3Path_physicalRawFourierDecoder244
        (h3RawFinLerayOuterProductDivergenceFourierL2 V V i)‖ ≤ A
    rw [← h3Path_physicalRawFourierDecoder_sub244]
    exact (h3Path_physicalRawFourierDecoder_norm_le244 _).trans
      (by
        dsimp only [A, C]
        exact h3Path_rawLerayFourier_diagonal_sub_norm_le244 U V i)
  have hNorm := norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
    (h3AuditSpectralPhysicalLerayForcing U -
      h3AuditSpectralPhysicalLerayForcing V) hA hCoordinate
  calc
    _ ≤ 3 * A := hNorm
    _ = h3AuditInitialLerayEnergyCoefficient *
        (‖U‖ + ‖V‖) * ‖U - V‖ := by
      dsimp only [A, C, h3AuditInitialLerayEnergyCoefficient]
      ring

/-- Physical diffusion is linear in the weighted spectral state and has
an explicit three-component Lipschitz constant. -/
theorem h3Path_physicalLaplacian_spectralSub_norm_le244
    (U V : H3SpectralVelocityState) :
    ‖h3AuditSpectralPhysicalLaplacian U -
        h3AuditSpectralPhysicalLaplacian V‖ ≤ 3 * ‖U - V‖ := by
  have hCoordinate (i : Fin 3) :
      ‖(h3AuditSpectralPhysicalLaplacian U -
          h3AuditSpectralPhysicalLaplacian V) i‖ ≤ ‖U - V‖ := by
    change ‖h3Path_physicalRawFourierDecoder244
        (h3SpectralScalarLaplacianRawFourierL2 (U i)) -
      h3Path_physicalRawFourierDecoder244
        (h3SpectralScalarLaplacianRawFourierL2 (V i))‖ ≤ ‖U - V‖
    rw [← h3Path_physicalRawFourierDecoder_sub244]
    rw [← h3SpectralScalarLaplacianRawFourierL2_sub]
    have hCoord : ‖U i - V i‖ ≤ ‖U - V‖ := by
      simpa only [Pi.sub_apply] using
        (h3SpectralVelocity_coordinate_norm_le (U - V) i)
    exact (h3Path_physicalRawFourierDecoder_norm_le244 _).trans
      ((norm_h3SpectralScalarLaplacianRawFourierL2_le (U i - V i)).trans hCoord)
  exact norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
    (h3AuditSpectralPhysicalLaplacian U -
      h3AuditSpectralPhysicalLaplacian V) (norm_nonneg (U - V)) hCoordinate

/-- Full quantitative projected source difference, from the ACTUAL spectral
H³ state at two arbitrary inputs with no time parameter or continuity axiom. -/
theorem h3Path_physicalProjectedSpectralSource_sub_norm_le244
    (U V : H3SpectralVelocityState) :
    ‖(h3AuditSpectralPhysicalLaplacian U -
         h3AuditSpectralPhysicalLerayForcing U) -
        (h3AuditSpectralPhysicalLaplacian V -
         h3AuditSpectralPhysicalLerayForcing V)‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖)) *
        ‖U - V‖ := by
  have hIdentity :
      (h3AuditSpectralPhysicalLaplacian U -
          h3AuditSpectralPhysicalLerayForcing U) -
        (h3AuditSpectralPhysicalLaplacian V -
          h3AuditSpectralPhysicalLerayForcing V) =
      (h3AuditSpectralPhysicalLaplacian U -
          h3AuditSpectralPhysicalLaplacian V) -
        (h3AuditSpectralPhysicalLerayForcing U -
          h3AuditSpectralPhysicalLerayForcing V) := by
    abel
  rw [hIdentity]
  calc
    _ ≤ ‖h3AuditSpectralPhysicalLaplacian U -
            h3AuditSpectralPhysicalLaplacian V‖ +
          ‖h3AuditSpectralPhysicalLerayForcing U -
            h3AuditSpectralPhysicalLerayForcing V‖ := norm_sub_le _ _
    _ ≤ 3 * ‖U - V‖ +
        h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖) * ‖U - V‖ :=
      add_le_add (h3Path_physicalLaplacian_spectralSub_norm_le244 U V)
        (h3Path_physicalLeray_spectralSub_norm_le244 U V)
    _ = (3 + h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖)) *
        ‖U - V‖ := by ring

/-- The actual positive-time projected Hilbert source has the same concrete
spectral difference control, not merely a compact-window continuity claim. -/
theorem h3Path_actualProjectedSource_temporalSub_norm_le_spectral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3PathActualProjectedMomentumSource244 hH3 s -
        h3PathActualProjectedMomentumSource244 hH3 t‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 s‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 t‖)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 s -
          h3AuditActualSpectralVelocityTotal hH3 t‖ := by
  have hS : h3PathActualProjectedMomentumSource244 hH3 s =
      h3AuditSpectralPhysicalLaplacian
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3AuditSpectralPhysicalLerayForcing
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
    simp only [h3PathActualProjectedMomentumSource244,
      h3AuditInitialActualSpectralLaplacianTotal,
      h3AuditInitialActualSpectralLerayTotal, dite_eq_left hs]
  have hT : h3PathActualProjectedMomentumSource244 hH3 t =
      h3AuditSpectralPhysicalLaplacian
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3AuditSpectralPhysicalLerayForcing
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
    simp only [h3PathActualProjectedMomentumSource244,
      h3AuditInitialActualSpectralLaplacianTotal,
      h3AuditInitialActualSpectralLerayTotal, dite_eq_left ht]
  rw [hS, hT]
  exact h3Path_physicalProjectedSpectralSource_sub_norm_le244
    (h3AuditActualSpectralVelocityTotal hH3 s)
    (h3AuditActualSpectralVelocityTotal hH3 t)

/-- Same canonical cofinal Fourier-kinetic witnesses, source-maximizing times,
minimal outer cuts and disjoint H³-dissipation charging windows. The precise
physical source-time increment is controlled by actual spectral H³ motion,
with no new assumptions and no reselected physical times. The critical-width
branch retains its explicit noncompression/rate/width hypotheses. -/
theorem h3Path_noL2Trace_canonicalWidth_physicalSourceSpectralTemporalBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ k,
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k) -
          h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤
        (3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)) *
          ‖h3AuditActualSpectralVelocityTotal hH3 (s k) -
            h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∨
          M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k) -
            h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖) ∧
        (∀ E : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ≤ E) →
          Tendsto (fun k : ℕ =>
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k) -
              h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
            atTop atTop) ∧
        (∀ E : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k) -
              h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ≤ E) →
          Tendsto (fun k : ℕ =>
            ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
            atTop atTop)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hAlternative⟩ :=
    h3Path_noL2Trace_canonicalWidth_spectralAnchorOrDisplacement244
      hH3 hClass hMass hNoTrace hDInt
  have hBound (k : ℕ) :
      ‖h3PathActualProjectedMomentumSource244 hH3 (s k) -
        h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k) -
          h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ := by
    have hsAbs : s k ∈ Set.Ioo (0 : ℝ) T := by
      constructor
      · exact lt_of_lt_of_le
          (lt_trans hClass.terminal_start.1 (hTime (v k)).1)
          (hPeak k).1.1
      · have hEnd : τ (v k) + (T - τ (v k)) / 2 < T := by
          have ht := (hTime (v k)).2
          linarith only [ht]
        exact lt_of_le_of_lt (hPeak k).1.2 hEnd
    have htAbs : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
        (hTime (v k)).2⟩
    exact h3Path_actualProjectedSource_temporalSub_norm_le_spectral244
      hH3 (s k) (τ (v k)) hsAbs htAbs
  exact ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, hBound, hAlternative⟩

end
end PrimeTensor.FirstMonomialTriad
