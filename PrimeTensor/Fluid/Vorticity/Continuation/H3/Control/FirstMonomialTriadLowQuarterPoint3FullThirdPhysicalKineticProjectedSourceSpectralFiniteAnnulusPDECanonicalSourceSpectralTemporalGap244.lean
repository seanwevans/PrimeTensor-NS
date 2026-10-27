import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceLaplacianLerayTemporalSplit244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Bilinear
import Mathlib.Tactic

/-!
# Raw Leray diagonal difference and physical spectral temporal displacement

The full raw Fourier Leray forcing is bilinear. Its existing 576 π C₃
bilinear L² estimate therefore yields the quantitative diagonal difference
bound for the ACTUAL spectral input, without a pointwise representative
assumption. Separately, the already-established inverse-Fourier physical
source bound proves a spectral anchor/displacement alternative on the fixed
canonical source-maximizing windows.

Importantly, a quantitative physical inverse-Fourier subtraction bridge is
not asserted here merely from the scalar forcing bound. The physical
spectral-displacement alternative uses the proven physical source majorant,
so it does not assume the missing terminal-uniform source modulus.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The Fourier carrier is indexed by the finite three-dimensional axis type.
The corresponding `MeasureSpace H3FourierPoint3` instance is synthesized
from this local finite-axis instance, as in the existing H³ source modules. -/
noncomputable local instance axisFintypeCanonicalSourceSpectralTemporalGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Diagonal subtraction for the real, genuine raw Leray Fourier L² classes,
not just for pointwise smooth representatives. -/
theorem h3Path_rawLerayFourier_diagonal_sub_eq244
    (U V : H3SpectralVelocityState) (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceFourierL2 U U i -
        h3RawFinLerayOuterProductDivergenceFourierL2 V V i =
      h3RawFinLerayOuterProductDivergenceFourierL2 (U - V) U i +
        h3RawFinLerayOuterProductDivergenceFourierL2 V (U - V) i := by
  apply MeasureTheory.Lp.ext
  have hUU :
      ((h3RawFinLerayOuterProductDivergenceFourierL2 U U i :
        H3FourierComplexL2) : H3FourierPoint3 → ℂ) =ᵐ[volume]
        h3RawFinLerayOuterProductDivergence U U i := by
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact MemLp.coeFn_toLp (h3RawFinLerayOuterProductDivergence_memLp2 U U i)
  have hVV :
      ((h3RawFinLerayOuterProductDivergenceFourierL2 V V i :
        H3FourierComplexL2) : H3FourierPoint3 → ℂ) =ᵐ[volume]
        h3RawFinLerayOuterProductDivergence V V i := by
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact MemLp.coeFn_toLp (h3RawFinLerayOuterProductDivergence_memLp2 V V i)
  have hDU :
      ((h3RawFinLerayOuterProductDivergenceFourierL2 (U - V) U i :
        H3FourierComplexL2) : H3FourierPoint3 → ℂ) =ᵐ[volume]
        h3RawFinLerayOuterProductDivergence (U - V) U i := by
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2 (U - V) U i)
  have hVD :
      ((h3RawFinLerayOuterProductDivergenceFourierL2 V (U - V) i :
        H3FourierComplexL2) : H3FourierPoint3 → ℂ) =ᵐ[volume]
        h3RawFinLerayOuterProductDivergence V (U - V) i := by
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2 V (U - V) i)
  have hSub := MeasureTheory.Lp.coeFn_sub
    (h3RawFinLerayOuterProductDivergenceFourierL2 U U i)
    (h3RawFinLerayOuterProductDivergenceFourierL2 V V i)
  have hAdd := MeasureTheory.Lp.coeFn_add
    (h3RawFinLerayOuterProductDivergenceFourierL2 (U - V) U i)
    (h3RawFinLerayOuterProductDivergenceFourierL2 V (U - V) i)
  filter_upwards [hUU, hVV, hDU, hVD, hSub, hAdd] with
      ξ hu hv hdu hvd hsub hadd
  rw [hsub, hadd]
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [hu, hv, hdu, hvd]
  calc
    h3RawFinLerayOuterProductDivergence U U i ξ -
        h3RawFinLerayOuterProductDivergence V V i ξ =
      (h3RawFinLerayOuterProductDivergence U U i ξ -
         h3RawFinLerayOuterProductDivergence V U i ξ) +
      (h3RawFinLerayOuterProductDivergence V U i ξ -
         h3RawFinLerayOuterProductDivergence V V i ξ) := by ring
    _ = h3RawFinLerayOuterProductDivergence (U - V) U i ξ +
          h3RawFinLerayOuterProductDivergence V (U - V) i ξ := by
      rw [h3RawFinLerayOuterProductDivergence_sub_left U V U i ξ,
        h3RawFinLerayOuterProductDivergence_sub_right V U V i ξ]

/-- Quadratic forcing has an explicit locally Lipschitz difference bound
on the actual weighted H³ spectral space, coordinatewise in Fourier L². -/
theorem h3Path_rawLerayFourier_diagonal_sub_norm_le244
    (U V : H3SpectralVelocityState) (i : Fin 3) :
    ‖h3RawFinLerayOuterProductDivergenceFourierL2 U U i -
        h3RawFinLerayOuterProductDivergenceFourierL2 V V i‖ ≤
      (576 * Real.pi * h3SobolevDeweightingConstant) *
        (‖U‖ + ‖V‖) * ‖U - V‖ := by
  rw [h3Path_rawLerayFourier_diagonal_sub_eq244]
  calc
    ‖h3RawFinLerayOuterProductDivergenceFourierL2 (U - V) U i +
        h3RawFinLerayOuterProductDivergenceFourierL2 V (U - V) i‖ ≤
      ‖h3RawFinLerayOuterProductDivergenceFourierL2 (U - V) U i‖ +
        ‖h3RawFinLerayOuterProductDivergenceFourierL2 V (U - V) i‖ :=
          norm_add_le _ _
    _ ≤ (576 * Real.pi * h3SobolevDeweightingConstant) *
          ‖U - V‖ * ‖U‖ +
        (576 * Real.pi * h3SobolevDeweightingConstant) *
          ‖V‖ * ‖U - V‖ :=
      add_le_add
        (norm_h3RawFinLerayOuterProductDivergenceFourierL2_le (U - V) U i)
        (norm_h3RawFinLerayOuterProductDivergenceFourierL2_le V (U - V) i)
    _ = (576 * Real.pi * h3SobolevDeweightingConstant) *
        (‖U‖ + ‖V‖) * ‖U - V‖ := by ring

/-- Quantitative physical source threshold: its Fourier-reconstructed L²
norm forces the anchor spectral norm OR its temporal spectral displacement
to exceed A. The source bound used here is already proved for actual H³
states, so there is no separate physical inverse-Fourier subtraction premise. -/
theorem h3Path_sourceHigh_forces_anchorSpectralOrDisplacement244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (A : ℝ) (hA : 0 ≤ A)
    (hLarge : 3 * (2 * A) +
      h3AuditInitialLerayEnergyCoefficient * (2 * A) ^ 2 + 1 ≤
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖) :
    A < ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ∨
      A < ‖h3AuditActualSpectralVelocityTotal hH3 s -
        h3AuditActualSpectralVelocityTotal hH3 t‖ := by
  let U := h3AuditActualSpectralVelocityTotal hH3 s
  let V := h3AuditActualSpectralVelocityTotal hH3 t
  let CL := h3AuditInitialLerayEnergyCoefficient
  have hCL : 0 ≤ CL := h3AuditInitialLerayEnergyCoefficient_nonneg
  by_contra hNot
  push_neg at hNot
  have hTriangle : ‖U‖ ≤ ‖V‖ + ‖U - V‖ := by
    calc
      ‖U‖ = ‖V + (U - V)‖ := by
        congr 1
        abel
      _ ≤ ‖V‖ + ‖U - V‖ := norm_add_le _ _
  have hU : ‖U‖ ≤ 2 * A := by
    linarith only [hTriangle, hNot.1, hNot.2]
  have hU2 : ‖U‖ ^ 2 ≤ (2 * A) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg U) (by positivity : 0 ≤ 2 * A)).2 hU
  have hBound : ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
      3 * (2 * A) + CL * (2 * A) ^ 2 := by
    calc
      _ ≤ 3 * ‖U‖ + CL * ‖U‖ ^ 2 := by
        simpa only [U, CL] using
          h3Path_physicalProjectedSource_norm_le_actualSpectralGrowth244
            hH3 s hs
      _ ≤ 3 * (2 * A) + CL * (2 * A) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num))
          (mul_le_mul_of_nonneg_left hU2 hCL)
  have hLarge' : 3 * (2 * A) + CL * (2 * A) ^ 2 + 1 ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ := by
    simpa only [CL] using hLarge
  linarith only [hLarge', hBound]

/-- A diverging spectral peak either grows at its anchor or has a large
spectral temporal displacement. Neither alternative selects a different
maximizing time. -/
theorem h3Path_spectralPeakEscape_anchorOrDisplacement244
    (peak anchor : ℕ → H3SpectralVelocityState)
    (hPeak : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop) :
    ∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
      M ≤ ‖anchor k‖ ∨ M ≤ ‖peak k - anchor k‖ := by
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop, 2 * M ≤ ‖peak k‖ :=
    hPeak.eventually (eventually_ge_atTop (2 * M))
  filter_upwards [hLarge] with k hk
  have hTriangle : ‖peak k‖ ≤ ‖anchor k‖ + ‖peak k - anchor k‖ := by
    calc
      ‖peak k‖ = ‖anchor k + (peak k - anchor k)‖ := by
        congr 1
        abel
      _ ≤ ‖anchor k‖ + ‖peak k - anchor k‖ := norm_add_le _ _
  by_cases hAnchor : M ≤ ‖anchor k‖
  · exact Or.inl hAnchor
  · right
    have hLess : ‖anchor k‖ < M := lt_of_not_ge hAnchor
    linarith only [hk, hTriangle, hLess]

/-- With uniformly bounded spectral anchor norms, diverging spectral
peaks force diverging *spectral state increments*, not just source jumps. -/
theorem h3Path_boundedSpectralAnchor_forces_displacementEscape244
    (peak anchor : ℕ → H3SpectralVelocityState)
    (hPeak : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop)
    (E : ℝ) (hAnchor : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E) :
    Tendsto (fun k : ℕ => ‖peak k - anchor k‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop, M + E ≤ ‖peak k‖ :=
    hPeak.eventually (eventually_ge_atTop (M + E))
  filter_upwards [hLarge, hAnchor] with k hk ha
  have hTriangle : ‖peak k‖ ≤ ‖anchor k‖ + ‖peak k - anchor k‖ := by
    calc
      ‖peak k‖ = ‖anchor k + (peak k - anchor k)‖ := by
        congr 1
        abel
      _ ≤ ‖anchor k‖ + ‖peak k - anchor k‖ := norm_add_le _ _
  linarith only [hk, ha, hTriangle]

/-- Conversely, bounded state displacement transfers actual H³ spectral
peaks to the SAME anchors of the disjoint PDE persistence windows. -/
theorem h3Path_boundedSpectralDisplacement_forces_anchorEscape244
    (peak anchor : ℕ → H3SpectralVelocityState)
    (hPeak : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop)
    (E : ℝ) (hDisplacement :
      ∀ᶠ k : ℕ in atTop, ‖peak k - anchor k‖ ≤ E) :
    Tendsto (fun k : ℕ => ‖anchor k‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop, M + E ≤ ‖peak k‖ :=
    hPeak.eventually (eventually_ge_atTop (M + E))
  filter_upwards [hLarge, hDisplacement] with k hk hd
  have hTriangle : ‖peak k‖ ≤ ‖anchor k‖ + ‖peak k - anchor k‖ := by
    calc
      ‖peak k‖ = ‖anchor k + (peak k - anchor k)‖ := by
        congr 1
        abel
      _ ≤ ‖anchor k‖ + ‖peak k - anchor k‖ := norm_add_le _ _
  linarith only [hk, hd, hTriangle]

/-- Physical canonical projected-source first-crossing clocks: under the
conditional noncompression, linear sixth-rate, and critical ninth/eighth
width cap, the SAME preselected source-maximizer sequence either displays
large spectral anchor states or large spectral temporal increments. A bound
on one channel forces the other to diverge, with no new time selection. -/
theorem h3Path_noL2Trace_canonicalWidth_spectralAnchorOrDisplacement244
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
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hMass hNoTrace hDInt
  let peak : ℕ → H3SpectralVelocityState := fun k =>
    h3AuditActualSpectralVelocityTotal hH3 (s k)
  let anchor : ℕ → H3SpectralVelocityState := fun k =>
    h3AuditActualSpectralVelocityTotal hH3 (τ (v k))
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η B D hη hB hD hRegime
  have hSpectral : Tendsto (fun k : ℕ => ‖peak k‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [peak, anchor] using
      h3Path_spectralPeakEscape_anchorOrDisplacement244 peak anchor hSpectral
  · intro E hBound
    have hBound' : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E := by
      simpa only [anchor] using hBound
    simpa only [peak, anchor] using
      h3Path_boundedSpectralAnchor_forces_displacementEscape244
        peak anchor hSpectral E hBound'
  · intro E hBound
    have hBound' : ∀ᶠ k : ℕ in atTop,
        ‖peak k - anchor k‖ ≤ E := by
      simpa only [peak, anchor] using hBound
    simpa only [anchor] using
      h3Path_boundedSpectralDisplacement_forces_anchorEscape244
        peak anchor hSpectral E hBound'

end
end PrimeTensor.FirstMonomialTriad
