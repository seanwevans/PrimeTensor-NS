import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzMatchedSobolevJets244
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Actual.Selected.Bound
import Mathlib.Tactic

/-!
# Uniform Schwartz first-jet approximation of an actual physical H³ velocity slice

The preceding checkpoint gives ONE synchronized real Schwartz sequence with
weighted-H³ spectral convergence, pointwise decoder realization, 27+81
mixed L⁴/L² Sobolev jet Cauchy control, and convergence of its signed 243-slot
monomial to the canonical weighted-H³ completion.

There is an important remaining PHYSICAL identification step: the canonical
C¹ representative of a genuine Fourier-compatible, Navier–Stokes-admissible
slice is exactly the OLD logged velocity, pointwise on Point3.  Applying that
already-proved reconstruction equality to the quantitative spectral H³ first
jet bound provides a uniform-in-space estimate against the actual intrinsic
physical gradient:

  |∂ᵢ Ψₙⱼ(x) - ∂ᵢ uⱼ(ofLp x)| ≤ C₁ ‖Vₙⱼ - Uⱼ‖.

The right hand side tends to zero uniformly in x.  The 243-slot signed
monomial of the SAME Schwartz sequence continues to converge to the canonical
weighted-H³ signed completion.

This theorem does NOT assert that the completed signed monomial equals the
separately defined physical cubic transport of an arbitrary nonsmooth slice.
The latter still requires identifying the physical L²/L⁴ trilinear pairing.
Nor is an H⁴ dissipation approximation inferred from H³ density.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalFirstJet244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical signed H³ Schwarz completion evaluated at an actual
Fourier-compatible physical H³ velocity slice. This is a definition, NOT an
identification with the path's independently defined physical commutator. -/
noncomputable def h3PhysicalSnapshotCanonicalSignedMonomial244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) : ℝ :=
  weightedH3CanonicalSignedFirstMonomial244
    (velocityH3SpectralStateAt u t hInt hMeas hFourier)

/-- Quantitative first-jet error of a pointwise decoder-matched Schwartz
profile against the ACTUAL logged velocity, with the original Point3 spatial
derivative and the exact Fourier coordinate carrier conversion.  The same
H³ constant works at every spatial point and along every axis. -/
theorem thirdFullSchwartz_physicalFirstJetError_le_spectral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (V : H3SpectralVelocityState)
    (ψ : Fin 3 → SchwartzMap V3 ℝ)
    (hMatch : ∀ j : Fin 3,
      h3SchwartzPoint3Scalar (ψ j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (V j))
    (j : Fin 3) (i : A3) (x : V3) :
    |(∂_{h3FourierAxisDirection i} (ψ j)) x -
      spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
        ((WithLp.ofLp : V3 → Point3) x)| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖V j - velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖ := by
  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt u t hInt hMeas hFourier j
  have hPhysical :
      h3SpectralScalarRealC1RepresentativeOnPoint3 G =
        loggedVelocityComponent u t (h3AxisOfFin3 j) := by
    exact h3SpectralScalarRealC1RepresentativeOnPoint3_velocityH3SpectralScalarAt_eq_loggedVelocityComponent
      hNS ht hFourier j
  have hSchwartz := thirdFullSchwartz_firstJet_eq_of_zerothRealization244
    (ψ j) (V j) (hMatch j) i x
  have hEstimate :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
      (V j) G (h3ClassicalizationFinOfAxis i)
      ((WithLp.ofLp : V3 → Point3) x)
  rw [← hPhysical, hSchwartz]
  simpa only [G, h3AxisOfFin3_h3ClassicalizationFinOfAxis,
    Real.norm_eq_abs] using hEstimate

/-- At a genuine Fourier-compatible preterminal slice, one *single* matched
Schwartz family simultaneously has (i) a uniform-in-space physical first-jet
error gauge tending to zero, (ii) all 27 L⁴ and 81 L² derivative Cauchy
estimates, and (iii) the full canonical signed 243-slot monomial limit.

The gauge is the actual spectral H³ difference, not an unrelated pointwise
majorant; no first-derivative matching or boundedness hypotheses are added. -/
theorem exists_thirdFullSchwartz_physicalFirstJetGaugeAndSigned244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
    ∃ δ : ℕ → Fin 3 → ℝ,
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ n j, 0 ≤ δ n j) ∧
      (∀ j : Fin 3, Tendsto (fun n => δ n j) atTop (𝓝 0)) ∧
      (∀ n : ℕ, ∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
        |(∂_{h3FourierAxisDirection i} (Ψ n j)) x -
          spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
            ((WithLp.ofLp : V3 → Point3) x)| ≤ δ n j) ∧
      SchwartzMixedJetGraphCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      Tendsto
        (fun n => lowNormalRealSchwartzPoint3Monomial
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (h3PhysicalSnapshotCanonicalSignedMonomial244 u t hFourier)) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨V, Ψ, hWeighted, hMatch, hGraph, hMonomial⟩ :=
    exists_thirdFullSchwartz_decoderMatchedCanonicalMonomial244 U
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let δ : ℕ → Fin 3 → ℝ := fun n j => C * ‖V n j - U j‖
  have hC : 0 ≤ C :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hδNonneg : ∀ n j, 0 ≤ δ n j := by
    intro n j
    exact mul_nonneg hC (norm_nonneg _)
  have hδLimit (j : Fin 3) :
      Tendsto (fun n => δ n j) atTop (𝓝 0) := by
    have hCoordinate : Tendsto (fun n => V n j) atTop (𝓝 (U j)) :=
      (tendsto_pi_nhds.mp hWeighted) j
    have hNorm : Tendsto (fun n => ‖V n j - U j‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hCoordinate
    have hMul := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hNorm
    simpa only [δ, mul_zero] using hMul
  have hError :
      ∀ n : ℕ, ∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
        |(∂_{h3FourierAxisDirection i} (Ψ n j)) x -
          spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
            ((WithLp.ofLp : V3 → Point3) x)| ≤ δ n j := by
    intro n j i x
    have hBound :=
      thirdFullSchwartz_physicalFirstJetError_le_spectral244
        hNS ht hFourier (V n) (Ψ n) (hMatch n) j i x
    simpa only [δ, C, U, velocityH3SpectralStateAt] using hBound
  refine ⟨V, Ψ, δ, ?_, hδNonneg, hδLimit, hError, hGraph, ?_⟩
  · exact hWeighted
  · simpa only [h3PhysicalSnapshotCanonicalSignedMonomial244, U] using hMonomial

/-- Pointwise convergence of the TRUE Schwartz first derivatives to the
actual old physical coordinate derivatives, carried by the SAME family whose
signed monomial approaches the canonical H³ completion.  The preceding theorem
provides the stronger uniform-in-x error estimate. -/
theorem exists_thirdFullSchwartz_physicalFirstJetTendstoAndSigned244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      SchwartzMixedJetGraphCauchy244
        (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) ∧
      Tendsto
        (fun n => lowNormalRealSchwartzPoint3Monomial
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (h3PhysicalSnapshotCanonicalSignedMonomial244 u t hFourier)) ∧
      (∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
        Tendsto
          (fun n => (∂_{h3FourierAxisDirection i} (Ψ n j)) x)
          atTop
          (𝓝 (spatial3.d i
            (loggedVelocityComponent u t (h3AxisOfFin3 j))
            ((WithLp.ofLp : V3 → Point3) x)))) := by
  obtain ⟨_V, Ψ, δ, _hWeighted, _hNonneg, hGauge, hError,
    hGraph, hSigned⟩ :=
    exists_thirdFullSchwartz_physicalFirstJetGaugeAndSigned244
      hNS ht hFourier
  refine ⟨Ψ, hGraph, hSigned, ?_⟩
  intro j i x
  have hAbs :
      Tendsto
        (fun n => |(∂_{h3FourierAxisDirection i} (Ψ n j)) x -
          spatial3.d i (loggedVelocityComponent u t (h3AxisOfFin3 j))
            ((WithLp.ofLp : V3 → Point3) x)|)
        atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact hError n j i x
    · exact hGauge j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hAbs

end
end PrimeTensor.FirstMonomialTriad
