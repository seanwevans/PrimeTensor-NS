import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierFrozenDiffusionCommutator
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Diffusion.Sign
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassFourierMassEscape
import Mathlib.Tactic

/-!
# Genuine physical highpass frozen diffusion has the dissipative sign

The frozen-diffusion temporal ledger previously retained the signed scalar
`-inner ℝ H D`, because an integrated Laplacian increment is NOT the heat
semigroup. Here only the FROZEN positive-time physical pairing is identified:

  inner ℝ (P_{>=rho} u(x)) (P_{>=rho} Delta u(x)) <= 0.

The proof uses the exact sharp Fourier indicator, q(ξ) = (2π)^2 |ξ|^2,
raw-Laplacian identification, and real physical Plancherel. Unlike a
postulated spectral pairing, both operands are the actual old physical
velocity and actual decoded physical Laplacian at the same time.

There is no cutoff-uniform estimate on the temporal commutator. The remaining
cofinal obstruction thus separates an honest nonnegative diffusion payment
from the uncontrolled commutator and signed nonlinear Leray transfer.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeOuterFrozenDiffusionSign244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceOuterFrozenDiffusionSign244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Highpass LOCALIZATION of the Fourier multiplier dissipation sign.
This is not a statement about a fabricated spectral projection: the cutoff
is the exact complement of the genuine radial frequency ball. -/
theorem thirdFullKinetic_sharpHighpassRawLaplacian_inner_nonpos244
    (rho : ℝ) (G : H3SpectralScalarState) :
    (inner ℂ
      (h3SpectralScalarRawFourierL2 G -
        h3CriticalFourierSharpLowCutoffCLM rho
          (h3SpectralScalarRawFourierL2 G))
      (h3SpectralScalarLaplacianRawFourierL2 G -
        h3CriticalFourierSharpLowCutoffCLM rho
          (h3SpectralScalarLaplacianRawFourierL2 G))).re ≤ 0 := by
  let F : H3FourierComplexL2 := h3SpectralScalarRawFourierL2 G
  let L : H3FourierComplexL2 := h3SpectralScalarLaplacianRawFourierL2 G
  let H : H3FourierComplexL2 :=
    F - h3CriticalFourierSharpLowCutoffCLM rho F
  let D : H3FourierComplexL2 :=
    L - h3CriticalFourierSharpLowCutoffCLM rho L
  change (inner ℂ H D).re ≤ 0
  calc
    (inner ℂ H D).re =
        Complex.re (∫ ξ : H3FourierPoint3, inner ℂ (H ξ) (D ξ)) := by
          rw [MeasureTheory.L2.inner_def]
    _ = ∫ ξ : H3FourierPoint3, Complex.re (inner ℂ (H ξ) (D ξ)) := by
          symm
          exact Complex.reCLM.integral_comp_comm
            (MeasureTheory.L2.integrable_inner H D)
    _ ≤ 0 := by
      apply MeasureTheory.integral_nonpos_of_ae
      have hLap :=
        h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw G
      filter_upwards [
        h3Critical_fourierSharpHighpass_ae rho F,
        h3Critical_fourierSharpHighpass_ae rho L,
        hLap
      ] with ξ hHighF hHighL hLapξ
      change Complex.re (inner ℂ (H ξ) (D ξ)) ≤ 0
      rw [hHighF, hHighL]
      by_cases hξ : ξ ∈ (h3TerminalRadialFrequencyBelow rho)ᶜ
      · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, hLapξ]
        let z : ℂ := F ξ
        let q : ℝ := h3FourierGradientSquare ξ
        have hq : 0 ≤ q := h3FourierGradientSquare_nonneg ξ
        change Complex.re (inner ℂ z ((-(q : ℂ)) • z)) ≤ 0
        rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        have hComplex :
            (-(q : ℂ)) * ((‖z‖ : ℂ) ^ 2) =
              ((-q * ‖z‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
        have hRe :
            Complex.re ((-(q : ℂ)) * ((‖z‖ : ℂ) ^ 2)) =
              -q * ‖z‖ ^ 2 := by
          have h := congrArg Complex.re hComplex
          simpa only [Complex.ofReal_re] using h
        calc
          Complex.re ((-(q : ℂ)) * ((‖z‖ : ℂ) ^ 2)) =
              -q * ‖z‖ ^ 2 := hRe
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr hq) (sq_nonneg ‖z‖)
      · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
        simp

/-- Scalar REAL physical highpass diffusion pairing: the same physical
sharp cutoff is applied to the velocity and its genuine Laplacian.
The two Fourier identifications can be established from a realizable H³
snapshot; they are not assumed in the final physical-time theorem below. -/
theorem thirdFullPhysical_scalarSharpHighpassLaplacian_inner_nonpos244
    (rho : ℝ) (F L : H3ScalarL2) (G : H3SpectralScalarState)
    (hF : h3ScalarFourierL2 F = h3SpectralScalarRawFourierL2 G)
    (hL : h3ScalarFourierL2 L =
      h3SpectralScalarLaplacianRawFourierL2 G) :
    inner ℝ
      (F - h3CriticalPhysicalSharpLowCutoffApply rho F)
      (L - h3CriticalPhysicalSharpLowCutoffApply rho L) ≤ 0 := by
  apply h3ScalarL2_inner_nonpos_of_fourier_re_inner_nonpos
  simpa only [h3Critical_scalarFourier_physicalHighpass_eq, hF, hL] using
    (thirdFullKinetic_sharpHighpassRawLaplacian_inner_nonpos244 rho G)

/-- At EVERY strictly positive physical time, the frozen actual highpass
Laplacian pairing is dissipative. No extra scalar Fourier-identification
data are supplied: both identifications are constructed from the logged H³
path and its actual real-physical Laplacian. -/
theorem thirdFullPhysical_outerFrozenHighpassDiffusion_inner_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x rho : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T) :
    inner ℝ
      (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)
      (thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho) ≤ 0 := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let L : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialActualSpectralLaplacianTotal hH3 x
  have hHerm : H3SpectralVelocityRawHermitian U :=
    h3Critical_actualSpectralVelocity_rawHermitian hH3 x hx
  change inner ℝ
    (V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V)
    (L - thirdFullPhysicalSharpLowCutoffHilbert244 rho L) ≤ 0
  apply h3PhysicalRealFinVectorL2_inner_nonpos_of_coordinate_nonpos
  intro j
  change inner ℝ
    (V.ofLp j - h3CriticalPhysicalSharpLowCutoffApply rho (V.ofLp j))
    (L.ofLp j - h3CriticalPhysicalSharpLowCutoffApply rho (L.ofLp j)) ≤ 0
  have hReal : H3SpectralScalarRealizable (U j) :=
    h3SpectralScalarRawHermitian_realizable (hHerm j)
  have hVelFourier :
      h3ScalarFourierL2 (V.ofLp j) =
        h3SpectralScalarRawFourierL2 (U j) := by
    dsimp only [V]
    rw [h3Audit_initialOldPhysicalHilbertTotal_eq_actualSpectralDecode
      hH3 x hx]
    change h3ScalarFourierL2
        (h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2 (U j))) =
      h3SpectralScalarRawFourierL2 (U j)
    exact h3ScalarFourierL2_h3FromFourierRealL2_decodeReal_eq_raw_of_realizable
      hReal
  have hLapFourier :
      h3ScalarFourierL2 (L.ofLp j) =
        h3SpectralScalarLaplacianRawFourierL2 (U j) := by
    have hPhysical : L.ofLp j =
        h3Path_physicalRawFourierDecoder244
          (h3SpectralScalarLaplacianRawFourierL2 (U j)) := by
      dsimp only [L, h3AuditInitialActualSpectralLaplacianTotal]
      simp only [dite_eq_left hx]
      rfl
    rw [hPhysical]
    exact h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
      _ (h3SpectralScalarLaplacianRawFourierL2_preserves_hermitian
        (hHerm j))
  exact thirdFullPhysical_scalarSharpHighpassLaplacian_inner_nonpos244
    rho (V.ofLp j) (L.ofLp j) (U j) hVelFourier hLapFourier

/-- The previously signed frozen diffusion work now has an UNCONDITIONAL
nonnegative physical realization at each strict positive time. -/
theorem thirdFullPhysical_outerFrozenDiffusionWork_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x rho : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T) :
    0 ≤ -inner ℝ
      (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)
      (thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho) :=
  neg_nonneg.mpr
    (thirdFullPhysical_outerFrozenHighpassDiffusion_inner_nonpos244
      hH3 x rho hx)

/-- The exact physical three-way carrier obstruction can now be read with a
PROVED nonnegative frozen diffusion channel rather than an abstract signed
viscous pairing. The temporal commutator and nonlinear Leray transfer remain
unresolved physical payments. -/
theorem thirdFullPhysical_outerFrozenNonnegativeThreeChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho K epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) (hK : 0 < K)
    (hForced : epsilon < K *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)) :
    0 ≤ -inner ℝ
      (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)
      (thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho) ∧
    (epsilon / 2 < K * (2 * (s - x) *
      (-inner ℝ
        (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)
        (thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho))) ∨
     epsilon / 2 < K * (2 *
      ‖thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho‖ *
      ‖thirdFullPhysical_outerDiffusionTemporalCommutator244 hH3 x s rho‖) ∨
     0 < inner ℝ
       (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho +
         thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho)
       (thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho)) := by
  constructor
  · exact thirdFullPhysical_outerFrozenDiffusionWork_nonneg244 hH3 x rho hx
  · exact thirdFullPhysical_outerFrozenBudget_threeChannelAlternative244
      hH3 x s rho K epsilon hx hs hxs hK hForced

end
end PrimeTensor.FirstMonomialTriad
