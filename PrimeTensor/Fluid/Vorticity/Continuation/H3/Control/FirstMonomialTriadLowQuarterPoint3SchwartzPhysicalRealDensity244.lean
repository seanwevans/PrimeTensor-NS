import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralRealPhysicalDensity244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Raw.Approximation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Complex
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Actual real physical Schwartz density from weighted H³ spectral velocity

Previous spectral density showed only that the real L² decoders of weighted
Schwartz spectral approximants converge. This file constructs actual REAL
physical Schwartz functions and proves they converge in physical real L².

The input is the already-proved *deweighted raw-Fourier Schwartz density*:
for every spectral G there is a complex Schwartz S whose L² class approximates
the genuine raw Fourier class of G. The inverse Schwartz Fourier transform
is again Schwartz; applying its real-part continuous linear projection remains
Schwartz. The exact Schwartz/L² Plancherel compatibility gives

  ‖decodeReal(G) - realPart(fourierInv(S)).toLp‖
      ≤ ‖rawFourierL2(G) - S.toLp‖.

We build a simultaneous three-component real physical Schwartz sequence
converging to decodeReal(U), then identify the target for a genuinely encoded
physical H³ snapshot with the actual zeroth-order velocity L² jets.

Important limitation: no convergence of H³ physical derivative energies E₂,
E₃ is asserted; arbitrary raw-L² Schwartz approximants need not approximate
weighted H³ strongly. No solenoidal approximation is asserted either.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology FourierTransform
open scoped BigOperators ENNReal SchwartzMap FourierTransform

noncomputable section
set_option maxHeartbeats 800000

noncomputable local instance axisFintypeSchwartzPhysicalRealDensity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise real projection of any complex Schwartz function agrees exactly
with taking the real part of its L² equivalence class. -/
theorem h3RealPartFourierL2_schwartz_toLp244
    (S : SchwartzMap H3FourierPoint3 ℂ) :
    h3RealPartFourierL2
        (S.toLp 2 (volume : Measure H3FourierPoint3)) =
      (h3ComplexSchwartzRealPart S).toLp
        2 (volume : Measure H3FourierPoint3) := by
  unfold h3RealPartFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.reCLM.coeFn_compLp
      (S.toLp 2 (volume : Measure H3FourierPoint3)),
    S.coeFn_toLp 2 (volume : Measure H3FourierPoint3),
    (h3ComplexSchwartzRealPart S).coeFn_toLp
      2 (volume : Measure H3FourierPoint3)
  ] with x hRe hS hSchwartz
  rw [hRe, hSchwartz, hS]
  exact (h3ComplexSchwartzRealPart_apply S x).symm

/-- The actual physical real Schwartz representative associated with one
raw complex Schwartz Fourier approximation. -/
noncomputable def h3RawSchwartzPhysicalRealInverse244
    (S : SchwartzMap H3FourierPoint3 ℂ) :
    SchwartzMap H3FourierPoint3 ℝ :=
  h3ComplexSchwartzRealPart (𝓕⁻ S)

/-- Quantitative comparison with the genuine raw-Fourier L² approximation:
inverse Plancherel is an isometry and real projection is a contraction. -/
theorem norm_h3SpectralScalarDecodeRealL2_sub_schwartzInverse_le244
    (G : H3SpectralScalarState)
    (S : SchwartzMap H3FourierPoint3 ℂ) :
    ‖h3SpectralScalarDecodeRealL2 G -
        (h3RawSchwartzPhysicalRealInverse244 S).toLp
          2 (volume : Measure H3FourierPoint3)‖ ≤
      ‖h3SpectralScalarRawFourierL2 G -
        S.toLp 2 (volume : Measure H3FourierPoint3)‖ := by
  let T := MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ
  have hInverse :
      T.symm (S.toLp 2 (volume : Measure H3FourierPoint3)) =
        (𝓕⁻ S).toLp 2 (volume : Measure H3FourierPoint3) := by
    change 𝓕⁻ (S.toLp 2 (volume : Measure H3FourierPoint3)) =
      (𝓕⁻ S).toLp 2 (volume : Measure H3FourierPoint3)
    exact SchwartzMap.toLp_fourierInv_eq S
  have hReal :
      h3RealPartFourierL2 (T.symm
        (S.toLp 2 (volume : Measure H3FourierPoint3))) =
      (h3RawSchwartzPhysicalRealInverse244 S).toLp
        2 (volume : Measure H3FourierPoint3) := by
    rw [hInverse]
    exact h3RealPartFourierL2_schwartz_toLp244 (𝓕⁻ S)
  rw [← hReal]
  change
    ‖h3RealPartFourierL2 (T.symm (h3SpectralScalarRawFourierL2 G)) -
      h3RealPartFourierL2
        (T.symm (S.toLp 2 (volume : Measure H3FourierPoint3)))‖ ≤ _
  have hRealSub (F H : H3FourierComplexL2) :
      h3RealPartFourierL2 (F - H) =
        h3RealPartFourierL2 F - h3RealPartFourierL2 H := by
    simp only [sub_eq_add_neg, h3RealPartFourierL2_add,
      h3RealPartFourierL2_neg]
  rw [← hRealSub]
  calc
    ‖h3RealPartFourierL2
        (T.symm (h3SpectralScalarRawFourierL2 G) -
          T.symm (S.toLp 2 (volume : Measure H3FourierPoint3)))‖ ≤
      ‖T.symm (h3SpectralScalarRawFourierL2 G) -
        T.symm (S.toLp 2 (volume : Measure H3FourierPoint3))‖ :=
      norm_h3RealPartFourierL2_le _
    _ = ‖h3SpectralScalarRawFourierL2 G -
          S.toLp 2 (volume : Measure H3FourierPoint3)‖ := by
      rw [← map_sub]
      exact T.symm.norm_map _

/-- Every weighted H³ spectral scalar admits an ACTUAL real physical Schwartz
representative close to its canonical real inverse-Fourier decoder in L². -/
theorem exists_h3PhysicalRealSchwartz_spectralApprox_norm244
    (G : H3SpectralScalarState)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : SchwartzMap H3FourierPoint3 ℝ,
      ‖h3SpectralScalarDecodeRealL2 G -
        ψ.toLp 2 (volume : Measure H3FourierPoint3)‖ < ε := by
  obtain ⟨S, hRaw⟩ := exists_h3Schwartz_rawFourierApprox_norm G hε
  refine ⟨h3RawSchwartzPhysicalRealInverse244 S, ?_⟩
  exact (norm_h3SpectralScalarDecodeRealL2_sub_schwartzInverse_le244 G S).trans_lt
    hRaw

/-- Three-component real PHYSICAL Schwartz approximation: the actual real
inverse-Fourier decoder of an arbitrary weighted H³ velocity is the L² limit
of a single sequence of real Schwartz velocity vectors. -/
theorem exists_h3PhysicalRealSchwartzVelocityApprox_sequence244
    (U : H3SpectralVelocityState) :
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℝ,
      Tendsto
        (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) ∧
      CauchySeq
        (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3)) := by
  classical
  have hRadiusPos (n : ℕ) :
      0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hApprox (n : ℕ) (j : Fin 3) :
      ∃ ψ : SchwartzMap H3FourierPoint3 ℝ,
        dist (h3SpectralVelocityDecodeRealL2 U j)
          (ψ.toLp 2 (volume : Measure H3FourierPoint3)) <
        (1 : ℝ) / ((n : ℝ) + 1) := by
    obtain ⟨ψ, hψ⟩ :=
      exists_h3PhysicalRealSchwartz_spectralApprox_norm244
        (U j) (hRadiusPos n)
    refine ⟨ψ, ?_⟩
    simpa only [dist_eq_norm, h3SpectralVelocityDecodeRealL2_apply] using hψ
  choose Ψ hΨ using hApprox
  have hRadiusTendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hConverges :
      Tendsto (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) := by
    rw [tendsto_pi_nhds]
    intro j
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRadiusTendsto) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hRadiusSmall :
        (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      have h := hN n hn
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (hRadiusPos n)] using h
    calc
      dist ((Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
          (h3SpectralVelocityDecodeRealL2 U j) =
          dist (h3SpectralVelocityDecodeRealL2 U j)
            ((Ψ n j).toLp 2 (volume : Measure H3FourierPoint3)) :=
        dist_comm _ _
      _ < (1 : ℝ) / ((n : ℝ) + 1) := hΨ n j
      _ < ε := hRadiusSmall
  exact ⟨Ψ, hConverges, hConverges.cauchySeq⟩

/-- For a genuine Fourier-compatible physical H³ velocity slice, the target
of the CONSTRUCTED real Schwartz sequence is exactly the physical zeroth-order
velocity L² jet, not an abstract complex inverse-Fourier limit. -/
theorem exists_h3PhysicalRealSchwartzApprox_actualVelocityZeroJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℝ,
      Tendsto
        (fun n : ℕ => fun j : Fin 3 =>
          (Ψ n j).toLp 2 (volume : Measure H3FourierPoint3))
        atTop (𝓝 (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  obtain ⟨Ψ, hConverges, _⟩ :=
    exists_h3PhysicalRealSchwartzVelocityApprox_sequence244 U
  have hEq :
      h3SpectralVelocityDecodeRealL2 U =
      (fun j : Fin 3 =>
        h3ToFourierRealL2
          (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j))) := by
    funext j
    exact h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
      hFourier j
  refine ⟨Ψ, ?_⟩
  rw [← hEq]
  exact hConverges

end
end PrimeTensor.FirstMonomialTriad
