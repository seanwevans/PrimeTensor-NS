import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdComplexTransverseProjection
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralVelocityDensity244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Incompressibility.Projection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Continuity
import Mathlib.Tactic

/-!
# Strong Leray-projected spectral H³ density in the exact finite-vector carrier

For a divergence-free weighted H³ state `U`, choose genuine *weighted spectral*
Schwartz vectors `Phi_n` converging to `U`. Apply the already constructed
bounded Fourier Leray operator to the actual states represented by `Phi_n`.

Every projected state is *exactly* Fourier divergence-free; the projection is
idempotent and the quantitative error is bounded by six times the original
weighted H³ error in the project's finite-product sup norm. Thus the projected
sequence converges strongly and is Cauchy, without assuming a solenoidal
approximation sequence. As a converse stability fact, the divergence-free
spectral subspace is sequentially closed in the same genuine norm.

Important: the projector's image is an H³ `L²` spectral state. This file DOES
NOT assert that it admits a physical real Schwartz representative, nor that
its Fourier profile is smooth at zero frequency, nor that the exact pointwise
second/third Schwartz jet realization has already been proved. Fourier
reality, origin excision, physical Schwartz realization, and jet matching
remain the following analytic bridge.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section

private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeSolenoidalSpectralDensity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Apply the actual bounded H³ Leray operator to a spectral Schwartz vector.
The result is an H³ spectral state, not (yet) a Schwartz-map representative. -/
noncomputable def h3SchwartzSpectralLerayState244
    (Phi : Fin 3 → SchwartzMap V3 ℂ) : H3SpectralVelocityState :=
  h3SpectralFinLerayApply (h3SchwartzSpectralVelocityRealization244 Phi)

/-- Each projected approximate state is divergence-free in the actual L²
spectral sense, even if the input Schwartz vector was not. -/
theorem h3SchwartzSpectralLerayState_divergenceFree244
    (Phi : Fin 3 → SchwartzMap V3 ℂ) :
    H3SpectralFinDivergenceFree (h3SchwartzSpectralLerayState244 Phi) := by
  exact h3SpectralFinLerayApply_divergenceFree
    (h3SchwartzSpectralVelocityRealization244 Phi)

/-- Leray is idempotent on each projected spectral approximation, with no
additional spectral support or regularity premise. -/
theorem h3SchwartzSpectralLerayState_fixed244
    (Phi : Fin 3 → SchwartzMap V3 ℂ) :
    h3SpectralFinLerayApply (h3SchwartzSpectralLerayState244 Phi) =
      h3SchwartzSpectralLerayState244 Phi := by
  exact h3SpectralFinLerayApply_eq_of_divergenceFree
    (h3SchwartzSpectralLerayState_divergenceFree244 Phi)

/-- Exact H³ stability: projecting an arbitrary complex spectral Schwartz
approximation of a solenoidal target multiplies the error by at most six. -/
theorem h3SchwartzSpectralLerayState_error_le244
    (U : H3SpectralVelocityState)
    (hU : H3SpectralFinDivergenceFree U)
    (Phi : Fin 3 → SchwartzMap V3 ℂ) :
    ‖U - h3SchwartzSpectralLerayState244 Phi‖ ≤
      6 * ‖U - h3SchwartzSpectralVelocityRealization244 Phi‖ := by
  have hFixed : h3SpectralFinLerayApply U = U :=
    h3SpectralFinLerayApply_eq_of_divergenceFree hU
  have hErr : U - h3SchwartzSpectralLerayState244 Phi =
      h3SpectralFinLerayApply
        (U - h3SchwartzSpectralVelocityRealization244 Phi) := by
    rw [h3SpectralFinLerayApply_sub, hFixed]
    rfl
  rw [hErr]
  exact norm_h3SpectralFinLerayApply_le
    (U - h3SchwartzSpectralVelocityRealization244 Phi)

/-- No solenoidal-density assumption is needed: for every positive H³ error
threshold, the projected image of a genuine Schwartz vector approximates an
arbitrary divergence-free spectral target within that threshold. -/
theorem exists_h3SchwartzSpectralLerayState_approx244
    (U : H3SpectralVelocityState)
    (hU : H3SpectralFinDivergenceFree U)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ Phi : Fin 3 → SchwartzMap V3 ℂ,
      H3SpectralFinDivergenceFree (h3SchwartzSpectralLerayState244 Phi) ∧
      ‖U - h3SchwartzSpectralLerayState244 Phi‖ < epsilon := by
  have hSmall : 0 < epsilon / 6 := by positivity
  obtain ⟨Phi, hPhi⟩ :=
    exists_h3SchwartzSpectralVelocityApprox_norm244 U hSmall
  refine ⟨Phi, h3SchwartzSpectralLerayState_divergenceFree244 Phi, ?_⟩
  calc
    ‖U - h3SchwartzSpectralLerayState244 Phi‖ ≤
        6 * ‖U - h3SchwartzSpectralVelocityRealization244 Phi‖ :=
      h3SchwartzSpectralLerayState_error_le244 U hU Phi
    _ < 6 * (epsilon / 6) :=
      mul_lt_mul_of_pos_left hPhi (by norm_num)
    _ = epsilon := by ring

/-- Construct a FULL sequence of Fourier-divergence-free weighted H³ states,
represented as Leray projections of genuine input Schwartz spectra, converging
strongly to the same solenoidal target. The sequence is automatically Cauchy. -/
theorem exists_h3SchwartzSpectralLerayState_sequence244
    (U : H3SpectralVelocityState)
    (hU : H3SpectralFinDivergenceFree U) :
    ∃ Phi : ℕ → Fin 3 → SchwartzMap V3 ℂ,
      Tendsto (fun n => h3SchwartzSpectralLerayState244 (Phi n))
        atTop (𝓝 U) ∧
      CauchySeq (fun n => h3SchwartzSpectralLerayState244 (Phi n)) ∧
      (∀ n, H3SpectralFinDivergenceFree
        (h3SchwartzSpectralLerayState244 (Phi n))) := by
  obtain ⟨Phi, hTendsto, _hCauchy⟩ :=
    exists_h3SchwartzSpectralVelocityApprox_sequence244 U
  have hFixed : h3SpectralFinLerayApply U = U :=
    h3SpectralFinLerayApply_eq_of_divergenceFree hU
  have hProjected : Tendsto
      (fun n => h3SchwartzSpectralLerayState244 (Phi n))
      atTop (𝓝 (h3SpectralFinLerayApply U)) := by
    exact (continuous_h3SpectralFinLerayApply.tendsto U).comp hTendsto
  rw [hFixed] at hProjected
  exact ⟨Phi, hProjected, hProjected.cauchySeq,
    fun n => h3SchwartzSpectralLerayState_divergenceFree244 (Phi n)⟩

/-- Strong weighted-H³ limits of Fourier-divergence-free states remain
Fourier-divergence-free. The proof uses the genuine bounded Leray operator,
not pointwise convergence of arbitrary L² representatives. -/
theorem h3SpectralFinDivergenceFree_of_tendsto244
    (U : H3SpectralVelocityState)
    (V : ℕ → H3SpectralVelocityState)
    (hTendsto : Tendsto V atTop (𝓝 U))
    (hV : ∀ n, H3SpectralFinDivergenceFree (V n)) :
    H3SpectralFinDivergenceFree U := by
  have hEach (n : ℕ) : h3SpectralFinLerayApply (V n) = V n :=
    h3SpectralFinLerayApply_eq_of_divergenceFree (hV n)
  have hEq : (fun n => h3SpectralFinLerayApply (V n)) = V := by
    funext n
    exact hEach n
  have hP : Tendsto (fun n => h3SpectralFinLerayApply (V n))
      atTop (𝓝 (h3SpectralFinLerayApply U)) :=
    (continuous_h3SpectralFinLerayApply.tendsto U).comp hTendsto
  rw [hEq] at hP
  have hFixed : h3SpectralFinLerayApply U = U :=
    tendsto_nhds_unique hP hTendsto
  rw [← hFixed]
  exact h3SpectralFinLerayApply_divergenceFree U

end
end PrimeTensor.FirstMonomialTriad
