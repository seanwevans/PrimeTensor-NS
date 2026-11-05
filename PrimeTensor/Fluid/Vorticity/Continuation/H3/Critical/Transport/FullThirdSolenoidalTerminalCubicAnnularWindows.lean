import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalArbitraryViscousDiagonal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusIntegratedWindows244
import Mathlib.Tactic

/-!
# Genuine cubic finite-frequency persistence without a kinetic nontrace premise

The new arbitrary-height viscous escape diagonal is specialized to cubic
heights. The existing physical finite-annulus theorem then extracts an outer
Fourier cutoff and a positive right-hand time width that preserves at least
half the cubic dissipation height. The integration cost is paid by a finite
annulus of the ACTUAL physical H³ dissipation.

The only nontrace hypothesis is failure of the strong weighted H³ endpoint,
not failure of the physical kinetic L² endpoint nor positivity of its
terminal mass. No uniform lower bound for the window widths is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalCubicAnnular244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Failure of a terminal H³ spectral trace gives one cofinal sequence
carrying a strictly cubic lower bound for high-radial physical H³ viscosity
at the NATURAL n+1 cutoff, with no physical kinetic nontrace hypothesis. -/
theorem thirdFullPhysical_noH3Trace_cubicViscousDiagonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ τ : ℕ → ℝ,
      (∀ n, τ n ∈ Set.Ioo b T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) ^ 3 <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) := by
  obtain ⟨τ, hτ, _hDist, hLimit, hHigh, _hFull⟩ :=
    thirdFullPhysical_noH3Trace_arbitraryViscousHeightDiagonal244
      hH3 hClass b hb hNoTrace (fun n => ((n : ℝ) + 1) ^ 3)
  exact ⟨τ, hτ, hLimit, hHigh⟩

/-- At each time of the unconditional H³-nontrace cubic diagonal there is a
finite Fourier annulus whose ACTUAL H³ dissipation remains above half its
cubic height throughout a genuine positive-width interval. These windows
are initially indexed but need not be disjoint. -/
theorem thirdFullPhysical_noH3Trace_cubicFiniteAnnularWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ),
      (∀ n, τ n ∈ Set.Ioo b T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n, n ≤ N n ∧ 0 < δ n ∧ τ n + δ n < T) ∧
      (∀ n, ∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) ∧
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ n, δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
        ∫ s in τ n..(τ n + δ n),
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨τ, hτ, hLimit, hCubic⟩ :=
    thirdFullPhysical_noH3Trace_cubicViscousDiagonal244
      hH3 hClass b hb hNoTrace
  have hWindow (n : ℕ) :
      ∃ (N : ℕ) (δ : ℝ), n ≤ N ∧ 0 < δ ∧ τ n + δ < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) ∧
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
          (∫ s in τ n..(τ n + δ),
            h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
    exact h3Path_cubicHighSnapshot_has_integratedFiniteAnnulusWindow244
      hH3 hClass (τ n) ht n (hCubic n)
  choose N δ hInfo using hWindow
  exact ⟨τ, N, δ, hτ, hLimit,
    (fun n => ⟨(hInfo n).1, (hInfo n).2.1, (hInfo n).2.2.1⟩),
    (fun n s hs => (hInfo n).2.2.2.1 s hs),
    (fun n => (hInfo n).2.2.2.2)⟩

end
end PrimeTensor.FirstMonomialTriad
