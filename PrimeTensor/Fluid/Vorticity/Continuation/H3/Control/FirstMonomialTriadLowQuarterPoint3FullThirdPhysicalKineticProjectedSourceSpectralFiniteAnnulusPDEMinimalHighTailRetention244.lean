import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalOuterGrowth244
import Mathlib.Tactic

/-!
# Physical high-frequency dissipation retained before the first spectral crossing

The canonical first-crossing outer cutoff has a stronger consequence when its
original high-radial cubic snapshot is retained: at EVERY preceding admissible
frequency cutoff, at least one quarter of the inner cubic height remains in
the actual physical high-frequency H³ dissipation. The proof is the exact
physical low/high radial partition, not an assumption that frequency mass
has some generic decay rate.

The final theorem constructs cofinal actual Navier–Stokes snapshots whose
minimal quadratic-sharp PDE windows and the retained quarter-cubic high tail
refer to precisely the same physical state and minimal outer cutoff.
No terminal H³ integrability is used here; joining these witnesses to the
separated-window ninth/eighth barrier is a further step.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A cubic high-radial snapshot cannot lose more than three quarters of
its cubic height below a cutoff without retaining a quarter above it.
This is the genuine physical H³ dissipation partition. -/
theorem h3Path_cubicHighSnapshot_preCrossing_quarterHighTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n m : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hBelow :
      h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        3 * (((n : ℝ) + 1) ^ 3) / 4) :
    ((n : ℝ) + 1) ^ 3 / 4 <
      h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have hPartInner := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht ((n : ℝ) + 1)
  have hPartCandidate := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht ((m : ℝ) + 1)
  linarith only [hCube, hBelow, hPartInner, hPartCandidate]

/-- Even without retaining the initial cubic snapshot, the strict
first-crossing annular surplus gives a positive, quantitative lower bound
on the tail above any preceding cutoff. The bound may vanish in the
cofinal limit, so it is distinct from the fixed quarter-cubic floor. -/
theorem h3Path_firstCrossingSurplus_preCrossing_highTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n N m : ℕ)
    (hGap : ((n : ℝ) + 1) ^ 3 / 4 <
      (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2)
    (hBelow :
      h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        3 * (((n : ℝ) + 1) ^ 3) / 4) :
    0 < h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2) - ((n : ℝ) + 1) ^ 3 / 4 ≤
      h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  have hNonneg : 0 ≤ h3PathActualHighRadialDissipation244 ((N : ℝ) + 1) G := by
    unfold h3PathActualHighRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hPartOuter := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht ((N : ℝ) + 1)
  have hPartCandidate := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht ((m : ℝ) + 1)
  constructor
  · dsimp only [G] at hNonneg
    linarith only [hNonneg, hPartOuter, hPartCandidate, hGap, hBelow]
  · dsimp only [G] at hNonneg
    linarith only [hNonneg, hPartOuter, hPartCandidate, hBelow]

/-- Cofinal no-strong-terminal-L²-trace snapshots now retain the cubic
high-radial inequality used to select their minimal annulus. Thus each
pre-first-crossing radius retains >R³/4 actual high-frequency dissipation
at the SAME time used by the exact quadratic-sharp physical PDE clock. -/
theorem h3Path_noL2Trace_minimalQuadraticSharpClocks_retain_quarterHighTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧ 0 < δ n ∧
        τ n + δ n < T ∧
        δ n = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N n)
          (h3PathCubicAnnulusActualLinearRate244 N K C n)
          (h3PathCubicAnnulusActualQuadraticRate244 N C n) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        ((n : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N n ∧
        (∀ m : ℕ, n ≤ m → m < N n →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
              3 * (((n : ℝ) + 1) ^ 3) / 4) ∧
        (∀ m : ℕ, n ≤ m → m < N n →
          ((n : ℝ) + 1) ^ 3 / 4 <
            h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)))) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ τ n + δ < T ∧
      (δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2 ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
            3 * (((n : ℝ) + 1) ^ 3) / 4) :=
    h3Path_cubicHighSnapshot_has_minimalQuadraticSharpClock244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N K C δ hAll using hChoice
  refine ⟨τ, N, K, C, δ, hτ, hLimit, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, hK, hC, hδ, hEnd, hExact, hFloor, hGap, hMinimal⟩
  have hTail (m : ℕ) (hnm : n ≤ m) (hmN : m < N n) :
      ((n : ℝ) + 1) ^ 3 / 4 <
        h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) :=
    h3Path_cubicHighSnapshot_preCrossing_quarterHighTail244
      hH3 hClass (τ n) (hτ n) n m (hCube n)
      (hMinimal m hnm hmN)
  exact ⟨hnN, hK, hC, hδ, hEnd,
    (by simpa only [h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hExact),
    hFloor, (by simpa only [h3PathCubicAnnulusActualGap244] using hGap),
    hMinimal, hTail⟩

end
end PrimeTensor.FirstMonomialTriad
