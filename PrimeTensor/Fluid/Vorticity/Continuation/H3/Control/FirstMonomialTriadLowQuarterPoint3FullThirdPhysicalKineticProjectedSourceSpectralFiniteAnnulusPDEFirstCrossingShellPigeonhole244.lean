import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFirstCrossingLastShell244
import Mathlib.Tactic

/-!
# Width-averaged kinetic shell inside the canonical first crossing

The last-shell overshoot may be arbitrarily small.  Nevertheless the *total*
first-crossing annular dissipation exceeds three quarters of the inner cubic
height.  A finite telescoping argument therefore selects some integer shell
inside the SAME first-crossing band with dissipation larger than the cubic
height divided by the actual shell count.  The already-proved physical
Fourier multiplier transfers that floor to raw kinetic mass on that shell.

This is a width-dependent pigeonhole statement, not a uniform last-shell
lower bound, an upper bound on the first-crossing radius, or a regularity
contradiction.  No terminal full-H³ integrability is assumed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Finite telescoping pigeonhole, without monotonicity assumptions on D.
When `D N - D n > A`, at least one integer shell has increment strictly
larger than `A / (N-n)`.  This multiplicative version avoids division. -/
theorem h3Path_finiteCrossing_exists_widthAveragedShell244
    (D : ℕ → ℝ) (n N : ℕ) (hnN : n < N) (A : ℝ)
    (hCross : A < D N - D n) :
    ∃ m : ℕ, n ≤ m ∧ m < N ∧
      A < ((N - n : ℕ) : ℝ) * (D (m + 1) - D m) := by
  let L : ℝ := ((N - n : ℕ) : ℝ)
  have hSteps : 0 < N - n := by omega
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast hSteps
  by_contra hNo
  have hNoJump (m : ℕ) (hnm : n ≤ m) (hmN : m < N) :
      L * (D (m + 1) - D m) ≤ A := by
    apply le_of_not_gt
    intro hBig
    apply hNo
    exact ⟨m, hnm, hmN, (by simpa only [L] using hBig)⟩
  have hPrefix : ∀ i : ℕ, n ≤ i → i ≤ N →
      L * (D i - D n) ≤ ((i - n : ℕ) : ℝ) * A := by
    intro i hni
    induction i, hni using Nat.le_induction with
    | base =>
        intro _
        simp
    | succ i hni ih =>
        intro hSuccN
        have hiN : i < N := by omega
        have hiLeN : i ≤ N := by omega
        have hIH := ih hiLeN
        have hJump := hNoJump i hni hiN
        have hDiff : (i + 1 - n : ℕ) = (i - n) + 1 := by omega
        have hCast : (((i + 1 - n : ℕ) : ℝ)) =
            ((i - n : ℕ) : ℝ) + 1 := by
          rw [hDiff]
          push_cast
          ring
        rw [hCast]
        nlinarith only [hIH, hJump]
  have hAtN := hPrefix N hnN.le le_rfl
  change L * (D N - D n) ≤ L * A at hAtN
  have hStrict : L * A < L * (D N - D n) :=
    mul_lt_mul_of_pos_left hCross hL
  exact (not_lt_of_ge hAtN) hStrict

/-- A physical minimal first crossing has a quantitatively large shell
somewhere in its finite annulus.  The same shell has positive raw Fourier
kinetic mass, and the *width-times-eighth-power* shell cost exceeds the
three-quarter cubic height.  No positive lower bound on the last shell's
overshoot is used. -/
theorem h3Path_physicalFirstCrossing_exists_widthAveragedKineticShell244
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
          (h3AuditActualSpectralVelocityTotal hH3 t))
    (hMinimal : ∀ m : ℕ, n ≤ m → m < N →
      h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        3 * (((n : ℝ) + 1) ^ 3) / 4) :
    ∃ m : ℕ, n ≤ m ∧ m < N ∧
      3 * (((n : ℝ) + 1) ^ 3) / 4 <
        ((N - n : ℕ) : ℝ) *
          (h3PathActualLowRadialDissipation244 ((m : ℝ) + 2)
              (h3AuditActualSpectralVelocityTotal hH3 t) -
            h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t)) ∧
      0 < h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2)
        (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      3 * (((n : ℝ) + 1) ^ 3) / 4 <
        ((N - n : ℕ) : ℝ) *
          (4 * (((m : ℝ) + 3) ^ 8) *
            h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2)
              (h3AuditActualSpectralVelocityTotal hH3 t)) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let D : ℕ → ℝ := fun j =>
    h3PathActualLowRadialDissipation244 ((j : ℝ) + 1) G
  have hC : 3 * (((n : ℝ) + 1) ^ 3) / 4 < D N - D n := by
    simpa only [D, G] using hCross
  have hMin : ∀ m : ℕ, n ≤ m → m < N →
      D m - D n ≤ 3 * (((n : ℝ) + 1) ^ 3) / 4 := by
    intro m hnm hmN
    simpa only [D, G] using hMinimal m hnm hmN
  obtain ⟨j, hjN, hnj, _, _⟩ :=
    h3Path_firstCrossing_lastShellOvershoot244 D n N hnN hC hMin
  have hnNstrict : n < N := by omega
  obtain ⟨m, hnm, hmN, hAveraged⟩ :=
    h3Path_finiteCrossing_exists_widthAveragedShell244
      D n N hnNstrict (3 * (((n : ℝ) + 1) ^ 3) / 4) hC
  have hShell := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass t ht ((m : ℝ) + 1) ((m : ℝ) + 2)
    (by linarith) (by positivity)
  have hShellBound : D (m + 1) - D m ≤
      4 * (((m : ℝ) + 3) ^ 8) *
        h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2) G := by
    dsimp only [D, G] at hShell ⊢
    convert hShell using 1 <;> push_cast <;> ring
  have hL : 0 ≤ ((N - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hMassCost : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      ((N - n : ℕ) : ℝ) *
        (4 * (((m : ℝ) + 3) ^ 8) *
          h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2) G) :=
    lt_of_lt_of_le hAveraged
      (mul_le_mul_of_nonneg_left hShellBound hL)
  have hMassPos : 0 < h3PathActualBandRawKineticMass244
      ((m : ℝ) + 1) ((m : ℝ) + 2) G := by
    by_contra hNot
    have hMassLe : h3PathActualBandRawKineticMass244
        ((m : ℝ) + 1) ((m : ℝ) + 2) G ≤ 0 := le_of_not_gt hNot
    have hFactor : 0 ≤ ((N - n : ℕ) : ℝ) *
        (4 * (((m : ℝ) + 3) ^ 8)) := by positivity
    have hNonpos : ((N - n : ℕ) : ℝ) *
        (4 * (((m : ℝ) + 3) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((m : ℝ) + 1) ((m : ℝ) + 2) G) ≤ 0 := by
      calc
        _ = (((N - n : ℕ) : ℝ) *
              (4 * (((m : ℝ) + 3) ^ 8))) *
            h3PathActualBandRawKineticMass244
              ((m : ℝ) + 1) ((m : ℝ) + 2) G := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hFactor hMassLe
    have hCpos : 0 < 3 * (((n : ℝ) + 1) ^ 3) / 4 := by positivity
    linarith only [hMassCost, hNonpos, hCpos]
  refine ⟨m, hnm, hmN, ?_, ?_, ?_⟩
  · have hIndex : (((m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) + 2 := by
      push_cast
      ring
    dsimp only [D, G] at hAveraged
    rw [hIndex] at hAveraged
    exact hAveraged
  · simpa only [G] using hMassPos
  · simpa only [G] using hMassCost

/-- The cofinal physical no-terminal-L²-trace first-crossing selector has
an explicitly width-averaged, positive raw-kinetic Fourier shell at EVERY
index.  This avoids choosing a second independent sequence of annuli. -/
theorem h3Path_noL2Trace_minimalFirstCrossing_widthAveragedKineticShell244
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
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ m < N n ∧
        3 * (((n : ℝ) + 1) ^ 3) / 4 <
          ((N n - n : ℕ) : ℝ) *
            (h3PathActualLowRadialDissipation244 ((m : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
              h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
        0 < h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ∧
        3 * (((n : ℝ) + 1) ^ 3) / 4 <
          ((N n - n : ℕ) : ℝ) *
            (4 * (((m : ℝ) + 3) ^ 8) *
              h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ n)))) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_minimalQuadraticSharpClocks_retain_quarterHighTail244
      hH3 hClass hMass hNoTrace
  refine ⟨τ, N, hLimit, hTime, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, _, _, _, _, _, _, hGap, hMinimal, _⟩
  have hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) := by
    dsimp only [h3PathCubicAnnulusActualGap244] at hGap
    linarith only [hGap]
  exact h3Path_physicalFirstCrossing_exists_widthAveragedKineticShell244
    hH3 hClass (τ n) (hTime n) n (N n) hnN hCross hMinimal

end
end PrimeTensor.FirstMonomialTriad
