import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDeficitUniformSlope
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCofinalGapCompression
import Mathlib.Tactic

/-!
# Cofinal extraction of disjoint actual annular deficit clocks

The previous finite-radius result selects a single physical right-time
window simultaneously preserving strict kinetic excess and a positive
annular deficit throughout every prescribed bounded-radius annular family.
It does not assert any uniformity as the outer radius goes to infinity.

Here the family may depend on a cofinal index k, with no common upper
frequency ceiling and no common positive margin. Given the TRUE strict
physical snapshot margins at each index, we take the finite-radius window
there, then shorten it to half the next time gap. The shortened physical
intervals are disjoint, preserve the ORIGINAL deficit and excess, and can
be charged by the existing physical H3 disjoint-clock summability theorem.
Their genuine H3 dissipation integrals also converge to zero as their start
times approach the finite terminal endpoint.

This theorem never promotes the snapshot margin hypotheses to conclusions
of Navier--Stokes. In particular it does not prove noncompression of the
cofinal clock heights or widths, nor terminal H3 continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Every cofinal sequence of snapshots satisfying *per-index*, uniform
actual kinetic-excess and deficit margins on a finite annular family
has a constructively shortened sequence of disjoint physical clock windows.
The radii R(k), positive margins and positive deficits may vary arbitrarily
with k. The exact self-calibrated viscous charges are summable and tend to
zero, while the actual dissipation spent on those windows vanishes.

The hypotheses do not assert any missing frequency-uniform margin or width. -/
theorem thirdFullPhysical_cofinalAnnularUniformSnapshots_disjointSummable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x radiusMin R margin epsilon rhoSel sigmaSel : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hStep : ∀ k : ℕ, x k < x (k + 1))
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRadiusMin : ∀ k : ℕ, 0 < radiusMin k)
    (hRadiusMax : ∀ k : ℕ, radiusMin k ≤ R k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hSelected : ∀ k : ℕ,
      radiusMin k ≤ rhoSel k ∧ rhoSel k ≤ sigmaSel k ∧
        sigmaSel k ≤ R k)
    (hExcess : ∀ k : ℕ, ∀ rho sigma : ℝ,
      radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin k ≤
          ((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (hPeak : ∀ k : ℕ, ∀ rho sigma : ℝ,
      radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
        2 * epsilon k ≤
          thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b (x k) rho sigma) :
    ∃ delta : ℕ → ℝ,
      (∀ k : ℕ,
        0 < delta k ∧ x k + delta k < x (k + 1) ∧
          x k + delta k < T ∧
          ∀ s : ℝ, s ∈ Set.Icc (x k) (x k + delta k) →
            ∀ rho sigma : ℝ,
              radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
                Real.sqrt (velocityH3Energy0At u b) *
                    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                      rho (velocityH3Energy0At u b)) + margin k ≤
                  ((rho ^ 2 + sigma ^ 2) / 2) *
                    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
                epsilon k ≤
                  thirdFullPhysicalActualAnnularKineticDeficit244
                    hH3 b s rho sigma) ∧
      Summable (fun k : ℕ =>
        delta k * (epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244
            u b (rhoSel k) (epsilon k))) ∧
      Tendsto (fun k : ℕ =>
        delta k * (epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244
            u b (rhoSel k) (epsilon k))) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          delta k * (epsilon k /
            thirdFullPhysicalAnnularCapClockFactor244
              u b (rhoSel k) (epsilon k))) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in x k..(x k + delta k),
          velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) := by
  classical
  have hAt (k : ℕ) : x k ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 (hx k).1), (hx k).2⟩
  have hWin (k : ℕ) :
      ∃ d : ℝ, 0 < d ∧ x k + d < T ∧
        ∀ s : ℝ, s ∈ Set.Icc (x k) (x k + d) →
          ∀ rho sigma : ℝ,
            radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
              Real.sqrt (velocityH3Energy0At u b) *
                  (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                    rho (velocityH3Energy0At u b)) + margin k ≤
                ((rho ^ 2 + sigma ^ 2) / 2) *
                  thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
              epsilon k ≤
                thirdFullPhysicalActualAnnularKineticDeficit244
                  hH3 b s rho sigma := by
    exact thirdFullPhysical_actualAnnularDeficit_uniformFloorRightWindow244
      hH3 b (radiusMin k) (R k) (x k) (margin k) (epsilon k)
      (hRadiusMin k) (hRadiusMax k) (hAt k)
      (hMargin k) (hEps k) (hExcess k) (hPeak k)
  let d₀ : ℕ → ℝ := fun k => Classical.choose (hWin k)
  have hd₀ (k : ℕ) :
      0 < d₀ k ∧ x k + d₀ k < T ∧
        ∀ s : ℝ, s ∈ Set.Icc (x k) (x k + d₀ k) →
          ∀ rho sigma : ℝ,
            radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
              Real.sqrt (velocityH3Energy0At u b) *
                  (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                    rho (velocityH3Energy0At u b)) + margin k ≤
                ((rho ^ 2 + sigma ^ 2) / 2) *
                  thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
              epsilon k ≤
                thirdFullPhysicalActualAnnularKineticDeficit244
                  hH3 b s rho sigma :=
    Classical.choose_spec (hWin k)
  let delta : ℕ → ℝ :=
    fun k => min (d₀ k) ((x (k + 1) - x k) / 2)
  have hd (k : ℕ) : 0 < delta k := by
    change 0 < min (d₀ k) ((x (k + 1) - x k) / 2)
    exact lt_min (hd₀ k).1 (by linarith only [hStep k])
  have hLeRaw (k : ℕ) : delta k ≤ d₀ k :=
    min_le_left _ _
  have hLeGap (k : ℕ) :
      delta k ≤ (x (k + 1) - x k) / 2 :=
    min_le_right _ _
  have hSeparate (k : ℕ) : x k + delta k < x (k + 1) := by
    linarith only [hLeGap k, hStep k]
  have hEnd (k : ℕ) : x k + delta k < T := by
    linarith only [hLeRaw k, (hd₀ k).2.1]
  have hPreserved (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k))
      (rho sigma : ℝ)
      (hRad : radiusMin k ≤ rho) (hOrder : rho ≤ sigma)
      (hUpper : sigma ≤ R k) :
      Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + margin k ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
      epsilon k ≤
        thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s rho sigma := by
    have hsRaw : s ∈ Set.Icc (x k) (x k + d₀ k) :=
      ⟨hs.1, by linarith only [hs.2, hLeRaw k]⟩
    exact (hd₀ k).2.2 s hsRaw rho sigma hRad hOrder hUpper
  have hRho (k : ℕ) : 0 ≤ rhoSel k :=
    (hRadiusMin k).le.trans (hSelected k).1
  have hOrder (k : ℕ) : rhoSel k ≤ sigmaSel k :=
    (hSelected k).2.1
  have hStart (k : ℕ) : a ≤ x k :=
    (lt_trans hb.1 (hx k).1).le
  have hWidth (k : ℕ) : 0 ≤ delta k := (hd k).le
  have hEndLe (k : ℕ) : x k + delta k ≤ T :=
    (hEnd k).le
  have hSepLe (k : ℕ) : x k + delta k ≤ x (k + 1) :=
    (hSeparate k).le
  have hTimes (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      s ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le (hx k).1 hs.1,
      lt_of_le_of_lt hs.2 (hEnd k)⟩
  have hSelectedExcess (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rhoSel k) (velocityH3Energy0At u b)) ≤
        ((rhoSel k ^ 2 + sigmaSel k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rhoSel k) := by
    have hM := (hPreserved k s hs (rhoSel k) (sigmaSel k)
      (hSelected k).1 (hSelected k).2.1 (hSelected k).2.2).1
    linarith only [hM, hMargin k]
  have hSelectedFloor (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      epsilon k ≤
        thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s (rhoSel k) (sigmaSel k) :=
    (hPreserved k s hs (rhoSel k) (sigmaSel k)
      (hSelected k).1 (hSelected k).2.1 (hSelected k).2.2).2
  have hCharge :=
    thirdFullPhysical_disjointAnnularDeficit_selfCalibratedSummable244
      hH3 hClass b hb hDInt
      x delta rhoSel sigmaSel epsilon
      hRho hOrder hEps hStart hWidth hEndLe hSepLe
      hTimes hSelectedExcess hSelectedFloor
  have hInside (k : ℕ) :
      a ≤ x k ∧ x k ≤ x k + delta k ∧ x k + delta k ≤ T :=
    ⟨hStart k, le_add_of_nonneg_right (hd k).le, (hEnd k).le⟩
  have hActualTail :=
    thirdFull_scalar_cofinalSubintervalCost_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt (velocityH3DissipationAt_nonneg u)
      x (fun k => x k + delta k) hInside hCofinal
  refine ⟨delta, ?_, hCharge.1, hCharge.2.1, hCharge.2.2, hActualTail⟩
  intro k
  exact ⟨hd k, hSeparate k, hEnd k,
    fun s hs rho sigma hRad hOrder hUpper =>
      hPreserved k s hs rho sigma hRad hOrder hUpper⟩

end
end PrimeTensor.FirstMonomialTriad
