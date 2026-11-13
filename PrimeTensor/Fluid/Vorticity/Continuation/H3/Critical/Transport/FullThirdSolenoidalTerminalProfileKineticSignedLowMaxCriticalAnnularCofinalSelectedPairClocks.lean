import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalHeightSaturation
import Mathlib.Tactic

/-!
# Selected annular excess: quantitative separation and nonvacuous cofinal clocks

The previously constructed bounded-rectangle kinetic-excess windows required
strict excess even at rho = sigma, and hence have empty snapshot hypotheses.
Here the snapshot family consists of ONE genuine, possibly widely separated
annulus at each cofinal time. The actual sharp highpass, actual kinetic-only
source ceiling, full nonlinear Young-width cost, and actual deficit are kept.

The first result sharpens sigma^2 > 5 rho^2 to a margin-sensitive inequality:
    2 margin <= E_b * (sigma^2 - 5 rho^2).
This follows from the true kinetic source ceiling and highpass kinetic anchor;
there is no invented frequency-localization hypothesis.

The second result selects genuine single-annulus physical persistence windows,
shortens them to be strictly disjoint, and charges the normalized viscous
clock to the full integral and individually to each terminal tail. The
condition is per selected pair, NOT over every annulus in a rectangle.
This repairs the logical vacuity of the full-family continuation route,
but does not establish existence of such selected snapshots or continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A scalar aperture inequality including the exact positive excess margin.
The Bernstein source controls three copies of the kinetic Laplacian term;
the true highpass mass cannot exceed the earlier kinetic anchor. -/
theorem thirdFullKinetic_selectedExcess_apertureMargin_scalar244
    (E S M rho sigma margin : ℝ)
    (hE : 0 ≤ E)
    (hSource : rho ^ 2 * Real.sqrt E ≤ S)
    (hMass : M ≤ E)
    (hExcess : Real.sqrt E * (3 * S) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) * M) :
    2 * margin ≤ E * (sigma ^ 2 - 5 * rho ^ 2) := by
  have hSourceMul :
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) ≤
        Real.sqrt E * (3 * S) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hSource (by norm_num))
      (Real.sqrt_nonneg E)
  have hSourceIdentity :
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) =
        3 * rho ^ 2 * E := by
    calc
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) =
          (Real.sqrt E * Real.sqrt E) * (3 * rho ^ 2) := by ring
      _ = 3 * rho ^ 2 * E := by
        rw [Real.mul_self_sqrt hE]
        ring
  have hSourceLower : 3 * rho ^ 2 * E ≤ Real.sqrt E * (3 * S) := by
    calc
      3 * rho ^ 2 * E =
          Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) := hSourceIdentity.symm
      _ ≤ Real.sqrt E * (3 * S) := hSourceMul
  have hRadialNonneg : 0 ≤ (rho ^ 2 + sigma ^ 2) / 2 := by positivity
  have hMassBound :
      ((rho ^ 2 + sigma ^ 2) / 2) * M ≤
        ((rho ^ 2 + sigma ^ 2) / 2) * E :=
    mul_le_mul_of_nonneg_left hMass hRadialNonneg
  have hGap :
      3 * rho ^ 2 * E + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) * E := by
    linarith only [hSourceLower, hExcess, hMassBound]
  nlinarith only [hGap]

/-- Quantitative angular separation for one actual PHYSICAL annular witness.
In particular, a positive strict margin forces sigma^2 > 5 rho^2. -/
theorem thirdFullPhysical_selectedAnnularExcess_apertureMargin244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin : ℝ)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    2 * margin ≤ velocityH3Energy0At u b *
      (sigma ^ 2 - 5 * rho ^ 2) := by
  have hE : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hSource :
      rho ^ 2 * Real.sqrt (velocityH3Energy0At u b) ≤
        thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b) := by
    unfold thirdFullPhysicalKineticLowBandSourceCeiling244
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hMass := thirdFullPhysical_actualSharpHighMass_le_kineticAnchor244
    hH3 hClass b hb x hx rho
  exact thirdFullKinetic_selectedExcess_apertureMargin_scalar244
    (velocityH3Energy0At u b)
    (thirdFullPhysicalKineticLowBandSourceCeiling244 rho
      (velocityH3Energy0At u b))
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    rho sigma margin hE hSource hMass hExcess

/-- A bounded outer/inner aspect ratio forces a strictly positive highpass
kinetic fraction: even without any highpass tightness theorem, the selected
excess inequality entails 6 E <= (1 + K^2) M. This is the precise new
quantitative condition a moving-frequency spectral escape argument must meet. -/
theorem thirdFullKinetic_selectedExcess_boundedAspect_massFraction_scalar244
    (E S M rho sigma K margin : ℝ)
    (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hRho : 0 < rho) (hSigma : 0 ≤ sigma)
    (hK : 0 ≤ K) (hAspect : sigma ≤ K * rho)
    (hSource : rho ^ 2 * Real.sqrt E ≤ S)
    (hMargin : 0 ≤ margin)
    (hExcess : Real.sqrt E * (3 * S) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) * M) :
    6 * E ≤ (1 + K ^ 2) * M := by
  have hSourceMul :
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) ≤
        Real.sqrt E * (3 * S) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hSource (by norm_num))
      (Real.sqrt_nonneg E)
  have hSourceIdentity :
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) =
        3 * rho ^ 2 * E := by
    calc
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) =
          (Real.sqrt E * Real.sqrt E) * (3 * rho ^ 2) := by ring
      _ = 3 * rho ^ 2 * E := by
        rw [Real.mul_self_sqrt hE]
        ring
  have hSourceLower : 3 * rho ^ 2 * E ≤ Real.sqrt E * (3 * S) := by
    calc
      3 * rho ^ 2 * E =
          Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) := hSourceIdentity.symm
      _ ≤ Real.sqrt E * (3 * S) := hSourceMul
  have hSigmaSq : sigma ^ 2 ≤ (K * rho) ^ 2 :=
    pow_le_pow_left₀ hSigma hAspect 2
  have hRadius :
      (rho ^ 2 + sigma ^ 2) / 2 ≤
        ((1 + K ^ 2) / 2) * rho ^ 2 := by
    nlinarith only [hSigmaSq]
  have hUpper :
      ((rho ^ 2 + sigma ^ 2) / 2) * M ≤
        (((1 + K ^ 2) / 2) * rho ^ 2) * M :=
    mul_le_mul_of_nonneg_right hRadius hM
  have hBound :
      3 * rho ^ 2 * E ≤
        (((1 + K ^ 2) / 2) * rho ^ 2) * M := by
    linarith only [hSourceLower, hExcess, hUpper, hMargin]
  have hScaled :
      (6 * E) * rho ^ 2 ≤ ((1 + K ^ 2) * M) * rho ^ 2 := by
    nlinarith only [hBound]
  by_contra hNot
  have hReverse : (1 + K ^ 2) * M < 6 * E := lt_of_not_ge hNot
  have hStrict := mul_lt_mul_of_pos_right hReverse (pow_pos hRho 2)
  exact (not_lt_of_ge hScaled) hStrict

/-- For the original sharp PHYSICAL highpass at a strict time, a positive
excess witness of bounded annular aspect forces a fixed fraction of the
earlier kinetic anchor to remain in the highpass. -/
theorem thirdFullPhysical_selectedExcess_boundedAspect_highpassFraction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma K margin : ℝ)
    (hRho : 0 < rho) (hOrder : rho ≤ sigma)
    (hK : 0 ≤ K) (hAspect : sigma ≤ K * rho)
    (hMargin : 0 ≤ margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    6 * velocityH3Energy0At u b ≤
      (1 + K ^ 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho := by
  have hE : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hMass :
      0 ≤ thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho :=
    sq_nonneg _
  have hSource :
      rho ^ 2 * Real.sqrt (velocityH3Energy0At u b) ≤
        thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b) := by
    unfold thirdFullPhysicalKineticLowBandSourceCeiling244
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  exact thirdFullKinetic_selectedExcess_boundedAspect_massFraction_scalar244
    (velocityH3Energy0At u b)
    (thirdFullPhysicalKineticLowBandSourceCeiling244 rho
      (velocityH3Energy0At u b))
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    rho sigma K margin hE hMass hRho (hRho.le.trans hOrder)
    hK hAspect hSource hMargin hExcess

/-- Strict selected excess at a uniformly bounded outer/inner aspect ratio
is incompatible with vanishing actual highpass kinetic mass. This is the
precise tightness-vs-annular-excess obstruction needed to connect the existing
terminal physical L² trace to moving frequency cutoffs. Tightness is an
explicit hypothesis here; it is NOT inferred merely from cofinal time. -/
theorem thirdFullPhysical_selectedBoundedAspect_noHighpassTightness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hOrder : ∀ k : ℕ, rho k ≤ sigma k)
    (K : ℝ) (hK : 0 ≤ K)
    (hAspect : ∀ k : ℕ, sigma k ≤ K * rho k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
        ((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k)) :
    ¬ Tendsto (fun k : ℕ =>
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
        atTop (𝓝 (0 : ℝ)) := by
  intro hZero
  have hEpos : 0 < velocityH3Energy0At u b :=
    thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244
      hH3 hClass b hb (x 0) (hx 0) (rho 0) (sigma 0)
      (margin 0) (hMargin 0) (hExcess 0)
  let c : ℝ := (6 * velocityH3Energy0At u b) / (1 + K ^ 2)
  have hDen : 0 < 1 + K ^ 2 := by positivity
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos (by norm_num) hEpos) hDen
  have hSmall : ∀ᶠ k : ℕ in atTop,
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k) < c :=
    hZero.eventually (eventually_lt_nhds hc)
  obtain ⟨k, hk⟩ := hSmall.exists
  have hMass := thirdFullPhysical_selectedExcess_boundedAspect_highpassFraction244
    hH3 hClass b hb (x k) (hx k) (rho k) (sigma k)
    K (margin k) (hRho k) (hOrder k) hK
    (hAspect k) (hMargin k).le (hExcess k)
  have hLower : c ≤
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k) := by
    dsimp only [c]
    apply (div_le_iff₀ hDen).2
    simpa only [mul_comm] using hMass
  exact (not_lt_of_ge hLower) hk

/-- A COFINAL selected-pair replacement for the logically empty rectangular
family. Each snapshot supplies strict excess and a positive deficit at just
ONE actual annulus, which must automatically be widely separated. The actual
physical dissipation on the extracted disjoint intervals is summable, and
its terminal tails vanish. No width noncompression is assumed. -/
theorem thirdFullPhysical_cofinalSelectedAnnularSnapshots_disjointClocks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hStep : ∀ k : ℕ, x k < x (k + 1))
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hOrder : ∀ k : ℕ, rho k ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
        ((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
    (hPeak : ∀ k : ℕ,
      2 * epsilon k ≤
        thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b (x k) (rho k) (sigma k)) :
    ∃ delta : ℕ → ℝ,
      (∀ k : ℕ,
        0 < delta k ∧ x k + delta k < x (k + 1) ∧
          x k + delta k < T ∧
          ∀ s : ℝ, s ∈ Set.Icc (x k) (x k + delta k) →
            Real.sqrt (velocityH3Energy0At u b) *
                (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                  (rho k) (velocityH3Energy0At u b)) ≤
              ((rho k ^ 2 + sigma k ^ 2) / 2) *
                thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) ∧
            epsilon k ≤
              thirdFullPhysicalActualAnnularKineticDeficit244
                hH3 b s (rho k) (sigma k)) ∧
      (∀ k : ℕ, 2 * margin k ≤ velocityH3Energy0At u b *
        (sigma k ^ 2 - 5 * rho k ^ 2)) ∧
      (∀ k : ℕ, 5 * rho k ^ 2 < sigma k ^ 2) ∧
      Summable (fun k : ℕ =>
        delta k * (epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244
            u b (rho k) (epsilon k))) ∧
      Tendsto (fun k : ℕ =>
        delta k * (epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244
            u b (rho k) (epsilon k))) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          delta k * (epsilon k /
            thirdFullPhysicalAnnularCapClockFactor244
              u b (rho k) (epsilon k))) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ k : ℕ,
        delta k * (epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244
            u b (rho k) (epsilon k)) ≤
        ∫ r in x k..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in x k..(x k + delta k),
          velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) := by
  classical
  have hWin (k : ℕ) :
      ∃ d : ℝ, 0 < d ∧ x k + d < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (x k) (x k + d) →
          Real.sqrt (velocityH3Energy0At u b) *
              (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                (rho k) (velocityH3Energy0At u b)) ≤
            ((rho k ^ 2 + sigma k ^ 2) / 2) *
              thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) ∧
          epsilon k ≤
            thirdFullPhysicalActualAnnularKineticDeficit244
              hH3 b s (rho k) (sigma k)) ∧
        d * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r := by
    have hStrict :
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            (rho k) (velocityH3Energy0At u b)) <
        ((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k) := by
      linarith only [hExcess k, hMargin k]
    exact thirdFullPhysical_annularDeficit_snapshotRightWindowCharge_auto244
      hH3 hClass hDInt b hb (rho k) (sigma k)
      (hRho k).le (hOrder k) (x k) (hx k)
      (epsilon k) (hEps k) hStrict (hPeak k)
  let d₀ : ℕ → ℝ := fun k => Classical.choose (hWin k)
  have hd₀ (k : ℕ) :
      0 < d₀ k ∧ x k + d₀ k < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (x k) (x k + d₀ k) →
          Real.sqrt (velocityH3Energy0At u b) *
              (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                (rho k) (velocityH3Energy0At u b)) ≤
            ((rho k ^ 2 + sigma k ^ 2) / 2) *
              thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) ∧
          epsilon k ≤
            thirdFullPhysicalActualAnnularKineticDeficit244
              hH3 b s (rho k) (sigma k)) ∧
        d₀ k * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r :=
    Classical.choose_spec (hWin k)
  let delta : ℕ → ℝ :=
    fun k => min (d₀ k) ((x (k + 1) - x k) / 2)
  have hd (k : ℕ) : 0 < delta k := by
    change 0 < min (d₀ k) ((x (k + 1) - x k) / 2)
    exact lt_min (hd₀ k).1 (by linarith only [hStep k])
  have hRawBound (k : ℕ) : delta k ≤ d₀ k := min_le_left _ _
  have hGapBound (k : ℕ) :
      delta k ≤ (x (k + 1) - x k) / 2 := min_le_right _ _
  have hSeparate (k : ℕ) : x k + delta k < x (k + 1) := by
    linarith only [hGapBound k, hStep k]
  have hEnd (k : ℕ) : x k + delta k < T := by
    linarith only [hRawBound k, (hd₀ k).2.1]
  have hPreserved (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            (rho k) (velocityH3Energy0At u b)) ≤
        ((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) ∧
      epsilon k ≤
        thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s (rho k) (sigma k) := by
    have hsRaw : s ∈ Set.Icc (x k) (x k + d₀ k) :=
      ⟨hs.1, by linarith only [hs.2, hRawBound k]⟩
    exact (hd₀ k).2.2.1 s hsRaw
  have hStart (k : ℕ) : a ≤ x k :=
    (lt_trans hb.1 (hx k).1).le
  have hTimes (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      s ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le (hx k).1 hs.1,
      lt_of_le_of_lt hs.2 (hEnd k)⟩
  have hCharge :=
    thirdFullPhysical_disjointAnnularDeficit_selfCalibratedSummable244
      hH3 hClass b hb hDInt x delta rho sigma epsilon
      (fun k => (hRho k).le) hOrder hEps
      hStart (fun k => (hd k).le)
      (fun k => (hEnd k).le)
      (fun k => (hSeparate k).le)
      hTimes (fun k s hs => (hPreserved k s hs).1)
      (fun k s hs => (hPreserved k s hs).2)
  have hInside (k : ℕ) :
      a ≤ x k ∧ x k ≤ x k + delta k ∧ x k + delta k ≤ T :=
    ⟨hStart k, le_add_of_nonneg_right (hd k).le, (hEnd k).le⟩
  have hActualTail :=
    thirdFull_scalar_cofinalSubintervalCost_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt (velocityH3DissipationAt_nonneg u)
      x (fun k => x k + delta k) hInside hCofinal
  have hPoint (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (rho k) (epsilon k) ≤ velocityH3DissipationAt u s := by
    have hBoth := hPreserved k s hs
    exact thirdFullPhysical_annularDeficit_forces_selfCalibratedClock244
      hH3 hClass b hb (rho k) (sigma k)
      (hRho k).le (hOrder k) s (hTimes k s hs)
      (epsilon k) (hEps k) hBoth.1 hBoth.2
  have hTailCost (k : ℕ) :
      delta k * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (rho k) (epsilon k)) ≤
        ∫ r in x k..T, velocityH3DissipationAt u r := by
    exact thirdFull_scalar_rightWindowHeight_le_terminalTail244
      (velocityH3DissipationAt u) a T (x k) (delta k)
      (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (rho k) (epsilon k))
      hClass.terminal_start.2 (hStart k) (hx k).2
      (hd k) (hEnd k).le hDInt
      (velocityH3DissipationAt_nonneg u) (hPoint k)
  have hAperture (k : ℕ) :
      2 * margin k ≤ velocityH3Energy0At u b *
        (sigma k ^ 2 - 5 * rho k ^ 2) :=
    thirdFullPhysical_selectedAnnularExcess_apertureMargin244
      hH3 hClass b hb (x k) (hx k)
      (rho k) (sigma k) (margin k) (hExcess k)
  have hSeparated (k : ℕ) :
      5 * rho k ^ 2 < sigma k ^ 2 :=
    thirdFullPhysical_strictAnnularExcess_forces_radialSeparation244
      hH3 hClass b hb (x k) (hx k)
      (rho k) (sigma k) (margin k) (hMargin k) (hExcess k)
  refine ⟨delta, ?_, hAperture, hSeparated, hCharge.1,
    hCharge.2.1, hCharge.2.2, hTailCost, hActualTail⟩
  intro k
  exact ⟨hd k, hSeparate k, hEnd k, hPreserved k⟩

end
end PrimeTensor.FirstMonomialTriad
