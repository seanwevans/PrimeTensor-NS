import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSubcutoffTemporalWindow244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# A quantitative temporal persistence frontier for physical H³ dissipation

The four-channel terminal sequence has D_high(n+1,t_n) > (n+1) D_low(n+1,t_n).
The previous module obtained a positive but unquantified neighborhood on
which the normalized low share stays below 1/(n+2), conditional on temporal
continuity of the actual low-frequency and total physical dissipations.

We now retain the HEIGHT as well as the SHARE. Under precisely the same
continuity conditions, there is a neighborhood of each selected snapshot
on which

  D_high(n+1,s) > D_total(t_n)/4.

This is genuine pointwise physical high-frequency dissipation, not merely a
normalized fraction, and it is proved using the exact physical spectral
low+high partition. The positive widths need not be bounded below uniformly.
A separate interval integral lemma explains how a positive-width lower bound
converts to an integrated cost once local interval integrability is known.

No time continuity of full H³ dissipation, quantitative width control,
integrated terminal obstruction, or smooth continuation is inferred from the
basic H³ path assumptions alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3QuantitativeTemporal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3QuantitativeTemporal244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A low-frequency share smaller than `1/R`, with `R ≥ 2` and total
physical dissipation above half its value at the anchor, forces an absolute
high-frequency dissipation lower bound at the same time. -/
theorem h3Path_smallLowShare_and_halfTotal_forces_highQuarter244
    (R L H D D₀ : ℝ)
    (hR : 2 ≤ R) (hD : 0 < D)
    (hAbove : D₀ / 2 < D)
    (hPartition : L + H = D)
    (hSmall : L / D < 1 / R) :
    D₀ / 4 < H := by
  have hRpos : 0 < R := by linarith only [hR]
  have hInv : 1 / R ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hR
  have hRatio : L / D < (1 : ℝ) / 2 :=
    lt_of_lt_of_le hSmall hInv
  have hLowHalf : L < D / 2 := by
    have h := (div_lt_iff₀ hD).1 hRatio
    nlinarith only [h]
  nlinarith only [hAbove, hPartition, hLowHalf]

/-- Joint continuity of the normalized low share and the total dissipation
preserves a strict low-share ceiling AND at least half the selected height.
No uniform modulus of continuity or positive uniform width is assumed. -/
theorem h3Path_continuousLowShare_and_total_localHeightWindow244
    (D F : ℝ → ℝ) (t q : ℝ)
    (hDCont : ContinuousAt D t)
    (hFCont : ContinuousAt F t)
    (hDPos : 0 < D t)
    (hSmall : F t < q) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, dist s t < δ → D t / 2 < D s ∧ F s < q := by
  have hHeightCont : ContinuousAt (fun s => D t / 2 - D s) t :=
    continuousAt_const.sub hDCont
  have hHeightAt : D t / 2 - D t < 0 := by
    linarith only [hDPos]
  obtain ⟨δD, hδD, hWindowD⟩ :=
    h3Path_continuousStrictInequality_localWindow244
      hHeightCont hHeightAt
  obtain ⟨δF, hδF, hWindowF⟩ :=
    h3Path_continuousStrictInequality_localWindow244
      hFCont hSmall
  refine ⟨min δD δF, lt_min hδD hδF, ?_⟩
  intro s hs
  have hsD : dist s t < δD :=
    lt_of_lt_of_le hs (min_le_left _ _)
  have hsF : dist s t < δF :=
    lt_of_lt_of_le hs (min_le_right _ _)
  constructor
  · have h := hWindowD s hsD
    linarith only [h]
  · exact hWindowF s hsF

/-- At a selected four-channel witness, continuity at that physical time
converts the normalized low-frequency estimate into a positive-width
absolute HIGH-frequency dissipation floor at that same radial cutoff.
The window is asserted inside the given physical H³ energy-class tail. -/
theorem h3Path_snapshot_radialLocalization_persists_highQuarter244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hDom : ((n : ℝ) + 1) *
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hLowCont : ContinuousAt (fun s =>
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) t)
    (hDCont : ContinuousAt (velocityH3DissipationAt u) t) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, s ∈ Set.Ioo a T → dist s t < δ →
        velocityH3DissipationAt u t / 4 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
  let R : ℝ := (n : ℝ) + 1
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : ℝ := h3PathActualLowRadialDissipation244 R G
  let H : ℝ := h3PathActualHighRadialDissipation244 R G
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let F : ℝ → ℝ := fun s =>
    h3PathActualLowRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s) / D s
  have hL : 0 ≤ L := by
    dsimp only [L, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hPartition : L + H = D t := by
    dsimp only [L, H, D, G]
    exact h3Path_actualRadialDissipation_partition244 hH3 hClass t ht R
  have hDom' : R * L < H := by
    simpa only [R, L, H, G] using hDom
  have hDPos : 0 < D t := by
    rw [← hPartition]
    exact (h3Path_highDissipationDominance_lowShare_bound244
      R L H (by dsimp only [R]; positivity) hL hDom').1
  have hShare : F t < 1 / (R + 1) := by
    have hBound := h3Path_subcutoff_dissipationShare_bound244
      hH3 hClass t ht n R (by dsimp only [R]; exact le_refl _) hDom
    simpa only [F, D, R,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hBound.2
  have hFCont : ContinuousAt F t := by
    dsimp only [F, D, R]
    exact h3Path_lowDissipationShare_continuousAt_of_parts244
      hH3 ((n : ℝ) + 1) t hLowCont hDCont hDPos
  obtain ⟨δ, hδ, hWindow⟩ :=
    h3Path_continuousLowShare_and_total_localHeightWindow244
      D F t (1 / (R + 1)) hDCont hFCont hDPos hShare
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsNear
  obtain ⟨hAbove, hSmall⟩ := hWindow s hsNear
  let Ls : ℝ := h3PathActualLowRadialDissipation244 R
    (h3AuditActualSpectralVelocityTotal hH3 s)
  let Hs : ℝ := h3PathActualHighRadialDissipation244 R
    (h3AuditActualSpectralVelocityTotal hH3 s)
  have hPart : Ls + Hs = D s := by
    dsimp only [Ls, Hs, D]
    exact h3Path_actualRadialDissipation_partition244 hH3 hClass s hs R
  have hR : 2 ≤ R + 1 := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hn]
  have hResult :=
    h3Path_smallLowShare_and_halfTotal_forces_highQuarter244
      (R + 1) Ls Hs (D s) (D t) hR (lt_trans (by
        have h : 0 < D t / 2 := by linarith only [hDPos]
        exact h) hAbove) hAbove hPart (by
          simpa only [F, Ls, D] using hSmall)
  simpa only [Hs, D, R] using hResult

/-- Scalar integral conversion: a uniform positive lower bound throughout
an ordered finite time interval forces a quantitative integrated cost.
Local interval integrability remains an explicit hypothesis. -/
theorem h3Path_localPositiveHeight_forces_integratedCost244
    (f : ℝ → ℝ) (s t m : ℝ)
    (hst : s ≤ t)
    (hInt : IntervalIntegrable f volume s t)
    (hFloor : ∀ r : ℝ, r ∈ Set.Icc s t → m ≤ f r) :
    (t - s) * m ≤ ∫ r in s..t, f r := by
  have hConst : IntervalIntegrable (fun _ : ℝ => m) volume s t :=
    intervalIntegrable_const
  have hBound := intervalIntegral.integral_mono_on hst hConst hInt hFloor
  simpa [mul_comm] using hBound

/-- Conditional four-channel terminal result. In addition to the original
no-L²-trace hypotheses, time continuity of the actual LOW and TOTAL H³
physical dissipations on the strict energy-class tail supplies positive
windows where high-radial dissipation stays above one fourth its value at
the selected time. No uniform or time-integrated bound is inferred. -/
theorem h3Path_noL2Trace_forces_quantitativeHighDissipationWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T))
    (hLowCont : ∀ n : ℕ, ContinuousOn (fun s =>
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) (Set.Ioo a T)) :
    ∃ (τ : ℕ → ℝ) (δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 0 < δ n) ∧
      (∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Ioo a T →
        dist s (τ n) < δ n →
        velocityH3DissipationAt u (τ n) / 4 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hDom, _hRatio⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialDissipationLocalization244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, s ∈ Set.Ioo a T → dist s (τ n) < δ →
        velocityH3DissipationAt u (τ n) / 4 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
    exact h3Path_snapshot_radialLocalization_persists_highQuarter244
      hH3 hClass (τ n) (hτ n) n (hDom n)
        ((hLowCont n).continuousAt (isOpen_Ioo.mem_nhds (hτ n)))
        (hDCont.continuousAt (isOpen_Ioo.mem_nhds (hτ n)))
  choose δ hδ using hChoice
  exact ⟨τ, δ, hτ, hLimit, (fun n => (hδ n).1),
    (fun n s hs hnear => (hδ n).2 s hs hnear)⟩

end
end PrimeTensor.FirstMonomialTriad
