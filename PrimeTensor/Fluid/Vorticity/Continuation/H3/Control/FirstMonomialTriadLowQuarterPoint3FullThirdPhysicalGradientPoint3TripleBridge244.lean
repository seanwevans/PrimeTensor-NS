import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientLinfTrace244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSpatialPairingBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientPathBridge244
import Mathlib.Tactic

/-!
# Physical H³ gradient: the L²–L²–L∞ triple on Point3

After strong L² convergence of the real Schwartz third derivatives and
strong L∞ convergence of the first derivatives, the remaining issue is
identifying the trilinear functional with the OLD physical spatial integral.

The first-derivative L∞ class has an actual pointwise representative from the
physical velocity. The third-order L² representatives were identified in the
previous signed-slot spatial bridge for EVERY H³ jet index. Together they
identify the complete 3–3–1 product almost everywhere. The exact
volume-preserving carrier conversion then identifies its old Point3 integral.

No third-derivative L⁴ bound, arbitrary physical Schwartz realization,
nonlinear trace premise, or PDE continuation conclusion is assumed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance gradientPoint3AxisFintype244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance gradientPoint3MeasureSpace244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance gradientPoint3Fact2244 : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩
local instance gradientPoint3FactTop244 : Fact (1 ≤ (∞ : ENNReal)) :=
  ⟨by simp⟩

/-- One OLD, fully ordered 3–3–1 gradient density on physical Point3.
The first and second third-jet components may differ. -/
noncomputable def h3OldPhysicalGradientTripleDensity244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j p q : Fin 3)
    (a b c d e f r : A3) : Point3 → ℝ :=
  fun x =>
    (spatial3.d a (spatial3.d b (spatial3.d c
      (loggedVelocityComponent u t (h3AxisOfFin3 j)))) x) *
    ((spatial3.d d (spatial3.d e (spatial3.d f
      (loggedVelocityComponent u t (h3AxisOfFin3 p)))) x) *
     (spatial3.d r (loggedVelocityComponent u t (h3AxisOfFin3 q)) x))

/-- The constructed L∞ class of the physical first derivative is exactly
its pointwise old derivative, a.e. on the Euclidean carrier. -/
theorem h3ActualPhysicalFirstJetLinf_ae_eq_oldField244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (q : Fin 3) (r : A3) :
    (h3ActualPhysicalFirstJetLinf244 hNS ht hFourier q r : V3 → ℝ)
      =ᵐ[(volume : Measure V3)]
    (fun x : V3 => spatial3.d r
      (loggedVelocityComponent u t (h3AxisOfFin3 q)) (WithLp.ofLp x)) := by
  unfold h3ActualPhysicalFirstJetLinf244
  exact MemLp.coeFn_toLp _

/-- The abstract two-L²/one-L∞ product has the correct OLD Point3 density
as a Fourier-space a.e. representative, with no choice of Schwartz family. -/
theorem h3ActualGradientTripleDensity_ae_eq_oldPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j p q : Fin 3) (a b c d e f r : A3) :
    (fun x : V3 =>
      (h3ActualThirdJetOnFourierCarrier244 hInt hMeas j a b c : V3 → ℝ) x *
        ((h3ActualThirdJetOnFourierCarrier244 hInt hMeas p d e f : V3 → ℝ) x *
         (h3ActualPhysicalFirstJetLinf244 hNS ht hFourier q r : V3 → ℝ) x))
      =ᵐ[(volume : Measure V3)]
    (fun x : V3 => h3OldPhysicalGradientTripleDensity244
      u t j p q a b c d e f r (WithLp.ofLp x)) := by
  have hA := h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244
    hInt hMeas
    (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b) (h3ClassicalizationFinOfAxis c))
  have hB := h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244
    hInt hMeas
    (h3JetSlot3 p (h3ClassicalizationFinOfAxis d)
      (h3ClassicalizationFinOfAxis e) (h3ClassicalizationFinOfAxis f))
  have hC := h3ActualPhysicalFirstJetLinf_ae_eq_oldField244
    hNS ht hFourier q r
  filter_upwards [hA, hB, hC] with x ha hb hc
  dsimp only [h3ActualThirdJetOnFourierCarrier244]
  rw [ha, hb, hc]
  simp only [h3OldPhysicalGradientTripleDensity244,
    velocityH3JetFieldAt, h3JetSlot3,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis]

/-- Genuine signed trilinear functional equals the ORIGINAL physical
third-third-first Lebesgue integral, with no normalization factors. -/
theorem h3ActualGradientLpTriple_eq_oldPhysicalIntegral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j p q : Fin 3) (a b c d e f r : A3) :
    h3PhysicalGradientLpTriple244
      (h3ActualThirdJetOnFourierCarrier244 hInt hMeas j a b c)
      (h3ActualThirdJetOnFourierCarrier244 hInt hMeas p d e f)
      (h3ActualPhysicalFirstJetLinf244 hNS ht hFourier q r) =
        ∫ x : Point3, h3OldPhysicalGradientTripleDensity244
          u t j p q a b c d e f r x := by
  have hAE := h3ActualGradientTripleDensity_ae_eq_oldPhysical244
    hNS ht hFourier j p q a b c d e f r
  have hEmb : MeasurableEmbedding (WithLp.ofLp : V3 → Point3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : A3 => ℝ)).toHomeomorph.measurableEmbedding
  rw [h3PhysicalGradientLpTriple_eq_integral244]
  calc
    (∫ x : V3,
      (h3ActualThirdJetOnFourierCarrier244 hInt hMeas j a b c : V3 → ℝ) x *
        ((h3ActualThirdJetOnFourierCarrier244 hInt hMeas p d e f : V3 → ℝ) x *
         (h3ActualPhysicalFirstJetLinf244 hNS ht hFourier q r : V3 → ℝ) x)) =
      ∫ x : V3, h3OldPhysicalGradientTripleDensity244
        u t j p q a b c d e f r (WithLp.ofLp x) :=
      integral_congr_ae hAE
    _ = ∫ x : Point3, h3OldPhysicalGradientTripleDensity244
        u t j p q a b c d e f r x :=
      (PiLp.volume_preserving_ofLp A3).integral_comp hEmb _

/-- For three actual Schwartz maps, `toLp` preserves the exact real triple
integral after passing to L², L², and L∞ equivalence classes. -/
theorem h3SchwartzGradientLpTriple_eq_integral244
    (A B C : SchwartzMap V3 ℝ) :
    h3PhysicalGradientLpTriple244
      (A.toLp 2 (volume : Measure V3))
      (B.toLp 2 (volume : Measure V3))
      (C.toLp (∞ : ENNReal) (volume : Measure V3)) =
      ∫ x : V3, A x * (B x * C x) := by
  rw [h3PhysicalGradientLpTriple_eq_integral244]
  apply integral_congr_ae
  filter_upwards [A.coeFn_toLp 2 (volume : Measure V3),
    B.coeFn_toLp 2 (volume : Measure V3),
    C.coeFn_toLp (∞ : ENNReal) (volume : Measure V3)] with x ha hb hc
  rw [ha, hb, hc]

/-- Any matched spectral Schwartz sequence converges, in one complete
3–3–1 slot, to the actual OLD spatial Point3 triple integral. -/
theorem h3MatchedSchwartz_gradientTripleIntegral_tendsto_oldPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (j p q : Fin 3) (a b c d e f r : A3) :
    Tendsto (fun n =>
      ∫ x : V3,
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (∂_{h3FourierAxisDirection c}
              (F.family.approximants n (h3AxisOfFin3 j))))) x *
          ((∂_{h3FourierAxisDirection d}
            (∂_{h3FourierAxisDirection e}
              (∂_{h3FourierAxisDirection f}
                (F.family.approximants n (h3AxisOfFin3 p))))) x *
           (∂_{h3FourierAxisDirection r}
             (F.family.approximants n (h3AxisOfFin3 q))) x))
      atTop (𝓝 (∫ x : Point3,
        h3OldPhysicalGradientTripleDensity244
          u t j p q a b c d e f r x)) := by
  have hLimit := h3MatchedSchwartz_physicalGradientLpTriple_tendsto244
    hNS ht hFourier F j p q a b c d e f r
  have hPointwise (n : ℕ) :=
    h3SchwartzGradientLpTriple_eq_integral244
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (F.family.approximants n (h3AxisOfFin3 j)))))
      (∂_{h3FourierAxisDirection d}
        (∂_{h3FourierAxisDirection e}
          (∂_{h3FourierAxisDirection f}
            (F.family.approximants n (h3AxisOfFin3 p)))))
      (∂_{h3FourierAxisDirection r}
        (F.family.approximants n (h3AxisOfFin3 q)))
  have hTarget := h3ActualGradientLpTriple_eq_oldPhysicalIntegral244
    hNS ht hFourier j p q a b c d e f r
  -- The equality of the entire indexed scalar sequence prevents Lean
  -- from unfolding the two Lp bilinear operators during limit rewriting.
  have hSeq :
      (fun n => h3PhysicalGradientLpTriple244
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (∂_{h3FourierAxisDirection c}
              (F.family.approximants n (h3AxisOfFin3 j))))).toLp
                2 (volume : Measure V3))
        ((∂_{h3FourierAxisDirection d}
          (∂_{h3FourierAxisDirection e}
            (∂_{h3FourierAxisDirection f}
              (F.family.approximants n (h3AxisOfFin3 p))))).toLp
                2 (volume : Measure V3))
        ((∂_{h3FourierAxisDirection r}
          (F.family.approximants n (h3AxisOfFin3 q))).toLp
                (∞ : ENNReal) (volume : Measure V3))) =
      (fun n => ∫ x : V3,
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (∂_{h3FourierAxisDirection c}
              (F.family.approximants n (h3AxisOfFin3 j))))) x *
          ((∂_{h3FourierAxisDirection d}
            (∂_{h3FourierAxisDirection e}
              (∂_{h3FourierAxisDirection f}
                (F.family.approximants n (h3AxisOfFin3 p))))) x *
           (∂_{h3FourierAxisDirection r}
             (F.family.approximants n (h3AxisOfFin3 q))) x)) := by
    funext n
    exact hPointwise n
  rw [hSeq, hTarget] at hLimit
  exact hLimit


/-- Restore the exact factor TWO used by `spatialEnergyPairing` when a
Schwartz gradient triple is transported to the old physical Point3 integral. -/
theorem h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier))
    (j p q : Fin 3) (a b c d e f r : A3) :
    Tendsto (fun n => fullGradientTriple244
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c}
            (F.family.approximants n (h3AxisOfFin3 j)))))
      (∂_{h3FourierAxisDirection d}
        (∂_{h3FourierAxisDirection e}
          (∂_{h3FourierAxisDirection f}
            (F.family.approximants n (h3AxisOfFin3 p)))))
      (∂_{h3FourierAxisDirection r}
        (F.family.approximants n (h3AxisOfFin3 q))))
      atTop (𝓝 (2 * (∫ x : Point3,
        h3OldPhysicalGradientTripleDensity244
          u t j p q a b c d e f r x))) := by
  have h := h3MatchedSchwartz_gradientTripleIntegral_tendsto_oldPhysical244
    hNS ht hFourier F j p q a b c d e f r
  have hTwo :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
      atTop (𝓝 (2 : ℝ))).mul h
  simpa only [fullGradientTriple244] using hTwo

end
end PrimeTensor.FirstMonomialTriad
