import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalRadialShellFluxGain
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzOrderedIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdPhysicalJetEnergyQuarticBridge
import Mathlib.Tactic

/-!
# True integrated annular gain with an explicit off-shell remainder

The previous theorem controls the actual complex sixth-power H³ transfer
POINTWISE by the spread of squared Fourier radii.  On an arbitrary measurable
subset of the real six-dimensional triad carrier whose three radii all lie
in [lo, hi], its integral gains the factor `3 * hi² * (hi - lo)`.

The cost is the INTEGRAL of the exact three-channel complex contraction
budget, not an invented universal H³ energy bound.  The budget's local
integrability is an explicit hypothesis.  The full flux splits EXACTLY
into the near-annulus contribution and its off-shell complement; the latter
is not discarded.  Finally the split passes through any existing solenoidal
Schwartz H³ transport limit, including the physical snapshot construction.

This is a rigorous localized gain and a quantitative off-shell alternative;
it does not assert a universal bound on the budget or infer regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeSolenoidalAnnularIntegral244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The three *actual* Fourier-polarization contractions at a real triad.
Unlike a crude amplitude upper bound, it retains the exact p,q,r labels
and complex Fourier field on the momentum-conservation manifold. -/
noncomputable def thirdFullSchwartzSixthFluxBudget244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) : ℝ :=
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  let U := h3SchwartzTriadPolarization v
  thirdFullComplexSixthFluxContractionBudget244 p q r (U p) (U q) (U r)

/-- The complex contraction budget is pointwise nonnegative. -/
theorem thirdFullSchwartzSixthFluxBudget_nonneg244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) :
    0 ≤ thirdFullSchwartzSixthFluxBudget244 v z := by
  unfold thirdFullSchwartzSixthFluxBudget244
    thirdFullComplexSixthFluxContractionBudget244
  positivity

/-- A Schwartz triad is in the indicated common squared-radius interval.
No norm ratios or division by frequency occur, including at zero. -/
def thirdFullTriadWithinSquareAnnulus244 (lo hi : ℝ) (z : PairV) : Prop :=
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  (lo ≤ thirdTriadAxisDot244 p p ∧ thirdTriadAxisDot244 p p ≤ hi) ∧
  (lo ≤ thirdTriadAxisDot244 q q ∧ thirdTriadAxisDot244 q q ≤ hi) ∧
  (lo ≤ thirdTriadAxisDot244 r r ∧ thirdTriadAxisDot244 r r ≤ hi)

/-- Every actual complex Fourier triad in an annulus has the exact
linear squared-radius-width gain, before any spatial integration. -/
theorem thirdFullSchwartzSixthPowerFlux_annularBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (z : PairV) (hz : thirdFullTriadWithinSquareAnnulus244 lo hi z) :
    ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
      (3 * hi ^ 2 * (hi - lo)) * thirdFullSchwartzSixthFluxBudget244 v z := by
  rcases hz with ⟨hp, hq, hr⟩
  exact thirdFullComplexSixthPowerFlux_annularGain244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
    (WithLp.ofLp z.2)
    (h3SchwartzTriadPolarization v (WithLp.ofLp z.1))
    (h3SchwartzTriadPolarization v (WithLp.ofLp (-(z.1 + z.2))))
    (h3SchwartzTriadPolarization v (WithLp.ofLp z.2))
    lo hi hlo hlohi hp hq hr

/-- Solenoidality plus already-proved ordered-kernel integrability
provides a genuine L¹ SIX-DIMENSIONAL flux, with no cutoff premise. -/
theorem thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0) :
    Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) := by
  exact thirdFullSchwartzComplexSixthPowerFlux_integrable_of_ordered244
    v (h3SchwartzTriadPolarization_divergence_zero v hDiv)
    (thirdFullSchwartzComplexOrderedKernel_integrable244 v)

/-- The pointwise radial-width saving survives INTEGRATION on any
measurable near-shell sector, provided the exact contraction budget is
integrable there.  The latter is an explicit analytic contract, not a
pretended consequence of the H³ bound. -/
theorem thirdFullSchwartzSixthPowerFlux_annularIntegral_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (s : Set PairV) (hs : MeasurableSet s)
    (hShell : ∀ z ∈ s, thirdFullTriadWithinSquareAnnulus244 lo hi z)
    (hBudget : IntegrableOn (thirdFullSchwartzSixthFluxBudget244 v) s
      (volume.prod volume)) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      (3 * hi ^ 2 * (hi - lo)) *
        ∫ z in s, thirdFullSchwartzSixthFluxBudget244 v z
          ∂volume.prod volume := by
  let K : ℝ := 3 * hi ^ 2 * (hi - lo)
  have hFlux := thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244
    v hDiv
  have hNormInt : IntegrableOn
      (fun z : PairV => ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖)
      s (volume.prod volume) := hFlux.integrableOn.norm
  have hMajorInt : IntegrableOn
      (fun z : PairV => K * thirdFullSchwartzSixthFluxBudget244 v z)
      s (volume.prod volume) := hBudget.const_mul K
  have hPoint (z : PairV) (hz : z ∈ s) :
      ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
        K * thirdFullSchwartzSixthFluxBudget244 v z := by
    exact thirdFullSchwartzSixthPowerFlux_annularBound244
      v lo hi hlo hlohi z (hShell z hz)
  have hAlmost : ∀ᵐ z ∂((volume.prod volume : Measure PairV).restrict s),
      ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
        K * thirdFullSchwartzSixthFluxBudget244 v z := by
    filter_upwards [ae_restrict_mem hs] with z hz
    exact hPoint z hz
  calc
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
        ∫ z in s, ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖
          ∂volume.prod volume := norm_integral_le_integral_norm _
    _ ≤ ∫ z in s, K * thirdFullSchwartzSixthFluxBudget244 v z
          ∂volume.prod volume :=
        setIntegral_mono_ae_restrict hNormInt hMajorInt hAlmost
    _ = K * ∫ z in s, thirdFullSchwartzSixthFluxBudget244 v z
          ∂volume.prod volume := by rw [integral_const_mul]

/-- The global solenoidal sixth-power Fourier integral is an EXACT sum
of its annular part and its off-shell complement; neither is discarded.
The identity holds for any measurable Fourier sector, not just balls. -/
theorem thirdFullSchwartzSixthPowerFlux_setSplit244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (s : Set PairV) (hs : MeasurableSet s) :
    (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
      ∂volume.prod volume) =
      (∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume) +
      (∫ z in sᶜ, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume) := by
  exact (integral_add_compl hs
    (thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv)).symm

/-- Full quantitative on/off-shell alternative at the COMPLEX integral
level.  The local gain is proportional to shell width, while the true
complementary integral appears without an unproved estimate. -/
theorem thirdFullSchwartzSixthPowerFlux_annularOffshellBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (s : Set PairV) (hs : MeasurableSet s)
    (hShell : ∀ z ∈ s, thirdFullTriadWithinSquareAnnulus244 lo hi z)
    (hBudget : IntegrableOn (thirdFullSchwartzSixthFluxBudget244 v) s
      (volume.prod volume)) :
    ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      (3 * hi ^ 2 * (hi - lo)) *
        (∫ z in s, thirdFullSchwartzSixthFluxBudget244 v z
          ∂volume.prod volume) +
      ‖∫ z in sᶜ, thirdFullSchwartzComplexSixthPowerFlux244 v z
          ∂volume.prod volume‖ := by
  rw [thirdFullSchwartzSixthPowerFlux_setSplit244 v hDiv s hs]
  exact (norm_add_le _ _).trans (add_le_add_left
    (thirdFullSchwartzSixthPowerFlux_annularIntegral_le244
      v hDiv lo hi hlo hlohi s hs hShell hBudget) _)


/-- If the total complex flux exceeds the annular cost plus a threshold,
then its complementary frequency integral must carry that threshold.
This is an EXACT off-shell necessary condition, not an assumed tail bound. -/
theorem thirdFullSchwartzSixthPowerFlux_offshellFloor244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (s : Set PairV) (hs : MeasurableSet s)
    (hShell : ∀ z ∈ s, thirdFullTriadWithinSquareAnnulus244 lo hi z)
    (hBudget : IntegrableOn (thirdFullSchwartzSixthFluxBudget244 v) s
      (volume.prod volume))
    (M : ℝ)
    (hExcess :
      (3 * hi ^ 2 * (hi - lo)) *
        (∫ z in s, thirdFullSchwartzSixthFluxBudget244 v z
          ∂volume.prod volume) + M <
      ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖) :
    M < ‖∫ z in sᶜ,
      thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ := by
  have hSplit := thirdFullSchwartzSixthPowerFlux_annularOffshellBound244
    v hDiv lo hi hlo hlohi s hs hShell hBudget
  linarith only [hSplit, hExcess]

/-- The identical annulus/complement partition passes through ANY existing
solenoidal Schwartz transport limit, including the previously constructed
physical Navier--Stokes H³ snapshot. Annuli may change with the sequence.
There is no uniform-in-n budget assertion. -/
theorem thirdFullSchwartzSixthPowerFlux_split_tendsto244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hDiv : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify (f n j)) x
          (h3FourierAxisDirection j) = 0)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (L : ℝ)
    (hFull : Tendsto (fun n => fullSchwartzThirdCommutator244 (f n))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      ((∫ z in s n,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume) +
       (∫ z in (s n)ᶜ,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume)).im)
      atTop (𝓝 L) := by
  have hPure := thirdFullSchwartz_pureFlux_tendsto_of_complexDivergence244
    f hDiv L hFull
  have hEq : (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
      ((∫ z in s n,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume) +
       (∫ z in (s n)ᶜ,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume)).im) =
      (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : PairV,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume).im) := by
    funext n
    rw [thirdFullSchwartzSixthPowerFlux_setSplit244
      (fun j => h3SchwartzComplexify (f n j)) (hDiv n) (s n) (hs n)]
  rw [hEq]
  exact hPure


/-- The measurable near/off-shell split is VALID ALONG THE VERY SAME real
solenoidal Schwartz sequence representing a physical H³ Navier--Stokes
snapshot. The sum of the two integral pieces converges to the old physical
third transport; no separate convergence of the pieces is postulated. -/
theorem exists_thirdFullPhysicalSnapshot_solenoidalAnnularFluxSplit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (htNS : t ∈ Set.Ioo (0 : ℝ) T)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n)) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ),
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (velocityH3Energy2At u t)) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (velocityH3Energy3At u t)) ∧
      Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        ((∫ z in s n,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume) +
         (∫ z in (s n)ᶜ,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume)).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  obtain ⟨V, Ψ, hV, _hAE, hDiv, _hDefect,
    hE2, hE3, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hNS htNS hH3 hClass ht hFourier
  have hE2Physical : Tendsto
      (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (velocityH3Energy2At u t)) := by
    rw [← thirdFullPhysical_canonicalSecondJetEnergy_eq244 hFourier]
    exact hE2
  have hE3Physical : Tendsto
      (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (velocityH3Energy3At u t)) := by
    rw [← thirdFullPhysical_canonicalThirdJetEnergy_eq244 hFourier]
    exact hE3
  have hEq (n : ℕ) :
      (∫ z in s n,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : A3 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume) +
       (∫ z in (s n)ᶜ,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : A3 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume) =
      ∫ z : PairV,
        thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : A3 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume := by
    exact (thirdFullSchwartzSixthPowerFlux_setSplit244
      (fun j => h3SchwartzComplexify
        (Ψ n (h3ClassicalizationFinOfAxis j)))
      (hDiv n) (s n) (hs n)).symm
  have hSplitLimit : Tendsto (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        ((∫ z in s n,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume) +
         (∫ z in (s n)ᶜ,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume)).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
    convert hFlux using 1
    funext n
    rw [hEq n]
  exact ⟨V, Ψ, hV, hDiv, hE2Physical, hE3Physical, hSplitLimit⟩

end
end PrimeTensor.FirstMonomialTriad
