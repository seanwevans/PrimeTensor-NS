import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalSelectedPairClocks
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMovingRawFourierTightness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# Selected annular excess forces outer/inner aspect escape under finite H³ dissipation

The previous selected-pair theorem correctly removed the impossible requirement
of strict kinetic excess on every member of a rectangular annular family. Its
remaining obstacle was actual physical highpass tightness at moving cutoffs.

The present module supplies that tightness at natural real radii `n+1` using
(1) exact physical Plancherel of the genuine three-component sharp highpass,
(2) the established moving raw Fourier L² tightness theorem, and
(3) the actual physical L² terminal trace furnished by finite full-H³
    dissipation. No H³ terminal trace is used.

At each cofinal time, any positive strict selected excess with inner radius
`n(k)+1`, where `n(k) → ∞`, then forces the outer/inner ratio to escape:
for every fixed K≥0, eventually σ(k) > K ((n(k):ℝ)+1).
This rules out persistently bounded-aspect selected annuli in the finite-
dissipation regime. It does not prove that positive deficit witnesses exist,
nor does it prove full Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeSelectedAspectEscape244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSelectedAspectEscape244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The ORIGINAL three-component physical sharp highpass at a natural radial
cutoff has square mass at most three times the square of the raw Fourier
vector highpass sup norm. The exact Plancherel equalities are used in each
coordinate. No abstract kinetic highpass is substituted. -/
theorem thirdFullPhysical_naturalSharpHighpass_sq_le_rawSpectral244
    (n : ℕ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 ((n : ℝ) + 1) V‖ ^ 2 ≤
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 n
        (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap V)‖ ^ 2 := by
  let F : H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap V
  let H : H3SpectralVelocityState :=
    thirdFullSpectralVelocityHighRadialApply244 n F
  have hComponent (j : Fin 3) :
      ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 ((n : ℝ) + 1) V).ofLp j‖ ^ 2 =
        ‖H j‖ ^ 2 := by
    have hFj : F j = h3ScalarFourierL2 (V.ofLp j) := rfl
    change ‖V.ofLp j -
        h3CriticalPhysicalSharpLowCutoffApply ((n : ℝ) + 1) (V.ofLp j)‖ ^ 2 =
      ‖thirdFullSpectralHighRadialApply244 n (F j)‖ ^ 2
    calc
      ‖V.ofLp j - h3CriticalPhysicalSharpLowCutoffApply ((n : ℝ) + 1)
          (V.ofLp j)‖ ^ 2 =
          ‖h3ScalarFourierL2
            (V.ofLp j - h3CriticalPhysicalSharpLowCutoffApply
              ((n : ℝ) + 1) (V.ofLp j))‖ ^ 2 := by
          rw [norm_h3ScalarFourierL2]
      _ = ‖h3ScalarFourierL2 (V.ofLp j) -
          h3CriticalFourierSharpLowCutoffCLM ((n : ℝ) + 1)
            (h3ScalarFourierL2 (V.ofLp j))‖ ^ 2 := by
          rw [h3Critical_scalarFourier_physicalHighpass_eq]
      _ = ∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
          ‖(h3ScalarFourierL2 (V.ofLp j) : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ∂volume :=
          h3Critical_fourierSharpHighpass_norm_sq_eq_integral _ _
      _ = ‖thirdFullSpectralHighRadialApply244 n (F j)‖ ^ 2 := by
          rw [hFj]
          simpa only [h3TopTailNaturalHighRadialSet] using
            (thirdFullSpectralHighRadialApply_norm_sq244 n
              (h3ScalarFourierL2 (V.ofLp j))).symm
  have hSum :
      ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 ((n : ℝ) + 1) V‖ ^ 2 =
        ∑ j : Fin 3,
          ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244
            ((n : ℝ) + 1) V).ofLp j‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => H3ScalarL2)
      (V - thirdFullPhysicalSharpLowCutoffHilbert244 ((n : ℝ) + 1) V)
  calc
    ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 ((n : ℝ) + 1) V‖ ^ 2 =
        ∑ j : Fin 3, ‖H j‖ ^ 2 := by
      rw [hSum]
      exact Finset.sum_congr rfl (fun j _ => hComponent j)
    _ ≤ ∑ _j : Fin 3, ‖H‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (h3SpectralVelocity_coordinate_norm_le H j) 2
    _ = 3 * ‖H‖ ^ 2 := by
      rw [Fin.sum_univ_three]
      ring

/-- Strong physical L² convergence at the sampled times makes the ACTUAL
sharp highpass kinetic mass vanish at any moving natural inner radius.
This is a theorem about the physical sharp projector, not a surrogate
weighted-H³ tail. -/
theorem thirdFullPhysical_naturalSharpHighMass_tendsto_zero_of_trace244
    (X : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (L : H3PhysicalRealFinVectorL2Hilbert)
    (n : ℕ → ℕ)
    (hX : Tendsto X atTop (𝓝 L)) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k : ℕ =>
      ‖X k - thirdFullPhysicalSharpLowCutoffHilbert244
        ((n k : ℝ) + 1) (X k)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  have hRaw := thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244
    X L n hX hn
  have hUpper : Tendsto (fun k : ℕ =>
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 (n k)
        (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
          (X k))‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hSq := (hRaw.pow 2).const_mul 3
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using hSq
  have hLow (k : ℕ) :
      0 ≤ ‖X k - thirdFullPhysicalSharpLowCutoffHilbert244
        ((n k : ℝ) + 1) (X k)‖ ^ 2 := sq_nonneg _
  have hCap (k : ℕ) :
      ‖X k - thirdFullPhysicalSharpLowCutoffHilbert244
        ((n k : ℝ) + 1) (X k)‖ ^ 2 ≤
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 (n k)
        (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
          (X k))‖ ^ 2 :=
    thirdFullPhysical_naturalSharpHighpass_sq_le_rawSpectral244 (n k) (X k)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLow)
    (Filter.Eventually.of_forall hCap) hUpper

/-- Finite full-H³ dissipation produces the physical L² terminal trace,
which in turn forces tightness of the ORIGINAL sharp kinetic highpass at
cofinally increasing natural radii. -/
theorem thirdFullPhysical_finiteDissipation_naturalHighMass_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (x : ℕ → ℝ) (n : ℕ → ℕ)
    (hx : ∀ k : ℕ, x k < T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun k : ℕ =>
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k)
        ((n k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hL⟩ :=
    h3Critical_physicalL2_terminal_trace_of_finite_dissipation
      hH3 hClass hDInt
  have hX : Tendsto (fun k : ℕ =>
      h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)) atTop (𝓝 L) := by
    have hLeft : Tendsto x atTop (𝓝[<] T) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hCofinal, Filter.Eventually.of_forall hx⟩
    exact hL.comp hLeft
  change Tendsto (fun k : ℕ =>
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 (x k) -
        thirdFullPhysicalSharpLowCutoffHilbert244 ((n k : ℝ) + 1)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (x k))‖ ^ 2)
      atTop (𝓝 (0 : ℝ))
  exact thirdFullPhysical_naturalSharpHighMass_tendsto_zero_of_trace244
    (fun k => h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)) L n hX hn

/-- If selected strict physical excess persists while its sharp highpass
mass tends to zero, then every fixed positive aspect cap is eventually
violated. This is stronger than assuming bounded aspect and deriving `False`;
it is a quantitative statement of required geometric escape. -/
theorem thirdFullPhysical_selectedExcess_aspectEscapes_of_highMassTight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hOrder : ∀ k : ℕ, rho k ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
        ((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
    (hMassZero : Tendsto (fun k : ℕ =>
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
        atTop (𝓝 (0 : ℝ))) :
    ∀ K : ℝ, 0 ≤ K →
      ∀ᶠ k : ℕ in atTop, K * rho k < sigma k := by
  have hE : 0 < velocityH3Energy0At u b :=
    thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244
      hH3 hClass b hb (x 0) (hx 0) (rho 0) (sigma 0)
      (margin 0) (hMargin 0) (hExcess 0)
  intro K hK
  let c : ℝ := 6 * velocityH3Energy0At u b / (1 + K ^ 2)
  have hDen : 0 < 1 + K ^ 2 := by positivity
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos (by norm_num) hE) hDen
  have hSmall : ∀ᶠ k : ℕ in atTop,
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k) < c :=
    hMassZero.eventually (eventually_lt_nhds hc)
  filter_upwards [hSmall] with k hk
  by_contra hNot
  have hAspect : sigma k ≤ K * rho k := le_of_not_gt hNot
  have hFraction := thirdFullPhysical_selectedExcess_boundedAspect_highpassFraction244
    hH3 hClass b hb (x k) (hx k) (rho k) (sigma k) K (margin k)
    (hRho k) (hOrder k) hK hAspect (hMargin k).le (hExcess k)
  have hBound : c ≤ thirdFullPhysicalActualSharpKineticHighMass244
      hH3 (x k) (rho k) := by
    dsimp only [c]
    apply (div_le_iff₀ hDen).mpr
    simpa only [mul_comm] using hFraction
  exact (not_lt_of_ge hBound) hk

/-- HARD PHYSICAL CONSEQUENCE. On the finite-full-dissipation branch, any
cofinal family of genuine strictly excessive selected annuli with natural
inner radii tending to infinity MUST have outer/inner aspect escaping every
fixed finite bound. The moving sharp highpass tightness premise is proved
above, not inserted as an additional hypothesis. -/
theorem thirdFullPhysical_finiteDissipation_selectedNaturalExcess_aspectEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x sigma margin : ℕ → ℝ) (n : ℕ → ℕ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hn : Tendsto n atTop atTop)
    (hOrder : ∀ k : ℕ, (n k : ℝ) + 1 ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          ((n k : ℝ) + 1) (velocityH3Energy0At u b)) + margin k ≤
        ((((n k : ℝ) + 1) ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k)
            ((n k : ℝ) + 1)) :
    ∀ K : ℝ, 0 ≤ K →
      ∀ᶠ k : ℕ in atTop, K * ((n k : ℝ) + 1) < sigma k := by
  have hMass := thirdFullPhysical_finiteDissipation_naturalHighMass_tendsto_zero244
    hH3 hClass hDInt x n (fun k => (hx k).2) hCofinal hn
  exact thirdFullPhysical_selectedExcess_aspectEscapes_of_highMassTight244
    hH3 hClass b hb x (fun k => (n k : ℝ) + 1) sigma margin
    hx (fun k => by positivity) hOrder hMargin hExcess hMass

end
end PrimeTensor.FirstMonomialTriad
