import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierDominance
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.Tactic

/-!
# Fixed-inner obstruction for selected wide annuli: terminal Fourier bandlimit

The preceding exact sharp mass ledger and actual Young-width inequality show
that, on any positive-deficit annulus whose outer radius doubles its inner
radius, at least 119/128 of the physical kinetic highpass survives ABOVE the
outer radius. This module uses the ACTUAL sharp physical Fourier cutoff,
not an abstract carrier, to identify the endpoint consequence.

At one fixed positive time, the physical L² highpass mass tends to zero as
natural outer radii grow. Therefore a nonzero fixed-inner carrier cannot
sustain strict-excess/positive-deficit witnesses at arbitrarily high outer
cutoffs. Along a cofinal physical sequence with finite H³ dissipation, the
same reasoning forces the fixed-inner highpass mass to vanish. The actual
physical L² terminal trace is consequently sharp-bandlimited to that radius.

This is a conditional obstruction: positivity of selected strict kinetic
excess and nonnegativity of the full Young-width physical deficit are NOT
asserted to follow automatically from Navier--Stokes.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Scalar carrier extinction: a fixed-factor lower bound for an inner
nonnegative mass cannot coexist with an outer mass tending to zero, unless
the inner mass itself tends to zero. The constants 119 and 128 are the exact
physical Young-width retention coefficients at a doubled aperture. -/
theorem thirdFullKinetic_outerRetention_tight_forces_innerVanishing244
    (inner outer : ℕ → ℝ)
    (hInner : ∀ k : ℕ, 0 ≤ inner k)
    (hOuter : Tendsto outer atTop (𝓝 (0 : ℝ)))
    (hRetention : ∀ᶠ k : ℕ in atTop,
      119 * inner k ≤ 128 * outer k) :
    Tendsto inner atTop (𝓝 (0 : ℝ)) := by
  have hUpperLimit : Tendsto (fun k : ℕ => (128 / 119 : ℝ) * outer k)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hOuter.const_mul (128 / 119 : ℝ)
  have hUpper : ∀ᶠ k : ℕ in atTop,
      inner k ≤ (128 / 119 : ℝ) * outer k := by
    filter_upwards [hRetention] with k hk
    nlinarith only [hk]
  exact squeeze_zero' (Filter.Eventually.of_forall hInner) hUpper hUpperLimit

/-- A natural outer cutoff tending to infinity eventually doubles every
fixed positive inner radius. This is a pure frequency-order lemma. -/
theorem thirdFullKinetic_naturalOuter_eventually_double244
    (rho : ℝ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ k : ℕ in atTop, 2 * rho ≤ (n k : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * rho)
  filter_upwards [hn.eventually (eventually_ge_atTop N)] with k hk
  have hCast : (N : ℝ) ≤ (n k : ℝ) := by exact_mod_cast hk
  linarith only [hN, hCast]

/-- At one fixed physical snapshot, the genuine sharp physical Fourier
highpass above any natural radius escaping to infinity has vanishing square
kinetic mass. This only uses the canonical physical L² Plancherel map. -/
theorem thirdFullPhysical_fixedSnapshot_naturalOuterHighMass_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k : ℕ =>
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t ((n k : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have h := thirdFullPhysical_naturalSharpHighMass_tendsto_zero_of_trace244
    (fun _ : ℕ => V) V n tendsto_const_nhds hn
  simpa only [V, thirdFullPhysicalActualSharpKineticHighMass244] using h

/-- A nonzero fixed-inner physical kinetic tail cannot support selected
strict excess AND positive full Young-width deficit at every sufficiently
large natural outer radius at ONE physical snapshot. -/
theorem thirdFullPhysical_fixedSnapshot_noPersistentWidePositiveDeficit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (b rho : ℝ) (hRho : 0 < rho)
    (hInnerPos : 0 < thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (margin : ℕ → ℝ)
    (hMargin : ∀ᶠ k : ℕ in atTop, 0 < margin k)
    (hExcess : ∀ᶠ k : ℕ in atTop,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin k ≤
      ((rho ^ 2 + ((n k : ℝ) + 1) ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho) :
    ¬ (∀ᶠ k : ℕ in atTop,
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b t rho ((n k : ℝ) + 1)) := by
  intro hDeficit
  have hWide := thirdFullKinetic_naturalOuter_eventually_double244 rho n hn
  have hRet : ∀ᶠ k : ℕ in atTop,
      119 * thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho ≤
        128 * thirdFullPhysicalActualSharpKineticHighMass244
          hH3 t ((n k : ℝ) + 1) := by
    filter_upwards [hWide, hMargin, hExcess, hDeficit]
      with k hk hm he hd
    have hOrder : rho ≤ (n k : ℝ) + 1 := by
      linarith only [hk, hRho]
    exact thirdFullPhysical_doubleAperture_outerCarrier119of128244
      hH3 t ht b rho ((n k : ℝ) + 1) (margin k)
      hRho hOrder hk hm he hd
  have hOuter := thirdFullPhysical_fixedSnapshot_naturalOuterHighMass_tendsto_zero244
    hH3 t n hn
  have hInner := thirdFullKinetic_outerRetention_tight_forces_innerVanishing244
    (fun _ : ℕ => thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (fun k : ℕ => thirdFullPhysicalActualSharpKineticHighMass244
      hH3 t ((n k : ℝ) + 1))
    (fun _ => sq_nonneg _) hOuter hRet
  have hConstant : Tendsto
      (fun _ : ℕ => thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
      atTop (𝓝 (thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)) :=
    tendsto_const_nhds
  have hZero : thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho = 0 :=
    tendsto_nhds_unique hConstant hInner
  exact (ne_of_gt hInnerPos) hZero

/-- Cofinal selected wide-annulus positive deficits imply extinction of the
ACTUAL highpass at any one fixed inner radius when finite physical H³
viscous dissipation provides terminal raw Fourier tightness. -/
theorem thirdFullPhysical_finiteDissipation_cofinalFixedInnerHighMassVanishes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (rho : ℝ) (hRho : 0 < rho)
    (x : ℕ → ℝ) (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (margin : ℕ → ℝ)
    (hMargin : ∀ᶠ k : ℕ in atTop, 0 < margin k)
    (hExcess : ∀ᶠ k : ℕ in atTop,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin k ≤
      ((rho ^ 2 + ((n k : ℝ) + 1) ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (hDeficit : ∀ᶠ k : ℕ in atTop,
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) rho ((n k : ℝ) + 1)) :
    Tendsto (fun k : ℕ => thirdFullPhysicalActualSharpKineticHighMass244
      hH3 (x k) rho) atTop (𝓝 (0 : ℝ)) := by
  have hWide := thirdFullKinetic_naturalOuter_eventually_double244 rho n hn
  have hRet : ∀ᶠ k : ℕ in atTop,
      119 * thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho ≤
        128 * thirdFullPhysicalActualSharpKineticHighMass244
          hH3 (x k) ((n k : ℝ) + 1) := by
    filter_upwards [hWide, hMargin, hExcess, hDeficit]
      with k hk hm he hd
    have hOrder : rho ≤ (n k : ℝ) + 1 := by
      linarith only [hk, hRho]
    have ht : x k ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1
        (hx k).1), (hx k).2⟩
    exact thirdFullPhysical_doubleAperture_outerCarrier119of128244
      hH3 (x k) ht b rho ((n k : ℝ) + 1) (margin k)
      hRho hOrder hk hm he hd
  have hOuter := thirdFullPhysical_finiteDissipation_naturalHighMass_tendsto_zero244
    hH3 hClass hDInt x n (fun k => (hx k).2) hCofinal hn
  exact thirdFullKinetic_outerRetention_tight_forces_innerVanishing244
    (fun k : ℕ => thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (fun k : ℕ => thirdFullPhysicalActualSharpKineticHighMass244
      hH3 (x k) ((n k : ℝ) + 1))
    (fun _ => sq_nonneg _) hOuter hRet

/-- HARD PDE-FACING CONCLUSION: the fixed-inner selected positive-deficit
route has a rigid terminal frequency support. If finite full physical H³
dissipation and cofinal strict selected excess/deficit both hold at a fixed
inner radius, the genuine strong physical L² terminal trace is sharply
bandlimited to that radius. No artificial terminal spectral state is added. -/
theorem thirdFullPhysical_finiteDissipation_cofinalFixedInner_terminalBandlimit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (rho : ℝ) (hRho : 0 < rho)
    (x : ℕ → ℝ) (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (margin : ℕ → ℝ)
    (hMargin : ∀ᶠ k : ℕ in atTop, 0 < margin k)
    (hExcess : ∀ᶠ k : ℕ in atTop,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin k ≤
      ((rho ^ 2 + ((n k : ℝ) + 1) ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (hDeficit : ∀ᶠ k : ℕ in atTop,
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) rho ((n k : ℝ) + 1)) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 L) ∧
      ‖L - thirdFullPhysicalSharpLowCutoffHilbert244 rho L‖ ^ 2 = 0 := by
  obtain ⟨L, hL⟩ :=
    h3Critical_physicalL2_terminal_trace_of_finite_dissipation
      hH3 hClass hDInt
  have hInner :=
    thirdFullPhysical_finiteDissipation_cofinalFixedInnerHighMassVanishes244
      hH3 hClass hDInt b hb rho hRho x hx hCofinal n hn
      margin hMargin hExcess hDeficit
  have hLeft : Tendsto x atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hCofinal, Filter.Eventually.of_forall (fun k => (hx k).2)⟩
  have hX : Tendsto
      (fun k : ℕ => h3AuditInitialOldPhysicalHilbertTotal hH3 (x k))
      atTop (𝓝 L) := hL.comp hLeft
  let P : H3PhysicalRealFinVectorL2Hilbert → ℝ :=
    fun V => ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2
  have hP : Continuous P := by
    dsimp only [P]
    exact (continuous_norm.comp
      (thirdFullPhysical_sharpVectorHighpass_continuous244 rho)).pow 2
  have hLimit : Tendsto (fun k : ℕ => P
      (h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)))
      atTop (𝓝 (P L)) := (hP.tendsto L).comp hX
  have hZero : Tendsto (fun k : ℕ => P
      (h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [P, thirdFullPhysicalActualSharpKineticHighMass244]
      using hInner
  refine ⟨L, hL, ?_⟩
  exact tendsto_nhds_unique hLimit hZero

end
end PrimeTensor.FirstMonomialTriad
