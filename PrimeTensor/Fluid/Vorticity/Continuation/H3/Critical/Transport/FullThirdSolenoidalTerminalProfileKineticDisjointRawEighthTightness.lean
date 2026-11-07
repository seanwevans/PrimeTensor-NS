import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticIntermittentRateDichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMovingRawFourierTightness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthKineticGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationTerminalTrace
import Mathlib.Tactic

/-!
# Raw kinetic concentration on the exact disjoint kinetic H3 annular PDE clocks

The earlier eighth-power kinetic bound uses the total physical kinetic energy.
Here the ACTUAL annular H3 dissipation is paid by its own raw Fourier L2 mass,
not by global kinetic mass. At the same kinetic-selected start time and radii,

  M/4 < 4 (N+2)^8 * mu[n+1,N+1](u(x)).

The already-proved physical moving-raw-Fourier tightness theorem makes this
annular mass vanish along any cofinal sequence of increasing inner cutoffs,
provided the physical velocity has a strong terminal L2 trace. In particular,

  M(v(k)) / (N(v(k))+2)^8 -> 0.

This is stronger than the constant-coefficient M <= 16 E (N+1)^8 bound.
No terminal H3 trace is assumed. A finite full-H3 dissipation integral is
used ONLY to obtain the established terminal physical L2 trace in the final
corollary. The kinetic windows, outer frequencies, and exact widths remain
untouched. The old critical-eighth minimal-crossing results involve different
windows; the new result applies to the kinetic PDE-rate windows themselves.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeKineticRawEighth244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceKineticRawEighth244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At the actual start of a kinetic-selected annular PDE clock, the entire
positive viscous height is supported by raw L2 mass in THAT finite annulus.
Neither total kinetic energy nor a global H3 state maximum appears. -/
theorem thirdFullPhysical_kineticWindow_rawEighthAnnularCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (n N : ℕ) (M δ : ℝ)
    (hWindow : ThirdFullKineticNaturalAnnularLocalWitness244
      hH3 b x n N M δ) :
    M / 4 < 4 * (((N : ℝ) + 2) ^ 8) *
      h3PathActualBandRawKineticMass244 ((n : ℝ) + 1)
        ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 x) := by
  rcases hWindow with ⟨hnN, hδ, _hEq, _hEnd, hFloor, _hCost⟩
  have hxWindow : x ∈ Set.Icc x (x + δ) :=
    ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩
  have hPeak := (hFloor x hxWindow).1
  have hCast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hRadial : ((n : ℝ) + 1) ≤ ((N : ℝ) + 1) := by
    linarith only [hCast]
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hFourier := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass x hxClass ((n : ℝ) + 1) ((N : ℝ) + 1)
    hRadial (by positivity)
  simpa only [show ((N : ℝ) + 1) + 1 = (N : ℝ) + 2 by ring] using
    (lt_of_lt_of_le hPeak hFourier)

/-- If the actual raw mass of a moving annulus vanishes, its weighted H3
viscous height is little-o of the eighth power of the OUTER radius. -/
theorem thirdFull_scalar_rawEighthCarrier_normalizedHeight_tendsto_zero244
    (M Q μ : ℕ → ℝ)
    (hM : ∀ k, 0 ≤ M k) (hQ : ∀ k, 1 ≤ Q k)
    (hCost : ∀ k, M k / 4 < 4 * (Q k) ^ 8 * μ k)
    (hμ : Tendsto μ atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => M k / (Q k) ^ 8) atTop (𝓝 (0 : ℝ)) := by
  have hPositive (k : ℕ) : 0 < (Q k) ^ 8 :=
    pow_pos (lt_of_lt_of_le zero_lt_one (hQ k)) 8
  have hLower (k : ℕ) : 0 ≤ M k / (Q k) ^ 8 :=
    div_nonneg (hM k) (hPositive k).le
  have hUpper (k : ℕ) : M k / (Q k) ^ 8 ≤ 16 * μ k := by
    apply (div_le_iff₀ (hPositive k)).2
    nlinarith only [hCost k]
  have hTail : Tendsto (fun k => 16 * μ k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hμ.const_mul 16
  exact squeeze_zero hLower hUpper hTail

/-- Transfer actual physical terminal L2 tightness to the SAME separated
kinetic clocks, with arbitrary prescribed positive heights and outer radii.
The exact annular raw kinetic masses vanish and the height is little-o of
the outer critical-eighth frequency. No full-H3 dissipation finiteness is
needed once the physical L2 terminal trace has been supplied. -/
theorem thirdFullPhysical_kineticDisjointWindows_rawEighthTightness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (hM : ∀ n, 0 < M n)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hMono : StrictMono v)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hWindows : ∀ k : ℕ, τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (hTrace : ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    Tendsto (fun k : ℕ =>
      h3PathActualBandRawKineticMass244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      M (v k) / (((N (v k) : ℝ) + 2) ^ 8))
      atTop (𝓝 (0 : ℝ)) := by
  have hBefore (k : ℕ) : τ (v k) < T := (hWindows k).1.2
  have hBeforeEvent : ∀ᶠ k : ℕ in atTop,
      τ (v k) ∈ Set.Iio T :=
    Filter.Eventually.of_forall (fun k => hBefore k)
  have hLimitLeft : Tendsto (fun k : ℕ => τ (v k))
      atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr ⟨hLimit, hBeforeEvent⟩
  have hStrict : ∀ᶠ k : ℕ in atTop,
      τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    Filter.Eventually.of_forall (fun k =>
      ⟨lt_trans hClass.terminal_start.1
        (lt_trans hb.1 (hWindows k).1.1), (hWindows k).1.2⟩)
  have hIndex : Tendsto v atTop atTop := hMono.tendsto_atTop
  have hMass := thirdFullPhysical_movingBandRawMass_tendsto_zero_of_L2Trace244
    hH3 (fun k => τ (v k)) v
    (fun k => (N (v k) : ℝ) + 1)
    hLimitLeft hStrict hIndex hTrace
  have hCost (k : ℕ) :
      M (v k) / 4 < 4 * (((N (v k) : ℝ) + 2) ^ 8) *
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) :=
    thirdFullPhysical_kineticWindow_rawEighthAnnularCost244
      hH3 hClass b hb (τ (v k)) (hWindows k).1
      (v k) (N (v k)) (M (v k)) (δ (v k)) (hWindows k).2
  have hNormalized :=
    thirdFull_scalar_rawEighthCarrier_normalizedHeight_tendsto_zero244
      (fun k => M (v k))
      (fun k => (N (v k) : ℝ) + 2)
      (fun k => h3PathActualBandRawKineticMass244
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
      (fun k => (hM (v k)).le)
      (fun k => by
        have hn : (0 : ℝ) ≤ (N (v k) : ℝ) := Nat.cast_nonneg _
        linarith only [hn])
      hCost hMass
  exact ⟨hMass, hNormalized⟩

/-- With finite ordinary terminal physical H3 dissipation, the established
L2 terminal trace discharges the ONLY additional compactness input.
Consequently any no-H3-trace kinetic diagonal has a vanishing raw band mass
and M/(N+2)^8 -> 0 on exactly its chosen disjoint physical clocks. -/
theorem thirdFullPhysical_noH3Trace_disjointKineticRawEighthEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k) ∧
      (∀ k : ℕ, τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      Tendsto (fun k : ℕ =>
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        M (v k) / (((N (v k) : ℝ) + 2) ^ 8))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hWindows⟩ :=
    thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244
      hH3 hClass b hb hNoTrace M hM
  have hTrace := h3Critical_physicalL2_terminal_trace_of_finite_dissipation
    hH3 hClass hDInt
  obtain ⟨hRaw, hNormalized⟩ :=
    thirdFullPhysical_kineticDisjointWindows_rawEighthTightness244
      hH3 hClass b hb M hM τ N δ v hv hCofinal hWindows hTrace
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hWindows, hRaw, hNormalized⟩


/-- At critical eighth height relative to the inner natural frequency, the
same kinetic-selected disjoint annuli must have outer frequency growing by
an UNBOUNDED factor relative to that inner frequency. This transfers the
previous critical-eighth mass-or-escape mechanism from minimal-source
windows to the genuinely kinetic-selected PDE-rate windows. -/
theorem thirdFullPhysical_noH3Trace_disjointKineticCriticalEighthEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (η : ℝ) (hη : 0 < η)
    (hCritical : ∀ n : ℕ,
      2 * η * (((n : ℝ) + 1) ^ 8) ≤ M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      Tendsto (fun k : ℕ =>
        h3PathActualBandRawKineticMass244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        M (v k) / (((N (v k) : ℝ) + 2) ^ 8))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1))
        atTop atTop := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hWindows, hMass, hNormalized⟩ :=
    thirdFullPhysical_noH3Trace_disjointKineticRawEighthEscape244
      hH3 hClass b hb hNoTrace hDInt M hM
  let μ : ℕ → ℝ := fun k =>
    h3PathActualBandRawKineticMass244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
  have hμ (k : ℕ) : 0 ≤ μ k :=
    thirdFull_bandRawKineticMass_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
  have hR (k : ℕ) : 1 ≤ ((v k : ℝ) + 1) := by
    have hvk : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hvk]
  have hQ (k : ℕ) : 0 ≤ ((N (v k) : ℝ) + 1) := by positivity
  have hHeight : ∀ᶠ k : ℕ in atTop,
      η * (((v k : ℝ) + 1) ^ 8) ≤ M (v k) / 2 := by
    apply Filter.Eventually.of_forall
    intro k
    have hk := hCritical (v k)
    linarith only [hk]
  have hBandCost (k : ℕ) :
      M (v k) / 2 < 8 * ((((N (v k) : ℝ) + 1) + 1) ^ 8) * μ k := by
    have hWindow := (hWindows k).2
    have hAt := thirdFullPhysical_kineticWindow_rawEighthAnnularCost244
      hH3 hClass b hb (τ (v k)) (hWindows k).1
      (v k) (N (v k)) (M (v k)) (δ (v k)) hWindow
    dsimp only [μ]
    have hArithmetic : (((N (v k) : ℝ) + 1) + 1) =
        (N (v k) : ℝ) + 2 := by ring
    rw [hArithmetic]
    nlinarith only [hAt]
  have hCost : ∀ᶠ k : ℕ in atTop,
      M (v k) / 2 < 8 * ((((N (v k) : ℝ) + 1) + 1) ^ 8) * μ k :=
    Filter.Eventually.of_forall hBandCost
  have hEscape :=
    thirdFull_criticalEighthHeight_vanishingBand_forces_escape244
      (fun k : ℕ => ((v k : ℝ) + 1))
      (fun k : ℕ => ((N (v k) : ℝ) + 1))
      (fun k : ℕ => M (v k) / 2)
      μ η hR hQ hμ hη hHeight hCost hMass
  have hEscapeNormalized : Tendsto (fun k : ℕ =>
      ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop := by
    simpa only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using hEscape
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    (fun k => ⟨hIndex k, (hWindows k).2⟩),
    hMass, hNormalized, hEscapeNormalized⟩

end
end PrimeTensor.FirstMonomialTriad
