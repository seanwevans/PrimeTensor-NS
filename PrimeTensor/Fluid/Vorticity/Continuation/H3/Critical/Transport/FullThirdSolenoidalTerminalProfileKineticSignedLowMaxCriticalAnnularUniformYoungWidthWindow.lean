import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularUniformYoungWidthModulus
import Mathlib.Tactic

/-!
# One actual-time window for all bounded annular Young-width costs

Fix one strictly positive physical time x and one finite radial ceiling R.
The already kernel-proved two-state modulus for the *original* nonlinear
Young-gap plus physical width cost is independent of the individual annulus.
The coefficient in that estimate is a continuous function of the actual H3
spectral state. Consequently the actual strong spectral continuity supplies
one positive time window for *every* 0 <= rho <= sigma <= R simultaneously.

No temporal derivative of the nonlinear source and no fourth or sixth
spatial Sobolev norm is required. The radius R is fixed; nothing in this
module asserts uniform control as R tends to infinity. This also does not
assert simultaneous persistence of the kinetic excess or deficit, whose
physical highpass term must be charged separately.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularUniformYoungWindow244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularUniformYoungWindow244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- With its second argument fixed, the full cutoff-independent coefficient
is strongly continuous in the first H3 input. This is the missing local
boundedness step needed to turn a two-state modulus into a single window
for an entire (uncountable) family of annuli. -/
theorem thirdFullPhysical_annularFullYoungWidthModulus_continuous_left244
    (R : ℝ) (U : H3SpectralVelocityState) :
    Continuous (fun V : H3SpectralVelocityState =>
      thirdFullPhysicalAnnularFullYoungWidthModulus244 R V U) := by
  change Continuous (fun V : H3SpectralVelocityState =>
    ∑ j : Fin 3,
      ((8 * R ^ 6) *
        (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖ +
         ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) *
        ((576 * Real.pi * h3SobolevDeweightingConstant) *
          (‖V‖ + ‖U‖) + 2) +
       (8 * R ^ 10) * (‖V‖ + ‖U‖)))
  apply continuous_finsetSum Finset.univ
  intro j _
  have hResidual : Continuous (fun V : H3SpectralVelocityState =>
      ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) :=
    (thirdFullPhysical_annularYoungResidualFourier_continuous244 j).norm
  have hMass : Continuous (fun V : H3SpectralVelocityState => ‖V‖) :=
    continuous_norm
  have hMassSum := hMass.add
    (continuous_const : Continuous (fun _ : H3SpectralVelocityState => ‖U‖))
  change Continuous (fun V : H3SpectralVelocityState =>
    ‖V‖ + ‖U‖) at hMassSum
  have hResidualSum := hResidual.add
    (continuous_const : Continuous (fun _ : H3SpectralVelocityState =>
      ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖))
  change Continuous (fun V : H3SpectralVelocityState =>
    ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖ +
      ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖)
    at hResidualSum
  have hLinear :=
    ((continuous_const : Continuous (fun _ : H3SpectralVelocityState =>
        (576 * Real.pi * h3SobolevDeweightingConstant))).mul
      hMassSum).add
      (continuous_const : Continuous (fun _ : H3SpectralVelocityState => (2 : ℝ)))
  change Continuous (fun V : H3SpectralVelocityState =>
    (576 * Real.pi * h3SobolevDeweightingConstant) *
      (‖V‖ + ‖U‖) + 2) at hLinear
  have hYoung :=
    ((continuous_const : Continuous (fun _ : H3SpectralVelocityState =>
        (8 * R ^ 6 : ℝ))).mul hResidualSum).mul hLinear
  change Continuous (fun V : H3SpectralVelocityState =>
    (8 * R ^ 6) *
      (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖ +
       ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) *
      ((576 * Real.pi * h3SobolevDeweightingConstant) *
        (‖V‖ + ‖U‖) + 2)) at hYoung
  have hWidth :=
    (continuous_const : Continuous (fun _ : H3SpectralVelocityState =>
      (8 * R ^ 10 : ℝ))).mul hMassSum
  change Continuous (fun V : H3SpectralVelocityState =>
    (8 * R ^ 10) * (‖V‖ + ‖U‖)) at hWidth
  have hResult := hYoung.add hWidth
  change Continuous (fun V : H3SpectralVelocityState =>
    (8 * R ^ 6) *
      (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖ +
       ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖) *
      ((576 * Real.pi * h3SobolevDeweightingConstant) *
        (‖V‖ + ‖U‖) + 2) +
    (8 * R ^ 10) * (‖V‖ + ‖U‖)) at hResult
  exact hResult

/-- The ACTUAL original Young-gap/width functional is uniformly continuous
at a single strict physical time, with one common temporal radius for all
real annuli within any fixed finite upper radius R. The coefficient is not
assumed bounded: its local bound follows from strong actual H3 continuity. -/
theorem thirdFullPhysical_actualYoungWidth_uniformAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R x : ℝ) (hR : 0 ≤ R) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (epsilon : ℝ) (hEps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, dist s x < delta →
        ∀ rho sigma : ℝ, 0 ≤ rho → rho ≤ sigma → sigma ≤ R →
          |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| <
            epsilon := by
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let M : ℝ → ℝ := fun s =>
    thirdFullPhysicalAnnularFullYoungWidthModulus244 R (U s) (U x)
  let L : ℝ := M x + 1
  have hL : 0 < L := by
    have hNonneg : 0 ≤ M x := by
      dsimp only [M]
      exact thirdFullPhysical_annularFullYoungWidthModulus_nonneg244
        R hR (U x) (U x)
    dsimp only [L]
    linarith only [hNonneg]
  have hState : ContinuousAt U x :=
    h3Audit_initialActualSpectralVelocity_continuousAt hH3 hx
  have hMod : ContinuousAt M x := by
    exact (thirdFullPhysical_annularFullYoungWidthModulus_continuous_left244
      R (U x)).continuousAt.comp hState
  obtain ⟨rM, hrM, hNearM⟩ :=
    (Metric.continuousAt_iff.mp hMod) 1 (by norm_num)
  obtain ⟨rU, hrU, hNearU⟩ :=
    (Metric.continuousAt_iff.mp hState) (epsilon / L) (div_pos hEps hL)
  refine ⟨min rM rU, lt_min hrM hrU, ?_⟩
  intro s hs rho sigma hRho hOrder hUpper
  have hsM : dist s x < rM :=
    lt_of_lt_of_le hs (min_le_left _ _)
  have hsU : dist s x < rU :=
    lt_of_lt_of_le hs (min_le_right _ _)
  have hMNear : dist (M s) (M x) < 1 := hNearM hsM
  have hMBound : M s ≤ L := by
    rw [Real.dist_eq] at hMNear
    have hUp := (abs_lt.mp hMNear).2
    dsimp only [L]
    linarith only [hUp]
  have hUNear : ‖U s - U x‖ < epsilon / L := by
    simpa only [dist_eq_norm] using hNearU hsU
  have hBasic := thirdFullPhysical_actualAnnularYoungWidth_uniformTwoTime244
    hH3 rho sigma R s x hRho hOrder hUpper
  change |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| ≤
    M s * ‖U s - U x‖ at hBasic
  have hProduct : L * ‖U s - U x‖ < epsilon := by
    have h := (lt_div_iff₀ hL).mp hUNear
    nlinarith only [h]
  calc
    |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| ≤
      M s * ‖U s - U x‖ := hBasic
    _ ≤ L * ‖U s - U x‖ :=
      mul_le_mul_of_nonneg_right hMBound (norm_nonneg _)
    _ < epsilon := hProduct

/-- A SINGLE positive right-time window preserves an arbitrarily prescribed
Young-width error tolerance for *every* bounded annulus simultaneously.
This uses the original physical Young integral, not an abstract surrogate. -/
theorem thirdFullPhysical_actualYoungWidth_uniformRightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R x : ℝ) (hR : 0 ≤ R) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (epsilon : ℝ) (hEps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        ∀ rho sigma : ℝ, 0 ≤ rho → rho ≤ sigma → sigma ≤ R →
          |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| <
            epsilon := by
  obtain ⟨r, hr, hNear⟩ :=
    thirdFullPhysical_actualYoungWidth_uniformAt244 hH3 R x hR hx epsilon hEps
  let delta : ℝ := min (r / 2) ((T - x) / 2)
  have hDelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by linarith only [hr]) (by linarith only [hx.2])
  have hUpper : delta ≤ (T - x) / 2 :=
    min_le_right _ _
  have hEnd : x + delta < T := by
    linarith only [hUpper, hx.2]
  refine ⟨delta, hDelta, hEnd, ?_⟩
  intro s hs rho sigma hRho hOrder hSigma
  have hDist : dist s x < r := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have hLeft : delta ≤ r / 2 := min_le_left _ _
    linarith only [hs.2, hLeft, hr]
  exact hNear s hDist rho sigma hRho hOrder hSigma

/-- Any uniform strict upper margin for a bounded annular family persists
on the SAME positive right-time interval, with no choice of a separate
radius-dependent window for each member of the family. -/
theorem thirdFullPhysical_actualYoungWidth_uniformUpperMarginWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R x threshold epsilon : ℝ) (hR : 0 ≤ R)
    (hx : x ∈ Set.Ioo (0 : ℝ) T) (hEps : 0 < epsilon)
    (hMargin : ∀ rho sigma : ℝ,
      0 ≤ rho → rho ≤ sigma → sigma ≤ R →
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma +
          epsilon ≤ threshold) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        ∀ rho sigma : ℝ, 0 ≤ rho → rho ≤ sigma → sigma ≤ R →
          thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
            threshold := by
  obtain ⟨delta, hd, hEnd, hNear⟩ :=
    thirdFullPhysical_actualYoungWidth_uniformRightWindow244
      hH3 R x hR hx epsilon hEps
  refine ⟨delta, hd, hEnd, ?_⟩
  intro s hs rho sigma hRho hOrder hUpper
  have h := hNear s hs rho sigma hRho hOrder hUpper
  have hAt := hMargin rho sigma hRho hOrder hUpper
  have hUp := (abs_lt.mp h).2
  linarith only [hAt, hUp]

/-- The real physical sharp highpass has a radius-independent quadratic
variation estimate. Unlike the Fourier two-cutoff estimate, the genuine
physical highpass is itself contractive, so no artificial factor two occurs. -/
theorem thirdFullPhysical_sharpHighpassSquare_uniformVariation244
    (rho : ℝ) (V W : H3PhysicalRealFinVectorL2Hilbert) :
    |‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 -
      ‖W - thirdFullPhysicalSharpLowCutoffHilbert244 rho W‖ ^ 2| ≤
      ‖V - W‖ * (‖V‖ + ‖W‖) := by
  let A : H3PhysicalRealFinVectorL2Hilbert :=
    V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V
  let B : H3PhysicalRealFinVectorL2Hilbert :=
    W - thirdFullPhysicalSharpLowCutoffHilbert244 rho W
  have hA : ‖A‖ ≤ ‖V‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V
  have hB : ‖B‖ ≤ ‖W‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 rho W
  have hDiff : ‖A - B‖ ≤ ‖V - W‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_sub_le244 rho V W
  have hPositive : 0 ≤ ‖A‖ + ‖B‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  change |‖A‖ ^ 2 - ‖B‖ ^ 2| ≤ ‖V - W‖ * (‖V‖ + ‖W‖)
  calc
    |‖A‖ ^ 2 - ‖B‖ ^ 2| =
        |‖A‖ - ‖B‖| * (‖A‖ + ‖B‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg hPositive]
      ac_rfl
    _ ≤ ‖A - B‖ * (‖A‖ + ‖B‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le A B) hPositive
    _ ≤ ‖V - W‖ * (‖A‖ + ‖B‖) :=
      mul_le_mul_of_nonneg_right hDiff hPositive
    _ ≤ ‖V - W‖ * (‖V‖ + ‖W‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hB) (norm_nonneg _)

/-- This modulus applies to the original physical kinetic highpass at
arbitrary real times, with a constant that is independent of rho. -/
theorem thirdFullPhysical_actualSharpHighMass_uniformTwoTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (rho s t : ℝ) :
    let V := h3AuditInitialOldPhysicalHilbertTotal hH3 s
    let W := h3AuditInitialOldPhysicalHilbertTotal hH3 t
    |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho| ≤
      ‖V - W‖ * (‖V‖ + ‖W‖) := by
  exact thirdFullPhysical_sharpHighpassSquare_uniformVariation244 rho _ _

/-- Strong actual physical L² continuity yields a SINGLE time radius for
all physical highpass kinetic masses, independently of the cutoff rho. -/
theorem thirdFullPhysical_actualSharpHighMass_uniformAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x epsilon : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hEps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, dist s x < delta →
        ∀ rho : ℝ,
          |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| <
            epsilon := by
  let V : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let L : ℝ := 2 * ‖V x‖ + 1
  have hL : 0 < L := by
    dsimp only [L]
    have hN := norm_nonneg (V x)
    linarith only [hN]
  have hState : ContinuousAt V x :=
    h3Audit_initialOldPhysicalHilbert_continuousAt hH3 hx
  obtain ⟨rOne, hrOne, hNearOne⟩ :=
    (Metric.continuousAt_iff.mp hState) 1 (by norm_num)
  obtain ⟨rEps, hrEps, hNearEps⟩ :=
    (Metric.continuousAt_iff.mp hState) (epsilon / L) (div_pos hEps hL)
  refine ⟨min rOne rEps, lt_min hrOne hrEps, ?_⟩
  intro s hs rho
  have hsOne : dist s x < rOne :=
    lt_of_lt_of_le hs (min_le_left _ _)
  have hsEps : dist s x < rEps :=
    lt_of_lt_of_le hs (min_le_right _ _)
  have hDiffOne : ‖V s - V x‖ < 1 := by
    simpa only [dist_eq_norm] using hNearOne hsOne
  have hDiffSmall : ‖V s - V x‖ < epsilon / L := by
    simpa only [dist_eq_norm] using hNearEps hsEps
  have hTriangle : ‖V s‖ ≤ ‖V s - V x‖ + ‖V x‖ := by
    calc
      ‖V s‖ = ‖(V s - V x) + V x‖ := by rw [sub_add_cancel]
      _ ≤ ‖V s - V x‖ + ‖V x‖ := norm_add_le _ _
  have hSum : ‖V s‖ + ‖V x‖ ≤ L := by
    dsimp only [L]
    linarith only [hTriangle, hDiffOne]
  have hBasic := thirdFullPhysical_actualSharpHighMass_uniformTwoTime244
    hH3 rho s x
  change |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
      ‖V s - V x‖ * (‖V s‖ + ‖V x‖) at hBasic
  have hProduct : ‖V s - V x‖ * L < epsilon :=
    (lt_div_iff₀ hL).mp hDiffSmall
  calc
    |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
      ‖V s - V x‖ * (‖V s‖ + ‖V x‖) := hBasic
    _ ≤ ‖V s - V x‖ * L :=
      mul_le_mul_of_nonneg_left hSum (norm_nonneg _)
    _ < epsilon := hProduct

/-- A SINGLE common physical interval now controls BOTH components required
by the annular deficit: genuine nonlinear cubic Young-width cost and genuine
physical kinetic highpass mass. No radius-dependent time windows remain for
either component at fixed finite R. -/
theorem thirdFullPhysical_actualAnnularCosts_jointRightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R x epsilonY epsilonM : ℝ) (hR : 0 ≤ R)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hEpsY : 0 < epsilonY) (hEpsM : 0 < epsilonM) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        (∀ rho sigma : ℝ, 0 ≤ rho → rho ≤ sigma → sigma ≤ R →
          |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| <
            epsilonY) ∧
        (∀ rho : ℝ,
          |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| <
            epsilonM) := by
  obtain ⟨deltaY, hdY, hEndY, hYoung⟩ :=
    thirdFullPhysical_actualYoungWidth_uniformRightWindow244
      hH3 R x hR hx epsilonY hEpsY
  obtain ⟨rM, hrM, hMass⟩ :=
    thirdFullPhysical_actualSharpHighMass_uniformAt244
      hH3 x epsilonM hx hEpsM
  let delta : ℝ := min deltaY (rM / 2)
  have hd : 0 < delta := by
    dsimp only [delta]
    exact lt_min hdY (by linarith only [hrM])
  have hLeY : delta ≤ deltaY := min_le_left _ _
  have hLeM : delta ≤ rM / 2 := min_le_right _ _
  have hEnd : x + delta < T := by
    linarith only [hLeY, hEndY]
  refine ⟨delta, hd, hEnd, ?_⟩
  intro s hs
  have hsY : s ∈ Set.Icc x (x + deltaY) := by
    exact ⟨hs.1, by linarith only [hs.2, hLeY]⟩
  have hDist : dist s x < rM := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith only [hs.2, hLeM, hrM]
  exact ⟨hYoung s hsY, hMass s hDist⟩

end
end PrimeTensor.FirstMonomialTriad
