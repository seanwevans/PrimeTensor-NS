import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierSignedSourceWork
import Mathlib.Tactic

/-!
# Two-step physical highpass drain: viscous increment and Leray transfer

The exact projected Navier--Stokes source is Laplacian minus Leray forcing.
The physical Bochner FTC gives a two-step decomposition for the selected
sharp highpass velocity:

  H(s) = (H(x) + A_D) - A_N,

where A_D and A_N are the actual highpass projections of the individually
integrable time-integrated Laplacian and Leray source, respectively.
Polarization around the intermediate *viscous-only increment* H(x)+A_D
then produces the exact signed energy decomposition

  M(x)-M(s)
    = [M(x)-||H(x)+A_D||^2]
      + 2 <H(x)+A_D,A_N> - ||A_N||^2.

There is no assumption that H(x)+A_D is the heat semigroup evolution;
A_D integrates the actual time-dependent viscous source and the intermediate
state need not be contractive. The theorem isolates the extra *signed*
nonlinear Leray payment required when the prescribed carrier drain exceeds
this genuine viscous-only contribution, keeping its favorable negative
quadratic correction.

The final conditional physical gate consumes the previously proved no-Young-
growth source drain. It does not postulate a positive Leray pairing and does
not assert a terminal H3 continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact two-stage Hilbert polarization, with both the viscous-only energy
change and the *signed* Leray correction visible. -/
theorem thirdFullKinetic_twoStepViscousLeray_massLoss244
    (H A B : H3PhysicalRealFinVectorL2Hilbert) :
    ‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2 =
      (‖H‖ ^ 2 - ‖H + A‖ ^ 2) +
        2 * inner ℝ (H + A) B - ‖B‖ ^ 2 := by
  have hReassoc : H + (A - B) = (H + A) + (-B) := by abel
  rw [hReassoc, norm_add_sq_real]
  simp only [inner_neg_right, norm_neg]
  ring

/-- If a strict highpass drain exceeds the viscous-only drain, actual
Leray transfer is positively aligned with the intermediate state and
beats half its own quadratic increment. -/
theorem thirdFullKinetic_twoStepExcess_forcesLerayPairing244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (hExcess :
      ‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2 >
        ‖H‖ ^ 2 - ‖H + A‖ ^ 2) :
    ‖B‖ ^ 2 < 2 * inner ℝ (H + A) B ∧
      0 < inner ℝ (H + A) B := by
  have hIdentity := thirdFullKinetic_twoStepViscousLeray_massLoss244 H A B
  rw [hIdentity] at hExcess
  have hSq : 0 ≤ ‖B‖ ^ 2 := sq_nonneg _
  constructor <;> linarith only [hExcess, hSq]

/-- An already established strict quantitative kinetic-drain obligation
forces a genuinely signed Leray pairing if the viscous-only contribution
cannot pay the same obligation. No viscous sign is presumed. -/
theorem thirdFullKinetic_twoStepQuantitativeLerayGate244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (K epsilon : ℝ) (hK : 0 < K)
    (hForced : epsilon < K *
      (‖H‖ ^ 2 - ‖H + (A - B)‖ ^ 2))
    (hViscous : K * (‖H‖ ^ 2 - ‖H + A‖ ^ 2) ≤ epsilon) :
    0 < inner ℝ (H + A) B := by
  have hIdentity := thirdFullKinetic_twoStepViscousLeray_massLoss244 H A B
  rw [hIdentity] at hForced
  by_contra hNot
  have hInner : inner ℝ (H + A) B ≤ 0 := le_of_not_gt hNot
  have hKInner : K * (2 * inner ℝ (H + A) B) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hK.le (by linarith only [hInner])
  have hKSq : 0 ≤ K * (‖B‖ ^ 2) :=
    mul_nonneg hK.le (sq_nonneg _)
  nlinarith only [hForced, hViscous, hKInner, hKSq]

/-- The exact ACTUAL positive-time projected momentum FTC, split into
its individually Bochner-integrable physical viscous and Leray increments
and then projected into the same genuine sharp highpass. -/
theorem thirdFullPhysical_outerTwoStepViscousLeray_vectorFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) :
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Vs := h3AuditInitialOldPhysicalHilbertTotal hH3 s
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let Hs := Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs
    let JD : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
    let JN : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
    let A := JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD
    let B := JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN
    Hs = (Hx + A) - B := by
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let JD : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
  let JN : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let Hs : H3PhysicalRealFinVectorL2Hilbert :=
    Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs
  let A : H3PhysicalRealFinVectorL2Hilbert :=
    JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD
  let B : H3PhysicalRealFinVectorL2Hilbert :=
    JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN
  obtain ⟨hDInt, hNInt⟩ :=
    thirdFullPhysical_outerSourceComponents_intervalIntegrable244
      hH3 x s hx hs hxs
  have hJ : J = JD - JN := by
    dsimp only [J, JD, JN]
    change (∫ r in x..s,
      h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r) = _
    exact intervalIntegral.integral_sub hDInt hNInt
  have hDiff : Hs - Hx =
      J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J := by
    exact thirdFullPhysical_outerHighpassSourceVectorFTC244
      hH3 x s rho hx hs
  have hHigh :
      J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J = A - B := by
    dsimp only [A, B]
    rw [hJ, thirdFullPhysical_sharpVectorLowCutoff_sub244 rho JD JN]
    abel
  change Hs = (Hx + A) - B
  rw [hHigh] at hDiff
  calc
    Hs = (Hs - Hx) + Hx := by abel
    _ = (A - B) + Hx := by rw [hDiff]
    _ = (Hx + A) - B := by abel

/-- Actual physical two-step identity: all four states are the
established physical L2 and Fourier-cutoff objects, not formal placeholders. -/
theorem thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) :
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let JD : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
    let JN : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
    let A := JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD
    let B := JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      (‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2) +
        2 * inner ℝ (Hx + A) B - ‖B‖ ^ 2 := by
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let Hs : H3PhysicalRealFinVectorL2Hilbert :=
    Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs
  let JD : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
  let JN : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
  let A : H3PhysicalRealFinVectorL2Hilbert :=
    JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD
  let B : H3PhysicalRealFinVectorL2Hilbert :=
    JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN
  have hVector : Hs = (Hx + A) - B :=
    thirdFullPhysical_outerTwoStepViscousLeray_vectorFTC244
      hH3 x s rho hx hs hxs
  change ‖Hx‖ ^ 2 - ‖Hs‖ ^ 2 =
    (‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2) +
      2 * inner ℝ (Hx + A) B - ‖B‖ ^ 2
  rw [hVector]
  have hEq : (Hx + A) - B = Hx + (A - B) := by abel
  rw [hEq]
  exact thirdFullKinetic_twoStepViscousLeray_massLoss244 Hx A B

/-- Physical Leray transfer is strictly positive if actual sharp highpass
mass drops more than the real time-integrated viscous-only increment pays.
The conclusion also controls half the nonlinear quadratic increment. -/
theorem thirdFullPhysical_outerExcessDrain_forcesLerayTransfer244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) :
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let JD : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
    let JN : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
    let A := JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD
    let B := JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN
    ∀ (hExcess :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho >
          ‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2),
      ‖B‖ ^ 2 < 2 * inner ℝ (Hx + A) B ∧
        0 < inner ℝ (Hx + A) B := by
  intro Vx Hx JD JN A B hExcess
  have hExact := thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    hH3 x s rho hx hs hxs
  -- Introduce all six theorem-level `let` binders before the proof hypothesis.
  have hExcess' :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho >
          ‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2 := hExcess
  change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      (‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2) +
        2 * inner ℝ (Hx + A) B - ‖B‖ ^ 2 at hExact
  rw [hExact] at hExcess'
  have hSq : 0 ≤ ‖B‖ ^ 2 := sq_nonneg _
  constructor <;> linarith only [hExcess', hSq]


/-- If a selected no-Young-growth carrier already has a strictly required
highpass drain, and the genuine viscous-only increment cannot pay it,
then the remaining payment is necessarily a positively aligned nonlinear
Leray transfer. The signed quadratic nonlinear correction is retained. -/
theorem thirdFullPhysical_outerForcedDrain_beyondViscous_forcesLeray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho K epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s)
    (hK : 0 < K) :
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let JD : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
    let JN : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
    let A := JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD
    let B := JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN
    ∀ (hForced : epsilon < K *
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho))
      (hViscous : K * (‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2) ≤ epsilon),
      0 < inner ℝ (Hx + A) B := by
  intro Vx Hx JD JN A B hForced hViscous
  have hExact := thirdFullPhysical_outerTwoStepViscousLeray_energyExact244
    hH3 x s rho hx hs hxs
  change thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      (‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2) +
        2 * inner ℝ (Hx + A) B - ‖B‖ ^ 2 at hExact
  have hForced' :
      epsilon < K *
        (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) := hForced
  have hViscous' :
      K * (‖Hx‖ ^ 2 - ‖Hx + A‖ ^ 2) ≤ epsilon := hViscous
  rw [hExact] at hForced'
  have hHilbert := thirdFullKinetic_twoStepViscousLeray_massLoss244 Hx A B
  rw [← hHilbert] at hForced'
  exact thirdFullKinetic_twoStepQuantitativeLerayGate244
    Hx A B K epsilon hK hForced' hViscous'

end
end PrimeTensor.FirstMonomialTriad
