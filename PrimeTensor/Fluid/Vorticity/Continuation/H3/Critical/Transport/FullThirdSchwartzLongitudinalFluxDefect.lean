import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzPhysicalFluxIdentity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientCanonicalClosure244
import Mathlib.Tactic

/-!
# Full H³ sixth-power Fourier flux with the exact longitudinal remainder

For arbitrary complex Fourier polarizations, the corrected full physical
six-orbit is NOT in general the three sixth-power transfers alone. The
missing terms are precisely three multiples of the longitudinal Fourier
contractions p·A, q·B and r·C. We prove the defect polynomial with no
solenoidality premise. Its corrected integral is unconditionally valid for
arbitrary complex Schwartz fields, and it recovers the signed real physical
commutator with the exact coefficient (2π)^7/3.

Crucially, the project's existing matched Schwartz approximants for a
physical H³ state are NOT assumed to be solenoidal. Keeping this explicit
remainder produces a rigorous Fourier-flux representation of their canonical
limit, without adding a false divergence-free hypothesis to that family.

No assertion is made here that the longitudinal remainder tends to zero.
That is the next analytic problem, separate from identifying the true old
physical top transport with the canonical H³ completion.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdLongitudinalFlux244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The entire correction to the solenoidal sixth-power symbol. Every term
contains exactly one longitudinal divergence contraction. These are
COMPLEX-bilinear amplitudes, not Hermitian polarization products. -/
noncomputable def thirdFullComplexLongitudinalFluxDefect244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) : ℂ :=
  let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
  let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
  let c : ℂ := (thirdTriadAxisDot244 q r : ℂ)
  ((-((thirdFullComplexPolarizationDot244 B C * mixedDot p A) * b *
      (b ^ 2 + 3 * b * c + 3 * c ^ 2))) -
    ((thirdFullComplexPolarizationDot244 A C * mixedDot q B) * c *
      (3 * b ^ 2 + 3 * b * c + c ^ 2))) -
    ((thirdFullComplexPolarizationDot244 A B * mixedDot r C) * c *
      (3 * a ^ 2 + 3 * a * c + c ^ 2))

private theorem thirdFullLongitudinalDot_comm244 (A B : A3 → ℂ) :
    thirdFullComplexPolarizationDot244 A B =
      thirdFullComplexPolarizationDot244 B A := by
  unfold thirdFullComplexPolarizationDot244
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Universal 12-term complex polynomial: remove NO longitudinal mode.
The unbalanced terms are linear in the three exact Fourier divergences. -/
private theorem thirdFullLongitudinal_scalar_identity244
    (a b c X Y Z t s u α β γ : ℂ) :
    (X * t) * (a ^ 3 + 3 * a ^ 2 * b) +
      (Y * s) * (3 * a ^ 2 * b) +
    (Y * s) * (b ^ 3 + 3 * b ^ 2 * a) +
      (X * t) * (3 * b ^ 2 * a) +
    (Z * u) * (a ^ 3 + 3 * a ^ 2 * c) +
      (Y * (-s - γ)) * (3 * a ^ 2 * c) +
    (Y * (-s - γ)) * (c ^ 3 + 3 * c ^ 2 * a) +
      (Z * u) * (3 * c ^ 2 * a) +
    (Z * (-u - α)) * (b ^ 3 + 3 * b ^ 2 * c) +
      (X * (-t - β)) * (3 * b ^ 2 * c) +
    (X * (-t - β)) * (c ^ 3 + 3 * c ^ 2 * b) +
      (Z * (-u - α)) * (3 * c ^ 2 * b) =
    (X * t) * ((-(b + c)) ^ 3 - (-(a + b)) ^ 3) +
    (Y * s) * ((-(a + c)) ^ 3 - (-(a + b)) ^ 3) +
    (Z * u) * ((-(b + c)) ^ 3 - (-(a + c)) ^ 3) -
    (Z * α) * b * (b ^ 2 + 3 * b * c + 3 * c ^ 2) -
    (X * β) * c * (3 * b ^ 2 + 3 * b * c + c ^ 2) -
    (Y * γ) * c * (3 * a ^ 2 + 3 * a * c + c ^ 2) := by
  ring

/-- Momentum conservation alone suffices: the six genuine gradient plus
interpolation orderings equal three sixth-power transfers PLUS the exact
longitudinal defect. No Fourier divergence hypothesis is used or hidden. -/
theorem thirdFullComplexSix_eq_flux_add_longitudinal244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0) :
    thirdFullComplexSixSymbol244 p q r A B C =
      thirdFullComplexSixthPowerFlux244 p q r A B C +
        thirdFullComplexLongitudinalFluxDefect244 p q r A B C := by
  have hmA := thirdFullComplex_momentum_dot244 p q r A hm
  have hmB := thirdFullComplex_momentum_dot244 p q r B hm
  have hmC := thirdFullComplex_momentum_dot244 p q r C hm
  have hAq : mixedDot q A = -mixedDot r A - mixedDot p A := by
    calc
      _ = (mixedDot p A + mixedDot q A + mixedDot r A) -
            mixedDot r A - mixedDot p A := by ring
      _ = _ := by rw [hmA]; ring
  have hBp : mixedDot p B = -mixedDot r B - mixedDot q B := by
    calc
      _ = (mixedDot p B + mixedDot q B + mixedDot r B) -
            mixedDot r B - mixedDot q B := by ring
      _ = _ := by rw [hmB]; ring
  have hCp : mixedDot p C = -mixedDot q C - mixedDot r C := by
    calc
      _ = (mixedDot p C + mixedDot q C + mixedDot r C) -
            mixedDot q C - mixedDot r C := by ring
      _ = _ := by rw [hmC]; ring
  have hqp := thirdFullAxisDot_comm244 q p
  have hrp := thirdFullAxisDot_comm244 r p
  have hrq := thirdFullAxisDot_comm244 r q
  have hBA := thirdFullLongitudinalDot_comm244 B A
  have hCA := thirdFullLongitudinalDot_comm244 C A
  have hCB := thirdFullLongitudinalDot_comm244 C B
  let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
  let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
  let c : ℂ := (thirdTriadAxisDot244 q r : ℂ)
  let P : ℂ := (thirdTriadAxisDot244 p p : ℂ)
  let Q : ℂ := (thirdTriadAxisDot244 q q : ℂ)
  let R : ℂ := (thirdTriadAxisDot244 r r : ℂ)
  let X : ℂ := thirdFullComplexPolarizationDot244 A C
  let Y : ℂ := thirdFullComplexPolarizationDot244 A B
  let Z : ℂ := thirdFullComplexPolarizationDot244 B C
  let t : ℂ := mixedDot r B
  let s : ℂ := mixedDot q C
  let u : ℂ := mixedDot r A
  let α : ℂ := mixedDot p A
  let β : ℂ := mixedDot q B
  let γ : ℂ := mixedDot r C
  have hpRaw := momentum_dot p q r p hm
  have hqRaw := momentum_dot p q r q hm
  have hrRaw := momentum_dot p q r r hm
  change thirdTriadAxisDot244 p p + thirdTriadAxisDot244 q p +
    thirdTriadAxisDot244 r p = 0 at hpRaw
  change thirdTriadAxisDot244 p q + thirdTriadAxisDot244 q q +
    thirdTriadAxisDot244 r q = 0 at hqRaw
  change thirdTriadAxisDot244 p r + thirdTriadAxisDot244 q r +
    thirdTriadAxisDot244 r r = 0 at hrRaw
  rw [hqp, hrp] at hpRaw
  rw [hrq] at hqRaw
  have hpC : P + a + b = 0 := by
    dsimp only [P, a, b]
    exact_mod_cast hpRaw
  have hqC : a + Q + c = 0 := by
    dsimp only [a, Q, c]
    exact_mod_cast hqRaw
  have hrC : b + c + R = 0 := by
    dsimp only [b, c, R]
    exact_mod_cast hrRaw
  have hP : P = -(a + b) := by
    calc
      P = (P + a + b) - (a + b) := by ring
      _ = -(a + b) := by rw [hpC]; ring
  have hQ : Q = -(a + c) := by
    calc
      Q = (a + Q + c) - (a + c) := by ring
      _ = -(a + c) := by rw [hqC]; ring
  have hR : R = -(b + c) := by
    calc
      R = (b + c + R) - (b + c) := by ring
      _ = -(b + c) := by rw [hrC]; ring
  have hSix : thirdFullComplexSixSymbol244 p q r A B C =
      (X * t) * (a ^ 3 + 3 * a ^ 2 * b) +
        (Y * s) * (3 * a ^ 2 * b) +
      (Y * s) * (b ^ 3 + 3 * b ^ 2 * a) +
        (X * t) * (3 * b ^ 2 * a) +
      (Z * u) * (a ^ 3 + 3 * a ^ 2 * c) +
        (Y * (-s - γ)) * (3 * a ^ 2 * c) +
      (Y * (-s - γ)) * (c ^ 3 + 3 * c ^ 2 * a) +
        (Z * u) * (3 * c ^ 2 * a) +
      (Z * (-u - α)) * (b ^ 3 + 3 * b ^ 2 * c) +
        (X * (-t - β)) * (3 * b ^ 2 * c) +
      (X * (-t - β)) * (c ^ 3 + 3 * c ^ 2 * b) +
        (Z * (-u - α)) * (3 * c ^ 2 * b) := by
    unfold thirdFullComplexSixSymbol244 thirdFullComplexOrderedSymbol244
    simp only [hqp, hrp, hrq, hBA, hCA, hCB, hAq, hBp, hCp]
    dsimp only [a, b, c, X, Y, Z, t, s, u, α, β, γ]
    ring
  have hFlux : thirdFullComplexSixthPowerFlux244 p q r A B C =
      (X * t) * (R ^ 3 - P ^ 3) +
      (Y * s) * (Q ^ 3 - P ^ 3) +
      (Z * u) * (R ^ 3 - Q ^ 3) := by
    rfl
  have hDef : thirdFullComplexLongitudinalFluxDefect244 p q r A B C =
      -((Z * α) * b * (b ^ 2 + 3 * b * c + 3 * c ^ 2)) -
      ((X * β) * c * (3 * b ^ 2 + 3 * b * c + c ^ 2)) -
      ((Y * γ) * c * (3 * a ^ 2 + 3 * a * c + c ^ 2)) := by
    rfl
  rw [hSix, hFlux, hDef, hP, hQ, hR]
  calc
    _ = _ := thirdFullLongitudinal_scalar_identity244 a b c X Y Z t s u α β γ
    _ = _ := by ring

/-- The defect reduces identically to zero for exactly transverse Fourier
polarizations. This is a check on the unrestricted identity, not an
additional assumption in the corrected formula below. -/
theorem thirdFullComplexLongitudinalFluxDefect_zero_of_solenoidal244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hA : mixedDot p A = 0) (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0) :
    thirdFullComplexLongitudinalFluxDefect244 p q r A B C = 0 := by
  simp [thirdFullComplexLongitudinalFluxDefect244, hA, hB, hC]

/-- Apply the exact longitudinal correction to genuine Fourier transforms
of an arbitrary complex Schwartz velocity, not frozen polarizations. -/
noncomputable def thirdFullSchwartzLongitudinalFluxDefect244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  let U := h3SchwartzTriadPolarization u
  thirdFullComplexLongitudinalFluxDefect244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
    (U (WithLp.ofLp z.1))
    (U (WithLp.ofLp (-(z.1 + z.2))))
    (U (WithLp.ofLp z.2))

/-- The arbitrary-Schwartz pointwise version, with NO spectral-divergence
premise and NO conjugated amplitude. -/
theorem thirdFullSchwartzComplexSix_eq_flux_add_longitudinal244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    thirdFullSchwartzComplexSixSymbol244 u z =
      thirdFullSchwartzComplexSixthPowerFlux244 u z +
        thirdFullSchwartzLongitudinalFluxDefect244 u z := by
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  have hm : ∀ i, p i + q i + r i = 0 := by
    intro i
    change (WithLp.ofLp z.1) i +
      (WithLp.ofLp (-(z.1 + z.2))) i + (WithLp.ofLp z.2) i = 0
    simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
    abel
  exact thirdFullComplexSix_eq_flux_add_longitudinal244 p q r
    (h3SchwartzTriadPolarization u p)
    (h3SchwartzTriadPolarization u q)
    (h3SchwartzTriadPolarization u r) hm

/-- The corrected (flux plus divergence) integrand is absolutely integrable
for *every* complex Schwartz vector, even if it is not solenoidal. -/
theorem thirdFullSchwartz_correctedFlux_integrable244
    (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (fun z : V3 × V3 =>
      thirdFullSchwartzComplexSixthPowerFlux244 u z +
        thirdFullSchwartzLongitudinalFluxDefect244 u z)
      (volume.prod volume) := by
  have hSix := thirdFullSchwartzComplexSix_integrable_of_ordered244 u
    (thirdFullSchwartzComplexOrderedKernel_integrable244 u)
  exact hSix.congr (Filter.Eventually.of_forall (fun z =>
    thirdFullSchwartzComplexSix_eq_flux_add_longitudinal244 u z))

/-- For unrestricted complex Schwartz velocities the exact *corrected*
radial flux integral, not the uncorrected solenoidal one, is six times the
fully physical ordered H³ Fourier kernel. No extra integrability premise. -/
theorem thirdFullSchwartz_correctedFlux_integral244
    (u : A3 → SchwartzMap V3 ℂ) :
    (∫ z : V3 × V3,
      (thirdFullSchwartzComplexSixthPowerFlux244 u z +
        thirdFullSchwartzLongitudinalFluxDefect244 u z)
        ∂volume.prod volume) =
      6 * ∫ z : V3 × V3,
        thirdFullSchwartzComplexOrderedKernel244 u z
          ∂volume.prod volume := by
  calc
    _ = ∫ z : V3 × V3,
        thirdFullSchwartzComplexSixSymbol244 u z
          ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z =>
        (thirdFullSchwartzComplexSix_eq_flux_add_longitudinal244 u z).symm)
    _ = ∫ z : V3 × V3,
        h3TriadSixOrbit (thirdFullSchwartzComplexOrderedKernel244 u) z
          ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (thirdFullSchwartzComplexSix_eq_sixOrbit244 u)
    _ = _ := h3TriadSixOrbit_integral
      (thirdFullSchwartzComplexOrderedKernel244 u)
      (thirdFullSchwartzComplexOrderedKernel_integrable244 u)

/-- Physical complex coefficient with explicit Fourier-divergence defect.
This identity remains exact even for a Schwartz approximation whose
components are not solenoidal. -/
theorem fullThirdSchwartzFourierCoefficient_eq_correctedFlux244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullThirdSchwartzFourierCoefficient244 f =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 / 3) *
        (∫ z : V3 × V3,
          (thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f j)) z +
           thirdFullSchwartzLongitudinalFluxDefect244
            (fun j => h3SchwartzComplexify (f j)) z)
            ∂volume.prod volume) := by
  let v : A3 → SchwartzMap V3 ℂ := fun j => h3SchwartzComplexify (f j)
  have hCoeff := fullThirdSchwartzFourierCoefficient_eq_physicalHalfIntegral244 f
  have hInt : (∫ z : V3 × V3,
      thirdFullSchwartzPhysicalHalfSevenKernel244 v z
        ∂volume.prod volume) =
      ∫ z : V3 × V3,
        thirdFullSchwartzComplexOrderedKernel244 v z
          ∂volume.prod volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (thirdFullSchwartzPhysicalHalfSeven_eq_ordered244 v)
  change fullThirdSchwartzFourierCoefficient244 f =
    2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      (∫ z : V3 × V3,
        thirdFullSchwartzPhysicalHalfSevenKernel244 v z
          ∂volume.prod volume) at hCoeff
  rw [hInt] at hCoeff
  have hFlux := thirdFullSchwartz_correctedFlux_integral244 v
  calc
    fullThirdSchwartzFourierCoefficient244 f =
        2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          (∫ z : V3 × V3,
            thirdFullSchwartzComplexOrderedKernel244 v z
              ∂volume.prod volume) := hCoeff
    _ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 / 3) *
          (6 * (∫ z : V3 × V3,
            thirdFullSchwartzComplexOrderedKernel244 v z
              ∂volume.prod volume)) := by ring
    _ = _ := by rw [hFlux]

/-- Exact REAL physical full-third commutator from the full six-order
Fourier flux WITH the longitudinal remainder, without any divergence-free
assumption on the real Schwartz velocity. -/
theorem fullSchwartzThirdCommutator_eq_correctedFlux244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzThirdCommutator244 f =
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          (thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f j)) z +
           thirdFullSchwartzLongitudinalFluxDefect244
            (fun j => h3SchwartzComplexify (f j)) z)
            ∂volume.prod volume).im := by
  rw [fullSchwartzThirdCommutator_eq_fullFourierRe244,
    fullThirdSchwartzFourierCoefficient_eq_correctedFlux244 f]
  exact fullThirdSeventhPhase_divThree_real_eq_imag244 _

/-- Every already-constructed derivative-matched Schwartz completion now
admits an exact corrected Fourier-flux limit. Crucially, *no claim* is made
that its approximants are solenoidal, or that the defect has vanished. -/
theorem h3MatchedSchwartz_correctedFlux_tendsto244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U) :
    Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          (thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z +
           thirdFullSchwartzLongitudinalFluxDefect244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z)
            ∂volume.prod volume).im)
      atTop (𝓝 (weightedH3CanonicalFullThirdCommutator244 U)) := by
  have hPoint (n : ℕ) :
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          (thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z +
           thirdFullSchwartzLongitudinalFluxDefect244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z)
            ∂volume.prod volume).im =
      fullSchwartzThirdCommutator244 (F.family.approximants n) :=
    (fullSchwartzThirdCommutator_eq_correctedFlux244
      (F.family.approximants n)).symm
  have hEq :
      (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : V3 × V3,
            (thirdFullSchwartzComplexSixthPowerFlux244
              (fun j => h3SchwartzComplexify (F.family.approximants n j)) z +
             thirdFullSchwartzLongitudinalFluxDefect244
              (fun j => h3SchwartzComplexify (F.family.approximants n j)) z)
              ∂volume.prod volume).im) =
      (fun n => fullSchwartzThirdCommutator244 (F.family.approximants n)) := by
    funext n
    exact hPoint n
  rw [hEq]
  exact h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U F

/-- At each genuine Fourier-compatible preterminal Navier–Stokes slice,
the corrected Fourier-flux sequence of ANY matched Schwartz completion
converges to the actual old physical H³ transport scalar. No solenoidal
approximation assumption is inserted; the exact defect stays visible. -/
theorem h3Path_matchedSchwartz_correctedFlux_tendsto_physical244
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
    (F : H3MatchedSchwartzGradientCompletion244
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)) :
    Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          (thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z +
           thirdFullSchwartzLongitudinalFluxDefect244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z)
            ∂volume.prod volume).im)
      atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  have hLimit := h3MatchedSchwartz_correctedFlux_tendsto244
    (velocityH3SpectralStateAt u t hInt hMeas hFourier) F
  have hPhysical := h3PhysicalFullThird_eq_weightedCanonical244
    hNS htNS hH3 hClass ht hFourier
  rw [hPhysical]
  simpa only [h3PhysicalSnapshotCanonicalFullThird244] using hLimit

end
end PrimeTensor.FirstMonomialTriad
