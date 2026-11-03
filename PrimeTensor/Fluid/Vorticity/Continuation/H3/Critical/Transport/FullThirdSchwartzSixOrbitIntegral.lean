import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdComplexSixthPowerFlux
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSixIntegral
import Mathlib.Tactic

/-!
# Unrestricted complex Schwartz six-orbit reindexing for the H³ radial flux

The preceding exact sixth-power identity is now applied on the actual
complex Fourier spectrum of a Schwartz field, without fixed real
polarizations or selected windows. The six changes of variables are the
existing measure-preserving transformations of the physical Hilbert-frequency
pair. In particular, integration of the whole six-symbol is exactly six times
the integral of the corrected ordered symbol.

The integrability of the corrected ordered symbol is kept explicit: it is the
remaining analytic bridge between the full 3+3+1 plus 3+2+2 seven-derivative
Schwartz kernels and their finite-dimensional contracted symbol. This module
does NOT claim that this bridge, or the full physical H³ transport identity,
has been proved merely by symmetrizing an abstract polynomial.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdSchwartzSixOrbitIntegral
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Corrected full-third ORDERED physical symbol on the three complex Fourier
amplitudes of a *single arbitrary Schwartz field*. The 2 from physical energy
pairing and the odd seventh-derivative Fourier phase are not included. -/
noncomputable def thirdFullSchwartzComplexOrderedKernel244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  let U := h3SchwartzTriadPolarization u
  thirdFullComplexOrderedSymbol244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
    (U (WithLp.ofLp z.1))
    (U (WithLp.ofLp (-(z.1 + z.2))))
    (U (WithLp.ofLp z.2))

/-- The complete six-order FULL THIRD complex Fourier polynomial is exactly
six changes of arguments of the same corrected ordered complex kernel.
This is a pointwise equality for arbitrary Schwartz fields: no divergence or
Hermitian hypothesis is needed for the permutation identity itself. -/
theorem thirdFullSchwartzComplexSix_eq_sixOrbit244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    thirdFullSchwartzComplexSixSymbol244 u z =
      h3TriadSixOrbit (thirdFullSchwartzComplexOrderedKernel244 u) z := by
  -- Make the six old physical permutations explicit rather than unfolding
  -- the file-private swap helper from FirstMonomialTriadSixIntegral.
  have hp0 (w : V3 × V3) :
      h3TriadPermutation (0 : Fin 6) w = w := by
    rfl
  have hp1 (w : V3 × V3) :
      h3TriadPermutation (1 : Fin 6) w =
        (w.1, -(w.1 + w.2)) := by
    rfl
  have hp2 (w : V3 × V3) :
      h3TriadPermutation (2 : Fin 6) w =
        (-(w.1 + w.2), w.2) := by
    change (-(w.1 + w.2), -(-(w.1 + w.2) + w.1)) = _
    rw [show -(-(w.1 + w.2) + w.1) = w.2 by abel]
  have hp3 (w : V3 × V3) :
      h3TriadPermutation (3 : Fin 6) w =
        (-(w.1 + w.2), w.1) := by
    rfl
  have hp4 (w : V3 × V3) :
      h3TriadPermutation (4 : Fin 6) w =
        (w.2, -(w.1 + w.2)) := by
    change (w.2, -(w.2 + w.1)) = _
    rw [add_comm w.2 w.1]
  have hp5 (w : V3 × V3) :
      h3TriadPermutation (5 : Fin 6) w = (w.2, w.1) := by
    rfl
  have h1 : -(z.1 + -(z.1 + z.2)) = z.2 := by abel
  have h2 : -(-(z.1 + z.2) + z.1) = z.2 := by abel
  have h3 : -(z.2 + -(z.1 + z.2)) = z.1 := by abel
  have h4 : -(-(z.1 + z.2) + z.2) = z.1 := by abel
  have h5 : -(z.2 + z.1) = -(z.1 + z.2) := by abel
  simp [thirdFullSchwartzComplexSixSymbol244,
    thirdFullSchwartzComplexOrderedKernel244,
    thirdFullComplexSixSymbol244, h3TriadSixOrbit,
    Fin.sum_univ_succ, hp0, hp1, hp2, hp3, hp4, hp5,
    h1, h2, h3, h4, h5] <;> ac_rfl

/-- Actual global integrability of the six-orbit follows from that of its
ordered Schwartz coefficient. No *extra* integrability assumption is needed
for the frequency transforms or for individual permuted integrands. -/
theorem thirdFullSchwartzComplexSix_integrable_of_ordered244
    (u : A3 → SchwartzMap V3 ℂ)
    (hOrdered : Integrable (thirdFullSchwartzComplexOrderedKernel244 u)
      (volume.prod volume)) :
    Integrable (thirdFullSchwartzComplexSixSymbol244 u)
      (volume.prod volume) := by
  have hOrbit := h3TriadSixOrbit_integrable
    (thirdFullSchwartzComplexOrderedKernel244 u) hOrdered
  exact hOrbit.congr (Filter.Eventually.of_forall (fun z =>
    (thirdFullSchwartzComplexSix_eq_sixOrbit244 u z).symm))

/-- For solenoidal data, the genuine three-term SIXTH-POWER radial flux is
absolutely integrable whenever the original corrected ordered multiplier is.
This transports integrability through the actual six measure-preserving maps. -/
theorem thirdFullSchwartzComplexSixthPowerFlux_integrable_of_ordered244
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ ξ : A3 → ℝ,
      mixedDot ξ (h3SchwartzTriadPolarization u ξ) = 0)
    (hOrdered : Integrable (thirdFullSchwartzComplexOrderedKernel244 u)
      (volume.prod volume)) :
    Integrable (thirdFullSchwartzComplexSixthPowerFlux244 u)
      (volume.prod volume) := by
  have hSix := thirdFullSchwartzComplexSix_integrable_of_ordered244
    u hOrdered
  exact hSix.congr (Filter.Eventually.of_forall (fun z =>
    thirdFullSchwartzComplexSix_eq_sixthPowerFlux244 u hDiv z))

/-- Unrestricted six-dimensional complex FOURIER integral of the genuine
sixth-power H³ radial flux. Six changes of variables are exact, no Jacobian,
no extra phase, and no loss from termwise absolute values:

    ∫ (three sixth-power fluxes) = 6 ∫ (corrected ordered coefficient).

The missing identification with the original physical seven-derivative
Schwartz integral is deliberately *not* smuggled into this theorem. -/
theorem thirdFullSchwartzComplexSixthPowerFlux_integral_eq_sixOrdered244
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ ξ : A3 → ℝ,
      mixedDot ξ (h3SchwartzTriadPolarization u ξ) = 0)
    (hOrdered : Integrable (thirdFullSchwartzComplexOrderedKernel244 u)
      (volume.prod volume)) :
    (∫ z : V3 × V3,
      thirdFullSchwartzComplexSixthPowerFlux244 u z
        ∂volume.prod volume) =
      6 * ∫ z : V3 × V3,
        thirdFullSchwartzComplexOrderedKernel244 u z
          ∂volume.prod volume := by
  calc
    (∫ z : V3 × V3,
        thirdFullSchwartzComplexSixthPowerFlux244 u z
          ∂volume.prod volume) =
        ∫ z : V3 × V3,
          thirdFullSchwartzComplexSixSymbol244 u z
            ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z =>
        (thirdFullSchwartzComplexSix_eq_sixthPowerFlux244 u hDiv z).symm)
    _ = ∫ z : V3 × V3,
        h3TriadSixOrbit (thirdFullSchwartzComplexOrderedKernel244 u) z
          ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (thirdFullSchwartzComplexSix_eq_sixOrbit244 u)
    _ = _ := h3TriadSixOrbit_integral
      (thirdFullSchwartzComplexOrderedKernel244 u) hOrdered

/-- The same global Fourier flux formula with the ORIGINAL real physical
Point3 divergence predicate, rather than an independently assumed spectral
solenoidality condition. The analytic ordered-kernel integrability is still
shown as the precise outstanding contract. -/
theorem thirdFullRealSchwartz_sixthPowerFlux_integral_of_point3Solenoidal244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hOrdered : Integrable
      (thirdFullSchwartzComplexOrderedKernel244
        (fun j => h3SchwartzComplexify (f j)))
      (volume.prod volume)) :
    (∫ z : V3 × V3,
      thirdFullSchwartzComplexSixthPowerFlux244
        (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume) =
    6 * ∫ z : V3 × V3,
      thirdFullSchwartzComplexOrderedKernel244
        (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume := by
  have hDeriv : ∀ y : V3,
      ∑ j : A3, fderiv ℝ (h3SchwartzComplexify (f j)) y
        (h3FourierAxisDirection j) = 0 := by
    intro y
    have hr := hDiv (WithLp.ofLp y)
    simp only [h3SchwartzPoint3Scalar_spatial_d,
      h3SchwartzPoint3Scalar] at hr
    have hr' : (∑ j : A3,
        (∂_{h3FourierAxisDirection j} (f j)) y) = 0 := hr
    simp only [← SchwartzMap.lineDerivOp_apply_eq_fderiv,
      h3TriadComplexify_lineDeriv, h3SchwartzComplexify_apply]
    exact_mod_cast hr'
  exact thirdFullSchwartzComplexSixthPowerFlux_integral_eq_sixOrdered244
    (fun j => h3SchwartzComplexify (f j))
    (h3SchwartzTriadPolarization_divergence_zero _ hDeriv) hOrdered

end
end PrimeTensor.FirstMonomialTriad
