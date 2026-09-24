import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Test.Laplacian.Fourier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Diffusion.Sign

/-!
# Selected weak diffusion equals the physical L² Laplacian pairing

The previous increment identified the Fourier transform of the compact-test
Laplacian.  This file uses that identity to close the last representation seam
in the selected weak temporal equation.

For one compact scalar test `φ` and one weighted H³ scalar state `G`,

    Σₖ Fourier(∂ₖ² φ) = -q Fourier(φ)

while the quotient-safe Fourier Laplacian satisfies

    lap(G) = -q raw(G).

Because `-q` is real, multiplication by this symbol is self-adjoint in the
complex `L²` pairing.  Scalar Plancherel therefore gives

    Σₖ <∂ₖ² φ, V> = <φ, L>

whenever `V` Fourier-transforms to `raw(G)` and `L` Fourier-transforms to
`lap(G)`.

The existing selected physical velocity and selected physical Laplacian
packages satisfy exactly those two Plancherel identities.  Summing the scalar
coordinate statement closes the full selected weak diffusion pairing and
removes the final `hDiffusion` hypothesis from the physical projected-RHS
bridge.

No endpoint passage, selected--old agreement, or new analytic estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakDiffusionPhysicalPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongSelectedWeakDiffusionPhysicalPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Fourier-side self-adjointness of the scalar Laplacian against one compact
weak test. -/
theorem re_sum_inner_h3WeakTestFunction_secondSpatialDerivative_raw_eq_inner_laplacian
    (φ : H3WeakTestFunction)
    (G : H3SpectralScalarState) :
    (∑ k : Fin 3,
      (inner ℂ
        (h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSecondSpatialDerivative
              (h3AxisOfFin3 k) φ)))
        (h3SpectralScalarRawFourierL2 G)).re)
      =
    (inner ℂ
      (h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2 φ))
      (h3SpectralScalarLaplacianRawFourierL2 G)).re := by
  let T0 : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3WeakTestFunctionPhysicalL2
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 (0 : Fin 3)) φ))

  let T1 : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3WeakTestFunctionPhysicalL2
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 (1 : Fin 3)) φ))

  let T2 : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3WeakTestFunctionPhysicalL2
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 (2 : Fin 3)) φ))

  let Φ : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3WeakTestFunctionPhysicalL2 φ)

  let U : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2 G

  let L : H3FourierComplexL2 :=
    h3SpectralScalarLaplacianRawFourierL2 G

  have hAdd01 :=
    MeasureTheory.Lp.coeFn_add T0 T1

  have hAdd012 :=
    MeasureTheory.Lp.coeFn_add (T0 + T1) T2

  have hTest :=
    sum_h3WeakTestFunctionPhysicalL2_secondSpatialDerivative_fourier_ae
      φ

  have hTsum :
      (((T0 + T1) + T2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ) * Φ ξ) := by
    filter_upwards [hAdd01, hAdd012, hTest] with
        ξ h01 h012 hTestξ

    rw [h012]
    simp only [Pi.add_apply]
    rw [h01]
    simp only [Pi.add_apply]

    dsimp only [T0, T1, T2, Φ]

    simpa only [Fin.sum_univ_three] using hTestξ

  have hLap :
      (L : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ) * U ξ) := by
    dsimp only [L, U]

    exact
      h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
        G

  have hComplex :
      inner ℂ ((T0 + T1) + T2) U
        =
      inner ℂ Φ L := by
    rw [MeasureTheory.L2.inner_def]
    rw [MeasureTheory.L2.inner_def]

    apply integral_congr_ae

    filter_upwards [hTsum, hLap] with ξ hTξ hLξ

    rw [hTξ, hLξ]

    change
      inner ℂ
          ((-(h3FourierGradientSquare ξ : ℂ)) • Φ ξ)
          (U ξ)
        =
      inner ℂ
          (Φ ξ)
          ((-(h3FourierGradientSquare ξ : ℂ)) • U ξ)

    rw [inner_smul_left, inner_smul_right]

    simp

  have hComplexExpanded :
      (inner ℂ T0 U + inner ℂ T1 U) + inner ℂ T2 U
        =
      inner ℂ Φ L := by
    calc
      (inner ℂ T0 U + inner ℂ T1 U) + inner ℂ T2 U
          =
        inner ℂ ((T0 + T1) + T2) U := by
          simp only [inner_add_left]
      _ = inner ℂ Φ L := hComplex

  have hRe :=
    congrArg Complex.re hComplexExpanded

  simp only [Complex.add_re] at hRe

  dsimp only [T0, T1, T2, Φ, U, L] at hRe

  simpa only [Fin.sum_univ_three] using hRe

/-- Quotient-safe physical scalar version of the same self-adjoint Laplacian
pairing. -/
theorem sum_inner_h3WeakTestFunction_secondSpatialDerivative_eq_inner_laplacian_of_fourier
    (φ : H3WeakTestFunction)
    (V L : H3ScalarL2)
    (G : H3SpectralScalarState)
    (hV :
      h3ScalarFourierL2 V
        =
      h3SpectralScalarRawFourierL2 G)
    (hL :
      h3ScalarFourierL2 L
        =
      h3SpectralScalarLaplacianRawFourierL2 G) :
    (∑ k : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 k) φ))
        V)
      =
    inner ℝ
      (h3WeakTestFunctionPhysicalL2 φ)
      L := by
  have hFourier :=
    re_sum_inner_h3WeakTestFunction_secondSpatialDerivative_raw_eq_inner_laplacian
      φ G

  simp only [Fin.sum_univ_three]

  rw [
    ← re_inner_h3ScalarFourierL2_eq_inner
      (h3WeakTestFunctionPhysicalL2
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 (0 : Fin 3)) φ))
      V,
    ← re_inner_h3ScalarFourierL2_eq_inner
      (h3WeakTestFunctionPhysicalL2
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 (1 : Fin 3)) φ))
      V,
    ← re_inner_h3ScalarFourierL2_eq_inner
      (h3WeakTestFunctionPhysicalL2
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 (2 : Fin 3)) φ))
      V,
    ← re_inner_h3ScalarFourierL2_eq_inner
      (h3WeakTestFunctionPhysicalL2 φ)
      L
  ]

  rw [hV, hL]

  simpa only [Fin.sum_univ_three] using hFourier

/-- One selected velocity coordinate: moving the two derivatives onto the
compact test gives exactly the Hilbert pairing with the selected physical
Laplacian coordinate. -/
theorem sum_inner_h3WeakTestFunction_secondSpatialDerivative_selectedVelocity_eq_selectedLaplacian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    (∑ k : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 k) φ))
        ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)) i))
      =
    inner ℝ
      (h3WeakTestFunctionPhysicalL2 φ)
      (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
        hNS ht hE hTail q i) := by
  let G : H3SpectralScalarState :=
    (h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q) i

  have hV :
      h3ScalarFourierL2
          ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) i)
        =
      h3SpectralScalarRawFourierL2 G := by
    dsimp only [G]

    exact
      h3ScalarFourierL2_h3PreterminalSelectedUnitVelocityPhysicalL2OnRadius
        hNS ht hE hTail q i

  have hL :
      h3ScalarFourierL2
          (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
            hNS ht hE hTail q i)
        =
      h3SpectralScalarLaplacianRawFourierL2 G := by
    have h :=
      h3ScalarFourierL2_h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
        hNS ht hE hTail q i

    dsimp only [G]

    simpa only [
      h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
    ] using h

  exact
    sum_inner_h3WeakTestFunction_secondSpatialDerivative_eq_inner_laplacian_of_fourier
      φ
      ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)) i)
      (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
        hNS ht hE hTail q i)
      G
      hV
      hL

/-- The selected weak diffusion functional is exactly the physical `L²`
Hilbert pairing with the selected Laplacian vector. -/
theorem h3PreterminalSelectedUnitWeakDiffusionPairingAt_eq_inner_laplacian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (φ : H3WeakTestVector) :
    h3PreterminalSelectedUnitWeakDiffusionPairingAt
        hNS ht hE hTail (q : ℝ) φ
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  unfold h3PreterminalSelectedUnitWeakDiffusionPairingAt

  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius

  rw [PiLp.inner_apply]

  apply Finset.sum_congr rfl
  intro i hi

  exact
    sum_inner_h3WeakTestFunction_secondSpatialDerivative_selectedVelocity_eq_selectedLaplacian
      hNS ht hE hTail q (φ i) i

/-- The named selected weak projected-RHS pairing is therefore exactly the
physical selected projected-RHS Hilbert pairing, with no auxiliary diffusion
hypothesis. -/
theorem h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius_eq_inner_projectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (φ : H3WeakTestVector) :
    h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
        hNS ht hE hTail q φ
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  exact
    h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius_eq_inner_projectedRHS_of_diffusion
      hNS ht hE hTail q φ
      (h3PreterminalSelectedUnitWeakDiffusionPairingAt_eq_inner_laplacian
        hNS ht hE hTail q φ)

/-- Strict-positive selected weak temporal evolution is now exactly the
physical selected projected-RHS Hilbert pairing, with the diffusion seam
closed internally. -/
theorem h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_inner_projectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (hq0 : 0 < (q : ℝ))
    (hqR :
      (q : ℝ) <
        h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) x)
            (q : ℝ))
        ∂volume)
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  exact
    h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_inner_projectedRHS_of_diffusion
      hNS ht hE hTail q hq0 hqR φ
      (h3PreterminalSelectedUnitWeakDiffusionPairingAt_eq_inner_laplacian
        hNS ht hE hTail q φ)

end

end Euclidean
end Bridge
end PrimeTensor
