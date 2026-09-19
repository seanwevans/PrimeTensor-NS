import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.MiddleLocalizedGradientPhysical
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicLocalizedGradientFourier
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.FrequencyShellTelescoping

/-!
# BKM endpoint: Fourier reconstruction of the bounded middle gradient state

The physical middle-frequency `L²` states are already bounded logarithmically,
and each one-shell state has now been identified spectrally as

    ψ_{R_n}(ξ) * (d_i(ξ) * û_j(ξ)).

This file sums those identities at the bundled `L²` level.  For each target
velocity component `j`, the Fourier transform of the middle state is represented
almost everywhere by

    ∑_{n=lo}^{hi}
      ψ_{R_n}(ξ) * (d_i(ξ) * û_j(ξ)).

The telescoping shell theorem then turns this into the genuine canonical first
derivative on the interior annulus

    R_{lo+1} ≤ ‖ξ‖ ≤ R_{hi+1}.

Thus the logarithmically bounded physical middle state is now spectrally
identified with the actual middle-frequency velocity gradient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointMiddleLocalizedGradientFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fourier transform commutes with the finite middle sum -/

theorem h3BKMMiddleLocalizedGradientComponent0InverseL2_fourier_eq_sum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3BKMMiddleLocalizedGradientComponent0InverseL2
        hFourier lo hi i)
      =
    ∑ n ∈ Finset.Icc lo hi,
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3BKMDyadicLocalizedGradientComponent0InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i) := by

  unfold h3BKMMiddleLocalizedGradientComponent0InverseL2
  simp only [map_sum]

theorem h3BKMMiddleLocalizedGradientComponent1InverseL2_fourier_eq_sum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3BKMMiddleLocalizedGradientComponent1InverseL2
        hFourier lo hi i)
      =
    ∑ n ∈ Finset.Icc lo hi,
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3BKMDyadicLocalizedGradientComponent1InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i) := by

  unfold h3BKMMiddleLocalizedGradientComponent1InverseL2
  simp only [map_sum]

theorem h3BKMMiddleLocalizedGradientComponent2InverseL2_fourier_eq_sum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3BKMMiddleLocalizedGradientComponent2InverseL2
        hFourier lo hi i)
      =
    ∑ n ∈ Finset.Icc lo hi,
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3BKMDyadicLocalizedGradientComponent2InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i) := by

  unfold h3BKMMiddleLocalizedGradientComponent2InverseL2
  simp only [map_sum]

/-! ## A.e. finite-shell gradient representatives -/

theorem h3BKMMiddleLocalizedGradientComponent0InverseL2_fourier_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMMiddleLocalizedGradientComponent0InverseL2
        hFourier lo hi i) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (
          h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 0 ξ
        ) := by

  rw [
    h3BKMMiddleLocalizedGradientComponent0InverseL2_fourier_eq_sum
      hFourier lo hi i
  ]

  let F : ℕ → H3FourierComplexL2 :=
    fun n =>
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3BKMDyadicLocalizedGradientComponent0InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)

  have hRep :=
    h3FourierComplexL2_finsetSum_ae
      (Finset.Icc lo hi)
      F

  have hEach :
      ∀ n ∈ Finset.Icc lo hi,
        (F n : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        fun ξ : H3FourierPoint3 =>
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 0 ξ
          ) := by
    intro n hn
    dsimp only [F]
    exact
      h3BKMDyadicLocalizedGradientComponent0InverseL2_fourier_ae
        hNS ht hFourier
        (h3BKMDyadicRadius_pos n)
        i

  have hAll :
      ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
        ∀ n ∈ Finset.Icc lo hi,
          (F n : H3FourierPoint3 → ℂ) ξ
            =
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 0 ξ
          ) := by
    exact
      (Finset.eventually_all (Finset.Icc lo hi)).2 hEach

  filter_upwards [hRep, hAll] with ξ hRepξ hAllξ

  rw [hRepξ]

  apply Finset.sum_congr rfl
  intro n hn
  exact hAllξ n hn

theorem h3BKMMiddleLocalizedGradientComponent1InverseL2_fourier_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMMiddleLocalizedGradientComponent1InverseL2
        hFourier lo hi i) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (
          h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 1 ξ
        ) := by

  rw [
    h3BKMMiddleLocalizedGradientComponent1InverseL2_fourier_eq_sum
      hFourier lo hi i
  ]

  let F : ℕ → H3FourierComplexL2 :=
    fun n =>
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3BKMDyadicLocalizedGradientComponent1InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)

  have hRep :=
    h3FourierComplexL2_finsetSum_ae
      (Finset.Icc lo hi)
      F

  have hEach :
      ∀ n ∈ Finset.Icc lo hi,
        (F n : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        fun ξ : H3FourierPoint3 =>
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 1 ξ
          ) := by
    intro n hn
    dsimp only [F]
    exact
      h3BKMDyadicLocalizedGradientComponent1InverseL2_fourier_ae
        hNS ht hFourier
        (h3BKMDyadicRadius_pos n)
        i

  have hAll :
      ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
        ∀ n ∈ Finset.Icc lo hi,
          (F n : H3FourierPoint3 → ℂ) ξ
            =
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 1 ξ
          ) := by
    exact
      (Finset.eventually_all (Finset.Icc lo hi)).2 hEach

  filter_upwards [hRep, hAll] with ξ hRepξ hAllξ

  rw [hRepξ]

  apply Finset.sum_congr rfl
  intro n hn
  exact hAllξ n hn

theorem h3BKMMiddleLocalizedGradientComponent2InverseL2_fourier_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMMiddleLocalizedGradientComponent2InverseL2
        hFourier lo hi i) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
          *
        (
          h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas 2 ξ
        ) := by

  rw [
    h3BKMMiddleLocalizedGradientComponent2InverseL2_fourier_eq_sum
      hFourier lo hi i
  ]

  let F : ℕ → H3FourierComplexL2 :=
    fun n =>
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3BKMDyadicLocalizedGradientComponent2InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)

  have hRep :=
    h3FourierComplexL2_finsetSum_ae
      (Finset.Icc lo hi)
      F

  have hEach :
      ∀ n ∈ Finset.Icc lo hi,
        (F n : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        fun ξ : H3FourierPoint3 =>
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 2 ξ
          ) := by
    intro n hn
    dsimp only [F]
    exact
      h3BKMDyadicLocalizedGradientComponent2InverseL2_fourier_ae
        hNS ht hFourier
        (h3BKMDyadicRadius_pos n)
        i

  have hAll :
      ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
        ∀ n ∈ Finset.Icc lo hi,
          (F n : H3FourierPoint3 → ℂ) ξ
            =
          (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
            *
          (
            h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas 2 ξ
          ) := by
    exact
      (Finset.eventually_all (Finset.Icc lo hi)).2 hEach

  filter_upwards [hRep, hAll] with ξ hRepξ hAllξ

  rw [hRepξ]

  apply Finset.sum_congr rfl
  intro n hn
  exact hAllξ n hn

/-! ## Interior annulus reconstruction -/

theorem h3BKMMiddleLocalizedGradientComponent0InverseL2_fourier_ae_eq_gradient_on_annulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i : Fin 3) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      h3BKMDyadicRadius (lo + 1) ≤ ‖ξ‖
        →
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1)
        →
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier lo hi i) :
          H3FourierPoint3 → ℂ) ξ
        =
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas 0 ξ := by

  have hMiddle :=
    h3BKMMiddleLocalizedGradientComponent0InverseL2_fourier_ae
      hNS ht hFourier lo hi i

  filter_upwards [hMiddle] with ξ hMiddleξ

  intro hLower hUpper

  rw [hMiddleξ]

  have hShellReal :=
    h3BKMDyadicFrequencyShell_sum_Icc_eq_one
      hlohi hLower hUpper

  have hShellComplex :
      (∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ))
        =
      1 := by
    exact_mod_cast hShellReal

  rw [← Finset.sum_mul]
  rw [hShellComplex]
  ring

theorem h3BKMMiddleLocalizedGradientComponent1InverseL2_fourier_ae_eq_gradient_on_annulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i : Fin 3) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      h3BKMDyadicRadius (lo + 1) ≤ ‖ξ‖
        →
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1)
        →
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier lo hi i) :
          H3FourierPoint3 → ℂ) ξ
        =
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas 1 ξ := by

  have hMiddle :=
    h3BKMMiddleLocalizedGradientComponent1InverseL2_fourier_ae
      hNS ht hFourier lo hi i

  filter_upwards [hMiddle] with ξ hMiddleξ

  intro hLower hUpper

  rw [hMiddleξ]

  have hShellReal :=
    h3BKMDyadicFrequencyShell_sum_Icc_eq_one
      hlohi hLower hUpper

  have hShellComplex :
      (∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ))
        =
      1 := by
    exact_mod_cast hShellReal

  rw [← Finset.sum_mul]
  rw [hShellComplex]
  ring

theorem h3BKMMiddleLocalizedGradientComponent2InverseL2_fourier_ae_eq_gradient_on_annulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i : Fin 3) :
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      h3BKMDyadicRadius (lo + 1) ≤ ‖ξ‖
        →
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1)
        →
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier lo hi i) :
          H3FourierPoint3 → ℂ) ξ
        =
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas 2 ξ := by

  have hMiddle :=
    h3BKMMiddleLocalizedGradientComponent2InverseL2_fourier_ae
      hNS ht hFourier lo hi i

  filter_upwards [hMiddle] with ξ hMiddleξ

  intro hLower hUpper

  rw [hMiddleξ]

  have hShellReal :=
    h3BKMDyadicFrequencyShell_sum_Icc_eq_one
      hlohi hLower hUpper

  have hShellComplex :
      (∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ))
        =
      1 := by
    exact_mod_cast hShellReal

  rw [← Finset.sum_mul]
  rw [hShellComplex]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
