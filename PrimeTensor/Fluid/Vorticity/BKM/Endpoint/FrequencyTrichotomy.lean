import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.FrequencyShellTelescoping

/-!
# BKM endpoint: exact low / middle / high frequency trichotomy

The telescoping shell theorem gives

    ∑_{n=lo}^{hi} ψ_{R_n}
      = χ_{R_{hi+1}} - χ_{R_lo}.

Consequently the three multipliers

    low    = χ_{R_lo},
    middle = ∑_{n=lo}^{hi} ψ_{R_n},
    high   = 1 - χ_{R_{hi+1}}

form an exact global partition of unity.

This is the decomposition needed by the corrected BKM endpoint proof.  The
middle piece is already represented by the logarithmically bounded physical
`L²` state.  The remaining analytic work is now cleanly isolated to pointwise
bounds for the low and high inverse-Fourier pieces.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFrequencyTrichotomy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Low-frequency cutoff at the lower dyadic endpoint. -/
noncomputable def h3BKMDyadicLowFrequencyFactor
    (lo : ℕ)
    (ξ : H3FourierPoint3) :
    ℝ :=
  h3BKMFrequencyCutoffBump
    (h3BKMDyadicRadius lo)
    (h3BKMDyadicRadius_pos lo)
    ξ

/-- High-frequency complement beyond the successor of the upper dyadic endpoint. -/
noncomputable def h3BKMDyadicHighFrequencyFactor
    (hi : ℕ)
    (ξ : H3FourierPoint3) :
    ℝ :=
  1
    -
  h3BKMFrequencyCutoffBump
    (h3BKMDyadicRadius (hi + 1))
    (h3BKMDyadicRadius_pos (hi + 1))
    ξ

/--
The low cutoff, finite middle shell sum, and high complement form an exact
real-valued partition of unity.
-/
theorem h3BKMDyadicFrequencyTrichotomy_eq_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicLowFrequencyFactor lo ξ
      +
    (
      ∑ n ∈ Finset.Icc lo hi,
        h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ
    )
      +
    h3BKMDyadicHighFrequencyFactor hi ξ
      =
    1 := by

  unfold
    h3BKMDyadicLowFrequencyFactor
    h3BKMDyadicHighFrequencyFactor

  rw [
    h3BKMDyadicFrequencyShell_sum_Icc_eq_cutoff_sub
      hlohi ξ
  ]

  ring

/--
Complex-valued version of the exact frequency trichotomy.
-/
theorem h3BKMDyadicFrequencyTrichotomy_complex_eq_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
      +
    (
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
    )
      +
    (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
      =
    1 := by

  exact_mod_cast
    h3BKMDyadicFrequencyTrichotomy_eq_one
      hlohi ξ

/--
Any complex Fourier amplitude decomposes exactly into low, middle, and high
pieces under the BKM dyadic trichotomy.
-/
theorem h3BKMDyadicFrequencyTrichotomy_mul
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    z
      =
    (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ) * z
      +
    (
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
    ) * z
      +
    (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ) * z := by

  have hPart :=
    h3BKMDyadicFrequencyTrichotomy_complex_eq_one
      hlohi ξ

  calc
    z
        =
      1 * z := by
        ring

    _ =
      (
        (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
          +
        (
          ∑ n ∈ Finset.Icc lo hi,
            (h3BKMFrequencyShell
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              ξ : ℂ)
        )
          +
        (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
      ) * z := by
        rw [hPart]

    _ =
      (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ) * z
        +
      (
        ∑ n ∈ Finset.Icc lo hi,
          (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
      ) * z
        +
      (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ) * z := by
        ring

/--
Exact low/middle/high decomposition of one canonical Fourier gradient
coordinate.
-/
theorem velocityH3BaseFourier_gradient_frequencyTrichotomy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
      =
    (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
      *
    (
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
    )
      +
    (
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMFrequencyShell
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          ξ : ℂ)
    )
      *
    (
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
    )
      +
    (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
      *
    (
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
    ) := by

  exact
    h3BKMDyadicFrequencyTrichotomy_mul
      hlohi
      ξ
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      )

/--
The middle term may equivalently be written as the finite sum of individually
localized gradient amplitudes.
-/
theorem velocityH3BaseFourier_gradient_frequencyTrichotomy_sum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
      =
    (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
      *
    (
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
    )
      +
    (
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
            u t hInt hMeas j ξ
        )
    )
      +
    (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
      *
    (
      h3FourierDerivativeSymbol i ξ
        *
      velocityH3BaseFourierAt
        u t hInt hMeas j ξ
    ) := by

  calc
    h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
        =
      (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      )
        +
      (
        ∑ n ∈ Finset.Icc lo hi,
          (h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ : ℂ)
      )
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      )
        +
      (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      ) := by
        exact
          velocityH3BaseFourier_gradient_frequencyTrichotomy
            hlohi i j ξ

    _ =
      (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      )
        +
      (
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
              u t hInt hMeas j ξ
          )
      )
        +
      (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      ) := by
        rw [Finset.sum_mul]

end

end Euclidean
end Bridge
end PrimeTensor
