import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Diffusion.Pairing.Bridge

/-!
# Scalar Plancherel preserves the real L² pairing

The project already proves that

    h3ScalarFourierL2 : H3ScalarL2 → H3FourierComplexL2

is norm preserving and respects addition/subtraction.

For diffusion dissipation we need the corresponding pairing identity

    Re ⟪F̂, Ĝ⟫_ℂ = ⟪F,G⟫_ℝ.

Rather than reopening the Fourier-isometry construction, this file derives the
identity from the polarization formula.  This is entirely algebraic and gives
the next diffusion step a clean Fourier-side target.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2PlancherelPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The scalar physical-to-Fourier Plancherel bridge preserves the real part of
the Hilbert pairing exactly. -/
theorem re_inner_h3ScalarFourierL2_eq_inner
    (F G : H3ScalarL2) :
    (inner ℂ
        (h3ScalarFourierL2 F)
        (h3ScalarFourierL2 G)).re
      =
    inner ℝ F G := by
  change
    RCLike.re
        (inner ℂ
          (h3ScalarFourierL2 F)
          (h3ScalarFourierL2 G))
      =
    inner ℝ F G

  rw [
    re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
  ]

  rw [
    ← h3ScalarFourierL2_add,
    ← h3ScalarFourierL2_sub,
    norm_h3ScalarFourierL2,
    norm_h3ScalarFourierL2
  ]

  simpa using
    (re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
      (𝕜 := ℝ)
      F
      G).symm

/-- Therefore any Fourier-side nonpositivity statement immediately transfers
back to the real physical `L²` pairing. -/
theorem h3ScalarL2_inner_nonpos_of_fourier_re_inner_nonpos
    (F G : H3ScalarL2)
    (hFourier :
      (inner ℂ
          (h3ScalarFourierL2 F)
          (h3ScalarFourierL2 G)).re
        ≤
      0) :
    inner ℝ F G ≤ 0 := by
  rw [← re_inner_h3ScalarFourierL2_eq_inner F G]
  exact hFourier

end

end Euclidean
end Bridge
end PrimeTensor
