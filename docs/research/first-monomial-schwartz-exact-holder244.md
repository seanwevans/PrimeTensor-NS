# Exact 243-slot physical Schwartz 2-4-4 Hölder reduction

Parent commit: `f2c5c4b9` — formalize exact critical-half Sobolev exponent closure.

This file applies the project’s existing **proved generic real** `L² × L⁴ × L⁴` Hölder inequality to each of the real Schwartz 3/2/2-derivative slots. Schwartz continuity itself discharges all measurability obligations. The canonical complexification theorem identifies each real integral with the real part of its corresponding complex monomial slot. The full five-index sum is reassembled, retaining the **factor two** arising from `spatialEnergyPairing`.

The precise unconditional result is

    ‖M(f)‖ₑ ≤ ‖2‖ₑ ∑_{i,k,l,r,j}
      realLpEnorm 2 (D_i D_k D_l f_j)
      · realLpEnorm 4 (D_k D_l f_r)
      · realLpEnorm 4 (D_i D_r f_j).

This is an extended-nonnegative-real estimate and is not the final universal critical-half inequality. It uses **all 243 ordered slots** and does not assume divergence-free fields, PDE evolution, or a Sobolev bound. The new proof removes one of the three explicit premises of the previous seventh-power closure: the 2-4-4 product Hölder step.

**Unproved analytic work:** quantitative homogeneous `Ḣ^(3/4) → L⁴` on the physical Schwartz Hilbert carrier, and fractional Fourier interpolation with the correct normalization. These are standard functional inequalities, not a new large-data Navier–Stokes regularity mechanism.

Build checks: `lake env lean` on the new module, `lake build` that module, audit `lake env lean`, and full `lake build`.
