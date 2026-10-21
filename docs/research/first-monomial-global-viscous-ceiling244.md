# Global physical viscous ceiling for normalized Fourier concentration

Base checkpoint `a3d86ca1`: the exact global heat/Leray source and unconditional `36 h` normalized order-two transport budget are closed.

## A second unconditional budget

Set `A = E0 D3 > 0`, `E2 >= 0`, `L0 = velocityH3DiffusionDerivative0At <= 0`, `L2 = velocityH3DiffusionDerivative2At <= 0`, and `H = h3PathTopFourierGlobalHeatRate244 <= 0`. The actual Fourier Cauchy inequality gives `E2^2 <= A`.

The normalized signed heat/moment production is

    B = [2 E2 L2 A - E2^2 (L0 D3 + E0 H)] / A^2.

Because `2 E2 L2 A <= 0` and `-(L0 D3 + E0 H) >= 0`, Cauchy gives the *unconditional* upper bound

    B <= -(L0 D3 + E0 H) / A =: V.

By whole-space diffusion IBP `L0 = -2 D0` and global heat `H = -2 M5`, this ceiling represents the positive kinetic and fifth-moment viscous losses after kinetic/top-dissipation normalization. It is a time-dependent, finite strict-slice quantity, NOT a uniform terminal bound. The normalized heat/moment contribution itself is **not** asserted to have one sign.

The already established order-two commutator budget is `T2_normalized <= 36 C1 sqrt(E_H3)`. Therefore the exact signed variance source satisfies

    X/A^2 <= V + 36 C1 sqrt(E_H3) + F_Leray_normalized.

At an exact near-Young secant witness `r in (s,t)`, this forces

    F_Leray_normalized(r) >=
        [R(s) - 256 delta/(27 K^4 E0(t))]/(t-s)
        - 36 C1 sqrt(E_H3(r)) - V(r).

This is a genuinely PDE-derived *necessary* global Leray bound: no postulated background ceiling is required. It does **not** prove the RHS positive, control fifth moments uniformly, or exclude terminal concentration.

## Audit workflow

The registrar adds the module to `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean` and emits `#check`/`#print axioms` for one definition and four theorems. Regenerate `proof/order.txt`, verify fragments, build module and full repository, and run the baseline before push.
