# Selected outer H³ carriers — two-radius signed source payment

Base commit: `126c2beb5` (kinetic-only signed cancellation).

## Actual new estimate

The exact earlier-Young identity is

    G_x - G_s = (M_x-M_s) [w a(a(M_x+M_s)-2B)-(Y_x+wP)]
                + M_s (Y_s-Y_x),
    w = rho^6, a = (rho²+sigma²)/2.

The signed positive-deficit polarization proved in the preceding module
bounds the first summand by `2*w*a*(a*M_x-B)*|M_x-M_s|`. For `rho<=sigma`,
`a<=sigma²`, `B>=0`, and `M_x<=||V_x||²`, the SHARP two-radius step is

    2*w*a*(a*M_x-B) <= 2*rho^6*sigma^4*||V_x||².

The previous theorem enlarged `w` to `sigma^6` and therefore obtained
`2*sigma^10*||V_x||²`. Retaining the highpass radius saves the exact factor
`(rho/sigma)^6`, essential for annuli with `rho/sigma -> 0`.

The true physical projected Navier--Stokes FTC gives

    |M_x-M_s| <= A(x),
    A(x) = H(x)*(2||V_x||+H(x)),
    H(x) = (3+C_L)*[(1+6 E_0(b))*(T-x)+3 V(x)],
    V(x) = ∫_x^T D_H3(t) dt.

Hence whenever `G_x-G_s>epsilon`,

    epsilon - 2*rho^6*sigma^4*||V_x||²*A(x)
        < M_s*(Y_s-Y_x).

The verified positive-time physical kinetic antitonicity separately gives
`||V_x||² <= E_0(b)`. Thus if `Y_s<=Y_x`,

    epsilon < 2*rho^6*sigma^4*E_0(b)*A(x).

If also `rho<=R`, this implies the QUARTIC outer-frequency requirement

    epsilon < 2*R^6*sigma^4*E_0(b)*A(x).

No hidden assumption of terminal H³ boundedness or frequency-uniform
source Lipschitz control is used. The inequality is a necessary escape
rate if signed Young growth fails; without controlling the weighted
source tail, there is no continuation contradiction.

## Formal deliverables

- Scalar two-radius kinetic slope estimate and its comparison to the former
  tenth-power outer-radius estimate.
- Scalar bounded-inner-radius quartic source payment.
- Physical two-radius coefficient and its kinetic anchor.
- Full physical early-anchored deficit residual, half-tail and cofinal forms.
- No-Young-growth forces source payment, with bounded-inner quartic corollary.
- No proof placeholders or added axioms.

The Lean 4/mathlib toolchain is unavailable in this authoring container.
Compile and audit this package in the project's pinned environment.
