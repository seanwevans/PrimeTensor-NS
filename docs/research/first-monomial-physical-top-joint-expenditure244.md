# Automatic joint normalized fifth/phase expenditure on strict physical intervals

Base: `753da845` — exact physical cubic action and normalized fifth/phase expenditure.

## What changes

The exact physical PDE identity reads

    D3'(r) + M5(r) + P(r) = M3(r),      M5 >= 0, P >= 0.

On a strict interval with D3 positive, define the **actual combined** expenditure by its original Fourier masses:

    J(r) = M5(r)/D3(r) + P(r)/D3(r).

The pointwise PDE gives `J = M3/D3 - (log D3)'` without replacing either mass with an artificial estimate.

The previous checkpoint proves compact-interval integrability of `M3/D3` from physical continuity. Assuming only interval-integrability of `(log D3)'`, this patch derives interval-integrability of the **sum J** by congruence on the ordered interval. Individual time-integrability of its two summands is not asserted (though both are pointwise nonnegative).

Consequently,

    integral_s^t J(r) dr
       = integral_s^t M3(r)/D3(r) dr - [log D3(t) - log D3(s)].

This identity does not require independent hypotheses that `M5/D3` and `P/D3` are integrable.

## Near-Young consequence

The preceding physical near-Young obstruction can now be read as

    R(s) - 256 δ/(27 K^4 E0(t))
      - [log E0(s)-log E0(t)]
      - 36 integral_s^t C1 sqrt(E_H3(r)) dr
      <= integral_s^t J(r) dr.

The same explicit hypotheses for the variance derivative, middle coupling, top phase, kinetic log loss, positive/negative top log variation, and the signed top-log rate remain. The separate fifth/phase hypotheses are eliminated from the combined near-Young theorem.

## Open analytic obstruction

`J >= 0` and a **lower** necessary bound for its action do not give an upper bound on `J` up to terminal time. A continuation theorem needs a dynamical estimate controlling the joint action (or its signed response in the normalized variance equation) and the remaining temporal sources. The current module does not assert such an estimate.
