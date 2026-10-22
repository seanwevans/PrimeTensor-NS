# Signed physical top phase and downward logarithmic variation

Base checkpoint: `40dcbde5` — exact physical kinetic logarithmic loss and integrated signed top-phase budget.

## Exact PDE orientation

Let `E0(t)` be the physical kinetic energy, `E2(t)` the second-order Fourier energy, and `D3(t)>0` the fourth-radial/top-dissipation Hilbert mass. The exact signed phase identity previously proved in the repository gives

    D3' + M5 + P = M3,
    P >= 0.

Therefore the genuine normalized top production is

    Ctop(t) = -w(t) D3'(t),
    w(t) = E2(t)^2 E0(t) / (E0(t) D3(t))^2.

The sharp Fourier Cauchy inequality `E2^2 <= E0 D3` implies

    0 <= w(t) D3(t) <= 1.

Hence, for *any sign* of `D3'`,

    Ctop(t) <= max(-D3'(t),0)/D3(t).

In particular, if `Ctop(t)>0`, the actual physical derivative `D3'(t)<0`. The nonnegative phase defect is still counted with its true positive sign: the constraint is on the **complete signed combination**, not the phase defect alone.

## Integrated negative-log-variation obstruction

On a compact strict physical interval `[s,t]`, assume `E0,D3>0` throughout and the appropriate normalized sources are interval-integrable. Integration then gives

    integral_s^t Ctop <= integral_s^t max(-D3',0)/D3.

Together with the previous exact physical near-Young concentration budget, this establishes

    R(s) - 256 delta / (27 K^4 E0(t))
      - (log E0(s) - log E0(t))
      - 36 integral_s^t [C1 sqrt(E_H3(r))] dr
    <= integral_s^t max(-D3'(r),0)/D3(r) dr.

This is a concrete geometric constraint on the physical top-dissipation trajectory. It does not assume `D3` is monotone: the right side counts only downward relative motion, allowing replenishment and repeated oscillation.

## Mathematical limit

Compact-time integrability is explicit for the source profiles. Nothing here bounds the positive downward-log variation up to the terminal time, proves uniform continuity of the normalized rate, or implies unconditional Navier–Stokes regularity. The remaining hard analytic issue is to bound the repeated time-integrated decreases in `log D3`, rather than merely its instantaneous rate or net endpoint change.
