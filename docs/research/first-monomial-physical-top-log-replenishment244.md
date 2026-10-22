# Top-dissipation log replenishment and near-Young concentration

Base checkpoint: `f410df62` — signed physical top phase bounded by downward logarithmic variation.

## Signed Jordan decomposition of top-mass changes

For the actual positive fourth-radial Hilbert mass `D3(t)`, define on the strict energy-class interval

- `N(t) = max(-D3'(t),0)/D3(t)` — downward log variation
- `P(t) = max(D3'(t),0)/D3(t)` — upward log variation / replenishment
- `S(t) = D3'(t)/D3(t)` — signed log rate

At every positive-mass time, `N(t) = P(t) - S(t)`. The physical D3 Hilbert derivative gives `d/dt log D3 = S`. On compact strict intervals, under explicit interval integrability hypotheses, the exact FTC yields

    integral_s^t N = log D3(s) - log D3(t) + integral_s^t P.

This identity is mathematically different from treating downward variation as an endpoint quantity: upward compensation may produce arbitrarily large total downward variation with little net change.

## Required positive replenishment for near-Young narrowing

The previous checkpoint gives a necessary lower bound on `integral N` in terms of the early Young gap minus final near-Young tolerance, kinetic logarithmic loss and 36 times canonical H3 gradient action. Substituting the exact Jordan identity now forces

    integral_s^t P >= R(s) - 256 delta/(27 K^4 E0(t))
      - (log E0(s) - log E0(t)) - 36 integral_s^t h
      - (log D3(s) - log D3(t)).

Thus near-Young narrowing requires either net loss of top dissipation or compensating positive logarithmic replenishment. This is an exact physical necessary condition; it does not bound the replenishment integral or establish regularity.

Time-integrability of the signed log rate, positive variation, negative variation, and physical source profiles is explicitly assumed; bare differentiability alone cannot justify FTC. The new Lean file formalizes the algebraic decomposition, the physical logarithmic derivative, FTC, and the resulting replenishment burden.
