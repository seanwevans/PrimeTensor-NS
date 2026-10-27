# Critical kinetic-shell depletion and conditional PDE annular width escape

Base: `9194a15a` — force relative shell frequency escape under critical kinetic depletion.

Let `R=v(k)+1`, `L=N(v(k))-v(k)`, `J=m(k)+3`, and let `μ` be the actual raw Fourier kinetic mass in the selected unit shell. The canonical physical witness gives `v(k) ≤ m(k) < N(v(k))`, and therefore `J ≤ R+L+1` exactly. Thus critical depletion `L R^5 μ → 0` implies `J/R → ∞` (from the base theorem) and consequently `L/R → ∞` by annular geometry. **This implication is conditional** on critical depletion.

The independent **PDE branch** gives, for every fixed `M≥0`, eventually `M R^9 < (R+L+1)^8`, assuming an eventually noncompressed clock, a fixed sixth-order linear rate bound and fixed bounded source. For each `A≥0`, specialize `M=(A+2)^8`. If `L≤A R`, then `(R+L+1)^8≤(A+2)^8R^8≤MR^9`, contradiction. Hence `L/R→∞` **without** critical depletion on this branch.

The final physical theorem transports both mechanisms through the **same** strict-time, cofinal, disjoint, summable quadratic-sharp physical witnesses, using the exported ninth/eighth conditional source. Neither the regime assumptions nor terminal trace failure nor finite H³ dissipation integrability is proved here. No unconditional regularity assertion results.

The five non-existential lemmas separate elementary geometry from physical-PDE assumptions; the final sixth theorem packages the synchronized witness.
