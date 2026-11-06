# Cofinal residual physical PDE source-state-frequency obstruction

**Base:** `6d0d24e31752925555c91309008db5cbc5e4d964` — force residual physical H3 PDE rate after exact dual clock overlap.

The exact overlap cofinal theorem retains the primary PDE clock, primary cutoff J, the original attained source/state times and the full H3 terminal dissipation tail. The selected-secondary residual theorem proves a local obstruction but does not retain the secondary finite cutoff J2 or attained maxima on the cofinal witnesses.

This module bridges those statements. For each late cofinal witness, put

- `A = V/(2P) > 0`, `B = integral_m^T D_H3 >= 0`;
- `C0 = 3 + initial Leray coefficient`, `E0 = 1 + 6 initial H3 energy`;
- `R = 96*C0*(J+2)^5 > 0`, and the actual two-time rate condition `A² <= R*(E0+3D_state)*(E0+3D_source)*B`.

In the kinetic gap `4*R*B*E0² < A²` and genuine excess `24*sqrt(R*B) < 1`, the established constructive theorem selects an actual secondary PDE spike of height `h=A/(12sqrt(R B))`. The **same** secondary certificate is destructed by the existing selected-clock residual-rate theorem to retain `s, eta2, J2, zSource, zState`, their compact-time containment, and the exact overlap envelope.

Set `H=h/2`, let `L` be the secondary interval duration outside the primary one, and `E=B-eta1*A-L*A`. We formally establish `0<E<=B` from positive excess `H>A`, positive secondary duration and the envelope; the upper bound subtracts only nonnegative primary and exterior charges.

The old residual quintic PDE-rate alternative then becomes

    (T-s)*(H-A) <= 4E
      OR
    (H*(H-A)-2E)/(48E) <= ||U_spectral(zState)|| * ||Source(zSource)|| * (J2+2)^5.

The latter is an explicit lower bound on the ACTUAL source-state-frequency product, not a new boundedness premise. The former is terminal-time compression. When the kinetic or smallness conditions fail, we make no strengthened claim. No terminal-uniform cutoff or Navier–Stokes global regularity follows.

The final theorem retains exactly the same cofinal minimal first crossings, Fourier/kinetic alternatives, frequency escape, original disjoint viscous sums and the terminal dissipation-tail limit. No new subsequence or primary clock is selected. The secondary chosen by this theorem need not coincide with an older independently existential secondary certificate; its own envelope and rate use one and the same secondary selection.

No proof placeholders. The registrar checks all three theorems and both definitions, including printed axioms. The pinned Lean toolchain must still elaborate the new module.
