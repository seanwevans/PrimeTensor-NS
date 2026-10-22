# Physical integrated signed Fourier concentration budget

Base checkpoint: `f81b694a`, exact integrated two-band heat action.

Unlike the heat-only two-band algebra, a physical preterminal H3 Navier--Stokes trajectory obeys an exact three-channel normalized Fourier variance equation. On a compact strict-time subinterval `[s,t]` of positive kinetic and top H3 masses, let `H` be the normalized Fourier heat moment contribution, `T2` the exact signed order-two transport, and `L` the global signed fourth-radial Leray transfer. The theorem packages them as class-local functions (zero-extended outside the class interval).

**Under explicit interval-integrability of the actual normalized variance derivative**, its ordinary FTC gives

    R(s)-R(t) = integral_s^t [H(r)+T2(r)+L(r)] dr.

For separate integrability of H, T2, and L, the three integrals split. Under upper interval budgets `int H <= Hbar` and `int T2 <= Gbar`, an actual drop demands

    int L >= R(s)-R(t)-Hbar-Gbar.

For a later near-Young configuration satisfying the repository's sharp Young-gap estimate `R(t)<= 256 delta/(27 K^4 E0(t))`, the Leray integral must meet the corresponding residual threshold.

These are conditional necessities, not a new unconditional estimate on Leray transfer. Integrability is left explicit rather than inferred from mere differentiability; closing it from strict-time PDE regularity is a distinct analytical task. No positive sign is claimed for physical heat or nonlinear forcing.
