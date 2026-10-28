# Canonical exact-anchor H³ energy fourth-power obstruction

**Base:** `531fa995` — propagated the physical spectral norm anchor into the canonical minimal first-crossing annulus and disjoint quadratic-sharp PDE clock.

The new result replaces a source–spectral product requirement by a necessary **physical H³ energy floor at the actual annulus anchor**. For weighted spectral state `G=U₃(t)`, the bounded low-radial gradient Fourier multiplier and its literal three-component Hilbert sum give

    LowDissipation(Q,G) ≤ 3 (Q+1)² ‖G‖² ≤ 3 (Q+1)² E₃(t).

A minimal first crossing with annular dissipation difference strictly greater than `3 R³ / 4` therefore satisfies

    R³ < 4 (Q+1)² E₃(t).

If the *outer cutoff* obeys `(Q+1)^8 ≤ D R^9`, raising the preceding inequality to the fourth power and canceling the positive `R^9` yields the root-free bound

    R³ < 256 D E₃(t)^4.

For the preselected minimal canonical annulus (`R=v(k)+1`, `L=N(v(k))-v(k)`, `Q=N(v(k))+1`), the existing outer-cutoff comparison converts the **additional critical-width cap** `(L+1)^8 ≤ V R^9` into `(Q+1)^8 ≤ 256(V+1)R^9`. Consequently

    R³ < 65536 (V+1) E₃(τ(v(k)))⁴

holds eventually. The wrapper theorem preserves the same exact-anchor cofinal sequence with source maxima attained on the original half-terminal windows, pairwise separated physical persistence windows and summable dissipation costs.

**Crucial scope:** This is conditional on the critical ninth/eighth cutoff-width cap. Geometric noncompression and linear-rate bounds are NOT assumed. The bound does not control integrated H³ dissipation and does not prove unconditional continuation. It makes the required anchor energy growth explicit under the width branch.

Lean compilation must be checked in the pinned repository; the packaging environment has no Lean/Lake installation.
