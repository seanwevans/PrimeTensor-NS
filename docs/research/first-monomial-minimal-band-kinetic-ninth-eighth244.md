# Same physical witness for first-crossing kinetic-band cost and ninth/eighth PDE concentration

Base commit `1020bfe3` — the local band raw kinetic mass was identified and bounded by actual annular H³ dissipation.

## Why witness synchronization is necessary

The earlier no-terminal-trace band-mass theorem and ninth/eighth concentration theorem independently select cofinal sequences. One cannot intersect two existential subsequences to claim both estimates for the same physical state. This module rebuilds the *minimal first-crossing quadratic-sharp selector*, obtains disjoint windows by finite terminal full H³ dissipation, and retains both conclusions on the **identical** `tau (v k)` and `N (v k)`.

The preliminary lemmas show `K_band(R,Q;G) <= RawSquare(G)` for arbitrary weighted spectral states, and identify `K_band(R,Q;t) <= E0(t)` on actual physical strict-time velocities by Plancherel. The main existence theorem preserves strict preterminal snapshot construction, cubic-annulus persistence and summable disjoint costs, annular minimality and the quarter-cubic high radial H³ tail floor. It adds the already-proved physical band-kinetic lower cost

    3 * R_k^3 < 16 * (Q_k + 1)^8 * K_band(R_k,Q_k; tau(v k))

where `R_k = v(k)+1`, `Q_k=N(v k)+1` and `K_band` integrates the *raw* Fourier velocity square density exactly on `{R_k <= |grad| < Q_k}`.

The second theorem combines that same cost with the conditional ninth/eighth outer-radius barrier:

    eta <= R_k^3*(T-tau(v k))/4
    Lambda_k+1 <= B*R_k^6
    C_k^2 <= S^2
       => eventually M*R_k^9 < (Q_k+1)^8

for any fixed positive eta and nonnegative B, M and any fixed S.

No upper bound on `Q_k` is obtained. The lower band kinetic mass cost can tend to zero as `Q_k` grows; the combined theorem neither contradicts finite kinetic energy nor proves Navier–Stokes regularity. In particular the apparent cancellation of factors `R^9` does NOT imply an independent band mass floor without an **upper** bound on the outer cutoff.

## Validation

Package checks are static. Run `lake env lean` on the new module and full `lake build` before committing; no proof checker is present in the packaging environment.
