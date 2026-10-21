# Sharp global Leray requirement after the order-two gradient budget

Base checkpoint: `daaba8af` — identify the global fourth-radial heat/Leray rate at zero Fourier cutoff.

## The missing estimate is partially closed

The zero-cutoff theorem closes the actual physical identity

    X = B_global + N_global,
    R' = -X / (E0 D3)^2,

where `R = 1 - E2^2/(E0 D3)`, `B_global` contains exactly the order-zero/order-two diffusion and global fifth-radial heat contributions, and `N_global` contains order-two transport and the genuine fourth-radial nonlinear Leray transfer.

The new module identifies three separately normalized rates:

    X/(E0 D3)^2 = B_normalized + T2_normalized + F_global_normalized,
    T2_normalized = -2 E2 T2 / (E0 D3),
    F_global_normalized = -E2^2 E0 F_global / (E0 D3)^2.

There are no low-frequency correction terms.

## An unconditional bound on the normalized order-two term

The existing physical energy-class commutator theorem proves

    |T2(t)| <= 18 h(t) E2(t),
    h(t) = C1 sqrt(E_H3(t)).

The existing physical Fourier first-Cauchy defect and strict moment-ratio theorem give

    E2(t)^2 <= E0(t) D3(t).

On any strict time with positive E0 and D3, these combine to prove

    T2_normalized(t) <= 36 h(t).

This is a *signed* upper bound needed by the spectral concentration rate. It uses no unproved global Leray bound and no hidden PDE continuation assumption. It also shows why one cannot simply attribute arbitrary normalized variance loss to the lower-order commutator.

## New near-Young consequence

When `[s,t]` belongs to one physical H3 energy-class interval, `E0,D3>0` throughout, `K>0`, and the actual Young gap at `t` is bounded by `delta`, the exact secant theorem produces `r∈(s,t)` satisfying

    [R(s) - 256 delta/(27 K^4 E0(t))]/(t-s) - 36 C1 sqrt(E_H3(r))
          <= B_normalized(r) + F_global_normalized(r).

Only the *genuine global Leray transfer and linear heat/moment production* remain on the right. This is an unconditional necessary inequality under the stated near-Young hypothesis. A bound on the global heat/moment part would further isolate top-order nonlinear forcing; a bound on that forcing sufficient to contradict the required concentration rate is not established here.

This theorem is not a Navier–Stokes global regularity proof, and does not assert terminal Young near-saturation. It is a genuine normalization improvement using proven PDE transport estimates and Fourier Cauchy rigidity.

## Audit

The registrar imports the new module into `PrimeTensor.lean` and the central `FirstMonomialTriad` audit. It adds `#check` and `#print axioms` for three definitions and four theorems. Run the source check, index generation/check, all fragment verification, module build, central audit, full build and baseline audit before committing.
