# Physical kinetic Gram terminal action — checkpoint 710bb144

## Pointwise identities

For the actual Hilbert velocity `U`, source `R=U'`, kinetic energy
`E0=‖U‖²`, viscous expenditure `D0=-inner(U,R)`, and transverse source
`Q=R+(D0/E0)U`, let `Δ=E0‖R‖²-D0²`. The committed Gram package proves
`Δ=E0‖Q‖²` for positive E0. Hence

- `sqrt Δ = sqrt E0 * ‖Q‖`
- `sqrt Δ / sqrt E0 = ‖Q‖`
- `sqrt Δ / E0 = ‖N'‖`, where `N=U/sqrt E0`.

These are pointwise *physical* Hilbert-space identities, without a chosen
coordinate frame, and do not assume anything about the behavior at T.

## Terminal action reformulation

For `a<s≤t<T` with established `L=lim_{r↑T} E0(r)>0`, the Gram action
integral `∫_s^t sqrt Δ(r)/sqrt E0(r) dr` equals `∫_s^t ‖Q(r)‖ dr`.
Uniform terminal smallness of this scalar Gram action is *equivalent* to
the previously formalized transverse variation hypothesis and is therefore
sufficient to obtain both the physical velocity terminal L² trace and the
terminal normalized-unit-velocity trace.

Importantly, the scalar Gram criterion is still a condition; a finite
kinetic energy budget alone does **not** establish it. Likewise, strong
physical L² trace does not by itself exclude loss of higher Sobolev regularity,
and angular speed may have nonintegrable absolute variation even when direction
has a limit. The next test should compare `sqrt Δ / E0` to the previously
localized signed spectral H³ transport and determine whether a *provable*
coercive inequality exists, instead of assuming one.
