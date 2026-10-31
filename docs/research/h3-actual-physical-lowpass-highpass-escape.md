# Actual physical sharp cutoff and high-pass projected source escape

Base commit: `7515d1a3`.

## Quantitative bridge

Define the **physical scalar cutoff** on the actual physical real `L²(Point3)` carrier by

`Pρ f := decoder(1_{2π‖ξ‖<ρ} · (h3ScalarFourierL2 f))`.

The canonical scalar Plancherel bridge is isometric, the complex Fourier
cutoff is a contraction, and the physical real decoder is contractive.  Thus
`‖Pρ f‖ ≤ ‖f‖` and `‖Pρ f - Pρ g‖ ≤ ‖f-g‖`: `Pρ` is 1-Lipschitz.

The repository already proves the exact round trip
`Fourier(decoder F) = F` **for Hermitian** Fourier `L²` states.  The new file
establishes the genuine old actual weighted H³ spectral velocity is
raw-Hermitian, using its equality with the real canonical restart state.
Existing preservation results then give Hermitian reality of the true
Laplacian and nonlinear Leray Fourier states at each strict time.

Therefore, with `U(t)` the actual old spectral velocity and `R(t)` the
physical projected momentum source,

`Pρ (R(t)_i) = decoder(1_{Sρ} Δ̂(U_i(t))) - decoder(1_{Sρ} N̂_i(U(t)))`.

This is an identity of **actual physical scalar L²** elements, not merely an
identity of two differently named reconstructions.  The preceding kinetic
cutoff bounds prove its right side is Bochner-`L¹` on `(b,T)` for every
`b∈(a,T)`, `ρ≥0`, and `i : Fin 3`.

## No-terminal-trace implication

If the true old physical L² velocity lacks a strong terminal trace at `T`,
existing trace-obstruction results select a single component `i` of `R(t)`
that is not time-`L¹` on *any* positive terminal tail.  Subtracting the now
proved integrable physical correction `Pρ(R_i(t))` yields a genuine physical
high-pass residual `(I-Pρ) R_i(t)` that remains non-`L¹` on every tail
`(c,T)` with `b<c<T`.  Continuity forces cofinal physical `L²` spikes in this
*same* coordinate for every fixed `ρ≥0`.

The lack of a terminal trace is an explicit hypothesis; this theorem does
not assert its occurrence.  The operators are defined using the canonical
complex Fourier transform and real decoder, with genuine Hermitian reality
proved for the actual sources.  The new file proves their nonexpansiveness
and continuity, not an arbitrary complex-linear projector structure on real
physical `L²`.
