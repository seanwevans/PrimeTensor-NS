# Kinetic bound on the actual low-radial quadratic Fourier source

Based on `4ee5c8e2`. Four new theorems within `PrimeTensor.Bridge.Euclidean` prove a literal kinetic-anchor estimate on the raw product convolution of two actual velocity coordinates and, within a fixed radial ball, on one Fourier derivative of that convolution. The estimates use only the *actual* kinetic anchor, no positive terminal kinetic mass, no uniform H³ norm ceiling, and no raw Fourier L¹ input.

The quantitative estimates are

    |(û_j * û_k)(ξ,t)| ≤ E₀(b), t∈(b,T), every ξ,
    |d_i(ξ) (û_j * û_k)(ξ,t)| ≤ ρ E₀(b), |d(ξ)|<ρ.

The Fourier convention uses the repository's actual symbol `h3FourierDerivativeSymbol`; no untracked `2π` factor is inserted.

## Next genuinely missing steps

1. Sum finitely many differentiated products and contract with the actual Leray matrix, retaining a pointwise `C ρ E₀(b)` bound.
2. Convert the bounded-frequency Fourier pointwise bound to a spatial `L²` bound, with the explicit volume of the radial ball.
3. Identify that spectral low-pass source with a bounded physical Fourier projection of the actual time-dependent momentum source; then Bochner L¹ follows on each finite tail from time continuity and the kinetic ceiling.
4. Combine with the already proven conditional high-pass residual theorem at `31522454` to force actual high-pass source nonintegrability for the **same fixed spatial coordinate**.

This archive proves step zero (the exact quadratic convolution and first-derivative kinetic Bernstein estimates); it does not claim the Leray matrix and low-pass momentum-source estimates are already established.
