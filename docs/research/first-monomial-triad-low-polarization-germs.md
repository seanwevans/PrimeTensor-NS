# Solenoidal polynomial germs at the sharp low-normal centers

Checkpoint: `455da94d` — quantitative separation of six sharp low-normal triad centers.

The center geometry now admits isolated frequency neighborhoods with
radius `min(1, |t|)/4`. The next obstruction is constructing Fourier amplitudes
that are exactly solenoidal and that have the prescribed complex polarizations
at those centers.

For a real frequency ξ and complex vector a, define

    R(ξ) = Σ_j ξ_j²,
    P_ξ(a) = R(ξ) a − ξ (Σ_j ξ_j a_j).

The contraction `ξ · P_ξ(a)` vanishes identically, including at ξ = 0.
This polynomial is preferable to the pointwise Leray projection
`a − ξ(ξ·a)/|ξ|²`, since it introduces no singular frequency denominator.

At any nonzero center η with `η·a = 0`, the **normalized polynomial germ**

    G_{η,a}(ξ) = P_ξ(a) / R(η)

satisfies `G_{η,a}(η) = a`. The denominator is a constant for each packet.
The new module proves these identities for the prescribed sharp A/B/C
polarizations at p, q, r whenever t ≠ 0, and proves the polynomial reflection
identity

    P_{−ξ}(conj a) = conj(P_ξ(a)).

It does **not** claim these polynomial germs are Schwartz. The remaining
construction is to multiply each by a suitably supported scalar smooth bump,
reflect the three positive-center packets with complex conjugation, and sum
all six. A rigorous integrated lower-bound analysis must also account for the
packet width as t tends to zero and for all twelve resonant orderings.
