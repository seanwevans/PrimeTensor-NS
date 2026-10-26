# Ninth-order physical PDE rate versus eighth-order Fourier cutoff gain

Base revision: `4ba304e6`, joint sixth/ninth-order intermittent obstruction.

The physical quadratic PDE rate is **exactly** the square of the selected
projected momentum source ceiling multiplied by the cutoff amplifier.
The radial H³ weight-square ceiling is exactly

    W(ρ) = 1 + ρ² + ρ⁴ + ρ⁶.

For every nonnegative radius, `W(ρ) <= 4*(ρ+1)^6`.
The quadratic amplifier therefore simplifies *without any square-root
remainder* to

    H(R,Q) = 9*((Q+1)^2*W(Q) + (R+1)^2*W(R))
           <= 36*((Q+1)^8 + (R+1)^8).

This yields the literal physical quadratic-rate bound

    Ξ(R,Q,C) <= 36*C^2*((Q+1)^8 + (R+1)^8).

The same quadratic-sharp no-terminal-L²-trace witnesses from the parent
joint theorem now imply: for every positive geometric threshold and
nonnegative sixth-/ninth-rate thresholds, sufficiently late noncompressed
witnesses with bounded linear rate `Λ+1<=B*R^6` and squared source ceiling
`C^2<=S^2` satisfy

    D*R^9 < 36*S^2*((Q+1)^8 + (R+1)^8)+1.

In other words, the actual ninth-order quadratic barrier cannot be
attributed to an unconstrained abstract gain: a concrete eighth-power
cutoff cost is necessary. There is also a pointwise quantitative lemma:
when `R>=1`, `Q>=0`, and

    36*S²*(M^8+256)+1 <= D*R,

this lower bound excludes `Q+1<=M*R`.

The next task is to extract an eventual outer-to-inner radius escape from
the cofinal witnesses using their strictly increasing inner radii, and
to link any such radial separation to kinetic and spectral energy bounds.

**Scope:** The physical results remain conditional on *finite terminal
full H³ dissipation* and absence of a strong terminal physical L² trace.
Neither source boundedness, sixth-order linear-rate boundedness, geometric
noncompression, nor global Navier–Stokes regularity is established.

**Validation:** Packaged without a local Lean executable. The repository's
single-file, module, audit, index, and full builds are required.

## Compiler compatibility corrections

The proof-only replacement uses the existing strict positivity theorem for
the radial Sobolev ceiling instead of asking `positivity` to unfold it.
It scales the source-square comparison by 36 before multiplying by the
nonnegative radius sum, and uses a linear arithmetic step for the final
addition-order normalization. The theorem statements are unchanged.
