# Same-time critical annular anti-heat deficit: high dissipation or linear viscous charge

Accepted base: `e94e45997f113da4bac90375704f1b6cd65e0f1b` — bound annular outer Fourier tail by actual kinetic and H3 dissipation.

## Why the preceding quadratic budget does not close a disjoint L1 clock

The accepted physical Fourier outer-tail bound is

    Outer(t) ≤ 2 [k (B+3 D(t))]^2 + 2 rate^2 E,
    k = 3+C_L, B = 1+6 E, E = E0(b), D(t) = D3(t).

The existing disjoint-clock estimates pay integrals of the **first power** of D(t); no L2-in-time dissipation estimate has been established. Squaring the pointwise source ceiling therefore cannot be charged automatically to disjoint L1 viscous intervals.

## The exact cap linearization

For any real cap H with D(t) ≤ H (and D(t) ≥ 0), the elementary factorization gives

    [k(B+3D)]^2
       ≤ (k B)^2 + [6 k^2 B + 9 k^2 H] D.

The difference on the right minus left is exactly `9 k^2 D (H-D) ≥ 0`. This comparison requires **no** assumption of global terminal H3 boundedness. Define

    OuterBase = 2 (k B)^2 + 2 rate^2 E,
    OuterSlope(H) = 12 k^2 B + 18 k^2 H.

Consequently, for each genuine strict time below its selected cap,

    Outer(t) ≤ OuterBase + OuterSlope(H) D(t).

The annular Young-gap integral and the annulus-width mass remain untouched in the decomposition of the preceding physical annular cost.

## Physical charge-or-spike gate

Let `M(t,rho)` denote actual physical sharp highpass kinetic mass; let

    W = rho^6,
    rate = (rho^2+sigma^2)/2,
    K = 3 sqrt(E) C_kin(rho,E),
    X = W (rate M-K)^2,
    Shell = 2 ActualYoungGapAnnulus + ActualAnnularWidthMass.

On the original kinetic-excess branch `K ≤ rate M`, define the precisely unfunded amount

    Deficit = X - M [Shell + W OuterBase].

The new physical theorem proves at every strict time, for any real cap H,

    D(t) > H
    OR
    Deficit ≤ M W OuterSlope(H) D(t).

Thus on the bounded-D branch the previously quadratic tail is replaced by a **linear** actual physical H3 viscous charge. No division by M, radius-uniformity, terminal integrability, or artificially independent Fourier state is introduced. It remains meaningful when the highpass mass vanishes.

## Remaining hard-math frontier

This is a *same-time* algebraic/PDE alternative. An arbitrary pointwise viscous spike has zero time measure; the existing disjoint physical L1 clocks cannot be applied until a quantitative persistence duration is proved for whichever branch is selected. Also, the shell and width terms remain nonuniform as the radii move. The cap slope itself grows linearly with H, so taking H → ∞ does not yield a bound.

The next step is to synchronize this high-D/linear-charge split with actual selected annular PDE windows, deriving an explicit positive width or rate alternative rather than assuming it. No H3 continuation theorem is claimed.

## Audit

The registered Lean increment has seven theorem declarations and six definitions. It imports the accepted physical outer-tail and Plancherel compensation results. It introduces no axiom, `sorry`, or PDE assumption beyond those already explicit in the physical theorem. Lean kernel compilation must be performed using the repository's pinned toolchain.
