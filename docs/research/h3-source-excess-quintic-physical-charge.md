# Quintic physical H³ charge from an actual projected Fourier-source peak

Base: `b063ac0e`, the physical source-excess enhanced square-root quartic persistence theorem.

## New analytic coupling

Let κ=3(3+C_L)>0, and suppose the **actual** highpass Fourier source at a
strict physical time t exceeds the kinetic-anchored threshold by 5q, q>0:

    ||H_{ρ,i}(t)|| > Barrier(E₀,σ,M) + 5q.

The pre-existing barrier-shift estimate gives

    Barrier(E₀,σ,M+q/κ) <= Barrier(E₀,σ,M)+q.

Thus at the *enhanced* dissipation floor M'=M+q/κ the genuine source retains
strict excess P>4q. The accepted square-root-calibrated physical PDE theorem
then produces a positive actual interval of width δ=min(w,R⁻⁴), where

    A = 3+C_L(||U(t)||+E)
    B = 12 C²+2(D_full(t)+M')
    R = max(1,σ)+1+sqrt(A²B)/P.

Here C and E are boundedness certificates for the true physical source and
the true weighted spectral state on the one compact strict-time interval of
available width w. They are already derivable from local physical continuity;
no terminal-uniform bound is required. Because P>4q, the actual interval
satisfies the **explicit certified lower width**

    δ >= min(w, [max(1,σ)+1+sqrt(A²B)/(4q)]⁻⁴)

and the **true physical dissipation floor**

    D_full(s) >= D_>σ(s) > M+q/κ, for all s∈[t,t+δ].

## Fifth-power source-amplitude obstruction

Let J>0 bound the extended Lebesgue integral of real full-H³ viscous
dissipation on the *same certified window*. Its floor forces M'δ<=J.
Using the explicit lower width and the previously proved exact square-root
fourth-degree charge theorem, one obtains:

    w <= J/(M+q/κ)
      OR
    64 q⁵ <= κ J [16(max(1,σ)+1)² q² + A² B]².

This is fifth-degree in the prescribed source margin q: the extra factor
arises because physical high-radial dissipation must increase by q/κ at
the very same window, while the quartic persistence clock retains 4q of
source margin. The scalar normalization is exact: it multiplies the
existing fourth-degree margin constraint by κ/4.

The theorem `h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate`
instantiates this alternative directly from the actual physical Fourier
source and the PDE-certified persistence window. It does *not* require the
user to supply a separate calibrated-window equation.

The split q:4q corresponds to allocating one fifth of the source amplitude
to higher dissipation and four fifths to the clock. In a model with fixed
PDE cost and a dominant quartic term, this maximizes θ(1-θ)^4 at θ=1/5.
The cost B here depends on the enhanced floor and is not fixed as θ varies,
so this is a motivated explicit allocation, not a globally optimized NS bound.

## Limits

The geometric branch can still hold if original windows shrink too fast;
A and B can still diverge along terminal times. The full H³ dissipation
integral is **not** assumed finite up to T. Hence the present theorem is a
necessary local concentration constraint, not a global regularity result.

Declarations:

- `h3Critical_fivefoldSourceExcess_survives_oneFifthDissipationShift`
- `h3Critical_fivefoldSourceExcess_physicalOneFifthSquareRootPersistence`
- `h3Critical_fivefoldSourceExcess_noncompressedCharge_forces_quintic`
- `h3Critical_fivefoldSourceExcess_physicalDissipationBudget_forces_quintic`
- `h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate`

The source package is statically audited. Lean elaboration and the full
project baseline must be checked with the repository's pinned Lean/Mathlib.
