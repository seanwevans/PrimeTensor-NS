# Critical-eighth viscosity clock versus actual projected-source action

Base commit: `615a63c93e07da7ae9341d2a419c0ea1697e555e`.

## New hard estimate

On the physically selected, disjoint, *minimal first crossing* windows from
`thirdFullPhysical_noH3Trace_constructiveCriticalEighthSourceEscape244`, the
height is fixed by

    M_η(n) = η (n+1)^8 + (n+1),    η > 0.

Finite H³ dissipation already makes the actual disjoint window charges

    Σ_k δ(v k) M_η(v k)/4 < ∞.

Since each δ(v k) > 0 and M_η(v k) ≥ η (v k+1)^8, we have

    0 ≤ (η/4) δ(v k)(v k+1)^8
      ≤ δ(v k) M_η(v k)/4  → 0,

so the *actual PDE window clock* obeys

    Σ_k δ(v k) (v k+1)^8 < ∞,
    δ(v k) (v k+1)^8 → 0.

This is a critical-frequency clock constraint, not a new assumed time scale.
It is independent of the selected outer radius N(v k), which is already
known to escape relative to v k.

## Attained physical PDE alternative

C(v k) is the actual attained maximum of the projected physical momentum
source on the selected half-terminal interval. For every ε>0, D≥0, the
shrinking eighth-order viscous clock forces, eventually,

    C(v k) δ(v k) < ε

or there exists a real source-attainment point s_k in

    [τ(v k), (τ(v k)+T)/2]

for which

    D (v k+1)^8 < ‖projected momentum source(s_k)‖.

This comes directly from multiplying the negation of the source peak
inequality by the positive selected window width, and using the converging
viscous clock. The source alternative uses the same source whose maximum
enters the physical Hilbert FTC transport estimate on the original windows.

In particular, if some ε>0 satisfies

    ε ≤ C(v k) δ(v k)

at all sufficiently large selected k, then the attained projected-source
maxima must eventually exceed every fixed eighth-power multiple.

## Logical boundary

This is a *necessary* property of a putative no-terminal-H³-trace branch
under the established physical admissibility, energy class, and finite
full H³ dissipation. Source peak amplification is an alternative, not a
proved impossibility. Nor does small peak-times-width force small absolute
source integrals outside these selected windows. No new axiom or unsolved
Lean placeholder is introduced.

## Verification

Source-only ZIP. Regenerate the project import index with
`proof/generate_index.py`, check registrar and index, compile the new module,
run the complete project build and baseline audit before committing. The
packaging environment does not have Lean/Lake, so local compilation remains
the necessary verification gate.
