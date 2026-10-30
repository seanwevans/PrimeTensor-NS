# Physical signed logarithmic secant gate for critical all-orders H³ radii

Base commit: `880d31c7` — force unbounded normalized signed H3 transport on every terminal tail.

This package does **not** impose any new transport estimate. It makes the
previously qualitative growth obstruction quantitative in the original
physical annular radius. On any strict physical H³ energy-class interval
`b < t < T`, exact differentiability and the mean-value theorem for
`log(velocityH3EnergyAt u)` select `s ∈ (b,t)` such that

    E₃(t) ≤ E₃(b) exp((t-b) g(s)),

where `g(s) = max(0,(-Transport₃(s)-2D₃(s))/E₃(s))` is *exactly* the
full-dissipation normalized physical PDE transport excess. The proof makes
no continuity assumption on g or on derivatives and does not relocate the
canonical PDE anchors.

Combining this sample ceiling with the established higher radial critical
fourth-power cost gives, for every fixed b∈(a,T) and eventually every
original canonical anchor tₖ=τ(v k), an intermediate sₖ∈(b,tₖ) with

    Rₖ^(16m+3) ≤ (512 ε²)^4
      (2304 E₃(b) exp((tₖ-b) g(sₖ)) S² + 1)^4 D^5.

Here Rₖ=v k+1. This sharp explicit gate retains all original hypotheses:
physical q^(4+m) time-integrable envelope, bounded attained projected source,
critical 8th-power outer cutoff, noncompressed weighted clock, positive epsilon
and epsilon smallness. This is not an unconditional Navier–Stokes estimate;
the PDE upper bound on g remains the open-strength closure step.

New declarations:
- `h3Path_physicalH3_signedLogSecant_exponentialCeiling244`
- `h3Path_higherBudget_energyFourth_to_signedExponentialFourth244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_signedExponentialSecantGate244`

No local Lean toolchain was available when packaging; compile with the pinned
Lake toolchain and report any elaboration errors.
