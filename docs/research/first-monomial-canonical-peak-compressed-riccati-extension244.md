# Compressed canonical H³ peaks versus the intrinsic Riccati floor

Base commit: `956a3292`.

The existing critical-width joint-escape theorem selects physical disjoint
quadratic-sharp windows and the canonical physical projected-source maximizers
`s(k)` *before* the conditional critical-width tests. Under those tests,
`A_k = ‖U₃(s(k))‖ → ∞`.

The immediately preceding theorem eliminates the half-loss alternative at
sufficiently high peaks. In the remaining compressed branch,

    A^8 = 16384*(E₀(b)+1)*H^3,
    T-s ≤ (B+1)/H,

where `B` is the finite physical viscous budget.

If there is **no smooth continuation**, the previously established intrinsic
Riccati lower clock applies to this exact physical time `s`:

    2 ≤ K*(T-s)*sqrt(E₃(s)),
    K = 4422*(C₁+1) ≥ 0.

The physical H³ energy is **not** `1+A²`: it is `1+Σⱼ‖Gⱼ‖²`.
The previous three-component product-sup estimate gives
`E₃(s) ≤ 1+3A² ≤ 4A²` for `A≥2`. Thus

    H ≤ K*(B+1)*A.

Substituting into the exact optimized height identity yields

    A^5 ≤ 16384*(E₀(b)+1)*(K*(B+1))^3,
    A ≤ 16384*(E₀(b)+1)*(K*(B+1))^3.

The right-hand side is independent of the diverging `A_k`, so the unchanged
conditional critical-width regime and nonextension cannot both hold.

The main theorem `h3Path_noL2Trace_canonicalWidth_criticalRegime_forces_extension244`
retains the same cofinal canonical source maxima, first-crossing annuli,
and pairwise-separated quadratic-sharp windows. Given an admissible preterminal
H³ class, positive terminal kinetic mass, no strong terminal H³ trace,
and integrable full physical dissipation, it proves **if** the original
three critical-width/rate hypotheses hold eventually (for any fixed admissible
positive `η`, nonnegative `U,V`) **then** a smooth continuation exists.

**Scope:** This is not unconditional Navier–Stokes regularity. The eventual
critical-width/rate bounds are substantive additional hypotheses and are
not proved here. The conclusion is a conditional closure of the existing
canonical peak argument.

Validation: source and registrar syntax, proof placeholder checks, ZIP
integrity and idempotent registration. Lean compilation must run against
pinned project dependencies in the user's repository.
