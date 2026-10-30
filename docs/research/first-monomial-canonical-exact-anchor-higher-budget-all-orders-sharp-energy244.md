# Sharp fourth-power H³ energy for every higher-radial order

Base commit `c5b8b135` (`sharpen critical higher radial physical H3 energy cost to fourth power`).

For each fixed `m : ℕ` suppose an **additional** nonnegative interval-integrable
real envelope controls the physical extended q^(4+m) moment. On exactly the
canonical disjoint first-crossing PDE windows with inner frequency `R=v(k)+1`,
outer `Q=N(v(k))+1`, and anchor `t=τ(v(k))`, the existing four-way alternative
has the linear arm

    ((R²)^m R⁶)² ≤ 512 ε² (2304 E₃(t) S² (Q+1)¹⁰+1).

Assume eventually the actual attained projected source ceiling `C ≤ S`, the
critical cutoff `(Q+1)^8 ≤ D R^9`, and the noncompressed weighted time
`η ≤ R^(2m+3)(T-t)/4`, where `S,D ≥ 0`, `η>ε>0`, and

    16 ε² (36 S²(D+256)+1) < 1.

The source and time branches are excluded by the corresponding bounds.
Because `R≥1`, `((R²)^m)²≥1`, and `(R+1)^8≤256 R^9`, the quadratic arm is
excluded with the **same** small-ε threshold for every m≥0.

From the eighth-power outer bound:

    ((Q+1)¹⁰)^4 = ((Q+1)^8)^5 ≤ D^5 R^45.

Since `(Q+1)¹⁰≥1`, the linear arm raised to the fourth power yields

    R^(16m+48) ≤ (512 ε²)^4 (2304 E₃(t) S²+1)^4 D^5 R^45.

Canceling `R^45>0` proves the new bound

    **R^(16m+3) ≤ (512 ε²)^4 (2304 E₃(t) S²+1)^4 D^5.**

This specializes to exponent `35` at m=2, exactly the preceding commit.
The theorem preserves the same original canonical witnesses; no higher-order
spacetime integrability, source ceiling, geometric cutoff cap, or
noncompression is proved here. An arbitrary exponent does not supply an
unconditional terminal regularity result.

Declarations:
- `h3Path_higherBudget_anyMoment_linear_forces_sharpEnergyFourth244`
- `h3Path_higherBudget_anyMoment_outerCap_excludesQuadratic244`
- `h3Path_higherBudget_anyMoment_criticalBranches_force_sharpEnergyFourth244`
- `h3Path_noL2Trace_exactAnchor_anyHigherBudget_criticalOuter_sharpEnergyFourth244`

Static checks were run; Lean compilation must be verified with the repository's
pinned Lake/Mathlib environment.

## Local fix1

The intermediate fourth-power identity now has exactly the type consumed by the final `calc` chain. Its exponent equality is discharged once by `omega`, and `pow_add` / `pow_mul` handle the power algebra without trailing tactics after a closed goal. The theorem statements are unchanged.
