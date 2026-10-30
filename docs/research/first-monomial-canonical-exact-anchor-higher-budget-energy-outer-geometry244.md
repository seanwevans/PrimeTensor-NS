# Exact canonical higher-budget source–energy–outer geometry barrier

Base commit: `ce6a8e9c` — identify physical source and spectral gain costs of higher radial PDE rates.

The preceding source/gain theorem preserved the actual canonical first-crossing PDE windows and the attained physical projected-source envelope, but its last two alternatives still contained the abstract spectral linear and quadratic gains.

The physical anchor `K_k = ‖U₃(t_k)‖` also satisfies `K_k² ≤ E₃(t_k)` and the original first crossing gives `R_k=v(k)+1 ≤ Q_k=N(v(k))+1`. For a fixed radial order `m` admitting a nonnegative integrable real envelope of the actual `q^(4+m)` top physical moment, put `P_k=(R_k²)^m R_k⁶` and `Z_k=((R_k²)^m)² R_k⁹`.

For any source threshold `S ≥ 0`, and `ε > 0`, all sufficiently late original canonical windows satisfy at least one of:

1. An actual physical projected-source time inside `[t_k,t_k+(T-t_k)/2]` has norm strictly greater than `S`.
2. `R_k^(2m+3)*(T-t_k)/4 ≤ ε`.
3. `P_k² ≤ 512 ε² (2304 E₃(t_k) S² (Q_k+1)^10 + 1)`.
4. `Z_k ≤ 16 ε² (36 S² ((Q_k+1)^8+(R_k+1)^8) + 1)`.

The third branch uses the pinned physical quadratic linear-coefficient bound `Λ² ≤ 2304 E₃ C² (Q+1)^10`. The fourth uses the pinned eighth-power bound on the source-quadratic physical rate. There is no additional outer width cap, moment finiteness assumption, fixed cutoff ceiling, or new source estimate. The **only higher-moment upper-bound hypothesis** is the stated nonnegative real interval-integrable envelope for the chosen order `m`. The terminal no-L²-trace, kinetic mass, H³ admissibility/class and H³ full dissipation integrability assumptions remain those in the canonical construction.

This is a necessary conditional alternative, not a singularity contradiction or smooth continuation theorem. To exclude it, one needs additional genuinely PDE-derived source/energy/cutoff estimates or a bound preventing the geometric terminal-lag arm.

New Lean declarations:
- `h3Path_higherBudget_linearGain_forces_energyOuterTenth244`
- `h3Path_higherBudget_quadraticGain_forces_outerEighth244`
- `h3Path_scalar_higherBudget_sourceEnergyOrOuterEighth244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_sourceEnergyOuterGeometry244`

Compilation with the pinned project Lean/Mathlib toolchain is unavailable in the packaging container. Use the provided Lake, audit and baseline commands for validation.

## Local Lean correction (fix1)

The quadratic gain ceiling now uses a `calc` chain with an explicit
commutativity/associativity equality rather than `convert ... <;> ring`,
which had a closed/non-arithmetic goal. The positive inner-radius hypothesis
`1 ≤ R` is converted to the required `0 ≤ R` using
`le_trans (by norm_num : (0 : ℝ) ≤ 1) hR` before invoking the
linear energy and quadratic eighth-radius estimates.
No theorem statements or coefficients change. The original source-peak
and higher-moment envelope hypotheses remain explicit.
