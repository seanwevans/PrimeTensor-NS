# Frequency-resolved coercivity from physical kinetic mass and weighted H³ concentration

Base: Git commit `6891600a` — construct disjoint persistence of canonical high-radial source peaks.

This checkpoint takes a more direct analytic step than adding qualitative persistence. It uses the exact Fourier splitting of the *three-coordinate Hilbert-square energy* and the physical kinetic monotonicity to prove a quantitative frequency-resolved estimate for the actual weighted H³ spectral velocity.

Let `U(t) = h3AuditActualSpectralVelocityTotal hH3 t`, let `b<t<T` with `b` in the energy-class interval, and let `ρ >= 0`. Define

- `K(ρ) = 1+ρ²+ρ⁴+ρ⁶` (exact ordered-derivative radial Fourier ceiling);
- `L_ρ(t) = h3PathActualSpectralLowRadialSquareMass244 ρ U(t)`;
- `H_ρ(t) = h3PathActualSpectralHighRadialRemainder244 ρ U(t)`, which the existing `h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244` theorem identifies with the *actual* high-frequency Fourier integral;
- `E₀(b) = velocityH3Energy0At u b` (old physical L² kinetic mass);
- `D₃(t) = velocityH3DissipationAt u t` (actual full H³ dissipation).

We prove at every strict physical time:

    ‖U(t)‖² <= K(ρ) E₀(b) + H_ρ(t)
    ρ² ‖U(t)‖² <= D₃(t) + ρ² K(ρ) E₀(b).

The norm is the **SUP** norm over the three spectral coordinates, not the Hilbert 2 norm. The proof uses `‖U‖² <= ∑ ‖U_j‖²`, then exact low/high splitting, instead of asserting a false equality.

If `2 K(ρ) E₀(b) <= ‖U(t)‖²`, then

    ‖U(t)‖²/2 <= H_ρ(t)
    (ρ²/2) ‖U(t)‖² <= D₃(t).

The polynomial bound `K(ρ) <= 4ρ⁶` for `ρ>=1` gives the explicit sufficient threshold `8ρ⁶ E₀(b) <= ‖U(t)‖²`. This exposes how moving Fourier radii must be balanced against physical kinetic mass in attempts to optimize dissipation coercivity.

The same half-dissipation inequality is proved *eventually* on **any fixed cofinal sequence of actual spectral peaks** with `‖U(s_k)‖ -> +∞`. It does not reselect physical times. In particular, one may instantiate it with the canonical source-maximizer peak sequence already established in the explicit critical-width branch by the preceding modules.

Finally, bounded partial sums of **nonnegative** disjoint persistence charges `d_k * (ρ² H_k)` imply `Summable` of the charges and `d_k * (ρ² H_k) -> 0`. The nonnegative-floor premise is stated explicitly in these generic budget theorems. For the canonical peak-centred construction the floor chosen at each original time is `max 0 (...)` and hence nonnegative, but the preceding existential witness interfaces do not expose that fact as a standalone conclusion.

## Remaining obstruction

The moving-radius threshold is **pointwise**, not a lower bound on physical persistence widths. Neither `D₃(s_k)` large nor strong spectral continuity alone bounds from below the time during which the high-frequency mass stays large. The new disjoint-window charges can still be summable, so no contradiction with finite terminal dissipation or unconditional Navier–Stokes regularity is claimed. A genuinely quantitative temporal bound at the moving Fourier scale is needed.

Status: generated and statically checked; Lean compilation requires the target checkout.
