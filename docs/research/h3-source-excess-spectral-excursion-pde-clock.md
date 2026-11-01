# Cofinal fivefold H³ source: actual finite-band PDE clock or high-radial temporal mass

**Base:** `e9acb4cd` — accepted physical anchor continuity radii.

## Physical obstacle

Strong positive-time continuity of the actual weighted H³ spectral velocity
supplies, on each compact preterminal window, a positive but uncontrolled
continuity radius. It does **not** supply a terminal-uniform Lipschitz bound
for the full H³ spectral norm. In contrast, the repository already proves a
quantitative finite-frequency bound using the genuine physical projected
momentum FTC and the exact Plancherel normalization:

    L_R(U(x),U(s)) ≤ 3 K(R) [C (s-x)]²,
    K(R) = 1 + R² + R⁴ + R⁶,  R ≥ 0.

Here `C` bounds the norm of the actual projected momentum source between
`x` and `s`, and `L_R` is the true weighted spectral velocity square defect
on the low Fourier ball of radius `R`. The exact low/high identity and the
preexisting spectral norm/square-energy estimate give

    ||U(x)-U(s)||² ≤ L_R(U(x),U(s)) + H_R(U(x),U(s)),

where `H_R` is the *actual* high-radial temporal Fourier square mass.

## Unconditional selected-window quantitative gate

On any selected source window `[x,x+w]` and any `s∈[x,x+w]`, with
`C ≥ 0` an actual projected-source ceiling, a spectral excursion
`ε ≤ ||U(s)-U(x)||` (for `ε≥0`) implies

    ε² ≤ 3 K(R) C² w² + H_R(U(x),U(s)).

Consequently at least one of

    ε² ≤ 6 K(R) C² w²
    ε² < 2 H_R(U(x),U(s))

must hold. This is a rigorous finite-radius time-rate / genuine high-radial
spectral-motion alternative, not an assumed global H³ temporal modulus.

## Cofinal transfer with exact original witnesses

The accepted no-terminal-physical-L²-trace theorem supplies *the same* strictly
cofinal times, pairwise-separated calibrated windows, attained source/spectral
maximizers, exact A/B coefficients, strict full H³ dissipation floors, and
sum of physical viscous charges. No reselection is made.

For every window index `k`, every `R≥0`, and every `ε>0` satisfying

    3 + 4 C_L ε ≤ S_k = max(1,σ(v(k)))+1,

the previously accepted non-spectral-excursion branches remain, OR

    ε² ≤ 6 K(R) ||ProjectedSource(sSource_k)||² w_k²,

OR

    ε² < 2 H_R(U(t_k),U(sState_k)).

The preserved other branches are: actual Riccati observation, geometric
compression, cutoff-only cost, *spectral anchor* concentration, projected
source anchor concentration, projected source temporal excursion, physical
instantaneous dissipation, and source-floor expenditure. The projected-source
temporal excursion is *not* removed because the available physical momentum
FTC controls U in L², not the time derivative of its projected source R.

The maximizing times may remain outside the shorter calibrated windows.
This theorem cannot yield a terminal H³ bound without controlling the growth
of K(R), the source maximum and the complementary high-radial mass.

## Audit declarations

- `h3Critical_actualSpectralExcursion_lowPDEPlusHighRadial`
- `h3Critical_actualSpectralExcursion_PDEClockOrHighRadial`
- `h3Critical_scalar_spectralThreshold_forces_excursion`
- `h3Critical_fivefold_nonSpectralExcursionAlternative`
- `h3Critical_noL2Trace_cofinalFivefold_spectralExcursionPDEClockGate`

Run the pinned Lean compiler and full project baseline. Static source and
archive checks alone are not proof elaboration.
