# Exact physical terminal source-tail moment barrier

Base HEAD: `10bfbccd564d5a454098615c1097e036f5adcfc1`.

## Why this is a new endpoint estimate

The prior committed dynamic-moment bound charges the physical eighth-order
annular dissipation to two quantities on a selected window: the **initial**
raw Fourier highpass and the source's absolute L¹ action **on that window**.
Those terms vanish but depend on the chosen window and its start time.

Here the already proved actual physical Hilbert FTC and terminal Bochner L¹
integrability of the projected momentum source G produce an **explicit, fixed**
physical endpoint state

    U := X(b) + ∫_b^T G(r) dr,
    X(t) + ∫_t^T G(r) dr = U,       b < t < T.

No limit is postulated. This identity is simply the FTC and additivity of the
Bochner integral, with the exact projected Navier–Stokes source.

Applying the genuine bounded real-linear physical Fourier map F and its
nonexpansive sharp high-radial projection yields for every b < s < T:

    ‖P⁺_n F X(s)‖ ≤ ‖P⁺_n F U‖ + ‖F‖ ∫_s^T ‖G(r)‖ dr.

Unlike the previous window-start estimate, the right side is controlled by
the actual terminal physical trace and the absolute source *terminal tail*.

## Exact critical-eighth consequence

For the same genuinely minimal physical annuli and their exact persistence
windows, set R_k=v(k)+1 and Q_k=N(v(k))+2. At any selected time s, the previous
annular dissipation floor and eighth-power Fourier comparison give

    η R_k^8 < 16 Q_k^8 μ_k(s).

The endpoint highpass inequality and monotonicity of the positive L¹ source
integral give

    μ_k(s) ≤ 3 (‖P⁺_(v k) F U‖ + ‖F‖ ∫_(τ_(v k))^T ‖G‖)^2.

Accounting for the factor already built into the exact fourth-jet annular
moment comparison, the resulting same-window bound is

    η R_k^8 < 48 Q_k^8 B_k^2,
    B_k = ‖P⁺_(v k) F U‖ + ‖F‖ ∫_(τ_(v k))^T ‖G‖.

Both terms of B_k tend to zero: the first by L² Fourier highpass tightness
for the *fixed* state F U, the second by absolute continuity of the Bochner
source integral at terminal time and τ_(v k)→T. The original summable
eighth-order clocks, uniform moving raw-mass smallness, and minimal radius
escape are all kept on the *same* physical witnesses.

## Boundary of the result

The bound does not limit the minimal outer frequency Q_k; a diverging Q_k/R_k
can still compensate for vanishing B_k. This establishes a cleaner physical
endpoint modulus against which any future *upper* transport/viscous frequency
amplification estimate must compete. It does not prove Navier–Stokes
regularity, the existence of a singularity, or a terminal strong H³ trace.

## Verification

The patch introduces four theorems, no new axioms and no Lean proof holes.
Only source structural checks are available in the packaging environment;
the repository-pinned Lean/mathlib toolchain and full baseline audit must
still be run locally before committing.
