# Critical-eighth terminal carrier: actual kinetic mass or frequency escape

Baseline: `11cc6a5b14a92235a70f7633e5d8fcadd7ef71ae`

## Mathematical advance

The previous result bounded an arbitrary-profile terminal first-crossing
height by the full earlier kinetic energy:

    M_n < 8 (N_n + 2)^8 E_0(b).

That estimate requires super-eighth height growth to force superlinear outer
frequency. The exact radial finite-band Fourier comparison yields instead

    M_n < 8 (N_n + 2)^8 μ_n,
    μ_n = ∫_{n+1 < |2πξ| ≤ N_n+1} |û(τ_n,ξ)|² dξ,

where the displayed shell convention is schematic and the formal theorem uses
the project's exact `h3TerminalRadialFrequencyBelow` set difference.

At any profile with **critical eighth lower height**

    η (n+1)^8 ≤ M_n,   η > 0,

we obtain the *same-witness* alternative, for every D ≥ 0,

    D (n+1) < N_n+2   or   η < 8 D^8 μ_n.

The choice of `N_n` remains the least physical annular crossing, not an
artificially inflated cutoff. In particular, if μ_{v(k)} -> 0, then

    (N_{v(k)}+2)/(v(k)+1) -> +∞.

This improves the exponent requirement from strictly super-eighth to the
critical eighth scale **conditional on actual moving-band kinetic mass
vanishing**.

## Physical source transport

For a strict positive-time interval [t,t+δ] with the genuine source envelope

    C = max_{r∈[t,(t+T)/2]} ‖Δu(r)-P(u·∇u)(r)‖_{L²},

the committed physical Hilbert FTC gives, for s∈[t,t+δ],

    ‖u(s)-u(t)‖_{L²} ≤ C (s-t).

The main theorem attaches this bound to the same disjoint, summably charged,
minimal first-crossing windows and retains their genuine source observation
and quintic/eighth-order rate alternatives.

## Remaining hard-math obligation

The repository already proves that finite full H³ dissipation yields a
strong physical L² terminal trace (`h3Critical_physicalL2_terminal_trace_of_finite_dissipation`).
A strong L² trace should imply uniform unweighted Fourier tail tightness,
and therefore μ_{v(k)} -> 0 whenever the inner cutoff tends to infinity.
The present Lean patch **does not claim that last implication has been
formalized**. It states the moving-band vanishing premise explicitly at the
last transport gate. A future module should derive it through the actual
physical Fourier transform, Plancherel, the sharp highpass projection, and
uniform tightness of a convergent family. This is distinct from proving an
H³ terminal trace or any solution of the 3D Navier–Stokes continuation problem.

## Audit and build

Run the included registrar with `--apply` then `--check`, rebuild generated
indexes using `proof/generate_index.py`, and compile the two Lean modules
in dependency order before the full build and baseline audit. Both theorem
files contain no `sorry`, `admit`, or new axioms. Compilation is not
available in the packaging environment and must be checked by Lake.
