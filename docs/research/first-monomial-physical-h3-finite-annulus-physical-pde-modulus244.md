# Quantitative physical L² momentum variation from the genuine projected PDE

Checkpoint: `5341437b`, finite-annulus quantitative stability.

The actual physical projected PDE source `R(t)` is the strong derivative of the
old physical L² momentum `U(t)` at every strict preterminal time. The
previously proved source estimate

    ‖R(t)‖ ≤ (3 + C_Leray) velocityH3EnergyAt(u,t)

therefore yields on any strict interval [s,t] with `E3 ≤ E`:

    ‖U(t)-U(s)‖ ≤ (3+C_Leray) E (t-s).

A compact strict-time interval also admits a finite source ceiling without
imposing a global H³ energy ceiling, and the same rate controls all Hilbert
weak probes. The Lean module makes these precise with the actual physical
Hilbert types, and consumes the previously established unconditional interior
strong derivative, not an auxiliary physical evolution assumption.

## Still unresolved: cutoff–Plancherel transfer

The finite-annulus estimate in the preceding checkpoint is in the H³-weighted
Fourier state. The strong projected source is in *unweighted physical L²*.
The former cannot be bounded globally by the latter. One must construct the
band-limited Fourier encoder and prove, for a finite radius Q, a bound such as

    ‖1_{|D|<Q} W3 [û(t)-û(s)]‖₂ ≤ K(Q) ‖u(t)-u(s)‖₂,

using the exact physical Plancherel bridge and the boundedness of W3 on the
ball. Only after that identification can the genuine projected PDE source
supply the temporal variation of bounded-band H³ dissipation, and any window
width still depends on the selected outer cutoff and energy/source ceilings.

No uniform terminal time width, integrated divergence, or global smooth
continuation is claimed.
