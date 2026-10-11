# Initial weak scalar FTC from positive-time derivatives and one sequence

Checkpoint: `3fefdb43` (`derive compact initial weak trace from scalar FTC`).

## Proven implication

An initial scalar weak FTC *at every time* does not need to be assumed. Given:

1. A single scalar `IntervalIntegrable g volume 0 b` source for each compact physical weak test and coordinate;
2. `HasDerivAt` of the actual positive-time scalar pairing with derivative `g` at every time in `(0,b)`;
3. Any one right-approaching sequence `τ n → 0+` on which the pairing converges to its prescribed actual initial value,

the interior FTC gives `F(t)=C+∫₀ᵗg` for all positive `t<b`. The Bochner/scalar interval integral has right limit zero. The sequence identifies `C` with the prescribed initial pairing. Thus the entire initial weak FTC family from the previous audit is *proved*, then fed into its existing canonical overlap, physical initial L², and H³ energy results.

The sequence and derivative can depend on the compact test; **no common strong physical L² source or uniform test estimate** is required.

## Still open

- Derive positive-time compact-test pairing derivatives, their initial-time `L¹` control, and the prescribed weak initial subsequence from a Navier–Stokes initial-value formulation. Pointwise NS on `(0,T)` alone does not identify the selected initial value.
- Establish the *actual old/selected* canonical H³ mild overlap from the PDE and initial condition. It is not implied by this scalar reduction.
- Resolve the independent actual terminal vorticity strong-H³ endpoint.

No `sorry`, `admit`, or new axiom is introduced. Local Lean verification must be performed with the project's installed mathlib toolchain.
