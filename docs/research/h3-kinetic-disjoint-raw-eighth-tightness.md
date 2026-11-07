# Kinetic-selected H³ disjoint annuli: vanishing raw eighth carrier

**Base:** `736fe0fe0188f412950345ac5e93656b2984af2f`.

The current kinetic-only diagonal already realizes arbitrary physical
H³ dissipation spikes as finite annuli on exact disjoint PDE-selected clocks.
It proves a coarse instantaneous bandwidth ceiling

    M <= 16 * E0(b) * (N+1)^8.

The actual energy in the selected annulus is more informative than a fixed
global kinetic-energy constant. This module transfers an earlier sharp
physical annulus-to-raw-Fourier comparison to the **new** kinetic windows.

## Hard Fourier estimate on the actual witness

At the original selected time `x`, the local witness gives

    M/4 < D_low(N+1,x) - D_low(n+1,x).

The already-formalized actual spectral annular Bernstein estimate, with
no new Fourier normalization axiom, gives

    D_low(N+1,x) - D_low(n+1,x)
      <= 4*(N+2)^8 * mu(n+1,N+1,x),

where `mu` is the raw, unweighted physical Fourier L² kinetic mass
*inside the same annulus*. Hence

    M/4 < 4*(N+2)^8 * mu.

Unlike the old fixed coefficient `E0(b)`, this `mu` is a moving quantity
whose convergence can be proved independently from the physical terminal L²
trace. No minimal-crossing premise is added or cutoffs reselected.

## Raw mass tightness on the same disjoint kinetic clocks

The earlier theorem `thirdFullPhysical_movingBandRawMass_tendsto_zero_of_L2Trace244`
uses strong terminal physical L² convergence, exact raw Fourier Plancherel,
and a sharp highpass projector. On any strictly increasing cofinal inner
cutoff subsequence `v(k)`, it yields

    mu(v(k)+1,N(v(k))+1,tau(v(k))) -> 0.

Combining this with the actual annular cost gives the NEW consequence

    M(v(k)) / (N(v(k))+2)^8 -> 0.

This is a critical-eighth *little-o*, not a fixed-coefficient bound.
It applies to **arbitrary prescribed positive spike height profiles** on the
kinetic-only PDE-selected windows, not merely the existing minimal-attained
source windows.

## Physical hypothesis audit

The main transfer theorem takes the physical L² terminal trace as an
**explicit input**. The corollary obtains that trace from the existing
`h3Critical_physicalL2_terminal_trace_of_finite_dissipation`, under

    IntervalIntegrable (velocityH3DissipationAt u) volume a T.

An extended-real upper bound on dissipation was NOT silently substituted
for this ordinary interval-integrability hypothesis. There is no assumption
of a strong terminal H³ trace and no assumption of no terminal L² trace.

## Critical eighth outer-to-inner frequency separation

If additionally `M(n) >= 2*eta*(n+1)^8` for every n with `eta>0`, then
`thirdFull_criticalEighthHeight_vanishingBand_forces_escape244` applies with
`R=v(k)+1`, `Q=N(v(k))+1`, and `M'=M(v(k))/2`:

    (N(v(k))+2)/(v(k)+1) -> +infinity.

This retains the original kinetic-only selected width `delta(v(k))`, all
strict separation inequalities, and the actual annular Fourier mass. It is
not a continuation proof: unbounded outer-frequency escape is still possible.

## New theorems

- `thirdFullPhysical_kineticWindow_rawEighthAnnularCost244`
- `thirdFull_scalar_rawEighthCarrier_normalizedHeight_tendsto_zero244`
- `thirdFullPhysical_kineticDisjointWindows_rawEighthTightness244`
- `thirdFullPhysical_noH3Trace_disjointKineticRawEighthEscape244`
- `thirdFullPhysical_noH3Trace_disjointKineticCriticalEighthEscape244`

The source has no `sorry`, `admit`, or added axioms. It must still be compiled
under the repository's Lean 4 / Mathlib toolchain before a commit is made.
