# Actual physical source-margin polynomial obstruction to quartic cost compression

Base: `ec333d53` (`TerminalActualSourcePeakCalibratedWidthCompression`).

## From cofinal calibrated width to a denominator-free PDE constraint

The previously proved calibrated quartic radius and physical width are

    R = max(1,sigma) + 1 + A^2 B / P^2,
    delta = min(w, R^(-4)),

with `P` the ACTUAL highpass Fourier source norm minus its kinetic-anchored
threshold, `A` the actual spectral-velocity source Lipschitz coefficient,
and `B=12 C² + 2(D_full(t)+M)` the nonnegative local PDE cost.

For `P != 0`, clearing the sole denominator gives the exact identity

    R^4 P^8 = ((max(1,sigma)+1) P² + A² B)^4.

If `M>0`, `J>0`, `B>=0` and the physical dissipation charge on a calibrated
window is at most J, the previous precise width dichotomy gives

    w <= J/M  OR  M/J <= R^4.

The second branch can now be expressed *without R or a fractional power*:

    M P^8 <= J ((max(1,sigma)+1)P² + A²B)^4.

This remains true if `P=0`, when the polynomial inequality is immediate.
A strict geometric noncompression condition `J/M < w` eliminates the first
branch outright. Thus any small cost J relative to the original available
physical window forces the actual source margin and PDE source/viscous
costs to obey the eighth/fourth degree polynomial constraint.

## Physical and family consequences

The Lean file proves that a genuine full-H³ viscous dissipation lintegral
ceiling on `[t,t+delta]`, together with a pointwise lower floor `D>=M`,
implies this same width-or-margin-polynomial alternative. The final theorem
lifts it to a family of cofinal candidate windows and index-dependent
physical charges. This can be applied directly to the witness arrays from
the cofinal calibrated theorem, after establishing whatever actual local
charge ceilings are desired. No uniform terminal ceiling is assumed.

The result is **necessary**, not an upper bound on source norm, a proof of
non-summable widths, or a continuation theorem. Deriving a contradiction
requires PDE information ruling out simultaneous geometric compression
and the polynomial source-margin cost branch.

## Lean declarations

- `h3Critical_calibratedRadius_sourceMargin_fourthPowerIdentity`
- `h3Critical_calibratedFiniteCharge_forces_window_or_marginPolynomial`
- `h3Critical_noncompressedCalibratedCharge_forces_marginPolynomial`
- `h3Critical_physicalDissipationBudget_forces_marginPolynomial_or_width`
- `h3Critical_calibratedFamily_physicalCharges_force_marginPolynomial`

Static validation is not Lean elaboration; compile in the repository's pinned toolchain.
