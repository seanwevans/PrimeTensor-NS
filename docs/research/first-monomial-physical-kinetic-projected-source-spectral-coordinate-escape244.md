# Fixed spectral coordinate behind terminal projected-source escape

**Base:** `e135f57a` — transfer fixed physical source escape to actual H³ spectral state.

Write `S(t) = h3AuditActualSpectralVelocityTotal hH3 t`. The previous
checkpoint proves that, when terminal kinetic mass is positive and the
physical Hilbert velocity has no strong L² terminal trace,

    ∀ b ∈ (a,T), ∀ M, ∃ t ∈ (b,T), M < ‖S(t)‖.

The state has exactly three coordinates in `Fin 3 → H3SpectralScalarState`
with the supremum product norm. New finite-coordinate pigeonhole argument:
if *each* coordinate had a ceiling on *some* terminal subtail, the maximum
of the three subtail starts and the maximum of the three ceilings would give
one common terminal subtail with a ceiling for the full product norm.
This contradicts the displayed statement, so **one fixed** `j : Fin 3`
works simultaneously for all terminal subtails and all thresholds:

    ∃ j, ∀ b ∈ (a,T), ∀ M, ∃ t ∈ (b,T), M < ‖S(t) j‖.

A separate generic triangle-inequality lemma proves that any uniformly
bounded spectral carrier `Low(t)` can be subtracted without extinguishing
cofinal norm escape:

    sup_{t∈(a,T)} ‖Low(t)‖ ≤ C
      ⇒ ∀ b ∈ (a,T), ∀ M, ∃ t ∈ (b,T), M < ‖S(t)-Low(t)‖.

This is **not yet** a high-frequency conclusion: an explicit low-frequency
cutoff and its kinetic-energy-based uniform ceiling still have to be proved.

Finally, the exact-mass strong physical L² trace versus fixed-spectral-
coordinate escape dichotomy is packaged for all nonnegative terminal kinetic
limits. If the limit is zero, the established zero-mass convergence theorem
produces the strong trace without any spectral escape claim.

The second branch remains conditional on failure of the physical L² terminal
trace. No inference from H³ nonextension to no-L²-trace, nor a Navier–Stokes
regularity closure, is asserted.
