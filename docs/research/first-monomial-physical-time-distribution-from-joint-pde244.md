# Joint-temporal-regularity bridge: classical PDE to distributions

**Base:** `0f70f9ed` — identify physical momentum distributions with strong Hilbert derivatives.

Existing `h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime`
proves the *actual old physical L² velocity* has derivative equal to the canonical
Laplacian-minus-Leray source at all positive times if the old temporal derivative
is **jointly continuous** in (time,space). The proof uses the preterminal
Navier--Stokes PDE, canonical short-window weak FTC and the old/selected
identifications already developed earlier.

This new bridge transfers that concrete PDE-side regularity theorem to:

1. The genuine regular scalar distributional momentum identity on any strict `(a,b)`;
2. The explicit compact-time-test identity with the correct derivative minus sign;
3. Actual physical solenoidal weak FTC on `[a,b]`;
4. The necessary obstruction: a nonzero Hilbert FTC defect refutes joint regularity.

Joint continuity is **not** derived from separate continuity, H³ path
admissibility alone, or a pointwise Navier--Stokes PDE. This is one
*conditional* completed PDE-to-distribution channel, not an unconditional
Navier--Stokes regularity proof. A weaker locally dominated test-product
channel remains an independent analytic goal.
