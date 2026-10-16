# Radius-dependent quantitative Sobolev with split norms

Baseline: `44554639` — quantitative radius-dependent cutoff Sobolev bound.

The old lemma proves a cutoff bound by the `L²` norm of a *function-valued*
majorant `‖Dg‖ + (C/R)|g|`. This module applies the already existing
`eLpNorm_add_le` and `eLpNorm_const_smul` to obtain the **quantitative**
finite-radius bound

    ‖χ_R g‖₆ ≤ S ( ‖Dg‖₂ + (C/R) ‖g‖₂ ).

Here `S` is exactly the Mathlib finite-dimensional compact-support Sobolev
constant, and the finite `C` is the PrimeTensor cutoff derivative constant,
independent of the field and radius. The result is unconditional for `C¹`
fields satisfying the stated `L²` hypotheses. Nothing relies on solenoidality
or Navier–Stokes.

The norm splitting is the part needed for the **next** proof: letting `R` tend
to infinity and using lower semicontinuity/Fatou to conclude

    ‖g‖₆ ≤ S ‖Dg‖₂.

That limit theorem is *not* claimed in this file. The limiting estimate is
classical, not a new Navier–Stokes regularity theorem.
