# Actual old-pressure temporal L¹ mass and the physical momentum distribution

Baseline: `6d268469` — *reduce physical momentum distributions to pressure defect L1 mass*.

## New reduction

The endpoint-independent snapshot estimate already gives a uniform pointwise
bound on each canonical pressure gradient, from the retained H³ ceiling:

    |∂ᵢ p_can(t,x)| ≤ B(E).

Thus for any smooth compact test coordinate φᵢ and every elapsed q:

    M_defect(q,i,φᵢ) ≤ M_old(q,i,φᵢ) + B(E) ‖φᵢ‖₁.

If the time profile of the old compact-tested gradient mass has an integrable
upper bound gᵢ, the defect is bounded by the integrable upper function
`gᵢ + B(E) ‖φᵢ‖₁` on each finite elapsed interval. This discharges the exact
pressure-defect temporal L¹ predicate already proved sufficient for old
spacetime Fubini, physical Hilbert differentiability and the physical
solenoidal distributional momentum identity.

The previous pressure-witness uniqueness result equates the spatial gradients
of any two actual pressures solving preterminal Navier–Stokes for the SAME
velocity. A second bridge therefore allows the temporal mass profile to be
proved using a convenient concrete pressure witness rather than the
`Classical.choose` witness from `LoggedPreterminalNavierStokesAdmissible`.

## What remains

The time-integrability of the old pressure gradient's compact-tested spatial
absolute mass is an explicit analytic premise. Separate continuity of the
old temporal derivative or pointwise spatial C² pressure regularity does
not suffice to infer that premise. The higher-order energy pressure witness
is a natural candidate for an independent time-regularity or compact-cylinder
estimate. This patch does not assert pressure-difference harmonicity,
pressure uniqueness beyond spatial constants, or unconditional regularity.

Audit: the new Lean module is imported by `PrimeTensor.lean`, all theorem and
predicate names are registered in `tools/audit/FirstMonomialTriad.lean`, and
`proof/generate_index.py` must be run after extraction.
