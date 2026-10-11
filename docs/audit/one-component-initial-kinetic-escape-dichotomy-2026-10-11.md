# Initial kinetic escape alternative (checkpoint 016fb037)

## Newly derived result

The scalar initial-filter theorem separates a bounded cofinal sequence of
right-time samples from genuine divergence to the top filter. It uses no
monotonicity, no initial-time trace, and no integrability assumption.

For the actual Navier--Stokes order-zero kinetic energy, the previously
verified `h3Audit_initialKineticEnergy_antitoneOn_positiveInterval` promotes
cofinal boundedness to an entire positive-time kinetic ceiling. The physical
`L²` velocity norm-squared equals that kinetic energy by the prior physical
Fourier/jet identity.

Under the initial-data compatibility and the epsilon-accurate old/selected
relative-energy inequalities already used in the project, this gives:

* `h3Audit_initialComparison_compactWeakUniqueness_or_kineticEscape`:
  either the old and selected solutions have the audited compact initial
  weak-test comparison, or actual order-zero kinetic energy tends to infinity
  toward the right initial endpoint;
* `h3Audit_initialKineticNoEscape_implies_compactWeakComparisonData`:
  explicitly excluding kinetic escape removes the earlier cofinal-anchor
  assumption;
* an analogous alternative for the conditional two-component
  full-time intrinsic homogeneous three-halves time-`L²` bounds under the
  separate terminal strong-H³ actual-vorticity hypothesis.

## Remaining mathematical inputs

The open-time `LoggedPreterminalH3PathAdmissible` predicate alone does not
specify a finite right kinetic energy or establish that it cannot diverge
as time approaches zero. Its positive-time energy dissipation only makes
kinetic energy antitone going **forward** in time. The old/selected
vanishing-residual relative-energy inequality remains an independently
assumed PDE comparison, not a proven Navier--Stokes theorem.

The initial kinetic escape branch and the terminal strong-H³ vorticity
endpoint are distinct. This patch neither eliminates the escape branch nor
establishes a global regularity theorem.

Lean compilation must be performed in the user's configured repository.
