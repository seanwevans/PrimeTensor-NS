# Initial canonical weak FTC transferred to actual positive time

Checkpoint: `67441a3a` (`derive full Schwartz momentum derivative from solenoidal weak FTC`).

## New proof results

`OneComponentInitialCanonicalWeakFTCAbsoluteTransfer.lean` proves that the exact old physical zeroth-order Hilbert velocity at absolute time `t + q` equals the canonical elapsed zero-jet on every strictly positive old restart window. Alongside the committed physical RHS identification, this transfers the existing old scalar divergence-free weak FTC from elapsed time to the actual physical time interval `[t,t + τ]`. The integral transfer uses `intervalIntegral.integral_comp_add_right` and explicit pointwise identification on the integration interval.

The committed Leray-fixed weak-to-strong theorem then upgrades this transported solenoidal FTC to an actual physical Schwartz-test `HasDerivAt` identity for every interior time of the interval. Under the separately declared `H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous`, the repository's earlier old-branch weak-FTC theorem discharges the solenoidal FTC premise. Using local canonical restart-window coverage, this gives a global *positive-preterminal-time* statement against all physical Schwartz tests.

## Assumptions still not closed

* Joint spacetime continuity of the old physical temporal derivative is an **additional old-branch frontier**, not an automatic consequence of the basic `LoggedPreterminalH3PathAdmissible`.
* Initial `IntervalIntegrable (velocityH3EnergyAt u) volume 0 b` is not derived from positive-time regularity.
* Vanishing selected/old initial relative-energy residual is separate.
* Terminal actual-vorticity strong-H³ endpoint is separate.
* The patch does not assert global Navier–Stokes regularity or remove any independent PDE hypothesis.

No `sorry`, `admit`, or custom axioms are introduced. Local Lean compilation and complete audit must be performed in the user's Rocky Linux repository before committing.
