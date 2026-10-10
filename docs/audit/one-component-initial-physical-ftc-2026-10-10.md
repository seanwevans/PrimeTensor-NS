# Initial H³ physical trace: derive vanishing modulus from physical FTC bounds

Parent: `7716b23e` — reduce initial physical H3 trace to vanishing time modulus.

`OneComponentInitialPhysicalFTCControl.lean` replaces the prescribed linear-time
velocity/energy bounds with genuinely separate physical initial-time integral
identities and time-dependent source terms:

* `u_j(t) - u_j(0) = ∫₀ᵗ V_j(s) ds` in the actual physical L² class, with
  `‖V_j(s)‖ ≤ Cvelocity` almost everywhere on each `(0,t)`;
* `E_H³(t) - E_H³(0) = ∫₀ᵗ g(s) ds` with integrable scalar rate
  `g(s) ≤ Cenergy` on `[0,t]`.

The Banach-valued interval-integral norm estimate and scalar integral
monotonicity supply respectively the quantitative velocity displacement and
energy ceiling with common rate `max Cvelocity Cenergy`.

This is a *conditional initial-value PDE interface*, not a derivation of
temporal velocity derivatives or top-order energy growth from the open-time
NS class, which excludes t=0. The strong terminal vorticity endpoint remains
independent. No new axioms, `sorry`, or `admit` have been added.

New declarations:

* `H3AuditInitialPhysicalZeroJetFTCControlData`
* `h3Audit_initialPhysicalZeroJet_FTC_displacement_le`
* `h3Audit_initialPhysicalH3Energy_FTC_growth_le`
* `h3Audit_initialPhysicalFTCControl_implies_linearRateData`
* `h3Audit_initialPhysicalFTCControl_implies_strongH3Trace`
* `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalFTC`
