# Initial kinetic control from a full physical L² Bochner derivative

Parent checkpoint: `7914992b` (`derive initial kinetic control from bounded weak pairings`).

## New Lean module

`PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialBochnerDerivativeKineticControl.lean`

Rather than postulating bounded pairings against every full-L² probe along a cofinal positive-time sequence, this module uses an explicit temporal PDE regularity input:

- one Bochner-integrable three-component physical L² velocity derivative `V` on `(0,b)`;
- the actual old physical velocity has strong temporal derivative `V(t)` at every strictly positive `t` in `(0,b)`.

The already-proved interval FTC gives the old physical velocity increment identity between any two positive times. The integrable Bochner primitive has limit zero as `t → 0+`, giving a **finite strong L² right limit** (whose value is not initially identified with the time-zero velocity). From the exact physical kinetic norm identity, the genuine zeroth-order kinetic energy also has a finite right limit. The existing right-kinetic-trace comparison reduction supplies a uniform kinetic ceiling on a possibly shorter interval, then compact weak-test uniqueness and the physical initial trace follow under the independent vanishing-residual nonlinear comparison.

## Mathematical boundary

This does **not** derive an initial Bochner-integrable L² derivative from the preterminal H³ path class or prove that the right limit equals the prescribed time-zero jet before the comparison. The initial derivative estimate can require a genuine physical Navier–Stokes PDE-to-L² bridge, and is a stronger temporal regularity condition than mere bounded weak pairings. The vanishing old/selected relative-energy residual and the terminal actual-vorticity strong-H³ endpoint remain independent hypotheses. The results do not establish unconditional global regularity.

No `sorry`, `admit`, or added axioms are used. Verification requires `lake env lean` and `lake build` in the user repository; the assistant environment does not have Lean/Lake available.
