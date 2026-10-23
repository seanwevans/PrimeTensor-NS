# Physical projected FTC defect: interval cocycle and local gluing

Base commit: `6a91dcc4`.

Let `U(t)` be the actual physical old Hilbert velocity and `R(t)` the continuous physical projected Navier–Stokes source. Define

`D(a,b) = U(b) - U(a) - ∫_a^b R(s) ds`.

This module proves **unconditionally on every strict physical interval** the exact identity

`D(a,c) = D(a,b) + D(b,c)`

and consequently `‖D(a,c)‖ ≤ ‖D(a,b)‖+‖D(b,c)‖`. It also identifies the paired defect as the precise scalar velocity-increment residual against the projected source and gives the corresponding scalar cocycle.

**Local-to-global theorem.** If scalar solenoidal weak FTC holds on adjacent physical windows `[a,b]` and `[b,c]`, it holds on `[a,c]`. The premise may be weakened further: each window can have its own dense temporal sample family and only require zero *scalar solenoidal* defect pairings at those samples.

Neither continuity of the projected source nor the cocycle implies weak FTC by itself. The missing analytic obligation remains deriving local scalar distributional momentum evolution from the preterminal classical PDE with only the existing H³ bounds; pressure cancellation and justifying temporal-spatial integration remain material challenges.

No new global regularity claim is made. The cocycle and gluing are structural tools for local mollification or distributional arguments and for assembling overlapping restart intervals.
