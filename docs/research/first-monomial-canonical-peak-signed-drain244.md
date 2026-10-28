# Physical signed H³ energy drain at canonical source half-amplitude loss

Base: `d3dd7ac7` (forced half-amplitude loss or terminal compression).

At strict times `s<r<T`, suppose the **actual weighted H³ spectral** SUP norm decreases by a factor greater than two: `‖U₃(r)‖ < ‖U₃(s)‖/2`. Since this spectral velocity is a three-component product with the SUP norm and the real physical H³ energy equals `1 + ∑j ‖U₃(t)j‖²`, the endpoint inequality is

    E₃(s) - E₃(r) > ‖U₃(s)‖² / 4.

The physical energy path is differentiable at all strict energy-class times, and its exact Navier–Stokes balance is already proved:

    E₃'(q) + 2D₃(q) = -Transport₃(q).

The mean-value theorem therefore selects a genuine intermediate physical time `q ∈ (s,r)` with

    (r-s) (2 D₃(q) + Transport₃(q)) > ‖U₃(s)‖² / 4.

This is a signed rate identity, not positivity of transport. For the existing dissipation-budget-selected horizon `L=(B+1)/H`, the theorem upgrades the previous half-loss branch: either `T-s ≤ L`, or there exist `r ∈ [s,s+L]` and `q ∈ (s,r)` with both half-loss and the signed rate inequality above. The last theorem transports this result to the SAME canonical projected physical source maxima, unchanged disjoint annulus clocks and the same explicit critical-width assumptions.

This remains an alternative compatible with finite H³ dissipation; the transport term may be negative or positive, and no uniform-in-time control or global regularity is claimed. A next analytic step is an estimate on signed transport on short intervals strong enough to rule out or quantify the rapid-loss branch.

Status: source and registration checks only; build locally with Lean and audit axioms.
