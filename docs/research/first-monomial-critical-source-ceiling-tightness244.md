# Audit of chosen PDE ceilings versus actual projected L² source

Base commit: `80d011c6` — force projected PDE source escape under bounded critical annular width.

The predecessor forces `C(v(k))² → +∞` under the specified persistent noncompression, sixth-order rate, and ninth/eighth width cap. The quantity `C` originates from the existential strict-time uniform L² source bound `h3Path_actualProjectedMomentumSource_uniformL2OnStrict244`. Such a chosen *upper bound* is not in general equal to the actual projected source norm or the least window supremum. Therefore divergent selected `C` alone cannot establish divergence of `‖Δu - P(u·∇u)‖`.

This module formally separates the two mathematically legitimate scenarios on the *same* cofinal physical witness sequence. If a fixed `E` satisfies `|C(v k)| ≤ ‖R(τ(v k))‖ + E` eventually, then actual snapshot source norms tend to `+∞`. If instead `‖R(τ(v k))‖ ≤ E` eventually, then the slack `|C(v k)| - ‖R(τ(v k))‖` tends to `+∞`. Both follow from coefficient-square divergence by elementary order/filter facts; no extra PDE hypothesis or nonzero spectral mass is smuggled in.

This exposes the next genuine analytic obligation: construct source ceiling choices whose overhead relative to an **actual physical source observable** is controlled. The existing arbitrary compact-interval ceiling does not provide that efficiency. An alternative is to prove a uniform bound on the chosen ceiling from actual PDE estimates, which would contradict the width-capped regime. Neither is proved in this file.
