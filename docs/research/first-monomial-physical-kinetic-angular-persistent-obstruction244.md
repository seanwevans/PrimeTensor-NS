# Physical angular Gram cofinal obstruction after checkpoint `eb1402df`

Let `U(t)` denote the actual physical Hilbert `L²` velocity, `E₀(t)=‖U(t)‖²`,
`L=lim_(t↑T) E₀(t)`, and let `R(t)` denote the physical projected momentum source.
The previously identified source Gram determinant is

    Δ(t) = E₀(t) ‖R(t)‖² − D₀(t)².

On the positive kinetic-energy branch it obeys

    √Δ(t)/E₀(t) = ‖(U(t)/√E₀(t))'‖.

The previous checkpoint (`eb1402df`) proved a terminal strong `L²` trace under
uniformly vanishing normalized Gram angular action. This file proves its
contrapositive in an explicitly quantitative form: if `L>0` and no terminal
strong `L²` trace exists, then there is `ε>0` such that for **every** cutoff
`b∈(a,T)` there are ordered `s,t∈(b,T)` with

    ε ≤ ∫_s^t √Δ(r)/E₀(r) dr
      = ∫_s^t ‖(U(r)/√E₀(r))'‖ dr.

Both endpoints are strictly later than `b`; the fixed lower bound cannot be
removed by passing to a shorter terminal tail. Moreover, since the interval
length is less than `T-b`, choosing `b` sufficiently late gives intervals of
**arbitrarily small duration** with the same fixed lower bound on angular action.

This is a *path-length* obstruction. It does not force a large chord
`‖N(t)−N(s)‖`: a curved path may rotate many times and return near its start.
Nor is the converse true: a strongly convergent path can have infinite
angular length. The current result does not infer H³ blowup or smooth
continuation, and does not prove that any Navier–Stokes trajectory has such
bursts. The final theorem includes the zero-kinetic-mass case, which has a
strong zero terminal trace unconditionally.

Lean source:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularPersistentObstruction244.lean`
