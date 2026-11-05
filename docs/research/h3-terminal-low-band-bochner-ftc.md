# Terminal low-band H³ Cauchy from the actual physical projected source

**Base:** `86d196bd12fed89b75ba6fb57107b96848934140`

## The missing localization in the preceding checkpoint

The preceding kinetic-to-H³ finite-band estimate bounded the weighted low
band by the **whole** physical kinetic velocity difference. The physical
kinetic velocity may fail to be terminal Cauchy even when each *fixed* Fourier
ball of the projected momentum RHS is integrable in terminal time. Applying
the full bound to the cutoff RHS would therefore have been mathematically
invalid.

These modules perform the missing localization: the sharp radial indicator
acts both on the weighted solver state and on the raw physical Fourier state.
On `|D(ξ)| < R+1`, the exact weight satisfies

    W₃(ξ) ≤ C_R := sqrt(1+(R+1)^2+(R+1)^4+(R+1)^6).

Thus for arbitrary solver states `U,V`, with `raw(U)` their exact deweighting,

    ‖Q_R(U-V)‖_{H³} ≤ C_R ‖P_R(raw(U)-raw(V))‖_{L²}.

For two actual physical times the right side is the real physical
Plancherel transform of the *low-pass physical kinetic difference*.
The repository already proves that `P_R` preserves Hermitian reality
and has the exact physical Fourier round trip.

## Terminal Bochner Cauchy mechanism

At every fixed radius, the previous critical-energy branch proves that the
**actual physical low-pass projected momentum source** is Bochner-L¹ in
time on `(b,T)` under `PreterminalH3EnergyClass`. The three-component
sharp physical Fourier map is assembled as one bounded **real** continuous
linear map. Its image of the source is also Bochner-L¹ on `(b,T)`.

The already established `h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes`
transfers through this map, yielding *exact* low-band Fourier increments:

    F_R(t) - F_R(s) = ∫_s^t G_R(r) dr,    b < s,t < T.

The primitive of the L¹ Bochner path extends continuously to the closed
interval `[b,T]`, so its increments vanish uniformly as both observation
times approach `T`. Combining the quantitative fixed-band weight yields

    ∀R ∀ε>0 ∃δ>0 ∀s,t∈(b,T), T-s,T-t<δ
         => ‖Q_R U(s)-Q_R U(t)‖_{H³}<ε.

**No terminal full physical L² Cauchy input and no terminal full-source L¹
input** are needed.

## The precise outstanding hypothesis

This particular route uses the project's
`H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous` as an
EXPLICIT premise, because the already-proved global physical Hilbert FTC
consumes that premise. The new modules do not pretend it follows from
`LoggedPreterminalH3PathAdmissible` without additional work. An alternate
route would derive the same Hilbert FTC from the physical distributional
momentum equation on strict intervals; the existing equivalence theorem
shows why a proof of that PDE-to-FTC implication would discharge this gate.

Once fixed-band terminal Cauchy is available, the previously proved radial
Cauchy criterion shows that terminal H³ convergence follows from endpoint-
uniform high-radial tightness. In its absence the existing contrapositive
forces a single positive high-frequency threshold to recur beyond every
fixed cutoff at times cofinal in `T`.

This is not a Navier–Stokes continuation proof. The endpoint-high-frequency
tightness alternative is the remaining hard compactness problem.
