# Source-driven dissipation drop forces actual high-radial spectral temporal transport

Base `3428e0d7`: the source peak-to-dissipation drop forces actual H³ spectral displacement.

## New PDE bridge

For two strict times `t <= s`, independent source cutoff `rho`, dissipation cutoff `sigma >= 0`, and velocity cutoff `R >= 0`, define:

- `H_rho,i(t)`: the actual highpass Fourier projected-momentum source
- `B(sigma,M)`: its kinetic-anchored source barrier when high-H³ dissipation is at most M
- `P = ‖H_rho,i(t)‖ - B(sigma,M) >= 0`: source margin at t
- `A = 3 + C_L (‖U(t)‖ + ‖U(s)‖)`: actual calibrated nonlinear PDE difference coefficient
- `L_R`: the exact weighted H³ temporal spectral square difference on the radial ball below R
- `H_R`: the exact weighted H³ temporal spectral square difference on its complement

The previous source-drop theorem yields `P <= A ‖U(t)-U(s)‖` if the actual
high-H³ dissipation has fallen to M by time s. The true finite-product sup
norm satisfies `‖U(t)-U(s)‖² <= spectralSquareEnergy(U(t)-U(s))`, while the
existing exact Plancherel partition proves that square energy equals `L_R+H_R`.
Therefore, with no temporal derivative assumption,

    P² <= A² (L_R + H_R).

The physical projected momentum FTC already proves that a local physical L²
source ceiling C on [t,s] forces

    L_R <= 3 W_3(R) (C (s-t))².

Consequently the PDE supplies the genuine finite-band cost in

    P² <= A² [3 W_3(R) (C (s-t))² + H_R].

If an independently established high-band temporal square displacement ceiling
`H_R <= J` is too small to satisfy this inequality, then high-radial H³
dissipation at s must remain **strictly above M**. The last theorem formalizes
this contrapositive, not a new assumption that high-band motion is bounded.

The physical source ceiling C is a local physical PDE quantity. Compact-time
existence of such a C is available upstream; no terminal-uniform C is shown.
The result explicitly isolates **high-frequency spectral transport** as the
unpaid remaining contribution, instead of postulating a full H³ time-Lipschitz
constant. It does not prove persistence uniformly to T, finite-time blowup,
or a Navier–Stokes regularity theorem.

## Declarations

- `h3Critical_sourceDrop_forces_temporalSpectralLowHighBudget`
- `h3Critical_sourceDrop_forces_highRadialSpectralMotion_or_PDEClock`
- `h3Critical_sourceDrop_PDEClock_and_highRadialCeiling_preclude_drop`

Lean compilation and the full audit baseline must be run in the user's pinned environment.

## Lean correction (fix1 at `3428e0d7`)

The two compiler failures were orientation mismatches in ordered addition.
`add_le_add_left hLow highTemporal` gives `low + highTemporal ≤
lowBudget + highTemporal`, matching the first sum exactly. In the final
contradiction, `add_le_add_right hHigh lowBudget` gives
`lowBudget + highTemporal ≤ lowBudget + J`, matching the prescribed
source-margin budget. Neither proof step changes any hypothesis or theorem
statement. This correction has been checked statically but still requires
Lean elaboration under the pinned toolchain.
