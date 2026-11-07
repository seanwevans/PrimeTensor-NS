# Secondary physical H³ PDE amplification forces **high-radial** dissipation slices

**Base:** `1864934ff82f7006cf696edc91ca2acf5e9dc79f`.

## New physical step

The earlier squared-tail residual theorem chooses a secondary physical clock,
finite cutoff `J₂`, and actual maximizing times `zState`, `zSource`.
Under its activated two-slice rate, kinetic gap and deep-excess condition,
the obstruction was already reduced to either the normalized clock

    (T - s) A <= 192 B sqrt(R B)

or the two-time physical dissipation amplification

    A² <= 576 R B² [96 C₀ (E_b + 3 D(zState))
                         (E_b + 3 D(zSource)) (J₂+2)^5 + 4].

Here `A=V/(2P)`, `B=integral_m^T D`, `R=96 C₀ (J+2)^5`,
`C₀=3+initialLerayEnergyCoefficient` and `E_b=1+6 E_0(b)`.

At **any** nonnegative radial cutoff `σ`, independent of `J₂`, the previously
formalized physical kinetic anchor and exact Fourier partition imply at
both actual secondary observation times

    D(z) = D_low,σ(z) + D_high,σ(z),
    D_low,σ(z) <= Lσ = σ² W₃(σ) E_0(b),
    W₃(σ) = h3TerminalRadialSobolevWeightSquareCeiling σ.

Thus if the clock is not compressed and

    A² > 576 R B² [96 C₀ (E_b + 3(Lσ + M))² (J₂+2)^5 + 4],

then **at the same predetermined secondary observation times**

    D_high,σ(zState) > M   OR   D_high,σ(zSource) > M.

This is a *fixed-radius frequency localization* of the nonlinear PDE
amplification. The quantifiers are significant: the selected `s`, `eta₂`,
`J₂`, `zSource` and `zState` are chosen first, then the conclusion holds for
all `σ >= 0`, `M` satisfying the explicit strict threshold. No time or
cutoff is reselected to make the conclusion true.

## What is and is not proved

The proof reuses the exact physical Fourier low/high viscous partition,
the kinetic low-frequency ceiling, and the cofinal squared PDE branch.
The original frequency escape, physical primary clock, terminal viscous
charge and disjoint windows are preserved. No new axioms or proof
placeholders are used.

**Still open:** a quantitative *temporal persistence width* for one of these
selected high-frequency spikes, sufficient to charge a positive portion of
the integrated terminal H³ dissipation. Pointwise amplification is compatible
with a finite integral when its time widths collapse. In particular, this
result neither bounds moving `J₂` nor asserts full H³ regularity.

To verify: pinned Lean 4.34.0-rc1 + mathlib, new module + audit + root
build, regenerate `proof/order.txt` with `proof/generate_index.py`.
