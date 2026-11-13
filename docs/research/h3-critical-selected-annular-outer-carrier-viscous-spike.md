# Selected outer-carrier rigidity: physical eighth-order viscous payment

Base: `3781b517a6370c4b7e2c507c6c6272a20d23207f`.

## Actual cutoff identities

The **same** physical sharp Fourier highpass mass used in the annular excess
ledger is `M_r(t) = ‖U(t) - P_r U(t)‖²` for the real physical three-vector L²
velocity. For a weighted spectral scalar `G`, the actual H³ multiplier
satisfies `W₃(ξ)² = 1 + q + q² + q³`, `q = (2π‖ξ‖)²`.

On the radial complement `q ≥ r²`, so `r⁶ ≤ W₃²`. The raw-Fourier decoder's
a.e. inverse identity and the exact sharp complementary indicator yield

    r⁶ * ‖(I - P_r) raw(G)‖² ≤ ‖(I - P_r) G‖².

Applying this to the three actual physical coordinates and using the exact
physical Plancherel identification gives

    r⁶ M_r(t) ≤ weightedH3HighRemainder_r(t).

The already-established physical dissipation radial theorem supplies an
additional factor `r²`:

    **r⁸ M_r(t) ≤ D_H3(t).**

The result is pointwise for any genuine strict physical H³ time and
nonnegative real cutoff, without terminal H³ boundedness.

## Wide-annulus margin and viscous spikes

The previously compiled annular theorem establishes
`119 M_r(t) ≤ 128 M_s(t)` whenever `s ≥ 2r`, the strict physical kinetic
excess has positive margin `m`, and the exact actual annular deficit is
nonnegative. The original positive low-band kinetic budget also guarantees

    m ≤ ((r²+s²)/2) M_r(t).

Because `s ≥ 2r` implies `(r²+s²)/2 ≤ (5/8)s²`, it follows that

    **119 m s⁶ ≤ 80 D_H3(t).**

This preserves all physical fields, exact Fourier cutoffs, true Young-cost
and actual viscous dissipation. An actual pointwise cap `D_H3(t) ≤ H` forces
`119 m s⁶ ≤ 80 H`.

If the outer radii `s_k → +∞` at selected strict-time snapshots and their
strict margins satisfy `m_k ≥ c > 0`, then `D_H3(t_k) → +∞`. The conclusion
does **not** by itself imply divergence of `∫D_H3 dt`; the times may form
narrow, disjoint spikes. The remaining hard frontier is a lower time-width
bound or sufficient temporal persistence, from the physical PDE itself.

## Theorems

- `thirdFullKinetic_rawSharpHighpass_sixthMoment_le_weighted244`
- `thirdFullKinetic_weightedSharpVectorHighpass_exact244`
- `thirdFullPhysical_actualSharpHighMass_sixthMoment_le_weighted244`
- `thirdFullPhysical_actualSharpHighMass_eighthViscousCharge244`
- `thirdFullKinetic_wideOuterMargin_sixthViscous_scalar244`
- `thirdFullPhysical_selectedWideOuterMargin_forces_viscousSpike244`
- `thirdFullPhysical_selectedWideOuterMargin_viscousCapRadius244`
- `thirdFullPhysical_selectedWideOuterMargins_force_viscousSpikes244`

No axioms, admits, or sorry placeholders are introduced. Lean kernel
compilation must be checked on the user's configured repository/toolchain.
