# Uniform kinetic-only projected source and weighted H³ finite-band time modulus

**Base:** `715ab4964c84b495d93debfe70d7c31601b5b83f`.

## Actual Navier–Stokes source, with no full H³ ceiling

Let `b ∈ (a,T)` be a strict kinetic anchor, `E=velocityH3Energy0At u b`, and
`ρ≥0` any **fixed** Fourier gradient-frequency radius. Write `Sρ` for the
actual strict radial Fourier ball and `G(t)` for the true projected physical
Navier–Stokes momentum source. The verified physical source identity is

    physicalSharpLowCutoff_ρ (G_i(t))
      = lowRadialLaplacianPhysicalL2_ρ(U_i(t))
        - lowRadialLerayPhysicalL2_ρ(U(t),i).

The committed kinetic estimates give the genuine pointwise-in-time bounds

    ||lowRadialLaplacian_ρ||₂ ≤ ρ² sqrt(E),
    ||lowRadialLeray_ρ||₂² ≤ μ(Sρ) (18 ρ E)².

Consequently the *complete projected source* satisfies, **for every**
`b<t<T` and every coordinate `i : Fin 3`,

    ||physicalSharpLowCutoff_ρ (G_i(t))||₂ ≤ C_kin(ρ,E),
    C_kin(ρ,E) = ρ² sqrt(E) + sqrt( μ(Sρ) (18 ρ E)² ).

Crucially this is an actual Navier–Stokes estimate. It has NO factor depending
on a high-H³ energy bound, actual source maximum, terminal H³ norm or choice
of a large outer annulus cutoff. The sole source of frequency growth is the
specified finite radius. This is stronger than the earlier terminal Bochner
`L¹` conclusion for each fixed band: it provides a time-uniform pointwise
upper bound on the localized source.

## Physical momentum FTC → genuine finite-band Lipschitz regularity

The already formalized **unconditional** physical Hilbert FTC gives the exact
momentum increment between arbitrary strict times. Composing it with the
physical finite-band Fourier CLM and using the sharp cutoff/Plancherel identity
therefore yields, whenever `b<s≤t<T`,

    ||F_ρ X(t) - F_ρ X(s)|| ≤ C_kin(ρ,E) (t-s),

with `F_ρ` the actual real-physical-to-complex-Fourier sharp lowpass and
`X(t)` the genuine old physical Hilbert velocity.

The existing exact finite-band Sobolev weight multiplier then transfers this
to the **actual weighted H³ spectral state** `U(t)`:

    ||P_R U(t) - P_R U(s)||
       ≤ W_R C_kin(R+1,E) (t-s),

for **each fixed** natural radius R. This is a constructive, kinetic-only
physical time modulus, not an assumed spectral Lipschitz regularity.

## Original secondary observation times

The preserved secondary clock selects `zState,zSource` in
`[s,s+(T-s)/2]`, with `b<s<T`. For every fixed natural R,

    ||P_R U(zState) - P_R U(zSource)||
       ≤ (W_R C_kin(R+1,E)/2) (T-s).

The same original observations are retained, irrespective of which one
exhibits the secondary high-radial viscous spike. Therefore fixed-frequency
weighted H³ drift across these two actual times decays linearly with their
remaining terminal horizon. Any extreme temporal amplification must exploit
frequency growth, not a fixed-band source rate or a fixed-band spectral jump.

## Remaining analytical gap

The active secondary high-radial dissipation spike is eventually captured in
an **outer radius N that depends on the spike**, while `C_kin(N+1,E)` grows
with N. The theorem does not supply an upper bound on N, a radius-uniform H³
modulus, or the full terminal H³ trace. Next: combine the kinetic-only fixed
band source rate with annular gradient polarization to replace its existing
attained full-H³ state/source coefficients by an explicit kinetic/cutoff
polynomial, then test it against the original disjoint dissipation charges.
Do not sum new overlapping annular windows.

Lean 4.34.0-rc1 + pinned mathlib compilation is required on the user machine.
No `sorry`, `admit`, new PDE axioms, or .sh files are included.

## Registered declarations

- `thirdFullPhysicalKineticLowBandSourceCeiling244`
- `thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244`
- `thirdFullPhysical_actualLowBandSource_kineticCeiling244`
- `thirdFullPhysical_actualLowBandFourierSource_kineticCeiling244`
- `thirdFullPhysical_kineticLowBandFourierCoordinateLipschitz244`
- `thirdFullPhysical_kineticLowRadialH3Lipschitz244`
- `thirdFullPhysical_secondarySelectedTimes_fixedLowBandDrift244`
