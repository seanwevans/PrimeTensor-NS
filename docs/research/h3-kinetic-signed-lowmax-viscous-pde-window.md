# Signed LowMax sixth flux: PDE-certified finite-annulus physical viscous window

**Pinned base:** `765ce69e5f0d6d298761ea6ab5ad2342126cc239`.

The preceding signed-flux theorem forces an actual physical H3 viscous spike at
one of two selected strict times, or charges the weighted Schwartz-recovery and
true projected momentum source clock. Pointwise dissipation does **not** imply
a nonzero integrated charge without additional time regularity.

## New hard-math transfer

At a fixed LowMax radius `R`, write

- `A = 243[2(R+1)]^7 C0 (1+||V||+||W||)^3`, the native signed flux clock weight;
- `η > 0`, the adverse imaginary signed sixth-flux increment;
- `H = (R+1)^2 (η/4)^2 / [2(A^2+1)] > 0`.

The high-tail branch has `η/4 ≤ A ||P_R U(z)||` for an **original** observation
time `z=t` or `z=s`. Squaring and applying the already proven *high-radial*
physical dissipation coercivity at this same time gives

`(R+1)^2 (η/4)^2 ≤ A^2 D_>R(z)`.

Because `A^2 H < (R+1)^2 (η/4)^2` with no assumption that `A` is
nonzero, the actual positive high-radial viscous height satisfies

`H < D_>R(z)`.

The imported `thirdFullPhysical_highRadialSnapshot_profileAnchoredPDEClock244`
then selects one finite outer natural radius `N >= R`, actual local spectral
and projected-source ceilings `K,C`, and the **explicit** forward PDE width

`δ = min((T-z)/4, 1, (B(z)-H/4)/(2(Λ+Ξ+1))) > 0`,

where `B(z) = D_≤N(z)-D_≤R(z)` and `Λ,Ξ` are the imported *actual*
finite-annulus PDE variation coefficients. On the whole physical interval
`[z,z+δ]`, `B(r)>H/4`, and the exact real cost obeys

`δ*(H/4) <= integral_z^(z+δ) B(r) dr`.

The main theorem `thirdFullPhysical_strictGap_signedLowMax_clockOrPDEAnnularWindow244`
is an **unconditional alternative**: either the correctly weighted recovery
and physical source charge exceeds `η/2`, or one of the same original gap
times anchors the above physical annular window. It introduces no arbitrary
pointwise-viscous continuity or terminal H3 bound.

## Remaining obstruction

The new forward persistence window may extend beyond the right endpoint of
the **original** kinetic gap. Its outer radius `N` and width `δ` depend on the
actual selected time and on `K,C`. Neither disjointness nor a uniform width
lower bound follows here. To sum these real endpoint charges, one must
synchronize them with the original separated windows and retain the moving
frequency and cubic amplitude factors.

## Verification

Run the registrar, `proof/generate_index.py`, targeted Lean elaboration,
module build, full repository build, and proof fragment checks on the pinned
base before committing. Static ZIP checks do not prove Lean elaboration.
