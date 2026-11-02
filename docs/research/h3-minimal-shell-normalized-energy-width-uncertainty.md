# Unconditional physical H3 energy–width restriction at minimal first crossings

Base GitHub commit: `73397f9e` (`force minimal H3 annular width escape under sublinear physical anchor energy`).

## New root-free normalized inequality

The same genuine minimal first-crossing physical H3 annulus used for the exact quadratic-sharp PDE window satisfies

    R^3 < 4 (Q+1)^2 E3(t),

where `R = v(k)+1`, `Q = N(v(k))+1`, `E3(t)` is actual physical H3 energy, and `L = N(v(k))-v(k)` is the true integer shell count. Since `R>0`, cancellation gives

    1 < 4 [E3(t)/R] [(Q+1)/R]^2
      = 4 [E3(t)/R] [(R+L+1)/R]^2.

This is a strictly positive *nonasymptotic* obstruction on each selected physical window, without assuming any terminal H3 energy, source ceiling, clock lower bound, finite full-H3 dissipation integral, or kinetic-mass depletion.

For any `D : Real`, if `L<=D*R`, then `Q+1=R+L+1<=(D+2)*R`, because `R>=1`, and therefore

    1 < 4 (D+2)^2 E3(t)/R.

Equivalently, every selected window lies in the pair of branches

    D*R < L  OR  1 < 4 (D+2)^2 E3(t)/R.

There is **no assumption** that one of these branches can be excluded. In particular, linear relative frequency width requires at least linear normalized H3 energy along that window; a superlinear width can instead pay for smaller energy.

## Same-witness transfer

The exported physical theorem reuses the cofinal disjoint minimal-shell witnesses and retains their exact minimality and last-shell-positive raw kinetic mass through `h3CriticalMinimalShellEnergyWindow`. It also retains the width-averaged energetic shell, the certified annular integral charge sum, and `h3CriticalMinimalShellPhysicalSixthNinthAlternative` (including its unbounded-charge branch). No independent cutoffs or times are selected.

## Limits of the result

This refines the earlier conditional `E3/R -> 0 => L/R -> infinity` theorem by making the tradeoff explicit at every snapshot. It does **not** establish `E3/R -> 0`, uniform kinetic control of the last shell, or a Navier–Stokes continuation theorem. The central unresolved work is deriving a dynamical restriction on `E3/R` or `L/R` from the signed physical H3 PDE and source estimates.

## Verification

The provided registrar adds one root import and three theorem `#check`/`#print axioms` entries to the existing audit, idempotently. Run the included build/push script. Lean compilation cannot be performed in the artifact packaging environment.
