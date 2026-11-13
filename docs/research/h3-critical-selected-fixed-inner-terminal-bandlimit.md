# Fixed-inner selected annuli: the outer-carrier terminal bandlimit obstruction

**Base:** `f3ba426f92ec0ae70caabf84a35f394225de1114`

## New mathematical step

The accepted *exact* physical sharp cutoff identity at a strict positive
snapshot is

    M_rho(t) = N_[rho,sigma)(t) + M_sigma(t).

The accepted positive-excess, nonnegative-deficit Young-width estimate at
sigma >= 2*rho is

    119 M_rho(t) <= 128 M_sigma(t).

Unlike the earlier cofinal aspect-escape statement, this is a **relative**
retention requirement. At one fixed snapshot, physical Plancherel and raw L2
Fourier tightness give M_(n+1)(t) -> 0 as n -> infinity. Therefore if
M_rho(t)>0, the actual Navier--Stokes annular deficit cannot be nonnegative
at every sufficiently large natural outer radius where positive strict
kinetic excess also holds. No full H3 moment estimate is necessary for this
fixed-snapshot obstruction.

For cofinal physical times x(k) -> T, finite full H3 dissipation yields an
actual strong L2 terminal state L and moving sharp Fourier highpass tightness

    M_(n(k)+1)(x(k)) -> 0  (n(k) -> infinity).

If the **fixed** inner radius rho>0 supports eventually positive strict
selected kinetic excess and eventually nonnegative genuine Young-width
annular deficits, then the exact retention inequality forces

    M_rho(x(k)) -> 0.

The continuous sharp physical projector then identifies the endpoint:

    ||L - P_rho L||_L2^2 = 0.

This is a *terminal Fourier bandlimit*, not a spectral approximation: P_rho
is the same real Plancherel sharp cutoff that defines the actual physical
highpass mass. The proof never uses an independent highpass-tightness
assumption, invented frequencies, or an H3 terminal trace.

## Formal declarations

1. `thirdFullKinetic_outerRetention_tight_forces_innerVanishing244`
2. `thirdFullKinetic_naturalOuter_eventually_double244`
3. `thirdFullPhysical_fixedSnapshot_naturalOuterHighMass_tendsto_zero244`
4. `thirdFullPhysical_fixedSnapshot_noPersistentWidePositiveDeficit244`
5. `thirdFullPhysical_finiteDissipation_cofinalFixedInnerHighMassVanishes244`
6. `thirdFullPhysical_finiteDissipation_cofinalFixedInner_terminalBandlimit244`

## Scope and remaining frontier

This does not derive the strict annular excess or positive deficit from
Navier--Stokes. It demonstrates that *if* these witnesses persist on a fixed
inner cutoff and on diverging natural outer cutoffs, the terminal L2 velocity
must be bandlimited to the inner cutoff. The main remaining issue is to
connect the actual selected surplus/deficit witness construction to a
frequency carrier of the physical terminal trace (or to show that such
witnesses necessarily move their **inner** cutoffs as well).

Lean kernel verification is deferred to the repository's `lake` build.
