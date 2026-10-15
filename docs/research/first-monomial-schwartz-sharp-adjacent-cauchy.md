# Exact coefficient-one adjacent interpolation for real Schwartz H³ energies

Base: `d74ddab9` (`prove full physical Schwartz Hessian Laplacian contraction`).

## Analytic mechanism

The existing real Schwartz integration-by-parts lemma supplies the signed
identity, for each scalar Schwartz field `F`,

\[
  \sum_i \int (\partial_i F)^2 = -\int F \sum_i \partial_i^2 F.
\]

This is carried through all three physical velocity components to obtain

\[
  E_1(f)=-\sum_j \int f_j \Delta f_j.
\]

Applying the same identity to every first derivative `∂ₖ fⱼ`, with an exact
finite-index interchange, gives

\[
  E_2(f)=-\sum_{j,k}\int (\partial_k f_j)\Delta(\partial_k f_j).
\]

Both identities use the *actual ordered derivatives* in the project's H³
energy definition. A new SchwartzMap-valued axis Laplacian is definitionally
compatible with the already-established physical Laplacian of `d74ddab9`.

## Coefficient-one conclusions

Finite-family signed Cauchy–Schwarz, the 27-slot Hessian/Laplacian identity,
and its 81-slot first-jet counterpart yield, with no extra assumptions,

\[
  E_1(f)^2\le E_0(f)E_2(f),\qquad E_2(f)^2\le E_1(f)E_3(f).
\]

The existing division-free algebra bridge then gives exact-constant cubic
interpolation:

\[
  E_1(f)^3\le E_0(f)^2E_3(f),\qquad
  E_2(f)^3\le E_0(f)E_3(f)^2.
\]

Consequently a positive balancing scale `λ` with `λ⁶E₃=E₀>0` satisfies

\[
  E_0+\lambda^2E_1+\lambda^4E_2+\lambda^6E_3\le4E_0.
\]

This removes the earlier factor-three loss and its downstream constants
`27` and `8`, *without using Fourier normalization, incompressibility, or a
Navier–Stokes trajectory*.

## Boundaries of the result

The coefficient-one inequalities are established, but their optimality is not
separately proved in Lean. They are not a
proof that the signed 243-slot nonlinear first monomial satisfies a universal
critical-half bound. That nonlinear estimate remains a distinct analytic
obligation. No continuation conclusion is asserted by this module.

## Lean modules

- `FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentPairing.lean`: exact
  signed Schwartz Laplacian pairings for the first and second energies.
- `FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentCauchy.lean`: joint
  physical Cauchy, sharp adjacent and cubic inequalities, and balanced-scale
  four-block bound.

The audit registers `#check` and `#print axioms` for the public definitions
and theorem contracts. No new axioms or `sorry` are introduced.
