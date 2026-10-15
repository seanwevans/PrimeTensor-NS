# Sharp five-order physical Schwartz interpolation

Parent commit: `506d9be6` — prove sharp physical Schwartz fourth-order coercivity.

The real Schwartz full-order squared energy blocks are `E0`, `E1`, `E2`,
`E3`; the existing `D` is the complete 243-slot integral of fourth
ordered derivatives. These are not substitutes for the physical quantities.

## Mathematical derivation

Three now-proved adjacent coefficient-one Cauchy inequalities give

    E1² ≤ E0 E2,  E2² ≤ E1 E3,  E3² ≤ E2 D.

Squaring the middle inequality and chaining the two others shows

    E2⁴ ≤ E1² E3² ≤ (E0 E2)(E2 D) = E0 D E2².

If E2=0 the desired result is automatic. Otherwise E2²>0 and
cancellation yields **E2² ≤ E0 D**, with no interpolation constant.
The other two follow by squaring the outside adjacent inequalities:

    E1⁴ ≤ E0² E2² ≤ E0³ D,
    E3⁴ ≤ E2² D² ≤ E0 D³.

Every implication is formalized without dividing by an energy that could
vanish. Fourth-order coercivity also forces `D>0` whenever `E3>0`,
so every positive-endpoint profile has a strictly positive sharp shape
denominator before normalization. On the unit-endpoint representative (`E0=E3=1`) we obtain
`E1⁴≤D`, `E2²≤D`, `1≤D³`. The previously proved stronger `D≥1`
remains available.

## Scope and open issue

The results require no solenoidality or PDE evolution. They do **not by themselves** control the signed first-monomial term `M` or imply finite-time Navier–Stokes regularity. A finite universal critical-half constant **does exist mathematically**, by standard physical homogeneous Sobolev `L⁴` embedding and fractional interpolation; a proof for the project's exact Schwartz definitions, normalization, and aggregate is still a **Lean formalization target**. That bound alone is insufficient to absorb the nonlinear dissipation term at arbitrary critical norm. See `docs/audit/critical-half-roadmap-correction-2026-10-15.md`.

Public Lean module:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3SchwartzFiveOrderInterpolation.lean`.
