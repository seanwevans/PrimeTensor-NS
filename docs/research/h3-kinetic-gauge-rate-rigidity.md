# Arbitrary-gauge kinetic H³ rate rigidity under finite physical extended dissipation

**Base:** `1c5b3e93a36a5b4db0e1e82ff776f4fd1e6fd404`.

The previous accepted modules provide: (1) a no-terminal-H³-trace
arbitrary-frequency-gauge diagonal with its **unchanged physical times, natural
outer cutoffs, strictly separated annular windows and exact kinetic PDE widths**;
(2) finite-sum bounds against a single physical full-H³ extended dissipation
integral; and (3) real summability and vanishing of height-times-width charges
when an independently finite global extended dissipation budget is supplied.

## Exact charge identity

For `M >= 0` and `Lambda >= 0` and the exact physically selected width

    delta = min((T-x)/4, (M/4)/(2*(Lambda+1))),

the new scalar theorem proves the **identity**

    delta * (M/4)
      = min((T-x)*M/16, M^2/(32*(Lambda+1))).

This is stronger than a cost-based upper estimate: it isolates precisely the
two mathematical mechanisms that can make the actual dissipation charges
vanish. No terminal time regularity or additional PDE assumption enters.

## Quantified rate domination when the terminal clock does not collapse

If `delta(k)*(M(k)/4) -> 0` and, for some `eta > 0`,

    eventually eta <= (T-x(k))*M(k),

then for **every** fixed `K >= 0`,

    eventually K*M(k)^2 <= Lambda(k)+1.

Proof: for any K choose `epsilon` smaller than both `eta/32` and
`1/(32*(K+1))`. At late indices the accepted exact-width small-charge fork
prohibits its clock branch, so the rate branch gives
`M^2 <= 32*(Lambda+1)*epsilon`. The second epsilon constraint yields
`(K+1)*M^2 <= Lambda+1`, implying the desired domination. This avoids
asserting that the normalized rate is uniformly bounded.

## Actual physical consequence with arbitrary frequency gauge

Given any `G : ℕ -> ℕ`, choose the existing

    M(n) = 16 E0(b) (G(n)+1)^8 + 1.

The accepted physical diagonal supplies the **same** no-H³-trace witnesses
whose outer natural radii satisfy `G(v(k)) < N(v(k))`. If additionally

    lintegral_(a,T) ofReal(D_H3) <= ofReal(C),    C >= 0,

then the window charges `delta(v(k))*M(v(k))/4` are summable and vanish.
For every positive noncompression threshold eta and fixed K>=0, the explicit
condition

    eventually eta <= (T-tau(v(k)))*M(v(k))

forces eventually

    K*M(v(k))^2
      <= L_{N(v(k))}(E0(b)) + L_{v(k)}(E0(b)) + 1.

This is a necessary **superquadratic PDE-rate concentration law**, not a
proof of upper frequency control, of noncompression, or of Navier–Stokes
continuation. No no-physical-L²-trace premise is used, and no inconsistent
finite-dissipation/no-L²-trace combination enters.

## Registered declarations

- `thirdFull_scalar_exactKineticWidth_charge_minIdentity244`
- `thirdFull_scalar_noncompressedKineticCharge_superquadraticRate244`
- `thirdFullPhysical_noH3Trace_gaugeFiniteBudget_rateRigidity244`

The source is a proof candidate without `sorry`, `admit`, or added axioms;
its Lean elaboration must be checked with the repository's pinned toolchain.
