# Construct the critical-eighth physical Fourier carrier profile

Base HEAD: `a8d4a82957595dc7aad1932328f5bbe79f788c13`.

## Mathematical increment

The previous moving tightness theorem established the exact implication

    η(n+1)^8 ≤ M_n,   η > 0,
    finite full H³ dissipation, no strong terminal H³ trace
        ⇒ minimal (N_{v(k)}+2)/(v(k)+1) → +∞.

That theorem left `M` and its positivity, divergence, and critical-eighth
lower bound for its caller. The new theorem removes **all** of these profile
inputs. Given *any* positive real `η`, it selects

    M_η(n) := η(n+1)^8 + (n+1).

The existing minimal-first-crossing physical theorem may be applied directly
to this genuinely diverging profile. It constructs actual disjoint cofinal
windows with the attained projected-momentum-source maximum. Finite H³
dissipation gives a strong terminal **physical L²** trace, and the prior
raw Fourier tightness lemma proves exact moving-band mass tends to zero.
Hence the selected minimal outer/inner radius ratio tends to +∞ at the
critical-eighth scale. No artificially enlarged carrier radius is used.

The theorem *also retains on these same witnesses* the summable full H³
dissipation charges, genuine physical L² Hilbert momentum increment bound,
physical quintic/eighth source-viscosity rates, and the quantified attained
projected-source-or-spectral-gain alternative.

## Boundary of the conclusion

This is a conditional necessary consequence of **failure of the strong H³
terminal trace**, with finite full H³ dissipation and the established
physical admissibility/energy-class assumptions. It does not eliminate the
no-trace branch, establish the existence of blowup, or prove Navier–Stokes
regularity. The remaining hard mathematical task is to use actual PDE
transport and dissipation to rule out the now-explicit minimal frequency
cascade or to prove the requisite terminal H³ energy control.

No new assumptions, axioms, `sorry`, or `admit` are introduced.

## Verification

Source package only; the packaging environment does not include Lean/Lake.
The user-side script will regenerate `proof/order.txt`, compile the new
module using the repo-pinned Lean/mathlib toolchain, build the project, and
run the existing complete baseline audit before committing.
