# Third-order spatial absorption

Base: `849c3164`. New source:
[Control/ThirdOrderAbsorption.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/ThirdOrderAbsorption.lean).

The repository already proves the physical Fourier interpolation inequality
E₃⁴ ≤ E₀ D₃³ on each strict energy-class slice of an admissible H³ path.
Here E₀ and E₃ are the zeroth- and third-order energy blocks; D₃ is the
fourth-derivative dissipation block. These are not the normalized total E.

The new estimate is

    K E₃ ≤ ε D₃ + K⁴ E₀ / ε³,       K ≥ 0, ε > 0.

It follows from a division-free moment bound and a scalar polynomial Young
argument. The proof multiplies the established interpolation bound by K⁴,
then absorbs the resulting fourth-power inequality. The displayed remainder
constant is convenient; no optimal-constant claim is made.

This spends dissipation inside the spatial energy estimate without assuming
the nonlinear dissipation floor introduced in the preceding patch. It retains
the actual zeroth-order energy rather than replacing every factor with the
total H³ energy.

## Connection to the existing transport estimate

`velocityH3TransportDerivative3At_le_of_interpolation` provides a spatial bound

    |T₃| ≤ (24 + C) h(t) E₃

under its explicit regularity, flux-cancellation, pairing-integrability,
gradient-envelope, and interpolation hypotheses. Set K = (24 + C) h(t) when
that coefficient is nonnegative. The new transport corollary accepts this
bound and returns

    |T₃| ≤ ε D₃ + K⁴ E₀ / ε³.

Its input `hTransport` is explicit. It does not silently discharge the older
spatial theorem's hypotheses or claim a new estimate for the lower-order
transport blocks. The first physical interpolation theorem itself needs only
the admissible H³ path, energy-class slice, and scalar coefficient conditions.

## What is still required

This is a spatial absorption estimate, not a continuation theorem. To use it
in the full energy balance, the lower-order transport terms must also be
controlled and the residual coefficient must have sufficient time integrability.
The relevant normalized remainder is K⁴ E₀ / (ε³ E).

Substituting the coarse canonical K proportional to sqrt(E) can leave a
remainder proportional to E₀ E² before normalization. Thus the absorption step
alone does not automatically improve the temporal criterion. The next target
is a better coefficient K, or control of the normalized quartic remainder,
using the spatial structure that the coarse gradient envelope discards.

No existing proof or theorem statement is modified. The new module has a short
path and is imported by the root. Static source/index checks are available;
Lean compilation and axiom reports await the local baseline run.
