# Orthogonal covariance of the triad geometry

Base: 6428aafa, planar cancellation and normal-polarization geometry.

The new orthogonalFrequency action uses a real Euclidean linear isometry.
orthogonalPolarization applies that same map to the real and imaginary
parts of a complex polarization separately. The construction works for
any finite coordinate index type, not only Fin 3.

The patch proves preservation of:

- the real dot product;
- the mixed real-frequency/complex-polarization contraction;
- the complex bilinear amplitude contraction;
- momentum conservation and incompressibility;
- the ordered coefficient and complete six-order coefficient.

No Hermitian pairing replaces the bilinear contraction. Its real and
imaginary parts are expressed as real dot products, each preserved by
the supplied isometry. Both rotations and reflections are covered.

The concrete consequence is a planar-zero theorem for every orthogonal
image of the preceding planeFrequency/planePolarization configuration.
The result no longer depends on keeping the frequency plane aligned with
the ambient xy axes. The same covariance theorem also transports the full
plane-geometry formula when needed.

## Remaining steps

The current result takes an orthogonal frame as input. It does not yet
construct one from arbitrary frequencies, prove that every incompressible
polarization has the stated planar/normal parameterization in that frame,
or choose such frames measurably over the frequency integral. Degenerate
frequencies also require appropriate treatment in any representation theorem.

This is a basis-independent transport result for the symbol, not yet a
new integral estimate or a dynamical restriction on normal polarization.
The next quantitative question remains how much normal-polarization
interaction can be controlled along the actual flow.

## Checks

Source index, fragment consistency and whitespace checks run before packaging.
Lean compilation and the theorem audit remain pending on the pinned local
toolchain. No axioms or sorry declarations are introduced.
