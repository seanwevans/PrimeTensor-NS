# Full-third projected Hermitian germ: hard-math checkpoint

Base commit: `912fdfaa` — close full third Hermitian local sign and polynomial lift proofs.

**New issue closed at the polynomial-symbol level:** The earlier local-tube
coefficient with value `-192` used frozen polarization vectors. Such vectors
are solenoidal only at their three center frequencies; they cannot be used
as a divergence-free Fourier field at displaced frequencies.

On PrimeTensor's native `Axis Depth.three`, use the polynomial transverse lift

`P_ξ(a) = (ξ·ξ) a - (ξ·a) ξ`.

At a center `η` with `η·η ≠ 0`, define the globally continuous germ

`L_{η,a}(ξ) = P_ξ(a)/(η·η)`.

The denominator is the **fixed** center frequency mass; there is no
frequency-variable denominator and no singularity at `ξ=0`.
The proofs establish `ξ·L_{η,a}(ξ)=0`, and if `η·a=0`, then
`L_{η,a}(η)=a`.

The module proves the corrected physical six-permutation polynomial is
trilinear in the three polarization slots. Substituting the three separate
germs `L_{p,A}(p')`, `L_{q,B}(-p'-r')`, `L_{r,C}(r')` gives a globally continuous,
pointwise solenoidal corrected Hermitian-phase kernel on the six-dimensional
momentum plane. It takes exactly the earlier `-192` value at the explicit
resonance. Hence a strictly negative closed ball exists and has a strictly
negative **localized integral**.

An additional exact trilinearity theorem factors an arbitrary common real
frequency window as `w(p) w(q) w(r)` times the transverse symbol.
This proves strict negativity where the three window values are positive,
and zero contribution when any one window vanishes. It is the algebraic
interface for the next global support argument.

**Not yet proved:** compact Hermitian scalar cutoffs, exclusion of noncoherent
interactions on the six-wave support, identification of this projected
polynomial with the actual complex Fourier polarization kernel for a single
Schwartz field, or nonvanishing of the global physical `G₃+3M` integral. The
new theorem cannot by itself discharge the nonzero physical-profile hypothesis.
