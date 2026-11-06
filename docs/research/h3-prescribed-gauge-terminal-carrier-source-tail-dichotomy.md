# Prescribed-gauge terminal carrier / projected-source two-channel obstruction

Base commit: `2617b4ec2be05d43d78020211cf46e3cd42d2f77`.

## New analytic separation

The existing actual physical Hilbert momentum primitive constructs one fixed
terminal physical L2 state U. For a chosen H(n)>=1, the pre-existing
minimal-crossing physical windows with profile M(n)=H(n)^8 have eighth-moment
obstruction

    H(vk)^8 < 48 Qk^8 (Ak + Sk)^2

where Qk=N(vk)+2, Ak=||P+_(vk) Fourier(U)||, and
Sk=||Fourier|| int_(tau(vk))^T ||G(t)|| dt. Both Ak and Sk are nonnegative
and tend to zero. The new elementary coercive split proves, at *every*
selected k, the strict alternative

    H(vk)^4 < 14 Qk^4 Ak

or

    H(vk)^4 < 14 Qk^4 Sk.

The constant is valid because 14^2=196>4*48=192. If the fixed terminal
Fourier carrier does not pay 1/14 of the quartic-weighted height, the actual
projected physical source action necessarily pays it. Neither channel is
assumed nonzero a priori. The split does not replace actual source integrals
with peaks or unrelated source bounds.

## PDE-level significance

The first branch is a terminal kinetic Fourier carrier, the second is an
actual Navier--Stokes projected momentum-source tail. They have different
possible signed transport mechanisms. The result isolates which estimate
must be improved to obtain a true continuation obstruction. The gauge-escape
sequence, finite disjoint physical viscous charges, and vanishing combined
amplitude are the *same witnesses* from the committed prior theorem. The
witnesses remain dependent on the gauge H.

This is a necessary obstruction conditional on absence of terminal H3 trace.
It does NOT establish that either alternative occurs eventually on its own,
that Q/H is bounded above, or that Navier--Stokes continuation follows.

## Verification

Five theorem declarations. No `sorry`, `admit`, or axioms. ZIP and registrar
can be validated statically in this environment; Lean/Lake is unavailable.
Run the full project-pinned Lean/audit workflow before commit.
