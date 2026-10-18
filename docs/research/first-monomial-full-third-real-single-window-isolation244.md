# Exact isolation of the actual full-third real Schwartz Fourier windows

Checkpoint: `87628bb9` (global six-sector commutator integral).

For Fourier width `ρ > 0` with `2ρ ≤ 1`, the established unit separation
of the six axis-coordinate frequency centers forces all windows other than
the selected one to vanish throughout its radius-ρ center ball. On each of
the three positive center balls, even the conjugate-reflected positive packet
vanishes at the opposite frequency; consequently the *actual recovered real
Schwartz velocity* Fourier vector is precisely the prescribed compact smooth
window times the moving solenoidal transverse germ. The third positive
center preserves its complex phase `I`.

New theorem declarations include the nonresonance-width bridge, generic separation and uniqueness
results, three Hermitianized single-window identifications, and three
corresponding identities for the real physical Schwartz Fourier spectrum.

**Unresolved:** this does not by itself compute or bound the complete signed
trilinear H³ kernel on each of the six coherent pair sectors. The next hard
step is to substitute the three isolated moving germs into the full 3+3+1
plus 3+2+2 kernel and prove a uniform sign/margin over all six positive
orientations, preserving the amplitude of every scalar window and excluding
uncontrolled cancellation.

No local Lean executable was available in the packaging environment;
compilation is deliberately left to the repository's pinned Lean toolchain.
