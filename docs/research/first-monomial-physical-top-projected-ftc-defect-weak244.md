# Physical projected FTC defect: Leray-fixedness and weak determination

Baseline: `fd65c7e4` (`master`).

The previous increment constructed the actual physical Hilbert evolution defect

\[D(a,b)=U(b)-U(a)-\int_a^b R(s)\,ds\]

and independently proved compact-strict-time `L²` continuity of `R`.
The present increment proves the new **unconditional subspace property**

\[D(a,b)\in\operatorname{Ran}\mathbb P,\qquad 0<a<b<T.\]

The physical velocity snapshots are Leray-fixed; the actual projected source
is Leray-fixed at all times; the defining closed linear subspace is preserved
by Bochner integration. A physical Hilbert defect thus vanishes iff all
compact divergence-free weak-test pairings against it vanish. Conversely,
every nonzero defect has a specific detecting compact solenoidal test.

On a positive compact interval `[a,b]`, the statement that all prefix defects
`D(a,r)` vanish is equivalent to the preexisting absolute-time solenoidal weak
FTC predicate: for all compact solenoidal test fields `φ` and all `r∈[a,b]`,

\[\langle\phi,U(r)-U(a)\rangle=\int_a^r\langle\phi,R(s)\rangle\,ds.\]

The proof uses source continuity to commute the Bochner integral through a
Hilbert weak test and uses the preexisting weak-determination theorem in the
converse direction. The canonical short-restart scalar weak FTC implies
vanishing of the actual Hilbert defect on every prefix, by an already-proved
canonical-to-physical weak-test identification.

**Frontier:** None of these equivalences proves the solenoidal weak FTC from
H³ admissibility alone. Deriving scalar weak-test evolution from the actual
preterminal PDE without assuming joint spacetime time-derivative continuity
or a pointwise domination hypothesis remains the analytic gap. This is not an
unconditional Navier–Stokes regularity or continuation theorem.
