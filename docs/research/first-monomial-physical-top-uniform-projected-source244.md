# Actual projected source on strict H³ windows

Base commit: `6d83f4e4`.

The actual projected momentum source has the exact physical Hilbert realization

\[
R(t)=\Delta u(t)-\mathbb P\nabla\cdot(u(t)\otimes u(t)).
\]

The repository already establishes continuity of the canonical physical L²
source on arbitrary strictly preterminal closed intervals. This patch extracts
its unconditional local uniform L² bound, uniform Hilbert weak-test pairing
bounds, and Bochner interval integrability,
then transfers the bound to the sliding canonical restart windows constructed
from the H³ path.

These are **not** spatial pointwise L∞ bounds of Δu or pressure, nor do they
justify differentiation of `∫φ u` on their own. The continuous source admits
a Bochner primitive; the distinction between this primitive and the genuine
physical velocity is recorded as an explicit Hilbert FTC defect:

\[
D(a,b)=V(b)-V(a)-\int_a^bR(r)\,dr.
\]

The necessary remaining step is `D(a,b)=0`, i.e. the weak/strong evolution
identity. A compact support L² source estimate is not a substitute for that
identification. Future work should use the PDE in the weak-distribution sense
to prove this identity, keeping pressure cancellation against solenoidal tests.
