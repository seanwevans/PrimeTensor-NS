# Canonical initial uniqueness from vanishing relative-energy defects

Base: `66bd1dad` (`weaken initial uniqueness to scalar relative energy continuity`).

## New reduction

Instead of demanding a perfectly exact PDE relative-energy inequality at the
outset, supply a sequence of approximate inequalities with a **single common**
comparison coefficient `K`:

    e(t) = ‖D(t)‖²
    e(t) ≤ K ∫₀ᵗ e(s) ds + δ(n),      for all n, all t in [0,b]
    δ(n) → 0.

The lemma `h3Audit_initialRelativeEnergy_exact_of_vanishingDefects` chooses a
sufficiently large approximation index for each epsilon and passes to the
order limit `ε ↓ 0`, proving the exact inequality. This passage does not
assume scalar continuity, Hilbert continuity, or energy integrability; those
are separate prerequisites only for the subsequent Gronwall step.

The new `H3AuditInitialCanonicalVanishingDefectRelativeEnergyData` contract
retains the noncircular initial scalar-energy continuity obligation and
provides the residual family. It is equivalent to the previous exact-scalar
contract at the level of abstract analysis (zero defects give the converse),
but better matches PDE proofs that first construct approximations.

From it the patch derives:
- the previous exact scalar relative-energy data;
- compact physical weak-test comparison and canonical initial H³ overlap;
- the physical initial L² right trace and H³ energy upper limit;
- the two conditional full-time transverse homogeneous 3/2-Sobolev estimates.

## Remaining genuine PDE obligations

1. Prove the uniform approximate relative-energy estimate and construct its
   vanishing error sequence from the actual old/selected Navier–Stokes PDE,
   including pressure/commutator error control.
2. Obtain scalar relative-energy continuity at the initial endpoint without
   assuming the sought canonical old/selected overlap.
3. Keep the independent physical terminal-vorticity strong-H³ endpoint
   hypothesis explicit.

No `sorry`, `admit`, or new axioms in this patch. Lean verification must be
performed in the pinned project environment; the patch has not been compiled
locally by the authoring environment.
