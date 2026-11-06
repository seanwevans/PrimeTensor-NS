# Proof repair: factor the bounded observation

Base HEAD: `9758179ab008683d8cdd01d5c2779a24a953ccef`.

The previous attempt failed with a deterministic `whnf` elaboration timeout in
`thirdFullPhysical_rawHighpass_transport_le_sourceL1244` and a type mismatch
between a private raw Fourier abbreviation from an imported module and the
local Fourier map definition. Increasing Lean's heartbeat budget did not fix
the underlying issue.

The repair changes the *interfaces of the first two transport lemmas* to
accept any actual continuous real-linear map `F` from physical L² into raw
Fourier L². This is mathematically stronger and avoids repeatedly elaborating
the full Plancherel implementation in their theorem types.

A separate highpass triangle lemma is proved solely in spectral L². The
actual Plancherel operator is instantiated **once**, in the physical annular
kinetic-mass theorem, and the last two terminal-cascade theorem statements
are unchanged. The original physical transport inequalities follow by
instantiating `F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap`.

Unlike the previous patch, the annular mass theorem keeps that same
canonical Fourier map constant on both sides, so there is no private
`RawPhysicalFourier244` versus local `PhysicalRawFourierWindow244` mismatch.
No new mathematical assumptions, axioms, or proof placeholders are introduced.

Lean/Lake are not installed in the packaging environment; full compilation
and the baseline audit remain the required local verification.

---

# Dynamic raw Fourier tightness across the full physical critical-eighth window

Baseline: `9758179ab008683d8cdd01d5c2779a24a953ccef`.

## Next hard mathematical interface

The newly proved vanishing absolute physical-source action does **not**
by itself give a bound on the weighted H³ transport or on the source peak.
The missing exact bridge is between real physical L² momentum increments,
the raw Fourier projection at a **moving** cutoff, and the exact raw mass
inside the minimal first-crossing annulus.

Let `X(t)` denote the genuine physical L² velocity and
`G(t)` its actual projected-momentum PDE source. Let `F` be the existing
bounded real-linear physical-to-raw-Fourier Plancherel map and `P⁺_n` the
sharp high-frequency projector. For strict positive times `t ≤ s`:

    ‖P⁺_n F X(s)‖
      ≤ ‖P⁺_n F X(t)‖ + ‖F‖ ∫_t^s ‖G(r)‖ dr.

This follows from the **actual physical Hilbert FTC** and the contraction
and additivity of the exact highpass projector. No unsupported claim that
the real-linear Fourier norm is exactly one is made; its operator norm
appears explicitly.

For every intermediate `s ∈ [t, σ]`, positivity of the norm integrand
allows the right integral to be replaced by the common full-window action
`∫_t^σ ‖G‖`. The previously proved exact annular-mass/highpass comparison
then gives the physical estimate

    μ_{n,Q}(s) ≤ 3 (‖P⁺_n F X(t)‖ + ‖F‖ ∫_t^σ ‖G‖)².

On the same **minimal first-crossing** critical-eighth windows `τ(vk)` to
`τ(vk)+δ(vk)`, physical terminal L² convergence implies the first term
vanishes when `v(k) → ∞`, and the preceding absolute source L¹ theorem
makes the second term vanish. Consequently, **uniformly for every time in
that physical window**:

    sup_{s∈[τ(vk), τ(vk)+δ(vk)]} μ_{vk,N(vk)+1}(s) → 0.

Lean formalizes the equivalent `∀ ε>0, ∀ᶠ k, ∀ s∈window, μ_k(s)<ε`
without introducing a supremum of a time-dependent integral.

## The remaining obstruction

The same exact minimal-attained window definition also provides a positive
lower bound on its **weighted H³ annular dissipation** at *every* time in
the interval. Hence the only way to maintain those high-weighted modes
alongside uniformly vanishing raw mass is genuine high-frequency
amplification. This is not a contradiction: the carrier ratio already
escapes, and the current proof does not establish a PDE estimate excluding
that amplification.

The next unresolved bridge must control the signed H³ transport by actual
physical source action plus frequency costs, or supply an independently
coercive bound on the weighted high-frequency energy budget.

## Verification

This is a source-only Lean package; the local toolchain must compile the new
file and the project. The registrar is idempotent and installs the root and
audit imports and `#check`/`#print axioms` entries. The run script also
regenerates the dependency index before builds and audits.

## Compilation proof repair (2026-11-06)

The source patch fixes two additive monotonicity applications without changing
any mathematical statements: the first estimate requires
`add_le_add_left` (coefficient inequality first, common term last), whereas
the second requires `add_le_add_right` (common highpass norm first).

The named physical Plancherel map is now a fully typed `private noncomputable
def` rather than an `abbrev`, avoiding eager unfolding of its nested Lp/CLM
implementation during theorem statement elaboration; the heartbeat budget is
also expanded for slow local mathlib normalization. No axioms or placeholders.

This is a candidate local Lean proof repair. It must pass `lake env lean`
and the repo build before commit.
