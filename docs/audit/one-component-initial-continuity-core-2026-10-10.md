# Initial physical continuity dependency audit (after `9454c647`)

The signed NS transport initial trace contract `H3AuditInitialPhysicalSignedTransportCoreData`
assumes closed-initial-interval continuity for both the physical zeroth-order
`L²` velocity jet and the canonical `H³` energy. These facts already imply the
initial `L²` right trace and a one-sided `H³` energy ceiling. No temporal
velocity derivative, Bochner FTC, interval-integrable formal energy derivative,
or signed transport bound is needed to *deduce that initial strong H³ trace*.

This module:

1. Proves right convergence at zero from `ContinuousOn F (Icc 0 b)` in a
   pseudometric space, including the actual physical velocity `L²` space.
2. Extracts the initial physical `L²` right trace and H³ energy upper ceiling
   from those continuities.
3. Reuses the proved raw-Fourier to weak-H³ plus Hilbert-polarization result
   to obtain the actual initial strong H³ spectral trace.
4. Shows the former signed-transport core entails the smaller continuity
   criterion, independently of its derivative and transport fields.
5. Propagates the reduced criterion to the conditional full-time transverse
   `L²_t dot H^(3/2)_x` statement without altering its separate terminal
   strong-vorticity endpoint premise.

**What is not proved:** neither continuity at `t=0` nor a genuine
initial-value NS/mild-solution condition supplying it follows from the
project's open-time `LoggedPreterminalH3PathAdmissible` predicate. The proof
is a rigorous dependency reduction and makes the remaining initial endpoint
requirements explicit, not an unconditional regularity theorem.

Audit the theorem hypotheses and axioms with the appended `#check` and
`#print axioms` commands in `tools/audit/Contracts.lean`.
