# Physical Schwartz Bochner weak FTC → actual initial L² vector

Base checkpoint: `aaae53ee`.

This patch resolves the issue that the preceding scalar increment theorem
tests against the prescribed `u(0)`, which may not be Schwartz. It uses
the **existing density of three-component physical Schwartz vectors** to
pass a Schwartz-tested Bochner momentum identity into the complete L²
Hilbert carrier. Pairing an integrable common Hilbert source `G` against
`u(0)` then gives one interval-integrable scalar source, whose increments
agree with the old physical velocity's correlation increments.

The patch proves five theorems and introduces one contract:

- `h3Audit_initialSchwartzBochner_extends_hilbertIncrement`
- `h3Audit_initialBochner_intervalInner_comm`
- `h3Audit_initialSchwartzBochner_allPhysicalScalarIncrements`
- `H3AuditInitialFrequentKineticSchwartzBochnerData`
- `h3Audit_initialSchwartzBochner_implies_oneDirectionData`
- `h3Audit_initialSchwartzBochner_physicalAndKineticRightTrace`

The trace is conditional on the same frequent kinetic anchors and one
self-pairing matching sequence. It additionally assumes an actual shared
physical `L¹_tL²_x` source and a Schwartz-tested **Bochner integral**
momentum identity. This is a *stronger source hypothesis* than arbitrary
testwise scalar L¹ sources, not a result of open-time H³ admissibility.
No unconditional global smoothness or terminal H³ extension is claimed.

Register the module and audits, regenerate `proof/order.txt` with
`python3 proof/generate_index.py` and its `--check`, validate
`proof/check_fragment.py --all`, then perform local Lean/Lake compilation.
