# Finite H³ dissipation → terminal physical L² trace: registration

Base Git commit: `f82c08a6`. This patch bundles Steps 1 and 2, with an idempotent root and theorem-audit registrar. There is **no shell script inside this ZIP**.

The 8 new Lean theorem statements are registered under `PrimeTensor.Bridge.Euclidean`. Step 1 was locally compiled by the user; Step 2 is a proof candidate and must compile in the pinned Lean/mathlib environment. The formal result is conditional on `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, and `IntervalIntegrable (velocityH3DissipationAt u) volume a T`.

The registrar modifies only `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`, appending imports and audit checks. It is idempotent: `--apply` followed by `--check`; a second `--apply` leaves the files unchanged. Source index regeneration, full Lean builds and baseline auditing are required before committing or pushing.

This result cannot by itself establish full smooth continuation or global regularity. In particular finite full H³ dissipation is an explicit additional hypothesis.
