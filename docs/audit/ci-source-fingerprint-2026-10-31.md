# CI source-fingerprint stability repair

Base: `60857a11` (`master`). This patch is infrastructure-only: it changes no Lean declarations.

## Observed failure

GitHub Actions Lean CI for both `f82c08a6` and `60857a11` built Lean successfully on
x86_64 and ARM64. The subsequent `bash tools/audit/baseline.sh --reuse-build` failed at
its final source-identity comparison, reporting:

    Source inputs changed during the baseline run; rerun on a stable tree.

The baseline takes the initial file fingerprint using `git ls-files --cached --others
--exclude-standard`. The newly added refactor audit modules execute a Python helper import
(`from module_migration import main`), which writes `tools/refactor/__pycache__/` on a
fresh checkout. The original `.gitignore` did not exclude Python bytecode, so the second
fingerprint includes generated `.pyc` files even when source and HEAD never changed.

## Repair

1. Add Python bytecode ignores to `.gitignore` (`__pycache__/` and `*.py[cod]`).
2. Export `PYTHONDONTWRITEBYTECODE=1` at the start of `tools/audit/baseline.sh`, before
   the initial `inspect_source.py` inventory.
3. Run the idempotent registrar `tools/audit/repair_ci_source_fingerprint.py --apply`
   and `--check` to apply and verify both changes.

Both layers matter: disabling bytecode prevents audit side effects, while ignoring
existing bytecode prevents it from ever counting as source if created by an earlier
independent command. The fingerprint still detects changes to tracked project files
and normal nonignored untracked inputs.

## Validation

- Run `python3 -B tools/audit/repair_ci_source_fingerprint.py --check`.
- Run `bash tools/audit/baseline.sh --reuse-build` twice; the second run is the
  stability/regression check.
- Verify both GitHub Actions platforms and the rolling binary-release job after pushing.

Do not relax the source-identity comparison; it remains a meaningful guard.
