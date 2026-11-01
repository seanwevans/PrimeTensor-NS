#!/usr/bin/env python3
"""Unregister an uncommitted single-span experiment from the gap-spike build.

Only the exact legacy import and the eight matching #check/#print lines are
removed. Untracked experiment sources are moved to Downloads for safekeeping.
This does not change accepted Lean theorem declarations.
"""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
OLD_MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
    'TerminalActualSourceExcessSingleSpanGradientBudget'
)
OLD_THEOREMS = (
    'h3Critical_scalar_disjointGaps_sum_le_singleSpan',
    'h3Critical_scalar_cumulativeGapBudget_to_singleSpan',
    'h3Critical_scalar_singleSpanCost_forces_gradientEscape',
    'h3Critical_noL2Trace_cofinalQuintic_singleSpanGradientTransportBudget',
)
OLD_ENTRIES = {'import ' + OLD_MODULE}
for name in OLD_THEOREMS:
    OLD_ENTRIES.add('#check PrimeTensor.Bridge.Euclidean.' + name)
    OLD_ENTRIES.add('#print axioms PrimeTensor.Bridge.Euclidean.' + name)

ROOT_IMPORT = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
EXPERIMENTS = (
    'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Energy/'
    'TerminalActualSourceExcessSingleSpanGradientBudget.lean',
    'docs/research/h3-source-excess-single-span-gradient-budget.md',
    'tools/audit/register_h3_source_excess_single_span_gradient_budget.py',
)


def status(path):
    return [line.strip() for line in path.read_text(encoding='utf-8').splitlines()
            if line.strip() in OLD_ENTRIES]


def git_tracked(path):
    r = subprocess.run(
        ['git', '-C', str(ROOT), 'ls-files', '--error-unmatch', str(path)],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    return r.returncode == 0


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--apply', action='store_true')
    g.add_argument('--check', action='store_true')
    args = p.parse_args()
    for path in (ROOT_IMPORT, AUDIT):
        if not path.is_file():
            p.error('missing required file: ' + str(path))

    if args.check:
        for path in (ROOT_IMPORT, AUDIT):
            obsolete = status(path)
            if obsolete:
                p.error(f'{path.relative_to(ROOT)} retains {obsolete!r}')
        for rel in EXPERIMENTS:
            if (ROOT / rel).exists() and not git_tracked(rel):
                p.error('uncommitted experiment remains in source tree: ' + rel)
        print('PASS: no stale single-span registration or uncommitted source')
        return

    # Refuse to move an experiment if Git tracks it. At the expected HEAD,
    # these were never committed, but this makes the command safe to rerun.
    for rel in EXPERIMENTS:
        if (ROOT / rel).exists() and git_tracked(rel):
            p.error('experiment is Git-tracked; refusing to relocate: ' + rel)

    for path in (ROOT_IMPORT, AUDIT):
        original = path.read_text(encoding='utf-8')
        cleaned_lines = [line for line in original.splitlines(keepends=True)
                         if line.strip() not in OLD_ENTRIES]
        cleaned = ''.join(cleaned_lines)
        if cleaned != original:
            path.write_text(cleaned, encoding='utf-8')
            print('Removed obsolete registrations from', path.relative_to(ROOT))
        else:
            print('Already clean:', path.relative_to(ROOT))

    present = [rel for rel in EXPERIMENTS if (ROOT / rel).exists()]
    if present:
        backups = Path.home() / 'Downloads'
        backups.mkdir(parents=True, exist_ok=True)
        # A fresh directory avoids overwriting earlier backups.
        import tempfile
        destination = Path(tempfile.mkdtemp(prefix='primetensor-single-span-backup-', dir=backups))
        for rel in present:
            dest = destination / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(str(ROOT / rel), str(dest))
            print('Preserved', rel, 'at', dest)
    print('PASS: cleanup applied')


if __name__ == '__main__':
    main()
