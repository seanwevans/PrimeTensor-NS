#!/usr/bin/env python3
"""Idempotently register fixed-channel terminal physical-source obstruction."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedPhysicalSourceChannel'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
IMPORT = 'import ' + MODULE
NAMES = (
    'h3Critical_physicalSource_integrable_mono_terminal_tail',
    'h3Critical_noL2Trace_fixed_physicalSource_nonintegrable',
    'h3Critical_physicalSource_terms_continuousOn_positiveTime',
    'h3Critical_continuous_physicalSource_integrable_of_terminal_ceiling',
    'h3Critical_continuous_physicalSource_nonintegrable_forces_spikes',
    'h3Critical_noL2Trace_fixed_physicalSource_nonintegrable_and_spikes',
)
CHECKS = tuple(line for name in NAMES for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path: Path, needed: tuple[str, ...], *, first=False) -> None:
    contents = path.read_text()
    existing = set(contents.splitlines())
    missing = [line for line in needed if line not in existing]
    if missing:
        insert = '\n'.join(missing) + '\n'
        path.write_text(insert + contents if first else contents.rstrip('\n') + '\n' + insert)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (SOURCE, root, audit):
        if not p.is_file():
            parser.error('Missing ' + str(p.relative_to(ROOT)))
    if args.apply:
        append_missing(root, (IMPORT,))
        append_missing(audit, (IMPORT,), first=True)
        append_missing(audit, CHECKS)
    for p, lines in ((root, (IMPORT,)), (audit, (IMPORT,) + CHECKS)):
        found = p.read_text().splitlines()
        for line in lines:
            if found.count(line) != 1:
                parser.error(f'Expected exactly one {line!r} in {p.relative_to(ROOT)}')
    content = SOURCE.read_text()
    for name in NAMES:
        if content.count('theorem ' + name + '\n') != 1:
            parser.error(f'Missing/duplicate theorem: {name}')
    for placeholder in ('sorry', 'admit', 'unsafe axiom'):
        if placeholder in content:
            parser.error(f'Placeholder marker {placeholder!r} in source')
    print(f'PASS: {len(NAMES)} theorems registered with #check and #print axioms')


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    main()
