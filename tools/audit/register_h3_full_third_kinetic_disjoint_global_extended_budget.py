#!/usr/bin/env python3
"""Register actual global extended-cost packing for disjoint kinetic H3 windows."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticDisjointGlobalExtendedBudget'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFull_scalar_disjointWindows_le_globalExtendedBudget244',
    'thirdFull_scalar_disjointWindows_divergence_forces_infinite244',
    'thirdFullPhysical_noH3Trace_kineticDisjointGlobalExtendedBudget244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(s for name in THEOREMS for s in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    original = path.read_text(encoding='utf-8')
    present = set(original.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(
            block + original if prepend else original.rstrip('\n') + '\n' + block,
            encoding='utf-8',
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error('missing ' + str(path))
    data = source.read_text(encoding='utf-8')
    for theorem in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(theorem) + r'\b', data)) != 1:
            parser.error('missing or repeated theorem ' + theorem)
    sans_comments = re.sub(r'/-.*?-/', '', data, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', sans_comments):
        parser.error('unproved placeholder / unsafe axiom')
    if any(line.rstrip() != line for line in data.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        ensure_once(root, (IMPORT,))
        ensure_once(audit, (IMPORT,), prepend=True)
        ensure_once(audit, CHECKS)
    for path, required in ((root, (IMPORT,)), (audit, (IMPORT,) + CHECKS)):
        existing = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if existing.count(line) != 1:
                parser.error('expected exactly one ' + repr(line) + ' in ' + str(path))
    print(f'PASS: kinetic disjoint global extended budget; '
          f'{len(THEOREMS)} theorem and {len(CHECKS)} audit entries')


if __name__ == '__main__':
    main()
