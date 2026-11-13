#!/usr/bin/env python3
"""Register selected annular cofinal clocks and physical aperture obstructions."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalSelectedPairClocks'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFullKinetic_selectedExcess_apertureMargin_scalar244', 'thirdFullPhysical_selectedAnnularExcess_apertureMargin244', 'thirdFullKinetic_selectedExcess_boundedAspect_massFraction_scalar244', 'thirdFullPhysical_selectedExcess_boundedAspect_highpassFraction244', 'thirdFullPhysical_selectedBoundedAspect_noHighpassTightness244', 'thirdFullPhysical_cofinalSelectedAnnularSnapshots_disjointClocks244')
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name))


def register(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(added + old if prepend else old.rstrip('\n') + '\n' + added,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    rootlean = ROOT / 'PrimeTensor.lean'
    auditlean = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, rootlean, auditlean):
        if not p.is_file():
            parser.error(f'missing {p}')
    content = source.read_text(encoding='utf-8')
    sanitized = re.sub(r'/-.*?-/', '', content, flags=re.S)
    sanitized = re.sub(r'--[^\n]*', '', sanitized)
    if re.search(r'\b(?:sorry|admit|axiom)\b', sanitized):
        parser.error('unproved placeholder in Lean source')
    for name in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', sanitized))
        if count != 1:
            parser.error(f'theorem absent or duplicated: {name} ({count})')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for p, wanted in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        all_lines = p.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if all_lines.count(line) != 1:
                parser.error(f'expected exactly one {line} in {p}')
    print(f'PASS: selected annular cofinal clocks ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
