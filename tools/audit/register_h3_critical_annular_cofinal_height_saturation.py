#!/usr/bin/env python3
"""Register the physical annular saturation ceiling and diagonal-excess no-go."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalHeightSaturation'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFull_scalar_affineCapHeight_saturation244', 'thirdFullPhysical_annularClockSaturationCeiling_pos244', 'thirdFullPhysical_annularClockHeight_le_saturation244', 'thirdFullPhysical_annularClockHeight_le_fixedInnerSaturation244', 'thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244', 'thirdFullPhysical_cofinalClockHeight_autoSubcritical244', 'thirdFullPhysical_cofinalClockHeight_noCriticalFloor244', 'thirdFullPhysical_strictAnnularExcess_forces_radialSeparation244', 'thirdFullPhysical_strictAnnularExcess_noDiagonal244', 'thirdFullPhysical_boundedAnnularUniformExcess_impossible244', 'thirdFullPhysical_cofinalSelectedExcess_autoSubcritical244')
DEFS = ('thirdFullPhysicalAnnularClockSaturationCeiling244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS) for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name))


def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
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
        parser.error('placeholder or unproved axiom found in Lean source')
    for ty, names in (('theorem', THEOREMS), ('noncomputable def', DEFS)):
        for name in names:
            count = len(re.findall(r'(?m)^' + ty + r'\s+' + re.escape(name) + r'\b', sanitized))
            if count != 1:
                parser.error(f'{ty} missing/duplicated: {name}: {count}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for p, expected in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = p.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line} in {p}')
    print(f'PASS: annular saturation and no-go ({len(THEOREMS)} theorems, {len(DEFS)} defs)')


if __name__ == '__main__':
    main()
