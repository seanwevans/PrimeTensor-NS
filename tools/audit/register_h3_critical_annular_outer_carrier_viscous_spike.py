#!/usr/bin/env python3
"""Register selected annular outer-carrier H3 viscous payment in PrimeTensor."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierViscousSpike')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_rawSharpHighpass_sixthMoment_le_weighted244',
    'thirdFullKinetic_weightedSharpVectorHighpass_exact244',
    'thirdFullPhysical_actualSharpHighMass_sixthMoment_le_weighted244',
    'thirdFullPhysical_actualSharpHighMass_eighthViscousCharge244',
    'thirdFullKinetic_wideOuterMargin_sixthViscous_scalar244',
    'thirdFullPhysical_selectedWideOuterMargin_forces_viscousSpike244',
    'thirdFullPhysical_selectedWideOuterMargin_viscousCapRadius244',
    'thirdFullPhysical_selectedWideOuterMargins_force_viscousSpikes244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in
               ('#check ' + NS + name, '#print axioms ' + NS + name))


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
    prime = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, prime, audit):
        if not path.is_file():
            parser.error(f'missing {path}')
    content = source.read_text(encoding='utf-8')
    sanitized = re.sub(r'/-.*?-/', '', content, flags=re.S)
    sanitized = re.sub(r'--[^\n]*', '', sanitized)
    if re.search(r'\b(?:sorry|admit|axiom)\b', sanitized):
        parser.error('unproved placeholder in Lean source')
    for name in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', sanitized))
        if count != 1:
            parser.error(f'theorem missing or duplicated: {name} ({count})')
    if args.apply:
        register(prime, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, wanted in ((prime, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        actual = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if actual.count(line) != 1:
                parser.error(f'expected exactly one {line} in {path}')
    print(f'PASS: selected annular viscous spikes ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
