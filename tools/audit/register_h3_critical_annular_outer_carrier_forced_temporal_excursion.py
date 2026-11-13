#!/usr/bin/env python3
"""Register selected outer-carrier forced temporal excursions and physical state motion."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierForcedTemporalExcursion')
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_selectedOuterMargin_lowTail_forcesRightExcursion244',
    'thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesExcursion244',
    'thirdFullPhysical_selectedOuterMassDrop_forcesPhysicalL2Increment244',
    'thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesVelocityOrDeficit244',
    'thirdFullPhysical_selectedOuterDeficitDrop_massOrYoung244',
    'thirdFullPhysical_selectedOuterDeficitDrop_forcesStateMovement244',
    'thirdFullPhysical_cofinalSelectedOuterMargins_forceVelocityOrDeficit244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in
    ('#check ' + NAMESPACE + name, '#print axioms ' + NAMESPACE + name))


def register(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text((addition + old) if prepend else (old.rstrip('\n') + '\n' + addition),
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    rootlean = ROOT / 'PrimeTensor.lean'
    auditlean = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, rootlean, auditlean):
        if not path.is_file():
            parser.error(f'missing {path}')
    clean = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '',
        source.read_text(encoding='utf-8'), flags=re.S))
    if re.search(r'\b(?:sorry|admit|axiom)\b', clean):
        parser.error('Lean source contains a proof placeholder or introduced axiom')
    for name in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', clean))
        if count != 1:
            parser.error(f'missing or duplicated theorem {name}: {count}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, required in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one line: {line} in {path}')
    print(f'PASS: forced selected outer-carrier excursions ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
