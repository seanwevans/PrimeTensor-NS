#!/usr/bin/env python3
"""Register actual physical selected-outer-carrier integrated compression."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierIntegratedCompression'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFullPhysical_selectedOuterMargin_rightWindow244', 'thirdFullPhysical_selectedOuterMargin_integratedWindow244', 'thirdFullPhysical_selectedOuterMargin_snapshotIntegratedSpike244', 'thirdFullPhysical_cofinalSelectedOuterMargins_integratedCompression244')
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in THEOREMS for item in
    ('#check ' + NAMESPACE + name, '#print axioms ' + NAMESPACE + name))


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
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    rootlean = ROOT / 'PrimeTensor.lean'
    auditlean = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, rootlean, auditlean):
        if not p.is_file():
            parser.error(f'missing {p}')
    clean = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '',
        source.read_text(encoding='utf-8'), flags=re.S))
    if re.search(r'\b(?:sorry|admit|axiom)\b', clean):
        parser.error('Lean source has a proof placeholder or introduced axiom')
    for name in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', clean))
        if count != 1:
            parser.error(f'missing or repeated theorem {name}: {count}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, required in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        all_lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if all_lines.count(line) != 1:
                parser.error(f'expected exactly one {line} in {path}')
    print(f'PASS: integrated selected outer carriers ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
