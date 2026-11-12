#!/usr/bin/env python3
"""Register finite-radius cofinal annular clock extraction and summability."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalUniformClockExtraction'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_cofinalAnnularUniformSnapshots_disjointSummable244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(s for name in THEOREMS
               for s in ('#check ' + NS + name, '#print axioms ' + NS + name))


def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [x for x in wanted if x not in existing]
    if missing:
        inserted = '\n'.join(missing) + '\n'
        path.write_text(inserted + old if prepend else old.rstrip('\n') + '\n' + inserted,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (source, root, audit):
        if not file.is_file():
            parser.error(f'missing {file}')
    lean = source.read_text(encoding='utf-8')
    code = re.sub(r'/-.*?-/', '', lean, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    if re.search(r'\b(?:sorry|admit|axiom)\b', code):
        parser.error('prohibited proof placeholder or axiom')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error(f'missing/duplicate theorem: {name}')
    if args.apply:
        register(root, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for file, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = file.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate: {line} in {file}')
    print(f'PASS: annular cofinal clock extraction ({len(THEOREMS)} theorem)')


if __name__ == '__main__':
    main()
