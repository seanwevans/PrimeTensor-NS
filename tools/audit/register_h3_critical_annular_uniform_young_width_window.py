#!/usr/bin/env python3
"""Register a common actual-time window for all bounded annular Young-width costs."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularUniformYoungWidthWindow'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_annularFullYoungWidthModulus_continuous_left244',
    'thirdFullPhysical_actualYoungWidth_uniformAt244',
    'thirdFullPhysical_actualYoungWidth_uniformRightWindow244',
    'thirdFullPhysical_actualYoungWidth_uniformUpperMarginWindow244',
    'thirdFullPhysical_sharpHighpassSquare_uniformVariation244',
    'thirdFullPhysical_actualSharpHighMass_uniformTwoTime244',
    'thirdFullPhysical_actualSharpHighMass_uniformAt244',
    'thirdFullPhysical_actualAnnularCosts_jointRightWindow244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS
               for line in ('#check ' + NS + name,
                            '#print axioms ' + NS + name))


def register(path: Path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    found = set(old.splitlines())
    missing = [entry for entry in entries if entry not in found]
    if missing:
        extra = '\n'.join(missing) + '\n'
        path.write_text(
            extra + old if prepend else old.rstrip('\n') + '\n' + extra,
            encoding='utf-8'
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--apply', action='store_true')
    choice.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    main_file = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for f in (src, main_file, audit):
        if not f.is_file():
            parser.error(f'missing path: {f}')
    source = src.read_text(encoding='utf-8')
    source = re.sub(r'/-.*?-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    if re.search(r'\b(?:sorry|admit|axiom)\b', source):
        parser.error('placeholder or new axiom detected')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/duplicate theorem: {name}')
    if args.apply:
        register(main_file, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for f, required in ((main_file, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = f.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if lines.count(entry) != 1:
                parser.error(f'missing/duplicate registration: {entry} in {f}')
    print(f'PASS: common bounded annular Young-width window ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
