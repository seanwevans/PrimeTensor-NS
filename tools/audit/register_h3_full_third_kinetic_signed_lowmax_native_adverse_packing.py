#!/usr/bin/env python3
"""Register the native adverse signed-sixth-flux physical annulus selection and packing theorem."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxNativeAdversePacking'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
DEFS = (
    'ThirdFullKineticSignedLowMaxNativeAdverseGap244',
    'ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244',
)
THEOREMS = (
    'thirdFullPhysical_kineticGaps_signedLowMax_nativeAdverseCertifiedOccupancy244',
)
IMPORT = 'import ' + MODULE
AUDIT_LINES = tuple(line for name in (*DEFS, *THEOREMS)
                    for line in ('#check ' + NAMESPACE + name,
                                 '#print axioms ' + NAMESPACE + name))


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    lines = set(old.splitlines())
    missing = [line for line in wanted if line not in lines]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (source, root_file, audit):
        if not file.is_file():
            parser.error(f'missing file: {file}')
    code = source.read_text(encoding='utf-8')
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' +
                          re.escape(name) + r'\b', code)) != 1:
            parser.error(f'missing/duplicate definition: {name}')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error(f'missing/duplicate theorem: {name}')
    clean = re.sub(r'/-.*?-/', '', code, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    if re.search(r'\b(?:sorry|admit|axiom)\b', clean):
        parser.error('unproved placeholder or axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        add_missing(root_file, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, AUDIT_LINES)
    for file, wanted in ((root_file, (IMPORT,)),
                         (audit, (IMPORT, *AUDIT_LINES))):
        lines = file.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate registration: {file}: {line}')
    print(f'PASS: native adverse certified selection and packing; '
          f'{len(DEFS)} definitions, {len(THEOREMS)} theorem')


if __name__ == '__main__':
    main()
