#!/usr/bin/env python3
"""Register cutoff-uniform actual cubic-weighted nonlinear Young stability."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularUniformYoungModulus'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_sharpAnnulus_norm_le_two244',
    'thirdFullKinetic_sharpAnnulus_sub244',
    'thirdFullKinetic_sharpAnnulus_sub_norm_le_two244',
    'thirdFullKinetic_cubicAnnulusApply_norm_le_uniform244',
    'thirdFullKinetic_cubicAnnulusApply_sub244',
    'thirdFullKinetic_cubicAnnulusApply_sub_norm_le_uniform244',
    'thirdFullPhysical_annularYoungResidual_uniformBandDifference244',
    'thirdFullKinetic_fourierNormSquare_difference_le244',
    'thirdFullPhysical_annularYoungResidual_uniformSquareDifference244',
    'thirdFullPhysical_actualAnnularYoung_uniformSquareTwoTime244',
)
DEFS = ('thirdFullKineticCubicAnnulusApply244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*THEOREMS, *DEFS)
               for line in ('#check ' + NS + name, '#print axioms ' + NS + name))


def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in wanted if entry not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(
            added + old if prepend else old.rstrip('\n') + '\n' + added,
            encoding='utf-8'
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    pt = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for f in (src, pt, audit):
        if not f.is_file():
            parser.error(f'missing path: {f}')
    source = src.read_text(encoding='utf-8')
    source = re.sub(r'/-.*?-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    if re.search(r'\b(?:sorry|admit|axiom)\b', source):
        parser.error('placeholder proof or new axiom detected')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing or duplicated theorem {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing or duplicated definition {name}')
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for f, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = f.read_text(encoding='utf-8').splitlines()
        for entry in wanted:
            if lines.count(entry) != 1:
                parser.error(f'missing or duplicated entry {entry} in {f}')
    print(f'PASS: cutoff-uniform Young modulus ({len(THEOREMS)} theorems; {len(DEFS)} definition)')


if __name__ == '__main__':
    main()
