#!/usr/bin/env python3
"""Register actual finite-radius annular deficit slope and common viscous windows."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDeficitUniformSlope'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_fourierBallVolume_mono_real244',
    'thirdFullPhysical_kineticSourceCeiling_mono_real244',
    'thirdFullPhysical_outerViscousCapBase_boundedReal244',
    'thirdFullPhysical_annularSnapshotYoungEnvelope_nonneg244',
    'thirdFullPhysical_actualYoungWidth_le_snapshotEnvelope244',
    'thirdFullPhysical_actualYoungWidth_nonneg244',
    'thirdFullKinetic_deficitSlope_bound_of_caps244',
    'thirdFullPhysical_annularDeficitSlopeCeiling_nonneg244',
    'thirdFullPhysical_actualAnnularDeficitSlope_uniform244',
    'thirdFullPhysical_actualAnnularDeficit_uniformFloorRightWindow244',
    'thirdFullPhysical_actualAnnularDeficit_uniformViscousRightWindow244',
    'thirdFullPhysical_actualAnnularDeficit_uniformIntegratedClock244',
)
DEFS = (
    'thirdFullPhysicalAnnularSnapshotYoungEnvelope244',
    'thirdFullPhysicalAnnularDeficitSlopeCeiling244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*THEOREMS, *DEFS)
               for line in ('#check ' + NS + name,
                            '#print axioms ' + NS + name))


def register(path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in wanted if entry not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(added + old if prepend else old.rstrip('\n') + '\n' + added,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--apply', action='store_true')
    choice.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    pt = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (src, pt, audit):
        if not file.is_file():
            parser.error(f'missing file: {file}')
    source = src.read_text(encoding='utf-8')
    source = re.sub(r'/-.*?-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    if re.search(r'\b(?:sorry|admit|axiom)\b', source):
        parser.error('admitted statement or new axiom detected')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/duplicate theorem: {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/duplicate definition: {name}')
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for file, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = file.read_text(encoding='utf-8').splitlines()
        for entry in wanted:
            if lines.count(entry) != 1:
                parser.error(f'missing/duplicate registration: {entry}')
    print(f'PASS: annular deficit uniform slope ({len(THEOREMS)} theorems, '
          f'{len(DEFS)} definitions)')


if __name__ == '__main__':
    main()
