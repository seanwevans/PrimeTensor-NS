#!/usr/bin/env python3
"""Register selected-annular wide-aperture actual kinetic-band evacuation."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularWideApertureBandEvacuation'
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullPhysicalActualSharpAnnularRawMass244',)
THEOREMS = (
    'thirdFullPhysical_actualAnnularYoungWidth_controls_rawBand244',
    'thirdFullKinetic_positiveDeficit_forcesWidthBudget244',
    'thirdFullKinetic_wideAperture_bandWidth_scalar244',
    'thirdFullPhysical_wideAnnularPositiveDeficit_forces_rawBandEvacuation244',
    'thirdFullKinetic_wideAnnularBand_normalizedAspect244',
    'thirdFullPhysical_cofinalSelectedWideAnnularDeficit_bandEvacuation244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS)
               for line in ('#check ' + NS + name, '#print axioms ' + NS + name))


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
    src = source.read_text(encoding='utf-8')
    sanitized = re.sub(r'/-.*?-/', '', src, flags=re.S)
    sanitized = re.sub(r'--[^\n]*', '', sanitized)
    if re.search(r'\b(?:sorry|admit|axiom)\b', sanitized):
        parser.error('unproved placeholder in Lean source')
    for keyword, names in (('theorem', THEOREMS), ('noncomputable def', DEFS)):
        for name in names:
            matches = re.findall(r'(?m)^'+keyword+r'\s+'+re.escape(name)+r'\b', sanitized)
            if len(matches) != 1:
                parser.error(f'{keyword} {name} absent or duplicated: {len(matches)}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, wanted in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for item in wanted:
            if lines.count(item) != 1:
                parser.error(f'expected one {item} in {path}')
    print(f'PASS: selected wide-aperture band evacuation ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
