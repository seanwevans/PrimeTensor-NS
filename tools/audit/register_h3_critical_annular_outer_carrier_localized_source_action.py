#!/usr/bin/env python3
"""Register highpass-localized physical source action and signed Young residual."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierLocalizedSourceAction'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFullPhysical_outerHighpassIncrement_eq_sourceAction244', 'thirdFullPhysical_outerHighpassSourceAction_le_globalAction244', 'thirdFullKinetic_highpassSquareDrift_fitted244', 'thirdFullPhysical_outerHighpassMassDrift_le_localizedSource244', 'thirdFullKinetic_earlyYoung_kineticSlope_initialHighpassCap244', 'thirdFullPhysical_outerDeficitDrop_localizedSourceYoungResidual244', 'thirdFullPhysical_outerNoYoungGrowth_forcesLocalizedSourcePayment244', 'thirdFullPhysical_outerNoYoungGrowth_forcesCubicHighpassSource244', 'thirdFullPhysical_selectedOuter_lowHalfTail_localizedYoungResidual244', 'thirdFullPhysical_outerHighpassSourceAction_le_terminalSourceTail244', 'thirdFullPhysical_cofinalOuter_movingHighpassSourceAction_zero244', 'thirdFullPhysical_cofinalOuter_localizedSourceYoungResidual244')
DEFINITIONS = ('thirdFullPhysicalOuterHighpassSourceAction244', 'thirdFullPhysicalOuterLocalizedSourceMassBudget244')
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in THEOREMS for item in
    ('#check ' + NAMESPACE + name, '#print axioms ' + NAMESPACE + name))
CHECKS += tuple('#check ' + NAMESPACE + name for name in DEFINITIONS)


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
    for path in (source, rootlean, auditlean):
        if not path.is_file():
            parser.error(f'missing {path}')
    clean = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '',
        source.read_text(encoding='utf-8'), flags=re.S))
    if re.search(r'\b(?:sorry|admit|axiom)\b', clean):
        parser.error('Lean source contains a proof placeholder or introduced axiom')
    for kind, names in (('theorem', THEOREMS), ('noncomputable def', DEFINITIONS)):
        for name in names:
            count = len(re.findall(r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b', clean))
            if count != 1:
                parser.error(f'missing or repeated {kind} {name}: {count}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, required in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line} in {path}')
    print(f'PASS: localized source action: {len(THEOREMS)} theorems, {len(DEFINITIONS)} definitions')


if __name__ == '__main__':
    main()
