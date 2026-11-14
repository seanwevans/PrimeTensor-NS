#!/usr/bin/env python3
"""Register genuine physical sharp highpass CLM and signed Leray alignment."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierSharpHighpassCLM'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFullPhysical_scalarSharpLow_add244', 'thirdFullPhysical_scalarSharpLow_smul244', 'thirdFullPhysical_sharpVectorLow_add244', 'thirdFullPhysical_sharpVectorLow_smul244', 'thirdFullPhysical_outerSharpHighpassCLM_apply244', 'thirdFullPhysical_outerSharpHighpassCLM_norm_le244', 'thirdFullPhysical_outerSharpHighpass_linearCertificate244', 'thirdFullPhysical_outerDiffusionCommutator_uniformActual244', 'thirdFullPhysical_outerFrozenFullQuadratic_uniformActual244', 'thirdFullKinetic_quadraticLeray_initialCarrierAlignment244', 'thirdFullPhysical_outerFrozenForcesInitialAlignment_uniformActual244')
DEFS = ("thirdFullPhysical_outerSharpHighpassLinear244", "thirdFullPhysical_outerSharpHighpassCLM244")
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in (*THEOREMS, *DEFS) for item in
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
            parser.error(f'missing or repeated theorem {name}: {count}')
    for name in DEFS:
        count = len(re.findall(r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b', clean))
        if count != 1:
            parser.error(f'missing or repeated definition {name}: {count}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, required in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line} in {path}')
    print(f'PASS: physical sharp highpass CLM: {len(THEOREMS)} theorems')

if __name__ == '__main__':
    main()
