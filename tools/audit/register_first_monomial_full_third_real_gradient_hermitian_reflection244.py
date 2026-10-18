#!/usr/bin/env python3
"""Idempotently register the real full-third gradient Hermitian reflection proof."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGradientHermitianReflection244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('thirdFullAxisRealSpectrum_reflect244', 'thirdFullMiddleFrequency_pair_reflect244', 'thirdFullGradientSevenWeight_star244', 'thirdFullGradientSevenWeight_reflect244', 'thirdFullAxisRealGradientSlot_reflect244', 'thirdFullSeventhPhase_oddConj_re244', 'thirdFullAxisRealGradientSlot_signed_reflect244')


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qname = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in (f'#check {qname}', f'#print axioms {qname}'):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered full-third actual Hermitian reflection and signed phase proofs')


if __name__ == '__main__':
    main()
