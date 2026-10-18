#!/usr/bin/env python3
"""Idempotently register full-third coherent-sector Hermitian-phase lemmas."""
from pathlib import Path

MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdCoherentHermitianPhase244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPhysicalSix_swap_first_coherent244',
    'thirdFullPhysicalSix_swap_last_coherent244',
    'thirdFullMiddleFrequency_swap_first_coherent244',
    'thirdFullMiddleFrequency_swap_last_coherent244',
    'thirdFullProjectedHermitianKernel_swap_first_coherent244',
    'thirdFullProjectedHermitianKernel_swap_last_coherent244',
    'thirdFullLabelledWindowedProjectedKernel_coherent244',
    'thirdFullLabelledWindowedProjectedKernel_noncoherent_zero244',
    'thirdFullLabelledWindowedProjectedKernel_swap_first244',
    'thirdFullLabelledWindowedProjectedKernel_swap_last244',
    'thirdFullAxisDot_neg_neg_coherent244',
    'thirdFullAxisDot_neg_left_coherent244',
    'thirdFullTransversePolynomial_reflect_coherent244',
    'thirdFullFixedCenterTransverseGerm_reflect_coherent244',
    'thirdFullMiddleFrequency_reflect_coherent244',
    'thirdFullPhysicalHermitianOrbit_reflect_conj_coherent244',
    'thirdFullMovingHermitianOrbit_coherent244',
    'thirdFullMovingHermitianOrbit_I_coherent244',
    'thirdFullMovingHermitianOrbit_phase_coherent244',
    'thirdFullMovingHermitianOrbit_reflect_conj_coherent244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for name in NAMES:
        if not any(f'{kw} {name}' in source for kw in ('theorem', 'noncomputable def', 'def')):
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    audit = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in audit if line.startswith('import ')] + [imp]))
    body = [line for line in audit if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in (f'#check {qualified}', f'#print axioms {qualified}'):
            if command not in body:
                body.append(command)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != AUDIT.read_text():
        AUDIT.write_text(result)
    print('Registered coherent-sector permutation, phase, and reflection identities')

if __name__ == '__main__':
    main()
