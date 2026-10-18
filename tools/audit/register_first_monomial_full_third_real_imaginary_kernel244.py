#!/usr/bin/env python3
"""Register the phase-free real full-third imaginary Fourier sign frontier."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealImaginaryKernel244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisRealGradientAxisComplexDensity_eq_phase_unphased244',
    'thirdFullAxisRealGradientTotalComplexDensity_eq_phase_unphased244',
    'thirdFullAxisRealThirdComplexDensity_eq_phase_unphased244',
    'thirdFullAxisRealGradientAxisUnphased_integrable244',
    'thirdFullAxisRealGradientTotalUnphased_integrable244',
    'thirdFullAxisRealThirdUnphasedKernel_integrable244',
    'thirdFullSeventhPhase_real_eq_imag244',
    'thirdFullAxisRealThirdSignedDensity_eq_imagKernel244',
    'thirdFullAxisRealThirdUnphasedImag_reflect244',
    'thirdFullAxisRealThirdUnphasedImag_zero_off_tube244',
    'thirdFullAxisRealThirdCommutator_eq_imagKernel_integral244',
    'thirdFullAxisRealThirdCommutator_eq_imagKernel_tube244',
    'thirdFullAxisRealThirdCommutator_neg_iff_imagKernel_integral_neg244',
)


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    body = SOURCE.read_text()
    for n in NAMES:
        if f'theorem {n}' not in body:
            raise SystemExit(f'Missing theorem: {n}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + n
        for cmd in (f'#check {qualified}', f'#print axioms {qualified}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered full-third phase-free imaginary Fourier sign frontier')


if __name__ == '__main__':
    main()
