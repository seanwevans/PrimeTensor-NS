#!/usr/bin/env python3
"""Register actual E2/E3-energy Cauchy bridge for the matched real Schwartz family."""
from pathlib import Path
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedEnergyCauchy244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = ('h3RealSchwartz_toLp_sub244', 'h3RealSchwartz_toLp_norm_sq_eq_integral244', 'h3RealSchwartz_differenceEnergy2_eq_Lp244', 'h3RealSchwartz_differenceEnergy3_eq_Lp244', 'finite_pi_L2_squareEnergy_cauchy244', 'exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy244', 'exists_h3WeightedPhysicalSchwartz_completedSignedFirstMonomial244')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing expected file: {p}')
    src = SOURCE.read_text()
    for name in DECLS:
        if 'theorem ' + name not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    audit = AUDIT.read_text().splitlines()
    header = list(dict.fromkeys([line for line in audit if line.startswith('import ')] + [imp]))
    body = [line for line in audit if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qname = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qname, '#print axioms ' + qname):
            if command not in body:
                body.append(command)
    out = '\n'.join(header + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != out:
        AUDIT.write_text(out)
    print('Registered matched actual E2/E3 Schwartz Cauchy and signed completion')

if __name__ == '__main__':
    main()
