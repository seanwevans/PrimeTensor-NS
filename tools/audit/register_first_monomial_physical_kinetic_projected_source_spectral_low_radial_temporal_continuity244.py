#!/usr/bin/env python3
"""Register genuine positive-time continuity of bounded-frequency H3 dissipation."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
          'SpectralLowRadialTemporalContinuity244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_lowRadialGradientMultiplier_mem_Icc244',
    'h3Path_lowRadialGradientMultiplier_measurable244',
    'h3Path_lowRadialGradientMultiplier_memLp244',
    'h3Path_lowRadialGradientMultiplierApply_ae244',
    'h3Path_lowRadialGradientMultiplierApply_norm_le244',
    'h3Path_lowRadialGradientMultiplierApply_add244',
    'h3Path_lowRadialGradientMultiplierApply_smul244',
    'h3Path_lowRadialGradientMultiplierCLM_apply244',
    'h3Path_lowRadialGradientMultiplier_norm_sq_eq_integral244',
    'h3Path_lowRadialGradientCoordinate_integrableOn244',
    'h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244',
    'h3Path_actualLowRadialDissipation_continuous244',
    'h3Path_actualLowRadialDissipation_continuousOn_positiveTime244',
    'h3Path_noL2Trace_forces_cubicIntegralWindows_of_totalContinuous244',
)
DEFINITIONS = (
    'h3PathLowRadialGradientMultiplier244',
    'h3PathLowRadialGradientMultiplierApply244',
    'h3PathLowRadialGradientMultiplierCLM244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    content = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', content, re.M):
        raise SystemExit('Unproven placeholder or axiom found')
    for name in THEOREMS:
        if not re.search(r'^\s*(?:noncomputable\s+)?(?:@\[simp\]\s*)?theorem\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    for name in DEFINITIONS:
        if not re.search(r'^\s*noncomputable\s+def\s+' + re.escape(name) + r'\b', content, re.M):
            raise SystemExit(f'Missing definition: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in (*DEFINITIONS, *THEOREMS):
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in rest:
                rest.append(command)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != old:
        AUDIT.write_text(updated)
    print(f'Registered {len(THEOREMS)} theorems, {len(DEFINITIONS)} definitions.')

if __name__ == '__main__':
    main()
