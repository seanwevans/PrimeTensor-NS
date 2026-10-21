#!/usr/bin/env python3
"""Idempotently register the two-channel H3 signed spectral obstruction."""
from pathlib import Path
import re

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSignedChannelAlternative244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = {
    'noncomputable def': ('h3PathWeightedThirdSplitBudget244',),
    'theorem': (
        'h3PathWeightedThirdSplitBudget_antitone244',
        'h3Path_weightedThirdSplit_adverse_witness244',
        'h3_twoChannel_cofinal_threshold_selection244',
        'h3Path_weightedThird_fixedCofinalChannel244',
        'h3Path_extension_of_bothWeightedHalfBudgets244',
    ),
}

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    # Do not register incomplete proof terms.
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean placeholder present')
    for keyword, names in DECLS.items():
        for name in names:
            pattern = r'^' + re.escape(keyword) + r'\s+' + re.escape(name) + r'\b'
            if not re.search(pattern, source, re.M):
                raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([ln for ln in lines if ln.startswith('import ')] + [imp]))
    rest = [ln for ln in lines if not ln.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for names in DECLS.values():
        for name in names:
            qualified = 'PrimeTensor.FirstMonomialTriad.' + name
            for cmd in ('#check ' + qualified, '#print axioms ' + qualified):
                if cmd not in rest:
                    rest.append(cmd)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != AUDIT.read_text():
        AUDIT.write_text(new)
    print('Registered signed H3 gradient/interpolation cofinal alternative')

if __name__ == '__main__':
    main()
