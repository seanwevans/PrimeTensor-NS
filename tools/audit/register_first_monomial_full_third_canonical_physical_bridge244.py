#!/usr/bin/env python3
"""Register canonical H3 full-third transport and explicit physical gaps."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalPhysicalBridge244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = {
    'noncomputable def': (
        'weightedH3CanonicalFullThirdCommutator244',
        'h3MatchedGradientCompletion_toSignedCompletion244',
        'fullSchwartzThirdSpectralPairEnvelope244',
        'h3PhysicalSnapshotCanonicalFullThird244',
    ),
    'theorem': (
        'h3MatchedSchwartzGradientCompletion_fullThird_tendsto244',
        'h3MatchedSchwartzGradientCompletion_fullThird_unique244',
        'fullSchwartzThirdCommutator_spectralPair_modulus244',
        'exists_weightedH3Matched_fullThirdApproximation244',
        'exists_physicalSnapshot_matchedFullThirdAndFirstJet244',
        'physicalFullThird_minus_canonical_eq_gradient_and_signed_gaps244',
        'physicalFullThird_canonical_error_le_component_errors244',
    ),
}

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean placeholder present')
    for keyword, names in DECLS.items():
        for name in names:
            if not re.search(r'^' + re.escape(keyword) + r'\s+' + re.escape(name) + r'\b', source, re.M):
                raise SystemExit(f'Missing declaration {keyword} {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for names in DECLS.values():
        for name in names:
            qualified = 'PrimeTensor.FirstMonomialTriad.' + name
            for command in ('#check ' + qualified, '#print axioms ' + qualified):
                if command not in body:
                    body.append(command)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print('Registered canonical H3 full-third and physical trace gap proofs')

if __name__ == '__main__':
    main()
