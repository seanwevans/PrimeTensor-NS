#!/usr/bin/env python3
"""Register synchronized H³ matched real-Schwartz Sobolev jet closure."""
from pathlib import Path
import re

MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzMatchedSobolevJets244")
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
PATCH = Path('tools/audit/strengthen_first_monomial_matched_energy_decoder244.py')
BASE = Path('PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3SchwartzMatchedEnergyCauchy244.lean')
NAMES = (
  'exists_thirdFullSchwartz_matchedDecoderAndMixedGraph244',
  'exists_thirdFullSchwartz_matchedAll243StrongJetCauchy244',
  'exists_thirdFullSchwartz_allSecondJetsL4Cauchy244',
  'exists_thirdFullSchwartz_matchedFirstAndHigherJets244',
  'exists_thirdFullSchwartz_decoderMatchedCanonicalMonomial244',
)
STRENGTHENED = 'exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_withDecoder244'

def main():
    for p in (SOURCE, ROOT, AUDIT, PATCH, BASE):
        if not p.is_file():
            raise SystemExit(f'Missing {p}')
    src=SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b',src):
        raise SystemExit('Proof placeholder detected')
    found=set(re.findall(r'^theorem\s+(\w+)',src,re.M))
    if not set(NAMES) <= found or ('theorem '+STRENGTHENED) not in BASE.read_text():
        raise SystemExit('Missing synchronized declarations; run strengthening patch first')
    imp='import '+MODULE
    root=ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root+[imp])+'\n')
    old=AUDIT.read_text()
    lines=old.splitlines()
    imports=list(dict.fromkeys([l for l in lines if l.startswith('import ')]+[imp]))
    rest=[l for l in lines if not l.startswith('import ')]
    while rest and not rest[0].strip(): rest.pop(0)
    for name in (STRENGTHENED,)+NAMES:
        fq='PrimeTensor.FirstMonomialTriad.'+name
        for check in ('#check '+fq, '#print axioms '+fq):
            if check not in rest: rest.append(check)
    updated='\n'.join(imports+['']+rest).rstrip()+'\n'
    if updated!=old: AUDIT.write_text(updated)
    print(f'Registered strengthened E2/E3 decoder and {len(NAMES)} Sobolev jet theorems')

if __name__=='__main__': main()
