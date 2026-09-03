#!/usr/bin/env python3
"""Verify that every Lean snippet in a fragment is quoted verbatim.

A fragment under proof/ renders exactly one module under PrimeTensor/.  Each
of its lstlisting blocks is meant to be an excerpt of that module's source,
copied character for character, so that a reader can trust the quoted code
without diffing it against the repository by hand.

This checks that.  For proof/<M>.tex it reads PrimeTensor/<M>.lean and
requires each block to occur in it verbatim, ignoring only leading and
trailing blank lines and a uniform indent.

A block that is deliberately not a quote -- a signature written in isolation,
say -- opts out with a LaTeX comment on the line before it:

    % listing:paraphrase

Usage:  check_listings.py <module> [<module> ...]      (paths relative to proof/)
        check_listings.py --all
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
BLOCK = re.compile(
    r'(?P<opt>[^\n]*)\n\s*\\begin\{lstlisting\}(?:\[[^\]]*\])?\n'
    r'(?P<body>.*?)\\end\{lstlisting\}',
    re.DOTALL)


def dedent(text):
    lines = [ln for ln in text.split('\n')]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if not lines:
        return ''
    pad = min((len(ln) - len(ln.lstrip()) for ln in lines if ln.strip()),
              default=0)
    return '\n'.join(ln[pad:] if ln.strip() else '' for ln in lines)


def check(module):
    tex = os.path.join(HERE, module + '.tex')
    lean = os.path.join(REPO, 'PrimeTensor', module + '.lean')
    if not os.path.isfile(tex):
        return [f'{module}: no fragment at proof/{module}.tex']
    if not os.path.isfile(lean):
        return [f'{module}: no source at PrimeTensor/{module}.lean']

    with open(tex, encoding='utf-8') as fh:
        fragment = fh.read()
    with open(lean, encoding='utf-8') as fh:
        source = dedent(fh.read())

    problems, checked = [], 0
    for m in BLOCK.finditer(fragment):
        if 'listing:paraphrase' in m.group('opt'):
            continue
        checked += 1
        body = dedent(m.group('body'))
        if body and body in source:
            continue
        line = fragment[:m.start('body')].count('\n') + 1
        head = body.split('\n')[0] if body else '(empty)'
        problems.append(
            f'{module}.tex:{line}: block is not verbatim in '
            f'PrimeTensor/{module}.lean\n    first line: {head!r}')
    if not problems:
        print(f'  {module}: {checked} listing(s) verbatim')
    return problems


def main(argv):
    if argv[:1] == ['--all']:
        modules = []
        for root, _, files in os.walk(HERE):
            for f in sorted(files):
                if f.endswith('.tex') and f not in (
                        'main.tex', 'preamble.tex', 'standalone.tex',
                        'modules.tex'):
                    modules.append(
                        os.path.relpath(os.path.join(root, f), HERE)[:-4])
        modules.sort()
    else:
        modules = [m[:-4] if m.endswith('.tex') else m for m in argv]
    if not modules:
        print('usage: check_listings.py <module> ... | --all', file=sys.stderr)
        return 2

    problems = []
    for module in modules:
        problems += check(module)
    for p in problems:
        print('check_listings: ' + p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
