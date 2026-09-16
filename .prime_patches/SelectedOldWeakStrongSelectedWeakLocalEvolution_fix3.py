from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
text = path.read_text()

pat = re.compile(
    r'''(?mx)
    ^(?P<i>[ \t]*)rw[ \t]+\[←[ \t]*(?:MeasureTheory\.)?integral_sub[ \t]+hLapInt[ \t]+hForceInt\][ \t]*\n
    (?P=i)apply[ \t]+integral_congr_ae[ \t]*\n
    (?P=i)filter_upwards[ \t]+with[ \t]+x[ \t]*\n
    (?P=i)rw[ \t]+\[map_sub\][ \t]*\n
    (?:
      ^[ \t]*\n
    )*
    (?P=i)apply[ \t]+integral_congr_ae[ \t]*\n
    (?P=i)filter_upwards[ \t]+with[ \t]+x[ \t]*\n
    (?P=i)rw[ \t]+\[map_sub\][ \t]*
    '''
)

m = pat.search(text)
if m:
    i = m.group("i")
    replacement = (
        f"{i}rw [← integral_sub hLapInt hForceInt]\n"
        f"{i}apply integral_congr_ae\n"
        f"{i}filter_upwards with x\n"
        f"{i}rw [map_sub]"
    )
    text = text[:m.start()] + replacement + text[m.end():]
    path.write_text(text)
    raise SystemExit(0)

lines = text.splitlines(keepends=True)

rewrite_idx = None
rewrite_re = re.compile(
    r'^(?P<i>[ \t]*)rw[ \t]+\[←[ \t]*(?:MeasureTheory\.)?integral_sub[ \t]+hLapInt[ \t]+hForceInt\][ \t]*\r?\n?$'
)

for idx, line in enumerate(lines):
    if rewrite_re.match(line):
        if rewrite_idx is not None:
            raise SystemExit("found more than one fixed integral_sub rewrite; refusing ambiguous edit")
        rewrite_idx = idx

if rewrite_idx is None:
    raise SystemExit("could not locate the fix1 integral_sub rewrite")

wanted = [
    "apply integral_congr_ae",
    "filter_upwards with x",
    "rw [map_sub]",
    "apply integral_congr_ae",
    "filter_upwards with x",
    "rw [map_sub]",
]

nonblank = []
for idx in range(rewrite_idx + 1, min(len(lines), rewrite_idx + 16)):
    stripped = lines[idx].strip()
    if stripped:
        nonblank.append((idx, stripped))
    if len(nonblank) == 6:
        break

got = [s for _, s in nonblank]
if got != wanted:
    raise SystemExit(
        "located fix1 rewrite, but following tactics were not the expected duplicated tail:\n"
        + "\n".join(f"  {idx+1}: {s}" for idx, s in nonblank)
    )

second_start = nonblank[3][0]
second_end = nonblank[5][0]
del lines[second_start:second_end + 1]

path.write_text("".join(lines))
