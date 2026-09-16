from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text()

dup = """      rw [← integral_sub hLapInt hForceInt]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_sub]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_sub]"""

single = """      rw [← integral_sub hLapInt hForceInt]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_sub]"""

count = text.count(dup)
if count == 1:
    text = text.replace(dup, single, 1)
elif count == 0:
    # Fall back to removing one duplicated tail immediately after the fixed block.
    marker = single + "\n"
    idx = text.find(marker)
    if idx < 0:
        raise SystemExit("could not find fix1 block")
    rest = text[idx + len(marker):]
    tail = """      apply integral_congr_ae
      filter_upwards with x
      rw [map_sub]"""
    if not rest.startswith(tail):
        raise SystemExit("fix1 block found, but duplicated tail did not match expected tactics")
    text = text[:idx + len(single)] + text[idx + len(marker) + len(tail):]
else:
    raise SystemExit(f"expected one duplicated block, found {count}")

path.write_text(text)
