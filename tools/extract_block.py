#!/usr/bin/env python3
"""Base-relative block extraction for merging worktree pss_scratch.thy additions
into main. Usage:
  python3 extract_block.py <base_file> <wt_file>            # prints the appended block
  python3 extract_block.py <base_file> <wt_file> --check    # exit 0 if wt = base + appended block (before final 'end')
The invariant: agents append ONLY before the final 'end' line. So with
base_body = base minus its trailing 'end' (+ trailing blank lines) and likewise
wt_body, base_body must be an exact line-prefix of wt_body; the block is the
suffix. Any prefix mismatch => merge REFUSED (agent edited existing lines)."""
import sys

def body(path):
    lines = open(path, encoding='utf-8').read().splitlines()
    # strip trailing blank lines and the final 'end'
    while lines and lines[-1].strip() == '':
        lines.pop()
    if not lines or lines[-1].strip() != 'end':
        raise SystemExit(f"REFUSE: {path} does not end with 'end'")
    lines.pop()
    return lines

base = body(sys.argv[1])
wt = body(sys.argv[2])
if wt[:len(base)] != base:
    for i, (a, b) in enumerate(zip(base, wt)):
        if a != b:
            raise SystemExit(f"REFUSE: prefix mismatch at line {i+1}:\n  base: {a!r}\n  wt:   {b!r}")
    raise SystemExit(f"REFUSE: wt file shorter than base ({len(wt)} < {len(base)})")
block = wt[len(base):]
if '--check' in sys.argv:
    print(f"OK: clean append of {len(block)} lines")
    sys.exit(0)
sys.stdout.write('\n'.join(block) + ('\n' if block else ''))
