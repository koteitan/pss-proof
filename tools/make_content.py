#!/usr/bin/env python3
"""Regenerate tmp/content.md (the extracted article text) from tmp/original.html.

CONTEXT
-------
`tmp/content.md` is the article "ペア数列の停止性" (P進大好きbot, Googology Wiki)
converted to plain markdown for grepping and for the §-traceability references
(`content.md line NNN`) scattered across the .thy/.md sources.  It is a DERIVED
file, gitignored and stored outside the repo (the new layout keeps tmp/ as a
symlink into the parent directory holding the external sources).  `pss_defs.thy`
and `pss_paper.thy` reference it via `@{file "tmp/content.md"}`, so the Isabelle
build needs the file to EXIST.

This script makes content.md reproducible so it can never become an
un-regenerable mystery file again (it was lost once to a stray `git merge` that
clobbered the gitignored tmp/ directory; this tool is the recovery path).

HOW THE ORIGINAL content.md WAS PRODUCED
----------------------------------------
The original extraction recipe (reverse-engineered from a 43% transcript
recovery) is: take original.html from the `mw-parser-output` article div, run
`html2text` (body_width=0, ul_item_mark='-', ignore_links=True), then
post-process: halve doubled backslashes (`\\\\` -> `\\`), rstrip each line,
render lists "loose" (a blank line between consecutive items) and flatten list
indentation.  That recipe alone reproduces the CONTENT faithfully but its line
NUMBERS drift from the original by tens of lines at block boundaries (html2text
version differences in the TOC / reference-list formatting).

To keep the 30-odd `content.md line NNN` references valid, this script ANCHORS
the output to `tools/content-anchors.md` — the transcript-recovered ground
truth (every line that was ever Read in a session, at its exact original line
number; gaps marked `<<<MISSING ...>>>`).  Known lines are pinned to their exact
positions; the ~13 gaps are filled with the html2text regen, content-aligned at
the gap boundaries and sized to fit so downstream line numbers stay exact.
Result: 6426 lines, 43% byte-exact at exact positions, gaps faithful (the few
references inside the large §8.6 gap are within ±a handful of lines).

USAGE
-----
    python3 tools/make_content.py            # writes tmp/content.md
Requires `html2text` (pip install html2text) and tmp/original.html present.
"""
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORIGINAL = os.path.join(REPO, "tmp", "original.html")
ANCHORS = os.path.join(REPO, "tools", "content-anchors.md")
OUT = os.path.join(REPO, "tmp", "content.md")


def regen_from_html(html):
    """html2text the article div, apply the extraction recipe -> list[str]."""
    import html2text
    i = html.find("mw-parser-output")
    if i < 0:
        sys.exit("ERROR: 'mw-parser-output' div not found in original.html")
    h = html2text.HTML2Text()
    h.body_width = 0
    h.ul_item_mark = "-"
    h.ignore_links = True            # [text](url) -> text ; heading edit-links -> []
    out = h.handle(html[i:]).replace("\\\\", "\\")   # halve doubled backslashes
    lines = [ln.rstrip() for ln in out.split("\n")]
    item = re.compile(r"^\s*(- |\d+\. )")
    proc, prev_item = [], False
    for ln in lines:
        if item.match(ln):
            ded = re.sub(r"^\s+(- |\d+\. )", r"\1", ln)   # flatten indentation
            if prev_item:
                proc.append("")                            # loose list
            proc.append(ded)
            prev_item = True
        else:
            proc.append(ln)
            if ln.strip() != "":
                prev_item = False
    return proc


def load_anchors(path):
    """Return (N, {lineno: text}) of the transcript-recovered known lines."""
    lines = open(path, encoding="utf-8").read().split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    known = {n + 1: lines[n] for n in range(len(lines)) if "MISSING" not in lines[n]}
    return len(lines), known


def reconstruct(regen, N, known):
    """Pin known lines to exact positions; fill gaps from regen, sized to fit."""
    from collections import defaultdict
    ridx = defaultdict(list)
    for k, ln in enumerate(regen):
        ridx[ln].append(k)

    def between(a_text, b_text):
        if a_text in ridx and b_text in ridx:
            for ra in ridx[a_text]:
                for rb in ridx[b_text]:
                    if rb > ra:
                        return ra, rb
        return None, None

    final = [None] * N
    for n, t in known.items():
        final[n - 1] = t
    n = 1
    while n <= N:
        if final[n - 1] is not None:
            n += 1
            continue
        a = n
        while a <= N and final[a - 1] is None:
            a += 1
        b = a - 1                       # gap is [n, b]; known resumes at a
        size = b - n + 1
        before, after = known.get(n - 1), known.get(a)
        content = None
        if before is not None and after is not None:
            ra, rb = between(before, after)
            if ra is not None:
                content = regen[ra + 1:rb]
        if content is None and after in ridx:
            rb = ridx[after][0]
            content = regen[max(0, rb - size):rb]
        if content is None and before in ridx:
            ra = ridx[before][-1]
            content = regen[ra + 1:ra + 1 + size]
        if content is None:
            content = []
        content = content[:size] + [""] * (size - len(content))   # fit exactly
        for k in range(size):
            final[n - 1 + k] = content[k]
        n = b + 1
    return [x if x is not None else "" for x in final]


def main():
    if not os.path.exists(ORIGINAL):
        sys.exit("ERROR: %s not found (restore the external source first)" % ORIGINAL)
    if not os.path.exists(ANCHORS):
        sys.exit("ERROR: %s not found" % ANCHORS)
    html = open(ORIGINAL, encoding="utf-8").read()
    regen = regen_from_html(html)
    N, known = load_anchors(ANCHORS)
    final = reconstruct(regen, N, known)
    with open(OUT, "w", encoding="utf-8") as f:
        f.write("\n".join(final) + "\n")
    bad = sum(1 for n, t in known.items() if final[n - 1] != t)
    print("wrote %s: %d lines, %d anchor lines pinned (%d violations)"
          % (OUT, len(final), len(known), bad))


if __name__ == "__main__":
    main()
