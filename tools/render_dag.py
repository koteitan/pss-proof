#!/usr/bin/env python3
"""Render dag.dot -> dag.svg/dag.png/dag.html (dark, 2-column staircase).

dag.dot is the clean hand-maintained source. This script computes the layout,
splits every over-wide rank (>= THRESH nodes) into a 2-column staircase via
invisible edges c[i]->c[i+2], then renders. dag.html gets the zoom/pan/touch UI.
Run after editing dag.dot:  python3 tools/render_dag.py
"""
import os, re, subprocess
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOT  = os.path.join(ROOT, 'dag.dot')
THRESH = 10   # ranks with >= THRESH nodes get 2-columned

dot = open(DOT).read()
nodes = set()
for ln in dot.splitlines():
    m = re.match(r'\s*([A-Za-z_]\w*)\s*\[label=', ln)
    if m and m.group(1) != 'G':
        nodes.add(m.group(1))

# 1) layout to get each node's rank (y) and order (x)
plain = subprocess.run(['dot','-Tplain'], input=dot, capture_output=True, text=True).stdout
pos = {}
for ln in plain.splitlines():
    p = ln.split()
    if p and p[0] == 'node' and p[1] in nodes:
        pos[p[1]] = (float(p[2]), float(p[3]))

from collections import defaultdict
ranks = defaultdict(list)
for n,(x,y) in pos.items():
    ranks[round(y,2)].append((x,n))

invis = []
for y,lst in ranks.items():
    if len(lst) >= THRESH:
        names = [n for _,n in sorted(lst)]
        for i in range(len(names)-2):
            invis.append(f'  {names[i]} -> {names[i+2]} [style=invis,weight=10];')

i = dot.rstrip().rfind('}')
dot2 = dot[:i] + '\n  /* 2-column staircase of wide ranks (auto, invisible) */\n' \
      + '\n'.join(invis) + '\n}\n'

# 2) render svg + png
subprocess.run(['dot','-Tsvg','-o',os.path.join(ROOT,'dag.svg')], input=dot2, text=True)
subprocess.run(['dot','-Tpng','-Gdpi=90','-o',os.path.join(ROOT,'dag.png')], input=dot2, text=True)

m = re.search(r'width="([\d.]+)pt" height="([\d.]+)pt"', open(os.path.join(ROOT,'dag.svg')).read())
if m:
    w,h = float(m.group(1)), float(m.group(2))
    print(f"dag.svg/png: {int(w)}x{int(h)}pt  ratio {round(w/h,2)}  ({len(invis)} invis edges)")

# 3) zoomable/touch dark html
subprocess.run(['python3', os.path.join(ROOT,'tools','build_dag_html.py')])
