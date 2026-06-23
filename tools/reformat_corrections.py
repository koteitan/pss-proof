#!/usr/bin/env python3
"""Reformat corrections.md: ### headers, order = 位置/原文/訂正案/原文の問題点/.../形式化での扱い.
Content is preserved verbatim; only section headers (**X**) become ### X and sections are reordered
so 原文 and 訂正案 sit adjacent and the problem analysis comes after them."""
import re, sys

src = open('corrections.md').read()
lines = src.split('\n')
start = next(i for i, l in enumerate(lines) if l.startswith('## '))
preamble = '\n'.join(lines[:start]).rstrip()

# split into entries on top-level '## ' (not '### ')
entries = []
cur = None
for l in lines[start:]:
    if l.startswith('## ') and not l.startswith('### '):
        if cur is not None:
            entries.append(cur)
        cur = [l]
    elif cur is not None:
        cur.append(l)
if cur is not None:
    entries.append(cur)

HDR = re.compile(r'^\*\*(.+?)\*\*(.*)$')

# A line `**X**...` is a SECTION header only if X starts with one of these.
# (avoids catching inline bold lead-ins / bold list items inside prose, e.g. A4/A6.)
HEADER_PREFIXES = ('位置', '所在', '該当', '原文', '問題', '観察', 'メタ観察', '不足',
                   '単調性', '結論', '補足', '経験的確認', '確認', '反例', '根本原因',
                   '追補', '訂正案', '形式化での扱い', '明確化')

def is_header(m):
    lbl = m.group(1).strip()
    return '。' not in lbl and len(lbl) < 80 and lbl.startswith(HEADER_PREFIXES)

def categorize(lbl):
    l = lbl.strip()
    if l.startswith(('位置', '所在', '該当')): return 'loc'
    if l.startswith('原文'):       return 'orig'
    if l.startswith('訂正案'):     return 'fix'
    if l.startswith('形式化での扱い'): return 'formal'
    return 'rest'

def parse_sections(body):
    secs = []
    curlbl, curcontent = None, []
    for l in body:
        if l.strip() == '---':
            continue
        m = HDR.match(l)
        if m and is_header(m):
            if curlbl is not None:
                secs.append((curlbl, curcontent))
            curlbl = m.group(1).strip()
            trailing = re.sub(r'^[\s:：]+', '', m.group(2))
            curcontent = [trailing] if trailing.strip() else []
        elif curlbl is not None:
            curcontent.append(l)
    if curlbl is not None:
        secs.append((curlbl, curcontent))
    return secs

def trim(content):
    while content and content[0].strip() == '': content = content[1:]
    while content and content[-1].strip() == '': content = content[:-1]
    return content

out = [preamble, '']
for ent in entries:
    title = ent[0].strip()
    secs = parse_sections(ent[1:])
    by = {'loc': [], 'orig': [], 'fix': [], 'formal': [], 'rest': []}
    for lbl, content in secs:
        by[categorize(lbl)].append((lbl, content))

    ordered = []
    for lbl, content in by['loc']:   ordered.append(('位置', content))
    for lbl, content in by['orig']:  ordered.append((lbl, content))
    for lbl, content in by['fix']:   ordered.append((lbl, content))
    # rest: first one becomes 原文の問題点 (only if there is an 原文 to compare against)
    rest = by['rest']
    for i, (lbl, content) in enumerate(rest):
        if i == 0 and by['orig']:
            ordered.append(('原文の問題点', content))
        else:
            ordered.append((lbl, content))
    for lbl, content in by['formal']: ordered.append(('形式化での扱い', content))

    out.append(title)
    out.append('')
    for lbl, content in ordered:
        out.append('### ' + lbl)
        c = trim(content)
        if c:
            out.extend(c)
        out.append('')
    # entry separator already provided by trailing blank

result = '\n'.join(out).rstrip() + '\n'
open('/tmp/corrections_new.md', 'w').write(result)

# sanity report
print(f"entries: {len(entries)}")
print(f"orig chars: {len(src)}  new chars: {len(result)}")
for ent in entries:
    title = ent[0].strip()[:50]
    secs = parse_sections(ent[1:])
    labs = [categorize(l) for l, _ in secs]
    print(f"  {title:50}  sections={[l for l,_ in secs]}")
