#!/usr/bin/env python3
"""Ensure every corrections.md entry has a verbatim `### 原文` section, in order
位置 / 原文 / 訂正案(or 明確化) / 原文の問題点 / extras / 形式化での扱い."""
import re

# entries whose 位置 ends with the verbatim original as a blockquote / bullet list:
# split that trailing block off into a 原文 section.
BLOCKQUOTE_SPLIT = {'A7', 'A8', 'A9', 'A10', 'A11', 'A12', 'A13'}

# entries where the original is not quoted in 位置: provide the verbatim 原文.
GENBUN = {
'A14': "(3) $t$ は第$0$種scb分解可能でないか、または $t$ は第$1$種scb分解可能でない。\n\n(4) $t$ の第$0$種scb分解は一意である。\n\n(5) $t$ の第$1$種scb分解は一意である。",
'A15': "命題（$\\textrm{Trans}$ のwell-defined性）: 上の条件を全て満たす写像 $\\textrm{Trans}$ と $\\textrm{Mark}$ が一意に存在する。",
'A16': "任意の $M \\in T_{\\textrm{PS}}$ に対し、以下は同値である：\n\n(1) $M$ は単項である。\n\n(2) $\\textrm{Trans}(M)$ は単項であるか、$P(M)_0$ が零項でありかつ $\\textrm{Lng}(P(M)) = 2$ である。",
'A17': "$m = j_1$ であることと $\\textrm{Mark}(M,m) = D_{M_{1,m}} 0$ であることは同値である。",
'A18': "$j_1=\\textrm{Lng}\\,M-1$ の一意な NextAdm 親 $j_0$ と、$(0,j)\\le_M(0,j_0)$ なる任意の $j$ について、$\\textrm{Mark}(M,j)$ は $\\textrm{Mark}(M,j_0)$ の周りに scb 分解される。",
'A19': "$(M,m_0),(M,m_1)\\in T_{\\textrm{PS}}^{\\textrm{Marked}}$ に対し、次は同値: (1) $m_0<m_1$。 (2) $\\textrm{Mark}(M,m_1)\\neq\\textrm{Mark}(M,m_0)$ かつ $(\\textrm{Mark}(M,m_1),\\textrm{Mark}(M,m_0))\\in T_{\\textrm{B}}^{\\textrm{Marked}}$。",
'A20': "$c_1 = \\textrm{Mark}(\\textrm{Pred}(M),j_{-1}) = \\textrm{Trans}((M_j)_{j=j_0}^{j_1-1})$",
'A21': "$N := (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)}$ について、$j_0^N = j'_0$（$\\textrm{parent}\\,N\\,0\\,(\\textrm{Lng}\\,N-1) = j'_0$）である。",
'A22': "$M[n]_{0,\\ q'(j_1-j_0)+r'}$",
'C1':  "左端2文字は $D_{M_{1,0}} D_u$ である。",
}

# clean 位置 (strip the inline original quote that is now in 原文)
ICHI = {
'A18': "§7.4「系（$\\textrm{Mark}$ と $<_M^{\\textrm{NextAdm}}$ の関係）」(content.md 付近、`p_7_4_Mark_nextAdm`)。",
'A19': "§7.4「命題（$\\textrm{Mark}$ が順序関係を保つこと）」(content.md 2466)。",
'A20': "§8.1「補題（条件(I)か(III)の下での $c_1$ 前後の具体表示）」(content.md 2923) の (1)(content.md 2955)。",
'A21': "§8.1「補題（条件(I)か(III)の下での $c_1$ 前後の具体表示）」(content.md 2923) の (5)(content.md 2945-2947)。",
'C1':  "§7.3 命題（$\\textrm{Trans}$ の最左単項成分の左端の基本性質）clause (3)（content.md 2342）。",
}

PROBLEM_LABELS = ('問題', '観察', '不足')  # first section starting with one of these -> 原文の問題点 (not メタ観察)

src = open('corrections.md').read()
lines = src.split('\n')
start = next(i for i, l in enumerate(lines) if l.startswith('## '))
preamble = '\n'.join(lines[:start]).rstrip()

entries, cur = [], None
for l in lines[start:]:
    if l.startswith('## ') and not l.startswith('### '):
        if cur: entries.append(cur)
        cur = [l]
    elif cur is not None:
        cur.append(l)
if cur: entries.append(cur)

def trim(c):
    while c and c[0].strip() == '': c = c[1:]
    while c and c[-1].strip() == '': c = c[:-1]
    return c

out = [preamble, '']
for ent in entries:
    title = ent[0].strip()
    eid = re.match(r'^## (A\d+|C\d+)', title).group(1)
    # parse sections
    secs, curlbl, curc = [], None, []
    for l in ent[1:]:
        m = re.match(r'^### (.+)$', l)
        if m:
            if curlbl is not None: secs.append((curlbl, curc))
            curlbl, curc = m.group(1).strip(), []
        elif curlbl is not None:
            curc.append(l)
    if curlbl is not None: secs.append((curlbl, curc))
    D = {lbl: trim(c) for lbl, c in secs}
    order_labels = [lbl for lbl, _ in secs]

    # rename first problem-ish label -> 原文の問題点
    for i, lbl in enumerate(order_labels):
        if lbl.startswith(PROBLEM_LABELS) and lbl != 'メタ観察':
            order_labels[i] = '原文の問題点'
            D['原文の問題点'] = D.pop(lbl)
            break

    # build 原文
    if '原文' not in D:
        if eid in BLOCKQUOTE_SPLIT:
            ic = D.get('位置', [])
            # split at first line that is a blockquote or bullet
            k = next((j for j, x in enumerate(ic) if x.lstrip().startswith(('>', '- '))), None)
            if k is not None:
                D['位置'] = trim(ic[:k])
                D['原文'] = trim(ic[k:])
        elif eid in GENBUN:
            D['原文'] = GENBUN[eid].split('\n')
        # place 原文 right after 位置 in order
        if '原文' in D:
            order_labels = [l for l in order_labels]  # copy
            if '原文' not in order_labels:
                pos = order_labels.index('位置') + 1 if '位置' in order_labels else 0
                order_labels.insert(pos, '原文')
    # 位置 override (strip inline quote)
    if eid in ICHI:
        D['位置'] = ICHI[eid].split('\n')

    # A6: move the parenthetical commentary out of 原文 into 原文の問題点
    if eid == 'A6' and '原文' in D:
        keep  = [x for x in D['原文'] if not x.strip().startswith('（命題そのものは')]
        moved = [x for x in D['原文'] if x.strip().startswith('（命題そのものは')]
        D['原文'] = trim(keep)
        if moved:
            D['原文の問題点'] = trim(moved) + [''] + D.get('原文の問題点', [])

    out.append(title); out.append('')
    for lbl in order_labels:
        if lbl not in D: continue
        out.append('### ' + lbl)
        c = trim(D[lbl])
        if c: out.extend(c)
        out.append('')

result = re.sub(r'\n{3,}', '\n\n', '\n'.join(out)).rstrip() + '\n'
open('/tmp/corrections_genbun.md', 'w').write(result)
# report
print("entries:", result.count('\n## '))
miss = []
for ent in entries:
    eid = re.match(r'^## (A\d+|C\d+)', ent[0]).group(1)
    body = '\n'.join(ent)
print("### 原文 count:", result.count('\n### 原文\n'))
# list entries lacking 原文 in output
for blk in re.split(r'\n## ', result)[1:]:
    eid = blk.split('.')[0].split(' ')[0].split('（')[0]
    if '### 原文\n' not in ('\n'+blk) and eid != 'C1' or ('### 原文' not in blk):
        pass
print("entries WITHOUT ### 原文:",
      [b.split('\n')[0][:8] for b in re.split(r'\n## ', result)[1:] if '\n### 原文\n' not in '\n'+b])
