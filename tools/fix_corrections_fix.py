#!/usr/bin/env python3
"""Replace each entry's `### 訂正案...` body with the post-replacement string ONLY
(no explanatory prose). Keys are the entry id (A1, A2, ...)."""
import re

# 訂正案 = ONLY the corrected text that replaces 原文. No "...に直す", no rationale.
FIX = {
'A1': r'''- (2) $(M[n],f(n)) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],f(n)) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(f(n))$''',

'A2': r'''$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(N)$''',

'A3': r'''(4) を削除。''',

'A4': r'''系（直系先祖の $\textrm{Red}$ 不変性）: $S \in \textrm{ST}_{\textrm{PS}}$（または $S \in \textrm{RT}_{\textrm{PS}} \cap \textrm{PT}_{\textrm{PS}}$）と $a \le b$, $(0,a) \le_S (0,b)$ に対する $M = (S_j)_{j=a}^{b}$ に限り、$\leq_M$ と $\leq_{\textrm{Red}(M)}$ は一致する。''',

'A5': r'''任意の $M \in RT_{\textrm{PS}}$ に対し、$j_1 := \textrm{Lng}(M)-1$ と置くと、任意の $j'_1 \in \mathbb{N}$ に対し $\textrm{TrMax}(M) \le j'_1 \le j_1$ ならば $(M_j)_{j=0}^{j'_1}$ は簡約である。''',

'A6': r'''補題（標準形の階層の単調性）: $S_{k-1}T_{\textrm{PS}} \subseteq S_kT_{\textrm{PS}}$。''',

'A7': r'''$M$ が単項であるという条件下で $\textrm{Br}(M')$ が降順となることを $k_0$ に関する数学的帰納法で示す。''',

'A8': r'''$j_1 = j_0^N + n(j_1^N-j_0^N) - 1$''',

'A9': r'''$J_1 := \textrm{Lng}(\textrm{Br}(M)) - 1$。$\textrm{Br}(M) = ()$ ならば $\textrm{LastStep}(M) = 0$。''',

'A10': r'''脚注[19]/[20]の不到達（命題（単項性と $\textrm{Red}$ の関係））を、系（直系先祖の $\textrm{Red}$ 不変性）を経由せず独立に証明し、それを起点に他の命題を導く。''',

'A11': r'''(2) $(s,c,b)$ が $t$ の scb分解で $c$ が主表現列（`isPTB_str c`）ならば、$(D_v s, c, b)$ は $D_v t$ の scb分解である。''',

'A12': r'''$c_0, c_1 \in T_{\textrm{B}}$、$t_0 \in T_{\textrm{B}}$、$t_0 \neq ()$、$(s, \textrm{flat}(c_0), b)$ が $t_0$ の scb分解であるとする。このとき $t_1 \in T_{\textrm{B}}$ が存在して $\textrm{flat}(t_1) = s\frown\textrm{flat}(c_1)\frown b$ かつ $(s, \textrm{flat}(c_1), b)$ が $t_1$ の scb分解となる。''',

'A13': r'''$c' \in T_{\textrm{B}}$ が主表現、$u_1 \in T_{\textrm{B}}$、$\textrm{flat}(u_1) = s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1$、$(s_0, \textrm{flat}(c), b_0)$ が $u_1$ の scb分解、**かつ $s_0 = s_1 \frown D_v\,\textrm{flat}(t)$**（2 出現の一致）であるとき、ある $u_1'$ が存在して $\textrm{flat}(u_1') = s_1 \frown D_v\,\textrm{flat}(t+c') \frown b_1$ かつ $(s_0, \textrm{flat}(c'), b_0)$ が $u_1'$ の scb分解となる。''',

'A14': r'''(3)(4)(5) の前提に「$t \neq ()$」を追加する。''',

'A15': r'''$\textrm{Red}(M)$ が簡約である $M$（簡約ペア数列・標準形・[[A4]] の祖先 anchored 切片）に対し $\textrm{Trans}/\textrm{Mark}$ が一意に定まり、$(\textrm{IncrFirst},\textrm{Red})$ 不変性が成り立つ。''',

'A16': r'''$M \in RT_{\textrm{PS}} \land \neg\textrm{zeroT}(P(M)_0)$ の下で、$\Sigma_{\textrm{B}}$ 表示および単項性命題 (2) を述べる。''',

'A17': r'''§7.3 の基点・順序命題の前提に「$M$ は非零項」（$M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}$）を追加する。''',

'A18': r'''命題の仮定に「$j$ は $M$-許容（$(M,j)\in\textrm{Marked}$）」を追加する。''',

'A19': r'''(2) $(\textrm{Mark}(M,m_0),\textrm{Mark}(M,m_1)) \in T_{\textrm{B}}^{\textrm{Marked}}$''',

'A20': r'''part(1) の $\textrm{Trans}(\text{切片}) = c_1$ に「$j_0 < j_1-1$（切片が非単項）」を課す。''',

'A21': r'''part(5) を「$\textrm{transCondI}\,M$」に限定する。''',

'A22': r'''$M[n]_{0,\ j_0+q'(j_1-j_0)+r'}$''',

'A23': r'''> すなわち[Buc1] ([].4) (ii)の場合分けにおいて、各 \(i \in \mathbb{N}\) に対し \(x_i\) を「\(i = 0\) ならば \(x_i = D_u 0\)、\(i > 0\) ならば \(x_i = b[D_u x_{i-1}]\)」と定め、\(a[n]\) の定義を \(D_v x_n\) に変えるということである。''',
}

src = open('corrections.md').read()
lines = src.split('\n')

# split into entries
out = []
i = 0
# pass through, locating "### 訂正案" sections and the entry id they belong to
cur_id = None
n = len(lines)
result = []
idx = 0
while idx < n:
    l = lines[idx]
    m = re.match(r'^## (A\d+|C\d+)', l)
    if m:
        cur_id = m.group(1)
    # normalize 原文 header only (NOT 原文の問題点); drop stale parentheticals
    if re.match(r'^### 原文(（.*）)?\s*$', l):
        l = '### 原文'
    fixmatch = re.match(r'^### 訂正案', l)
    if fixmatch and cur_id in FIX:
        result.append('### 訂正案')           # normalized header
        # skip old body until next "### " or "## " or EOF
        idx += 1
        while idx < n and not re.match(r'^#{2,3} ', lines[idx]):
            idx += 1
        # insert new body
        result.append('')
        result.extend(FIX[cur_id].split('\n'))
        result.append('')
        continue
    result.append(l)
    idx += 1

newsrc = '\n'.join(result)
newsrc = re.sub(r'\n{3,}', '\n\n', newsrc).rstrip() + '\n'
open('/tmp/corrections_fixed.md', 'w').write(newsrc)
print("replaced 訂正案 for:", sorted(FIX.keys(), key=lambda s:int(s[1:])))
print("entries:", newsrc.count('\n## '))
