# §6.5 `Red`: definition and termination measure

`Red : T_PS -> T_PS` (簡約化, reduction) is the most intricate definition in the
formalization. Its recursion is deeply nested, so **the very fact that the
recursion terminates — i.e. that `Red` is well-defined — is a proposition to be
proved** (the article's 命題（Red の well-defined 性）, transcribed as
`p_6_5_Red_welldef`). The termination measure is the non-negative quantity that
decreases along every recursive call.

## The recursive definition (article §6.5)

With `j1 = Lng M - 1`, `j1' = TrMax M`, `m00 = M_{0,0}`, `m10 = M_{1,0}`:

- **`M` zero**: `Red M = ((0,0))`.
- **`M` multi**: `Red M = ⊕_J Red (P(M)_J)` (each `P`-component is shorter).
- **`M` mono, `M_0 = (0,0)`** (so `m00 = m10 = 0`):
  - `j1' = j1` (trunk is the whole thing): `Red M = ((j,j))_{j=m10}^{m10+j1}`.
  - `j1' < j1`: `Red M = ((j,j))_{j=0}^{j1'} ⊕ ⊕_J IncrFirst^{e_J}(Red N_J)`,
    where, encoding `n_J ∈ ℕ∪{-1}` by `np = n_J + 1 ∈ ℕ`:
    - `np = 0` if `(Br(M)_J)_{1,0} = 0`, else `np = Suc (THE j. (1,j) <_M^Next (1, FirstNodes(M)_J))`;
    - `e_J = Joints(M)_J + 1 - np`;
    - `N_J = (m00 + Joints(M)_J + 1, m10 + np) ⊕ Derp(Br(M)_J)`.
- **`M` mono, `M_0 ≠ (0,0)`**:
  - `m10 = 0`: `Red M = Red ((M_{0,j} - m00, M_{1,j}))_{j=0}^{j1}`
    (shifts row 0 down so that `M_0` becomes `(0,0)` — reduces to the core).
  - `m10 > 0`: with `N = Red (((j,j))_{j=0}^{m10-1} ⊕ IncrFirst^{m10}(M))` and
    `jN = Lng N - 1`: if `m10 ≤ jN` and `(N_j)_{j=m10}^{jN} ∈ PT_PS` then
    `Red M = (N_{0,j} - N_{0,m10} + N_{1,m10}, N_{1,j})_{j=m10}^{jN}`, otherwise
    `Red M = M`. The two `= M` fall-throughs (article footnotes [19]/[20]) are
    **dead branches** — later §6.5 propositions prove they never occur — but are
    needed for totality.

## The measure: `Lng(M) − TrMax(M)`

The article (content.md line 886) proves well-definedness as follows:

- On the **core** `{M ∈ PT_PS | M_0 = (0,0)}`, uniqueness/existence follows by
  induction on **`Lng(M) − TrMax(M)`** (the number of branch positions to the
  right of the trunk end).
- The extension to all of `T_PS` follows immediately from the definition in the
  remaining cases.

**Why a plain `Lng` measure fails.** The mono / `M_0 ≠ (0,0)` / `m10 > 0` case
recurses on
```
N = Red( ((j,j))_{j=0}^{m10-1} ⊕ IncrFirst^{m10}(M) )
```
whose argument is **longer** than `M` (a diagonal prefix of length `m10` is
prepended). So `Lng` increases. But the prepended diagonal also **extends the
trunk** by `m10`, so `Lng − TrMax` does not increase. Hence the measure must be
`Lng − TrMax`, not `Lng`. The other recursive calls reduce to the core:
- multi: `P`-components are strictly shorter;
- `m10 = 0`: one-step reduction to a core element (same `Lng`, same `TrMax`, now
  `M_0 = (0,0)`).

This measure depends on the §6.4 facts about `TrMax`, `Br`, `Joints`,
`FirstNodes` — so `Red_dom` cannot be proved before §6.4 is in place.

## Isabelle encoding

`Red` is defined with `function` and discharged by `by pat_completeness auto`
**only** — termination is **deferred** (no `termination` command). This is sound
because all recursive calls are on `Red`-free arguments (not nested recursion).

Consequences:
- `Red` is still a total HOL function, so terms like `Red M`, `Lng (Red M)`,
  etc. are meaningful; the §6.5 statements are stated about them directly.
- The simp/induction rules are the **conditional** `Red.psimps` / `Red.pinduct`,
  guarded by the domain predicate `Red_dom`; `Red.domintros` is available too.
- The article's well-definedness proposition becomes exactly
  `p_6_5_Red_welldef : M ∈ T_PS ⟹ Red_dom M` (currently `sorry`). Discharging it
  via the `Lng − TrMax` measure (plus §6.4) then unlocks all other §6.5 proofs,
  which need `Red.psimps`.

The helper `diagSeq a b = map (λj. (j,j)) [a..<Suc b]` encodes `((j,j))_{j=a}^b`;
`IncrFirst^k` is `(IncrFirst ^^ k)`.

## The explicit measure (refined 2026-05-24)

The article says the extension to `T_PS` is "immediate", but for a single
Isabelle `function`/`domintros` termination proof we need ONE measure that
strictly decreases on EVERY direct recursive call. No simple `Lng`, `β`, or
`rank` lexicographic measure works alone:

- `Lng` increases in the mono / `M_0 ≠ (0,0)` / `m10 > 0` case (case 4: the
  argument `diagSeq 0 (m10-1) @ IncrFirst^{m10} M` is longer);
- `β = Lng − TrMax` is unchanged in case 3 (`m10 = 0` shift) and not obviously
  monotone for `multi` blocks;
- `rank` (core < non-core) goes UP in the core case 2 (`Red N_J`, `N_J`
  non-core).

The working measure separates the two regimes that never interleave (a **mono**
argument never produces a **multi** one; `multi` only appears at entry or via
`P`-blocks):

- **mono `M`**: let `coreReduce M` be the core element a non-core mono `M`
  reduces to in one step (`m10 = 0`: shift row 0 down by `m00`; `m10 > 0`:
  `diagSeq 0 (m10-1) @ IncrFirst^{m10} M`). Define
  ```
  μ_mono(M) = (if M_0 = (0,0) then 2·β(M) else 2·β(coreReduce M) + 1)
  ```
  Checks (all strict):
  - case 2 (core `M` → `N_J`, non-core): `μ_mono(N_J) = 2·β(coreReduce N_J)+1
    ≤ 2(β(M)−1)+1 = 2β(M)−1 < 2β(M) = μ_mono(M)`, using the branch bound
    `Lng(Br M ! J) ≤ Lng M − TrMax M − 1` and that a `diagSeq 0 k` prefix
    extends the trunk (so `β(coreReduce N_J) ≤ Lng N_J ≤ β(M)−1`);
  - case 3 (non-core `m10=0` → `coreReduce M`): `2β(coreReduce M) <
    2β(coreReduce M)+1`;
  - case 4 (non-core `m10>0` → `coreReduce M`): same as case 3.
- **multi `M`**: a separate measure on `P`-blocks (strictly shorter `Lng`).
  Because mono recursion never yields a multi argument, a global well-founded
  relation can take `multi` blocks via `Lng`-descent and feed each mono entry
  into the `μ_mono` order independently.

The two arithmetic facts the mono part rests on:
1. **Branch bound**: `Lng (Br M ! J) ≤ Lng M − TrMax M − 1`
   (`Br M = P (seg M (TrMax M + 1) (Lng M − 1))`, each `P`-block ≤ the segment).
2. **Trunk extension by a diagonal prefix**: `TrMax (diagSeq 0 k @ rest) ≥ k`
   (the consecutive diagonal `(0,0),…,(k-1,k-1)` is a trunk), giving
   `β(coreReduce M) ≤ Lng (non-trunk part)`.

These (plus `Lng_diagSeq`, `entry_diagSeq`, and `β`-invariance of the row-0
shift and of `IncrFirst`) are the foundational helpers to prove first; the
`Red_dom` induction then follows the `μ_mono`/`Lng` split above.

> Method note: this refined measure came from re-checking the article's
> "extension is immediate" claim **on paper before grinding in Isabelle**
> (a transferable lesson from the BMS meta-advice; see `tmp/advices-answer.md`).
> The claim is true, but the Isabelle measure is non-trivial — exactly the kind
> of "paper says easy, formalization says subtle" gap worth resolving up front.

### Simplifications found while proving the helper lemmas (2026-05-24)

- **`μ_mono`'s VALUE branches only on `hd M = (0,0)`** (i.e. `entry M 0 0 = 0 ∧
  entry M 1 0 = 0`), NOT on `monoT`; so `coreReduce M`'s contribution to
  `μ_mono` only needs it to **start with `(0,0)`** (`coreReduce_core`).
  *Caveat (corrected):* the GLOBAL measure `ν` still needs `coreReduce M` to be
  **non-multi** (zero/mono), otherwise `ν(coreReduce M) = 1 + ∑…` rather than
  `μ_mono(coreReduce M)` and the case-3/4 descent `ν(coreReduce M) < ν(M)`
  breaks. Since `P`-blocks are always zero/mono (`m_6_2_P_components_1`), only
  the mono recursion can introduce a multi argument — so a `coreReduce`-is-mono
  (or just non-multi) lemma is still required. The found `m_6_2_P_components_1`
  does make `ν` itself **non-recursive** (multi blocks are zero/mono, so
  `ν(block) = μ_mono(block)` directly — no nested `ν`).
- **The `m10 = 0` (shift) sub-case needs no `TrMax`-invariance.** For the case-2
  bound it suffices that `β(coreReduce N_J) = β(shift N_J) = Lng N_J −
  TrMax(shift N_J) ≤ Lng N_J` (since `Lng` is preserved by the row-0 `map` and
  `β ≤ Lng` always). So the planned "row-0 shift preserves `TrMax`" lemma (which
  would have needed `m00 = min row 0`, a `PT_PS` structural fact) is **not
  required**. Only the `m10 > 0` sub-case uses `TrMax_diagSeq_append_ge`.
- **Multi via a sum measure.** A global `ν` can be defined by
  `ν(M) = (if multiT M then 1 + (∑_J ν(P M ! J)) else μ_mono(M))`,
  well-defined by `Lng`-recursion (blocks are shorter). Each block then has
  `ν(block) ≤ ∑ < ν(M)`. The mono entries feed `μ_mono`. Open obligation for
  this branch: `N_J ∈ PT_PS` (so case 2's argument is mono, never multi) — an
  article fact to transcribe/derive.

**Helper lemmas proved so far** (in `pss_mechanized.thy`): `Lng_diagSeq`,
`diagSeq_nth`, `entry_diagSeq`, `length_nth_le_concat`, `Lng_Br_le`,
`nextR1_consecutive`, `nextR1_diagSeq`, `TrMax_diagSeq`,
`entry_diagSeq_append_lo`, `entry_diagSeq_append_junction`, `le_TrMax_intro`,
`nextR1_diagSeq_append`, `TrMax_diagSeq_append_ge`, `TrMax_IncrFirst`,
`Lng_funpow_IncrFirst`, `TrMax_funpow_IncrFirst`.

**Remaining**: define `ν`/`μ_mono` (and `coreReduce`); prove the per-case
descent; run the `Red_dom` induction via `Red.domintros` / a well-founded
relation on `ν`.

## UPDATE 2026-05-29: dead-branch[20] reachability — empirically UNREACHABLE

`python/dead20_check.py` runs an instrumented `Red` on standard-form inputs
(yaBMS `is_standard`) and ALL recursive sub-calls, counting how often the
mono / M0≠(0,0) / m10>0 case is reached and whether its `else: return M`
fall-through (dead-branch[20]) is ever taken:

| range | standard inputs | m10>0 reached | dead-branch[20] taken |
|---|---|---|---|
| len≤4, val≤3 | 56 | 22 | 0 |
| len≤3, val≤6 | 14 | 2 | 0 |
| len≤5, val≤2 | 152 | 98 | 0 |
| len≤4, val≤4 | 56 | 22 | 0 |
| **total** | | **144** | **0** |

So `m10 ≤ jN ∧ seg(N,m10,jN) ∈ PT_PS` held on every one of the 144 m10>0
evaluations: **dead-branch[20] is empirically unreachable**, hence the
unreachability lemma (the shared blocker of `Red_IncrFirst` m10>0 and
`Red_Pred` case 6) is TRUE and worth proving. Recommended timing: after §6.8
prop1 (d0pos) closes and as part of the §6.5 A4 anchored-slice cleanup (so the
Red scaffolding is on a sound domain first).

## UPDATE 2026-06-01: §6.5 understand-phase plan (post-§6.8-merge)

A 3-agent understand workflow (scaffolding / empirical / article-deps) mapped
the §6.5 dependency structure. **The whole subsection funnels through ONE
bottleneck: `Red_le` (直系先祖の Red 不変性) on the anchored-slice domain.**

Strict proof order (`→` = "unlocks"):
**7a `Red_le` on `anchored_slice` → 5 dead-branch[20] unreachable → 6
`monoT_Red` → 3,4 `Red_IncrFirst`/`Red_Pred` (m10>0 cases)**.

- **Now provable, A4-independent**: `Lng_Red` (✅), `Red_zeroT` (✅), and the two
  clean structural lemmas the article's `monoT_Red` proof rests on —
  **fact 1 (length): `Lng(N) = Lng(M) + m10`** (from `Lng_Red` + `Lng_diagSeq` +
  `Lng_funpow_IncrFirst`, unconditional) and **fact 2 (ancestor index-shift):
  `(i,j) ≤_M (i',j') ⟺ (i,j+m10) ≤_N (i',j'+m10)`** (from the diagSeq-prefix +
  `IncrFirst^m10` trunk structure). Both verified TRUE 990/0.
- **`monoT_Red`** (= dead-branch[20]/[19] unreachability, the §6.5 keystone) =
  fact1 + fact2 + `Red_le`-anchored. Its use-site IS anchored (the `m10..jN`
  slice of `N` is anchored by `(0,m10) ≤_N (0,jN)`), so `Red_le`-anchored closes it.
- **`Red_le`-anchored (7a)** is the hardest proof in the project. Prereqs are in
  place: `anchored_slice` is defined (`pss_defs.thy` 463-466 = anchored slices of
  `ST_PS ∪ (RT_PS∩PT_PS)`), `Red_dom` termination is GREEN (ν/`coreReduce`). The
  remaining work is the global argument: the article's "immediate by Lng
  induction" fails in the **multi case** (block concatenation can create/destroy
  a row-0 `≤` across block boundaries — counterexample `Red((0,0)(0,1)) =
  (0,0)(1,1)`); on the anchored domain the anchor `(0,a) ≤_S (0,b)` fixes the
  inter-block ancestor structure so concatenation preserves `≤`.

Empirical (rank-stratified, BOTH counts, rank≥12 val≥5; scripts
`python/red65_*.py`): fact1 990/0, fact2 990/0, dead-branch 344 reached/0 taken
(gen_std sub-calls, L=3..12) + 990 direct/0, `Red_le` 307/0 on standard / 776/0
on anchored-mono slices / FALSE only on general `T_PS` (`(0,0)(0,1)`).

**First concrete targets**: facts 1 & 2 (clean bricks), then design + prove
`Red_le`-anchored (7a).
