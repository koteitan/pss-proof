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

- **`μ_mono` branches only on `hd M = (0,0)`** (i.e. `entry M 0 0 = 0 ∧
  entry M 1 0 = 0`), NOT on `monoT`. So `coreReduce M` need only be shown to
  **start with `(0,0)`** — its `monoT`-ness is irrelevant to the measure. This
  removes a whole class of "shift/append preserves `monoT`" obligations.
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
