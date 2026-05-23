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
