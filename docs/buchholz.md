# §7: the Buchholz notation system [Buc1]

§7 of the article translates reduced pair sequences into Buchholz's ordinal
notation system. That system's core definitions (the ordering `<`, the `[]`
operator, `dom`, `OT`) are **not spelled out in the article** — it cites

> **[Buc1]** W. Buchholz, "A new system of proof-theoretic ordinal functions",
> Annals of Pure and Applied Logic 32 (1986), pp. 195–207.

This file extracts the [Buc1] definitions we need, and records how they are
encoded in `pss_paper.thy` (the Buchholz formulas are an external reference, so
they live on the paper side, not in `pss_defs.thy`).

[Buc2] (W. Buchholz, "Relating ordinals to proofs in a perspicuous way",
unpublished) is **unavailable**, but the only part the article uses — the
modification of `([].4)(ii)` — is written out explicitly in the article's own
footnote (content.md line 6427), so it is reconstructed below.

## [Buc1] §2 (pp. 200–201): the notation system (OT, <)

Symbols `D_0, D_1, …, D_ω`. (Indices `v ≤ ω` are modelled by `enat`; `ω = ∞`.)

- **Terms `T` (T1)–(T3)**: (T1) `0 ∈ T`. (T2) `a ∈ T, v ≤ ω ⟹ D_v a ∈ T`
  (a *principal term*). (T3) `a_0,…,a_k` principal, `k ≥ 1 ⟹ (a_0,…,a_k) ∈ T`.
  A single principal: `(a) := a`.
- **Order `a < b` (<1)–(<3)**: (<1) `b ≠ 0 ⟹ 0 < b`.
  (<2) `u < v ∨ (u = v ∧ a < b) ⟹ D_u a < D_v b`.
  (<3) `a = (a_0..a_n)`, `b = (b_0..b_m)`, `1 ≤ m+n`: `a < b` iff
  (i) `n < m ∧ ∀i≤n. a_i = b_i`, or (ii) `∃k≤min(n,m). a_k < b_k ∧ ∀i<k. a_i = b_i`.
  `<` is a linear order on `T` (Lemma 2.1). (This is the dictionary order on the
  principal-term lists, with a proper prefix counting as smaller.)
- **Abbreviations**: `M ≤ M' :⟺ ∀x∈M ∃y∈M'. x ≤ y`; `M < a :⟺ ∀x∈M. x < a`;
  `a ≤ M :⟺ ∃x∈M. a ≤ x`.
- **`G_u a ⊆ T` (G1)–(G3)**: (G1) `G_u 0 = ∅`. (G2) `G_u (a_0..a_k) = ⋃ G_u a_i`.
  (G3) `G_u D_v b = {b} ∪ G_u b` if `u ≤ v`, `∅` if `v < u`.
- **`OT ⊆ T` (OT1)–(OT3)**: (OT1) `0 ∈ OT`. (OT2) `a_0..a_k ∈ OT` principal,
  `k ≥ 1`, `a_k ≤ … ≤ a_0 ⟹ (a_0..a_k) ∈ OT`. (OT3) `b ∈ OT ∧ G_v b < b ⟹
  D_v b ∈ OT`. Also `a ∈ OT ⟹ G_u a ⊆ OT`.
- **Ordinal value `o(a)`**: `o(0) = 0`; `o((a_0..a_k)) = o(a_0) # … # o(a_k)`
  (natural sum); `o(D_v b) = ψ_v o(b)`.

## [Buc1] §3 (pp. 203–204): addition and fundamental sequences

- **Addition / multiplication**: `a+0 = 0+a = a`;
  `(a_0..a_n) + (b_0..b_m) = (a_0..a_n, b_0..b_m)`; `a·0 = 0`, `a·(n+1) = a·n + a`.
- **`T_v` (`v ≤ ω`)**: `T_v = {0} ∪ {(D_{u_0}a_0,…,D_{u_n}a_n) : n≥0, a_i∈T,
  u_i ≤ v}`. Then `T_0 ⊊ T_1 ⊊ … ⊊ T_ω = T`, and `T_u = {x∈T : x < D_{u+1}0}`
  for `u < ω`. Abbreviation `1 := D_0 0`; `ℕ ≅ {0,1,1+1,…} ⊆ OT ∩ T_0`.
- **`dom(a)` and `a[z]` ([].0)–([].5)**:
  - ([].0) `dom(0) = ∅`.
  - ([].1) `dom(1) = {0}`; `1[0] = 0`.
  - ([].2) `dom(D_{u+1}0) = T_u`; `(D_{u+1}0)[z] = z`.
  - ([].3) `dom(D_ω 0) = ℕ`; `(D_ω 0)[n] = D_{n+1}0`.
  - ([].4) `a = D_v b` with `b ≠ 0`:
    - (i) `dom(b) = {0}`: `dom(a) = ℕ`; `a[n] = (D_v b[0])·(n+1)`.
    - (ii) `dom(b) = T_u`, `v ≤ u < ω`: `dom(a) = ℕ`; **[Buc1] original**:
      `a[n] = D_v b[D_u b[1]]`. **[Buc2] modification (used by the article)**:
      `x_0 = D_u 0`, `x_i = b[D_u x_{i-1}]` (`i>0`), `a[n] = D_v b[x_n]`.
    - (iii) `dom(b) ∈ {ℕ} ∪ {T_u : u < v}`: `dom(a) = dom(b)`; `a[z] = D_v b[z]`.
  - ([].5) `a = (a_0..a_k)`, `k ≥ 1`: `dom(a) = dom(a_k)`;
    `a[z] = (a_0..a_{k-1}) + a_k[z]`.
  - Also `0[n] = 0`; if `dom(a) = {0}` then `a[n] = a[0]`.
- **Lemma 3.2**: (a) `z∈dom(a) ⟹ a[z] < a`. (b) `z,z'∈dom(a)=T_u, z<z' ⟹
  a[z] < a[z']`. (c) `0≠a∈T_v ⟹ dom(a) ∈ {{0},ℕ}∪{T_u:u<v} ∧ a[z]∈T_v`.
- **Lemma 3.3**: `a,z∈OT ∧ z∈dom(a) ⟹ a[z]∈OT`.
- **Lemma 2.2**: `(OT_B, <)` is well-founded — this is the foundation of the
  whole termination argument (descent along fundamental sequences + well-
  foundedness).

## Derived notions used in the article's §7

- `T_B` := the `D_ω`-free terms of `T` (no index equals `ω` anywhere — note this
  is **recursive**, unlike `T_v` which constrains only top-level indices).
  `OT_B := OT ∩ T_B` (content.md line 5951). `PT_B` / `MT_B` are the `D_ω`-free
  principal (mono) / multi terms.
- `Σ` = alphabet `{(, „, ", ), 0} ∪ {D_u : u ≤ ω}`; `Σ_B t` builds a `T_B` term
  from a list of principal terms. `P_B : T_B → PT_B^{<ω}` decomposes a term into
  its principal components (the Buchholz analogue of the pair-sequence `P`).
- §7.2 scb-decomposition `(s, c, b)`: splits a term's symbol string into a
  prefix `s`, a sub-term `c`, and a suffix `b` (`s, b ∈ Σ^{<ω}`). `RightNodes`.
- §7.3 `Trans`: `RT_PS → T_B` (reduced pair sequence → Buchholz term), extended
  to all of `T_PS` via `Red`. `Mark`. §7.4 admissible parent relation
  `<_M^{NextAdm}`.

## Isabelle encoding (in `pss_paper.thy`, §7.1)

Done:
- `datatype BT = Trm "BP list" and BP = DB enat BT` — `Trm []` is `0`,
  `Trm [DB v a]` is the principal `D_v a`, length `≥ 2` is a tuple.
- `lessBT` / `lessBP` (the `<` dictionary order), `leBT` (`≤`).
- `GBT` / `GBP` (`G_u`); `addBT` (`+B`), `multBT` (`*B`); `TBv` (`T_v`);
  `dfree_BT` / `dfree_BP` and `T_B` (the `D_ω`-free terms).
- `descP`, `isOT_BT` / `isOT_BP`, `OT` (OT1)-(OT3); `OT_B = OT ∩ T_B`.
- `domB` / `operB` (`a[z]`) / `xseq` as a mutual `function` with **deferred
  termination** (`by pat_completeness auto`, like `Red`): ([].0)-([].5) with the
  [Buc2]-modified ([].4)(ii). Helpers `Dprin`, `numBT` / `numNat` / `NatSet`,
  `tbvIdx`.
- `untrm`, `PB` (`P_B`) and `SigmaB` (`Σ_B`), mutually inverse.

To do: a flatten-to-`Σ`-string view (needed to state the string-level
propositions faithfully — parenthesis balance, sub-expression inequality
extension), scb-decomposition / `RightNodes` (§7.2), then §7.3 `Trans` / `Mark`,
§7.4 admissible parent relation, and the §7 statements. `Trans` connects to the
pair-sequence side (`pss_defs`), so it is defined in `pss_paper` (which imports
`pss_defs`). The well-foundedness of `(OT_B, <)` ([Buc1] Lemma 2.2) is the
eventual source of termination; it (and `domB`/`operB`/`Red` termination) will
be stated as the relevant §7/§8 propositions.
