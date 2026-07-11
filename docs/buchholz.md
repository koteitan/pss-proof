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

- §7.2: `Sym` (the alphabet `Σ`), `flatBT` / `flatBP` (term to `Σ`-string),
  `RightNodes` (deferred termination), `scb_decomp` (predicate:
  `flatBT t = s @ c @ b`, `c` the string of a `PT_B` principal, `b` all `)`),
  `scb_kind0` / `scb_kind1` (第0種/第1種), `isPTB_str`, `MarkedB` (`T_B^Marked`).

To do (§7.3 `Trans` / `Mark` — the crux, most complex definition, harder than
`Red`): a mutual `function Trans :: pairseq ⇒ BT` and `Mark :: pairseq ⇒ nat ⇒
BT`, deferred termination (well-definedness = `Trans_dom`, by induction on
`Lng M`). The body is a large case analysis (`M` reduced with `j1 = 0`; reduced
mono with `j1 > 0` under the mutually-exclusive conditions (I)–(VI), building
`c_2` and setting `Trans M := s_1 c_2 b_1`; reduced multi; non-reduced ⟶
`Trans (Red M)`). The key missing primitive is **`scb_replace t_1 c_1 c_2`** =
`t_1` with its scb-marked principal subterm `c_1` (on the rightmost spine, where
the suffix is all `)`) replaced by `c_2` (i.e. `s_1 c_2 b_1`); a constructive
(function, not predicate) scb-decomposition is also needed. `Trans` connects to
the pair-sequence side, so it lives in `pss_paper` (imports `pss_defs`). Then
§7.4 (admissible parent relation `<_M^NextAdm`) and all the §7 statements; §8
(expansion rules under (I)–(VI) and the main result) depends entirely on
`Trans` / `Mark`. The well-foundedness of `(OT_B, <)` ([Buc1] Lemma 2.2) is the
eventual source of termination.

### Formalizing Lemma 2.2 (well-foundedness) — two routes, one recommended

The article cites [Buc1] Lemma 2.2 without proof, so leaving `buc1_2_2_OT_B_wf`
as a cited `sorry` is *faithful*. If we want the internal proof, note that
[Buc1] (1986) itself proves wf **semantically** (Lemma 2.2(c)+2.3: `o(·)` is an
order-embedding of `(OT,<)` into a set of genuine ordinals `C₀(ε_{Ω_ω+1})`, so
wf pulls back from the ordinals). That is **not** the route our `wds_`/`wcl_`
code takes. Two options:

- **Route D — distinguished sets (`ausgezeichnete Mengen`), what `wds_`/`wcl_`
  do.** A *finitary/syntactic* well-ordering proof: pure `Wellfounded.acc`/`wf`
  on the term system, **no ordinals, no set theory, no `Isabelle/ZF`, no
  `ZFC_in_HOL`**. This is why proof theorists invented the method — to avoid
  semantic ordinals. Source proof: **Buchholz–Schütte monograph Ch. IV §1–§4**
  (refined in the Buchholz Hydra paper — the companion `[1]`, held locally as
  `../1984_Buchholz_BHydra_an-independence-result-for-...pdf` = *An independence
  result for (Π¹₁-CA)+BI*, APAL 33 (1987) 131–155). The wall is the impredicative
  accessibility step (`wcl_upper`): a proof-engineering difficulty, **not** a
  logical-strength one — HOL is far strong enough. **Recommended: continue
  Route D in plain HOL**, transcribing the Ch. IV / `[1]` distinguished-sets
  accessibility argument into `wcl_upper`.
- **Route S — semantic (the 1986 paper's own proof).** Define the `ψ_ν`
  collapsing functions on *real* ordinals (up to `ε_{Ω_ω+1}`, needs cardinals
  `ℵ_1..ℵ_ω`), prove `o : OT → Ord` order-preserving, pull back wf. This needs a
  set-theory library — **`ZFC_in_HOL`** (Paulson, AFP; ZFC inside HOL, so it
  interoperates), **not `Isabelle/ZF`** (a separate object logic that cannot be
  combined with this HOL development). Bigger, different undertaking; only worth
  it if we deliberately pivot away from distinguished sets.

**`Isabelle/ZF` is not useful here** either way: object logics don't interoperate,
so it would mean re-doing the entire HOL development. No existing Isabelle
formalization reaches ψ₀(ε_{Ω_ω+1}) (the AFP hereditary-multiset ordinals stop at
ε₀); a full Buchholz-ψ well-ordering would be frontier work — the Route-D
transcription is the shortest path.

## Empirical validation (`python/buchholz.py`, `python/buchholz_audit.py`)

A faithful Python model of the notation system (terms, `<`, `+`, `T_v`, `G_u`,
`OT`, `dom`, `a[z]`). Enumerated small terms (indices 0–2, depth 2):

- **Lemma 2.1** (`<` strict linear order: irreflexive / transitive / trichotomous)
  — **validated**, 0 failures. This is the well-foundedness crux.
- **`[]` cases** `0/1/2/3/5` and `([].4)(i),(iii)` — validated against
  `dom`/order and known values (e.g. `(D_ω 0)[n]=D_{n+1}0`).
- **`([].4)(ii)` [Buc2] modification — NOT yet validated.** Implemented verbatim
  from the footnote (content.md 6427), but Lemma 3.2a (`a[z] < a`) FAILS for
  non-principal `b` (e.g. `a = D_0((D_1 0, D_1 0))`): the outer `b[x_n]` is
  applied with `x_n ∈ T_{u+1} ∉ dom(b)=T_u`. The [Buc1] original
  `a[n]=D_v b[D_u b[1]]` keeps the outer argument `D_u`-wrapped (`∈ T_u`); the
  literal [Buc2] reading loses that. **TODO**: study [Buc1] p.203 to pin the
  intended reading before using case-(ii) fundamental sequences in any audit.
