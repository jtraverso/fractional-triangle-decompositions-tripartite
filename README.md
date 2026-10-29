# Fractional triangle decompositions of dense tripartite graphs in Lean 4

Author and maintainer of the formalization: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0
(see `LICENSE`).

A Lean 4 / Mathlib formalization of the main results of

> J. Allsop, C. Bowtell, T. Lesgourgues and K. Petrova, *Improved bounds on completion of partial
> Latin squares*, arXiv:2609.37877 (30 September 2026), preprint v1.

The formalization is by a different author than the article and has not been reviewed by its
authors.

A tripartite graph is a simple graph `G` on a finite type `V` together with `part : V → Fin 3`
such that adjacent vertices lie in different parts; it is a spanning subgraph of `K_{n,n,n}` when
every part has `n` vertices. `G` is `K₃`-divisible when every vertex has as many neighbours in
each of the other two parts, and its minimum partite degree is the least number of neighbours a
vertex has in another part.

| Lean (namespace `ABLP2026`) | Statement |
|---|---|
| `theorem_1_3` | There is `η > 0` such that every `K₃`-divisible spanning subgraph of `K_{n,n,n}` with minimum partite degree at least `(0.769 − η)n` has a fractional triangle decomposition. Proved with `η = 1/20000`. |
| `lemma_2_1` | (Farkas) `G` has no fractional triangle decomposition iff it has a triangle-covered, totally negative edge weighting. |
| `proposition_3_1` | A triangle-covered weighting of a `K₃`-divisible tripartite graph can be replaced, at cost at most `ε` in total weight, by a triangle-covered, balanced, untied and nonzero one. |
| `corollary_3_5` | A `K₃`-divisible tripartite graph has no fractional triangle decomposition iff it has a triangle-covered, totally negative, balanced, untied and nonzero weighting. |
| `proposition_4_2` | In the `f`-proportional discharging (Definition 4.1), a blue edge sends at most its own weight. |
| `proposition_4_3` | A red edge `uv` with `d_u ≥ d_v` receives at least `g_d(d_u/n, d_v/n)·|φ(uv)|`. |
| `proposition_4_4` | For the function `f` of equation (8), `g_d(x, y) ≥ 1` for all `0 ≤ d ≤ 0.231 + η` and all `x ≥ y` in `(0, 1)` with `x + y ≤ 1`. |

Corollary 1.4 of the article (completion of partial Latin squares with at most `0.231n`
occurrences per row, column and symbol) is not formalized here: it combines Theorem 1.3 with the
fractional-to-exact transfer of Barber, Kühn, Lo, Osthus and Taylor for tripartite graphs.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the seven statements; it imports only
  Mathlib.
- [`Solution.lean`](Solution.lean): the same definitions, copied verbatim, and a proof of each
  statement from the library.
- [`PartiteFractional/`](PartiteFractional): the library (namespace `ABLP`).
- [`scripts/bernstein44.py`](scripts/bernstein44.py): regenerates
  `PartiteFractional/Bernstein44.lean` (see below).
- [`comparator.json`](comparator.json), [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md),
  [`formalization.yaml`](formalization.yaml).

## How the proof is organized

| Module | Content |
|---|---|
| `Farkas` | Lemma 2.1, from the Farkas lemma `FiniteLP.farkas_ge` of the registered Erdős #81 Paper I (v2). |
| `Tripartite`, `Minimizer`, `LocalMin` | Lemma 3.3 (translations by a vertex potential keep the total weight and the triangle sums), a potential minimizing the `ℓ¹` norm, and the crossing inequalities (5) and (6). |
| `IntFlow`, `Network`, `Colouring`, `Lemma34` | Claim 3.4.1 and Lemma 3.4: an integral maximum flow in the auxiliary network (built on the max-flow/min-cut theorem of the registered Dross entry) gives a red-balanced set containing every negative edge; one with fewest edges contains no triangle. |
| `Balanced` | Proposition 3.1 and Corollary 3.5. |
| `Discharging` | Definition 4.1, Propositions 4.2 and 4.3, and `fracDecomp_of_gd`: Theorem 1.3 from any `f` with `g_d ≥ 1`. |
| `Bernstein44`, `Numerics` | Proposition 4.4 and Theorem 1.3. |

Two steps differ from the article.

- **Proposition 3.1, last step.** The article makes the weighting untied by ordering the edges
  and stretching them by powers of `ν`. Here `ψ = φ_p + ν·a`, where `a` is `−(i + 1)` on the red
  set and `2M + i` off it for an injective numbering `i` of the edges; `ψ` is negative exactly on
  the red set for every `ν > 0`, triangle-covered because every triangle has an edge off the red
  set, and injective on the edges except for finitely many `ν`.
- **Proposition 4.4.** The article bounds `M(a, b) ≥ m(a)` by a case analysis and reports the
  minima in Case 3 from a numerical minimisation (its Appendices B and C). Here
  `M(a, b) ≥ √70/(3√a) − 5/3 − 1/(6a)` is proved for every `a > 0` by the AM–GM inequality, and
  the two-variable inequalities of Case 3 are proved exactly: with `x = t²` and `y = s²` and
  `√70 ≥ 8.3666` they become `P(s, t) ≥ 0` for two polynomials of degree 4 in each variable, and
  `P` is written on every piece of a subdivision of the box (20 pieces and 5 pieces) as a
  combination with nonnegative rational coefficients of the Bernstein products
  `(s − a)^i (b − s)^(4−i) (t − c)^j (e − t)^(4−j)`. `scripts/bernstein44.py` computes the
  subdivisions and coefficients in exact rational arithmetic and writes the Lean file; Lean checks
  each identity with `ring` (`linear_combination`). Everything is proved at `d = 0.23105`, where
  the minimum of the bound is about `1.00024`, and transferred to smaller `d` by monotonicity.

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`. `lake build`; no `sorry`;
`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for all seven statements;
the elaborated statements and definitions of the Challenge and the Solution are identical
(`pp.all`).

```
lake build
```

The first build also compiles the two pinned dependencies.
