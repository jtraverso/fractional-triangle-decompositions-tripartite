# Mathlib definitions used in the statements

The statements in [`ABLPChallenge.lean`](ABLPChallenge.lean) use the following
Mathlib definitions. They are reproduced verbatim from Mathlib at the pinned revision
`c55e6e786f49471c72fbddbec5415808896aec1e` (Lean `v4.35.0-rc3`).

## `SimpleGraph` — `Mathlib/Combinatorics/SimpleGraph/Basic.lean:95`

```lean
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## `SimpleGraph.IsClique` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:48`

```lean
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
```

## `SimpleGraph.IsNClique` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:246`

```lean
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n
```

## `SimpleGraph.cliqueFinset` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:854`

```lean
def cliqueFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNClique n s}
```

## `SimpleGraph.edgeFinset` — `Mathlib/Combinatorics/SimpleGraph/Finite.lean:59`

```lean
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet
```

## `Sym2` — `Mathlib/Data/Sym/Sym2.lean:100`

```lean
abbrev Sym2 (α : Type u) := Quot (Sym2.Rel α)
```

`s(a, b)` denotes the class of the pair `(a, b)`.

## `sSup` on `ℝ` — `Mathlib/Algebra/Order/Archimedean/Real/Basic.lean:115`

```lean
noncomputable instance : SupSet ℝ :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩
```

In particular `Real.sSup_empty : sSup (∅ : Set ℝ) = 0` (line 168), the convention of the article
for the supremum in `M`.

## `Set.Ioc` and `Set.Icc` — `Mathlib/Order/Interval/Set/Defs.lean:63`, `:76`

```lean
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }
```

## `AntitoneOn` — `Mathlib/Order/Monotone/Defs.lean:80`

```lean
def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a
```
