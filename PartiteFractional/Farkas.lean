/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ErdosPaperI.FiniteLPDuality

/-!
Draft: Allsop–Bowtell–Lesgourgues–Petrova, Lemma 2.1 (Farkas' lemma for fractional triangle
decompositions, after Delcourt–Postle, Lemma 2.2).
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G` with both endpoints in the vertex set `t`. -/
def edgesIn (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- A fractional triangle decomposition of `G`. -/
def IsFracTriangleDecomp (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t = 1

/-- Every triangle of `G` has nonnegative total weight. -/
def IsTriangleCovered (φ : Sym2 V → ℝ) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, 0 ≤ ∑ e ∈ edgesIn G t, φ e

/-- The total weight of the edges of `G` is negative. -/
def IsTotallyNegative (φ : Sym2 V → ℝ) : Prop :=
  ∑ e ∈ G.edgeFinset, φ e < 0

theorem edgesIn_subset (t : Finset V) : edgesIn G t ⊆ G.edgeFinset := filter_subset _ _

/-- The edges of `G` inside a triangle `{a, b, c}`. -/
theorem edgesIn_triple {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    edgesIn G {a, b, c} = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [edgesIn, mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp,
      forall_eq, mem_insert, mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨hxy, hx, hy⟩
      have := hxy.ne
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp_all [G.adj_symm]

/-- The sum of a function over the edges of a triangle `{a, b, c}`. -/
theorem sum_edgesIn_triple {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (f : Sym2 V → ℝ) : ∑ e ∈ edgesIn G {a, b, c}, f e = f s(a, b) + f s(a, c) + f s(b, c) := by
  have h1 := hab.ne
  have h2 := hac.ne
  have h3 := hbc.ne
  rw [edgesIn_triple G hab hac hbc, sum_insert, sum_insert, sum_singleton, add_assoc]
  · simp [h1, h3.symm]
  · simp [h1, h2, h3, h1.symm]

/-- The incidence coefficient of edge `e` and vertex set `t`: one when `t` is a triangle of `G`
containing `e`. -/
noncomputable def inc (e : Sym2 V) (t : Finset V) : ℝ :=
  if t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ edgesIn G t) then 1 else 0

theorem sum_inc_mul (e : Sym2 V) (x : Finset V → ℝ) :
    ∑ t, inc G e t * x t = ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, x t := by
  simp only [inc, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_mul_inc (t : Finset V) (y : Sym2 V → ℝ) (ht : t ∈ G.cliqueFinset 3) :
    ∑ e, inc G e t * y e = ∑ e ∈ edgesIn G t, y e := by
  simp only [inc, mem_filter, ht, true_and, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_inc_of_not_mem (t : Finset V) (y : Sym2 V → ℝ) (ht : t ∉ G.cliqueFinset 3) :
    ∑ e, inc G e t * y e = 0 := by
  simp [inc, ht]

/-- Weighting by a fractional decomposition: `∑ₑ φ(e) = ∑ₜ w(t) ∑_{e ⊆ t} φ(e)`. -/
theorem sum_eq_sum_triangles {w : Finset V → ℝ} (hw : IsFracTriangleDecomp G w)
    (φ : Sym2 V → ℝ) :
    ∑ e ∈ G.edgeFinset, φ e = ∑ t ∈ G.cliqueFinset 3, w t * ∑ e ∈ edgesIn G t, φ e := by
  calc ∑ e ∈ G.edgeFinset, φ e
      = ∑ e ∈ G.edgeFinset, φ e * ∑ t, inc G e t * w t := by
        refine sum_congr rfl fun e he => ?_
        rw [sum_inc_mul, hw.2 e he, mul_one]
    _ = ∑ e, φ e * ∑ t, inc G e t * w t := by
        refine sum_subset (subset_univ _) fun e _ he => ?_
        have : ∀ t, inc G e t = 0 := fun t => by
          simp only [inc, mem_filter]
          rw [ite_eq_right]
          rintro ⟨-, h⟩
          exact he (edgesIn_subset G t h)
        simp [this]
    _ = ∑ t, w t * ∑ e, inc G e t * φ e := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun t _ => sum_congr rfl fun e _ => by ring
    _ = ∑ t ∈ G.cliqueFinset 3, w t * ∑ e ∈ edgesIn G t, φ e := by
        rw [← sum_subset (subset_univ (G.cliqueFinset 3)) fun t _ ht => by
          rw [sum_inc_of_not_mem G t φ ht, mul_zero]]
        exact sum_congr rfl fun t ht => by rw [sum_mul_inc G t φ ht]

/-- **Lemma 2.1** (Farkas' lemma for triangle decompositions). A finite graph has no fractional
triangle decomposition if and only if some edge weighting is triangle-covered and totally
negative. -/
theorem not_fracDecomp_iff :
    (¬ ∃ w, IsFracTriangleDecomp G w) ↔
      ∃ φ : Sym2 V → ℝ, IsTriangleCovered G φ ∧ IsTotallyNegative G φ := by
  constructor
  · intro hno
    -- the system `x ≥ 0`, `A x ≥ 1`, `-A x ≥ -1` on the edges of `G`
    let N : Sym2 V ⊕ Sym2 V → Finset V → ℝ :=
      Sum.elim (fun e t => if e ∈ G.edgeFinset then inc G e t else 0)
        (fun e t => if e ∈ G.edgeFinset then -inc G e t else 0)
    let c : Sym2 V ⊕ Sym2 V → ℝ :=
      Sum.elim (fun e => if e ∈ G.edgeFinset then 1 else 0)
        (fun e => if e ∈ G.edgeFinset then -1 else 0)
    have hinf : ¬ ∃ x : Finset V → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j) := by
      rintro ⟨x, hx0, hx⟩
      refine hno ⟨x, hx0, fun e he => le_antisymm ?_ ?_⟩
      · have := hx (Sum.inr e)
        simp only [N, c, Sum.elim_inr, he, ite_true, neg_mul, sum_neg_distrib] at this
        rw [sum_inc_mul] at this
        linarith
      · have := hx (Sum.inl e)
        simp only [N, c, Sum.elim_inl, he, ite_true] at this
        rwa [sum_inc_mul] at this
    obtain ⟨y, hy0, hyN, hyc⟩ := FiniteLP.farkas_ge N c hinf
    let φ : Sym2 V → ℝ := fun e => y (Sum.inr e) - y (Sum.inl e)
    have hcol : ∀ t, ∑ i, N i t * y i = -∑ e ∈ G.edgeFinset, inc G e t * φ e := by
      intro t
      rw [Fintype.sum_sum_type, ← sum_neg_distrib, ← sum_add_distrib]
      rw [← sum_subset (subset_univ G.edgeFinset) fun e _ he => by
        simp only [N, Sum.elim_inl, Sum.elim_inr, he, ite_false, zero_mul, add_zero]]
      refine sum_congr rfl fun e he => ?_
      simp only [N, Sum.elim_inl, Sum.elim_inr, he, ite_true, φ]
      ring
    have hrow : ∑ i, c i * y i = -∑ e ∈ G.edgeFinset, φ e := by
      rw [Fintype.sum_sum_type, ← sum_neg_distrib, ← sum_add_distrib]
      rw [← sum_subset (subset_univ G.edgeFinset) fun e _ he => by
        simp only [c, Sum.elim_inl, Sum.elim_inr, he, ite_false, zero_mul, add_zero]]
      refine sum_congr rfl fun e he => ?_
      simp only [c, Sum.elim_inl, Sum.elim_inr, he, ite_true, φ]
      ring
    refine ⟨φ, fun t ht => ?_, ?_⟩
    · have h1 := hyN t
      rw [hcol] at h1
      have h2 : ∑ e ∈ G.edgeFinset, inc G e t * φ e = ∑ e, inc G e t * φ e :=
        sum_subset (subset_univ _) fun e _ he => by
          have : inc G e t = 0 := by
            simp only [inc, mem_filter]
            rw [ite_eq_right]
            rintro ⟨-, h⟩
            exact he (edgesIn_subset G t h)
          simp [this]
      rw [h2, sum_mul_inc G t φ ht] at h1
      linarith
    · change ∑ e ∈ G.edgeFinset, φ e < 0
      linarith
  · rintro ⟨φ, hcov, hneg⟩ ⟨w, hw⟩
    have h := sum_eq_sum_triangles G hw φ
    have : 0 ≤ ∑ t ∈ G.cliqueFinset 3, w t * ∑ e ∈ edgesIn G t, φ e :=
      sum_nonneg fun t ht => mul_nonneg (hw.1 t) (hcov t ht)
    exact absurd hneg (by unfold IsTotallyNegative; linarith)

end ABLP
