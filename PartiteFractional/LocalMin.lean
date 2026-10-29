/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Minimizer

/-!
# Consequences of `ℓ¹`-minimality (inequalities (3)–(6) of Lemma 3.4)

Let `ψ` be a translate of minimum `ℓ¹` norm. Translating `ψ` further by `±ε` on a vertex set `S`,
with `ε` smaller than every nonzero `|ψ(e)|`, changes the norm by `ε` times a signed count of the
edges crossing `S`. Minimality makes both changes nonnegative; with `K₃`-divisibility (as many
edges leave `S` forwards as enter it) this gives, for every `S`,
`n_in(S) - n_out(S) ≤ z_out(S)` and `n_out(S) - n_in(S) ≤ z_in(S)`, where `z` and `n` count the
zero and negative edges `uv` with `u ≺ v` leaving (`u ∈ S`, `v ∉ S`) or entering `S`.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {part : V → Fin 3}

/-- The ordered pairs `(u, v)` with `uv ∈ E(G)` and `u ≺ v`: each edge once. -/
def arcs (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin 3) : Finset (V × V) :=
  univ.filter fun x => G.Adj x.1 x.2 ∧ Prec part x.1 x.2

theorem sum_edgeFinset_eq_sum_arcs (hG : IsTripartite G part) (f : Sym2 V → ℝ) :
    ∑ e ∈ G.edgeFinset, f e = ∑ x ∈ arcs G part, f s(x.1, x.2) := by
  rw [sum_edgeFinset_eq_sum_prec hG, arcs, sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

/-- The indicator of a proposition, as a real number. -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- The change of `|x|` under `x ↦ x + ε` for small `ε > 0`. -/
noncomputable def sgnUp (x : ℝ) : ℝ := ind (x = 0) + ind (0 < x) - ind (x < 0)

/-- The change of `|x|` under `x ↦ x - ε` for small `ε > 0`. -/
noncomputable def sgnDown (x : ℝ) : ℝ := ind (x = 0) - ind (0 < x) + ind (x < 0)

theorem abs_add_small {x ε : ℝ} (hε : 0 < ε) (hx : x = 0 ∨ ε < |x|) :
    |x + ε| = |x| + ε * sgnUp x := by
  unfold sgnUp ind
  rcases lt_trichotomy x 0 with h | rfl | h
  · have h1 : ε < -x := by
      rcases hx with h' | h'
      · exact absurd h' h.ne
      · rwa [abs_of_neg h] at h'
    rw [abs_of_neg h, abs_of_neg (by linarith)]
    simp [h, h.ne, not_lt.2 h.le]
    ring
  · simp [abs_of_pos hε]
  · rw [abs_of_pos h, abs_of_pos (by linarith)]
    simp [h, h.ne', not_lt.2 h.le]

theorem abs_sub_small {x ε : ℝ} (hε : 0 < ε) (hx : x = 0 ∨ ε < |x|) :
    |x - ε| = |x| + ε * sgnDown x := by
  unfold sgnDown ind
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [abs_of_neg h, abs_of_neg (by linarith)]
    simp [h, h.ne, not_lt.2 h.le]
    ring
  · simp [abs_of_pos hε]
  · have h1 : ε < x := by
      rcases hx with h' | h'
      · exact absurd h' h.ne'
      · rwa [abs_of_pos h] at h'
    rw [abs_of_pos h, abs_of_pos (by linarith)]
    simp [h, h.ne', not_lt.2 h.le]
    ring

/-- A positive `ε` below every nonzero `|ψ(e)|` on the edges. -/
theorem exists_small (ψ : Sym2 V → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ e ∈ G.edgeFinset, ψ e = 0 ∨ ε < |ψ e| := by
  classical
  set T := (G.edgeFinset.filter fun e => ψ e ≠ 0).image fun e => |ψ e|
  by_cases hT : T.Nonempty
  · have hpos : 0 < T.min' hT := by
      obtain ⟨e, he, hm⟩ := mem_image.1 (T.min'_mem hT)
      rw [← hm]
      exact abs_pos.2 (mem_filter.1 he).2
    refine ⟨T.min' hT / 2, by positivity, fun e he => ?_⟩
    by_cases h0 : ψ e = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      have : T.min' hT ≤ |ψ e| := T.min'_le _ (mem_image.2 ⟨e, mem_filter.2 ⟨he, h0⟩, rfl⟩)
      linarith
  · refine ⟨1, one_pos, fun e he => Or.inl ?_⟩
    by_contra h0
    exact hT ⟨_, mem_image.2 ⟨e, mem_filter.2 ⟨he, h0⟩, rfl⟩⟩

/-- `ε` times the indicator of `S`. -/
noncomputable def bump (S : Finset V) (ε : ℝ) : V → ℝ := fun v => if v ∈ S then ε else 0

theorem shift_bump_arc {u v : V} (h : Prec part u v) (S : Finset V) (ε : ℝ) :
    shift part (bump S ε) s(u, v) = ε * (ind (v ∈ S) - ind (u ∈ S)) := by
  simp only [shift_mk, h, ite_true, bump, ind]
  split_ifs <;> ring

/-- The signed crossing count governing the change of the norm under `bump S ε`. -/
noncomputable def crossUp (ψ : Sym2 V → ℝ) (S : Finset V) (x : V × V) : ℝ :=
  ind (x.1 ∉ S ∧ x.2 ∈ S) * sgnUp (ψ s(x.1, x.2)) +
    ind (x.1 ∈ S ∧ x.2 ∉ S) * sgnDown (ψ s(x.1, x.2))

/-- The signed crossing count governing the change of the norm under `bump S (-ε)`. -/
noncomputable def crossDown (ψ : Sym2 V → ℝ) (S : Finset V) (x : V × V) : ℝ :=
  ind (x.1 ∉ S ∧ x.2 ∈ S) * sgnDown (ψ s(x.1, x.2)) +
    ind (x.1 ∈ S ∧ x.2 ∉ S) * sgnUp (ψ s(x.1, x.2))

theorem abs_translate_bump (hG : IsTripartite G part) {ψ : Sym2 V → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ e ∈ G.edgeFinset, ψ e = 0 ∨ ε < |ψ e|) (S : Finset V) {x : V × V}
    (hx : x ∈ arcs G part) :
    |translate part ψ (bump S ε) s(x.1, x.2)| = |ψ s(x.1, x.2)| + ε * crossUp ψ S x ∧
      |translate part ψ (bump S (-ε)) s(x.1, x.2)| = |ψ s(x.1, x.2)| + ε * crossDown ψ S x := by
  obtain ⟨hadj, hprec⟩ := (mem_filter.1 hx).2
  have hs := hsmall s(x.1, x.2) (by simpa using hadj)
  have a1 := abs_add_small hε hs
  have a2 := abs_sub_small hε hs
  simp only [translate, shift_bump_arc hprec, crossUp, crossDown, ind]
  by_cases h1 : x.1 ∈ S <;> by_cases h2 : x.2 ∈ S <;>
    simp only [h1, h2, not_true_eq_false, not_false_eq_true, and_self, and_true, and_false,
      true_and, false_and, ite_true, ite_false] <;>
    first
    | (simp; done)
    | (ring_nf at a1 a2 ⊢; exact ⟨by linarith, by linarith⟩)

/-- **Minimality, inequality (3) and its mirror image.** -/
theorem crossing_nonneg (hG : IsTripartite G part) {ψ : Sym2 V → ℝ}
    (hmin : ∀ q : V → ℝ, l1 G ψ ≤ l1 G (translate part ψ q)) (S : Finset V) :
    0 ≤ ∑ x ∈ arcs G part, crossUp ψ S x ∧ 0 ≤ ∑ x ∈ arcs G part, crossDown ψ S x := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small (G := G) ψ
  have hup := hmin (bump S ε)
  have hdown := hmin (bump S (-ε))
  simp only [l1, sum_edgeFinset_eq_sum_arcs hG] at hup hdown
  rw [sum_congr rfl fun x hx => (abs_translate_bump hG hε hsmall S hx).1, sum_add_distrib,
    ← mul_sum] at hup
  rw [sum_congr rfl fun x hx => (abs_translate_bump hG hε hsmall S hx).2, sum_add_distrib,
    ← mul_sum] at hdown
  exact ⟨(mul_nonneg_iff_of_pos_left hε).1 (by linarith),
    (mul_nonneg_iff_of_pos_left hε).1 (by linarith)⟩

theorem sum_arcs_eq (f : V × V → ℝ) :
    ∑ x ∈ arcs G part, f x = ∑ u, ∑ v, if G.Adj u v ∧ Prec part u v then f (u, v) else 0 := by
  rw [arcs, sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

/-- With `K₃`-divisibility, as many edges leave `S` forwards as enter it. -/
theorem card_out_eq_card_in (hdiv : IsK3Divisible G part) (S : Finset V) :
    ∑ x ∈ arcs G part, ind (x.1 ∈ S ∧ x.2 ∉ S) = ∑ x ∈ arcs G part, ind (x.1 ∉ S ∧ x.2 ∈ S) := by
  have hsplit1 : ∀ x : V × V,
      ind (x.1 ∈ S) = ind (x.1 ∈ S ∧ x.2 ∉ S) + ind (x.1 ∈ S ∧ x.2 ∈ S) := by
    intro x; unfold ind; by_cases h1 : x.1 ∈ S <;> by_cases h2 : x.2 ∈ S <;> simp [h1, h2]
  have hsplit2 : ∀ x : V × V,
      ind (x.2 ∈ S) = ind (x.1 ∉ S ∧ x.2 ∈ S) + ind (x.1 ∈ S ∧ x.2 ∈ S) := by
    intro x; unfold ind; by_cases h1 : x.1 ∈ S <;> by_cases h2 : x.2 ∈ S <;> simp [h1, h2]
  have hfst : ∑ x ∈ arcs G part, ind (x.1 ∈ S) =
      ∑ u, ind (u ∈ S) * (degTo G part u (part u + 1) : ℝ) := by
    rw [sum_arcs_eq]
    refine sum_congr rfl fun u _ => ?_
    rw [← card_prec_right, natCast_card_filter, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  have hsnd : ∑ x ∈ arcs G part, ind (x.2 ∈ S) =
      ∑ v, ind (v ∈ S) * (degTo G part v (part v - 1) : ℝ) := by
    rw [sum_arcs_eq, sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← card_prec_left, natCast_card_filter, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  have heq : ∑ x ∈ arcs G part, ind (x.1 ∈ S) = ∑ x ∈ arcs G part, ind (x.2 ∈ S) := by
    rw [hfst, hsnd]
    exact sum_congr rfl fun v _ => by rw [hdiv v]
  simp only [hsplit1, hsplit2, sum_add_distrib] at heq
  linarith

/-- Crossing counts of `S` by sign class: `zOut`, `pOut`, `nOut`, `zIn`, `pIn`, `nIn`. -/
noncomputable def crossCount (ψ : Sym2 V → ℝ) (S : Finset V) (out : Bool) (P : ℝ → Prop)
    [DecidablePred P] : ℝ :=
  ∑ x ∈ arcs G part,
    (if out then ind (x.1 ∈ S ∧ x.2 ∉ S) else ind (x.1 ∉ S ∧ x.2 ∈ S)) * ind (P (ψ s(x.1, x.2)))

theorem ind_split (y : ℝ) : ind (y = 0) + ind (0 < y) + ind (y < 0) = 1 := by
  unfold ind
  rcases lt_trichotomy y 0 with h | rfl | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp
  · simp [h, h.ne', not_lt.2 h.le]

variable (G part) in
/-- **Inequalities (5) and (6) of Lemma 3.4.** For a translate of minimum `ℓ¹` norm of a
`K₃`-divisible tripartite graph, `n_in(S) - n_out(S) ≤ z_out(S)` and
`n_out(S) - n_in(S) ≤ z_in(S)` for every vertex set `S`. -/
theorem crossing_ineqs (hG : IsTripartite G part) (hdiv : IsK3Divisible G part)
    {ψ : Sym2 V → ℝ} (hmin : ∀ q : V → ℝ, l1 G ψ ≤ l1 G (translate part ψ q)) (S : Finset V) :
    crossCount (G := G) (part := part) ψ S false (· < 0) -
        crossCount (G := G) (part := part) ψ S true (· < 0) ≤
      crossCount (G := G) (part := part) ψ S true (· = 0) ∧
    crossCount (G := G) (part := part) ψ S true (· < 0) -
        crossCount (G := G) (part := part) ψ S false (· < 0) ≤
      crossCount (G := G) (part := part) ψ S false (· = 0) := by
  obtain ⟨hup, hdown⟩ := crossing_nonneg hG hmin S
  have hk := card_out_eq_card_in hdiv S
  have hsplitOut : ∑ x ∈ arcs G part, ind (x.1 ∈ S ∧ x.2 ∉ S) =
      crossCount (G := G) (part := part) ψ S true (· = 0) +
        crossCount (G := G) (part := part) ψ S true (0 < ·) +
        crossCount (G := G) (part := part) ψ S true (· < 0) := by
    simp only [crossCount, ite_true, ← sum_add_distrib, ← mul_add, ind_split, mul_one]
  have hsplitIn : ∑ x ∈ arcs G part, ind (x.1 ∉ S ∧ x.2 ∈ S) =
      crossCount (G := G) (part := part) ψ S false (· = 0) +
        crossCount (G := G) (part := part) ψ S false (0 < ·) +
        crossCount (G := G) (part := part) ψ S false (· < 0) := by
    simp only [crossCount, Bool.false_eq_true, ite_false, ← sum_add_distrib, ← mul_add,
      ind_split, mul_one]
  have hU : ∑ x ∈ arcs G part, crossUp ψ S x =
      (crossCount (G := G) (part := part) ψ S false (· = 0) +
        crossCount (G := G) (part := part) ψ S false (0 < ·) -
        crossCount (G := G) (part := part) ψ S false (· < 0)) +
      (crossCount (G := G) (part := part) ψ S true (· = 0) -
        crossCount (G := G) (part := part) ψ S true (0 < ·) +
        crossCount (G := G) (part := part) ψ S true (· < 0)) := by
    simp only [crossCount, crossUp, sgnUp, sgnDown, Bool.false_eq_true, ite_true, ite_false,
      ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  have hD : ∑ x ∈ arcs G part, crossDown ψ S x =
      (crossCount (G := G) (part := part) ψ S false (· = 0) -
        crossCount (G := G) (part := part) ψ S false (0 < ·) +
        crossCount (G := G) (part := part) ψ S false (· < 0)) +
      (crossCount (G := G) (part := part) ψ S true (· = 0) +
        crossCount (G := G) (part := part) ψ S true (0 < ·) -
        crossCount (G := G) (part := part) ψ S true (· < 0)) := by
    simp only [crossCount, crossDown, sgnUp, sgnDown, Bool.false_eq_true, ite_true, ite_false,
      ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  constructor <;> linarith

end ABLP
