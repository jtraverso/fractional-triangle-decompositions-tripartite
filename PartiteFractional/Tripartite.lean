/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Farkas

/-!
Draft: tripartite setting and Lemma 3.3 of Allsop–Bowtell–Lesgourgues–Petrova (translation of an
edge weighting by a vertex potential).
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (part : V → Fin 3)

/-- `G` is tripartite with parts `part ⁻¹' {i}`. -/
def IsTripartite : Prop := ∀ u v, G.Adj u v → part u ≠ part v

/-- The number of neighbours of `v` in part `i`. -/
def degTo (v : V) (i : Fin 3) : ℕ := #{u | G.Adj v u ∧ part u = i}

/-- `K₃`-divisibility of a tripartite graph: every vertex has as many neighbours in each of the
other two parts. -/
def IsK3Divisible : Prop := ∀ v, degTo G part v (part v + 1) = degTo G part v (part v - 1)

/-- `u ≺ v`: `v` is in the part after the part of `u` (indices modulo 3). -/
def Prec (u v : V) : Prop := part v = part u + 1

instance : DecidableRel (Prec part) := fun u v => inferInstanceAs (Decidable (part v = _))

theorem not_prec_of_prec {u v : V} (h : Prec part u v) : ¬ Prec part v u := by
  unfold Prec at *
  rw [h]
  generalize part u = a
  revert a
  decide

theorem prec_or_prec {u v : V} (h : part u ≠ part v) : Prec part u v ∨ Prec part v u := by
  unfold Prec
  generalize part u = a at *
  generalize part v = b at *
  revert a b
  decide

/-- The change of an edge weight under the potential `p`: `p v - p u` on an edge `uv` with
`u ≺ v`. -/
noncomputable def shift (p : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => if Prec part u v then p v - p u else if Prec part v u then p u - p v else 0,
    fun u v => by
      by_cases h : Prec part u v
      · simp [h, not_prec_of_prec part h]
      · by_cases h' : Prec part v u <;> simp [h, h']⟩

@[simp] theorem shift_mk (p : V → ℝ) (u v : V) :
    shift part p s(u, v) =
      if Prec part u v then p v - p u else if Prec part v u then p u - p v else 0 := rfl

/-- The translation `φ_p(uv) = φ(uv) - p(u) + p(v)` for `u ≺ v`. -/
noncomputable def translate (φ : Sym2 V → ℝ) (p : V → ℝ) : Sym2 V → ℝ :=
  fun e => φ e + shift part p e

variable {G part}

/-- Each edge of a tripartite graph is counted once as an ordered pair `(u, v)` with `u ≺ v`. -/
theorem sum_edgeFinset_eq_sum_prec (hG : IsTripartite G part) (f : Sym2 V → ℝ) :
    ∑ e ∈ G.edgeFinset, f e =
      ∑ u, ∑ v, if G.Adj u v ∧ Prec part u v then f s(u, v) else 0 := by
  rw [← Finset.sum_product' (f := fun u v => if G.Adj u v ∧ Prec part u v then f s(u, v) else 0),
    ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ => s(x.1, x.2)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ h
    simp only [mem_filter, mem_product, mem_univ, true_and] at h
    simpa using h.1
  · rintro ⟨u, v⟩ h ⟨u', v'⟩ h' heq
    simp only [mem_filter, mem_product, mem_univ, true_and] at h h'
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd h'.2 (not_prec_of_prec part h.2)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      rcases prec_or_prec part (hG a b hab) with h | h
      · exact ⟨(a, b), by simp [hab, h], rfl⟩
      · exact ⟨(b, a), by simp [hab.symm, h], Sym2.eq_swap⟩
  · intro _ _
    rfl

theorem prec_iff_left (u v : V) : Prec part u v ↔ part u = part v - 1 := by
  unfold Prec
  generalize part u = a
  generalize part v = b
  revert a b
  decide

/-- `∑ᵤ [u ~ v, u ≺ v] = d(v, V_{i-1})`. -/
theorem card_prec_left (v : V) :
    #{u | G.Adj u v ∧ Prec part u v} = degTo G part v (part v - 1) := by
  unfold degTo
  congr 1
  ext u
  simp [prec_iff_left, G.adj_comm]

theorem card_prec_right (u : V) :
    #{v | G.Adj u v ∧ Prec part u v} = degTo G part u (part u + 1) := by
  unfold degTo Prec
  rfl

/-- **Lemma 3.3, first part.** Translation preserves the total weight of a `K₃`-divisible
tripartite graph. -/
theorem sum_shift_eq_zero (hG : IsTripartite G part) (hdiv : IsK3Divisible G part)
    (p : V → ℝ) : ∑ e ∈ G.edgeFinset, shift part p e = 0 := by
  rw [sum_edgeFinset_eq_sum_prec hG]
  have h1 : ∀ u v, (if G.Adj u v ∧ Prec part u v then shift part p s(u, v) else 0) =
      (if G.Adj u v ∧ Prec part u v then p v else 0) -
        (if G.Adj u v ∧ Prec part u v then p u else 0) := by
    intro u v
    split_ifs with h
    · simp [h.2]
    · ring
  simp_rw [h1, sum_sub_distrib]
  rw [sum_comm (f := fun u v => if G.Adj u v ∧ Prec part u v then p v else 0)]
  have h2 : ∀ v, ∑ u, (if G.Adj u v ∧ Prec part u v then p v else 0) =
      (degTo G part v (part v - 1) : ℝ) * p v := by
    intro v
    rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, card_prec_left]
  have h3 : ∀ u, ∑ v, (if G.Adj u v ∧ Prec part u v then p u else 0) =
      (degTo G part u (part u + 1) : ℝ) * p u := by
    intro u
    rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, card_prec_right]
  simp_rw [h2, h3]
  rw [← sum_sub_distrib]
  exact sum_eq_zero fun v _ => by rw [hdiv v]; ring

theorem sum_translate (hG : IsTripartite G part) (hdiv : IsK3Divisible G part)
    (φ : Sym2 V → ℝ) (p : V → ℝ) :
    ∑ e ∈ G.edgeFinset, translate part φ p e = ∑ e ∈ G.edgeFinset, φ e := by
  simp only [translate, sum_add_distrib, sum_shift_eq_zero hG hdiv, add_zero]

theorem fin3_cyclic (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (y = x + 1 ∧ z = y + 1 ∧ x = z + 1) ∨ (x = y + 1 ∧ y = z + 1 ∧ z = x + 1) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> first | decide | (exfalso; simp_all)

/-- **Lemma 3.3, second part.** The shift vanishes on every triangle of a tripartite graph. -/
theorem sum_shift_triangle (hG : IsTripartite G part) (p : V → ℝ) {t : Finset V}
    (ht : t ∈ G.cliqueFinset 3) : ∑ e ∈ edgesIn G t, shift part p e = 0 := by
  rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  rw [sum_edgesIn_triple G hab hac hbc]
  rcases fin3_cyclic _ _ _ (hG a b hab) (hG a c hac) (hG b c hbc) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have pab : Prec part a b := h1
    have pbc : Prec part b c := h2
    have pca : Prec part c a := h3
    simp only [shift_mk, pab, pbc, pca, ite_true, ite_eq_right (not_prec_of_prec part pca)]
    ring
  · have pba : Prec part b a := h1
    have pcb : Prec part c b := h2
    have pac : Prec part a c := h3
    simp only [shift_mk, pba, pcb, pac, ite_true, ite_eq_right (not_prec_of_prec part pba),
      ite_eq_right (not_prec_of_prec part pcb)]
    ring

/-- **Lemma 3.3.** A translate of a triangle-covered weighting of a `K₃`-divisible tripartite
graph is triangle-covered and has the same total weight. -/
theorem translate_triangleCovered (hG : IsTripartite G part) {φ : Sym2 V → ℝ}
    (hφ : IsTriangleCovered G φ) (p : V → ℝ) : IsTriangleCovered G (translate part φ p) := by
  intro t ht
  simp only [translate, sum_add_distrib, sum_shift_triangle hG p ht, add_zero]
  exact hφ t ht

end ABLP
