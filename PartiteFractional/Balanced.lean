/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Lemma34

/-!
# Proposition 3.1 and Corollary 3.5 of Allsop–Bowtell–Lesgourgues–Petrova

A triangle-covered edge weighting of a `K₃`-divisible tripartite graph can be replaced, at an
arbitrarily small cost in total weight, by one that is triangle-covered, balanced (every vertex
meets as many negative edges from the previous part as from the next), untied (injective on the
edges) and nonzero on the edges.

The proof here differs from the paper's in the last step. Take `p` and `R` from Lemma 3.4, number
the edges injectively by `idx`, and put `a(e) = -(idx e + 1)` on `R` and `a(e) = 2M + idx e` off
`R`, where `M` bounds the indices. Then `ψ = φ_p + ν a` is negative exactly on `R` for every
`ν > 0` (so it is balanced and nonzero), every triangle has an edge off `R` and so `∑_T a ≥ 0`
(so `ψ` is triangle-covered), and `ψ` is injective on the edges except for finitely many `ν`.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (part : V → Fin 3)

/-- Every vertex meets as many negative edges from the previous part as from the next. -/
def IsBalanced (ψ : Sym2 V → ℝ) : Prop :=
  ∀ v, #{u | G.Adj u v ∧ part u = part v - 1 ∧ ψ s(u, v) < 0} =
    #{u | G.Adj u v ∧ part u = part v + 1 ∧ ψ s(u, v) < 0}

/-- No two edges have the same weight. -/
def IsUntied (ψ : Sym2 V → ℝ) : Prop :=
  ∀ e ∈ G.edgeFinset, ∀ f ∈ G.edgeFinset, e ≠ f → ψ e ≠ ψ f

/-- No edge has weight zero. -/
def IsNonzero (ψ : Sym2 V → ℝ) : Prop := ∀ e ∈ G.edgeFinset, ψ e ≠ 0

variable {G part}

/-- An injective numbering of `Sym2 V`. -/
noncomputable def idx (e : Sym2 V) : ℕ := (Fintype.equivFin (Sym2 V) e : ℕ)

theorem idx_injective : Function.Injective (idx (V := V)) := fun e f h =>
  (Fintype.equivFin (Sym2 V)).injective (Fin.ext h)

theorem idx_lt (e : Sym2 V) : idx e < Fintype.card (Sym2 V) := (Fintype.equivFin (Sym2 V) e).2

/-- The perturbation coefficients: negative on `R`, larger than twice every negative one in
absolute value off `R`. -/
noncomputable def coef (R : Finset (Sym2 V)) (e : Sym2 V) : ℝ :=
  if e ∈ R then -((idx e : ℝ) + 1) else 2 * Fintype.card (Sym2 V) + idx e

theorem coef_ge (R : Finset (Sym2 V)) (e : Sym2 V) : -(Fintype.card (Sym2 V) : ℝ) ≤ coef R e := by
  have h := idx_lt e
  have h' : (idx e : ℝ) + 1 ≤ Fintype.card (Sym2 V) := by exact_mod_cast h
  unfold coef
  split_ifs
  · linarith
  · have : (0 : ℝ) ≤ idx e := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ Fintype.card (Sym2 V) := Nat.cast_nonneg _
    linarith

theorem coef_ge_of_not_mem {R : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ R) :
    2 * (Fintype.card (Sym2 V) : ℝ) ≤ coef R e := by
  unfold coef
  rw [ite_eq_right he]
  have : (0 : ℝ) ≤ idx e := Nat.cast_nonneg _
  linarith

theorem coef_neg_of_mem {R : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ R) : coef R e < 0 := by
  unfold coef
  rw [ite_eq_left he]
  have : (0 : ℝ) ≤ idx e := Nat.cast_nonneg _
  linarith

theorem coef_pos_of_not_mem {R : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ R) : 0 < coef R e := by
  have := coef_ge_of_not_mem he
  have : (0 : ℝ) < Fintype.card (Sym2 V) := by
    have : 0 < Fintype.card (Sym2 V) := lt_of_le_of_lt (Nat.zero_le _) (idx_lt e)
    exact_mod_cast this
  linarith

theorem coef_injective (R : Finset (Sym2 V)) : Function.Injective (coef R) := by
  intro e f h
  by_cases he : e ∈ R <;> by_cases hf : f ∈ R
  · unfold coef at h
    rw [ite_eq_left he, ite_eq_left hf] at h
    exact idx_injective (by exact_mod_cast (by linarith : (idx e : ℝ) = idx f))
  · exact absurd h (ne_of_lt ((coef_neg_of_mem he).trans (coef_pos_of_not_mem hf)))
  · exact absurd h (ne_of_gt ((coef_neg_of_mem hf).trans (coef_pos_of_not_mem he)))
  · unfold coef at h
    rw [ite_eq_right he, ite_eq_right hf] at h
    exact idx_injective (by exact_mod_cast (by linarith : (idx e : ℝ) = idx f))

/-- On a triangle with an edge off `R` the coefficients have nonnegative sum. -/
theorem coef_sum_triangle {R : Finset (Sym2 V)} {t : Finset V} (ht : t ∈ G.cliqueFinset 3)
    (hfree : ¬ edgesIn G t ⊆ R) : 0 ≤ ∑ e ∈ edgesIn G t, coef R e := by
  have ht' := ht
  rw [mem_cliqueFinset_iff, is3Clique_iff] at ht'
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht'
  rw [edgesIn_triple G hab hac hbc] at hfree
  rw [sum_edgesIn_triple G hab hac hbc]
  have h1 := coef_ge R s(a, b)
  have h2 := coef_ge R s(a, c)
  have h3 := coef_ge R s(b, c)
  by_cases e1 : s(a, b) ∈ R
  · by_cases e2 : s(a, c) ∈ R
    · by_cases e3 : s(b, c) ∈ R
      · exact absurd (by simp [insert_subset_iff, e1, e2, e3]) hfree
      · have := coef_ge_of_not_mem e3; linarith
    · have := coef_ge_of_not_mem e2; linarith
  · have := coef_ge_of_not_mem e1; linarith

/-- **Proposition 3.1.** A triangle-covered edge weighting `φ` of a `K₃`-divisible tripartite
graph can be replaced, changing its total weight by at most `ε`, by a triangle-covered, balanced,
untied and nonzero one. -/
theorem prop_3_1 (hG : IsTripartite G part) (hdiv : IsK3Divisible G part) {φ : Sym2 V → ℝ}
    (hφ : IsTriangleCovered G φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Sym2 V → ℝ, IsTriangleCovered G ψ ∧ IsBalanced G part ψ ∧ IsUntied G ψ ∧
      IsNonzero G ψ ∧ |∑ e ∈ G.edgeFinset, ψ e - ∑ e ∈ G.edgeFinset, φ e| ≤ ε := by
  classical
  obtain ⟨p, R, hRsub, hRneg, hRle, hRbal, hRfree⟩ := lemma_3_4 hG hdiv hφ
  set χ := translate part φ p with hχ
  set A := ∑ e ∈ G.edgeFinset, |coef R e| with hA
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
  have hν0 : 0 < ε / (A + 1) := by positivity
  set B : Finset ℝ := ((G.edgeFinset ×ˢ G.edgeFinset).filter fun x => x.1 ≠ x.2).image
    fun x => (χ x.2 - χ x.1) / (coef R x.1 - coef R x.2)
  obtain ⟨ν, hνI, hνB⟩ := (Set.Ioo_infinite hν0).exists_notMem_finset B
  obtain ⟨hν, hνlt⟩ := hνI
  set ψ : Sym2 V → ℝ := fun e => χ e + ν * coef R e with hψ
  have hsign : ∀ e ∈ G.edgeFinset, (e ∈ R → ψ e < 0) ∧ (e ∉ R → 0 < ψ e) := by
    intro e he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hRle e h
      have := mul_neg_of_pos_of_neg hν (coef_neg_of_mem h)
      simp only [hψ]; linarith
    · have : 0 ≤ χ e := by
        by_contra hc
        exact h (hRneg e he (lt_of_not_ge hc))
      have := mul_pos hν (coef_pos_of_not_mem h)
      simp only [hψ]; linarith
  have hneg_iff : ∀ e ∈ G.edgeFinset, ψ e < 0 ↔ e ∈ R := by
    intro e he
    constructor
    · intro hn
      by_contra h
      exact absurd hn (not_lt.2 ((hsign e he).2 h).le)
    · exact (hsign e he).1
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h1 := translate_triangleCovered hG hφ p t ht
    have h2 := coef_sum_triangle ht (hRfree t ht)
    simp only [hψ, sum_add_distrib, ← mul_sum]
    nlinarith
  · intro v
    have key : ∀ i : Fin 3, (univ.filter fun u => G.Adj u v ∧ part u = i ∧ ψ s(u, v) < 0) =
        univ.filter fun u => part u = i ∧ s(u, v) ∈ R := by
      intro i
      ext u
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hadj, hp, hn⟩
        exact ⟨hp, (hneg_iff _ (by simpa using hadj)).1 hn⟩
      · rintro ⟨hp, hR⟩
        have he := hRsub hR
        exact ⟨by simpa using he, hp, (hneg_iff _ he).2 hR⟩
    rw [key, key]
    exact hRbal v
  · intro e he f hf hef hψef
    have hc : coef R e - coef R f ≠ 0 := sub_ne_zero.2 fun h => hef (coef_injective R h)
    apply hνB
    refine mem_image.2 ⟨(e, f), mem_filter.2 ⟨mem_product.2 ⟨he, hf⟩, hef⟩, ?_⟩
    simp only [hψ] at hψef
    field_simp
    linarith
  · intro e he
    by_cases h : e ∈ R
    · exact ((hsign e he).1 h).ne
    · exact ((hsign e he).2 h).ne'
  · have hsum : ∑ e ∈ G.edgeFinset, ψ e - ∑ e ∈ G.edgeFinset, φ e =
        ν * ∑ e ∈ G.edgeFinset, coef R e := by
      simp only [hψ, sum_add_distrib, ← mul_sum, hχ, sum_translate hG hdiv]
      ring
    rw [hsum, abs_mul, abs_of_pos hν]
    have h1 : |∑ e ∈ G.edgeFinset, coef R e| ≤ A := abs_sum_le_sum_abs _ _
    have h2 : ν * A ≤ ε / (A + 1) * A := mul_le_mul_of_nonneg_right hνlt.le hA0
    have h3 : ε / (A + 1) * A ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ν * |∑ e ∈ G.edgeFinset, coef R e| ≤ ν * A := mul_le_mul_of_nonneg_left h1 hν.le
      _ ≤ ε := h2.trans h3

/-- **Corollary 3.5.** A `K₃`-divisible tripartite graph has no fractional triangle decomposition
if and only if it has a triangle-covered, totally negative, balanced, untied and nonzero edge
weighting. -/
theorem cor_3_5 (hG : IsTripartite G part) (hdiv : IsK3Divisible G part) :
    (¬ ∃ w, IsFracTriangleDecomp G w) ↔
      ∃ ψ : Sym2 V → ℝ, IsTriangleCovered G ψ ∧ IsTotallyNegative G ψ ∧ IsBalanced G part ψ ∧
        IsUntied G ψ ∧ IsNonzero G ψ := by
  constructor
  · intro h
    obtain ⟨φ, hφc, hφn⟩ := (not_fracDecomp_iff G).1 h
    have hε : 0 < -(∑ e ∈ G.edgeFinset, φ e) / 2 := by unfold IsTotallyNegative at hφn; linarith
    obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := prop_3_1 hG hdiv hφc hε
    refine ⟨ψ, h1, ?_, h2, h3, h4⟩
    unfold IsTotallyNegative at hφn ⊢
    have := (abs_le.1 h5).2
    linarith
  · rintro ⟨ψ, h1, h2, -⟩
    exact (not_fracDecomp_iff G).2 ⟨ψ, h1, h2⟩

end ABLP
