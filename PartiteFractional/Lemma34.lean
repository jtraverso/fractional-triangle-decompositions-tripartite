/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Colouring

/-!
# Lemma 3.4 of Allsop–Bowtell–Lesgourgues–Petrova

For a triangle-covered edge weighting `φ` of a `K₃`-divisible tripartite graph there are a
potential `p` and a set `R` of edges such that `R` contains every edge where `φ_p < 0`, `φ_p ≤ 0`
on `R`, `R` is red-balanced, and `R` contains no triangle.

The potential minimizes the `ℓ¹` norm of the translate; the red-balanced set comes from an
integral flow (Claim 3.4.1); among the admissible sets one with fewest edges contains no triangle:
the three edges of a red triangle have weight zero (the translate is triangle-covered and
nonpositive on red edges), and removing a triangle, a directed 3-cycle for `≺`, keeps the balance.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {part : V → Fin 3}

theorem fin3_add_ne (x : Fin 3) : x + 1 ≠ x := by revert x; decide
theorem fin3_sub_ne (x : Fin 3) : x - 1 ≠ x := by revert x; decide
theorem fin3_add_ne_sub (x : Fin 3) : x + 1 ≠ x - 1 := by revert x; decide
theorem fin3_add_add (x : Fin 3) : x + 1 + 1 = x - 1 := by revert x; decide
theorem fin3_sub_sub (x : Fin 3) : x - 1 - 1 = x + 1 := by revert x; decide
theorem fin3_add_sub (x : Fin 3) : x + 1 - 1 = x := by revert x; decide
theorem fin3_sub_add (x : Fin 3) : x - 1 + 1 = x := by revert x; decide

/-- The three vertices of a triangle of a tripartite graph lie in the three different parts. -/
theorem card_filter_part_triangle (hG : IsTripartite G part) {t : Finset V}
    (ht : t ∈ G.cliqueFinset 3) (i : Fin 3) : #(t.filter fun u => part u = i) = 1 := by
  rw [mem_cliqueFinset_iff] at ht
  have hinj : Set.InjOn part t := by
    intro x hx y hy hxy
    by_contra hne
    exact hG x y (ht.1 hx hy hne) hxy
  have himg : t.image part = univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, ht.2, Fintype.card_fin]
  obtain ⟨u, hu, hpu⟩ := mem_image.1 (himg ▸ mem_univ i)
  rw [card_eq_one]
  refine ⟨u, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hu, hpu⟩, fun w hw => ?_⟩⟩
  obtain ⟨hw, hpw⟩ := mem_filter.1 hw
  exact hinj hw hu (hpw.trans hpu.symm)

/-- The neighbours of `v` in a triangle `t` lying in a given other part. -/
theorem filter_edgesIn_triangle {t : Finset V} (ht : t ∈ G.cliqueFinset 3) {v : V} (hv : v ∈ t)
    {i : Fin 3} (hi : i ≠ part v) :
    (univ.filter fun u => part u = i ∧ s(u, v) ∈ edgesIn G t) = t.filter fun u => part u = i := by
  rw [mem_cliqueFinset_iff] at ht
  ext u
  simp only [mem_filter, mem_univ, true_and, edgesIn, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hp, -, hu, -⟩
    exact ⟨hu, hp⟩
  · rintro ⟨hu, hp⟩
    have hne : u ≠ v := by rintro rfl; exact hi hp.symm
    exact ⟨hp, ht.1 hu hv hne, hu, hv⟩

/-- A triangle meets each of its vertices in one edge from the previous part and one edge from
the next part. -/
theorem triangle_balanced (hG : IsTripartite G part) {t : Finset V}
    (ht : t ∈ G.cliqueFinset 3) (v : V) :
    #{u | part u = part v - 1 ∧ s(u, v) ∈ edgesIn G t} =
      #{u | part u = part v + 1 ∧ s(u, v) ∈ edgesIn G t} := by
  by_cases hv : v ∈ t
  · rw [filter_edgesIn_triangle ht hv (fin3_sub_ne _), filter_edgesIn_triangle ht hv (fin3_add_ne _),
      card_filter_part_triangle hG ht, card_filter_part_triangle hG ht]
  · have h0 : ∀ i : Fin 3, (univ.filter fun u => part u = i ∧ s(u, v) ∈ edgesIn G t) = ∅ := by
      intro i
      refine filter_eq_empty_iff.2 fun u _ ⟨_, he⟩ => hv ?_
      exact (mem_filter.1 he).2 v (Sym2.mem_mk_right u v)
    rw [h0, h0]

/-- **Lemma 3.4.** For a triangle-covered edge weighting `φ` of a `K₃`-divisible tripartite graph
there are a potential `p` and a triangle-free red-balanced set `R` of edges with
`{e : φ_p(e) < 0} ⊆ R ⊆ {e : φ_p(e) ≤ 0}`. -/
theorem lemma_3_4 (hG : IsTripartite G part) (hdiv : IsK3Divisible G part) {φ : Sym2 V → ℝ}
    (hφ : IsTriangleCovered G φ) :
    ∃ p : V → ℝ, ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧
      (∀ e ∈ G.edgeFinset, translate part φ p e < 0 → e ∈ R) ∧
      (∀ e ∈ R, translate part φ p e ≤ 0) ∧ RedBalanced part R ∧
      ∀ t ∈ G.cliqueFinset 3, ¬ edgesIn G t ⊆ R := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_translate_min (G := G) (part := part) φ
  set ψ := translate part φ p₀ with hψ
  have htr : ∀ q, translate part ψ q = translate part φ (p₀ + q) := fun q => funext fun e => by
    simp only [hψ, translate, shift_add]; ring
  have hmin : ∀ q, l1 G ψ ≤ l1 G (translate part ψ q) := fun q => by rw [htr]; exact hp₀ _
  obtain ⟨F, hF, hval⟩ := IntFlow.exists_integral_flow_ge (network G part ψ)
    (network_intCaps G part ψ) _ (cut_capacity_ge hG hdiv hmin)
  let Adm : Finset (Finset (Sym2 V)) := G.edgeFinset.powerset.filter fun R =>
    (∀ e ∈ G.edgeFinset, ψ e < 0 → e ∈ R) ∧ (∀ e ∈ R, ψ e ≤ 0) ∧ RedBalanced part R
  have hne : redSet ψ F ∈ Adm := mem_filter.2 ⟨mem_powerset.2 (redSet_subset F),
    fun e he hn => mem_redSet_of_neg F hG he hn, fun e he => le_zero_of_mem_redSet F he,
    redSet_balanced F hF hval⟩
  obtain ⟨R, hR, hRmin⟩ := exists_min_image Adm card ⟨_, hne⟩
  obtain ⟨hRsub, hRneg, hRle, hRbal⟩ := mem_filter.1 hR
  rw [mem_powerset] at hRsub
  refine ⟨p₀, R, hRsub, hRneg, hRle, hRbal, fun t ht hsub => ?_⟩
  have hψcov : IsTriangleCovered G ψ := translate_triangleCovered hG hφ p₀
  have hle : ∀ f ∈ edgesIn G t, ψ f ≤ 0 := fun f hf => hRle f (hsub hf)
  have hs0 : ∑ f ∈ edgesIn G t, ψ f = 0 := le_antisymm (sum_nonpos hle) (hψcov t ht)
  have hzero : ∀ e ∈ edgesIn G t, ψ e = 0 := (sum_eq_zero_iff_of_nonpos hle).1 hs0
  set R' := R \ edgesIn G t with hR'
  have hR'adm : R' ∈ Adm := by
    refine mem_filter.2 ⟨mem_powerset.2 (sdiff_subset.trans hRsub), fun e he hn =>
      mem_sdiff.2 ⟨hRneg e he hn, fun h => by linarith [hzero e h]⟩,
      fun e he => hRle e (mem_sdiff.1 he).1, fun v => ?_⟩
    have hsplit : ∀ i : Fin 3, #{u | part u = i ∧ s(u, v) ∈ R} =
        #{u | part u = i ∧ s(u, v) ∈ R'} + #{u | part u = i ∧ s(u, v) ∈ edgesIn G t} := by
      intro i
      rw [← card_union_of_disjoint (disjoint_filter.2 fun u _ h1 h2 =>
        (mem_sdiff.1 h1.2).2 h2.2)]
      congr 1
      ext u
      simp only [mem_union, mem_filter, mem_univ, true_and, hR', mem_sdiff]
      by_cases h : s(u, v) ∈ edgesIn G t
      · simp [h, hsub h]
      · simp [h]
    have h1 := hRbal v
    have h2 := triangle_balanced hG ht v
    rw [hsplit, hsplit] at h1
    omega
  have hEt : (edgesIn G t).Nonempty := by
    have ht' := ht
    rw [mem_cliqueFinset_iff, is3Clique_iff] at ht'
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht'
    rw [edgesIn_triple G hab hac hbc]
    exact ⟨s(a, b), mem_insert_self _ _⟩
  have hlt : #R' < #R := card_lt_card (sdiff_ssubset hsub hEt)
  exact absurd (hRmin R' hR'adm) (not_le.2 hlt)

end ABLP
