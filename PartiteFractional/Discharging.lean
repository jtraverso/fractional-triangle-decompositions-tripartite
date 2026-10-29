/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Balanced

/-!
# Section 4 of Allsop–Bowtell–Lesgourgues–Petrova: non-uniform proportional discharging

For a balanced edge weighting `φ` of a tripartite graph with parts of size `n`, an edge is red
when `φ < 0` and blue otherwise, and `d_v` is the number of red edges from `v` to either other
part. Given `f : [0, 1] → [0, 1/2]`, every blue edge `vw` sends weight to the red edges `uv` of the
triangles `uvw` (Definition 4.1). We prove that a blue edge never sends more than its weight
(Proposition 4.2) and the lower bound `g_d(x, y) ≤ Δ(r) / |φ(r)|` on what a red edge `r = uv`
receives (Proposition 4.3), and we assemble the proof of Theorem 1.3 from these and Corollary 3.5:
if `g_d ≥ 1` on the region `0 < y ≤ x < 1`, `x + y ≤ 1`, then every `K₃`-divisible tripartite
graph with parts of size `n` and minimum partite degree at least `(1 - d) n` has a fractional
triangle decomposition. The numerical inequality `g_d ≥ 1` itself (Proposition 4.4) is not
proved here.

A transfer is indexed by the ordered triple `(u, v, w)`: `dis u v w` is the weight sent by the
blue edge `vw` to the red edge `uv` through the triangle `uvw`, and `disE b r` is the weight sent
by the edge `b` to the edge `r`.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (part : V → Fin 3) (n : ℕ) (f : ℝ → ℝ) (φ : Sym2 V → ℝ)

/-- The red degree `d_v`: the number of negative edges from `v` to the previous part. For a
balanced weighting it is also the number of negative edges from `v` to the next part. -/
noncomputable def redDeg (v : V) : ℕ := #{u | G.Adj u v ∧ part u = part v - 1 ∧ φ s(u, v) < 0}

/-- The proportion `λ_b` of the blue edge `b = vw`: `1/2` if `d_v = d_w`, and
`f(max(d_v, d_w) / n)` otherwise. -/
noncomputable def lam (v w : V) : ℝ :=
  if redDeg G part φ v = redDeg G part φ w then 1 / 2
  else f (max (redDeg G part φ v : ℝ) (redDeg G part φ w) / n)

/-- The proportion of the weight of the blue edge `vw` sent through its endpoint `v` into
quasi-positive triangles: `λ_b` if `d_v ≥ d_w`, and `1 - λ_b` otherwise. -/
noncomputable def share (v w : V) : ℝ :=
  if redDeg G part φ w ≤ redDeg G part φ v then lam G part n f φ v w
  else 1 - lam G part n f φ v w

/-- **Definition 4.1.** The weight `dis^f_φ(vw, uv)` sent by the blue edge `vw` to the red edge
`uv` through the triangle `uvw`, which is quasi-positive when `uw` is blue and quasi-negative when
`uw` is red. It is zero unless `uvw` is a triangle, `vw` is blue and `uv` is red. -/
noncomputable def dis (u v w : V) : ℝ :=
  if G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧ 0 ≤ φ s(v, w) ∧ φ s(u, v) < 0 then
    if 0 ≤ φ s(u, w) then share G part n f φ v w * φ s(v, w) / redDeg G part φ v
    else lam G part n f φ v w * |φ s(u, v)| / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
      (1 - lam G part n f φ v w) * |φ s(u, v)| / min (redDeg G part φ v : ℝ) (redDeg G part φ w)
  else 0

/-- `dis^f_φ(b, r)` for a pair of edges: the weight sent by `b` to `r` through their common
triangle, and zero when there is none. -/
noncomputable def disE (b r : Sym2 V) : ℝ :=
  ∑ u, ∑ v, ∑ w, if s(v, w) = b ∧ s(u, v) = r then dis G part n f φ u v w else 0

/-- `M(a, b) = 1/a - sup_{a < z ≤ b} f(z) (1/a - 1/z)`, where the supremum over the empty set is
`0` (which is the value of `sSup ∅` in `ℝ`). -/
noncomputable def M (a b : ℝ) : ℝ :=
  1 / a - sSup ((fun z => f z * (1 / a - 1 / z)) '' Set.Ioc a b)

/-- The lower bound `g_d(x, y)` of Propositions 4.3 and 4.4. -/
noncomputable def gd (d x y : ℝ) : ℝ :=
  (M f y (1 - x) - f x / x) * max (x - d) 0 + (M f x (1 - y) - f x / x) * max (y - d) 0 +
    f x / x * (1 - 2 * d)

variable {G part n f φ}

/-! ### Elementary facts -/

theorem fin3_ne_iff (i x : Fin 3) (h : i ≠ x) : i = x - 1 ∨ i = x + 1 := by
  revert i x; decide

theorem fin3_third (a b c : Fin 3) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    c = -(a + b) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> first | decide | (exfalso; simp_all)

theorem fin3_neg_add_ne_left (a b : Fin 3) (hab : a ≠ b) : -(a + b) ≠ a := by
  revert a b; decide

theorem fin3_neg_add_ne_right (a b : Fin 3) (hab : a ≠ b) : -(a + b) ≠ b := by
  revert a b; decide

theorem div_mul_le_of_le_denom {c a d : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (had : a ≤ d) :
    c / d * a ≤ c := by
  rcases (ha.trans had).eq_or_lt with h | h
  · have : a = 0 := le_antisymm (by linarith) ha
    simp [this, hc]
  · calc c / d * a ≤ c / d * d := mul_le_mul_of_nonneg_left had (div_nonneg hc h.le)
      _ = c := div_mul_cancel₀ c h.ne'

/-- For a balanced weighting the red degree counts the red edges to either other part. -/
theorem redDeg_eq (hbal : IsBalanced G part φ) {v : V} {i : Fin 3} (hi : i ≠ part v) :
    #{u | G.Adj u v ∧ part u = i ∧ φ s(u, v) < 0} = redDeg G part φ v := by
  rcases fin3_ne_iff i (part v) hi with rfl | rfl
  · rfl
  · exact (hbal v).symm

theorem redDeg_le (hn : ∀ i, #{v | part v = i} = n) (v : V) : redDeg G part φ v ≤ n := by
  rw [← hn (part v - 1)]
  exact card_le_card fun u hu => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hu).2.2.1⟩

theorem one_le_redDeg (hG : IsTripartite G part) (hbal : IsBalanced G part φ) {u w : V}
    (h : G.Adj u w) (hneg : φ s(u, w) < 0) : 1 ≤ redDeg G part φ w := by
  rw [← redDeg_eq hbal (hG u w h)]
  exact card_pos.2 ⟨u, mem_filter.2 ⟨mem_univ _, h, rfl, hneg⟩⟩

/-- The weights of the three edges of a triangle have nonnegative sum. -/
theorem tri_sum (hφ : IsTriangleCovered G φ) {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc : G.Adj b c) : 0 ≤ φ s(a, b) + φ s(a, c) + φ s(b, c) := by
  have ht : ({a, b, c} : Finset V) ∈ G.cliqueFinset 3 := by
    rw [mem_cliqueFinset_iff, is3Clique_triple_iff]
    exact ⟨hab, hac, hbc⟩
  have := hφ _ ht
  rwa [sum_edgesIn_triple G hab hac hbc] at this

/-- The endpoints of a red edge have red degrees summing to at most `n`: a common red neighbour
would span a red triangle. -/
theorem redDeg_add_le (hG : IsTripartite G part) (hn : ∀ i, #{v | part v = i} = n)
    (hφ : IsTriangleCovered G φ) (hbal : IsBalanced G part φ) {v w : V} (h : G.Adj v w)
    (hneg : φ s(v, w) < 0) : redDeg G part φ v + redDeg G part φ w ≤ n := by
  have hvw := hG v w h
  rw [← redDeg_eq hbal (fin3_neg_add_ne_left _ _ hvw),
    ← redDeg_eq hbal (fin3_neg_add_ne_right _ _ hvw), ← card_union_of_disjoint, ← hn (-(part v + part w))]
  · exact card_le_card fun u hu => by
      rcases mem_union.1 hu with hu | hu <;> exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hu).2.2.1⟩
  · refine disjoint_filter.2 fun u _ h1 h2 => ?_
    have := tri_sum hφ h1.1 h2.1 h
    linarith [h1.2.2, h2.2.2]

/-- Common neighbours `u` of the endpoints of an edge `vw` with `uv` red number at most `d_v`. -/
theorem card_common_red_le (hG : IsTripartite G part) (hbal : IsBalanced G part φ) {v w : V}
    (h : G.Adj v w) : #{u | G.Adj u v ∧ G.Adj u w ∧ φ s(u, v) < 0} ≤ redDeg G part φ v := by
  have hvw := hG v w h
  rw [← redDeg_eq hbal (fin3_neg_add_ne_left _ _ hvw)]
  refine card_le_card fun u hu => ?_
  obtain ⟨-, h1, h2, h3⟩ := mem_filter.1 hu
  exact mem_filter.2 ⟨mem_univ _, h1, fin3_third _ _ _ hvw (hG u v h1) (hG u w h2), h3⟩

/-! ### The proportions -/

theorem lam_comm (v w : V) : lam G part n f φ v w = lam G part n f φ w v := by
  unfold lam
  by_cases h : redDeg G part φ v = redDeg G part φ w
  · simp [h]
  · rw [max_comm]
    simp [h, Ne.symm h]

theorem lam_mem (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (v w : V) :
    0 ≤ lam G part n f φ v w ∧ lam G part n f φ v w ≤ 1 / 2 := by
  unfold lam
  split_ifs
  · norm_num
  · apply hf
    have h1 : (redDeg G part φ v : ℝ) ≤ n := by exact_mod_cast redDeg_le hn v
    have h2 : (redDeg G part φ w : ℝ) ≤ n := by exact_mod_cast redDeg_le hn w
    exact ⟨div_nonneg (le_max_of_le_left (Nat.cast_nonneg _)) (Nat.cast_nonneg _),
      div_le_one_of_le₀ (max_le h1 h2) (Nat.cast_nonneg _)⟩

theorem share_nonneg (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (v w : V) :
    0 ≤ share G part n f φ v w := by
  have hl := lam_mem (G := G) (φ := φ) hn hf v w
  unfold share
  split_ifs <;> linarith [hl.1, hl.2]

/-- The share through `v` is at least `f(d_v / n)`. -/
theorem share_ge (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (v w : V) :
    f (redDeg G part φ v / n) ≤ share G part n f φ v w := by
  have hl := lam_mem (G := G) (φ := φ) hn hf v w
  have hy : f (redDeg G part φ v / n) ≤ 1 / 2 := by
    refine (hf _ ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)⟩).2
    exact_mod_cast redDeg_le hn v
  unfold share
  rcases lt_trichotomy (redDeg G part φ v) (redDeg G part φ w) with h | h | h
  · rw [ite_eq_right (not_le.2 h)]
    linarith [hl.2]
  · rw [ite_eq_left h.ge]
    unfold lam
    rw [ite_eq_left h]
    exact hy
  · rw [ite_eq_left h.le]
    unfold lam
    have h' : (redDeg G part φ w : ℝ) ≤ redDeg G part φ v := by exact_mod_cast h.le
    rw [ite_eq_right h.ne', max_eq_left h']

theorem share_add (v w : V) : share G part n f φ v w + share G part n f φ w v = 1 := by
  unfold share
  rw [lam_comm w v]
  rcases lt_trichotomy (redDeg G part φ v) (redDeg G part φ w) with h | h | h
  · rw [ite_eq_right (not_le.2 h), ite_eq_left h.le]
    ring
  · have hl : lam G part n f φ v w = 1 / 2 := by
      unfold lam
      rw [ite_eq_left h]
    rw [ite_eq_left h.ge, ite_eq_left h.le, hl]
    norm_num
  · rw [ite_eq_left h.le, ite_eq_right (not_le.2 h)]
    ring

/-- The coefficient of a quasi-negative transfer splits as the shares through the endpoints. -/
theorem qn_coef (v w : V) :
    lam G part n f φ v w / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
        (1 - lam G part n f φ v w) / min (redDeg G part φ v : ℝ) (redDeg G part φ w) =
      share G part n f φ v w / redDeg G part φ v + share G part n f φ w v / redDeg G part φ w := by
  unfold share
  rw [lam_comm w v]
  rcases lt_trichotomy (redDeg G part φ v) (redDeg G part φ w) with h | h | h
  · have h' : (redDeg G part φ v : ℝ) ≤ redDeg G part φ w := by exact_mod_cast h.le
    rw [max_eq_right h', min_eq_left h', ite_eq_right (not_le.2 h), ite_eq_left h.le]
    ring
  · have hl : lam G part n f φ v w = 1 / 2 := by
      unfold lam
      rw [ite_eq_left h]
    rw [ite_eq_left h.ge, ite_eq_left h.le, hl, h, max_self, min_self]
    ring
  · have h' : (redDeg G part φ w : ℝ) ≤ redDeg G part φ v := by exact_mod_cast h.le
    rw [max_eq_left h', min_eq_right h', ite_eq_left h.le, ite_eq_right (not_le.2 h)]

theorem dis_nonneg (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (u v w : V) :
    0 ≤ dis G part n f φ u v w := by
  have hl := lam_mem (G := G) (φ := φ) hn hf v w
  have hs := share_nonneg (G := G) (φ := φ) hn hf v w
  unfold dis
  split_ifs with h1 h2
  · exact div_nonneg (mul_nonneg hs h1.2.2.2.1) (Nat.cast_nonneg _)
  · exact add_nonneg
      (div_nonneg (mul_nonneg hl.1 (abs_nonneg _)) (le_max_of_le_left (Nat.cast_nonneg _)))
      (div_nonneg (mul_nonneg (by linarith [hl.2]) (abs_nonneg _))
        (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  · exact le_rfl

/-! ### Transfers between edges -/

theorem dis_ne_zero {u v w : V} (h : dis G part n f φ u v w ≠ 0) :
    G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧ 0 ≤ φ s(v, w) ∧ φ s(u, v) < 0 := by
  by_contra hc
  exact h (by unfold dis; exact ite_eq_right hc)

/-- Only blue edges send, and only red edges receive. -/
theorem disE_ne_zero {b r : Sym2 V} (h : disE G part n f φ b r ≠ 0) :
    b ∈ G.edgeFinset ∧ r ∈ G.edgeFinset ∧ 0 ≤ φ b ∧ φ r < 0 := by
  obtain ⟨u, -, hu⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨v, -, hv⟩ := exists_ne_zero_of_sum_ne_zero hu
  obtain ⟨w, -, hw⟩ := exists_ne_zero_of_sum_ne_zero hv
  by_cases hc : s(v, w) = b ∧ s(u, v) = r
  · rw [ite_eq_left hc] at hw
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨h1, h2, -, h4, h5⟩ := dis_ne_zero hw
    exact ⟨by simpa using h2, by simpa using h1, h4, h5⟩
  · exact absurd (ite_eq_right hc) hw

theorem sum_sym2_pair {v w : V} (hvw : v ≠ w) (F : V → V → ℝ) :
    ∑ a, ∑ c, (if s(a, c) = s(v, w) then F a c else 0) = F v w + F w v := by
  rw [← Finset.sum_product' (f := fun a c => if s(a, c) = s(v, w) then F a c else 0),
    ← sum_filter (fun x : V × V => s(x.1, x.2) = s(v, w)) (fun x => F x.1 x.2)]
  have : (univ ×ˢ univ).filter (fun x : V × V => s(x.1, x.2) = s(v, w)) = {(v, w), (w, v)} := by
    ext ⟨a, c⟩
    simp [Sym2.eq_iff]
  rw [this, sum_pair (by simp [hvw])]

theorem sum_disE_right (b : Sym2 V) :
    ∑ r ∈ G.edgeFinset, disE G part n f φ b r =
      ∑ u, ∑ v, ∑ w, if s(v, w) = b then dis G part n f φ u v w else 0 := by
  rw [sum_subset (subset_univ _) fun r _ hr => by
    by_contra h
    exact hr (disE_ne_zero h).2.1]
  simp only [disE]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  by_cases h : s(v, w) = b <;> simp [h]

theorem sum_disE_left (r : Sym2 V) :
    ∑ b ∈ G.edgeFinset, disE G part n f φ b r =
      ∑ u, ∑ v, ∑ w, if s(u, v) = r then dis G part n f φ u v w else 0 := by
  rw [sum_subset (subset_univ _) fun b _ hb => by
    by_contra h
    exact hb (disE_ne_zero h).1]
  simp only [disE]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  by_cases h : s(u, v) = r <;> simp [h]

/-- The weight sent by the blue edge `vw`. -/
theorem sum_disE_mk_left {v w : V} (hvw : v ≠ w) :
    ∑ r ∈ G.edgeFinset, disE G part n f φ s(v, w) r =
      ∑ u, (dis G part n f φ u v w + dis G part n f φ u w v) := by
  rw [sum_disE_right]
  exact sum_congr rfl fun u _ => sum_sym2_pair hvw (fun a c => dis G part n f φ u a c)

/-- The weight `Δ(uv)` received by the red edge `uv`. -/
theorem sum_disE_mk_right {u v : V} (huv : u ≠ v) :
    ∑ b ∈ G.edgeFinset, disE G part n f φ b s(u, v) =
      ∑ w, (dis G part n f φ u v w + dis G part n f φ v u w) := by
  rw [sum_disE_left]
  calc _ = ∑ a, ∑ w, ∑ c, (if s(a, c) = s(u, v) then dis G part n f φ a c w else 0) :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ w, ∑ a, ∑ c, (if s(a, c) = s(u, v) then dis G part n f φ a c w else 0) := sum_comm
    _ = _ := sum_congr rfl fun w _ => sum_sym2_pair huv (fun a c => dis G part n f φ a c w)

/-! ### Proposition 4.2 -/

/-- **Proposition 4.2.** During the `f`-proportional discharging of a triangle-covered balanced
weighting, a blue edge sends at most its own weight. -/
theorem prop_4_2 (hG : IsTripartite G part) (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (hφ : IsTriangleCovered G φ)
    (hbal : IsBalanced G part φ) {b : Sym2 V} (hb : b ∈ G.edgeFinset) (hb0 : 0 ≤ φ b) :
    0 ≤ φ b - ∑ r ∈ G.edgeFinset, disE G part n f φ b r := by
  induction b using Sym2.ind with
  | _ v w =>
  have hvw : G.Adj v w := by simpa using hb
  rw [sum_disE_mk_left hvw.ne, sub_nonneg]
  have hwv : φ s(w, v) = φ s(v, w) := by rw [Sym2.eq_swap]
  have hα := share_nonneg (G := G) (φ := φ) hn hf v w
  have hβ := share_nonneg (G := G) (φ := φ) hn hf w v
  have hl := lam_mem (G := G) (φ := φ) hn hf v w
  have key : ∀ u, dis G part n f φ u v w + dis G part n f φ u w v ≤
      share G part n f φ v w * φ s(v, w) / redDeg G part φ v *
          (if G.Adj u v ∧ G.Adj u w ∧ φ s(u, v) < 0 then 1 else 0) +
        share G part n f φ w v * φ s(v, w) / redDeg G part φ w *
          (if G.Adj u w ∧ G.Adj u v ∧ φ s(u, w) < 0 then 1 else 0) := by
    intro u
    have hR : 0 ≤ share G part n f φ v w * φ s(v, w) / redDeg G part φ v *
          (if G.Adj u v ∧ G.Adj u w ∧ φ s(u, v) < 0 then 1 else 0) +
        share G part n f φ w v * φ s(v, w) / redDeg G part φ w *
          (if G.Adj u w ∧ G.Adj u v ∧ φ s(u, w) < 0 then 1 else 0) := by
      refine add_nonneg (mul_nonneg (div_nonneg (mul_nonneg hα hb0) (Nat.cast_nonneg _)) ?_)
        (mul_nonneg (div_nonneg (mul_nonneg hβ hb0) (Nat.cast_nonneg _)) ?_) <;>
        split_ifs <;> norm_num
    by_cases htri : G.Adj u v ∧ G.Adj u w
    swap
    · have h1 : dis G part n f φ u v w = 0 := by
        unfold dis
        exact ite_eq_right fun h => htri ⟨h.1, h.2.2.1⟩
      have h2 : dis G part n f φ u w v = 0 := by
        unfold dis
        exact ite_eq_right fun h => htri ⟨h.2.2.1, h.1⟩
      rw [h1, h2, add_zero]
      exact hR
    obtain ⟨huv, huw⟩ := htri
    rcases lt_or_ge (φ s(u, v)) 0 with h1 | h1 <;> rcases lt_or_ge (φ s(u, w)) 0 with h2 | h2
    · -- quasi-negative triangle
      have hsum : |φ s(u, v)| + |φ s(u, w)| ≤ φ s(v, w) := by
        rw [abs_of_neg h1, abs_of_neg h2]
        linarith [tri_sum hφ huv huw hvw]
      have hK : 0 ≤ lam G part n f φ v w / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
          (1 - lam G part n f φ v w) / min (redDeg G part φ v : ℝ) (redDeg G part φ w) :=
        add_nonneg (div_nonneg hl.1 (le_max_of_le_left (Nat.cast_nonneg _)))
          (div_nonneg (by linarith [hl.2]) (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      have e1 : dis G part n f φ u v w =
          lam G part n f φ v w * |φ s(u, v)| / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
            (1 - lam G part n f φ v w) * |φ s(u, v)| /
              min (redDeg G part φ v : ℝ) (redDeg G part φ w) := by
        unfold dis
        rw [ite_eq_left ⟨huv, hvw, huw, hb0, h1⟩, ite_eq_right (not_le.2 h2)]
      have e2 : dis G part n f φ u w v =
          lam G part n f φ v w * |φ s(u, w)| / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
            (1 - lam G part n f φ v w) * |φ s(u, w)| /
              min (redDeg G part φ v : ℝ) (redDeg G part φ w) := by
        unfold dis
        rw [ite_eq_left ⟨huw, hvw.symm, huv, by rwa [hwv], h2⟩, ite_eq_right (not_le.2 h1),
          lam_comm w v, max_comm (redDeg G part φ w : ℝ), min_comm (redDeg G part φ w : ℝ)]
      rw [e1, e2, ite_eq_left ⟨huv, huw, h1⟩, ite_eq_left ⟨huw, huv, h2⟩]
      calc _ = (|φ s(u, v)| + |φ s(u, w)|) *
            (lam G part n f φ v w / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
              (1 - lam G part n f φ v w) / min (redDeg G part φ v : ℝ) (redDeg G part φ w)) := by
            ring
        _ ≤ φ s(v, w) *
            (lam G part n f φ v w / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
              (1 - lam G part n f φ v w) / min (redDeg G part φ v : ℝ) (redDeg G part φ w)) :=
            mul_le_mul_of_nonneg_right hsum hK
        _ = _ := by
            rw [qn_coef]
            ring
    · -- quasi-positive triangle, red edge at `v`
      have e1 : dis G part n f φ u v w =
          share G part n f φ v w * φ s(v, w) / redDeg G part φ v := by
        unfold dis
        rw [ite_eq_left ⟨huv, hvw, huw, hb0, h1⟩, ite_eq_left h2]
      have e2 : dis G part n f φ u w v = 0 := by
        unfold dis
        exact ite_eq_right fun h => absurd h.2.2.2.2 (not_lt.2 h2)
      rw [e1, e2, ite_eq_left ⟨huv, huw, h1⟩,
        ite_eq_right fun h => absurd h.2.2 (not_lt.2 h2)]
      simp
    · -- quasi-positive triangle, red edge at `w`
      have e1 : dis G part n f φ u v w = 0 := by
        unfold dis
        exact ite_eq_right fun h => absurd h.2.2.2.2 (not_lt.2 h1)
      have e2 : dis G part n f φ u w v =
          share G part n f φ w v * φ s(v, w) / redDeg G part φ w := by
        unfold dis
        rw [ite_eq_left ⟨huw, hvw.symm, huv, by rwa [hwv], h2⟩, ite_eq_left h1, hwv]
      rw [e1, e2, ite_eq_right fun h => absurd h.2.2 (not_lt.2 h1),
        ite_eq_left ⟨huw, huv, h2⟩]
      simp
    · -- no red edge at `u`
      have e1 : dis G part n f φ u v w = 0 := by
        unfold dis
        exact ite_eq_right fun h => absurd h.2.2.2.2 (not_lt.2 h1)
      have e2 : dis G part n f φ u w v = 0 := by
        unfold dis
        exact ite_eq_right fun h => absurd h.2.2.2.2 (not_lt.2 h2)
      rw [e1, e2, add_zero]
      exact hR
  have hA : (#{u | G.Adj u v ∧ G.Adj u w ∧ φ s(u, v) < 0} : ℝ) ≤ redDeg G part φ v := by
    exact_mod_cast card_common_red_le hG hbal hvw
  have hB : (#{u | G.Adj u w ∧ G.Adj u v ∧ φ s(u, w) < 0} : ℝ) ≤ redDeg G part φ w := by
    exact_mod_cast card_common_red_le hG hbal hvw.symm
  calc ∑ u, (dis G part n f φ u v w + dis G part n f φ u w v)
      ≤ ∑ u, (share G part n f φ v w * φ s(v, w) / redDeg G part φ v *
          (if G.Adj u v ∧ G.Adj u w ∧ φ s(u, v) < 0 then 1 else 0) +
        share G part n f φ w v * φ s(v, w) / redDeg G part φ w *
          (if G.Adj u w ∧ G.Adj u v ∧ φ s(u, w) < 0 then 1 else 0)) := sum_le_sum fun u _ => key u
    _ = share G part n f φ v w * φ s(v, w) / redDeg G part φ v *
          #{u | G.Adj u v ∧ G.Adj u w ∧ φ s(u, v) < 0} +
        share G part n f φ w v * φ s(v, w) / redDeg G part φ w *
          #{u | G.Adj u w ∧ G.Adj u v ∧ φ s(u, w) < 0} := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_boole, sum_boole]
    _ ≤ share G part n f φ v w * φ s(v, w) + share G part n f φ w v * φ s(v, w) :=
      add_le_add (div_mul_le_of_le_denom (mul_nonneg hα hb0) (Nat.cast_nonneg _) hA)
        (div_mul_le_of_le_denom (mul_nonneg hβ hb0) (Nat.cast_nonneg _) hB)
    _ = φ s(v, w) := by rw [← add_mul, share_add, one_mul]

/-! ### The function `M` -/

theorem M_aux (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) {a b : ℝ} (ha : 0 < a)
    (hb : b ≤ 1) : ∀ y ∈ (fun z => f z * (1 / a - 1 / z)) '' Set.Ioc a b,
      0 ≤ y ∧ y ≤ 1 / (2 * a) := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
  have hz : 0 < z := ha.trans hz1
  have hfz := hf z ⟨hz.le, hz2.trans hb⟩
  have h1 : 1 / z ≤ 1 / a := one_div_le_one_div_of_le ha hz1.le
  have h2 : 0 < 1 / z := one_div_pos.2 hz
  constructor
  · exact mul_nonneg hfz.1 (by linarith)
  · calc f z * (1 / a - 1 / z) ≤ 1 / 2 * (1 / a) :=
          mul_le_mul hfz.2 (by linarith) (by linarith) (by norm_num)
      _ = 1 / (2 * a) := one_div_mul_one_div 2 a

theorem M_le (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) {a b : ℝ} (ha : 0 < a)
    (hb : b ≤ 1) : M f a b ≤ 1 / a := by
  unfold M
  have := Real.sSup_nonneg fun y hy => (M_aux hf ha hb y hy).1
  linarith

theorem le_M (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) {a b : ℝ} (ha : 0 < a)
    (hb : b ≤ 1) : 1 / (2 * a) ≤ M f a b := by
  unfold M
  have := Real.sSup_le (fun y hy => (M_aux hf ha hb y hy).2) (by positivity : (0 : ℝ) ≤ 1 / (2 * a))
  have e : 1 / a - 1 / (2 * a) = 1 / (2 * a) := by ring
  linarith

theorem M_le_of_mem (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) {a b : ℝ}
    (ha : 0 < a) (hb : b ≤ 1) {z : ℝ} (hz : z ∈ Set.Ioc a b) :
    M f a b ≤ 1 / a - f z * (1 / a - 1 / z) := by
  unfold M
  have : f z * (1 / a - 1 / z) ≤ sSup ((fun z => f z * (1 / a - 1 / z)) '' Set.Ioc a b) :=
    le_csSup ⟨1 / (2 * a), fun y hy => (M_aux hf ha hb y hy).2⟩ ⟨z, hz, rfl⟩
  linarith

/-- The coefficient of a quasi-negative transfer from `pw` to the red edge `pq` is at least
`M(d_p / n, 1 - d_q / n) / n`. -/
theorem qn_bound (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) {p w : V} {dq : ℕ}
    (hp : 1 ≤ redDeg G part φ p) (hw : 1 ≤ redDeg G part φ w)
    (hsum : redDeg G part φ w + dq ≤ n) :
    M f (redDeg G part φ p / n) (1 - dq / n) / n ≤
      lam G part n f φ p w / max (redDeg G part φ p : ℝ) (redDeg G part φ w) +
        (1 - lam G part n f φ p w) / min (redDeg G part φ p : ℝ) (redDeg G part φ w) := by
  have hl := lam_mem (G := G) (φ := φ) hn hf p w
  have hpn := redDeg_le (G := G) (φ := φ) hn p
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hdp : (1 : ℝ) ≤ redDeg G part φ p := by exact_mod_cast hp
  have hdw : (1 : ℝ) ≤ redDeg G part φ w := by exact_mod_cast hw
  have hdp0 : (redDeg G part φ p : ℝ) ≠ 0 := by positivity
  have hdw0 : (redDeg G part φ w : ℝ) ≠ 0 := by positivity
  have hX : 0 < (redDeg G part φ p : ℝ) / n := div_pos (by linarith) hnpos
  have hB : 1 - (dq : ℝ) / n ≤ 1 := by
    have : 0 ≤ (dq : ℝ) / n := by positivity
    linarith
  rcases le_or_gt (redDeg G part φ w) (redDeg G part φ p) with h | h
  · have h' : (redDeg G part φ w : ℝ) ≤ redDeg G part φ p := by exact_mod_cast h
    rw [max_eq_left h', min_eq_right h']
    calc M f (redDeg G part φ p / n) (1 - dq / n) / n ≤ 1 / (redDeg G part φ p / n) / n :=
          div_le_div_of_nonneg_right (M_le hf hX hB) hnpos.le
      _ = lam G part n f φ p w / redDeg G part φ p +
            (1 - lam G part n f φ p w) / redDeg G part φ p := by
          field_simp
          ring
      _ ≤ lam G part n f φ p w / redDeg G part φ p +
            (1 - lam G part n f φ p w) / redDeg G part φ w :=
          add_le_add le_rfl (div_le_div_of_nonneg_left (by linarith [hl.2]) (by linarith) h')
  · have h' : (redDeg G part φ p : ℝ) < redDeg G part φ w := by exact_mod_cast h
    have hlam : lam G part n f φ p w = f (redDeg G part φ w / n) := by
      unfold lam
      rw [ite_eq_right h.ne, max_eq_right h'.le]
    rw [max_eq_right h'.le, min_eq_left h'.le, hlam]
    have hz : (redDeg G part φ w : ℝ) / n ∈ Set.Ioc ((redDeg G part φ p : ℝ) / n) (1 - dq / n) := by
      constructor
      · exact div_lt_div_of_pos_right h' hnpos
      · rw [le_sub_iff_add_le, ← add_div, div_le_one hnpos]
        exact_mod_cast hsum
    calc M f (redDeg G part φ p / n) (1 - dq / n) / n
        ≤ (1 / (redDeg G part φ p / n) - f (redDeg G part φ w / n) *
            (1 / (redDeg G part φ p / n) - 1 / (redDeg G part φ w / n))) / n :=
          div_le_div_of_nonneg_right (M_le_of_mem hf hX hB hz) hnpos.le
      _ = _ := by
          field_simp
          ring

/-! ### Proposition 4.3 -/

/-- Red neighbours `w` of `p` (in the third part) such that `qw` is blue, where `pq` is a red
edge: all red neighbours of `p` except at most `d n` non-neighbours of `q`. -/
theorem card_red_blue_ge (hG : IsTripartite G part) (hn : ∀ i, #{v | part v = i} = n) {d : ℝ}
    (hδ : ∀ v (i : Fin 3), i ≠ part v → (1 - d) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ))
    (hφ : IsTriangleCovered G φ) (hbal : IsBalanced G part φ) {p q : V} (hpq : G.Adj p q)
    (hneg : φ s(p, q) < 0) :
    (redDeg G part φ p : ℝ) - d * n ≤
      #{w | G.Adj p w ∧ G.Adj q w ∧ φ s(p, w) < 0 ∧ 0 ≤ φ s(q, w)} := by
  have hpq' := hG p q hpq
  have hkp := fin3_neg_add_ne_left _ _ hpq'
  have hkq := fin3_neg_add_ne_right _ _ hpq'
  set k := -(part p + part q) with hk
  set W := univ.filter fun w => G.Adj p w ∧ G.Adj q w ∧ φ s(p, w) < 0 ∧ 0 ≤ φ s(q, w) with hW
  set Pk := univ.filter fun w => part w = k with hPk
  set Nq := univ.filter fun w => part w = k ∧ G.Adj q w with hNq
  have hsub : (univ.filter fun w => G.Adj w p ∧ part w = k ∧ φ s(w, p) < 0) ⊆ W ∪ (Pk \ Nq) := by
    intro w hw
    obtain ⟨-, hwp, hwk, hwn⟩ := mem_filter.1 hw
    have hpw : G.Adj p w := hwp.symm
    have hpwn : φ s(p, w) < 0 := by rwa [Sym2.eq_swap]
    by_cases hqw : G.Adj q w
    · have h0 : 0 ≤ φ s(q, w) := by
        by_contra hc
        push_neg at hc
        linarith [tri_sum hφ hpq hpw hqw]
      exact mem_union.2 (Or.inl (mem_filter.2 ⟨mem_univ _, hpw, hqw, hpwn, h0⟩))
    · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, hwk⟩,
        fun h => hqw (mem_filter.1 h).2.2⟩))
  have h1 := card_le_card hsub
  rw [redDeg_eq hbal hkp] at h1
  have h2 := card_union_le W (Pk \ Nq)
  have h3 : #(Pk \ Nq) + #Nq = #Pk :=
    card_sdiff_add_card_eq_card fun w hw => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hw).2.1⟩
  have h4 : #Pk = n := hn k
  have h5 : (1 - d) * n ≤ (#Nq : ℝ) := hδ q k hkq
  have hnat : redDeg G part φ p + #Nq ≤ #W + n := by omega
  have : (redDeg G part φ p : ℝ) + #Nq ≤ #W + n := by exact_mod_cast hnat
  linarith

/-- The common neighbours of the endpoints of a red edge `uv` number at least `(1 - 2d) n`, and
none of them spans a red triangle with `uv`. -/
theorem card_common_ge (hG : IsTripartite G part) (hn : ∀ i, #{v | part v = i} = n) {d : ℝ}
    (hδ : ∀ v (i : Fin 3), i ≠ part v → (1 - d) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ))
    (hφ : IsTriangleCovered G φ) {u v : V} (huv : G.Adj u v) (hr : φ s(u, v) < 0) :
    (1 - 2 * d) * n ≤ (#{w | G.Adj u w ∧ G.Adj v w ∧ 0 ≤ φ s(u, w) ∧ 0 ≤ φ s(v, w)} : ℝ) +
      #{w | G.Adj u w ∧ G.Adj v w ∧ φ s(u, w) < 0 ∧ 0 ≤ φ s(v, w)} +
      #{w | G.Adj v w ∧ G.Adj u w ∧ φ s(v, w) < 0 ∧ 0 ≤ φ s(u, w)} := by
  have huv' := hG u v huv
  have hku := fin3_neg_add_ne_left _ _ huv'
  have hkv := fin3_neg_add_ne_right _ _ huv'
  set k := -(part u + part v) with hk
  set Wp := univ.filter fun w => G.Adj u w ∧ G.Adj v w ∧ 0 ≤ φ s(u, w) ∧ 0 ≤ φ s(v, w) with hWp
  set Wu := univ.filter fun w => G.Adj u w ∧ G.Adj v w ∧ φ s(u, w) < 0 ∧ 0 ≤ φ s(v, w) with hWu
  set Wv := univ.filter fun w => G.Adj v w ∧ G.Adj u w ∧ φ s(v, w) < 0 ∧ 0 ≤ φ s(u, w) with hWv
  set Nu := univ.filter fun w => part w = k ∧ G.Adj u w with hNu
  set Nv := univ.filter fun w => part w = k ∧ G.Adj v w with hNv
  have h1 : (1 - d) * n ≤ (#Nu : ℝ) := hδ u k hku
  have h2 : (1 - d) * n ≤ (#Nv : ℝ) := hδ v k hkv
  have hU := card_union_add_card_inter Nu Nv
  have hUle : #(Nu ∪ Nv) ≤ n := by
    rw [← hn k]
    exact card_le_card fun w hw => by
      rcases mem_union.1 hw with h | h <;> exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 h).2.1⟩
  have hsub : Nu ∩ Nv ⊆ Wp ∪ Wu ∪ Wv := by
    intro w hw
    have huw := (mem_filter.1 (mem_inter.1 hw).1).2.2
    have hvw := (mem_filter.1 (mem_inter.1 hw).2).2.2
    rcases lt_or_ge (φ s(u, w)) 0 with a1 | a1 <;> rcases lt_or_ge (φ s(v, w)) 0 with a2 | a2
    · exfalso
      linarith [tri_sum hφ huv huw hvw]
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_filter.2 ⟨mem_univ _, huw, hvw, a1, a2⟩))))
    · exact mem_union.2 (Or.inr (mem_filter.2 ⟨mem_univ _, hvw, huw, a2, a1⟩))
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_filter.2 ⟨mem_univ _, huw, hvw, a1, a2⟩))))
  have h3 := card_le_card hsub
  have h4 := card_union_le (Wp ∪ Wu) Wv
  have h5 := card_union_le Wp Wu
  have hnat : #Nu + #Nv ≤ n + (#Wp + #Wu + #Wv) := by omega
  have : (#Nu : ℝ) + #Nv ≤ n + (#Wp + #Wu + #Wv) := by exact_mod_cast hnat
  linarith

theorem gd_le_aux {d x y c M1 M2 P Qu Qv : ℝ} (hc : 0 ≤ c) (hM1 : c ≤ M1) (hM2 : c ≤ M2)
    (hC : 1 - 2 * d ≤ P + Qu + Qv) (hQu : x - d ≤ Qu) (hQu0 : 0 ≤ Qu) (hQv : y - d ≤ Qv)
    (hQv0 : 0 ≤ Qv) :
    (M1 - c) * max (x - d) 0 + (M2 - c) * max (y - d) 0 + c * (1 - 2 * d) ≤
      c * P + M1 * Qu + M2 * Qv := by
  have h1 := mul_le_mul_of_nonneg_left (max_le hQu hQu0) (sub_nonneg.2 hM1)
  have h2 := mul_le_mul_of_nonneg_left (max_le hQv hQv0) (sub_nonneg.2 hM2)
  have h3 := mul_le_mul_of_nonneg_left hC hc
  linarith

/-- **Proposition 4.3.** Let `φ` be a triangle-covered balanced weighting of a tripartite graph
with parts of size `n` and minimum partite degree at least `(1 - d) n`. For every red edge `uv`
with `d_u ≥ d_v`, the numbers `x = d_u / n` and `y = d_v / n` satisfy `0 < y ≤ x < 1`,
`x + y ≤ 1`, and the weight `Δ(uv)` received by `uv` satisfies `g_d(x, y) ≤ Δ(uv) / |φ(uv)|`. -/
theorem prop_4_3 (hG : IsTripartite G part) (hn : ∀ i, #{v | part v = i} = n) {d : ℝ}
    (hδ : ∀ v (i : Fin 3), i ≠ part v → (1 - d) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (hfa : AntitoneOn f (Set.Icc 0 1))
    (hφ : IsTriangleCovered G φ) (hbal : IsBalanced G part φ) {u v : V} (huv : G.Adj u v)
    (hr : φ s(u, v) < 0) (hdeg : redDeg G part φ v ≤ redDeg G part φ u) :
    0 < (redDeg G part φ v : ℝ) / n ∧
      (redDeg G part φ v : ℝ) / n ≤ (redDeg G part φ u : ℝ) / n ∧
      (redDeg G part φ u : ℝ) / n < 1 ∧
      (redDeg G part φ u : ℝ) / n + (redDeg G part φ v : ℝ) / n ≤ 1 ∧
      gd f d ((redDeg G part φ u : ℝ) / n) ((redDeg G part φ v : ℝ) / n) ≤
        (∑ b ∈ G.edgeFinset, disE G part n f φ b s(u, v)) / |φ s(u, v)| := by
  have hvu : φ s(v, u) = φ s(u, v) := by rw [Sym2.eq_swap]
  have hdu1 : 1 ≤ redDeg G part φ u := one_le_redDeg hG hbal huv.symm (by rwa [hvu])
  have hdv1 : 1 ≤ redDeg G part φ v := one_le_redDeg hG hbal huv hr
  have hsum := redDeg_add_le hG hn hφ hbal huv hr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdu : (1 : ℝ) ≤ redDeg G part φ u := by exact_mod_cast hdu1
  have hdv : (1 : ℝ) ≤ redDeg G part φ v := by exact_mod_cast hdv1
  have hdvu : (redDeg G part φ v : ℝ) ≤ redDeg G part φ u := by exact_mod_cast hdeg
  have hsumR : (redDeg G part φ u : ℝ) + redDeg G part φ v ≤ n := by exact_mod_cast hsum
  have hy0 : 0 < (redDeg G part φ v : ℝ) / n := div_pos (by linarith) hn0
  have hyx : (redDeg G part φ v : ℝ) / n ≤ (redDeg G part φ u : ℝ) / n :=
    div_le_div_of_nonneg_right hdvu hn0.le
  have hX0 : 0 < (redDeg G part φ u : ℝ) / n := hy0.trans_le hyx
  have hx1 : (redDeg G part φ u : ℝ) / n < 1 := (div_lt_one hn0).2 (by linarith)
  have hxy1 : (redDeg G part φ u : ℝ) / n + (redDeg G part φ v : ℝ) / n ≤ 1 := by
    rw [← add_div, div_le_one hn0]
    exact hsumR
  refine ⟨hy0, hyx, hx1, hxy1, ?_⟩
  rw [sum_disE_mk_right huv.ne, le_div_iff₀ (abs_pos.2 hr.ne)]
  have hfx := hf ((redDeg G part φ u : ℝ) / n) ⟨hX0.le, hx1.le⟩
  have hw : ∀ w,
      (if G.Adj u w ∧ G.Adj v w ∧ 0 ≤ φ s(u, w) ∧ 0 ≤ φ s(v, w) then
          f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / n
        else 0) +
      (if G.Adj u w ∧ G.Adj v w ∧ φ s(u, w) < 0 ∧ 0 ≤ φ s(v, w) then
          M f ((redDeg G part φ v : ℝ) / n) (1 - (redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / n
        else 0) +
      (if G.Adj v w ∧ G.Adj u w ∧ φ s(v, w) < 0 ∧ 0 ≤ φ s(u, w) then
          M f ((redDeg G part φ u : ℝ) / n) (1 - (redDeg G part φ v : ℝ) / n) * |φ s(u, v)| / n
        else 0) ≤ dis G part n f φ u v w + dis G part n f φ v u w := by
    intro w
    have hd1 := dis_nonneg (G := G) (φ := φ) hn hf u v w
    have hd2 := dis_nonneg (G := G) (φ := φ) hn hf v u w
    by_cases huw : G.Adj u w
    swap
    · simp only [huw, false_and, and_false, ite_false]
      linarith
    by_cases hvw : G.Adj v w
    swap
    · simp only [hvw, false_and, and_false, ite_false]
      linarith
    rcases lt_or_ge (φ s(u, w)) 0 with h1 | h1 <;> rcases lt_or_ge (φ s(v, w)) 0 with h2 | h2
    · exfalso
      linarith [tri_sum hφ huv huw hvw]
    · -- `uvw` is quasi-negative and `vw` is its blue edge
      rw [ite_eq_right fun h => absurd h.2.2.1 (not_le.2 h1), ite_eq_left ⟨huw, hvw, h1, h2⟩,
        ite_eq_right fun h => absurd h.2.2.1 (not_lt.2 h2), zero_add, add_zero]
      have e : dis G part n f φ u v w = |φ s(u, v)| *
          (lam G part n f φ v w / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
            (1 - lam G part n f φ v w) / min (redDeg G part φ v : ℝ) (redDeg G part φ w)) := by
        unfold dis
        rw [ite_eq_left ⟨huv, hvw, huw, h2, hr⟩, ite_eq_right (not_le.2 h1)]
        ring
      have hq := qn_bound (G := G) (φ := φ) hn hf (p := v) (w := w) (dq := redDeg G part φ u)
        hdv1 (one_le_redDeg hG hbal huw h1)
        (by have := redDeg_add_le hG hn hφ hbal huw h1; omega)
      calc M f ((redDeg G part φ v : ℝ) / n) (1 - (redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / n
          = |φ s(u, v)| *
            (M f ((redDeg G part φ v : ℝ) / n) (1 - (redDeg G part φ u : ℝ) / n) / n) := by ring
        _ ≤ |φ s(u, v)| *
            (lam G part n f φ v w / max (redDeg G part φ v : ℝ) (redDeg G part φ w) +
              (1 - lam G part n f φ v w) / min (redDeg G part φ v : ℝ) (redDeg G part φ w)) :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
        _ = dis G part n f φ u v w := e.symm
        _ ≤ _ := le_add_of_nonneg_right hd2
    · -- `uvw` is quasi-negative and `uw` is its blue edge
      rw [ite_eq_right fun h => absurd h.2.2.2 (not_le.2 h2),
        ite_eq_right fun h => absurd h.2.2.1 (not_lt.2 h1), ite_eq_left ⟨hvw, huw, h2, h1⟩,
        zero_add, zero_add]
      have e : dis G part n f φ v u w = |φ s(u, v)| *
          (lam G part n f φ u w / max (redDeg G part φ u : ℝ) (redDeg G part φ w) +
            (1 - lam G part n f φ u w) / min (redDeg G part φ u : ℝ) (redDeg G part φ w)) := by
        unfold dis
        rw [ite_eq_left ⟨huv.symm, huw, hvw, h1, by rwa [hvu]⟩, ite_eq_right (not_le.2 h2), hvu]
        ring
      have hq := qn_bound (G := G) (φ := φ) hn hf (p := u) (w := w) (dq := redDeg G part φ v)
        hdu1 (one_le_redDeg hG hbal hvw h2)
        (by have := redDeg_add_le hG hn hφ hbal hvw h2; omega)
      calc M f ((redDeg G part φ u : ℝ) / n) (1 - (redDeg G part φ v : ℝ) / n) * |φ s(u, v)| / n
          = |φ s(u, v)| *
            (M f ((redDeg G part φ u : ℝ) / n) (1 - (redDeg G part φ v : ℝ) / n) / n) := by ring
        _ ≤ |φ s(u, v)| *
            (lam G part n f φ u w / max (redDeg G part φ u : ℝ) (redDeg G part φ w) +
              (1 - lam G part n f φ u w) / min (redDeg G part φ u : ℝ) (redDeg G part φ w)) :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
        _ = dis G part n f φ v u w := e.symm
        _ ≤ _ := le_add_of_nonneg_left hd1
    · -- `uvw` is quasi-positive
      rw [ite_eq_left ⟨huw, hvw, h1, h2⟩, ite_eq_right fun h => absurd h.2.2.1 (not_lt.2 h1),
        ite_eq_right fun h => absurd h.2.2.1 (not_lt.2 h2), add_zero, add_zero]
      have e1 : dis G part n f φ u v w =
          share G part n f φ v w * φ s(v, w) / redDeg G part φ v := by
        unfold dis
        rw [ite_eq_left ⟨huv, hvw, huw, h2, hr⟩, ite_eq_left h1]
      have e2 : dis G part n f φ v u w =
          share G part n f φ u w * φ s(u, w) / redDeg G part φ u := by
        unfold dis
        rw [ite_eq_left ⟨huv.symm, huw, hvw, h1, by rwa [hvu]⟩, ite_eq_left h2]
      have hs1 := share_ge (G := G) (φ := φ) hn hf v w
      have hs2 := share_ge (G := G) (φ := φ) hn hf u w
      have hfxy : f ((redDeg G part φ u : ℝ) / n) ≤ f ((redDeg G part φ v : ℝ) / n) :=
        hfa ⟨hy0.le, hyx.trans hx1.le⟩ ⟨hX0.le, hx1.le⟩ hyx
      have hA : |φ s(u, v)| ≤ φ s(u, w) + φ s(v, w) := by
        rw [abs_of_neg hr]
        linarith [tri_sum hφ huv huw hvw]
      have k1 : f ((redDeg G part φ u : ℝ) / n) / redDeg G part φ u ≤
          share G part n f φ v w / redDeg G part φ v :=
        (div_le_div_of_nonneg_left hfx.1 (by linarith) hdvu).trans
          (div_le_div_of_nonneg_right (hfxy.trans hs1) (by linarith))
      have k2 : f ((redDeg G part φ u : ℝ) / n) / redDeg G part φ u ≤
          share G part n f φ u w / redDeg G part φ u :=
        div_le_div_of_nonneg_right hs2 (by linarith)
      have hXn : (redDeg G part φ u : ℝ) / n * n = redDeg G part φ u := div_mul_cancel₀ _ hn0.ne'
      rw [e1, e2]
      calc f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / n
          = f ((redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / ((redDeg G part φ u : ℝ) / n * n) := by
            ring
        _ = f ((redDeg G part φ u : ℝ) / n) / redDeg G part φ u * |φ s(u, v)| := by
            rw [hXn]
            ring
        _ ≤ f ((redDeg G part φ u : ℝ) / n) / redDeg G part φ u * (φ s(u, w) + φ s(v, w)) :=
            mul_le_mul_of_nonneg_left hA (div_nonneg hfx.1 (by linarith))
        _ = f ((redDeg G part φ u : ℝ) / n) / redDeg G part φ u * φ s(v, w) +
              f ((redDeg G part φ u : ℝ) / n) / redDeg G part φ u * φ s(u, w) := by ring
        _ ≤ share G part n f φ v w / redDeg G part φ v * φ s(v, w) +
              share G part n f φ u w / redDeg G part φ u * φ s(u, w) :=
            add_le_add (mul_le_mul_of_nonneg_right k1 h2) (mul_le_mul_of_nonneg_right k2 h1)
        _ = _ := by ring
  have hc : 0 ≤ f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) :=
    div_nonneg hfx.1 hX0.le
  have hcx : f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) ≤
      1 / (2 * ((redDeg G part φ u : ℝ) / n)) :=
    calc _ ≤ 1 / 2 / ((redDeg G part φ u : ℝ) / n) := div_le_div_of_nonneg_right hfx.2 hX0.le
      _ = _ := by ring
  have hM1 : f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) ≤
      M f ((redDeg G part φ v : ℝ) / n) (1 - (redDeg G part φ u : ℝ) / n) :=
    hcx.trans ((one_div_le_one_div_of_le (by positivity) (by linarith)).trans
      (le_M hf hy0 (by linarith)))
  have hM2 : f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) ≤
      M f ((redDeg G part φ u : ℝ) / n) (1 - (redDeg G part φ v : ℝ) / n) :=
    hcx.trans (le_M hf hX0 (by linarith))
  have hC := card_common_ge hG hn hδ hφ huv hr
  have hQu := card_red_blue_ge hG hn hδ hφ hbal huv hr
  have hQv := card_red_blue_ge hG hn hδ hφ hbal huv.symm (by rwa [hvu])
  have aux := gd_le_aux (d := d) hc hM1 hM2
    (P := (#{w | G.Adj u w ∧ G.Adj v w ∧ 0 ≤ φ s(u, w) ∧ 0 ≤ φ s(v, w)} : ℝ) / n)
    (Qu := (#{w | G.Adj u w ∧ G.Adj v w ∧ φ s(u, w) < 0 ∧ 0 ≤ φ s(v, w)} : ℝ) / n)
    (Qv := (#{w | G.Adj v w ∧ G.Adj u w ∧ φ s(v, w) < 0 ∧ 0 ≤ φ s(u, w)} : ℝ) / n)
    (by rw [← add_div, ← add_div, le_div_iff₀ hn0]; exact hC)
    (by rw [le_div_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']; exact hQu)
    (div_nonneg (Nat.cast_nonneg _) hn0.le)
    (by rw [le_div_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']; exact hQv)
    (div_nonneg (Nat.cast_nonneg _) hn0.le)
  calc gd f d ((redDeg G part φ u : ℝ) / n) ((redDeg G part φ v : ℝ) / n) * |φ s(u, v)|
      ≤ (f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) *
            ((#{w | G.Adj u w ∧ G.Adj v w ∧ 0 ≤ φ s(u, w) ∧ 0 ≤ φ s(v, w)} : ℝ) / n) +
          M f ((redDeg G part φ v : ℝ) / n) (1 - (redDeg G part φ u : ℝ) / n) *
            ((#{w | G.Adj u w ∧ G.Adj v w ∧ φ s(u, w) < 0 ∧ 0 ≤ φ s(v, w)} : ℝ) / n) +
          M f ((redDeg G part φ u : ℝ) / n) (1 - (redDeg G part φ v : ℝ) / n) *
            ((#{w | G.Adj v w ∧ G.Adj u w ∧ φ s(v, w) < 0 ∧ 0 ≤ φ s(u, w)} : ℝ) / n)) *
          |φ s(u, v)| := mul_le_mul_of_nonneg_right aux (abs_nonneg _)
    _ = ∑ w,
        ((if G.Adj u w ∧ G.Adj v w ∧ 0 ≤ φ s(u, w) ∧ 0 ≤ φ s(v, w) then
            f ((redDeg G part φ u : ℝ) / n) / ((redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / n
          else 0) +
        (if G.Adj u w ∧ G.Adj v w ∧ φ s(u, w) < 0 ∧ 0 ≤ φ s(v, w) then
            M f ((redDeg G part φ v : ℝ) / n) (1 - (redDeg G part φ u : ℝ) / n) * |φ s(u, v)| / n
          else 0) +
        (if G.Adj v w ∧ G.Adj u w ∧ φ s(v, w) < 0 ∧ 0 ≤ φ s(u, w) then
            M f ((redDeg G part φ u : ℝ) / n) (1 - (redDeg G part φ v : ℝ) / n) * |φ s(u, v)| / n
          else 0)) := by
      rw [sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter, ← sum_filter, sum_const,
        sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
      ring
    _ ≤ _ := sum_le_sum fun w _ => hw w

/-! ### Theorem 1.3 from Proposition 4.4 -/

/-- **Theorem 1.3, assuming the numerical Proposition 4.4.** Let `f : [0, 1] → [0, 1/2]` be
non-increasing and suppose `g_d(x, y) ≥ 1` whenever `0 < y ≤ x < 1` and `x + y ≤ 1`. Then every
`K₃`-divisible tripartite graph with parts of size `n` and minimum partite degree at least
`(1 - d) n` has a fractional triangle decomposition. -/
theorem fracDecomp_of_gd (hG : IsTripartite G part) (hdiv : IsK3Divisible G part)
    (hn : ∀ i, #{v | part v = i} = n) {d : ℝ}
    (hδ : ∀ v (i : Fin 3), i ≠ part v → (1 - d) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (hfa : AntitoneOn f (Set.Icc 0 1))
    (hnum : ∀ x y : ℝ, 0 < y → y ≤ x → x < 1 → x + y ≤ 1 → 1 ≤ gd f d x y) :
    ∃ w, IsFracTriangleDecomp G w := by
  by_contra hno
  obtain ⟨φ, hφc, hφn, hbal, -, -⟩ := (cor_3_5 hG hdiv).1 hno
  have key : ∀ a b : V, G.Adj a b → φ s(a, b) < 0 →
      redDeg G part φ b ≤ redDeg G part φ a →
      0 ≤ φ s(a, b) + ∑ c ∈ G.edgeFinset, disE G part n f φ c s(a, b) := by
    intro a b hab hneg hle
    obtain ⟨h1, h2, h3, h4, h5⟩ := prop_4_3 hG hn hδ hf hfa hφc hbal hab hneg hle
    have := (hnum _ _ h1 h2 h3 h4).trans h5
    rw [le_div_iff₀ (abs_pos.2 hneg.ne), one_mul, abs_of_neg hneg] at this
    linarith
  have hterm : ∀ e ∈ G.edgeFinset, 0 ≤ φ e - ∑ r ∈ G.edgeFinset, disE G part n f φ e r +
      ∑ b ∈ G.edgeFinset, disE G part n f φ b e := by
    intro e he
    rcases le_or_gt 0 (φ e) with h | h
    · have h0 : ∑ b ∈ G.edgeFinset, disE G part n f φ b e = 0 := sum_eq_zero fun b _ => by
        by_contra hc
        exact absurd (disE_ne_zero hc).2.2.2 (not_lt.2 h)
      rw [h0, add_zero]
      exact prop_4_2 hG hn hf hφc hbal he h
    · have h0 : ∑ r ∈ G.edgeFinset, disE G part n f φ e r = 0 := sum_eq_zero fun r _ => by
        by_contra hc
        exact absurd (disE_ne_zero hc).2.2.1 (not_le.2 h)
      rw [h0, sub_zero]
      induction e using Sym2.ind with
      | _ a b =>
      have hab : G.Adj a b := by simpa using he
      rcases le_total (redDeg G part φ b) (redDeg G part φ a) with hle | hle
      · exact key a b hab h hle
      · have := key b a hab.symm (by rwa [Sym2.eq_swap]) hle
        rwa [Sym2.eq_swap] at this
  have hsum : ∑ e ∈ G.edgeFinset, (φ e - ∑ r ∈ G.edgeFinset, disE G part n f φ e r +
      ∑ b ∈ G.edgeFinset, disE G part n f φ b e) = ∑ e ∈ G.edgeFinset, φ e := by
    rw [sum_add_distrib, sum_sub_distrib, sum_comm]
    ring
  unfold IsTotallyNegative at hφn
  linarith [sum_nonneg hterm]

end ABLP
