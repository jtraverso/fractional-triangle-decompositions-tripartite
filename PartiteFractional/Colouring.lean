/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Network

/-!
# A red-balanced colouring (Claim 3.4.1 and the colouring of Lemma 3.4)

An integral flow of value `C = ∑_v max(w(v), 0)` in the network of Claim 3.4.1 saturates the arcs
leaving the source and, since `∑_v w(v) = 0`, the arcs entering the sink. Its value on a zero edge
`uv` with `u ≺ v` is `0` or `1`; let `R₀` be the zero edges carrying one unit. Conservation at `v`
gives `|R₀ leaving v| - |R₀ entering v| = w(v) = n_in(v) - n_out(v)`, so the negative edges
together with `R₀` meet every vertex in as many edges from the previous part as from the next.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {part : V → Fin 3}

variable (part) in
/-- A set of edges is **red-balanced** if every vertex meets as many of its edges from the
previous part as from the next. -/
def RedBalanced (R : Finset (Sym2 V)) : Prop :=
  ∀ v, #{u | part u = part v - 1 ∧ s(u, v) ∈ R} = #{u | part u = part v + 1 ∧ s(u, v) ∈ R}

/-- `∑_v w(v) = 0`: as many negative edges leave vertices forwards as enter them. -/
theorem sum_demand_univ (ψ : Sym2 V → ℝ) : ∑ v, (demand G part ψ v : ℝ) = 0 := by
  rw [sum_demand]
  simp [crossCount, ind]

section Flow

open Contrib.MaxFlowMinCut

variable {ψ : Sym2 V → ℝ} (F : Flow (network G part ψ))

theorem flow_self (a : Option (Option V)) : F.f a a = 0 := by
  have := F.skew a a
  linarith

theorem flow_le_cap (a b : Option (Option V)) : F.f a b ≤ (netCap G part ψ a b : ℝ) :=
  F.capacitated a b

/-- The value splits over the source arcs. -/
theorem value_eq (F : Flow (network G part ψ)) :
    F.value = F.f none (some none) + ∑ v, F.f none (some (some v)) := by
  change ∑ x, F.f none x = _
  rw [Fintype.sum_option, Fintype.sum_option, flow_self, zero_add]

/-- Flow of value at least `C` saturates every source arc. -/
theorem source_saturated (hval : ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) ≤ F.value)
    (v : V) : F.f none (some (some v)) = ((max (demand G part ψ v) 0 : ℤ) : ℝ) := by
  have hst : F.f none (some none) ≤ 0 := by
    have := flow_le_cap F none (some none); simpa using this
  have hle : ∀ u, F.f none (some (some u)) ≤ ((max (demand G part ψ u) 0 : ℤ) : ℝ) :=
    fun u => flow_le_cap F none (some (some u))
  rw [value_eq] at hval
  have hsum : ∑ u, (((max (demand G part ψ u) 0 : ℤ) : ℝ) - F.f none (some (some u))) = 0 := by
    have h0 : 0 ≤ ∑ u, (((max (demand G part ψ u) 0 : ℤ) : ℝ) - F.f none (some (some u))) :=
      sum_nonneg fun u _ => sub_nonneg.2 (hle u)
    rw [sum_sub_distrib] at h0 ⊢
    linarith
  have := (sum_eq_zero_iff_of_nonneg fun u _ => sub_nonneg.2 (hle u)).1 hsum v (mem_univ v)
  linarith

/-- The total of the skew flow over all ordered pairs vanishes. -/
theorem sum_sum_flow : ∑ a, ∑ b, F.f a b = 0 := by
  have h : ∑ a, ∑ b, F.f a b = -∑ a, ∑ b, F.f a b := by
    conv_rhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun a _ => by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun b _ => F.skew a b
  linarith

/-- Flow into the sink equals the value. -/
theorem sink_inflow : F.f none (some none) + ∑ v, F.f (some (some v)) (some none) = F.value := by
  have htot := sum_sum_flow F
  rw [Fintype.sum_option (fun a => ∑ b, F.f a b),
    Fintype.sum_option (fun a => ∑ b, F.f (some a) b)] at htot
  have hcons : ∀ v : V, ∑ b, F.f (some (some v)) b = 0 :=
    fun v => F.conserved _ (by simp [network]) (by simp [network])
  simp only [hcons, sum_const_zero, add_zero] at htot
  have hrow : ∑ b, F.f (some none) b =
      -(F.f none (some none) + ∑ v, F.f (some (some v)) (some none)) := by
    rw [Fintype.sum_option, Fintype.sum_option, flow_self, F.skew (some none) none, neg_add,
      ← sum_neg_distrib]
    simp only [zero_add]
    congr 1
    exact sum_congr rfl fun v _ => F.skew _ _
  have hval : ∑ b, F.f none b = F.value := rfl
  linarith

/-- Flow of value at least `C` saturates every sink arc. -/
theorem sink_saturated (hval : ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) ≤ F.value) (v : V) :
    F.f (some (some v)) (some none) = ((max (-demand G part ψ v) 0 : ℤ) : ℝ) := by
  have hst : F.f none (some none) ≤ 0 := by
    have := flow_le_cap F none (some none); simpa using this
  have hle : ∀ u, F.f (some (some u)) (some none) ≤ ((max (-demand G part ψ u) 0 : ℤ) : ℝ) :=
    fun u => flow_le_cap F (some (some u)) (some none)
  have hin := sink_inflow F
  have hC : ∑ u, ((max (-demand G part ψ u) 0 : ℤ) : ℝ) =
      ∑ u, ((max (demand G part ψ u) 0 : ℤ) : ℝ) := by
    have h0 := sum_demand_univ (G := G) (part := part) ψ
    have : ∀ u, ((max (-demand G part ψ u) 0 : ℤ) : ℝ) =
        ((max (demand G part ψ u) 0 : ℤ) : ℝ) - (demand G part ψ u : ℝ) := by
      intro u
      rcases le_total (demand G part ψ u) 0 with h | h
      · rw [max_eq_left (by omega), max_eq_right h]; push_cast; ring
      · rw [max_eq_right (by omega), max_eq_left h]; push_cast; ring
    simp_rw [this, sum_sub_distrib, h0, sub_zero]
  have hsum : ∑ u, (((max (-demand G part ψ u) 0 : ℤ) : ℝ) -
      F.f (some (some u)) (some none)) = 0 := by
    have h0 : 0 ≤ ∑ u, (((max (-demand G part ψ u) 0 : ℤ) : ℝ) -
        F.f (some (some u)) (some none)) :=
      sum_nonneg fun u _ => sub_nonneg.2 (hle u)
    rw [sum_sub_distrib] at h0 ⊢
    linarith
  have := (sum_eq_zero_iff_of_nonneg fun u _ => sub_nonneg.2 (hle u)).1 hsum v (mem_univ v)
  linarith

/-- The flow between two vertices: one unit along a used zero edge, in either direction. -/
theorem flow_vertex (hF : IntFlow.IsIntegral F) (u v : V) :
    F.f (some (some u)) (some (some v)) =
      (if ZeroArc G part ψ u v ∧ F.f (some (some u)) (some (some v)) = 1 then 1 else 0) -
        (if ZeroArc G part ψ v u ∧ F.f (some (some v)) (some (some u)) = 1 then 1 else 0) := by
  have h1 := flow_le_cap F (some (some u)) (some (some v))
  have h2 := flow_le_cap F (some (some v)) (some (some u))
  have hsk := F.skew (some (some u)) (some (some v))
  obtain ⟨z, hz⟩ := hF (some (some u)) (some (some v))
  simp only [netCap_vertex_vertex] at h1 h2
  by_cases huv : ZeroArc G part ψ u v
  · have hvu : ¬ ZeroArc G part ψ v u := fun h => not_prec_of_prec part huv.2.1 h.2.1
    simp only [huv, hvu, ite_true, ite_false, Int.cast_one, Int.cast_zero] at h1 h2
    have : 0 ≤ z ∧ z ≤ 1 := by
      constructor
      · have : (0 : ℝ) ≤ z := by linarith
        exact_mod_cast this
      · have : (z : ℝ) ≤ 1 := by linarith
        exact_mod_cast this
    rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl <;> simp_all
  · by_cases hvu : ZeroArc G part ψ v u
    · simp only [huv, hvu, ite_true, ite_false, Int.cast_one, Int.cast_zero] at h1 h2
      have : -1 ≤ z ∧ z ≤ 0 := by
        constructor
        · have : (-1 : ℝ) ≤ z := by linarith
          exact_mod_cast this
        · have : (z : ℝ) ≤ 0 := by linarith
          exact_mod_cast this
      rcases (show z = -1 ∨ z = 0 by omega) with rfl | rfl <;> simp_all <;> linarith
    · simp only [huv, hvu, false_and, ite_false, Int.cast_zero, sub_zero] at h1 h2 ⊢
      linarith

end Flow

section Red

open Contrib.MaxFlowMinCut

variable {ψ : Sym2 V → ℝ} (F : Flow (network G part ψ))

/-- A zero edge `uv` with `u ≺ v` carrying one unit of flow. -/
def Used (u v : V) : Prop :=
  ZeroArc G part ψ u v ∧ F.f (some (some u)) (some (some v)) = 1

noncomputable instance : DecidableRel (Used F) := fun _ _ => by unfold Used; infer_instance

/-- Conservation at `v`: the flow from `v` to the other vertices is `w(v)`. -/
theorem flow_out_vertex (hval : ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) ≤ F.value) (v : V) :
    ∑ u, F.f (some (some v)) (some (some u)) = (demand G part ψ v : ℝ) := by
  have hc := F.conserved (some (some v)) (by simp [network]) (by simp [network])
  rw [Fintype.sum_option (fun b => F.f (some (some v)) b),
    Fintype.sum_option (fun b => F.f (some (some v)) (some b))] at hc
  rw [F.skew, source_saturated F hval, sink_saturated F hval] at hc
  have : ((max (demand G part ψ v) 0 : ℤ) : ℝ) - ((max (-demand G part ψ v) 0 : ℤ) : ℝ) =
      (demand G part ψ v : ℝ) := by
    rcases le_total (demand G part ψ v) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by omega)]; push_cast; ring
    · rw [max_eq_left h, max_eq_right (by omega)]; push_cast; ring
  linarith

/-- Used edges leaving `v` minus used edges entering `v` is `w(v)`. -/
theorem used_balance (hF : IntFlow.IsIntegral F)
    (hval : ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) ≤ F.value) (v : V) :
    (#{u | Used F v u} : ℝ) - #{u | Used F u v} = (demand G part ψ v : ℝ) := by
  rw [← flow_out_vertex F hval v, natCast_card_filter, natCast_card_filter, ← sum_sub_distrib]
  exact sum_congr rfl fun u _ => by rw [flow_vertex F hF v u]; rfl

variable (ψ) in
/-- The red edges: the negative edges and the used zero edges. -/
noncomputable def redSet : Finset (Sym2 V) :=
  ((arcs G part).filter fun x => ψ s(x.1, x.2) < 0 ∨ Used F x.1 x.2).image fun x => s(x.1, x.2)

theorem mem_redSet {u v : V} (h : Prec part u v) :
    s(u, v) ∈ redSet ψ F ↔ G.Adj u v ∧ (ψ s(u, v) < 0 ∨ Used F u v) := by
  constructor
  · intro hm
    obtain ⟨x, hx, hxe⟩ := mem_image.1 hm
    obtain ⟨hxa, hxp⟩ := mem_filter.1 hx
    obtain ⟨hadj, hprec⟩ := (mem_filter.1 hxa).2
    rcases Sym2.eq_iff.1 hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      exact ⟨hadj, hxp⟩
    · subst h1; subst h2
      exact absurd hprec (not_prec_of_prec part h)
  · rintro ⟨hadj, hp⟩
    exact mem_image.2 ⟨(u, v), mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hadj, h⟩, hp⟩, rfl⟩

theorem redSet_subset : redSet ψ F ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := mem_image.1 he
  exact mem_edgeFinset.2 ((mem_filter.1 (mem_filter.1 hx).1).2.1)

theorem le_zero_of_mem_redSet {e : Sym2 V} (he : e ∈ redSet ψ F) : ψ e ≤ 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_image.1 he
  rcases (mem_filter.1 hx).2 with h | h
  · exact h.le
  · exact h.1.2.2.le

theorem mem_redSet_of_neg (hG : IsTripartite G part) {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (hneg : ψ e < 0) : e ∈ redSet ψ F := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := by simpa using he
    rcases prec_or_prec part (hG a b hab) with h | h
    · exact (mem_redSet F h).2 ⟨hab, Or.inl hneg⟩
    · rw [Sym2.eq_swap]
      exact (mem_redSet F h).2 ⟨hab.symm, Or.inl (by rwa [Sym2.eq_swap])⟩

/-- **The red set is red-balanced.** -/
theorem redSet_balanced (hF : IntFlow.IsIntegral F)
    (hval : ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) ≤ F.value) :
    RedBalanced part (redSet ψ F) := by
  intro v
  have hin : (#{u | part u = part v - 1 ∧ s(u, v) ∈ redSet ψ F} : ℝ) =
      (nIn G part ψ v : ℝ) + #{u | Used F u v} := by
    rw [nIn, natCast_card_filter, natCast_card_filter, natCast_card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    by_cases hp : Prec part u v
    · have hp' : part u = part v - 1 := (prec_iff_left u v).1 hp
      simp only [mem_redSet F hp]
      by_cases hU : Used F u v
      · have hz : ψ s(u, v) = 0 := hU.1.2.2
        simp [hp', hp, hU, hU.1.1, hz]
      · by_cases hadj : G.Adj u v <;> by_cases hn : ψ s(u, v) < 0 <;> simp [hp', hp, hU, hadj, hn]
    · have hp' : ¬ part u = part v - 1 := fun h => hp ((prec_iff_left u v).2 h)
      have hU : ¬ Used F u v := fun h => hp h.1.2.1
      simp [hp', hp, hU]
  have hout : (#{u | part u = part v + 1 ∧ s(u, v) ∈ redSet ψ F} : ℝ) =
      (nOut G part ψ v : ℝ) + #{u | Used F v u} := by
    rw [nOut, natCast_card_filter, natCast_card_filter, natCast_card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    by_cases hp : Prec part v u
    · have hp' : part u = part v + 1 := hp
      have hm : s(u, v) ∈ redSet ψ F ↔ G.Adj v u ∧ (ψ s(v, u) < 0 ∨ Used F v u) := by
        rw [Sym2.eq_swap]; exact mem_redSet F hp
      simp only [hm]
      by_cases hU : Used F v u
      · have hz : ψ s(v, u) = 0 := hU.1.2.2
        simp [hp', hp, hU, hU.1.1, hz]
      · by_cases hadj : G.Adj v u <;> by_cases hn : ψ s(v, u) < 0 <;> simp [hp', hp, hU, hadj, hn]
    · have hp' : ¬ part u = part v + 1 := hp
      have hU : ¬ Used F v u := fun h => hp h.1.2.1
      simp [hp', hp, hU]
  have hb := used_balance F hF hval v
  have hd : (demand G part ψ v : ℝ) = (nIn G part ψ v : ℝ) - nOut G part ψ v := by
    simp [demand]
  have : (#{u | part u = part v - 1 ∧ s(u, v) ∈ redSet ψ F} : ℝ) =
      #{u | part u = part v + 1 ∧ s(u, v) ∈ redSet ψ F} := by
    rw [hin, hout]; linarith
  exact_mod_cast this

end Red

end ABLP
