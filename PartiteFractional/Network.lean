/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.LocalMin
public import PartiteFractional.IntFlow

/-!
# The flow network of Claim 3.4.1

For an edge weighting `ψ` of a tripartite graph let `w(v) = n_in(v) - n_out(v)`, the number of
negative edges `uv` with `u ≺ v` minus the number of negative edges `vu` with `v ≺ u`. The network
has a source `s`, a sink `t` and the vertices of `G`: an arc `s → v` of capacity `max(w(v), 0)`,
an arc `v → t` of capacity `max(-w(v), 0)`, and an arc `u → v` of capacity one for every zero edge
`uv` with `u ≺ v`. A cut `S ∪ {s}` has capacity
`∑_{v ∉ S} max(w(v), 0) + ∑_{v ∈ S} max(-w(v), 0) + z_out(S) = C - w(S) + z_out(S)`, where
`C = ∑_v max(w(v), 0)`; inequality (5) gives `w(S) ≤ z_out(S)`, so every cut has capacity at
least `C`.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (part : V → Fin 3) (ψ : Sym2 V → ℝ)

/-- Negative edges entering `v` from the previous part. -/
noncomputable def nIn (v : V) : ℕ := #{u | G.Adj u v ∧ Prec part u v ∧ ψ s(u, v) < 0}

/-- Negative edges leaving `v` to the next part. -/
noncomputable def nOut (v : V) : ℕ := #{u | G.Adj v u ∧ Prec part v u ∧ ψ s(v, u) < 0}

/-- The demand `w(v) = n_in(v) - n_out(v)`. -/
noncomputable def demand (v : V) : ℤ := (nIn G part ψ v : ℤ) - nOut G part ψ v

/-- `uv` is a zero edge with `u ≺ v`. -/
def ZeroArc (u v : V) : Prop := G.Adj u v ∧ Prec part u v ∧ ψ s(u, v) = 0

noncomputable instance : DecidableRel (ZeroArc G part ψ) := fun _ _ => by unfold ZeroArc; infer_instance

/-- The capacities of the network on `Option (Option V)`: `none` is the source, `some none` the
sink, `some (some v)` the vertex `v`. -/
noncomputable def netCap : Option (Option V) → Option (Option V) → ℤ
  | none, some (some v) => max (demand G part ψ v) 0
  | some (some v), some none => max (-demand G part ψ v) 0
  | some (some u), some (some v) => if ZeroArc G part ψ u v then 1 else 0
  | _, _ => 0

@[simp] theorem netCap_source_vertex (v : V) :
    netCap G part ψ none (some (some v)) = max (demand G part ψ v) 0 := rfl

@[simp] theorem netCap_vertex_sink (v : V) :
    netCap G part ψ (some (some v)) (some none) = max (-demand G part ψ v) 0 := rfl

@[simp] theorem netCap_vertex_vertex (u v : V) :
    netCap G part ψ (some (some u)) (some (some v)) = if ZeroArc G part ψ u v then 1 else 0 := rfl

@[simp] theorem netCap_source_source : netCap G part ψ none none = 0 := rfl

@[simp] theorem netCap_source_sink : netCap G part ψ none (some none) = 0 := rfl

@[simp] theorem netCap_vertex_source (v : V) : netCap G part ψ (some (some v)) none = 0 := rfl

@[simp] theorem netCap_sink (b : Option (Option V)) : netCap G part ψ (some none) b = 0 := by
  rcases b with _ | _ | _ <;> rfl

theorem netCap_nonneg (a b : Option (Option V)) : 0 ≤ netCap G part ψ a b := by
  rcases a with _ | _ | u <;> rcases b with _ | _ | v <;> simp only [netCap] <;>
    first | exact le_rfl | exact le_max_right _ _ | (split_ifs <;> norm_num)

/-- The network of Claim 3.4.1. -/
noncomputable def network : Contrib.MaxFlowMinCut.Network (Option (Option V)) where
  cap a b := netCap G part ψ a b
  capNonneg a b := by exact_mod_cast netCap_nonneg G part ψ a b
  s := none
  t := some none
  st := by simp

theorem network_intCaps : IntFlow.IntCaps (network G part ψ) := fun a b => ⟨_, rfl⟩

variable {G part ψ}

/-- `z_out(S)` as a double sum. -/
theorem crossCount_zero_out (S : Finset V) :
    crossCount (G := G) (part := part) ψ S true (· = 0) =
      ∑ u, ∑ v, if u ∈ S ∧ v ∉ S ∧ ZeroArc G part ψ u v then (1 : ℝ) else 0 := by
  rw [crossCount, sum_arcs_eq]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  simp only [ite_true, ind, ZeroArc, mul_ite, mul_one, mul_zero]
  by_cases h1 : G.Adj u v <;> by_cases h2 : Prec part u v <;> by_cases h3 : u ∈ S <;>
    by_cases h4 : v ∈ S <;> by_cases h5 : ψ s(u, v) = 0 <;> simp [h1, h2, h3, h4, h5]

/-- `∑_{v ∈ S} n_in(v)` and `∑_{v ∈ S} n_out(v)` as sums over the arcs. -/
theorem sum_nIn (S : Finset V) :
    ∑ v ∈ S, (nIn G part ψ v : ℝ) =
      ∑ x ∈ arcs G part, ind (x.2 ∈ S) * ind (ψ s(x.1, x.2) < 0) := by
  calc ∑ v ∈ S, (nIn G part ψ v : ℝ) = ∑ v, if v ∈ S then (nIn G part ψ v : ℝ) else 0 := by
        rw [sum_ite_mem, univ_inter]
    _ = ∑ v, ∑ u, if G.Adj u v ∧ Prec part u v then
          ind (v ∈ S) * ind (ψ s(u, v) < 0) else 0 := sum_congr rfl fun v _ => by
        by_cases hv : v ∈ S
        · rw [ite_eq_left hv, nIn, natCast_card_filter]
          refine sum_congr rfl fun u _ => ?_
          by_cases h1 : G.Adj u v <;> by_cases h2 : Prec part u v <;>
            by_cases h3 : ψ s(u, v) < 0 <;> simp [ind, hv, h1, h2, h3]
        · rw [ite_eq_right hv]
          exact (sum_eq_zero fun u _ => by simp [ind, hv]).symm
    _ = _ := by rw [sum_arcs_eq, sum_comm]

theorem sum_nOut (S : Finset V) :
    ∑ v ∈ S, (nOut G part ψ v : ℝ) =
      ∑ x ∈ arcs G part, ind (x.1 ∈ S) * ind (ψ s(x.1, x.2) < 0) := by
  calc ∑ v ∈ S, (nOut G part ψ v : ℝ) = ∑ u, if u ∈ S then (nOut G part ψ u : ℝ) else 0 := by
        rw [sum_ite_mem, univ_inter]
    _ = ∑ u, ∑ v, if G.Adj u v ∧ Prec part u v then
          ind (u ∈ S) * ind (ψ s(u, v) < 0) else 0 := sum_congr rfl fun u _ => by
        by_cases hu : u ∈ S
        · rw [ite_eq_left hu, nOut, natCast_card_filter]
          refine sum_congr rfl fun v _ => ?_
          by_cases h1 : G.Adj u v <;> by_cases h2 : Prec part u v <;>
            by_cases h3 : ψ s(u, v) < 0 <;> simp [ind, hu, h1, h2, h3]
        · rw [ite_eq_right hu]
          exact (sum_eq_zero fun v _ => by simp [ind, hu]).symm
    _ = _ := by rw [sum_arcs_eq]

/-- `w(S) = n_in(S) - n_out(S)`: the edges inside `S` cancel. -/
theorem sum_demand (S : Finset V) :
    ∑ v ∈ S, (demand G part ψ v : ℝ) =
      crossCount (G := G) (part := part) ψ S false (· < 0) -
        crossCount (G := G) (part := part) ψ S true (· < 0) := by
  have h : ∑ v ∈ S, (demand G part ψ v : ℝ) =
      ∑ v ∈ S, (nIn G part ψ v : ℝ) - ∑ v ∈ S, (nOut G part ψ v : ℝ) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun v _ => by simp [demand]
  rw [h, sum_nIn, sum_nOut, crossCount, crossCount, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [Bool.false_eq_true, ite_true, ite_false]
  unfold ind
  by_cases h1 : x.1 ∈ S <;> by_cases h2 : x.2 ∈ S <;> simp [h1, h2]

theorem sum_mem_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) (f : α → ℝ) :
    ∑ a ∈ T, f a = ∑ a, if a ∈ T then f a else 0 := by
  rw [sum_ite_mem, univ_inter]

theorem sum_sdiff_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α)
    (f : α → ℝ) : ∑ a ∈ univ \ T, f a = ∑ a, if a ∈ T then 0 else f a := by
  rw [sdiff_eq_filter, sum_filter]
  exact sum_congr rfl fun a _ => by by_cases h : a ∈ T <;> simp [h]

/-- The capacity of a cut of the network of Claim 3.4.1. -/
theorem cut_capacity_eq (C : Contrib.MaxFlowMinCut.Cut (network G part ψ)) :
    C.capacity =
      (∑ v, if some (some v) ∈ C.S then 0 else ((max (demand G part ψ v) 0 : ℤ) : ℝ)) +
      (∑ v, if some (some v) ∈ C.S then ((max (-demand G part ψ v) 0 : ℤ) : ℝ) else 0) +
      ∑ u, ∑ v, if some (some u) ∈ C.S ∧ some (some v) ∉ C.S ∧ ZeroArc G part ψ u v
        then (1 : ℝ) else 0 := by
  have hs : (none : Option (Option V)) ∈ C.S := C.hs
  have ht : (some none : Option (Option V)) ∉ C.S := C.ht
  unfold Contrib.MaxFlowMinCut.Cut.capacity
  simp_rw [sum_sdiff_eq_sum_ite C.S]
  rw [sum_mem_eq_sum_ite C.S]
  simp only [Fintype.sum_option, hs, ht, ite_true, ite_false, network, netCap_source_vertex,
    netCap_vertex_sink, netCap_vertex_vertex, netCap_source_source, netCap_source_sink,
    netCap_vertex_source, netCap_sink, Int.cast_zero, sum_const_zero, zero_add, add_zero]
  rw [add_assoc]
  repeat rw [← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : some (some u) ∈ C.S
  · simp only [hu, ite_true, true_and, zero_add]
    congr 1
    refine sum_congr rfl fun v _ => ?_
    by_cases hv : some (some v) ∈ C.S <;> by_cases hz : ZeroArc G part ψ u v <;> simp [hv, hz]
  · simp only [hu, ite_false, false_and, sum_const_zero]
    ring

/-- **Every cut has capacity at least `C = ∑_v max(w(v), 0)`** (the cut condition of
Claim 3.4.1), from inequality (5). -/
theorem cut_capacity_ge (hG : IsTripartite G part) (hdiv : IsK3Divisible G part)
    (hmin : ∀ q : V → ℝ, l1 G ψ ≤ l1 G (translate part ψ q))
    (C : Contrib.MaxFlowMinCut.Cut (network G part ψ)) :
    ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) ≤ C.capacity := by
  set S : Finset V := univ.filter fun v => some (some v) ∈ C.S
  have h5 := (crossing_ineqs G part hG hdiv hmin S).1
  rw [← sum_demand, crossCount_zero_out] at h5
  rw [cut_capacity_eq]
  have hz : ∑ u, ∑ v, (if some (some u) ∈ C.S ∧ some (some v) ∉ C.S ∧ ZeroArc G part ψ u v
      then (1 : ℝ) else 0) = ∑ u, ∑ v, if u ∈ S ∧ v ∉ S ∧ ZeroArc G part ψ u v then 1 else 0 := by
    simp [S]
  have hw : ∑ v ∈ S, (demand G part ψ v : ℝ) =
      ∑ v, if some (some v) ∈ C.S then (demand G part ψ v : ℝ) else 0 := by
    rw [sum_mem_eq_sum_ite]
    simp [S]
  have hmax : ∀ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ) =
      (if some (some v) ∈ C.S then (0 : ℝ) else ((max (demand G part ψ v) 0 : ℤ) : ℝ)) +
        (if some (some v) ∈ C.S then ((max (-demand G part ψ v) 0 : ℤ) : ℝ) else 0) +
        (if some (some v) ∈ C.S then (demand G part ψ v : ℝ) else 0) := by
    intro v
    by_cases hv : some (some v) ∈ C.S
    · simp only [hv, ite_true, zero_add]
      rcases le_total (demand G part ψ v) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by omega)]; push_cast; ring
      · rw [max_eq_left h, max_eq_right (by omega)]; push_cast; ring
    · simp [hv]
  rw [hz]
  calc ∑ v, ((max (demand G part ψ v) 0 : ℤ) : ℝ)
      = (∑ v, if some (some v) ∈ C.S then (0 : ℝ) else ((max (demand G part ψ v) 0 : ℤ) : ℝ)) +
        (∑ v, if some (some v) ∈ C.S then ((max (-demand G part ψ v) 0 : ℤ) : ℝ) else 0) +
        ∑ v ∈ S, (demand G part ψ v : ℝ) := by
        rw [hw, ← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun v _ => hmax v
    _ ≤ _ := by linarith

end ABLP
