/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.MaxFlowMinCut

/-!
Draft: integral max-flow / min-cut on top of the registered real-valued development
(`Contrib.MaxFlowMinCut`, dross-fractional-triangle-decomposition). With integer capacities, a
flow of maximum value among the integral flows leaves the sink unreachable in the residual graph
(augmenting along a simple path by one keeps it integral), so its value is a cut capacity.
-/

@[expose] public section

open Finset

namespace ABLP.IntFlow

open Contrib.MaxFlowMinCut

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- All capacities are integers. -/
def IntCaps (Net : Network N) : Prop := ∀ u v, ∃ z : ℤ, Net.cap u v = z

/-- All flow values are integers. -/
def IsIntegral {Net : Network N} (F : Flow Net) : Prop := ∀ u v, ∃ z : ℤ, F.f u v = z

/-- A flow of maximum value among the integral flows exists. -/
theorem exists_max_integral_flow (Net : Network N) (hcap : IntCaps Net) :
    ∃ F : Flow Net, IsIntegral F ∧ ∀ F' : Flow Net, IsIntegral F' → F'.value ≤ F.value := by
  choose zc hzc using hcap
  let S : Set (N → N → ℤ) := {g | (fun u v => (g u v : ℝ)) ∈ FlowSet Net}
  have hSsub : S ⊆ Set.pi Set.univ fun u => Set.pi Set.univ fun v => Set.Icc (-zc v u) (zc u v) := by
    intro g hg u _ v _
    obtain ⟨hskew, hcap', -⟩ := hg
    constructor
    · have h1 := hcap' v u
      have h2 := hskew u v
      rw [hzc] at h1
      have : (-(zc v u : ℝ)) ≤ g u v := by simp only at h1 h2; linarith
      exact_mod_cast this
    · have h1 := hcap' u v
      rw [hzc] at h1
      simp only at h1
      exact_mod_cast h1
  have hSfin : S.Finite :=
    (Set.Finite.pi fun u => Set.Finite.pi fun v => Set.finite_Icc _ _).subset hSsub
  have hSne : S.Nonempty := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · intro u v; simp
    · intro u v; simpa using Net.capNonneg u v
    · intro u _ _; simp
  obtain ⟨g, hg, hgmax⟩ :=
    Set.exists_max_image S (fun g => ∑ v, (g Net.s v : ℝ)) hSfin hSne
  refine ⟨⟨fun u v => g u v, hg.1, hg.2.1, hg.2.2⟩, fun u v => ⟨g u v, rfl⟩, ?_⟩
  intro F' hF'
  choose z hz using hF'
  have hzS : z ∈ S := by
    change (fun u v => (z u v : ℝ)) ∈ FlowSet Net
    have : (fun u v => (z u v : ℝ)) = F'.f := by funext u v; exact (hz u v).symm
    rw [this]
    exact ⟨F'.skew, F'.capacitated, F'.conserved⟩
  have := hgmax z hzS
  simp only [Flow.value]
  calc ∑ v, F'.f Net.s v = ∑ v, (z Net.s v : ℝ) := sum_congr rfl fun v _ => hz _ _
    _ ≤ _ := this

/-- A maximum integral flow leaves the sink unreachable. -/
theorem t_not_reachable_of_int_max {Net : Network N} (hcap : IntCaps Net) (F : Flow Net)
    (hF : IsIntegral F) (hmax : ∀ F' : Flow Net, IsIntegral F' → F'.value ≤ F.value) :
    Net.t ∉ reachableSet F := by
  rw [mem_reachableSet]
  intro hreach
  obtain ⟨P, δ, hδ, hres, hanti, hbal⟩ := augEdges_exists F hreach
  -- residual capacities on `P` are positive integers, hence at least one
  have hres1 : ∀ p ∈ P, 1 ≤ Net.cap p.1 p.2 - F.f p.1 p.2 := by
    intro p hp
    obtain ⟨a, ha⟩ := hcap p.1 p.2
    obtain ⟨b, hb⟩ := hF p.1 p.2
    have hpos : (0 : ℝ) < a - b := by rw [← ha, ← hb]; linarith [hres p hp]
    have : (0 : ℤ) < a - b := by exact_mod_cast hpos
    rw [ha, hb]
    exact_mod_cast (show (1 : ℤ) ≤ a - b by omega)
  set push : N → N → ℝ :=
    fun u v => (if (u, v) ∈ P then 1 else 0) - (if (v, u) ∈ P then 1 else 0) with hpush
  have push_skew : ∀ u v, push u v = - push v u := by
    intro u v; simp only [hpush]; ring
  have hrowsum : ∀ u, ∑ v, push u v
      = (if u = Net.s then 1 else 0) - (if u = Net.t then 1 else 0) := by
    intro u
    simp only [hpush]
    rw [Finset.sum_sub_distrib]
    exact hbal u
  have cap' : ∀ u v, F.f u v + push u v ≤ Net.cap u v := by
    intro u v
    simp only [hpush]
    by_cases huv : (u, v) ∈ P
    · have hvu : (v, u) ∉ P := hanti u v huv
      simp only [huv, hvu, ite_true, ite_false]
      have := hres1 (u, v) huv
      simp only at this
      linarith
    · have hle : F.f u v ≤ Net.cap u v := F.capacitated u v
      by_cases hvu : (v, u) ∈ P
      · simp only [huv, hvu, ite_true, ite_false]; linarith
      · simp only [huv, hvu, ite_false]; linarith
  have cons' : ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, (F.f u v + push u v) = 0 := by
    intro u hus hut
    rw [Finset.sum_add_distrib, F.conserved u hus hut, hrowsum u]
    simp [hus, hut]
  let F' : Flow Net :=
    { f := fun u v => F.f u v + push u v
      skew := by intro u v; rw [F.skew u v, push_skew u v]; ring
      capacitated := cap'
      conserved := cons' }
  have hF' : IsIntegral F' := by
    intro u v
    obtain ⟨b, hb⟩ := hF u v
    refine ⟨b + ((if (u, v) ∈ P then 1 else 0) - (if (v, u) ∈ P then 1 else 0)), ?_⟩
    change F.f u v + push u v = _
    simp only [hpush, hb]
    split_ifs <;> push_cast <;> ring
  have hval : F'.value = F.value + 1 := by
    change ∑ v, (F.f Net.s v + push Net.s v) = F.value + 1
    rw [Finset.sum_add_distrib, hrowsum Net.s, ite_eq_left rfl, ite_eq_right Net.st]
    simp only [Flow.value]
    ring
  have := hmax F' hF'
  rw [hval] at this
  linarith

/-- **Integral max-flow / min-cut.** With integer capacities there is an integral flow whose
value is the capacity of some cut. -/
theorem exists_integral_flow_eq_cut (Net : Network N) (hcap : IntCaps Net) :
    ∃ F : Flow Net, IsIntegral F ∧ ∃ C : Cut Net, F.value = C.capacity := by
  obtain ⟨F, hF, hmax⟩ := exists_max_integral_flow Net hcap
  have ht : Net.t ∉ reachableSet F := t_not_reachable_of_int_max hcap F hF hmax
  have hs : Net.s ∈ reachableSet F := by
    rw [mem_reachableSet]; exact Relation.ReflTransGen.refl
  exact ⟨F, hF, ⟨reachableSet F, hs, ht⟩, saturated_cut_value F (reachableSet F) hs ht
    (fun u hu v hv => reachable_saturates F hu hv)⟩

/-- If every cut has capacity at least `c`, some integral flow has value at least `c`. -/
theorem exists_integral_flow_ge (Net : Network N) (hcap : IntCaps Net) (c : ℝ)
    (hcut : ∀ C : Cut Net, c ≤ C.capacity) :
    ∃ F : Flow Net, IsIntegral F ∧ c ≤ F.value := by
  obtain ⟨F, hF, C, hC⟩ := exists_integral_flow_eq_cut Net hcap
  exact ⟨F, hF, hC ▸ hcut C⟩

end ABLP.IntFlow
