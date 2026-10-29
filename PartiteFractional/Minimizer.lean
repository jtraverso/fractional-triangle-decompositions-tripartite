/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Tripartite

/-!
# A translate of minimum `ℓ¹` norm

Lemma 3.4 of Allsop–Bowtell–Lesgourgues–Petrova starts from a translate `φ_p` of an edge weighting
`φ` minimizing `L(φ_p) = ∑ₑ |φ_p(e)|`. The shifts `p ↦ (p(v) - p(u))_{uv}` form a linear map into
the finite-dimensional space of weightings of the edges, whose range is closed; the sublevel set
`L ≤ L(φ)` of that range is closed and bounded, hence compact, and `L` attains its minimum there.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {part : V → Fin 3}

theorem shift_add (p q : V → ℝ) (e : Sym2 V) :
    shift part (p + q) e = shift part p e + shift part q e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [shift_mk, Pi.add_apply]
    split_ifs <;> ring

theorem shift_smul (c : ℝ) (p : V → ℝ) (e : Sym2 V) :
    shift part (c • p) e = c * shift part p e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [shift_mk, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring

variable (G part) in
/-- The shifts on the edges of `G`, as a linear map. -/
noncomputable def shiftMap : (V → ℝ) →ₗ[ℝ] (G.edgeFinset → ℝ) where
  toFun p e := shift part p e.1
  map_add' p q := funext fun e => shift_add p q e.1
  map_smul' c p := funext fun e => by simp [shift_smul]

variable (G) in
/-- The `ℓ¹` norm of an edge weighting on the edges of `G`. -/
noncomputable def l1 (ψ : Sym2 V → ℝ) : ℝ := ∑ e ∈ G.edgeFinset, |ψ e|

theorem l1_translate (φ : Sym2 V → ℝ) (p : V → ℝ) :
    l1 G (translate part φ p) = ∑ e : G.edgeFinset, |φ e.1 + shiftMap G part p e| := by
  rw [l1, ← Finset.sum_coe_sort G.edgeFinset]
  rfl

/-- **A translate of minimum `ℓ¹` norm exists.** -/
theorem exists_translate_min (φ : Sym2 V → ℝ) :
    ∃ p₀ : V → ℝ, ∀ p : V → ℝ, l1 G (translate part φ p₀) ≤ l1 G (translate part φ p) := by
  set g : (G.edgeFinset → ℝ) → ℝ := fun x => ∑ e : G.edgeFinset, |φ e.1 + x e| with hg
  have hgc : Continuous g := by fun_prop
  set R := LinearMap.range (shiftMap G part)
  set K : Set (G.edgeFinset → ℝ) := (R : Set _) ∩ {x | g x ≤ g 0}
  have hKc : IsClosed K :=
    (Submodule.closed_of_finiteDimensional R).inter (isClosed_le hgc continuous_const)
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2
      ⟨g 0 + ∑ e : G.edgeFinset, |φ e.1|, fun x hx => ?_⟩
    have hx2 : g x ≤ g 0 := hx.2
    have hpos : 0 ≤ g 0 + ∑ e : G.edgeFinset, |φ e.1| :=
      add_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hpos]
    intro e
    rw [Real.norm_eq_abs]
    have h1 : |φ e.1 + x e| ≤ g x :=
      single_le_sum (f := fun e : G.edgeFinset => |φ e.1 + x e|) (fun _ _ => abs_nonneg _)
        (mem_univ e)
    have h2 : |φ e.1| ≤ ∑ e : G.edgeFinset, |φ e.1| :=
      single_le_sum (f := fun e : G.edgeFinset => |φ e.1|) (fun _ _ => abs_nonneg _)
        (mem_univ e)
    have h3 : |x e| ≤ |φ e.1 + x e| + |φ e.1| := by
      have := abs_sub (φ e.1 + x e) (φ e.1)
      simpa using this
    linarith
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  have hne : K.Nonempty := ⟨0, R.zero_mem, show g 0 ≤ g 0 from le_rfl⟩
  obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne hgc.continuousOn
  obtain ⟨p₀, hp₀⟩ := hxK.1
  refine ⟨p₀, fun p => ?_⟩
  rw [l1_translate, l1_translate]
  show g (shiftMap G part p₀) ≤ g (shiftMap G part p)
  rw [hp₀]
  by_cases hp : g (shiftMap G part p) ≤ g 0
  · exact hxmin ⟨LinearMap.mem_range_self _ p, hp⟩
  · exact (hxmin ⟨R.zero_mem, show g 0 ≤ g 0 from le_rfl⟩).trans (le_of_not_ge hp)

end ABLP
