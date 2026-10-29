/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PartiteFractional.Numerics

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`; they agree definitionally with the
library definitions in the namespace `ABLP` (`PartiteFractional/`). Each theorem is the
corresponding library result:
`ABLP.not_fracDecomp_iff` (Lemma 2.1), `ABLP.prop_3_1`, `ABLP.cor_3_5`, `ABLP.prop_4_2`,
`ABLP.prop_4_3`, `ABLP.prop_4_4` with `ABLP.f44_mem` and `ABLP.f44_antitone`, and
`ABLP.thm_1_3`.
-/

@[expose] public section

open SimpleGraph Finset

namespace ABLP2026

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Edge weightings and fractional decompositions -/

/-- The edges of `G` with both endpoints in the vertex set `t`. -/
def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- A fractional triangle decomposition of `G`: nonnegative weights on the triangles such that
the triangles through each edge have total weight one. -/
def IsFracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t = 1

/-- Every triangle of `G` has nonnegative total weight. -/
def IsTriangleCovered (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Sym2 V → ℝ) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, 0 ≤ ∑ e ∈ edgesIn G t, φ e

/-- The total weight of the edges of `G` is negative. -/
def IsTotallyNegative (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Sym2 V → ℝ) : Prop :=
  ∑ e ∈ G.edgeFinset, φ e < 0

/-! ### Tripartite graphs -/

/-- `G` is tripartite with parts `part ⁻¹' {i}`. -/
def IsTripartite (G : SimpleGraph V) (part : V → Fin 3) : Prop :=
  ∀ u v, G.Adj u v → part u ≠ part v

/-- The number of neighbours of `v` in part `i`. -/
def degTo (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin 3) (v : V) (i : Fin 3) : ℕ :=
  #{u | G.Adj v u ∧ part u = i}

/-- `K₃`-divisibility of a tripartite graph: every vertex has as many neighbours in each of the
other two parts. -/
def IsK3Divisible (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin 3) : Prop :=
  ∀ v, degTo G part v (part v + 1) = degTo G part v (part v - 1)

/-- Every vertex meets as many negative edges from the previous part as from the next. -/
def IsBalanced (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin 3) (ψ : Sym2 V → ℝ) :
    Prop :=
  ∀ v, #{u | G.Adj u v ∧ part u = part v - 1 ∧ ψ s(u, v) < 0} =
    #{u | G.Adj u v ∧ part u = part v + 1 ∧ ψ s(u, v) < 0}

/-- No two edges have the same weight. -/
def IsUntied (G : SimpleGraph V) [DecidableRel G.Adj] (ψ : Sym2 V → ℝ) : Prop :=
  ∀ e ∈ G.edgeFinset, ∀ f ∈ G.edgeFinset, e ≠ f → ψ e ≠ ψ f

/-- No edge has weight zero. -/
def IsNonzero (G : SimpleGraph V) [DecidableRel G.Adj] (ψ : Sym2 V → ℝ) : Prop :=
  ∀ e ∈ G.edgeFinset, ψ e ≠ 0

/-! ### Non-uniform proportional discharging (Section 4) -/

section Discharging

variable (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin 3) (n : ℕ) (f : ℝ → ℝ)
  (φ : Sym2 V → ℝ)

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

end Discharging

/-- `M(a, b) = 1/a - sup_{a < z ≤ b} f(z) (1/a - 1/z)`, where the supremum over the empty set is
`0` (which is the value of `sSup ∅` in `ℝ`). -/
noncomputable def M (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  1 / a - sSup ((fun z => f z * (1 / a - 1 / z)) '' Set.Ioc a b)

/-- The lower bound `g_d(x, y)` of Propositions 4.3 and 4.4. -/
noncomputable def gd (f : ℝ → ℝ) (d x y : ℝ) : ℝ :=
  (M f y (1 - x) - f x / x) * max (x - d) 0 + (M f x (1 - y) - f x / x) * max (y - d) 0 +
    f x / x * (1 - 2 * d)

/-- The function `f` of equation (8). -/
noncomputable def f8 (t : ℝ) : ℝ :=
  if t ≤ 2 / 5 then 1 / 2 else if 7 / 10 < t then 0 else (7 - 10 * t) / 6

/-! ### Statements -/

/-- **Lemma 2.1.** `G` has no fractional triangle decomposition if and only if it has a
triangle-covered, totally negative edge weighting. -/
theorem lemma_2_1 (G : SimpleGraph V) [DecidableRel G.Adj] :
    (¬ ∃ w, IsFracTriangleDecomp G w) ↔
      ∃ φ : Sym2 V → ℝ, IsTriangleCovered G φ ∧ IsTotallyNegative G φ := by
  exact ABLP.not_fracDecomp_iff G

/-- **Proposition 3.1.** A triangle-covered edge weighting `φ` of a `K₃`-divisible tripartite
graph can be replaced, changing its total weight by at most `ε`, by a triangle-covered, balanced,
untied and nonzero one. -/
theorem proposition_3_1 {G : SimpleGraph V} [DecidableRel G.Adj] {part : V → Fin 3}
    (hG : IsTripartite G part) (hdiv : IsK3Divisible G part) {φ : Sym2 V → ℝ}
    (hφ : IsTriangleCovered G φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Sym2 V → ℝ, IsTriangleCovered G ψ ∧ IsBalanced G part ψ ∧ IsUntied G ψ ∧
      IsNonzero G ψ ∧ |∑ e ∈ G.edgeFinset, ψ e - ∑ e ∈ G.edgeFinset, φ e| ≤ ε := by
  exact ABLP.prop_3_1 hG hdiv hφ hε

/-- **Corollary 3.5.** A `K₃`-divisible tripartite graph has no fractional triangle
decomposition if and only if it has a triangle-covered, totally negative, balanced, untied and
nonzero edge weighting. -/
theorem corollary_3_5 {G : SimpleGraph V} [DecidableRel G.Adj] {part : V → Fin 3}
    (hG : IsTripartite G part) (hdiv : IsK3Divisible G part) :
    (¬ ∃ w, IsFracTriangleDecomp G w) ↔
      ∃ ψ : Sym2 V → ℝ, IsTriangleCovered G ψ ∧ IsTotallyNegative G ψ ∧ IsBalanced G part ψ ∧
        IsUntied G ψ ∧ IsNonzero G ψ := by
  exact ABLP.cor_3_5 hG hdiv

/-- **Proposition 4.2.** In the `f`-proportional discharging of a triangle-covered balanced
weighting of a `K₃`-divisible tripartite graph with parts of size `n`, a blue edge sends at most
its own weight. -/
theorem proposition_4_2 {G : SimpleGraph V} [DecidableRel G.Adj] {part : V → Fin 3} {n : ℕ}
    {f : ℝ → ℝ} {φ : Sym2 V → ℝ} (hG : IsTripartite G part) (hdiv : IsK3Divisible G part)
    (hn : ∀ i, #{v | part v = i} = n)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (hfa : AntitoneOn f (Set.Icc 0 1))
    (hφ : IsTriangleCovered G φ) (hbal : IsBalanced G part φ) {b : Sym2 V}
    (hb : b ∈ G.edgeFinset) (hb0 : 0 ≤ φ b) :
    0 ≤ φ b - ∑ r ∈ G.edgeFinset, disE G part n f φ b r := by
  exact ABLP.prop_4_2 hG hn hf hφ hbal hb hb0

/-- **Proposition 4.3.** Let `G` be a `K₃`-divisible tripartite graph with parts of size `n` and
minimum partite degree at least `(1 - d) n` for some `d ∈ [0, 1/2)`, and `φ` a nonzero,
triangle-covered, balanced weighting. For every red edge `uv` with `d_u ≥ d_v`, the numbers
`x = d_u / n` and `y = d_v / n` satisfy `0 < y ≤ x < 1` and `x + y ≤ 1`, and the weight
`Δ(uv) = ∑_b dis(b, uv)` received by `uv` satisfies `g_d(x, y) ≤ Δ(uv) / |φ(uv)|`. -/
theorem proposition_4_3 {G : SimpleGraph V} [DecidableRel G.Adj] {part : V → Fin 3} {n : ℕ}
    {f : ℝ → ℝ} {φ : Sym2 V → ℝ} {d : ℝ} (hG : IsTripartite G part)
    (hdiv : IsK3Divisible G part) (hn : ∀ i, #{v | part v = i} = n) (hd0 : 0 ≤ d)
    (hd : d < 1 / 2)
    (hδ : ∀ v (i : Fin 3), i ≠ part v → (1 - d) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ 1 / 2) (hfa : AntitoneOn f (Set.Icc 0 1))
    (hnz : IsNonzero G φ) (hφ : IsTriangleCovered G φ) (hbal : IsBalanced G part φ) {u v : V}
    (huv : G.Adj u v) (hr : φ s(u, v) < 0) (hdeg : redDeg G part φ v ≤ redDeg G part φ u) :
    0 < (redDeg G part φ v : ℝ) / n ∧
      (redDeg G part φ v : ℝ) / n ≤ (redDeg G part φ u : ℝ) / n ∧
      (redDeg G part φ u : ℝ) / n < 1 ∧
      (redDeg G part φ u : ℝ) / n + (redDeg G part φ v : ℝ) / n ≤ 1 ∧
      gd f d ((redDeg G part φ u : ℝ) / n) ((redDeg G part φ v : ℝ) / n) ≤
        (∑ b ∈ G.edgeFinset, disE G part n f φ b s(u, v)) / |φ s(u, v)| := by
  exact ABLP.prop_4_3 hG hn hδ hf hfa hφ hbal huv hr hdeg

/-- **Proposition 4.4.** The function `f` of (8) maps `[0, 1]` to `[0, 1/2]` and is
non-increasing there, and there is `η > 0` such that `g_d(x, y) ≥ 1` for every
`0 ≤ d ≤ 0.231 + η` and all `x ≥ y` in `(0, 1)` with `x + y ≤ 1`. -/
theorem proposition_4_4 :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f8 t ∧ f8 t ≤ 1 / 2) ∧ AntitoneOn f8 (Set.Icc 0 1) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ d : ℝ, 0 ≤ d → d ≤ 231 / 1000 + η →
        ∀ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → y ≤ x → x + y ≤ 1 → 1 ≤ gd f8 d x y := by
  refine ⟨fun t _ => ABLP.f44_mem t, ABLP.f44_antitone.antitoneOn _, 1 / 20000, by norm_num,
    fun d _ hd x y _ hx hy _ hyx hxy => ?_⟩
  exact ABLP.prop_4_4 hd hy hyx hx hxy

/-- **Theorem 1.3.** There is `η > 0` such that every `K₃`-divisible spanning subgraph `G` of
`K_{n,n,n}` with minimum partite degree at least `(0.769 - η) n` has a fractional triangle
decomposition. -/
theorem theorem_1_3 : ∃ η : ℝ, 0 < η ∧ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (part : W → Fin 3) (n : ℕ),
    IsTripartite G part → IsK3Divisible G part → (∀ i, #{v | part v = i} = n) →
    (∀ v (i : Fin 3), i ≠ part v → (769 / 1000 - η) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ)) →
    ∃ w, IsFracTriangleDecomp G w := by
  obtain ⟨η, hη, h⟩ := ABLP.thm_1_3.{0}
  exact ⟨η, hη, fun W _ _ G _ part n hG hdiv hn hδ => h W G part n hG hdiv hn hδ⟩

end ABLP2026
