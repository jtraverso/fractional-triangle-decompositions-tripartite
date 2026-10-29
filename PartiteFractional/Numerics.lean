/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartiteFractional.Discharging
public import PartiteFractional.Bernstein44

/-!
# Proposition 4.4 and Theorem 1.3 of Allsop–Bowtell–Lesgourgues–Petrova

With the piecewise-linear `f` of equation (8), `g_d(x, y) ≥ 1` on the region
`0 < y ≤ x < 1`, `x + y ≤ 1`, for every `d ≤ 0.231 + η` with `η = 1/20000`. Together with
`fracDecomp_of_gd` this gives Theorem 1.3: a `K₃`-divisible tripartite graph with parts of size
`n` and minimum partite degree at least `(0.769 - η) n` has a fractional triangle decomposition.

The proof follows Appendix A of the paper, with two changes.
* The bound `M(a, b) ≥ √70 / (3√a) - 5/3 - 1/(6a)` is proved for every `a > 0` by the AM-GM
  inequality; on `(0, 8/35]` the paper's other branch `1/(2a) + 5/4` is larger.
* The two-variable inequalities of Case 3, for which the paper reports a numerical minimisation,
  are proved with `x = t²`, `y = s²` by Bernstein certificates (`PartiteFractional.Bernstein44`).
Everything is done at `d₀ = 0.23105` and transferred to smaller `d` by monotonicity.
-/

@[expose] public section

open Finset

namespace ABLP

/-- The function `f` of equation (8). -/
noncomputable def f44 (t : ℝ) : ℝ :=
  if t ≤ 2 / 5 then 1 / 2 else if 7 / 10 < t then 0 else (7 - 10 * t) / 6

theorem f44_of_le {t : ℝ} (h : t ≤ 2 / 5) : f44 t = 1 / 2 := by
  unfold f44
  rw [ite_eq_left h]

theorem f44_mid {t : ℝ} (h1 : 2 / 5 ≤ t) (h2 : t ≤ 7 / 10) : f44 t = (7 - 10 * t) / 6 := by
  unfold f44
  rcases h1.lt_or_eq with h | h
  · rw [ite_eq_right (not_le.2 h), ite_eq_right (not_lt.2 h2)]
  · rw [ite_eq_left h.ge, ← h]
    norm_num

theorem f44_of_ge {t : ℝ} (h : 7 / 10 ≤ t) : f44 t = 0 := by
  unfold f44
  rcases h.lt_or_eq with h | h
  · rw [ite_eq_right (not_le.2 (by linarith)), ite_eq_left h]
  · rw [ite_eq_right (not_le.2 (by linarith)), ite_eq_right (not_lt.2 h.ge), ← h]
    norm_num

theorem f44_mem (t : ℝ) : 0 ≤ f44 t ∧ f44 t ≤ 1 / 2 := by
  unfold f44
  split_ifs with h1 h2 <;> constructor <;> linarith

theorem f44_antitone : Antitone f44 := by
  intro a b hab
  unfold f44
  split_ifs <;> linarith

/-! ### Lower bounds for `M` -/

theorem M_ge_of_bound {f : ℝ → ℝ} {a b U : ℝ} (hU : 0 ≤ U)
    (h : ∀ z ∈ Set.Ioc a b, f z * (1 / a - 1 / z) ≤ U) : 1 / a - U ≤ M f a b := by
  unfold M
  have := Real.sSup_le (s := (fun z => f z * (1 / a - 1 / z)) '' Set.Ioc a b)
    (fun y hy => by obtain ⟨z, hz, rfl⟩ := hy; exact h z hz) hU
  linarith

/-- `M(a, b) ≥ √70 / (3 √a) - 5/3 - 1/(6a)`, written with `√(70 a)`. -/
theorem M_f44_sqrt {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (2 * √(70 * a) - 1 - 10 * a) / (6 * a) ≤ M f44 a b := by
  set r := √(70 * a) with hr_def
  have hr : r ^ 2 = 70 * a := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have ha0 : a ≠ 0 := ha.ne'
  have hpos : 0 < 7 + 10 * a + 2 * r := by linarith
  have hnum : 0 ≤ 7 + 10 * a - 2 * r := by nlinarith [sq_nonneg (7 - 10 * a)]
  have hU : 0 ≤ (7 + 10 * a - 2 * r) / (6 * a) := div_nonneg hnum (by linarith)
  have key := M_ge_of_bound (f := f44) (b := b) hU fun z hz => by
    obtain ⟨hz1, -⟩ := hz
    have hz0 : 0 < z := ha.trans hz1
    rcases le_or_gt z (2 / 5) with h1 | h1
    · rw [f44_of_le h1]
      have hiz : 5 / 2 ≤ 1 / z := by
        rw [le_div_iff₀ hz0]
        linarith
      have e : (7 + 10 * a - 2 * r) / (6 * a) =
          1 / a / 2 - 5 / 4 + (8 + 35 * a - 4 * r) / (12 * a) := by
        field_simp
        ring
      have h8 : 0 ≤ (8 + 35 * a - 4 * r) / (12 * a) :=
        div_nonneg (by nlinarith [sq_nonneg (r - 4)]) (by linarith)
      rw [e]
      linarith
    · rcases le_or_gt z (7 / 10) with h2 | h2
      · rw [f44_mid h1.le h2]
        have e1 : (7 - 10 * z) / 6 * (1 / a - 1 / z) = (7 - 10 * z) * (z - a) / (6 * a * z) := by
          field_simp
        have e2 : (7 + 10 * a - 2 * r) / (6 * a) = (7 + 10 * a - 2 * r) * z / (6 * a * z) := by
          field_simp
        rw [e1, e2]
        exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (10 * z - r)]) (by positivity)
      · rw [f44_of_ge h2.le, zero_mul]
        exact hU
  have e : 1 / a - (7 + 10 * a - 2 * r) / (6 * a) = (2 * r - 1 - 10 * a) / (6 * a) := by
    field_simp
    ring
  rw [← e]
  exact key

/-- `M(a, b) ≥ 3.413` for `0 < a ≤ 0.23105`. -/
theorem M_f44_const {a : ℝ} (ha : 0 < a) (had : a ≤ 4621 / 20000) (b : ℝ) :
    3413 / 1000 ≤ M f44 a b := by
  have hw : 20000 / 4621 ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    nlinarith
  have hU : 0 ≤ 1 / a - 3413 / 1000 := by linarith
  have key := M_ge_of_bound (f := f44) (b := b) hU fun z hz => by
    obtain ⟨hz1, -⟩ := hz
    have hz0 : 0 < z := ha.trans hz1
    rcases le_or_gt z (2 / 5) with h1 | h1
    · rw [f44_of_le h1]
      have hiz : 5 / 2 ≤ 1 / z := by
        rw [le_div_iff₀ hz0]
        linarith
      linarith
    · rcases le_or_gt z (7 / 10) with h2 | h2
      · rw [f44_mid h1.le h2]
        have hq : 0 ≤ 10 * (20000 / 4621) * z ^ 2 -
            (20000 / 4621 + 10 + 6 * (3413 / 1000)) * z + 7 := by
          nlinarith [sq_nonneg (z - 40211 / 100000)]
        have e : 1 / a - 3413 / 1000 - (7 - 10 * z) / 6 * (1 / a - 1 / z) =
            (1 / a - 20000 / 4621) * (10 * z - 1) / 6 +
              (10 * (20000 / 4621) * z ^ 2 - (20000 / 4621 + 10 + 6 * (3413 / 1000)) * z + 7) /
                (6 * z) := by
          field_simp
          ring
        have h3 : 0 ≤ (1 / a - 20000 / 4621) * (10 * z - 1) / 6 :=
          div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
        have h4 : 0 ≤ (10 * (20000 / 4621) * z ^ 2 -
            (20000 / 4621 + 10 + 6 * (3413 / 1000)) * z + 7) / (6 * z) :=
          div_nonneg hq (by linarith)
        linarith
      · rw [f44_of_ge h2.le, zero_mul]
        exact hU
  linarith

/-! ### The two-variable inequalities of Case 3 -/

theorem sqrt_le_of_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : √a ≤ b :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hb)

/-- Case 3 with `2/5 ≤ x ≤ 7/10`, in the variables `y = s²`, `x = t²`, `q = √70`. -/
theorem case3_lin {s t q : ℝ} (hs : 12 / 25 ≤ s) (hs' : s ≤ 71 / 100) (ht : 632 / 1000 ≤ t)
    (ht' : t ≤ 837 / 1000) (hq : 83666 / 10000 ≤ q) (hsd : 4621 / 20000 ≤ s ^ 2)
    (htd : 4621 / 20000 ≤ t ^ 2) :
    1 ≤ (t ^ 2 - 4621 / 20000) * ((2 * q * s - 1 - 10 * s ^ 2) / (6 * s ^ 2)) +
      (s ^ 2 - 4621 / 20000) * ((2 * q * t - 1 - 10 * t ^ 2) / (6 * t ^ 2)) +
      (7 - 10 * t ^ 2) / 6 / t ^ 2 * (1 - t ^ 2 - s ^ 2) := by
  have hP := polyLin_nonneg (by linarith) (by linarith) (by linarith) (by linarith) (s := s) (t := t)
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hmono : 0 ≤ 2 * (q - 83666 / 10000) *
      (s * t ^ 2 * (t ^ 2 - 4621 / 20000) + t * s ^ 2 * (s ^ 2 - 4621 / 20000)) :=
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_nonneg (by positivity) (by linarith)))
  have e : (t ^ 2 - 4621 / 20000) * ((2 * q * s - 1 - 10 * s ^ 2) / (6 * s ^ 2)) +
      (s ^ 2 - 4621 / 20000) * ((2 * q * t - 1 - 10 * t ^ 2) / (6 * t ^ 2)) +
      (7 - 10 * t ^ 2) / 6 / t ^ 2 * (1 - t ^ 2 - s ^ 2) - 1 =
      (polyLin s t + 2 * (q - 83666 / 10000) *
        (s * t ^ 2 * (t ^ 2 - 4621 / 20000) + t * s ^ 2 * (s ^ 2 - 4621 / 20000))) /
        (6 * s ^ 2 * t ^ 2) := by
    unfold polyLin
    field_simp
    ring
  have : 0 ≤ (polyLin s t + 2 * (q - 83666 / 10000) *
        (s * t ^ 2 * (t ^ 2 - 4621 / 20000) + t * s ^ 2 * (s ^ 2 - 4621 / 20000))) /
        (6 * s ^ 2 * t ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

/-- Case 3 with `x ≤ 2/5`, in the variables `y = s²`, `x = t²`, `q = √70`. -/
theorem case3_half {s t q : ℝ} (hs : 12 / 25 ≤ s) (hs' : s ≤ 633 / 1000) (ht : 12 / 25 ≤ t)
    (ht' : t ≤ 633 / 1000) (hq : 83666 / 10000 ≤ q) (hsd : 4621 / 20000 ≤ s ^ 2)
    (htd : 4621 / 20000 ≤ t ^ 2) :
    1 ≤ (t ^ 2 - 4621 / 20000) * ((2 * q * s - 1 - 10 * s ^ 2) / (6 * s ^ 2)) +
      (s ^ 2 - 4621 / 20000) * ((2 * q * t - 1 - 10 * t ^ 2) / (6 * t ^ 2)) +
      1 / 2 / t ^ 2 * (1 - t ^ 2 - s ^ 2) := by
  have hP := polyHalf_nonneg (by linarith) (by linarith) (by linarith) (by linarith) (s := s) (t := t)
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hmono : 0 ≤ 2 * (q - 83666 / 10000) *
      (s * t ^ 2 * (t ^ 2 - 4621 / 20000) + t * s ^ 2 * (s ^ 2 - 4621 / 20000)) :=
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_nonneg (by positivity) (by linarith)))
  have e : (t ^ 2 - 4621 / 20000) * ((2 * q * s - 1 - 10 * s ^ 2) / (6 * s ^ 2)) +
      (s ^ 2 - 4621 / 20000) * ((2 * q * t - 1 - 10 * t ^ 2) / (6 * t ^ 2)) +
      1 / 2 / t ^ 2 * (1 - t ^ 2 - s ^ 2) - 1 =
      (polyHalf s t + 2 * (q - 83666 / 10000) *
        (s * t ^ 2 * (t ^ 2 - 4621 / 20000) + t * s ^ 2 * (s ^ 2 - 4621 / 20000))) /
        (6 * s ^ 2 * t ^ 2) := by
    unfold polyHalf
    field_simp
    ring
  have : 0 ≤ (polyHalf s t + 2 * (q - 83666 / 10000) *
        (s * t ^ 2 * (t ^ 2 - 4621 / 20000) + t * s ^ 2 * (s ^ 2 - 4621 / 20000))) /
        (6 * s ^ 2 * t ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

/-! ### Proposition 4.4 -/

/-- `g_d(x, y) ≥ 1` at `d = 0.23105` on the whole region. -/
theorem gd_f44_ge_one {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hx : x < 1) (hxy : x + y ≤ 1) :
    1 ≤ gd f44 (4621 / 20000) x y := by
  have hx0 : 0 < x := hy.trans_le hyx
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f44 t ∧ f44 t ≤ 1 / 2 := fun t _ => f44_mem t
  have hfx := f44_mem x
  have hcx : f44 x / x ≤ 1 / (2 * x) :=
    calc f44 x / x ≤ 1 / 2 / x := div_le_div_of_nonneg_right hfx.2 hx0.le
      _ = 1 / (2 * x) := by ring
  have hc : 0 ≤ f44 x / x := div_nonneg hfx.1 hx0.le
  have hM1c : f44 x / x ≤ M f44 y (1 - x) :=
    hcx.trans ((one_div_le_one_div_of_le (by positivity) (by linarith)).trans
      (le_M hf hy (by linarith)))
  have hM2c : f44 x / x ≤ M f44 x (1 - y) := hcx.trans (le_M hf hx0 (by linarith))
  unfold gd
  rcases le_total x (4621 / 20000) with h1 | h1
  · -- Case 1: `x ≤ d`
    rw [max_eq_right (by linarith : x - 4621 / 20000 ≤ 0),
      max_eq_right (by linarith : y - 4621 / 20000 ≤ 0), f44_of_le (by linarith)]
    have : 20000 / 4621 / 2 ≤ 1 / 2 / x := by
      rw [div_le_div_iff₀ (by norm_num) hx0]
      linarith
    nlinarith
  rcases le_total y (4621 / 20000) with h2 | h2
  · -- Case 2: `y ≤ d ≤ x`
    rw [max_eq_left (by linarith : 0 ≤ x - 4621 / 20000),
      max_eq_right (by linarith : y - 4621 / 20000 ≤ 0), mul_zero, add_zero]
    have hL := M_f44_const hy h2 (1 - x)
    have hL' := mul_le_mul_of_nonneg_right hL (by linarith : (0 : ℝ) ≤ x - 4621 / 20000)
    suffices h : 1 ≤ 3413 / 1000 * (x - 4621 / 20000) + f44 x / x * (1 - x - 4621 / 20000) by
      nlinarith
    rcases le_total x (2 / 5) with h3 | h3
    · rw [f44_of_le h3]
      have e : 3413 / 1000 * (x - 4621 / 20000) + 1 / 2 / x * (1 - x - 4621 / 20000) - 1 =
          (2 * (3413 / 1000) * x * (x - 4621 / 20000) + 1 - x - 4621 / 20000 - 2 * x) /
            (2 * x) := by
        field_simp
        ring
      have : 0 ≤ (2 * (3413 / 1000) * x * (x - 4621 / 20000) + 1 - x - 4621 / 20000 - 2 * x) /
          (2 * x) := div_nonneg (by nlinarith [sq_nonneg (x - 33527 / 100000)]) (by linarith)
      linarith
    rcases le_total x (7 / 10) with h4 | h4
    · rw [f44_mid h3 h4]
      have e : 3413 / 1000 * (x - 4621 / 20000) + (7 - 10 * x) / 6 / x * (1 - x - 4621 / 20000)
          - 1 = (6 * (3413 / 1000) * x * (x - 4621 / 20000) +
            (7 - 10 * x) * (1 - x - 4621 / 20000) - 6 * x) / (6 * x) := by
        field_simp
      have : 0 ≤ (6 * (3413 / 1000) * x * (x - 4621 / 20000) +
          (7 - 10 * x) * (1 - x - 4621 / 20000) - 6 * x) / (6 * x) :=
        div_nonneg (by nlinarith [sq_nonneg (x - 41703 / 100000)]) (by linarith)
      linarith
    · rw [f44_of_ge h4, zero_div, zero_mul, add_zero]
      linarith
  -- Case 3: `d ≤ y ≤ x`
  rw [max_eq_left (by linarith : 0 ≤ x - 4621 / 20000),
    max_eq_left (by linarith : 0 ≤ y - 4621 / 20000)]
  have hA := M_f44_sqrt hy (1 - x)
  have hB := M_f44_sqrt hx0 (1 - y)
  have hA' := mul_le_mul_of_nonneg_right hA (by linarith : (0 : ℝ) ≤ x - 4621 / 20000)
  have hB' := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ y - 4621 / 20000)
  rcases le_total (7 / 10) x with h3 | h3
  · -- Case 3(iv): `x ≥ 7/10`
    rw [f44_of_ge h3, zero_div] at hM2c ⊢
    have hB'' := mul_le_mul_of_nonneg_right hM2c (by linarith : (0 : ℝ) ≤ y - 4621 / 20000)
    set r := √(70 * y) with hr_def
    have hr : r ^ 2 = 70 * y := Real.sq_sqrt (by linarith)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr4 : 4 ≤ r := by nlinarith
    have hr5 : r ≤ 46 / 10 := by nlinarith
    have hm : 22 / 10 ≤ (2 * r - 1 - 10 * y) / (6 * y) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - 4) (by linarith : (0 : ℝ) ≤ 46 / 10 - r)]
    have := mul_le_mul_of_nonneg_right hm (by linarith : (0 : ℝ) ≤ x - 4621 / 20000)
    nlinarith
  -- Cases 3(i)–(iii): `x ≤ 7/10`
  set s := √y with hs_def
  set t := √x with ht_def
  have hs2 : s ^ 2 = y := Real.sq_sqrt hy.le
  have ht2 : t ^ 2 = x := Real.sq_sqrt hx0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hq : 83666 / 10000 ≤ √70 := Real.le_sqrt_of_sq_le (by norm_num)
  have hry : √(70 * y) = √70 * s := Real.sqrt_mul (by norm_num) y
  have hrx : √(70 * x) = √70 * t := Real.sqrt_mul (by norm_num) x
  have eA : (2 * √(70 * y) - 1 - 10 * y) / (6 * y) =
      (2 * √70 * s - 1 - 10 * s ^ 2) / (6 * s ^ 2) := by
    rw [hry, hs2]
    ring
  have eB : (2 * √(70 * x) - 1 - 10 * x) / (6 * x) =
      (2 * √70 * t - 1 - 10 * t ^ 2) / (6 * t ^ 2) := by
    rw [hrx, ht2]
    ring
  rw [eA] at hA
  rw [eB] at hB
  have hA2 := mul_le_mul_of_nonneg_right hA (by linarith : (0 : ℝ) ≤ x - 4621 / 20000)
  have hB2 := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ y - 4621 / 20000)
  have hs48 : 12 / 25 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have ht48 : 12 / 25 ≤ t := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hsd : 4621 / 20000 ≤ s ^ 2 := by rw [hs2]; exact h2
  have htd : 4621 / 20000 ≤ t ^ 2 := by rw [ht2]; exact h1
  rcases le_total x (2 / 5) with h4 | h4
  · rw [f44_of_le h4]
    have key := case3_half (q := √70) hs48 (sqrt_le_of_le_sq (by norm_num) (by norm_num; linarith))
      ht48 (sqrt_le_of_le_sq (by norm_num) (by norm_num; linarith)) hq hsd htd
    rw [← hs2, ← ht2] at hA2 hB2 ⊢
    linarith
  · rw [f44_mid h4 h3]
    have key := case3_lin (q := √70) hs48 (sqrt_le_of_le_sq (by norm_num) (by norm_num; linarith))
      (Real.le_sqrt_of_sq_le (by norm_num; linarith))
      (sqrt_le_of_le_sq (by norm_num) (by norm_num; linarith)) hq hsd htd
    rw [← hs2, ← ht2] at hA2 hB2 ⊢
    linarith

/-- `g_d` is non-increasing in `d` where `M ≥ f(x)/x ≥ 0`. -/
theorem gd_anti {f : ℝ → ℝ} {d d' x y : ℝ} (hdd : d ≤ d') (hc : 0 ≤ f x / x)
    (hM1 : f x / x ≤ M f y (1 - x)) (hM2 : f x / x ≤ M f x (1 - y)) :
    gd f d' x y ≤ gd f d x y := by
  unfold gd
  have h1 := mul_le_mul_of_nonneg_left
    (max_le (le_max_of_le_left (by linarith : x - d' ≤ x - d)) (le_max_right (x - d) 0))
    (sub_nonneg.2 hM1)
  have h2 := mul_le_mul_of_nonneg_left
    (max_le (le_max_of_le_left (by linarith : y - d' ≤ y - d)) (le_max_right (y - d) 0))
    (sub_nonneg.2 hM2)
  have h3 := mul_le_mul_of_nonneg_left (by linarith : 1 - 2 * d' ≤ 1 - 2 * d) hc
  linarith

/-- **Proposition 4.4**, with `f` from (8) and `η = 1/20000`: `g_d(x, y) ≥ 1` for every
`d ≤ 0.231 + η` and all `0 < y ≤ x < 1` with `x + y ≤ 1`. -/
theorem prop_4_4 {d : ℝ} (hd : d ≤ 231 / 1000 + 1 / 20000) {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hx : x < 1) (hxy : x + y ≤ 1) : 1 ≤ gd f44 d x y := by
  have hx0 : 0 < x := hy.trans_le hyx
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f44 t ∧ f44 t ≤ 1 / 2 := fun t _ => f44_mem t
  have hfx := f44_mem x
  have hcx : f44 x / x ≤ 1 / (2 * x) :=
    calc f44 x / x ≤ 1 / 2 / x := div_le_div_of_nonneg_right hfx.2 hx0.le
      _ = 1 / (2 * x) := by ring
  have hM1c : f44 x / x ≤ M f44 y (1 - x) :=
    hcx.trans ((one_div_le_one_div_of_le (by positivity) (by linarith)).trans
      (le_M hf hy (by linarith)))
  have hM2c : f44 x / x ≤ M f44 x (1 - y) := hcx.trans (le_M hf hx0 (by linarith))
  exact (gd_f44_ge_one hy hyx hx hxy).trans
    (gd_anti (by linarith) (div_nonneg hfx.1 hx0.le) hM1c hM2c)

/-- **Theorem 1.3.** There is `η > 0` (here `η = 1/20000`) such that every `K₃`-divisible
tripartite graph with parts of size `n` and minimum partite degree at least `(0.769 - η) n` has a
fractional triangle decomposition. -/
theorem thm_1_3 : ∃ η : ℝ, 0 < η ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin 3) (n : ℕ),
    IsTripartite G part → IsK3Divisible G part → (∀ i, #{v | part v = i} = n) →
    (∀ v (i : Fin 3), i ≠ part v → (769 / 1000 - η) * n ≤ (#{u | part u = i ∧ G.Adj v u} : ℝ)) →
    ∃ w, IsFracTriangleDecomp G w := by
  refine ⟨1 / 20000, by norm_num, fun V _ _ G _ part n hG hdiv hn hδ => ?_⟩
  refine fracDecomp_of_gd (f := f44) (d := 231 / 1000 + 1 / 20000) hG hdiv hn
    (fun v i hi => by have := hδ v i hi; ring_nf at this ⊢; linarith)
    (fun t _ => f44_mem t) (f44_antitone.antitoneOn _)
    (fun x y hy hyx hx hxy => prop_4_4 le_rfl hy hyx hx hxy)

end ABLP
