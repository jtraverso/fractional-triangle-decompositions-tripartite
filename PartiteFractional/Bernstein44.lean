/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Real.Basic

/-!
# Polynomial inequalities for Proposition 4.4

The two-variable inequalities of Case 3 of the proof of Proposition 4.4, with `x = t²` and
`y = s²`, `d = 0.23105` and `√70 ≥ 8.3666`. Each is proved on a box by subdividing it and writing
the polynomial on every piece as a nonnegative combination of the Bernstein products
`(s - a)^i (b - s)^(4-i) (t - c)^j (e - t)^(4-j)`. The subdivisions and the coefficients were
computed in exact rational arithmetic by a script; Lean checks each identity with `ring`.
-/

@[expose] public section

namespace ABLP

/-- `6 s² t² (B_d(t², s²) - 1)` with `√70` replaced by `8.3666`, where `f(x) = (7 - 10x)/6`. -/
noncomputable def polyLin (s t : ℝ) : ℝ :=
  (t ^ 2 - (4621 / 20000 : ℝ)) * t ^ 2 * (2 * (83666 / 10000 : ℝ) * s - 1 - 10 * s ^ 2) +
    (s ^ 2 - (4621 / 20000 : ℝ)) * s ^ 2 * (2 * (83666 / 10000 : ℝ) * t - 1 - 10 * t ^ 2) - 6 * s ^ 2 * t ^ 2 +
    s ^ 2 * (7 - 10 * t ^ 2) * (1 - t ^ 2 - s ^ 2)

theorem polyLin_leaf0 {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (43 / 80 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (12 / 25 : ℝ) := by linarith
  have u2 : 0 ≤ (43 / 80 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (79 / 125 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (5589804192457591619584 / 19769094600025 : ℝ) * k0_0 +
    (18219336399780415799296 / 19769094600025 : ℝ) * k0_1 +
    (28688342339796057718784 / 19769094600025 : ℝ) * k0_2 +
    (1117616942732009275392 / 859525852175 : ℝ) * k0_3 +
    (9659096715485089234944 / 19769094600025 : ℝ) * k0_4 +
    (19545769126033130258432 / 19769094600025 : ℝ) * k1_0 +
    (56523645154551092215808 / 19769094600025 : ℝ) * k1_1 +
    (83309020372291038380032 / 19769094600025 : ℝ) * k1_2 +
    (3383704468175826518016 / 859525852175 : ℝ) * k1_3 +
    (31546667136841290611712 / 19769094600025 : ℝ) * k1_4 +
    (25971091928841340321792 / 19769094600025 : ℝ) * k2_0 +
    (63569221554590753947648 / 19769094600025 : ℝ) * k2_1 +
    (82462422935161929531392 / 19769094600025 : ℝ) * k2_2 +
    (3570557707579789213696 / 859525852175 : ℝ) * k2_3 +
    (37340057111901050729472 / 19769094600025 : ℝ) * k2_4 +
    (15910519181635039002624 / 19769094600025 : ℝ) * k3_0 +
    (31512614336536605229056 / 19769094600025 : ℝ) * k3_1 +
    (31475881794966811213824 / 19769094600025 : ℝ) * k3_2 +
    (1514029599729226022912 / 859525852175 : ℝ) * k3_3 +
    (19004982970441149379584 / 19769094600025 : ℝ) * k3_4 +
    (780554425930381787136 / 3953818920005 : ℝ) * k4_0 +
    (1255935751383251984384 / 3953818920005 : ℝ) * k4_1 +
    (737157778640605863936 / 3953818920005 : ℝ) * k4_2 +
    (42232684512892755968 / 171905170435 : ℝ) * k4_3 +
    (712466734049603480576 / 3953818920005 : ℝ) * k4_4

theorem polyLin_leaf1 {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (43 / 80 : ℝ)) (h3 : (2733 / 4000 : ℝ) ≤ t) (h4 : t ≤ (1469 / 2000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (12 / 25 : ℝ) := by linarith
  have u2 : 0 ≤ (43 / 80 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (2733 / 4000 : ℝ) := by linarith
  have v2 : 0 ≤ (1469 / 2000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((43 / 80 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((43 / 80 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((43 / 80 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((43 / 80 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((43 / 80 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (9659096715485089234944 / 19769094600025 : ℝ) * k0_0 +
    (51567584041044500545536 / 19769094600025 : ℝ) * k0_1 +
    (106275525414420919353344 / 19769094600025 : ℝ) * k0_2 +
    (97162851660892110585856 / 19769094600025 : ℝ) * k0_3 +
    (1426457858137074434048 / 859525852175 : ℝ) * k0_4 +
    (31546667136841290611712 / 19769094600025 : ℝ) * k1_0 +
    (174548134326686314979328 / 19769094600025 : ℝ) * k1_1 +
    (373477815048217953574912 / 19769094600025 : ℝ) * k1_2 +
    (352303351497006241906688 / 19769094600025 : ℝ) * k1_3 +
    (5299113580487116079104 / 859525852175 : ℝ) * k1_4 +
    (37340057111901050729472 / 19769094600025 : ℝ) * k2_0 +
    (216597629620873253920768 / 19769094600025 : ℝ) * k2_1 +
    (485886829974776235548672 / 19769094600025 : ℝ) * k2_2 +
    (475688370474868764540928 / 19769094600025 : ℝ) * k2_3 +
    (7353940702436658561024 / 859525852175 : ℝ) * k2_4 +
    (19004982970441149379584 / 19769094600025 : ℝ) * k3_0 +
    (117217182969756996509696 / 19769094600025 : ℝ) * k3_1 +
    (278659388322921205161984 / 19769094600025 : ℝ) * k3_2 +
    (284678198372181037449216 / 19769094600025 : ℝ) * k3_3 +
    (4534221689796081532928 / 859525852175 : ℝ) * k3_4 +
    (712466734049603480576 / 3953818920005 : ℝ) * k4_0 +
    (4728382128600294457344 / 3953818920005 : ℝ) * k4_1 +
    (12008248933051889074176 / 3953818920005 : ℝ) * k4_2 +
    (12835409927208082202624 / 3953818920005 : ℝ) * k4_3 +
    (210694253571638689792 / 171905170435 : ℝ) * k4_4

theorem polyLin_leaf2 {s t : ℝ} (h1 : (43 / 80 : ℝ) ≤ s) (h2 : s ≤ (453 / 800 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (5261 / 8000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (43 / 80 : ℝ) := by linarith
  have u2 : 0 ≤ (453 / 800 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (79 / 125 : ℝ) := by linarith
  have v2 : 0 ≤ (5261 / 8000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (199821933038177737506816 / 3953818920005 : ℝ) * k0_0 +
    (560403642253411729014784 / 3953818920005 : ℝ) * k0_1 +
    (588050661655849762553856 / 3953818920005 : ℝ) * k0_2 +
    (298742152286368902938624 / 3953818920005 : ℝ) * k0_3 +
    (71319462940806024052736 / 3953818920005 : ℝ) * k0_4 +
    (3958111535896047132868608 / 19769094600025 : ℝ) * k1_0 +
    (10722209039565439151112192 / 19769094600025 : ℝ) * k1_1 +
    (10554260973055113327280128 / 19769094600025 : ℝ) * k1_2 +
    (4866994742673374405722112 / 19769094600025 : ℝ) * k1_3 +
    (1077770455605366294765568 / 19769094600025 : ℝ) * k1_4 +
    (5985671314901060596793344 / 19769094600025 : ℝ) * k2_0 +
    (15781209682577780159021056 / 19769094600025 : ℝ) * k2_1 +
    (14664700943729866733256704 / 19769094600025 : ℝ) * k2_2 +
    (6069498706890656950255616 / 19769094600025 : ℝ) * k2_3 +
    (1201765784939062608666624 / 19769094600025 : ℝ) * k2_4 +
    (4102276945448800756957184 / 19769094600025 : ℝ) * k3_0 +
    (10640656336232980103561216 / 19769094600025 : ℝ) * k3_1 +
    (9485024360100299440390144 / 19769094600025 : ℝ) * k3_2 +
    (3552587865034947023077376 / 19769094600025 : ℝ) * k3_3 +
    (606909918869850837131264 / 19769094600025 : ℝ) * k3_4 +
    (1075725580345421351354368 / 19769094600025 : ℝ) * k4_0 +
    (2780129457900223800082432 / 19769094600025 : ℝ) * k4_1 +
    (2435098534431090795020288 / 19769094600025 : ℝ) * k4_2 +
    (856904434485568045514752 / 19769094600025 : ℝ) * k4_3 +
    (126455013501199514902528 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf3 {s t : ℝ} (h1 : (43 / 80 : ℝ) ≤ s) (h2 : s ≤ (453 / 800 : ℝ)) (h3 : (5261 / 8000 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (43 / 80 : ℝ) := by linarith
  have u2 : 0 ≤ (453 / 800 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (5261 / 8000 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((453 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((453 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((453 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((453 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((453 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (71319462940806024052736 / 3953818920005 : ℝ) * k0_0 +
    (271813551240079289483264 / 3953818920005 : ℝ) * k0_1 +
    (507264858516980922187776 / 3953818920005 : ℝ) * k0_2 +
    (489115991039353255624704 / 3953818920005 : ℝ) * k0_3 +
    (182391483916698491027456 / 3953818920005 : ℝ) * k0_4 +
    (1077770455605366294765568 / 19769094600025 : ℝ) * k1_0 +
    (3755168902169555952402432 / 19769094600025 : ℝ) * k1_1 +
    (7218783451543657967321088 / 19769094600025 : ℝ) * k1_2 +
    (7579552519946242721841152 / 19769094600025 : ℝ) * k1_3 +
    (3039106697284487610236928 / 19769094600025 : ℝ) * k1_4 +
    (1201765784939062608666624 / 19769094600025 : ℝ) * k2_0 +
    (3544627572621843919077376 / 19769094600025 : ℝ) * k2_1 +
    (7090087540923427639721984 / 19769094600025 : ℝ) * k2_2 +
    (8500114727703806848270336 / 19769094600025 : ℝ) * k2_3 +
    (3754318628564713348399104 / 19769094600025 : ℝ) * k2_4 +
    (606909918869850837131264 / 19769094600025 : ℝ) * k3_0 +
    (1302691485923859673972736 / 19769094600025 : ℝ) * k3_1 +
    (2735335222767037393076224 / 19769094600025 : ℝ) * k3_2 +
    (4089504127584080169271296 / 19769094600025 : ℝ) * k3_3 +
    (2050917495022075520876544 / 19769094600025 : ℝ) * k3_4 +
    (126455013501199514902528 / 19769094600025 : ℝ) * k4_0 +
    (154735673524028073705472 / 19769094600025 : ℝ) * k4_1 +
    (328592251546470879592448 / 19769094600025 : ℝ) * k4_2 +
    (723971898035707310702592 / 19769094600025 : ℝ) * k4_3 +
    (423905542403984805593088 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf4 {s t : ℝ} (h1 : (453 / 800 : ℝ) ≤ s) (h2 : s ≤ (119 / 200 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (5261 / 8000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (453 / 800 : ℝ) := by linarith
  have u2 : 0 ≤ (119 / 200 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (79 / 125 : ℝ) := by linarith
  have v2 : 0 ≤ (5261 / 8000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (1075725580345421351354368 / 19769094600025 : ℝ) * k0_0 +
    (2780129457900223800082432 / 19769094600025 : ℝ) * k0_1 +
    (2435098534431090795020288 / 19769094600025 : ℝ) * k0_2 +
    (856904434485568045514752 / 19769094600025 : ℝ) * k0_3 +
    (126455013501199514902528 / 19769094600025 : ℝ) * k0_4 +
    (900705539462914010775552 / 3953818920005 : ℝ) * k1_0 +
    (2320075865393762059419648 / 3953818920005 : ℝ) * k1_1 +
    (1999152783069685383954432 / 3953818920005 : ℝ) * k1_2 +
    (660529522169919468208128 / 3953818920005 : ℝ) * k1_3 +
    (80946037827949056417792 / 3953818920005 : ℝ) * k1_4 +
    (7189423570498368487555072 / 19769094600025 : ℝ) * k2_0 +
    (18660378654785270739632128 / 19769094600025 : ℝ) * k2_1 +
    (16196919609474249171402752 / 19769094600025 : ℝ) * k2_2 +
    (5319677944334607904145408 / 19769094600025 : ℝ) * k2_3 +
    (595226595748745943539712 / 19769094600025 : ℝ) * k2_4 +
    (5180468949376069414158336 / 19769094600025 : ℝ) * k3_0 +
    (13678896308757081844875264 / 19769094600025 : ℝ) * k3_1 +
    (12207403582455665761714176 / 19769094600025 : ℝ) * k3_2 +
    (4200887608008066574843904 / 19769094600025 : ℝ) * k3_3 +
    (492934089751058571206656 / 19769094600025 : ℝ) * k3_4 +
    (1418965574939372374982656 / 19769094600025 : ℝ) * k4_0 +
    (3839259498987040951762944 / 19769094600025 : ℝ) * k4_1 +
    (3571916807183546288439296 / 19769094600025 : ℝ) * k4_2 +
    (1327484135137236047888384 / 19769094600025 : ℝ) * k4_3 +
    (176120408309933506789376 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf5 {s t : ℝ} (h1 : (453 / 800 : ℝ) ≤ s) (h2 : s ≤ (929 / 1600 : ℝ)) (h3 : (5261 / 8000 : ℝ) ≤ t) (h4 : t ≤ (10727 / 16000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (453 / 800 : ℝ) := by linarith
  have u2 : 0 ≤ (929 / 1600 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (5261 / 8000 : ℝ) := by linarith
  have v2 : 0 ≤ (10727 / 16000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (32372483456307075815047168 / 19769094600025 : ℝ) * k0_0 +
    (84551133123689745064394752 / 19769094600025 : ℝ) * k0_1 +
    (99297878600048140167938048 / 19769094600025 : ℝ) * k0_2 +
    (75237871222577003219648512 / 19769094600025 : ℝ) * k0_3 +
    (28122566064182249351938048 / 19769094600025 : ℝ) * k0_4 +
    (116550431122501547737481216 / 19769094600025 : ℝ) * k1_0 +
    (268565604412329636946509824 / 19769094600025 : ℝ) * k1_1 +
    (266671457400041754998603776 / 19769094600025 : ℝ) * k1_2 +
    (197093008033555822104018944 / 19769094600025 : ℝ) * k1_3 +
    (82452530383758267357003776 / 19769094600025 : ℝ) * k1_4 +
    (32872284725442289654038528 / 3953818920005 : ℝ) * k2_0 +
    (66871805096354165441953792 / 3953818920005 : ℝ) * k2_1 +
    (51690647338862273201963008 / 3953818920005 : ℝ) * k2_2 +
    (35235431996718242111946752 / 3953818920005 : ℝ) * k2_3 +
    (17549080375892650862379008 / 3953818920005 : ℝ) * k2_4 +
    (108908732885522699653218304 / 19769094600025 : ℝ) * k3_0 +
    (202639532238442652506259456 / 19769094600025 : ℝ) * k3_1 +
    (116241430599825955311058944 / 19769094600025 : ℝ) * k3_2 +
    (63490105421206609171316736 / 19769094600025 : ℝ) * k3_3 +
    (40995503361383203433938944 / 19769094600025 : ℝ) * k3_4 +
    (28727460743210925096435712 / 19769094600025 : ℝ) * k4_0 +
    (52303950596744943271149568 / 19769094600025 : ℝ) * k4_1 +
    (25175467447576671663685632 / 19769094600025 : ℝ) * k4_2 +
    (9177369353252281445777408 / 19769094600025 : ℝ) * k4_3 +
    (7582426896813587846725632 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf6 {s t : ℝ} (h1 : (453 / 800 : ℝ) ≤ s) (h2 : s ≤ (929 / 1600 : ℝ)) (h3 : (10727 / 16000 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (453 / 800 : ℝ) := by linarith
  have u2 : 0 ≤ (929 / 1600 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (10727 / 16000 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 0 * ((929 / 1600 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 1 * ((929 / 1600 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 2 * ((929 / 1600 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 3 * ((929 / 1600 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (453 / 800 : ℝ)) ^ 4 * ((929 / 1600 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (28122566064182249351938048 / 19769094600025 : ℝ) * k0_0 +
    (149742657290880991595855872 / 19769094600025 : ℝ) * k0_1 +
    (322812236804960105296560128 / 19769094600025 : ℝ) * k0_2 +
    (309708040659410756233592832 / 19769094600025 : ℝ) * k0_3 +
    (108519818855420110231830528 / 19769094600025 : ℝ) * k0_4 +
    (82452530383758267357003776 / 19769094600025 : ℝ) * k1_0 +
    (462527235036510316752011264 / 19769094600025 : ℝ) * k1_1 +
    (1062974138408905238942580736 / 19769094600025 : ℝ) * k1_2 +
    (1071485101065432073223798784 / 19769094600025 : ℝ) * k1_3 +
    (388601473769694994718785536 / 19769094600025 : ℝ) * k1_4 +
    (17549080375892650862379008 / 3953818920005 : ℝ) * k2_0 +
    (105157211010422964787085312 / 3953818920005 : ℝ) * k2_1 +
    (261455984379976441227378688 / 3953818920005 : ℝ) * k2_2 +
    (278636172327040849618665472 / 3953818920005 : ℝ) * k2_3 +
    (104793093928719528480473088 / 3953818920005 : ℝ) * k2_4 +
    (40995503361383203433938944 / 19769094600025 : ℝ) * k3_0 +
    (264473921469859018300194816 / 19769094600025 : ℝ) * k3_1 +
    (719192878745783182697693184 / 19769094600025 : ℝ) * k3_2 +
    (812301032670644368568221696 / 19769094600025 : ℝ) * k3_3 +
    (316602601220419597457424384 / 19769094600025 : ℝ) * k3_4 +
    (7582426896813587846725632 / 19769094600025 : ℝ) * k4_0 +
    (51482045821256421328027648 / 19769094600025 : ℝ) * k4_1 +
    (152089496851589091310436352 / 19769094600025 : ℝ) * k4_2 +
    (180907147652569177129484288 / 19769094600025 : ℝ) * k4_3 +
    (72721304863026879190269952 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf7 {s t : ℝ} (h1 : (929 / 1600 : ℝ) ≤ s) (h2 : s ≤ (119 / 200 : ℝ)) (h3 : (5261 / 8000 : ℝ) ≤ t) (h4 : t ≤ (10727 / 16000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (929 / 1600 : ℝ) := by linarith
  have u2 : 0 ≤ (119 / 200 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (5261 / 8000 : ℝ) := by linarith
  have v2 : 0 ≤ (10727 / 16000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (28727460743210925096435712 / 19769094600025 : ℝ) * k0_0 +
    (52303950596744943271149568 / 19769094600025 : ℝ) * k0_1 +
    (25175467447576671663685632 / 19769094600025 : ℝ) * k0_2 +
    (9177369353252281445777408 / 19769094600025 : ℝ) * k0_3 +
    (7582426896813587846725632 / 19769094600025 : ℝ) * k0_4 +
    (120910953060164701118267392 / 19769094600025 : ℝ) * k1_0 +
    (215792072535516893662937088 / 19769094600025 : ℝ) * k1_1 +
    (85162308980787417998426112 / 19769094600025 : ℝ) * k1_2 +
    (9928849404811642394902528 / 19769094600025 : ℝ) * k1_3 +
    (19663911813125499339866112 / 19769094600025 : ℝ) * k1_4 +
    (200368084151137452665339904 / 19769094600025 : ℝ) * k2_0 +
    (373816646372993550679801856 / 19769094600025 : ℝ) * k2_1 +
    (165215871837195754071916544 / 19769094600025 : ℝ) * k2_2 +
    (15493391934406310230491136 / 19769094600025 : ℝ) * k2_3 +
    (23750627234690142029676544 / 19769094600025 : ℝ) * k2_4 +
    (30653842508564290518122496 / 3953818920005 : ℝ) * k3_0 +
    (62184505949856005298847744 / 3953818920005 : ℝ) * k3_1 +
    (35571856100349147709177856 / 3953818920005 : ℝ) * k3_2 +
    (7882037230080543268798464 / 3953818920005 : ℝ) * k3_3 +
    (3844139499106223955705856 / 3953818920005 : ℝ) * k3_4 +
    (45086824527342977738080256 / 19769094600025 : ℝ) * k4_0 +
    (100602977866491652298768384 / 19769094600025 : ℝ) * k4_1 +
    (72643944939829198340489216 / 19769094600025 : ℝ) * k4_2 +
    (24677561372213831012450304 / 19769094600025 : ℝ) * k4_3 +
    (7553916272470509961609216 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf8 {s t : ℝ} (h1 : (929 / 1600 : ℝ) ≤ s) (h2 : s ≤ (119 / 200 : ℝ)) (h3 : (10727 / 16000 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (929 / 1600 : ℝ) := by linarith
  have u2 : 0 ≤ (119 / 200 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (10727 / 16000 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (929 / 1600 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (7582426896813587846725632 / 19769094600025 : ℝ) * k0_0 +
    (51482045821256421328027648 / 19769094600025 : ℝ) * k0_1 +
    (152089496851589091310436352 / 19769094600025 : ℝ) * k0_2 +
    (180907147652569177129484288 / 19769094600025 : ℝ) * k0_3 +
    (72721304863026879190269952 / 19769094600025 : ℝ) * k0_4 +
    (19663911813125499339866112 / 19769094600025 : ℝ) * k1_0 +
    (147382445100192352324026368 / 19769094600025 : ℝ) * k1_1 +
    (497523096066929547785797632 / 19769094600025 : ℝ) * k1_2 +
    (634956148549909048467652608 / 19769094600025 : ℝ) * k1_3 +
    (265167837683795436064735232 / 19769094600025 : ℝ) * k1_4 +
    (23750627234690142029676544 / 19769094600025 : ℝ) * k2_0 +
    (174511625943114826006921216 / 19769094600025 : ℝ) * k2_1 +
    (642270573863321301401206784 / 19769094600025 : ℝ) * k2_2 +
    (861146209272998287791620096 / 19769094600025 : ℝ) * k2_3 +
    (369661179033725158224297984 / 19769094600025 : ℝ) * k2_4 +
    (3844139499106223955705856 / 3953818920005 : ℝ) * k3_0 +
    (22871078762769248376848384 / 3953818920005 : ℝ) * k3_1 +
    (80538980698415263033327616 / 3953818920005 : ℝ) * k3_2 +
    (108530935661973232894869504 / 3953818920005 : ℝ) * k3_3 +
    (47022189155304107898044416 / 3953818920005 : ℝ) * k3_4 +
    (7553916272470509961609216 / 19769094600025 : ℝ) * k4_0 +
    (35753768807550248680423424 / 19769094600025 : ℝ) * k4_1 +
    (105872567245838451344408576 / 19769094600025 : ℝ) * k4_2 +
    (135567386145315487685279744 / 19769094600025 : ℝ) * k4_3 +
    (57898817935493977788645376 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf9 {s t : ℝ} (h1 : (43 / 80 : ℝ) ≤ s) (h2 : s ≤ (119 / 200 : ℝ)) (h3 : (2733 / 4000 : ℝ) ≤ t) (h4 : t ≤ (1469 / 2000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (43 / 80 : ℝ) := by linarith
  have u2 : 0 ≤ (119 / 200 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (2733 / 4000 : ℝ) := by linarith
  have v2 : 0 ≤ (1469 / 2000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (43 / 80 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (712466734049603480576 / 3953818920005 : ℝ) * k0_0 +
    (4728382128600294457344 / 3953818920005 : ℝ) * k0_1 +
    (12008248933051889074176 / 3953818920005 : ℝ) * k0_2 +
    (12835409927208082202624 / 3953818920005 : ℝ) * k0_3 +
    (210694253571638689792 / 171905170435 : ℝ) * k0_4 +
    (9493686391542989843456 / 19769094600025 : ℝ) * k1_0 +
    (71918102174254781784064 / 19769094600025 : ℝ) * k1_1 +
    (201670568999154357805056 / 19769094600025 : ℝ) * k1_2 +
    (228738198716142250655744 / 19769094600025 : ℝ) * k1_3 +
    (3893548453069466058752 / 859525852175 : ℝ) * k1_4 +
    (8806167375206572121088 / 19769094600025 : ℝ) * k2_0 +
    (80700387234366609743872 / 19769094600025 : ℝ) * k2_1 +
    (254920372003475693477888 / 19769094600025 : ℝ) * k2_2 +
    (307868371506752404160512 / 19769094600025 : ℝ) * k2_3 +
    (5431920992256812138496 / 859525852175 : ℝ) * k2_4 +
    (3748443113405676643328 / 19769094600025 : ℝ) * k3_0 +
    (41777329095769855762432 / 19769094600025 : ℝ) * k3_1 +
    (147476674264134778544128 / 19769094600025 : ℝ) * k3_2 +
    (187977338289589519286272 / 19769094600025 : ℝ) * k3_3 +
    (3417069523168730136576 / 859525852175 : ℝ) * k3_4 +
    (883465849845794338816 / 19769094600025 : ℝ) * k4_0 +
    (9394940401132470779904 / 19769094600025 : ℝ) * k4_1 +
    (34252023277871439036416 / 19769094600025 : ℝ) * k4_2 +
    (44716837765552961552384 / 19769094600025 : ℝ) * k4_3 +
    (825760274271919439872 / 859525852175 : ℝ) * k4_4

theorem polyLin_leaf10 {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (119 / 200 : ℝ)) (h3 : (1469 / 2000 : ℝ) ≤ t) (h4 : t ≤ (837 / 1000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (12 / 25 : ℝ) := by linarith
  have u2 : 0 ≤ (119 / 200 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (1469 / 2000 : ℝ) := by linarith
  have v2 : 0 ≤ (837 / 1000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((119 / 200 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((119 / 200 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((119 / 200 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((119 / 200 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((119 / 200 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (5572101008347947008 / 859525852175 : ℝ) * k0_0 +
    (778815099703313760256 / 19769094600025 : ℝ) * k0_1 +
    (1749341529562000523264 / 19769094600025 : ℝ) * k0_2 +
    (1697653388836191338496 / 19769094600025 : ℝ) * k0_3 +
    (599763458605633634304 / 19769094600025 : ℝ) * k0_4 +
    (19110920814163806336 / 859525852175 : ℝ) * k1_0 +
    (2806213391971366474752 / 19769094600025 : ℝ) * k1_1 +
    (6549118258406354393088 / 19769094600025 : ℝ) * k1_2 +
    (6535164879306794360832 / 19769094600025 : ℝ) * k1_3 +
    (2356105631936806176768 / 19769094600025 : ℝ) * k1_4 +
    (4827990996598737792 / 171905170435 : ℝ) * k2_0 +
    (751415385556891833344 / 3953818920005 : ℝ) * k2_1 +
    (1829916096287402715136 / 3953818920005 : ℝ) * k2_2 +
    (1880840698429338159104 / 3953818920005 : ℝ) * k2_3 +
    (692380486067358468096 / 3953818920005 : ℝ) * k2_4 +
    (13793351364256962944 / 859525852175 : ℝ) * k3_0 +
    (2267220245933615582208 / 19769094600025 : ℝ) * k3_1 +
    (5741534434882639153152 / 19769094600025 : ℝ) * k3_2 +
    (6060229239558453014528 / 19769094600025 : ℝ) * k3_3 +
    (2272499780042766415872 / 19769094600025 : ℝ) * k3_4 +
    (3225626071374685312 / 859525852175 : ℝ) * k4_0 +
    (540922500656030633984 / 19769094600025 : ℝ) * k4_1 +
    (1397262788973657783296 / 19769094600025 : ℝ) * k4_2 +
    (1497532489888448185344 / 19769094600025 : ℝ) * k4_3 +
    (568015131259575033856 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf11 {s t : ℝ} (h1 : (119 / 200 : ℝ) ≤ s) (h2 : s ≤ (499 / 800 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (5261 / 8000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (119 / 200 : ℝ) := by linarith
  have u2 : 0 ≤ (499 / 800 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (79 / 125 : ℝ) := by linarith
  have v2 : 0 ≤ (5261 / 8000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 0 * ((5261 / 8000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 1 * ((5261 / 8000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 2 * ((5261 / 8000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 3 * ((5261 / 8000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 4 * ((5261 / 8000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (1418965574939372374982656 / 19769094600025 : ℝ) * k0_0 +
    (3839259498987040951762944 / 19769094600025 : ℝ) * k0_1 +
    (3571916807183546288439296 / 19769094600025 : ℝ) * k0_2 +
    (1327484135137236047888384 / 19769094600025 : ℝ) * k0_3 +
    (176120408309933506789376 / 19769094600025 : ℝ) * k0_4 +
    (6171255650138909585702912 / 19769094600025 : ℝ) * k1_0 +
    (17035179683139245769228288 / 19769094600025 : ℝ) * k1_1 +
    (16367930875012704545800192 / 19769094600025 : ℝ) * k1_2 +
    (6418985473089821808263168 / 19769094600025 : ℝ) * k1_3 +
    (916029176728409483108352 / 19769094600025 : ℝ) * k1_4 +
    (406471346911475560087552 / 790763784001 : ℝ) * k2_0 +
    (1149169151117270500507648 / 790763784001 : ℝ) * k2_1 +
    (1147140059485814620946432 / 790763784001 : ℝ) * k2_2 +
    (478958861583194944176128 / 790763784001 : ℝ) * k2_3 +
    (74580474267231947169792 / 790763784001 : ℝ) * k2_4 +
    (7495437590225986925887488 / 19769094600025 : ℝ) * k3_0 +
    (21750683554672600979341312 / 19769094600025 : ℝ) * k3_1 +
    (22604409362954061855326208 / 19769094600025 : ℝ) * k3_2 +
    (10044905194783588909842432 / 19769094600025 : ℝ) * k3_3 +
    (1696820182760407854850048 / 19769094600025 : ℝ) * k3_4 +
    (2086062071731157880274944 / 19769094600025 : ℝ) * k4_0 +
    (6217866936839686633619456 / 19769094600025 : ℝ) * k4_1 +
    (6722689396922648162402304 / 19769094600025 : ℝ) * k4_2 +
    (3162966288256049147478016 / 19769094600025 : ℝ) * k4_3 +
    (572354833167160263860224 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf12 {s t : ℝ} (h1 : (119 / 200 : ℝ) ≤ s) (h2 : s ≤ (39 / 64 : ℝ)) (h3 : (5261 / 8000 : ℝ) ≤ t) (h4 : t ≤ (10727 / 16000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (119 / 200 : ℝ) := by linarith
  have u2 : 0 ≤ (39 / 64 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (5261 / 8000 : ℝ) := by linarith
  have v2 : 0 ≤ (10727 / 16000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((10727 / 16000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((10727 / 16000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((10727 / 16000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((10727 / 16000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((10727 / 16000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (45086824527342977738080256 / 19769094600025 : ℝ) * k0_0 +
    (100602977866491652298768384 / 19769094600025 : ℝ) * k0_1 +
    (72643944939829198340489216 / 19769094600025 : ℝ) * k0_2 +
    (24677561372213831012450304 / 19769094600025 : ℝ) * k0_3 +
    (7553916272470509961609216 / 19769094600025 : ℝ) * k0_4 +
    (207425383675922369314029568 / 19769094600025 : ℝ) * k1_0 +
    (493901293182653191895908352 / 19769094600025 : ℝ) * k1_1 +
    (403292279016887848178024448 / 19769094600025 : ℝ) * k1_2 +
    (158010304827307931755610112 / 19769094600025 : ℝ) * k1_3 +
    (41210632684232959914344448 / 19769094600025 : ℝ) * k1_4 +
    (362836597550440202835591168 / 19769094600025 : ℝ) * k2_0 +
    (922752936673113046884810752 / 19769094600025 : ℝ) * k2_1 +
    (841514867382622082968322048 / 19769094600025 : ℝ) * k2_2 +
    (371293747965121956465344512 / 19769094600025 : ℝ) * k2_3 +
    (89720432800795662437122048 / 19769094600025 : ℝ) * k2_4 +
    (284109217905502966074310656 / 19769094600025 : ℝ) * k3_0 +
    (767699447692829864685993984 / 19769094600025 : ℝ) * k3_1 +
    (765996050421581082634223616 / 19769094600025 : ℝ) * k3_2 +
    (368804448438823594797563904 / 19769094600025 : ℝ) * k3_3 +
    (86415547898317950207983616 / 19769094600025 : ℝ) * k3_4 +
    (3344535332893894264225792 / 790763784001 : ℝ) * k4_0 +
    (9530151955492463339634688 / 790763784001 : ℝ) * k4_1 +
    (10205728474323444681408512 / 790763784001 : ℝ) * k4_2 +
    (5234109241338152121008128 / 790763784001 : ℝ) * k4_3 +
    (1214167704184094337728512 / 790763784001 : ℝ) * k4_4

theorem polyLin_leaf13 {s t : ℝ} (h1 : (119 / 200 : ℝ) ≤ s) (h2 : s ≤ (39 / 64 : ℝ)) (h3 : (10727 / 16000 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (119 / 200 : ℝ) := by linarith
  have u2 : 0 ≤ (39 / 64 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (10727 / 16000 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((39 / 64 : ℝ) - s) ^ 4 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((39 / 64 : ℝ) - s) ^ 3 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((39 / 64 : ℝ) - s) ^ 2 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((39 / 64 : ℝ) - s) ^ 1 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((39 / 64 : ℝ) - s) ^ 0 * (t - (10727 / 16000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (7553916272470509961609216 / 19769094600025 : ℝ) * k0_0 +
    (35753768807550248680423424 / 19769094600025 : ℝ) * k0_1 +
    (105872567245838451344408576 / 19769094600025 : ℝ) * k0_2 +
    (135567386145315487685279744 / 19769094600025 : ℝ) * k0_3 +
    (57898817935493977788645376 / 19769094600025 : ℝ) * k0_4 +
    (41210632684232959914344448 / 19769094600025 : ℝ) * k1_0 +
    (171674756646555747559145472 / 19769094600025 : ℝ) * k1_1 +
    (444285634474631295588630528 / 19769094600025 : ℝ) * k1_2 +
    (541884410852657737007890432 / 19769094600025 : ℝ) * k1_3 +
    (228079597707431282818940928 / 19769094600025 : ℝ) * k1_4 +
    (89720432800795662437122048 / 19769094600025 : ℝ) * k2_0 +
    (346469714441243343031631872 / 19769094600025 : ℝ) * k2_1 +
    (767042766810986242667184128 / 19769094600025 : ℝ) * k2_2 +
    (858835406901373005392248832 / 19769094600025 : ℝ) * k2_3 +
    (348567134826457388210454528 / 19769094600025 : ℝ) * k2_4 +
    (86415547898317950207983616 / 19769094600025 : ℝ) * k3_0 +
    (322519934747720006866305024 / 19769094600025 : ℝ) * k3_1 +
    (627142509348270318840446976 / 19769094600025 : ℝ) * k3_2 +
    (635928905473785734935609344 / 19769094600025 : ℝ) * k3_3 +
    (244907703068666012186443776 / 19769094600025 : ℝ) * k3_4 +
    (1214167704184094337728512 / 790763784001 : ℝ) * k4_0 +
    (4479232392134602580819968 / 790763784001 : ℝ) * k4_1 +
    (7941097926712796060844032 / 790763784001 : ℝ) * k4_2 +
    (7336817579634508741214208 / 790763784001 : ℝ) * k4_3 +
    (2660954655443038746181632 / 790763784001 : ℝ) * k4_4

theorem polyLin_leaf14 {s t : ℝ} (h1 : (39 / 64 : ℝ) ≤ s) (h2 : s ≤ (499 / 800 : ℝ)) (h3 : (5261 / 8000 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (39 / 64 : ℝ) := by linarith
  have u2 : 0 ≤ (499 / 800 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (5261 / 8000 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 0 * ((499 / 800 : ℝ) - s) ^ 4 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 1 * ((499 / 800 : ℝ) - s) ^ 3 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 2 * ((499 / 800 : ℝ) - s) ^ 2 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 3 * ((499 / 800 : ℝ) - s) ^ 1 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (39 / 64 : ℝ)) ^ 4 * ((499 / 800 : ℝ) - s) ^ 0 * (t - (5261 / 8000 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (209033458305868391514112 / 790763784001 : ℝ) * k0_0 +
    (355135161213084351397888 / 790763784001 : ℝ) * k0_1 +
    (231825885106397767073792 / 790763784001 : ℝ) * k0_2 +
    (251863533593553906106368 / 790763784001 : ℝ) * k0_3 +
    (166309665965189921636352 / 790763784001 : ℝ) * k0_4 +
    (24049865542079742923177984 / 19769094600025 : ℝ) * k1_0 +
    (46091905757388878712406016 / 19769094600025 : ℝ) * k1_1 +
    (36212500586131869735583744 / 19769094600025 : ℝ) * k1_2 +
    (32108519301654067400933376 / 19769094600025 : ℝ) * k1_3 +
    (17955201751246358565617664 / 19769094600025 : ℝ) * k1_4 +
    (41556405615859935307825152 / 19769094600025 : ℝ) * k2_0 +
    (88105305513011741587406848 / 19769094600025 : ℝ) * k2_1 +
    (78589562127605762392850432 / 19769094600025 : ℝ) * k2_2 +
    (61745637809849339363196928 / 19769094600025 : ℝ) * k2_3 +
    (29730856855017785175048192 / 19769094600025 : ℝ) * k2_4 +
    (31889916123432391282327552 / 19769094600025 : ℝ) * k3_0 +
    (73545166204996846260584448 / 19769094600025 : ℝ) * k3_1 +
    (71874345872760922827128832 / 19769094600025 : ℝ) * k3_2 +
    (52455494564667277105430528 / 19769094600025 : ℝ) * k3_3 +
    (22253764320552320045678592 / 19769094600025 : ℝ) * k3_4 +
    (9157677330674564221763584 / 19769094600025 : ℝ) * k4_0 +
    (22653958033299727414460416 / 19769094600025 : ℝ) * k4_1 +
    (23702522614371193762873344 / 19769094600025 : ℝ) * k4_2 +
    (16522397650039115036491776 / 19769094600025 : ℝ) * k4_3 +
    (6320524965896772873355264 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf15 {s t : ℝ} (h1 : (499 / 800 : ℝ) ≤ s) (h2 : s ≤ (261 / 400 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (499 / 800 : ℝ) := by linarith
  have u2 : 0 ≤ (261 / 400 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (79 / 125 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (499 / 800 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (130378879483197367517184 / 19769094600025 : ℝ) * k0_0 +
    (255717849172171359133696 / 19769094600025 : ℝ) * k0_1 +
    (131245524814963758096384 / 19769094600025 : ℝ) * k0_2 +
    (1318392567338848264192 / 859525852175 : ℝ) * k0_3 +
    (24689550648034269036544 / 19769094600025 : ℝ) * k0_4 +
    (14013809426254994079744 / 482173039025 : ℝ) * k1_0 +
    (29286993819507133710336 / 482173039025 : ℝ) * k1_1 +
    (18160465718260362706944 / 482173039025 : ℝ) * k1_2 +
    (254177498440992489472 / 20964045175 : ℝ) * k1_3 +
    (2985782293221859221504 / 482173039025 : ℝ) * k1_4 +
    (953415490811172285841408 / 19769094600025 : ℝ) * k2_0 +
    (2118079778511390337073152 / 19769094600025 : ℝ) * k2_1 +
    (1524415428489932846071808 / 19769094600025 : ℝ) * k2_2 +
    (1117454610119156891648 / 37370689225 : ℝ) * k2_3 +
    (233062569564668418121728 / 19769094600025 : ℝ) * k2_4 +
    (141057678171173193515008 / 3953818920005 : ℝ) * k3_0 +
    (331901156099971346071552 / 3953818920005 : ℝ) * k3_1 +
    (268911633655284624785408 / 3953818920005 : ℝ) * k3_2 +
    (5110369952471381704704 / 171905170435 : ℝ) * k3_3 +
    (39697166810532940259328 / 3953818920005 : ℝ) * k3_4 +
    (196067586981233743101952 / 19769094600025 : ℝ) * k4_0 +
    (486506876636287248498688 / 19769094600025 : ℝ) * k4_1 +
    (433527961421104557719552 / 19769094600025 : ℝ) * k4_2 +
    (8954882603329353547776 / 859525852175 : ℝ) * k4_3 +
    (63160625252409959596032 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf16 {s t : ℝ} (h1 : (119 / 200 : ℝ) ≤ s) (h2 : s ≤ (261 / 400 : ℝ)) (h3 : (2733 / 4000 : ℝ) ≤ t) (h4 : t ≤ (1469 / 2000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (119 / 200 : ℝ) := by linarith
  have u2 : 0 ≤ (261 / 400 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (2733 / 4000 : ℝ) := by linarith
  have v2 : 0 ≤ (1469 / 2000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((261 / 400 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((261 / 400 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((261 / 400 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((261 / 400 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((261 / 400 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (883465849845794338816 / 19769094600025 : ℝ) * k0_0 +
    (9394940401132470779904 / 19769094600025 : ℝ) * k0_1 +
    (34252023277871439036416 / 19769094600025 : ℝ) * k0_2 +
    (44716837765552961552384 / 19769094600025 : ℝ) * k0_3 +
    (825760274271919439872 / 859525852175 : ℝ) * k0_4 +
    (132771347414427122688 / 790763784001 : ℝ) * k1_0 +
    (1335287764531596419072 / 790763784001 : ℝ) * k1_1 +
    (5061580478353469349888 / 790763784001 : ℝ) * k1_2 +
    (6790294553393366925312 / 790763784001 : ℝ) * k1_3 +
    (127560506840265015296 / 34381034087 : ℝ) * k1_4 +
    (7518689091071576392704 / 19769094600025 : ℝ) * k2_0 +
    (55514982286926773886976 / 19769094600025 : ℝ) * k2_1 +
    (192108885087581559087104 / 19769094600025 : ℝ) * k2_2 +
    (253208448142486365700096 / 19769094600025 : ℝ) * k2_3 +
    (4747750435770497875968 / 859525852175 : ℝ) * k2_4 +
    (9020572943480597763072 / 19769094600025 : ℝ) * k3_0 +
    (50193590450212452999168 / 19769094600025 : ℝ) * k3_1 +
    (144355572737017122742272 / 19769094600025 : ℝ) * k3_2 +
    (177946036333487904227328 / 19769094600025 : ℝ) * k3_3 +
    (3253630014634442932224 / 859525852175 : ℝ) * k3_4 +
    (3947539078275622474752 / 19769094600025 : ℝ) * k4_0 +
    (18707668883919034073088 / 19769094600025 : ℝ) * k4_1 +
    (44600573013718299901952 / 19769094600025 : ℝ) * k4_2 +
    (49824836162896756891648 / 19769094600025 : ℝ) * k4_3 +
    (869666533747379830784 / 859525852175 : ℝ) * k4_4

theorem polyLin_leaf17 {s t : ℝ} (h1 : (261 / 400 : ℝ) ≤ s) (h2 : s ≤ (71 / 100 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (2733 / 4000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (261 / 400 : ℝ) := by linarith
  have u2 : 0 ≤ (71 / 100 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (79 / 125 : ℝ) := by linarith
  have v2 : 0 ≤ (2733 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 0 * ((2733 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 1 * ((2733 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 2 * ((2733 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 3 * ((2733 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (79 / 125 : ℝ)) ^ 4 * ((2733 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (12254224186327108943872 / 19769094600025 : ℝ) * k0_0 +
    (30406679789767953031168 / 19769094600025 : ℝ) * k0_1 +
    (27095497588819034857472 / 19769094600025 : ℝ) * k0_2 +
    (559680162708084596736 / 859525852175 : ℝ) * k0_3 +
    (3947539078275622474752 / 19769094600025 : ℝ) * k0_4 +
    (58889641378942061379584 / 19769094600025 : ℝ) * k1_0 +
    (157441934914733345079296 / 19769094600025 : ℝ) * k1_1 +
    (157076200031275527798784 / 19769094600025 : ℝ) * k1_2 +
    (3522180732202401595392 / 859525852175 : ℝ) * k1_3 +
    (22559739682724382034944 / 19769094600025 : ℝ) * k1_4 +
    (21326507810321548181504 / 3953818920005 : ℝ) * k2_0 +
    (60907330042595645259776 / 3953818920005 : ℝ) * k2_1 +
    (66326557521547015880704 / 3953818920005 : ℝ) * k2_2 +
    (1580452362354039652352 / 171905170435 : ℝ) * k2_3 +
    (9627237861760585841664 / 3953818920005 : ℝ) * k2_4 +
    (85948035963311175499776 / 19769094600025 : ℝ) * k3_0 +
    (259825702575111726956544 / 19769094600025 : ℝ) * k3_1 +
    (302763517170089554968576 / 19769094600025 : ℝ) * k3_2 +
    (7549509955589136908288 / 859525852175 : ℝ) * k3_3 +
    (44829847861978373538816 / 19769094600025 : ℝ) * k3_4 +
    (25958294047601058643968 / 19769094600025 : ℝ) * k4_0 +
    (82356284707298624929792 / 19769094600025 : ℝ) * k4_1 +
    (101163084005714135482368 / 19769094600025 : ℝ) * k4_2 +
    (2611352718284465373184 / 859525852175 : ℝ) * k4_3 +
    (15315696547975921266688 / 19769094600025 : ℝ) * k4_4

theorem polyLin_leaf18 {s t : ℝ} (h1 : (261 / 400 : ℝ) ≤ s) (h2 : s ≤ (71 / 100 : ℝ)) (h3 : (2733 / 4000 : ℝ) ≤ t) (h4 : t ≤ (1469 / 2000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (261 / 400 : ℝ) := by linarith
  have u2 : 0 ≤ (71 / 100 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (2733 / 4000 : ℝ) := by linarith
  have v2 : 0 ≤ (1469 / 2000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 0 * ((1469 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 1 * ((1469 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 2 * ((1469 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 3 * ((1469 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (261 / 400 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (2733 / 4000 : ℝ)) ^ 4 * ((1469 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (3947539078275622474752 / 19769094600025 : ℝ) * k0_0 +
    (18707668883919034073088 / 19769094600025 : ℝ) * k0_1 +
    (44600573013718299901952 / 19769094600025 : ℝ) * k0_2 +
    (49824836162896756891648 / 19769094600025 : ℝ) * k0_3 +
    (869666533747379830784 / 859525852175 : ℝ) * k0_4 +
    (22559739682724382034944 / 19769094600025 : ℝ) * k1_0 +
    (99467760621139819585536 / 19769094600025 : ℝ) * k1_1 +
    (212449011372729276473344 / 19769094600025 : ℝ) * k1_2 +
    (220652652969686150905856 / 19769094600025 : ℝ) * k1_3 +
    (3703702255344595714048 / 859525852175 : ℝ) * k1_4 +
    (9627237861760585841664 / 3953818920005 : ℝ) * k2_0 +
    (40667498559941774729216 / 3953818920005 : ℝ) * k2_1 +
    (79277840198943604056064 / 3953818920005 : ℝ) * k2_2 +
    (76265659610216221147136 / 3953818920005 : ℝ) * k2_3 +
    (1219593431580191244288 / 171905170435 : ℝ) * k2_4 +
    (44829847861978373538816 / 19769094600025 : ℝ) * k3_0 +
    (185000053917276839419904 / 19769094600025 : ℝ) * k3_1 +
    (336847491986269626556416 / 19769094600025 : ℝ) * k3_2 +
    (302118749945952659472384 / 19769094600025 : ℝ) * k3_3 +
    (4587757976378205519872 / 859525852175 : ℝ) * k3_4 +
    (15315696547975921266688 / 19769094600025 : ℝ) * k4_0 +
    (62464459863264666550272 / 19769094600025 : ℝ) * k4_1 +
    (108373126033880024383488 / 19769094600025 : ℝ) * k4_2 +
    (91664990604274954534912 / 19769094600025 : ℝ) * k4_3 +
    (1324361098223194013696 / 859525852175 : ℝ) * k4_4

theorem polyLin_leaf19 {s t : ℝ} (h1 : (119 / 200 : ℝ) ≤ s) (h2 : s ≤ (71 / 100 : ℝ)) (h3 : (1469 / 2000 : ℝ) ≤ t) (h4 : t ≤ (837 / 1000 : ℝ)) :
    0 ≤ polyLin s t := by
  have u1 : 0 ≤ s - (119 / 200 : ℝ) := by linarith
  have u2 : 0 ≤ (71 / 100 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (1469 / 2000 : ℝ) := by linarith
  have v2 : 0 ≤ (837 / 1000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 0 * ((71 / 100 : ℝ) - s) ^ 4 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 1 * ((71 / 100 : ℝ) - s) ^ 3 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 2 * ((71 / 100 : ℝ) - s) ^ 2 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 3 * ((71 / 100 : ℝ) - s) ^ 1 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 0 * ((837 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 1 * ((837 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 2 * ((837 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 3 * ((837 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (119 / 200 : ℝ)) ^ 4 * ((71 / 100 : ℝ) - s) ^ 0 * (t - (1469 / 2000 : ℝ)) ^ 4 * ((837 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyLin
  linear_combination (3225626071374685312 / 859525852175 : ℝ) * k0_0 +
    (540922500656030633984 / 19769094600025 : ℝ) * k0_1 +
    (1397262788973657783296 / 19769094600025 : ℝ) * k0_2 +
    (1497532489888448185344 / 19769094600025 : ℝ) * k0_3 +
    (568015131259575033856 / 19769094600025 : ℝ) * k0_4 +
    (12011657206740519552 / 859525852175 : ℝ) * k1_0 +
    (2060159759314629489664 / 19769094600025 : ℝ) * k1_1 +
    (5436567876906623113216 / 19769094600025 : ℝ) * k1_2 +
    (5920030679549132468224 / 19769094600025 : ℝ) * k1_3 +
    (2271621270033833854976 / 19769094600025 : ℝ) * k1_4 +
    (18794872510444358784 / 859525852175 : ℝ) * k2_0 +
    (3135895467927500889088 / 19769094600025 : ℝ) * k2_1 +
    (8234680807508965455872 / 19769094600025 : ℝ) * k2_2 +
    (8983607812118729156608 / 19769094600025 : ℝ) * k2_3 +
    (3459266900309994657792 / 19769094600025 : ℝ) * k2_4 +
    (3029743406143464832 / 171905170435 : ℝ) * k3_0 +
    (464994277791212698624 / 3953818920005 : ℝ) * k3_1 +
    (1172639939181415827456 / 3953818920005 : ℝ) * k3_2 +
    (1255987578201774915584 / 3953818920005 : ℝ) * k3_3 +
    (479598185840713455616 / 3953818920005 : ℝ) * k3_4 +
    (5173285539934351616 / 859525852175 : ℝ) * k4_0 +
    (711694069925982963712 / 19769094600025 : ℝ) * k4_1 +
    (1673356083014757347328 / 19769094600025 : ℝ) * k4_2 +
    (1722823520556912648192 / 19769094600025 : ℝ) * k4_3 +
    (643405775890259857408 / 19769094600025 : ℝ) * k4_4

theorem polyLin_nonneg {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (71 / 100 : ℝ)) (h3 : (79 / 125 : ℝ) ≤ t) (h4 : t ≤ (837 / 1000 : ℝ)) :
    0 ≤ polyLin s t := by
  rcases le_total s (119 / 200 : ℝ) with h | h
  · rcases le_total t (1469 / 2000 : ℝ) with h | h
    · rcases le_total s (43 / 80 : ℝ) with h | h
      · rcases le_total t (2733 / 4000 : ℝ) with h | h
        · exact polyLin_leaf0 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact polyLin_leaf1 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total t (2733 / 4000 : ℝ) with h | h
        · rcases le_total s (453 / 800 : ℝ) with h | h
          · rcases le_total t (5261 / 8000 : ℝ) with h | h
            · exact polyLin_leaf2 (by linarith) (by linarith) (by linarith) (by linarith)
            · exact polyLin_leaf3 (by linarith) (by linarith) (by linarith) (by linarith)
          · rcases le_total t (5261 / 8000 : ℝ) with h | h
            · exact polyLin_leaf4 (by linarith) (by linarith) (by linarith) (by linarith)
            · rcases le_total s (929 / 1600 : ℝ) with h | h
              · rcases le_total t (10727 / 16000 : ℝ) with h | h
                · exact polyLin_leaf5 (by linarith) (by linarith) (by linarith) (by linarith)
                · exact polyLin_leaf6 (by linarith) (by linarith) (by linarith) (by linarith)
              · rcases le_total t (10727 / 16000 : ℝ) with h | h
                · exact polyLin_leaf7 (by linarith) (by linarith) (by linarith) (by linarith)
                · exact polyLin_leaf8 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact polyLin_leaf9 (by linarith) (by linarith) (by linarith) (by linarith)
    · exact polyLin_leaf10 (by linarith) (by linarith) (by linarith) (by linarith)
  · rcases le_total t (1469 / 2000 : ℝ) with h | h
    · rcases le_total s (261 / 400 : ℝ) with h | h
      · rcases le_total t (2733 / 4000 : ℝ) with h | h
        · rcases le_total s (499 / 800 : ℝ) with h | h
          · rcases le_total t (5261 / 8000 : ℝ) with h | h
            · exact polyLin_leaf11 (by linarith) (by linarith) (by linarith) (by linarith)
            · rcases le_total s (39 / 64 : ℝ) with h | h
              · rcases le_total t (10727 / 16000 : ℝ) with h | h
                · exact polyLin_leaf12 (by linarith) (by linarith) (by linarith) (by linarith)
                · exact polyLin_leaf13 (by linarith) (by linarith) (by linarith) (by linarith)
              · exact polyLin_leaf14 (by linarith) (by linarith) (by linarith) (by linarith)
          · exact polyLin_leaf15 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact polyLin_leaf16 (by linarith) (by linarith) (by linarith) (by linarith)
      · rcases le_total t (2733 / 4000 : ℝ) with h | h
        · exact polyLin_leaf17 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact polyLin_leaf18 (by linarith) (by linarith) (by linarith) (by linarith)
    · exact polyLin_leaf19 (by linarith) (by linarith) (by linarith) (by linarith)

/-- `6 s² t² (B_d(t², s²) - 1)` with `√70` replaced by `8.3666`, where `f(x) = 1/2`. -/
noncomputable def polyHalf (s t : ℝ) : ℝ :=
  (t ^ 2 - (4621 / 20000 : ℝ)) * t ^ 2 * (2 * (83666 / 10000 : ℝ) * s - 1 - 10 * s ^ 2) +
    (s ^ 2 - (4621 / 20000 : ℝ)) * s ^ 2 * (2 * (83666 / 10000 : ℝ) * t - 1 - 10 * t ^ 2) - 6 * s ^ 2 * t ^ 2 +
    3 * s ^ 2 * (1 - t ^ 2 - s ^ 2)

theorem polyHalf_leaf0 {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (1113 / 2000 : ℝ)) (h3 : (12 / 25 : ℝ) ≤ t) (h4 : t ≤ (1113 / 2000 : ℝ)) :
    0 ≤ polyHalf s t := by
  have u1 : 0 ≤ s - (12 / 25 : ℝ) := by linarith
  have u2 : 0 ≤ (1113 / 2000 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (12 / 25 : ℝ) := by linarith
  have v2 : 0 ≤ (1113 / 2000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyHalf
  linear_combination (1501126218219520000000000 / 33364831591822329 : ℝ) * k0_0 +
    (3939631661252608000000000 / 33364831591822329 : ℝ) * k0_1 +
    (1124451840537804800000000 / 11121610530607443 : ℝ) * k0_2 +
    (1047920065941176320000000 / 33364831591822329 : ℝ) * k0_3 +
    (117675890339989504000000 / 33364831591822329 : ℝ) * k0_4 +
    (7318733357252608000000000 / 33364831591822329 : ℝ) * k1_0 +
    (20158516734545920000000000 / 33364831591822329 : ℝ) * k1_1 +
    (6258164730932301440000000 / 11121610530607443 : ℝ) * k1_2 +
    (6824110387727501056000000 / 33364831591822329 : ℝ) * k1_3 +
    (908354789110480643200000 / 33364831591822329 : ℝ) * k1_4 +
    (4439897702937804800000000 / 11121610530607443 : ℝ) * k2_0 +
    (12761744788532301440000000 / 11121610530607443 : ℝ) * k2_1 +
    (4241452156620983680000000 / 3707203510202481 : ℝ) * k2_2 +
    (5167132932546071936000000 / 11121610530607443 : ℝ) * k2_3 +
    (774347955215085195200000 / 11121610530607443 : ℝ) * k2_4 +
    (10729939455381176320000000 / 33364831591822329 : ℝ) * k3_0 +
    (32035781161487501056000000 / 33364831591822329 : ℝ) * k3_1 +
    (11269388261826071936000000 / 11121610530607443 : ℝ) * k3_2 +
    (14928305392107068416000000 / 33364831591822329 : ℝ) * k3_3 +
    (2445886715616825913600000 / 33364831591822329 : ℝ) * k3_4 +
    (3229536821747989504000000 / 33364831591822329 : ℝ) * k4_0 +
    (9976696818742480643200000 / 33364831591822329 : ℝ) * k4_1 +
    (3682623955631085195200000 / 11121610530607443 : ℝ) * k4_2 +
    (5211311051808825913600000 / 33364831591822329 : ℝ) * k4_3 +
    (915679677886739382400000 / 33364831591822329 : ℝ) * k4_4

theorem polyHalf_leaf1 {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (2073 / 4000 : ℝ)) (h3 : (1113 / 2000 : ℝ) ≤ t) (h4 : t ≤ (2379 / 4000 : ℝ)) :
    0 ≤ polyHalf s t := by
  have u1 : 0 ≤ s - (12 / 25 : ℝ) := by linarith
  have u2 : 0 ≤ (2073 / 4000 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (1113 / 2000 : ℝ) := by linarith
  have v2 : 0 ≤ (2379 / 4000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((2379 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((2379 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((2379 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((2379 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((2379 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((2379 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((2379 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((2379 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((2379 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((2379 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((2379 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((2379 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((2379 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((2379 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((2379 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((2379 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((2379 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((2379 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((2379 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((2379 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((2379 / 4000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((2379 / 4000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((2379 / 4000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((2379 / 4000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((2379 / 4000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyHalf
  linear_combination (30125027927037313024000000 / 33364831591822329 : ℝ) * k0_0 +
    (46616399121753309184000000 / 33364831591822329 : ℝ) * k0_1 +
    (6326890805381562368000000 / 11121610530607443 : ℝ) * k0_2 +
    (22900987031519494144000000 / 33364831591822329 : ℝ) * k0_3 +
    (20485380257757036544000000 / 33364831591822329 : ℝ) * k0_4 +
    (176519468860216148377600000 / 33364831591822329 : ℝ) * k1_0 +
    (354106211465795684761600000 / 33364831591822329 : ℝ) * k1_1 +
    (81012814306393519923200000 / 11121610530607443 : ℝ) * k1_2 +
    (147238536903437178265600000 / 33364831591822329 : ℝ) * k1_3 +
    (82085867220261196825600000 / 33364831591822329 : ℝ) * k1_4 +
    (122755489600354870169600000 / 11121610530607443 : ℝ) * k2_0 +
    (285746267133139600793600000 / 11121610530607443 : ℝ) * k2_1 +
    (80196026596174800947200000 / 3707203510202481 : ℝ) * k2_2 +
    (123779847057004150937600000 / 11121610530607443 : ℝ) * k2_3 +
    (46334110520393753657600000 / 11121610530607443 : ℝ) * k2_4 +
    (329207756019159584972800000 / 33364831591822329 : ℝ) * k3_0 +
    (845724705485666174156800000 / 33364831591822329 : ℝ) * k3_1 +
    (267075378194281909145600000 / 11121610530607443 : ℝ) * k3_2 +
    (399980041013626897100800000 / 33364831591822329 : ℝ) * k3_3 +
    (115577936111453216012800000 / 33364831591822329 : ℝ) * k3_4 +
    (107370255017588656460800000 / 33364831591822329 : ℝ) * k4_0 +
    (296117164543749638656000000 / 33364831591822329 : ℝ) * k4_1 +
    (101245540271636361555200000 / 11121610530607443 : ℝ) * k4_2 +
    (153125723028613227251200000 / 33364831591822329 : ℝ) * k4_3 +
    (38213730979401565734400000 / 33364831591822329 : ℝ) * k4_4

theorem polyHalf_leaf2 {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (2073 / 4000 : ℝ)) (h3 : (2379 / 4000 : ℝ) ≤ t) (h4 : t ≤ (633 / 1000 : ℝ)) :
    0 ≤ polyHalf s t := by
  have u1 : 0 ≤ s - (12 / 25 : ℝ) := by linarith
  have u2 : 0 ≤ (2073 / 4000 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (2379 / 4000 : ℝ) := by linarith
  have v2 : 0 ≤ (633 / 1000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (2379 / 4000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (2379 / 4000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (2379 / 4000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (2379 / 4000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 0 * ((2073 / 4000 : ℝ) - s) ^ 4 * (t - (2379 / 4000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (2379 / 4000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (2379 / 4000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (2379 / 4000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (2379 / 4000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 1 * ((2073 / 4000 : ℝ) - s) ^ 3 * (t - (2379 / 4000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (2379 / 4000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (2379 / 4000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (2379 / 4000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (2379 / 4000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 2 * ((2073 / 4000 : ℝ) - s) ^ 2 * (t - (2379 / 4000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (2379 / 4000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (2379 / 4000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (2379 / 4000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (2379 / 4000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 3 * ((2073 / 4000 : ℝ) - s) ^ 1 * (t - (2379 / 4000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (2379 / 4000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (2379 / 4000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (2379 / 4000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (2379 / 4000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (12 / 25 : ℝ)) ^ 4 * ((2073 / 4000 : ℝ) - s) ^ 0 * (t - (2379 / 4000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyHalf
  linear_combination (20485380257757036544000000 / 33364831591822329 : ℝ) * k0_0 +
    (140982055030536798208000000 / 33364831591822329 : ℝ) * k0_1 +
    (124407958804398866432000000 / 11121610530607443 : ℝ) * k0_2 +
    (410026614412816678912000000 / 33364831591822329 : ℝ) * k0_3 +
    (157373107220066074624000000 / 33364831591822329 : ℝ) * k0_4 +
    (82085867220261196825600000 / 33364831591822329 : ℝ) * k1_0 +
    (509448400858652396339200000 / 33364831591822329 : ℝ) * k1_1 +
    (443222678261608737996800000 / 11121610530607443 : ℝ) * k1_2 +
    (1477932868418038713548800000 / 33364831591822329 : ℝ) * k1_3 +
    (575926397902028741017600000 / 33364831591822329 : ℝ) * k1_4 +
    (46334110520393753657600000 / 11121610530607443 : ℝ) * k2_0 +
    (246893037106145878323200000 / 11121610530607443 : ℝ) * k2_1 +
    (203309216645316528332800000 / 3707203510202481 : ℝ) * k2_2 +
    (673939423989508316364800000 / 11121610530607443 : ℝ) * k2_3 +
    (264722266358440130969600000 / 11121610530607443 : ℝ) * k2_4 +
    (115577936111453216012800000 / 33364831591822329 : ℝ) * k3_0 +
    (524643447877998831001600000 / 33364831591822329 : ℝ) * k3_1 +
    (391738785058653843046400000 / 11121610530607443 : ℝ) * k3_2 +
    (1257913296248696882790400000 / 33364831591822329 : ℝ) * k3_3 +
    (492069533053446425804800000 / 33364831591822329 : ℝ) * k3_4 +
    (38213730979401565734400000 / 33364831591822329 : ℝ) * k4_0 +
    (152584124806599298624000000 / 33364831591822329 : ℝ) * k4_1 +
    (100703942049622432928000000 / 11121610530607443 : ℝ) * k4_2 +
    (304160033713378076492800000 / 33364831591822329 : ℝ) * k4_3 +
    (116496320631244951552000000 / 33364831591822329 : ℝ) * k4_4

theorem polyHalf_leaf3 {s t : ℝ} (h1 : (2073 / 4000 : ℝ) ≤ s) (h2 : s ≤ (1113 / 2000 : ℝ)) (h3 : (1113 / 2000 : ℝ) ≤ t) (h4 : t ≤ (633 / 1000 : ℝ)) :
    0 ≤ polyHalf s t := by
  have u1 : 0 ≤ s - (2073 / 4000 : ℝ) := by linarith
  have u2 : 0 ≤ (1113 / 2000 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (1113 / 2000 : ℝ) := by linarith
  have v2 : 0 ≤ (633 / 1000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 0 * ((1113 / 2000 : ℝ) - s) ^ 4 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 1 * ((1113 / 2000 : ℝ) - s) ^ 3 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 2 * ((1113 / 2000 : ℝ) - s) ^ 2 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 3 * ((1113 / 2000 : ℝ) - s) ^ 1 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (2073 / 4000 : ℝ)) ^ 4 * ((1113 / 2000 : ℝ) - s) ^ 0 * (t - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyHalf
  linear_combination (6710640938599291028800000 / 33364831591822329 : ℝ) * k0_0 +
    (10172081813571540716800000 / 33364831591822329 : ℝ) * k0_1 +
    (1718021377138967614400000 / 11121610530607443 : ℝ) * k0_2 +
    (8895924056361021673600000 / 33364831591822329 : ℝ) * k0_3 +
    (7281020039452809472000000 / 33364831591822329 : ℝ) * k0_4 +
    (33109642757596854169600000 / 33364831591822329 : ℝ) * k1_0 +
    (57963005327653950208000000 / 33364831591822329 : ℝ) * k1_1 +
    (11539945151854587276800000 / 11121610530607443 : ℝ) * k1_2 +
    (36945613683162669491200000 / 33364831591822329 : ℝ) * k1_3 +
    (27493814499782074163200000 / 33364831591822329 : ℝ) * k1_4 +
    (20206376106421559494400000 / 11121610530607443 : ℝ) * k2_0 +
    (39578767138289307238400000 / 11121610530607443 : ℝ) * k2_1 +
    (9010878744043042547200000 / 3707203510202481 : ℝ) * k2_2 +
    (20785696324515672396800000 / 11121610530607443 : ℝ) * k2_3 +
    (13284610331344180736000000 / 11121610530607443 : ℝ) * k2_4 +
    (48868843417310267545600000 / 33364831591822329 : ℝ) * k3_0 +
    (104762350543743163801600000 / 33364831591822329 : ℝ) * k3_1 +
    (26573026423807488972800000 / 11121610530607443 : ℝ) * k3_2 +
    (49990552423041074483200000 / 33364831591822329 : ℝ) * k3_3 +
    (26486791372358385664000000 / 33364831591822329 : ℝ) * k3_4 +
    (14650874846187830118400000 / 33364831591822329 : ℝ) * k4_0 +
    (33826021940561426329600000 / 33364831591822329 : ℝ) * k4_1 +
    (9367028401717574835200000 / 11121610530607443 : ℝ) * k4_2 +
    (15692923512004655564800000 / 33364831591822329 : ℝ) * k4_3 +
    (6848273336852373913600000 / 33364831591822329 : ℝ) * k4_4

theorem polyHalf_leaf4 {s t : ℝ} (h1 : (1113 / 2000 : ℝ) ≤ s) (h2 : s ≤ (633 / 1000 : ℝ)) (h3 : (12 / 25 : ℝ) ≤ t) (h4 : t ≤ (633 / 1000 : ℝ)) :
    0 ≤ polyHalf s t := by
  have u1 : 0 ≤ s - (1113 / 2000 : ℝ) := by linarith
  have u2 : 0 ≤ (633 / 1000 : ℝ) - s := by linarith
  have v1 : 0 ≤ t - (12 / 25 : ℝ) := by linarith
  have v2 : 0 ≤ (633 / 1000 : ℝ) - t := by linarith
  have k0_0 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_1 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_2 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_3 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k0_4 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - s) ^ 4 * (t - (12 / 25 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_0 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_1 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_2 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_3 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k1_4 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - s) ^ 3 * (t - (12 / 25 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_0 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_1 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_2 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_3 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k2_4 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - s) ^ 2 * (t - (12 / 25 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_0 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_1 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_2 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_3 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k3_4 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - s) ^ 1 * (t - (12 / 25 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_0 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 0 * ((633 / 1000 : ℝ) - t) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_1 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 1 * ((633 / 1000 : ℝ) - t) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_2 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 2 * ((633 / 1000 : ℝ) - t) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_3 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 3 * ((633 / 1000 : ℝ) - t) ^ 1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  have k4_4 : 0 ≤ (s - (1113 / 2000 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - s) ^ 0 * (t - (12 / 25 : ℝ)) ^ 4 * ((633 / 1000 : ℝ) - t) ^ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))
      (pow_nonneg v2 _)
  unfold polyHalf
  linear_combination (201846051359249344000000 / 33364831591822329 : ℝ) * k0_0 +
    (439702896905812704400000 / 33364831591822329 : ℝ) * k0_1 +
    (77260989283459906400000 / 11121610530607443 : ℝ) * k0_2 +
    (15596694049218029200000 / 33364831591822329 : ℝ) * k0_3 +
    (26751067722079585600000 / 33364831591822329 : ℝ) * k0_4 +
    (944147194912671232000000 / 33364831591822329 : ℝ) * k1_0 +
    (2195635393905858083200000 / 33364831591822329 : ℝ) * k1_1 +
    (463971062074451859200000 / 11121610530607443 : ℝ) * k1_2 +
    (233770177366799113600000 / 33364831591822329 : ℝ) * k1_3 +
    (114084755068405139200000 / 33364831591822329 : ℝ) * k1_4 +
    (551019585384960512000000 / 11121610530607443 : ℝ) * k2_0 +
    (1358891285397301011200000 / 11121610530607443 : ℝ) * k2_1 +
    (329986363337158307200000 / 3707203510202481 : ℝ) * k2_2 +
    (239834903646576281600000 / 11121610530607443 : ℝ) * k2_3 +
    (68307082635035700800000 / 11121610530607443 : ℝ) * k2_4 +
    (1284121494335162368000000 / 33364831591822329 : ℝ) * k3_0 +
    (3339432146378233676800000 / 33364831591822329 : ℝ) * k3_1 +
    (904967011651783020800000 / 11121610530607443 : ℝ) * k3_2 +
    (817302391325436582400000 / 33364831591822329 : ℝ) * k3_3 +
    (179172711450109283200000 / 33364831591822329 : ℝ) * k3_4 +
    (373469090242898944000000 / 33364831591822329 : ℝ) * k4_0 +
    (1019178071844412614400000 / 33364831591822329 : ℝ) * k4_1 +
    (301990111073237926400000 / 11121610530607443 : ℝ) * k4_2 +
    (316562843617591187200000 / 33364831591822329 : ℝ) * k4_3 +
    (61742557028656844800000 / 33364831591822329 : ℝ) * k4_4

theorem polyHalf_nonneg {s t : ℝ} (h1 : (12 / 25 : ℝ) ≤ s) (h2 : s ≤ (633 / 1000 : ℝ)) (h3 : (12 / 25 : ℝ) ≤ t) (h4 : t ≤ (633 / 1000 : ℝ)) :
    0 ≤ polyHalf s t := by
  rcases le_total s (1113 / 2000 : ℝ) with h | h
  · rcases le_total t (1113 / 2000 : ℝ) with h | h
    · exact polyHalf_leaf0 (by linarith) (by linarith) (by linarith) (by linarith)
    · rcases le_total s (2073 / 4000 : ℝ) with h | h
      · rcases le_total t (2379 / 4000 : ℝ) with h | h
        · exact polyHalf_leaf1 (by linarith) (by linarith) (by linarith) (by linarith)
        · exact polyHalf_leaf2 (by linarith) (by linarith) (by linarith) (by linarith)
      · exact polyHalf_leaf3 (by linarith) (by linarith) (by linarith) (by linarith)
  · exact polyHalf_leaf4 (by linarith) (by linarith) (by linarith) (by linarith)

end ABLP
