/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.EmbeddingDef

/-! # Non-expansive Metric Embeddings — Auxiliary Lemmas

The definitions needed to **state** Rabinovich's average-distortion embedding theorem live
in `Padding/Statements/EmbeddingDef.lean`.  This file collects the auxiliary lemmas
about those notions together with the convenience definition `avgDistortion`.  None of its
contents are needed to read the statement of the headline theorem.

## Contents

* `avgDistortion`: the average distortion `pairDistSum X / embeddingSum f` of an embedding.
* Basic API lemmas relating `IsNonExpansive` to `LipschitzWith 1`, and elementary facts
  about `pairDistSum` and `embeddingSum`.
-/

open Finset BigOperators

/-- The average distortion of a non-expansive embedding `f`. -/
noncomputable def avgDistortion {X : Type*} [Fintype X] [PseudoMetricSpace X]
    (f : X → ℝ) : ℝ :=
  pairDistSum X / embeddingSum f

/-! ## Basic Properties -/

/-- Non-expansive functions are 1-Lipschitz. -/
lemma IsNonExpansive.lipschitzWith {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} (hf : IsNonExpansive f) : LipschitzWith 1 f := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [Real.dist_eq]
  exact hf x y

/-- 1-Lipschitz functions are non-expansive. -/
lemma LipschitzWith.isNonExpansive {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} (hf : LipschitzWith 1 f) : IsNonExpansive f := by
  intro x y
  have := hf.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at this
  rwa [Real.dist_eq] at this

/-- `IsNonExpansive` is equivalent to `LipschitzWith 1`. -/
lemma isNonExpansive_iff_lipschitzWith {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) : IsNonExpansive f ↔ LipschitzWith 1 f :=
  ⟨IsNonExpansive.lipschitzWith, LipschitzWith.isNonExpansive⟩

/-- `pairDistSum` equals the double sum of distances. -/
lemma pairDistSum_eq {X : Type*} [Fintype X] [PseudoMetricSpace X] :
    pairDistSum X = ∑ x : X, ∑ y : X, dist x y := rfl

/-- `embeddingSum` equals the double sum of absolute differences. -/
lemma embeddingSum_eq {X : Type*} [Fintype X] (f : X → ℝ) :
    embeddingSum f = ∑ x : X, ∑ y : X, |f x - f y| := rfl

/-- Average distortion ≤ C means `pairDistSum ≤ C * embeddingSum`. -/
lemma avgDistortion_le_iff {X : Type*} [Fintype X] [PseudoMetricSpace X]
    {f : X → ℝ} {C : ℝ} (hf : 0 < embeddingSum f) :
    avgDistortion f ≤ C ↔ pairDistSum X ≤ C * embeddingSum f := by
  rw [avgDistortion, div_le_iff₀ hf]

/-- `pairDistSum` is non-negative. -/
lemma pairDistSum_nonneg (X : Type*) [Fintype X] [PseudoMetricSpace X] :
    0 ≤ pairDistSum X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

/-- `embeddingSum` is non-negative. -/
lemma embeddingSum_nonneg {X : Type*} [Fintype X] (f : X → ℝ) :
    0 ≤ embeddingSum f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
