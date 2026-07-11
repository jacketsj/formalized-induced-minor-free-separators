/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.EmbeddingDefs
import Padding.Embedding.Core

/-! # Non-expansive Metric Embeddings — Main Results

This file re-exports the main theorem about non-expansive embeddings of finite metric
spaces into the real line with bounded average distortion.

For the definitions needed to *state* this result (`IsNonExpansive`, `pairDistSum`,
`embeddingSum`), see `Statements/EmbeddingDef.lean`.  Auxiliary lemmas and `avgDistortion`
live in `EmbeddingDefs.lean`.  For the proof implementation, see `Embedding/Core.lean`.

## Main Results

* `nonexpansive_avg_distortion_embedding`: Every n-point metric space admits a
  1-Lipschitz embedding f : X → ℝ with average distortion O(log n).
  Precisely: `pairDistSum X ≤ 1280 · log(n) · embeddingSum f`.

* `nonexpansive_avg_distortion_embedding'`: Same result stated using the
  `IsNonExpansive`, `pairDistSum`, and `embeddingSum` API.
-/

open PaddedDecomposition MeasureTheory Metric Set Real Finset BigOperators

noncomputable section

/-- **Average Distortion Embedding** (API version): Every n-point metric space admits a
non-expansive embedding into ℝ with average distortion O(log n).

Precisely, there exists `f : X → ℝ` with `IsNonExpansive f` such that
`pairDistSum X ≤ 1280 · log(n) · embeddingSum f`. -/
theorem nonexpansive_avg_distortion_embedding'
    (X : Type*) [MetricSpace X] [Fintype X] :
    ∃ (f : X → ℝ), IsNonExpansive f ∧
      pairDistSum X ≤ 1280 * Real.log (Fintype.card X) * embeddingSum f := by
  obtain ⟨f, hf_lip, hf_bound⟩ := PaddedDecomposition.nonexpansive_avg_distortion_embedding X
  exact ⟨f, hf_lip.isNonExpansive, hf_bound⟩

end
