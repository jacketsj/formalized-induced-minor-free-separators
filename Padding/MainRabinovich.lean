/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.EmbeddingDef
import Padding.Embedding

/-! # Main Result 2 — Rabinovich's average-distortion embedding (independent entry point)

This file states **Rabinovich's average-distortion embedding theorem** in isolation.

## How to verify this result by hand

To convince yourself of what is proved, you only need to read:

1. **The statement** below (the theorem `MainResults.rabinovich_embedding`); and
2. **The definitions it uses**, all of which live in the single file
   `Padding/Statements/EmbeddingDef.lean`
   (`IsNonExpansive`, `pairDistSum`, `embeddingSum`).

You do **not** need to read the proof or any implementation file: the import of
`Padding.Embedding` only supplies the proof term, and the compiler checks that it has
the stated type.  Everything in that implementation chain is built on top of the very same
definitions from `Statements/EmbeddingDef.lean`, so there is no hidden re-definition.
-/

namespace MainResults

/-- **Rabinovich's average-distortion embedding.** Every finite metric space admits a
non-expansive (`1`-Lipschitz) embedding `f : X → ℝ` with average distortion `O(log n)`:
precisely `pairDistSum X ≤ 1280 · log(n) · embeddingSum f`.

See `nonexpansive_avg_distortion_embedding'`. -/
theorem rabinovich_embedding (X : Type*) [MetricSpace X] [Fintype X] :
    ∃ (f : X → ℝ), IsNonExpansive f ∧
      pairDistSum X ≤ 1280 * Real.log (Fintype.card X) * embeddingSum f :=
  nonexpansive_avg_distortion_embedding' X

end MainResults
