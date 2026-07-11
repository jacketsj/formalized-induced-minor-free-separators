/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.PaddedDecompDef
import Padding.PaddedDecomp

/-! # Main Result 1 — Bartal's theorem (independent entry point)

This file states **Bartal's theorem** in isolation.

## How to verify this result by hand

To convince yourself of what is proved, you only need to read:

1. **The statement** below (the theorem `MainResults.bartal`); and
2. **The definitions it uses**, all of which live in the single file
   `Padding/Statements/PaddedDecompDef.lean`
   (`AdmitsPaddedDecompScheme`, `PaddedDecomp`, `Partition`, `Partition.cluster`,
   `Partition.IsBounded`).

You do **not** need to read the proof or any implementation file: the import of
`Padding.PaddedDecomp` only supplies the proof term, and the compiler checks that it
has the stated type.  Everything in that implementation chain is built on top of the very
same definitions from `Statements/PaddedDecompDef.lean`, so there is no hidden re-definition.
-/

open PaddedDecomposition

namespace MainResults

/-- **Bartal's theorem.** Every finite metric space on `n` points admits an
`(8·log n, 1/4)`-padded decomposition scheme: the padding parameter `δ₀ = 1/4` is a
universal constant independent of `n`, and `β = 8·log n = O(log n)`.

See `PaddedDecomposition.bartal_padded_decomposition_strong`. -/
theorem bartal (X : Type*) [MetricSpace X] [Fintype X] :
    AdmitsPaddedDecompScheme X (8 * Real.log (Fintype.card X)) (1 / 4) :=
  bartal_padded_decomposition_strong X

end MainResults
