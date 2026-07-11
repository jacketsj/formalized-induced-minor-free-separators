/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.PaddedDecompDefs
import Padding.PaddedDecomp.Bartal
import Padding.PaddedDecomp.BartalHelpers
import Padding.PaddedDecomp.BartalProb
import Padding.PaddedDecomp.HasPaddedModulus

/-! # Padded Decompositions — Main Results

This file re-exports the main theorems about padded decompositions of finite metric spaces.

For the definitions needed to *state* these results, see
`Statements/PaddedDecompDef.lean`.  Auxiliary lemmas live in `PaddedDecompDefs.lean`, and
the proofs live in the `PaddedDecomp/` implementation folder.

## Main Results

* `PaddedDecomposition.bartal_padded_decomposition_strong`: **Bartal's theorem** in its
  faithful `(O(log n), Ω(1))` form — every finite metric space on `n` points admits an
  `(8 · log n, 1/4)`-padded decomposition scheme.  Here the padding parameter `δ₀ = 1/4`
  is a **universal constant**, independent of the number of points `n` (this is the `Ω(1)`
  guarantee).  It is proved by the genuine probabilistic greedy ball-carving construction:
  a uniformly random radius `R ∈ [Δ/4, Δ/2]` together with a uniformly random ordering of
  the points, analysed via Jensen's inequality on the ball-growth function.
* `PaddedDecomposition.bartal_padded_decomposition`: a weaker existential form
  `∃ C δ₀ > 0, AdmitsPaddedDecompScheme X (C · log n) δ₀`, witnessed here by a simpler
  deterministic connected-component construction (with a non-universal `δ₀`).  The strong
  form above is the one capturing Bartal's `Ω(1)` padding guarantee.
* `PaddedDecomposition.has_padded_modulus_linear`: Every finite metric space on `n ≥ 2` points
  has padded modulus at most `2(n − 1)`.
* `PaddedDecomposition.bartal_has_padded_modulus`: Every finite metric space on `n` points
  has padded modulus at most `16 · ln(n)`.
-/
