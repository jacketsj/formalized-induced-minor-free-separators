/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Non-expansive Metric Embeddings — Statement Definitions

This file contains **only** the definitions needed to *state* Rabinovich's
average-distortion embedding theorem.  A human who wants to understand what that theorem
claims needs to read only this file.

Auxiliary lemmas about these notions, and the convenience definition `avgDistortion`, live
in `Padding/EmbeddingDefs.lean`; the proof lives in `Padding/Embedding/Core.lean`.

## Definitions

* `IsNonExpansive`: a function `f : X → ℝ` is non-expansive (1-Lipschitz).
* `pairDistSum`: the pairwise distance sum `Σ_{x,y} d(x,y)` of a finite pseudometric space.
* `embeddingSum`: the embedding sum `Σ_{x,y} |f(x) - f(y)|` of a function `f`.
-/

open Finset BigOperators

/-- A function `f : X → ℝ` is non-expansive with respect to a pseudometric space. -/
def IsNonExpansive {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) : Prop :=
  ∀ x y : X, |f x - f y| ≤ dist x y

/-- The pairwise distance sum `Σ_{x,y} d(x,y)` for a finite pseudometric space. -/
noncomputable def pairDistSum (X : Type*) [Fintype X] [PseudoMetricSpace X] : ℝ :=
  ∑ x : X, ∑ y : X, dist x y

/-- The embedding sum `Σ_{x,y} |f(x) - f(y)|` for a function `f`. -/
noncomputable def embeddingSum {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  ∑ x : X, ∑ y : X, |f x - f y|
