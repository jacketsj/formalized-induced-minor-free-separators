/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Sparse Covers of Metric Spaces

This file defines sparse covers and sparse partition covers for general metric spaces,
following the definition from Filtser et al.

## Main Definitions

* `SparseCover`: A `(β, s, Δ)`-sparse cover of a metric space — a collection of clusters
  with bounded diameter, padding, and bounded overlap.
* `SparsePartitionCover`: A `(β, s, Δ)`-sparse partition cover — a sparse cover whose
  clusters can be partitioned into `s` partitions.
* `AdmitsSparseCoverScheme`: A metric space admits a `(β, s)`-sparse cover scheme.
* `AdmitsSPCS`: A metric space admits a `(β, s)`-sparse partition cover scheme.

## References

* A. Filtser, "Scattering and sparse partitions, and their applications", 2024.
-/

open Metric Set Finset Classical

noncomputable section

/-! ## Sparse Covers -/

/-- A `(β, s, Δ)`-sparse cover of a pseudo-metric space `X`.

A collection of clusters `{C₁, ..., Cₜ}` such that:
1. **Bounded diameter**: Every cluster has diameter at most `Δ`.
2. **Padding**: For each `v ∈ X`, there exists a cluster `Cᵢ` containing `B(v, Δ/β)`.
3. **Sparsity**: Each `v ∈ X` is contained in at most `s` clusters.
-/
structure SparseCover (X : Type u) [PseudoMetricSpace X] (β : ℝ) (s : ℕ) (Δ : ℝ) where
  /-- The index type for the clusters. -/
  ι : Type u
  /-- The index type is finite. -/
  [finι : Fintype ι]
  /-- The clusters. -/
  cluster : ι → Set X
  /-- Every cluster has diameter at most `Δ`. -/
  diam_le : ∀ i : ι, Metric.diam (cluster i) ≤ Δ
  /-- For each point, some cluster contains the ball `B(v, Δ/β)`. -/
  padding : ∀ v : X, ∃ i : ι, Metric.closedBall v (Δ / β) ⊆ cluster i
  /-- Each point is in at most `s` clusters. -/
  sparse : ∀ v : X, (Finset.univ.filter (fun i => v ∈ cluster i)).card ≤ s

attribute [instance] SparseCover.finι

/-- A `(β, s, Δ)`-sparse partition cover: a family of `s` partitions
`P₁, ..., Pₛ` such that their union forms a `(β, s, Δ)`-sparse cover.

Each partition consists of disjoint clusters covering `X`, and for each point
there exists some partition where the padded ball is entirely in one cluster. -/
structure SparsePartitionCover (X : Type u) [PseudoMetricSpace X]
    (β : ℝ) (s : ℕ) (Δ : ℝ) where
  /-- The index type for clusters within each partition. -/
  ι : Type u
  /-- The index type is finite. -/
  [finι : Fintype ι]
  /-- The `s` partitions, each indexed by `ι`. -/
  partition : Fin s → ι → Set X
  /-- Clusters in each partition are pairwise disjoint. -/
  disjoint : ∀ j : Fin s, ∀ i₁ i₂ : ι, i₁ ≠ i₂ →
    Disjoint (partition j i₁) (partition j i₂)
  /-- Each partition covers all of `X`. -/
  covers : ∀ j : Fin s, ∀ v : X, ∃ i : ι, v ∈ partition j i
  /-- Every cluster has diameter at most `Δ`. -/
  diam_le : ∀ j : Fin s, ∀ i : ι, Metric.diam (partition j i) ≤ Δ
  /-- For each point, some cluster (in some partition) contains `B(v, Δ/β)`. -/
  padding : ∀ v : X, ∃ j : Fin s, ∃ i : ι,
    Metric.closedBall v (Δ / β) ⊆ partition j i

attribute [instance] SparsePartitionCover.finι

/-- A metric space **admits a `(β, s)`-sparse cover scheme** if for every `Δ > 0`,
there exists a `(β, s, Δ)`-sparse cover. -/
def AdmitsSparseCoverScheme (X : Type u) [PseudoMetricSpace X]
    (β : ℝ) (s : ℕ) : Prop :=
  ∀ Δ : ℝ, 0 < Δ → Nonempty (SparseCover.{u} X β s Δ)

/-- A metric space **admits a `(β, s)`-sparse partition cover scheme** (SPCS) if for
every `Δ > 0`, there exists a `(β, s, Δ)`-sparse partition cover. -/
def AdmitsSPCS (X : Type u) [PseudoMetricSpace X]
    (β : ℝ) (s : ℕ) : Prop :=
  ∀ Δ : ℝ, 0 < Δ → Nonempty (SparsePartitionCover.{u} X β s Δ)

end
