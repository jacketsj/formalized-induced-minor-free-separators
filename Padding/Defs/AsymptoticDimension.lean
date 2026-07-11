/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Asymptotic Dimension and (δ,ρ)-Partitions

This file defines δ-components and (δ,ρ)-partitions, which are the key concepts
for bounding the asymptotic (Assouad-Nagata) dimension of metric spaces and graphs.

## Main Definitions

* `DeltaRhoPartition`: A (δ,ρ)-partition of a set `S` in a graph `G`.
* `HasLinearAsymptoticDimension`: A graph has Assouad-Nagata dimension at most `d`
  with linear control constant `c`.

## References

* Bonamy, Bousquet, Esperet, Groenland, Pirot, Scott,
  "Asymptotic dimension of minor-closed families and Assouad-Nagata dimension
  of surfaces", 2024.
-/

open SimpleGraph Metric Set

/-! ## (δ,ρ)-Partitions

A `(δ, ρ)`-partition of a set `S ⊆ V(G)` is a partition of `S` such that
every `δ`-component of each part has radius at most `ρ`.

A `δ`-component of `U ⊆ V(G)` in `G` is an inclusion-minimal nonempty
`C ⊆ U` such that `d(u, v) > δ` for all `u ∈ C, v ∈ U \ C`.
Equivalently, it is the set of vertices reachable from a given vertex
via chains of vertices in `U` with consecutive distance ≤ `δ`. -/

/-- A `(δ, ρ)`-partition of a set `S ⊆ V(G)` in graph `G` with `k` parts.

This consists of a labeling function assigning each vertex of `S` to one of `k` parts,
such that any two points `u, v` in the same part that are connected by a chain of
steps within the part with each step having graph distance ≤ `δ` must satisfy
`G.dist u v ≤ ρ`.

This captures the condition that every `δ`-component of each part has radius ≤ `ρ`. -/
structure DeltaRhoPartition {V : Type*} (G : SimpleGraph V)
    (δ ρ : ℕ) (S : Set V) (k : ℕ) where
  /-- The labeling function assigning each point of `S` to a part in `Fin k`. -/
  label : V → Fin k
  /-- Every δ-component of each part has radius at most ρ:
      if `u, v ∈ S` have the same label and are connected by a chain of
      vertices in `S` with the same label and consecutive distance ≤ δ,
      then `G.dist u v ≤ ρ`. -/
  component_radius : ∀ (u v : V), u ∈ S → v ∈ S → label u = label v →
    (Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ label a = label u ∧
      label b = label u ∧ G.dist a b ≤ δ) u v) →
    G.dist u v ≤ ρ

/-- A graph `G` has **(Assouad-Nagata) asymptotic dimension at most `d` with
linear control constant `c`** if for every `δ ≥ 1`, `V(G)` has a
`(δ, c · δ)`-partition of size at most `d + 1`.

This is the "linear" form of Assouad-Nagata dimension. -/
def HasLinearAsymptoticDimension {V : Type*} (G : SimpleGraph V)
    (d : ℕ) (c : ℕ) : Prop :=
  ∀ δ : ℕ, 1 ≤ δ →
    Nonempty (DeltaRhoPartition G δ (c * δ) Set.univ (d + 1))
