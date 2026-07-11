/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Statements.PaddedDecompDef
import Padding.Defs.WeightedGraph
import Padding.RegionIntersection.WeightedMetricSpace

/-! # Region Intersection Graphs — Statement Definitions

This file defines the region-intersection and minor-exclusion constants that occur in the
main padded-decomposition statement.

For statement verification, audit the declaration bodies of:

* `RegionIntersectionModel`;
* `SimpleGraph.HasCompleteMinor`;
* `SimpleGraph.ExcludesMinor`.

The imports make the main statement file convenient to use; they are not a recommendation
to audit imported proof infrastructure.

## References

* Bonamy, Bousquet, Esperet, Groenland, Pirot, Scott,
  "Asymptotic dimension of minor-closed families and Assouad-Nagata dimension
  of surfaces", 2024.
-/

open SimpleGraph Set

/-! ## Region Intersection Models -/

/-- A **region intersection model** of a graph `G` over a graph `H` is a mapping `μ`
from `V(G)` to connected subsets of `V(H)` such that `μ(u) ∩ μ(v) ≠ ∅` exactly when
`uv` is an edge of `G`.

The connectedness condition means that the induced subgraph `H[μ(v)]` is connected
for each `v`. -/
structure RegionIntersectionModel {V₁ V₂ : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂) where
  /-- The mapping from vertices of `G` to subsets of `V(H)`. -/
  region : V₁ → Set V₂
  /-- Each region is nonempty. -/
  region_nonempty : ∀ v : V₁, (region v).Nonempty
  /-- Each region is connected in `H`. -/
  region_connected : ∀ v : V₁, ∀ a b : V₂, a ∈ region v → b ∈ region v →
    ∃ (w : H.Walk a b), ∀ x ∈ w.support, x ∈ region v
  /-- Adjacent vertices have intersecting regions. -/
  adj_intersect : ∀ u v : V₁, G.Adj u v → (region u ∩ region v).Nonempty
  /-- Non-adjacent distinct vertices have disjoint regions. -/
  nonadj_disjoint : ∀ u v : V₁, u ≠ v → ¬G.Adj u v → Disjoint (region u) (region v)

/-! ## Graph Minors -/

/-- A graph `H` has `K_t` as a minor if there exist `t` pairwise disjoint connected
subsets of `V(H)` that are pairwise adjacent (i.e., for each pair, some edge connects them).

This is the standard definition: `K_t ≤_m H` iff `H` contains `t` disjoint connected
subgraphs, any two of which are joined by an edge. -/
def SimpleGraph.HasCompleteMinor {V : Type*} (H : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ (bags : Fin t → Set V),
    (∀ i : Fin t, (bags i).Nonempty) ∧
    (∀ i : Fin t, ∀ a b : V, a ∈ bags i → b ∈ bags i →
      ∃ (w : H.Walk a b), ∀ x ∈ w.support, x ∈ bags i) ∧
    (∀ i j : Fin t, i ≠ j → Disjoint (bags i) (bags j)) ∧
    (∀ i j : Fin t, i ≠ j → ∃ a ∈ bags i, ∃ b ∈ bags j, H.Adj a b)

/-- A graph `H` **excludes `K_t` as a minor** if `H` does not have `K_t` as a minor. -/
def SimpleGraph.ExcludesMinor {V : Type*} (H : SimpleGraph V) (t : ℕ) : Prop :=
  ¬H.HasCompleteMinor t
