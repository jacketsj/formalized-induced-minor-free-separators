/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection

/-! # t-Models and μ-Models

Definitions of `TModel` and `MuModel` used in the asymptotic dimension proof.
-/

open SimpleGraph Set

/-- A `t`-model in a graph `H`: `t` connected subsets of `V(H)` that are pairwise
disjoint and pairwise adjacent. -/
structure TModel {V : Type*} (H : SimpleGraph V) (t : ℕ) where
  /-- The `t` subsets (bags). -/
  bag : Fin t → Set V
  /-- Each bag is nonempty. -/
  nonempty : ∀ i, (bag i).Nonempty
  /-- Each bag is connected. -/
  connected : ∀ i, ∀ a b : V, a ∈ bag i → b ∈ bag i →
    ∃ (w : H.Walk a b), ∀ x ∈ w.support, x ∈ bag i
  /-- Bags are pairwise disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (bag i) (bag j)
  /-- Bags are pairwise adjacent. -/
  adjacent : ∀ i j, i ≠ j → ∃ a ∈ bag i, ∃ b ∈ bag j, H.Adj a b

/-- A `(μ, S, γ, t)`-model: a `t`-model in `H` where each bag `Tⱼ` contains the
image under `μ` of the closed `γ`-neighborhood of some point `xⱼ ∈ S`. -/
structure MuModel {V₁ V₂ : Type*} {G : SimpleGraph V₁} {H : SimpleGraph V₂}
    (μ : RegionIntersectionModel G H)
    (S : Set V₁) (γ : ℕ) (t : ℕ) extends TModel H t where
  /-- The center points in `S`. -/
  center : Fin t → V₁
  /-- Each center is in `S`. -/
  center_mem : ∀ j, center j ∈ S
  /-- The image of the γ-neighborhood is contained in the bag.
  We require reachability to correctly exclude disconnected vertices
  (since `SimpleGraph.dist` maps unreachable pairs to 0). -/
  neighborhood_contained : ∀ j, ∀ v : V₁, G.Reachable (center j) v →
    G.dist (center j) v ≤ γ → μ.region v ⊆ bag j
