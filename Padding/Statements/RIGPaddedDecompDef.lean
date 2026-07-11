/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Verifier-facing definitions for the region-intersection padded-decomposition theorem

This file is the public definition surface for
`MainResults.rig_padded_decomposition_schemes`.

It intentionally avoids proof-side metric infrastructure.  The padded-decomposition notion
below is stated directly for a distance function `d : X → X → ℝ`; in the main theorem, the
two distances are `endpointLightDist` and `endpointHeavyDist`.
-/

namespace RIGPadded

open Classical

noncomputable section

/-! ## Vertex-weighted shortest-path distances -/

/-- Endpoint-light length of a walk:
`(w u + w v) / 2` on each traversed edge, equivalently half weight on the endpoints of
the whole path and full weight on its internal vertices. -/
def endpointLightWalkLength {V : Type*} {G : SimpleGraph V} (w : V → ℝ)
    {u v : V} (p : G.Walk u v) : ℝ :=
  p.edges.map (fun e => Sym2.lift ⟨fun a b => (w a + w b) / 2, fun _ _ => by ring⟩ e)
    |>.sum

/-- The endpoint-light vertex-weighted shortest-path distance. -/
def endpointLightDist {V : Type*} (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ :=
  ⨅ (p : G.Walk u v), endpointLightWalkLength w p

/-- Endpoint-heavy length of a walk: the sum of `w` over the vertices of the walk. -/
def endpointHeavyWalkLength {V : Type*} {G : SimpleGraph V} (w : V → ℝ)
    {u v : V} (p : G.Walk u v) : ℝ :=
  (p.support.map w).sum

/-- The endpoint-heavy vertex-weighted shortest-path distance.

For equal endpoints the distance is defined to be `0`; for distinct endpoints it is the
infimum of the vertex-weight sums over walks from `u` to `v`. -/
def endpointHeavyDist {V : Type*} (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ :=
  if u = v then 0 else ⨅ (p : G.Walk u v), endpointHeavyWalkLength w p

/-! ## Partitions and explicit-distance padded decompositions -/

/-- A partition of `X`, represented by assigning a natural-number label to each point. -/
@[ext]
structure Partition (X : Type*) where
  /-- The label of a point.  Points with the same label are in the same cluster. -/
  label : X → ℕ

namespace Partition

variable {X : Type*}

instance : CoeFun (Partition X) (fun _ => X → ℕ) := ⟨Partition.label⟩

/-- The cluster containing `z`. -/
def cluster (P : Partition X) (z : X) : Set X :=
  {x : X | P x = P z}

/-- `P` is `Δ`-bounded for the distance `d` if every cluster has pairwise `d`-diameter
at most `Δ`. -/
def IsBounded (P : Partition X) (d : X → X → ℝ) (Δ : ℝ) : Prop :=
  ∀ z x y : X, x ∈ P.cluster z → y ∈ P.cluster z → d x y ≤ Δ

end Partition

/-- The closed ball for an explicit distance function. -/
def closedBall {X : Type*} (d : X → X → ℝ) (z : X) (r : ℝ) : Set X :=
  {x : X | d x z ≤ r}

universe u

/-- A `(β, δ, Δ)`-padded decomposition for an explicit distance function `d`. -/
structure PaddedDecomp (X : Type u) (d : X → X → ℝ) (β δ Δ : ℝ) where
  /-- The sample space for random partitions. -/
  Ω : Type u
  /-- The measurable-space structure on the sample space. -/
  msΩ : MeasurableSpace Ω
  /-- The probability measure on the sample space. -/
  μ : @MeasureTheory.Measure Ω msΩ
  /-- The measure is a probability measure. -/
  hμ : @MeasureTheory.IsProbabilityMeasure Ω msΩ μ
  /-- The sampled partition. -/
  partition : Ω → Partition X
  /-- Every sampled partition is `Δ`-bounded. -/
  bounded : ∀ ω, (partition ω).IsBounded d Δ
  /-- For every `0 ≤ γ ≤ δ`, the ball of radius `γ * Δ` around each point is contained
  in that point's sampled cluster with probability at least `exp (-β * γ)`. -/
  padding : ∀ γ : ℝ, 0 ≤ γ → γ ≤ δ → ∀ z : X,
    μ.toOuterMeasure {ω | closedBall d z (γ * Δ) ⊆ (partition ω).cluster z} ≥
      ENNReal.ofReal (Real.exp (-β * γ))

attribute [instance] PaddedDecomp.msΩ PaddedDecomp.hμ

/-- A distance function admits a `(β, δ)`-padded decomposition scheme if every positive
scale `Δ` has a `(β, δ, Δ)`-padded decomposition. -/
def AdmitsPaddedDecompScheme (X : Type u) (d : X → X → ℝ) (β δ : ℝ) : Prop :=
  ∀ Δ : ℝ, 0 < Δ → Nonempty (PaddedDecomp X d β δ Δ)

/-! ## Region-intersection models and complete-minor exclusion -/

/-- A region-intersection model of `G` over `H`.

Each vertex of `G` is assigned a nonempty connected region of `H`; distinct vertices of
`G` are adjacent exactly when their regions intersect. -/
structure RegionIntersectionModel {V₁ V₂ : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂) where
  /-- The region assigned to each vertex of `G`. -/
  region : V₁ → Set V₂
  /-- Each region is nonempty. -/
  region_nonempty : ∀ v : V₁, (region v).Nonempty
  /-- Each region is connected in `H`. -/
  region_connected : ∀ v : V₁, ∀ a b : V₂, a ∈ region v → b ∈ region v →
    ∃ walk : H.Walk a b, ∀ x ∈ walk.support, x ∈ region v
  /-- Adjacent vertices have intersecting regions. -/
  adj_intersect : ∀ u v : V₁, G.Adj u v → (region u ∩ region v).Nonempty
  /-- Non-adjacent distinct vertices have disjoint regions. -/
  nonadj_disjoint : ∀ u v : V₁, u ≠ v → ¬G.Adj u v → Disjoint (region u) (region v)

/-- `H` has a complete minor of size `t` if `H` contains `t` pairwise disjoint nonempty
connected bags, with an edge between every two distinct bags. -/
def HasCompleteMinor {V : Type*} (H : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ bags : Fin t → Set V,
    (∀ i : Fin t, (bags i).Nonempty) ∧
    (∀ i : Fin t, ∀ a b : V, a ∈ bags i → b ∈ bags i →
      ∃ walk : H.Walk a b, ∀ x ∈ walk.support, x ∈ bags i) ∧
    (∀ i j : Fin t, i ≠ j → Disjoint (bags i) (bags j)) ∧
    (∀ i j : Fin t, i ≠ j → ∃ a ∈ bags i, ∃ b ∈ bags j, H.Adj a b)

/-- `H` excludes the complete minor of size `t`. -/
def ExcludesCompleteMinor {V : Type*} (H : SimpleGraph V) (t : ℕ) : Prop :=
  ¬ HasCompleteMinor H t

end

end RIGPadded
