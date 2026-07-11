import Mathlib
import InducedMinorFreeSeparators.InducedMinor
import InducedMinorFreeSeparators.ConcurrentFlowDefs

/-!
# Shared definitions for the Flow-Induced Minor formalization

This file re-exports the core definitions (`ConcurrentFlow`, `InducedMinorModel`,
`HasInducedMinor`) from the main project and adds the additional definitions
used by the concurrent-flow proof files:

* `MutuallyInducedPaths` — two paths with disjoint vertex sets and no cross-edges
* `InducedAlmostEmbedding` — an almost-embedding of a graph into another
* `InducedMinorModel.mapIso` — transfer of an induced-minor model along a graph iso
* `SimpleGraph.IsSubcubic` — every vertex has degree ≤ 3
-/

open Finset Real
open scoped BigOperators NNReal

noncomputable section

/-! ### Mutual induced paths -/

def MutuallyInducedPaths {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (l₁ l₂ : List V) : Prop :=
  Disjoint l₁.toFinset l₂.toFinset ∧
    ∀ v₁ ∈ l₁, ∀ v₂ ∈ l₂, ¬G.Adj v₁ v₂

/-! ### Induced almost-embedding -/

structure InducedAlmostEmbedding {V : Type*} [Fintype V] [DecidableEq V]
    {W : Type*} [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) where
  vertexMap : W → V
  edgeMap : (w₁ : W) → (w₂ : W) → H.Adj w₁ w₂ → List V
  edgeMap_valid : ∀ (w₁ w₂ : W) (h : H.Adj w₁ w₂),
    let l := edgeMap w₁ w₂ h
    l.IsChain G.Adj ∧ l.Nodup ∧ 2 ≤ l.length ∧
    l.head? = some (vertexMap w₁) ∧ l.getLast? = some (vertexMap w₂)
  mutually_induced : ∀ (w₁ w₂ w₃ w₄ : W)
    (h₁ : H.Adj w₁ w₂) (h₂ : H.Adj w₃ w₄),
    w₁ ≠ w₃ → w₁ ≠ w₄ → w₂ ≠ w₃ → w₂ ≠ w₄ →
    MutuallyInducedPaths G (edgeMap w₁ w₂ h₁) (edgeMap w₃ w₄ h₂)

/-! ### Transfer of InducedMinorModel along a graph isomorphism -/

private theorem mapIso_branch_connected {V₁ : Type*} {V₂ : Type*} {W : Type*}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {H : SimpleGraph W}
    (m : InducedMinorModel G₁ H) (iso : G₁ ≃g G₂) (w : W) :
    (G₂.induce (iso '' m.branch w)).Connected := by
  have h_connected_image : ∀ (S : Set V₁), (SimpleGraph.induce S G₁).Connected → (SimpleGraph.induce (iso '' S) G₂).Connected := by
    intro S hS;
    convert hS.map _;
    rotate_left;
    exact { v : V₂ // v ∈ iso '' S };
    exact SimpleGraph.induce (⇑iso '' S) G₂;
    use fun x => ⟨ iso x, Set.mem_image_of_mem iso x.2 ⟩;
    all_goals simp +decide [ Function.Surjective ];
    exact fun a ha b hb hab => iso.map_adj_iff.mpr hab;
  exact h_connected_image _ ( m.branch_connected w )

/-- Transfer an InducedMinorModel along a graph isomorphism on the left. -/
def InducedMinorModel.mapIso {V₁ : Type*} {V₂ : Type*} {W : Type*}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {H : SimpleGraph W}
    (m : InducedMinorModel G₁ H) (iso : G₁ ≃g G₂) : InducedMinorModel G₂ H where
  branch w := iso '' (m.branch w)
  branch_connected w := mapIso_branch_connected m iso w
  branch_disjoint w₁ w₂ hne := by
    simp only [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, heb⟩
    exact Set.disjoint_left.mp (m.branch_disjoint w₁ w₂ hne) ha
      (by have := iso.toEquiv.injective heb; subst this; exact hb)
  adj_preserved w₁ w₂ hadj := by
    obtain ⟨v₁, hv₁, v₂, hv₂, hadj'⟩ := m.adj_preserved w₁ w₂ hadj
    exact ⟨iso v₁, Set.mem_image_of_mem _ hv₁, iso v₂, Set.mem_image_of_mem _ hv₂,
      iso.map_rel_iff.mpr hadj'⟩
  nonadj_preserved w₁ w₂ hne hnadj v₁ hv₁ v₂ hv₂ := by
    obtain ⟨a, ha, rfl⟩ := hv₁
    obtain ⟨b, hb, rfl⟩ := hv₂
    intro hadj'
    exact m.nonadj_preserved w₁ w₂ hne hnadj a ha b hb (iso.map_rel_iff.mp hadj')

/-! ### Subcubic graphs -/

namespace SimpleGraph

def IsSubcubic {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v ≤ 3

end SimpleGraph

end
