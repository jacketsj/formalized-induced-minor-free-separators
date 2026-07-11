/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.RegionIntersection
import Padding.Defs.MuModel
import Padding.Defs.AsymptoticDimension

/-! # Induced subgraphs on connected components

General infrastructure for applying an induction hypothesis (which requires a connected graph)
to the connected components of a possibly-disconnected graph: the induced subgraph on a
connected component is connected, distances agree with the ambient graph on a component, the
ambient region-intersection model restricts to the component, and the absence of a `μ`-model
is inherited by the component.
-/

open SimpleGraph Set

namespace BandPartition

universe u

variable {W W₂ : Type u} {G' : SimpleGraph W} {H' : SimpleGraph W₂}

/-
An ambient walk from a vertex of `c.supp` stays inside `c.supp` and lifts to the induced
subgraph.
-/
lemma walk_to_induce_supp (c : G'.ConnectedComponent) {a b : W}
    (ha : a ∈ c.supp) (p : G'.Walk a b) :
    ∃ (hb : b ∈ c.supp) (q : (G'.induce c.supp).Walk ⟨a, ha⟩ ⟨b, hb⟩), q.length = p.length := by
  induction p <;> simp_all +decide;
  rename_i u v w huv p ih; specialize ih ( by
    grind +suggestions ) ; obtain ⟨ hc, q, hq ⟩ := ih; use hc; (
  exact ⟨ SimpleGraph.Walk.cons ( by aesop ) q, by simp +decide [ hq ] ⟩)

/-
The induced subgraph on a connected component is connected.
-/
lemma connectedComponent_induce_connected (c : G'.ConnectedComponent) :
    (G'.induce c.supp).Connected := by
  rw [ SimpleGraph.connected_iff ];
  constructor;
  · intro a b;
    obtain ⟨p, hp⟩ : ∃ p : G'.Walk a.val b.val, True := by
      have h_walk : G'.Reachable a.val b.val := by
        grind +suggestions;
      exact ⟨ h_walk.some, trivial ⟩;
    obtain ⟨ q, hq ⟩ := walk_to_induce_supp c a.2 p;
    exact ⟨ hq.choose ⟩;
  · exact ⟨ _, c.exists_rep.choose_spec ⟩

/-
On a connected component, the induced-subgraph distance equals the ambient distance.
-/
lemma induce_dist_eq_supp (c : G'.ConnectedComponent) (a b : ↥c.supp) :
    (G'.induce c.supp).dist a b = G'.dist a.val b.val := by
  refine' le_antisymm _ _;
  · by_cases h : G'.Reachable a.val b.val;
    · obtain ⟨ p, hp ⟩ := h.exists_walk_length_eq_dist;
      obtain ⟨ q, hq ⟩ := walk_to_induce_supp c a.2 p;
      obtain ⟨ q, hq ⟩ := hq;
      exact le_trans ( SimpleGraph.dist_le q ) ( by aesop );
    · grind +suggestions;
  · obtain ⟨q, hq⟩ : ∃ q : (G'.induce c.supp).Walk a b, q.length = (G'.induce c.supp).dist a b := by
      convert SimpleGraph.Reachable.exists_walk_length_eq_dist ( show ( G'.induce c.supp ).Reachable a b from ?_ ) using 1
      generalize_proofs at *;
      have h_connected : (G'.induce c.supp).Connected := by
        convert connectedComponent_induce_connected c using 1;
      exact h_connected a b;
    refine' le_trans _ ( hq.le );
    exact SimpleGraph.dist_le ( q.map ( SimpleGraph.Embedding.induce c.supp |> SimpleGraph.Embedding.toHom ) ) |> le_trans <| by simp +decide ;

/-- The ambient region-intersection model restricts to an induced subgraph. -/
def induceModel (μ' : RegionIntersectionModel G' H') (s : Set W) :
    RegionIntersectionModel (G'.induce s) H' where
  region w := μ'.region w.val
  region_nonempty w := μ'.region_nonempty w.val
  region_connected w := μ'.region_connected w.val
  adj_intersect u v h := μ'.adj_intersect u.val v.val h
  nonadj_disjoint u v hne h :=
    μ'.nonadj_disjoint u.val v.val (fun he => hne (Subtype.ext he)) h

@[simp] lemma induceModel_region (μ' : RegionIntersectionModel G' H') (s : Set W) (w : ↥s) :
    (induceModel μ' s).region w = μ'.region w.val := rfl

/-
Absence of a `μ`-model is inherited by a connected component: a model on the component
lifts to a model on the ambient graph (same bags, centres projected to the ambient graph).
-/
lemma induceModel_no_model (μ' : RegionIntersectionModel G' H') (c : G'.ConnectedComponent)
    (Scenters : Set W) (γ' m : ℕ) (hno : IsEmpty (MuModel μ' Scenters γ' m)) :
    IsEmpty (MuModel (induceModel μ' c.supp) {w : ↥c.supp | w.val ∈ Scenters} γ' m) := by
  refine ⟨ fun M => hno.elim ?_ ⟩;
  refine' { bag := M.bag, nonempty := M.nonempty, connected := M.connected, disjoint := M.disjoint, adjacent := M.adjacent, center := fun j => ( M.center j ).val, center_mem := _, neighborhood_contained := _ };
  · exact fun j => M.center_mem j;
  · intro j v hv hv';
    -- Since $v$ is reachable from $(M.center j).val$ and $G'.dist (M.center j).val v ≤ γ'$, we have $v ∈ c.supp$.
    have hv_supp : v ∈ c.supp := by
      have hv_supp : G'.connectedComponentMk v = c := by
        grind +suggestions;
      exact hv_supp ▸ by simp +decide [ SimpleGraph.ConnectedComponent.supp ] ;
    convert M.neighborhood_contained j ⟨ v, hv_supp ⟩ _ _;
    · obtain ⟨ p ⟩ := walk_to_induce_supp c ( M.center j |>.2 ) ( hv.some );
      exact ⟨ ‹∃ q : ( G'.induce c.supp ).Walk ( M.center j ) ⟨ v, hv_supp ⟩, q.length = ( Nonempty.some hv ).length›.choose ⟩;
    · convert hv' using 1;
      convert induce_dist_eq_supp c ( M.center j ) ⟨ v, hv_supp ⟩ using 1

end BandPartition