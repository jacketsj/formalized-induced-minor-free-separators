/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.Defs.WeightedGraph
import Mathlib

/-! # Basic metric facts for vertex-weighted shortest-path distance

This file contains just the elementary facts needed to package
`SimpleGraph.weightedDist` as a `PseudoMetricSpace`.
-/

open SimpleGraph

noncomputable section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {w : V → ℝ}

/-- The range of edge-weight sums of walks is bounded below by `0` when weights are
nonnegative. -/
lemma weightedDist_bddBelow (hw : ∀ v, 0 ≤ w v) (x y : V) :
    BddBelow (Set.range fun p : G.Walk x y => p.edgeWeightSum w) := by
  refine' ⟨ 0, Set.forall_mem_range.2 fun p => _ ⟩;
  induction p <;> simp_all +decide [ SimpleGraph.Walk.edgeWeightSum ];
  exact add_nonneg ( add_nonneg ( hw _ ) ( hw _ ) ) ‹_›

/-- The weighted distance is at most the edge-weight sum of any walk. -/
lemma weightedDist_le_walk (hw : ∀ v, 0 ≤ w v) {x y : V} (p : G.Walk x y) :
    G.weightedDist w x y ≤ p.edgeWeightSum w := by
  apply_rules [ ciInf_le, weightedDist_bddBelow ]

/-- For an edge `xy`, the weighted distance is at most `w x + w y`. -/
lemma weightedDist_le_of_adj (hw : ∀ v, 0 ≤ w v) {x y : V} (h : G.Adj x y) :
    G.weightedDist w x y ≤ w x + w y := by
  convert weightedDist_le_walk hw ( SimpleGraph.Walk.cons h SimpleGraph.Walk.nil ) using 1;
  simp +decide [ SimpleGraph.Walk.edgeWeightSum ]

/-- If every walk from `x` to `y` has edge-weight sum at least `c`, then the weighted
distance is at least `c`. -/
lemma le_weightedDist {x y : V} {c : ℝ}
    (hne : Nonempty (G.Walk x y))
    (h : ∀ p : G.Walk x y, c ≤ p.edgeWeightSum w) :
    c ≤ G.weightedDist w x y := by
  exact le_ciInf h

/-- A walk between distinct endpoints has edge-weight sum at least the weight of its first
vertex. -/
lemma Walk.weight_head_le_edgeWeightSum (hw : ∀ v, 0 ≤ w v) {x y : V}
    (p : G.Walk x y) (hne : x ≠ y) :
    w x ≤ p.edgeWeightSum w := by
  induction p <;> simp_all +decide [ SimpleGraph.Walk.edgeWeightSum ];
  rename_i u v w huv p ih;
  by_cases hvw : v = w <;> simp_all +decide [ add_assoc ];
  · refine' add_nonneg ( hw _ ) ( List.sum_nonneg _ );
    intro x hx; rw [ List.mem_map ] at hx; obtain ⟨ e, he, rfl ⟩ := hx; exact (by
    rcases e with ⟨ a, b ⟩ ; exact add_nonneg ( hw a ) ( hw b ));
  · linarith [ hw v ]

/-- For distinct, reachable endpoints, the weighted distance is at least the weight of the
source. -/
lemma weight_le_weightedDist (hw : ∀ v, 0 ≤ w v) {x y : V}
    (hreach : G.Reachable x y) (hne : x ≠ y) :
    w x ≤ G.weightedDist w x y := by
  by_contra h;
  obtain ⟨p, hp⟩ : ∃ p : G.Walk x y, p.edgeWeightSum w < w x := by
    contrapose! h;
    exact le_csInf ⟨ _, ⟨ hreach.some, rfl ⟩ ⟩ ( by aesop );
  exact hp.not_ge ( Walk.weight_head_le_edgeWeightSum hw p hne )

/-- The edge-weight sum is additive under append. -/
lemma Walk.edgeWeightSum_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).edgeWeightSum w = p.edgeWeightSum w + q.edgeWeightSum w := by
  simp [Walk.edgeWeightSum, Walk.edges_append, List.map_append, List.sum_append]

/-- The edge-weight sum is nonnegative. -/
lemma Walk.edgeWeightSum_nonneg (hw : ∀ v, 0 ≤ w v) {x y : V} (p : G.Walk x y) :
    0 ≤ p.edgeWeightSum w := by
  unfold Walk.edgeWeightSum
  apply List.sum_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨e, _, rfl⟩ := ha
  exact Sym2.ind (fun u v => add_nonneg (hw u) (hw v)) e

/-- The weighted distance from a vertex to itself is `0`. -/
lemma weightedDist_self (hw : ∀ v, 0 ≤ w v) (x : V) : G.weightedDist w x x = 0 := by
  refine' le_antisymm _ _;
  · convert weightedDist_le_walk hw ( SimpleGraph.Walk.nil );
  · exact Real.iInf_nonneg fun p => Walk.edgeWeightSum_nonneg hw p

/-- The weighted distance is symmetric. -/
lemma weightedDist_comm (x y : V) : G.weightedDist w x y = G.weightedDist w y x := by
  by_contra h_neq;
  have h_def : G.weightedDist w x y = ⨅ p : G.Walk x y, p.edgeWeightSum w ∧ G.weightedDist w y x = ⨅ p : G.Walk y x, p.edgeWeightSum w := by
    exact ⟨ rfl, rfl ⟩;
  refine' h_neq ( h_def.1.trans ( h_def.2.symm ▸ _ ) );
  rw [ ← Equiv.iInf_congr ( show G.Walk x y ≃ G.Walk y x from { toFun := fun p => p.reverse, invFun := fun p => p.reverse, left_inv := fun p => by simp +decide, right_inv := fun p => by simp +decide } ) ];
  simp +decide [ Walk.edgeWeightSum ]

/-- Triangle inequality for the weighted distance, over a preconnected graph. -/
lemma weightedDist_triangle (hw : ∀ v, 0 ≤ w v) (hconn : G.Preconnected) (x y z : V) :
    G.weightedDist w x z ≤ G.weightedDist w x y + G.weightedDist w y z := by
  have h_eps : ∀ ε > 0, ∃ p : G.Walk x y, p.edgeWeightSum w < G.weightedDist w x y + ε / 2 := by
    intro ε εpos;
    have := exists_lt_of_csInf_lt ( show Set.Nonempty ( Set.range fun p : G.Walk x y => p.edgeWeightSum w ) from ?_ ) ( lt_add_of_pos_right _ ( half_pos εpos ) );
    · aesop;
    · exact ⟨ _, ⟨ hconn x y |> Classical.choice, rfl ⟩ ⟩;
  refine' le_of_forall_pos_le_add fun ε εpos => _;
  obtain ⟨ p, hp ⟩ := h_eps ε εpos;
  have h_eps' : ∀ ε > 0, ∃ q : G.Walk y z, q.edgeWeightSum w < G.weightedDist w y z + ε / 2 := by
    intro ε εpos;
    have := exists_lt_of_csInf_lt ( show Set.Nonempty ( Set.range fun p : G.Walk y z => p.edgeWeightSum w ) from ⟨ _, ⟨ hconn y z |> Classical.choice, rfl ⟩ ⟩ ) ( lt_add_of_pos_right _ ( half_pos εpos ) ) ; aesop;
  obtain ⟨ q, hq ⟩ := h_eps' ε εpos;
  exact le_trans ( weightedDist_le_walk hw ( p.append q ) ) ( by rw [ Walk.edgeWeightSum_append ] ; linarith )

end SimpleGraph
