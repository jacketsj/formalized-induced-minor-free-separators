/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.RegionIntersection.WeightedDistBasics

/-! # Additional lemmas on vertex-weighted shortest-path distance

This file contains the weighted-budget-ball API used in the grown-region construction.
The imported metric-axiom API is proof infrastructure for
`SimpleGraph.weightedPseudoMetricSpace`; it is not part of the reader-facing theorem
statement.
-/

open SimpleGraph

noncomputable section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {w : V → ℝ}

/-
A walk between distinct endpoints has edge-weight-sum at least `w` of its last vertex.
-/
lemma Walk.weight_last_le_edgeWeightSum (hw : ∀ v, 0 ≤ w v) {x y : V}
    (p : G.Walk x y) (hne : x ≠ y) :
    w y ≤ p.edgeWeightSum w := by
  convert Walk.weight_head_le_edgeWeightSum hw p.reverse ( Ne.symm hne ) using 1;
  simp +decide [ Walk.edgeWeightSum, Sym2.lift ]

/-
Taking a prefix of a walk does not increase its edge-weight-sum.
-/
lemma Walk.edgeWeightSum_takeUntil_le [DecidableEq V] (hw : ∀ v, 0 ≤ w v) {x y : V}
    (p : G.Walk x y) {v : V} (hv : v ∈ p.support) :
    (p.takeUntil v hv).edgeWeightSum w ≤ p.edgeWeightSum w := by
  convert le_add_of_nonneg_right ( Walk.edgeWeightSum_nonneg hw ( p.dropUntil v hv ) ) using 1;
  rw [ ← Walk.edgeWeightSum_append, Walk.take_spec ]

/-! ## Weighted budget balls

`weightedBall G w x ρ` is the set of vertices reachable from `x` by a walk of total
edge-weight at most `ρ`.  By construction it is connected in `G` (every prefix of a budget
walk is again a budget walk), which makes the corresponding union of regions connected in the
host graph. -/

/-- The set of vertices reachable from `x` by a walk of total edge-weight at most `ρ`. -/
def weightedBall (G : SimpleGraph V) (w : V → ℝ) (x : V) (ρ : ℝ) : Set V :=
  {y | ∃ p : G.Walk x y, p.edgeWeightSum w ≤ ρ}

lemma mem_weightedBall_self {ρ : ℝ} (hρ : 0 ≤ ρ) (x : V) : x ∈ weightedBall G w x ρ :=
  ⟨Walk.nil, by simpa [Walk.edgeWeightSum] using hρ⟩

/-- A vertex in the budget ball is at weighted distance at most `ρ`. -/
lemma weightedDist_le_of_mem_weightedBall (hw : ∀ v, 0 ≤ w v) {x y : V} {ρ : ℝ}
    (hy : y ∈ weightedBall G w x ρ) : G.weightedDist w x y ≤ ρ := by
  obtain ⟨p, hp⟩ := hy
  exact le_trans (weightedDist_le_walk hw p) hp

/-
If the weighted distance is strictly below `ρ`, the vertex is in the budget ball.
-/
lemma mem_weightedBall_of_weightedDist_lt {x y : V} {ρ : ℝ}
    (hreach : G.Reachable x y) (h : G.weightedDist w x y < ρ) :
    y ∈ weightedBall G w x ρ := by
  contrapose! h;
  convert le_csInf ?_ ?_;
  · exact ⟨ _, ⟨ hreach.some, rfl ⟩ ⟩;
  · rintro _ ⟨ p, rfl ⟩;
    exact le_of_not_gt fun h' => h ⟨ p, h'.le ⟩

/-
Every vertex of the budget ball (other than the centre) has weight at most `ρ`.
-/
lemma weight_le_of_mem_weightedBall (hw : ∀ v, 0 ≤ w v) {x y : V} {ρ : ℝ}
    (hy : y ∈ weightedBall G w x ρ) (hne : y ≠ x) : w y ≤ ρ := by
  obtain ⟨ p, hp ⟩ := hy;
  exact le_trans ( by simpa using Walk.weight_last_le_edgeWeightSum hw p hne.symm ) hp

/-
The budget ball is connected: every member is joined to the centre by a walk staying
inside the budget ball.
-/
lemma exists_walk_mem_weightedBall {x y : V} {ρ : ℝ} (hw : ∀ v, 0 ≤ w v)
    (hy : y ∈ weightedBall G w x ρ) :
    ∃ p : G.Walk x y, ∀ v ∈ p.support, v ∈ weightedBall G w x ρ := by
  by_contra h;
  exact h ( by haveI := Classical.decEq V; exact ⟨ hy.choose, fun v hv => ⟨ hy.choose.takeUntil v hv, by simpa using hy.choose_spec.trans' ( Walk.edgeWeightSum_takeUntil_le hw _ _ ) ⟩ ⟩ )

end SimpleGraph
