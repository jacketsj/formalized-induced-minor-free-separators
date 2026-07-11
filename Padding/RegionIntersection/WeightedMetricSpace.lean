/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Padding.RegionIntersection.WeightedDistBasics
import Mathlib

/-! # The vertex-weighted shortest-path pseudo-metric space

This file packages `SimpleGraph.weightedDist` into a `PseudoMetricSpace` instance on the
vertex set of a preconnected graph with nonnegative vertex weights.  It is separated from the
padded-decomposition development so that both the sparse-cover construction and the final
padded-decomposition theorem can refer to the same instance.

For statement verification, the relevant line is `dist := G.weightedDist w` in
`SimpleGraph.weightedPseudoMetricSpace`.  The other fields below are proof obligations
showing that this distance is a pseudometric under the stated hypotheses.
-/

open SimpleGraph

noncomputable section

/-- Pseudo-metric space on a **preconnected** graph via vertex-weighted shortest-path
distance (edge weights `w(u) + w(v)`).

Preconnectedness is required because when vertices lie in different components,
`weightedDist` returns `0` (infimum over an empty set), which would break the triangle
inequality. -/
noncomputable def SimpleGraph.weightedPseudoMetricSpace
    {V : Type*} (G : SimpleGraph V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) :
    PseudoMetricSpace V where
  dist := G.weightedDist w
  dist_self x := weightedDist_self hw x
  dist_comm x y := weightedDist_comm x y
  dist_triangle x y z := weightedDist_triangle hw hconn x y z
  edist_dist x y := by
    convert ENNReal.ofReal_eq_ofReal_iff ( le_of_lt ( Real.exp_pos _ ) ) ( le_of_lt ( Real.exp_pos _ ) );
    any_goals exact Real.log ( G.weightedDist w x y );
    by_cases h : G.weightedDist w x y = 0 <;> simp +decide [ h, Real.exp_log_eq_abs ];
    exact ENNReal.coe_nnreal_eq _

@[simp] lemma SimpleGraph.weightedPseudoMetricSpace_dist
    {V : Type*} (G : SimpleGraph V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hconn : G.Preconnected) (x y : V) :
    @Dist.dist V (G.weightedPseudoMetricSpace w hw hconn).toDist x y = G.weightedDist w x y :=
  rfl

end
