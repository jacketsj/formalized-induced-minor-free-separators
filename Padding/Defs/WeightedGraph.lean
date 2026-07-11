/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Weighted Graph Distance

This file defines the shortest-path distance in a graph with vertex weights,
where edge weights are given by `w(u) + w(v)`.

## Main Definitions

* `SimpleGraph.Walk.edgeWeightSum`: The sum of edge weights `w(u) + w(v)` along a walk.
* `SimpleGraph.weightedDist`: The shortest-path distance with edge weights `w(u) + w(v)`.
-/

namespace SimpleGraph

variable {V : Type*}

/-- The sum of vertex-weight edge costs along a walk. For each edge `{u, v}` traversed,
the cost is `w(u) + w(v)`. -/
noncomputable def Walk.edgeWeightSum {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (w : V → ℝ) : ℝ :=
  p.edges.map (fun e => Sym2.lift ⟨fun a b => w a + w b, fun _ _ => by ring⟩ e) |>.sum

/-- The shortest-path distance with edge weights `w(u) + w(v)`. -/
noncomputable def weightedDist
    (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ :=
  ⨅ (p : G.Walk u v), p.edgeWeightSum w

end SimpleGraph
